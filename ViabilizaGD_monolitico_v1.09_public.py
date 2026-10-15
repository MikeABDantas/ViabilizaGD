#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
ViabilizaGD — protótipo monolítico v1.09
==================================

Autor: Mike Alexandre Bicalho Dantas

Ferramenta desktop em Tkinter para:
1. selecionar a File Geodatabase (.gdb), a pasta de shapefiles e a pasta DSS;
2. localizar uma unidade consumidora nos arquivos OpenDSS;
3. inserir uma GD como elemento Generator;
4. comparar o fluxo nos transformadores antes e depois da GD;
5. quando necessário, testar a transferência conjunta das cargas regulares da
   UC, de suas cargas não técnicas correspondentes (quando existirem) e do
   Generator para transformadores candidatos, sempre partindo novamente da
   rede original;
6. salvar relatórios JSON, CSV, TXT e um arquivo DSS de modificações.

Dependência principal para simulação:
    pip install opendssdirect.py

Dependências espaciais opcionais:
    pip install geopandas pyogrio shapely

A interface abre normalmente ao executar:
    python ViabilizaGD_monolitico_v1.09_public.py

No Windows, o arquivo também pode ser aberto com dois cliques quando a extensão
.py estiver associada ao Python. Para evitar a janela de console, pode-se criar
uma cópia chamada ViabilizaGD.pyw.

Observação metodológica da versão atual:
- a UC é localizada exclusivamente em arquivos regulares CargasBT_, CargasMT_
  ou CargasAT_; arquivos CargasBTNT_, CargasMTNT_ e CargasATNT_ não podem ser
  usados como referência de conexão da GD;
- a transferência para um transformador candidato é representada por uma
  alteração direta do bus1 das cargas regulares da UC, de suas cargas NT
  correspondentes e do Generator para o barramento de baixa tensão do candidato,
  preservando os nós/condutores originais da conexão da UC;
- os relatórios distinguem fluxo reverso físico (potência ativa negativa) de
  violação do critério configurado (exportação acima da tolerância);
- no modo "Estado atual do Master — rápido", o fluxo de potência é recalculado
  como snapshot no instante deixado pelo Master, sem herdar o número de passos
  da simulação temporal nem avançar o relógio do OpenDSS;
- os transformadores do OpenDSS são associados exclusivamente ao campo COD_ID
  do UNTRMT.shp, por igualdade normalizada exata e sem buscas por substring em
  outros atributos; associações ausentes ou ambíguas não recebem distância
  espacial;
- quando existem distâncias espaciais válidas, os candidatos são ordenados
  somente em metros. A distância no grafo elétrico é usada apenas como método
  alternativo para todos os candidatos quando a classificação espacial não
  pode ser realizada, sem misturar unidades diferentes na mesma ordenação;
- a criação física de um novo ramal/segmento BT, com impedância e comprimento,
  fica reservada para uma versão posterior.
"""

from __future__ import annotations

import argparse
import csv
import datetime as dt
import heapq
import json
import math
import os
import queue
import re
import sys
import threading
import traceback
import unicodedata
import uuid
from collections import defaultdict, deque
from dataclasses import asdict, dataclass, field, replace
from pathlib import Path
from typing import Any, Callable, Iterable, Iterator, Optional, Sequence

try:
    import tkinter as tk
    from tkinter import filedialog, messagebox, ttk
except Exception as exc:  # pragma: no cover - só ocorre em instalação sem Tk
    raise SystemExit(
        "O Tkinter não está disponível nesta instalação do Python. "
        "Instale uma versão do Python que inclua suporte a Tcl/Tk."
    ) from exc


APP_NAME = "ViabilizaGD"
APP_VERSION = "v1.09"
REGULAR_CONSUMER_LOAD_FILE_PREFIXES = ("cargasbt_", "cargasmt_", "cargasat_")
DEFAULT_SOLAR_PROFILE = (
    0.0, 0.0, 0.0, 0.0, 0.0, 0.0,
    0.03, 0.12, 0.30, 0.55, 0.78, 0.94,
    1.00, 0.94, 0.78, 0.55, 0.30, 0.12,
    0.03, 0.0, 0.0, 0.0, 0.0, 0.0,
)


# =============================================================================
# Estruturas de dados
# =============================================================================

@dataclass
class ConsumerReference:
    requested_id: str
    load_name_hint: str
    source_file: str
    source_line: int
    command: str
    feeder_hint: str = ""


@dataclass
class LoadConnection:
    load_name: str
    bus1: str
    phases: int
    kv: float
    connection: str
    nodes_suffix: str


@dataclass
class TransformerInfo:
    name: str
    buses: list[str]
    winding_kv: list[float]
    hv_terminal: int
    lv_terminal: int
    hv_bus: str
    lv_bus: str
    kv_high: float
    kv_low: float
    kva: float = 0.0


@dataclass
class TransformerPower:
    name: str
    p_hv_kw: float
    physical_reverse: bool
    reverse_violation: bool


@dataclass
class TimeStepResult:
    step_index: int
    hour: float
    converged: bool
    min_voltage_pu: Optional[float]
    min_voltage_node: Optional[str]
    max_voltage_pu: Optional[float]
    max_voltage_node: Optional[str]
    transformers: dict[str, TransformerPower]


@dataclass
class SolutionState:
    mode_code: Optional[int]
    mode_name: str
    hour: Optional[float]


@dataclass
class ScenarioRun:
    master_file: str
    temporal_mode: str
    load_name: str
    load_names: list[str]
    load_bus: str
    load_buses: dict[str, str]
    generator_bus: Optional[str]
    moved_to_transformer: Optional[str]
    inherited_solution_state: SolutionState
    steps: list[TimeStepResult]
    warnings: list[str] = field(default_factory=list)


@dataclass
class TransformerComparison:
    transformer: str
    original_min_p_kw: float
    modified_min_p_kw: float
    original_max_export_kw: float
    modified_max_export_kw: float
    original_physical_reverse: bool
    modified_physical_reverse: bool
    original_reverse_violation: bool
    modified_reverse_violation: bool
    new_reverse_violation: bool
    aggravated_reverse_violation: bool
    aggravation_kw: float


@dataclass
class ComparisonSummary:
    transformers: dict[str, TransformerComparison]
    original_physical_reverse: list[str]
    modified_physical_reverse: list[str]
    new_physical_reverse: list[str]
    original_reverse_violations: list[str]
    modified_reverse_violations: list[str]
    new_reverse_violations: list[str]
    eliminated_reverse_violations: list[str]
    aggravated_reverse_violations: list[str]
    acceptable: bool


@dataclass
class CandidateResult:
    transformer: str
    lv_bus: str
    rank: int
    distance_value: float
    distance_unit: str
    accepted: bool
    comparison: ComparisonSummary
    scenario_runs: list[ScenarioRun]
    reason: str
    spatial_cod_id: Optional[str] = None
    spatial_reference_cod_id: Optional[str] = None


@dataclass(frozen=True)
class CodIdMatch:
    """Associação única entre um Transformer do OpenDSS e UNTRMT.COD_ID."""

    transformer_name: str
    cod_id: str
    normalized_cod_id: str
    row_position: int
    rule: str


@dataclass
class SpatialDistanceResult:
    """Distâncias métricas e associações espaciais que puderam ser auditadas."""

    distances_m: dict[str, float] = field(default_factory=dict)
    cod_ids: dict[str, str] = field(default_factory=dict)
    original_cod_id: Optional[str] = None


@dataclass(frozen=True)
class RankedCandidate:
    transformer: TransformerInfo
    distance_value: float
    distance_unit: str
    spatial_cod_id: Optional[str] = None
    spatial_reference_cod_id: Optional[str] = None


@dataclass
class AnalysisConfig:
    gdb_path: str
    shp_path: str
    dss_path: str
    output_path: str
    consumer_id: str
    generator_kw: float
    generator_pf: float
    generator_model: int
    generator_profile: str
    master_scope: str
    selected_master: str
    temporal_mode: str
    reverse_tolerance_kw: float
    aggravation_tolerance_kw: float
    max_candidates: int
    try_relocation: bool
    voltage_min_pu: float
    voltage_max_pu: float
    check_voltage: bool


@dataclass
class AnalysisOutcome:
    app_name: str
    app_version: str
    config: AnalysisConfig
    consumer_reference: ConsumerReference
    load_connection: LoadConnection
    load_connections: list[LoadConnection]
    master_files: list[str]
    baseline_runs: list[ScenarioRun]
    original_gd_runs: list[ScenarioRun]
    initial_comparison: ComparisonSummary
    original_transformer: Optional[str]
    candidate_results: list[CandidateResult]
    accepted_candidate: Optional[str]
    output_directory: str
    final_message: str
    warnings: list[str]


class AnalysisCancelled(RuntimeError):
    pass


# =============================================================================
# Funções utilitárias gerais
# =============================================================================

# O que esta função faz:
# Deixa nomes e códigos no mesmo formato para facilitar as comparações.
def normalize_identifier(value: Any) -> str:
    """Normaliza identificadores para comparações tolerantes a pontuação."""
    if value is None:
        return ""
    text = unicodedata.normalize("NFKD", str(value))
    text = "".join(ch for ch in text if not unicodedata.combining(ch))
    return re.sub(r"[^a-zA-Z0-9]", "", text).lower()


# O que esta função faz:
# Gera, em ordem de preferência, chaves exatas possíveis de UNTRMT.COD_ID.
def transformer_cod_id_candidates(transformer_name: str) -> list[tuple[str, str]]:
    """Gera, em ordem de preferência, chaves exatas possíveis de UNTRMT.COD_ID.

    O OpenDSS normalmente usa nomes como ``trf_739et002287299a``, enquanto o
    COD_ID da BDGD pode ser ``739ET002287299``. Primeiro é tentado o conteúdo
    integral após o prefixo de classe/TRF. Somente depois é removido um sufixo
    final A, B ou C quando ele vem após um algarismo. Nenhuma substring é usada.
    """
    normalized = normalize_identifier(transformer_name)
    if normalized.startswith("transformer"):
        normalized = normalized[len("transformer"):]
    if normalized.startswith("trf"):
        normalized = normalized[len("trf"):]
    if not normalized:
        return []

    candidates = [(normalized, "COD_ID integral")]
    if re.search(r"\d[abc]$", normalized):
        candidates.append((normalized[:-1], "COD_ID sem sufixo de fase A/B/C"))
    return candidates


# O que esta função faz:
# Retorna apenas uma associação exata, existente e não ambígua.
def match_transformer_to_cod_id(
    transformer_name: str,
    cod_index: dict[str, list[tuple[int, str]]],
) -> tuple[Optional[CodIdMatch], str]:
    """Retorna apenas uma associação exata, existente e não ambígua."""
    for normalized_cod_id, rule in transformer_cod_id_candidates(transformer_name):
        rows = cod_index.get(normalized_cod_id)
        if rows is None:
            continue
        if len(rows) != 1:
            return None, (
                f"COD_ID {rows[0][1] if rows else normalized_cod_id} aparece "
                f"{len(rows)} vezes no UNTRMT.shp"
            )
        row_position, raw_cod_id = rows[0]
        return CodIdMatch(
            transformer_name=transformer_name,
            cod_id=raw_cod_id,
            normalized_cod_id=normalized_cod_id,
            row_position=row_position,
            rule=rule,
        ), ""
    attempted = ", ".join(
        candidate for candidate, _rule in transformer_cod_id_candidates(transformer_name)
    )
    return None, f"nenhum COD_ID exato encontrado (tentativas: {attempted or 'nenhuma'})"


# O que esta função faz:
# Localiza um arquivo diretamente na pasta sem depender da caixa do nome.
def find_case_insensitive_file(folder: Path, filename: str) -> Optional[Path]:
    """Localiza um arquivo diretamente na pasta sem depender da caixa do nome."""
    wanted = filename.casefold()
    try:
        return next(
            (
                path for path in folder.iterdir()
                if path.is_file() and path.name.casefold() == wanted
            ),
            None,
        )
    except OSError:
        return None


# O que esta função faz:
# Transforma um identificador em um sufixo curto e seguro para nomear objetos do OpenDSS.
def safe_object_suffix(value: str, max_length: int = 24) -> str:
    normalized = re.sub(r"[^A-Za-z0-9_]", "_", value).strip("_")
    if not normalized:
        normalized = "UC"
    return normalized[-max_length:]


# O que esta função faz:
# Remove o número dos nós e mantém apenas o nome principal do barramento.
def canonical_bus(bus: str) -> str:
    """Remove os números de nós do nome do barramento."""
    if not bus:
        return ""
    text = str(bus).strip().strip('"\'[]()')
    return text.split(".", 1)[0].lower()


# O que esta função faz:
# Separa os números dos nós ligados a um barramento.
def bus_nodes_suffix(bus: str) -> str:
    if not bus or "." not in bus:
        return ""
    return "." + bus.split(".", 1)[1]


# O que esta função faz:
# Adiciona aspas quando um valor precisa delas para ser entendido pelo OpenDSS.
def quote_dss(value: str) -> str:
    """Coloca valor entre aspas quando ele contém caracteres problemáticos."""
    text = str(value)
    if re.search(r"\s", text):
        return f'"{text}"'
    return text


# O que esta função faz:
# Converte um número informado como texto para um valor numérico.
def parse_decimal(text: str) -> float:
    return float(str(text).strip().replace(" ", "").replace(",", "."))


# O que esta função faz:
# Converte o valor para número; se não for possível, utiliza o valor padrão.
def to_float(value: Any, default: float = 0.0) -> float:
    try:
        return float(value)
    except (TypeError, ValueError):
        try:
            return parse_decimal(str(value))
        except Exception:
            return default


# O que esta função faz:
# Monta uma frase legível a partir de uma lista de nomes.
def human_join(items: Sequence[str]) -> str:
    values = [str(item) for item in items if str(item)]
    if not values:
        return "nenhum"
    if len(values) == 1:
        return values[0]
    return ", ".join(values[:-1]) + " e " + values[-1]


# O que esta função faz:
# Verifica se o usuário pediu para cancelar a execução.
def ensure_not_cancelled(cancel_event: threading.Event) -> None:
    if cancel_event.is_set():
        raise AnalysisCancelled("Análise cancelada pelo usuário.")


# O que esta função faz:
# Lê um arquivo de texto e informa a codificação que funcionou.
def read_text_with_encoding(path: Path) -> tuple[str, str]:
    """Lê um arquivo de texto e informa a codificação que funcionou."""
    for encoding in ("utf-8-sig", "utf-8", "cp1252", "latin-1"):
        try:
            return path.read_text(encoding=encoding), encoding
        except UnicodeDecodeError:
            continue
    return path.read_text(encoding="latin-1", errors="replace"), "latin-1"


# O que esta função faz:
# Lê o arquivo tentando codificações comuns usadas nos modelos DSS.
def read_text_flexible(path: Path) -> str:
    text, _encoding = read_text_with_encoding(path)
    return text


# O que esta função faz:
# Normaliza visualmente o caminho sem exigir ausência de acentos.
def normalize_path_for_display(path: str) -> str:
    """Normaliza visualmente o caminho sem exigir ausência de acentos."""
    value = str(path).strip()
    return os.path.normpath(value) if value else ""


# O que esta função faz:
# Comenta comandos Export e suas linhas de continuação em uma cópia do DSS.
def disable_export_commands(text: str) -> tuple[str, int]:
    """
    Comenta comandos Export e suas linhas de continuação em uma cópia do DSS.

    Os arquivos originais não são alterados. Isso evita que Masters usados na
    análise gerem CSVs que o ViabilizaGD não consome e contorna falhas de
    codificação nas rotinas legadas de exportação do OpenDSS.
    """
    output: list[str] = []
    disabled_count = 0
    suppress_continuations = False

    for raw_line in text.splitlines(keepends=True):
        line_without_ending = raw_line.rstrip("\r\n")
        ending = raw_line[len(line_without_ending):]
        stripped = line_without_ending.lstrip()
        indent = line_without_ending[: len(line_without_ending) - len(stripped)]

        is_comment = stripped.startswith("!") or stripped.startswith("//")
        is_export = bool(re.match(r"(?i)^export(?:\s|$)", stripped)) and not is_comment
        is_continuation = stripped.startswith("~")

        if is_export:
            disabled_count += 1
            suppress_continuations = True
            output.append(
                f"{indent}! ViabilizaGD: comando ignorado durante a análise -> "
                f"{stripped}{ending}"
            )
            continue

        if suppress_continuations and is_continuation:
            output.append(
                f"{indent}! ViabilizaGD: continuação de Export ignorada -> "
                f"{stripped}{ending}"
            )
            continue

        suppress_continuations = False
        output.append(raw_line)

    return "".join(output), disabled_count


# O que esta função faz:
# Remove comentários ! e //, preservando o conteúdo dentro de aspas.
def strip_dss_comment(line: str) -> str:
    """Remove comentários ! e //, preservando o conteúdo dentro de aspas."""
    result: list[str] = []
    quote: Optional[str] = None
    index = 0
    while index < len(line):
        char = line[index]
        if quote:
            result.append(char)
            if char == quote:
                quote = None
            index += 1
            continue
        if char in ('"', "'"):
            quote = char
            result.append(char)
            index += 1
            continue
        if char == "!":
            break
        if char == "/" and index + 1 < len(line) and line[index + 1] == "/":
            break
        result.append(char)
        index += 1
    return "".join(result).strip()


# O que esta função faz:
# Lê comandos OpenDSS, juntando linhas iniciadas por ~.
def iter_dss_commands(path: Path) -> Iterator[tuple[int, str]]:
    """Lê comandos OpenDSS, juntando linhas iniciadas por ~."""
    text = read_text_flexible(path)
    current = ""
    start_line = 0
    for line_number, raw_line in enumerate(text.splitlines(), start=1):
        line = strip_dss_comment(raw_line)
        if not line:
            continue
        if line.lstrip().startswith("~"):
            continuation = line.lstrip()[1:].strip()
            if current:
                current += " " + continuation
            else:
                current = continuation
                start_line = line_number
            continue
        if current:
            yield start_line, current.strip()
        current = line.strip()
        start_line = line_number
    if current:
        yield start_line, current.strip()


# O que esta função faz:
# Identifica o nome de um objeto em comandos como New Load.nome.
def extract_object_name(command: str, object_class: str) -> Optional[str]:
    # O GeoPerdas costuma escrever New "Load.nome"; também aceita a forma
    # usual sem aspas (New Load.nome) e a notação entre colchetes.
    pattern = (
        rf"(?i)^\s*(?:new|edit)\s+[\"'\[]?"
        rf"{re.escape(object_class)}\.([^\s\"'\]]+)"
    )
    match = re.search(pattern, command)
    if not match:
        return None
    return match.group(1).strip('"\'[]()')


# O que esta função faz:
# Extrai propriedades simples key=value de um comando DSS.
def extract_property(command: str, property_name: str) -> Optional[str]:
    """Extrai propriedades simples key=value de um comando DSS."""
    pattern = rf"(?i)(?:^|\s){re.escape(property_name)}\s*=\s*(\([^)]*\)|\[[^]]*\]|\"[^\"]*\"|'[^']*'|[^\s]+)"
    match = re.search(pattern, command)
    if not match:
        return None
    return match.group(1).strip().strip('"\'[]()')


# O que esta função faz:
# Procura o código do alimentador no nome do arquivo DSS.
def infer_feeder_from_filename(filename: str) -> str:
    stem = Path(filename).stem
    match = re.search(r"_(?:19|20)\d{6,10}_([A-Za-z0-9]+)_", stem)
    if match:
        return match.group(1)
    tokens = stem.split("_")
    for token in tokens:
        if re.fullmatch(r"[A-Za-z]{2,5}\d{1,5}", token):
            return token
    return ""


# O que esta função faz:
# Indica se o arquivo pode identificar uma UC regular para conexão da GD.
def is_regular_consumer_load_file(path: Path) -> bool:
    """Indica se o arquivo pode identificar uma UC regular para conexão da GD."""
    filename = Path(path).name.casefold()
    return filename.startswith(REGULAR_CONSUMER_LOAD_FILE_PREFIXES)


# O que esta função faz:
# Reconhece o token NT sem confundi-lo com parte do identificador da UC.
def is_nontechnical_load_name(load_name: str) -> bool:
    """Reconhece o token NT sem confundi-lo com parte do identificador da UC."""
    return re.search(r"(?i)(?:^|_)nt(?:_|$)", str(load_name)) is not None


# O que esta função faz:
# Procura a unidade consumidora nos arquivos de cargas regulares. Não usa cargas NT para escolher o ponto de conexão.
def find_consumer_reference(
    dss_folder: Path,
    consumer_id: str,
    log: Callable[[str], None],
    cancel_event: threading.Event,
    files: Optional[Sequence[Path]] = None,
) -> ConsumerReference:
    """Localiza a UC somente em CargasBT_, CargasMT_ ou CargasAT_ regulares."""
    requested_norm = normalize_identifier(consumer_id)
    if not requested_norm:
        raise ValueError("Informe o identificador da unidade consumidora.")

    candidate_files = sorted(
        {Path(path).resolve() for path in files}
        if files is not None
        else {path.resolve() for path in dss_folder.rglob("*.dss")}
    )
    if not candidate_files:
        raise FileNotFoundError("Não foram encontrados arquivos .dss na pasta selecionada.")

    search_files = [
        path for path in candidate_files
        if is_regular_consumer_load_file(path)
    ]
    if not search_files:
        raise FileNotFoundError(
            "Não foram encontrados arquivos regulares CargasBT_, CargasMT_ ou "
            "CargasAT_ no escopo pesquisado. Arquivos de cargas não técnicas "
            "(CargasBTNT_, CargasMTNT_ e CargasATNT_) não podem identificar o "
            "ponto de conexão da GD."
        )

    log(
        f"Pesquisa da UC restrita a {len(search_files)} arquivo(s) de carga regular "
        "CargasBT_/CargasMT_/CargasAT_."
    )

    direct_candidates: list[ConsumerReference] = []
    generic_candidates: list[ConsumerReference] = []

    for file_index, path in enumerate(search_files, start=1):
        ensure_not_cancelled(cancel_event)
        try:
            for line_number, command in iter_dss_commands(path):
                command_norm = normalize_identifier(command)
                if requested_norm not in command_norm:
                    continue
                load_name = extract_object_name(command, "load")
                if not load_name or is_nontechnical_load_name(load_name):
                    continue
                reference = ConsumerReference(
                    requested_id=consumer_id,
                    load_name_hint=load_name or consumer_id,
                    source_file=str(path),
                    source_line=line_number,
                    command=command,
                    feeder_hint=infer_feeder_from_filename(path.name),
                )
                load_norm = normalize_identifier(load_name)
                if requested_norm == load_norm or requested_norm in load_norm or load_norm in requested_norm:
                    direct_candidates.append(reference)
                else:
                    generic_candidates.append(reference)
        except OSError as exc:
            log(f"Aviso: não foi possível ler {path.name}: {exc}")

        if file_index % 50 == 0:
            log(f"Pesquisa da UC: {file_index}/{len(search_files)} arquivos examinados.")

    candidates = direct_candidates or generic_candidates
    if not candidates:
        raise LookupError(
            f"A unidade consumidora {consumer_id} não foi localizada em arquivos "
            "regulares CargasBT_, CargasMT_ ou CargasAT_. Ocorrências em arquivos "
            "CargasBTNT_, CargasMTNT_ ou CargasATNT_ não são aceitas como ponto "
            "de conexão da GD."
        )

    # Todos os candidatos já pertencem a arquivos regulares; usa o nome mais
    # específico e uma ordenação determinística entre cenários equivalentes.
    candidates.sort(
        key=lambda ref: (
            len(ref.load_name_hint),
            ref.source_file,
            ref.source_line,
        )
    )
    selected = candidates[0]
    log(
        f"Unidade consumidora localizada em {Path(selected.source_file).name}, "
        f"linha {selected.source_line}; Load sugerido: {selected.load_name_hint}."
    )
    return selected


# O que esta função faz:
# Extrai o caminho de comandos Redirect/Compile simples do OpenDSS.
def extract_redirect_target(command: str) -> Optional[str]:
    """Extrai o caminho de comandos Redirect/Compile simples do OpenDSS."""
    clean = strip_dss_comment(command).strip()
    match = re.match(r"(?i)^(?:redirect|compile)\s+(.+?)\s*$", clean)
    if not match:
        return None
    target = match.group(1).strip()
    if target.startswith("[") and target.endswith("]"):
        target = target[1:-1].strip()
    elif len(target) >= 2 and target[0] == target[-1] and target[0] in {'"', "'"}:
        target = target[1:-1]
    return target.strip() or None


# O que esta função faz:
# Segue os comandos Redirect e Compile para descobrir os arquivos usados por cada Master.
def collect_master_dependency_files(
    masters: Sequence[Path],
    log: Callable[[str], None],
) -> list[Path]:
    """Coleta cada Master e os DSS alcançados por Redirect/Compile recursivos."""
    pending = deque(Path(master).resolve() for master in masters)
    visited: set[Path] = set()

    while pending:
        path = pending.popleft()
        if path in visited:
            continue
        visited.add(path)
        try:
            commands = iter_dss_commands(path)
            for _line_number, command in commands:
                target = extract_redirect_target(command)
                if not target:
                    continue
                referenced = Path(target)
                if not referenced.is_absolute():
                    referenced = path.parent / referenced
                referenced = referenced.resolve()
                if referenced.suffix.lower() == ".dss" and referenced.exists():
                    pending.append(referenced)
        except OSError as exc:
            log(f"Aviso: não foi possível rastrear as referências de {path.name}: {exc}")

    return sorted(visited)


# O que esta função faz:
# Encontra os arquivos Master e, quando solicitado, filtra pelo alimentador.
def discover_master_files(
    dss_folder: Path,
    feeder_hint: str,
    scope: str,
    selected_master: str,
) -> list[Path]:
    masters = sorted(dss_folder.rglob("Master*.dss"))
    if not masters:
        masters = sorted(
            path for path in dss_folder.rglob("*.dss")
            if path.stem.lower().startswith("master")
        )
    if not masters:
        raise FileNotFoundError(
            "Nenhum arquivo Master*.dss foi encontrado na pasta OpenDSS."
        )

    if scope == "Selecionar um Master":
        if not selected_master:
            raise ValueError("Selecione o arquivo Master que será analisado.")
        selected = Path(selected_master)
        if not selected.exists():
            raise FileNotFoundError(f"O arquivo Master selecionado não existe: {selected}")
        return [selected]

    if feeder_hint:
        filtered = [path for path in masters if f"_{feeder_hint}_".lower() in path.name.lower()]
        if filtered:
            masters = filtered

    return masters


# O que esta função faz:
# Confere os caminhos informados antes de iniciar a simulação.
def validate_input_paths(config: AnalysisConfig) -> list[str]:
    warnings: list[str] = []
    gdb = Path(config.gdb_path)
    shp = Path(config.shp_path)
    dss = Path(config.dss_path)

    if not gdb.is_dir():
        raise FileNotFoundError("A pasta .gdb informada não existe.")
    if gdb.suffix.lower() != ".gdb":
        warnings.append("A pasta selecionada como geodatabase não termina com .gdb.")
    if not any(gdb.glob("*.gdbtable")):
        warnings.append("Não foram encontrados arquivos .gdbtable dentro da pasta .gdb.")

    if not shp.is_dir():
        raise FileNotFoundError("A pasta de shapefiles informada não existe.")
    shp_names = {path.name.lower() for path in shp.glob("*.shp")}
    for expected in ("untrmt.shp", "ssdmt.shp", "ssdbt.shp", "ponnot.shp"):
        if expected not in shp_names:
            warnings.append(f"Shapefile esperado não encontrado: {expected}")

    if not dss.is_dir():
        raise FileNotFoundError("A pasta OpenDSS informada não existe.")
    if not any(dss.rglob("*.dss")):
        raise FileNotFoundError("A pasta OpenDSS não contém arquivos .dss.")

    output = Path(config.output_path)
    output.mkdir(parents=True, exist_ok=True)
    return warnings


# =============================================================================
# Adaptador OpenDSSDirect
# =============================================================================

class OpenDSSBackend:
    """Encapsula o uso da API classic do OpenDSSDirect.py."""

    # O que esta função faz:
    # Prepara as informações e os recursos necessários para utilizar esta parte do programa.
    def __init__(self, log: Optional[Callable[[str], None]] = None) -> None:
        self.log = log or (lambda _text: None)
        self._masters_with_reported_exports: set[str] = set()
        self._masters_with_reported_states: set[str] = set()

        try:
            from opendssdirect import dss as dss_instance

        except ModuleNotFoundError as exc:
            missing_name = str(getattr(exc, "name", "") or "")
            if missing_name.lower() == "opendssdirect":
                raise RuntimeError(
                    "A biblioteca OpenDSSDirect.py não está instalada no "
                    "interpretador Python usado pelo ViabilizaGD.\n\n"
                    f"Interpretador atual:\n{sys.executable}\n\n"
                    "Instale usando este mesmo interpretador:\n\n"
                    f'"{sys.executable}" -m pip install OpenDSSDirect.py\n\n'
                    "Depois, abra novamente o ViabilizaGD."
                ) from exc

            raise RuntimeError(
                "O pacote OpenDSSDirect.py foi localizado, mas uma dependência "
                "necessária não pôde ser importada.\n\n"
                f"Interpretador atual:\n{sys.executable}\n\n"
                f"Dependência ausente: {missing_name or 'não identificada'}\n"
                f"Erro real: {type(exc).__name__}: {exc}"
            ) from exc

        except ImportError as exc:
            raise RuntimeError(
                "O pacote OpenDSSDirect.py foi localizado, mas não pôde ser "
                "importado corretamente.\n\n"
                f"Interpretador atual:\n{sys.executable}\n\n"
                f"Erro real: {type(exc).__name__}: {exc}"
            ) from exc

        except Exception as exc:
            raise RuntimeError(
                "O OpenDSSDirect.py foi encontrado, mas ocorreu um erro "
                "inesperado durante seu carregamento.\n\n"
                f"Interpretador atual:\n{sys.executable}\n\n"
                f"Erro real: {type(exc).__name__}: {exc}"
            ) from exc

        self.dss = dss_instance

    # O que esta função faz:
    # Envia um comando de texto ao motor do OpenDSS.
    def command(self, text: str) -> Any:
        # O objeto moderno é chamável; Text.Command é mantido como reserva.
        try:
            return self.dss(text)
        except TypeError:
            return self.dss.Text.Command(text)

    # O que esta função faz:
    # Cria, quando necessário, uma cópia temporária sem comandos Export.
    def _temporary_master_without_exports(
        self, master_file: Path
    ) -> tuple[Path, Optional[Path], int]:
        """Cria, quando necessário, uma cópia temporária sem comandos Export."""
        source_text, source_encoding = read_text_with_encoding(master_file)
        sanitized_text, disabled_count = disable_export_commands(source_text)

        if disabled_count == 0:
            return master_file, None, 0

        temporary_name = (
            f".__viabilizagd_{uuid.uuid4().hex}_"
            f"{master_file.name}"
        )
        temporary_path = master_file.with_name(temporary_name)
        temporary_path.write_text(sanitized_text, encoding=source_encoding)
        return temporary_path, temporary_path, disabled_count

    # O que esta função faz:
    # Limpa o circuito e processa o Master sem modificar o arquivo original.
    def compile(self, master_file: Path) -> None:
        """
        Limpa o circuito e processa o Master sem modificar o arquivo original.

        Quando o Master contém comandos Export, uma cópia temporária é criada
        na mesma pasta, com esses comandos comentados. Assim, os Redirects
        relativos continuam funcionando e o OpenDSS não tenta gravar exports
        desnecessários em caminhos problemáticos.
        """
        self.dss.Basic.ClearAll()
        master_absolute = master_file.resolve()
        execution_master: Path = master_absolute
        temporary_path: Optional[Path] = None
        disabled_count = 0

        try:
            execution_master, temporary_path, disabled_count = (
                self._temporary_master_without_exports(master_absolute)
            )

            master_key = os.path.normcase(str(master_absolute))
            if (
                disabled_count > 0
                and master_key not in self._masters_with_reported_exports
            ):
                self.log(
                    f"{master_absolute.name}: {disabled_count} comando(s) "
                    "Export será(ão) ignorado(s) somente durante a análise. "
                    "O arquivo original permanece intacto."
                )
                self._masters_with_reported_exports.add(master_key)

            # Redirect mantém a resolução dos caminhos relativos ao arquivo.
            self.command(f"Redirect [{execution_master}]")

        except Exception as exc:
            raise RuntimeError(
                f"Falha ao processar o Master {master_absolute.name}.\n\n"
                f"Caminho: {master_absolute}\n"
                f"Erro real: {type(exc).__name__}: {exc}"
            ) from exc

        finally:
            if temporary_path is not None:
                try:
                    temporary_path.unlink(missing_ok=True)
                except OSError as exc:
                    self.log(
                        "Aviso: não foi possível apagar o Master temporário "
                        f"{temporary_path.name}: {exc}"
                    )

    # O que esta função faz:
    # Executa o cálculo de fluxo de potência no OpenDSS.
    def solve(self) -> None:
        self.dss.Solution.Solve()

    # O que esta função faz:
    # Resolve o ponto atual com controles, sem avançar o tempo do OpenDSS.
    def solve_snapshot_current_time(self) -> None:
        """Resolve o ponto atual com controles, sem avançar o tempo do OpenDSS."""
        self.dss.Solution.SolveSnap()

    # O que esta função faz:
    # Consulta se o fluxo de potência do OpenDSS terminou com convergência.
    def converged(self) -> bool:
        try:
            return bool(self.dss.Solution.Converged())
        except Exception:
            return True

    # O que esta função faz:
    # Lista os nomes de todas as cargas do circuito carregado.
    def all_load_names(self) -> list[str]:
        return [str(name) for name in self.dss.Loads.AllNames() if str(name)]

    # O que esta função faz:
    # Retorna cargas regulares da UC seguidas de suas equivalentes NT.
    def resolve_load_names(self, consumer_id: str, hint: str) -> list[str]:
        """Retorna cargas regulares da UC seguidas de suas equivalentes NT."""
        names = self.all_load_names()
        if not names:
            raise LookupError("O circuito compilado não contém elementos Load.")

        requested_norm = normalize_identifier(consumer_id)
        requested_text = str(consumer_id).strip().lower()

        # O que esta função faz:
        # Verifica se uma carga pertence à unidade consumidora procurada.
        def belongs_to_consumer(name: str) -> bool:
            name_norm = normalize_identifier(name)
            if name_norm == requested_norm:
                return True
            if requested_text and re.search(
                rf"(?<![a-z0-9]){re.escape(requested_text)}(?![a-z0-9])",
                name.lower(),
            ):
                return True
            # Identificadores longos (como hashes da BDGD) permanecem seguros
            # mesmo quando o nome do Load remove prefixos/separadores.
            return len(requested_norm) >= 16 and requested_norm in name_norm

        matches = [
            name for name in names
            if belongs_to_consumer(name)
        ]

        if not matches:
            exact_map = {normalize_identifier(name): name for name in names}
            for candidate in (hint, consumer_id):
                norm = normalize_identifier(candidate)
                if norm in exact_map:
                    matches = [exact_map[norm]]
                    break

        if matches:
            regular = sorted(
                (name for name in matches if not is_nontechnical_load_name(name)),
                key=lambda name: (len(name), name.casefold()),
            )
            nontechnical = sorted(
                (name for name in matches if is_nontechnical_load_name(name)),
                key=lambda name: (len(name), name.casefold()),
            )
            if not regular:
                raise LookupError(
                    f"A UC {consumer_id} apareceu no circuito somente em cargas não "
                    "técnicas (_NT_). A conexão da GD exige pelo menos um objeto "
                    "Load regular."
                )
            return regular + nontechnical

        raise LookupError(
            f"O Load da UC {consumer_id} foi encontrado no texto DSS, mas não apareceu "
            "no circuito depois da compilação do Master."
        )

    # O que esta função faz:
    # Consulta e devolve load connections a partir dos dados disponíveis.
    def get_load_connections(self, load_names: Sequence[str]) -> list[LoadConnection]:
        connections = [self.get_load_connection(name) for name in load_names]
        if not connections:
            raise LookupError("Nenhum objeto Load foi associado à unidade consumidora.")
        return connections

    # O que esta função faz:
    # Consulta e devolve load connection a partir dos dados disponíveis.
    def get_load_connection(self, load_name: str) -> LoadConnection:
        self.dss.Loads.Name(load_name)
        self.dss.Circuit.SetActiveElement(f"Load.{load_name}")
        buses = [str(value) for value in self.dss.CktElement.BusNames()]
        if not buses:
            raise LookupError(f"Não foi possível obter o bus1 do Load.{load_name}.")
        bus1 = buses[0]
        phases = int(self.dss.Loads.Phases())
        kv = float(self.dss.Loads.kV())
        try:
            connection = "delta" if bool(self.dss.Loads.IsDelta()) else "wye"
        except Exception:
            connection = "wye"
        return LoadConnection(
            load_name=load_name,
            bus1=bus1,
            phases=max(1, phases),
            kv=kv,
            connection=connection,
            nodes_suffix=bus_nodes_suffix(bus1),
        )

    # O que esta função faz:
    # Altera o barramento de ligação de uma carga no circuito da simulação.
    def edit_load_bus(self, load_name: str, bus1: str) -> None:
        self.command(f"Edit Load.{load_name} bus1={quote_dss(bus1)}")

    # O que esta função faz:
    # Insere um Generator no OpenDSS com as características informadas na interface.
    def add_generator(
        self,
        generator_name: str,
        connection: LoadConnection,
        bus1: str,
        kw: float,
        pf: float,
        model: int,
        profile: str,
    ) -> None:
        daily_clause = ""
        if profile == "Curva solar padrão de 24 horas":
            shape_name = f"VGD_SOLAR_{safe_object_suffix(generator_name, 18)}"
            multipliers = " ".join(f"{value:.6f}" for value in DEFAULT_SOLAR_PROFILE)
            self.command(
                f"New LoadShape.{shape_name} npts=24 interval=1 mult=({multipliers})"
            )
            daily_clause = f" daily={shape_name} status=variable"

        cmd = (
            f"New Generator.{generator_name} "
            f"phases={connection.phases} "
            f"bus1={quote_dss(bus1)} "
            f"conn={connection.connection} "
            f"kV={connection.kv:.12g} "
            f"kW={kw:.12g} "
            f"PF={pf:.12g} "
            f"model={int(model)}"
            f"{daily_clause}"
        )
        self.command(cmd)

    # O que esta função faz:
    # Converte pares de valores reais e imaginários para números complexos.
    @staticmethod
    def _complex_values(values: Sequence[Any]) -> list[complex]:
        if not values:
            return []
        if isinstance(values[0], complex):
            return [complex(value) for value in values]
        result: list[complex] = []
        for index in range(0, len(values) - 1, 2):
            result.append(complex(float(values[index]), float(values[index + 1])))
        return result

    # O que esta função faz:
    # Lê os enrolamentos, as tensões e os barramentos de um transformador.
    def transformer_info(self, name: str) -> TransformerInfo:
        self.dss.Transformers.Name(name)
        num_windings = int(self.dss.Transformers.NumWindings())
        winding_kv: list[float] = []
        winding_kva: list[float] = []
        for winding in range(1, num_windings + 1):
            self.dss.Transformers.Wdg(winding)
            winding_kv.append(float(self.dss.Transformers.kV()))
            try:
                winding_kva.append(float(self.dss.Transformers.kVA()))
            except Exception:
                winding_kva.append(0.0)

        self.dss.Circuit.SetActiveElement(f"Transformer.{name}")
        buses = [str(bus) for bus in self.dss.CktElement.BusNames()]
        if not winding_kv:
            winding_kv = [0.0 for _ in buses]
        hv_index = max(range(len(winding_kv)), key=lambda idx: winding_kv[idx])
        lv_index = min(range(len(winding_kv)), key=lambda idx: winding_kv[idx])
        hv_bus = buses[hv_index] if hv_index < len(buses) else ""
        lv_bus = buses[lv_index] if lv_index < len(buses) else ""
        return TransformerInfo(
            name=name,
            buses=buses,
            winding_kv=winding_kv,
            hv_terminal=hv_index + 1,
            lv_terminal=lv_index + 1,
            hv_bus=hv_bus,
            lv_bus=lv_bus,
            kv_high=winding_kv[hv_index] if winding_kv else 0.0,
            kv_low=winding_kv[lv_index] if winding_kv else 0.0,
            kva=max(winding_kva) if winding_kva else 0.0,
        )

    # O que esta função faz:
    # Reúne as informações dos transformadores do circuito.
    def all_transformer_infos(self) -> dict[str, TransformerInfo]:
        result: dict[str, TransformerInfo] = {}
        for name in self.dss.Transformers.AllNames():
            if not str(name):
                continue
            try:
                info = self.transformer_info(str(name))
                result[info.name] = info
            except Exception:
                continue
        return result

    # O que esta função faz:
    # Calcula a potência ativa no lado de alta tensão e verifica reversão.
    def transformer_power(self, info: TransformerInfo, tolerance_kw: float) -> TransformerPower:
        self.dss.Circuit.SetActiveElement(f"Transformer.{info.name}")
        totals_raw = self.dss.CktElement.TotalPowers()
        totals = self._complex_values(totals_raw)
        index = info.hv_terminal - 1
        if index >= len(totals):
            # Reserva para APIs antigas que possam não devolver complexos já agrupados.
            powers_raw = self.dss.CktElement.Powers()
            powers = self._complex_values(powers_raw)
            ncond = max(1, int(self.dss.CktElement.NumConductors()))
            offset = index * ncond
            p_hv = sum(value.real for value in powers[offset: offset + ncond])
        else:
            p_hv = totals[index].real
        return TransformerPower(
            name=info.name,
            p_hv_kw=float(p_hv),
            physical_reverse=float(p_hv) < 0.0,
            reverse_violation=float(p_hv) < -abs(tolerance_kw),
        )

    # O que esta função faz:
    # Aceita somente os nós de fase 1, 2 e 3; exclui terra e neutro.
    @staticmethod
    def _is_phase_node(node_name: str) -> bool:
        """Aceita somente os nós de fase 1, 2 e 3; exclui terra e neutro."""
        match = re.search(r"\.(-?\d+)$", str(node_name).strip())
        return bool(match and int(match.group(1)) in (1, 2, 3))

    # O que esta função faz:
    # Encontra as menores e maiores tensões da solução, considerando os nós de fase.
    def voltage_extremes(
        self,
    ) -> tuple[Optional[float], Optional[str], Optional[float], Optional[str]]:
        samples: list[tuple[float, str]] = []
        try:
            node_names = [str(name) for name in self.dss.Circuit.AllNodeNames()]
            magnitudes = [float(value) for value in self.dss.Circuit.AllBusMagPu()]
            if len(node_names) == len(magnitudes):
                samples = [
                    (value, node)
                    for node, value in zip(node_names, magnitudes)
                    if self._is_phase_node(node)
                    and math.isfinite(value)
                    and value >= 0.0
                ]
        except Exception:
            samples = []

        # Reserva para versões da API que não expõem AllNodeNames ou retornam
        # listas de tamanhos diferentes.
        if not samples:
            try:
                for bus_name in self.dss.Circuit.AllBusNames():
                    self.dss.Circuit.SetActiveBus(str(bus_name))
                    nodes = [int(node) for node in self.dss.Bus.Nodes()]
                    values = [float(value) for value in self.dss.Bus.puVmagAngle()]
                    magnitudes = values[0::2]
                    for node, value in zip(nodes, magnitudes):
                        node_name = f"{bus_name}.{node}"
                        if node in (1, 2, 3) and math.isfinite(value) and value >= 0.0:
                            samples.append((value, node_name))
            except Exception:
                return None, None, None, None

        if not samples:
            return None, None, None, None
        min_value, min_node = min(samples, key=lambda item: item[0])
        max_value, max_node = max(samples, key=lambda item: item[0])
        return min_value, min_node, max_value, max_node

    # O que esta função faz:
    # Consulta o modo de simulação e o horário atual do OpenDSS.
    def solution_state(self) -> SolutionState:
        mode_names = {
            0: "Snapshot",
            1: "Daily",
            2: "Yearly",
            3: "Monte Carlo 1",
            4: "Load Duration 1",
            5: "Peak Day",
            6: "Duty Cycle",
            7: "Direct",
            8: "Monte Carlo Fault",
            9: "Fault Study",
            10: "Monte Carlo 2",
            11: "Monte Carlo 3",
            12: "Load Duration 2",
            13: "Auto Add",
            14: "Dynamic",
            15: "Harmonic",
        }
        try:
            mode_code: Optional[int] = int(self.dss.Solution.Mode())
        except Exception:
            mode_code = None
        try:
            hour: Optional[float] = float(self.dss.Solution.DblHour())
        except Exception:
            hour = None
        mode_name = mode_names.get(mode_code, f"modo {mode_code}") if mode_code is not None else "não identificado"
        return SolutionState(mode_code=mode_code, mode_name=mode_name, hour=hour)

    # O que esta função faz:
    # Cria um mapa de ligações entre barramentos para procurar caminhos dentro da rede elétrica.
    def build_connectivity_graph(self) -> dict[str, list[tuple[str, str, float]]]:
        """Cria grafo de barramentos; peso usa comprimento para linhas quando disponível."""
        graph: dict[str, list[tuple[str, str, float]]] = defaultdict(list)
        elements = [str(name) for name in self.dss.Circuit.AllElementNames()]
        for full_name in elements:
            lower = full_name.lower()
            if lower.startswith(("load.", "generator.", "pvsystem.", "capacitor.", "reactor.")):
                continue
            try:
                self.dss.Circuit.SetActiveElement(full_name)
                if not bool(self.dss.CktElement.Enabled()):
                    continue
                buses = [canonical_bus(bus) for bus in self.dss.CktElement.BusNames()]
                buses = [bus for bus in buses if bus]
                if len(buses) < 2:
                    continue
                weight = 1.0
                if lower.startswith("line."):
                    try:
                        line_name = full_name.split(".", 1)[1]
                        self.dss.Lines.Name(line_name)
                        length = float(self.dss.Lines.Length())
                        if math.isfinite(length) and length > 0:
                            weight = length
                    except Exception:
                        pass
                for left_index in range(len(buses)):
                    for right_index in range(left_index + 1, len(buses)):
                        left, right = buses[left_index], buses[right_index]
                        graph[left].append((right, full_name, weight))
                        graph[right].append((left, full_name, weight))
            except Exception:
                continue
        return graph

    # O que esta função faz:
    # Percorre a rede a partir de um barramento e devolve o primeiro transformador encontrado.
    @staticmethod
    def find_first_transformer_from_bus(
        graph: dict[str, list[tuple[str, str, float]]],
        start_bus: str,
    ) -> Optional[str]:
        start = canonical_bus(start_bus)
        if not start:
            return None
        visited = {start}
        search_queue: deque[str] = deque([start])
        while search_queue:
            bus = search_queue.popleft()
            for neighbor, element, _weight in graph.get(bus, []):
                if element.lower().startswith("transformer."):
                    return element.split(".", 1)[1]
                if neighbor not in visited:
                    visited.add(neighbor)
                    search_queue.append(neighbor)
        return None

    # O que esta função faz:
    # Procura o menor custo de caminho entre dois barramentos no grafo da rede.
    @staticmethod
    def shortest_path_distance(
        graph: dict[str, list[tuple[str, str, float]]],
        start_bus: str,
        target_bus: str,
    ) -> float:
        start = canonical_bus(start_bus)
        target = canonical_bus(target_bus)
        if not start or not target:
            return math.inf
        if start == target:
            return 0.0
        distances = {start: 0.0}
        heap: list[tuple[float, str]] = [(0.0, start)]
        while heap:
            distance, bus = heapq.heappop(heap)
            if distance != distances.get(bus):
                continue
            if bus == target:
                return distance
            for neighbor, _element, weight in graph.get(bus, []):
                candidate = distance + max(weight, 1e-9)
                if candidate < distances.get(neighbor, math.inf):
                    distances[neighbor] = candidate
                    heapq.heappush(heap, (candidate, neighbor))
        return math.inf

    # O que esta função faz:
    # Executa o fluxo de potência no modo rápido ou ao longo das 24 horas.
    def solve_steps(
        self,
        temporal_mode: str,
        transformer_infos: dict[str, TransformerInfo],
        reverse_tolerance_kw: float,
        cancel_event: threading.Event,
    ) -> list[TimeStepResult]:
        steps: list[TimeStepResult] = []

        daily_mode = temporal_mode == "24 horas — modo daily"
        if daily_mode:
            self.command("Set mode=daily number=1 stepsize=1h hour=0 sec=0")
            step_count = 24
        else:
            step_count = 1

        for step_index in range(step_count):
            ensure_not_cancelled(cancel_event)
            if daily_mode:
                self.solve()
            else:
                # SolveSnap recalcula a solução no estado temporal corrente e
                # executa as ações de controle, mas não percorre o Number
                # herdado do Master. Assim, por exemplo, hora=24 permanece 24
                # em vez de avançar mais 24 passos e terminar em hora=48.
                self.solve_snapshot_current_time()
            converged = self.converged()
            min_v, min_node, max_v, max_node = self.voltage_extremes()
            transformer_powers: dict[str, TransformerPower] = {}
            for name, info in transformer_infos.items():
                try:
                    transformer_powers[name] = self.transformer_power(
                        info, reverse_tolerance_kw
                    )
                except Exception:
                    continue
            try:
                hour_value = float(self.dss.Solution.DblHour())
            except Exception:
                hour_value = float(step_index)
            steps.append(
                TimeStepResult(
                    step_index=step_index,
                    hour=hour_value,
                    converged=converged,
                    min_voltage_pu=min_v,
                    min_voltage_node=min_node,
                    max_voltage_pu=max_v,
                    max_voltage_node=max_node,
                    transformers=transformer_powers,
                )
            )
        return steps


# =============================================================================
# Análise elétrica e comparação
# =============================================================================

# O que esta função faz:
# Muda o nome do barramento sem trocar os nós da carga. Isso evita alterar a tensão da conexão por engano.
def merge_bus_with_original_nodes(candidate_bus: str, original_bus: str) -> str:
    """Troca somente o nome-base e preserva os nós originais da conexão.

    ``TransformerInfo.lv_bus`` representa apenas um dos enrolamentos de baixa
    tensão. Em secundários com derivação central ele pode ser, por exemplo,
    ``BT_DESTINO.1.4``, embora uma carga de 254 V esteja ligada entre os nós 1 e
    2 e traga ``bus1=...1.2.4``. Reutilizar o sufixo do enrolamento reduziria a
    carga para 127 V. Por isso, quando a carga possui nós explícitos, somente o
    nome-base do barramento candidato é aproveitado.
    """
    candidate = str(candidate_bus).strip()
    suffix = bus_nodes_suffix(original_bus)
    if not suffix:
        return candidate
    candidate_base = candidate.split(".", 1)[0]
    return candidate_base + suffix


# O que esta função faz:
# Retorna os nós explícitos de um barramento na ordem declarada.
def bus_node_tokens(bus: str) -> tuple[str, ...]:
    """Retorna os nós explícitos de um barramento na ordem declarada."""
    suffix = bus_nodes_suffix(bus)
    if not suffix:
        return ()
    return tuple(token for token in suffix[1:].split(".") if token)


# O que esta função faz:
# Retorna os nós eletricamente usados pelo Load, na ordem do bus1.
def load_connection_nodes(connection: LoadConnection) -> tuple[str, ...]:
    """Retorna os nós eletricamente usados pelo Load, na ordem do bus1."""
    nodes = bus_node_tokens(connection.bus1)
    if not nodes:
        return ()
    if connection.connection.casefold() == "wye":
        conductor_count = connection.phases + 1
    else:
        # Uma carga Delta monofásica usa dois terminais; em três fases, três.
        conductor_count = max(2, connection.phases)
    return nodes[:conductor_count]


# O que esta função faz:
# Lista nós e tensão dos enrolamentos no mesmo secundário de ``lv_bus``.
def transformer_secondary_windings(
    transformer: TransformerInfo,
) -> list[tuple[tuple[str, ...], float]]:
    """Lista nós e tensão dos enrolamentos no mesmo secundário de ``lv_bus``."""
    lv_base = canonical_bus(transformer.lv_bus)
    result: list[tuple[tuple[str, ...], float]] = []
    for index, bus in enumerate(transformer.buses):
        if index == transformer.hv_terminal - 1:
            continue
        if lv_base and canonical_bus(bus) != lv_base:
            continue
        kv = transformer.winding_kv[index] if index < len(transformer.winding_kv) else 0.0
        result.append((bus_node_tokens(bus), float(kv)))
    return result


# O que esta função faz:
# Calcula tensões nominais que o secundário oferece à conexão da carga.
def transformer_connection_nominal_kvs(
    transformer: TransformerInfo,
    connection: LoadConnection,
) -> list[float]:
    """Calcula tensões nominais que o secundário oferece à conexão da carga.

    Para secundário 127/254 V com derivação central, os enrolamentos ``.1.4`` e
    ``.4.2`` são tratados como dois trechos em série. Assim, a conexão entre os
    nós 1 e 2 recebe 0,254 kV, enquanto 1-4 ou 4-2 recebe 0,127 kV.
    """
    required = load_connection_nodes(connection)
    windings = transformer_secondary_windings(transformer)
    nominal_kvs: list[float] = []

    if len(required) == 2:
        graph: dict[str, list[tuple[str, float]]] = defaultdict(list)
        for nodes, kv in windings:
            if len(nodes) == 2 and kv > 0:
                first, second = nodes
                graph[first].append((second, kv))
                graph[second].append((first, kv))

        start, destination = required
        queue_items: list[tuple[float, str]] = [(0.0, start)]
        best: dict[str, float] = {start: 0.0}
        while queue_items:
            distance, node = heapq.heappop(queue_items)
            if distance > best.get(node, math.inf):
                continue
            if node == destination:
                nominal_kvs.append(distance)
                break
            for neighbor, edge_kv in graph.get(node, []):
                candidate_distance = distance + edge_kv
                if candidate_distance < best.get(neighbor, math.inf):
                    best[neighbor] = candidate_distance
                    heapq.heappush(queue_items, (candidate_distance, neighbor))

    required_set = set(required)
    for nodes, kv in windings:
        if kv <= 0 or not nodes:
            continue
        if required_set and not required_set.issubset(nodes):
            continue
        if (
            connection.connection.casefold() == "wye"
            and connection.phases == 1
            and len(nodes) >= 3
        ):
            nominal_kvs.append(kv / math.sqrt(3.0))
        else:
            nominal_kvs.append(kv)

    # Alguns modelos e os autotestes não expõem nós nos nomes dos barramentos.
    # Nessa situação, mantém uma comparação conservadora apenas por tensão.
    if not nominal_kvs and not any(nodes for nodes, _kv in windings):
        if transformer.kv_low > 0:
            nominal_kvs.append(transformer.kv_low)
            if connection.connection.casefold() == "wye" and connection.phases == 1:
                nominal_kvs.append(transformer.kv_low / math.sqrt(3.0))

    return sorted({round(value, 12) for value in nominal_kvs if value > 0})


# O que esta função faz:
# Valida disponibilidade de nós e tensão nominal no secundário candidato.
def transformer_supports_load_connection(
    transformer: TransformerInfo,
    connection: LoadConnection,
    voltage_tolerance: float = 0.10,
) -> bool:
    """Valida disponibilidade de nós e tensão nominal no secundário candidato."""
    required = set(load_connection_nodes(connection))
    windings = transformer_secondary_windings(transformer)
    available = {node for nodes, _kv in windings for node in nodes}
    if required and available and not required.issubset(available):
        return False

    if connection.kv <= 0:
        return True
    nominal_kvs = transformer_connection_nominal_kvs(transformer, connection)
    if not nominal_kvs:
        return False
    return any(
        abs(candidate_kv - connection.kv) / connection.kv <= voltage_tolerance
        for candidate_kv in nominal_kvs
    )


# O que esta função faz:
# Monta e executa um cenário elétrico. Pode incluir a GD e, quando necessário, transferir suas cargas para outro transformador.
def run_master_scenario(
    backend: OpenDSSBackend,
    master: Path,
    consumer_id: str,
    load_hint: str,
    config: AnalysisConfig,
    cancel_event: threading.Event,
    add_generator: bool,
    target_transformer: Optional[TransformerInfo] = None,
) -> tuple[ScenarioRun, list[LoadConnection], dict[str, TransformerInfo], dict[str, list[tuple[str, str, float]]]]:
    backend.compile(master)
    inherited_state = backend.solution_state()
    master_key = os.path.normcase(str(master.resolve()))
    if master_key not in backend._masters_with_reported_states:
        hour_text = (
            f"{inherited_state.hour:g}"
            if inherited_state.hour is not None
            else "não identificada"
        )
        backend.log(
            f"{master.name}: estado definido pelo Master antes da solução — "
            f"mode={inherited_state.mode_name} ({inherited_state.mode_code}), "
            f"hora={hour_text}."
        )
        backend._masters_with_reported_states.add(master_key)

    load_names = backend.resolve_load_names(consumer_id, load_hint)
    connections = backend.get_load_connections(load_names)
    regular_connections = [
        item for item in connections
        if not is_nontechnical_load_name(item.load_name)
    ]
    nontechnical_connections = [
        item for item in connections
        if is_nontechnical_load_name(item.load_name)
    ]
    if not regular_connections:
        raise LookupError(
            f"A UC {consumer_id} não possui carga regular no circuito compilado; "
            "a conexão da GD não pode ser determinada por uma carga _NT_."
        )
    connection = regular_connections[0]
    backend.log(
        f"{master.name}: UC representada por {len(regular_connections)} carga(s) "
        f"regular(es) e {len(nontechnical_connections)} carga(s) NT correspondente(s). "
        f"Objetos: {human_join([item.load_name for item in connections])}."
    )
    transformer_infos = backend.all_transformer_infos()
    graph = backend.build_connectivity_graph()

    target_bus: Optional[str] = None
    if target_transformer is not None:
        target_bus = merge_bus_with_original_nodes(target_transformer.lv_bus, connection.bus1)
        for item in connections:
            item_target_bus = merge_bus_with_original_nodes(
                target_transformer.lv_bus, item.bus1
            )
            backend.edit_load_bus(item.load_name, item_target_bus)
        backend.log(
            f"{master.name}: transferência aplicada a {len(regular_connections)} "
            f"carga(s) regular(es), {len(nontechnical_connections)} carga(s) NT "
            "correspondente(s)"
            + (" e ao Generator." if add_generator else ".")
        )

    if add_generator:
        generator_bus = target_bus or connection.bus1
        generator_name = f"VGD_{safe_object_suffix(consumer_id)}"
        backend.add_generator(
            generator_name=generator_name,
            connection=connection,
            bus1=generator_bus,
            kw=config.generator_kw,
            pf=config.generator_pf,
            model=config.generator_model,
            profile=config.generator_profile,
        )
    else:
        generator_bus = None

    steps = backend.solve_steps(
        temporal_mode=config.temporal_mode,
        transformer_infos=transformer_infos,
        reverse_tolerance_kw=config.reverse_tolerance_kw,
        cancel_event=cancel_event,
    )

    warnings: list[str] = []
    if any(not step.converged for step in steps):
        warnings.append("Pelo menos um passo de solução não convergiu.")
    if config.temporal_mode == "Estado atual do Master — rápido" and steps:
        solved_state = backend.solution_state()
        solved_hour = steps[0].hour
        backend.log(
            f"{master.name}: ponto efetivamente analisado no modo rápido — "
            f"mode={solved_state.mode_name} ({solved_state.mode_code}), "
            f"hora={solved_hour:g}."
        )

    resulting_buses = {
        item.load_name: (
            merge_bus_with_original_nodes(target_transformer.lv_bus, item.bus1)
            if target_transformer is not None
            else item.bus1
        )
        for item in connections
    }

    run = ScenarioRun(
        master_file=str(master),
        temporal_mode=config.temporal_mode,
        load_name=connection.load_name,
        load_names=[item.load_name for item in connections],
        load_bus=target_bus or connection.bus1,
        load_buses=resulting_buses,
        generator_bus=generator_bus,
        moved_to_transformer=target_transformer.name if target_transformer else None,
        inherited_solution_state=inherited_state,
        steps=steps,
        warnings=warnings,
    )
    return run, connections, transformer_infos, graph


# O que esta função faz:
# Encontra a menor potência ativa de cada transformador nos cenários analisados.
def aggregate_transformer_min_power(runs: Sequence[ScenarioRun]) -> dict[str, float]:
    result: dict[str, float] = {}
    for run in runs:
        for step in run.steps:
            for name, power in step.transformers.items():
                result[name] = min(result.get(name, math.inf), power.p_hv_kw)
    return {name: value for name, value in result.items() if math.isfinite(value)}


# O que esta função faz:
# Encontra as menores e maiores tensões observadas e seus respectivos nós.
def aggregate_voltage_extremes(
    runs: Sequence[ScenarioRun],
) -> tuple[Optional[float], Optional[str], Optional[float], Optional[str]]:
    mins: list[tuple[float, Optional[str]]] = []
    maxs: list[tuple[float, Optional[str]]] = []
    for run in runs:
        for step in run.steps:
            if step.min_voltage_pu is not None:
                mins.append((step.min_voltage_pu, step.min_voltage_node))
            if step.max_voltage_pu is not None:
                maxs.append((step.max_voltage_pu, step.max_voltage_node))
    min_item = min(mins, key=lambda item: item[0]) if mins else (None, None)
    max_item = max(maxs, key=lambda item: item[0]) if maxs else (None, None)
    return min_item[0], min_item[1], max_item[0], max_item[1]


# O que esta função faz:
# Obtém somente os limites mínimo e máximo de tensão dos cenários.
def aggregate_voltage_range(runs: Sequence[ScenarioRun]) -> tuple[Optional[float], Optional[float]]:
    min_v, _min_node, max_v, _max_node = aggregate_voltage_extremes(runs)
    return min_v, max_v


# O que esta função faz:
# Compara o cenário original com o cenário modificado e verifica fluxo reverso, agravamentos e tensão.
def compare_runs(
    baseline_runs: Sequence[ScenarioRun],
    modified_runs: Sequence[ScenarioRun],
    reverse_tolerance_kw: float,
    aggravation_tolerance_kw: float,
    check_voltage: bool,
    voltage_min_pu: float,
    voltage_max_pu: float,
) -> ComparisonSummary:
    baseline = aggregate_transformer_min_power(baseline_runs)
    modified = aggregate_transformer_min_power(modified_runs)
    names = sorted(set(baseline) | set(modified))
    comparisons: dict[str, TransformerComparison] = {}

    original_physical_reverse: list[str] = []
    modified_physical_reverse: list[str] = []
    new_physical_reverse: list[str] = []
    original_reverse_violations: list[str] = []
    modified_reverse_violations: list[str] = []
    new_reverse_violations: list[str] = []
    eliminated_reverse_violations: list[str] = []
    aggravated_reverse_violations: list[str] = []

    for name in names:
        original_p = baseline.get(name, math.inf)
        modified_p = modified.get(name, math.inf)
        original_physical = original_p < 0.0
        modified_physical = modified_p < 0.0
        new_physical = modified_physical and not original_physical
        original_violation = original_p < -abs(reverse_tolerance_kw)
        modified_violation = modified_p < -abs(reverse_tolerance_kw)
        new_violation = modified_violation and not original_violation
        eliminated_violation = original_violation and not modified_violation

        original_export = max(0.0, -original_p) if math.isfinite(original_p) else 0.0
        modified_export = max(0.0, -modified_p) if math.isfinite(modified_p) else 0.0
        aggravation = modified_export - original_export
        aggravated_violation = (
            original_violation
            and modified_violation
            and aggravation > aggravation_tolerance_kw
        )

        comparisons[name] = TransformerComparison(
            transformer=name,
            original_min_p_kw=original_p,
            modified_min_p_kw=modified_p,
            original_max_export_kw=original_export,
            modified_max_export_kw=modified_export,
            original_physical_reverse=original_physical,
            modified_physical_reverse=modified_physical,
            original_reverse_violation=original_violation,
            modified_reverse_violation=modified_violation,
            new_reverse_violation=new_violation,
            aggravated_reverse_violation=aggravated_violation,
            aggravation_kw=aggravation,
        )
        if original_physical:
            original_physical_reverse.append(name)
        if modified_physical:
            modified_physical_reverse.append(name)
        if new_physical:
            new_physical_reverse.append(name)
        if original_violation:
            original_reverse_violations.append(name)
        if modified_violation:
            modified_reverse_violations.append(name)
        if new_violation:
            new_reverse_violations.append(name)
        if eliminated_violation:
            eliminated_reverse_violations.append(name)
        if aggravated_violation:
            aggravated_reverse_violations.append(name)

    acceptable = not new_reverse_violations and not aggravated_reverse_violations
    if check_voltage:
        min_v, max_v = aggregate_voltage_range(modified_runs)
        if min_v is not None and min_v < voltage_min_pu:
            acceptable = False
        if max_v is not None and max_v > voltage_max_pu:
            acceptable = False

    return ComparisonSummary(
        transformers=comparisons,
        original_physical_reverse=original_physical_reverse,
        modified_physical_reverse=modified_physical_reverse,
        new_physical_reverse=new_physical_reverse,
        original_reverse_violations=original_reverse_violations,
        modified_reverse_violations=modified_reverse_violations,
        new_reverse_violations=new_reverse_violations,
        eliminated_reverse_violations=eliminated_reverse_violations,
        aggravated_reverse_violations=aggravated_reverse_violations,
        acceptable=acceptable,
    )


# O que esta função faz:
# Explica quais critérios levaram à rejeição de um cenário ou candidato.
def comparison_reason(
    comparison: ComparisonSummary,
    runs: Sequence[ScenarioRun],
    config: AnalysisConfig,
) -> str:
    reasons: list[str] = []
    if comparison.new_reverse_violations:
        reasons.append(
            "nova violação da tolerância de reversão em "
            + human_join(comparison.new_reverse_violations)
        )
    if comparison.aggravated_reverse_violations:
        reasons.append(
            "agravamento acima da tolerância em "
            + human_join(comparison.aggravated_reverse_violations)
        )
    if config.check_voltage:
        min_v, min_node, max_v, max_node = aggregate_voltage_extremes(runs)
        if min_v is not None and min_v < config.voltage_min_pu:
            reasons.append(
                f"tensão mínima {min_v:.4f} pu em {min_node or 'nó não identificado'} "
                f"abaixo de {config.voltage_min_pu:.4f} pu"
            )
        if max_v is not None and max_v > config.voltage_max_pu:
            reasons.append(
                f"tensão máxima {max_v:.4f} pu em {max_node or 'nó não identificado'} "
                f"acima de {config.voltage_max_pu:.4f} pu"
            )
    return "; ".join(reasons) if reasons else "critérios atendidos"


# =============================================================================
# Classificação dos transformadores candidatos
# =============================================================================

# O que esta função faz:
# Associa Transformer a COD_ID exato e mede centro a centro em metros.
def try_spatial_transformer_distances(
    shp_folder: Path,
    original_transformer: str,
    candidate_names: Sequence[str],
    log: Callable[[str], None],
) -> SpatialDistanceResult:
    """Associa Transformer a COD_ID exato e mede centro a centro em metros."""
    result = SpatialDistanceResult()
    untrmt = find_case_insensitive_file(shp_folder, "UNTRMT.shp")
    if untrmt is None:
        log(
            "UNTRMT.shp não encontrado; os candidatos serão classificados pelo "
            "grafo elétrico."
        )
        return result
    try:
        import geopandas as gpd  # type: ignore
    except Exception:
        log(
            "Geopandas não instalado; os candidatos serão classificados pelo "
            "grafo elétrico."
        )
        return result

    try:
        gdf = gpd.read_file(untrmt)
    except Exception as exc:
        log(f"Não foi possível abrir UNTRMT.shp: {exc}")
        return result
    if gdf.empty or "geometry" not in gdf:
        log("UNTRMT.shp está vazio ou não possui geometria utilizável.")
        return result

    columns_by_name = {
        str(column).strip().casefold(): column
        for column in gdf.columns
        if str(column).strip().casefold() != "geometry"
    }
    cod_column = columns_by_name.get("cod_id")
    if cod_column is None:
        log(
            "UNTRMT.shp não possui o campo COD_ID; os candidatos serão "
            "classificados pelo grafo elétrico."
        )
        return result

    cod_index: dict[str, list[tuple[int, str]]] = defaultdict(list)
    for row_position, raw_cod_id in enumerate(gdf[cod_column]):
        normalized_cod_id = normalize_identifier(raw_cod_id)
        if normalized_cod_id:
            cod_index[normalized_cod_id].append((row_position, str(raw_cod_id).strip()))

    original_match, original_problem = match_transformer_to_cod_id(
        original_transformer, cod_index
    )
    if original_match is None:
        log(
            f"O transformador original {original_transformer} não pôde ser associado "
            f"de forma única ao UNTRMT.COD_ID: {original_problem}. Os candidatos "
            "serão classificados pelo grafo elétrico."
        )
        return result

    matches: dict[str, CodIdMatch] = {original_transformer: original_match}
    rejected_matches: list[str] = []
    for name in candidate_names:
        match, problem = match_transformer_to_cod_id(name, cod_index)
        if match is None:
            rejected_matches.append(f"{name}: {problem}")
            continue
        if match.normalized_cod_id == original_match.normalized_cod_id:
            rejected_matches.append(
                f"{name}: mesmo COD_ID do transformador original ({match.cod_id})"
            )
            continue
        matches[name] = match

    log(
        f"Associação espacial do transformador original: {original_transformer} "
        f"↔ UNTRMT.COD_ID={original_match.cod_id} ({original_match.rule})."
    )
    matched_candidate_count = len(matches) - 1
    log(
        f"Associação espacial exata: {matched_candidate_count}/{len(candidate_names)} "
        "transformador(es) candidato(s) localizado(s) por COD_ID único."
    )
    if rejected_matches:
        sample = "; ".join(rejected_matches[:5])
        extra = len(rejected_matches) - 5
        if extra > 0:
            sample += f"; e mais {extra}"
        log("Candidatos sem associação espacial válida: " + sample + ".")
    if matched_candidate_count == 0:
        return result

    if gdf.crs is None:
        log(
            "UNTRMT.shp não possui sistema de referência (CRS); não é seguro "
            "interpretar suas coordenadas como metros. Será usado o grafo elétrico."
        )
        return result

    try:
        # Reprojeta antes de obter centroides para que a distância seja métrica.
        subset_names = list(matches)
        subset_positions = [matches[name].row_position for name in subset_names]
        subset = gdf.iloc[subset_positions].copy()
        subset["_vgd_transformer_name"] = subset_names

        unit_to_metre = 1.0
        if getattr(subset.crs, "is_geographic", False):
            metric_crs = subset.estimate_utm_crs()
            if metric_crs is not None:
                subset = subset.to_crs(metric_crs)
            else:
                log(
                    "Não foi possível estimar um CRS UTM para UNTRMT.shp; será "
                    "usado o grafo elétrico."
                )
                return result
        else:
            axis_info = list(getattr(subset.crs, "axis_info", []) or [])
            conversion_factors = [
                to_float(getattr(axis, "unit_conversion_factor", None), math.nan)
                for axis in axis_info[:2]
            ]
            conversion_factors = [
                factor for factor in conversion_factors
                if math.isfinite(factor) and factor > 0
            ]
            if not conversion_factors:
                log(
                    "O CRS projetado de UNTRMT.shp não informa a unidade linear; "
                    "será usado o grafo elétrico."
                )
                return result
            if any(
                not math.isclose(factor, conversion_factors[0], rel_tol=1e-9)
                for factor in conversion_factors[1:]
            ):
                log(
                    "Os eixos do CRS de UNTRMT.shp possuem unidades incompatíveis; "
                    "será usado o grafo elétrico."
                )
                return result
            unit_to_metre = conversion_factors[0]

        geometries: dict[str, Any] = {}
        for name, geometry in zip(subset["_vgd_transformer_name"], subset.geometry):
            if geometry is None or geometry.is_empty:
                rejected_matches.append(f"{name}: geometria vazia")
                continue
            geometries[str(name)] = geometry.centroid

        origin = geometries.get(original_transformer)
        if origin is None:
            log(
                "A feição do transformador original possui geometria vazia; será "
                "usado o grafo elétrico."
            )
            return result

        for name in candidate_names:
            match = matches.get(name)
            geometry = geometries.get(name)
            if match is None or geometry is None:
                continue
            distance_m = float(origin.distance(geometry)) * unit_to_metre
            if not math.isfinite(distance_m) or distance_m < 0:
                continue
            result.distances_m[name] = distance_m
            result.cod_ids[name] = match.cod_id
        result.original_cod_id = original_match.cod_id
        return result
    except Exception as exc:
        log(f"Falha ao calcular distâncias espaciais: {exc}")
        return SpatialDistanceResult()


# O que esta função faz:
# Filtra e ordena os transformadores candidatos, usando distâncias espaciais quando disponíveis.
def rank_candidate_transformers(
    transformer_infos: dict[str, TransformerInfo],
    original_transformer: Optional[str],
    load_connection: LoadConnection,
    graph: dict[str, list[tuple[str, str, float]]],
    shp_folder: Path,
    max_candidates: int,
    log: Callable[[str], None],
) -> list[RankedCandidate]:
    if not original_transformer or original_transformer not in transformer_infos:
        log(
            "Não foi possível identificar o transformador original no grafo; "
            "os candidatos serão ordenados por distância elétrica ao barramento da carga."
        )
        original_info = None
    else:
        original_info = transformer_infos[original_transformer]

    candidates: list[TransformerInfo] = []
    incompatible_count = 0
    for info in transformer_infos.values():
        if original_transformer and normalize_identifier(info.name) == normalize_identifier(original_transformer):
            continue
        if not info.lv_bus:
            continue
        if info.kv_high <= info.kv_low * 1.05:
            continue
        # Compara a tensão nos nós usados pela carga. Isso distingue, por
        # exemplo, 127 V fase-neutro de 254 V entre as extremidades de um
        # secundário com derivação central.
        if not transformer_supports_load_connection(info, load_connection):
            incompatible_count += 1
            continue
        candidates.append(info)

    if incompatible_count:
        log(
            f"{incompatible_count} transformador(es) candidato(s) foram excluídos "
            "por incompatibilidade de nós ou tensão com a conexão da UC."
        )

    spatial = try_spatial_transformer_distances(
        shp_folder,
        original_transformer or "",
        [candidate.name for candidate in candidates],
        log,
    ) if original_transformer else SpatialDistanceResult()

    if spatial.distances_m:
        ranked_spatial = [
            RankedCandidate(
                transformer=candidate,
                distance_value=spatial.distances_m[candidate.name],
                distance_unit="m",
                spatial_cod_id=spatial.cod_ids.get(candidate.name),
                spatial_reference_cod_id=spatial.original_cod_id,
            )
            for candidate in candidates
            if candidate.name in spatial.distances_m
        ]
        ranked_spatial.sort(
            key=lambda item: (
                item.distance_value,
                normalize_identifier(item.transformer.name),
            )
        )
        if len(ranked_spatial) < min(max_candidates, len(candidates)):
            log(
                f"Somente {len(ranked_spatial)} candidato(s) possuem distância "
                "espacial válida. Os demais não serão misturados à ordenação em "
                "metros com valores do grafo elétrico."
            )
        selected = ranked_spatial[:max_candidates]
        log("Candidatos selecionados por distância espacial centro a centro:")
        for rank, item in enumerate(selected, start=1):
            log(
                f"  {rank}. {item.transformer.name} ↔ COD_ID={item.spatial_cod_id}; "
                f"{item.distance_value:.3f} m."
            )
            if math.isclose(item.distance_value, 0.0, abs_tol=1e-9):
                log(
                    "     Observação: os COD_ID são distintos, mas os centroides "
                    "das duas feições coincidem; distância espacial igual a zero."
                )
        return selected

    log(
        "Nenhuma distância espacial completa e válida ficou disponível; todos os "
        "candidatos serão classificados somente pelo custo do grafo elétrico."
    )
    ranked_electrical: list[RankedCandidate] = []
    start_bus = original_info.lv_bus if original_info else load_connection.bus1
    for candidate in candidates:
        distance = OpenDSSBackend.shortest_path_distance(
            graph, start_bus, candidate.lv_bus
        )
        if math.isfinite(distance):
            ranked_electrical.append(
                RankedCandidate(
                    transformer=candidate,
                    distance_value=distance,
                    distance_unit="custo do grafo elétrico",
                )
            )

    ranked_electrical.sort(
        key=lambda item: (
            item.distance_value,
            normalize_identifier(item.transformer.name),
        )
    )
    selected = ranked_electrical[:max_candidates]
    if selected:
        log("Candidatos selecionados pelo método alternativo do grafo elétrico:")
        for rank, item in enumerate(selected, start=1):
            log(
                f"  {rank}. {item.transformer.name}; "
                f"custo={item.distance_value:.6g}."
            )
    return selected


# =============================================================================
# Relatórios
# =============================================================================

# O que esta função faz:
# Monta initial message com base nas informações disponíveis.
def build_initial_message(
    consumer_id: str,
    comparison: ComparisonSummary,
    generator_kw: float,
    reverse_tolerance_kw: float,
) -> str:
    # O que esta função faz:
    # Prepara list para os relatórios de saída.
    def export_list(names: Sequence[str], modified: bool) -> str:
        values: list[str] = []
        for name in names:
            item = comparison.transformers.get(name)
            if item is None:
                values.append(name)
                continue
            export_kw = (
                item.modified_max_export_kw
                if modified
                else item.original_max_export_kw
            )
            values.append(f"{name} ({export_kw:.6f} kW)")
        return human_join(values)

    if not comparison.original_physical_reverse:
        original_text = (
            "No cenário-base, antes da inclusão da nova GD, nenhum transformador "
            "apresentava fluxo reverso físico."
        )
    else:
        original_text = (
            "No cenário-base, antes da inclusão da nova GD, havia fluxo reverso "
            "físico em "
            + export_list(comparison.original_physical_reverse, modified=False)
            + "."
        )

    if comparison.new_reverse_violations:
        modified_text = (
            f" Com a GD de {generator_kw:g} kW conectada à unidade consumidora "
            f"{consumer_id} no ponto original, houve exportação acima da tolerância "
            f"de reversão de {reverse_tolerance_kw:g} kW em "
            f"{export_list(comparison.new_reverse_violations, modified=True)}; "
            "portanto, houve violação do critério."
        )
    elif comparison.aggravated_reverse_violations:
        modified_text = (
            f" Com a GD de {generator_kw:g} kW conectada à unidade consumidora "
            f"{consumer_id} no ponto original, não surgiu nova violação de reversão, "
            "mas uma violação preexistente foi agravada acima da tolerância em "
            f"{human_join(comparison.aggravated_reverse_violations)}."
        )
    elif comparison.modified_physical_reverse:
        modified_text = (
            f" Com a GD de {generator_kw:g} kW conectada à unidade consumidora "
            f"{consumer_id} no ponto original, houve fluxo reverso físico em "
            f"{export_list(comparison.modified_physical_reverse, modified=True)}, "
            f"mas nenhuma exportação ultrapassou a tolerância de "
            f"{reverse_tolerance_kw:g} kW; portanto, não houve violação do critério."
        )
    else:
        modified_text = (
            f" Com a GD de {generator_kw:g} kW conectada à unidade consumidora "
            f"{consumer_id} no ponto original, não houve fluxo reverso físico nem "
            "violação do critério."
        )
    return original_text + modified_text


# O que esta função faz:
# Monta final message com base nas informações disponíveis.
def build_final_message(
    initial_message: str,
    initial_comparison: ComparisonSummary,
    config: AnalysisConfig,
    candidate_results: Sequence[CandidateResult],
    accepted_candidate: Optional[str],
) -> str:
    if accepted_candidate:
        accepted = next(
            item for item in candidate_results
            if item.transformer == accepted_candidate
        )
        candidate_power = accepted.comparison.transformers.get(accepted_candidate)
        if candidate_power is None:
            electrical_result = "O candidato atendeu aos critérios configurados."
        elif candidate_power.modified_physical_reverse:
            electrical_result = (
                f"O candidato permaneceu exportando "
                f"{candidate_power.modified_max_export_kw:.6f} kW, valor que não "
                f"ultrapassou a tolerância de {config.reverse_tolerance_kw:g} kW, "
                "e foi aceito."
            )
        else:
            import_kw = max(0.0, candidate_power.modified_min_p_kw)
            electrical_result = (
                f"O candidato passou a importar {import_kw:.6f} kW; o fluxo reverso "
                "físico foi eliminado e o candidato foi aceito."
            )
        return (
            initial_message
            + " A unidade consumidora e a GD foram transferidas, no modelo, "
              f"para o transformador {accepted_candidate}. {electrical_result}"
        )
    if initial_comparison.acceptable:
        return initial_message + " Não foi necessário remanejar a unidade consumidora."
    if not config.try_relocation:
        return (
            initial_message
            + " A transferência automática estava desativada; nenhum transformador "
              "candidato foi testado."
        )
    if candidate_results:
        return (
            initial_message
            + " Nenhum dos transformadores candidatos testados eliminou os problemas "
              "de acordo com os critérios configurados."
        )
    return (
        initial_message
        + " A transferência automática foi solicitada, mas nenhum transformador "
          "candidato compatível e alcançável pôde ser testado."
    )


# O que esta função faz:
# Prepara alguns tipos de dados para que possam ser salvos em JSON.
def json_default(value: Any) -> Any:
    if isinstance(value, Path):
        return str(value)
    if isinstance(value, (dt.datetime, dt.date)):
        return value.isoformat()
    if hasattr(value, "__dict__"):
        return value.__dict__
    raise TypeError(f"Tipo não serializável: {type(value)!r}")


# O que esta função faz:
# Grava os resultados da análise nos formatos de saída utilizados pelo projeto.
def write_reports(outcome: AnalysisOutcome) -> None:
    output = Path(outcome.output_directory)
    output.mkdir(parents=True, exist_ok=True)

    # JSON completo
    (output / "resultado.json").write_text(
        json.dumps(asdict(outcome), ensure_ascii=False, indent=2, default=json_default),
        encoding="utf-8",
    )

    # CSV resumido de potências por transformador
    with (output / "comparacao_transformadores.csv").open(
        "w", newline="", encoding="utf-8-sig"
    ) as handle:
        writer = csv.writer(handle, delimiter=";")
        writer.writerow([
            "transformador",
            "p_min_cenario_base_kw",
            "p_min_gd_ponto_original_kw",
            "exportacao_cenario_base_kw",
            "exportacao_gd_ponto_original_kw",
            "fluxo_reverso_fisico_cenario_base",
            "fluxo_reverso_fisico_gd_ponto_original",
            "violacao_reversao_cenario_base",
            "violacao_reversao_gd_ponto_original",
            "nova_violacao_reversao",
            "violacao_agravamento",
            "agravamento_kw",
        ])
        for item in outcome.initial_comparison.transformers.values():
            writer.writerow([
                item.transformer,
                item.original_min_p_kw,
                item.modified_min_p_kw,
                item.original_max_export_kw,
                item.modified_max_export_kw,
                item.original_physical_reverse,
                item.modified_physical_reverse,
                item.original_reverse_violation,
                item.modified_reverse_violation,
                item.new_reverse_violation,
                item.aggravated_reverse_violation,
                item.aggravation_kw,
            ])

    # CSV auditável da classificação e das tentativas de transferência.
    with (output / "candidatos_testados.csv").open(
        "w", newline="", encoding="utf-8-sig"
    ) as handle:
        writer = csv.writer(handle, delimiter=";")
        writer.writerow([
            "classificacao",
            "transformador_referencia",
            "cod_id_referencia",
            "transformador_candidato",
            "cod_id_candidato",
            "distancia",
            "unidade_ou_metodo",
            "tolerancia_reversao_kw",
            "tolerancia_agravamento_kw",
            "p_candidato_antes_kw",
            "p_candidato_depois_kw",
            "exportacao_candidato_depois_kw",
            "fluxo_reverso_fisico_candidato_depois",
            "violacao_reversao_candidato_depois",
            "p_transformador_original_apos_transferencia_kw",
            "convergiu",
            "vmin_pu",
            "vmax_pu",
            "aceito",
            "motivo",
        ])
        for candidate in outcome.candidate_results:
            candidate_power = candidate.comparison.transformers.get(
                candidate.transformer
            )
            original_after = (
                candidate.comparison.transformers.get(outcome.original_transformer)
                if outcome.original_transformer
                else None
            )
            min_v, _min_node, max_v, _max_node = aggregate_voltage_extremes(
                candidate.scenario_runs
            )
            converged = bool(candidate.scenario_runs) and all(
                step.converged
                for run in candidate.scenario_runs
                for step in run.steps
            )
            writer.writerow([
                candidate.rank,
                outcome.original_transformer or "",
                candidate.spatial_reference_cod_id or "",
                candidate.transformer,
                candidate.spatial_cod_id or "",
                candidate.distance_value,
                candidate.distance_unit,
                outcome.config.reverse_tolerance_kw,
                outcome.config.aggravation_tolerance_kw,
                candidate_power.original_min_p_kw if candidate_power else "",
                candidate_power.modified_min_p_kw if candidate_power else "",
                candidate_power.modified_max_export_kw if candidate_power else "",
                candidate_power.modified_physical_reverse if candidate_power else "",
                candidate_power.modified_reverse_violation if candidate_power else "",
                original_after.modified_min_p_kw if original_after else "",
                converged,
                min_v if min_v is not None else "",
                max_v if max_v is not None else "",
                candidate.accepted,
                candidate.reason,
            ])

    original_min_v, original_min_node, original_max_v, original_max_node = (
        aggregate_voltage_extremes(outcome.baseline_runs)
    )
    gd_min_v, gd_min_node, gd_max_v, gd_max_node = aggregate_voltage_extremes(
        outcome.original_gd_runs
    )

    # O que esta função faz:
    # Formata o valor e o nó de uma tensão para o relatório.
    def voltage_text(value: Optional[float], node: Optional[str]) -> str:
        if value is None:
            return "não disponível"
        return f"{value:.6f} pu em {node or 'nó não identificado'}"

    # O que esta função faz:
    # Prepara text para os relatórios de saída.
    def export_text(
        names: Sequence[str],
        comparison: ComparisonSummary,
        modified: bool,
    ) -> str:
        values: list[str] = []
        for name in names:
            item = comparison.transformers.get(name)
            if item is None:
                values.append(name)
                continue
            export_kw = (
                item.modified_max_export_kw
                if modified
                else item.original_max_export_kw
            )
            values.append(f"{name} ({export_kw:.6f} kW)")
        return human_join(values)

    regular_loads = [
        item.load_name for item in outcome.load_connections
        if not is_nontechnical_load_name(item.load_name)
    ]
    nontechnical_loads = [
        item.load_name for item in outcome.load_connections
        if is_nontechnical_load_name(item.load_name)
    ]

    # Relatório textual
    lines = [
        f"{APP_NAME} {APP_VERSION}",
        "=" * 72,
        "",
        outcome.final_message,
        "",
        f"Unidade consumidora: {outcome.config.consumer_id}",
        f"Loads regulares OpenDSS ({len(regular_loads)}): {human_join(regular_loads)}",
        f"Loads NT correspondentes ({len(nontechnical_loads)}): "
        f"{human_join(nontechnical_loads)}",
        f"Barramento original: {outcome.load_connection.bus1}",
        f"Transformador original identificado: {outcome.original_transformer or 'não identificado'}",
        f"Potência do Generator: {outcome.config.generator_kw:g} kW",
        f"Fator de potência: {outcome.config.generator_pf:g}",
        f"Perfil: {outcome.config.generator_profile}",
        f"Masters analisados: {len(outcome.master_files)}",
        f"Modo temporal solicitado: {outcome.config.temporal_mode}",
        f"Tolerância de reversão: {outcome.config.reverse_tolerance_kw:g} kW",
        f"Tolerância de agravamento: {outcome.config.aggravation_tolerance_kw:g} kW",
        f"Máximo de candidatos: {outcome.config.max_candidates}",
        "Critério de tensão habilitado: "
        + ("sim" if outcome.config.check_voltage else "não"),
        "Fluxo reverso físico no cenário-base: "
        + export_text(
            outcome.initial_comparison.original_physical_reverse,
            outcome.initial_comparison,
            modified=False,
        ),
        "Violações da tolerância de reversão no cenário-base: "
        + human_join(outcome.initial_comparison.original_reverse_violations),
        "Fluxo reverso físico com a GD no ponto original: "
        + export_text(
            outcome.initial_comparison.modified_physical_reverse,
            outcome.initial_comparison,
            modified=True,
        ),
        "Novas violações da tolerância de reversão: "
        + human_join(outcome.initial_comparison.new_reverse_violations),
        "Violações de agravamento: "
        + human_join(outcome.initial_comparison.aggravated_reverse_violations),
        "",
        "Extremos de tensão (somente nós de fase 1, 2 e 3):",
        f"- Cenário-base sem a nova GD — mínimo: {voltage_text(original_min_v, original_min_node)}; "
        f"máximo: {voltage_text(original_max_v, original_max_node)}.",
        f"- GD no ponto original — mínimo: {voltage_text(gd_min_v, gd_min_node)}; "
        f"máximo: {voltage_text(gd_max_v, gd_max_node)}.",
        "",
        "Estado temporal por Master:",
    ]
    for run in outcome.baseline_runs:
        inherited = run.inherited_solution_state
        inherited_hour = (
            f"{inherited.hour:g}" if inherited.hour is not None else "não identificada"
        )
        solved_hours = human_join([f"{step.hour:g}" for step in run.steps])
        lines.append(
            f"- {Path(run.master_file).name}: antes da solução, "
            f"mode={inherited.mode_name} ({inherited.mode_code}), hora={inherited_hour}; "
            f"hora(s) efetivamente resolvida(s): {solved_hours}."
        )
    lines.extend([
        "",
        "Tentativas de transferência:",
    ])
    if outcome.candidate_results:
        for candidate in outcome.candidate_results:
            if candidate.spatial_cod_id and candidate.spatial_reference_cod_id:
                cod_id_text = (
                    f"; COD_ID de referência={candidate.spatial_reference_cod_id}"
                    f"; COD_ID candidato={candidate.spatial_cod_id}"
                )
            else:
                cod_id_text = ""
            candidate_power = candidate.comparison.transformers.get(
                candidate.transformer
            )
            original_after = (
                candidate.comparison.transformers.get(outcome.original_transformer)
                if outcome.original_transformer
                else None
            )
            min_v, _min_node, max_v, _max_node = aggregate_voltage_extremes(
                candidate.scenario_runs
            )
            converged = bool(candidate.scenario_runs) and all(
                step.converged
                for run in candidate.scenario_runs
                for step in run.steps
            )
            lines.append(
                f"- {candidate.transformer}: {'ACEITO' if candidate.accepted else 'rejeitado'}; "
                f"distância={candidate.distance_value:.3f} {candidate.distance_unit}"
                f"{cod_id_text}; {candidate.reason}."
            )
            if candidate_power is not None:
                lines.append(
                    f"  Potência no candidato: antes={candidate_power.original_min_p_kw:.6f} kW; "
                    f"depois={candidate_power.modified_min_p_kw:.6f} kW; "
                    f"exportação depois={candidate_power.modified_max_export_kw:.6f} kW; "
                    "fluxo reverso físico="
                    + ("sim" if candidate_power.modified_physical_reverse else "não")
                    + "; violação da tolerância="
                    + ("sim" if candidate_power.modified_reverse_violation else "não")
                    + "."
                )
            if original_after is not None:
                lines.append(
                    "  Potência no transformador original após a transferência: "
                    f"{original_after.modified_min_p_kw:.6f} kW."
                )
            voltage_summary = (
                f"Vmín={min_v:.6f} pu" if min_v is not None else "Vmín não disponível"
            )
            voltage_summary += "; " + (
                f"Vmáx={max_v:.6f} pu" if max_v is not None else "Vmáx não disponível"
            )
            lines.append(
                f"  Convergência={'sim' if converged else 'não'}; {voltage_summary}."
            )
    elif not outcome.config.try_relocation:
        lines.append("- A transferência automática estava desativada; nenhum candidato foi testado.")
    elif outcome.initial_comparison.acceptable:
        lines.append("- A transferência não foi necessária, pois o cenário inicial atendeu aos critérios.")
    else:
        lines.append("- Não houve tentativa de transferência.")

    if outcome.warnings:
        lines.extend(["", "Avisos:"])
        lines.extend(f"- {warning}" for warning in outcome.warnings)

    (output / "relatorio.txt").write_text("\n".join(lines), encoding="utf-8")

    # Script DSS aplicável ao cenário escolhido.
    generator_name = f"VGD_{safe_object_suffix(outcome.config.consumer_id)}"
    if outcome.accepted_candidate:
        accepted = next(
            item for item in outcome.candidate_results
            if item.transformer == outcome.accepted_candidate
        )
        final_bus = accepted.lv_bus
        accepted_load_buses = (
            accepted.scenario_runs[0].load_buses
            if accepted.scenario_runs
            else {}
        )
        edit_lines = [
            f"Edit Load.{item.load_name} "
            f"bus1={quote_dss(accepted_load_buses.get(item.load_name, final_bus))}"
            for item in outcome.load_connections
        ]
    else:
        final_bus = outcome.load_connection.bus1
        edit_lines = ["! As cargas da UC permaneceram no barramento original."]

    daily_lines: list[str] = []
    daily_clause = ""
    if outcome.config.generator_profile == "Curva solar padrão de 24 horas":
        shape_name = f"VGD_SOLAR_{safe_object_suffix(generator_name, 18)}"
        multipliers = " ".join(f"{value:.6f}" for value in DEFAULT_SOLAR_PROFILE)
        daily_lines.append(
            f"New LoadShape.{shape_name} npts=24 interval=1 mult=({multipliers})"
        )
        daily_clause = f" daily={shape_name} status=variable"

    generator_line = (
        f"New Generator.{generator_name} "
        f"phases={outcome.load_connection.phases} "
        f"bus1={quote_dss(final_bus)} "
        f"conn={outcome.load_connection.connection} "
        f"kV={outcome.load_connection.kv:.12g} "
        f"kW={outcome.config.generator_kw:.12g} "
        f"PF={outcome.config.generator_pf:.12g} "
        f"model={outcome.config.generator_model}"
        f"{daily_clause}"
    )
    dss_lines = [
        "! Modificações geradas pelo ViabilizaGD",
        "! Redirecione este arquivo depois de compilar o Master original.",
        "",
        *edit_lines,
        *daily_lines,
        generator_line,
        "Solve",
    ]
    (output / "ViabilizaGD_modificacoes.dss").write_text(
        "\n".join(dss_lines), encoding="utf-8"
    )


# O que esta função faz:
# Cria uma pasta própria para guardar os resultados de uma análise.
def create_output_directory(config: AnalysisConfig) -> Path:
    timestamp = dt.datetime.now().strftime("%Y%m%d-%H%M%S")
    suffix = safe_object_suffix(config.consumer_id, 16)
    folder = Path(config.output_path) / f"{timestamp}_{suffix}_{config.generator_kw:g}kW"
    folder.mkdir(parents=True, exist_ok=False)
    return folder


# =============================================================================
# Orquestração principal
# =============================================================================

# O que esta função faz:
# Organiza o trabalho completo: encontra a UC, executa cenários, testa transformadores e salva os resultados.
def execute_analysis(
    config: AnalysisConfig,
    log: Callable[[str], None],
    progress: Callable[[float], None],
    cancel_event: threading.Event,
) -> AnalysisOutcome:
    warnings = validate_input_paths(config)
    for warning in warnings:
        log("Aviso: " + warning)
    progress(0.03)

    dss_folder = Path(config.dss_path)
    preliminary_ref: Optional[ConsumerReference] = None
    if config.master_scope == "Selecionar um Master":
        masters = discover_master_files(
            dss_folder, "", config.master_scope, config.selected_master
        )
    else:
        preliminary_ref = find_consumer_reference(
            dss_folder, config.consumer_id, log, cancel_event
        )
        masters = discover_master_files(
            dss_folder,
            preliminary_ref.feeder_hint,
            config.master_scope,
            config.selected_master,
        )

    log(f"{len(masters)} arquivo(s) Master será(ão) analisado(s).")
    dependency_files = collect_master_dependency_files(masters, log)
    log(
        f"Pesquisa da UC limitada a {len(dependency_files)} arquivo(s) DSS "
        "alcançado(s) pelo(s) Master(s) selecionado(s)."
    )
    try:
        consumer_ref = find_consumer_reference(
            dss_folder,
            config.consumer_id,
            log,
            cancel_event,
            files=dependency_files,
        )
    except LookupError:
        warning = (
            "Não foi possível localizar textualmente a UC apenas nos Redirects/Compiles "
            "rastreáveis do Master; foi usada a pesquisa geral como reserva. A associação "
            "final continuará limitada aos Loads existentes no circuito compilado."
        )
        warnings.append(warning)
        log("Aviso: " + warning)
        consumer_ref = preliminary_ref or find_consumer_reference(
            dss_folder, config.consumer_id, log, cancel_event
        )
    progress(0.08)

    backend = OpenDSSBackend(log)
    baseline_runs: list[ScenarioRun] = []
    gd_runs: list[ScenarioRun] = []
    first_connection: Optional[LoadConnection] = None
    first_connections: list[LoadConnection] = []
    first_transformers: dict[str, TransformerInfo] = {}
    first_graph: dict[str, list[tuple[str, str, float]]] = {}

    total_initial_runs = max(1, len(masters) * 2)
    completed_runs = 0

    log("Executando o cenário-base, sem a nova GD...")
    for master in masters:
        ensure_not_cancelled(cancel_event)
        log(f"Cenário-base sem a nova GD: {master.name}")
        run, connections, transformer_infos, graph = run_master_scenario(
            backend=backend,
            master=master,
            consumer_id=config.consumer_id,
            load_hint=consumer_ref.load_name_hint,
            config=config,
            cancel_event=cancel_event,
            add_generator=False,
        )
        baseline_runs.append(run)
        if first_connection is None:
            first_connections = connections
            first_connection = connections[0]
            first_transformers = transformer_infos
            first_graph = graph
        completed_runs += 1
        progress(0.08 + 0.32 * completed_runs / total_initial_runs)

    if first_connection is None:
        raise RuntimeError("Não foi possível obter os dados elétricos da unidade consumidora.")

    original_transformer = backend.find_first_transformer_from_bus(
        first_graph, first_connection.bus1
    )
    log(
        "Transformador que atende originalmente a UC: "
        + (original_transformer or "não identificado")
    )

    log("Executando a GD no ponto de conexão original da UC...")
    for master in masters:
        ensure_not_cancelled(cancel_event)
        log(f"GD no ponto original: {master.name}")
        run, _connections, _transformers, _graph = run_master_scenario(
            backend=backend,
            master=master,
            consumer_id=config.consumer_id,
            load_hint=consumer_ref.load_name_hint,
            config=config,
            cancel_event=cancel_event,
            add_generator=True,
        )
        gd_runs.append(run)
        completed_runs += 1
        progress(0.08 + 0.32 * completed_runs / total_initial_runs)

    initial_comparison = compare_runs(
        baseline_runs=baseline_runs,
        modified_runs=gd_runs,
        reverse_tolerance_kw=config.reverse_tolerance_kw,
        aggravation_tolerance_kw=config.aggravation_tolerance_kw,
        check_voltage=config.check_voltage,
        voltage_min_pu=config.voltage_min_pu,
        voltage_max_pu=config.voltage_max_pu,
    )
    initial_message = build_initial_message(
        config.consumer_id,
        initial_comparison,
        config.generator_kw,
        config.reverse_tolerance_kw,
    )
    log(initial_message)
    progress(0.42)

    candidate_results: list[CandidateResult] = []
    accepted_candidate: Optional[str] = None

    should_try = config.try_relocation and not initial_comparison.acceptable
    if should_try:
        ranked_candidates = rank_candidate_transformers(
            transformer_infos=first_transformers,
            original_transformer=original_transformer,
            load_connection=first_connection,
            graph=first_graph,
            shp_folder=Path(config.shp_path),
            max_candidates=config.max_candidates,
            log=log,
        )
        if not ranked_candidates:
            warnings.append(
                "Nenhum transformador candidato compatível e alcançável foi encontrado."
            )
            log(warnings[-1])

        total_candidate_runs = max(1, len(ranked_candidates) * len(masters))
        completed_candidate_runs = 0
        for rank, ranked_candidate in enumerate(ranked_candidates, start=1):
            ensure_not_cancelled(cancel_event)
            candidate = ranked_candidate.transformer
            distance = ranked_candidate.distance_value
            unit = ranked_candidate.distance_unit
            cod_id_text = (
                f", UNTRMT.COD_ID={ranked_candidate.spatial_cod_id}"
                if ranked_candidate.spatial_cod_id
                else ""
            )
            log(
                f"Testando candidato {rank}/{len(ranked_candidates)}: "
                f"{candidate.name}{cod_id_text}, distância {distance:.3f} {unit}."
            )
            candidate_runs: list[ScenarioRun] = []
            for master in masters:
                ensure_not_cancelled(cancel_event)
                run, _connections, _transformers, _graph = run_master_scenario(
                    backend=backend,
                    master=master,
                    consumer_id=config.consumer_id,
                    load_hint=consumer_ref.load_name_hint,
                    config=config,
                    cancel_event=cancel_event,
                    add_generator=True,
                    target_transformer=candidate,
                )
                candidate_runs.append(run)
                completed_candidate_runs += 1
                progress(
                    0.42 + 0.53 * completed_candidate_runs / total_candidate_runs
                )

            comparison = compare_runs(
                baseline_runs=baseline_runs,
                modified_runs=candidate_runs,
                reverse_tolerance_kw=config.reverse_tolerance_kw,
                aggravation_tolerance_kw=config.aggravation_tolerance_kw,
                check_voltage=config.check_voltage,
                voltage_min_pu=config.voltage_min_pu,
                voltage_max_pu=config.voltage_max_pu,
            )
            reason = comparison_reason(comparison, candidate_runs, config)
            accepted = comparison.acceptable
            candidate_bus = merge_bus_with_original_nodes(
                candidate.lv_bus, first_connection.bus1
            )
            candidate_results.append(
                CandidateResult(
                    transformer=candidate.name,
                    lv_bus=candidate_bus,
                    rank=rank,
                    distance_value=distance,
                    distance_unit=unit,
                    accepted=accepted,
                    comparison=comparison,
                    scenario_runs=candidate_runs,
                    reason=reason,
                    spatial_cod_id=ranked_candidate.spatial_cod_id,
                    spatial_reference_cod_id=(
                        ranked_candidate.spatial_reference_cod_id
                    ),
                )
            )
            log(
                f"Candidato {candidate.name}: "
                f"{'ACEITO' if accepted else 'rejeitado'} — {reason}."
            )
            if accepted:
                accepted_candidate = candidate.name
                break
    elif config.try_relocation:
        log("A transferência não foi necessária: o cenário inicial atendeu aos critérios.")
    else:
        log("A tentativa automática de transferência está desativada.")

    output_dir = create_output_directory(config)
    final_message = build_final_message(
        initial_message=initial_message,
        initial_comparison=initial_comparison,
        config=config,
        candidate_results=candidate_results,
        accepted_candidate=accepted_candidate,
    )

    outcome = AnalysisOutcome(
        app_name=APP_NAME,
        app_version=APP_VERSION,
        config=config,
        consumer_reference=consumer_ref,
        load_connection=first_connection,
        load_connections=first_connections,
        master_files=[str(master) for master in masters],
        baseline_runs=baseline_runs,
        original_gd_runs=gd_runs,
        initial_comparison=initial_comparison,
        original_transformer=original_transformer,
        candidate_results=candidate_results,
        accepted_candidate=accepted_candidate,
        output_directory=str(output_dir),
        final_message=final_message,
        warnings=warnings,
    )
    write_reports(outcome)
    progress(1.0)
    log(f"Resultados salvos em: {output_dir}")
    return outcome


# =============================================================================
# Interface Tkinter
# =============================================================================

class ViabilizaGDApp(tk.Tk):
    # O que esta função faz:
    # Prepara as informações e os recursos necessários para utilizar esta parte do programa.
    def __init__(self) -> None:
        super().__init__()
        self.title(f"{APP_NAME} {APP_VERSION}")
        self.geometry("1120x820")
        self.minsize(940, 700)
        self.protocol("WM_DELETE_WINDOW", self.on_close)

        self.ui_queue: queue.Queue[tuple[str, Any]] = queue.Queue()
        self.cancel_event = threading.Event()
        self.worker: Optional[threading.Thread] = None

        self.var_gdb = tk.StringVar()
        self.var_shp = tk.StringVar()
        self.var_dss = tk.StringVar()
        self.var_output = tk.StringVar()
        self.var_consumer = tk.StringVar(value="")
        self.var_kw = tk.StringVar(value="10,0")
        self.var_pf = tk.StringVar(value="1,0")
        self.var_model = tk.StringVar(value="1")
        self.var_profile = tk.StringVar(value="Curva solar padrão de 24 horas")
        self.var_master_scope = tk.StringVar(value="Analisar todos os Masters")
        self.var_selected_master = tk.StringVar()
        self.var_temporal_mode = tk.StringVar(value="24 horas — modo daily")
        self.var_reverse_tolerance = tk.StringVar(value="0,1")
        self.var_aggravation_tolerance = tk.StringVar(value="0,1")
        self.var_max_candidates = tk.StringVar(value="20")
        self.var_try_relocation = tk.BooleanVar(value=True)
        self.var_check_voltage = tk.BooleanVar(value=True)
        self.var_vmin = tk.StringVar(value="0,90")
        self.var_vmax = tk.StringVar(value="1,05")
        self.var_status = tk.StringVar(value="Pronto.")

        self._configure_style()
        self._build_ui()
        self.after(100, self._process_ui_queue)

    # O que esta função faz:
    # Define o tema, as fontes e a aparência dos componentes da interface.
    def _configure_style(self) -> None:
        style = ttk.Style(self)
        try:
            style.theme_use("vista")
        except tk.TclError:
            try:
                style.theme_use("clam")
            except tk.TclError:
                pass
        style.configure("Title.TLabel", font=("Segoe UI", 20, "bold"))
        style.configure("Subtitle.TLabel", font=("Segoe UI", 10))
        style.configure("Section.TLabelframe.Label", font=("Segoe UI", 11, "bold"))
        style.configure("Primary.TButton", font=("Segoe UI", 10, "bold"), padding=8)

    # O que esta função faz:
    # Desenha as abas e os controles da interface do ViabilizaGD.
    def _build_ui(self) -> None:
        outer = ttk.Frame(self, padding=14)
        outer.pack(fill="both", expand=True)

        header = ttk.Frame(outer)
        header.pack(fill="x", pady=(0, 10))
        ttk.Label(header, text=APP_NAME, style="Title.TLabel").pack(anchor="w")
        ttk.Label(
            header,
            text=(
                "Análise de fluxo reverso e busca de alternativa de conexão para geração distribuída"
            ),
            style="Subtitle.TLabel",
        ).pack(anchor="w")

        notebook = ttk.Notebook(outer)
        notebook.pack(fill="both", expand=True)

        input_tab = ttk.Frame(notebook, padding=10)
        result_tab = ttk.Frame(notebook, padding=10)
        notebook.add(input_tab, text="Dados e análise")
        notebook.add(result_tab, text="Execução e resultados")

        self._build_input_tab(input_tab)
        self._build_result_tab(result_tab)

    # O que esta função faz:
    # Cria os campos usados para definir os dados e as opções de simulação.
    def _build_input_tab(self, parent: ttk.Frame) -> None:
        parent.columnconfigure(0, weight=1)

        paths = ttk.LabelFrame(
            parent, text="1–3. Arquivos de entrada", style="Section.TLabelframe"
        )
        paths.grid(row=0, column=0, sticky="ew", pady=(0, 10))
        paths.columnconfigure(1, weight=1)

        self._path_row(paths, 0, "File Geodatabase (.gdb):", self.var_gdb, self.select_gdb)
        self._path_row(paths, 1, "Pasta dos shapefiles:", self.var_shp, self.select_shp)
        self._path_row(paths, 2, "Pasta dos arquivos .dss:", self.var_dss, self.select_dss)
        self._path_row(paths, 3, "Pasta-base de resultados:", self.var_output, self.select_output)

        generator = ttk.LabelFrame(
            parent, text="4. Unidade consumidora e Generator", style="Section.TLabelframe"
        )
        generator.grid(row=1, column=0, sticky="ew", pady=(0, 10))
        for column in (1, 3, 5):
            generator.columnconfigure(column, weight=1)

        ttk.Label(generator, text="Consumidor:").grid(row=0, column=0, sticky="w", padx=8, pady=7)
        ttk.Entry(generator, textvariable=self.var_consumer).grid(
            row=0, column=1, columnspan=5, sticky="ew", padx=8, pady=7
        )

        ttk.Label(generator, text="Potência ativa:").grid(row=1, column=0, sticky="w", padx=8, pady=7)
        ttk.Entry(generator, textvariable=self.var_kw, width=12).grid(
            row=1, column=1, sticky="ew", padx=8, pady=7
        )
        ttk.Label(generator, text="kW AC").grid(row=1, column=2, sticky="w")

        ttk.Label(generator, text="Fator de potência:").grid(row=1, column=3, sticky="w", padx=8, pady=7)
        ttk.Entry(generator, textvariable=self.var_pf, width=10).grid(
            row=1, column=4, sticky="ew", padx=8, pady=7
        )

        ttk.Label(generator, text="Modelo:").grid(row=1, column=5, sticky="e", padx=8, pady=7)
        ttk.Combobox(
            generator,
            textvariable=self.var_model,
            values=("1", "7"),
            width=7,
            state="readonly",
        ).grid(row=1, column=6, sticky="ew", padx=8, pady=7)

        ttk.Label(generator, text="Perfil de geração:").grid(row=2, column=0, sticky="w", padx=8, pady=7)
        ttk.Combobox(
            generator,
            textvariable=self.var_profile,
            values=("Curva solar padrão de 24 horas", "Potência constante"),
            state="readonly",
        ).grid(row=2, column=1, columnspan=3, sticky="ew", padx=8, pady=7)

        scenarios = ttk.LabelFrame(
            parent, text="5. Cenários OpenDSS", style="Section.TLabelframe"
        )
        scenarios.grid(row=2, column=0, sticky="ew", pady=(0, 10))
        scenarios.columnconfigure(1, weight=1)

        ttk.Label(scenarios, text="Escopo dos Masters:").grid(row=0, column=0, sticky="w", padx=8, pady=7)
        scope_combo = ttk.Combobox(
            scenarios,
            textvariable=self.var_master_scope,
            values=("Analisar todos os Masters", "Selecionar um Master"),
            state="readonly",
        )
        scope_combo.grid(row=0, column=1, sticky="ew", padx=8, pady=7)
        scope_combo.bind("<<ComboboxSelected>>", lambda _event: self._update_master_state())

        ttk.Label(scenarios, text="Master específico:").grid(row=1, column=0, sticky="w", padx=8, pady=7)
        self.master_entry = ttk.Entry(scenarios, textvariable=self.var_selected_master, state="disabled")
        self.master_entry.grid(row=1, column=1, sticky="ew", padx=8, pady=7)
        self.master_button = ttk.Button(
            scenarios, text="Procurar", command=self.select_master, state="disabled"
        )
        self.master_button.grid(row=1, column=2, padx=8, pady=7)

        ttk.Label(scenarios, text="Modo temporal:").grid(row=2, column=0, sticky="w", padx=8, pady=7)
        ttk.Combobox(
            scenarios,
            textvariable=self.var_temporal_mode,
            values=("24 horas — modo daily", "Estado atual do Master — rápido"),
            state="readonly",
        ).grid(row=2, column=1, sticky="ew", padx=8, pady=7)

        criteria = ttk.LabelFrame(
            parent, text="6. Critérios e busca automática", style="Section.TLabelframe"
        )
        criteria.grid(row=3, column=0, sticky="ew", pady=(0, 10))
        for column in (1, 3, 5):
            criteria.columnconfigure(column, weight=1)

        ttk.Label(criteria, text="Tolerância de reversão:").grid(row=0, column=0, sticky="w", padx=8, pady=7)
        ttk.Entry(criteria, textvariable=self.var_reverse_tolerance, width=10).grid(
            row=0, column=1, sticky="ew", padx=8, pady=7
        )
        ttk.Label(criteria, text="kW").grid(row=0, column=2, sticky="w")

        ttk.Label(criteria, text="Tolerância de agravamento:").grid(row=0, column=3, sticky="w", padx=8, pady=7)
        ttk.Entry(criteria, textvariable=self.var_aggravation_tolerance, width=10).grid(
            row=0, column=4, sticky="ew", padx=8, pady=7
        )
        ttk.Label(criteria, text="kW").grid(row=0, column=5, sticky="w")

        ttk.Label(criteria, text="Máximo de candidatos:").grid(row=1, column=0, sticky="w", padx=8, pady=7)
        ttk.Entry(criteria, textvariable=self.var_max_candidates, width=10).grid(
            row=1, column=1, sticky="ew", padx=8, pady=7
        )

        ttk.Checkbutton(
            criteria,
            text="Testar transferência automática da carga e do Generator",
            variable=self.var_try_relocation,
        ).grid(row=1, column=3, columnspan=3, sticky="w", padx=8, pady=7)

        ttk.Checkbutton(
            criteria,
            text="Também exigir faixa de tensão",
            variable=self.var_check_voltage,
        ).grid(row=2, column=0, columnspan=2, sticky="w", padx=8, pady=7)
        ttk.Label(criteria, text="Vmín:").grid(row=2, column=2, sticky="e", padx=4)
        ttk.Entry(criteria, textvariable=self.var_vmin, width=8).grid(row=2, column=3, sticky="ew", padx=4)
        ttk.Label(criteria, text="Vmáx:").grid(row=2, column=4, sticky="e", padx=4)
        ttk.Entry(criteria, textvariable=self.var_vmax, width=8).grid(row=2, column=5, sticky="ew", padx=4)

        note = ttk.Label(
            parent,
            text=(
                "Nesta versão, a transferência é elétrica e simplificada: os bus1 das cargas regulares da UC, "
                "das cargas NT de mesmo identificador e do Generator são alterados para o barramento BT do "
                "transformador candidato. A GD é sempre localizada por uma carga regular; arquivos Cargas*NT "
                "não são usados como referência. Os arquivos originais não são modificados."
            ),
            wraplength=950,
            justify="left",
        )
        note.grid(row=4, column=0, sticky="ew", pady=(0, 10))

        buttons = ttk.Frame(parent)
        buttons.grid(row=5, column=0, sticky="ew")
        self.run_button = ttk.Button(
            buttons, text="Executar análise", style="Primary.TButton", command=self.start_analysis
        )
        self.run_button.pack(side="left")
        self.cancel_button = ttk.Button(
            buttons, text="Cancelar", command=self.cancel_analysis, state="disabled"
        )
        self.cancel_button.pack(side="left", padx=8)
        ttk.Button(buttons, text="Limpar log", command=self.clear_log).pack(side="left")

    # O que esta função faz:
    # Monta a área em que aparecem o andamento e os resultados da análise.
    def _build_result_tab(self, parent: ttk.Frame) -> None:
        parent.rowconfigure(1, weight=1)
        parent.columnconfigure(0, weight=1)

        top = ttk.Frame(parent)
        top.grid(row=0, column=0, sticky="ew", pady=(0, 8))
        top.columnconfigure(0, weight=1)
        self.progress = ttk.Progressbar(top, mode="determinate", maximum=100)
        self.progress.grid(row=0, column=0, sticky="ew")
        ttk.Label(top, textvariable=self.var_status).grid(row=1, column=0, sticky="w", pady=(4, 0))

        text_frame = ttk.Frame(parent)
        text_frame.grid(row=1, column=0, sticky="nsew")
        text_frame.rowconfigure(0, weight=1)
        text_frame.columnconfigure(0, weight=1)
        self.log_text = tk.Text(
            text_frame,
            wrap="word",
            font=("Consolas", 10),
            state="disabled",
        )
        self.log_text.grid(row=0, column=0, sticky="nsew")
        scrollbar = ttk.Scrollbar(text_frame, orient="vertical", command=self.log_text.yview)
        scrollbar.grid(row=0, column=1, sticky="ns")
        self.log_text.configure(yscrollcommand=scrollbar.set)

    # O que esta função faz:
    # Cria uma linha com rótulo, campo de caminho e botão Procurar.
    @staticmethod
    def _path_row(
        parent: ttk.LabelFrame,
        row: int,
        label: str,
        variable: tk.StringVar,
        command: Callable[[], None],
    ) -> None:
        ttk.Label(parent, text=label).grid(row=row, column=0, sticky="w", padx=8, pady=7)
        ttk.Entry(parent, textvariable=variable).grid(row=row, column=1, sticky="ew", padx=8, pady=7)
        ttk.Button(parent, text="Procurar", command=command).grid(row=row, column=2, padx=8, pady=7)

    # O que esta função faz:
    # Abre o seletor para escolher gdb na interface.
    def select_gdb(self) -> None:
        path = filedialog.askdirectory(title="Selecione a pasta File Geodatabase (.gdb)")
        if path:
            self.var_gdb.set(normalize_path_for_display(path))

    # O que esta função faz:
    # Abre o seletor para escolher shp na interface.
    def select_shp(self) -> None:
        path = filedialog.askdirectory(title="Selecione a pasta dos shapefiles")
        if path:
            self.var_shp.set(normalize_path_for_display(path))

    # O que esta função faz:
    # Abre o seletor para escolher dss na interface.
    def select_dss(self) -> None:
        path = filedialog.askdirectory(title="Selecione a pasta dos arquivos OpenDSS")
        if path:
            normalized = normalize_path_for_display(path)
            self.var_dss.set(normalized)
            if not self.var_output.get().strip():
                self.var_output.set(
                    normalize_path_for_display(
                        str(Path(normalized) / "ViabilizaGD_Resultados")
                    )
                )

    # O que esta função faz:
    # Abre o seletor para escolher output na interface.
    def select_output(self) -> None:
        path = filedialog.askdirectory(title="Selecione a pasta-base para os resultados")
        if path:
            self.var_output.set(normalize_path_for_display(path))

    # O que esta função faz:
    # Abre o seletor para escolher master na interface.
    def select_master(self) -> None:
        initial = self.var_dss.get().strip() or None
        path = filedialog.askopenfilename(
            title="Selecione um arquivo Master OpenDSS",
            initialdir=initial,
            filetypes=(("Arquivos OpenDSS", "*.dss"), ("Todos os arquivos", "*.*")),
        )
        if path:
            self.var_selected_master.set(normalize_path_for_display(path))

    # O que esta função faz:
    # Habilita a seleção manual do Master somente quando essa opção estiver ativa.
    def _update_master_state(self) -> None:
        enabled = self.var_master_scope.get() == "Selecionar um Master"
        self.master_entry.configure(state="normal" if enabled else "disabled")
        self.master_button.configure(state="normal" if enabled else "disabled")

    # O que esta função faz:
    # Lê os valores preenchidos na interface e valida os parâmetros da análise.
    def _collect_config(self) -> AnalysisConfig:
        output = self.var_output.get().strip()
        if not output and self.var_dss.get().strip():
            output = str(Path(self.var_dss.get().strip()) / "ViabilizaGD_Resultados")
            self.var_output.set(output)

        config = AnalysisConfig(
            gdb_path=self.var_gdb.get().strip(),
            shp_path=self.var_shp.get().strip(),
            dss_path=self.var_dss.get().strip(),
            output_path=output,
            consumer_id=self.var_consumer.get().strip(),
            generator_kw=parse_decimal(self.var_kw.get()),
            generator_pf=parse_decimal(self.var_pf.get()),
            generator_model=int(self.var_model.get()),
            generator_profile=self.var_profile.get(),
            master_scope=self.var_master_scope.get(),
            selected_master=self.var_selected_master.get().strip(),
            temporal_mode=self.var_temporal_mode.get(),
            reverse_tolerance_kw=parse_decimal(self.var_reverse_tolerance.get()),
            aggravation_tolerance_kw=parse_decimal(self.var_aggravation_tolerance.get()),
            max_candidates=int(self.var_max_candidates.get()),
            try_relocation=bool(self.var_try_relocation.get()),
            voltage_min_pu=parse_decimal(self.var_vmin.get()),
            voltage_max_pu=parse_decimal(self.var_vmax.get()),
            check_voltage=bool(self.var_check_voltage.get()),
        )
        if config.generator_kw <= 0:
            raise ValueError("A potência do Generator deve ser maior que zero.")
        if not 0 < abs(config.generator_pf) <= 1:
            raise ValueError("O fator de potência deve estar entre -1 e 1, diferente de zero.")
        if config.max_candidates < 1:
            raise ValueError("O número máximo de candidatos deve ser pelo menos 1.")
        if config.reverse_tolerance_kw < 0 or config.aggravation_tolerance_kw < 0:
            raise ValueError("As tolerâncias não podem ser negativas.")
        if config.voltage_min_pu <= 0 or config.voltage_max_pu <= config.voltage_min_pu:
            raise ValueError("A faixa de tensão configurada é inválida.")
        return config

    # O que esta função faz:
    # Valida as entradas e inicia a análise sem travar a janela do programa.
    def start_analysis(self) -> None:
        if self.worker and self.worker.is_alive():
            return
        try:
            config = self._collect_config()
        except Exception as exc:
            messagebox.showerror(APP_NAME, str(exc), parent=self)
            return

        self.cancel_event.clear()
        self.progress["value"] = 0
        self.var_status.set("Iniciando análise...")
        self.run_button.configure(state="disabled")
        self.cancel_button.configure(state="normal")
        self._append_log("\n" + "=" * 80)
        self._append_log(f"{APP_NAME} {APP_VERSION} — {dt.datetime.now():%d/%m/%Y %H:%M:%S}")

        # O que esta função faz:
        # Executa a simulação em outra thread e envia o resultado para a interface.
        def worker_target() -> None:
            try:
                outcome = execute_analysis(
                    config=config,
                    log=lambda text: self.ui_queue.put(("log", text)),
                    progress=lambda value: self.ui_queue.put(("progress", value)),
                    cancel_event=self.cancel_event,
                )
                self.ui_queue.put(("success", outcome))
            except AnalysisCancelled as exc:
                self.ui_queue.put(("cancelled", str(exc)))
            except Exception as exc:
                self.ui_queue.put(("error", (str(exc), traceback.format_exc())))

        self.worker = threading.Thread(target=worker_target, daemon=True)
        self.worker.start()

    # O que esta função faz:
    # Sinaliza que a análise em andamento deve ser interrompida.
    def cancel_analysis(self) -> None:
        if self.worker and self.worker.is_alive():
            self.cancel_event.set()
            self.var_status.set("Cancelamento solicitado...")
            self._append_log("Cancelamento solicitado. A etapa atual será encerrada com segurança.")

    # O que esta função faz:
    # Atualiza a janela com o progresso, os avisos e os resultados da análise.
    def _process_ui_queue(self) -> None:
        try:
            while True:
                event, payload = self.ui_queue.get_nowait()
                if event == "log":
                    self._append_log(str(payload))
                elif event == "progress":
                    percentage = max(0.0, min(1.0, float(payload))) * 100
                    self.progress["value"] = percentage
                    self.var_status.set(f"Executando... {percentage:.0f}%")
                elif event == "success":
                    outcome: AnalysisOutcome = payload
                    self.progress["value"] = 100
                    self.var_status.set("Análise concluída.")
                    self._append_log(outcome.final_message)
                    self._append_log(f"Pasta de resultados: {outcome.output_directory}")
                    messagebox.showinfo(
                        APP_NAME,
                        outcome.final_message + "\n\nResultados salvos em:\n" + outcome.output_directory,
                        parent=self,
                    )
                    self._set_idle()
                elif event == "cancelled":
                    self.var_status.set("Análise cancelada.")
                    self._append_log(str(payload))
                    self._set_idle()
                elif event == "error":
                    message, details = payload
                    self.var_status.set("Erro na análise.")
                    self._append_log("ERRO: " + message)
                    self._append_log(details)
                    messagebox.showerror(APP_NAME, message, parent=self)
                    self._set_idle()
        except queue.Empty:
            pass
        self.after(100, self._process_ui_queue)

    # O que esta função faz:
    # Libera o botão de execução e desativa o botão de cancelamento.
    def _set_idle(self) -> None:
        self.run_button.configure(state="normal")
        self.cancel_button.configure(state="disabled")

    # O que esta função faz:
    # Adiciona uma mensagem ao painel de registro da execução.
    def _append_log(self, text: str) -> None:
        self.log_text.configure(state="normal")
        self.log_text.insert("end", str(text).rstrip() + "\n")
        self.log_text.see("end")
        self.log_text.configure(state="disabled")

    # O que esta função faz:
    # Apaga as mensagens exibidas no painel de registro.
    def clear_log(self) -> None:
        self.log_text.configure(state="normal")
        self.log_text.delete("1.0", "end")
        self.log_text.configure(state="disabled")

    # O que esta função faz:
    # Pede confirmação antes de fechar se uma análise ainda estiver em andamento.
    def on_close(self) -> None:
        if self.worker and self.worker.is_alive():
            if not messagebox.askyesno(
                APP_NAME,
                "Existe uma análise em execução. Deseja cancelar e fechar?",
                parent=self,
            ):
                return
            self.cancel_event.set()
        self.destroy()


# =============================================================================
# Autotestes leves, sem OpenDSS
# =============================================================================

# O que esta função faz:
# Executa testes pequenos, com dados simulados, sem precisar abrir a janela principal.
def run_self_test() -> int:
    import tempfile
    import types

    with tempfile.TemporaryDirectory() as temp_dir:
        root = Path(temp_dir)
        dss_file = root / "CargasBT_DU01_202312380_AFC01_TESTE.dss"
        dss_file.write_text(
            "! comentário\n"
            "New Load.0000000399c6aea5ad0c709a9bc331a3ed649470 "
            "bus1=BT1.1.2.3 phases=3 conn=wye kV=0.22 kW=5\n"
            "~ daily=CURVA\n",
            encoding="utf-8",
        )
        cancel = threading.Event()
        ref = find_consumer_reference(root, "0000000399c6aea5ad0c709a9bc331a3ed649470", print, cancel)
        assert ref.load_name_hint.startswith("0000000399")
        commands = list(iter_dss_commands(dss_file))
        assert len(commands) == 1
        assert "daily=CURVA" in commands[0][1]
        assert canonical_bus("BT1.1.2.3") == "bt1"
        assert bus_nodes_suffix("BT1.1.2.3") == ".1.2.3"
        assert merge_bus_with_original_nodes("BT2", "BT1.1.2.3") == "BT2.1.2.3"
        assert merge_bus_with_original_nodes("BT2.1.4", "BT1.1.2.4") == "BT2.1.2.4"
        assert infer_feeder_from_filename(dss_file.name) == "AFC01"

        # Regressão v1.08: um secundário 127/254 V com derivação central não
        # pode fazer uma carga Delta de 254 V cair no enrolamento 1-4 de 127 V.
        split_secondary = TransformerInfo(
            name="trf_split",
            buses=["MT1.1.0", "BT_DESTINO.1.4", "BT_DESTINO.4.2"],
            winding_kv=[7.62102355330306, 0.127, 0.127],
            hv_terminal=1,
            lv_terminal=2,
            hv_bus="MT1.1.0",
            lv_bus="BT_DESTINO.1.4",
            kv_high=7.62102355330306,
            kv_low=0.127,
        )
        delta_254 = LoadConnection(
            "load_delta_254", "BT_ORIGEM.1.2.4", 1, 0.254, "delta", ".1.2.4"
        )
        assert load_connection_nodes(delta_254) == ("1", "2")
        assert transformer_connection_nominal_kvs(split_secondary, delta_254) == [0.254]
        assert transformer_supports_load_connection(split_secondary, delta_254)

        single_127 = TransformerInfo(
            name="trf_127",
            buses=["MT2.1.0", "BT_127.1.4"],
            winding_kv=[7.62102355330306, 0.127],
            hv_terminal=1,
            lv_terminal=2,
            hv_bus="MT2.1.0",
            lv_bus="BT_127.1.4",
            kv_high=7.62102355330306,
            kv_low=0.127,
        )
        assert not transformer_supports_load_connection(single_127, delta_254)

        # A associação espacial usa somente igualdade exata com COD_ID. O nome
        # completo tem prioridade; o sufixo A/B/C é retirado apenas como regra
        # secundária, e duplicidades nunca são resolvidas escolhendo a primeira.
        transformer_name = "trf_739et002287299a"
        assert transformer_cod_id_candidates(transformer_name) == [
            ("739et002287299a", "COD_ID integral"),
            ("739et002287299", "COD_ID sem sufixo de fase A/B/C"),
        ]
        full_index = {
            "739et002287299a": [(4, "739ET002287299A")],
            "739et002287299": [(7, "739ET002287299")],
            "a": [(0, "A")],
        }
        full_match, problem = match_transformer_to_cod_id(
            transformer_name, full_index
        )
        assert not problem
        assert full_match is not None
        assert full_match.row_position == 4
        assert full_match.cod_id == "739ET002287299A"

        stripped_match, problem = match_transformer_to_cod_id(
            transformer_name,
            {"739et002287299": [(7, "739ET002287299")], "a": [(0, "A")]},
        )
        assert not problem
        assert stripped_match is not None
        assert stripped_match.row_position == 7
        assert stripped_match.rule == "COD_ID sem sufixo de fase A/B/C"

        ambiguous_match, problem = match_transformer_to_cod_id(
            transformer_name,
            {"739et002287299": [(7, "739ET002287299"), (8, "739ET002287299")]},
        )
        assert ambiguous_match is None
        assert "aparece 2 vezes" in problem

        false_match, problem = match_transformer_to_cod_id(
            transformer_name, {"a": [(0, "A")]}
        )
        assert false_match is None
        assert "nenhum COD_ID exato" in problem

        # Exercita o cálculo espacial completo com uma implementação mínima de
        # GeoDataFrame. A primeira linha contém apenas "A": na v1.06 ela era
        # associada incorretamente a todos os Transformers terminados em A.
        class FakeAxis:
            unit_conversion_factor = 1.0

        class FakeCRS:
            is_geographic = False
            axis_info = [FakeAxis(), FakeAxis()]

        class FakeGeometry:
            # O que esta função faz:
            # Prepara as informações e os recursos necessários para utilizar esta parte do programa.
            def __init__(self, x: float) -> None:
                self.x = x
                self.is_empty = False

            # O que esta função faz:
            # Devolve o próprio ponto usado como centro da geometria de teste.
            @property
            def centroid(self) -> "FakeGeometry":
                return self

            # O que esta função faz:
            # Calcula a distância entre dois pontos de teste.
            def distance(self, other: "FakeGeometry") -> float:
                return abs(self.x - other.x)

        class FakeILoc:
            # O que esta função faz:
            # Prepara as informações e os recursos necessários para utilizar esta parte do programa.
            def __init__(self, frame: "FakeGeoFrame") -> None:
                self.frame = frame

            # O que esta função faz:
            # Permite acessar linhas ou colunas do conjunto de dados simulado.
            def __getitem__(self, positions: Sequence[int]) -> "FakeGeoFrame":
                return FakeGeoFrame(
                    [dict(self.frame.rows[position]) for position in positions],
                    self.frame.crs,
                )

        class FakeGeoFrame:
            # O que esta função faz:
            # Prepara as informações e os recursos necessários para utilizar esta parte do programa.
            def __init__(self, rows: list[dict[str, Any]], crs: Any) -> None:
                self.rows = rows
                self.crs = crs

            # O que esta função faz:
            # Indica se o conjunto de dados de teste está vazio.
            @property
            def empty(self) -> bool:
                return not self.rows

            # O que esta função faz:
            # Lista os nomes das colunas do conjunto de dados de teste.
            @property
            def columns(self) -> list[str]:
                names: list[str] = []
                for row in self.rows:
                    for name in row:
                        if name not in names:
                            names.append(name)
                return names

            # O que esta função faz:
            # Devolve as geometrias presentes nos dados simulados.
            @property
            def geometry(self) -> list[FakeGeometry]:
                return [row["geometry"] for row in self.rows]

            # O que esta função faz:
            # Permite selecionar linhas por posição nos dados de teste.
            @property
            def iloc(self) -> FakeILoc:
                return FakeILoc(self)

            # O que esta função faz:
            # Permite acessar linhas ou colunas do conjunto de dados simulado.
            def __getitem__(self, name: str) -> list[Any]:
                return [row.get(name) for row in self.rows]

            # O que esta função faz:
            # Verifica se uma coluna existe nos dados de teste.
            def __contains__(self, name: object) -> bool:
                return str(name) in self.columns

            # O que esta função faz:
            # Insere ou atualiza os valores de uma coluna nos dados de teste.
            def __setitem__(self, name: str, values: Sequence[Any]) -> None:
                for row, value in zip(self.rows, values):
                    row[name] = value

            # O que esta função faz:
            # Cria uma cópia independente do conjunto de dados simulado.
            def copy(self) -> "FakeGeoFrame":
                return FakeGeoFrame([dict(row) for row in self.rows], self.crs)

        fake_gdf = FakeGeoFrame(
            [
                {"COD_ID": "A", "OUTRO_CAMPO": "A", "geometry": FakeGeometry(999.0)},
                {
                    "COD_ID": "739ET002287299",
                    "OUTRO_CAMPO": "origem",
                    "geometry": FakeGeometry(0.0),
                },
                {
                    "COD_ID": "739ET000040379",
                    "OUTRO_CAMPO": "destino",
                    "geometry": FakeGeometry(123.5),
                },
            ],
            FakeCRS(),
        )
        (root / "UNTRMT.shp").write_bytes(b"autoteste")
        previous_geopandas = sys.modules.get("geopandas")
        sys.modules["geopandas"] = types.SimpleNamespace(
            read_file=lambda _path: fake_gdf
        )
        try:
            spatial_result = try_spatial_transformer_distances(
                root,
                "trf_739et002287299a",
                ["trf_739et000040379a"],
                lambda _text: None,
            )
        finally:
            if previous_geopandas is None:
                sys.modules.pop("geopandas", None)
            else:
                sys.modules["geopandas"] = previous_geopandas
        assert spatial_result.original_cod_id == "739ET002287299"
        assert spatial_result.cod_ids == {
            "trf_739et000040379a": "739ET000040379"
        }
        assert spatial_result.distances_m == {
            "trf_739et000040379a": 123.5
        }

        model_folder = root / "modelo"
        model_folder.mkdir()
        nt_loads = model_folder / "CargasBTNT_DO01_202312380_AFC01_TESTE.dss"
        nt_loads.write_text(
            "New \"Load.BT_00713f8ea9dc52ac49e46b6ba81853d0b4b23132_NT_M1\" "
            "bus1=BT2.1.4 phases=1 conn=wye kV=0.127 kW=0\n"
            "New \"Load.BT_00713f8ea9dc52ac49e46b6ba81853d0b4b23132_NT_M2\" "
            "bus1=BT2.1.4 phases=1 conn=wye kV=0.127 kW=0\n",
            encoding="utf-8",
        )
        used_loads = model_folder / "CargasBT_DO01_202312380_AFC01_TESTE.dss"
        used_loads.write_text(
            "New \"Load.BT_00713f8ea9dc52ac49e46b6ba81853d0b4b23132_M1\" "
            "bus1=BT2.1.4 phases=1 conn=wye kV=0.127 kW=1\n"
            "New \"Load.BT_00713f8ea9dc52ac49e46b6ba81853d0b4b23132_M2\" "
            "bus1=BT2.1.4 phases=1 conn=wye kV=0.127 kW=1\n",
            encoding="utf-8",
        )
        master = root / "Master_DO01_202312380_AFC01_TESTE.dss"
        master.write_text(
            "Clear\n"
            "Redirect [modelo/CargasBTNT_DO01_202312380_AFC01_TESTE.dss]\n"
            "Redirect [modelo/CargasBT_DO01_202312380_AFC01_TESTE.dss]\n",
            encoding="utf-8",
        )
        dependencies = collect_master_dependency_files([master], lambda _text: None)
        assert dependencies == sorted(
            [master.resolve(), nt_loads.resolve(), used_loads.resolve()]
        )
        scoped_ref = find_consumer_reference(
            root,
            "00713f8ea9dc52ac49e46b6ba81853d0b4b23132",
            lambda _text: None,
            cancel,
            files=dependencies,
        )
        assert Path(scoped_ref.source_file) == used_loads.resolve()
        assert not is_nontechnical_load_name(scoped_ref.load_name_hint)
        assert is_regular_consumer_load_file(used_loads)
        assert not is_regular_consumer_load_file(nt_loads)

        try:
            find_consumer_reference(
                root,
                "00713f8ea9dc52ac49e46b6ba81853d0b4b23132",
                lambda _text: None,
                cancel,
                files=[nt_loads],
            )
        except FileNotFoundError as exc:
            assert "não técnicas" in str(exc)
        else:
            raise AssertionError("Uma carga NT não pode identificar o ponto de conexão da GD.")

        backend = object.__new__(OpenDSSBackend)
        backend.all_load_names = lambda: [  # type: ignore[method-assign]
            "BT_00713f8ea9dc52ac49e46b6ba81853d0b4b23132_NT_M1",
            "BT_00713f8ea9dc52ac49e46b6ba81853d0b4b23132_NT_M2",
            "BT_00713f8ea9dc52ac49e46b6ba81853d0b4b23132_M1",
            "BT_00713f8ea9dc52ac49e46b6ba81853d0b4b23132_M2",
            "BT_outra_unidade_M1",
        ]
        resolved = backend.resolve_load_names(
            "00713f8ea9dc52ac49e46b6ba81853d0b4b23132",
            "BT_00713f8ea9dc52ac49e46b6ba81853d0b4b23132_NT_M1",
        )
        assert resolved == [
            "BT_00713f8ea9dc52ac49e46b6ba81853d0b4b23132_M1",
            "BT_00713f8ea9dc52ac49e46b6ba81853d0b4b23132_M2",
            "BT_00713f8ea9dc52ac49e46b6ba81853d0b4b23132_NT_M1",
            "BT_00713f8ea9dc52ac49e46b6ba81853d0b4b23132_NT_M2",
        ]

        backend.all_load_names = lambda: [  # type: ignore[method-assign]
            "BT_00713f8ea9dc52ac49e46b6ba81853d0b4b23132_NT_M1",
            "BT_00713f8ea9dc52ac49e46b6ba81853d0b4b23132_NT_M2",
        ]
        try:
            backend.resolve_load_names(
                "00713f8ea9dc52ac49e46b6ba81853d0b4b23132",
                "BT_00713f8ea9dc52ac49e46b6ba81853d0b4b23132_NT_M1",
            )
        except LookupError as exc:
            assert "somente em cargas não técnicas" in str(exc)
        else:
            raise AssertionError("A GD não pode ser conectada usando somente cargas NT.")

        scenario_connections = [
            LoadConnection(name, "BT2.1.4", 1, 0.127, "wye", ".1.4")
            for name in resolved
        ]

        class FakeScenarioBackend:
            # O que esta função faz:
            # Prepara as informações e os recursos necessários para utilizar esta parte do programa.
            def __init__(self) -> None:
                self._masters_with_reported_states: set[str] = set()
                self.edited_loads: list[tuple[str, str]] = []
                self.generator_connection: Optional[LoadConnection] = None
                self.generator_bus: Optional[str] = None

            # O que esta função faz:
            # Simula a abertura de um Master durante os autotestes.
            def compile(self, _master: Path) -> None:
                return None

            # O que esta função faz:
            # Consulta o modo de simulação e o horário atual do OpenDSS.
            def solution_state(self) -> SolutionState:
                return SolutionState(0, "snapshot", 0.0)

            # O que esta função faz:
            # Ignora as mensagens de log durante o autoteste.
            def log(self, _text: str) -> None:
                return None

            # O que esta função faz:
            # Devolve as cargas da unidade consumidora simulada.
            def resolve_load_names(self, _consumer_id: str, _hint: str) -> list[str]:
                return list(resolved)

            # O que esta função faz:
            # Consulta e devolve load connections a partir dos dados disponíveis.
            def get_load_connections(
                self, _load_names: Sequence[str]
            ) -> list[LoadConnection]:
                return list(scenario_connections)

            # O que esta função faz:
            # Reúne as informações dos transformadores do circuito.
            def all_transformer_infos(self) -> dict[str, TransformerInfo]:
                return {}

            # O que esta função faz:
            # Cria um mapa de ligações entre barramentos para procurar caminhos dentro da rede elétrica.
            def build_connectivity_graph(
                self,
            ) -> dict[str, list[tuple[str, str, float]]]:
                return {}

            # O que esta função faz:
            # Percorre a rede a partir de um barramento e devolve o primeiro transformador encontrado.
            def find_first_transformer_from_bus(
                self,
                _graph: dict[str, list[tuple[str, str, float]]],
                _bus: str,
            ) -> Optional[str]:
                return "trf_original"

            # O que esta função faz:
            # Altera o barramento de ligação de uma carga no circuito da simulação.
            def edit_load_bus(self, load_name: str, bus1: str) -> None:
                self.edited_loads.append((load_name, bus1))

            # O que esta função faz:
            # Insere um Generator no OpenDSS com as características informadas na interface.
            def add_generator(
                self,
                generator_name: str,
                connection: LoadConnection,
                bus1: str,
                kw: float,
                pf: float,
                model: int,
                profile: str,
            ) -> None:
                del generator_name, kw, pf, model, profile
                self.generator_connection = connection
                self.generator_bus = bus1

            # O que esta função faz:
            # Executa o fluxo de potência no modo rápido ou ao longo das 24 horas.
            def solve_steps(
                self,
                temporal_mode: str,
                transformer_infos: dict[str, TransformerInfo],
                reverse_tolerance_kw: float,
                cancel_event: threading.Event,
            ) -> list[TimeStepResult]:
                del temporal_mode, transformer_infos, reverse_tolerance_kw, cancel_event
                return []

        fake_backend = FakeScenarioBackend()
        candidate = TransformerInfo(
            name="trf_candidato",
            buses=["MT1.1.2.3", "BT_DESTINO"],
            winding_kv=[13.2, 0.22],
            hv_terminal=1,
            lv_terminal=2,
            hv_bus="MT1.1.2.3",
            lv_bus="BT_DESTINO",
            kv_high=13.2,
            kv_low=0.22,
        )
        original_for_ranking = TransformerInfo(
            name="trf_original",
            buses=["MT0", "BT_ORIGEM"],
            winding_kv=[13.2, 0.22],
            hv_terminal=1,
            lv_terminal=2,
            hv_bus="MT0",
            lv_bus="BT_ORIGEM",
            kv_high=13.2,
            kv_low=0.22,
        )
        unmapped_candidate = TransformerInfo(
            name="trf_sem_cod_id",
            buses=["MT2", "BT_PERTINHO"],
            winding_kv=[13.2, 0.22],
            hv_terminal=1,
            lv_terminal=2,
            hv_bus="MT2",
            lv_bus="BT_PERTINHO",
            kv_high=13.2,
            kv_low=0.22,
        )
        ranking_infos = {
            item.name: item
            for item in (original_for_ranking, candidate, unmapped_candidate)
        }
        ranking_graph = {
            "bt_origem": [
                ("bt_destino", "Line.longa", 50.0),
                ("bt_pertinho", "Line.curta", 1.0),
            ],
            "bt_destino": [("bt_origem", "Line.longa", 50.0)],
            "bt_pertinho": [("bt_origem", "Line.curta", 1.0)],
        }

        real_spatial_function = globals()["try_spatial_transformer_distances"]
        try:
            # Se uma distância espacial está disponível, o candidato sem COD_ID
            # não pode entrar na mesma lista usando uma unidade elétrica menor.
            globals()["try_spatial_transformer_distances"] = (
                lambda *_args, **_kwargs: SpatialDistanceResult(
                    distances_m={"trf_candidato": 25.0},
                    cod_ids={"trf_candidato": "COD_CANDIDATO"},
                    original_cod_id="COD_ORIGINAL",
                )
            )
            spatial_ranking = rank_candidate_transformers(
                transformer_infos=ranking_infos,
                original_transformer="trf_original",
                load_connection=scenario_connections[0],
                graph=ranking_graph,
                shp_folder=root,
                max_candidates=3,
                log=lambda _text: None,
            )
            assert [item.transformer.name for item in spatial_ranking] == [
                "trf_candidato"
            ]
            assert spatial_ranking[0].distance_unit == "m"
            assert spatial_ranking[0].spatial_cod_id == "COD_CANDIDATO"
            assert spatial_ranking[0].spatial_reference_cod_id == "COD_ORIGINAL"

            # Sem nenhuma distância espacial, todos usam o mesmo método do
            # grafo, e a menor distância elétrica fica em primeiro lugar.
            globals()["try_spatial_transformer_distances"] = (
                lambda *_args, **_kwargs: SpatialDistanceResult()
            )
            electrical_ranking = rank_candidate_transformers(
                transformer_infos=ranking_infos,
                original_transformer="trf_original",
                load_connection=scenario_connections[0],
                graph=ranking_graph,
                shp_folder=root,
                max_candidates=3,
                log=lambda _text: None,
            )
            assert [item.transformer.name for item in electrical_ranking] == [
                "trf_sem_cod_id",
                "trf_candidato",
            ]
            assert all(
                item.distance_unit == "custo do grafo elétrico"
                for item in electrical_ranking
            )
        finally:
            globals()["try_spatial_transformer_distances"] = real_spatial_function

        test_config = AnalysisConfig(
            gdb_path="",
            shp_path="",
            dss_path="",
            output_path="",
            consumer_id="00713f8ea9dc52ac49e46b6ba81853d0b4b23132",
            generator_kw=10.0,
            generator_pf=1.0,
            generator_model=1,
            generator_profile="Potência constante",
            master_scope="Selecionar um Master",
            selected_master="",
            temporal_mode="Estado atual do Master — rápido",
            reverse_tolerance_kw=0.1,
            aggravation_tolerance_kw=0.1,
            max_candidates=3,
            try_relocation=True,
            voltage_min_pu=0.90,
            voltage_max_pu=1.05,
            check_voltage=False,
        )
        scenario, _connections, _transformers, _graph = run_master_scenario(
            backend=fake_backend,  # type: ignore[arg-type]
            master=master,
            consumer_id=test_config.consumer_id,
            load_hint=scoped_ref.load_name_hint,
            config=test_config,
            cancel_event=cancel,
            add_generator=True,
            target_transformer=candidate,
        )
        assert [name for name, _bus in fake_backend.edited_loads] == resolved
        assert all(bus == "BT_DESTINO.1.4" for _name, bus in fake_backend.edited_loads)
        assert fake_backend.generator_connection is scenario_connections[0]
        assert not is_nontechnical_load_name(fake_backend.generator_connection.load_name)
        assert fake_backend.generator_bus == "BT_DESTINO.1.4"
        assert scenario.load_names == resolved
        assert scenario.moved_to_transformer == "trf_candidato"
        assert "serving_transformer" not in asdict(scenario)

        class FakeCircuit:
            # O que esta função faz:
            # Devolve nomes fictícios de nós para o teste de tensão.
            @staticmethod
            def AllNodeNames() -> list[str]:
                return ["bt1.1", "bt1.4", "mt1.2"]

            # O que esta função faz:
            # Devolve valores fictícios de tensão por unidade para o teste.
            @staticmethod
            def AllBusMagPu() -> list[float]:
                return [0.978, 0.00001, 1.061]

        class FakeDSS:
            Circuit = FakeCircuit()

        backend.dss = FakeDSS()
        assert backend.voltage_extremes() == (0.978, "bt1.1", 1.061, "mt1.2")

        class FakeFastSolution:
            # O que esta função faz:
            # Prepara as informações e os recursos necessários para utilizar esta parte do programa.
            def __init__(self) -> None:
                self.hour = 24.0
                self.solve_calls = 0
                self.solve_snap_calls = 0

            # O que esta função faz:
            # Simula uma solução que avançaria indevidamente o relógio.
            def Solve(self) -> None:
                # Reproduz o defeito da v1.05: o Solve herdaria Number=24.
                self.solve_calls += 1
                self.hour += 24.0

            # O que esta função faz:
            # Simula uma solução instantânea sem avançar o relógio.
            def SolveSnap(self) -> None:
                self.solve_snap_calls += 1

            # O que esta função faz:
            # Indica convergência na simulação usada pelo autoteste.
            @staticmethod
            def Converged() -> bool:
                return True

            # O que esta função faz:
            # Devolve o horário configurado no simulador de teste.
            def DblHour(self) -> float:
                return self.hour

        class FakeFastDSS:
            # O que esta função faz:
            # Prepara as informações e os recursos necessários para utilizar esta parte do programa.
            def __init__(self) -> None:
                self.Solution = FakeFastSolution()
                self.Circuit = FakeCircuit()

        fast_dss = FakeFastDSS()
        backend.dss = fast_dss
        rapid_steps = backend.solve_steps(
            temporal_mode="Estado atual do Master — rápido",
            transformer_infos={},
            reverse_tolerance_kw=0.1,
            cancel_event=cancel,
        )
        assert len(rapid_steps) == 1
        assert rapid_steps[0].hour == 24.0
        assert fast_dss.Solution.solve_snap_calls == 1
        assert fast_dss.Solution.solve_calls == 0

        # O que esta função faz:
        # Cria um resultado de potência fictício para testar as tolerâncias.
        def power_run(p_hv_kw: float) -> ScenarioRun:
            return ScenarioRun(
                master_file="Master_teste.dss",
                temporal_mode="Estado atual do Master — rápido",
                load_name="load_teste",
                load_names=["load_teste"],
                load_bus="BT_TESTE.1.2.4",
                load_buses={"load_teste": "BT_TESTE.1.2.4"},
                generator_bus=None,
                moved_to_transformer=None,
                inherited_solution_state=SolutionState(1, "Daily", 24.0),
                steps=[
                    TimeStepResult(
                        step_index=0,
                        hour=24.0,
                        converged=True,
                        min_voltage_pu=0.95,
                        min_voltage_node="bt_teste.1",
                        max_voltage_pu=1.02,
                        max_voltage_node="bt_teste.2",
                        transformers={
                            "trf_teste": TransformerPower(
                                name="trf_teste",
                                p_hv_kw=p_hv_kw,
                                physical_reverse=p_hv_kw < 0.0,
                                reverse_violation=False,
                            )
                        },
                    )
                ],
            )

        baseline_power_run = power_run(0.650404)
        reverse_power_run = power_run(-0.039265)
        zero_tolerance = compare_runs(
            [baseline_power_run],
            [reverse_power_run],
            reverse_tolerance_kw=0.0,
            aggravation_tolerance_kw=0.0,
            check_voltage=False,
            voltage_min_pu=0.9,
            voltage_max_pu=1.05,
        )
        assert zero_tolerance.new_physical_reverse == ["trf_teste"]
        assert zero_tolerance.new_reverse_violations == ["trf_teste"]
        assert not zero_tolerance.acceptable
        zero_message = build_initial_message(
            "uc_teste", zero_tolerance, 0.69, 0.0
        )
        assert "0.039265 kW" in zero_message
        assert "houve violação do critério" in zero_message

        tolerant = compare_runs(
            [baseline_power_run],
            [reverse_power_run],
            reverse_tolerance_kw=0.1,
            aggravation_tolerance_kw=0.1,
            check_voltage=False,
            voltage_min_pu=0.9,
            voltage_max_pu=1.05,
        )
        assert tolerant.new_physical_reverse == ["trf_teste"]
        assert tolerant.new_reverse_violations == []
        assert tolerant.acceptable
        tolerant_message = build_initial_message(
            "uc_teste", tolerant, 0.69, 0.1
        )
        assert "fluxo reverso físico" in tolerant_message
        assert "não houve violação do critério" in tolerant_message

        rejected = ComparisonSummary(
            transformers={},
            original_physical_reverse=[],
            modified_physical_reverse=["trf_teste"],
            new_physical_reverse=["trf_teste"],
            original_reverse_violations=[],
            modified_reverse_violations=["trf_teste"],
            new_reverse_violations=["trf_teste"],
            eliminated_reverse_violations=[],
            aggravated_reverse_violations=[],
            acceptable=False,
        )
        disabled_config = replace(test_config, try_relocation=False)
        disabled_message = build_final_message(
            "Resultado inicial.", rejected, disabled_config, [], None
        )
        assert "estava desativada" in disabled_message
        assert "nenhum transformador candidato foi testado" in disabled_message
        no_candidate_message = build_final_message(
            "Resultado inicial.", rejected, test_config, [], None
        )
        assert "nenhum transformador candidato compatível" in no_candidate_message

        export_sample = (
            "Clear\n"
            "Export meters\n"
            "~ multiple=yes\n"
            "! Export voltages\n"
            "New Circuit.Teste\n"
        )
        sanitized, disabled = disable_export_commands(export_sample)
        assert disabled == 1
        assert "! ViabilizaGD: comando ignorado" in sanitized
        assert "! ViabilizaGD: continuação de Export ignorada" in sanitized
        assert "! Export voltages" in sanitized
        assert "New Circuit.Teste" in sanitized

    print("Autotestes concluídos com sucesso.")
    return 0


# O que esta função faz:
# Lê os argumentos do programa e decide entre executar os autotestes ou abrir a interface.
def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="ViabilizaGD — protótipo monolítico")
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="executa autotestes leves sem abrir a interface",
    )
    args = parser.parse_args(argv)
    if args.self_test:
        return run_self_test()
    app = ViabilizaGDApp()
    app.mainloop()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
