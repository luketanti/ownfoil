import importlib
import json
import os
import shutil
import struct
import sys
import tempfile
import hashlib
import base64
import logging
from contextlib import contextmanager
from pathlib import Path


DEFAULT_SWITCH_GUIDES_SUBMODULE_SCRIPTS_DIR = (
    Path(__file__).resolve().parent / "vendor" / "switch_ghidra_scripts"
)
DEFAULT_LOCAL_METADATA_CACHE_DIR = (
    Path(__file__).resolve().parent / "data" / "cache" / "local-file-metadata"
)
logger = logging.getLogger("main")
CACHE_SCHEMA_VERSION = 2

_ALL_ICON_LANGUAGE_TOKENS = [
    "AmericanEnglish",
    "BritishEnglish",
    "Japanese",
    "French",
    "German",
    "LatinAmericanSpanish",
    "Spanish",
    "Italian",
    "Dutch",
    "CanadianFrench",
    "Portuguese",
    "Russian",
    "Korean",
    "TraditionalChinese",
    "SimplifiedChinese",
    "BrazilianPortuguese",
    "Polish",
    "Thai",
]

_LANGUAGE_CODE_TO_ICON_TOKENS = {
    "en": ["AmericanEnglish", "BritishEnglish"],
    "ja": ["Japanese"],
    "fr": ["French", "CanadianFrench"],
    "de": ["German"],
    "es": ["Spanish", "LatinAmericanSpanish"],
    "it": ["Italian"],
    "nl": ["Dutch"],
    "pt": ["Portuguese", "BrazilianPortuguese"],
    "ru": ["Russian"],
    "ko": ["Korean"],
    "zh": ["TraditionalChinese", "SimplifiedChinese"],
    "pl": ["Polish"],
    "th": ["Thai"],
}

_REGIONS_EN_GB = {"GB", "AU", "NZ", "IE"}
_REGIONS_ES_LATAM = {"AR", "BO", "BR", "CL", "CO", "CR", "DO", "EC", "GT", "HN", "MX", "NI", "PA", "PE", "PY", "SV", "UY", "VE"}
_REGIONS_ZH_TRADITIONAL = {"HK", "TW", "MO"}

_ICON_TOKEN_TO_NACP_LANGUAGE_INDEX = {
    "AmericanEnglish": 0,
    "BritishEnglish": 1,
    "Japanese": 2,
    "French": 3,
    "German": 4,
    "LatinAmericanSpanish": 5,
    "Spanish": 6,
    "Italian": 7,
    "Dutch": 8,
    "CanadianFrench": 9,
    "Portuguese": 10,
    "Russian": 11,
    "Korean": 12,
    "TraditionalChinese": 13,
    "SimplifiedChinese": 14,
    "BrazilianPortuguese": 15,
    "Polish": 16,
    "Thai": 17,
}


def resolve_switch_guides_scripts_dir():
    candidate = DEFAULT_SWITCH_GUIDES_SUBMODULE_SCRIPTS_DIR
    if candidate.is_dir():
        return candidate
    return None


def _file_signature(filepath):
    try:
        stat = os.stat(filepath)
        mtime_ns = getattr(stat, "st_mtime_ns", int(float(stat.st_mtime) * 1e9))
        return f"{int(stat.st_size)}:{int(mtime_ns)}"
    except Exception:
        return None


def _cache_file_for_path(filepath):
    try:
        normalized = str(Path(filepath).resolve()).lower()
    except Exception:
        normalized = str(filepath or "").strip().lower()
    digest = hashlib.sha256(normalized.encode("utf-8", errors="ignore")).hexdigest()
    return DEFAULT_LOCAL_METADATA_CACHE_DIR / f"{digest}.json"


def _decode_cached_payload(payload):
    if not isinstance(payload, dict):
        return None
    out = {}
    for key in ("title_id", "version", "name", "publisher", "display_version"):
        if key in payload:
            out[key] = payload.get(key)
    icon_b64 = payload.get("icon_b64")
    if icon_b64:
        try:
            out["icon_bytes"] = base64.b64decode(icon_b64.encode("ascii"))
        except Exception:
            pass
    return out


def _encode_cache_payload(metadata):
    payload = {}
    for key in ("title_id", "version", "name", "publisher", "display_version"):
        if key in metadata:
            payload[key] = metadata.get(key)
    icon_bytes = metadata.get("icon_bytes")
    if isinstance(icon_bytes, (bytes, bytearray)) and icon_bytes:
        try:
            payload["icon_b64"] = base64.b64encode(bytes(icon_bytes)).decode("ascii")
        except Exception:
            pass
    return payload


def _load_persistent_metadata_cache(filepath):
    signature = _file_signature(filepath)
    if not signature:
        return None
    cache_file = _cache_file_for_path(filepath)
    try:
        with open(cache_file, "r", encoding="utf-8") as handle:
            data = json.load(handle)
    except Exception:
        return None
    if not isinstance(data, dict):
        return None
    if int(data.get("schema_version") or 0) != CACHE_SCHEMA_VERSION:
        return None
    if str(data.get("signature") or "") != signature:
        return None
    if bool(data.get("miss")):
        return {}
    return _decode_cached_payload(data.get("payload") or {})


def _save_persistent_metadata_cache(filepath, metadata):
    signature = _file_signature(filepath)
    if not signature:
        return
    cache_file = _cache_file_for_path(filepath)
    try:
        DEFAULT_LOCAL_METADATA_CACHE_DIR.mkdir(parents=True, exist_ok=True)
    except Exception:
        return
    cache_doc = {
        "schema_version": CACHE_SCHEMA_VERSION,
        "signature": signature,
        "miss": not (isinstance(metadata, dict) and bool(metadata)),
        "payload": _encode_cache_payload(metadata or {}),
    }
    temp_file = cache_file.with_suffix(".tmp")
    try:
        with open(temp_file, "w", encoding="utf-8") as handle:
            json.dump(cache_doc, handle, ensure_ascii=False)
        os.replace(str(temp_file), str(cache_file))
    except Exception:
        try:
            if temp_file.is_file():
                temp_file.unlink()
        except Exception:
            pass


@contextmanager
def _switch_guides_import_path(scripts_dir):
    scripts_dir = str(scripts_dir)
    already_present = scripts_dir in sys.path
    if not already_present:
        sys.path.insert(0, scripts_dir)
    try:
        yield
    finally:
        if not already_present:
            try:
                sys.path.remove(scripts_dir)
            except ValueError:
                pass


def _load_switch_guides_modules(scripts_dir):
    with _switch_guides_import_path(scripts_dir):
        return {
            "pfs0": importlib.import_module("pfs0"),
            "hfs0": importlib.import_module("hfs0"),
            "nca": importlib.import_module("nca"),
            "cnmt": importlib.import_module("cnmt"),
            "romfs": importlib.import_module("romfs"),
            "nacp": importlib.import_module("nacp"),
            "xci": importlib.import_module("xci"),
        }


def _pick_best_name(nacp_obj):
    if nacp_obj is None:
        return ""
    try:
        name = str(nacp_obj.get_english_title() or "").strip()
        if name:
            return name
    except Exception:
        pass
    try:
        for title in list(getattr(nacp_obj, "titles", []) or []):
            candidate = str(getattr(title, "name", "") or "").strip()
            if candidate:
                return candidate
    except Exception:
        pass
    return ""


def _pick_best_publisher(nacp_obj):
    if nacp_obj is None:
        return ""
    try:
        publisher = str(nacp_obj.get_english_publisher() or "").strip()
        if publisher:
            return publisher
    except Exception:
        pass
    try:
        for title in list(getattr(nacp_obj, "titles", []) or []):
            candidate = str(getattr(title, "publisher", "") or "").strip()
            if candidate:
                return candidate
    except Exception:
        pass
    return ""


def _normalize_language_code(language_code):
    return str(language_code or "").strip().lower()


def _normalize_region_code(region_code):
    return str(region_code or "").strip().upper()


def _preferred_icon_tokens(language_code=None, region_code=None):
    lang = _normalize_language_code(language_code)
    region = _normalize_region_code(region_code)

    preferred = list(_LANGUAGE_CODE_TO_ICON_TOKENS.get(lang) or [])

    if lang == "en" and region in _REGIONS_EN_GB:
        preferred = ["BritishEnglish", "AmericanEnglish"]
    elif lang == "fr" and region == "CA":
        preferred = ["CanadianFrench", "French"]
    elif lang == "es" and region in _REGIONS_ES_LATAM:
        preferred = ["LatinAmericanSpanish", "Spanish"]
    elif lang == "pt" and region == "BR":
        preferred = ["BrazilianPortuguese", "Portuguese"]
    elif lang == "zh" and region == "CN":
        preferred = ["SimplifiedChinese", "TraditionalChinese"]
    elif lang == "zh" and region in _REGIONS_ZH_TRADITIONAL:
        preferred = ["TraditionalChinese", "SimplifiedChinese"]

    if "AmericanEnglish" not in preferred:
        preferred.append("AmericanEnglish")

    final_tokens = []
    seen = set()
    for token in preferred + list(_ALL_ICON_LANGUAGE_TOKENS):
        key = str(token or "").strip()
        if not key:
            continue
        lower_key = key.lower()
        if lower_key in seen:
            continue
        seen.add(lower_key)
        final_tokens.append(key)
    return final_tokens


def _icon_filenames_by_preference(language_code=None, region_code=None):
    out = [f"icon_{token}.dat" for token in _preferred_icon_tokens(language_code, region_code)]
    out.append("icon.dat")
    return out


def _pick_localized_title_and_publisher(nacp_obj, language_code=None, region_code=None):
    if nacp_obj is None:
        return _pick_best_name(nacp_obj), _pick_best_publisher(nacp_obj)

    for token in _preferred_icon_tokens(language_code, region_code):
        lang_idx = _ICON_TOKEN_TO_NACP_LANGUAGE_INDEX.get(token)
        if lang_idx is None:
            continue
        try:
            entry = nacp_obj.get_title_by_language(lang_idx)
        except Exception:
            entry = None
        if entry is None:
            continue
        name = str(getattr(entry, "name", "") or "").strip()
        publisher = str(getattr(entry, "publisher", "") or "").strip()
        if name:
            return name, publisher

    return _pick_best_name(nacp_obj), _pick_best_publisher(nacp_obj)


def _extract_nacp_and_icon_from_control_nca(
    nca_obj,
    romfs_mod,
    nacp_mod,
    preferred_language=None,
    preferred_region=None,
):
    section_idx = 0
    if not nca_obj.fsheaders[section_idx].section_has_content:
        return {}
    section_type = nca_obj.get_section_type(section_idx)
    if section_type != "RomFS":
        return {}

    decrypted_section = nca_obj.decrypted_sections[section_idx]
    fs_header = nca_obj.fsheaders[section_idx]
    romfs_data = decrypted_section[fs_header.content_start:fs_header.content_end]

    nacp_data = romfs_mod.extract_file_from_romfs(romfs_data, "control.nacp")
    icon_data = None
    for icon_name in _icon_filenames_by_preference(preferred_language, preferred_region):
        icon_data = romfs_mod.extract_file_from_romfs(romfs_data, icon_name)
        if icon_data:
            break

    out = {}
    if nacp_data:
        nacp_obj = nacp_mod.parse_nacp(nacp_data)
        title_name, publisher = _pick_localized_title_and_publisher(
            nacp_obj,
            language_code=preferred_language,
            region_code=preferred_region,
        )
        display_version = str(getattr(nacp_obj, "display_version", "") or "").strip()
        if title_name:
            out["name"] = title_name
        if publisher:
            out["publisher"] = publisher
        if display_version:
            out["display_version"] = display_version
    if icon_data:
        out["icon_bytes"] = icon_data
    return out


def _extract_cnmt_payload_from_meta_nca(nca_obj, pfs0_mod):
    if nca_obj is None:
        return None
    if not getattr(nca_obj, "fsheaders", None):
        return None
    if not nca_obj.fsheaders[0].section_has_content:
        return None

    decrypted_section = nca_obj.decrypted_sections[0]
    fs_header = nca_obj.fsheaders[0]
    section0_data = decrypted_section[fs_header.content_start:fs_header.content_end]
    if not section0_data:
        return None

    # Modern meta NCAs usually contain a PFS0 where one file is the CNMT payload.
    if section0_data[:4] in (b"PFS0", b"HFS0"):
        try:
            header = pfs0_mod.Pfs0Header(section0_data)
            strtab = section0_data[
                header.string_table_offset:header.string_table_offset + header.string_table_size
            ]
            entries = []
            for idx in range(header.num_files):
                pos = header.entry_table_offset + (idx * pfs0_mod.PFS0_FILE_ENTRY_SIZE)
                chunk = section0_data[pos:pos + pfs0_mod.PFS0_FILE_ENTRY_SIZE]
                entry = pfs0_mod.Pfs0FileEntry.from_bytes(chunk)
                null_pos = strtab.find(b"\x00", entry.string_offset)
                if null_pos == -1:
                    null_pos = len(strtab)
                filename = strtab[entry.string_offset:null_pos].decode("utf-8", errors="replace")
                entries.append((filename, entry))

            cnmt_entry = next(
                (item for item in entries if str(item[0]).lower().endswith(".cnmt")),
                None,
            )
            if cnmt_entry is None and entries:
                cnmt_entry = entries[0]
            if cnmt_entry is not None:
                _, entry = cnmt_entry
                start = header.data_offset + entry.offset
                end = start + entry.size
                if 0 <= start < end <= len(section0_data):
                    return section0_data[start:end]
        except Exception:
            logger.debug("Local metadata parse: failed to parse PFS0-wrapped CNMT payload", exc_info=True)

    # Legacy fallback heuristics.
    for start in (0, 0x20, 0x60):
        if start >= len(section0_data):
            continue
        candidate = section0_data[start:]
        if len(candidate) >= 0x20:
            return candidate
    return None


def _extract_from_nsp(filepath, modules, preferred_language=None, preferred_region=None):
    pfs0_mod = modules["pfs0"]
    nca_mod = modules["nca"]
    cnmt_mod = modules["cnmt"]
    romfs_mod = modules["romfs"]
    nacp_mod = modules["nacp"]

    with open(filepath, "rb") as handle:
        base_header = handle.read(pfs0_mod.PFS0_HEADER_SIZE_BASE)
    if len(base_header) < pfs0_mod.PFS0_HEADER_SIZE_BASE:
        raise ValueError("invalid NSP header")

    num_files, string_table_size, _ = struct.unpack("<III", base_header[4:16])
    full_header_size = (
        pfs0_mod.PFS0_HEADER_SIZE_BASE
        + num_files * pfs0_mod.PFS0_FILE_ENTRY_SIZE
        + string_table_size
    )
    with open(filepath, "rb") as handle:
        full_header_data = handle.read(full_header_size)
    header = pfs0_mod.Pfs0Header(full_header_data)
    strtab = full_header_data[
        header.string_table_offset:header.string_table_offset + header.string_table_size
    ]

    name_to_entry = {}
    for idx in range(header.num_files):
        pos = header.entry_table_offset + (idx * pfs0_mod.PFS0_FILE_ENTRY_SIZE)
        chunk = full_header_data[pos:pos + pfs0_mod.PFS0_FILE_ENTRY_SIZE]
        entry = pfs0_mod.Pfs0FileEntry.from_bytes(chunk)
        null_pos = strtab.find(b"\x00", entry.string_offset)
        if null_pos == -1:
            null_pos = len(strtab)
        filename = strtab[entry.string_offset:null_pos].decode("utf-8", errors="replace")
        name_to_entry[filename] = entry

    def _read_file_from_container(filename):
        entry = name_to_entry.get(filename)
        if entry is None:
            return None
        abs_offset = header.data_offset + entry.offset
        with open(filepath, "rb") as handle:
            handle.seek(abs_offset)
            return handle.read(entry.size)

    titlekey = None
    tik_name = next((name for name in name_to_entry if name.endswith(".tik")), None)
    if tik_name:
        tik_data = _read_file_from_container(tik_name)
        if tik_data and len(tik_data) >= 0x190:
            titlekey = tik_data[0x180:0x190]

    nca_names = [
        name
        for name in name_to_entry
        if str(name).lower().endswith(".nca") or str(name).lower().endswith(".ncz")
    ]
    if not nca_names:
        logger.warning("Local metadata NSP parse: no NCA/NCZ entries found in %s", filepath)
        return {}

    cnmt_nca_name = next(
        (
            name
            for name in nca_names
            if str(name).lower().endswith(".cnmt.nca") or str(name).lower().endswith(".cnmt.ncz")
        ),
        None,
    )
    if cnmt_nca_name is None:
        logger.warning("Local metadata NSP parse: CNMT NCA/NCZ not found in %s", filepath)
        return {}
    logger.info(
        "Local metadata NSP parse: selected CNMT container %s (total nca/ncz entries=%s) for %s",
        cnmt_nca_name,
        len(nca_names),
        filepath,
    )

    largest_name = max(
        (name for name in nca_names if name != cnmt_nca_name),
        key=lambda value: name_to_entry[value].size,
        default=None,
    )

    def _read_nca_or_ncz_from_container(filename):
        raw_data = _read_file_from_container(filename)
        if not raw_data:
            return None
        if str(filename).lower().endswith(".ncz"):
            return _decompress_ncz_bytes(raw_data)
        return raw_data

    def _read_nca_header_probe_from_container(filename):
        # ncz is compressed, so decompression can't be skipped; raw nca entries can be read partially
        if str(filename).lower().endswith(".ncz"):
            return _read_nca_or_ncz_from_container(filename)
        entry = name_to_entry.get(filename)
        if entry is None:
            return None
        abs_offset = header.data_offset + entry.offset
        with open(filepath, "rb") as handle:
            handle.seek(abs_offset)
            return handle.read(min(entry.size, nca_mod.NCA_HEADER_SIZE))

    cnmt_nca_data = _read_nca_or_ncz_from_container(cnmt_nca_name)
    if not cnmt_nca_data:
        logger.warning("Local metadata NSP parse: failed to load/decompress CNMT container %s in %s", cnmt_nca_name, filepath)
        return {}
    cnmt_nca_obj = nca_mod.Nca(cnmt_nca_data, titlekey=titlekey)
    cnmt_data = _extract_cnmt_payload_from_meta_nca(cnmt_nca_obj, pfs0_mod)
    if not cnmt_data:
        logger.warning("Local metadata NSP parse: failed to extract CNMT payload from %s", filepath)
        return {}
    cnmt_obj = cnmt_mod.parse_cnmt(cnmt_data)
    out = {
        "title_id": f"{int(cnmt_obj.title_id):016X}",
        "version": int(getattr(cnmt_obj, "version", 0) or 0),
    }
    logger.info(
        "Local metadata NSP parse: CNMT parsed title_id=%s version=%s for %s",
        out.get("title_id"),
        out.get("version"),
        filepath,
    )

    control_nca_data = None
    for name in nca_names:
        if name in (cnmt_nca_name, largest_name):
            continue
        probe_data = _read_nca_header_probe_from_container(name)
        if not probe_data:
            continue
        try:
            nca_header = nca_mod.NcaHeaderOnly(probe_data[:nca_mod.NCA_HEADER_SIZE])
            if nca_header.content_type == "Control":
                control_nca_data = _read_nca_or_ncz_from_container(name)
                logger.info("Local metadata NSP parse: control NCA found in %s via %s", filepath, name)
                break
        except Exception:
            continue

    if control_nca_data is None and largest_name is not None:
        probe_data = _read_nca_header_probe_from_container(largest_name)
        if probe_data:
            try:
                nca_header = nca_mod.NcaHeaderOnly(probe_data[:nca_mod.NCA_HEADER_SIZE])
                if nca_header.content_type == "Control":
                    control_nca_data = _read_nca_or_ncz_from_container(largest_name)
                    logger.info("Local metadata NSP parse: control NCA fallback hit in %s via %s", filepath, largest_name)
            except Exception:
                pass

    if control_nca_data:
        control_nca_obj = nca_mod.Nca(control_nca_data, titlekey=titlekey)
        out.update(
            _extract_nacp_and_icon_from_control_nca(
                control_nca_obj,
                romfs_mod,
                nacp_mod,
                preferred_language=preferred_language,
                preferred_region=preferred_region,
            )
        )
    else:
        logger.warning("Local metadata NSP parse: control NCA not found in %s", filepath)

    return out


def _extract_from_xci(filepath, modules, preferred_language=None, preferred_region=None):
    hfs0_mod = modules["hfs0"]
    pfs0_mod = modules["pfs0"]
    nca_mod = modules["nca"]
    cnmt_mod = modules["cnmt"]
    romfs_mod = modules["romfs"]
    nacp_mod = modules["nacp"]
    xci_mod = modules["xci"]

    with open(filepath, "rb") as handle:
        header_data = handle.read(0x200)
    header = xci_mod.XciHeader(header_data)
    hfs0_offset = int(header.hfs0_offset)

    with open(filepath, "rb") as handle:
        handle.seek(hfs0_offset)
        root_header = handle.read(int(header.hfs0_header_size))
    root_ctx = hfs0_mod.Hfs0Context(root_header, offset=0, verbose=False, name="rootpt")

    secure_offset = None
    for idx in range(root_ctx.header.num_files):
        name = root_ctx.get_file_name(idx)
        if name == "secure":
            entry = root_ctx.get_entry(idx)
            secure_offset = hfs0_offset + root_ctx.header_size + entry.offset
            break
    if secure_offset is None:
        logger.warning("Local metadata XCI parse: secure partition not found in %s", filepath)
        return {}

    with open(filepath, "rb") as handle:
        handle.seek(secure_offset)
        secure_peek = handle.read(16)
    num_files, string_table_size = struct.unpack("<II", secure_peek[4:12])
    secure_header_size = 16 + (num_files * hfs0_mod.Hfs0FileEntry.SIZE) + string_table_size
    with open(filepath, "rb") as handle:
        handle.seek(secure_offset)
        secure_header = handle.read(secure_header_size)
    secure_ctx = hfs0_mod.Hfs0Context(secure_header, offset=0, verbose=False, name="secure")

    name_to_index = {}
    for idx in range(secure_ctx.header.num_files):
        name = secure_ctx.get_file_name(idx)
        if name and (
            str(name).lower().endswith(".nca")
            or str(name).lower().endswith(".ncz")
        ):
            name_to_index[name] = idx
    if not name_to_index:
        logger.warning("Local metadata XCI parse: no NCA/NCZ entries found in secure partition for %s", filepath)
        return {}

    cnmt_nca_name = next(
        (
            name
            for name in name_to_index
            if str(name).lower().endswith(".cnmt.nca") or str(name).lower().endswith(".cnmt.ncz")
        ),
        None,
    )
    if cnmt_nca_name is None:
        logger.warning("Local metadata XCI parse: CNMT NCA/NCZ not found in %s", filepath)
        return {}
    logger.info(
        "Local metadata XCI parse: selected CNMT container %s (total nca/ncz entries=%s) for %s",
        cnmt_nca_name,
        len(name_to_index),
        filepath,
    )

    largest_name = None
    largest_size = -1
    for name, idx in name_to_index.items():
        if name == cnmt_nca_name:
            continue
        entry = secure_ctx.get_entry(idx)
        if entry and entry.size > largest_size:
            largest_size = entry.size
            largest_name = name

    def _read_nca_or_ncz_from_secure(name):
        idx = name_to_index[name]
        entry = secure_ctx.get_entry(idx)
        abs_offset = secure_offset + secure_ctx.header_size + entry.offset
        with open(filepath, "rb") as handle:
            handle.seek(abs_offset)
            raw = handle.read(entry.size)
        if str(name).lower().endswith(".ncz"):
            return _decompress_ncz_bytes(raw)
        return raw

    def _read_nca_header_probe_from_secure(name):
        # ncz is compressed, so decompression can't be skipped; raw nca entries can be read partially
        if str(name).lower().endswith(".ncz"):
            return _read_nca_or_ncz_from_secure(name)
        idx = name_to_index[name]
        entry = secure_ctx.get_entry(idx)
        abs_offset = secure_offset + secure_ctx.header_size + entry.offset
        with open(filepath, "rb") as handle:
            handle.seek(abs_offset)
            return handle.read(min(entry.size, nca_mod.NCA_HEADER_SIZE))

    cnmt_nca_data = _read_nca_or_ncz_from_secure(cnmt_nca_name)
    if not cnmt_nca_data:
        logger.warning("Local metadata XCI parse: failed to load/decompress CNMT container %s in %s", cnmt_nca_name, filepath)
        return {}
    cnmt_nca_obj = nca_mod.Nca(cnmt_nca_data, titlekey=None)
    cnmt_data = _extract_cnmt_payload_from_meta_nca(cnmt_nca_obj, pfs0_mod)
    if not cnmt_data:
        logger.warning("Local metadata XCI parse: failed to extract CNMT payload from %s", filepath)
        return {}
    cnmt_obj = cnmt_mod.parse_cnmt(cnmt_data)
    out = {
        "title_id": f"{int(cnmt_obj.title_id):016X}",
        "version": int(getattr(cnmt_obj, "version", 0) or 0),
    }
    logger.info(
        "Local metadata XCI parse: CNMT parsed title_id=%s version=%s for %s",
        out.get("title_id"),
        out.get("version"),
        filepath,
    )

    control_nca_data = None
    for name in name_to_index:
        if name in (cnmt_nca_name, largest_name):
            continue
        probe_data = _read_nca_header_probe_from_secure(name)
        if not probe_data:
            continue
        try:
            nca_header = nca_mod.NcaHeaderOnly(probe_data[:nca_mod.NCA_HEADER_SIZE])
            if nca_header.content_type == "Control":
                control_nca_data = _read_nca_or_ncz_from_secure(name)
                logger.info("Local metadata XCI parse: control NCA found in %s via %s", filepath, name)
                break
        except Exception:
            continue

    if control_nca_data is None and largest_name is not None:
        probe_data = _read_nca_header_probe_from_secure(largest_name)
        if probe_data:
            try:
                nca_header = nca_mod.NcaHeaderOnly(probe_data[:nca_mod.NCA_HEADER_SIZE])
                if nca_header.content_type == "Control":
                    control_nca_data = _read_nca_or_ncz_from_secure(largest_name)
                    logger.info("Local metadata XCI parse: control NCA fallback hit in %s via %s", filepath, largest_name)
            except Exception:
                pass

    if control_nca_data:
        control_nca_obj = nca_mod.Nca(control_nca_data, titlekey=None)
        out.update(
            _extract_nacp_and_icon_from_control_nca(
                control_nca_obj,
                romfs_mod,
                nacp_mod,
                preferred_language=preferred_language,
                preferred_region=preferred_region,
            )
        )
    else:
        logger.warning("Local metadata XCI parse: control NCA not found in %s", filepath)

    return out


def _decompress_ncz_bytes(ncz_bytes):
    if not isinstance(ncz_bytes, (bytes, bytearray)) or not ncz_bytes:
        return None
    try:
        from nsz.NszDecompressor import decompress as nsz_decompress
    except Exception:
        logger.warning("Local metadata parse: nsz.NszDecompressor is unavailable for NCZ partial decompression")
        return None

    temp_root = Path(__file__).resolve().parent / "data" / "tmp" / "local-metadata"
    try:
        temp_root.mkdir(parents=True, exist_ok=True)
    except Exception:
        return None

    temp_dir = tempfile.mkdtemp(prefix="decompress-ncz-", dir=str(temp_root))
    in_path = Path(temp_dir) / "part.ncz"
    out_path = Path(temp_dir) / "part.nca"
    try:
        with open(in_path, "wb") as handle:
            handle.write(bytes(ncz_bytes))
        logger.debug("Local metadata parse: decompressing NCZ chunk (%s bytes)", len(ncz_bytes))
        nsz_decompress(str(in_path), temp_dir, False, None, True)
        if not out_path.is_file():
            candidates = list(Path(temp_dir).glob("*.nca"))
            if not candidates:
                return None
            out_path = candidates[0]
        with open(out_path, "rb") as handle:
            return handle.read()
    except Exception:
        logger.warning("Local metadata parse: NCZ partial decompression failed", exc_info=True)
        return None
    finally:
        try:
            shutil.rmtree(temp_dir, ignore_errors=True)
        except Exception:
            pass


def extract_local_metadata(filepath, scripts_dir=None, preferred_language=None, preferred_region=None):
    filepath = str(filepath or "").strip()
    if not filepath:
        return {}
    if not os.path.isfile(filepath):
        return {}

    cached = _load_persistent_metadata_cache(filepath)
    if isinstance(cached, dict):
        logger.debug("Local metadata parse: cache hit for %s", filepath)
        return dict(cached)

    # Only allow loading vendored Switch-Ghidra parser modules from this repo.
    scripts_dir = resolve_switch_guides_scripts_dir()
    if not scripts_dir:
        logger.warning("Local metadata parse: vendored parser scripts directory missing for %s", filepath)
        _save_persistent_metadata_cache(filepath, {})
        return {}

    try:
        modules = _load_switch_guides_modules(scripts_dir)
    except Exception:
        logger.warning("Local metadata parse: failed to load parser modules from %s for %s", scripts_dir, filepath, exc_info=True)
        _save_persistent_metadata_cache(filepath, {})
        return {}

    ext = Path(filepath).suffix.lower()
    logger.info("Local metadata parse: start for %s (ext=%s)", filepath, ext)
    try:
        if ext == ".nsp":
            out = _extract_from_nsp(
                filepath,
                modules,
                preferred_language=preferred_language,
                preferred_region=preferred_region,
            )
            _save_persistent_metadata_cache(filepath, out if isinstance(out, dict) else {})
            return out
        if ext == ".xci":
            out = _extract_from_xci(
                filepath,
                modules,
                preferred_language=preferred_language,
                preferred_region=preferred_region,
            )
            _save_persistent_metadata_cache(filepath, out if isinstance(out, dict) else {})
            return out
        if ext == ".nsz":
            out = _extract_from_nsp(
                filepath,
                modules,
                preferred_language=preferred_language,
                preferred_region=preferred_region,
            )
            _save_persistent_metadata_cache(filepath, out if isinstance(out, dict) else {})
            return out
        if ext == ".xcz":
            out = _extract_from_xci(
                filepath,
                modules,
                preferred_language=preferred_language,
                preferred_region=preferred_region,
            )
            _save_persistent_metadata_cache(filepath, out if isinstance(out, dict) else {})
            return out
    except Exception:
        logger.warning("Local metadata parse: extractor failed for %s", filepath, exc_info=True)
        _save_persistent_metadata_cache(filepath, {})
        return {}
    _save_persistent_metadata_cache(filepath, {})
    return {}
