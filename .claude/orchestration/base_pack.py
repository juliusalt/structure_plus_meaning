#!/usr/bin/env python3
"""Pack the EXISTING load list without selecting, summarizing or dropping content.

All packing edits are reversible. verify reconstructs every original digest,
byte for byte, from the packed text and the restoration record. The original
digest levels are inherited unchanged from manifest.py.

build --output DIR       freeze sources, produce bounded chunks and a size report
verify DIR               check every chunk, reconstruction and source boundary
bootstrap DIR            instructions for loading chunks through Bash, without Read's line numbers
emit DIR PART            emit exactly one bounded, hash-checked chunk
check-load DIR TRANSCRIPT require every complete chunk in the actual main transcript
snapshot DIR OUTPUT      manifest of the sources actually packed, not their later versions
count DIR                count payload variants with Anthropic's token-count endpoint (needs ANTHROPIC_API_KEY)

The loaded form is `all-but-fact-groups`: every reversible layer except the
grouping of fact names (and the prose reuse, which finds nothing to share), so
Isabelle symbols appear as glyphs, omission notes are short, layout outside
strings is compact, the theory-name index shares prefixes and theory headers are
compact. Lemma names stay written out. Every other variant is built for
comparison only. Estimates use byte-per-token ratios measured on Opus 5;
`base.sh max status` reports the loaded context. count does not launch a model
or change the active base.
"""
import argparse
import collections
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import sys
import time
import urllib.request

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import manifest
from digest import py_digest, thy_digest
from pack_notation import FACTS, expand_facts, fact_edits, theory_name

FORMAT = 2
CHUNK_BYTES = 120_000  # a Bash result is shown whole up to bashOutputMaxChars (128,000 characters, base-settings.json)
LEGEND = """# Loaded reference library
The original source paths and digest levels are retained below. This is reference
material, with the same authority as its sources. Read the current source before
editing or relying on a proof. No definitions, assumptions, theorem statements,
theorem names, or prose were selected out by this packing step.
Isabelle escapes are displayed using Isabelle's Unicode symbol table.
In theory digests, (* proof:N *) and (* code:N *) mean N omitted lines, as in
the original digest; spaces outside quotations, cartouches and comments are
compacted. The theory-name index explains its shared-prefix notation locally.
Repeated prose is shown once between EXCERPT markers; REPEAT uses that exact
excerpt, including its quotation marks and attribution, at the indicated place.
Source line numbers refer to the original files, not this display.
"""
NOTE = re.compile(r"\(\* (proof|code|equations) omitted: ([0-9]+) lines \*\)")
ESCAPE = re.compile(r"\\<[^>]+>")
NEW_LEGEND = LEGEND.replace(
    "Isabelle escapes are displayed using Isabelle's Unicode symbol table.",
    "Isabelle escape spellings and Unicode glyphs follow Isabelle's symbol table."
) + """In fact-name lists, prefix_{a,b} means prefix_a, prefix_b, in that order;
each suffix is concatenated with the complete prefix before the opening brace.
For a header showing only a digest level, the following theory X declaration
identifies its source as theories/X.thy. Declaration bodies are not factored.
"""
# The loaded text carries only what is needed to read it. Nothing about how it was selected or loaded.
BUNDLED_LEGEND = """# Reference library
Each section is one source file, named in its === header. Theory and tool texts are digests of their
sources: declarations, statements and commentary verbatim, each omitted proof or code body replaced by a
comment giving its length. [statements] keeps every lemma and theorem statement; [definitions] keeps the
definitions and lists only the names of what is proved. Read the current source before editing it or
relying on how something is proved; line numbers refer to the source files.
"""
PACKED_LEGEND = r"""# Reference library
Each section is one source file, named in its === header; a header showing only a digest level belongs to
theories/X.thy for the theory X that follows it. Theory and tool texts are digests of their sources:
declarations, statements and commentary verbatim, with (* proof:N *), (* code:N *) or (* equations:N *)
where N lines are omitted. [statements] keeps every lemma and theorem statement; [definitions] keeps the
definitions and lists only the names of what is proved; [signatures] is [definitions] with each definition
cut to its name and type up to `where`. Indentation outside strings, cartouches and comments is removed.
Isabelle symbols are shown as glyphs such as ⇒ ⟹ ∀ ‹ ›; the files spell them as escapes such as \<Rightarrow>
\<Longrightarrow> \<forall> \<open> \<close>, and text written into a theory must use the escapes, because
Isabelle rejects the glyphs. The theory-name index explains its prefix notation where it uses it. Read the
current source before editing it or relying on how something is proved; line numbers refer to the source files.
"""
BOOTSTRAP_PREFIX = "Load the reference library; do no development work."
# Measured 2026-09-19 with Opus 5 on this project's sources, one-word runs per variant: bytes per token as
# loaded (the theory ratio holds for every written form), the lean session a base starts from (its tools,
# the role prompt and the project memory, with the load's opening and closing turns), and one chunk call.
# Calibrated on the first full packed load (2026-09-19, base 32f5e011: 560,299 tokens against an estimate of
# 526,647): the sampled ratios scaled by 0.954, the session as measured, and per chunk its call, result
# wrapper and the model's turn between batches at max effort.
PACKED_RATIO = {".thy": 2.30, ".md": 3.80, ".txt": 3.80, ".py": 2.42}
INDEX_RATIO = 2.30  # the theory-name index: capitalised names tokenize like theory text
SESSION_TOKENS = 15_000
CALL_TOKENS = 190
# Tokens of the loaded form relative to the plain bundle, for the files it rewrites (measured the same day).
SELECTED_FACTOR = {".thy": 0.877, "index": 0.670}


def sha(text):
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def write_json(path, value):
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n")


def symbol_table(path):
    table = {}
    for line in path.read_text().splitlines():
        m = re.match(r"(\\<[^>]+>)\s+.*\bcode:\s*0x([0-9A-Fa-f]+)", line)
        if m and not m[1].startswith("\\<^"):
            char = chr(int(m[2], 16))
            if char.isprintable():
                table[m[1]] = char
    return table


def apply_edits(text, edits):
    """Apply disjoint edits, retaining enough information to invert each one."""
    out, restore, cursor, offset = [], [], 0, 0
    for start, end, replacement in sorted(edits):
        if start < cursor or end < start or end > len(text):
            raise ValueError("overlapping or invalid packing edit")
        prefix = text[cursor:start]
        out.extend((prefix, replacement))
        offset += len(prefix)
        restore.append([offset, replacement, text[start:end]])
        offset += len(replacement)
        cursor = end
    out.append(text[cursor:])
    return "".join(out), restore


def restore_text(text, edits):
    out, cursor = [], 0
    for at, packed, original in edits:
        if at < cursor or text[at:at + len(packed)] != packed:
            raise ValueError("packing restoration does not match its text")
        out.extend((text[cursor:at], original))
        cursor = at + len(packed)
    out.append(text[cursor:])
    return "".join(out)


def outer_layout_edits(text):
    """Only remove indentation/blank lines OUTSIDE strings, cartouches and comments.

    Contents of all three are opaque. In particular this never rewrites a string
    literal, quoted proposition, or explanatory text cartouche.
    """
    edits = []
    i = 0
    comment = cartouche = 0
    string = False
    line_start = True
    while i < len(text):
        if line_start and not (comment or cartouche or string):
            end = i
            while end < len(text) and text[end] in " \t":
                end += 1
            if end < len(text) and text[end] == "\n":
                edits.append((i, end + 1, ""))
                i = end + 1
                continue
            if end > i:
                edits.append((i, end, ""))
                i = end
                if i == len(text):
                    break
        line_start = text[i] == "\n"
        if comment:
            if text.startswith("(*", i):
                comment += 1
                i += 2
                continue
            if text.startswith("*)", i):
                comment -= 1
                i += 2
                continue
        elif cartouche:
            for token, change in (("\\<open>", 1), ("\\<close>", -1), ("‹", 1), ("›", -1)):
                if text.startswith(token, i):
                    cartouche += change
                    i += len(token)
                    break
            else:
                i += 1
            continue
        elif string:
            if text[i] == "\\" and i + 1 < len(text) and text[i + 1] in '\\"':
                i += 2
                continue
            if text[i] == '"':
                string = False
        elif text.startswith("(*", i):
            comment = 1
            i += 2
            continue
        elif text.startswith("\\<open>", i) or text[i] == "‹":
            cartouche = 1
            i += 7 if text[i] == "\\" else 1
            continue
        elif text[i] == '"':
            string = True
        i += 1
    if comment or cartouche or string:
        # Digests may contain deliberately omitted ML bodies. An unclosed body
        # is not a license to guess at its lexical boundary.
        return []
    return edits


def enabled_layers(stage):
    """The layers a cumulative stage number stands for, or a given set of layer names."""
    return set(STAGES[1:stage + 1]) if isinstance(stage, int) else set(stage)


def pack_theory(text, symbols, stage, literal_notes=()):
    on = enabled_layers(stage)
    edits = []
    if "unicode" in on:
        edits.extend((m.start(), m.end(), symbols[m[0]]) for m in ESCAPE.finditer(text) if m[0] in symbols)
    if "short-notes" in on:
        # A marker that already occurred in the real source might be part of a
        # proposition or quoted example. Only abbreviate generated digest notes.
        edits.extend((m.start(), m.end(), "(* " + m[1] + ":" + m[2] + " *)")
                     for m in NOTE.finditer(text) if m[0] not in literal_notes)
    if "outer-layout" in on:
        edits.extend(outer_layout_edits(text))
    return apply_edits(text, edits)


def index_names(text):
    return [word for line in text.splitlines() if line and not line.startswith("#") for word in line.split()]


def expand_index(text):
    names = []
    for line in text.splitlines():
        if not line or line.startswith("#"):
            continue
        if "*: " in line:
            prefix, suffixes = line.split("*: ", 1)
            names.extend(prefix + suffix for suffix in suffixes.split())
        else:
            names.extend(line.split())
    return names


def pack_index(text):
    """Factor contiguous shared prefixes; preserve every name, order and section."""
    # Keep interspersed section headings in place (e.g. ROOT-listed versus
    # additional source files). Moving all comments to the top would lose that
    # distinction even though the list of names still round-tripped.
    boundaries, offset, seen_name = [0], 0, False
    for line in text.splitlines(keepends=True):
        if line.startswith("#") and seen_name:
            boundaries.append(offset)
            seen_name = False
        elif line.strip() and not line.startswith("#"):
            seen_name = True
        offset += len(line)
    if len(boundaries) > 1:
        boundaries.append(len(text))
        packed = "".join(pack_index(text[a:b])[0] for a, b in zip(boundaries, boundaries[1:]))
        return (packed, [[0, packed, text]]) if len(packed) < len(text) else (text, [])
    names = index_names(text)
    if not all(re.fullmatch(r"[A-Za-z][A-Za-z_0-9]*", n) for n in names):
        return text, []
    size = len(names)
    costs, choices = [0] * (size + 1), [None] * size
    for i in range(size - 1, -1, -1):
        costs[i], choices[i] = len(names[i]) + 1 + costs[i + 1], (i + 1, "")
        for match in re.finditer("_", names[i]):
            prefix = names[i][:match.end()]
            chars = len(prefix) + 3
            for j in range(i, size):
                if not names[j].startswith(prefix) or names[j] == prefix:
                    break
                chars += len(names[j]) - len(prefix) + 1
                if j > i and chars + costs[j + 1] < costs[i]:
                    costs[i], choices[i] = chars + costs[j + 1], (j + 1, prefix)
    out = [line for line in text.splitlines() if line.startswith("#")]
    out += ["# prefix*: suffix1 suffix2 expands to prefix+suffix1, prefix+suffix2; original source order.", ""]
    i = 0
    while i < size:
        j, prefix = choices[i]
        if prefix:
            out.append(prefix + "*: " + " ".join(n[len(prefix):] for n in names[i:j]))
        else:
            out.append(names[i])
        i = j
    packed = "\n".join(out) + "\n"
    if len(packed) >= len(text):
        return text, []
    if expand_index(packed) != names:
        raise ValueError("theory-name expansion changed names or import order")
    return packed, [[0, packed, text]]


def split_bytes(text, limit):
    """Prefer line boundaries, but also bound a single very long line."""
    if limit < 256:
        raise ValueError("chunk size must be at least 256 bytes")
    parts, current, size = [], [], 0
    for line in text.splitlines(keepends=True):
        for char in line:
            width = len(char.encode())
            if size + width > limit:
                parts.append("".join(current))
                current, size = [], 0
            current.append(char)
            size += width
        if size >= limit * 0.9:
            parts.append("".join(current))
            current, size = [], 0
    if current:
        parts.append("".join(current))
    return parts


def frozen_sources():
    files = manifest.held_files()
    result = []
    for tier, path in files:
        raw = Path(path).read_bytes()
        text = raw.decode("utf-8")
        literal_notes = [m[0] for m in NOTE.finditer(text)]
        literal_facts = [m[0] for m in FACTS.finditer(text)]
        level = manifest.level_of(path)
        if path.endswith(".thy"):
            text = thy_digest(text, level)
        elif path.endswith(".py"):
            text = py_digest(text)
        result.append({"path": path, "label": manifest.short(path), "tier": tier, "level": level,
                       "source_sha256": hashlib.sha256(raw).hexdigest(),
                       "source_sha1": hashlib.sha1(raw).hexdigest(), "text": text,
                       "literal_omission_notes": literal_notes,
                       "literal_fact_notes": literal_facts})
    # Refuse an inconsistent snapshot if a producer changed a source during capture.
    for item in result:
        if hashlib.sha256(Path(item["path"]).read_bytes()).hexdigest() != item["source_sha256"]:
            raise ValueError("source changed while packing: " + item["path"])
    return result


def prose_repetitions(sources):
    """Only exact paragraph repetitions. No paraphrasing or similarity matching."""
    pattern = re.compile(r"[^\n]+(?:\n(?!\n)[^\n]+)*")
    occurrences = collections.defaultdict(list)
    for i, source in enumerate(sources):
        if source["path"].endswith((".md", ".txt")) and not source["label"].endswith("/theory-names.md"):
            for m in pattern.finditer(source["text"]):
                if len(m[0]) >= 150:
                    occurrences[m[0]].append((i, m.start(), m.end()))
    edits = collections.defaultdict(list)
    for text, uses in occurrences.items():
        if len(uses) < 2 or "EXCERPT " in text or "REPEAT " in text:
            continue
        label = "R" + str(len(edits) + 1) + "-" + sha(text)[:6]
        first = "[EXCERPT " + label + "]\n" + text + "\n[END EXCERPT " + label + "]"
        repeat = "[REPEAT " + label + " VERBATIM]"
        if len(first) + (len(uses) - 1) * len(repeat) >= len(text) * len(uses):
            continue
        i, start, end = uses[0]
        edits[i].append((start, end, first))
        for i, start, end in uses[1:]:
            edits[i].append((start, end, repeat))
    return edits


def expand_prose(text):
    """Independent decoder for the explicit, backwards-only prose references."""
    pattern = re.compile(r"\[EXCERPT (R[0-9]+-[0-9a-f]{6})\]\n(.*?)\n\[END EXCERPT \1\]"
                         r"|\[REPEAT (R[0-9]+-[0-9a-f]{6}) VERBATIM\]", re.S)
    excerpts = {}

    def expand(match):
        if match[1]:
            if match[1] in excerpts:
                raise ValueError("duplicate excerpt label")
            excerpts[match[1]] = match[2]
            return match[2]
        if match[3] not in excerpts:
            raise ValueError("excerpt reference precedes its text")
        return excerpts[match[3]]

    return pattern.sub(expand, text)


def source_header(source, text, compact=False):
    name = theory_name(text)
    # A digest level only means something for digested sources; other files are held verbatim.
    level = " [" + source["level"] + "]" if source["label"].endswith((".thy", ".py")) else ""
    if compact and name and source["label"] == "theories/" + name + ".thy":
        return "\n===" + level + " ===\n"
    return "\n=== " + source["label"] + level + " ===\n"


def tier_heading(tier):
    """A tier's heading in the loaded text: its subject only, without the load list's curation notes."""
    subject = re.sub(r"\s*\([^()]*\)", "", tier).strip()
    for prefix, shown in (("pinned idea:", "Idea:"), ("pinned:", "")):
        if subject.startswith(prefix):
            subject = (shown + " " + subject[len(prefix):].strip()).strip()
    subject = subject.replace(" since the sealed base", "")
    if subject == "measured":
        subject = "Working frontier: theories and tools in current use"
    return "\n# " + subject[:1].upper() + subject[1:] + "\n"


def restore_source(text, source):
    for edits in reversed(source.get("restore_layers", [source.get("restore", [])])):
        text = restore_text(text, edits)
    return text


def sources_from_pack(directory):
    """Use the preceding candidate's exact frozen inputs for a fair comparison."""
    meta = verify(directory)
    text = "".join(checked_chunks(directory, meta))
    fields = ("path", "label", "tier", "level", "source_sha256", "source_sha1",
              "literal_omission_notes", "literal_fact_notes")
    sources = []
    for record in meta["sources"]:
        source = {k: record[k] for k in fields if k in record}
        source["text"] = restore_source(text[record["start"]:record["start"] + record["length"]], record)
        # Format 1 did not record these exclusions. Read the source only if its
        # bytes still match; otherwise conservatively leave matching notes alone.
        if "literal_fact_notes" not in source or "literal_omission_notes" not in source:
            path = Path(source["path"])
            raw = path.read_bytes() if path.exists() else b""
            matches = hashlib.sha256(raw).hexdigest() == source["source_sha256"]
            original = raw.decode() if matches else source["text"]
            source.setdefault("literal_fact_notes", [m[0] for m in FACTS.finditer(original)])
            source.setdefault("literal_omission_notes", [m[0] for m in NOTE.finditer(original)])
        sources.append(source)
    return sources, meta


def render(sources, symbols, stage):
    on = enabled_layers(stage)
    out, records, offset = [LOADED_LEGEND + "\n"], [], len(LOADED_LEGEND) + 1
    payload_estimate = 0.0
    repeats = prose_repetitions(sources) if "exact-prose-reuse" in on else {}
    previous_tier = None
    for i, source in enumerate(sources):
        text = source["text"]
        edits = []
        if source["path"].endswith(".thy"):
            text, edits = pack_theory(text, symbols, stage, source.get("literal_omission_notes", ()))
        elif "shared-name-prefixes" in on and source["label"].endswith("/theory-names.md"):
            text, edits = pack_index(text)
        elif i in repeats:
            text, edits = apply_edits(text, repeats[i])
        layers = [edits]
        before_facts = None
        if "shared-fact-prefixes" in on and source["level"] in ("definitions", "signatures") and source["path"].endswith(".thy"):
            before_facts = text
            text, edits = apply_edits(text, fact_edits(text, source.get("literal_fact_notes", ())))
            layers.append(edits)
            if expand_facts(text, source.get("literal_fact_notes", ())) != before_facts:
                raise ValueError("fact-name expansion differs: " + source["label"])
        header = source_header(source, text, compact="compact-theory-headers" in on)
        if source["tier"] != previous_tier:
            header = tier_heading(source["tier"]) + header
            previous_tier = source["tier"]
        out.append(header)
        offset += len(header)
        record = {k: v for k, v in source.items() if k != "text"} | {
            "start": offset, "length": len(text), "digest_sha256": sha(source["text"]),
            "packed_sha256": sha(text), "restore_layers": layers, "compact_header": "compact-theory-headers" in on}
        if before_facts is not None:
            record["before_facts_sha256"] = sha(before_facts)
        if restore_source(text, record) != source["text"]:
            raise ValueError("variant does not restore the complete digest: " + source["label"])
        records.append(record)
        out.append(text)
        offset += len(text)
        index = source["label"].endswith("/theory-names.md")
        ratio = INDEX_RATIO if index else PACKED_RATIO.get(Path(source["path"]).suffix, 2.6)
        payload_estimate += len(text.encode()) / ratio
    result = "".join(out)
    overhead = len(result.encode()) - sum(len(result[r["start"]:r["start"] + r["length"]].encode()) for r in records)
    return result, records, round(payload_estimate + overhead / 3.0)


STAGES = ("bundled", "unicode", "short-notes", "outer-layout", "shared-name-prefixes", "exact-prose-reuse",
          "shared-fact-prefixes", "compact-theory-headers")
SELECTED = "all-but-fact-groups"
SELECTED_LAYERS = set(STAGES[1:]) - {"shared-fact-prefixes", "exact-prose-reuse"}
LOADED_LEGEND = {"all-but-fact-groups": PACKED_LEGEND, "bundled": BUNDLED_LEGEND}.get(SELECTED, NEW_LEGEND)


def build(output, symbols_path, chunk_bytes, from_pack=None):
    if output.exists():
        raise ValueError("output already exists; use a new path to keep the previous pack fixed")
    sources, previous = sources_from_pack(from_pack) if from_pack else (frozen_sources(), None)
    symbols = symbol_table(symbols_path)
    if previous and hashlib.sha256(symbols_path.read_bytes()).hexdigest() != previous["symbols_sha256"]:
        raise ValueError("Isabelle symbol table changed since the frozen input pack")
    frequencies = collections.Counter(escape for source in sources if source["path"].endswith(".thy")
                                      for escape in ESCAPE.findall(source["text"]))
    common = {key: value for key, value in symbols.items() if frequencies[key] >= 100}
    specifications = [(name, stage, symbols) for stage, name in enumerate(STAGES)]
    specifications += [("escaped-symbols", 7, {}), ("common-unicode", 7, common), (SELECTED, SELECTED_LAYERS, symbols)]
    variants, texts, selected_records = [], {}, None
    for name, stage, spellings in specifications:
        text, records, estimate = render(sources, spellings, stage)
        texts[name] = text
        if name == SELECTED:
            selected_records = records
        parts = split_bytes(text, chunk_bytes)
        variants.append({"name": name, "bytes": len(text.encode()), "characters": len(text),
                         "sha256": sha(text),
                         "payload_token_estimate": estimate,
                         "loaded_token_estimate": estimate + SESSION_TOKENS + CALL_TOKENS * len(parts),
                         "chunks": len(parts)})
    final = texts[SELECTED]
    ident = sha(final)
    original_estimate = manifest.OVERHEAD_TOKENS
    original_calls = 0
    for source in sources:
        text = source["text"]
        ratio = manifest.RATIO.get(Path(source["path"]).suffix, 2.6)
        tokens = int((len(text.encode()) + manifest.LINE_PREFIX * (text.count("\n") + 1)) / ratio)
        calls = 1 + tokens // manifest.PART_TOKENS
        original_estimate += tokens + 90 * calls
        original_calls += calls
    meta = {"format": FORMAT, "id": ident, "created": time.strftime("%Y-%m-%dT%H:%M:%S"),
            "symbols_path": str(symbols_path), "symbols_sha256": hashlib.sha256(symbols_path.read_bytes()).hexdigest(),
            "chunk_bytes": chunk_bytes, "sources": selected_records, "chunks": [],
            "legend": LOADED_LEGEND, "selected_variant": SELECTED,
            "selected_loaded_token_estimate": next(r["loaded_token_estimate"] for r in variants if r["name"] == SELECTED),
            "frozen_from_pack": previous["id"] if previous else None,
            "variants": variants, "original_read_calls": original_calls,
            "original_loaded_token_estimate": original_estimate,
            "token_count_status": "estimates from byte-per-token ratios measured on Opus 5, 2026-09-19",
            "limitations": ["The ratios were measured on samples: 27 theories, 40K of Markdown and the theory index.",
                            "Payload token counts do not establish a live session's total context or cache reuse."]}
    output.mkdir(parents=True)
    for name, text in texts.items():
        (output / (name + ".txt")).write_text(text)
    parts_dir = output / "chunks"
    parts_dir.mkdir()
    for i, text in enumerate(split_bytes(final, chunk_bytes), 1):
        name = f"chunks/{i:04d}.txt"
        (output / name).write_text(text)
        meta["chunks"].append({"part": i, "file": name, "sha256": sha(text), "bytes": len(text.encode())})
    write_json(output / "pack.json", meta)
    verify(output)
    (output / "bootstrap.txt").write_text(bootstrap(output, meta))
    (output / "REPORT.md").write_text(report(meta))
    return meta


def load(directory):
    meta = json.loads((directory / "pack.json").read_text())
    if meta.get("format") not in (1, FORMAT):
        raise ValueError("unsupported pack format")
    return meta


def checked_chunks(directory, meta):
    texts = []
    for i, item in enumerate(meta["chunks"], 1):
        if item["part"] != i or item["file"] != f"chunks/{i:04d}.txt":
            raise ValueError("invalid chunk sequence")
        text = (directory / item["file"]).read_text()
        if sha(text) != item["sha256"] or len(text.encode()) != item["bytes"] or item["bytes"] > meta["chunk_bytes"]:
            raise ValueError("changed or oversized chunk " + str(i))
        texts.append(text)
    if sha("".join(texts)) != meta["id"]:
        raise ValueError("chunk sequence does not reproduce the packed bundle")
    return texts


def verify(directory):
    meta = load(directory)
    text = "".join(checked_chunks(directory, meta))
    baseline = (directory / (STAGES[0] + ".txt")).read_text()
    legend = meta.get("legend", LEGEND)
    expected_baseline = [legend + "\n"]
    previous_end = len(legend) + 1
    previous_tier = None
    before_facts_parts = [legend + "\n"]
    full_header_parts = [legend + "\n"]
    for item in meta["sources"]:
        part = text[item["start"]:item["start"] + item["length"]]
        header = source_header(item, part, compact=item.get("compact_header", False))
        original_header = source_header(item, part)
        if item["tier"] != previous_tier:
            header = tier_heading(item["tier"]) + header
            original_header = tier_heading(item["tier"]) + original_header
            previous_tier = item["tier"]
        if text[previous_end:item["start"]] != header:
            raise ValueError("source boundary changed: " + item["label"])
        if sha(part) != item["packed_sha256"]:
            raise ValueError("packed source changed: " + item["label"])
        original = restore_source(part, item)
        if sha(original) != item["digest_sha256"]:
            raise ValueError("source reconstruction failed: " + item["label"])
        if item["label"].endswith("/theory-names.md") and expand_index(part) != index_names(original):
            raise ValueError("theory names/order changed")
        expected_baseline.extend((original_header, original))
        full_header_parts.extend((original_header, part))
        expanded = expand_facts(part, item.get("literal_fact_notes", ())) if "before_facts_sha256" in item else part
        if "before_facts_sha256" in item and sha(expanded) != item["before_facts_sha256"]:
            raise ValueError("fact-name expansion differs from the complete preceding source")
        before_facts_parts.extend((original_header, expanded))
        previous_end = item["start"] + item["length"]
    if previous_end != len(text) or "".join(expected_baseline) != baseline:
        raise ValueError("reconstructed original bundle differs")
    for variant in meta["variants"]:
        variant_text = (directory / (variant["name"] + ".txt")).read_text()
        if (sha(variant_text) != variant["sha256"] or len(variant_text.encode()) != variant["bytes"]
                or len(variant_text) != variant["characters"]):
            raise ValueError("variant size differs")
    # When the most compact notation is loaded, its layers are also checked to expand, one by one, into the
    # preceding variants. The plain bundle is itself the baseline checked above.
    if meta.get("selected_variant", "compact-theory-headers") == "compact-theory-headers":
        if meta["format"] == FORMAT and "".join(full_header_parts) != (directory / "shared-fact-prefixes.txt").read_text():
            raise ValueError("compact headers do not expand to the complete source headers")
        expanded_facts = "".join(before_facts_parts)
        if meta["format"] == FORMAT and expanded_facts != (directory / "exact-prose-reuse.txt").read_text():
            raise ValueError("fact-name groups do not expand to the preceding complete variant")
        if expand_prose(expanded_facts) != (directory / "shared-name-prefixes.txt").read_text():
            raise ValueError("prose references do not expand to the preceding complete variant")
    return meta


def envelope(meta, number, text):
    marker = f"BASE-PACK {meta['id'][:12]} PART {number}/{len(meta['chunks'])}"
    return "BEGIN " + marker + "\n" + text + "\nEND " + marker + "\n"


def bootstrap(directory, meta):
    command = shlex.join([sys.executable, str(HERE / "base_pack.py"), "emit", str(directory)]) + " PART"
    return (BOOTSTRAP_PREFIX + " For PART=1 through " + str(len(meta["chunks"])) + ", run the command below "
            "once with that integer replacing PART, each part as its own Bash call; independent calls may go "
            "together in one response. Do not use Read, combine parts, summarize, edit, or run any other command. "
            "Every result must contain matching BEGIN and END lines; run a part again if its result is incomplete. "
            "When every part has arrived complete, reply with exactly LOADED " + meta["id"] + " and end your "
            "turn.\n\n" + command + "\n")


def check_load(directory, transcript):
    meta = verify(directory)
    # Claude Code stores a Bash result without its trailing newline, so the envelope is matched without it.
    expected = {envelope(meta, i, text).rstrip("\n"): i for i, text in enumerate(checked_chunks(directory, meta), 1)}
    found, completion = set(), False
    for line in transcript.read_text().splitlines():
        record = json.loads(line)
        if record.get("isSidechain"):
            continue
        content = (record.get("message") or {}).get("content", [])
        if not isinstance(content, list):
            continue
        for block in content:
            if record.get("type") == "user" and block.get("type") == "tool_result" and not block.get("is_error"):
                body = block.get("content", "")
                if isinstance(body, list):
                    body = "\n".join(b.get("text", "") for b in body if b.get("type") == "text")
                for value, number in expected.items():
                    if value in body:
                        found.add(number)
            if record.get("type") == "assistant" and block.get("type") == "text":
                if block.get("text", "").strip() == "LOADED " + meta["id"] and len(found) == len(expected):
                    completion = True
    if len(found) != len(expected) or not completion:
        raise ValueError(f"incomplete load: {len(found)}/{len(expected)} complete chunks; final acknowledgement={completion}")
    return {"pack": meta["id"], "complete_chunks": len(found), "sources": len(meta["sources"])}


def report(meta):
    lines = ["# Base packing comparison", "",
             "Same source list and digest levels throughout. Token figures below are estimates, not tokenizer counts.",
             "Every original digest reconstructs byte for byte; no prose, definition or theorem statement was selected out.",
             "", f"Sources: {len(meta['sources'])}. Original Read calls: {meta['original_read_calls']}.",
             f"Original loaded estimate: {meta['original_loaded_token_estimate']:,} tokens.",
             "", "| Variant | UTF-8 bytes | Payload estimate | Loaded estimate | Chunks |",
             "|---|---:|---:|---:|---:|"]
    for row in meta["variants"]:
        lines.append(f"| {row['name']} | {row['bytes']:,} | {row['payload_token_estimate']:,} | "
                     f"{row['loaded_token_estimate']:,} | {row['chunks']} |")
    selected = meta.get("selected_variant", meta["variants"][-1]["name"])
    estimate = meta.get("selected_loaded_token_estimate", meta["variants"][-1]["loaded_token_estimate"])
    lines += ["", f"Loaded: {selected}, about {estimate:,} tokens with the lean session's {SESSION_TOKENS:,} and "
                  f"{CALL_TOKENS} per chunk call.",
              f"Target: {manifest.TARGET:,} (ORCH_BASE_TARGET)" + (
                  f"; the load is about {estimate - manifest.TARGET:,} over it" if estimate > manifest.TARGET else ""),
              "The other rows are reversible notations kept for comparison; none of them is loaded.",
              "Estimates use measured byte-per-token ratios; base.sh max status reports the loaded context.", ""]
    return "\n".join(lines)


def count(directory, model, names=None):
    """Only use the standard endpoint; credentials never enter artifacts or output."""
    meta = verify(directory)
    key = os.environ.get("ANTHROPIC_API_KEY")
    if not key:
        raise ValueError("count needs ANTHROPIC_API_KEY; it does not borrow Claude Code's login")
    headers = {"content-type": "application/json", "anthropic-version": "2023-06-01", "x-api-key": key}
    results = []
    rows = meta["variants"]
    if names:
        unknown = set(names) - {row["name"] for row in rows}
        if unknown:
            raise ValueError("unknown count variants: " + ", ".join(sorted(unknown)))
        rows = [row for row in rows if row["name"] in names]
    for row in rows:
        content = (directory / (row["name"] + ".txt")).read_text()
        request = urllib.request.Request("https://api.anthropic.com/v1/messages/count_tokens",
                                         data=json.dumps({"model": model, "messages": [
                                             {"role": "user", "content": content}]}).encode(), headers=headers)
        with urllib.request.urlopen(request, timeout=60) as response:
            tokens = json.load(response)["input_tokens"]
        if not isinstance(tokens, int) or tokens <= 0:
            raise ValueError("token endpoint returned no positive integer count")
        results.append({"variant": row["name"], "payload_sha256": sha(content), "input_tokens": tokens})
        print(row["name"], tokens, flush=True)
        write_json(directory / "token-counts.json", {"model": model, "kind": "payload only", "counts": results})
    print("Smallest measured payload:", min(results, key=lambda r: r["input_tokens"])["variant"])


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="command", required=True)
    p = sub.add_parser("build")
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--symbols", type=Path, default=Path(os.environ.get("ISABELLE_SYMBOLS", "/opt/isabelle/etc/symbols")))
    p.add_argument("--chunk-bytes", type=int, default=CHUNK_BYTES)
    p.add_argument("--from-pack", type=Path, help="reuse exactly the previous candidate's frozen source digests")
    for name in ("verify", "bootstrap", "emit", "check-load", "snapshot", "count"):
        p = sub.add_parser(name)
        p.add_argument("directory", type=Path)
        if name == "emit":
            p.add_argument("part", type=int)
        if name == "check-load":
            p.add_argument("transcript", type=Path)
        if name == "snapshot":
            p.add_argument("output", type=Path)
        if name == "count":
            p.add_argument("--model", default="claude-opus-5")
            p.add_argument("--variants", nargs="+", help="count only these named variants")
    args = parser.parse_args()
    if args.command == "build":
        meta = build(args.output.resolve(), args.symbols, args.chunk_bytes, args.from_pack)
        print(report(meta))
    elif args.command == "count":
        count(args.directory, args.model, args.variants)
    elif args.command == "emit":
        meta = load(args.directory)
        if not 1 <= args.part <= len(meta["chunks"]):
            raise ValueError("invalid part number")
        text = checked_chunks(args.directory, meta)[args.part - 1]
        sys.stdout.write(envelope(meta, args.part, text))
    elif args.command == "check-load":
        print(json.dumps(check_load(args.directory, args.transcript)))
    else:
        meta = verify(args.directory)
        if args.command == "verify":
            print(f"OK: {len(meta['sources'])} original digests reconstructed exactly; {len(meta['chunks'])} chunks verified")
        elif args.command == "bootstrap":
            sys.stdout.write(bootstrap(args.directory.resolve(), meta))
        elif args.command == "snapshot":
            write_json(args.output, {"taken": meta["created"], "pack": meta["id"],
                                    "files": {r["path"]: r["source_sha1"] for r in meta["sources"]}})


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, KeyError) as error:
        sys.exit(f"base_pack: {error}")
