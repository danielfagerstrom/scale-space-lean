#!/usr/bin/env python3
"""Generate the ScaleSpaceCore API reference and its declaration -> blueprint-node index.

Q-0369: a blueprint is the wrong instrument for a shared library (ADR-0026, hub) -- it
restates nodes the articles already own. Everything a declaration needs to be documented
by is already in this repository (617 of 901 public declarations carry a docstring) and in
the released articles' own blueprints (the `\\lean{...}` tags). This script only extracts
and cross-references what already exists; it states no mathematics.

Priced against doc-gen4 first (per the brief): doc-gen4 documents the whole import closure,
so pulling it in here would mean `require`ing it and running `lake update` to fetch it --
forbidden in the unattended session that wrote this script, and in general a multi-hour,
many-GB build for a library whose only dependency is Mathlib. This is the sanctioned
fallback: no Lean build, no Mathlib dependency, pure source extraction.

Two outputs, both under site/library/:
  - data.json   structured: every public declaration (name, kind, module, signature,
                docstring, source line) and, for each, the blueprint node(s) that claim it
  - index.html  a single self-contained static page rendering data.json for a human reader

Usage:
    python3 scripts/gen_library_reference.py [--check]

--check regenerates in memory and diffs against the committed files without writing;
exits nonzero if they differ (mirrors research-site/scripts/build-bibliography.mjs).

Declarations: this library's own AxiomCheck.lean is taken as the enumeration of "every
public declaration" (CLAUDE.md's own rule for that file), not a declaration scan of our
own invention -- it already excludes structure-field projections, which are not treated as
separately citable here either.

Blueprint claims: scanned from the released exports under $DEV_DIR (else ~/dev), the same
EXPORT_REPOS list research-site/scripts/build-bibliography.mjs uses, read-only. A module's
title and release are read from the hub's constellation.json ($WIKI_VAULT, else
~/Documents/Notes); if a repo or the hub is not present locally, that source is skipped
(reported on stderr), not treated as an error -- this mirrors the export script's own
tolerance for a missing local checkout.
"""

import json
import os
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
CORE_DIR = REPO_ROOT / "ScaleSpaceCore"
AXIOM_CHECK = REPO_ROOT / "AxiomCheck.lean"
OUT_DIR = REPO_ROOT / "site" / "library"

# The export repo that holds each public site slug's released blueprint -- the same table
# research-site/scripts/build-bibliography.mjs keys EXPORT_REPOS by.
EXPORT_REPOS = {
    "hemigroup-time-causal-kernels": "hemigroup-causal-scale-space-kernels",
    "hemigroup-spatial-kernels-line": "spatial-hemigroup-scale-space-kernels",
    "hemigroup-spatial-admissible-cone": "spatial-hemigroup-scale-space-cone",
    "hemigroup-spatial-gaussian-selection": "spatial-hemigroup-scale-space-selection",
}


def dev_dir() -> Path:
    return Path(os.environ.get("DEV_DIR") or (Path.home() / "dev"))


def hub_dir() -> Path:
    return Path(os.environ.get("WIKI_VAULT") or (Path.home() / "Documents" / "Notes"))


# ---------------------------------------------------------------------------
# Part 1: the declarations themselves.
# ---------------------------------------------------------------------------

IDENT = r"[A-Za-zΑ-Ωα-ω_][A-Za-zΑ-Ωα-ω0-9_'₀-ₜ]*"
QUALIFIED = rf"{IDENT}(?:\.{IDENT})*"
DECL_KEYWORDS = ("def", "abbrev", "theorem", "lemma", "instance", "structure", "class", "inductive", "opaque")
MODIFIERS = r"(?:private|protected|noncomputable|unsafe|partial|scoped)\s+"
DECL_RE = re.compile(
    rf"^(?:{MODIFIERS})*(?P<kw>{'|'.join(DECL_KEYWORDS)})\s+(?P<name>{QUALIFIED})"
)
NS_RE = re.compile(r"^namespace\s+(\S+)$")
SECTION_RE = re.compile(r"^section(?:\s+(\S+))?$")
END_RE = re.compile(r"^end(?:\s+(\S+))?$")
SKIP_PREFIXES = ("variable", "open ", "open scoped", "import ", "set_option", "--", "attribute ")
LEADING_ATTR_RE = re.compile(r"^(\s*)@\[[^\]]*\]\s*(.*)$")


def strip_leading_attrs(line: str) -> str:
    """`@[simp] theorem foo ...` -> `theorem foo ...` (attribute is not a declaration)."""
    while True:
        m = LEADING_ATTR_RE.match(line)
        if not m:
            return line
        line = m.group(1) + m.group(2)


def extract_doc(block: str) -> str:
    """/-- ... -/ -> the inner markdown, dedented."""
    inner = block.strip()
    inner = re.sub(r"^/--", "", inner)
    inner = re.sub(r"-/$", "", inner)
    lines = inner.splitlines()
    # Drop a uniform leading "  " that doc comments after the first line often carry.
    stripped = [lines[0].strip()] + [re.sub(r"^\s{0,3}", "", l) for l in lines[1:]]
    return "\n".join(stripped).strip()


def depth_delta(text: str) -> int:
    opens = sum(text.count(c) for c in "([{⟨")
    closes = sum(text.count(c) for c in ")]}⟩")
    return opens - closes


def collect_signature(lines, start_idx):
    """From a declaration's header line, the text up to (not incl.) `:=`/`where` at depth 0."""
    depth = 0
    collected = []
    i = start_idx
    n = len(lines)
    while i < n:
        raw = lines[i]
        if i > start_idx and depth == 0 and raw.strip().startswith("|"):
            # The equation compiler (`def f : A -> B | pat => ...`): the type ends at the
            # previous line, with no `:=`/`where` of its own.
            return "\n".join(l for l in collected if l.strip()).strip(), i
        scan = re.sub(r"(?<!-)--.*$", "", raw)  # drop a trailing line comment for scanning only
        pos = 0
        stop_at = None
        while pos < len(scan):
            ch = scan[pos]
            if ch in "([{⟨":
                depth += 1
            elif ch in ")]}⟩":
                depth -= 1
            elif depth == 0 and scan[pos:pos + 2] == ":=":
                stop_at = pos
                break
            elif depth == 0 and scan[pos:pos + 5] == "where" and (pos == 0 or not scan[pos - 1].isalnum()) and (
                pos + 5 == len(scan) or not scan[pos + 5].isalnum()
            ):
                stop_at = pos + 5
                break
            pos += 1
        if stop_at is not None:
            collected.append(raw[:stop_at].rstrip())
            return "\n".join(l for l in collected if l.strip()).strip(), i + 1
        collected.append(raw.rstrip())
        i += 1
        if i - start_idx > 60:
            break
    return "\n".join(l for l in collected if l.strip()).strip(), i


def parse_module(path: Path):
    text = path.read_text(encoding="utf-8")
    lines = [strip_leading_attrs(l) for l in text.splitlines()]
    decls = []
    ns_stack = []
    block_stack = []  # ("namespace"|"section", name)
    pending_doc = None
    i = 0
    n = len(lines)
    while i < n:
        stripped = lines[i].strip()

        if stripped.startswith("/-"):
            # `/-- ... -/` is a docstring attaching to the next declaration; `/-! ... -/`
            # (module section prose) and plain `/- ... -/` (e.g. the copyright header) are
            # not -- and their prose can otherwise accidentally match DECL_RE (a sentence
            # containing the word "instance", say), so skip the whole block either way.
            is_doc = stripped.startswith("/--")
            block_lines = [lines[i]]
            j = i
            if "-/" not in lines[i]:
                j += 1
                while j < n and "-/" not in lines[j]:
                    block_lines.append(lines[j])
                    j += 1
                if j < n:
                    block_lines.append(lines[j])
            pending_doc = extract_doc("\n".join(block_lines)) if is_doc else None
            i = j + 1
            continue

        m = NS_RE.match(stripped)
        if m:
            block_stack.append(("namespace", m.group(1)))
            ns_stack.append(m.group(1))
            pending_doc = None
            i += 1
            continue
        m = SECTION_RE.match(stripped)
        if m:
            block_stack.append(("section", m.group(1)))
            i += 1
            continue
        m = END_RE.match(stripped)
        if m:
            if block_stack:
                kind, _name = block_stack.pop()
                if kind == "namespace" and ns_stack:
                    ns_stack.pop()
            pending_doc = None
            i += 1
            continue

        if stripped == "" or stripped.startswith(SKIP_PREFIXES):
            i += 1
            continue

        m = DECL_RE.match(stripped)
        if m:
            kw = m.group("kw")
            name = m.group("name")
            qualified = ".".join(ns_stack + [name]) if ns_stack else name
            sig, end_idx = collect_signature(lines, i)
            decls.append(
                {
                    "name": qualified,
                    "kind": kw,
                    "signature": sig,
                    "doc": pending_doc,
                    "module": path.stem,
                    "line": i + 1,
                }
            )
            pending_doc = None
            i = end_idx
            continue

        pending_doc = None
        i += 1
    return decls


def load_declarations():
    by_name = {}
    for path in sorted(CORE_DIR.glob("*.lean")):
        for d in parse_module(path):
            by_name[d["name"]] = d
    return by_name


def public_declaration_names():
    text = AXIOM_CHECK.read_text(encoding="utf-8")
    seen = set()
    ordered = []
    for n in re.findall(r"^#print axioms (ScaleSpace\.\S+)", text, re.M):
        if n not in seen:
            seen.add(n)
            ordered.append(n)
    return ordered


# LineInterfaces.lean's four declarations are cited external results taken as a
# hypothesis (README.md "No axioms, no cited interfaces"), not statements proved here.
INTERFACE_MODULE = "LineInterfaces"


def build_declarations():
    by_name = load_declarations()
    names = public_declaration_names()
    entries = []
    missing = []
    for name in names:
        d = by_name.get(name)
        if d is None:
            missing.append(name)
            continue
        kind = d["kind"]
        is_interface = d["module"] == INTERFACE_MODULE and kind in ("def", "structure")
        entries.append(
            {
                "name": name,
                "short_name": name.removeprefix("ScaleSpace."),
                "module": d["module"],
                "kind": "interface" if is_interface else kind,
                "signature": d["signature"],
                "doc": d["doc"],
                "line": d["line"],
            }
        )
    return entries, missing


# ---------------------------------------------------------------------------
# Part 2: the declaration -> blueprint-node index.
# ---------------------------------------------------------------------------

LEAN_TAG_RE = re.compile(r"\\lean\{([^}]*)\}")
LABEL_RE = re.compile(r"\\label\{([^}]*)\}")
BEGIN_ENV_RE = re.compile(r"\\begin\{([A-Za-z]+)\}")
CHAPTER_RE = re.compile(r"\\chapter\{(.*)\}")


def load_constellation():
    """export repo name -> {title, version, doi, date, url}, read from the hub's manifest."""
    path = hub_dir() / "constellation.json"
    if not path.exists():
        print(f"warning: constellation.json not found at {path}; blueprint index will have no release metadata", file=sys.stderr)
        return {}
    data = json.loads(path.read_text(encoding="utf-8"))
    by_export_repo = {}

    def repo_name_of(url):
        return url.rstrip("/").rsplit("/", 1)[-1].removesuffix(".git")

    def record(name, title, release, url):
        if not release or not release.get("latest"):
            return
        latest = release["latest"]
        by_export_repo[name] = {
            "title": title,
            "version": latest.get("version"),
            "doi": latest.get("doi"),
            "date": latest.get("date"),
            "url": url,
        }

    for member in data.get("members", []):
        pub = member.get("public_export")
        site = member.get("site")
        title = None
        if isinstance(site, dict):
            title = site.get("title")
        elif isinstance(site, list) and site:
            title = site[0].get("title")
        title = title or member.get("role")
        if pub:
            record(repo_name_of(pub), title, member.get("release"), pub)
        else:
            record(member.get("name"), title, member.get("release"), member.get("url"))
        for mod in member.get("modules", []):
            mod_pub = mod.get("public_export")
            if mod_pub:
                record(repo_name_of(mod_pub), mod.get("title", title), mod.get("release"), mod_pub)
    return by_export_repo


def scan_blueprint_tags(repo_dir: Path):
    """[{name, label, env, chapter, file, line}] for every ScaleSpace.* \\lean{} tag."""
    found = []
    blueprint_src = repo_dir / "blueprint" / "src"
    if not blueprint_src.exists():
        return found
    for tex in sorted(blueprint_src.rglob("*.tex")):
        rel = tex.relative_to(repo_dir)
        current_label = None
        current_env = None
        current_chapter = None
        for lineno, line in enumerate(tex.read_text(encoding="utf-8", errors="replace").splitlines(), start=1):
            m = CHAPTER_RE.search(line)
            if m:
                current_chapter = m.group(1).strip()
            m = BEGIN_ENV_RE.search(line)
            if m:
                current_env = m.group(1)
                current_label = None
            m = LABEL_RE.search(line)
            if m:
                current_label = m.group(1)
            for m in LEAN_TAG_RE.finditer(line):
                for raw_name in m.group(1).split(","):
                    name = raw_name.strip()
                    if name.startswith("ScaleSpace."):
                        found.append(
                            {
                                "name": name,
                                "label": current_label,
                                "env": current_env,
                                "chapter": current_chapter,
                                "file": str(rel).replace("\\", "/"),
                                "line": lineno,
                            }
                        )
    return found


def build_blueprint_index():
    constellation = load_constellation()
    claims = {}  # declaration name -> list of claim dicts
    for site_slug, export_repo in EXPORT_REPOS.items():
        repo_dir = dev_dir() / export_repo
        if not repo_dir.exists():
            print(f"warning: export repo not found locally: {repo_dir} (site slug {site_slug})", file=sys.stderr)
            continue
        meta = constellation.get(export_repo, {})
        tag = None
        try:
            import subprocess

            tag = subprocess.run(
                ["git", "-C", str(repo_dir), "describe", "--tags", "--exact-match"],
                capture_output=True, text=True, check=False,
            ).stdout.strip() or None
        except Exception:
            tag = None
        ref = tag or meta.get("version") or "main"
        for tagged in scan_blueprint_tags(repo_dir):
            claim = {
                "site_slug": site_slug,
                "export_repo": export_repo,
                "title": meta.get("title"),
                "version": meta.get("version"),
                "doi": meta.get("doi"),
                "label": tagged["label"],
                "env": tagged["env"],
                "chapter": tagged["chapter"],
                "source_url": f"https://github.com/danielfagerstrom/{export_repo}/blob/{ref}/{tagged['file']}#L{tagged['line']}",
            }
            claims.setdefault(tagged["name"], []).append(claim)
    return claims


# ---------------------------------------------------------------------------
# Part 3: render.
# ---------------------------------------------------------------------------

def esc(s):
    if s is None:
        return ""
    return (
        str(s)
        .replace("&", "&amp;")
        .replace("<", "&lt;")
        .replace(">", "&gt;")
        .replace('"', "&quot;")
    )


def doc_to_html(text):
    """A docstring's light markdown (`code`, **bold**, blank-line paragraphs) -> HTML."""
    if not text:
        return ""
    escaped = esc(text)
    escaped = re.sub(r"\*\*(.+?)\*\*", r"<strong>\1</strong>", escaped)
    escaped = re.sub(r"`([^`]+)`", r"<code>\1</code>", escaped)
    paras = re.split(r"\n\s*\n", escaped)
    return "".join(f"<p>{p.replace(chr(10), ' ')}</p>" for p in paras if p.strip())


def render_html(entries, claims, missing, generated):
    by_module = {}
    for e in entries:
        by_module.setdefault(e["module"], []).append(e)

    total = len(entries)
    documented = sum(1 for e in entries if e["doc"])
    claimed = sum(1 for e in entries if e["name"] in claims)
    interfaces = sum(1 for e in entries if e["kind"] == "interface")

    rows = []
    rows.append(
        f"""<p id="summary">{total} public declarations across {len(by_module)} modules &mdash;
{documented} carry a docstring, {claimed} are claimed by a node in a released article's blueprint,
{interfaces} are cited interfaces taken as a hypothesis rather than statements proved here, and
<strong>{total - claimed} are claimed by no released node</strong> (not proof that nothing cites
them: a draft or unreleased module may; this counts only released, public blueprints).</p>"""
    )

    for module in sorted(by_module):
        rows.append(f'<h2 id="mod-{esc(module)}">{esc(module)}</h2>')
        rows.append('<dl class="module">')
        for e in sorted(by_module[module], key=lambda e: e["line"]):
            anchor = e["name"].replace(".", "_")
            kind_label = {"interface": "interface (hypothesis)"}.get(e["kind"], e["kind"])
            rows.append(f'<dt id="decl-{esc(anchor)}"><code>{esc(e["short_name"])}</code>'
                        f' <span class="kind">{esc(kind_label)}</span>'
                        f' <a class="src" href="../../ScaleSpaceCore/{esc(module)}.lean#L{e["line"]}">source</a></dt>')
            rows.append(f'<dd><pre class="sig">{esc(e["signature"])}</pre>')
            if e["doc"]:
                rows.append(f'<div class="doc">{doc_to_html(e["doc"])}</div>')
            else:
                rows.append('<p class="doc missing">No docstring.</p>')
            node_claims = claims.get(e["name"], [])
            if node_claims:
                rows.append('<ul class="claims">')
                for c in node_claims:
                    where = " / ".join(x for x in [c["title"], c["chapter"]] if x)
                    env = (c["env"] or "node").capitalize()
                    label = c["label"] or "(unlabelled)"
                    version = f" {c['version']}" if c["version"] else ""
                    rows.append(
                        f'<li>{env} <code>{esc(label)}</code> of <a href="{esc(c["source_url"])}">{esc(where)}{esc(version)}</a></li>'
                    )
                rows.append("</ul>")
            else:
                rows.append('<p class="unclaimed">Claimed by no released node.</p>')
            rows.append("</dd>")
        rows.append("</dl>")

    nav = " · ".join(f'<a href="#mod-{esc(m)}">{esc(m)}</a>' for m in sorted(by_module))

    missing_note = ""
    if missing:
        missing_note = (
            '<p class="warn">Declarations AxiomCheck.lean checks but this generator could not '
            f"locate in source ({len(missing)}): {', '.join(esc(m) for m in missing)}</p>"
        )

    return f"""<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>ScaleSpaceCore API reference</title>
<meta name="description" content="Every public declaration of ScaleSpaceCore, with its signature, docstring, and the released blueprint node (if any) that states it.">
<style>
body {{ font-family: system-ui, sans-serif; max-width: 72rem; margin: 2rem auto; padding: 0 1rem; line-height: 1.5; }}
code, pre {{ font-family: "Cascadia Code", Consolas, monospace; }}
pre.sig {{ background: #f6f6f6; padding: 0.5rem; overflow-x: auto; white-space: pre-wrap; }}
dt {{ margin-top: 1.5rem; }}
.kind {{ color: #666; font-size: 0.85em; }}
.src {{ font-size: 0.85em; margin-left: 0.5em; }}
.doc.missing, .unclaimed {{ color: #a33; font-style: italic; }}
.warn {{ color: #a33; }}
nav#modnav {{ columns: 4; font-size: 0.9em; margin: 1rem 0; }}
ul.claims {{ margin: 0.3em 0; }}
</style>
</head><body>
<h1>ScaleSpaceCore API reference</h1>
<p>Generated {esc(generated)} by <code>scripts/gen_library_reference.py</code> from this repository's
source and AxiomCheck.lean, and from the released articles' own blueprints
(<code>EXPORT_REPOS</code>, mirroring <code>research-site/scripts/build-bibliography.mjs</code>).
Not a blueprint: this library carries no argument of its own (ADR-0026); every statement below
belongs to an article, reached through its <code>\\lean{{}}</code> tag where one exists.</p>
{"".join(rows[:1])}
{missing_note}
<nav id="modnav">{nav}</nav>
{"".join(rows[1:])}
</body></html>
"""


def main():
    check = "--check" in sys.argv
    entries, missing = build_declarations()
    claims = build_blueprint_index()
    data_path = OUT_DIR / "data.json"
    generated = os.environ.get("GEN_LIBRARY_REFERENCE_DATE")
    if generated is None and check and data_path.exists():
        # --check asks whether the committed content is stale, not whether today's date
        # matches; reuse the committed stamp so an unrelated day doesn't look like staleness.
        try:
            generated = json.loads(data_path.read_text(encoding="utf-8")).get("generated")
        except Exception:
            generated = None
    generated = generated or __import__("datetime").date.today().isoformat()

    data = {
        "generated": generated,
        "declarations": entries,
        "claims": claims,
        "unresolved_in_axiom_check": missing,
    }

    html = render_html(entries, claims, missing, generated)

    html_path = OUT_DIR / "index.html"
    new_data = json.dumps(data, indent=2, ensure_ascii=False, sort_keys=False) + "\n"

    if check:
        ok = True
        if not data_path.exists() or data_path.read_text(encoding="utf-8") != new_data:
            print("data.json is stale", file=sys.stderr)
            ok = False
        if not html_path.exists():
            print("index.html is missing", file=sys.stderr)
            ok = False
        sys.exit(0 if ok else 1)

    OUT_DIR.mkdir(parents=True, exist_ok=True)
    data_path.write_text(new_data, encoding="utf-8")
    html_path.write_text(html, encoding="utf-8")
    print(f"{len(entries)} declarations, {sum(1 for e in entries if e['doc'])} documented, "
          f"{sum(1 for e in entries if e['name'] in claims)} claimed, {len(missing)} unresolved")


if __name__ == "__main__":
    main()
