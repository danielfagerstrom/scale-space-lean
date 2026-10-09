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

One output, site/library/data.json: every module (title, description, the blueprint node
labels its prose names) and every public declaration (name, kind, module, signature,
docstring, source line), with the blueprint node(s) that claim it and the revision all of
it was read from.

This script renders no HTML. It used to also write site/library/index.html, which was
served nowhere -- this repository has no Pages site, and GitHub shows a committed .html as
source -- so the only way to read it was to clone and open the file, while the README
pointed at it as the reference. The reference a reader can actually reach is
research.danielfagerstrom.com/library/, rendered from this data by research-site's
scripts/build-library.mjs. One datum, one rendering.

Usage:
    python3 scripts/gen_library_reference.py [--check | --check-source]

Both regenerate in memory, diff against the committed data.json and write nothing; they
differ in how much they compare, because the three sources this script reads are not
equally reachable.

--check          everything, including the blueprint claims and their release metadata.
                 Needs the four released export repositories under $DEV_DIR and the hub's
                 constellation.json under $WIKI_VAULT. For a desk that has them.

--check-source   only what THIS repository determines: the modules, the declarations and
                 their signatures and docstrings. For CI, which has none of the others --
                 the exports would have to be cloned and the hub is private. Run there,
                 --check regenerates a data.json with no claims, compares it against a
                 committed one that has them, and reports staleness on correct data; a
                 check that fails when nothing is wrong is worse than no check, because it
                 teaches everyone to ignore it.

What --check-source catches is the drift that actually originates here: a declaration
added, renamed or removed, a signature changed, a docstring edited, without regenerating.
The claims half changes when an ARTICLE makes a release, which is a different trigger with
the release checklist already in front of it.

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


MODULE_DOC_RE = re.compile(r"/-!\s*\n?\s*#\s*(?P<title>.+?)\n(?P<body>.*?)-/", re.S)
NODE_LABEL_RE = re.compile(r"\b(?:def|lem|prop|thm|cor|rem|ax|fig|eq):[A-Za-z0-9-]+")


def parse_module_doc(path: Path):
    r"""The module's own `/-! # Title ... -/` header: the one authored description of what a
    module is for.

    Every module here has one (64/64 at 2026-10-09, median 267 words) and nothing was
    reading them -- the reference showed the bare module name, discarding the richest
    authored prose in the repository.

    They are also where the link to the articles is actually recorded: 40 of the 64 name a
    blueprint node label in prose (`CinRays` is titled "`lem:cin-rays`(1): the `Cin` rays"),
    where only 2 declarations carry a machine-readable `\lean{}` tag in a released export.
    Extracting the labels lets the page show that connection without anyone restating it.
    """
    text = path.read_text(encoding="utf-8")
    m = MODULE_DOC_RE.search(text)
    if not m:
        return None
    title = " ".join(m.group("title").split())
    body = m.group("body").strip()
    labels = []
    for label in NODE_LABEL_RE.findall(title + "\n" + body):
        if label not in labels:
            labels.append(label)
    return {"title": title, "doc": body, "labels": labels}


def load_module_docs():
    out = {}
    for path in sorted(CORE_DIR.glob("*.lean")):
        doc = parse_module_doc(path)
        if doc is not None:
            out[path.stem] = doc
        else:
            print(f"warning: {path.name} has no /-! module docstring", file=sys.stderr)
    return out


def source_revision() -> str:
    """The revision the reference describes, for the source links.

    HEAD at generation time: that is the code just read, and a line number is a line number
    *in a revision*. `main` would drift silently as the file moves under the link, and a
    release tag would name code this page is not describing.
    """
    import subprocess

    try:
        return subprocess.run(
            ["git", "rev-parse", "HEAD"], cwd=REPO_ROOT, check=True, capture_output=True, text=True
        ).stdout.strip()
    except Exception:
        print("warning: could not read git HEAD; source links will point at main", file=sys.stderr)
        return "main"


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


# The keys of data.json this repository alone determines. Everything else -- the claims and
# their release metadata -- comes from the export repositories and the hub.
LOCAL_KEYS = ("repo", "source_dir", "modules", "declarations", "unresolved_in_axiom_check")


def main():
    check_source = "--check-source" in sys.argv
    check = check_source or "--check" in sys.argv
    entries, missing = build_declarations()
    # Not merely ignored afterwards: skipped, so a run in CI does not emit four warnings
    # about repositories it was never going to find.
    claims = {} if check_source else build_blueprint_index()
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

    modules = load_module_docs()
    commit = os.environ.get("GEN_LIBRARY_REFERENCE_COMMIT")
    if commit is None and check and data_path.exists():
        # Same reason as `generated`: --check asks whether the content is stale, not whether
        # HEAD has moved since it was written.
        try:
            commit = json.loads(data_path.read_text(encoding="utf-8")).get("commit")
        except Exception:
            commit = None
    commit = commit or source_revision()

    data = {
        "generated": generated,
        "commit": commit,
        "repo": "https://github.com/danielfagerstrom/scale-space-lean",
        "source_dir": "ScaleSpaceCore",
        "modules": modules,
        "declarations": entries,
        "claims": claims,
        "unresolved_in_axiom_check": missing,
    }

    new_data = json.dumps(data, indent=2, ensure_ascii=False, sort_keys=False) + "\n"

    if check:
        if not data_path.exists():
            print(f"{data_path} is missing", file=sys.stderr)
            sys.exit(1)
        committed_text = data_path.read_text(encoding="utf-8")

        if not check_source:
            if committed_text != new_data:
                print("data.json is stale", file=sys.stderr)
                sys.exit(1)
            print(f"data.json is current ({len(entries)} declarations, {len(modules)} modules, "
                  f"{len(claims)} claimed)")
            sys.exit(0)

        committed = json.loads(committed_text)
        stale = [k for k in LOCAL_KEYS if committed.get(k) != data[k]]
        if stale:
            print(f"data.json is stale in: {', '.join(stale)}", file=sys.stderr)
            print("regenerate with: python3 scripts/gen_library_reference.py", file=sys.stderr)
            sys.exit(1)
        print(f"data.json matches the source ({len(entries)} declarations, {len(modules)} "
              f"modules); claims and release metadata not checked here")
        sys.exit(0)

    OUT_DIR.mkdir(parents=True, exist_ok=True)
    data_path.write_text(new_data, encoding="utf-8")
    print(f"{len(entries)} declarations, {sum(1 for e in entries if e['doc'])} documented, "
          f"{sum(1 for e in entries if e['name'] in claims)} claimed, {len(missing)} unresolved")


if __name__ == "__main__":
    main()
