#!/usr/bin/env python3
"""Generate docs/INDEX.md, an index of every top-level declaration in src/.

Usage (from anywhere; stdlib only, Python >= 3.11):

    python3 -I scripts/gen_index.py          # rewrite docs/INDEX.md
    python3 -I scripts/gen_index.py --check  # exit 1 if docs/INDEX.md is stale

Both modes also check the source structure and the lakefile:
  * every src/*.lean file is a `lean_lib` in lakefile.toml and is listed in
    `defaultTargets` (so a bare `lake build` really builds everything);
  * every src/*.lean file starts with a `module` header (the project uses the
    module system, and a module cannot import a non-module file);
  * scripts/CheckAxioms.lean imports exactly the src modules (so CI's axiom
    check covers every library);
  * block comments are terminated (Lean comments nest, so a stray `/-`
    silently comments out the rest of a file);
  * `namespace`/`section`/`end` lines match.

The parser is line-based and only looks at column-0 commands, which is how
every file in this repo is written. It is not a Lean parser: if it reports
something odd, check the source by hand.
"""

from __future__ import annotations

import argparse
import difflib
import re
import sys
import tomllib
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LAKEFILE = ROOT / "lakefile.toml"
INDEX = ROOT / "docs" / "INDEX.md"
AXIOM_CHECK = ROOT / "scripts" / "CheckAxioms.lean"

KINDS = ("theorem", "lemma", "def", "abbrev", "instance", "structure", "class",
         "inductive", "opaque", "axiom")
MODIFIERS = ("private", "public", "protected", "noncomputable", "nonrec", "partial", "unsafe")

DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*"
    r"(?P<mods>(?:(?:" + "|".join(MODIFIERS) + r")\s+)*)"
    r"(?P<kind>" + "|".join(KINDS) + r")\b(?P<rest>.*)$"
)
IDENT_RE = re.compile(r"[^\s:(){}\[\]⦃⦄,]+")
NAMESPACE_RE = re.compile(r"^namespace\s+(\S+)\s*$")
# `@[expose] public section` (module system) opens the file-level scope; it stays open at EOF.
SECTION_RE = re.compile(
    r"^(?P<public>(?:@\[expose\]\s+)?public\s+)?(?:noncomputable\s+)?section(?:\s+(?P<name>\S+))?\s*$")
MUTUAL_RE = re.compile(r"^mutual\s*$")
END_RE = re.compile(r"^end(?:\s+(\S+))?\s*$")
MODULE_RE = re.compile(r"^module\b")
IMPORT_RE = re.compile(r"^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)")
# Lines allowed between a doc comment and the declaration it documents.
PREFIX_LINE_RE = re.compile(r"^(?:@\[.*\]|(?:omit|include|set_option|open)\b.*\bin)$")

SUMMARY_LEN = 110


class SourceError(Exception):
    pass


@dataclass
class DocComment:
    start: int  # offset of "/--"
    end: int    # offset just past "-/"
    text: str   # inner text


@dataclass
class Decl:
    name: str
    kind: str
    line: int
    summary: str
    root: bool  # declared outside any namespace


@dataclass
class ModuleInfo:
    module: str
    path: Path
    imports: list[str] = field(default_factory=list)
    namespaces: list[str] = field(default_factory=list)
    decls: list[Decl] = field(default_factory=list)


def strip_comments(text: str, rel: str) -> tuple[str, list[DocComment]]:
    """Blank out comments (keeping newlines and offsets); collect doc comments."""
    out = list(text)
    docs: list[DocComment] = []
    i, n = 0, len(text)
    while i < n:
        if text.startswith("/-", i):
            start, depth, j = i, 1, i + 2
            while j < n and depth:
                if text.startswith("/-", j):
                    depth, j = depth + 1, j + 2
                elif text.startswith("-/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            if depth:
                line = text.count("\n", 0, start) + 1
                raise SourceError(f"{rel}:{line}: unterminated block comment "
                                  "(Lean comments nest; everything after it is commented out)")
            if text.startswith("/--", start) and not text.startswith("/---", start):
                docs.append(DocComment(start, j, text[start + 3:j - 2]))
            for k in range(start, j):
                if out[k] != "\n":
                    out[k] = " "
            i = j
        elif text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j == -1 else j
            for k in range(i, j):
                out[k] = " "
            i = j
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            if j >= n:
                line = text.count("\n", 0, i) + 1
                raise SourceError(f"{rel}:{line}: unterminated string literal")
            i = j + 1
        else:
            i += 1
    return "".join(out), docs


def summarize(doc: str) -> str:
    para = re.split(r"\n\s*\n", doc.strip(), maxsplit=1)[0]
    s = " ".join(para.split())
    m = re.search(r"(?<=[.!?])\s", s)
    if m and m.start() <= SUMMARY_LEN:
        s = s[:m.start()]
    if len(s) > SUMMARY_LEN:
        s = s[:SUMMARY_LEN - 1].rstrip() + "…"
    return s.replace("|", "\\|")


def parse_module(module: str, path: Path) -> ModuleInfo:
    rel = path.relative_to(ROOT).as_posix()
    text = path.read_text(encoding="utf-8")
    code, docs = strip_comments(text, rel)
    lines = code.split("\n")
    offsets = [0]
    for ln in lines[:-1]:
        offsets.append(offsets[-1] + len(ln) + 1)

    info = ModuleInfo(module, path)
    first = next((ln.strip() for ln in lines if ln.strip()), "")
    if not MODULE_RE.match(first):
        raise SourceError(f"{rel}:1: missing `module` header (every file uses the module system; "
                          "the header is the copyright comment, `module`, then `public import`s)")
    scopes: list[tuple[str, str]] = []  # (kind, name) with kind in ns/section/public/mutual
    doc_idx = 0
    last_doc: DocComment | None = None

    def current_ns() -> str:
        return ".".join(name for kind, name in scopes if kind == "ns")

    for idx, raw in enumerate(lines):
        lineno = idx + 1
        line = raw.rstrip()
        while doc_idx < len(docs) and docs[doc_idx].end <= offsets[idx]:
            last_doc = docs[doc_idx]
            doc_idx += 1
        if not line or line[0].isspace():
            continue

        if m := IMPORT_RE.match(line):
            info.imports.append(m.group(1))
            continue
        if m := NAMESPACE_RE.match(line):
            scopes.extend(("ns", part) for part in m.group(1).split("."))
            ns = current_ns()
            if ns not in info.namespaces:
                info.namespaces.append(ns)
            continue
        if m := SECTION_RE.match(line):
            scopes.append(("public" if m.group("public") else "section", m.group("name") or ""))
            continue
        if MUTUAL_RE.match(line):
            scopes.append(("mutual", ""))
            continue
        if m := END_RE.match(line):
            parts = m.group(1).split(".") if m.group(1) else [""]
            for part in reversed(parts):
                if not scopes:
                    raise SourceError(f"{rel}:{lineno}: `{line}` with no open scope")
                kind, name = scopes.pop()
                if name != part:
                    opened = f"{kind} {name}".strip()
                    raise SourceError(f"{rel}:{lineno}: `{line}` closes `{opened}` "
                                      "(duplicated or missing section/namespace line?)")
            continue

        m = DECL_RE.match(line)
        if not m:
            continue
        kind = m.group("kind")
        rest = m.group("rest").strip()
        j = idx + 1
        while not rest and j < len(lines):  # name on the following line
            rest, j = lines[j].strip(), j + 1
        if kind == "instance":
            rest = re.sub(r"^\(priority\s*:=[^)]*\)\s*", "", rest)
        nm = IDENT_RE.match(rest)
        if not nm or nm.group(0) == "where":
            continue  # anonymous instance
        name = nm.group(0)
        ns = "" if name.startswith("_root_.") else current_ns()
        name = name.removeprefix("_root_.")
        full = f"{ns}.{name}" if ns else name
        if "private" in m.group("mods").split():
            kind = "private " + kind

        summary = ""
        if last_doc is not None:
            between = code[last_doc.end:offsets[idx]].split("\n")
            if all(not s.strip() or PREFIX_LINE_RE.match(s.strip()) for s in between):
                summary = summarize(last_doc.text)
        info.decls.append(Decl(full, kind, lineno, summary, root=not ns))

    scopes = [s for s in scopes if s != ("public", "")]  # file-level public section
    if scopes:
        open_ = ", ".join(f"{k} {n}".strip() for k, n in scopes)
        print(f"warning: {rel}: scopes still open at end of file: {open_}", file=sys.stderr)
    return info


def load_modules() -> tuple[list[ModuleInfo], list[str]]:
    """Parse the lakefile and every source file; return modules and problems."""
    problems: list[str] = []
    cfg = tomllib.loads(LAKEFILE.read_text(encoding="utf-8"))
    src = ROOT / cfg.get("srcDir", ".")
    libs = cfg.get("lean_lib", [])
    lib_names = [lib["name"] for lib in libs]
    for lib in libs:
        extra = sorted(set(lib) - {"name"})
        if extra:
            problems.append(f"lakefile.toml: lean_lib {lib['name']} sets {extra}; "
                            "scripts/gen_index.py assumes one root module per lib")
    defaults = set(cfg.get("defaultTargets", []))

    files = sorted(p for p in src.rglob("*.lean") if ".lake" not in p.parts)
    modules: dict[str, Path] = {
        ".".join(p.relative_to(src).with_suffix("").parts): p for p in files
    }
    for mod in modules:
        if mod not in lib_names:
            problems.append(f"lakefile.toml: no [[lean_lib]] for src module {mod}")
    for name in lib_names:
        if name not in modules:
            problems.append(f"lakefile.toml: lean_lib {name} has no source file")
        if name not in defaults:
            problems.append(f"lakefile.toml: lean_lib {name} missing from defaultTargets")

    check_rel = AXIOM_CHECK.relative_to(ROOT)
    if AXIOM_CHECK.exists():
        checked = {m.group(1) for line in AXIOM_CHECK.read_text(encoding="utf-8").splitlines()
                   if (m := IMPORT_RE.match(line))}
        for mod in sorted(modules.keys() - checked):
            problems.append(f"{check_rel}: does not import src module {mod}")
        for mod in sorted(checked - modules.keys()):
            problems.append(f"{check_rel}: imports {mod}, which is not a src module")
    else:
        problems.append(f"{check_rel} is missing")

    infos: list[ModuleInfo] = []
    for mod, path in modules.items():
        try:
            infos.append(parse_module(mod, path))
        except SourceError as e:
            problems.append(str(e))
    return infos, problems


def topo_order(infos: list[ModuleInfo]) -> list[ModuleInfo]:
    """Order modules so each comes after its project imports (ties: by name)."""
    by_name = {i.module: i for i in infos}
    deps = {i.module: {d for d in i.imports if d in by_name} for i in infos}
    order: list[ModuleInfo] = []
    done: set[str] = set()
    while len(order) < len(infos):
        ready = sorted(m for m in deps if m not in done and deps[m] <= done)
        if not ready:  # cycle; Lean would reject it anyway
            ready = sorted(m for m in deps if m not in done)[:1]
        done.add(ready[0])
        order.append(by_name[ready[0]])
    return order


def render(infos: list[ModuleInfo]) -> str:
    ordered = topo_order(infos)
    project = {i.module for i in infos}
    total = sum(len(i.decls) for i in infos)
    out = [
        "# Declaration index",
        "",
        "<!-- Generated by scripts/gen_index.py. Do not edit by hand; regenerate with",
        "     python3 -I scripts/gen_index.py -->",
        "",
        f"{total} top-level declarations in {len(infos)} files, with full names, kinds,",
        "1-based line numbers and the first sentence of each doc comment. Grep it",
        "rather than reading it whole. Files are listed so each comes after its imports.",
        "",
        "## Files",
        "",
        "| File | Project imports | Namespaces opened | Decls |",
        "|---|---|---|---|",
    ]
    for i in ordered:
        rel = i.path.relative_to(ROOT).as_posix()
        imports = ", ".join(sorted(d for d in i.imports if d in project)) or "—"
        nss = [f"`{ns}`" for ns in i.namespaces]
        if any(d.root for d in i.decls):
            nss.append("root")
        nss = ", ".join(nss) or "—"
        out.append(f"| [{i.path.name}](../{rel}) | {imports} | {nss} | {len(i.decls)} |")
    for i in ordered:
        rel = i.path.relative_to(ROOT).as_posix()
        out += ["", f"## {i.path.name}", "",
                "| Name | Kind | Location | Summary |", "|---|---|---|---|"]
        for d in i.decls:
            loc = f"[{i.path.name}:{d.line}](../{rel}#L{d.line})"
            out.append(f"| `{d.name}` | {d.kind} | {loc} | {d.summary} |")
    return "\n".join(out) + "\n"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--check", action="store_true",
                    help="do not write; exit 1 if docs/INDEX.md is out of date")
    args = ap.parse_args()

    infos, problems = load_modules()
    for p in problems:
        print(f"error: {p}", file=sys.stderr)
    if problems:
        return 1

    new = render(infos)
    if args.check:
        old = INDEX.read_text(encoding="utf-8") if INDEX.exists() else ""
        if old != new:
            diff = difflib.unified_diff(old.splitlines(), new.splitlines(),
                                        "docs/INDEX.md (committed)", "docs/INDEX.md (expected)",
                                        lineterm="", n=0)
            print("\n".join(list(diff)[:60]), file=sys.stderr)
            print("error: docs/INDEX.md is out of date; run "
                  "`python3 -I scripts/gen_index.py` and commit the result", file=sys.stderr)
            return 1
        print(f"docs/INDEX.md is up to date ({sum(len(i.decls) for i in infos)} declarations)")
        return 0

    INDEX.parent.mkdir(exist_ok=True)
    INDEX.write_text(new, encoding="utf-8")
    print(f"wrote {INDEX.relative_to(ROOT)} ({sum(len(i.decls) for i in infos)} declarations)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
