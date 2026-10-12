# R2-2 (solo lectura): parser heuristico de declaraciones de RPP y FOL + grafo de dependencias por constante.
# Escribe JSON en el scratchpad; no toca ningun repositorio.
import os, re, json, sys, collections

RPP = r"E:/dropbox/github/lean4/ROBINSON_PlusPlus"
FOL = r"E:/dropbox/github/lean4/FOL"
OUT = os.path.dirname(os.path.abspath(__file__))

def strip_comments(src):
    out = []; i = 0; depth = 0; n = len(src); instr = False
    while i < n:
        c = src[i]
        if depth == 0 and instr:
            out.append(c)
            if c == '\\' and i + 1 < n:
                out.append(src[i+1]); i += 2; continue
            if c == '"': instr = False
            i += 1; continue
        if depth == 0 and c == '"':
            instr = True; out.append(c); i += 1; continue
        if src.startswith("/-", i):
            depth += 1; i += 2; continue
        if depth > 0 and src.startswith("-/", i):
            depth -= 1; i += 2; continue
        if depth > 0:
            if c == "\n": out.append("\n")
            i += 1; continue
        if src.startswith("--", i):
            j = src.find("\n", i)
            if j < 0: break
            i = j; continue
        out.append(c); i += 1
    return "".join(out)

MODS = r"(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|scoped)\s+)*"
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)*" + MODS + r"(theorem|lemma|def|abbrev|instance|inductive|structure|class|axiom|opaque)\b\s*([^\s:({\[]*)")
NS = re.compile(r"^\s*namespace\s+(\S+)")
SEC = re.compile(r"^\s*(?:noncomputable\s+)?section\b\s*(\S*)")
END = re.compile(r"^\s*end\b\s*(\S*)")
EXPORT = re.compile(r"^\s*export\s+(\S+)\s*\(([^)]*)\)", re.S)
IMPORT = re.compile(r"^import\s+(\S+)", re.M)
CTOR = re.compile(r"^\s*\|\s*([^\s:({\[]+)")
IDENT = re.compile(r"(?<![\w'.\u2080-\u209C\u1D62\u1D34ᵢᴴ₀₁₂])((?:[A-Za-z_\u0370-\u03FF][\w'!?\u2080-\u209C\u1D62\u1D34ᵢᴴ]*)(?:\.[A-Za-z_\u0370-\u03FF][\w'!?\u2080-\u209C\u1D62\u1D34ᵢᴴ]*)*)")

def modname(root, path):
    rel = os.path.relpath(path, root).replace("\\", "/")[:-5]
    return rel.replace("/", ".")

def parse_file(root, path, lib):
    raw = open(path, encoding="utf-8").read()
    s = strip_comments(raw)
    lines = s.split("\n")
    mod = modname(root, path)
    imports = IMPORT.findall(s)
    stack = []  # (kind, name)
    decls = []; exports = []; opens = []
    cur = None
    def ns():
        return ".".join(x[1] for x in stack if x[0] == "ns" and x[1])
    i = 0
    while i < len(lines):
        L = lines[i]
        m = NS.match(L)
        if m and not L.startswith(" "):
            for part in [m.group(1)]:
                stack.append(("ns", part))
            i += 1; continue
        if re.match(r"^mutual\b", L):
            stack.append(("mut", "")); i += 1; continue
        m = SEC.match(L)
        if m and not L.startswith(" "):
            stack.append(("sec", m.group(1))); i += 1; continue
        m = END.match(L)
        if m and not L.startswith(" ") and L.strip().split()[0] == "end":
            name = m.group(1)
            if stack:
                stack.pop()
            if cur: cur["end"] = i; cur = None
            i += 1; continue
        m = re.match(r"^export\s+", L)
        if m:
            # may span lines
            j = i; txt = L
            while ")" not in txt and j + 1 < len(lines):
                j += 1; txt += " " + lines[j]
            mm = re.match(r"^\s*export\s+(\S+)\s*\(([^)]*)\)", txt, re.S)
            if mm:
                exports.append((ns(), mm.group(1), mm.group(2).split()))
            i = j + 1; continue
        mo = re.match(r"^\s*open\s+(.*)$", L)
        if mo:
            rest = mo.group(1)
            rest = re.split(r"\s(?:in|hiding|renaming)\b|\(", " " + rest)[0]
            for tok in rest.split():
                if re.match(r"^[A-Za-z_][\w.'ᵢᴴ₀-₉]*$", tok):
                    opens.append((ns(), tok))
        m = DECL.match(L)
        if m and not L.startswith(" "):
            kind, name = m.group(1), m.group(2)
            if kind == "instance" and (not name or name.startswith("{") or name.startswith(":")):
                name = f"_inst_{i+1}"
            if name.startswith("_root_."):
                full = name[len("_root_."):]
            else:
                full = (ns() + "." + name) if ns() else name
            if cur: cur["end"] = i
            cur = dict(module=mod, lib=lib, kind=kind, name=name, full=full, ns=ns(), line=i+1, end=None, ctors=[])
            decls.append(cur)
            i += 1; continue
        if cur and cur["kind"] in ("inductive", "structure", "class"):
            mc = CTOR.match(L)
            if mc: cur["ctors"].append(mc.group(1))
        i += 1
    if cur and cur["end"] is None: cur["end"] = len(lines)
    for d in decls:
        if d["end"] is None: d["end"] = len(lines)
        body = "\n".join(lines[d["line"]-1:d["end"]])
        d["text"] = body
    return dict(module=mod, lib=lib, path=path, imports=imports, decls=decls, exports=exports, opens=opens)

files = []
for lib, root, sub in [("RPP", RPP, "ROBINSON_PlusPlus"), ("FOL", FOL, "FOL"), ("FOL", FOL, "TheoryFramework")]:
    for dp, dn, fn in os.walk(os.path.join(root, sub)):
        for f in sorted(fn):
            if f.endswith(".lean"):
                files.append(parse_file(root, os.path.join(dp, f), lib))
# barrels
for lib, root, f in [("RPP", RPP, "ROBINSON_PlusPlus.lean"), ("FOL", FOL, "FOL.lean"), ("FOL", FOL, "TheoryFramework.lean")]:
    files.append(parse_file(root, os.path.join(root, f), lib))

json.dump(files, open(os.path.join(OUT, "parsed.json"), "w", encoding="utf-8"), ensure_ascii=False)
print("files:", len(files), "decls:", sum(len(f["decls"]) for f in files))
c = collections.Counter((f["lib"], d["kind"]) for f in files for d in f["decls"])
for k, v in sorted(c.items()): print(k, v)
