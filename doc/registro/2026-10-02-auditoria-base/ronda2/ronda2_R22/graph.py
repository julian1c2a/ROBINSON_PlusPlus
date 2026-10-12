# R2-2 (solo lectura): grafo de dependencias por constante, con resolucion de nombres por espacio de nombres
# (prefijos del namespace actual + `open` del fichero + alias de `export`). Heuristico: SOBRE-aproxima.
import os, re, json, sys, collections
OUT = os.path.dirname(os.path.abspath(__file__))
files = json.load(open(os.path.join(OUT, "parsed.json"), encoding="utf-8"))

IDENT = re.compile(r"(?<![\w'.₀-ₜᵢᴴ])((?:[A-Za-z_Ͱ-Ͽ][\w'!?₀-ₜᵢᴴ]*)(?:\.[A-Za-z_Ͱ-Ͽ][\w'!?₀-ₜᵢᴴ]*)*)")
D_TOK = re.compile(r"⊢(?![ᴴ₀₁₂ᵢ])")
H_TOK = re.compile(r"⊢ᴴ")

imports = {f["module"]: list(f["imports"]) for f in files}
closure_cache = {}
def closure(m):
    if m in closure_cache: return closure_cache[m]
    seen = set(); st = [m]
    while st:
        x = st.pop()
        if x in seen: continue
        seen.add(x)
        st.extend(imports.get(x, []))
    closure_cache[m] = seen
    return seen

decls = []
for f in files:
    for d in f["decls"]:
        d["id"] = len(decls); decls.append(d)

fullname = collections.defaultdict(set)   # full name -> ids (ctor names map to parent)
for d in decls:
    fullname[d["full"]].add(d["id"])
    for c in d["ctors"]:
        fullname[d["full"] + "." + c].add(d["id"])

def prefixes(ns):
    parts = ns.split(".") if ns else []
    return [".".join(parts[:k]) for k in range(len(parts), -1, -1)]

def lookup(name, ns, opens):
    """Resolve `name` as Lean would (approx.): current-namespace prefixes, then opened namespaces."""
    res = set()
    for p in prefixes(ns):
        q = (p + "." + name) if p else name
        if q in fullname: res |= fullname[q]
    for (ons, o) in opens:
        for p in prefixes(ons):
            base = (p + "." + o) if p else o
            q = base + "." + name
            if q in fullname: res |= fullname[q]
    return res

# exports -> aliases (alias full name -> target ids)
file_by_mod = {f["module"]: f for f in files}
alias_n = 0
for f in files:
    for (ns, src, names) in f["exports"]:
        for n in names:
            tg = set()
            for p in prefixes(ns):
                q = ((p + "." + src) if p else src) + "." + n
                if q in fullname: tg |= fullname[q]
            if not tg:
                q = src + "." + n
                tg = fullname.get(q, set())
            alias = (ns + "." + n) if ns else n
            if tg:
                fullname[alias] |= tg; alias_n += 1

DER = next(iter(fullname["Derives"]))
PRF = next(iter(fullname["ROBINSON_PlusPlus.Meta.Hilbert.Prf"]))

deps = {}
unres = collections.Counter()
for f in files:
    opens = [tuple(x) for x in f["opens"]]
    vis = closure(f["module"])
    for d in f["decls"]:
        out = set()
        txt = d["text"]
        if d["kind"] in ("inductive", "structure", "class"):
            txt = re.sub(r"(?m)^(\s*\|\s*)[^\s:({\[]+", r"\1", txt)
        ns = d.get("ns", "")
        # inside its own namespace, the decl's own parent namespace also counts (e.g. `Prf` inside `namespace Prf`)
        for t in set(IDENT.findall(txt)):
            cs = lookup(t, ns, opens)
            if not cs and "." in t:
                head, rest = t.split(".", 1)
                for h in lookup(head, ns, opens):
                    q = decls[h]["full"] + "." + rest
                    cs |= fullname.get(q, set())
                    # field access on a constant (e.g. `foo.mp`): depend on the head
                    cs.add(h)
            cs = {c for c in cs if decls[c]["module"] in vis and c != d["id"]
                  and not (decls[c]["module"] == f["module"] and decls[c]["line"] > d["line"])}
            out |= cs
        if D_TOK.search(txt): out.add(DER)
        if H_TOK.search(txt): out.add(PRF)
        deps[d["id"]] = sorted(out)

def sig_of(d):
    txt = d["text"]
    if d["kind"] in ("inductive", "structure", "class"): return txt
    k = len(txt)
    for tok in [":=", "\n  where", " where\n", "\n  |"]:
        j = txt.find(tok)
        if j >= 0: k = min(k, j)
    return txt[:k]

def cls(d):
    sig = sig_of(d)
    isD = bool(D_TOK.search(sig)) or bool(re.search(r"\bDerives\b(?![₀₁₂])", sig))
    isP = bool(re.search(r"\bPrf\b|\bPrfᵢ\b|\bPrfH\b", sig)) or ("⊢ᴴ" in sig)
    return "mixto" if (isD and isP) else "D" if isD else "P" if isP else "otro"

for d in decls:
    d["cls"] = cls(d)

json.dump(dict(deps={str(k): v for k, v in deps.items()}, cls=[d["cls"] for d in decls], DER=DER, PRF=PRF),
          open(os.path.join(OUT, "graph.json"), "w", encoding="utf-8"))
print("decls", len(decls), "aliases", alias_n, "DER", decls[DER]["full"], decls[DER]["module"], "PRF", decls[PRF]["full"])
