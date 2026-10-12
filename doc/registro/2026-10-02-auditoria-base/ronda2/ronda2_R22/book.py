import json, os, re, glob, collections
OUT = os.path.dirname(os.path.abspath(__file__))
RPP = r"E:/dropbox/github/lean4/ROBINSON_PlusPlus"
files = json.load(open(os.path.join(OUT, "parsed.json"), encoding="utf-8"))
t = json.load(open(os.path.join(OUT, "taint.json")))
decls = [d for f in files for d in f["decls"]]
DROP = set(t["TDB"])
P = "ROBINSON_PlusPlus."
DEL = set(P + m for m in """Full.Bounded Full.Divisibility Full.Division Full.Lists Full.Mod2 Full.Primality Meta.AxiomListCode
Meta.DerivCond Meta.Induction Meta.LineWFDerives Meta.ListInductionArith Meta.Necessitation Meta.OmegaStrength Meta.Reflection
Meta.StepArith Minimal.Theorems.Block1 Minimal.Theorems.Block2 Minimal.Theorems.Block3 Minimal.Theorems.Block4
Minimal.Theorems.Block4_C5 Minimal.Theorems.Block4_C6_C7 Minimal.Theorems.Block5 Minimal.Theorems.Block6 Minimal.Theorems.Block7
Minimal.Theorems.Block8 Full.Factorization Full.StrongInduction""".split())
gone = collections.Counter(); alive = collections.Counter()
for i, d in enumerate(decls):
    if d["lib"] == "RPP" and (i in DROP or d["module"] in DEL): gone[d["name"]] += 1
    else: alive[d["name"]] += 1
for i, d in enumerate(decls):
    if d["lib"] == "FOL" and d["module"] in ("FOL.MetaRules", "FOL.Inconsistencia"): gone[d["name"]] += 1; alive[d["name"]] -= 1
ids = collections.Counter(); where = collections.defaultdict(set)
for p in glob.glob(os.path.join(RPP, "doc", "book", "**", "*.tex"), recursive=True):
    s = open(p, encoding="utf-8", errors="replace").read()
    BS = chr(92)
    for m in re.finditer(BS + BS + r"ident\{([^}]+)\}", s):
        nm = m.group(1).replace(BS + "_", "_").split(".")[-1]
        if gone[nm] and alive[nm] <= 0:
            ids[nm] += 1; where[nm].add(os.path.relpath(p, RPP))
mods = collections.Counter()
for p in glob.glob(os.path.join(RPP, "doc", "book", "**", "*.tex"), recursive=True):
    s = open(p, encoding="utf-8", errors="replace").read()
    for m in DEL | {"FOL.MetaRules"}:
        short = m.replace(P, "").replace(".", "/") + ".lean"
        if short in s: mods[short] += s.count(short)
print("ident{} del libro que quedarian MUERTOS:", len(ids), "simbolos,", sum(ids.values()), "apariciones")
for k, v in ids.most_common(40): print(f"   {v:3d} {k}  {sorted(where[k])[:3]}")
print("rutas de modulos borrados citadas en el libro:", dict(mods))
