# open de espacios de nombres que DESAPARECEN (unknown namespace = error en Lean 4) en modulos supervivientes
import json, os, re, collections
OUT = os.path.dirname(os.path.abspath(__file__))
files = json.load(open(os.path.join(OUT, "parsed.json"), encoding="utf-8"))
t = json.load(open(os.path.join(OUT, "taint.json")))
decls = [d for f in files for d in f["decls"]]
DROP = set(t["TDB"])
P = "ROBINSON_PlusPlus."
DEL = set(P + m for m in """Full.Bounded Full.Divisibility Full.Division Full.Lists Full.Mod2 Full.Primality Meta.AxiomListCode
Meta.DerivCond Meta.Induction Meta.LineWFDerives Meta.ListInductionArith Meta.Necessitation Meta.OmegaStrength Meta.Reflection
Meta.StepArith Minimal.Theorems.Block1 Minimal.Theorems.Block2 Minimal.Theorems.Block3 Minimal.Theorems.Block4
Minimal.Theorems.Block4_C5 Minimal.Theorems.Block4_C6_C7 Minimal.Theorems.Block5 Minimal.Theorems.Block6 Minimal.Theorems.Block7
Minimal.Theorems.Block8 Full.Factorization Full.StrongInduction""".split()) | {"FOL.MetaRules"}
# namespaces that survive: those with at least one surviving decl
surv_ns = set(); all_ns = set()
for i, d in enumerate(decls):
    parts = d["full"].split(".")
    for k in range(1, len(parts)):
        ns = ".".join(parts[:k]); all_ns.add(ns)
        if not (d["module"] in DEL or i in DROP): surv_ns.add(ns)
n = 0; per = collections.Counter(); ex = []
for f in files:
    if f["lib"] != "RPP" or f["module"] in DEL: continue
    for (ons, o) in f["opens"]:
        cands = [(p + "." + o) if p else o for p in ([ons] + [".".join(ons.split(".")[:k]) for k in range(len(ons.split(".")), -1, -1)])]
        known = [c for c in cands if c in all_ns]
        if known and not any(c in surv_ns for c in known):
            n += 1; per[f["module"].replace(P, "")] += 1
            if len(ex) < 25: ex.append((f["module"].replace(P, ""), o))
print("`open` en modulos supervivientes de espacios que se quedan VACIOS:", n, dict(per))
for e in ex: print("   ", e)
