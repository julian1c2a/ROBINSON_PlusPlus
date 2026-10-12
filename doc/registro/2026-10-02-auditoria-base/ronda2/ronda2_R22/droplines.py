import json, os, collections
OUT = os.path.dirname(os.path.abspath(__file__))
files = json.load(open(os.path.join(OUT, "parsed.json"), encoding="utf-8"))
t = json.load(open(os.path.join(OUT, "taint.json")))
DROP = set(t["TDB"])
P = "ROBINSON_PlusPlus."
DEL = set(P + m for m in """Full.Bounded Full.Divisibility Full.Division Full.Lists Full.Mod2 Full.Primality Meta.AxiomListCode
Meta.DerivCond Meta.Induction Meta.LineWFDerives Meta.ListInductionArith Meta.Necessitation Meta.OmegaStrength Meta.Reflection
Meta.StepArith Minimal.Theorems.Block1 Minimal.Theorems.Block2 Minimal.Theorems.Block3 Minimal.Theorems.Block4
Minimal.Theorems.Block4_C5 Minimal.Theorems.Block4_C6_C7 Minimal.Theorems.Block5 Minimal.Theorems.Block6 Minimal.Theorems.Block7
Minimal.Theorems.Block8 Full.Factorization Full.StrongInduction""".split())
i = 0; per = collections.Counter(); nd = collections.Counter()
for f in files:
    for d in f["decls"]:
        if i in DROP and f["lib"] == "RPP" and f["module"] not in DEL:
            per[f["module"].replace(P, "")] += (d["end"] - d["line"] + 1); nd[f["module"].replace(P,"")] += 1
        i += 1
print("lineas (sin comentarios, aprox. por rango de declaracion) de DROP en modulos que se EDITAN:", sum(per.values()), "en", len(per), "modulos")
for k, v in per.most_common(): print(f"   {k:30s} {v:5d} lineas, {nd[k]:3d} decls")
