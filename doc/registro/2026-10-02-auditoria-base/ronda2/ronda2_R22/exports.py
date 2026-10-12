import json, os, collections
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
Minimal.Theorems.Block8 Full.Factorization Full.StrongInduction""".split())
dropfull = {decls[i]["full"] for i in DROP}
tot = 0; per = collections.Counter()
for f in files:
    if f["lib"] != "RPP" or f["module"] in DEL: continue
    for ns, src, names in f["exports"]:
        for n in names:
            full = src + "." + n
            if any(x == full or x.endswith("." + full) or x.endswith(src.split(".")[-1] + "." + n) for x in dropfull):
                tot += 1; per[f["module"].replace(P, "")] += 1
print("entradas de export en modulos SUPERVIVIENTES que nombran DROP:", tot, dict(per))
