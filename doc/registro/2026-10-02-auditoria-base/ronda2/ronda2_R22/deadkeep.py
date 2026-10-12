import json, os, collections
OUT = os.path.dirname(os.path.abspath(__file__))
files = json.load(open(os.path.join(OUT, "parsed.json"), encoding="utf-8"))
g = json.load(open(os.path.join(OUT, "graph.json"), encoding="utf-8"))
t = json.load(open(os.path.join(OUT, "taint.json")))
decls = [d for f in files for d in f["decls"]]
deps = {int(k): v for k, v in g["deps"].items()}
cls = g["cls"]; DROP = set(t["TDB"])
P = "ROBINSON_PlusPlus."
DEL = set(P + m for m in """Full.Bounded Full.Divisibility Full.Division Full.Lists Full.Mod2 Full.Primality Meta.AxiomListCode
Meta.DerivCond Meta.Induction Meta.LineWFDerives Meta.ListInductionArith Meta.Necessitation Meta.OmegaStrength Meta.Reflection
Meta.StepArith Minimal.Theorems.Block1 Minimal.Theorems.Block2 Minimal.Theorems.Block3 Minimal.Theorems.Block4
Minimal.Theorems.Block4_C5 Minimal.Theorems.Block4_C6_C7 Minimal.Theorems.Block5 Minimal.Theorems.Block6 Minimal.Theorems.Block7
Minimal.Theorems.Block8 Full.Factorization Full.StrongInduction""".split())
rpp = [i for i, d in enumerate(decls) if d["lib"] == "RPP"]
keep = [i for i in rpp if i not in DROP and decls[i]["module"] not in DEL]
roots = [i for i in keep if cls[i] == "P"]
seen = set(); st = list(roots)
while st:
    x = st.pop()
    if x in seen: continue
    seen.add(x); st.extend(deps.get(x, []))
rdeps = collections.defaultdict(set)
for a, bs in deps.items():
    for b in bs: rdeps[b].add(a)
nonP = [i for i in keep if i not in seen]
# of those, which have no KEEP dependents at all (leaves)
leaf = [i for i in nonP if not any(j in set(keep) for j in rdeps.get(i, ()))]
c = collections.Counter(decls[i]["module"].replace(P, "") for i in nonP)
print("KEEP en modulos supervivientes:", len(keep), "; fuera del alcance de la libreria Prf:", len(nonP), "(hojas sin dependientes:", len(leaf), ")")
for m, n in c.most_common(25): print(f"   {m:32s} {n}")
