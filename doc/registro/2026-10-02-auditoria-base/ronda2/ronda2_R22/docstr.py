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
Minimal.Theorems.Block8 Full.Factorization Full.StrongInduction""".split())
gone = set(); alive = set()
for i, d in enumerate(decls):
    if d["lib"] == "RPP" and (i in DROP or d["module"] in DEL): gone.add(d["name"])
    else: alive.add(d["name"])
gone |= {"imp_intro", "raa", "or_elim", "ex_elim", "MetaRules"}
dead = {n for n in gone if n not in alive and len(n) > 3}
c = collections.Counter(); tot = 0
for f in files:
    if f["lib"] != "RPP" or f["module"] in DEL or f["module"] == "ROBINSON_PlusPlus": continue
    raw = open(f["path"], encoding="utf-8").read()
    # only comment text: block comments and line comments
    com = " ".join(re.findall(r"/-.*?-/", raw, flags=re.S) + re.findall(r"--[^\n]*", raw))
    hits = [m.group(1) for m in re.finditer(r"`([A-Za-z_][\w'.ᵢ]*)`", com) if m.group(1).split(".")[-1] in dead]
    if hits: c[f["module"].replace(P, "")] = len(hits); tot += len(hits)
print("citas `X` en COMENTARIOS de modulos supervivientes a simbolos que desaparecen:", tot, "en", len(c), "modulos")
for m, n in c.most_common(30): print(f"   {m:32s} {n}")
