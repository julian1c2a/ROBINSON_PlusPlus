# R2-2 (solo lectura): reparacion de imports si se BORRAN los modulos DEL; comprobacion de que cada
# modulo superviviente sigue viendo (por imports transitivos) los modulos de los que dependen sus KEEP.
import json, os, collections, sys
OUT = os.path.dirname(os.path.abspath(__file__))
files = json.load(open(os.path.join(OUT, "parsed.json"), encoding="utf-8"))
g = json.load(open(os.path.join(OUT, "graph.json"), encoding="utf-8"))
t = json.load(open(os.path.join(OUT, "taint.json")))
decls = [d for f in files for d in f["decls"]]
deps = {int(k): v for k, v in g["deps"].items()}
DROP = set(t["TDB"])
P = "ROBINSON_PlusPlus."
DEL = [P + m for m in """Full.Bounded Full.Divisibility Full.Division Full.Lists Full.Mod2 Full.Primality Meta.AxiomListCode
Meta.DerivCond Meta.Induction Meta.LineWFDerives Meta.ListInductionArith Meta.Necessitation Meta.OmegaStrength Meta.Reflection
Meta.StepArith Minimal.Theorems.Block1 Minimal.Theorems.Block2 Minimal.Theorems.Block3 Minimal.Theorems.Block4
Minimal.Theorems.Block4_C5 Minimal.Theorems.Block4_C6_C7 Minimal.Theorems.Block5 Minimal.Theorems.Block6 Minimal.Theorems.Block7
Minimal.Theorems.Block8 Full.Factorization Full.StrongInduction""".split()]
DELF = ["FOL.MetaRules"]
imports = {f["module"]: list(f["imports"]) for f in files}
rpp_mods = sorted(m for m in imports if m.startswith(P) or m == "ROBINSON_PlusPlus")
print("modulos RPP:", len(rpp_mods), " a borrar:", len(DEL))
# direct importers of deleted modules
imp_by = collections.defaultdict(list)
for m in rpp_mods:
    for x in imports[m]:
        if x in DEL or x in DELF: imp_by[x].append(m)
print("\n(1) importadores directos de modulos a borrar (supervivientes marcados *):")
for x in DEL + DELF:
    L = imp_by.get(x, [])
    surv = [m for m in L if m not in DEL]
    print(f"  {x.replace(P,'')}: {len(L)} importadores, {len(surv)} supervivientes: {[m.replace(P,'') for m in surv]}")
# new import lists: replace deleted imports by their (recursive) non-deleted imports
def expand(x, seen=None):
    seen = seen or set()
    out = []
    for y in imports.get(x, []):
        if y in seen: continue
        seen.add(y)
        if y in DEL or y in DELF: out += expand(y, seen)
        else: out.append(y)
    return out
new_imports = {}
for m in rpp_mods:
    if m in DEL: continue
    L = []
    for x in imports[m]:
        if x in DEL or x in DELF: L += expand(x)
        else: L.append(x)
    new_imports[m] = sorted(set(L))
def closure(m, imps):
    seen = set(); st = [m]
    while st:
        x = st.pop()
        if x in seen: continue
        seen.add(x); st.extend(imps.get(x, imports.get(x, [])))
    return seen
# check visibility of needed modules for KEEP decls
bad = 0
need_mod = collections.defaultdict(set)
for i, d in enumerate(decls):
    if d["lib"] != "RPP" or i in DROP or d["module"] in DEL: continue
    for j in deps.get(i, []):
        dm = decls[j]["module"]
        if dm != d["module"]: need_mod[d["module"]].add(dm)
print("\n(2) KEEP de supervivientes que dependen de un modulo BORRADO (habria que mover):")
for m, S in sorted(need_mod.items()):
    for dm in S:
        if dm in DEL or dm in DELF:
            ids = [i for i, d in enumerate(decls) if d["module"] == m and i not in DROP and any(decls[j]["module"] == dm for j in deps.get(i, []))]
            what = sorted({decls[j]["name"] for i in ids for j in deps[i] if decls[j]["module"] == dm})
            print(f"  {m.replace(P,'')} -> {dm.replace(P,'')}: {what[:10]}")
            bad += 1
print("  total:", bad)
print("\n(3) cambios de linea import en supervivientes (quitar borrados, reimportar lo que traian):")
n = 0
for m in rpp_mods:
    if m in DEL: continue
    rm = [x for x in imports[m] if x in DEL or x in DELF]
    if rm:
        n += 1
        add = sorted(set(new_imports[m]) - set(imports[m]))
        print(f"  {m.replace(P,'')}: quita {[x.replace(P,'') for x in rm]} ; anade {[x.replace(P,'') for x in add]}")
print("  modulos supervivientes que tocan su bloque de imports:", n)
