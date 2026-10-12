# R2-2 (solo lectura): plan por modulo. DROP = capa ⊢ (TDB: enunciado o cuerpo ⊢, o depende de ello, o de los 7 axiomas).
# KEEP = resto. R_P = alcanzable desde las declaraciones de clase P (la libreria Prf) + raices extra.
import json, os, collections, sys
OUT = os.path.dirname(os.path.abspath(__file__))
files = json.load(open(os.path.join(OUT, "parsed.json"), encoding="utf-8"))
g = json.load(open(os.path.join(OUT, "graph.json"), encoding="utf-8"))
t = json.load(open(os.path.join(OUT, "taint.json")))
decls = [d for f in files for d in f["decls"]]
deps = {int(k): v for k, v in g["deps"].items()}
cls = g["cls"]
DROP = set(t["TDB"]); T7 = set(t["T7"])
rpp = [i for i, d in enumerate(decls) if d["lib"] == "RPP"]
KEEP = [i for i in rpp if i not in DROP]
# Roots of the Prf library: every KEEP decl of class P, plus the AnclaEq class and the explicit titulares
roots = [i for i in KEEP if cls[i] == "P"]
seen = set(); st = list(roots)
while st:
    x = st.pop()
    if x in seen: continue
    seen.add(x); st.extend(deps.get(x, []))
RP = seen
# Gödel I/II chain
g12 = [i for i, d in enumerate(decls) if d["full"].endswith("GodelTwoPrf.goedel_first_prf") or d["full"].endswith("GodelTwoPrf.goedel_second_prf")]
seen = set(); st = list(g12)
while st:
    x = st.pop()
    if x in seen: continue
    seen.add(x); st.extend(deps.get(x, []))
RG = seen
assert not (RG & DROP), [decls[i]["full"] for i in RG & DROP]
assert not (RP & DROP), [decls[i]["full"] for i in list(RP & DROP)[:10]]
mods = collections.defaultdict(lambda: dict(drop=[], keepP=[], keepNotP=[], g12=[]))
for i in rpp:
    m = decls[i]["module"]
    if i in DROP: mods[m]["drop"].append(i)
    elif i in RP: mods[m]["keepP"].append(i)
    else: mods[m]["keepNotP"].append(i)
    if i in RG: mods[m]["g12"].append(i)
lines = []
cat = collections.Counter()
for m in sorted(mods):
    r = mods[m]; nd, nk, nn = len(r["drop"]), len(r["keepP"]), len(r["keepNotP"])
    if nd == 0: k = "LIMPIO"
    elif nk == 0 and nn == 0: k = "BORRAR"
    elif nk == 0: k = "BORRAR+meta"   # only ⊢ stuff + clean decls nobody in Prf uses
    else: k = "PARTIR"
    cat[k] += 1
    lines.append((k, m, nd, nk, nn, len(r["g12"])))
print("categoria de modulo:", dict(cat))
print("KEEP:", len(KEEP), " DROP:", len([i for i in rpp if i in DROP]), " R_P∩RPP:", len([i for i in RP if decls[i]['lib']=='RPP']), " R_G12∩RPP:", len([i for i in RG if decls[i]['lib']=='RPP']))
for k, m, nd, nk, nn, ng in sorted(lines):
    if k != "LIMPIO":
        print(f"{k:12s} {m:52s} drop={nd:4d} keepUsedByPrf={nk:4d} keepOther={nn:4d} inG12={ng:4d}")
if "--detail" in sys.argv:
    for k, m, nd, nk, nn, ng in sorted(lines):
        if k in ("PARTIR", "BORRAR+meta"):
            r = mods[m]
            print("\n##", k, m)
            print("   keep usado por Prf :", " ".join(f"{decls[i]['name']}({decls[i]['kind'][0]}{'*' if i in RG else ''})" for i in sorted(r["keepP"], key=lambda i: decls[i]['line'])))
            print("   keep resto         :", " ".join(f"{decls[i]['name']}({decls[i]['kind'][0]})" for i in sorted(r["keepNotP"], key=lambda i: decls[i]['line'])))
