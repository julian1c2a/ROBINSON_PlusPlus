import json, os, collections
OUT = os.path.dirname(os.path.abspath(__file__))
files = json.load(open(os.path.join(OUT, "parsed.json"), encoding="utf-8"))
g = json.load(open(os.path.join(OUT, "graph.json"), encoding="utf-8"))
t = json.load(open(os.path.join(OUT, "taint.json")))
decls = [d for f in files for d in f["decls"]]
deps = {int(k): v for k, v in g["deps"].items()}
cls = g["cls"]; DROP = set(t["TDB"])
rpp = [i for i, d in enumerate(decls) if d["lib"] == "RPP"]
bymod = collections.defaultdict(list)
for i in rpp: bymod[decls[i]["module"]].append(i)
dmods = {m for m, L in bymod.items() if any(i in DROP for i in L)}   # modules of the ⊢ library (contain ⊢ decls)
def reach(roots):
    seen = set(); st = list(roots)
    while st:
        x = st.pop()
        if x in seen: continue
        seen.add(x); st.extend(deps.get(x, []))
    return seen
P = [i for i in rpp if cls[i] == "P" and i not in DROP]
G12 = [i for i, d in enumerate(decls) if d["full"].endswith("GodelTwoPrf.goedel_first_prf") or d["full"].endswith("GodelTwoPrf.goedel_second_prf")]
for nm, roots in [("Godel I/II", G12), ("toda la libreria Prf (clase P)", P)]:
    R = reach(roots)
    used = [i for i in R if decls[i]["lib"] == "RPP" and decls[i]["module"] in dmods and not (decls[i]["module"].endswith("Prf") and decls[i]["module"] not in ("ROBINSON_PlusPlus.Meta.ChainNegPrf","ROBINSON_PlusPlus.Meta.GodelTwoPrf"))]
    k = collections.Counter((decls[i]["kind"] if decls[i]["kind"] in ("theorem",) else "def/otro", cls[i]) for i in used)
    print(f"== {nm}: alcanzables en modulos con ⊢ (excluidos *Prf salvo ChainNegPrf/GodelTwoPrf): {len(used)}; por (tipo, clase): {dict(k)}")
    print("   D/mixto alcanzables:", [decls[i]["full"] for i in R if cls[i] in ("D","mixto") and decls[i]["lib"]=="RPP"])
    print("   en DROP alcanzables:", len([i for i in R if i in DROP]))
    th = sorted({(decls[i]["module"].replace("ROBINSON_PlusPlus.",""), decls[i]["name"]) for i in used if decls[i]["kind"] == "theorem"})
    print("   teoremas usados de esos modulos:", len(th), th[:60])
