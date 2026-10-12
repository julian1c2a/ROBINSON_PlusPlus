# R2-2 (solo lectura): (1) dependientes KEEP fuera del modulo para los KEEP de modulos BORRAR+meta;
# (2) reparacion de imports: para cada modulo superviviente, imports a modulos borrados y lo que hay que reimportar.
import json, os, collections, sys
OUT = os.path.dirname(os.path.abspath(__file__))
files = json.load(open(os.path.join(OUT, "parsed.json"), encoding="utf-8"))
g = json.load(open(os.path.join(OUT, "graph.json"), encoding="utf-8"))
t = json.load(open(os.path.join(OUT, "taint.json")))
decls = [d for f in files for d in f["decls"]]
deps = {int(k): v for k, v in g["deps"].items()}
cls = g["cls"]; DROP = set(t["TDB"])
rpp = [i for i, d in enumerate(decls) if d["lib"] == "RPP"]
KEEP = set(i for i in rpp if i not in DROP)
rdeps = collections.defaultdict(set)
for a, bs in deps.items():
    for b in bs: rdeps[b].add(a)
bymod = collections.defaultdict(list)
for i in rpp: bymod[decls[i]["module"]].append(i)
borrar = [m for m in bymod if all(i in DROP for i in bymod[m])]
mixed = [m for m in bymod if any(i in DROP for i in bymod[m]) and any(i in KEEP for i in bymod[m])]
print("modulos solo-DROP:", len(borrar))
print("\n(1) KEEP de modulos mixtos usados por KEEP de OTROS modulos (no se pueden borrar sin mover):")
for m in sorted(mixed):
    ext = collections.defaultdict(set)
    for i in bymod[m]:
        if i not in KEEP: continue
        for j in rdeps.get(i, ()):
            if j in KEEP and decls[j]["module"] != m:
                ext[decls[i]["name"]].add(decls[j]["module"].replace("ROBINSON_PlusPlus.", ""))
    if ext:
        print(f"  {m.replace('ROBINSON_PlusPlus.','')}: " + "; ".join(f"{k}<-{sorted(v)[:4]}{'+' if len(v)>4 else ''}({len(v)})" for k, v in sorted(ext.items())))
    else:
        print(f"  {m.replace('ROBINSON_PlusPlus.','')}: (nadie fuera del modulo)")
