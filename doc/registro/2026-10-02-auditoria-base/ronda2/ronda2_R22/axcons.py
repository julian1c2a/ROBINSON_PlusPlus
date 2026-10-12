# R2-2 (solo lectura): consumidores directos y transitivos de cada uno de los 7 axiomas (heuristico, calibrado con la TABLA).
import json, os, collections
OUT = os.path.dirname(os.path.abspath(__file__))
files = json.load(open(os.path.join(OUT, "parsed.json"), encoding="utf-8"))
g = json.load(open(os.path.join(OUT, "graph.json"), encoding="utf-8"))
decls = [d for f in files for d in f["decls"]]
deps = {int(k): v for k, v in g["deps"].items()}
rdeps = collections.defaultdict(set)
for a, bs in deps.items():
    for b in bs: rdeps[b].add(a)
axs = [i for i, d in enumerate(decls) if d["kind"] == "axiom"]
def up(s):
    seen = set(s); st = list(s)
    while st:
        x = st.pop()
        for y in rdeps.get(x, ()):
            if y not in seen: seen.add(y); st.append(y)
    return seen - set(s)
for a in axs:
    d = decls[a]
    direct = sorted(rdeps.get(a, ()), key=lambda i: (decls[i]["module"], decls[i]["line"]))
    tr = up({a})
    trr = [i for i in tr if decls[i]["lib"] == "RPP"]; trf = [i for i in tr if decls[i]["lib"] == "FOL"]
    mods = collections.Counter(decls[i]["module"].replace("ROBINSON_PlusPlus.", "") for i in trr)
    print(f"== {d['full']} [{d['module']}:{d['line']}]")
    print(f"   directos ({len(direct)}): " + ", ".join(f"{decls[i]['name']}@{decls[i]['module'].split('.')[-1]}:{decls[i]['line']}" for i in direct[:60]) + (" ..." if len(direct) > 60 else ""))
    print(f"   transitivos: RPP {len(trr)} decls en {len(mods)} modulos; FOL {len(trf)}: {[decls[i]['full'] for i in trf][:6]}")
    print("   por modulo:", dict(mods.most_common()))
