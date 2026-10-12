import json, os, collections
OUT = os.path.dirname(os.path.abspath(__file__))
files = json.load(open(os.path.join(OUT, "parsed.json"), encoding="utf-8"))
g = json.load(open(os.path.join(OUT, "graph.json"), encoding="utf-8"))
decls = [d for f in files for d in f["decls"]]
deps = {int(k): v for k, v in g["deps"].items()}
rdeps = collections.defaultdict(set)
for a, bs in deps.items():
    for b in bs: rdeps[b].add(a)
def up(seeds):
    seen = set(seeds); st = list(seeds)
    while st:
        x = st.pop()
        for y in rdeps.get(x, ()):
            if y not in seen: seen.add(y); st.append(y)
    return seen
M4 = {i for i, d in enumerate(decls) if d["module"] == "FOL.MetaRules" and d["kind"] == "axiom"}
T4 = up(M4)
r = [i for i in T4 if decls[i]["lib"] == "RPP"]; f = [i for i in T4 if decls[i]["lib"] == "FOL"]
print("dependen de las 4 meta-reglas: RPP", len(r), "decls (", len(set(decls[i]['module'] for i in r)), "modulos); FOL", len(f), [decls[i]["full"] for i in f])
