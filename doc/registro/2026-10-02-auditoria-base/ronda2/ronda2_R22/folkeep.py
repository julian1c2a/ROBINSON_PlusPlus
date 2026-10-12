import json, os, collections
OUT = os.path.dirname(os.path.abspath(__file__))
files = json.load(open(os.path.join(OUT, "parsed.json"), encoding="utf-8"))
g = json.load(open(os.path.join(OUT, "graph.json"), encoding="utf-8"))
t = json.load(open(os.path.join(OUT, "taint.json")))
decls = [d for f in files for d in f["decls"]]
deps = {int(k): v for k, v in g["deps"].items()}
DROP = set(t["TDB"])
keep = [i for i, d in enumerate(decls) if d["lib"] == "RPP" and i not in DROP]
used = collections.defaultdict(set); usedD = collections.defaultdict(set)
for i in keep:
    for j in deps.get(i, []):
        if decls[j]["lib"] == "FOL": used[decls[j]["module"]].add(decls[j]["name"])
for i in DROP:
    if decls[i]["lib"] != "RPP": continue
    for j in deps.get(i, []):
        if decls[j]["lib"] == "FOL": usedD[decls[j]["module"]].add(decls[j]["name"])
print("FOL modules used DIRECTLY by KEEP RPP decls:")
for m in sorted(used): print(f"  {m}: {len(used[m])} -> {sorted(used[m])[:25]}")
print("FOL modules used ONLY by DROP decls:")
for m in sorted(set(usedD) - set(used)): print(f"  {m}: {len(usedD[m])} -> {sorted(usedD[m])[:12]}")
