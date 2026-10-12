import json, os, sys
OUT = os.path.dirname(os.path.abspath(__file__))
files = json.load(open(os.path.join(OUT, "parsed.json"), encoding="utf-8"))
g = json.load(open(os.path.join(OUT, "graph.json"), encoding="utf-8"))
decls = [d for f in files for d in f["decls"]]
deps = {int(k): v for k, v in g["deps"].items()}
for name in sys.argv[1:]:
    for i, d in enumerate(decls):
        if d["full"] == name or d["full"].endswith("." + name):
            print("==", d["kind"], d["full"], d["module"], d["line"], "-", d["end"], "ns=", d.get("ns"))
            print("   deps:", sorted(decls[j]["full"] for j in deps[i]))
