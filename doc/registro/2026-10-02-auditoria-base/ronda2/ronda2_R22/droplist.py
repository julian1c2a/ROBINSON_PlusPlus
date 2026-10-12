import json, os, collections, sys
OUT = os.path.dirname(os.path.abspath(__file__))
files = json.load(open(os.path.join(OUT, "parsed.json"), encoding="utf-8"))
g = json.load(open(os.path.join(OUT, "graph.json"), encoding="utf-8"))
t = json.load(open(os.path.join(OUT, "taint.json")))
decls = [d for f in files for d in f["decls"]]
cls = g["cls"]; DROP = set(t["TDB"]); T7 = set(t["T7"])
want = sys.argv[1:]
for m in want:
    ids = [i for i, d in enumerate(decls) if d["module"] == "ROBINSON_PlusPlus." + m and i in DROP]
    ids.sort(key=lambda i: decls[i]["line"])
    print(f"== {m}: DROP {len(ids)}")
    print("   " + ", ".join(f"{decls[i]['name']}:{decls[i]['line']}{'(7)' if i in T7 else ''}[{cls[i]}]" for i in ids))
