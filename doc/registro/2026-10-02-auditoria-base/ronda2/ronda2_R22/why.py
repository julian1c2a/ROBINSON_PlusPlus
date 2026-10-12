# For targets, show one path from roots (BFS) in the dependency graph.
import json, os, sys, collections
OUT = os.path.dirname(os.path.abspath(__file__))
files = json.load(open(os.path.join(OUT, "parsed.json"), encoding="utf-8"))
g = json.load(open(os.path.join(OUT, "graph.json"), encoding="utf-8"))
decls = [d for f in files for d in f["decls"]]
deps = {int(k): v for k, v in g["deps"].items()}
args = sys.argv[1:]
k = args.index("--to")
roots = [i for i, d in enumerate(decls) for a in args[:k] if d["full"] == a or d["full"].endswith("." + a)]
targets = set(i for i, d in enumerate(decls) for a in args[k+1:] if d["full"] == a or d["full"].endswith("." + a) or (a.endswith("*") and d["module"] == a[:-1]))
par = {r: None for r in roots}; q = collections.deque(roots); hit = []
while q:
    x = q.popleft()
    if x in targets: hit.append(x)
    for y in deps.get(x, []):
        if y not in par: par[y] = x; q.append(y)
for t in hit:
    path = []; x = t
    while x is not None: path.append(x); x = par[x]
    print(" <- ".join(f"{decls[p]['full']}@{decls[p]['module'].split('.')[-1]}:{decls[p]['line']}" for p in path))
