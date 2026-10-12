import json, os, collections, re, glob
OUT = os.path.dirname(os.path.abspath(__file__))
RPP = r"E:/dropbox/github/lean4/ROBINSON_PlusPlus"
files = json.load(open(os.path.join(OUT, "parsed.json"), encoding="utf-8"))
t = json.load(open(os.path.join(OUT, "taint.json")))
decls = [d for f in files for d in f["decls"]]
DROP = set(t["TDB"])
byfull = {d["full"]: i for i, d in enumerate(decls)}
rows = [l.rstrip("\n").split("|") for l in open(os.path.join(OUT, "tabla.txt"), encoding="utf-8") if l.strip()]
dr = [n for n, fp in rows if n.startswith("ROBINSON") and n in byfull and byfull[n] in DROP]
print("filas RPP de la TABLA cuyo titular es DROP:", len(dr))
# #print axioms lines in RPP library naming DROP decls
n = 0; per = collections.Counter()
dropfull = {decls[i]["full"] for i in DROP}
dropshort = collections.Counter(decls[i]["name"] for i in DROP)
for p in glob.glob(os.path.join(RPP, "ROBINSON_PlusPlus", "**", "*.lean"), recursive=True):
    for ln, L in enumerate(open(p, encoding="utf-8"), 1):
        m = re.match(r"^#print axioms\s+(\S+)", L)
        if not m: continue
        nm = m.group(1)
        hit = nm in dropfull or any(f.endswith("." + nm) for f in dropfull)
        if hit:
            n += 1; per[os.path.relpath(p, RPP)] += 1
print("lineas `#print axioms` sobre DROP en la libreria:", n, dict(per))
