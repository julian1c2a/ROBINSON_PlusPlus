import json, os, re, collections
OUT = os.path.dirname(os.path.abspath(__file__))
files = json.load(open(os.path.join(OUT, "parsed.json"), encoding="utf-8"))
g = json.load(open(os.path.join(OUT, "graph.json"), encoding="utf-8"))
t = json.load(open(os.path.join(OUT, "taint.json")))
decls = [d for f in files for d in f["decls"]]
cls = g["cls"]; DROP = set(t["TDB"])
def norm(n):
    n = re.sub(r"'+$", "", n)
    for pre in ("prf_", "derives_", "prfH_", "PrfH_", "prfI_", "pcc_"):
        if n.startswith(pre): n = n[len(pre):]
    for suf in ("_prf", "_derives", "_prfH", "_Prf", "_real", "_prim", "_ax", "_thm", "_t"):
        if n.endswith(suf) and len(n) > len(suf) + 2: n = n[: -len(suf)]
    return re.sub(r"'+$", "", n)
keepP = collections.defaultdict(list)
for i, d in enumerate(decls):
    if d["lib"] == "RPP" and i not in DROP and d["kind"] == "theorem" and cls[i] == "P": keepP[norm(d["name"])].append(i)
bymod = collections.defaultdict(lambda: [0, 0])
for i in DROP:
    d = decls[i]
    if d["lib"] != "RPP" or d["kind"] != "theorem": continue
    m = d["module"].replace("ROBINSON_PlusPlus.", "")
    bymod[m][0] += 1
    if norm(d["name"]) in keepP: bymod[m][1] += 1
tot = sum(v[0] for v in bymod.values()); tw = sum(v[1] for v in bymod.values())
print(f"teoremas DROP: {tot}; con gemelo Prf por NOMBRE normalizado (heuristico): {tw}")
for m, (a, b) in sorted(bymod.items(), key=lambda x: -x[1][0]): print(f"   {m:32s} {a:4d}  gemelo={b}")
