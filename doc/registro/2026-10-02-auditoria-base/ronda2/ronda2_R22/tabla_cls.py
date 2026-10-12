import json, os, collections
OUT = os.path.dirname(os.path.abspath(__file__))
files = json.load(open(os.path.join(OUT, "parsed.json"), encoding="utf-8"))
g = json.load(open(os.path.join(OUT, "graph.json"), encoding="utf-8"))
decls = [d for f in files for d in f["decls"]]
cls = g["cls"]
byfull = collections.defaultdict(list)
for i, d in enumerate(decls): byfull[d["full"]].append(i)
rows = [l.rstrip("\n").split("|") for l in open(os.path.join(OUT, "tabla.txt"), encoding="utf-8") if l.strip()]
c = collections.Counter(); miss = []
out = []
for name, fp in rows:
    ids = byfull.get(name)
    if not ids:
        miss.append(name); continue
    i = ids[0]; d = decls[i]
    tainted = any(x in fp for x in ["FOL.MetaRules", "ax_induction_prim", "ax_list_induction", "ax_axiomsCodeT_eq"])
    c[(d["lib"], cls[i], "tainted" if tainted else "clean")] += 1
    out.append((d["lib"], cls[i], tainted, d["module"], d["name"], fp))
for k, v in sorted(c.items()): print(k, v)
print("not found:", len(miss), miss[:20])
print("\nRPP clean rows whose STATEMENT is about ⊢ (D or mixto):")
for lib, cl, t, m, n, fp in sorted(out):
    if lib == "RPP" and cl in ("D", "mixto") and not t: print("  ", cl, m, n, fp)
print("\nRPP tainted rows with class otro / mixto:")
for lib, cl, t, m, n, fp in sorted(out):
    if lib == "RPP" and t and cl in ("otro", "mixto"): print("  ", cl, m, n)
print("\nFOL rows with class D:")
for lib, cl, t, m, n, fp in sorted(out):
    if lib == "FOL" and cl == "D": print("  ", cl, m, n, fp)
