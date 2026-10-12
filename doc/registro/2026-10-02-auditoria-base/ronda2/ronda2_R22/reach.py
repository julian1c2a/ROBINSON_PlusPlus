# R2-2 (solo lectura): alcanzables desde raices dadas (por nombre corto o completo), resumen por modulo.
import os, re, json, sys, collections
OUT = os.path.dirname(os.path.abspath(__file__))
files = json.load(open(os.path.join(OUT, "parsed.json"), encoding="utf-8"))
g = json.load(open(os.path.join(OUT, "graph.json"), encoding="utf-8"))
decls = [d for f in files for d in f["decls"]]
deps = {int(k): v for k, v in g["deps"].items()}
cls = g["cls"]

def find(name):
    r = [d["id"] if "id" in d else i for i, d in enumerate(decls) if d["full"] == name or d["full"].endswith("." + name) or d["name"] == name]
    return r

roots = []
for a in sys.argv[1:]:
    if a.startswith("--"): continue
    ids = [i for i, d in enumerate(decls) if d["full"] == a or d["full"].endswith("." + a)]
    if not ids: print("NO ROOT", a)
    roots += ids
seen = set(); st = list(roots)
while st:
    x = st.pop()
    if x in seen: continue
    seen.add(x)
    st.extend(deps.get(x, []))

def tag(i):
    d = decls[i]; return f"{d['kind']} {d['full']} [{d['module']}:{d['line']}] cls={cls[i]}"

print("roots:", [decls[r]["full"] for r in roots])
print("reachable:", len(seen))
bylib = collections.Counter(decls[i]["lib"] for i in seen)
print("by lib:", dict(bylib))
kinds = collections.Counter((decls[i]["lib"], decls[i]["kind"]) for i in seen)
print("by kind:", dict(kinds))
cl = collections.Counter((decls[i]["lib"], cls[i]) for i in seen)
print("by class:", dict(cl))
print("\n== reachable axioms:")
for i in sorted(seen):
    if decls[i]["kind"] == "axiom": print("  ", tag(i))
print("\n== reachable RPP decls with class D or mixto:")
for i in sorted(seen, key=lambda i: (decls[i]["module"], decls[i]["line"])):
    if decls[i]["lib"] == "RPP" and cls[i] in ("D", "mixto"): print("  ", tag(i))
print("\n== reachable FOL modules (count):")
fm = collections.Counter(decls[i]["module"] for i in seen if decls[i]["lib"] == "FOL")
for k, v in sorted(fm.items()): print("  ", k, v)
print("\n== reachable RPP modules: (defs, theorems, D/mixto)")
rm = collections.defaultdict(lambda: [0, 0, 0, []])
for i in seen:
    d = decls[i]
    if d["lib"] != "RPP": continue
    r = rm[d["module"]]
    if d["kind"] in ("theorem", "lemma"): r[1] += 1
    else: r[0] += 1; r[3].append(d["name"])
    if cls[i] in ("D", "mixto"): r[2] += 1
for k in sorted(rm):
    r = rm[k]
    print(f"   {k:55s} defs={r[0]:3d} thms={r[1]:4d} D/mix={r[2]:3d}")
if "--defs" in sys.argv:
    print("\n== reachable RPP NON-theorem decls by module:")
    for k in sorted(rm):
        print("  ", k, ":", " ".join(sorted(rm[k][3])))
