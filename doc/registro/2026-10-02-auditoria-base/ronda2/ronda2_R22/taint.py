# R2-2 (solo lectura): conjuntos "contaminados" por dependencia transitiva (heuristica) y calibracion con la TABLA.
import json, os, collections, sys
OUT = os.path.dirname(os.path.abspath(__file__))
files = json.load(open(os.path.join(OUT, "parsed.json"), encoding="utf-8"))
g = json.load(open(os.path.join(OUT, "graph.json"), encoding="utf-8"))
decls = [d for f in files for d in f["decls"]]
deps = {int(k): v for k, v in g["deps"].items()}
cls = g["cls"]; DER = g["DER"]
rdeps = collections.defaultdict(set)
for a, bs in deps.items():
    for b in bs: rdeps[b].add(a)
def ids(pred): return {i for i, d in enumerate(decls) if pred(d)}
META4 = ids(lambda d: d["module"] == "FOL.MetaRules" and d["kind"] == "axiom")
AX3 = ids(lambda d: d["lib"] == "RPP" and d["kind"] == "axiom")
def up(seeds):
    seen = set(seeds); st = list(seeds)
    while st:
        x = st.pop()
        for y in rdeps.get(x, ()):
            if y not in seen: seen.add(y); st.append(y)
    return seen
T7 = up(META4 | AX3)
# D-layer: any RPP decl whose statement is about ⊢ (D/mixto) or that uses ⊢/Derives anywhere, plus dependents
DSEED = {i for i, d in enumerate(decls) if d["lib"] == "RPP" and (cls[i] in ("D", "mixto"))}
TD = up(DSEED | META4 | AX3)
# Uses of Derives in the BODY (proof) only:
import re
D_TOK = re.compile(r"⊢(?![ᴴ₀₁₂ᵢ])")
def notac(s): return re.sub(r"\bat\b[^\n:=]*⊢", "at", s)
BODYD = {i for i, d in enumerate(decls) if d["lib"] == "RPP" and (D_TOK.search(notac(d["text"])) or re.search(r"\bDerives\b(?![₀₁₂])", d["text"]))}
TDB = up(DSEED | BODYD | META4 | AX3)

rpp = [i for i, d in enumerate(decls) if d["lib"] == "RPP"]
print("RPP decls:", len(rpp), " theorems:", sum(1 for i in rpp if decls[i]["kind"] == "theorem"))
for nm, S in [("T7 (depende de los 7 axiomas)", T7), ("TD (enunciado ⊢ o depende de él o de los 7)", TD), ("TDB (⊢ en enunciado o PRUEBA, o depende)", TDB)]:
    Sr = [i for i in rpp if i in S]
    print(f"{nm}: {len(Sr)} decls RPP ({sum(1 for i in Sr if decls[i]['kind']=='theorem')} teoremas, {sum(1 for i in Sr if decls[i]['kind']!='theorem')} no-teoremas)")

# calibration vs TABLA
rows = [l.rstrip("\n").split("|") for l in open(os.path.join(OUT, "tabla.txt"), encoding="utf-8") if l.strip()]
byfull = collections.defaultdict(list)
for i, d in enumerate(decls): byfull[d["full"]].append(i)
tp = fp_ = fn = tn = 0; fps = []; fns = []
for name, fp in rows:
    if not name.startswith("ROBINSON"): continue
    if name not in byfull: continue
    i = byfull[name][0]
    real = any(x in fp for x in ["FOL.MetaRules.imp_intro", "FOL.MetaRules.raa", "FOL.MetaRules.or_elim", "FOL.MetaRules.ex_elim", "ax_induction_prim", "ax_list_induction", "ax_axiomsCodeT_eq"])
    pred = i in T7
    if real and pred: tp += 1
    elif real and not pred: fn += 1; fns.append(name)
    elif pred and not real: fp_ += 1; fps.append(name)
    else: tn += 1
print(f"\nCALIBRACION T7 vs TABLA (261 filas RPP): TP={tp} FN={fn} FP={fp_} TN={tn}")
print("  FN:", fns[:20]); print("  FP:", fps[:40])

# per-module summary
mod = collections.defaultdict(lambda: collections.Counter())
for i in rpp:
    d = decls[i]; m = d["module"]
    k = "thm" if d["kind"] == "theorem" else "def"
    mod[m]["all_" + k] += 1
    if i in T7: mod[m]["T7_" + k] += 1
    if i in TD: mod[m]["TD_" + k] += 1
    if i in TDB: mod[m]["TDB_" + k] += 1
with open(os.path.join(OUT, "taint_by_module.txt"), "w", encoding="utf-8") as fo:
    fo.write(f"{'module':52s} {'thm':>5s} {'def':>4s} | {'T7t':>4s} {'T7d':>4s} | {'TDt':>4s} {'TDd':>4s} | {'TDBt':>4s} {'TDBd':>4s}\n")
    for m in sorted(mod):
        c = mod[m]
        fo.write(f"{m:52s} {c['all_thm']:5d} {c['all_def']:4d} | {c['T7_thm']:4d} {c['T7_def']:4d} | {c['TD_thm']:4d} {c['TD_def']:4d} | {c['TDB_thm']:4d} {c['TDB_def']:4d}\n")
json.dump(dict(T7=sorted(T7), TD=sorted(TD), TDB=sorted(TDB)), open(os.path.join(OUT, "taint.json"), "w"))
