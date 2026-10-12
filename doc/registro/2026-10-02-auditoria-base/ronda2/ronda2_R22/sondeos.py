# R2-2 (solo lectura): que sondeos/ (y Probe/) quedarian rotos por la retirada: imports de modulos borrados
# y uso por NOMBRE de declaraciones DROP o de FOL.MetaRules (heuristico: token = nombre corto o cualificado).
import json, os, re, collections, glob
OUT = os.path.dirname(os.path.abspath(__file__))
RPP = r"E:/dropbox/github/lean4/ROBINSON_PlusPlus"
files = json.load(open(os.path.join(OUT, "parsed.json"), encoding="utf-8"))
t = json.load(open(os.path.join(OUT, "taint.json")))
decls = [d for f in files for d in f["decls"]]
DROP = set(t["TDB"])
P = "ROBINSON_PlusPlus."
DEL = set(P + m for m in """Full.Bounded Full.Divisibility Full.Division Full.Lists Full.Mod2 Full.Primality Meta.AxiomListCode
Meta.DerivCond Meta.Induction Meta.LineWFDerives Meta.ListInductionArith Meta.Necessitation Meta.OmegaStrength Meta.Reflection
Meta.StepArith Minimal.Theorems.Block1 Minimal.Theorems.Block2 Minimal.Theorems.Block3 Minimal.Theorems.Block4
Minimal.Theorems.Block4_C5 Minimal.Theorems.Block4_C6_C7 Minimal.Theorems.Block5 Minimal.Theorems.Block6 Minimal.Theorems.Block7
Minimal.Theorems.Block8 Full.Factorization Full.StrongInduction""".split()) | {"FOL.MetaRules", "FOL.Core", "FOL.Inconsistencia"}
dropnames = {}
for i in DROP:
    d = decls[i]
    if d["lib"] == "RPP": dropnames[d["name"]] = d["module"]
# names that ALSO survive somewhere (ambiguous short names) are excluded to avoid false positives
alive = collections.Counter(d["name"] for i, d in enumerate(decls) if i not in DROP)
meta4 = {"imp_intro", "raa", "or_elim", "ex_elim"}
IDENT = re.compile(r"(?<![\w'.])([A-Za-z_][\w'!?ᵢᴴ₀-₉]*(?:\.[A-Za-z_][\w'!?ᵢᴴ₀-₉]*)*)")
def strip(src):
    src = re.sub(r"/-.*?-/", "", src, flags=re.S)
    return re.sub(r"--[^\n]*", "", src)
res = []
for folder in ["sondeos", "Probe"]:
    for p in sorted(glob.glob(os.path.join(RPP, folder, "*.lean"))):
        raw = open(p, encoding="utf-8").read(); s = strip(raw)
        imps = re.findall(r"^import\s+(\S+)", s, re.M)
        bad_imp = [x for x in imps if x in DEL or x == "FOL"]
        toks = set(IDENT.findall(s))
        def rppish(t):
            if "." not in t: return True
            head = t.split(".")[0]
            return head in ("ROBINSON_PlusPlus", "Full", "Minimal", "Meta", "Axioms", "Hilbert") or head[0].islower() is False and head in ("FOL",)
        used = sorted({t.split(".")[-1] for t in toks if rppish(t) and t.split(".")[-1] in dropnames and alive[t.split(".")[-1]] == 0})
        um = sorted({t.split(".")[-1] for t in toks if t.split(".")[-1] in meta4 and ("." not in t or "MetaRules" in t or "Minimal.Axioms" in t)})
        uses_D = bool(re.search(r"⊢(?![ᴴ₀₁₂ᵢ])", re.sub(r"\bat\b[^\n:=]*⊢", "at", s)))
        res.append((folder + "/" + os.path.basename(p), imps, bad_imp, used, um, uses_D))
broken = [r for r in res if r[2] or r[3] or r[4]]
print("ficheros:", len(res), " rotos (import borrado / usa DROP / usa meta-regla):", len(broken), " usan ⊢ en el texto:", sum(1 for r in res if r[5]))
for fn, imps, bi, used, um, ud in broken:
    print(f"  {fn}: imports_borrados={[x.replace(P,'') for x in bi]} DROP={used[:8]}{'…' if len(used)>8 else ''} meta={um}")
print("\nNO rotos pero mencionan ⊢ (sobreviven, pero enuncian sobre Derives):")
for fn, imps, bi, used, um, ud in res:
    if not (bi or used or um) and ud: print("  ", fn)
