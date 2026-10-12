# R2-2 (solo lectura): si se BORRAN las declaraciones DROP, ¿cuantas citas de [B] quedan muertas sin marcador?
import json, os, re, collections, glob
OUT = os.path.dirname(os.path.abspath(__file__))
RPP = r"E:/dropbox/github/lean4/ROBINSON_PlusPlus"
files = json.load(open(os.path.join(OUT, "parsed.json"), encoding="utf-8"))
t = json.load(open(os.path.join(OUT, "taint.json")))
decls = [d for f in files for d in f["decls"]]
DROP = set(t["TDB"])
drop_names = collections.Counter(decls[i]["name"] for i in DROP if decls[i]["lib"] == "RPP")
# names that survive anywhere (RPP keep, FOL, cuarentena): approximate with parsed decls not in DROP
alive = set(d["name"] for i, d in enumerate(decls) if i not in DROP)
# cuarentena decl names
for p in glob.glob(os.path.join(RPP, "cuarentena", "**", "*.lean"), recursive=True):
    for m in re.finditer(r"(?:theorem|def|abbrev|axiom|noncomputable def) +([A-Za-z_][A-Za-z0-9_']*)", open(p, encoding="utf-8").read()):
        alive.add(m.group(1))
auth = "REFERENCE.md CURRENT-STATUS-PROJECT.md DEPENDENCIES.md DECISIONS.md README.md AXIOMS.md GODEL-STATUS.md NEXT-STEPS.md".split()
auth += [os.path.relpath(p, RPP) for p in glob.glob(os.path.join(RPP, "doc", "REFERENCE-*.md"))]
auth += ["cuarentena/README.md", "sondeos/README.md"]
DEAD = r"YA NO EXISTE|NO EXISTEN|retirad|RETIRADO|eliminad|borrad|legacy|F7a|histórico|ANTERIORES|🗑️|muert|Aquí vivía|tampoco existe|inexistente|desapareci|ya no son|se borró|propuest|candidat|hipot[eé]tic|har[ií]a falta|si se |habr[ií]a que|añadir |descartad|no existe|NO EXISTE|sin materializar|20[0-9]{2}-[0-9]{2}-[0-9]{2}|falta|FALTA|construir|objetivo|medir|sin medir|pendiente|⏳|abiert|necesita|exige|pide|TAREA|hace falta|no hay ni habrá|sub‑familia|sub-familia|buscaba|buscó|usan la"
pat = re.compile(r"`((?:prf_|pcc_|goedel_|godel|d[123]_|repr_|ax_)[A-Za-z0-9_']+)`")
newly_dead = collections.Counter(); lines_bad = collections.Counter(); per_doc = collections.Counter()
examples = collections.defaultdict(list)
for doc in auth:
    p = os.path.join(RPP, doc)
    if not os.path.exists(p): continue
    for ln, line in enumerate(open(p, encoding="utf-8"), 1):
        for m in pat.finditer(line):
            s = m.group(1)
            if s.startswith("ax_") and len(s) > 3 and s[3].isupper(): continue
            # alive if some surviving decl STARTS with the symbol (prose abbreviates), mimicking [B]
            if any(a.startswith(s) for a in alive if a[:3] == s[:3]):
                continue
            if s not in drop_names and not any(n.startswith(s) for n in drop_names): continue  # not created by us
            if re.search(DEAD, line): continue
            newly_dead[s] += 1; per_doc[doc] += 1
            if len(examples[s]) < 2: examples[s].append(f"{doc}:{ln}")
print("simbolos [B] que pasarian a MUERTOS sin marcador si se BORRAN (no si van a cuarentena/):", len(newly_dead))
print("lineas afectadas por documento:", dict(per_doc))
for s, n in newly_dead.most_common(80): print(f"   {n:3d} {s}  {examples[s]}")
