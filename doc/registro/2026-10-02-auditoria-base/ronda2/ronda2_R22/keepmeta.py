import json, os, collections, re
OUT = os.path.dirname(os.path.abspath(__file__))
files = json.load(open(os.path.join(OUT, "parsed.json"), encoding="utf-8"))
g = json.load(open(os.path.join(OUT, "graph.json"), encoding="utf-8"))
t = json.load(open(os.path.join(OUT, "taint.json")))
decls = [d for f in files for d in f["decls"]]
deps = {int(k): v for k, v in g["deps"].items()}
DROP = set(t["TDB"])
keep = [i for i, d in enumerate(decls) if d["lib"] == "RPP" and i not in DROP]
c = collections.Counter(); ex = collections.defaultdict(list)
for i in keep:
    for j in deps.get(i, []):
        if decls[j]["module"] == "FOL.MetaRules" or decls[j]["full"] == "Derives":
            c[decls[j]["full"]] += 1
            if len(ex[decls[j]["full"]]) < 400: ex[decls[j]["full"]].append(i)
print(dict(c))
# for each, how the token appears: show line containing the token
for nm, ids in ex.items():
    tok = nm.split(".")[-1]
    kinds = collections.Counter()
    for i in ids:
        txt = decls[i]["text"]
        if tok == "Derives":
            m = re.search(r"\bDerives\b(?![₀₁₂])", txt)
            if m: kinds["Derives literal"] += 1
            elif "⊢" in txt: kinds["⊢ (tactic goal?)"] += 1
            continue
        for L in txt.split("\n"):
            if re.search(r"(?<![\w.'])" + tok + r"(?![\w'])", L):
                s = L.strip()
                if s.startswith("|"): kinds["case tag | " + tok] += 1
                else: kinds["other: " + s[:70]] += 1
                break
    print(nm, kinds.most_common(8))
