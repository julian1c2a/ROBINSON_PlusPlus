import json, os, collections, re
OUT = os.path.dirname(os.path.abspath(__file__))
files = json.load(open(os.path.join(OUT, "parsed.json"), encoding="utf-8"))
g = json.load(open(os.path.join(OUT, "graph.json"), encoding="utf-8"))
t = json.load(open(os.path.join(OUT, "taint.json")))
decls = [d for f in files for d in f["decls"]]
cls = g["cls"]; TD = set(t["TD"])
D_TOK = re.compile(r"⊢(?![ᴴ₀₁₂ᵢ])")
for i, d in enumerate(decls):
    if d["lib"] != "RPP" or i in TD: continue
    m = D_TOK.search(d["text"]) or re.search(r"\bDerives\b(?![₀₁₂])", d["text"])
    if m:
        s = d["text"]; k = m.start()
        print(d["module"].split(".")[-1], d["line"], d["kind"], d["name"], cls[i], "::", s[max(0,k-70):k+50].replace("\n"," "))
