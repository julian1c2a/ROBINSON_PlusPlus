import json, os, collections, re
OUT = os.path.dirname(os.path.abspath(__file__))
files = json.load(open(os.path.join(OUT, "parsed.json"), encoding="utf-8"))
g = json.load(open(os.path.join(OUT, "graph.json"), encoding="utf-8"))
t = json.load(open(os.path.join(OUT, "taint.json")))
decls = [d for f in files for d in f["decls"]]
cls = g["cls"]
TD = set(t["TD"]); TDB = set(t["TDB"]); T7 = set(t["T7"])
diff = [i for i in TDB - TD if decls[i]["lib"] == "RPP"]
c = collections.Counter((decls[i]["module"], cls[i]) for i in diff)
for k, v in c.most_common(60): print(v, k)
D_TOK = re.compile(r"⊢(?![ᴴ₀₁₂ᵢ])")
print("---- sample")
for i in diff[:12]:
    d = decls[i]
    m = D_TOK.search(d["text"]) or re.search(r"\bDerives\b(?![₀₁₂])", d["text"])
    s = d["text"]
    k = m.start() if m else 0
    print(d["module"], d["name"], cls[i], "::", s[max(0,k-80):k+40].replace("\n"," "))
