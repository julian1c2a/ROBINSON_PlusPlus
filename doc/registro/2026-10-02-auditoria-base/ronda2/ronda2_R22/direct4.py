import json, os, collections
OUT = os.path.dirname(os.path.abspath(__file__))
files = json.load(open(os.path.join(OUT, "parsed.json"), encoding="utf-8"))
g = json.load(open(os.path.join(OUT, "graph.json"), encoding="utf-8"))
decls = [d for f in files for d in f["decls"]]
deps = {int(k): v for k, v in g["deps"].items()}
M4 = {i for i, d in enumerate(decls) if d["module"] == "FOL.MetaRules" and d["kind"] == "axiom"}
W = {i for i, d in enumerate(decls) if d["module"] == "FOL.MetaRules" and d["kind"] != "axiom"}
users4 = [i for i, d in enumerate(decls) if d["lib"] == "RPP" and set(deps.get(i, [])) & M4 and d["name"] != "eq_congr_pred"]
usersW = [i for i, d in enumerate(decls) if d["lib"] == "RPP" and set(deps.get(i, [])) & W and d["name"] != "eq_congr_pred"]
print("decls RPP que usan DIRECTAMENTE alguno de los 4 axiomas:", len(users4), "en", len({decls[i]['module'] for i in users4}), "modulos")
print("decls RPP con arista a envoltorios de MetaRules (mp/gen/dne/and_intro/...; incluye falsos positivos por etiquetas de caso):", len(usersW))
