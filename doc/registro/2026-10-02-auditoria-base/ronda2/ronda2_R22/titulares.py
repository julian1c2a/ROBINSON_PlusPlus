import json, os, re
OUT = os.path.dirname(os.path.abspath(__file__))
files = json.load(open(os.path.join(OUT, "parsed.json"), encoding="utf-8"))
t = json.load(open(os.path.join(OUT, "taint.json")))
decls = [d for f in files for d in f["decls"]]
DROP = set(t["TDB"])
pat = re.compile(r"^(goedel_|godel|repr_pos|d1|d2|d3|negVerifier|reflects_of|derives_completo|derives_exclusivo|derives_decide|consistentH_of|necessitation|provability_|deuda_)")
for nm, S in [("SE VAN", [i for i in DROP if decls[i]["lib"] == "RPP"]), ("SE QUEDAN", [i for i, d in enumerate(decls) if d["lib"] == "RPP" and i not in DROP])]:
    L = sorted({(decls[i]["module"].replace("ROBINSON_PlusPlus.", ""), decls[i]["name"], decls[i]["line"]) for i in S if pat.match(decls[i]["name"]) and decls[i]["kind"] == "theorem"})
    print(nm, len(L)); 
    for x in L: print("   ", x)
