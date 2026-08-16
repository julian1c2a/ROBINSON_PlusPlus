import os, re, sys
R = r"e:\Dropbox\GitHub\lean4\ROBINSON_PlusPlus\ROBINSON_PlusPlus"
imp = {}
for dp, _, fs in os.walk(R):
    for f in fs:
        if not f.endswith(".lean"):
            continue
        p = os.path.join(dp, f)
        rel = os.path.relpath(p, R)
        mod = "ROBINSON_PlusPlus." + rel[:-5].replace(os.sep, ".").replace("/", ".")
        src = open(p, encoding="utf-8").read()
        imp[mod] = re.findall(r"^import\s+(ROBINSON_PlusPlus\.[\w.]+)", src, re.M)

def reach(start):
    seen, st = set(), [start]
    while st:
        m = st.pop()
        if m in seen:
            continue
        seen.add(m)
        st += imp.get(m, [])
    return seen

TARGET = "ROBINSON_PlusPlus.Meta.TcArithPrf"
for m in ["ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf",
          "ROBINSON_PlusPlus.Meta.DerivCondPrf",
          "ROBINSON_PlusPlus.Meta.InAxiomsCodePrf"]:
    if m not in imp:
        print(f"  !! {m} no existe"); continue
    r = reach(m)
    print(f"  {m:52}  TcArithPrf alcanzable = {TARGET in r:5}   ({len(r)} modulos)")
