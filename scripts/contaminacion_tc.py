import os, re
R = r"e:\Dropbox\GitHub\lean4\ROBINSON_PlusPlus\ROBINSON_PlusPlus"
imp = {}
for dp,_,fs in os.walk(R):
    for f in fs:
        if not f.endswith(".lean"): continue
        p = os.path.join(dp,f)
        mod = "ROBINSON_PlusPlus." + os.path.relpath(p,R)[:-5].replace(os.sep,".")
        imp[mod] = re.findall(r"^import\s+(ROBINSON_PlusPlus\.[\w.]+)", open(p,encoding="utf-8").read(), re.M)
def reach(s):
    seen,st=set(),[s]
    while st:
        m=st.pop()
        if m in seen: continue
        seen.add(m); st += imp.get(m,[])
    return seen
T="ROBINSON_PlusPlus.Meta.TcArithPrf"
cont=[m for m in imp if m!="ROBINSON_PlusPlus.Meta" and T in reach(m)]
libre=[m for m in imp if m!="ROBINSON_PlusPlus.Meta" and T not in reach(m)]
print(f"TOTAL modulos: {len(imp)}")
print(f"\nCONTAMINADOS (alcanzan TcArithPrf): {len(cont)}")
for m in sorted(cont): print("   ", m.replace("ROBINSON_PlusPlus.",""))
print(f"\nLIBRES: {len(libre)}")
