import os, re
Q='cuarentena'
RAICES={'CodeCtorKit','D3InDotPrf','EvalListPrf','EvalNthcPrf','InAxiomsCodePrf',
        'LineWFTrackedPrf','Sigma1CorePrf'}
imp={}
for f in os.listdir(Q):
    if not f.endswith('.lean'): continue
    m=f[:-5]
    t=open(os.path.join(Q,f),encoding='utf-8').read()
    imp[m]=[i.split('.')[-1] for i in re.findall(r"^import\s+(ROBINSON_PlusPlus\.[\w.]+)",t,re.M)]
def raices_de(m,seen=None):
    if seen is None: seen=set()
    if m in seen: return set()
    seen.add(m)
    r=set()
    if m in RAICES: r.add(m)
    for i in imp.get(m,[]):
        if i in imp: r |= raices_de(i,seen)
    return r
print(f"{'MODULO':24} {'RAICES QUE LO BLOQUEAN'}")
print("-"*70)
libres=[]
for m in sorted(imp):
    if m in RAICES: continue
    r=raices_de(m)
    if r: print(f"  {m:22} {sorted(r)}")
    else: libres.append(m)
print(f"\n*** RECUPERABLES YA (no dependen de ninguna raiz): {len(libres)} ***")
for m in libres: print("   ",m)
