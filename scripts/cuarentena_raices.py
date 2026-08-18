import os, re
Q='cuarentena'; R='ROBINSON_PlusPlus'
RETIRADOS = ["prf_tc_cons","prf_tc_of_cons","prf_tc_chars","prf_tc_str","prf_tc_term","prf_tc_terms",
             "prf_tc_form","prf_tc_cons'","tc_of_cons","tc_chars","tc_str","tc_term","tc_terms",
             "tc_form","diag_arith","godelC_fixedpoint","goedel_first_real","godelC'_fixedpoint"]
def strip(t):
    out=list(t); i=0; n=len(t)
    while i<n:
        if t.startswith("/-",i):
            d,j=1,i+2
            while j<n and d>0:
                if t.startswith("/-",j): d+=1; j+=2
                elif t.startswith("-/",j): d-=1; j+=2
                else: j+=1
            for k in range(i,min(j,n)):
                if out[k]!="\n": out[k]=" "
            i=j
        elif t.startswith("--",i):
            j=t.find("\n",i); j=n if j<0 else j
            for k in range(i,j): out[k]=" "
            i=j
        else: i+=1
    return "".join(out)
raiz, noraiz = [], []
for f in sorted(os.listdir(Q)):
    if not f.endswith('.lean'): continue
    t=strip(open(os.path.join(Q,f),encoding='utf-8').read())
    usa=[n for n in RETIRADOS if re.search(r"(?<![A-Za-z0-9_])"+re.escape(n)+r"(?![A-Za-z0-9_'])",t)]
    (raiz if usa else noraiz).append((f[:-5], usa))
print(f"RAICES ({len(raiz)}) -- usan DIRECTAMENTE algo retirado, hay que refundarlas:")
for m,u in raiz: print(f"   {m:22} usa: {sorted(set(u))}")
print(f"\nNO-RAICES ({len(noraiz)}) -- cayeron SOLO por dependencia:")
for m,_ in noraiz: print(f"   {m}")
