# valida_fix.py AWKBIN AWKFILE RAIZ... — (en WSL) compara `LC_ALL=C AWKBIN -f AWKFILE` con oracle2 (el
# oráculo de la tercera revisión, leanlex.py con sus huecos tapados), línea a línea y con el espacio
# colapsado. Las RAICES pueden ser directorios o ficheros .lean.
import os, re, sys, subprocess, tempfile
R3B = "<tmp>/scratchpad/r4/regresiones-v4"
sys.path.insert(0, R3B)
import oracle3 as oracle2
AWKBIN, AWKFILE = sys.argv[1], sys.argv[2]
roots = sys.argv[3:]
SORRY = re.compile(r"(^|[^A-Za-z0-9_'.`])(_root_\.)?(sorry|sorryAx|admit|stop)([^A-Za-z0-9_'!?]|$)")
AX = re.compile(r"^[ \t]*(@\[[^]]*\][ \t]*)*((private|protected|noncomputable|unsafe|partial)[ \t]+)*axiom[ \t]+[^ \t:({]+")
def norm(s): return ' '.join(s.split())
files = []
for r in roots:
    if os.path.isfile(r):
        files.append(r)
    else:
        for d, sub, fs in os.walk(r):
            sub[:] = [x for x in sub if x != '.lake']
            files += [os.path.join(d, f) for f in sorted(fs) if f.endswith('.lean')]
env = dict(os.environ, LC_ALL='C')
tmp = os.path.join(tempfile.gettempdir(), 'valida_fix.out')
nd = nrel = 0
for p in files:
    t = open(p, 'rb').read().decode('utf-8')
    ref, errs = oracle2.strip_text(t)
    with open(tmp, 'wb') as fo:
        subprocess.run([AWKBIN, '-f', AWKFILE, p], stdout=fo, stderr=subprocess.DEVNULL, stdin=subprocess.DEVNULL, env=env)
    aw = open(tmp, 'rb').read().decode('utf-8', 'replace').replace('\r\n', '\n')
    if aw.endswith('\n'):
        aw = aw[:-1]
    rl, al = ref.split('\n'), aw.split('\n')
    src = t.replace('\r\n', '\n').split('\n')
    for k in range(max(len(rl), len(al))):
        a = al[k] if k < len(al) else ''
        r = rl[k] if k < len(rl) else ''
        if norm(a) != norm(r):
            nd += 1
            rel = (bool(SORRY.search(a)) != bool(SORRY.search(r))) or (bool(AX.search(a)) != bool(AX.search(r)))
            nrel += rel
            if nd <= 40:
                print(f'{p}:{k+1}: {"RELEVANTE" if rel else ""}\n   src: {src[k][:160] if k < len(src) else ""!r}\n   awk: {norm(a)[:160]!r}\n   ref: {norm(r)[:160]!r}')
print(f'awk={AWKBIN} fichero={os.path.basename(AWKFILE)} ficheros={len(files)} lineas_distintas={nd} relevantes={nrel}')
