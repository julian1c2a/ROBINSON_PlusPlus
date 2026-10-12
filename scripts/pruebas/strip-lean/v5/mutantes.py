# mutantes.py AWKBIN — (en WSL) mutación de un punto de strip-lean.awk v5: borra cada sentencia de código y
# mira si la prueba de humo de check-sorry (el CONJUNTO de líneas, más la línea CRLF) la mata; de los que
# sobreviven, cuáles cambian las líneas con `sorry` de algún fixture de las revisiones (supervivientes PELIGROSOS).
import os, re, subprocess, sys, tempfile, glob
S = '<tmp>/scratchpad'
AWKBIN = sys.argv[1] if len(sys.argv) > 1 else '/usr/bin/gawk'
SRC = open(S + '/v5/strip-lean.awk', encoding='utf-8').read().split('\n')
HUMO = S + '/v5/humo_v5.lean'
ESPERADO = os.environ['ESPERADO']
SORRY = re.compile(r"(^|[^A-Za-z0-9_'.`])(_root_\.)?(sorry|sorryAx|admit|stop)([^A-Za-z0-9_'!?]|$)")
FIX = sorted(glob.glob(S + '/r3b/strip-v3/fx/*.lean') + glob.glob(S + '/rev2/synth/*.lean') +
             glob.glob(S + '/r4/censo-entorno/fixtures/*.lean'))
env = dict(os.environ, LC_ALL='C')
def lineas(awkf, entrada, stdin=None):
    try:
        r = subprocess.run([AWKBIN, '-f', awkf] + ([entrada] if entrada else []), input=stdin, capture_output=True,
                           env=env, timeout=5)
    except subprocess.TimeoutExpired:
        return 'TIMEOUT'
    out = r.stdout.decode('utf-8', 'replace').split('\n')
    return ' '.join(str(i + 1) for i, l in enumerate(out) if SORRY.search(l)) + ' '
def humo(awkf):
    a = lineas(awkf, HUMO)
    c = lineas(awkf, None, b'throwErrorAt\r\n  stx "a {(sorry : Nat)}"\r\n')
    return a, c
base = {f: lineas(S + '/v5/strip-lean.awk', f) for f in FIX}
h0 = humo(S + '/v5/strip-lean.awk')
assert h0[0] == ESPERADO and h0[1].strip() == '2', h0
tmp = tempfile.mkdtemp()
n = vivos = peligrosos = 0
for idx, l in enumerate(SRC):
    st = l.strip()
    if not st or st.startswith('#') or st in ('{', '}', '} else {') or st.endswith('{') or st.startswith('}') \
       or st.startswith('function') or st.startswith('BEGIN') or st.endswith('\\') or st.startswith('if (') and st.endswith(') {'):
        continue
    mut = SRC[:]; mut[idx] = '    # MUT'
    p = os.path.join(tmp, 'm%03d.awk' % idx)
    open(p, 'w', encoding='utf-8').write('\n'.join(mut))
    # que el mutante sea awk válido
    if subprocess.run([AWKBIN, '-f', p, '/dev/null'], capture_output=True, env=env).returncode != 0:
        continue
    n += 1
    a, c = humo(p)
    if a == ESPERADO and c.strip() == '2':
        vivos += 1
        malos = [os.path.basename(f) for f in FIX if lineas(p, f) != base[f]]
        if malos:
            peligrosos += 1
            print('PELIGROSO L%d: %s  ⇒ %s' % (idx + 1, st[:90], ' '.join(malos[:4])))
        else:
            print('vivo (inocuo en los fixtures) L%d: %s' % (idx + 1, st[:90]))
print('mutantes=%d sobreviven_al_humo=%d peligrosos=%d fixtures=%d' % (n, vivos, peligrosos, len(FIX)))
