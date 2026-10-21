#!/usr/bin/env python3
# mutantes_strip.py [AWK] — T47 (ADR-180): mutación de UN punto de `strip-lean.awk`: borra, una a una, cada
# sentencia de código, y mira si la PRUEBA DE HUMO de `check-sorry.bash` (la de verdad: su texto y sus líneas
# esperadas se leen del propio script) mata al mutante. De los que sobreviven, los que cambian las líneas con `sorry`
# de algún fixture de las revisiones de ADR-116 son PELIGROSOS: un fallo del despojador que el humo de la CI no ve.
# Sale con 1 si hay alguno peligroso. Antes era `strip-lean/v5/mutantes.py`, con las rutas del scratchpad de la
# sesión y un humo aparte (`humo_v5`); éste sólo usa lo del árbol, y el humo que de verdad corre en la CI.
# Uso (en la raíz de RPP): `make probar-controles`, o `python3 scripts/pruebas/mutantes_strip.py [awk|gawk|mawk]`.
import os, re, subprocess, sys, tempfile

AQUI = os.path.dirname(os.path.abspath(__file__))
RPP = os.path.abspath(os.path.join(AQUI, '..', '..'))
AWK = sys.argv[1] if len(sys.argv) > 1 else 'awk'
STRIP = os.path.join(RPP, 'strip-lean.awk')
SORRY = re.compile(r"(^|[^A-Za-z0-9_'.`])(_root_\.)?(sorry|sorryAx|admit|stop)([^A-Za-z0-9_'!?]|$)")
ENV = dict(os.environ, LC_ALL='C')

# el humo de check-sorry.bash: el heredoc de `SMOKE=$(STRIP <<'EOF'` y la cadena `SMOKE_ESPERADO="…"`
cs = open(os.path.join(RPP, 'check-sorry.bash'), encoding='utf-8').read()
m = re.search(r"SMOKE=\$\(STRIP <<'EOF'[^\n]*\n(.*?)\nEOF\n", cs, re.S)
e = re.search(r'SMOKE_ESPERADO="([^"]*)"', cs)
if not m or not e:
    sys.exit('❌ SIN MEDIR: no encuentro la prueba de humo en check-sorry.bash')
HUMO = (m.group(1) + '\n').encode('utf-8')
ESPERADO = e.group(1)
CRLF = b'throwErrorAt\r\n  stx "a {(sorry : Nat)}"\r\n'


def fixtures():
    fs = []
    for d in ('fx', 'synth', 'censo-entorno'):
        dd = os.path.join(AQUI, 'strip-lean', d)
        fs += sorted(os.path.join(dd, f) for f in os.listdir(dd) if f.endswith('.lean.txt'))
    return fs


def lineas(awkf, entrada=None, stdin=None):
    try:
        r = subprocess.run([AWK, '-f', awkf] + ([entrada] if entrada else []), input=stdin, capture_output=True,
                           env=ENV, timeout=20)
    except subprocess.TimeoutExpired:
        return 'TIMEOUT'
    out = r.stdout.decode('utf-8', 'replace').split('\n')
    return ' '.join(str(i + 1) for i, l in enumerate(out) if SORRY.search(l)) + ' '


def humo(awkf):
    # (como check-sorry: el humo, por el CONJUNTO de líneas; la línea CRLF, por la CUENTA de líneas con `sorry`)
    return lineas(awkf, stdin=HUMO), len(lineas(awkf, stdin=CRLF).split())


def main():
    FIX = fixtures()
    if len(FIX) < 100:
        sys.exit('❌ SIN MEDIR: sólo %d fixtures' % len(FIX))
    h0 = humo(STRIP)
    if h0[0] != ESPERADO or h0[1] != 1:
        sys.exit('❌ SIN MEDIR: el despojador sin mutar no pasa el humo (%s / %s)' % (h0, ESPERADO))
    base = {f: lineas(STRIP, f) for f in FIX}
    src = open(STRIP, encoding='utf-8').read().split('\n')
    tmp = tempfile.mkdtemp()
    vacio = os.path.join(tmp, 'vacio.lean')   # (no os.devnull: en Windows es «nul», y el awk de msys no lo abre)
    open(vacio, 'w').close()
    n = vivos = peligrosos = 0
    print('════ mutantes de strip-lean.awk frente al humo de check-sorry (awk: %s) ════' % AWK)
    for idx, l in enumerate(src):
        st = l.strip()
        if (not st or st.startswith('#') or st in ('{', '}', '} else {') or st.endswith('{') or st.startswith('}')
                or st.startswith('function') or st.startswith('BEGIN') or st.endswith('\\')
                or (st.startswith('if (') and st.endswith(') {'))):
            continue
        mut = src[:]
        mut[idx] = '    # MUT'
        p = os.path.join(tmp, 'm%03d.awk' % idx)
        open(p, 'w', encoding='utf-8', newline='\n').write('\n'.join(mut))
        # que el mutante sea awk válido
        if subprocess.run([AWK, '-f', p, vacio], capture_output=True, env=ENV).returncode != 0:
            continue
        n += 1
        if humo(p) == (ESPERADO, 1):
            vivos += 1
            malos = [os.path.basename(f) for f in FIX if lineas(p, f) != base[f]]
            if malos:
                peligrosos += 1
                print('  ✗ PELIGROSO L%d: %s  ⇒ %s' % (idx + 1, st[:90], ' '.join(malos[:3])))
    print('  mutantes=%d · sobreviven al humo=%d (inocuos en los %d fixtures, salvo los peligrosos) · peligrosos=%d'
          % (n, vivos, len(FIX), peligrosos))
    if n < 50:
        print('❌ SIN MEDIR: sólo %d mutantes (¿se leyó bien strip-lean.awk?)' % n)
        return 2
    print('❌ hay mutantes PELIGROSOS: el humo de check-sorry no los ve' if peligrosos else
          '✅ ningún mutante peligroso: todo fallo de una sentencia que cambia un `sorry` de un fixture, el humo lo ve')
    return 1 if peligrosos else 0


if __name__ == '__main__':
    sys.exit(main())
