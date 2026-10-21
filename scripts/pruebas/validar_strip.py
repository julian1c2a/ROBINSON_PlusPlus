#!/usr/bin/env python3
# validar_strip.py [AWK] — T47 (ADR-180): valida `strip-lean.awk` contra el ORÁCULO —el lexer de referencia
# (`leanlex.py`, que sigue función a función al de Lean v4.31.0) con las dos capas que le tapan los huecos conocidos
# (`oracle2.py` y `oracle3.py`, rescatadas el 2026-10-21)—, línea a línea y con el espacio colapsado, sobre:
#   · el CORPUS: todo `.lean` versionado de RPP y de FOL (`git ls-files`); lo esperado, 0 líneas distintas;
#   · los FIXTURES de las revisiones de ADR-116 (`strip-lean/{fx,synth,censo-entorno}/*.lean.txt`, 182): lo esperado,
#     las líneas de `FIXTURES_CONOCIDOS`, donde el que se equivoca es el oráculo. MEDIDO el 2026-10-21: ninguna (ADR-116
#     contaba dos, `throwNamedErrorAt args[0]! …`, que hoy cuadran).
# Sale con 0 si todo es lo esperado y con 1 si no. Antes era un script del scratchpad con rutas de la sesión
# (`strip-lean/v5/valida_o3.py`, que importaba el `oracle3` de su carpeta); éste sólo usa lo del árbol. Con el
# `leanlex.py` solo, sin las dos capas, los fixtures dan 74 líneas distintas: son los huecos que ellas tapan.
# Uso (en la raíz de RPP): `make probar-controles`, o `python3 scripts/pruebas/validar_strip.py [awk|gawk|mawk]`.
import os, re, subprocess, sys

AQUI = os.path.dirname(os.path.abspath(__file__))
RPP = os.path.abspath(os.path.join(AQUI, '..', '..'))
FOL = os.path.abspath(os.path.join(RPP, '..', 'FOL'))
sys.path.insert(0, AQUI)
import oracle3 as oraculo  # noqa: E402  (leanlex.py + oracle2.py + oracle3.py: el oráculo de la validación de la v5)

AWK = sys.argv[1] if len(sys.argv) > 1 else 'awk'
STRIP = os.path.join(RPP, 'strip-lean.awk')
SORRY = re.compile(r"(^|[^A-Za-z0-9_'.`])(_root_\.)?(sorry|sorryAx|admit|stop)([^A-Za-z0-9_'!?]|$)")
AX = re.compile(r"^[ \t]*(@\[[^]]*\][ \t]*)*((private|protected|noncomputable|unsafe|partial)[ \t]+)*axiom[ \t]+[^ \t:({]+")
# (fixture, línea) donde el oráculo se equivoca: MEDIDAS el 2026-10-21 con este script, ninguna
FIXTURES_CONOCIDOS = set()


def norm(s):
    return ' '.join(s.split())


def versionados(raiz):
    r = subprocess.run(['git', '-C', raiz, 'ls-files', '*.lean'], capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit('❌ SIN MEDIR: git ls-files falla en %s' % raiz)
    return [os.path.join(raiz, p) for p in r.stdout.split('\n') if p]


def fixtures():
    fs = []
    for d in ('fx', 'synth', 'censo-entorno'):
        dd = os.path.join(AQUI, 'strip-lean', d)
        fs += sorted(os.path.join(dd, f) for f in os.listdir(dd) if f.endswith('.lean.txt'))
    return fs


ENV = dict(os.environ, LC_ALL='C')


def compara(p):
    """→ lista de (línea, relevante, awk, oráculo) donde difieren."""
    t = open(p, 'rb').read().decode('utf-8')
    ref, _errs = oraculo.strip_text(t)
    r = subprocess.run([AWK, '-f', STRIP, p], capture_output=True, env=ENV, stdin=subprocess.DEVNULL)
    if r.returncode != 0:
        sys.exit('❌ SIN MEDIR: %s -f strip-lean.awk falla en %s' % (AWK, p))
    aw = r.stdout.decode('utf-8', 'replace').replace('\r\n', '\n')
    if aw.endswith('\n'):
        aw = aw[:-1]
    rl, al = ref.split('\n'), aw.split('\n')
    dif = []
    for k in range(max(len(rl), len(al))):
        a = al[k] if k < len(al) else ''
        o = rl[k] if k < len(rl) else ''
        if norm(a) != norm(o):
            rel = (bool(SORRY.search(a)) != bool(SORRY.search(o))) or (bool(AX.search(a)) != bool(AX.search(o)))
            dif.append((k + 1, rel, a, o))
    return dif


def main():
    corpus = versionados(RPP) + versionados(FOL)
    fx = fixtures()
    if len(corpus) < 100 or len(fx) < 100:
        sys.exit('❌ SIN MEDIR: corpus de %d ficheros y %d fixtures (¿falta ../FOL o los fixtures?)' % (len(corpus), len(fx)))
    print('════ strip-lean.awk frente al oráculo (leanlex + oracle2 + oracle3; awk: %s) ════' % AWK)
    nc = 0
    for p in corpus:
        for (k, rel, a, o) in compara(p):
            nc += 1
            if nc <= 10:
                print('  ✗ %s:%d%s\n      awk:     %s\n      oráculo: %s' % (os.path.relpath(p, RPP), k,
                      ' (CAMBIA un sorry o un axiom)' if rel else '', a[:150], o[:150]))
    fallo = False
    if nc == 0:
        print('  ✓ corpus: %d ficheros versionados de RPP y FOL, 0 líneas distintas' % len(corpus))
    else:
        print('  ✗ corpus: %d líneas distintas en %d ficheros' % (nc, len(corpus)))
        fallo = True
    vistas = set()
    for p in fx:
        for (k, rel, a, o) in compara(p):
            vistas.add((os.path.basename(p), k))
    if vistas == FIXTURES_CONOCIDOS:
        print('  ✓ fixtures: %d, y difieren sólo las %d líneas conocidas (las del oráculo)' % (len(fx), len(vistas)))
    else:
        for (f, k) in sorted(vistas - FIXTURES_CONOCIDOS):
            print('  ✗ fixture %s:%d difiere, y no es de las conocidas' % (f, k))
        for (f, k) in sorted(FIXTURES_CONOCIDOS - vistas):
            print('  ✗ fixture %s:%d era conocida y ya no difiere (¿se arregló el oráculo? actualizar la lista)' % (f, k))
        fallo = True
    print('❌ strip-lean.awk NO cuadra con el oráculo' if fallo else '✅ strip-lean.awk cuadra con el oráculo')
    return 1 if fallo else 0


if __name__ == '__main__':
    sys.exit(main())
