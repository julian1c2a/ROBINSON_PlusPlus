#!/usr/bin/env python3
# lineWFT_generar.py [--escribir] — T47 (ADR-180): el GENERADOR de las 21 cláusulas de `lineWFT`
# (`ROBINSON_PlusPlus/Meta/ModeloCodigo.lean`), reconstruido. Lee la RHS de cada `ax_lineWF_K` en
# `ROBINSON_PlusPlus/Minimal/Axioms.lean` (lo que sigue a `lineWF (.var 0) ⇔`) y la traduce, TEXTUALMENTE, a una `Prop`
# sobre `Nat`: los conectivos y los códigos del objeto (`Formula.and`, `=eq`, `implc`…) a los de §1ter (`And`, `=`,
# `implcN`…), los accesores sobre la línea `.var 0` a `lenN x`/`carN x`/`nthN x (k)`, los numerales a cifras, los
# códigos cerrados de `ind`/`listInd` a `TC0`…`TCONS`, y `axiomsCodeT` —lo que la regla `thy` mira dentro— a `V`: la
# parametrización que en 2026-10-05 se hizo «a mano» (ADR-148) es aquí una regla más.
# CONTROL: compara lo generado con las cláusulas de `ModeloCodigo.lean`, con el espacio colapsado y sin los
# comentarios de fin de línea; sale con 1 si alguna difiere (y la imprime). Lo que ADEMÁS garantiza el núcleo: cada
# `v_lineWF_*` (`Meta/ModeloCodificacion.lean`) cierra por `Iff.rfl` entre el axioma abierto y su cláusula.
# Antes era un script del scratchpad de la sesión del 2026-10-05, no versionado (T47 de la auditoría).
# Uso (en la raíz de RPP): `make probar-controles`, o `python3 scripts/lineWFT_generar.py` (con `--escribir`,
# imprime las cláusulas generadas).
import os, re, sys

RPP = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
AXIOMAS = os.path.join(RPP, 'ROBINSON_PlusPlus', 'Minimal', 'Axioms.lean')
MODELO = os.path.join(RPP, 'ROBINSON_PlusPlus', 'Meta', 'ModeloCodigo.lean')
# (para verlo fallar: LINEWFT_MODELO=<copia mutada> python3 scripts/lineWFT_generar.py)
MODELO = os.environ.get('LINEWFT_MODELO', MODELO)
TAGS = ['p1', 'p2', 'c1', 'c2', 'c3', 'j1', 'j2', 'j3', 'efq', 'q1', 'q2', 'q3', 'eqrefl', 'leibniz', 'p3', 'thy',
        'mp', 'gen', 'ind', 'qconf', 'listInd']

# las sustituciones, en ORDEN (las más largas antes que sus prefijos)
REGLAS = [
    (r'nthc \(\.var 0\) \(numeralM (\d+)\)', r'nthN x (\1)'),
    (r'lenc \(\.var 0\)', 'lenN x'),
    (r'carc \(\.var 0\)', 'carN x'),
    (r'In \(carN x\) axiomsCodeT', 'memN (carN x) V'),
    (r'termCodeM \(cons \(\.var 1\) \(\.var 0\)\)', 'TCONS'),
    (r'termCodeM \(succ \(\.var 0\)\)', 'TCS'),
    (r'termCodeM zero', 'TC0'),
    (r'termCodeM nil', 'TNIL'),
    (r'liftfc \(succ \(succ zero\)\)', 'liftfcN 2'),
    (r'liftfc \(succ zero\)', 'liftfcN 1'),
    (r'liftfc \(zero\)', 'liftfcN 0'),
    (r'substfc \(zero\)', 'substfcN 0'),
    (r'Formula\.and', 'And'),
    (r'=eq numeralM (\d+)', r'= \1'),
    (r'=eq', '='),
    (r'\bhasWitF\b', 'hasWitFN'),
    (r'\bhasWit\b', 'hasWitN'),
    (r'\bimplc\b', 'implcN'), (r'\bforallc\b', 'forallcN'), (r'\bexc\b', 'excN'), (r'\bandc\b', 'andcN'),
    (r'\borc\b', 'orcN'), (r'\beqc\b', 'eqcN'), (r'\bbotc\b', 'botcN'),
]


def norm(s):
    return ' '.join(s.split())


def rhs_axioma(src, tag):
    """El texto de la RHS de `ax_lineWF_<tag>`: tras `lineWF (.var 0) ⇔`, sin los dos `)` que cierran el `impl` y el
    `forall_`."""
    m = re.search(r'^def ax_lineWF_%s : Formula :=\n(.*?)(?=^def |\Z)' % re.escape(tag), src, re.S | re.M)
    if not m:
        sys.exit('❌ no encuentro ax_lineWF_%s en Axioms.lean' % tag)
    cuerpo = norm(m.group(1))
    k = cuerpo.find('lineWF (.var 0) ⇔ ')
    if k < 0 or not cuerpo.endswith('))'):
        sys.exit('❌ ax_lineWF_%s no tiene la forma esperada' % tag)
    return cuerpo[k + len('lineWF (.var 0) ⇔ '):-2]


def traduce(rhs):
    for (pat, rep) in REGLAS:
        rhs = re.sub(pat, rep, rhs)
    return rhs


def clausulas_modelo(src):
    """{K: texto} de `def lineWFT (V : Nat) : Nat → Nat → Prop`, sin los comentarios de fin de línea."""
    m = re.search(r'^def lineWFT \(V : Nat\) : Nat → Nat → Prop\n(.*?)^  \| _, _ => False', src, re.S | re.M)
    if not m:
        sys.exit('❌ no encuentro def lineWFT en ModeloCodigo.lean')
    sin_coment = '\n'.join(re.sub(r'\s+--.*$', '', l) for l in m.group(1).split('\n'))
    res = {}
    for c in re.finditer(r'^  \| (\d+), x => (.*?)(?=^  \| |\Z)', sin_coment, re.S | re.M):
        res[int(c.group(1))] = norm(c.group(2))
    return res


def main():
    ax = open(AXIOMAS, encoding='utf-8').read().replace('\r\n', '\n')
    mo = open(MODELO, encoding='utf-8').read().replace('\r\n', '\n')
    gen = {k: traduce(rhs_axioma(ax, t)) for k, t in enumerate(TAGS)}
    if '--escribir' in sys.argv:
        for k, t in enumerate(TAGS):
            print('  | %d, x => %s   -- %s' % (k, gen[k], t))
        return 0
    real = clausulas_modelo(mo)
    print('════ lineWFT: las 21 cláusulas de ModeloCodigo.lean frente a la traducción de ax_lineWF_* ════')
    malas = 0
    for k, t in enumerate(TAGS):
        if real.get(k) != gen[k]:
            malas += 1
            print('  ✗ %d (%s)\n      generada: %s\n      en el fuente: %s' % (k, t, gen[k], real.get(k)))
    if len(real) != len(TAGS):
        print('  ✗ ModeloCodigo.lean tiene %d cláusulas, y las etiquetas son %d' % (len(real), len(TAGS)))
        malas += 1
    if malas:
        print('❌ %d cláusula(s) de lineWFT no son la traducción de su axioma' % malas)
        return 1
    print('  ✓ las 21, idénticas (con el espacio colapsado): `lineWFT` es la traducción mecánica de `ax_lineWF_*`')
    print('✅ lineWFT cuadra con su generador')
    return 0


if __name__ == '__main__':
    sys.exit(main())
