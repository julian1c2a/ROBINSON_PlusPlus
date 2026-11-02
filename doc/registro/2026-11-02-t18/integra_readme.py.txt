"""T18, T48 y la reparación de A3IsFCBTracked en sondeos/README.md (ADR-246, 247 y 248)."""
import io, re, sys

RUTA = sys.argv[1]
FILAS = sys.argv[2]        # filas-redactadas.md del agente de T18
INFORME = sys.argv[3]      # informe-t48.md del agente de T48
crudo = io.open(RUTA, encoding='utf-8', newline='').read()
crlf = '\r\n' in crudo
t = crudo.replace('\r\n', '\n')
L = t.split('\n')

# ── 1 · las 19 filas «sin redactar»
fr = io.open(FILAS, encoding='utf-8').read()
textos = {}
for m in re.finditer(r'^### `([A-Za-z0-9_]+)\.lean` \(l\. \d+\)\n\n(.+?)\n(?=\n|$)', fr, re.M | re.S):
    textos[m.group(1)] = m.group(2).strip()
assert len(textos) == 19, len(textos)
hechas = 0
for i, l in enumerate(L):
    m = re.match(r'^\| (\*\*)?`([A-Za-z0-9_]+)\.lean`', l)
    if not m or '⬜ **sin redactar**' not in l:
        continue
    nombre = m.group(2)
    nuevo = textos[nombre].replace(' REGISTRO · ', ' · ').replace(' REGISTRO', '')
    a = l.index('⬜ **sin redactar**')
    assert l.endswith(' |'), nombre
    L[i] = l[:a] + nuevo + ' · ✏️ redactada el 2026‑11‑02 (T18, ADR‑246) |'
    hechas += 1
assert hechas == 19, hechas

# ── 2 · los 28 archivados de T18: el primer error de hoy, tras los dos arreglos
SUBST1_COMPILA = {'HasWitFRealMin', 'ClausuraSubsttc'}
clase = {}
for s in ('HasWitFCritica ClausuraLiftSinWTs ClausuraSubsttc EvalSubstfcPrf HasWitFReal HasWitFRealMin Paso2Guardado '
          'SubstfcEx').split():
    clase[s] = 'SUBST1'
for s in 'DiscriminaTestigoAbierto DiscriminaEcuacional ParticionDiscrimina ParticionTresPredicados'.split():
    clase[s] = 'GUARDA'
for s in 'EnsamblajeMedida GateGuardaEnriquecida SubCodesCritica SubCodesWitness'.split():
    clase[s] = 'AMBD7'
for s in ('CtorDotados DescensoLiftc EnsamblajeTriple EqTransCodeImp2 EvalSubsttc Paso2CasoForall ReflectorAtomoAllIn '
          'ReflectorDesdeConsumidor SubstfcPlanos').split():
    clase[s] = 'D7'
clase['ReflectorForallAnidado'] = 'GNUM'
clase['ParseWitness'] = 'COMPILA'
tabla = {}
for l in io.open(sys.argv[4], encoding='utf-8'):
    c = l.rstrip('\n').split('\t')
    if c[0] in clase:
        tabla[c[0]] = c
assert len(tabla) == 27, len(tabla)   # los 28 menos HasWitTcFn, que va en las 19


def linea(c):
    m = re.match(r'[A-Za-z0-9_]+\.lean:(\d+):', c[6])
    return m.group(1) if m else '?'


def nota(s):
    c = tabla[s]
    k = clase[s]
    pre = 'T18 (2026‑11‑02, ADR‑246): con el renombre de `PrfH_lt_subst2` y los ambiguos cualificados'
    if k == 'COMPILA':
        return pre + ', COMPILA entero (5 s; sus seis «#print axioms», `[propext, Quot.sound]`)'
    if k == 'SUBST1':
        r = (f', avanza a la l. {linea(c)}: `PrfH_lt_subst1`, su gemelo, movido con él a `ChainPrf`; renombrando también '
             'ése, ')
        return pre + r + ('COMPILA entero, `[propext, Quot.sound]`' if s in SUBST1_COMPILA else
                          'avanza hasta los literales `String` de D7')
    if k == 'GUARDA':
        return pre + f', avanza a la l. {linea(c)}: las guardas de testigo de la vía C (ADR‑020)'
    if k == 'AMBD7':
        return pre + f', avanza a la l. {linea(c)}: un literal `String` donde D7 pide `List Char`'
    if k == 'D7':
        return (f'T18 (2026‑11‑02, ADR‑246): su primer error, ya antes de los ambiguos, es un literal `String` donde D7 '
                f'pide `List Char` (l. {linea(c)})')
    if k == 'GNUM':
        return ('T18 (2026‑11‑02, ADR‑246): falla antes que en octubre, en la l. 179, por prf_gnum_lt (retirado en '
                'ADR‑190; hoy `prf_numeral_lt`, el mismo enunciado)')


puestas = 0
for i, l in enumerate(L):
    m = re.match(r'^\| `([A-Za-z0-9_]+)\.lean` \(archivado\)[^|]* \|', l)
    if not m or m.group(1) not in tabla:
        continue
    assert l.endswith(' |')
    L[i] = l[:-2] + ' · ' + nota(m.group(1)) + ' |'
    puestas += 1
assert puestas == 27, puestas

t = '\n'.join(L)


def cambia(v, n):
    global t
    assert t.count(v) == 1, v[:80]
    t = t.replace(v, n)


# ── 3 · la cola de la sección «sin redactar»
cambia('⬜ **La deuda, enunciada**: pasar cada una de estas diecinueve a la tabla de arriba, con su\n'
       'resultado medido. La columna «primera línea útil» está copiada **literalmente** del fichero.\n',
       '⬜ **La deuda, enunciada**: pasar cada una de estas diecinueve a la tabla de arriba, con su\n'
       'resultado medido. La columna «primera línea útil» está copiada **literalmente** del fichero.\n'
       '✏️ **2026‑11‑02 (T18, ADR‑246): las diecinueve, REDACTADAS** —las cinco de aquí y las catorce archivadas de\n'
       'abajo—, leyendo cada fichero y recompilándolo (el del árbol) o compilándolo desde su etiqueta (el archivado):\n'
       'qué medía y qué dio, y, si no lo dice su cabecera, de dónde sale (la fila vieja de arriba o el commit). Nueve de\n'
       'ellas ya tenían fila en la tabla de arriba, sin negrita (`PilotoDiagonal`, `S4`, `S3S5`, `PilotoAislado`,\n'
       '`Magnitud`, `S1Audit`, `KitPayoff`, `TcFormPayoff` y `CarcPayoff`); el texto nuevo es coherente con ella.\n'
       'Lo que dijo el agente que las redactó, en `doc/registro/2026-11-02-t18/`.\n')

# ── 4 · A3IsFCBTracked: de REPARAR a REGISTRO; y los dos de T48, a REGISTRO
m = re.search(r'\| \*\*REGISTRO\*\* \((\d+)\) \|[^\n]*', t)
assert m and m.group(1) == '34'
fila = m.group(0)
nueva = fila.replace('**REGISTRO** (34)', '**REGISTRO** (37)')
assert nueva.endswith(' |')
nueva = nueva[:-2] + ', y desde el 2026‑11‑02 `A3IsFCBTracked` (reparado, ADR‑248), `CongruenciaHueco` y ' \
    '`DuplicadosPorEnunciado` (promovidos de `Probe/`, ADR‑247) |'
t = t.replace(fila, nueva)
cambia('| **REPARAR** (1) | no compila y T10 pide no borrarlo: tres módulos del build citan lo que probó | `A3IsFCBTracked` |',
       '| **REPARAR** (0) | no compila y T10 pide no borrarlo | ninguno desde el 2026‑11‑02: `A3IsFCBTracked`, el único, '
       'compila otra vez (ADR‑248) y pasa a REGISTRO; tres módulos del build citan lo que probó, como procedencia |')
cambia('compilan 43 —el que no, `A3IsFCBTracked`, tampoco compila con v4.31.0— tras corregir una línea de `ChoiceFrontera`;',
       'compilan 43 —el que no, `A3IsFCBTracked`, tampoco compila con v4.31.0 (✏️ 2026‑11‑02, ADR‑248: reparado, compila)— '
       'tras corregir una línea de `ChoiceFrontera`;')

# ── 5 · la fila de A3IsFCBTracked en la tabla principal
i = t.index('| **`A3IsFCBTracked.lean`** ⬆️ **PROMOVIDO EN PARTE**')
j = t.index('\n', i)
fila = t[i:j]
assert fila.endswith(' |')
t = t[:i] + fila[:-2] + (' ✏️ **2026‑11‑02 (T10, ADR‑248): REPARADO**: compila otra vez contra el build (27 s, sin avisos) y '
                         '`pcc_isFCB_tracked` da `[propext, Quot.sound]` (en septiembre, también `Classical.choice` y el '
                         'axioma de Lean del ancla de entonces). Cambiaron las pruebas —las guardas de ADR‑020, por '
                         '`hw_auto`; `PrfH_lt_subst2`, de `ChainPrf`; un ambiguo, cualificado— y UN enunciado auxiliar, '
                         '`PrfH_in_transport`, que gana las tres guardas automáticas de su homónimo promovido '
                         '(`TrackedAtomsPrf.PrfH_in_transport`); los otros 80, idénticos. |') + t[j:]

# ── 6 · las dos filas nuevas de T48, al final de la tabla principal
inf = io.open(INFORME, encoding='utf-8').read()
filas48 = [l for l in inf.split('\n') if l.startswith('| **`CongruenciaHueco.lean`**') or
           l.startswith('| **`DuplicadosPorEnunciado.lean`**')]
assert len(filas48) == 2
filas48 = [f.replace('ADR‑NNN', 'ADR‑247').replace(' REGISTRO |', ' |') for f in filas48]
k = t.index('\n## ⚠️ Dos trampas metodológicas aprendidas hoy (no repetir)')
cola = t[:k].rstrip('\n')
t = cola + '\n' + '\n'.join(filas48) + '\n' + t[k:]

# ── 7 · HasWitTcFn no cita nada retirado
cambia('retirado fallaría después). Medían la capa `⊢`: **no se reparan**, son registro.\n',
       'retirado fallaría después). Medían la capa `⊢`: **no se reparan**, son registro. ✏️ 2026‑11‑02 (T18,\n'
       '  ADR‑246): `HasWitTcFn` no cita nada de la capa `⊢`: con los renombres de `PrfH_lt_subst2` y `PrfH_lt_subst1`\n'
       '  compila entero.\n')

io.open(RUTA, 'w', encoding='utf-8', newline='').write(t.replace('\n', '\r\n') if crlf else t)
print('ok: 19 filas, 27 notas, clasificación, A3, T48, HasWitTcFn')
