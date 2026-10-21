# regenera_guard.py FICHERO SALIDA_DE_LEAN — T42b: reescribe los docstrings de los `#guard_msgs` que no cuadran con el
# mensaje que GENERA el Lean de ahora, a partir del diff que imprime el propio `#guard_msgs` (líneas «  », «- », «+ »).
# Avisa si un bloque que fijaba un `error` pasa a no fijar ninguno (el núcleo dejó de rechazar: eso es otra cosa).
import io, os, re, sys
src_p, out_p = sys.argv[1], sys.argv[2]
raw = io.open(src_p, encoding='utf-8', newline='').read()
crlf = '\r\n' in raw
src = raw.replace('\r\n', '\n').split('\n')
out = io.open(out_p, encoding='utf-8', errors='replace').read().replace('\r\n', '\n').split('\n')
base = os.path.basename(src_p)
cab = re.compile(r'.*' + re.escape(base) + r':(\d+):\d+: error: ❌️ Docstring on `#guard_msgs` does not match generated message:')
otro = re.compile(r'.*' + re.escape(base) + r':\d+:\d+: ')
bloques = []
i = 0
while i < len(out):
    m = cab.match(out[i])
    if not m:
        i += 1
        continue
    L = int(m.group(1))
    i += 1
    if i < len(out) and out[i] == '':
        i += 1
    nuevo, viejo = [], []
    while i < len(out) and not otro.match(out[i]):
        l = out[i]
        if l.startswith('+ '):
            nuevo.append(l[2:])
        elif l.startswith('- '):
            viejo.append(l[2:])
        elif l.startswith('  '):
            nuevo.append(l[2:])
            viejo.append(l[2:])
        elif l == '+':
            nuevo.append('')
        elif l == '-':
            viejo.append('')
        elif l == '':
            nuevo.append('')
            viejo.append('')
        else:
            sys.exit('❌ línea del diff sin prefijo conocido (bloque %d): %r' % (L, l))
        i += 1
    while nuevo and nuevo[-1] == '':
        nuevo.pop()
    while viejo and viejo[-1] == '':
        viejo.pop()
    bloques.append((L, nuevo, viejo))
# de abajo arriba, para que los números de línea sigan valiendo
for (L, nuevo, viejo) in sorted(bloques, reverse=True):
    g = L - 1                      # índice de la línea `#guard_msgs …`
    assert src[g].startswith('#guard_msgs'), (L, src[g])
    fin = g - 1
    assert src[fin].strip() == '-/', (L, src[fin])
    ini = fin
    while not src[ini].startswith('/--'):
        ini -= 1
    actual = src[ini + 1:fin]
    if actual != viejo:
        sys.exit('❌ bloque %d: el docstring del fuente no es el «viejo» del diff' % L)
    era_error = any(l.startswith('error') for l in viejo)
    es_error = any(l.startswith('error') for l in nuevo)
    if era_error and not es_error:
        print('⚠️ línea %d: el bloque fijaba un error y el mensaje nuevo NO tiene ninguno' % L)
    cabeceras_v = [l for l in viejo if re.match(r'(error|warning|info)\b', l)]
    cabeceras_n = [l for l in nuevo if re.match(r'(error|warning|info)\b', l)]
    if cabeceras_v != cabeceras_n:
        print('⚠️ línea %d: las CABECERAS cambian:\n    antes: %s\n    ahora: %s' % (L, cabeceras_v, cabeceras_n))
    src[ini:fin + 1] = ['/--'] + nuevo + ['-/']
    print('bloque de la línea %d: %d líneas → %d (cabeceras iguales: %s)' % (L, len(viejo), len(nuevo),
                                                                           cabeceras_v == cabeceras_n))
t = '\n'.join(src)
if crlf:
    t = t.replace('\n', '\r\n')
io.open(src_p, 'w', encoding='utf-8', newline='').write(t)
print('bloques reescritos:', len(bloques))
