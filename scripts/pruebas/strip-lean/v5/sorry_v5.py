# sorry_v5.py — check-sorry.bash de los dos repos tras la cuarta revisión: `cd` al directorio del script, el
# autotest ANTES de la lista y por CONJUNTO de líneas (62 de entrada, 38 con sorry), «ningún .lean» = SIN MEDIR
# en modo all, `staged` sobre el ÍNDICE; y en RPP el censo de agujeros sobre el código despojado, por token y
# con todo lo que compila el build.
import io, os
HERE = os.path.dirname(os.path.abspath(__file__))
humo = io.open(os.path.join(HERE, 'humo_v5.lean'), encoding='utf-8').read().rstrip('\n')
ESPERADO = '3 4 5 6 7 11 12 14 15 16 17 18 19 21 23 24 27 30 32 34 36 37 38 39 40 41 42 43 44 45 47 49 51 54 56 58 59 62 64 '

def rep(s, old, new, tag, n=1):
    c = s.count(old)
    assert c == n, (tag, c, old[:90])
    return s.replace(old, new)

for path in ('E:/dropbox/github/lean4/ROBINSON_PlusPlus/check-sorry.bash', 'E:/dropbox/github/lean4/FOL/check-sorry.bash'):
    s = io.open(path, encoding='utf-8', newline='').read()
    assert '\r\n' not in s
    rpp = 'ROBINSON_PlusPlus/' in path
    # ── 1 · cd, y el bloque del despojador + humo ANTES de la lista ──────────────────────────
    a = s.index('MODE="${1:-all}"\n')
    b = s.index('# ── Despojador de comentarios y cadenas')
    c = s.index('echo "=== sorry report ==="')
    lista = s[a:b]           # MODE … LEAN_FILES … «No .lean files found»
    despojador = s[b:c]
    # el humo nuevo, en el bloque del despojador
    h0 = despojador.index("# ── PRUEBA DE HUMO del despojador")
    despojador = despojador[:h0] + '''# ── PRUEBA DE HUMO del despojador (2026-10-03, ADR-116; ampliada en cada revisión) ─────────────────
# Si `strip-lean.awk` falla (un error de sintaxis en una edición, un awk incompatible, un locale que
# no es C), sin esto el control daba «✅ No sorry found.» con `sorry` reales: la salida vacía de un
# awk roto pasa por limpia. Entrada fija con 38 `sorry` reales —uno por cada construcción que alguna
# versión del despojador leyó mal, en las cuatro revisiones adversariales— y señuelos; y aparte una
# línea con CRLF. ⛔ Se compara el CONJUNTO de líneas con `sorry`, no la cuenta (cuarta revisión): con
# la cuenta, un despojador que perdía un `sorry` real y hacía contar un señuelo daba la misma cifra.
SMOKE=$(STRIP <<'EOF' | grep -nE "$SORRY_RE" | cut -d: -f1 | tr '\\n' ' ' || true
''' + humo + '''
EOF
)
SMOKE_ESPERADO="''' + ESPERADO + '''"
SMOKE_CRLF=$(printf 'throwErrorAt\\r\\n  stx "a {(sorry : Nat)}"\\r\\n' | STRIP | grep -cE "$SORRY_RE" || true)
if [ "$SMOKE" != "$SMOKE_ESPERADO" ] || [ "$SMOKE_CRLF" != "1" ]; then
  echo "⚠️  SIN MEDIR — strip-lean.awk no pasa su prueba de humo."
  echo "    líneas con sorry: «$SMOKE»"
  echo "    esperadas:        «$SMOKE_ESPERADO»   (con CRLF: $SMOKE_CRLF de 1)"
  exit 2
fi

'''
    lista = rep(lista, '''if [ "$MODE" = "staged" ]; then
    LEAN_FILES=$(git diff --cached --name-only | grep '\\.lean$' || true)''', '''if [ "$MODE" = "staged" ]; then
    # (el ÍNDICE, no el árbol: se despoja `git show :FICHERO`, y sólo lo añadido o cambiado)
    LEAN_FILES=$(git diff --cached --name-only --diff-filter=ACM | grep '\\.lean$' || true)''', 'staged')
    lista = rep(lista, '''if [ -z "$LEAN_FILES" ]; then
    echo "No .lean files found."
    exit 0
fi''', '''if [ -z "$LEAN_FILES" ]; then
    # en modo all, no encontrar ningún `.lean` es no haber medido (cuarta revisión): antes, «No .lean files
    # found.» y salida 0, sin pasar siquiera por el autotest
    if [ "$MODE" = "all" ]; then echo "⚠️  SIN MEDIR — ningún .lean en $(pwd)"; exit 2; fi
    echo "No .lean files found."
    exit 0
fi''', 'vacio')
    s = s[:a] + '''# ⛔ 2026-10-04 (cuarta revisión de ADR-116): el script se sitúa en SU directorio, como los demás
# controles; antes medía donde lo lanzaran (y desde un directorio sin `.lean` salía en verde).
cd "$(dirname "$0")" || exit 2

''' + despojador + lista + '\n' + s[c:]
    # ── 2 · la lectura de cada fichero: en `staged`, el índice ────────────────────────────────
    s = rep(s, '''    HITS=$(STRIP "$FILE" | grep -nE "$SORRY_RE" | cut -d: -f1 || true)''', '''    if [ "$MODE" = "staged" ]; then
        CONTENIDO=$(git show ":$FILE" 2>/dev/null || true)
        HITS=$(printf '%s\\n' "$CONTENIDO" | STRIP | grep -nE "$SORRY_RE" | cut -d: -f1 || true)
    else
        HITS=$(STRIP "$FILE" | grep -nE "$SORRY_RE" | cut -d: -f1 || true)
    fi''', 'hits')
    s = rep(s, '''        printf '   %s:%s\\n' "$LN" "$(sed -n "${LN}p" "$FILE")"''', '''        if [ "$MODE" = "staged" ]; then
            printf '   %s:%s\\n' "$LN" "$(printf '%s\\n' "$CONTENIDO" | sed -n "${LN}p")"
        else
            printf '   %s:%s\\n' "$LN" "$(sed -n "${LN}p" "$FILE")"
        fi''', 'reprint')
    s = rep(s, '''    [ ! -f "$FILE" ] && continue''', '''    [ "$MODE" != "staged" ] && [ ! -f "$FILE" ] && continue''', 'isfile')
    if rpp:
        a = s.index('echo "════ CENSO DE AGUJEROS DE CONFIANZA (esperado: 0 en todos) ════"')
        b = s.index('''echo ""
if [ "$SORRY_FAIL" = "0" ] && [ "$AG_FAIL" = "0" ]; then''')
        s = s[:a] + '''echo "════ CENSO DE AGUJEROS DE CONFIANZA (esperado: 0 en todos) ════"
# ⛔⛔ 2026-10-04 (cuarta revisión de ADR-116): era un grep CRUDO y ANCLADO (`^unsafe `, `^opaque `,
# `@\\[implemented_by`, `@\\[extern`) sobre RPP y FOL/ —sin TheoryFramework ni los barrels—: no veía
# `attribute [implemented_by f] g`, `@[simp, implemented_by f]`, `private opaque`, `noncomputable opaque`
# ni `private unsafe def`, y con `implemented_by` y `Lean.ofReduceBool` se demuestra `False` con todo en verde
# (el propio core lo avisa, Init/Core.lean). Ahora: el TOKEN, sobre el código despojado de TODO lo que el
# build compila, y si falta un camino, SIN MEDIR. Y dos familias más: la confianza en el compilador
# (`ofReduceBool`, `ofReduceNat`, `trustCompiler`) y saltarse el kernel (`skipKernelTC`,
# `addDeclWithoutChecking`). El censo autoritativo, por entorno, está en `check-estratos.bash` (@TRUST,
# @NATIVO), y `leanchecker` en la CI vuelve a pasar cada declaración por el kernel.
AG_FAIL=0
AG_ALCANCE="ROBINSON_PlusPlus.lean ROBINSON_PlusPlus ../FOL/FOL.lean ../FOL/FOL ../FOL/TheoryFramework.lean ../FOL/TheoryFramework"
for p in $AG_ALCANCE; do
  [ -e "$p" ] || { echo "  ⚠️  SIN MEDIR — falta $p"; exit 2; }
done
AG_B0="(^|[^A-Za-z0-9_'.«\\`])"
AG_B1="([^A-Za-z0-9_'!?»]|\\$)"
AG_COD=$(mktemp)
find $AG_ALCANCE -name '*.lean' ! -path '*/.lake/*' | sort | while IFS= read -r f; do
  STRIP "$f" | LC_ALL=C grep -nE "${AG_B0}(native_decide|decide[[:space:]]+[+]native|unsafe|opaque|implemented_by|extern|(Lean[.])?(ofReduceBool|ofReduceNat|trustCompiler)|(debug[.])?skipKernelTC|addDeclWithoutChecking)${AG_B1}" \\
    | sed "s|^|$f:|" || true
done > "$AG_COD"
AG_N=0
for etiqueta in 'native_decide' 'decide +native' 'unsafe' 'opaque' 'implemented_by' 'extern' 'ofReduceBool · ofReduceNat · trustCompiler' 'skipKernelTC · addDeclWithoutChecking'; do
  case "$etiqueta" in
    'native_decide')  pat='native_decide' ;;
    'decide +native') pat='decide[[:space:]]+[+]native' ;;
    'unsafe')         pat='unsafe' ;;
    'opaque')         pat='opaque' ;;
    'implemented_by') pat='implemented_by' ;;
    'extern')         pat='extern' ;;
    'ofReduceBool'*)  pat='(Lean[.])?(ofReduceBool|ofReduceNat|trustCompiler)' ;;
    'skipKernelTC'*)  pat='(debug[.])?skipKernelTC|addDeclWithoutChecking' ;;
  esac
  AG_N=$((AG_N + 1))
  N=$(LC_ALL=C grep -cE "${AG_B0}(${pat})${AG_B1}" "$AG_COD" || true)
  if [ "$N" = "0" ]; then
    printf '  ✓ %-44s 0\\n' "$etiqueta"
  else
    printf '  ❌ %-44s %s  ← esperado 0\\n' "$etiqueta" "$N"
    LC_ALL=C grep -E "${AG_B0}(${pat})${AG_B1}" "$AG_COD" | head -5 | sed 's/^/      /' | cut -c1-140
    AG_FAIL=1
  fi
done
rm -f "$AG_COD"
if [ "$AG_FAIL" = "0" ]; then
  echo "  ✓ los $AG_N agujeros siguen a CERO en todo lo que compila el build (RPP, FOL y TheoryFramework)"
else
  echo "  🔑 Cada uno de éstos saca una prueba del kernel. Ninguno entra sin su ADR."
fi

''' + s[b:]
    io.open(path, 'w', encoding='utf-8', newline='').write(s)
    print('ok', path)
