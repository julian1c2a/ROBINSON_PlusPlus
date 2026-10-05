#!/bin/bash
# check-sorry.bash — Find all sorry statements in .lean files
#
# ⚠️ Cuenta `sorry` como TOKEN DE CÓDIGO, no como cadena de texto. Antes de buscar,
#    ELIMINA los comentarios de Lean (`--` de línea y `/- … -/` de bloque, anidados,
#    lo que incluye los docstrings `/-- … -/`) y los literales de cadena.
#
#    Sin eso el control MIENTE, y mucho: este proyecto declara «cero `sorry`» en
#    decenas de docstrings y anota «(sorry pendiente)» junto a varios axiomas, así que
#    la versión ingenua (`grep -c 'sorry'`) daba «101 sorry en 87 ficheros» donde hay 0,
#    y la versión que sólo excluye backticks seguía dando 15. Se arregla la
#    HERRAMIENTA, nunca la cifra.
#
#    Los números de línea que se imprimen son los del fichero ORIGINAL.
#
# Usage:
#   bash check-sorry.bash           # check all .lean files
#   bash check-sorry.bash staged    # check only staged files (for CI)
#   bash check-sorry.bash Module    # check files matching pattern

set -e

# ═══ PATH HIGIÉNICO ═════════════════════════════════════════════════════════
# ⚠️ No es paranoia: es un fallo MEDIDO el 2026-09-09. Lanzado desde PowerShell (o desde
# cualquier consola de Windows), `bash` hereda el PATH de Windows, y en esta máquina eso
# hace que `head` resuelva a C:/msys64/ucrt64/bin/head.exe — que no es el `head` de
# coreutils, sino el HEAD de Quantum ESPRESSO — y que `grep` sea otro build que rechaza
# las expresiones de este script («warning: ? at start of expression»).
#
# El resultado era el peor posible: los CUATRO controles [A] salían VACÍOS y el script
# imprimía «✅ DOCUMENTACIÓN SINCRONIZADA» sin haber comprobado absolutamente nada.
# Se antepone el /usr/bin de MSYS2, que es contra el que están escritos estos scripts.
[ -d /usr/bin ] && export PATH="/usr/bin:/bin:$PATH"

# ⛔ 2026-10-04 (cuarta revisión de ADR-116): el script se sitúa en SU directorio, como los demás
# controles; antes medía donde lo lanzaran (y desde un directorio sin `.lean` salía en verde).
cd "$(dirname "$0")" || exit 2

# ── Despojador de comentarios y cadenas ──────────────────────────────────────
# Vive en `strip-lean.awk` (2026-10-03): una definición delicada vive en UN sitio, y la usan
# también `check-doc-sync.bash` [A] y [B].
# Emite UNA línea por cada línea de entrada (los números de línea siguen siendo los del original)
# sin comentarios (`--`, `/- … -/` anidados, docstrings) ni literales (cadenas y caracteres).
# ⚠️ Se ejecuta con `LC_ALL=C`: despoja por BYTES (en otro locale se niega, y la prueba de humo lo dice).
STRIP_AWK="$(cd "$(dirname "$0")" && pwd)/strip-lean.awk"
[ -f "$STRIP_AWK" ] || { echo "⚠️  SIN MEDIR — falta $STRIP_AWK"; exit 2; }
STRIP () { LC_ALL=C awk -f "$STRIP_AWK" "$@"; }
# ⛔ 2026-10-03 (ADR-116): `admit` es `sorry`, `stop` es `repeat sorry` y `sorryAx` es el propio axioma
# (Init/Tactics.lean del core); el patrón sólo casaba `sorry` y los tres daban verde.
# (un literal de nombre, `` `sorryAx ``, no es un uso: se excluye la comilla invertida delante; el
# nombre calificado `_root_.sorryAx` sí lo es — 2026-10-04, segunda revisión)
SORRY_RE='(^|[^A-Za-z0-9_'"'"'.`])(_root_\.)?(sorry|sorryAx|admit|stop)([^A-Za-z0-9_'"'"'!?]|$)'
# ── PRUEBA DE HUMO del despojador (2026-10-03, ADR-116; ampliada en cada revisión) ─────────────────
# Si `strip-lean.awk` falla (un error de sintaxis en una edición, un awk incompatible, un locale que
# no es C), sin esto el control daba «✅ No sorry found.» con `sorry` reales: la salida vacía de un
# awk roto pasa por limpia. Entrada fija con 39 `sorry` reales —uno por cada construcción que alguna
# versión del despojador leyó mal, en las cuatro revisiones adversariales— y señuelos; y aparte una
# línea con CRLF. ⛔ Se compara el CONJUNTO de líneas con `sorry`, no la cuenta (cuarta revisión): con
# la cuenta, un despojador que perdía un `sorry` real y hacía contar un señuelo daba la misma cifra.
SMOKE=$(STRIP <<'EOF' | grep -nE "$SORRY_RE" | cut -d: -f1 | tr '\n' ' ' || true
-- sorry
"sorry" -- una cadena
/- sorry -/ sorry -- 1
('"', sorry) -- 2: '"' es un carácter, no abre cadena
s!"v {(sorry : Nat)}" -- 3: el código de una interpolación
theorem «a--b» : True := sorry -- 4: «…» es opaco
/-/- x -/ sorry -- 5: `/-` consume tres caracteres
r#"sorry"# -- una cadena en bruto
"uno
sorry dos" -- una cadena de dos líneas
by admit -- 6
throwError "x {(sorry : Nat)}" -- 7: throwError interpola
#eval !"{".isEmpty -- `!"…"` es el not de una cadena normal: su `{` no abre nada
sorry -- 8
s!"a {s!"b {(sorry : Nat)} c"} d" -- 9: interpolaciones anidadas
⟨'«', "»", sorry⟩ -- 10: un carácter tras un símbolo no ASCII
⟨r"\", sorry⟩ -- 11: una cadena en bruto tras un símbolo no ASCII
exact/- c -/sorry -- 12: un comentario es espacio
_root_.sorryAx Nat -- 13
(`sorryAx, h₀', Γ') -- un literal de nombre y dos primas
def b := !s!"{(sorry : Nat)}".isEmpty -- 14: el not de una interpolada
def N := { x : Int //-x > 0 }
sorry -- 15: `//` es un token, y lo que le sigue no abre comentario
def u := p |>.r"\"" sorry "x" -- 16: tras `|>.`, `r` es un identificador y su cadena es normal
def g := f '
'"' "
sorry -- 17: un carácter que es un salto de línea literal
def w := φs! "{sorry}" -- `φs!` es UN identificador: su cadena es normal
theorem t18 (p q : Prop) (hp : p) : p \/-- la izquierda
  q := Or.inl sorry -- 18: `\/` es un token
def m : IO Int := do
  let x <-- sorry -- 19: `<-` es un token
  return x
def u := f `r"\"" sorry "x" -- 20: tras la comilla invertida, `r` es un identificador
def U := Nat ⊕'"'" = "x"
theorem t21 : True := sorry -- 21: `⊕'` es un token
def k := 0...s!"{(sorry : Nat)}".length -- 22: `..` + `s!`
  throwErrorAt stx[0] "b {(sorry : Nat)}" -- 23: throwErrorAt x[…]
  throwErrorAt (← getRef) "c {(sorry : Nat)}" -- 24: throwErrorAt (…)
def pl : IO Unit := println! "v {(sorry : Nat)}" -- 25
def dt : Nat := dbg_trace "v {(sorry : Nat)}"; 0 -- 26
  trace[Meta.debug] "x {(sorry : Nat)}" -- 27
  Macro.trace[foo] "z {(sorry : Nat)}" -- 28
  logInfo m!"m {(sorry : Nat)}" -- 29
  let s := f!"f {(sorry : Nat)}" -- 30
  throwNamedError
    lean.foo "a {(sorry : Nat)}" -- 31
  logNamedErrorAt stx
    lean.foo "a {(sorry : Nat)}" -- 32
/- a /- b -/ "c -/
theorem t33 : True := sorry -- 33: los comentarios anidan
/- sorry -/
def r := r#"a "b"#
theorem t34 : True := sorry -- 34: la cadena en bruto acaba en `"#`
/- Says "hi -/
theorem t35 : True := sorry -- 35: una comilla dentro de un comentario
def q := p.1'"'
theorem t36 : True := sorry -- 36: tras `p.1`, `'"'` es un carácter
def f (args : Array Syntax) : MetaM Unit := throwErrorAt args[0]! "falta {(sorry : Nat)}" -- 37: throwErrorAt x[i]!
def f2 (a b : Nat) : Nat := a <<<-- "
  b
theorem t38 : True := sorry -- 38: `<<<` es un token, y lo de detrás un comentario
def nb := s!"{({a := 1} : P).a} y" -- llaves anidadas dentro de una interpolación
theorem t39 : True := sorry -- 39: detrás de las llaves anidadas
def w2 := x₁throwError "{sorry}" -- `x₁throwError` es UN identificador: su cadena es normal
EOF
)
SMOKE_ESPERADO="3 4 5 6 7 11 12 14 15 16 17 18 19 21 23 24 27 30 32 34 36 37 38 39 40 41 42 43 44 45 47 49 51 54 56 58 59 62 64 "
SMOKE_CRLF=$(printf 'throwErrorAt\r\n  stx "a {(sorry : Nat)}"\r\n' | STRIP | grep -cE "$SORRY_RE" || true)
if [ "$SMOKE" != "$SMOKE_ESPERADO" ] || [ "$SMOKE_CRLF" != "1" ]; then
  echo "⚠️  SIN MEDIR — strip-lean.awk no pasa su prueba de humo."
  echo "    líneas con sorry: «$SMOKE»"
  echo "    esperadas:        «$SMOKE_ESPERADO»   (con CRLF: $SMOKE_CRLF de 1)"
  exit 2
fi

MODE="${1:-all}"
TOTAL=0
FILES_WITH_SORRY=0

if [ "$MODE" = "staged" ]; then
    # (el ÍNDICE, no el árbol: se despoja `git show :FICHERO`, y sólo lo añadido o cambiado)
    LEAN_FILES=$(git diff --cached --name-only --diff-filter=ACM | grep '\.lean$' || true)
elif [ "$MODE" = "all" ]; then
    # (sin `_rpp/` —el clon de RPP que hace la CI de FOL— ni `Probe/` —local de RPP, fuera de git—: el
    #  alcance es el mismo en local que en la CI; 2026-10-04, tercera revisión de ADR-116)
    LEAN_FILES=$(find . -name "*.lean" ! -name "_template.lean" ! -path "./.lake/*" ! -path "./_rpp/*" ! -path "./Probe/*" | sort)
else
    LEAN_FILES=$(find . -name "*${MODE}*.lean" ! -path "./.lake/*" | sort)
fi

if [ -z "$LEAN_FILES" ]; then
    # en modo all, no encontrar ningún `.lean` es no haber medido (cuarta revisión): antes, «No .lean files
    # found.» y salida 0, sin pasar siquiera por el autotest
    if [ "$MODE" = "all" ]; then echo "⚠️  SIN MEDIR — ningún .lean en $(pwd)"; exit 2; fi
    echo "No .lean files found."
    exit 0
fi


echo "=== sorry report ==="
while IFS= read -r FILE; do
    [ -z "$FILE" ] && continue
    [ "$MODE" != "staged" ] && [ ! -f "$FILE" ] && continue
    if [ "$MODE" = "staged" ]; then
        CONTENIDO=$(git show ":$FILE" 2>/dev/null || true)
        HITS=$(printf '%s\n' "$CONTENIDO" | STRIP | grep -nE "$SORRY_RE" | cut -d: -f1 || true)
    else
        HITS=$(STRIP "$FILE" | grep -nE "$SORRY_RE" | cut -d: -f1 || true)
    fi
    [ -z "$HITS" ] && continue
    COUNT=$(printf '%s\n' "$HITS" | grep -c . || true)
    echo ""
    echo "📄 $FILE ($COUNT sorry)"
    while IFS= read -r LN; do
        [ -z "$LN" ] && continue
        if [ "$MODE" = "staged" ]; then
            printf '   %s:%s\n' "$LN" "$(printf '%s\n' "$CONTENIDO" | sed -n "${LN}p")"
        else
            printf '   %s:%s\n' "$LN" "$(sed -n "${LN}p" "$FILE")"
        fi
    done <<< "$HITS"
    TOTAL=$((TOTAL + COUNT))
    FILES_WITH_SORRY=$((FILES_WITH_SORRY + 1))
done <<< "$LEAN_FILES"

echo ""
if [ "$TOTAL" -eq 0 ]; then
    echo "✅ No sorry found."
    SORRY_FAIL=0
else
    echo "⚠️  Total: $TOTAL sorry in $FILES_WITH_SORRY file(s)."
    SORRY_FAIL=1
fi

# ═══ CENSO DE LOS OTROS AGUJEROS DE CONFIANZA ═══════════════════════════════
# ⛔⛔ POR QUÉ EXISTE (2026-09-22, ADR-085). `check-axioms.bash` censa los `axiom` y este
# script los `sorry`. Medido hoy: **nadie miraba el resto de la familia** — `native_decide`
# (que ejecuta código fuera del kernel), `unsafe`, `opaque`, `@[implemented_by]`, `@[extern]`.
#
# ⭐ Y la medición salió LIMPIA: los cinco están a CERO en los dos repos. Precisamente por eso
# se declara ahora: el coste de fijar un cero es nulo, y el de descubrir el primero tarde, no.
# 🔑 *Un agujero que hoy vale cero y que nadie vigila es un agujero abierto, no un agujero
#    cerrado.* Es la misma doctrina que `check-warnings`: igualdad EXACTA, nunca cota.
#
# ⚠️ Lo que NO entra, y por qué: `partial def` sale 1 en RPP y 3 en FOL, y los cuatro son
# inocuos —`termToString` (pretty-printing) y tres ayudantes de táctica en `MetaM`—: no
# aparecen en ningún término de prueba. Si algún día un `partial def` entra en una prueba,
# eso sí es un agujero; hoy la cifra no discrimina, así que se deja fuera y se dice.
echo ""
echo "════ CENSO DE AGUJEROS DE CONFIANZA (esperado: 0 en todos) ════"
# ⛔⛔ 2026-10-04 (cuarta revisión de ADR-116): era un grep CRUDO y ANCLADO (`^unsafe `, `^opaque `,
# `@\[implemented_by`, `@\[extern`) sobre RPP y FOL/ —sin TheoryFramework ni los barrels—: no veía
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
AG_B0="(^|[^A-Za-z0-9_'.«\`])"
AG_B1="([^A-Za-z0-9_'!?»]|\$)"
ag_patron () {   # $1 = etiqueta → el patrón de esa familia (la ÚNICA copia: la recogida sale de aquí)
  case "$1" in
    'native_decide')  echo 'native_decide' ;;
    'decide +native') echo 'decide[[:space:]]*([+]native|[(][^)]*native[[:space:]]*:=[[:space:]]*true)' ;;
    'unsafe')         echo 'unsafe' ;;
    'opaque')         echo 'opaque' ;;
    'implemented_by') echo 'implemented_by' ;;
    'extern')         echo 'extern' ;;
    'ofReduceBool'*)  echo '([A-Za-z0-9_]+[.])*(ofReduceBool|ofReduceNat|trustCompiler)' ;;
    'skipKernelTC'*)  echo '([A-Za-z0-9_]+[.])*(skipKernelTC|addDeclWithoutChecking)' ;;
  esac
}
AG_ETIQUETAS=('native_decide' 'decide +native' 'unsafe' 'opaque' 'implemented_by' 'extern' 'ofReduceBool · ofReduceNat · trustCompiler' 'skipKernelTC · addDeclWithoutChecking')
# ⛔ (revisión final de ADR-117) la recogida tenía su PROPIA copia de los patrones: una errata en ella
# (`extrn`) dejaba pasar el autotest —su caso salía por otra familia de la misma línea— y daba verde con un
# `@[extern]` real. Ahora se construye de `ag_patron`, y no hay dos copias que puedan divergir.
AG_FAMILIAS=$(for e in "${AG_ETIQUETAS[@]}"; do ag_patron "$e"; done | paste -sd'|' -)
ag_recoge () {   # $@ = caminos → «fichero:línea:código» de cada línea despojada con un agujero
  find "$@" -name '*.lean' ! -path '*/.lake/*' | sort | while IFS= read -r f; do
    STRIP "$f" | LC_ALL=C grep -nE "${AG_B0}(${AG_FAMILIAS})${AG_B1}" | sed "s|^|$f:|" || true
  done
}
# ⛔ 2026-10-04 (ADR-117): AUTOTEST. Los ocho dan 0 de verdad, y un patrón que dejara de casar (una errata
# en una edición) daría 0 también: verde sin medir (la causa 16 de los controles que no comprueban). Un
# fixture con UNA LÍNEA POR ALTERNATIVA —en las formas que el grep anclado de antes no veía, y las
# calificadas— y señuelos en un comentario, en una cadena, dentro de un identificador y un `decide` normal.
# Se compara el CONJUNTO de líneas de cada familia (como en el humo de arriba), no una cuenta.
AG_FIX=$(mktemp -d)
cat > "$AG_FIX/Agujeros.lean" <<'EOF'
attribute [implemented_by realF] fakeF
@[extern "c_fn"] def cfn : Nat → Nat := id
noncomputable opaque secreto : Nat
private unsafe def peligro : Nat := 0
theorem a1 : 2 + 2 = 4 := by native_decide
theorem a2 : 2 + 2 = 4 := by decide +native
theorem a3 : 2 + 2 = 4 := by decide (native := true)
theorem a4 : 2 + 2 = 4 := by decide (config := { native := true })
theorem a5 : c = false := Lean.ofReduceBool c false rfl
theorem a6 : n = 0 := _root_.Lean.ofReduceNat n 0 rfl
example := Lean.trustCompiler
set_option debug.skipKernelTC true in theorem a8 : True := trivial
run_cmd liftCoreM (Lean.Kernel.Environment.addDeclWithoutChecking env d)
#eval env.addDeclWithoutChecking d
-- unsafe opaque extern native_decide implemented_by ofReduceBool skipKernelTC
def s := "unsafe opaque extern native_decide implemented_by"
def unsafeX := 0
def x_opaque := opaqueY
theorem a9 : 2 + 2 = 4 := by decide
EOF
AG_FIXCOD=$(ag_recoge "$AG_FIX")
rm -rf "$AG_FIX"
AG_ESPERADO=('5 ' '6 7 8 ' '4 ' '3 ' '1 ' '2 ' '9 10 11 ' '12 13 14 ')
AG_AUTO=""
[ "$(printf '%s\n' "$AG_FIXCOD" | cut -d: -f2 | tr '\n' ' ')" = "1 2 3 4 5 6 7 8 9 10 11 12 13 14 " ] \
  || AG_AUTO=" la recogida da «$(printf '%s\n' "$AG_FIXCOD" | cut -d: -f2 | tr '\n' ' ')»;"
k=0
for etiqueta in "${AG_ETIQUETAS[@]}"; do
  L=$(printf '%s\n' "$AG_FIXCOD" | { LC_ALL=C grep -E "${AG_B0}($(ag_patron "$etiqueta"))${AG_B1}" || true; } | cut -d: -f2 | tr '\n' ' ')
  [ "$L" = "${AG_ESPERADO[$k]}" ] || AG_AUTO="$AG_AUTO «$etiqueta» da «$L» (esperadas «${AG_ESPERADO[$k]}»);"
  k=$((k + 1))
done
if [ -n "$AG_AUTO" ]; then
  echo "  ⚠️  SIN MEDIR — el autotest del censo no da sus líneas:$AG_AUTO"
  exit 2
fi
AG_COD=$(mktemp)
ag_recoge $AG_ALCANCE > "$AG_COD"
AG_N=0
for etiqueta in "${AG_ETIQUETAS[@]}"; do
  pat=$(ag_patron "$etiqueta")
  AG_N=$((AG_N + 1))
  N=$(LC_ALL=C grep -cE "${AG_B0}(${pat})${AG_B1}" "$AG_COD" || true)
  if [ "$N" = "0" ]; then
    printf '  ✓ %-44s 0\n' "$etiqueta"
  else
    printf '  ❌ %-44s %s  ← esperado 0\n' "$etiqueta" "$N"
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

echo ""
echo "════ EVALUAR EL ANCLA (ADR-117; esperado: ninguna orden) ════"
# ⛔ 2026-10-04 (ADR-117, decisión O1 del propietario: «todo computable»). `axioms` lleva al final el ancla
# diagonal, `ax_axiomsCodeT_def := axD axiomsBase`, cuyo enunciado contiene el numeral
# `nD = numeralM (codeNat ψ)`: un código de Cantor astronómico. Nada lo marca `noncomputable`, así que una
# orden que EVALÚE `axioms` —o el ancla, `axD`, `nD`, `deltaD`, `psiD`— construiría el numeral y no acabaría:
# en el build, la CI colgada; en un sondeo, su tiempo límite. Se buscan `#eval`, `#reduce` y `#guard` en el
# código despojado del build y de `sondeos/`, con la orden ENTERA (sus líneas sangradas siguientes).
# Lo que reduce el ancla DENTRO de una prueba (`decide`, `rfl`, `simp`) no se busca: falla a la vista
# —«(kernel) deep recursion detected», medido en la sonda del 2026-10-03—, nunca en verde.
EV_ALCANCE="ROBINSON_PlusPlus.lean ROBINSON_PlusPlus sondeos"
# (y los evaluadores META que llegan a `axioms`: `stepConcl` —`.thy k ⇒ axioms[k]?`—, y con él `checkAux`,
#  `checkProof`, `proofCode`, `proofCode'`; `ruleCode`/`rulesCode`; `decodeRuleTag` y la cadena de
#  `decodeChain` —revisión final de ADR-117—. Un `#eval` de cualquiera de ellos sobre una línea `thy` se colgaría.)
# ⭐ 2026-10-05 (ADR-120): y los valores del modelo que llevan dentro el numeral del ancla —`V₀`, el valor de
# `axiomsCodeT` en `MNV V₀`, y `codeNatList`, el código de una lista de fórmulas—, más las sentencias de Gödel y de
# Tarski, cuyo enunciado lleva el numeral de su propio código: `selfAppN`, `godelCN`, `liar` (lo pidió la medición
# de Tarski del 2026-10-05: el censo no las veía).
EV_TOK="(^|[^A-Za-z0-9_'«])(axioms|ax_axiomsCodeT_def|axD|nD|deltaD|psiD|stepConcl|checkAux|checkProof|ruleCode|rulesCode|proofCode'?|decodeRuleTag|decodeRule|decodeLine|decodeChainAux|decodeChain|V₀|codeNatList|selfAppN|godelCN|liar)([^A-Za-z0-9_'!?»]|\$)"
ev_ordenes () {   # stdin: código despojado → «línea:orden» de cada orden que evalúa, entera
  # Una orden abierta sigue en las líneas sangradas; NO se cierra en una línea en blanco (un comentario
  # despojado lo es); se cierra en una línea sin sangría o en otra orden o declaración. Si tras la palabra
  # clave no hay nada, toma la línea siguiente, tenga la sangría que tenga (`#eval` ⏎ `axioms.length` es Lean
  # válido: `"#eval " >> termParser`, sin comprobar la columna).
  LC_ALL=C awk '
    function cierra() { if (en) print n0 ":" txt; en = 0; pend = 0 }
    {
      if (en) {
        if ($0 ~ /^[ \t]*$/) next
        if (pend) { txt = txt " " $0; pend = 0; next }
        if ($0 ~ /^[^ \t]/ || $0 ~ /^[ \t]*(#[a-z_]+|theorem|lemma|def|example|instance|abbrev|structure|inductive|@\[)/) cierra()
        else { txt = txt " " $0; next }
      }
      if ($0 ~ /(^|[^A-Za-z0-9_#])(#eval|#reduce|#guard|run_cmd|run_elab|run_meta)!?([^A-Za-z0-9_]|$)/) {
        en = 1; n0 = NR; txt = $0
        t = $0; sub(/^.*(#eval|#reduce|#guard|run_cmd|run_elab|run_meta)!?/, "", t); pend = (t ~ /^[ \t]*$/)
      }
    }
    END { cierra() }'
}
ev_recoge () {   # $@ = caminos → «fichero:línea:orden» de cada orden que toca el ancla
  find "$@" -name '*.lean' ! -path '*/.lake/*' | sort | while IFS= read -r f; do
    STRIP "$f" | ev_ordenes | { LC_ALL=C grep -E "$EV_TOK" || true; } | sed "s|^|$f:|"
  done
}
for p in $EV_ALCANCE; do
  [ -e "$p" ] || { echo "  ⚠️  SIN MEDIR — falta $p"; exit 2; }
done
# AUTOTEST: una orden real por ficha y por forma —calificada, de varias líneas con una en blanco y un
# comentario, `#guard`, el término en la línea siguiente sin sangría, `run_cmd`, un evaluador META— y señuelos:
# la base, un comentario, una cadena, un teorema que NO es una orden, `#print axioms`, una línea sin sangría
# tras un `#eval` inocuo, y un `#print axioms` sangrado tras otro `#eval` sangrado. Se compara el CONJUNTO.
EV_FIX=$(mktemp -d)
cat > "$EV_FIX/Evalua.lean" <<'EOF'
#eval axioms.length
#eval ROBINSON_PlusPlus.Minimal.Axioms.axioms.length
#reduce

  -- el ancla
  ax_axiomsCodeT_def
#guard nD == nD
#eval axD axiomsBase
#reduce (deltaD axiomsBase)
#eval
psiD axiomsBase
run_cmd Lean.logInfo m!"{axioms.length}"
#eval checkProof []
#eval axiomsBase.length
-- #eval axioms.length
def s := "#eval axioms"
theorem t : axioms.length = 142 := rfl
#print axioms prf_ancla
#eval 1
theorem u : axioms.length = 142 := rfl
  #eval 2
  #print axioms foo
#eval V₀
#reduce ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN
#eval codeNatList axiomsBase
#reduce selfAppN P
#eval liar Tr
EOF
EV_AUTO=$(ev_recoge "$EV_FIX" | sed "s|^$EV_FIX/Evalua.lean:||" | cut -d: -f1 | tr '\n' ' ')
rm -rf "$EV_FIX"
if [ "$EV_AUTO" != "1 2 3 7 8 9 10 12 13 23 24 25 26 27 " ]; then
  echo "  ⚠️  SIN MEDIR — el autotest del censo da las líneas «$EV_AUTO» (esperadas «1 2 3 7 8 9 10 12 13 23 24 25 26 27 »)."
  exit 2
fi
EV_FAIL=0
EV_HITS=$(ev_recoge $EV_ALCANCE)
if [ -z "$EV_HITS" ]; then
  echo "  ✓ ninguna orden \`#eval\`, \`#reduce\`, \`#guard\` ni \`run_cmd\` toca \`axioms\`, el ancla ni un evaluador META (el build y sondeos/)"
else
  printf '  ❌ %s orden(es) evalúan el ancla (no acabarían):\n' "$(printf '%s\n' "$EV_HITS" | wc -l | tr -d ' ')"
  printf '%s\n' "$EV_HITS" | head -10 | cut -c1-160 | sed 's/^/      /'
  echo "  🔑 Para medir, \`axiomsBase\` (los 141 de la base): el ancla es el 142.º."
  EV_FAIL=1
fi

echo ""
if [ "$SORRY_FAIL" = "0" ] && [ "$AG_FAIL" = "0" ] && [ "$EV_FAIL" = "0" ]; then
  echo '✅ NI `sorry` NI AGUJEROS DE CONFIANZA.'
else
  echo '❌ HAY `sorry` O AGUJEROS DE CONFIANZA (o una orden que evalúa el ancla).'
  exit 1
fi
