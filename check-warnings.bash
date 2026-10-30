#!/bin/bash
# check-warnings.bash — los WARNINGS del build, declarados uno a uno.
#
# ⛔⛔ NACE DE UN FALLO MÍO, MEDIDO (ADR-060 §6, regla M-13). Las ADR-057, 058 y 059 cerraron
# las tres con «**0 warnings**». Era FALSO: la cifra cierta era la de la `lean_lib FOL` SOLA, y
# se generalizó al árbol entero sin volver a medirla. Reales: 7 en ROBINSON_PlusPlus y 4 en FOL.
#
# 🔑 La diferencia con las otras cifras de control no era que estuviera mal: era que **no había
#    NADA que la reejecutara**. `check-footprints`, `check-estratos`, `check-doc-sync`,
#    `check-axioms` y `check-sorry` se vuelven a ejecutar; «0 warnings» se COPIABA Y PEGABA.
#    Este script es lo que faltaba para que esa cifra sea una medición y no una costumbre.
#
# ⭐ Rompe en LOS DOS SENTIDOS, como `check-footprints`:
#   · si aparece un warning NUEVO → rojo (es lo que se quiere cazar);
#   · si DESAPARECE uno declarado → rojo también, para que la tabla baje. Una cota no protege
#     una cifra; sólo una igualdad lo hace (ADR-032 §4).
#
# ⚠️ Se declara por FICHERO + CLASE + CUENTA, no por número de línea: las líneas se mueven al
#    editar y un control frágil se acaba desactivando.
#
# 🔧 EJECUTAR DESDE POWERSHELL (desde Bash, `lake` no está en el PATH).
# Desde la raíz de ROBINSON_PlusPlus: los dos objetivos de FOL se construyen desde AQUÍ, con
#    `lake build FOL TheoryFramework` (M-3, ADR-205: el mismo toolchain en los dos repos).

set -uo pipefail
export PATH="/usr/bin:$PATH"
cd "$(dirname "$0")" || exit 2

# ── LA TABLA DECLARADA ────────────────────────────────────────────────────────
# fichero | clase | cuenta
#
# clases:
#   simp-unused  →  "This simp argument is unused"
#   var-unref    →  "Variable name `x` is not explicitly referenced"
#   deprecated   →  "`x` has been deprecated" (✏️ 2026-10-21, T42b, ADR-181: v4.35.0 da por obsoletos «if_pos», «if_neg»,
#                   «dif_pos», «dif_neg», «if_true» e «if_false»; se renombraron en todo el árbol MENOS en los módulos
#                   CONGELADOS de FOL —`../FOL/frozen_files.txt`: inmutables sin un «thaw», que decide el propietario—)
# ✏️ 2026-10-28 (T58, ADR-217): fuera los cuatro `var-unref` de `TheoryFramework/Relations.lean`, arreglados.
# ✏️ 2026-10-30 (T44, ADR-226): fuera los cuatro `simp-unused` de `CodeWitnessPrf.lean` y el `var-unref` de
# `SubstfcWitnessPrf.lean`, arreglados. Quedan los 19 `deprecated` de seis módulos CONGELADOS de FOL: arreglarlos pide un
# «thaw» del propietario.
# ✏️ 2026-10-30 (ADR-227): el propietario autorizó el thaw; los 19, renombrados (los mismos sustitutos de T42b) y los seis
# módulos, vueltos a congelar. La tabla, VACÍA: cualquier aviso es rojo.
DECLARED=$(cat <<'TABLA'
TABLA
)

if ! command -v lake >/dev/null 2>&1; then
  echo "⛔ 'lake' no está en el PATH de este shell."
  echo "   Lánzalo desde PowerShell. Un control que no puede medir NO es un control verde."
  exit 1
fi

TMP=$(mktemp)
echo "════ MIDIENDO ════"
echo "  · ROBINSON_PlusPlus  (lake build)"
lake build 2>&1 | grep -E "^warning: " >> "$TMP"
echo "  · FOL + TheoryFramework  (lake build FOL TheoryFramework)"
lake build FOL TheoryFramework 2>&1 | grep -E "^warning: " >> "$TMP"
# ✏️ 2026-10-28 (T67, ADR-195): un aviso es su fichero, su línea, su columna y su mensaje, y cuenta UNA vez aunque lo
# repitan los dos builds. Desde que RPP importa `FOL.Canonical0`, `FOL/Rename.lean` (congelado, dos avisos de
# deprecación) entra en el cierre de RPP y el primer build también lo imprime: sin esto, «dice 2, real 4».
sort -u "$TMP" -o "$TMP"
echo

# ── clasificar lo medido ──────────────────────────────────────────────────────
MEASURED=$(mktemp)
: > "$MEASURED"
while IFS= read -r line; do
  [ -z "$line" ] && continue
  f=$(printf '%s' "$line" | sed -E 's/^warning: ([^:]+):[0-9]+:[0-9]+:.*/\1/')
  case "$line" in
    *"simp argument is unused"*) c="simp-unused" ;;
    *"is not explicitly referenced"*) c="var-unref" ;;
    *"has been deprecated"*) c="deprecated" ;;
    *) c="OTRA" ;;
  esac
  printf '%s|%s\n' "$f" "$c" >> "$MEASURED"
done < "$TMP"
MEAS_TABLE=$(sort "$MEASURED" | uniq -c | awk '{printf "%s|%s\n", $2, $1}')

FAIL=0
TOTAL_D=0
# ✏️ 2026-10-30 (ADR-227): `grep -c` sin coincidencias imprime «0» Y sale con 1, y el `|| echo 0` añadía otro «0»: con
# cero avisos, TOTAL_M era «0⏎0» y el control daba ROJO. Nunca se había medido el caso de cero; con la tabla vacía, sí.
TOTAL_M=$(grep -c . "$MEASURED" 2>/dev/null); TOTAL_M=${TOTAL_M:-0}

echo "════ CONTRA LA TABLA DECLARADA ════"
while IFS='|' read -r f c n; do
  [ -z "${f:-}" ] && continue
  TOTAL_D=$((TOTAL_D + n))
  got=$(grep -c "^$f|$c$" "$MEASURED" 2>/dev/null); got=${got:-0}
  if [ "$got" = "$n" ]; then
    printf "  ✓ %-52s %-12s %s\n" "$f" "$c" "$n"
  else
    printf "  ✗ %-52s %-12s dice %s, real %s\n" "$f" "$c" "$n" "$got"
    FAIL=1
  fi
done <<< "$DECLARED"

# ── lo medido que NO está declarado: eso es lo que hay que cazar ──────────────
echo
echo "════ WARNINGS NO DECLARADOS ════"
NEW=0
while IFS= read -r row; do
  [ -z "$row" ] && continue
  f=${row%%|*}; rest=${row#*|}; c=${rest%%|*}
  if ! printf '%s' "$DECLARED" | grep -q "^$f|$c|"; then
    echo "  ✗ NO DECLARADO: $f  ($c)"
    NEW=1
    FAIL=1
  fi
done <<< "$MEAS_TABLE"
[ "$NEW" = "0" ] && echo "  ✓ ninguno"

rm -f "$TMP" "$MEASURED"

# ── 2 · EL CENSO DE LAS OPCIONES QUE APAGAN LINTERS O SUBEN LÍMITES (✏️ 2026-10-30, T44, ADR-226) ─────────────────
# Un aviso que un `set_option linter.X false` apaga no llega a la tabla de arriba, y un `set_option maxHeartbeats N`
# de fichero tapa el coste de todo lo que venga después. Nadie los contaba (la auditoría, T44: «106 y 74, sin censo»).
# Aquí, los de FICHERO —no los `… in`, que valen para una declaración— de RPP, FOL y TheoryFramework, sobre el código
# despojado (`strip-lean.awk`: no cuenta uno comentado), por fichero, opción y cuenta, contra `doc/control/opciones.tsv`,
# con IGUALDAD en los dos sentidos: uno nuevo es rojo, y uno que desaparece también, para que la tabla baje. La tabla
# la escribe `bash check-warnings.bash --generar-opciones` y sólo cambia con un ADR. Antes, un autotest con un fixture:
# si no da sus cuentas, SIN MEDIR.
# ✏️ 2026-10-30 (ADR-229): los de fichero, pasados a `set_option … in` delante de la declaración que los pide (en RPP y
# en FOL: ninguno queda), y el censo cuenta ahora LAS DOS FORMAS, con una columna más («fichero» o «in»): un `… in`
# nuevo también es rojo, y uno que sobra, al quitarlo, baja la tabla. La tabla ya no tiene filas «fichero»: uno que
# vuelva, rojo.
OPC_TABLA=doc/control/opciones.tsv
OPC_RE='^[[:space:]]*set_option[[:space:]]+(linter\.[A-Za-z0-9_.]+[[:space:]]+false|max[A-Za-z]+[[:space:]]+[0-9]+)[[:space:]]*$'
OPC_RE_IN='^[[:space:]]*set_option[[:space:]]+(linter\.[A-Za-z0-9_.]+[[:space:]]+false|max[A-Za-z]+[[:space:]]+[0-9]+)[[:space:]]+in([[:space:]]|$)'
opc_censo () {   # $@ = «raíz:directorio…» → «fichero<TAB>opción<TAB>forma<TAB>cuenta», ordenado; «@@SIN_MEDIR@@ f» si no despoja
  local arg raiz dir f
  for arg in "$@"; do
    raiz=${arg%%:*}; dir=${arg#*:}
    (cd "$raiz" && find "$dir" -name '*.lean' | LC_ALL=C sort | while IFS= read -r f; do
      if ! LC_ALL=C awk -f "$OPC_STRIP" "$f" > "$OPC_TMP.cod"; then echo "@@SIN_MEDIR@@ $f"; continue; fi
      LC_ALL=C grep -E "$OPC_RE" "$OPC_TMP.cod" | awk -v f="$f" '{ print f "\t" $2 "\tfichero" }'
      LC_ALL=C grep -E "$OPC_RE_IN" "$OPC_TMP.cod" | awk -v f="$f" '{ print f "\t" $2 "\tin" }'
    done)
  done | LC_ALL=C sort | uniq -c | awk '{ print $2 "\t" $3 "\t" $4 "\t" $1 }'
}
OPC_STRIP="$(pwd)/strip-lean.awk"
OPC_TMP=$(mktemp)
OPC_FIX=$(mktemp -d)
mkdir -p "$OPC_FIX/Fix"
cat > "$OPC_FIX/Fix/Opciones.lean" <<'EOF'
set_option linter.unusedVariables false
set_option maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false in
-- set_option linter.unusedSimpArgs false
/- set_option maxRecDepth 2000 -/
set_option linter.unusedVariables true
set_option maxRecDepth 4000 in
-- set_option maxRecDepth 4000 in
theorem t : True := by
  set_option maxHeartbeats 300000 in
  trivial
EOF
OPC_AUTO=$(opc_censo "$OPC_FIX:Fix" | tr '\t\n' '| ')
rm -rf "$OPC_FIX"
OPC_ESP='Fix/Opciones.lean|linter.unusedSimpArgs|in|1 Fix/Opciones.lean|linter.unusedVariables|fichero|1 Fix/Opciones.lean|maxHeartbeats|fichero|2 Fix/Opciones.lean|maxHeartbeats|in|1 Fix/Opciones.lean|maxRecDepth|in|1 '
echo
echo "════ OPCIONES QUE APAGAN LINTERS O SUBEN LÍMITES (de fichero y con «in») ════"
OPC_FAIL=0
if [ "$OPC_AUTO" != "$OPC_ESP" ]; then
  echo "  ⚠️  SIN MEDIR — el autotest da «$OPC_AUTO» (esperado «$OPC_ESP»)"
  rm -f "$OPC_TMP" "$OPC_TMP.cod"; exit 2
fi
OPC_MED=$(opc_censo ".:ROBINSON_PlusPlus" "../FOL:FOL" "../FOL:TheoryFramework")
rm -f "$OPC_TMP" "$OPC_TMP.cod"
if printf '%s\n' "$OPC_MED" | grep -q '@@SIN_MEDIR@@'; then
  echo "  ⚠️  SIN MEDIR — el despojador falló en: $(printf '%s\n' "$OPC_MED" | grep '@@SIN_MEDIR@@' | cut -d' ' -f2- | paste -sd' ' -)"
  exit 2
fi
if [ "${1:-}" = "--generar-opciones" ]; then
  { echo "# doc/control/opciones.tsv — los set_option que apagan un linter o suben un límite, de FICHERO o con «in» (T44,"
    echo "# ADR-226; la forma, ADR-229). Lo escribe \`bash check-warnings.bash --generar-opciones\`; lo compara"
    echo "# check-warnings.bash con igualdad. Sólo con un ADR."
    echo "# fichero	opción	forma	cuenta"
    printf '%s\n' "$OPC_MED"; } > "$OPC_TABLA"
  echo "  ✓ $OPC_TABLA, regenerada: $(printf '%s\n' "$OPC_MED" | grep -c .) filas"
fi
if [ ! -s "$OPC_TABLA" ]; then
  echo "  ⚠️  SIN MEDIR — falta $OPC_TABLA"; exit 2
fi
OPC_DEC=$(grep -v '^#' "$OPC_TABLA" | tr -d '\r' | grep . | LC_ALL=C sort)
if [ "$OPC_DEC" = "$OPC_MED" ]; then
  echo "  ✓ las $(printf '%s\n' "$OPC_MED" | grep -c .) filas cuadran: $(printf '%s\n' "$OPC_MED" | awk -F'\t' '$3 == "fichero" { f += $4 } $3 == "in" && $2 ~ /^linter/ { l += $4 } $3 == "in" && $2 ~ /^max/ { m += $4 } END { print (f + 0) " de fichero; con «in», " (l + 0) " que apagan un linter y " (m + 0) " que suben un límite" }') (autotest: 5 de 5)"
else
  echo "  ✗ no cuadran con $OPC_TABLA:"
  diff <(printf '%s\n' "$OPC_DEC") <(printf '%s\n' "$OPC_MED") | grep -E '^[<>]' | sed 's/^</      · en la tabla y no en el código:/; s/^>/      · en el código y no en la tabla:/' | head -20
  OPC_FAIL=1
fi

echo
echo "  declarados: $TOTAL_D   ·   medidos: $TOTAL_M"
if [ "$FAIL" = "0" ] && [ "$TOTAL_D" = "$TOTAL_M" ] && [ "$OPC_FAIL" = "0" ]; then
  echo "✅ LOS $TOTAL_M WARNINGS CUADRAN, Y LAS OPCIONES TAMBIÉN."
  exit 0
else
  echo "❌ LOS WARNINGS O LAS OPCIONES NO CUADRAN."
  echo
  echo "⚠️  Si has ARREGLADO uno, baja la tabla de arriba — el control rompe también hacia abajo,"
  echo "    a propósito: una cota no protege una cifra, sólo una igualdad lo hace."
  exit 1
fi
