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
# ⛔ Desde la raíz de ROBINSON_PlusPlus. NUNCA `cd FOL && lake build` (M-3): los dos objetivos
#    de FOL se construyen desde AQUÍ, con `lake build FOL TheoryFramework`.

set -uo pipefail
export PATH="/usr/bin:$PATH"
cd "$(dirname "$0")" || exit 2

# ── LA TABLA DECLARADA ────────────────────────────────────────────────────────
# fichero | clase | cuenta
#
# clases:
#   simp-unused  →  "This simp argument is unused"
#   var-unref    →  "Variable name `x` is not explicitly referenced"
DECLARED=$(cat <<'TABLA'
ROBINSON_PlusPlus/Meta/CodeWitnessPrf.lean|simp-unused|4
ROBINSON_PlusPlus/Meta/ChainNegPrf.lean|simp-unused|2
ROBINSON_PlusPlus/Meta/SubstfcWitnessPrf.lean|var-unref|1
TheoryFramework/Relations.lean|var-unref|4
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
    *) c="OTRA" ;;
  esac
  printf '%s|%s\n' "$f" "$c" >> "$MEASURED"
done < "$TMP"
MEAS_TABLE=$(sort "$MEASURED" | uniq -c | awk '{printf "%s|%s\n", $2, $1}')

FAIL=0
TOTAL_D=0
TOTAL_M=$(grep -c . "$MEASURED" 2>/dev/null || echo 0)

echo "════ CONTRA LA TABLA DECLARADA ════"
while IFS='|' read -r f c n; do
  [ -z "${f:-}" ] && continue
  TOTAL_D=$((TOTAL_D + n))
  got=$(grep -c "^$f|$c$" "$MEASURED" 2>/dev/null || echo 0)
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

echo
echo "  declarados: $TOTAL_D   ·   medidos: $TOTAL_M"
if [ "$FAIL" = "0" ] && [ "$TOTAL_D" = "$TOTAL_M" ]; then
  echo "✅ LOS $TOTAL_M WARNINGS CUADRAN."
  exit 0
else
  echo "❌ LOS WARNINGS NO CUADRAN."
  echo
  echo "⚠️  Si has ARREGLADO uno, baja la tabla de arriba — el control rompe también hacia abajo,"
  echo "    a propósito: una cota no protege una cifra, sólo una igualdad lo hace."
  exit 1
fi
