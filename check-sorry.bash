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

MODE="${1:-all}"
TOTAL=0
FILES_WITH_SORRY=0

if [ "$MODE" = "staged" ]; then
    LEAN_FILES=$(git diff --cached --name-only | grep '\.lean$' || true)
elif [ "$MODE" = "all" ]; then
    LEAN_FILES=$(find . -name "*.lean" ! -name "_template.lean" ! -path "./.lake/*" | sort)
else
    LEAN_FILES=$(find . -name "*${MODE}*.lean" ! -path "./.lake/*" | sort)
fi

if [ -z "$LEAN_FILES" ]; then
    echo "No .lean files found."
    exit 0
fi

# ── Despojador de comentarios y cadenas ──────────────────────────────────────
# Emite UNA línea de salida por cada línea de entrada (así los números de línea
# siguen siendo los del original) con el contenido de comentarios y de literales
# de cadena sustituido por nada. Los bloques `/- … -/` ANIDAN en Lean, por eso se
# lleva un contador de profundidad y no un booleano.
STRIP='
BEGIN { depth = 0 }
{
  line = $0; out = ""; i = 1; n = length(line)
  while (i <= n) {
    two = substr(line, i, 2)
    if (depth > 0) {
      if (two == "-/") { depth--; i += 2; continue }
      if (two == "/-") { depth++; i += 2; continue }
      i++; continue
    }
    if (two == "/-") { depth++; i += 2; continue }
    if (two == "--") { break }
    c = substr(line, i, 1)
    if (c == "\"") {
      i++
      while (i <= n) {
        c2 = substr(line, i, 1)
        if (c2 == "\\") { i += 2; continue }
        if (c2 == "\"") { i++; break }
        i++
      }
      out = out " "; continue
    }
    out = out c; i++
  }
  print out
}
'
SORRY_RE='(^|[^a-zA-Z_])sorry([^a-zA-Z_]|$)'

echo "=== sorry report ==="
while IFS= read -r FILE; do
    [ -z "$FILE" ] && continue
    [ ! -f "$FILE" ] && continue
    HITS=$(awk "$STRIP" "$FILE" 2>/dev/null | grep -nE "$SORRY_RE" | cut -d: -f1 || true)
    [ -z "$HITS" ] && continue
    COUNT=$(printf '%s\n' "$HITS" | grep -c . || true)
    echo ""
    echo "📄 $FILE ($COUNT sorry)"
    while IFS= read -r LN; do
        [ -z "$LN" ] && continue
        printf '   %s:%s\n' "$LN" "$(sed -n "${LN}p" "$FILE")"
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
AG_FAIL=0
for pat in 'native_decide' '^unsafe ' '^opaque ' '@\[implemented_by' '@\[extern'; do
  N=0
  for D in "ROBINSON_PlusPlus" "../FOL/FOL"; do
    [ -d "$D" ] || continue
    K=$(grep -rn "$pat" --include=*.lean "$D" 2>/dev/null | grep -c . || true)
    N=$((N + K))
  done
  if [ "$N" = "0" ]; then
    printf '  ✓ %-22s 0\n' "$pat"
  else
    printf '  ❌ %-22s %s  ← esperado 0\n' "$pat" "$N"
    for D in "ROBINSON_PlusPlus" "../FOL/FOL"; do
      [ -d "$D" ] || continue
      grep -rn "$pat" --include=*.lean "$D" 2>/dev/null | head -5 | sed 's/^/      /' | cut -c1-140
    done
    AG_FAIL=1
  fi
done
if [ "$AG_FAIL" = "0" ]; then
  echo "  ✓ los cinco agujeros graves siguen a CERO en los dos repos"
else
  echo "  🔑 Cada uno de éstos saca una prueba del kernel. Ninguno entra sin su ADR."
fi

echo ""
if [ "$SORRY_FAIL" = "0" ] && [ "$AG_FAIL" = "0" ]; then
  echo '✅ NI `sorry` NI AGUJEROS DE CONFIANZA.'
else
  echo '❌ HAY `sorry` O AGUJEROS DE CONFIANZA.'
  exit 1
fi
