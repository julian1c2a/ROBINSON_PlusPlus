#!/bin/bash
# scripts/leanchecker-cobertura.bash — QUÉ replaya `leanchecker`: los módulos de su `--verbose`, contra los de las tres
# librerías y contra los `.olean` que hay (T23, ADR-222).
#
# Uso (en la CI, tras `lake env leanchecker --verbose ROBINSON_PlusPlus FOL TheoryFramework > <log>`):
#   bash scripts/leanchecker-cobertura.bash <log>
#
# `leanchecker` replaya todo `.olean` del camino de búsqueda cuyo módulo empieza por uno de los prefijos, y sólo da
# error si un prefijo no encuentra NINGUNO (LeanChecker.lean, `checkOlean`). Cuántos replayaba no lo decía nadie: un
# camino de búsqueda que perdiera una carpeta, o un `.olean` que faltara, pasaban en verde. Aquí, tres conjuntos de
# módulos, que tienen que ser IGUALES:
#   · los que replayó (las líneas «replaying M» del log);
#   · los de las fuentes: los `.lean` versionados de las tres librerías (sus `globs` son `.andSubmodules`: todo el
#     directorio y la raíz; `[L]` de check-doc-sync comprueba que el cierre de imports es eso mismo);
#   · los `.olean` de esos módulos en las carpetas de build de RPP y de FOL (uno de más es un FANTASMA que leanchecker
#     replayaría; uno de menos, un módulo que no comprobó nadie).
# Antes, un autotest: una lista con un módulo de menos y otra con uno de más tienen que dar distinto. Si no, exit 2.

set -uo pipefail
export PATH="/usr/bin:$PATH"
cd "$(dirname "$0")/.." || exit 2

LOG=${1:-}
[ -n "$LOG" ] && [ -s "$LOG" ] || { echo "❌ NO PUEDO MEDIR: no hay log de leanchecker («$LOG»)"; exit 2; }
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT

# los módulos de una lista de rutas `.lean` (relativas a la raíz de su repo)
modulos() { sed 's/\.lean$//; s#/#.#g' | LC_ALL=C sort -u; }
# iguales <a> <b>: 0 si las dos listas (ordenadas) son iguales
iguales() { cmp -s "$1" "$2"; }

{ git ls-files 'ROBINSON_PlusPlus.lean' 'ROBINSON_PlusPlus/*.lean'
  git -C ../FOL ls-files 'FOL.lean' 'FOL/*.lean' 'TheoryFramework.lean' 'TheoryFramework/*.lean'; } | modulos > "$T/fuentes"
[ -s "$T/fuentes" ] || { echo "❌ NO PUEDO MEDIR: ninguna fuente (¿falta ../FOL?)"; exit 2; }

# ── autotest ─────────────────────────────────────────────────────────────────────────────────────────────────────────
sed 1d "$T/fuentes" > "$T/menos"
{ cat "$T/fuentes"; echo "ROBINSON_PlusPlus.Fantasma"; } | LC_ALL=C sort > "$T/mas"
if ! iguales "$T/fuentes" "$T/fuentes" || iguales "$T/menos" "$T/fuentes" || iguales "$T/mas" "$T/fuentes"; then
  echo "❌ NO PUEDO MEDIR: el autotest falla (la comparación no distingue un módulo de menos o de más)"; exit 2
fi

tr -d '\r' < "$LOG" | sed -n 's/^replaying \([^ ]*\)$/\1/p' | LC_ALL=C sort -u > "$T/replayados"
for d in .lake/build/lib/lean ../FOL/.lake/build/lib/lean; do
  [ -d "$d" ] || continue
  (cd "$d" && find ROBINSON_PlusPlus FOL TheoryFramework -name '*.olean' 2>/dev/null
   for r in ROBINSON_PlusPlus FOL TheoryFramework; do [ -f "$r.olean" ] && echo "$r.olean"; done)
done | sed 's/\.olean$/.lean/' | modulos > "$T/oleans"

NF=$(wc -l < "$T/fuentes"); NR=$(wc -l < "$T/replayados"); NO=$(wc -l < "$T/oleans")
FAIL=0
echo "módulos: $NF de las fuentes, $NR replayados por leanchecker, $NO .olean (autotest: 3 de 3)"
if iguales "$T/replayados" "$T/fuentes"; then
  echo "✓ leanchecker replayó exactamente los $NF módulos de las tres librerías"
else
  echo "❌ leanchecker NO replayó los módulos de las fuentes:"
  LC_ALL=C comm -13 "$T/replayados" "$T/fuentes" | sed 's/^/   sin replayar: /' | head -20
  LC_ALL=C comm -23 "$T/replayados" "$T/fuentes" | sed 's/^/   replayado sin fuente: /' | head -20
  FAIL=1
fi
if iguales "$T/oleans" "$T/fuentes"; then
  echo "✓ y hay un .olean por módulo, ni uno más"
else
  echo "❌ los .olean no son los módulos de las fuentes:"
  LC_ALL=C comm -13 "$T/oleans" "$T/fuentes" | sed 's/^/   sin .olean: /' | head -20
  LC_ALL=C comm -23 "$T/oleans" "$T/fuentes" | sed 's/^/   .olean sin fuente: /' | head -20
  FAIL=1
fi
if [ -n "${GITHUB_STEP_SUMMARY:-}" ]; then
  { echo "### Cobertura de leanchecker (T23)"; echo ""
    echo "$NF módulos en las fuentes · $NR replayados · $NO \`.olean\` · $([ "$FAIL" -eq 0 ] && echo "✓ iguales" || echo "❌ distintos")"; } >> "$GITHUB_STEP_SUMMARY"
fi
exit "$FAIL"
