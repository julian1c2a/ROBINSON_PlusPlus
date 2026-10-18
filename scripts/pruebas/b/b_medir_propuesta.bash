#!/bin/bash
# b_medir_propuesta.bash DIR_SALIDA [W] — la medición de la PROPUESTA de T04 (ADR‑166) sobre los documentos de RPP, con
# la PRIMERA versión del núcleo (la que FOL subió en 4d81a12, que se saca de git: la de hoy lee otras entradas):
# universo de identificadores con forma de declaración, ventana de W bytes (100 por omisión), sin la fecha como
# marcador, y [B2] (las rutas). Queda para el registro de ADR‑166; el control de hoy es [B] de check-doc-sync.bash.
# Desde PowerShell (necesita `lake` para volcar el entorno).
export PATH="/usr/bin:/bin:$PATH"
OUT=$1; W=${2:-100}
cd "$(dirname "$0")/../../.." || exit 2
mkdir -p "$OUT"
git -C ../FOL show 4d81a12:b-citas.awk > "$OUT/b-citas-v1.awk" || { echo "no encuentro la primera versión del núcleo (FOL 4d81a12)"; exit 2; }
VOLCADO="$OUT/env.txt" lake env lean scripts/VolcarEntorno.lean > /dev/null || { echo "no pude volcar el entorno"; exit 2; }
DECL_RE="(^|[^A-Za-z0-9_'.])(theorem|lemma|def|abbrev|axiom|opaque|instance|structure|inductive|class) +[^[:space:]:({[]+"
NOMBRES='{n = $NF; sub(/[.]$/, "", n); if (n == "") next; print n; k = n; sub(/.*[.]/, "", k); if (k != n && k != "") print k}'
find ROBINSON_PlusPlus/ ROBINSON_PlusPlus.lean cuarentena/ ../FOL/FOL/ ../FOL/TheoryFramework/ ../FOL/FOL.lean -name '*.lean' ! -path '*/.lake/*' -print0 2>/dev/null \
  | xargs -0 env LC_ALL=C awk -f strip-lean.awk | LC_ALL=C grep -oE "$DECL_RE" | LC_ALL=C awk "$NOMBRES" | LC_ALL=C sort -u > "$OUT/vivos.txt"
find sondeos/ -name '*.lean' 2>/dev/null | sort | while IFS= read -r f; do
  LC_ALL=C awk -f strip-lean.awk "$f" | LC_ALL=C grep -oE "$DECL_RE" | LC_ALL=C awk "$NOMBRES" | LC_ALL=C awk -v f="$f" '{print $0 "|" f}'
done | LC_ALL=C sort -u > "$OUT/sondeos.txt"
{ git ls-files '*.lean'; git -C ../FOL ls-files '*.lean'; } | sed 's/[.]lean$//; s|/|.|g' \
  | LC_ALL=C awk '{ n = $0; print n; while (sub(/^[^.]*[.]/, "", n)) print n }' | LC_ALL=C sort -u > "$OUT/modulos.txt"
{ git ls-files; git -C ../FOL ls-files; git tag; git -C ../FOL tag; } | LC_ALL=C sort -u > "$OUT/rutas.txt"
MARK='YA NO EXISTE|NO EXISTEN|retirad|RETIRADO|eliminad|borrad|legacy|F7a|histórico|ANTERIORES|🗑️|muert|Aquí vivía|tampoco existe|inexistente|desapareci|ya no son|se borró'
MARK="$MARK"'|propuest|candidat|hipot(e|é)tic|har(i|í)a falta|si se |habr(i|í)a que|añadir |descartad|no existe|NO EXISTE|sin materializar'
MARK="$MARK"'|falta|FALTA|construir|objetivo|medir|sin medir|pendiente|⏳|abiert|necesita|exige|pide|TAREA|hace falta|no hay ni habrá|sub‑familia|sub-familia|buscaba|buscó|usan la'
AUTHORITATIVE="REFERENCE.md CURRENT-STATUS-PROJECT.md DEPENDENCIES.md DECISIONS.md README.md AXIOMS.md GODEL-STATUS.md NEXT-STEPS.md"
AUTHORITATIVE="$AUTHORITATIVE TEOREMAS-E-HIPOTESIS.md $(ls doc/REFERENCE-*.md 2>/dev/null) cuarentena/README.md sondeos/README.md"
DOCS=""; for d in $AUTHORITATIVE; do [ -f "$d" ] && DOCS="$DOCS $d"; done
LC_ALL=C awk -v MARK="$MARK" -v W="$W" -f "$OUT/b-citas-v1.awk" "$OUT/vivos.txt" "$OUT/env.txt" "$OUT/sondeos.txt" \
  "$OUT/modulos.txt" "$OUT/rutas.txt" $DOCS > "$OUT/muertas.txt"
for c in B B2; do
  n=$(grep -c "^$c|" "$OUT/muertas.txt"); k=$(grep "^$c|" "$OUT/muertas.txt" | cut -d'|' -f2 | sort -u | grep -c .)
  echo "$c (W=$W): $n citas sin absolver, $k claves"
done
