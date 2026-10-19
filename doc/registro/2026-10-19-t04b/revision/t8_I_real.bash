#!/bin/bash
# t8: [I] sobre el árbol REAL (documentos: la copia wt/; .lean: los del cierre, leídos del repo), con el awk VERBATIM y con
# una variante que, en vez de saltar las líneas exentas, dice POR QUÉ las salta (marcador de línea, sección, valla).
H=$(cd "$(dirname "$0")" && pwd); R=/e/Dropbox/GitHub/lean4/ROBINSON_PlusPlus; SCRIPT=$H/rpp-check.bash
eval "$(sed -n "$(grep -n '^I_REGLAS=\$(mktemp)' "$SCRIPT" | cut -d: -f1),$(grep -n "^  > \"\$I_REGLAS\"" "$SCRIPT" | cut -d: -f1)p" "$SCRIPT")"
eval "$(sed -n "$(grep -n "^I_AWK='" "$SCRIPT" | cut -d: -f1),$(grep -n "substr(\$0, 1, 140) }'" "$SCRIPT" | cut -d: -f1)p" "$SCRIPT")"
printf '%s\n' goedel_I_neg rosser rosser_ext lob > "$H/t8_vivos"
DOCS=$(cat "$H/docs.list"); LEAN=$(grep '^ROBINSON_PlusPlus/.*[.]lean$' "$H/cierre.txt")
echo "== VERBATIM, documentos (wt):"; (cd "$H/wt" && LC_ALL=C awk "$I_AWK" "$I_REGLAS" "$H/t8_vivos" $DOCS) | cut -c1-200
echo "== VERBATIM, .lean del cierre ($(echo "$LEAN" | wc -l)):"; (cd "$R" && LC_ALL=C awk "$I_AWK" "$I_REGLAS" "$H/t8_vivos" $LEAN) | cut -c1-200
# la variante: lo que las exenciones SALTAN
V=$(printf '%s' "$I_AWK" | sed 's/^  hist_doc { next }/  hist_doc { why = "DOC-HIST" }/; s/^  valla { next }/  valla { why = "VALLA" }/; s/^  reg { next }/  reg { why = "SECCION" }/' \
  | sed 's/if (l ~ \/✏️|hist(o|ó)ric|registro|era |falso|ya no |antes|previo|correcci|inexact\/) next/if (l ~ \/✏️|hist(o|ó)ric|registro|era |falso|ya no |antes|previo|correcci|inexact\/) why = why "MARCADOR(" (match(l, \/✏️|hist(o|ó)ric|registro|era |falso|ya no |antes|previo|correcci|inexact\/) ? substr(l, RSTART, RLENGTH) : "") ")"/' \
  | sed 's/print FILENAME ":" FNR ": " POR\[i\] "\t" substr(\$0, 1, 140) }/{ if (why != "") print "EXENTA[" why "] " FILENAME ":" FNR ": " substr($0, 1, 160) }; why = "" }/')
V=$(printf '%s' "$V" | sed 's/^  { l = tolower/  { why = why; l = tolower/')
echo "== EXENTAS (documentos):"; (cd "$H/wt" && LC_ALL=C awk "$V" "$I_REGLAS" "$H/t8_vivos" $DOCS 2>&1) | sort | uniq | cut -c1-260
echo "== EXENTAS (.lean):"; (cd "$R" && LC_ALL=C awk "$V" "$I_REGLAS" "$H/t8_vivos" $LEAN 2>&1) | sort | uniq | cut -c1-260
rm -f "$I_REGLAS"; rm -rf "$I_AUTO"
