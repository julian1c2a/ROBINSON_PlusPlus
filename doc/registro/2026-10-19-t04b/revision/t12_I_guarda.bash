#!/bin/bash
# t12: la guarda de [I] (B_DECLS_OK y `goedel_I_neg` en $DECLS) y lo que NO guarda: si `rosser` o `lob` cambian de
# nombre (o no salen en $DECLS), sus reglas se apagan EN SILENCIO.
H=$(cd "$(dirname "$0")" && pwd); T=$H/t12_dir; rm -rf "$T"; mkdir -p "$T"; cd "$T"
printf '%s\n' '# Doc' 'Rosser está pendiente.' 'Löb está pendiente.' 'La mitad ⊬¬G no existe.' > doc.md
run () { printf '  %-58s ' "$1"; shift; env "$@" DOCS=doc.md CIERRE= bash "$H/harness.bash" "$T" I | grep -oE 'doc[.]md:[0-9]+|✓|FAIL=.|NO PUDE MEDIR' | tr '\n' ' '; echo; }
printf '%s\n' goedel_I_neg rosser lob > d_todo; printf '%s\n' rosser lob > d_sin_goedel; printf '%s\n' goedel_I_neg rosser_teorema lob_teorema > d_renombrados
run "B_DECLS_OK=0:"                                   B_DECLS_OK=0 DECLS=$T/d_todo
run "sin goedel_I_neg en DECLS:"                      B_DECLS_OK=1 DECLS=$T/d_sin_goedel
run "todo vivo:"                                      B_DECLS_OK=1 DECLS=$T/d_todo
run "rosser y lob RENOMBRADOS (rosser_teorema, lob_teorema):" B_DECLS_OK=1 DECLS=$T/d_renombrados
