#!/bin/bash
# t10: ¿el autotest de [I] (salida exacta «2;3;5;15;») mata los mutantes que HACEN CALLAR a [I]? Se corre el bloque [I]
# VERBATIM (harness.bash) con una copia mutada del script; un mutante VIVO (el autotest pasa) con el que una frase falsa
# real deja de marcarse es un hueco del autotest.
H=$(cd "$(dirname "$0")" && pwd); T=$H/t10_dir; rm -rf "$T"; mkdir -p "$T"; cd "$T"
printf '%s\n' goedel_I_neg rosser lob > decls
printf '%s\n' '# Estado' 'Rosser está pendiente.' 'La mitad ⊬¬G falta.' '## Hoy' 'Löb, por hacer.' > real.md
printf '%s\n' '# Otro' 'Nota: el capítulo HISTÓRICO va aparte.' 'La mitad ⊬¬G no existe.' > real2.md
corre () { # $1 = nombre  $2 = expresión sed sobre el script
  sed "$2" "$H/rpp-check.bash" > "$H/rpp-check.mut.bash"
  if cmp -s "$H/rpp-check.bash" "$H/rpp-check.mut.bash"; then echo "  $1: el sed NO cambió nada (mutante nulo)"; return; fi
  out=$(cd "$H" && sed -i 's|SCRIPT=$H/rpp-check.bash|SCRIPT=${MUT:-$H/rpp-check.bash}|' harness.bash; \
        MUT=$H/rpp-check.mut.bash DOCS="real.md real2.md" DECLS=$T/decls CIERRE= bash "$H/harness.bash" "$T" I)
  if printf '%s' "$out" | grep -q 'NO PUDE MEDIR'; then echo "  $1: MUERTO (el autotest falla)"
  else echo "  $1: VIVO — [I] marca: $(printf '%s\n' "$out" | grep -oE 'real2?[.]md:[0-9]+' | tr '\n' ' ')"; fi
}
echo "== sin mutar (lo que debe marcar: real.md:2, real.md:3, real.md:5 y real2.md:3):"; corre original 's/^//'
corre "M1 regla de Rosser rota"            's/rosser\[^.|\]{0,30}(pendiente/rosserX[^.|]{0,30}(pendiente/'
corre "M2 «DOCUMENTO» fuera de hist_doc"   's|FNR <= 10 \&\& /DOCUMENTO HIST(O\|Ó)RICO/|FNR <= 10 \&\& /HIST(O\|Ó)RICO/|'
corre "M3 hist_doc en todo el fichero"     's|FNR <= 10 \&\& /DOCUMENTO|FNR >= 1 \&\& /DOCUMENTO|'
corre "M4 sección de registro también de nivel 1" 's/if (!reg \&\& lv >= 2 \&\&/if (!reg \&\& lv >= 1 \&\&/'
corre "M5 sin «falta» en la regla 1"       's/sigue abiert|abiert\[oa\]|falta|pendiente|sin cerrar)/sigue abiert|abiert[oa]|pendiente|sin cerrar)/'
corre "M6 marcador «s» (todo exime)"       's/inexact\/) next/inexact|s\/) next/'
rm -f "$H/rpp-check.mut.bash"
