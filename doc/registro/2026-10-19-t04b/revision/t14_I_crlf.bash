#!/bin/bash
# t14: [I] (VERBATIM) con el mismo documento en LF (como en la CI) y en CRLF (como queda en Windows con
# core.autocrlf=true tras un checkout): la regla «no est(a|á)[^a-z]» necesita un carácter DETRÁS, y el \r lo pone.
H=$(cd "$(dirname "$0")" && pwd); T=$H/t14_dir; rm -rf "$T"; mkdir -p "$T"; cd "$T"
printf '%s\n' goedel_I_neg > decls
printf '%s\n' '# Doc' 'La mitad ⊬¬G no está' 'cerrada todavía (la línea sigue abajo).' > lf.md
sed 's/$/\r/' lf.md > crlf.md
for f in lf.md crlf.md; do printf '  %-8s ' "$f"; DOCS=$f DECLS=$T/decls CIERRE= bash "$H/harness.bash" "$T" I | grep -oE '[a-z]+[.]md:[0-9]+|✓|FAIL=.' | tr '\n' ' '; echo; done
