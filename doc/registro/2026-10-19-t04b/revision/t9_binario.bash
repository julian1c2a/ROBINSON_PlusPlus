#!/bin/bash
# t9: un byte que no es UTF-8 (0xFF) o un NUL en un documento. [A] y [A2] usan `grep` SIN -a y en la configuración del
# entorno: en UTF-8, grep suprime la línea mal codificada (y con un NUL, todo lo que sigue) y lo dice por stderr, que
# el script tira (2>/dev/null). Se corre [A] VERBATIM (harness.bash) sobre dos documentos de juguete.
H=$(cd "$(dirname "$0")" && pwd); T=$H/t9_dir; rm -rf "$T"; mkdir -p "$T"; cd "$T"
printf 'Estado: el build tiene 99 jobs. \xff\n' > A.md            # cifra vieja + byte inválido en LA MISMA línea
printf 'Estado: 0 sorry.\n' > B.md
printf 'Estado: hoy el build tiene 98 jobs.\n' >> B.md             # cifra vieja, línea limpia
echo "--- 0xFF en la línea de la cifra vieja (A.md); B.md limpio:"
for loc in C ${UTF:-es_ES.UTF-8}; do printf '  LC_ALL=%-12s ' "$loc"; LC_ALL=$loc DOCS="A.md B.md" bash "$H/harness.bash" "$T" A | grep -oE 'dice [0-9]+|FAIL=.' | tr '\n' ' '; echo; done
printf 'Intro\0 con un NUL\n' > A.md
echo "--- un NUL en A.md (delante de B.md en DOCS):"
for loc in C ${UTF:-es_ES.UTF-8}; do printf '  LC_ALL=%-12s ' "$loc"; LC_ALL=$loc DOCS="A.md B.md" bash "$H/harness.bash" "$T" A | grep -oE 'dice [0-9]+|FAIL=.' | tr '\n' ' '; echo; done
