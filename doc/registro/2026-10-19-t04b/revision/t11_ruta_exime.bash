#!/bin/bash
# t11: EXC_A se aplica a la línea ENTERA que da `grep -n` sobre la región, «N:documento:texto»: la RUTA del documento
# también puede eximir. Un REFERENCE nuevo (RPP los añade solo, `ls doc/REFERENCE-*.md`) con «antes» en el nombre.
H=$(cd "$(dirname "$0")" && pwd); T=$H/t11_dir; rm -rf "$T"; mkdir -p "$T/doc"; cd "$T"
for n in Kernel Constantes Variantes Ejemplos; do printf '%s\n' "# $n" 'Estado: el build tiene 99 jobs.' > "doc/REFERENCE-$n.md"; done
for n in Kernel Constantes Variantes Ejemplos; do printf '  %-32s ' "doc/REFERENCE-$n.md:"; DOCS="doc/REFERENCE-$n.md" bash "$H/harness.bash" "$T" A | grep -oE 'dice [0-9]+|FAIL=.' | tr '\n' ' '; echo; done
