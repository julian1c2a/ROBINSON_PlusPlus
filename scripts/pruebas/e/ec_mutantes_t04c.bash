#!/bin/bash
# ec_mutantes_t04c.bash [SALIDA] — los mutantes de T04c (ADR-177): cada uno cambia UNA cosa en el árbol, corre
# check-doc-sync.bash entero —el de hoy y, para comparar, el de HEAD (`git show HEAD:check-doc-sync.bash`)— y lo
# deshace (también si se interrumpe). Imprime, por mutante y por versión, el código de salida y las líneas de [E] y [C].
# Lo esperado, con el de hoy: rojo en E-cabecera-al-dia, C-subcadena y C-fuera-de-catalogo; verde en E-seccion-al-dia
# (el sello de una sección ya no cuenta) y en el de control (el árbol tal cual).
export PATH="/usr/bin:/bin:$PATH"
cd "$(dirname "$0")/../../.." || exit 2
SAL=${1:-/dev/stdout}
TMP=$(mktemp -d)
FICH="REFERENCE.md doc/REFERENCE-Kernel.md"
for f in $FICH; do cp "$f" "$TMP/$(printf '%s' "$f" | tr / _)"; done
git show HEAD:check-doc-sync.bash > check-doc-sync.viejo.bash
restaura() { for f in $FICH; do cp "$TMP/$(printf '%s' "$f" | tr / _)" "$f"; done; }
trap 'restaura; rm -f check-doc-sync.viejo.bash; rm -rf "$TMP"' EXIT INT TERM
HOY=$(date +%F)
corre() {   # $1 = nombre, $2 = lo que se cambió (el árbol ya lleva el cambio)
  local n="$1" que="$2" v rc
  echo "== $n: $que" >> "$SAL"
  for v in check-doc-sync.bash check-doc-sync.viejo.bash; do
    bash "$v" > "$TMP/out" 2>&1; rc=$?
    { echo "-- $v (salida $rc)"
      LC_ALL=C awk '/^════ \[(E|C)\]/ { p = 1; print; next } /^════/ { p = 0 } p && NF' "$TMP/out" \
        | grep -E '════|REFERENCE-Kernel|Diagonal|SegundoModelo|deuda declarada|✓|❌' | cut -c1-200
    } >> "$SAL"
  done
  echo >> "$SAL"
  restaura
}
: > "$SAL" 2>/dev/null || true
echo "# ec_mutantes_t04c.bash, $(date -u +%Y-%m-%dT%H:%MZ), HEAD $(git rev-parse --short HEAD) (más el árbol de trabajo)" >> "$SAL"
echo >> "$SAL"
corre control 'CONTROL: el árbol tal cual (los dos, verdes)'
sed -i "14s/\*\*Last updated:\*\* 2026-10-05/**Last updated:** $HOY/" doc/REFERENCE-Kernel.md
corre E-cabecera-al-dia 'la CABECERA de doc/REFERENCE-Kernel.md (a mitad de línea), al día: el de hoy dice «deuda saldada»; el viejo leía la de una sección y no lo veía'
sed -i "46s/^\*\*Last updated\*\*: 2026-06-06/**Last updated**: $HOY/" doc/REFERENCE-Kernel.md
corre E-seccion-al-dia 'sólo el sello de una SECCIÓN, al día: el de hoy sigue leyendo la cabecera (deuda declarada, verde); el viejo daba «deuda saldada»'
sed -i '178s/`Diagonal.lean`/`Diag.lean`/' REFERENCE.md
corre C-subcadena '«Diagonal» sale de §1 y sólo queda como subcadena de «DiagonalNumeral»: el viejo lo absolvía'
sed -i '/^| 84zn | \*\*`SegundoModelo`\*\*/d' REFERENCE.md
printf '\nSegundoModelo, citado fuera del catálogo.\n' >> REFERENCE.md
corre C-fuera-de-catalogo '«SegundoModelo» sale de §1 y sólo se cita al final del documento: el viejo lo absolvía'
