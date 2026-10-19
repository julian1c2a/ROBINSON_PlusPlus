#!/bin/bash
# a_mutantes_t04b.bash [SALIDA] — los mutantes de T04b (ADR-169): cada uno cambia UNA cosa en el árbol, corre
# check-doc-sync.bash entero y lo deshace (también si se interrumpe). Imprime, por mutante, el código de salida y las
# líneas de [A], [A2] e [I]. Lo esperado: rojo en todos menos en los dos de control (marcador de historia y cita «…»).
# El techo de [A2] sobre la base verificada se ve fallar con BASE_TECHO=<commit que tiene la tabla> (ADR-169 §4): sube
# una entrada de la tabla y añade la línea que la cuadra, de modo que sólo el techo pueda verlo. SOLO=<nombre> corre
# sólo ese mutante (p. ej. SOLO=A2-techo BASE_TECHO=HEAD, tras el commit que trae la tabla).
export PATH="/usr/bin:/bin:$PATH"
cd "$(dirname "$0")/../../.." || exit 2
SAL=${1:-/dev/stdout}
TMP=$(mktemp -d)
FICH="CURRENT-STATUS-PROJECT.md NEXT-STEPS.md doc/control/a2-deuda.tsv ROBINSON_PlusPlus/Meta/Lob.lean"
for f in $FICH; do cp "$f" "$TMP/$(printf '%s' "$f" | tr / _)"; done
restaura() { for f in $FICH; do cp "$TMP/$(printf '%s' "$f" | tr / _)" "$f"; done; }
trap 'restaura; rm -rf "$TMP"' EXIT INT TERM
inserta() { awk -v l="$2" -v t="$3" '{ print } NR == l { print t }' "$1" > "$TMP/x" && cat "$TMP/x" > "$1"; }
corre() {   # $1 = nombre, $2 = lo que se cambió; el resto, variables de entorno para check-doc-sync
  local n="$1" que="$2"; shift 2
  # (SOLO=<nombre> corre sólo ese mutante; los demás se deshacen sin correr)
  if [ -n "$SOLO" ] && [ "$SOLO" != "$n" ]; then restaura; return 0; fi
  env "$@" bash check-doc-sync.bash ${CDS_ARGS:-} > "$TMP/out" 2>&1; local rc=$?
  restaura
  { echo "== $n (salida $rc): $que"
    LC_ALL=C awk '/^════ \[(A|A2|I)\]/ { p = 1; print; next } /^════/ { p = 0 } p && NF' "$TMP/out" | cut -c1-200
    echo; } >> "$SAL"
}
: > "$SAL" 2>/dev/null || true
echo "# a_mutantes_t04b.bash, $(date -u +%Y-%m-%dT%H:%MZ), HEAD $(git rev-parse --short HEAD) (más el árbol de trabajo)" >> "$SAL"
echo >> "$SAL"
inserta CURRENT-STATUS-PROJECT.md 5 'Estado 2026-10-19: **120** jobs en el build.'
corre A-cabecera-fecha-negrita 'la cabecera dice «**120** jobs» con una fecha (antes la fecha la eximía, y la negrita la cegaba)'
inserta CURRENT-STATUS-PROJECT.md 5 'Hoy hay **44** `sondeos/`.'
corre A-cabecera-sondeos 'la cabecera dice 44 sondeos (SOND se calculaba y no se comparaba)'
inserta NEXT-STEPS.md 150 'Build 2026-10-19: 122 jobs.'
corre A2-cuerpo-cifra-nueva 'una cifra vieja NUEVA en el cuerpo, con fecha'
inserta NEXT-STEPS.md 150 'Build (histórico): 122 jobs.'
corre A2-control-historico 'CONTROL: la misma línea con un marcador de historia (debe salir verde)'
LC_ALL=C awk -F'\t' 'BEGIN { OFS = "\t" } $1 == "axiom de Lean" && $2 == "README.md" && $3 == "5" { $4 = $4 + 1 } { print }' \
  doc/control/a2-deuda.tsv > "$TMP/x" && cat "$TMP/x" > doc/control/a2-deuda.tsv
corre A2-tabla-por-encima-de-hoy 'la tabla dice una línea más de las que hay (una cifra arreglada sin bajar la tabla)'
corre A2-sin-base 'no hay base verificada (B_BASE_REF a una rama que no existe)' B_BASE_REF=refs/heads/no-existe-t04b
SUELTO=$(git commit-tree "HEAD^{tree}" -m 'mutante T04b: un commit sin padre')
corre A2-base-no-antepasada 'la base no es antepasada de HEAD (un commit suelto)' B_BASE_REF="$SUELTO"
if [ -n "$BASE_TECHO" ]; then
  # (una cifra vieja nueva en el cuerpo, y la entrada de la tabla que la cuadra: hoy y la tabla coinciden)
  inserta NEXT-STEPS.md 150 'Build: 0 jobs.'
  printf 'jobs\tNEXT-STEPS.md\t0\t1\n' >> doc/control/a2-deuda.tsv
  corre A2-techo 'la tabla sube con una línea que la cuadra: sólo el techo de la base verificada lo ve' B_BASE_REF="$BASE_TECHO"
fi
inserta NEXT-STEPS.md 150 'MUTANTE: la mitad ⊬¬G no existe todavía; Rosser está pendiente.'
corre I-documento 'dos frases que goedel_I_neg y rosser desmienten, en el cuerpo de NEXT-STEPS.md'
inserta NEXT-STEPS.md 150 'Se dijo «la mitad ⊬¬G no existe».'
corre I-control-cita 'CONTROL: la frase citada entre «…» (debe salir verde)'
inserta ROBINSON_PlusPlus/Meta/Lob.lean 39 '-- MUTANTE: la mitad ⊬¬G sigue abierta.'
corre I-comentario-lean 'la frase en un comentario de un .lean de la librería (T31)'
# ── los de la revisión adversarial de ADR-169 (§9) ──
inserta CURRENT-STATUS-PROJECT.md 5 'Fuera de las listas: **1** `axiom` de Lean.'
corre A-cabecera-palabra-dentro 'el marcador «era» dentro de «fuera» ya no exime (era CURRENT-STATUS-PROJECT.md:48)'
inserta CURRENT-STATUS-PROJECT.md 5 'Son 120 jobs (ver «ADR-121»).'
corre A-cabecera-cita-con-digito 'una cita «…» con un dígito en otra parte de la línea ya no la exime'
rm -f doc/control/a2-deuda.tsv
corre A2-tabla-borrada 'la tabla, borrada (tiene que existir siempre)'
LC_ALL=C awk '!/^#/ && !d { print; d = 1 } { print }' doc/control/a2-deuda.tsv > "$TMP/x" && cat "$TMP/x" > doc/control/a2-deuda.tsv
corre A2-clave-repetida 'una clave repetida en la tabla'
CDS_ARGS=--quick corre A2-control-quick 'CONTROL: con --quick (los jobs sin medir), [A2] no da rojo ni toca la tabla'
inserta NEXT-STEPS.md 150 $'LA MITAD \xe2\x8a\xac\xc2\xa0\xc2\xacG NO EST\xc3\x81 CERRADA.'
corre I-mayusculas-espacio-duro 'mayúsculas (también «Á») y un espacio duro entre «⊬» y «¬G»'
inserta NEXT-STEPS.md 150 'no existe aún.'
inserta NEXT-STEPS.md 150 'La mitad ⊬¬G'
corre I-partida 'la frase partida en dos líneas'
inserta NEXT-STEPS.md 150 '`⊬¬G` **no** está cerrado.'
corre I-negrita 'la negrita entre el símbolo y la frase'
