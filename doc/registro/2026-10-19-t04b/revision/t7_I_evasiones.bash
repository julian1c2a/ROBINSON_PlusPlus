#!/bin/bash
# t7: [I] VERBATIM (harness.bash) sobre un documento sintético: cada línea, una frase FALSA (con goedel_I_neg, rosser y
# lob vivos). Lo que [I] NO marca es un verde falso salvo que la exención sea legítima.
H=$(cd "$(dirname "$0")" && pwd); T=$H/t7_dir; rm -rf "$T"; mkdir -p "$T/ROBINSON_PlusPlus/Meta"; cd "$T"
printf '%s\n' goedel_I_neg rosser rosser_ext lob otra > decls
NBSP=$'\xc2\xa0'
cat > doc.md <<EOF2
# Doc de prueba
L2 control: la mitad ⊬¬G no existe todavía.
L3 LA MITAD ⊬¬G NO EXISTE.
L4 La mitad ⊬¬G NO ESTÁ cerrada.
L5 La mitad ⊬${NBSP}¬G no existe.
L6 La mitad ⊬  ¬G no existe.
L7 La mitad ⊬ (¬G) no existe.
L8 La primera mitad, ⊬¬G, no existe.
L9 Las constantes de ⊬¬G no existen.
L10 La mitad ⊬¬G está pendiente, fuera de toda duda.
L11 Lo que todavía falta es la mitad
L12 ⊬¬G (partida en dos líneas).
L13 ⊬¬G (ver «ADR-121») no existe.
L14 ⊬¬G no existe; los falsos positivos, aparte.
L15 LÖB está pendiente.
L16 Löb sigue abierto.
L17 Rosser: falta.
L18 Löb no está demostrado.
L19 Rosser está por hacer; las variantes, también.
L20 Lo que queda abierto: ⊬¬G.
L21 ⊬ ¬G no existe (sin cerrar).
L22 PA ⊬ ¬ G: sin cerrar.
L23 ⊬¬G: sin cerrar (véase el registro).
L24 Rosser: el teorema no está hecho.
L25 Ya no hay excusa: ⊬¬G sigue abierta.
L26 El teorema de Rosser, PENDIENTE.
L27 Rosser (la versión fuerte) está pendiente de formalizar.
## Estado actual (sin registro aparte)
L29 ⊬¬G no existe.
## Hoy
L31 ⊬¬G falta.
\`\`\`text
L33 dentro de la valla
~~~
L35 ⊬¬G no existe (tras un ~~~ dentro de la valla).
\`\`\`
L37 ⊬¬G no existe (la valla se ha DESCOMPENSADO).
EOF2
printf '%s\n' '-- L1 ⊬¬G no existe (en un .lean)' 'theorem t : True := trivial -- Löb: pendiente' > ROBINSON_PlusPlus/Meta/X.lean
echo "== [I] sobre doc.md y X.lean (lo marcado):"
DOCS=doc.md DECLS=$T/decls CIERRE=$'ROBINSON_PlusPlus.lean\nROBINSON_PlusPlus/Meta/X.lean' bash "$H/harness.bash" "$T" I \
  | grep -oE '(doc[.]md|X[.]lean):[0-9]+|✓.*|FAIL=.|NO PUDE.*' | tr '\n' ' '; echo
echo "== un documento que dice «no es un DOCUMENTO HISTÓRICO» en su cabecera:"
printf '%s\n' '# Otro' 'Esto no es un DOCUMENTO HISTÓRICO: es el estado.' 'La mitad ⊬¬G no existe.' > doc2.md
DOCS=doc2.md DECLS=$T/decls CIERRE= bash "$H/harness.bash" "$T" I | grep -oE 'doc2[.]md:[0-9]+|✓.*|FAIL=.' | tr '\n' ' '; echo
echo "== un documento que NO existe en DOCS, delante de los demás (¿se pierde el resto?):"
DOCS="noexiste.md doc2.md doc.md" DECLS=$T/decls CIERRE=$'ROBINSON_PlusPlus/Meta/X.lean' bash "$H/harness.bash" "$T" I | grep -oE '(doc[.]md|X[.]lean):[0-9]+|✓.*|FAIL=.' | tr '\n' ' '; echo
