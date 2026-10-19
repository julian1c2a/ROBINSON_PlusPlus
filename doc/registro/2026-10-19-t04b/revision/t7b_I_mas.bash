#!/bin/bash
# t7b: más casos de [I] (VERBATIM, harness.bash): rojos falsos (frases CIERTAS que marca) y evasiones con un punto.
H=$(cd "$(dirname "$0")" && pwd); T=$H/t7b_dir; rm -rf "$T"; mkdir -p "$T"; cd "$T"
printf '%s\n' goedel_I_neg rosser lob > decls
cat > doc.md <<'EOF2'
# Doc
L2 CIERTA: la mitad ⊬¬G está demostrada (goedel_I_neg); lo que falta es Con'.
L3 CIERTA: ⊬¬G se cerró en ADR-121, y la pregunta abierta es otra.
L4 CIERTA: Löb (ADR-159) cerrado; Rosser sin la hipótesis E, pendiente de pulir. 
L5 FALSA: ⊬¬G (cf. ADR-121) no existe.
L6 FALSA: la mitad ⊬¬G, véase el apartado 3.2, no existe.
L7 FALSA: ⊬¬G no existe en ningún cálculo de los que hay hoy en el árbol, ni en Meta ni en Full ni en el resto.
L8 FALSA: la mitad ⊬¬G —la que importa para la indecidibilidad de verdad, la de Gödel— no existe.
EOF2
DOCS=doc.md DECLS=$T/decls CIERRE= bash "$H/harness.bash" "$T" I | grep -oE 'doc[.]md:[0-9]+|✓.*|FAIL=.' | tr '\n' ' '; echo
