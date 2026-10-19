#!/bin/bash
# t7c: [I] VERBATIM con la negación y el «⊬» escritos de otras formas, y con «histórico» en cualquier sitio de la línea.
H=$(cd "$(dirname "$0")" && pwd); T=$H/t7c_dir; rm -rf "$T"; mkdir -p "$T"; cd "$T"
printf '%s\n' goedel_I_neg > decls
cat > doc.md <<'EOF2'
# Doc
L2 control: la mitad ⊬¬G no existe.
L3 la mitad ⊬∼G no existe.
L4 la mitad ⊬ ~G no existe.
L5 la mitad $\nvdash \neg G$ no existe.
L6 la mitad «no ⊢ ¬G» no existe (citada).
L7 la mitad ⊬ neg G no existe.
L8 la mitad PA ⊬ ¬G_R no existe.
L9 la mitad ⊬¬G no existe (lo confirma el histórico de commits).
L10 la mitad ⊢¬G no es derivable y sigue abierta.
L11 la mitad ⊬¬𝐺 no existe.
EOF2
DOCS=doc.md DECLS=$T/decls CIERRE= bash "$H/harness.bash" "$T" I | grep -oE 'doc[.]md:[0-9]+|✓|FAIL=.' | tr '\n' ' '; echo
