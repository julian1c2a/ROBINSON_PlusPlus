#!/bin/bash
# t7d: [I] (VERBATIM) quita lo que va entre «…» ANTES de mirar la regla: si el SÍMBOLO va entre comillas latinas (uso
# corriente en español para un término), la frase entera desaparece.
H=$(cd "$(dirname "$0")" && pwd); T=$H/t7d_dir; rm -rf "$T"; mkdir -p "$T"; cd "$T"
printf '%s\n' goedel_I_neg rosser lob > decls
printf '%s\n' '# Doc' 'L2 La mitad ⊬¬G no existe.' 'L3 La mitad «⊬¬G» no existe.' 'L4 El teorema de «Rosser» está pendiente.' 'L5 «Löb» está por hacer.' > doc.md
DOCS=doc.md DECLS=$T/decls CIERRE= bash "$H/harness.bash" "$T" I | grep -oE 'doc[.]md:[0-9]+|✓|FAIL=.' | tr '\n' ' '; echo
