#!/bin/bash
# rotura_v5.bash — pruebas de rotura de los arreglos de la cuarta revisión (texto; sin lake), con copia y restauración.
set -uo pipefail
R=/e/dropbox/github/lean4/ROBINSON_PlusPlus
F=/e/dropbox/github/lean4/FOL
BK=$(mktemp -d)
cp "$R/check-doc-sync.bash" "$R/REFERENCE.md" "$BK/"
restaura () {
  cp "$BK/check-doc-sync.bash" "$R/check-doc-sync.bash"; cp "$BK/REFERENCE.md" "$R/REFERENCE.md"
  rm -f "$R/ROBINSON_PlusPlus/ZZRoturaV5.lean" "$F/TheoryFramework/ZZRoturaV5.lean" "$F/cuarentena/ZZ Rotura - copia.lean"
  rm -rf "$BK/vacio"
}
trap restaura EXIT
ok () { echo "✓ $*"; }; ko () { echo "✗✗ $*"; }

# a · el censo de agujeros, por token y con TheoryFramework
cat > "$R/ROBINSON_PlusPlus/ZZRoturaV5.lean" <<'EOF'
attribute [implemented_by realF] fakeF
@[simp, implemented_by realG] def fakeG (_ : Nat) : Bool := true
private opaque secreto : Nat
noncomputable opaque otro : Nat
private unsafe def peligro : Nat := 0
theorem c_false : c = false := Lean.ofReduceBool c false rfl
set_option debug.skipKernelTC true in theorem t : True := trivial
EOF
printf '@[implemented_by gImpl] def g (n : Nat) : Nat := n\n' > "$F/TheoryFramework/ZZRoturaV5.lean"
o=$(cd "$R" && bash check-sorry.bash 2>&1 | grep -E '❌|✓ los|SIN MEDIR')
for e in 'unsafe' 'opaque' 'implemented_by' 'ofReduceBool' 'skipKernelTC'; do
  printf '%s\n' "$o" | grep -q "❌ $e" && ok "a censo: $e" || ko "a censo: $e — $o"
done
printf '%s\n' "$o" | grep -qE '❌ implemented_by +3' && ok "a implemented_by cuenta 3 (dos en RPP y uno en TheoryFramework)" || ko "a implemented_by: $(printf '%s\n' "$o" | grep implemented_by)"
rm -f "$R/ROBINSON_PlusPlus/ZZRoturaV5.lean" "$F/TheoryFramework/ZZRoturaV5.lean"

# b · check-sorry: desde otro directorio mide SU repo; sin .lean, SIN MEDIR
o=$(cd /tmp && bash "$R/check-sorry.bash" 2>&1 | tail -1); printf '%s' "$o" | grep -q 'NI `sorry` NI AGUJEROS' && ok "b desde /tmp mide RPP: $o" || ko "b desde /tmp: $o"
mkdir -p "$BK/vacio"; cp "$R/check-sorry.bash" "$R/strip-lean.awk" "$BK/vacio/"
o=$(bash "$BK/vacio/check-sorry.bash" 2>&1 | tail -1); rc=$?
printf '%s' "$o" | grep -q 'SIN MEDIR' && ok "b sin ningún .lean ⇒ SIN MEDIR: $o" || ko "b sin .lean: $o"

# c · [A]: la frontera nueva y `axiom«x»`
printf 'def k := `axiom\ndef αaxiom : Nat := 1\naxiom«zz_oculto» : False\ndef t := 0 axiom zz2 : False\n' > "$R/ROBINSON_PlusPlus/ZZRoturaV5.lean"
o=$(cd "$R" && bash -c 'set -uo pipefail; eval "$(sed -n "/^AX_TOK=/,/^\[ -n \"\$AXIOMS\" \] || AXIOMS_MISSING=1/p" check-doc-sync.bash)"; echo "AXIOMS=[$AXIOMS] MISSING=$AXIOMS_MISSING"')
[ "$o" = "AXIOMS=[2] MISSING=0" ] && ok "c [A] cuenta axiom«x» y el de tras código, no el literal ni αaxiom — $o" || ko "c $o"
rm -f "$R/ROBINSON_PlusPlus/ZZRoturaV5.lean"

# d · B_TOPE contra el MÍNIMO de su historia
printf '\nEl lema vigente es `prf_nuevo_zz`.\n' >> "$R/REFERENCE.md"
sed -i 's/^repr_neg$/repr_neg\nprf_nuevo_zz/; s/^B_TOPE=41$/B_TOPE=42/' "$R/check-doc-sync.bash"
o=$(bash /tmp/runB.bash "$R" 2>&1 | grep -E 'mínimo|B_FAIL='); printf '%s' "$o" | grep -q 'sin un ADR' && printf '%s' "$o" | grep -q 'B_FAIL=1' && ok "d tope 42 > mínimo 41, sin ADR ⇒ rojo" || ko "d $o"
sed -i 's/^B_TOPE_ADR=""/B_TOPE_ADR="ADR-115:43"/' "$R/check-doc-sync.bash"
o=$(bash /tmp/runB.bash "$R" 2>&1 | grep -E 'mínimo|B_FAIL='); printf '%s' "$o" | grep -q 'B_FAIL=1' && ok "d con un ADR para OTRO valor (43) ⇒ rojo" || ko "d43 $o"
sed -i 's/^B_TOPE_ADR="ADR-115:43"/B_TOPE_ADR="ADR-115:42"/' "$R/check-doc-sync.bash"
o=$(bash /tmp/runB.bash "$R" 2>&1 | grep -E 'mínimo|B_FAIL='); printf '%s' "$o" | grep -q 'con ADR-115' && printf '%s' "$o" | grep -q 'B_FAIL=0' && ok "d con ADR-115:42 ⇒ aviso y verde" || ko "d42 $o"
cp "$BK/check-doc-sync.bash" "$R/check-doc-sync.bash"; cp "$BK/REFERENCE.md" "$R/REFERENCE.md"

# e · FOL check-axioms, parte de texto: la cuarentena con espacios en el nombre
printf 'axiom zz_copia : False\n' > "$F/cuarentena/ZZ Rotura - copia.lean"
o=$(cd "$F" && bash -c 'set -uo pipefail; STRIP_AWK="$PWD/strip-lean.awk"; eval "$(sed -n "/^STRIP () {/p; /^AX_TOK=/,/^grep_lista () {/p" check-axioms.bash)"; grep_lista cuarentena | grep -v librerias-retiradas')
printf '%s' "$o" | grep -q 'ZZ Rotura - copia.lean:1:zz_copia' && ok "e la cuarentena con espacios se lee: $o" || ko "e $o"
rm -f "$F/cuarentena/ZZ Rotura - copia.lean"
restaura; trap - EXIT
cd "$R" && git status --short | head; cd "$F" && git status --short | head; echo "(restaurado)"
