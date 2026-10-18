import ROBINSON_PlusPlus

/-!
# Rosser, el SONDEO de `hasWitF`: la puerta del riesgo (ADR‑147; ADR‑151)

✏️ **2026‑10‑18 (ADR‑160, T66):** pasa de CONTROL a REGISTRO. Lo que mide lo dice ya el build, en general:
`prf_neg_hasWitF` (`Meta/RosserGuardNeg.lean`, ADR‑153) refuta la guarda de fórmula sobre todo numeral cuya guarda es
falsa en ℕ, con su `#pureza`.

**La pregunta** (ADR‑146 §4.4 y §6.1). GuardNeg es la etapa de más riesgo: la guarda de FÓRMULA es `∃∃`, tiene ocho
cláusulas y cruza la de términos, y de refutarla en `Prf` no había nada que compilara (los precedentes,
`CRIT_hasWitF_rejects_tag` y `CRIT_hasWitF_rejects_varc`, están archivados y rotos). ¿Se refuta sobre NUMERALES basura,
a profundidad 1 y 2, y cuánto cuesta?

**Qué dice** (todo sin el modelo, salvo el control):

    Prf (¬ hasWitF ⟨k, r⟩‾)            para todo k ∉ {2,…,9} y todo r      -- profundidad 1: la etiqueta
    Prf (¬ hasWitF ⟨5, ⟨k, r⟩, b⟩‾)     para todo k ∉ {2,…,9}, r y b        -- profundidad 2: una casilla de FÓRMULA
    Prf (¬ hasWitF ⟨4, ⟨k, r⟩, b⟩‾)     para todo k ∉ {0, 1}, r y b         -- profundidad 2: una casilla de TÉRMINO

y el control `control_codigo_no_refutable`: sobre el numeral del código de CUALQUIER fórmula, `¬ hasWitF` no es
demostrable (la solidez en `MNV V₀` y `prf_hasWitF_real`). No mide el método sino la guarda: lo refutado depende de
la basura.

**Cómo.** El `∃∃` se elimina con dos `prf_ex_elim_imp` (§1): basta refutar `isFC1 wF wT c̄` para testigos
CUALESQUIERA. De `c ∈ wF` y `wfAllF` sale `isFormCodeE2` (`prf_isFormCodeE2_of_In`). A profundidad 1, el
fortalecimiento a la forma posicional (`prf_isFormCodeE2_str`) y el rechazo por etiqueta (`crit_isFormCodeB2_rejects`),
con la etiqueta del numeral (`prf_carc_consN`, ADR‑150). A profundidad 2, la cláusula de la etiqueta se ELIGE refutando
las otras siete por la forma (§2), y su casilla se evalúa sobre el numeral (`prf_nthc_numeral`, ADR‑150): si es de
fórmula, otra vez `wfAllF` y la profundidad 1; si es de término, `wfAll1` y el rechazo de término
(`crit_isTermCodeB1_rejects`).

⚠️ Lo que NO dice: la versión hereditaria GENERAL (inducción sobre el numeral, con las ocho cláusulas en cada nivel), la
etiqueta buena con forma mala, la casilla de lista de `atom`, ni el `0` (es la técnica de `RosserBasura` §1).

## Cómo re‑ejecutarlo

    lake lean sondeos/RosserHasWitF.lean      # desde la raíz de RPP
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open FOL ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ChainPrf ROBINSON_PlusPlus.Meta.BoundedInPrf
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs
open ROBINSON_PlusPlus.Meta.ModeloCodigo ROBINSON_PlusPlus.Meta.RosserNumerales

namespace RosserHasWitF

/-! ## §1 · El `∃∃`, eliminado: basta refutar `isFC1` para testigos cualesquiera -/

theorem prf_neg_hasWitF_of (c : Nat) (h : ∀ wF wT : Term, Prf (isFC1 wF wT (numeralM c) ⇒ Formula.bottom)) :
    Prf (neg (hasWitF (numeralM c))) := by
  refine prf_ex_elim_imp ?_
  rw [ROBINSON_PlusPlus.Minimal.Axioms.liftTerm_numeralM, ROBINSON_PlusPlus.Minimal.Axioms.liftTerm_numeralM]
  show PrfH [Formula.ex (isFC1 (.var 1) (.var 0) (numeralM c))] Formula.bottom
  have hB : PrfH [isFC1 (.var 1) (.var 0) (numeralM c)] Formula.bottom :=
    PrfH.mp _ _ _ (prf_to_prfH (h (.var 1) (.var 0)) _) (prfH_hyp_self _)
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_ex_elim_imp (C := Formula.bottom) hB) _) (prfH_hyp_self _)

/-- De `c ∈ wF` y `wfAllF`, la cláusula de `c`: refutarla refuta `isFC1`. -/
theorem prf_isFC1_rejects_of (wF wT X : Term) (hE : Prf (isFormCodeE2 wF wT X ⇒ Formula.bottom)) :
    Prf (isFC1 wF wT X ⇒ Formula.bottom) := by
  refine prf_deduction ?_
  have hh := prfH_hyp_self (isFC1 wF wT X)
  have hwF := PrfH_and_elim_right (PrfH_and_elim_left hh)
  have hin := PrfH_and_elim_right hh
  have hcode := PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (ENS.prf_isFormCodeE2_of_In wF wT X) _) hin) hwF
  exact PrfH.mp _ _ _ (prf_to_prfH hE _) hcode

/-! ## §2 · La forma refuta la etiqueta equivocada, y elige la cláusula de la buena -/

theorem prf_tag_shapeNul {X : Term} {k : Nat} (m : Nat) (hkm : k ≠ m) (hX : Prf (carc X =eq numeralM k)) :
    Prf (shapeNul X m ⇒ Formula.bottom) :=
  impT (ENS.prf_shapeNul_str X m)
    (impT (Prf.incl (Prfᵢ.c3 _ _)) (impT (Prf.incl (Prfᵢ.c2 _ _)) (crit_tag_absurd X k m hkm hX)))

theorem prf_tag_shapeUn {X : Term} {k : Nat} (m : Nat) (hkm : k ≠ m) (hX : Prf (carc X =eq numeralM k)) :
    Prf (shapeUn X m ⇒ Formula.bottom) :=
  impT (ENS.prf_shapeUn_str' X m)
    (impT (Prf.incl (Prfᵢ.c3 _ _)) (impT (Prf.incl (Prfᵢ.c2 _ _)) (crit_tag_absurd X k m hkm hX)))

theorem prf_tag_shapeBin {X : Term} {k : Nat} (m : Nat) (hkm : k ≠ m) (hX : Prf (carc X =eq numeralM k)) :
    Prf (shapeBin X m ⇒ Formula.bottom) :=
  impT (ENS.prf_shapeBin_str' X m)
    (impT (Prf.incl (Prfᵢ.c3 _ _)) (impT (Prf.incl (Prfᵢ.c2 _ _)) (crit_tag_absurd X k m hkm hX)))

/-- Una cláusula `forma ∧ resto` cae si la forma cae. -/
theorem prf_land_rejects {A B : Formula} (hA : Prf (A ⇒ Formula.bottom)) : Prf (Formula.and A B ⇒ Formula.bottom) :=
  impT (Prf.incl (Prfᵢ.c2 _ _)) hA

/-- Con la etiqueta 5, de las ocho cláusulas sólo queda la de `implc`. -/
theorem prf_E2_sel5 (wF wT X : Term) (hX : Prf (carc X =eq numeralM 5)) :
    Prf (isFormCodeE2 wF wT X ⇒ clBin wF X 5) := by
  have efq : Prf (Formula.bottom ⇒ clBin wF X 5) := Prf.incl (Prfᵢ.efq _)
  simp only [isFormCodeE2, lorAll]
  exact prf_or_elim_imp (impT (prf_tag_shapeNul 2 (by decide) hX) efq)
    (prf_or_elim_imp (impT (prf_land_rejects (prf_tag_shapeBin 3 (by decide) hX)) efq)
    (prf_or_elim_imp (impT (prf_land_rejects (prf_tag_shapeBin 4 (by decide) hX)) efq)
    (prf_or_elim_imp (prf_deduction (prfH_hyp_self _))
    (prf_or_elim_imp (impT (prf_land_rejects (prf_tag_shapeUn 6 (by decide) hX)) efq)
    (prf_or_elim_imp (impT (prf_land_rejects (prf_tag_shapeBin 7 (by decide) hX)) efq)
    (prf_or_elim_imp (impT (prf_land_rejects (prf_tag_shapeBin 8 (by decide) hX)) efq)
      (impT (prf_land_rejects (prf_tag_shapeUn 9 (by decide) hX)) efq)))))))

/-- Con la etiqueta 4, sólo queda la de `eqc`. -/
theorem prf_E2_sel4 (wF wT X : Term) (hX : Prf (carc X =eq numeralM 4)) :
    Prf (isFormCodeE2 wF wT X ⇒ clEq wT X) := by
  have efq : Prf (Formula.bottom ⇒ clEq wT X) := Prf.incl (Prfᵢ.efq _)
  simp only [isFormCodeE2, lorAll]
  exact prf_or_elim_imp (impT (prf_tag_shapeNul 2 (by decide) hX) efq)
    (prf_or_elim_imp (impT (prf_land_rejects (prf_tag_shapeBin 3 (by decide) hX)) efq)
    (prf_or_elim_imp (prf_deduction (prfH_hyp_self _))
    (prf_or_elim_imp (impT (prf_land_rejects (prf_tag_shapeBin 5 (by decide) hX)) efq)
    (prf_or_elim_imp (impT (prf_land_rejects (prf_tag_shapeUn 6 (by decide) hX)) efq)
    (prf_or_elim_imp (impT (prf_land_rejects (prf_tag_shapeBin 7 (by decide) hX)) efq)
    (prf_or_elim_imp (impT (prf_land_rejects (prf_tag_shapeBin 8 (by decide) hX)) efq)
      (impT (prf_land_rejects (prf_tag_shapeUn 9 (by decide) hX)) efq)))))))

/-- La casilla 1 de `⟨j, a, b⟩‾`, evaluada sobre el numeral. -/
theorem prf_nthc1_triple (j a b : Nat) :
    Prf (nthc (numeralM (consN j (consN a (consN b 0)))) (numeralM 1) =eq numeralM a) := by
  have h := prf_nthc_numeral 1 (consN j (consN a (consN b 0)))
    (by rw [lenN_consN, lenN_consN, lenN_consN, lenN_zero]; omega)
  rw [nthN_cs, nthN_cz] at h
  exact h

/-! ## §3 · Profundidad 1: una etiqueta que no es de fórmula -/

theorem prf_E2_rejects_tag (wF wT X : Term) (k : Nat) (h2 : k ≠ 2) (h3 : k ≠ 3) (h4 : k ≠ 4) (h5 : k ≠ 5)
    (h6 : k ≠ 6) (h7 : k ≠ 7) (h8 : k ≠ 8) (h9 : k ≠ 9) (hX : Prf (carc X =eq numeralM k)) :
    Prf (isFormCodeE2 wF wT X ⇒ Formula.bottom) :=
  impT (ENS.prf_isFormCodeE2_str wF wT X) (crit_isFormCodeB2_rejects wF wT X k h2 h3 h4 h5 h6 h7 h8 h9 hX)

/-- 🏁 **Profundidad 1**: para TODO `k ∉ {2,…,9}` y todo `r`, `Prf (¬ hasWitF ⟨k, r⟩‾)`. -/
theorem prf_neg_hasWitF_num (k r : Nat) (h2 : k ≠ 2) (h3 : k ≠ 3) (h4 : k ≠ 4) (h5 : k ≠ 5)
    (h6 : k ≠ 6) (h7 : k ≠ 7) (h8 : k ≠ 8) (h9 : k ≠ 9) :
    Prf (neg (hasWitF (numeralM (consN k r)))) :=
  prf_neg_hasWitF_of _ fun wF wT => prf_isFC1_rejects_of wF wT _
    (prf_E2_rejects_tag wF wT _ k h2 h3 h4 h5 h6 h7 h8 h9 (prf_carc_consN k r))

/-! ## §4 · Profundidad 2: la basura en una casilla de FÓRMULA, y en una de TÉRMINO -/

theorem prf_isFC1_rejects_impl (wF wT : Term) (k r b : Nat) (h2 : k ≠ 2) (h3 : k ≠ 3) (h4 : k ≠ 4) (h5 : k ≠ 5)
    (h6 : k ≠ 6) (h7 : k ≠ 7) (h8 : k ≠ 8) (h9 : k ≠ 9) :
    Prf (isFC1 wF wT (numeralM (consN 5 (consN (consN k r) (consN b 0)))) ⇒ Formula.bottom) := by
  refine prf_deduction ?_
  have hh := prfH_hyp_self (isFC1 wF wT (numeralM (consN 5 (consN (consN k r) (consN b 0)))))
  have hwF := PrfH_and_elim_right (PrfH_and_elim_left hh)
  have hin := PrfH_and_elim_right hh
  have hE := PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (ENS.prf_isFormCodeE2_of_In wF wT _) _) hin) hwF
  have hsel := PrfH.mp _ _ _ (prf_to_prfH (prf_E2_sel5 wF wT _ (prf_carc_consN 5 _)) _) hE
  have hin1 := PrfH_congr_In_left (prf_to_prfH (prf_nthc1_triple 5 (consN k r) b) _)
    (PrfH_and_elim_left (PrfH_and_elim_right hsel))
  have hEa := PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (ENS.prf_isFormCodeE2_of_In wF wT _) _) hin1) hwF
  exact PrfH.mp _ _ _
    (prf_to_prfH (prf_E2_rejects_tag wF wT _ k h2 h3 h4 h5 h6 h7 h8 h9 (prf_carc_consN k r)) _) hEa

/-- 🏁 **Profundidad 2, casilla de FÓRMULA**: `Prf (¬ hasWitF ⟨5, ⟨k, r⟩, b⟩‾)`, la implicación con un antecedente
    que no es código de fórmula. -/
theorem prf_neg_hasWitF_impl (k r b : Nat) (h2 : k ≠ 2) (h3 : k ≠ 3) (h4 : k ≠ 4) (h5 : k ≠ 5)
    (h6 : k ≠ 6) (h7 : k ≠ 7) (h8 : k ≠ 8) (h9 : k ≠ 9) :
    Prf (neg (hasWitF (numeralM (consN 5 (consN (consN k r) (consN b 0)))))) :=
  prf_neg_hasWitF_of _ fun wF wT => prf_isFC1_rejects_impl wF wT k r b h2 h3 h4 h5 h6 h7 h8 h9

theorem prf_isFC1_rejects_eq (wF wT : Term) (k r b : Nat) (h0 : k ≠ 0) (h1 : k ≠ 1) :
    Prf (isFC1 wF wT (numeralM (consN 4 (consN (consN k r) (consN b 0)))) ⇒ Formula.bottom) := by
  refine prf_deduction ?_
  have hh := prfH_hyp_self (isFC1 wF wT (numeralM (consN 4 (consN (consN k r) (consN b 0)))))
  have hwT := PrfH_and_elim_left (PrfH_and_elim_left hh)
  have hwF := PrfH_and_elim_right (PrfH_and_elim_left hh)
  have hin := PrfH_and_elim_right hh
  have hE := PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (ENS.prf_isFormCodeE2_of_In wF wT _) _) hin) hwF
  have hsel := PrfH.mp _ _ _ (prf_to_prfH (prf_E2_sel4 wF wT _ (prf_carc_consN 4 _)) _) hE
  have hin1 := PrfH_congr_In_left (prf_to_prfH (prf_nthc1_triple 4 (consN k r) b) _)
    (PrfH_and_elim_left (PrfH_and_elim_right hsel))
  have hE1 := PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (prf_isTermCodeE1_of_In wT _) _) hin1) hwT
  exact PrfH.mp _ _ _ (prf_to_prfH (impT (prf_isTermCodeE1_str wT _)
    (crit_isTermCodeB1_rejects wT _ k h0 h1 (prf_carc_consN k r))) _) hE1

/-- 🏁 **Profundidad 2, casilla de TÉRMINO**: `Prf (¬ hasWitF ⟨4, ⟨k, r⟩, b⟩‾)`, una igualdad cuyo primer miembro no
    es código de término: la guarda de fórmula pasa por la de términos. -/
theorem prf_neg_hasWitF_eq (k r b : Nat) (h0 : k ≠ 0) (h1 : k ≠ 1) :
    Prf (neg (hasWitF (numeralM (consN 4 (consN (consN k r) (consN b 0)))))) :=
  prf_neg_hasWitF_of _ fun wF wT => prf_isFC1_rejects_eq wF wT k r b h0 h1

/-! ## §5 · Control: sobre el código de una fórmula, `¬ hasWitF` no es demostrable

Por la solidez (`prf_sound`) y la guarda que ya se demostraba (`prf_hasWitF_real`). Lo refutado en §3–§4 depende, pues,
de la basura. Sólo códigos de verdad. -/

theorem control_codigo_no_refutable (φ : Formula) : ¬ Prf (neg (hasWitF (numeralM (codeNat φ)))) := by
  intro h
  have hs := ROBINSON_PlusPlus.Meta.SolidezPrf.prf_sound ROBINSON_PlusPlus.Meta.Consistencia.estandar_MN h (fun _ => 0)
  have hw := ROBINSON_PlusPlus.Meta.SolidezPrf.prf_sound ROBINSON_PlusPlus.Meta.Consistencia.estandar_MN
    (ROBINSON_PlusPlus.Meta.CodeWitnessPrf.HW.prf_hasWitF_real φ) (fun _ => 0)
  apply hs
  rw [ROBINSON_PlusPlus.Meta.ModeloEstandar.ev_hasWitF, ROBINSON_PlusPlus.Meta.ModeloEstandar.ev_numeralM]
  rw [ROBINSON_PlusPlus.Meta.ModeloEstandar.ev_hasWitF, ROBINSON_PlusPlus.Meta.ModeloEstandar.ev_formCodeM] at hw
  exact hw

end RosserHasWitF

#print axioms RosserHasWitF.prf_neg_hasWitF_num
#print axioms RosserHasWitF.prf_neg_hasWitF_impl
#print axioms RosserHasWitF.prf_neg_hasWitF_eq
#print axioms RosserHasWitF.control_codigo_no_refutable

/-! T08: las tres refutaciones no nombran la semántica; el control, sí. -/
#pureza RosserHasWitF.prf_neg_hasWitF_num RosserHasWitF.prf_neg_hasWitF_impl RosserHasWitF.prf_neg_hasWitF_eq
  | RosserHasWitF.control_codigo_no_refutable
