/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.SolidezVerificadorModelo
import ROBINSON_PlusPlus.Meta.TarskiPrf
import ROBINSON_PlusPlus.Meta.GodelCorolarios

/-!
# `Meta/TitularesIII.lean` — los titulares de la clase (iii): usan la verdad en el modelo (C7.iii; ADR‑268)

Las capas de ADR‑266: todos los titulares en C7, separados por clase. Aquí, por ahora, los de
`Meta/SolidezVerificador.lean` —`goedel_I_neg` (`⊬ ¬G`), `godelCN_indecidible`, `godelCN_verdadera` y
`con_verdadera`, con sus dos lemas `gg_godelCN` y `clas_godelCN`—, los dos de Tarski semántico (de
`Meta/TarskiPrf.lean`) y `con_indecidible` (de `Meta/GodelCorolarios.lean`). Vendrán en el paso 4 de ADR‑266 los de
`Meta/RigidezEstandar.lean`, `Meta/ProvFiel.lean` y `Meta/PuenteFOL.lean`. Mismos enunciados y pruebas; el espacio de
nombres es el de este fichero (NAMING‑CONVENTIONS §6).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ROBINSON_PlusPlus.Meta.TitularesIII

section SolidezVerificador
open FOL FOL.Metamath.Semantics ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ModeloCodigo ROBINSON_PlusPlus.Meta.CodeNatInjPrf
open ROBINSON_PlusPlus.Meta.ModeloEstandar ROBINSON_PlusPlus.Meta.ModeloCodificacion
open ROBINSON_PlusPlus.Meta.SolidezVerificador ROBINSON_PlusPlus.Meta.SolidezVerificadorModelo

open ROBINSON_PlusPlus.Meta.SolidezDobleNegacion in
/-- `G`, LEÍDA POR `gg`, vale en todo modelo de la lectura doble‑negada en el que lo que se cree demostrable lo es
    (W1): el punto fijo, leído por `gg`, dice `gg G ⇔ ¬ gg Prov(⌜G⌝)`; y `gg Prov(⌜G⌝)` daría `¬¬ Prf G` (por `N`: la
    matriz de `Prov` no tiene cuantificadores ni disyunciones), que `goedel_I` refuta. Sin lógica clásica (ADR‑191). -/
theorem gg_godelCN {M : Model Nat} (hM : EstandarDN M)
    (hW1 : ∀ v, evalFormula M v (ROBINSON_PlusPlus.Meta.ProofChain.provCodeC' ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN) →
      Prf ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN)
    (v : Nat → Nat) : evalFormula M v (gg ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN) := by
  have hfp := prf_sound_dn hM ROBINSON_PlusPlus.Meta.GodelTwoPrf.prf_godelCN_fixedpoint v
  have hN : (clas Dnada (ROBINSON_PlusPlus.Meta.ProofChain.provCodeC'
      ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN)).2.1 = true := by
    rw [ROBINSON_PlusPlus.Meta.ProofChain.provCodeC', clas_subst]; rfl
  exact hfp.2 (fun hP => (transfer Dnada decNada _ v).2.1 hN hP
    (fun hp => ROBINSON_PlusPlus.Meta.Consistencia.goedel_I (hW1 v hp)))

open ROBINSON_PlusPlus.Meta.SolidezDobleNegacion in
/-- La polaridad de `G` admite `S`: `G` es `¬Prov(…)`, y la matriz de `Prov` no pide nada. La de `godelPred'`, por
    `clas_subst` dos veces: el numeral de `selfAppN` no se mira. -/
theorem clas_godelCN : (clas Dnada ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN).2.2 = true := by
  rw [ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN, ROBINSON_PlusPlus.Meta.DiagonalNumeral.selfAppN, clas_subst,
    ROBINSON_PlusPlus.Meta.DiagonalTwo.godelBeta', clas_subst]
  rfl

/-- 🏁🏁 **GÖDEL I, la mitad `⊬ ¬G`**, sin hipótesis: con `Prf ¬G`, la solidez doble‑negada en `MNV V₀` daría
    `¬ gg G`, y `gg G` vale (`gg_godelCN`, con W1 y `goedel_I`). Desde ADR‑191 sin lógica clásica: ya no hay
    `Classical.byContradiction` (sacar `Prov(⌜G⌝)` de su doble negación era Markov). -/
theorem goedel_I_neg : ¬ Prf (neg ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN) := fun hn =>
  ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.prf_sound_dn ROBINSON_PlusPlus.Meta.Consistencia.estandarDN_MN hn
    (fun _ => 0) (gg_godelCN ROBINSON_PlusPlus.Meta.Consistencia.estandarDN_MN (fun v hp => prf_of_prov _ v hp) _)

/-- 🏁🏁 **`G` es INDECIDIBLE en `Prf`**: ni `G` (`goedel_I`) ni `¬G` (`goedel_I_neg`). -/
theorem godelCN_indecidible : And (¬ Prf ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN)
    (¬ Prf (neg ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN)) :=
  ⟨ROBINSON_PlusPlus.Meta.Consistencia.goedel_I, goedel_I_neg⟩

/-! ## §6 · E10: `G` y `Con` son VERDADERAS en `MNV V₀`, el modelo estándar construido (y en todo modelo estándar:
`Meta/RigidezEstandar.lean`, ADR‑173; los modelos estándar no son uno solo, `Meta/SegundoModelo.lean`, ADR‑175)

Lo que dicen —«no soy demostrable», «`⊥` no es demostrable»— es cierto en `MNV V₀`: si el modelo creyera lo
contrario, `prf_of_prov` daría `Prf G` o `Prf ⊥`, y `goedel_I`/`consistencia` lo impiden. -/

/-- 🏁 **`G` es VERDADERA en `MNV V₀`** (y no demostrable: `goedel_I`): `gg G` vale (`gg_godelCN`), y `G` tiene `S`
    (`clas_godelCN`), así que vale también en la lectura clásica. Sin lógica clásica (ADR‑191). -/
theorem godelCN_verdadera (v : Nat → Nat) :
    evalFormula (MNV V₀) v ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN :=
  (ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.transfer ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.Dnada
    ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.decNada _ v).2.2 clas_godelCN
    (gg_godelCN ROBINSON_PlusPlus.Meta.Consistencia.estandarDN_MN (fun v' hp => prf_of_prov _ v' hp) v)

/-- 🏁 **`Con` es VERDADERA en `MNV V₀`** (y no demostrable: `goedel_II`). -/
theorem con_verdadera (v : Nat → Nat) :
    evalFormula (MNV V₀) v ROBINSON_PlusPlus.Meta.GodelTwo.consistencyFormula' :=
  fun hp => ROBINSON_PlusPlus.Meta.Consistencia.consistencia (prf_of_prov _ _ hp)

end SolidezVerificador

section Tarski
open FOL ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.HilbertDeduction ROBINSON_PlusPlus.Meta.Diagonal
open ROBINSON_PlusPlus.Meta.DiagonalNumeral ROBINSON_PlusPlus.Meta.GodelTwoPrf ROBINSON_PlusPlus.Meta.Sentencia
open ROBINSON_PlusPlus.Meta.TarskiPrf

/-! ## §7 · TARSKI SEMÁNTICO: en TODO modelo estándar, y en `MNV V₀`

Si `Tr(⌜L⌝)` y `L` valieran a la vez en el modelo, como el modelo satisface `L ⇔ ¬Tr(⌜L⌝)`, `Tr(⌜L⌝)` valdría y no
valdría. Vale en todo `M` con `Estandar M` (T75a, ADR‑175); `tarski_semantico` es la instancia en `MNV V₀`
(`estandar_MN`), que es también el control de que la hipótesis no es vacía.

✏️ *(ADR‑191)*: hasta ADR‑190, `L ⇔ ¬Tr(⌜L⌝)` se leía en el modelo por la solidez en `Prop` (`prf_sound`), que lleva la
lógica clásica (`p3`). Con `Tr` arbitraria eso no se puede leer de otro modo; lo que se lee ahora es UNA IGUALDAD, la del
término diagonal (`prf_diag_arith_num`): por la solidez doble‑negada vale en `M`, porque en `Nat` la igualdad es
decidible (`eq_de_prf`). Con ella, `L` es literalmente `¬Tr(t)` con `t` del mismo valor que `⌜L⌝`, y el resto es
lógica intuicionista. -/
open FOL.Metamath.Semantics in
/-- 🏁 Ninguna `Tr` define la verdad en un modelo estándar CUALQUIERA: falla en su mentiroso, para toda asignación. -/
theorem tarski_semantico_de {M : Model Nat} (hM : ROBINSON_PlusPlus.Meta.SolidezPrf.Estandar M) (Tr : Formula)
    (v : Nat → Nat) :
    ¬ (evalFormula M v (substFormula 0 (numeral (codeNat (liar Tr))) Tr) ↔ evalFormula M v (liar Tr)) := by
  intro h1
  -- el término diagonal vale lo que el numeral del mentiroso: una igualdad que `Prf` demuestra
  have he : evalTerm M v (substTerm 0 (numeral (codeNat (diagBeta (neg Tr)))) diagTerm) =
      evalTerm M v (numeral (codeNat (liar Tr))) :=
    ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.eq_de_prf
      (ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.estandarDN_de hM) (prf_diag_arith_num (diagBeta (neg Tr))) v
  -- `L` ES `¬ Tr(t)`, con `t` el término diagonal
  have hL : liar Tr = neg (substFormula 0 (substTerm 0 (numeral (codeNat (diagBeta (neg Tr)))) diagTerm) Tr) := by
    unfold liar selfAppN
    rw [diagBeta_comp, substFormula_neg]
  -- luego `L ↔ ¬ Tr(⌜L⌝)` en `M`, por el valor del término
  have hLT : evalFormula M v (liar Tr) ↔ ¬ evalFormula M v (substFormula 0 (numeral (codeNat (liar Tr))) Tr) := by
    have h2 : evalFormula M v (liar Tr) ↔
        ¬ evalFormula M v (substFormula 0 (substTerm 0 (numeral (codeNat (diagBeta (neg Tr)))) diagTerm) Tr) := by
      rw [hL]; exact Iff.rfl
    rw [h2, eval_substFormula_zero, eval_substFormula_zero M v (numeral (codeNat (liar Tr))), he]
  have hnT : ¬ evalFormula M v (substFormula 0 (numeral (codeNat (liar Tr))) Tr) := fun hT => hLT.mp (h1.mp hT) hT
  exact hnT (h1.mpr (hLT.mpr hnT))

open FOL.Metamath.Semantics in
/-- 🏁 Ninguna `Tr` define la verdad en `MNV V₀`: la instancia de `tarski_semantico_de` en `estandar_MN`. -/
theorem tarski_semantico (Tr : Formula) (v : Nat → Nat) :
    ¬ (evalFormula (ROBINSON_PlusPlus.Meta.ModeloEstandar.MNV ROBINSON_PlusPlus.Meta.ModeloCodigo.V₀) v
          (substFormula 0 (numeral (codeNat (liar Tr))) Tr) ↔
        evalFormula (ROBINSON_PlusPlus.Meta.ModeloEstandar.MNV ROBINSON_PlusPlus.Meta.ModeloCodigo.V₀) v
          (liar Tr)) :=
  tarski_semantico_de ROBINSON_PlusPlus.Meta.Consistencia.estandar_MN Tr v

end Tarski

section Corolarios
open FOL ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ProofChain ROBINSON_PlusPlus.Meta.DiagonalNumeral
open ROBINSON_PlusPlus.Meta.GodelTwo ROBINSON_PlusPlus.Meta.GodelTwoPrf ROBINSON_PlusPlus.Meta.DerivCondPrf
open ROBINSON_PlusPlus.Meta.Representability2Prf ROBINSON_PlusPlus.Meta.PremsBdAllPrf
open ROBINSON_PlusPlus.Meta.GodelCorolarios

/-- 🏁 **`Con'` es INDECIDIBLE**: `goedel_II`, y `¬ Prf ¬Con'` porque `Con'` es verdadera en `MNV V₀` y `Prf` es
    sólida. Clase (iii): la consistencia sola no basta (T+¬Con es consistente y demuestra ¬Con'). Desde ADR‑191, por la
    solidez doble‑negada: `Con'` es `¬Prov(⌜⊥⌝)`, tiene `P`, y lo verdadero con `P` no se refuta (`no_refuta`). -/
theorem con_indecidible : And (¬ Prf consistencyFormula') (¬ Prf (neg consistencyFormula')) := by
  refine ⟨ROBINSON_PlusPlus.Meta.Consistencia.goedel_II, ?_⟩
  have e : ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.clas ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.Dnada
      (ROBINSON_PlusPlus.Meta.ProofChain.provCodeC' Formula.bottom) =
      ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.clas ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.Dnada
        ROBINSON_PlusPlus.Meta.ProofChain.provFormulaC' := by
    rw [ROBINSON_PlusPlus.Meta.ProofChain.provCodeC', ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.clas_subst]
  have hP : (ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.clas ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.Dnada
      consistencyFormula').1 = true := by
    rw [consistencyFormula', neg]
    simp only [ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.clas, e]
    rfl
  exact ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.no_refuta ROBINSON_PlusPlus.Meta.Consistencia.estandarDN_MN
    ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.Dnada ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.decNada hP
    (fun _ => 0) (ROBINSON_PlusPlus.Meta.TitularesIII.con_verdadera (fun _ => 0))

end Corolarios

end ROBINSON_PlusPlus.Meta.TitularesIII

#print axioms ROBINSON_PlusPlus.Meta.TitularesIII.goedel_I_neg
#print axioms ROBINSON_PlusPlus.Meta.TitularesIII.godelCN_indecidible
#print axioms ROBINSON_PlusPlus.Meta.TitularesIII.godelCN_verdadera
#print axioms ROBINSON_PlusPlus.Meta.TitularesIII.con_verdadera
#print axioms ROBINSON_PlusPlus.Meta.TitularesIII.tarski_semantico_de
#print axioms ROBINSON_PlusPlus.Meta.TitularesIII.tarski_semantico
#print axioms ROBINSON_PlusPlus.Meta.TitularesIII.con_indecidible
