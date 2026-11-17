/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.SolidezVerificadorModelo
import ROBINSON_PlusPlus.Meta.TarskiPrf
import ROBINSON_PlusPlus.Meta.GodelCorolarios
import ROBINSON_PlusPlus.Meta.TitularesII
import ROBINSON_PlusPlus.Meta.ProvFiel

/-!
# `Meta/TitularesIII.lean` — los titulares de la clase (iii): usan la verdad en el modelo (C7.iii; ADR‑268)

Las capas de ADR‑266: todos los titulares en C7, separados por clase. Aquí, los DIECISÉIS de la clase (iii). Desde
ADR‑268, los de `Meta/SolidezVerificador.lean` —`goedel_I_neg` (`⊬ ¬G`), `godelCN_indecidible`, `godelCN_verdadera`
y `con_verdadera`, con sus dos lemas `gg_godelCN` y `clas_godelCN`—, los dos de Tarski semántico (de
`Meta/TarskiPrf.lean`) y `con_indecidible` (de `Meta/GodelCorolarios.lean`). Desde ADR‑269, los tres de
`Meta/RigidezEstandar.lean` (`prf_of_prov_de`, y E10 en todo modelo estándar: `godelCN_verdadera_de` y
`con_verdadera_de`), los dos de `Meta/ProvFiel.lean` (`modelo_prov_iff` y `modelo_prov_iff_de`) y los cuatro de la
clase (iii) de `Meta/PuenteFOL.lean` (`prf_completo`, `goedel_I_neg_fol`, `modelo_sin_G` y `goedel_I_semantico`).
Mismos enunciados y pruebas; el espacio de nombres es el de este fichero (NAMING‑CONVENTIONS §6).
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
    (fun hp => ROBINSON_PlusPlus.Meta.TitularesII.goedel_I (hW1 v hp)))

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
  ⟨ROBINSON_PlusPlus.Meta.TitularesII.goedel_I, goedel_I_neg⟩

/-! ## §6 · E10: `G` y `Con` son VERDADERAS en `MNV V₀`, el modelo estándar construido (y en todo modelo estándar:
más abajo, con la maquinaria de `Meta/RigidezEstandar.lean`, ADR‑173; los modelos estándar no son uno solo, `Meta/SegundoModelo.lean`, ADR‑175)

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
  refine ⟨ROBINSON_PlusPlus.Meta.TitularesII.goedel_II, ?_⟩
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

section RigidezEstandar
open FOL FOL.Metamath.Semantics
open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.ModeloCodigo ROBINSON_PlusPlus.Meta.SolidezPrf
open ROBINSON_PlusPlus.Meta.RigidezEstandar

variable {M : Model Nat}

/-- 🏁 **Lo que un modelo estándar CUALQUIERA cree demostrable, lo es.** -/
theorem prf_of_prov_de (hM : Estandar M) (φ : Formula) (v : Nat → Nat) :
    evalFormula M v (ROBINSON_PlusPlus.Meta.ProofChain.provCodeC' φ) → Prf φ := by
  intro hp
  obtain ⟨p, hc, hm⟩ := M_provCodeC' hM φ v hp
  obtain ⟨hch, hrun⟩ := M_cadena hM p 0 hc
  rw [hrun] at hm
  rw [M_axiomsCodeT hM] at hch
  have h := ROBINSON_PlusPlus.Meta.SolidezVerificador.cadena_buena
    ROBINSON_PlusPlus.Meta.SolidezVerificador.bueno_codeNatList (decodeL p) 0
    ROBINSON_PlusPlus.Meta.SolidezVerificador.bueno_zero hch (codeNat φ) hm
  rwa [ROBINSON_PlusPlus.Meta.SolidezVerificador.dec_codeNat] at h

/-- 🏁 **E10: `G` es VERDADERA en todo modelo estándar**: `gg G` vale (`gg_godelCN`, con `prf_of_prov_de`) y `G`
    tiene `S` (`clas_godelCN`). Sin lógica clásica (ADR‑191). -/
theorem godelCN_verdadera_de (hM : Estandar M) (v : Nat → Nat) :
    evalFormula M v ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN :=
  (ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.transfer ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.Dnada
    ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.decNada _ v).2.2
    ROBINSON_PlusPlus.Meta.TitularesIII.clas_godelCN
    (ROBINSON_PlusPlus.Meta.TitularesIII.gg_godelCN
      (ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.estandarDN_de hM) (fun v' hp => prf_of_prov_de hM _ v' hp) v)

/-- 🏁 **E10: `Con` es VERDADERA en todo modelo estándar.** -/
theorem con_verdadera_de (hM : Estandar M) (v : Nat → Nat) :
    evalFormula M v ROBINSON_PlusPlus.Meta.GodelTwo.consistencyFormula' :=
  fun hp => ROBINSON_PlusPlus.Meta.Consistencia.consistencia (prf_of_prov_de hM _ _ hp)

end RigidezEstandar

section ProvFiel
open FOL FOL.Metamath.Semantics ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ModeloCodigo ROBINSON_PlusPlus.Meta.ModeloEstandar
open ROBINSON_PlusPlus.Meta.SolidezDobleNegacion
open ROBINSON_PlusPlus.Meta.RosserW1 ROBINSON_PlusPlus.Meta.RosserPosNum ROBINSON_PlusPlus.Meta.RosserNegNum
open ROBINSON_PlusPlus.Meta.SolidezPrf ROBINSON_PlusPlus.Meta.RigidezEstandar
open ROBINSON_PlusPlus.Meta.ProvFiel (prov_de_proofN)

variable {M : Model Nat}

/-- 🏁 **`Prov` es FIEL en `MNV V₀`**, el modelo estándar construido: `MNV V₀ ⊨ Prov(⌜φ⌝)` exactamente cuando `φ` es
    teorema (en TODO modelo estándar: `modelo_prov_iff_de`). La ida es W1 (`prf_of_prov`); la vuelta, desde ADR‑191, el
    testigo de `proofN_of_prf`: sin lógica clásica. Es también el control de vacuidad de W1: su hipótesis se cumple para
    cada teorema. (Hasta ADR‑191 vivía en `Meta/SolidezVerificador.lean`, y su vuelta era D1 leído por `prf_sound`; hasta
    ADR‑269, en `Meta/ProvFiel.lean`, con el nombre de `SolidezVerificador`.) -/
theorem modelo_prov_iff (φ : Formula) (v : Nat → Nat) :
    evalFormula (MNV ROBINSON_PlusPlus.Meta.ModeloCodigo.V₀) v (ROBINSON_PlusPlus.Meta.ProofChain.provCodeC' φ) ↔
      Prf φ :=
  ⟨ROBINSON_PlusPlus.Meta.SolidezVerificadorModelo.prf_of_prov φ v, fun h => by
    obtain ⟨m, hm⟩ := ROBINSON_PlusPlus.Meta.ProvFiel.proofN_of_prf h
    exact prov_de_proofN hm v⟩


/-- 🏁 **`Prov` es FIEL en todo modelo estándar.** La ida, `prf_of_prov_de` (W1 en `M`); la vuelta, desde ADR‑191, el
    testigo de `proofN_of_prf`, que `M` cree (`M_cadena_de`): sin lógica clásica. (Hasta ADR‑191 vivía en
    `Meta/RigidezEstandar.lean`, y su vuelta era D1 leído por `prf_sound`; hasta ADR‑269, en `Meta/ProvFiel.lean`,
    con el nombre de `RigidezEstandar`.) -/
theorem modelo_prov_iff_de (hM : Estandar M) (φ : Formula) (v : Nat → Nat) :
    evalFormula M v (ROBINSON_PlusPlus.Meta.ProofChain.provCodeC' φ) ↔ Prf φ := by
  refine ⟨prf_of_prov_de hM φ v, fun h => ?_⟩
  obtain ⟨m, hc, hy⟩ := ROBINSON_PlusPlus.Meta.ProvFiel.proofN_of_prf h
  have hc' : chainOkN (M.func sym!"axiomsCodeT" []) 0 m := by rw [M_axiomsCodeT hM]; exact hc
  have hch := ROBINSON_PlusPlus.Meta.ProvFiel.M_cadena_de hM m 0 hc'
  have hrun := (M_cadena hM m 0 hch).2
  rw [ROBINSON_PlusPlus.Meta.ProofChain.provCodeC', eval_substFormula_zero,
    ← ROBINSON_PlusPlus.Meta.Representability.formCodeM_eq, M_formCodeM hM]
  simp only [ROBINSON_PlusPlus.Meta.ProofChain.provFormulaC', land, chainOk, In, runFn, nil, zero,
    evalFormula, evalTerm, evalTerms, shiftEnv, hM.hzero, M_mem hM]
  exact ⟨m, hch, by rw [hrun]; exact hy⟩

end ProvFiel

section PuenteFOL
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open FOL.Metamath.Semantics FOL.Henkin0
open ROBINSON_PlusPlus.Meta.PuenteFOL
open ROBINSON_PlusPlus.Meta.TitularesII (goedel_I_fol)

/-- 🏁 **`Prf` es COMPLETO** para su teoría, en el sentido de libro: lo que vale en todo modelo de `AxiomasT` —en
    TODA valuación—, `Prf` lo demuestra. Por la existencia de modelo de FOL sobre las clausuras de `AxiomasT` y
    `axiomasT_global`. ✏️ 2026‑11‑03 (ADR‑253): la hipótesis era la de UNA valuación (la semántica de FOL), más fuerte;
    ésta es más débil y da un teorema más fuerte, del que aquél es un corolario (el `example` de abajo). Titular desde
    ADR‑250, con el `Classical.choice` de la completitud de FOL. -/
theorem prf_completo {f : Formula}
    (h : ∀ (D : Type) (M : Model D), (∀ φ, AxiomasT φ → ∀ w, evalFormula M w φ) → ∀ w, evalFormula M w f) :
    Prf f := by
  refine Classical.byContradiction (fun hn => ?_)
  have hc : ¬ DerivesSet₀ ClausurasT f := fun hd => hn (prf_iff_derivesSet_clausuras.mpr hd)
  obtain ⟨D, M, v, hM⟩ := FOL.Canonical0.model_existence_lemma₀ (consistente_de hc)
  exact hM (neg f) (Or.inr rfl) (h D M (axiomasT_global (fun σ hσ => hM σ (Or.inl hσ))) v)

-- La forma de una sola valuación, la de antes de ADR‑253, es un corolario.
example {f : Formula}
    (h : ∀ (D : Type) (M : Model D) (v : Nat → D), (∀ φ, AxiomasT φ → evalFormula M v φ) → evalFormula M v f) :
    Prf f :=
  prf_completo (fun D M hM w => h D M w (fun φ hφ => hM φ hφ w))

/-- 🏁 Y tampoco `¬G` (titular, ADR‑210): con `goedel_I_fol`, todo conjunto de teoremas de `Prf` es INCOMPLETO en
    FOL. -/
theorem goedel_I_neg_fol {S : Formula → Prop} (hS : ∀ φ, S φ → Prf φ) :
    ¬ DerivesSet₀ S (neg ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN) :=
  fun h => ROBINSON_PlusPlus.Meta.TitularesIII.goedel_I_neg (prf_of_derivesSet hS h)

/-- 🏁 **Un modelo de `T_Prf` en el que `G` es FALSA**: satisface todos los teoremas de `Prf` en TODA valuación, y `G`
    en ninguna. Por la existencia de modelo de FOL sobre los teoremas de `Prf` y `¬G`, consistentes por `goedel_I` y el
    puente; de su valuación a todas, por las clausuras (`eval_forallN_toda`), y `G`, que es una sentencia, no depende
    de ella. ✏️ 2026‑11‑03 (ADR‑253): decía «en una valuación». Titular desde ADR‑250. -/
theorem modelo_sin_G : ∃ (D : Type) (M : Model D),
    And (∀ φ, Prf φ → ∀ w, evalFormula M w φ)
      (∀ w, ¬ evalFormula M w ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN) := by
  have hc : ¬ DerivesSet₀ (fun g => Prf g) ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN :=
    goedel_I_fol (fun _ h => h)
  obtain ⟨D, M, v, hM⟩ := FOL.Canonical0.model_existence_lemma₀ (consistente_de hc)
  refine ⟨D, M, fun φ hφ w => ?_, fun w hw => ?_⟩
  · exact eval_forallN_toda M (existe_cota φ) (hM _ (Or.inl (prf_forallN φ hφ _))) w
  · have hs : FOL.Sentence.IsSentence ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN :=
      (FOL.Sentence.isSentence_iff_lift _).mpr ROBINSON_PlusPlus.Meta.Sentencia.godelCN_isSentence
    exact hM (neg _) (Or.inr rfl) ((FOL.Sentence.eval_sentence M hs w v).mp hw)

/-- 🏁 **GÖDEL I SEMÁNTICO**: `G` es verdadera en todo modelo estándar (`godelCN_verdadera_de`) y falsa, en TODA
    valuación, en un modelo de `T_Prf` (`modelo_sin_G`). Junta los dos hechos; que ese modelo no sea estándar es su
    lectura, no parte del enunciado (los modelos estándar son sobre ℕ). ✏️ 2026‑11‑03 (ADR‑253): el modelo, en toda
    valuación. Titular desde ADR‑250. -/
theorem goedel_I_semantico :
    And (∀ (M : Model Nat), ROBINSON_PlusPlus.Meta.SolidezPrf.Estandar M →
          ∀ v, evalFormula M v ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN)
      (∃ (D : Type) (M : Model D),
          And (∀ φ, Prf φ → ∀ w, evalFormula M w φ)
            (∀ w, ¬ evalFormula M w ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN)) :=
  ⟨fun _ hM v => ROBINSON_PlusPlus.Meta.TitularesIII.godelCN_verdadera_de hM v, modelo_sin_G⟩

end PuenteFOL

end ROBINSON_PlusPlus.Meta.TitularesIII

#print axioms ROBINSON_PlusPlus.Meta.TitularesIII.goedel_I_neg
#print axioms ROBINSON_PlusPlus.Meta.TitularesIII.godelCN_indecidible
#print axioms ROBINSON_PlusPlus.Meta.TitularesIII.godelCN_verdadera
#print axioms ROBINSON_PlusPlus.Meta.TitularesIII.con_verdadera
#print axioms ROBINSON_PlusPlus.Meta.TitularesIII.tarski_semantico_de
#print axioms ROBINSON_PlusPlus.Meta.TitularesIII.tarski_semantico
#print axioms ROBINSON_PlusPlus.Meta.TitularesIII.con_indecidible
#print axioms ROBINSON_PlusPlus.Meta.TitularesIII.prf_of_prov_de
#print axioms ROBINSON_PlusPlus.Meta.TitularesIII.godelCN_verdadera_de
#print axioms ROBINSON_PlusPlus.Meta.TitularesIII.con_verdadera_de
#print axioms ROBINSON_PlusPlus.Meta.TitularesIII.modelo_prov_iff
#print axioms ROBINSON_PlusPlus.Meta.TitularesIII.modelo_prov_iff_de
#print axioms ROBINSON_PlusPlus.Meta.TitularesIII.prf_completo
#print axioms ROBINSON_PlusPlus.Meta.TitularesIII.goedel_I_neg_fol
#print axioms ROBINSON_PlusPlus.Meta.TitularesIII.modelo_sin_G
#print axioms ROBINSON_PlusPlus.Meta.TitularesIII.goedel_I_semantico
