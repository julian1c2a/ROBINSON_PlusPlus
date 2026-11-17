/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.TitularesII
import ROBINSON_PlusPlus.Meta.TitularesIII
import ROBINSON_PlusPlus.Meta.Lob
import ROBINSON_PlusPlus.Meta.RosserNegNum
import ROBINSON_PlusPlus.Meta.Consistencia
import ROBINSON_PlusPlus.Meta.PurezaComando

/-!
# `Meta/Controles.lean` — los controles que nombran la semántica, fuera de los módulos de titulares (C8; ADR‑268)

Las capas de ADR‑266 (decisión del propietario): los controles van a C8. Aquí, los que vivían en los módulos de las
etapas de Rosser, de Rosser y de Löb y USAN el modelo —los de «la hipótesis no es vacía»: donde la condición vale en ℕ,
`Prf` no la refuta, por la solidez en `MNV V₀`—, cada uno en un espacio de nombres con el nombre de su módulo de
origen (`Controles.RosserGuardNeg.control_exacta`…); y, al final, los controles POSITIVOS de los `#pureza` de esos
módulos: lo que TIENE que nombrar la semántica para que el criterio no esté ciego. En sus módulos queda cada
`#pureza` con sus puros. Mismos enunciados y pruebas. ✏️ 2026‑11‑17 (ADR‑269): y los dos de `Meta/RigidezEstandar.lean`,
que usan sus titulares, ahora de C7.iii: `control_instancia` (la hipótesis `Estandar M` no es vacía: `MNV V₀` la
cumple) y `control_ancla` (sin el ancla, `Prov` puede mentir).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ROBINSON_PlusPlus.Meta.Controles

namespace RosserGuardNeg
open FOL ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ChainPrf ROBINSON_PlusPlus.Meta.BoundedInPrf
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs
open ROBINSON_PlusPlus.Meta.ModeloCodigo ROBINSON_PlusPlus.Meta.RosserNumerales ROBINSON_PlusPlus.Meta.RosserNumEval
open ROBINSON_PlusPlus.Meta.RosserGuardNeg

/-- ✅ **…y sólo donde la guarda es falsa**: donde vale en ℕ, `Prf` no la refuta, por la solidez en `MNV V₀` (la doble‑negada, ADR‑191: lo verdadero con `P` no se refuta). Nombra la
    semántica: es el control positivo del `#pureza`. -/
theorem control_exacta (c : Nat) (h : hasWitN c) : ¬ Prf (neg (hasWit (numeralM c))) := by
  intro hp
  have hs := ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.prf_sound_dn ROBINSON_PlusPlus.Meta.Consistencia.estandarDN_MN
    hp (fun _ => 0)
  apply hs
  apply (ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.transfer ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.Dnada
    ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.decNada _ _).1 rfl
  rw [ROBINSON_PlusPlus.Meta.ModeloEstandar.ev_hasWit, ROBINSON_PlusPlus.Meta.ModeloEstandar.ev_numeralM]
  exact h

/-- ✅ Lo mismo para la guarda de fórmula. -/
theorem control_exactaF (c : Nat) (h : hasWitFN c) : ¬ Prf (neg (hasWitF (numeralM c))) := by
  intro hp
  have hs := ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.prf_sound_dn ROBINSON_PlusPlus.Meta.Consistencia.estandarDN_MN
    hp (fun _ => 0)
  apply hs
  apply (ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.transfer ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.Dnada
    ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.decNada _ _).1 rfl
  rw [ROBINSON_PlusPlus.Meta.ModeloEstandar.ev_hasWitF, ROBINSON_PlusPlus.Meta.ModeloEstandar.ev_numeralM]
  exact h

end RosserGuardNeg

namespace RosserNegLinea
open FOL ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ChainPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs
open ROBINSON_PlusPlus.Meta.ModeloCodigo ROBINSON_PlusPlus.Meta.RosserNumerales ROBINSON_PlusPlus.Meta.RosserNumEval
open ROBINSON_PlusPlus.Meta.RosserGuardNeg
open ROBINSON_PlusPlus.Meta.RosserNegLinea

/-- ✅ **…y sólo donde la línea es mala**: donde es buena en ℕ, `Prf` no la refuta, por la solidez en `MNV V₀` (la doble‑negada, ADR‑191: lo verdadero con `P` no se refuta).
    Nombra la semántica: es el control positivo del `#pureza`. -/
theorem control_exacta (x : Nat) (h : lineWFN Vax x) : ¬ Prf (neg (lineWF (numeralM x))) := by
  intro hp
  have hs := ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.prf_sound_dn ROBINSON_PlusPlus.Meta.Consistencia.estandarDN_MN
    hp (fun _ => 0)
  apply hs
  apply (ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.transfer ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.Dnada
    ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.decNada _ _).1 rfl
  have e := ROBINSON_PlusPlus.Meta.ModeloEstandar.ev_numeralM (V := codeNatList axioms) (fun _ => 0) x
  simp only [lineWF, FOL.Metamath.Semantics.evalFormula, FOL.Metamath.Semantics.evalTerms, e,
    ROBINSON_PlusPlus.Meta.ModeloEstandar.MN_lineWF, ROBINSON_PlusPlus.Meta.Consistencia.V₀_eq_codigo]
  exact h

end RosserNegLinea

namespace RosserNegNum
open FOL ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ChainPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs
open ROBINSON_PlusPlus.Meta.ModeloCodigo ROBINSON_PlusPlus.Meta.RosserNumerales ROBINSON_PlusPlus.Meta.RosserNumEval
open ROBINSON_PlusPlus.Meta.RosserGuardNeg ROBINSON_PlusPlus.Meta.RosserNegLinea
open ROBINSON_PlusPlus.Meta.RosserW1 ROBINSON_PlusPlus.Meta.RosserPosNum ROBINSON_PlusPlus.Meta.SolidezVerificador
open ROBINSON_PlusPlus.Meta.RosserNegNum

/-- ✅ **…y sólo donde no hay prueba**: donde `ProofN` vale, `Prf` no refuta `PfF`, por la solidez en `MNV V₀` (la doble‑negada, ADR‑191: lo verdadero con `P` no se refuta). -/
theorem control_exacta {m y : Nat} (h : ProofN m y) : ¬ Prf (neg (PfF (numeralM m) (numeralM y))) := by
  intro hp
  have hs := ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.prf_sound_dn ROBINSON_PlusPlus.Meta.Consistencia.estandarDN_MN
    hp (fun _ => 0)
  apply hs
  apply (ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.transfer ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.Dnada
    ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.decNada _ _).1 rfl
  have em := ROBINSON_PlusPlus.Meta.ModeloEstandar.ev_numeralM (V := codeNatList axioms) (fun _ => 0) m
  have ey := ROBINSON_PlusPlus.Meta.ModeloEstandar.ev_numeralM (V := codeNatList axioms) (fun _ => 0) y
  simp only [PfF, land, chainOk, In, runFn, nil, zero, FOL.Metamath.Semantics.evalFormula,
    FOL.Metamath.Semantics.evalTerm, FOL.Metamath.Semantics.evalTerms, ROBINSON_PlusPlus.Meta.Consistencia.V₀_eq_codigo,
    em, ey, ROBINSON_PlusPlus.Meta.ModeloEstandar.MN_chainOk, ROBINSON_PlusPlus.Meta.ModeloEstandar.MN_runFn]
  exact h

/-- ✅ La hipótesis puede fallar: la prueba de un axioma ES una prueba, y `Prf` no la refuta. -/
theorem control_falla {a : Formula} (ha : List.Mem a axioms) :
    ¬ Prf (neg (PfF (numeralM (consN (lineaThy a) 0)) (numeralM (codeNat a)))) :=
  control_exacta (proofN_axioma ha)

end RosserNegNum

namespace Rosser
open FOL ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.HilbertDeduction ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.DiagonalNumeral ROBINSON_PlusPlus.Meta.TarskiPrf
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs
open ROBINSON_PlusPlus.Meta.RosserPosNum ROBINSON_PlusPlus.Meta.RosserNegNum ROBINSON_PlusPlus.Meta.Sentencia
open ROBINSON_PlusPlus.Meta.Rosser

/-- ✅ La hipótesis puede VALER en una extensión NO sólida: T+¬Con es consistente (por Gödel II y la deducción), y
    demuestra ¬Con, FALSA en el modelo (`con_verdadera`). -/
theorem consistente_neg_con :
    ¬ PrfH [neg ROBINSON_PlusPlus.Meta.GodelTwo.consistencyFormula'] Formula.bottom := by
  intro h
  have hnn : Prf (neg (neg ROBINSON_PlusPlus.Meta.GodelTwo.consistencyFormula')) :=
    (prfH_iff_prf_impChain _ _).1 h
  exact ROBINSON_PlusPlus.Meta.TitularesII.goedel_II
    (Prf.mp _ _ (Prf.p3 ROBINSON_PlusPlus.Meta.GodelTwo.consistencyFormula') hnn)

/-- ✅ Y allí Rosser vale, por el titular: con E = [¬Con] las dos hipótesis de `rosser_ext` valen a la vez, y la
    sentencia de Rosser de T+¬Con es indecidible en T+¬Con, donde la solidez no puede sustituir a la consistencia. -/
theorem control_neg_con :
    And (¬ PrfH [neg ROBINSON_PlusPlus.Meta.GodelTwo.consistencyFormula']
        (R [neg ROBINSON_PlusPlus.Meta.GodelTwo.consistencyFormula']))
      (¬ PrfH [neg ROBINSON_PlusPlus.Meta.GodelTwo.consistencyFormula']
        (neg (R [neg ROBINSON_PlusPlus.Meta.GodelTwo.consistencyFormula']))) :=
  rosser_ext _ (fun φ h => by
      cases h with
      | head => exact negCon_isSentence
      | tail _ h' => cases h') consistente_neg_con

end Rosser

namespace Lob
open FOL ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.HilbertDeduction ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.ProofChain ROBINSON_PlusPlus.Meta.DiagonalNumeral ROBINSON_PlusPlus.Meta.GodelTwoPrf
open ROBINSON_PlusPlus.Meta.TarskiPrf ROBINSON_PlusPlus.Meta.DerivCondPrf ROBINSON_PlusPlus.Meta.Representability2Prf
open ROBINSON_PlusPlus.Meta.PremsBdAllPrf
open ROBINSON_PlusPlus.Meta.Lob

/-- ✅ La hipótesis puede FALLAR: T no demuestra su reflexión para ⊥ (con `consistencia`; es Gödel II). -/
theorem control_reflexion_bot : ¬ Prf (provCodeC' Formula.bottom ⇒ Formula.bottom) :=
  fun h => ROBINSON_PlusPlus.Meta.Consistencia.consistencia (lob Formula.bottom h)

/-- ✅ Ni para la sentencia de Gödel: T no demuestra Prov⌜G⌝ ⇒ G (Löb y Gödel I). -/
theorem control_reflexion_godel : ¬ Prf (provCodeC' godelCN ⇒ godelCN) :=
  fun h => ROBINSON_PlusPlus.Meta.TitularesII.goedel_I (lob godelCN h)

end Lob

namespace RigidezEstandar
open FOL FOL.Metamath.Semantics
open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.ModeloCodigo ROBINSON_PlusPlus.Meta.SolidezPrf
open ROBINSON_PlusPlus.Meta.RigidezEstandar ROBINSON_PlusPlus.Meta.ModeloEstandar
open ROBINSON_PlusPlus.Meta.TitularesIII (prf_of_prov_de con_verdadera_de)

/-- El control de que la hipótesis no es vacía: `MNV V₀` es estándar (`estandar_MN`), y la instancia es
    `prf_of_prov` de `Meta/SolidezVerificadorModelo.lean`. -/
theorem control_instancia (φ : Formula) (v : Nat → Nat) :
    evalFormula (ROBINSON_PlusPlus.Meta.ModeloEstandar.MNV ROBINSON_PlusPlus.Meta.ModeloCodigo.V₀) v
      (ROBINSON_PlusPlus.Meta.ProofChain.provCodeC' φ) → Prf φ :=
  prf_of_prov_de ROBINSON_PlusPlus.Meta.Consistencia.estandar_MN φ v

/-- ⛔ **El control del ancla**: `MNV V⊥` satisface los 119 de la base, `Con` es FALSA en él (cree demostrable `⊥`),
    y el ancla FALLA —sin evaluar su numeral: si valiera, `MNV V⊥` sería estándar y `con_verdadera_de` lo
    impediría—. Es el ancla la que fija el sentido de `Prov`; hermano de `control_tc_cons`. -/
theorem control_ancla : And (∀ v, contextSatisfies (MNV Vbot) v axiomsBase)
    (And (∀ v, ¬ evalFormula (MNV Vbot) v ROBINSON_PlusPlus.Meta.GodelTwo.consistencyFormula')
      (¬ ∀ v, evalFormula (MNV Vbot) v ax_axiomsCodeT_def)) := by
  refine ⟨MNbot_base, MNbot_no_con, fun ha => ?_⟩
  have hM : Estandar (MNV Vbot) :=
    { hzero := MN_zero, hsucc := MN_succ, hcons := MN_cons,
      haxs := fun v φ hφ => by
        rw [axioms_split] at hφ
        cases List.mem_append.mp hφ with
        | inl h => exact MNbot_base v φ h
        | inr h => rw [List.mem_singleton.mp h]; exact ha v }
  exact MNbot_no_con (fun _ => 0) (con_verdadera_de hM _)

end RigidezEstandar

end ROBINSON_PlusPlus.Meta.Controles

/-! T08 (ADR‑147, ADR‑268): los controles POSITIVOS de los `#pureza` de `RosserW1`, `RosserPosNum`,
`RosserNumerales`, `RosserNumEval`, `RosserGuardNeg`, `RosserNegLinea`, `RosserNegNum`, `Rosser`, `Lob` y
`GodelCorolarios`: cada uno TIENE que nombrar la semántica. -/
#pureza |
  ROBINSON_PlusPlus.Meta.SolidezVerificadorModelo.verificador_solido
  ROBINSON_PlusPlus.Meta.SolidezVerificadorModelo.prf_of_prov
  ROBINSON_PlusPlus.Meta.ModeloEstandar.ev_numeralM
  ROBINSON_PlusPlus.Meta.Controles.RosserGuardNeg.control_exacta ROBINSON_PlusPlus.Meta.Controles.RosserGuardNeg.control_exactaF
  ROBINSON_PlusPlus.Meta.Controles.RosserNegLinea.control_exacta
  ROBINSON_PlusPlus.Meta.Controles.RosserNegNum.control_exacta ROBINSON_PlusPlus.Meta.Controles.RosserNegNum.control_falla
  ROBINSON_PlusPlus.Meta.TitularesII.rosser ROBINSON_PlusPlus.Meta.Controles.Rosser.control_neg_con
  ROBINSON_PlusPlus.Meta.Controles.Lob.control_reflexion_bot ROBINSON_PlusPlus.Meta.Controles.Lob.control_reflexion_godel
  ROBINSON_PlusPlus.Meta.TitularesIII.con_indecidible

#print axioms ROBINSON_PlusPlus.Meta.Controles.RigidezEstandar.control_ancla
