import ROBINSON_PlusPlus

/-!
# Rosser, Etapa 0: la REFLEXIÓN numeral de `substfc` y `liftfc` (ADR‑123)

**Fecha**: 2026‑10‑05. Es la primera pieza del plan re‑medido de Rosser (ADR‑122 §2, ruta híbrida): «la reflexión
—la evaluación interna ya probada, la solidez y W1— da la evaluación EXTERNA de `substfc`/`liftfc` sobre numerales».
Este sondeo la CONFIRMA, y mide lo que cuesta.

**Qué dice**: para numerales `ā, b̄, c̄` cuyas guardas son VERDADERAS en el modelo estándar,

    Prf (substfc ā b̄ c̄ =eq ⟨substfcN a b c⟩‾)        Prf (liftfc ā c̄ =eq ⟨liftfcN a c⟩‾)

—la teoría CALCULA la sustitución y el lift de códigos sobre numerales—, sin inducción NUEVA sobre la fórmula y sin
abrir aquí ningún axioma de codificación: la inducción sobre el código (interna en `pcc_eval_substfc`/
`pcc_eval_liftfc`; externa en `dec_substfc`/`dec_liftfc`, que usa W1) y la apertura de los axiomas (sus `Caso*` y
`MN_axioms`) ya estaban pagadas; lo de aquí sólo induce sobre `Nat` (`decT_tcFnN`).

**Cómo** (cuatro piezas que ya estaban, y lo que se les añade):
1. la evaluación INTERNA (`pcc_eval_substfc_wit`, `pcc_eval_liftfc_wit`): `Prf (guardas → Prov⌜s(ā,b̄,c̄) = valor⌝)`;
2. la SOLIDEZ (`prf_sound`): en `MNV V₀`, con las guardas verdaderas allí, `Prov⌜…⌝` vale;
3. lo que el modelo cree demostrable lo es (`verificador_solido`, W1), DECODIFICADO;
4. el decodificador sobre el código de la ecuación (`dec_eq`, `decT_func`).
Lo nuevo: `decT_tcFnN` (`tcFn` codifica el numeral `numeralM`), W1 para un término‑código CUALQUIERA
(`ev_provFromCode`, `prf_dec_of_prov`; `prf_of_prov` sólo toma `provCodeC' φ`) y la evaluación de los dos códigos de
ecuación (`ev_evalSubstfcCode`, `ev_eqcLiftfc`). No exige `Prf guarda`: basta que la guarda sea VERDADERA en el modelo.

**No vacuidad**: `hasWitN_codigo`/`hasWitFN_codigo` (las guardas valen en los numerales de los códigos de verdad, por
la solidez de `prf_hasWit_termCodeM`/`prf_hasWitF_fc`), y `prf_eval_substfc_codigo` sin hipótesis, sobre
`numeralM (codeNatTerm t)` y `numeralM (codeNat φ)`; su valor DECODIFICA a `φ[t/n]` (`dec_valor_substfc`).

**Lo que añade a lo que había**: sobre los códigos CANÓNICOS la evaluación externa ya existía SIN el modelo
—`prf_substFormula_arith`/`prf_liftFormula_arith` (`Meta/ArithPrf.lean`), sobre `formCode φ`, con los puentes
`prf_termCode_numeral`/`prf_formCode_numeral`—. La reflexión la extiende a TODO numeral con las guardas verdaderas,
también a los NO canónicos (p. ej., un campo de símbolo que no es `codeNatStr` de ninguna cadena: las guardas no lo
miran), que son los que NegNum tiene que tratar al recorrer numerales arbitrarios.

⚠️ Lo que NO dice: nada de los numerales BASURA (las guardas falsas), que es la otra mitad de NegNum; ni que el
resto del plan de Rosser cueste lo estimado. Revisado por una auditoría adversarial (`wf_107c9121-80b`, ADR‑124).

## Medido (2026‑10‑05, RPP con ADR‑122)

Compila en 4 s (0,78 GB), 0 errores y 0 avisos; 189 líneas, 18 teoremas, 86 de declaraciones (38 de enunciado,
48 de prueba). Es la primera de las tres piezas de la Etapa 0, cuya ESTIMACIÓN conjunta era 120–200.
`#print axioms` de los tres titulares: `[propext, Classical.choice, Quot.sound]`.

## Cómo re‑ejecutarlo

    lake env lean sondeos/RosserReflexion.lean      # desde la raíz de RPP
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open FOL FOL.Metamath.Semantics ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ModeloCodigo ROBINSON_PlusPlus.Meta.ModeloEstandar ROBINSON_PlusPlus.Meta.ModeloCodificacion
open ROBINSON_PlusPlus.Meta.SolidezVerificador

namespace RosserReflexion

/-! ## §1 · Evaluaciones en `MNV V`, con `V` VARIABLE (⛔ nunca un `rfl` contra `V₀`) -/

section Evaluacion
variable {V : Nat}

theorem ev_numeral (v : Nat → Nat) (n : Nat) :
    evalTerm (MNV V) v (ROBINSON_PlusPlus.Meta.Godel.numeral n) = n := by
  rw [← ROBINSON_PlusPlus.Meta.CheckArith.numeralM_eq, ev_numeralM]

theorem ev_strCode (v : Nat → Nat) (s : String) :
    evalTerm (MNV V) v (ROBINSON_PlusPlus.Meta.Provability.strCode s) = codeNatStr s := by
  rw [← ROBINSON_PlusPlus.Meta.Representability.strCodeM_eq, ev_strCodeM]

theorem ev_liftfc (v : Nat → Nat) (a b : Term) :
    evalTerm (MNV V) v (liftfc a b) = liftfcN (evalTerm (MNV V) v a) (evalTerm (MNV V) v b) := rfl

theorem ev_uno (v : Nat → Nat) : evalTerm (MNV V) v (succ zero) = 1 := rfl
theorem ev_cuatro (v : Nat → Nat) : evalTerm (MNV V) v (succ (succ (succ (succ zero)))) = 4 := rfl

/-- El valor del código de la ecuación de la evaluación interna de `substfc`, sobre numerales. -/
theorem ev_evalSubstfcCode (v : Nat → Nat) (a b c : Nat) :
    evalTerm (MNV V) v (ROBINSON_PlusPlus.Meta.SubstfcCodePrf.evalSubstfcCode (numeralM a) (numeralM b) (numeralM c))
      = consN 4 (consN (consN 1 (consN (codeNatStr "substfc")
          (consN (consN (tcFnN a) (consN (tcFnN b) (consN (tcFnN c) 0))) 0)))
        (consN (tcFnN (substfcN a b c)) 0)) := by
  rw [ROBINSON_PlusPlus.Meta.SubstfcCodePrf.evalSubstfcCode, ROBINSON_PlusPlus.Meta.Sigma1AtomPrf.eqCodeFn,
    ROBINSON_PlusPlus.Meta.EvalArithPrf.substfcT, funcc]
  simp only [ev_cons, ev_nil, ev_numeral, ev_uno, ev_strCode, ev_tcFn, ev_substfc, ev_numeralM]

/-- Lo mismo para `liftfc` (su ecuación, la de `pcc_eval_liftfc_wit`, usa `eqc`: la etiqueta es `σ⁴0`). -/
theorem ev_eqcLiftfc (v : Nat → Nat) (a c : Nat) :
    evalTerm (MNV V) v (eqc (ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.liftfcT (tcFn (numeralM a)) (tcFn (numeralM c)))
      (tcFn (liftfc (numeralM a) (numeralM c))))
      = consN 4 (consN (consN 1 (consN (codeNatStr "liftfc")
          (consN (consN (tcFnN a) (consN (tcFnN c) 0)) 0)))
        (consN (tcFnN (liftfcN a c)) 0)) := by
  rw [eqc, ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.liftfcT, funcc]
  simp only [ev_cons, ev_nil, ev_cuatro, ev_uno, ev_strCode, ev_tcFn, ev_liftfc, ev_numeralM]

end Evaluacion

/-! ## §2 · `tcFn` codifica `numeralM`, y lo que el modelo cree demostrable de un código cualquiera -/

theorem decT_tcFnN : ∀ n : Nat, decT (tcFnN n) = numeralM n
  | 0 => by rw [tcFnN, decT_func, decS_codeNatStr, decTs_zero]; rfl
  | n + 1 => by rw [tcFnN, decT_func, decS_codeNatStr, decTs_consN, decTs_zero, decT_tcFnN n]; rfl

/-- `ev_provCodeC'` para un término‑código CUALQUIERA (no sólo `⌜φ⌝`). -/
theorem ev_provFromCode (c : Term) (v : Nat → Nat) :
    evalFormula (MNV V₀) v (ROBINSON_PlusPlus.Meta.Sigma1Prf.provFromCode c) →
      ∃ p, And (chainOkN V₀ 0 p) (memN (evalTerm (MNV V₀) v c) (runFnN 0 p)) := by
  intro h
  rw [ROBINSON_PlusPlus.Meta.Sigma1Prf.provFromCode, eval_substFormula_zero] at h
  simp only [ROBINSON_PlusPlus.Meta.ProofChain.provFormulaC', land, chainOk, In, runFn, nil, zero,
    in_sym, zero_sym, evalFormula, evalTerm, evalTerms, shiftEnv, MN_chainOk, MN_mem, MN_runFn, MN_zero] at h
  exact h

/-- Lo que `MNV V₀` cree demostrable, DECODIFICADO, es teorema (W1 sobre un código cualquiera). -/
theorem prf_dec_of_prov (c : Term) (v : Nat → Nat) :
    evalFormula (MNV V₀) v (ROBINSON_PlusPlus.Meta.Sigma1Prf.provFromCode c) → Prf (dec (evalTerm (MNV V₀) v c)) := by
  intro h
  obtain ⟨p, hp, hm⟩ := ev_provFromCode c v h
  exact verificador_solido hp hm

/-! ## §3 · 🏁 LA REFLEXIÓN: la teoría calcula `substfc` y `liftfc` sobre numerales -/

/-- 🏁 **`substfc` sobre numerales**, con las guardas VERDADERAS en el modelo (sin exigir su `Prf`). -/
theorem prf_eval_substfc_num (a b c : Nat) (hb : hasWitN b) (hc : hasWitFN c) :
    Prf (Formula.eq (substfc (numeralM a) (numeralM b) (numeralM c)) (numeralM (substfcN a b c))) := by
  have hs := ROBINSON_PlusPlus.Meta.SolidezPrf.prf_sound ROBINSON_PlusPlus.Meta.Consistencia.estandar_MN
    (ROBINSON_PlusPlus.Meta.EvalSubstfcPrf.pcc_eval_substfc_wit (numeralM a) (numeralM b) (numeralM c)) (fun _ => 0)
  have hg : evalFormula (MNV V₀) (fun _ => 0) (land (hasWit (numeralM b)) (hasWitF (numeralM c))) := by
    show And _ _
    exact ⟨(ev_hasWit _ _).mpr (by rw [ev_numeralM]; exact hb), (ev_hasWitF _ _).mpr (by rw [ev_numeralM]; exact hc)⟩
  have ht := hs hg
  rw [ROBINSON_PlusPlus.Meta.EvalSubstfcPrf.targetSubstfc] at ht
  have h := prf_dec_of_prov _ _ ht
  rw [ev_evalSubstfcCode, dec_eq, decT_func, decS_codeNatStr, decTs_consN, decTs_consN, decTs_consN, decTs_zero,
    decT_tcFnN, decT_tcFnN, decT_tcFnN, decT_tcFnN] at h
  exact h

/-- 🏁 **`liftfc` sobre numerales**, con la guarda VERDADERA en el modelo. -/
theorem prf_eval_liftfc_num (a c : Nat) (hc : hasWitFN c) :
    Prf (Formula.eq (liftfc (numeralM a) (numeralM c)) (numeralM (liftfcN a c))) := by
  have hs := ROBINSON_PlusPlus.Meta.SolidezPrf.prf_sound ROBINSON_PlusPlus.Meta.Consistencia.estandar_MN
    (ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.pcc_eval_liftfc_wit (numeralM a) (numeralM c)) (fun _ => 0)
  have ht := hs ((ev_hasWitF _ _).mpr (by rw [ev_numeralM]; exact hc))
  have h := prf_dec_of_prov _ _ ht
  rw [ev_eqcLiftfc, dec_eq, decT_func, decS_codeNatStr, decTs_consN, decTs_consN, decTs_zero,
    decT_tcFnN, decT_tcFnN, decT_tcFnN] at h
  exact h

/-! ## §4 · No vacuidad: las guardas valen en los códigos de verdad, y el valor es el que debe -/

theorem hasWitN_codigo (t : Term) : hasWitN (codeNatTerm t) := by
  have h := ROBINSON_PlusPlus.Meta.SolidezPrf.prf_sound ROBINSON_PlusPlus.Meta.Consistencia.estandar_MN
    (ROBINSON_PlusPlus.Meta.SubstTreeReflect.prf_hasWit_termCodeM t) (fun _ => 0)
  rw [ev_hasWit, ev_termCodeM] at h
  exact h

theorem hasWitFN_codigo (φ : Formula) : hasWitFN (codeNat φ) := by
  have h := ROBINSON_PlusPlus.Meta.SolidezPrf.prf_sound ROBINSON_PlusPlus.Meta.Consistencia.estandar_MN
    (ROBINSON_PlusPlus.Meta.Representability2.prf_hasWitF_fc φ) (fun _ => 0)
  rw [ev_hasWitF, ← ROBINSON_PlusPlus.Meta.Representability.formCodeM_eq, ev_formCodeM] at h
  exact h

/-- La evaluación externa sobre los NUMERALES de los códigos de verdad, calculada en la teoría. -/
theorem prf_eval_substfc_codigo (n : Nat) (t : Term) (φ : Formula) :
    Prf (Formula.eq (substfc (numeralM n) (numeralM (codeNatTerm t)) (numeralM (codeNat φ)))
      (numeralM (substfcN n (codeNatTerm t) (codeNat φ)))) :=
  prf_eval_substfc_num n _ _ (hasWitN_codigo t) (hasWitFN_codigo φ)

/-- …y el valor de la derecha DECODIFICA a `φ[t/n]`. -/
theorem dec_valor_substfc (n : Nat) (t : Term) (φ : Formula) :
    dec (substfcN n (codeNatTerm t) (codeNat φ)) = substFormula n t φ := by
  rw [dec_substfc, decT_codeNatTerm, dec_codeNat]

theorem prf_eval_liftfc_codigo (n : Nat) (φ : Formula) :
    Prf (Formula.eq (liftfc (numeralM n) (numeralM (codeNat φ))) (numeralM (liftfcN n (codeNat φ)))) :=
  prf_eval_liftfc_num n _ (hasWitFN_codigo φ)

theorem dec_valor_liftfc (n : Nat) (φ : Formula) : dec (liftfcN n (codeNat φ)) = liftFormula n φ := by
  rw [dec_liftfc, dec_codeNat]

end RosserReflexion

#print axioms RosserReflexion.prf_eval_substfc_num
#print axioms RosserReflexion.prf_eval_liftfc_num
#print axioms RosserReflexion.prf_eval_substfc_codigo
