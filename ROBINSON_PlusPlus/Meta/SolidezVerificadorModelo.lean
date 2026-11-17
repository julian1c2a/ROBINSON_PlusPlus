/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.SolidezVerificador
import ROBINSON_PlusPlus.Meta.Consistencia

/-!
# `Meta/SolidezVerificadorModelo.lean` — W1 leído en el modelo: lo que `MNV V₀` acepta como prueba es teorema (C5; ADR‑268)

`bueno_V₀` (el ÚNICO paso de W1 por el modelo: `V₀` es el código de los 120, `V₀_eq_codigo`), `verificador_solido`
(W1), `ev_provCodeC'` y `prf_of_prov` (lo que el modelo cree demostrable, lo es). Vivían al final de
`Meta/SolidezVerificador.lean`, cuyo resto —el decodificador y W1 sin el modelo, `cadena_buena`— no nombra la
semántica: aquel módulo baja a C4 (el espejo en ℕ) y esto queda en C5 (el nudo N2 de ADR‑266). Mismos enunciados y
pruebas; cambia el espacio de nombres, que es el de este fichero (NAMING‑CONVENTIONS §6).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open FOL FOL.Metamath.Semantics ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ModeloCodigo ROBINSON_PlusPlus.Meta.CodeNatInjPrf
open ROBINSON_PlusPlus.Meta.ModeloEstandar ROBINSON_PlusPlus.Meta.ModeloCodificacion
open ROBINSON_PlusPlus.Meta.SolidezVerificador

namespace ROBINSON_PlusPlus.Meta.SolidezVerificadorModelo

/-- `V₀`, el valor de `axiomsCodeT` en el modelo, es `Bueno`: es el código de los 120 por `V₀_eq_codigo`, que se
    prueba con la solidez. Es el ÚNICO paso de W1 por el modelo. -/
theorem bueno_V₀ : Bueno V₀ := by
  rw [ROBINSON_PlusPlus.Meta.Consistencia.V₀_eq_codigo]
  exact bueno_codeNatList

/-- 🏁 **W1**: si `MNV V₀` cree que la cadena `p` es una prueba, todo lo que concluye, decodificado, es teorema
    de `Prf`. -/
theorem verificador_solido {p y : Nat} (h : chainOkN V₀ 0 p) (hy : memN y (runFnN 0 p)) : Prf (dec y) :=
  cadena_buena bueno_V₀ (decodeL p) 0 bueno_zero h y hy

/-! ## §5 · ⊬ ¬G: Gödel I, la otra mitad, por la solidez del verificador en el modelo -/

theorem ev_provCodeC' (φ : Formula) (v : Nat → Nat) :
    evalFormula (MNV V₀) v (ROBINSON_PlusPlus.Meta.ProofChain.provCodeC' φ) →
      ∃ p, And (chainOkN V₀ 0 p) (memN (codeNat φ) (runFnN 0 p)) := by
  intro h
  rw [ROBINSON_PlusPlus.Meta.ProofChain.provCodeC', eval_substFormula_zero,
    ← ROBINSON_PlusPlus.Meta.Representability.formCodeM_eq, ev_formCodeM] at h
  simp only [ROBINSON_PlusPlus.Meta.ProofChain.provFormulaC', land, chainOk, In, runFn, nil, zero,
    in_sym, zero_sym, evalFormula, evalTerm, evalTerms, shiftEnv, MN_chainOk, MN_mem, MN_runFn, MN_zero] at h
  exact h

/-- Lo que el modelo cree demostrable, lo es: `ev_provCodeC'`, W1 y `dec_codeNat`. -/
theorem prf_of_prov (φ : Formula) (v : Nat → Nat) :
    evalFormula (MNV V₀) v (ROBINSON_PlusPlus.Meta.ProofChain.provCodeC' φ) → Prf φ := by
  intro hp
  obtain ⟨p, hc, hm⟩ := ev_provCodeC' _ _ hp
  have h := verificador_solido hc hm
  rw [dec_codeNat] at h
  exact h

-- (✏️ ADR‑191: `modelo_prov_iff` —`Prov` es fiel en `MNV V₀`— se mudó a `Meta/ProvFiel.lean`, con su nombre: su
-- vuelta pide ahora el testigo de `posNum` y `proofN_decide`, que van después de este módulo.)

end ROBINSON_PlusPlus.Meta.SolidezVerificadorModelo

#print axioms ROBINSON_PlusPlus.Meta.SolidezVerificadorModelo.verificador_solido
