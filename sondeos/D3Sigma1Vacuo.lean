/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus

/-!
# SONDEO · ¿son VACUOS `d3_prf_of_sigma1` y `d3_prf_of_reflect_bounded`?

**Fecha:** 2026‑10‑12 · **Origen:** la auditoría del suelo (`doc/AUDITORIA-SUELO-2026-10-12.md`, trabajo T05). El
enunciado lo propuso su verificador de vacuidad, por lectura y sin compilar; aquí se compila.

`d3_prf_of_sigma1` (`Meta/ReflectionPrf.lean`) toma la hipótesis
`hI : ∀ x L : Term, Prf (In x L ⇒ provCodeC' (In x L))`, y `d3_prf_of_reflect_bounded`
(`Meta/Sigma1BoundedPrf.lean`) la saca de `hbI`, la misma reflexión para `boundedIn`. Sus docstrings los
presentan como reducciones de D3 a un núcleo «claramente especificado».

**La refutación**, con el modelo `MNV V₀` y la solidez `prf_sound`: con `x := #0` y `L := cons zero nil`, la
fórmula `In #0 L` vale bajo la valoración `0`; por `hI` y la solidez, vale también `provCodeC' (In #0 L)`, y
`prf_of_prov` da `Prf (In #0 L)`; pero bajo la valoración `1` la fórmula es falsa (`1 ∉ [0]`), contra la solidez.
⇒ ninguna de las dos hipótesis se puede descargar: los dos teoremas son ciertos y VACUOS. Ninguno tiene
consumidor fuera del par (✏️ 2026‑10‑14: decía «Ninguno tiene consumidor»; `d3_prf_of_reflect_bounded` consume a
`d3_prf_of_sigma1`, `Meta/Sigma1BoundedPrf.lean`); el D3 que se usa, `d3_prf_real`, va por otra vía y no lo es.

⛔ Ni `simp` sobre `h0` ni `rfl` contra `V₀` (la trampa de `Meta/Consistencia.lean:39-42`).

**Resultado (2026‑10‑12):** compila (entre 4 y 76 s en tres ejecuciones, según la caché); `#print axioms` de los dos: `[propext, Classical.choice, Quot.sound]`.
Lo que queda de T05: retirar o marcar los dos teoremas (y `Meta/Sigma1BoundedPrf.lean`, que sólo importa el barril).
-/

open FOL FOL.Metamath.Semantics
open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ModeloCodigo ROBINSON_PlusPlus.Meta.ModeloEstandar

namespace D3Sigma1Vacuo

theorem hI_refutable :
    ¬ (∀ x L : Term, Prf (In x L ⇒ ROBINSON_PlusPlus.Meta.ProofChain.provCodeC' (In x L))) := by
  intro hI
  have h0 := ROBINSON_PlusPlus.Meta.SolidezPrf.prf_sound ROBINSON_PlusPlus.Meta.Consistencia.estandar_MN
    (hI (.var 0) (cons zero nil)) (fun _ => 0)
  have hm : evalFormula (MNV V₀) (fun _ => 0) (In (.var 0) (cons zero nil)) := by
    simp only [In, cons, nil, zero, in_sym, cons_sym, zero_sym, evalFormula, evalTerm, evalTerms, MN_mem, MN_cons, MN_zero]
    exact (memN_consN 0 0 0).2 (Or.inl rfl)
  have hp : Prf (In (.var 0) (cons zero nil)) :=
    ROBINSON_PlusPlus.Meta.SolidezVerificador.prf_of_prov _ (fun _ => 0) (h0 hm)
  have h1 := ROBINSON_PlusPlus.Meta.SolidezPrf.prf_sound ROBINSON_PlusPlus.Meta.Consistencia.estandar_MN hp (fun _ => 1)
  simp only [In, cons, nil, zero, in_sym, cons_sym, zero_sym, evalFormula, evalTerm, evalTerms, MN_mem, MN_cons, MN_zero] at h1
  rcases (memN_consN 1 0 0).1 h1 with h | h
  · exact absurd h (by decide)
  · exact memN_zero 1 h

theorem hbI_refutable :
    ¬ (∀ x L : Term, Prf (ROBINSON_PlusPlus.Meta.BoundedInPrf.boundedIn x L ⇒
        ROBINSON_PlusPlus.Meta.ProofChain.provCodeC' (ROBINSON_PlusPlus.Meta.BoundedInPrf.boundedIn x L))) :=
  fun hbI => hI_refutable (ROBINSON_PlusPlus.Meta.Sigma1BoundedPrf.prf_hI_of_reflect_boundedIn hbI)

end D3Sigma1Vacuo

#print axioms D3Sigma1Vacuo.hI_refutable
#print axioms D3Sigma1Vacuo.hbI_refutable
