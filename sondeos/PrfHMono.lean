/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.HilbertDeduction

/-!
# SONDEO · `PrfH_mono` / `PrfH_w1` — la **deuda B6b**, que ya estaba pagada sin que nadie lo supiera

**Rescatado el 2026‑09‑11** del barrido de `Probe/` (regla **M‑9**), desde
`Probe/CritDesc_consumidor.lean` §C2 (líneas 1517‑1539, `0 sorry`).

## ⛔ Por qué este fichero es un hallazgo y no una promoción rutinaria

`NEXT-STEPS.md` (rama B6b) dice, literalmente:

> `PrfH_mono` / `PrfH_w1` (monotonía del contexto en `PrfH`) **NO existen en NINGÚN sitio** —
> ni en producción ni en sondeos (verificado por grep 2026‑08‑31). Van a
> `Meta/HilbertDeduction.lean`, pero **hay que PROBARLOS primero**.

Estaban **probados** en `Probe/`, que está en `.gitignore`. El grep del 2026‑08‑31 fue correcto
—`Probe/` no es «producción ni sondeos»— y aun así la conclusión operativa era falsa: no había que
probarlos, había que **ir a buscarlos**.

⚠️ Y no es gratis: **cuatro módulos de producción pagan su ausencia por nombre**, todos con el
rodeo de meter la ecuación como **antecedente OBJETO** para que el `or`‑elim la conserve en cada
rama:

| módulo | línea |
|---|---|
| `Meta/LiftcCodePrf.lean` | 1426 |
| `Meta/EvalLiftfcPrf.lean` | 749 |
| `Meta/HasWitFTrackedPrf.lean` | 183 |
| `Meta/HasWitTrackedPrf.lean` | 757 |

🔑 **La lección, y van CINCO**: *trabajo hecho y no recogido, ahora en `Probe/`*. Lo nuevo esta vez
es la forma: **un documento de planificación afirmando en presente que algo no existe**, con su
medición citada y su fecha — y la medición era correcta. Lo que falló fue el **alcance** de la
medición, no la medición.

## Qué son

`PrfH_mono` es debilitamiento de contexto para `PrfH` por inducción sobre sus **8 constructores**
(`hyp`, `incl0`, `p3`, `ind`, `qconf`, `listInd`, `mp`, `gen`). El único caso no trivial es `gen`,
que reconstruye la inclusión a través de `Γ.map (liftFormula 0)` con `List.mem_map`.

## ⬜ Lo que este sondeo NO hace

**No los mueve a producción.** Su destino es `Meta/HilbertDeduction.lean`, junto a `prfH_weaken` y
`prf_to_prfH`, y eso cierra B6b — pero es una edición de producción y va en su propio commit.
-/

open FOL
open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.HilbertDeduction

namespace Sondeos.PrfHMono

/-- **Monotonía del contexto en `PrfH`**: si `Γ ⊆ Δ`, todo lo demostrable desde `Γ` lo es desde `Δ`.
    Inducción sobre los 8 constructores; el caso `gen` viaja por `List.mem_map`. -/
theorem PrfH_mono : ∀ {Γ : List Formula} {ψ : Formula}, PrfH Γ ψ →
    ∀ Δ : List Formula, (∀ φ, List.Mem φ Γ → List.Mem φ Δ) → PrfH Δ ψ := by
  intro Γ ψ h
  induction h with
  | hyp Γ' φ hm => intro Δ hsub; exact PrfH.hyp Δ φ (hsub φ hm)
  | incl0 Γ' φ h0 => intro Δ _; exact PrfH.incl0 Δ φ h0
  | p3 Γ' A => intro Δ _; exact PrfH.p3 Δ A
  | ind Γ' A => intro Δ _; exact PrfH.ind Δ A
  | qconf Γ' P C => intro Δ _; exact PrfH.qconf Δ P C
  | listInd Γ' A => intro Δ _; exact PrfH.listInd Δ A
  | mp Γ' A B hAB hA ihAB ihA => intro Δ hsub; exact PrfH.mp Δ A B (ihAB Δ hsub) (ihA Δ hsub)
  | gen Γ' A hdd ih =>
      intro Δ hsub
      refine PrfH.gen Δ A (ih (Δ.map (liftFormula 0)) ?_)
      intro φ hm
      have hm' : φ ∈ Γ'.map (liftFormula 0) := hm
      rcases List.mem_map.mp hm' with ⟨ψ0, hψ0, rfl⟩
      exact List.mem_map.mpr ⟨ψ0, hsub ψ0 hψ0, rfl⟩

/-- Debilitamiento por UNA hipótesis — el caso que consumen los cuatro módulos. -/
theorem PrfH_w1 {Γ : List Formula} {A ψ : Formula} (h : PrfH Γ ψ) : PrfH (A :: Γ) ψ :=
  PrfH_mono h _ (fun _ hm => List.Mem.tail _ hm)

end Sondeos.PrfHMono

/-! ## FOOTPRINT -/
#print axioms Sondeos.PrfHMono.PrfH_mono
#print axioms Sondeos.PrfHMono.PrfH_w1
