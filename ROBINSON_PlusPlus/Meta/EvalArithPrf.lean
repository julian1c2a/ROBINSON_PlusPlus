/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
import ROBINSON_PlusPlus.Meta.MpCodePrf
import ROBINSON_PlusPlus.Meta.Sigma1AtomPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.TcArithPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.MpCodePrf
open ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace ROBINSON_PlusPlus.Meta.EvalArithPrf

/-!
## META — NIVEL D real (§21): **evaluación provable** de la aritmética — base de `+`

**Qué es la evaluación provable.** El cuerpo Δ₀ del verificador contiene términos simbólicos
(`ȧ + ḃ`, `nthc L̇ i̇`, …) aplicados a **numerales**. La Σ₁‑completitud provable necesita que la
teoría objeto demuestre **internamente** que esos términos **evalúan** al numeral de su valor:

```text
⊢ Prov( ⌜ ȧ + ḃ  =  (a + b)˙ ⌝ )        (`ṫ` = `tcFn t`, el «numeral‑de»)
```

Aquí `ȧ + ḃ` es el código del **término simbólico** (`addcT (tcFn a) (tcFn b)`), mientras que
`(a+b)˙` es el código del **numeral del valor** (`tcFn (add a b)`). Son códigos distintos, y ése era
el hueco que §18 identificó como «la bestia».

**Este módulo cierra la BASE** (`b = 0`), reuniendo las tres piezas de las secciones anteriores:

* `pcc_ax4_inst` (§19.3) — instancia de `ax4` **codificado** con testigo `tcFn a`.
* `prf_substfc_arith_open` (§20) — **computa** el `substfc` con testigo‑código arbitrario.
* `prf_tc_zero` / `prf_congr_tcFn` + `prf_provCode_congr` — transporte Leibniz de códigos.

El caso `σ` es gratis (`prf_tc_succ`); el paso inductivo de `+` queda para `pcc_axiom_inst2` (`ax5`).
-/

/-! ### Constructor de código del término `x + y` -/

/-- Código object del término `x + y` desde los códigos `x`, `y` de sus argumentos:
    `⟨1, ⌜+⌝, [x, y]⟩`. Es `termCode` de `add` con los argumentos ya codificados. -/
def addcT (x y : Term) : Term := funcc (strCode add_sym) (cons x (cons y nil))

/-- **Puente definicional** con `termCode` (por definición de `termCode` sobre `.func`). -/
theorem addcT_termCode (a b : Term) : addcT (termCode a) (termCode b) = termCode (add a b) := rfl

/-- **Congruencia** de `addcT` en ambos argumentos (`Prf`). -/
theorem prf_congr_addcT {x x' y y' : Term}
    (hx : Prf (x =eq x')) (hy : Prf (y =eq y')) :
    Prf (addcT x y =eq addcT x' y') := by
  unfold addcT funcc
  exact prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head
    (prf_eq_trans (prf_congr_cons_head hx) (prf_congr_cons_tail (prf_congr_cons_head hy)))))

/-! ### El enunciado de la evaluación provable de `+` -/

/-- Código de la fórmula `ȧ + ḃ = (a+b)˙`: *el término simbólico suma de los numerales de `a` y `b`
    es igual al numeral del valor `a+b`*. Es lo que hay que demostrar **dentro** de `Prov`. -/
def evalAddCode (a b : Term) : Term :=
  eqCodeFn (addcT (tcFn a) (tcFn b)) (tcFn (add a b))

/-! ### Base de la inducción: `b = 0` -/

/-- Paso intermedio: la instancia **codificada** de `ax4` con testigo `tcFn a`, ya **computada**.
    Da `Prov(⌜ȧ + ⌜0⌝ = ȧ⌝)` — nótese `⌜0⌝ = termCode zero`, aún no `tcFn zero`. -/
theorem pcc_ax4_computed (a : Term) :
    Prf (provFromCode (eqCodeFn (addcT (tcFn a) (termCode zero)) (tcFn a))) :=
  prf_mp
    (prf_provCode_congr
      (prf_substfc_arith_open 0 (tcFn a) (add (.var 0) zero =eq (.var 0))))
    (pcc_ax4_inst (tcFn a))

/-- **BASE de la evaluación provable de `+`**: `⊢ Prov(⌜ȧ + 0̇ = (a+0)˙⌝)`.

    De `pcc_ax4_computed` (que da `Prov(⌜ȧ + ⌜0⌝ = ȧ⌝)`) transportando los **códigos** por Leibniz:

    * `⌜0⌝ =eq tcFn zero` — `prf_tc_zero` (simétrico);
    * `tcFn a =eq tcFn (add a zero)` — congruencia de `tcFn` sobre `add a 0 =eq a` (`prf_add_zero_t`). -/
theorem pcc_eval_add_zero (a : Term) : Prf (provFromCode (evalAddCode a zero)) := by
  have hz : Prf (termCode zero =eq tcFn zero) := prf_eq_symm prf_tc_zero
  have ha : Prf (tcFn a =eq tcFn (add a zero)) :=
    prf_eq_symm (prf_congr_tcFn (prf_add_zero_t a))
  exact prf_mp
    (prf_provCode_congr
      (prf_congr_eqCodeFn (prf_congr_addcT (prf_refl (tcFn a)) hz) ha))
    (pcc_ax4_computed a)

end ROBINSON_PlusPlus.Meta.EvalArithPrf

export ROBINSON_PlusPlus.Meta.EvalArithPrf (
  addcT addcT_termCode prf_congr_addcT
  evalAddCode pcc_ax4_computed pcc_eval_add_zero
)
