/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
import ROBINSON_PlusPlus.Meta.MpCodePrf
import ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
import ROBINSON_PlusPlus.Meta.NumCodeClosedPrf

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
open ROBINSON_PlusPlus.Meta.NumCodeClosedPrf

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

/-! ### (B) Cómputo de la instancia codificada de `ax5`

`substCodeF 1 W₁` sobre el cuerpo de `ax5` **computa por `rfl`**:

```text
substCodeF 1 W₁ (ȧ + σv₀ = σ(ȧ + v₀))  =  eqCodeFn (addcT W₁ (succcT ⌜v₀⌝)) (succcT (addcT W₁ ⌜v₀⌝))
```

Así que la composición **no necesita una inducción general** sobre fórmulas (§22.3 (B)): basta
computar el `substfc` externo sobre ese código explícito, con (A) (`prf_substtc_tcFn`) para que el
`W₁` incrustado sobreviva intacto. -/

/-- Código object del término `σ x` desde el código `x`: `⟨1, ⌜σ⌝, [x]⟩`. -/
def succcT (x : Term) : Term := funcc (strCode succ_sym) (cons x nil)

/-- `prf_tc_succ` dice exactamente `tcFn (σx) =eq succcT (tcFn x)` (definicional). -/
theorem prf_tc_succ' (x : Term) : Prf (tcFn (succ x) =eq succcT (tcFn x)) := prf_tc_succ x

/-- Congruencia de `succcT`. -/
theorem prf_congr_succcT {x y : Term} (h : Prf (x =eq y)) : Prf (succcT x =eq succcT y) :=
  prf_congr_funcc2 (prf_congr_cons_head h)

/-! #### `substtc` atraviesa los constructores de código de término -/

/-- `substtc` sobre un `funcc` de **un** argumento. -/
theorem prf_substtc_funcc1 (v W sc x : Term) :
    Prf (substtc v W (funcc sc (cons x nil)) =eq funcc sc (cons (substtc v W x) nil)) :=
  prf_eq_trans (prf_substtc_func v W sc (cons x nil))
    (prf_congr_funcc2
      (prf_eq_trans (prf_substtsc_cons v W x nil)
        (prf_congr_cons_tail (prf_substtsc_nil v W))))

/-- `substtc` sobre un `funcc` de **dos** argumentos. -/
theorem prf_substtc_funcc2 (v W sc x y : Term) :
    Prf (substtc v W (funcc sc (cons x (cons y nil)))
      =eq funcc sc (cons (substtc v W x) (cons (substtc v W y) nil))) :=
  prf_eq_trans (prf_substtc_func v W sc (cons x (cons y nil)))
    (prf_congr_funcc2
      (prf_eq_trans (prf_substtsc_cons v W x (cons y nil))
        (prf_congr_cons_tail
          (prf_eq_trans (prf_substtsc_cons v W y nil)
            (prf_congr_cons_tail (prf_substtsc_nil v W))))))

/-- `substtc` sobre `succcT`. -/
theorem prf_substtc_succcT (v W x : Term) :
    Prf (substtc v W (succcT x) =eq succcT (substtc v W x)) :=
  prf_substtc_funcc1 v W (strCode succ_sym) x

/-- `substtc` sobre `addcT`. -/
theorem prf_substtc_addcT (v W x y : Term) :
    Prf (substtc v W (addcT x y) =eq addcT (substtc v W x) (substtc v W y)) :=
  prf_substtc_funcc2 v W (strCode add_sym) x y

/-- `substtc zero W ⌜v₀⌝ =eq W` (la variable de código `0` recibe el testigo). -/
theorem prf_substtc_varc0 (W : Term) : Prf (substtc zero W (varc (numeral 0)) =eq W) :=
  prf_mp (prf_substtc_var_eq zero W (numeral 0)) (prf_refl zero)

/-! #### La instancia de `ax5`, computada -/

/-- **Instancia codificada de `ax5` ya computada**: `⊢ Prov(⌜ȧ + σḃ = σ(ȧ + ḃ)⌝)`.

    De `pcc_ax5_inst (tcFn a) (tcFn b)`, normalizando el `liftc zero (tcFn a)` con (A)
    (`prf_liftc_tcFn`) y computando el `substfc` externo sobre el código explícito, donde (A)
    (`prf_substtc_tcFn`) garantiza que el `tcFn a` incrustado sobrevive intacto. -/
theorem pcc_ax5_computed (a b : Term) :
    Prf (provFromCode
      (eqCodeFn (addcT (tcFn a) (succcT (tcFn b))) (succcT (addcT (tcFn a) (tcFn b))))) := by
  -- abreviaturas
  let W1 : Term := liftc zero (tcFn a)
  let B : Term := tcFn b
  -- (1) el `substfc` INTERNO se computa (y `substCodeF 1 W1 (cuerpo) ` es `rfl`)
  have hin : Prf (substfc (succ zero) W1
      (formCode (add (.var 1) (succ (.var 0)) =eq succ (add (.var 1) (.var 0))))
      =eq eqCodeFn (addcT W1 (succcT (varc (numeral 0))))
                   (succcT (addcT W1 (varc (numeral 0))))) :=
    prf_substfc_arith_open 1 W1 (add (.var 1) (succ (.var 0)) =eq succ (add (.var 1) (.var 0)))
  -- (2) (A): `liftc zero (tcFn a) =eq tcFn a` ⇒ normaliza `W1 → tcFn a` dentro del código
  have hnorm : Prf (eqCodeFn (addcT W1 (succcT (varc (numeral 0))))
                             (succcT (addcT W1 (varc (numeral 0))))
      =eq eqCodeFn (addcT (tcFn a) (succcT (varc (numeral 0))))
                   (succcT (addcT (tcFn a) (varc (numeral 0))))) := by
    have hA : Prf (W1 =eq tcFn a) := prf_liftc_tcFn a
    exact prf_congr_eqCodeFn
      (prf_congr_addcT hA (prf_refl _))
      (prf_congr_succcT (prf_congr_addcT hA (prf_refl _)))
  -- (3) el `substfc` EXTERNO sobre el código explícito
  have hout : Prf (substfc zero B
      (eqCodeFn (addcT (tcFn a) (succcT (varc (numeral 0))))
                (succcT (addcT (tcFn a) (varc (numeral 0)))))
      =eq eqCodeFn (addcT (tcFn a) (succcT B)) (succcT (addcT (tcFn a) B))) := by
    refine prf_eq_trans
      (prf_substfc_eq zero B (addcT (tcFn a) (succcT (varc (numeral 0))))
        (succcT (addcT (tcFn a) (varc (numeral 0))))) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · -- lado izquierdo: ȧ + σ v₀  ↦  ȧ + σ ḃ
      refine prf_eq_trans (prf_substtc_addcT zero B (tcFn a) (succcT (varc (numeral 0)))) ?_
      refine prf_congr_addcT (prf_substtc_tcFn B a) ?_
      exact prf_eq_trans (prf_substtc_succcT zero B (varc (numeral 0)))
        (prf_congr_succcT (prf_substtc_varc0 B))
    · -- lado derecho: σ(ȧ + v₀)  ↦  σ(ȧ + ḃ)
      refine prf_eq_trans (prf_substtc_succcT zero B (addcT (tcFn a) (varc (numeral 0)))) ?_
      refine prf_congr_succcT ?_
      exact prf_eq_trans (prf_substtc_addcT zero B (tcFn a) (varc (numeral 0)))
        (prf_congr_addcT (prf_substtc_tcFn B a) (prf_substtc_varc0 B))
  -- (4) ensamblar: transporta la instancia de `ax5` por toda la cadena de igualdades de código
  have hchain : Prf (substfc zero B (substfc (succ zero) W1
      (formCode (add (.var 1) (succ (.var 0)) =eq succ (add (.var 1) (.var 0)))))
      =eq eqCodeFn (addcT (tcFn a) (succcT B)) (succcT (addcT (tcFn a) B))) :=
    prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hout
  exact prf_mp (prf_provCode_congr hchain) (pcc_ax5_inst (tcFn a) B)

end ROBINSON_PlusPlus.Meta.EvalArithPrf

export ROBINSON_PlusPlus.Meta.EvalArithPrf (
  addcT addcT_termCode prf_congr_addcT
  evalAddCode pcc_ax4_computed pcc_eval_add_zero
  succcT prf_tc_succ' prf_congr_succcT
  prf_substtc_funcc1 prf_substtc_funcc2 prf_substtc_succcT prf_substtc_addcT prf_substtc_varc0
  pcc_ax5_computed
)
