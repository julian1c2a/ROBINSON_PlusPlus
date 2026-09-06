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
open ROBINSON_PlusPlus.Meta.DerivCondPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction

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
    (pcc_ax4_inst (tcFn a) (prf_hasWit_tcFn (liftTerm 0 a)))

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

/-! ### El KIT TERNARIO — `funcc3` y la imagen DOTADA de `substfc`

    ⚠️ **Bajado de `sondeos/SubstfcPlanos.lean` en B3 (2026‑09‑04), y AQUI porque este es su
    sitio mas alto posible**: `prf_substtc_funcc3`/`prf_congr_funcc3` son el escalon ternario
    del binario que ya vivia justo arriba, y no mencionan nada del frente `substfc`.

    🔑 **Es lo que mas paga de todo el sondeo**: `prf_substtc_funcc3` y `prf_congr_funcc3`
    estan copiados a mano en **NUEVE** sondeos cada uno. Promoverlos una vez los quita de
    todos ellos.

    ⛔ **`substfcT` es una DEFINICION y se queda en definicion.** Postular su ecuacion de
    recursion como axioma OBJETO (`ax_tc_substfc`) hace la teoria **INCONSISTENTE** —
    derivacion guardada en el proyecto. `substfcT_termCode` es un puente `:= rfl`, no un
    axioma; esa es toda la diferencia. -/

theorem prf_substtc_funcc3 (v W sc x y z : Term) :
    Prf (substtc v W (funcc sc (cons x (cons y (cons z nil))))
      =eq funcc sc (cons (substtc v W x) (cons (substtc v W y) (cons (substtc v W z) nil)))) :=
  prf_eq_trans (prf_substtc_func v W sc (cons x (cons y (cons z nil))))
    (prf_congr_funcc2
      (prf_eq_trans (prf_substtsc_cons v W x (cons y (cons z nil)))
        (prf_congr_cons_tail
          (prf_eq_trans (prf_substtsc_cons v W y (cons z nil))
            (prf_congr_cons_tail
              (prf_eq_trans (prf_substtsc_cons v W z nil)
                (prf_congr_cons_tail (prf_substtsc_nil v W))))))))

theorem prf_congr_funcc3 {sc x x' y y' z z' : Term}
    (hx : Prf (x =eq x')) (hy : Prf (y =eq y')) (hz : Prf (z =eq z')) :
    Prf (funcc sc (cons x (cons y (cons z nil)))
      =eq funcc sc (cons x' (cons y' (cons z' nil)))) :=
  prf_congr_funcc2 (prf_eq_trans (prf_congr_cons_head hx)
    (prf_congr_cons_tail (prf_eq_trans (prf_congr_cons_head hy)
      (prf_congr_cons_tail (prf_congr_cons_head hz)))))

/-- El constructor de código `substfc` (DEFINICIÓN; ninguna ecuación suya se postula). -/
def substfcT (v s f : Term) : Term :=
  funcc (strCode "substfc") (cons v (cons s (cons f nil)))

theorem substfcT_termCode (v s f : Term) :
    substfcT (termCode v) (termCode s) (termCode f) = termCode (substfc v s f) := rfl

theorem prf_congr_substfcT {v v' s s' f f' : Term}
    (hv : Prf (v =eq v')) (hs : Prf (s =eq s')) (hf : Prf (f =eq f')) :
    Prf (substfcT v s f =eq substfcT v' s' f') := prf_congr_funcc3 hv hs hf

theorem prf_substtc_substfcT (v W x y z : Term) :
    Prf (substtc v W (substfcT x y z)
      =eq substfcT (substtc v W x) (substtc v W y) (substtc v W z)) :=
  prf_substtc_funcc3 v W (strCode "substfc") x y z

theorem substtc_inv_substfcT {X Y Z : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y))
    (hZ : ∀ W, Prf (substtc zero W Z =eq Z)) :
    ∀ W, Prf (substtc zero W (substfcT X Y Z) =eq substfcT X Y Z) := fun W =>
  prf_eq_trans (prf_substtc_substfcT zero W X Y Z) (prf_congr_substfcT (hX W) (hY W) (hZ W))

theorem liftTerm_substfcT (k : Nat) (v s f : Term) :
    liftTerm k (substfcT v s f) = substfcT (liftTerm k v) (liftTerm k s) (liftTerm k f) := by
  simp only [substfcT, funcc, cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_strCode]
theorem substTerm_substfcT (k : Nat) (u v s f : Term) :
    substTerm k u (substfcT v s f)
      = substfcT (substTerm k u v) (substTerm k u s) (substTerm k u f) := by
  simp only [substfcT, funcc, cons, nil, zero, succ, substTerm, substTerms, substTerm_strCode]

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
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_ax5_inst (tcFn a) B (prf_hasWit_tcFn (liftTerm 0 a)) (prf_hasWit_tcFn (liftTerm 0 b)))

/-! ### Lógica ecuacional INTERNA sobre códigos (§25.4)

Con **`pcc_leibniz_code`** (Leibniz codificado, testigo de una línea, §25.2) y **`pcc_mp_code_open`**
(MP con códigos abiertos, §25.3) se razona ecuacionalmente **dentro de `Prov`**.

Una restricción real: al sustituir en el código‑contexto `Ac`, el `substtc` alcanza también los
subtérminos ya presentes. Por eso los lemas piden que el código fijo sea **`substtc`‑invariante**
(`∀ W, substtc zero W X =eq X`), hipótesis que (A) (`prf_substtc_tcFn`) y las ecuaciones de `funcc`
descargan para todos los códigos que construimos (`tcFn`, `addcT`, `succcT`). -/

/-! #### La GUARDA de los códigos que construimos (ADR-020)

Espejo exacto de las invariancias `substtc_inv_*`: los lemas de abajo piden que el código lleve
testigo, y como `addcT`/`succcT` son `funcc` de aridad 2 y 1, los paga **la escalera de aridad**
(`Meta/SubstfcWitnessPrf.lean` §28) en una línea cada uno. -/

/-- `succcT X` tiene testigo si `X` lo tiene. -/
theorem prf_hasWit_succcT {X : Term} (hX : Prf (hasWit X)) : Prf (hasWit (succcT X)) :=
  prf_hasWit_funcc1 (strCode succ_sym) X hX

/-- `addcT X Y` tiene testigo si lo tienen sus dos argumentos. -/
theorem prf_hasWit_addcT {X Y : Term} (hX : Prf (hasWit X)) (hY : Prf (hasWit Y)) :
    Prf (hasWit (addcT X Y)) :=
  prf_hasWit_funcc2 (strCode add_sym) X Y hX hY

/-- **Leibniz codificado, aplicado**: de `Prov(⌜t₁ = t₂⌝)` y `Prov(⌜Ac[t₁]⌝)` sale `Prov(⌜Ac[t₂]⌝)`.
    Dos usos de `pcc_mp_code_open` sobre `pcc_leibniz_code`. -/
theorem pcc_leibniz_apply (Ac t₁ t₂ : Term)
    (hwA : Prf (hasWitF Ac)) (hw1 : Prf (hasWit t₁)) (hw2 : Prf (hasWit t₂))
    (heq : Prf (provFromCode (eqc t₁ t₂)))
    (h1 : Prf (provFromCode (substfc zero t₁ Ac))) :
    Prf (provFromCode (substfc zero t₂ Ac)) :=
  pcc_mp_code_apply
    (pcc_mp_code_apply (pcc_leibniz_code Ac t₁ t₂ hwA hw1 hw2) heq)
    h1

/-- **Transitividad interna de `=`** sobre códigos: `Prov(⌜X=Y⌝) → Prov(⌜Y=Z⌝) → Prov(⌜X=Z⌝)`.
    Leibniz con el contexto `Ac := (X = v₀)`, sustituyendo `v₀ ↦ Y` y luego `v₀ ↦ Z`. -/
theorem pcc_eq_trans_code (X Y Z : Term) (hX : ∀ W, Prf (substtc zero W X =eq X))
    (hwX : Prf (hasWit X)) (hwY : Prf (hasWit Y)) (hwZ : Prf (hasWit Z))
    (h1 : Prf (provFromCode (eqc X Y))) (h2 : Prf (provFromCode (eqc Y Z))) :
    Prf (provFromCode (eqc X Z)) := by
  let Ac : Term := eqc X (varc (numeral 0))
  have hcomp : ∀ t : Term, Prf (substfc zero t Ac =eq eqc X t) := fun t =>
    prf_eq_trans (prf_substfc_eq zero t X (varc (numeral 0)))
      (prf_congr_eqCodeFn (hX t) (prf_substtc_varc0 t))
  have hY : Prf (provFromCode (substfc zero Y Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp Y))) h1
  have hZ : Prf (provFromCode (substfc zero Z Ac)) :=
    pcc_leibniz_apply Ac Y Z
      (prf_hasWitF_eq2 X (varc (numeral 0)) hwX (prf_hasWit_varc (numeral 0))) hwY hwZ h2 hY
  exact prf_mp (prf_provCode_congr (hcomp Z)) hZ

/-- **Congruencia interna de `σ`** sobre códigos: `Prov(⌜X=Y⌝) → Prov(⌜σX = σY⌝)`.
    Leibniz con el contexto `Ac := (σX = σv₀)`; la base `Ac[X]` es la **reflexividad codificada**
    (`prf_provFromCode_eqCodeFn_refl`, libre de muro). -/
theorem pcc_congr_succ_code (X Y : Term) (hX : ∀ W, Prf (substtc zero W X =eq X))
    (hwX : Prf (hasWit X)) (hwY : Prf (hasWit Y))
    (heq : Prf (provFromCode (eqc X Y))) :
    Prf (provFromCode (eqc (succcT X) (succcT Y))) := by
  let Ac : Term := eqc (succcT X) (succcT (varc (numeral 0)))
  have hcomp : ∀ t : Term, Prf (substfc zero t Ac =eq eqc (succcT X) (succcT t)) := by
    intro t
    refine prf_eq_trans (prf_substfc_eq zero t (succcT X) (succcT (varc (numeral 0)))) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_succcT zero t X) (prf_congr_succcT (hX t))
    · exact prf_eq_trans (prf_substtc_succcT zero t (varc (numeral 0)))
        (prf_congr_succcT (prf_substtc_varc0 t))
  have hrefl : Prf (provFromCode (eqc (succcT X) (succcT X))) :=
    prf_provFromCode_eqCodeFn_refl (succcT X)
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X))) hrefl
  have hAY : Prf (provFromCode (substfc zero Y Ac)) :=
    pcc_leibniz_apply Ac X Y
      (prf_hasWitF_eq2 (succcT X) (succcT (varc (numeral 0))) (prf_hasWit_succcT hwX)
        (prf_hasWit_succcT (prf_hasWit_varc (numeral 0)))) hwX hwY heq hAX
  exact prf_mp (prf_provCode_congr (hcomp Y)) hAY

/-! #### Invariancias `substtc` de los códigos que usamos (descargan `hX`) -/

/-- `tcFn a` es `substtc`‑invariante (es (A), `prf_substtc_tcFn`). -/
theorem substtc_inv_tcFn (a : Term) : ∀ W, Prf (substtc zero W (tcFn a) =eq tcFn a) :=
  fun W => prf_substtc_tcFn W a

/-- `succcT X` es `substtc`‑invariante si `X` lo es. -/
theorem substtc_inv_succcT {X : Term} (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    ∀ W, Prf (substtc zero W (succcT X) =eq succcT X) :=
  fun W => prf_eq_trans (prf_substtc_succcT zero W X) (prf_congr_succcT (hX W))

/-- `addcT X Y` es `substtc`‑invariante si `X` e `Y` lo son. -/
theorem substtc_inv_addcT {X Y : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y)) :
    ∀ W, Prf (substtc zero W (addcT X Y) =eq addcT X Y) :=
  fun W => prf_eq_trans (prf_substtc_addcT zero W X Y) (prf_congr_addcT (hX W) (hY W))

/-! ### Formas IMPLICACIÓN de los combinadores internos

`prf_nat_induction` exige el paso como `Prf (Φ ⇒ Φ[σ#0])`, no como una función `Prf → Prf`. Los
combinadores internos ya son implicaciones por dentro (`pcc_mp_code_open`), así que basta reordenar. -/

/-- Leibniz aplicado, en forma implicación sobre la **igualdad** (la premisa `Ac[t₁]` va cerrada). -/
theorem pcc_leibniz_apply_imp (Ac t₁ t₂ : Term)
    (hwA : Prf (hasWitF Ac)) (hw1 : Prf (hasWit t₁)) (hw2 : Prf (hasWit t₂))
    (h1 : Prf (provFromCode (substfc zero t₁ Ac))) :
    Prf (provFromCode (eqc t₁ t₂) ⇒ provFromCode (substfc zero t₂ Ac)) := by
  have hI : Prf (provFromCode (eqc t₁ t₂)
      ⇒ provFromCode (implc (substfc zero t₁ Ac) (substfc zero t₂ Ac))) :=
    prf_mp (pcc_mp_code_open (eqc t₁ t₂)
      (implc (substfc zero t₁ Ac) (substfc zero t₂ Ac))) (pcc_leibniz_code Ac t₁ t₂ hwA hw1 hw2)
  refine prf_deduction ?_
  have himp := PrfH.mp _ _ _ (prf_to_prfH hI _) (prfH_hyp_self (provFromCode (eqc t₁ t₂)))
  exact PrfH.mp _ _ _
    (PrfH.mp _ _ _ (prf_to_prfH (pcc_mp_code_open (substfc zero t₁ Ac) (substfc zero t₂ Ac)) _)
      himp)
    (prf_to_prfH h1 _)

/-- **Transitividad interna**, en forma implicación sobre la segunda igualdad. -/
theorem pcc_eq_trans_code_imp (X Y Z : Term) (hX : ∀ W, Prf (substtc zero W X =eq X))
    (hwX : Prf (hasWit X)) (hwY : Prf (hasWit Y)) (hwZ : Prf (hasWit Z))
    (h1 : Prf (provFromCode (eqc X Y))) :
    Prf (provFromCode (eqc Y Z) ⇒ provFromCode (eqc X Z)) := by
  let Ac : Term := eqc X (varc (numeral 0))
  have hcomp : ∀ t : Term, Prf (substfc zero t Ac =eq eqc X t) := fun t =>
    prf_eq_trans (prf_substfc_eq zero t X (varc (numeral 0)))
      (prf_congr_eqCodeFn (hX t) (prf_substtc_varc0 t))
  have hY : Prf (provFromCode (substfc zero Y Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp Y))) h1
  have himp : Prf (provFromCode (eqc Y Z) ⇒ provFromCode (substfc zero Z Ac)) :=
    pcc_leibniz_apply_imp Ac Y Z
      (prf_hasWitF_eq2 X (varc (numeral 0)) hwX (prf_hasWit_varc (numeral 0))) hwY hwZ hY
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Z)) _)
    (PrfH.mp _ _ _ (prf_to_prfH himp _) (prfH_hyp_self _))

/-- **Congruencia interna de `σ`**, en forma implicación. -/
theorem pcc_congr_succ_code_imp (X Y : Term) (hX : ∀ W, Prf (substtc zero W X =eq X))
    (hwX : Prf (hasWit X)) (hwY : Prf (hasWit Y)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (succcT X) (succcT Y))) := by
  let Ac : Term := eqc (succcT X) (succcT (varc (numeral 0)))
  have hcomp : ∀ t : Term, Prf (substfc zero t Ac =eq eqc (succcT X) (succcT t)) := by
    intro t
    refine prf_eq_trans (prf_substfc_eq zero t (succcT X) (succcT (varc (numeral 0)))) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_succcT zero t X) (prf_congr_succcT (hX t))
    · exact prf_eq_trans (prf_substtc_succcT zero t (varc (numeral 0)))
        (prf_congr_succcT (prf_substtc_varc0 t))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (succcT X))
  have himp : Prf (provFromCode (eqc X Y) ⇒ provFromCode (substfc zero Y Ac)) :=
    pcc_leibniz_apply_imp Ac X Y
      (prf_hasWitF_eq2 (succcT X) (succcT (varc (numeral 0))) (prf_hasWit_succcT hwX)
        (prf_hasWit_succcT (prf_hasWit_varc (numeral 0)))) hwX hwY hAX
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH.mp _ _ _ (prf_to_prfH himp _) (prfH_hyp_self _))

/-! ### PASO INDUCTIVO de `+` -/

/-- **Paso inductivo de la evaluación provable de `+`**:
    `⊢ Prov(⌜ȧ + ḃ = (a+b)˙⌝) ⇒ Prov(⌜ȧ + (σb)˙ = (a+σb)˙⌝)`.

    Cadena: `pcc_congr_succ_code_imp` sobre la HI, luego `pcc_eq_trans_code_imp` con (B)
    (`pcc_ax5_computed`), y finalmente transporte de códigos con `prf_tc_succ'` y `prf_congr_tcFn`
    sobre `prf_add_succ_t` (`add a (σb) =eq σ(a+b)`). -/
theorem pcc_eval_add_succ_imp (a b : Term) :
    Prf (provFromCode (evalAddCode a b) ⇒ provFromCode (evalAddCode a (succ b))) := by
  -- invariancias `substtc` (descargadas por (A) + ecuaciones de `funcc`)
  have hinvAB : ∀ W, Prf (substtc zero W (addcT (tcFn a) (tcFn b)) =eq addcT (tcFn a) (tcFn b)) :=
    substtc_inv_addcT (substtc_inv_tcFn a) (substtc_inv_tcFn b)
  have hinvX : ∀ W, Prf (substtc zero W (addcT (tcFn a) (succcT (tcFn b)))
      =eq addcT (tcFn a) (succcT (tcFn b))) :=
    substtc_inv_addcT (substtc_inv_tcFn a) (substtc_inv_succcT (substtc_inv_tcFn b))
  -- HI ⇒ `Prov(⌜σ(ȧ+ḃ) = σ((a+b)˙)⌝)`
  have hcs : Prf (provFromCode (eqc (addcT (tcFn a) (tcFn b)) (tcFn (add a b)))
      ⇒ provFromCode (eqc (succcT (addcT (tcFn a) (tcFn b))) (succcT (tcFn (add a b))))) :=
    pcc_congr_succ_code_imp _ _ hinvAB
      (prf_hasWit_addcT (prf_hasWit_tcFn a) (prf_hasWit_tcFn b)) (prf_hasWit_tcFn (add a b))
  -- (B) + transitividad
  have htr : Prf (provFromCode (eqc (succcT (addcT (tcFn a) (tcFn b))) (succcT (tcFn (add a b))))
      ⇒ provFromCode (eqc (addcT (tcFn a) (succcT (tcFn b))) (succcT (tcFn (add a b))))) :=
    pcc_eq_trans_code_imp _ _ _ hinvX
      (prf_hasWit_addcT (prf_hasWit_tcFn a) (prf_hasWit_succcT (prf_hasWit_tcFn b)))
      (prf_hasWit_succcT (prf_hasWit_addcT (prf_hasWit_tcFn a) (prf_hasWit_tcFn b)))
      (prf_hasWit_succcT (prf_hasWit_tcFn (add a b)))
      (pcc_ax5_computed a b)
  -- transporte final de códigos: `succcT ḃ =eq (σb)˙` y `σ((a+b)˙) =eq (a+σb)˙`
  have hcode : Prf (eqc (addcT (tcFn a) (succcT (tcFn b))) (succcT (tcFn (add a b)))
      =eq evalAddCode a (succ b)) :=
    prf_congr_eqCodeFn
      (prf_congr_addcT (prf_refl (tcFn a)) (prf_eq_symm (prf_tc_succ' b)))
      (prf_eq_symm (prf_eq_trans (prf_congr_tcFn (prf_add_succ_t a b)) (prf_tc_succ' (add a b))))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr hcode) _)
    (PrfH.mp _ _ _ (prf_to_prfH htr _)
      (PrfH.mp _ _ _ (prf_to_prfH hcs _) (prfH_hyp_self _)))

/-! ### Inducción object: la evaluación provable de `+`, COMPLETA

`prf_nat_induction` trabaja con `substFormula`/`liftFormula` sobre el predicado. Con
`substFormula_provFromCode_open` / `liftFormula_provFromCode_open` todo cae **sobre el código**, y
`evalAddCode` es transparente a `substTerm`/`liftTerm` (sus constantes — `numeral 4`, `strCode +`,
`cons`, `nil` — son cerradas). Esos dos lemas de transporte hacen la inducción rutinaria. -/

/-- `substTerm` atraviesa `evalAddCode` (las constantes de código son cerradas). -/
theorem substTerm_evalAddCode (v : Nat) (s X Y : Term) :
    substTerm v s (evalAddCode X Y)
      = evalAddCode (substTerm v s X) (substTerm v s Y) := by
  simp only [evalAddCode, eqCodeFn, addcT, succcT, funcc, tcFn, add, cons, nil, zero, succ,
    substTerm, substTerms, substTerm_numeral, substTerm_strCode]

/-- `liftTerm` atraviesa `evalAddCode`. -/
theorem liftTerm_evalAddCode (k : Nat) (X Y : Term) :
    liftTerm k (evalAddCode X Y) = evalAddCode (liftTerm k X) (liftTerm k Y) := by
  simp only [evalAddCode, eqCodeFn, addcT, succcT, funcc, tcFn, add, cons, nil, zero, succ,
    liftTerm, liftTerms, liftTerm_numeral, liftTerm_strCode]

/-- Predicado inductivo `Ψ(b) = Prov(⌜ȧ + ḃ = (a+b)˙⌝)` (`b` = `#0`; `a` liftado). -/
def evalAddPred (a : Term) : Formula := provFromCode (evalAddCode (liftTerm 0 a) (.var 0))

/-- Instanciar `Ψ` en un término `b` devuelve exactamente `provFromCode (evalAddCode a b)`. -/
theorem substFormula_evalAddPred (a b : Term) :
    substFormula 0 b (evalAddPred a) = provFromCode (evalAddCode a b) := by
  simp only [evalAddPred, substFormula_provFromCode_open, substTerm_evalAddCode, substTerm,
    reduceIte, FOL.substTerm_liftTerm]

/-- El paso de `prf_nat_induction` sobre `Ψ`: el `liftFormula 1` seguido del `substFormula 0 (σ#0)`
    devuelve `Ψ` con el argumento `σ#0` (el `a` liftado sobrevive: `↑₁↑₀a` es `↑₀↑₀a` por
    `liftTerm_comm_zero`, y el `substTerm 0` lo cancela). -/
theorem step_evalAddPred (a : Term) :
    substFormula 0 (succ (.var 0)) (liftFormula 1 (provFromCode (evalAddCode (liftTerm 0 a) (.var 0))))
      = provFromCode (evalAddCode (liftTerm 0 a) (succ (.var 0))) := by
  rw [liftFormula_provFromCode_open, liftTerm_evalAddCode, substFormula_provFromCode_open,
    substTerm_evalAddCode, ← FOL.liftTerm_comm_zero a 0, FOL.substTerm_liftTerm]
  simp only [liftTerm, substTerm, Nat.zero_lt_one, reduceIte, Nat.lt_irrefl, if_true]

/-- **EVALUACIÓN PROVABLE DE `+` (∀ object)**: `⊢ ∀b. Prov(⌜ȧ + ḃ = (a+b)˙⌝)`.

    Inducción interna (`prf_nat_induction`): base `pcc_eval_add_zero`, paso `pcc_eval_add_succ_imp`.
    Es la **primera** evaluación provable completa del proyecto: cierra el hueco que §18 identificó
    como «la bestia» para el símbolo `+`. -/
theorem prf_eval_add_all (a : Term) : Prf (Formula.forall (evalAddPred a)) := by
  refine prf_nat_induction (evalAddPred a) ?base ?step
  · rw [substFormula_evalAddPred]
    exact pcc_eval_add_zero a
  · refine Prf.gen _ ?_
    show Prf (Formula.impl (provFromCode (evalAddCode (liftTerm 0 a) (.var 0)))
      (substFormula 0 (succ (.var 0))
        (liftFormula 1 (provFromCode (evalAddCode (liftTerm 0 a) (.var 0))))))
    rw [step_evalAddPred]
    exact pcc_eval_add_succ_imp (liftTerm 0 a) (.var 0)

/-- **EVALUACIÓN PROVABLE DE `+`**: `⊢ Prov(⌜ȧ + ḃ = (a+b)˙⌝)` para `a`, `b` **arbitrarios**.
    Instancia del `∀` object. -/
theorem pcc_eval_add (a b : Term) : Prf (provFromCode (evalAddCode a b)) := by
  have h := prf_spec (prf_eval_add_all a) b
  rwa [substFormula_evalAddPred] at h

end ROBINSON_PlusPlus.Meta.EvalArithPrf

export ROBINSON_PlusPlus.Meta.EvalArithPrf (
  addcT addcT_termCode prf_congr_addcT
  evalAddCode pcc_ax4_computed pcc_eval_add_zero
  succcT prf_tc_succ' prf_congr_succcT
  prf_substtc_funcc1 prf_substtc_funcc2 prf_substtc_succcT prf_substtc_addcT prf_substtc_varc0
  -- KIT TERNARIO, bajado en B3 (2026-09-04). Retira 74 copias a mano repartidas por
  -- `sondeos/`: `substfcT` estaba en ONCE sondeos y los dos `funcc3` en NUEVE cada uno.
  prf_substtc_funcc3 prf_congr_funcc3
  substfcT substfcT_termCode prf_congr_substfcT prf_substtc_substfcT substtc_inv_substfcT
  liftTerm_substfcT substTerm_substfcT
  pcc_ax5_computed
  pcc_leibniz_apply pcc_eq_trans_code pcc_congr_succ_code
  substtc_inv_tcFn substtc_inv_succcT substtc_inv_addcT
  pcc_leibniz_apply_imp pcc_eq_trans_code_imp pcc_congr_succ_code_imp
  substTerm_evalAddCode liftTerm_evalAddCode evalAddPred substFormula_evalAddPred
  step_evalAddPred pcc_eval_add_succ_imp prf_eval_add_all pcc_eval_add
)
