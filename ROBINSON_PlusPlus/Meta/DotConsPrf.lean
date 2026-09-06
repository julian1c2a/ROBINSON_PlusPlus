/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.EvalMulPrf
import ROBINSON_PlusPlus.Meta.Div2ParityPrf
import ROBINSON_PlusPlus.Meta.CantorMonoPrf
import ROBINSON_PlusPlus.Meta.MpCodePrf
import ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
import ROBINSON_PlusPlus.Meta.NumCodeClosedPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.NatArithPrf
open ROBINSON_PlusPlus.Meta.NatMulPrf
open ROBINSON_PlusPlus.Meta.CantorMonoPrf
open ROBINSON_PlusPlus.Meta.Div2ParityPrf
open ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
open ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.MpCodePrf
open ROBINSON_PlusPlus.Meta.DerivCondPrf
open ROBINSON_PlusPlus.Meta.EvalArithPrf
open ROBINSON_PlusPlus.Meta.EvalMulPrf

set_option maxHeartbeats 1000000

namespace ROBINSON_PlusPlus.Meta.DotConsPrf

/-!
## META — **`pcc_dot_cons`**: `⊢ Prov(⌈ cons(ḣ, ṫ) = (cons h t)˙ ⌉)`

**Cuarto y último peldaño de la escalera (a.2)** (`PLAN-FRENTE-A.md`). Es `prf_cons_eval`
**internalizado y para argumentos ABSTRACTOS**: no habla de `numeral a`/`numeral b` concretos, sino
de dos términos objeto cualesquiera. Con él, `pcc_eval_carc` se reconstruye como
`pcc_axiom_inst ax_carc` + este puente.

### Por qué se puede sin inducción

`cons` no tiene ecuaciones recursivas propias: `ax_L0_cons_def` lo **define** como
`pair h (σt) = div2 (cantor_poly h (σt))`, o sea puro `+`, `·` y `div2`. Y los tres ya están
internalizados (`pcc_eval_add`, `pcc_eval_mul`, y `div2` por `pcc_thm_inst`). El trabajo, por tanto,
es **ensamblaje**, no inducción: se evalúa el polinomio dentro de `Prov` y se cancela el `div2`.

### Las tres fases

* **(A)** la instancia codificada de `ax_L0_cons_def` **computa** por `rfl` (igual que `ax5`/`ax9`),
  vía `prf_substfc_arith_open` ⇒ `Prov(⌜ cons(ḣ,ṫ) = div2(cpOfT ḣ ṫ) ⌝)`;
* **(B)** el polinomio se evalúa dentro de `Prov` en cinco pasos, alternando reescrituras
  **internas** (`pcc_rw`, que es Leibniz codificado) con reescrituras **de código**, que son gratis
  (`succcT (tcFn x) = tcFn (σx)` es `prf_tc_succ'`, y `tcFn` es congruente);
* **(C)** el `div2` se cancela contra `prf_div2_double`, subido a ∀ objeto con `Prf.gen` y metido en
  `Prov` con `pcc_thm_inst` en el testigo `(cons h t)˙`; el puente con el polinomio es
  **`prf_cons_double`**, que es un teorema OBJETO y por tanto se dota con `prf_congr_tcFn`, gratis.

### La pieza clave del diseño: `pcc_rw` cubre las ocurrencias REPETIDAS

El polinomio `(x+y)·σ(x+y) + 2y` menciona `x+y` **dos veces**. Reescribir por posiciones exigiría
congruencias a cada profundidad. Pero `substfc` sustituye **todas** las ocurrencias del hueco a la
vez, así que un único `pcc_leibniz_apply` con el contexto `Ac := C[v₀]` las cierra ambas de un golpe.
Ése es el motivo de que la fase (B) sean cinco pasos y no quince.
-/

/-! ### Constructores de código para `cons` y `div2` -/

/-- Código del término `cons x y`. -/
def consT (x y : Term) : Term := funcc (strCode cons_sym) (cons x (cons y nil))

/-- Código del término `div2 x`. -/
def div2cT (x : Term) : Term := funcc (strCode div2_sym) (cons x nil)

/-- `consT X Y` tiene testigo si lo tienen sus dos argumentos (escalera de aridad, §28). -/
theorem prf_hasWit_consT {X Y : Term} (hX : Prf (hasWit X)) (hY : Prf (hasWit Y)) :
    Prf (hasWit (consT X Y)) :=
  prf_hasWit_funcc2 (strCode cons_sym) X Y hX hY

/-- `div2cT X` tiene testigo si `X` lo tiene. -/
theorem prf_hasWit_div2cT {X : Term} (hX : Prf (hasWit X)) : Prf (hasWit (div2cT X)) :=
  prf_hasWit_funcc1 (strCode div2_sym) X hX

theorem prf_congr_consT {x x' y y' : Term} (hx : Prf (x =eq x')) (hy : Prf (y =eq y')) :
    Prf (consT x y =eq consT x' y') := by
  unfold consT funcc
  exact prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head
    (prf_eq_trans (prf_congr_cons_head hx) (prf_congr_cons_tail (prf_congr_cons_head hy)))))

theorem prf_congr_div2cT {x y : Term} (h : Prf (x =eq y)) :
    Prf (div2cT x =eq div2cT y) :=
  prf_congr_funcc2 (prf_congr_cons_head h)

theorem prf_substtc_consT (v W x y : Term) :
    Prf (substtc v W (consT x y) =eq consT (substtc v W x) (substtc v W y)) :=
  prf_substtc_funcc2 v W (strCode cons_sym) x y

theorem prf_substtc_div2cT (v W x : Term) :
    Prf (substtc v W (div2cT x) =eq div2cT (substtc v W x)) :=
  prf_substtc_funcc1 v W (strCode div2_sym) x

theorem substtc_inv_consT {X Y : Term} (hX : ∀ W, Prf (substtc zero W X =eq X))
    (hY : ∀ W, Prf (substtc zero W Y =eq Y)) :
    ∀ W, Prf (substtc zero W (consT X Y) =eq consT X Y) :=
  fun W => prf_eq_trans (prf_substtc_consT zero W X Y) (prf_congr_consT (hX W) (hY W))

theorem substtc_inv_div2cT {X : Term} (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    ∀ W, Prf (substtc zero W (div2cT X) =eq div2cT X) :=
  fun W => prf_eq_trans (prf_substtc_div2cT zero W X) (prf_congr_div2cT (hX W))

/-- `⌜2⌝` es `substtc`‑invariante: `two` es cerrado. -/
theorem prf_substtc_two (W : Term) : Prf (substtc zero W (termCode two) =eq termCode two) := by
  have h := prf_substtc_arith_open 0 W two
  rw [substCodeT_closed 0 W two (fun _ => rfl)] at h
  exact h

/-- `⌜2⌝ = 2˙`: `two` es el numeral 2, así que vale `prf_tc_numeral`. -/
theorem prf_tc_two : Prf (tcFn two =eq termCode two) := prf_tc_numeral 2

/-! ### FASE A — la instancia codificada de `ax_L0_cons_def`, computada

`ax_L0_cons_def : ∀∀. cons #1 #0 = pair #1 (σ#0)`, y `pair x y` se despliega a
`div2 (cantor_poly x y)`. Espejo de `pcc_ax9_computed`: `substCodeF` computa el cuerpo por `rfl`,
se normaliza el `liftc zero (tcFn h)` con (A), y el `substfc` externo se computa sobre el código
explícito. -/

/-- El código del polinomio de Cantor de `⟨X,Y⟩`, con los argumentos ya codificados. -/
def cpOfT (X Y : Term) : Term :=
  addcT (mulcT (addcT X (succcT Y)) (succcT (addcT X (succcT Y))))
        (mulcT (termCode two) (succcT Y))

theorem prf_congr_cpOfT {X X' Y Y' : Term} (hx : Prf (X =eq X')) (hy : Prf (Y =eq Y')) :
    Prf (cpOfT X Y =eq cpOfT X' Y') := by
  unfold cpOfT
  refine prf_congr_addcT ?_ (prf_congr_mulcT (prf_refl _) (prf_congr_succcT hy))
  exact prf_congr_mulcT (prf_congr_addcT hx (prf_congr_succcT hy))
    (prf_congr_succcT (prf_congr_addcT hx (prf_congr_succcT hy)))

theorem prf_substtc_cpOfT (W X Y : Term) :
    Prf (substtc zero W (cpOfT X Y)
      =eq cpOfT (substtc zero W X) (substtc zero W Y)) := by
  unfold cpOfT
  refine prf_eq_trans (prf_substtc_addcT zero W _ _) ?_
  refine prf_congr_addcT ?_ ?_
  · refine prf_eq_trans (prf_substtc_mulcT zero W _ _) ?_
    refine prf_congr_mulcT ?_ ?_
    · exact prf_eq_trans (prf_substtc_addcT zero W X (succcT Y))
        (prf_congr_addcT (prf_refl _)
          (prf_eq_trans (prf_substtc_succcT zero W Y) (prf_refl _)))
    · refine prf_eq_trans (prf_substtc_succcT zero W _) (prf_congr_succcT ?_)
      exact prf_eq_trans (prf_substtc_addcT zero W X (succcT Y))
        (prf_congr_addcT (prf_refl _)
          (prf_eq_trans (prf_substtc_succcT zero W Y) (prf_refl _)))
  · refine prf_eq_trans (prf_substtc_mulcT zero W _ _) ?_
    exact prf_congr_mulcT (prf_substtc_two W)
      (prf_eq_trans (prf_substtc_succcT zero W Y) (prf_refl _))

theorem pcc_axL0_inst (w₁ w₂ : Term)
    (hw₁ : Prf (hasWit (liftTerm 0 w₁))) (hw₂ : Prf (hasWit (liftTerm 0 w₂))) :
    Prf (provFromCode (substfc zero w₂ (substfc (succ zero) (liftc zero w₁)
      (formCode (cons (.var 1) (.var 0) =eq pair (.var 1) (succ (.var 0))))))) :=
  pcc_axiom_inst2 _ (show ax_L0_cons_def ∈ axioms by simp [axioms]) w₁ w₂ hw₁ hw₂

/-- **`substCodeF` computa sobre el cuerpo de `ax_L0`**, igual que sobre `ax5`/`ax9`. Era la
    pregunta arriesgada de la fase A: si no computase, la instancia no sería barata. -/
theorem prf_axL0_body_computes (W1 : Term) :
    Prf (substfc (succ zero) W1
      (formCode (cons (.var 1) (.var 0) =eq pair (.var 1) (succ (.var 0))))
      =eq eqCodeFn (consT W1 (varc (numeral 0)))
                   (div2cT (cpOfT W1 (varc (numeral 0))))) :=
  prf_substfc_arith_open 1 W1 (cons (.var 1) (.var 0) =eq pair (.var 1) (succ (.var 0)))

/-- **FASE A** — `⊢ Prov(⌜ cons(ḣ,ṫ) = div2(cpOfT ḣ ṫ) ⌝)`. -/
theorem pcc_axL0_computed (h t : Term) :
    Prf (provFromCode (eqCodeFn (consT (tcFn h) (tcFn t))
      (div2cT (cpOfT (tcFn h) (tcFn t))))) := by
  let W1 : Term := liftc zero (tcFn h)
  let B : Term := tcFn t
  have hA : Prf (W1 =eq tcFn h) := prf_liftc_tcFn h
  have hin := prf_axL0_body_computes W1
  have hnorm : Prf (eqCodeFn (consT W1 (varc (numeral 0)))
                             (div2cT (cpOfT W1 (varc (numeral 0))))
      =eq eqCodeFn (consT (tcFn h) (varc (numeral 0)))
                   (div2cT (cpOfT (tcFn h) (varc (numeral 0))))) :=
    prf_congr_eqCodeFn (prf_congr_consT hA (prf_refl _))
      (prf_congr_div2cT (prf_congr_cpOfT hA (prf_refl _)))
  have hout : Prf (substfc zero B
      (eqCodeFn (consT (tcFn h) (varc (numeral 0)))
                (div2cT (cpOfT (tcFn h) (varc (numeral 0)))))
      =eq eqCodeFn (consT (tcFn h) B) (div2cT (cpOfT (tcFn h) B))) := by
    refine prf_eq_trans (prf_substfc_eq zero B _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_consT zero B (tcFn h) (varc (numeral 0)))
        (prf_congr_consT (prf_substtc_tcFn B h) (prf_substtc_varc0 B))
    · refine prf_eq_trans (prf_substtc_div2cT zero B _) (prf_congr_div2cT ?_)
      exact prf_eq_trans (prf_substtc_cpOfT B (tcFn h) (varc (numeral 0)))
        (prf_congr_cpOfT (prf_substtc_tcFn B h) (prf_substtc_varc0 B))
  exact prf_mp (prf_provCode_congr
    (prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hout))
    (pcc_axL0_inst (tcFn h) B (prf_hasWit_tcFn (liftTerm 0 h)) (prf_hasWit_tcFn (liftTerm 0 t)))

/-! ### FASE B — evaluar el polinomio de Cantor DENTRO de `Prov`

Herramienta genérica: reescribir `X` por `Y` en cualquier hueco de un código‑contexto, dado
`Prov(⌜X=Y⌝)`. Es `pcc_leibniz_apply` con el `substfc` computado a los dos lados. Como `substfc`
sustituye **todas** las ocurrencias del hueco, un solo paso cubre las repeticiones. -/

/-- **Reescritura interna en un hueco.** El contexto `G` se da como función; la hipótesis `hG` dice
    que el hueco `v₀` se computa al argumento, y la descargan las ecuaciones de `substtc`. -/
theorem pcc_rw (G : Term → Term)
    (hG : ∀ s : Term, Prf (substfc zero s (G (varc (numeral 0))) =eq G s))
    (X Y : Term) (heq : Prf (provFromCode (eqc X Y)))
    (hbase : Prf (provFromCode (G X)))
    (hwG : Prf (hasWitF (G (varc (numeral 0)))))
    (hwX : Prf (hasWit X)) (hwY : Prf (hasWit Y)) :
    Prf (provFromCode (G Y)) := by
  have h1 : Prf (provFromCode (substfc zero X (G (varc (numeral 0))))) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hG X))) hbase
  exact prf_mp (prf_provCode_congr (hG Y))
    (pcc_leibniz_apply _ X Y hwG hwX hwY heq h1)

/-- **`pcc_rw` en forma IMPLICACIÓN.** Mismo contrato, pero devolviendo la implicación en vez de
    consumir la base.

    Hace falta cuando el sitio a reescribir vive dentro de **`PrfH`** (el cálculo con contexto de
    hipótesis): allí la base no es un `Prf` pelado, así que un `Prf → Prf` no encaja y hay que
    entrar con `PrfH.mp` + `prf_to_prfH`. Es la misma maniobra que `EvalArithPrf` ya hizo para la
    inducción (`pcc_leibniz_apply_imp`, `pcc_eq_trans_code_imp`, `pcc_congr_succ_code_imp`).

    **Net‑0** (`[propext, choice, Quot.sound]`): la base sancionada entra por `heq`, no por aquí. -/
theorem pcc_rw_imp (G : Term → Term)
    (hG : ∀ s : Term, Prf (substfc zero s (G (varc (numeral 0))) =eq G s))
    (X Y : Term) (heq : Prf (provFromCode (eqc X Y)))
    (hwG : Prf (hasWitF (G (varc (numeral 0)))))
    (hwX : Prf (hasWit X)) (hwY : Prf (hasWit Y)) :
    Prf (provFromCode (G X) ⇒ provFromCode (G Y)) := by
  let Ac : Term := G (varc (numeral 0))
  -- (1) Leibniz codificado, ya aplicado a la igualdad: `Prov(⌜Ac[X] ⇒ Ac[Y]⌝)`
  have himp : Prf (provFromCode (implc (substfc zero X Ac) (substfc zero Y Ac))) :=
    pcc_mp_code_apply (pcc_leibniz_code Ac X Y hwG hwX hwY) heq
  -- (2) abrir el `implc` a implicación REAL
  have hopen : Prf (provFromCode (substfc zero X Ac) ⇒ provFromCode (substfc zero Y Ac)) :=
    prf_mp (pcc_mp_code_open _ _) himp
  -- (3) normalizar los dos `substfc` a `G X` / `G Y`
  refine prf_deduction ?_
  have h1 : PrfH [provFromCode (G X)] (provFromCode (substfc zero X Ac)) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_eq_symm (hG X))) _)
      (prfH_hyp_self (provFromCode (G X)))
  have h2 : PrfH [provFromCode (G X)] (provFromCode (substfc zero Y Ac)) :=
    PrfH.mp _ _ _ (prf_to_prfH hopen _) h1
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hG Y)) _) h2

/-- Reescritura dentro de `L = div2(D ·)`: el molde de los cuatro pasos internos de la fase B. -/
theorem pcc_rw_div2 (L : Term) (hL : ∀ W, Prf (substtc zero W L =eq L)) (D : Term → Term)
    (hD : ∀ s : Term, Prf (substtc zero s (D (varc (numeral 0))) =eq D s))
    (X Y : Term) (heq : Prf (provFromCode (eqc X Y)))
    (hbase : Prf (provFromCode (eqc L (div2cT (D X)))))
    (hwL : Prf (hasWit L)) (hwD : Prf (hasWit (D (varc (numeral 0)))))
    (hwX : Prf (hasWit X)) (hwY : Prf (hasWit Y)) :
    Prf (provFromCode (eqc L (div2cT (D Y)))) := by
  refine pcc_rw (fun s => eqc L (div2cT (D s))) ?_ X Y heq hbase
    (prf_hasWitF_eq2 L (div2cT (D (varc (numeral 0)))) hwL (prf_hasWit_div2cT hwD)) hwX hwY
  intro s
  refine prf_eq_trans (prf_substfc_eq zero s L (div2cT (D (varc (numeral 0))))) ?_
  exact prf_congr_eqCodeFn (hL s)
    (prf_eq_trans (prf_substtc_div2cT zero s (D (varc (numeral 0)))) (prf_congr_div2cT (hD s)))

/-- El polinomio ya con `σy` codificado de una pieza: `cpOfT X Y` es **defeq** a
    `cpOfT' X (succcT Y)`. Sirve para plegar `σ(ṫ)` en `(σt)˙` a nivel de código, gratis. -/
def cpOfT' (X Y1 : Term) : Term :=
  addcT (mulcT (addcT X Y1) (succcT (addcT X Y1))) (mulcT (termCode two) Y1)

theorem prf_congr_cpOfT2 {X Y Y' : Term} (hy : Prf (Y =eq Y')) :
    Prf (cpOfT' X Y =eq cpOfT' X Y') :=
  prf_congr_addcT
    (prf_congr_mulcT (prf_congr_addcT (prf_refl _) hy)
      (prf_congr_succcT (prf_congr_addcT (prf_refl _) hy)))
    (prf_congr_mulcT (prf_refl _) hy)

/-! ### FASE C — cerrar el `div2`

`prf_div2_double` sube a ∀ objeto con `Prf.gen` y `pcc_thm_inst` lo mete dentro de `Prov` en el
testigo `(cons h t)˙`. El puente con el polinomio es `prf_cons_double`, que es **objeto**, así que
se dota con `prf_congr_tcFn` — gratis, a nivel de código. -/

/-- **FASE C** — `⊢ Prov(⌜ div2((cpOf h t)˙) = (cons h t)˙ ⌝)`. -/
theorem pcc_div2_cons (h t : Term) :
    Prf (provFromCode (eqc (div2cT (tcFn (cpOf h t))) (tcFn (cons h t)))) := by
  have hdiv : Prf (provFromCode (substfc zero (tcFn (cons h t))
      (formCode (div2 (mul (.var 0) two) =eq (.var 0))))) :=
    pcc_thm_inst _ (Prf.gen _ (prf_div2_double (.var 0))) (tcFn (cons h t))
      (prf_hasWit_tcFn (liftTerm 0 (cons h t)))
  have hdivc := prf_substfc_arith_open 0 (tcFn (cons h t))
    (div2 (mul (.var 0) two) =eq (.var 0))
  have hdiv' : Prf (provFromCode
      (eqc (div2cT (mulcT (tcFn (cons h t)) (termCode two))) (tcFn (cons h t)))) :=
    prf_mp (prf_provCode_congr hdivc) hdiv
  have hcd : Prf (provFromCode
      (eqc (mulcT (tcFn (cons h t)) (termCode two)) (tcFn (cpOf h t)))) :=
    prf_mp (prf_provCode_congr (prf_congr_eqCodeFn
        (prf_congr_mulcT (prf_refl _) prf_tc_two)
        (prf_congr_tcFn (prf_cons_double h t))))
      (pcc_eval_mul (cons h t) two)
  refine pcc_rw (fun s => eqc (div2cT s) (tcFn (cons h t))) ?_ _ _ hcd hdiv'
    (prf_hasWitF_eq2 (div2cT (varc (numeral 0))) (tcFn (cons h t))
      (prf_hasWit_div2cT (prf_hasWit_varc (numeral 0))) (prf_hasWit_tcFn (cons h t)))
    (prf_hasWit_mulcT (prf_hasWit_tcFn (cons h t)) (prf_hasWit_tc two))
    (prf_hasWit_tcFn (cpOf h t))
  intro s
  refine prf_eq_trans (prf_substfc_eq zero s (div2cT (varc (numeral 0))) (tcFn (cons h t))) ?_
  exact prf_congr_eqCodeFn
    (prf_eq_trans (prf_substtc_div2cT zero s (varc (numeral 0)))
      (prf_congr_div2cT (prf_substtc_varc0 s)))
    (prf_substtc_tcFn s (cons h t))

/-! ### El ensamblaje -/

/-- **`pcc_dot_cons`** — cuarto peldaño de la escalera (a.2):
    `⊢ Prov(⌜ cons(ḣ, ṫ) = (cons h t)˙ ⌝)`, para `h`, `t` **arbitrarios**. -/
theorem pcc_dot_cons (h t : Term) :
    Prf (provFromCode (eqc (consT (tcFn h) (tcFn t)) (tcFn (cons h t)))) := by
  have hL : ∀ W, Prf (substtc zero W (consT (tcFn h) (tcFn t)) =eq consT (tcFn h) (tcFn t)) :=
    substtc_inv_consT (substtc_inv_tcFn h) (substtc_inv_tcFn t)
  -- testigos (ADR-020): el mismo reparto que las invariancias `substtc` de arriba
  have hv0 : Prf (hasWit (varc (numeral 0))) := prf_hasWit_varc (numeral 0)
  have hw2 : Prf (hasWit (termCode two)) := prf_hasWit_tc two
  have hwL : Prf (hasWit (consT (tcFn h) (tcFn t))) :=
    prf_hasWit_consT (prf_hasWit_tcFn h) (prf_hasWit_tcFn t)
  have hwQ2 : Prf (hasWit (mulcT (termCode two) (tcFn (succ t)))) :=
    prf_hasWit_mulcT hw2 (prf_hasWit_tcFn (succ t))
  have hQ2 : ∀ W, Prf (substtc zero W (mulcT (termCode two) (tcFn (succ t)))
      =eq mulcT (termCode two) (tcFn (succ t))) :=
    substtc_inv_mulcT prf_substtc_two (substtc_inv_tcFn (succ t))
  -- paso 0 (nivel código, gratis): `σ(ṫ)` se pliega en `(σt)˙`
  have h0 : Prf (provFromCode (eqc (consT (tcFn h) (tcFn t))
      (div2cT (cpOfT' (tcFn h) (tcFn (succ t)))))) :=
    prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
      (prf_congr_div2cT (prf_congr_cpOfT2 (prf_eq_symm (prf_tc_succ' t))))))
      (pcc_axL0_computed h t)
  -- R1: `ḣ + (σt)˙ ⟶ (h+σt)˙`, en las DOS ocurrencias a la vez
  have h1 : Prf (provFromCode (eqc (consT (tcFn h) (tcFn t))
      (div2cT (addcT (mulcT (tcFn (add h (succ t))) (succcT (tcFn (add h (succ t)))))
                     (mulcT (termCode two) (tcFn (succ t))))))) := by
    refine pcc_rw_div2 _ hL
      (fun s => addcT (mulcT s (succcT s)) (mulcT (termCode two) (tcFn (succ t)))) ?_
      _ _ (pcc_eval_add h (succ t)) h0
      hwL
      (prf_hasWit_addcT (prf_hasWit_mulcT hv0 (prf_hasWit_succcT hv0)) hwQ2)
      (prf_hasWit_addcT (prf_hasWit_tcFn h) (prf_hasWit_tcFn (succ t)))
      (prf_hasWit_tcFn (add h (succ t)))
    intro s
    refine prf_eq_trans (prf_substtc_addcT zero s _ _) (prf_congr_addcT ?_ (hQ2 s))
    refine prf_eq_trans (prf_substtc_mulcT zero s _ _) (prf_congr_mulcT (prf_substtc_varc0 s) ?_)
    exact prf_eq_trans (prf_substtc_succcT zero s _) (prf_congr_succcT (prf_substtc_varc0 s))
  -- paso 2 (nivel código, gratis): `σ(Ṡ)` se pliega en `(σS)˙`
  have h2 : Prf (provFromCode (eqc (consT (tcFn h) (tcFn t))
      (div2cT (addcT (mulcT (tcFn (add h (succ t))) (tcFn (succ (add h (succ t)))))
                     (mulcT (termCode two) (tcFn (succ t))))))) :=
    prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
      (prf_congr_div2cT (prf_congr_addcT
        (prf_congr_mulcT (prf_refl _) (prf_eq_symm (prf_tc_succ' (add h (succ t)))))
        (prf_refl _))))) h1
  -- R3: `Ṡ · (σS)˙ ⟶ (S·σS)˙`
  have h3 : Prf (provFromCode (eqc (consT (tcFn h) (tcFn t))
      (div2cT (addcT (tcFn (mul (add h (succ t)) (succ (add h (succ t)))))
                     (mulcT (termCode two) (tcFn (succ t))))))) := by
    refine pcc_rw_div2 _ hL
      (fun s => addcT s (mulcT (termCode two) (tcFn (succ t)))) ?_
      _ _ (pcc_eval_mul (add h (succ t)) (succ (add h (succ t)))) h2
      hwL (prf_hasWit_addcT hv0 hwQ2)
      (prf_hasWit_mulcT (prf_hasWit_tcFn (add h (succ t)))
        (prf_hasWit_tcFn (succ (add h (succ t)))))
      (prf_hasWit_tcFn (mul (add h (succ t)) (succ (add h (succ t)))))
    intro s
    exact prf_eq_trans (prf_substtc_addcT zero s _ _)
      (prf_congr_addcT (prf_substtc_varc0 s) (hQ2 s))
  -- R4: `⌜2⌝ · (σt)˙ ⟶ (2·σt)˙`  (con `⌜2⌝ = 2˙`)
  have hQ : Prf (provFromCode (eqc (mulcT (termCode two) (tcFn (succ t)))
      (tcFn (mul two (succ t))))) :=
    prf_mp (prf_provCode_congr (prf_congr_eqCodeFn
      (prf_congr_mulcT prf_tc_two (prf_refl _)) (prf_refl _))) (pcc_eval_mul two (succ t))
  have h4 : Prf (provFromCode (eqc (consT (tcFn h) (tcFn t))
      (div2cT (addcT (tcFn (mul (add h (succ t)) (succ (add h (succ t)))))
                     (tcFn (mul two (succ t))))))) := by
    refine pcc_rw_div2 _ hL
      (fun s => addcT (tcFn (mul (add h (succ t)) (succ (add h (succ t))))) s) ?_ _ _ hQ h3
      hwL
      (prf_hasWit_addcT (prf_hasWit_tcFn (mul (add h (succ t)) (succ (add h (succ t))))) hv0)
      hwQ2 (prf_hasWit_tcFn (mul two (succ t)))
    intro s
    exact prf_eq_trans (prf_substtc_addcT zero s _ _)
      (prf_congr_addcT (substtc_inv_tcFn _ s) (prf_substtc_varc0 s))
  -- R5: la suma exterior ⟶ `(cpOf h t)˙`
  have h5 : Prf (provFromCode (eqc (consT (tcFn h) (tcFn t)) (div2cT (tcFn (cpOf h t))))) := by
    refine pcc_rw_div2 _ hL (fun s => s) (fun s => prf_substtc_varc0 s) _ _
      (pcc_eval_add (mul (add h (succ t)) (succ (add h (succ t)))) (mul two (succ t))) h4
      hwL hv0
      (prf_hasWit_addcT (prf_hasWit_tcFn (mul (add h (succ t)) (succ (add h (succ t)))))
        (prf_hasWit_tcFn (mul two (succ t))))
      (prf_hasWit_tcFn (add (mul (add h (succ t)) (succ (add h (succ t)))) (mul two (succ t))))
  -- FASE C: el `div2` se cancela contra el polinomio
  exact pcc_eq_trans_code _ _ _ hL hwL
    (prf_hasWit_div2cT (prf_hasWit_tcFn (cpOf h t))) (prf_hasWit_tcFn (cons h t))
    h5 (pcc_div2_cons h t)

end ROBINSON_PlusPlus.Meta.DotConsPrf

export ROBINSON_PlusPlus.Meta.DotConsPrf (
  consT div2cT prf_congr_consT prf_congr_div2cT prf_substtc_consT prf_substtc_div2cT
  substtc_inv_consT substtc_inv_div2cT prf_substtc_two prf_tc_two
  cpOfT prf_congr_cpOfT prf_substtc_cpOfT pcc_axL0_inst prf_axL0_body_computes
  pcc_axL0_computed pcc_rw pcc_rw_imp pcc_rw_div2 cpOfT' prf_congr_cpOfT2
  pcc_div2_cons pcc_dot_cons
)
