/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.EvalArithPrf
import ROBINSON_PlusPlus.Meta.NumListPrf
import ROBINSON_PlusPlus.Meta.DotConsPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.TcArithPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.MpCodePrf
open ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
open ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
open ROBINSON_PlusPlus.Meta.EvalArithPrf
open ROBINSON_PlusPlus.Meta.DerivCondPrf
open ROBINSON_PlusPlus.Meta.NumListPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.DotConsPrf

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace ROBINSON_PlusPlus.Meta.EvalListPrf

/-!
## META — NIVEL D real (§28): **evaluación provable** de la capa de listas (`carc`, `cdrc`, `lenc`)

Misma receta que §27 (`pcc_eval_add`), aplicada a los símbolos que el cuerpo Δ₀ del verificador
usa sobre listas. La diferencia estructural:

* `carc` / `cdrc` **no necesitan inducción**: sus axiomas (`ax_carc`, `ax_cdrc`) determinan el valor
  en un `cons` de una vez. Basta instanciar el axioma **codificado** con testigos `tcFn h`, `tcFn t`
  y transportar `consT ḣ ṫ ↦ (cons h t)˙` con **`pcc_dot_cons`** (antes: `prf_tc_cons`, retirado).
* `lenc` **sí** recurre sobre la estructura de lista ⇒ **inducción object de listas**
  (`prf_list_induction`), con base `ax_lenc_nil` y paso `ax_lenc_cons` + la lógica ecuacional
  interna de §26 (`pcc_congr_succ_code_imp`, `pcc_eq_trans_code_imp`).

Notación: `ṫ = tcFn t` (el «numeral‑de» object). Los objetivos tienen siempre la misma asimetría:
a la izquierda del código va el **término simbólico**, a la derecha el **numeral del valor**.
-/

/-! ### Constructores de código de los términos de lista -/

/-- Código object del término `carc x` desde el código `x`. -/
def carcT (x : Term) : Term := funcc (strCode "carc") (cons x nil)
/-- Código object del término `cdrc x`. -/
def cdrcT (x : Term) : Term := funcc (strCode "cdrc") (cons x nil)
/-- Código object del término `lenc x`. -/
def lencT (x : Term) : Term := funcc (strCode "lenc") (cons x nil)

/-! ### La GUARDA de los tres accesores (ADR-020): escalera de aridad, §28 -/

theorem prf_hasWit_carcT {X : Term} (hX : Prf (hasWit X)) : Prf (hasWit (carcT X)) :=
  prf_hasWit_funcc1 (strCode "carc") X hX

theorem prf_hasWit_cdrcT {X : Term} (hX : Prf (hasWit X)) : Prf (hasWit (cdrcT X)) :=
  prf_hasWit_funcc1 (strCode "cdrc") X hX

theorem prf_hasWit_lencT {X : Term} (hX : Prf (hasWit X)) : Prf (hasWit (lencT X)) :=
  prf_hasWit_funcc1 (strCode "lenc") X hX
-- `consT` (y su congruencia, `substtc` e invariancia) viven ahora en `Meta/DotConsPrf.lean`:
-- eran duplicados textuales. Aquí se usan vía `open`.

/-- Puentes definicionales con `termCode` (por definición de `termCode` sobre `.func`). -/
theorem carcT_termCode (a : Term) : carcT (termCode a) = termCode (carc a) := rfl
theorem cdrcT_termCode (a : Term) : cdrcT (termCode a) = termCode (cdrc a) := rfl
theorem lencT_termCode (a : Term) : lencT (termCode a) = termCode (lenc a) := rfl
theorem consT_termCode (a b : Term) : consT (termCode a) (termCode b) = termCode (cons a b) := rfl

/-! ### ⚠️ `prf_tc_cons'` RETIRADO (2026-08-23)

Aquí vivía `prf_tc_cons' (a b) : Prf (tcFn (cons a b) =eq consT (tcFn a) (tcFn b))`, que era
`prf_tc_cons` — la consecuencia directa de **`ax_tc_cons`**, la ecuación que hacía **inconsistente**
la teoría objeto (ADR-012). Retirado el axioma, ni el puente ni `prf_tc_cons` existen ya: bajo la
lectura numeral el enunciado es **falso** para `a`, `b` abstractos, no sólo indemostrable.

**Su sustituto es `pcc_dot_cons`** (`Meta/DotConsPrf.lean`), que prueba la misma ecuación **dentro de
`Prov`** en vez de a nivel de código. El cambio de nivel es real: el transporte pasa de
`prf_provCode_congr` (fuera) a `pcc_leibniz_apply` (dentro), y por eso hace falta dar el
código-contexto. `pcc_rw_dot_cons_un` (abajo) encapsula ese trámite. -/

/-! ### Congruencias e interacción con `substtc` -/

theorem prf_congr_carcT {x y : Term} (h : Prf (x =eq y)) : Prf (carcT x =eq carcT y) :=
  prf_congr_funcc2 (prf_congr_cons_head h)
theorem prf_congr_cdrcT {x y : Term} (h : Prf (x =eq y)) : Prf (cdrcT x =eq cdrcT y) :=
  prf_congr_funcc2 (prf_congr_cons_head h)
theorem prf_congr_lencT {x y : Term} (h : Prf (x =eq y)) : Prf (lencT x =eq lencT y) :=
  prf_congr_funcc2 (prf_congr_cons_head h)

theorem prf_substtc_carcT (v W x : Term) :
    Prf (substtc v W (carcT x) =eq carcT (substtc v W x)) :=
  prf_substtc_funcc1 v W (strCode "carc") x
theorem prf_substtc_cdrcT (v W x : Term) :
    Prf (substtc v W (cdrcT x) =eq cdrcT (substtc v W x)) :=
  prf_substtc_funcc1 v W (strCode "cdrc") x
theorem prf_substtc_lencT (v W x : Term) :
    Prf (substtc v W (lencT x) =eq lencT (substtc v W x)) :=
  prf_substtc_funcc1 v W (strCode "lenc") x

/-! #### Invariancias `substtc` (descargan la hipótesis `hX` de §26) -/

theorem substtc_inv_carcT {X : Term} (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    ∀ W, Prf (substtc zero W (carcT X) =eq carcT X) :=
  fun W => prf_eq_trans (prf_substtc_carcT zero W X) (prf_congr_carcT (hX W))
theorem substtc_inv_cdrcT {X : Term} (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    ∀ W, Prf (substtc zero W (cdrcT X) =eq cdrcT X) :=
  fun W => prf_eq_trans (prf_substtc_cdrcT zero W X) (prf_congr_cdrcT (hX W))
theorem substtc_inv_lencT {X : Term} (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    ∀ W, Prf (substtc zero W (lencT X) =eq lencT X) :=
  fun W => prf_eq_trans (prf_substtc_lencT zero W X) (prf_congr_lencT (hX W))

/-! ### El sustituto de `prf_tc_cons'`: reescritura del `cons` dotado, INTERNA

Los tres sitios que usaban `prf_tc_cons'` (`carc`, `cdrc`, `lenc`) tienen la **misma forma**: un
constructor de código **unario** `F` aplicado al `cons`, con un lado derecho `R` fijo. Así que basta
un molde, y los tres se cierran con él.

Es `pcc_rw` (`Meta/DotConsPrf.lean`) con el contexto `G s := ⌜F s = R⌝` y `pcc_dot_cons h t` como
igualdad interna. Las hipótesis sobre `F` (distribuye sobre `substtc`, es congruente) y sobre `R`
(es `substtc`-invariante) son justo lo que hace falta para computar el `substfc` del contexto. -/

/-- **Molde de repatriación.** De `⊢ Prov(⌜F (cons(ḣ,ṫ)) = R⌝)` sale `⊢ Prov(⌜F ((cons h t)˙) = R⌝)`.

    Sustituye al viejo transporte por `prf_tc_cons'`, que era **de código**; éste es **interno**. -/
theorem pcc_rw_dot_cons_un (F : Term → Term)
    (hFs : ∀ v W x : Term, Prf (substtc v W (F x) =eq F (substtc v W x)))
    (hFc : ∀ x y : Term, Prf (x =eq y) → Prf (F x =eq F y))
    (R : Term) (hR : ∀ W : Term, Prf (substtc zero W R =eq R))
    (h t : Term)
    (hbase : Prf (provFromCode (eqCodeFn (F (consT (tcFn h) (tcFn t))) R)))
    (hwF : Prf (hasWit (F (varc (numeral 0))))) (hwR : Prf (hasWit R)) :
    Prf (provFromCode (eqCodeFn (F (tcFn (cons h t))) R)) := by
  refine pcc_rw (fun s => eqCodeFn (F s) R) ?_ _ _ (pcc_dot_cons h t) hbase
    (prf_hasWitF_eq2 (F (varc (numeral 0))) R hwF hwR)
    (prf_hasWit_consT (prf_hasWit_tcFn h) (prf_hasWit_tcFn t))
    (prf_hasWit_tcFn (cons h t))
  intro s
  refine prf_eq_trans (prf_substfc_eq zero s (F (varc (numeral 0))) R) ?_
  exact prf_congr_eqCodeFn
    (prf_eq_trans (hFs zero s (varc (numeral 0))) (hFc _ _ (prf_substtc_varc0 s)))
    (hR s)

/-! ### `carc` y `cdrc`: evaluación provable SIN inducción

`ax_carc = ∀h∀t. carc (cons h t) = h` es un `forall_2` cuyo cuerpo determina el valor de una vez.
Instanciamos el axioma **codificado** (`pcc_axiom_inst2`) con testigos `tcFn h`, `tcFn t`, computamos
los dos `substfc` (interno con `prf_substfc_arith_open`, externo a mano sobre el código explícito,
usando (A) `prf_substtc_tcFn` para que los `tcFn` incrustados sobrevivan), y transportamos
`consT ḣ ṫ ↦ (cons h t)˙` con **`pcc_rw_dot_cons_un`** (que es `pcc_dot_cons` por dentro). -/

/-- Instancia codificada de `ax_carc`, ya computada: `⊢ Prov(⌜carc (cons h t)˙ = ḣ⌝)`. -/
theorem pcc_eval_carc (h t : Term) :
    Prf (provFromCode (eqCodeFn (carcT (tcFn (cons h t))) (tcFn h))) := by
  let W1 : Term := liftc zero (tcFn h)
  let W2 : Term := tcFn t
  let φ : Formula := carc (cons (.var 1) (.var 0)) =eq (.var 1)
  -- (1) `substfc` interno, computado
  have hin : Prf (substfc (succ zero) W1 (formCode φ)
      =eq eqCodeFn (carcT (consT W1 (varc (numeral 0)))) W1) :=
    prf_substfc_arith_open 1 W1 φ
  -- (2) normaliza `W1 ↦ tcFn h` (A)
  have hA : Prf (W1 =eq tcFn h) := prf_liftc_tcFn h
  have hnorm : Prf (eqCodeFn (carcT (consT W1 (varc (numeral 0)))) W1
      =eq eqCodeFn (carcT (consT (tcFn h) (varc (numeral 0)))) (tcFn h)) :=
    prf_congr_eqCodeFn (prf_congr_carcT (prf_congr_consT hA (prf_refl _))) hA
  -- (3) `substfc` externo sobre el código explícito
  have hout : Prf (substfc zero W2 (eqCodeFn (carcT (consT (tcFn h) (varc (numeral 0)))) (tcFn h))
      =eq eqCodeFn (carcT (consT (tcFn h) W2)) (tcFn h)) := by
    refine prf_eq_trans
      (prf_substfc_eq zero W2 (carcT (consT (tcFn h) (varc (numeral 0)))) (tcFn h)) ?_
    refine prf_congr_eqCodeFn ?_ (prf_substtc_tcFn W2 h)
    refine prf_eq_trans (prf_substtc_carcT zero W2 (consT (tcFn h) (varc (numeral 0)))) ?_
    refine prf_congr_carcT ?_
    exact prf_eq_trans (prf_substtc_consT zero W2 (tcFn h) (varc (numeral 0)))
      (prf_congr_consT (prf_substtc_tcFn W2 h) (prf_substtc_varc0 W2))
  -- (4) ensamblar y transportar `consT ḣ ṫ ↦ (cons h t)˙`
  have hchain : Prf (substfc zero W2 (substfc (succ zero) W1 (formCode φ))
      =eq eqCodeFn (carcT (consT (tcFn h) W2)) (tcFn h)) :=
    prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hout
  have hbase : Prf (provFromCode (eqCodeFn (carcT (consT (tcFn h) (tcFn t))) (tcFn h))) :=
    prf_mp (prf_provCode_congr hchain)
      (pcc_axiom_inst2 φ (show ax_carc ∈ axioms by simp [axioms]) (tcFn h) (tcFn t)
        (prf_hasWit_tcFn (liftTerm 0 h)) (prf_hasWit_tcFn (liftTerm 0 t)))
  exact pcc_rw_dot_cons_un carcT prf_substtc_carcT (fun _ _ => prf_congr_carcT)
    (tcFn h) (substtc_inv_tcFn h) h t hbase
    (prf_hasWit_carcT (prf_hasWit_varc (numeral 0))) (prf_hasWit_tcFn h)

/-- Instancia codificada de `ax_cdrc`, ya computada: `⊢ Prov(⌜cdrc (cons h t)˙ = ṫ⌝)`. -/
theorem pcc_eval_cdrc (h t : Term) :
    Prf (provFromCode (eqCodeFn (cdrcT (tcFn (cons h t))) (tcFn t))) := by
  let W1 : Term := liftc zero (tcFn h)
  let W2 : Term := tcFn t
  let φ : Formula := cdrc (cons (.var 1) (.var 0)) =eq (.var 0)
  have hin : Prf (substfc (succ zero) W1 (formCode φ)
      =eq eqCodeFn (cdrcT (consT W1 (varc (numeral 0)))) (varc (numeral 0))) :=
    prf_substfc_arith_open 1 W1 φ
  have hA : Prf (W1 =eq tcFn h) := prf_liftc_tcFn h
  have hnorm : Prf (eqCodeFn (cdrcT (consT W1 (varc (numeral 0)))) (varc (numeral 0))
      =eq eqCodeFn (cdrcT (consT (tcFn h) (varc (numeral 0)))) (varc (numeral 0))) :=
    prf_congr_eqCodeFn (prf_congr_cdrcT (prf_congr_consT hA (prf_refl _))) (prf_refl _)
  have hout : Prf (substfc zero W2
      (eqCodeFn (cdrcT (consT (tcFn h) (varc (numeral 0)))) (varc (numeral 0)))
      =eq eqCodeFn (cdrcT (consT (tcFn h) W2)) W2) := by
    refine prf_eq_trans
      (prf_substfc_eq zero W2 (cdrcT (consT (tcFn h) (varc (numeral 0)))) (varc (numeral 0))) ?_
    refine prf_congr_eqCodeFn ?_ (prf_substtc_varc0 W2)
    refine prf_eq_trans (prf_substtc_cdrcT zero W2 (consT (tcFn h) (varc (numeral 0)))) ?_
    refine prf_congr_cdrcT ?_
    exact prf_eq_trans (prf_substtc_consT zero W2 (tcFn h) (varc (numeral 0)))
      (prf_congr_consT (prf_substtc_tcFn W2 h) (prf_substtc_varc0 W2))
  have hchain : Prf (substfc zero W2 (substfc (succ zero) W1 (formCode φ))
      =eq eqCodeFn (cdrcT (consT (tcFn h) W2)) W2) :=
    prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hout
  have hbase : Prf (provFromCode (eqCodeFn (cdrcT (consT (tcFn h) (tcFn t))) (tcFn t))) :=
    prf_mp (prf_provCode_congr hchain)
      (pcc_axiom_inst2 φ (show ax_cdrc ∈ axioms by simp [axioms]) (tcFn h) (tcFn t)
        (prf_hasWit_tcFn (liftTerm 0 h)) (prf_hasWit_tcFn (liftTerm 0 t)))
  exact pcc_rw_dot_cons_un cdrcT prf_substtc_cdrcT (fun _ _ => prf_congr_cdrcT)
    (tcFn t) (substtc_inv_tcFn t) h t hbase
    (prf_hasWit_cdrcT (prf_hasWit_varc (numeral 0))) (prf_hasWit_tcFn t)

/-! ### `lenc`: evaluación provable POR INDUCCIÓN DE LISTAS -/

/-- Código de `lenc L̇ = (lenc L)˙`. -/
def evalLencCode (L : Term) : Term := eqCodeFn (lencT (tcFn L)) (tcFn (lenc L))

/-- **BASE**: `⊢ Prov(⌜lenc 0̇ = (lenc nil)˙⌝)`.
    `ax_lenc_nil` es una **sentencia cerrada**: su código demostrable sale directo de D1
    (`repr_pos'_prf`), y sólo hay que transportar `⌜nil⌝ ↦ 0̇` y `0̇ ↦ (lenc nil)˙`. -/
theorem pcc_eval_lenc_nil : Prf (provFromCode (evalLencCode nil)) := by
  have h0 : Prf (provFromCode (formCode (lenc nil =eq zero))) :=
    repr_pos'_prf (prf_ax (show ax_lenc_nil ∈ axioms by simp [axioms]))
  -- `formCode (lenc nil =eq zero) = eqCodeFn (lencT (termCode nil)) (termCode zero)`  (rfl)
  have hL : Prf (termCode nil =eq tcFn nil) := prf_eq_symm prf_tc_zero
  have hR : Prf (termCode zero =eq tcFn (lenc nil)) :=
    prf_eq_symm (prf_eq_trans (prf_congr_tcFn prf_lenc_nil) prf_tc_zero)
  exact prf_mp
    (prf_provCode_congr (prf_congr_eqCodeFn (prf_congr_lencT hL) hR))
    h0

/-- Instancia codificada de `ax_lenc_cons`, ya computada:
    `⊢ Prov(⌜lenc (cons h t)˙ = σ (lenc ṫ)⌝)`. -/
theorem pcc_ax_lenc_cons_computed (h t : Term) :
    Prf (provFromCode
      (eqCodeFn (lencT (tcFn (cons h t))) (succcT (lencT (tcFn t))))) := by
  let W1 : Term := liftc zero (tcFn h)
  let W2 : Term := tcFn t
  let φ : Formula := lenc (cons (.var 1) (.var 0)) =eq succ (lenc (.var 0))
  have hin : Prf (substfc (succ zero) W1 (formCode φ)
      =eq eqCodeFn (lencT (consT W1 (varc (numeral 0))))
                   (succcT (lencT (varc (numeral 0))))) :=
    prf_substfc_arith_open 1 W1 φ
  have hA : Prf (W1 =eq tcFn h) := prf_liftc_tcFn h
  have hnorm : Prf (eqCodeFn (lencT (consT W1 (varc (numeral 0))))
                             (succcT (lencT (varc (numeral 0))))
      =eq eqCodeFn (lencT (consT (tcFn h) (varc (numeral 0))))
                   (succcT (lencT (varc (numeral 0))))) :=
    prf_congr_eqCodeFn (prf_congr_lencT (prf_congr_consT hA (prf_refl _))) (prf_refl _)
  have hout : Prf (substfc zero W2
      (eqCodeFn (lencT (consT (tcFn h) (varc (numeral 0)))) (succcT (lencT (varc (numeral 0)))))
      =eq eqCodeFn (lencT (consT (tcFn h) W2)) (succcT (lencT W2))) := by
    refine prf_eq_trans
      (prf_substfc_eq zero W2 (lencT (consT (tcFn h) (varc (numeral 0))))
        (succcT (lencT (varc (numeral 0))))) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_lencT zero W2 (consT (tcFn h) (varc (numeral 0)))) ?_
      refine prf_congr_lencT ?_
      exact prf_eq_trans (prf_substtc_consT zero W2 (tcFn h) (varc (numeral 0)))
        (prf_congr_consT (prf_substtc_tcFn W2 h) (prf_substtc_varc0 W2))
    · refine prf_eq_trans (prf_substtc_succcT zero W2 (lencT (varc (numeral 0)))) ?_
      refine prf_congr_succcT ?_
      exact prf_eq_trans (prf_substtc_lencT zero W2 (varc (numeral 0)))
        (prf_congr_lencT (prf_substtc_varc0 W2))
  have hchain : Prf (substfc zero W2 (substfc (succ zero) W1 (formCode φ))
      =eq eqCodeFn (lencT (consT (tcFn h) W2)) (succcT (lencT W2))) :=
    prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hout
  have hbase : Prf (provFromCode
      (eqCodeFn (lencT (consT (tcFn h) (tcFn t))) (succcT (lencT (tcFn t))))) :=
    prf_mp (prf_provCode_congr hchain)
      (pcc_axiom_inst2 φ (show ax_lenc_cons ∈ axioms by simp [axioms]) (tcFn h) (tcFn t)
        (prf_hasWit_tcFn (liftTerm 0 h)) (prf_hasWit_tcFn (liftTerm 0 t)))
  exact pcc_rw_dot_cons_un lencT prf_substtc_lencT (fun _ _ => prf_congr_lencT)
    (succcT (lencT (tcFn t)))
    (substtc_inv_succcT (substtc_inv_lencT (substtc_inv_tcFn t))) h t hbase
    (prf_hasWit_lencT (prf_hasWit_varc (numeral 0)))
    (prf_hasWit_succcT (prf_hasWit_lencT (prf_hasWit_tcFn t)))

/-- **PASO INDUCTIVO** de `lenc`, en forma implicación (lo que pide `prf_list_induction`):
    `⊢ Prov(⌜lenc ṫ = (lenc t)˙⌝) ⇒ Prov(⌜lenc (cons h t)˙ = (lenc (cons h t))˙⌝)`. -/
theorem pcc_eval_lenc_cons_imp (h t : Term) :
    Prf (provFromCode (evalLencCode t) ⇒ provFromCode (evalLencCode (cons h t))) := by
  have hinvT : ∀ W, Prf (substtc zero W (lencT (tcFn t)) =eq lencT (tcFn t)) :=
    substtc_inv_lencT (substtc_inv_tcFn t)
  have hinvHT : ∀ W, Prf (substtc zero W (lencT (tcFn (cons h t))) =eq lencT (tcFn (cons h t))) :=
    substtc_inv_lencT (substtc_inv_tcFn (cons h t))
  -- HI ⇒ `Prov(⌜σ (lenc ṫ) = σ ((lenc t)˙)⌝)`
  have hcs : Prf (provFromCode (eqc (lencT (tcFn t)) (tcFn (lenc t)))
      ⇒ provFromCode (eqc (succcT (lencT (tcFn t))) (succcT (tcFn (lenc t))))) :=
    pcc_congr_succ_code_imp _ _ hinvT
      (prf_hasWit_lencT (prf_hasWit_tcFn t)) (prf_hasWit_tcFn (lenc t))
  -- transitividad con la instancia del axioma
  have htr : Prf (provFromCode (eqc (succcT (lencT (tcFn t))) (succcT (tcFn (lenc t))))
      ⇒ provFromCode (eqc (lencT (tcFn (cons h t))) (succcT (tcFn (lenc t))))) :=
    pcc_eq_trans_code_imp _ _ _ hinvHT
      (prf_hasWit_lencT (prf_hasWit_tcFn (cons h t)))
      (prf_hasWit_succcT (prf_hasWit_lencT (prf_hasWit_tcFn t)))
      (prf_hasWit_succcT (prf_hasWit_tcFn (lenc t)))
      (pcc_ax_lenc_cons_computed h t)
  -- transporte final del código: `σ ((lenc t)˙) =eq (lenc (cons h t))˙`
  have hcode : Prf (eqc (lencT (tcFn (cons h t))) (succcT (tcFn (lenc t)))
      =eq evalLencCode (cons h t)) :=
    prf_congr_eqCodeFn (prf_refl _)
      (prf_eq_symm
        (prf_eq_trans (prf_congr_tcFn (prf_lenc_cons h t)) (prf_tc_succ' (lenc t))))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr hcode) _)
    (PrfH.mp _ _ _ (prf_to_prfH htr _)
      (PrfH.mp _ _ _ (prf_to_prfH hcs _) (prfH_hyp_self _)))

/-! #### Transparencia de `evalLencCode` bajo `substTerm`/`liftTerm` -/

theorem substTerm_evalLencCode (v : Nat) (s L : Term) :
    substTerm v s (evalLencCode L) = evalLencCode (substTerm v s L) := by
  simp only [evalLencCode, eqCodeFn, lencT, funcc, tcFn, lenc, cons, nil, zero, succ,
    substTerm, substTerms, substTerm_numeral, substTerm_strCode]

theorem liftTerm_evalLencCode (k : Nat) (L : Term) :
    liftTerm k (evalLencCode L) = evalLencCode (liftTerm k L) := by
  simp only [evalLencCode, eqCodeFn, lencT, funcc, tcFn, lenc, cons, nil, zero, succ,
    liftTerm, liftTerms, liftTerm_numeral, liftTerm_strCode]

/-- Predicado inductivo `Ψ(L) = Prov(⌜lenc L̇ = (lenc L)˙⌝)`. -/
def evalLencPred : Formula := provFromCode (evalLencCode (.var 0))

theorem substFormula_evalLencPred (L : Term) :
    substFormula 0 L evalLencPred = provFromCode (evalLencCode L) := by
  simp only [evalLencPred, substFormula_provFromCode_open, substTerm_evalLencCode, substTerm,
    reduceIte]

/-- **EVALUACIÓN PROVABLE DE `lenc` (∀ object)**: `⊢ ∀L. Prov(⌜lenc L̇ = (lenc L)˙⌝)`.
    Inducción **de listas** (`prf_list_induction`): base `pcc_eval_lenc_nil`, paso
    `pcc_eval_lenc_cons_imp`. -/
theorem prf_eval_lenc_all : Prf (Formula.forall evalLencPred) := by
  refine prf_list_induction evalLencPred ?base ?step
  · rw [substFormula_evalLencPred]
    exact pcc_eval_lenc_nil
  · refine Prf.gen _ (Prf.gen _ ?_)
    show Prf (Formula.impl (liftFormula 1 evalLencPred)
      (substFormula 0 (cons (.var 1) (.var 0)) (liftFormula 2 (liftFormula 1 evalLencPred))))
    have hL : liftFormula 1 evalLencPred = provFromCode (evalLencCode (.var 0)) := by
      simp only [evalLencPred, liftFormula_provFromCode_open, liftTerm_evalLencCode, liftTerm,
        Nat.zero_lt_one, reduceIte]
    have hR : substFormula 0 (cons (.var 1) (.var 0)) (liftFormula 2 (liftFormula 1 evalLencPred))
        = provFromCode (evalLencCode (cons (.var 1) (.var 0))) := by
      simp only [evalLencPred, liftFormula_provFromCode_open, substFormula_provFromCode_open,
        liftTerm_evalLencCode, substTerm_evalLencCode, liftTerm, substTerm, Nat.zero_lt_one,
        Nat.zero_lt_two, reduceIte]
    rw [hR, hL]
    exact pcc_eval_lenc_cons_imp (.var 1) (.var 0)

/-- **EVALUACIÓN PROVABLE DE `lenc`**: `⊢ Prov(⌜lenc L̇ = (lenc L)˙⌝)` para `L` **arbitrario**. -/
theorem pcc_eval_lenc (L : Term) : Prf (provFromCode (evalLencCode L)) := by
  have h := prf_spec prf_eval_lenc_all L
  rwa [substFormula_evalLencPred] at h

end ROBINSON_PlusPlus.Meta.EvalListPrf

export ROBINSON_PlusPlus.Meta.EvalListPrf (
  carcT cdrcT lencT
  carcT_termCode cdrcT_termCode lencT_termCode consT_termCode
  prf_congr_carcT prf_congr_cdrcT prf_congr_lencT
  prf_substtc_carcT prf_substtc_cdrcT prf_substtc_lencT
  substtc_inv_carcT substtc_inv_cdrcT substtc_inv_lencT
  pcc_rw_dot_cons_un
  pcc_eval_carc pcc_eval_cdrc
  evalLencCode pcc_eval_lenc_nil pcc_ax_lenc_cons_computed pcc_eval_lenc_cons_imp
  substTerm_evalLencCode liftTerm_evalLencCode evalLencPred substFormula_evalLencPred
  prf_eval_lenc_all pcc_eval_lenc
  -- ADR-020: la guarda de los constructores dotados (escalera de aridad, §28)
  prf_hasWit_carcT prf_hasWit_cdrcT prf_hasWit_lencT
)
