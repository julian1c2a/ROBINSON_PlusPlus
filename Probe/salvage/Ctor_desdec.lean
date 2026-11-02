/- SONDEO — PASO 1 del frente `pcc_eval_substfc`: constructores DOTADOS de la familia
   sustitución/lift (`substfcT`, `liftcT`, …) y su KIT, dimensionados **desde (c) hacia atrás**.

   ESTRATEGIA 3: se arranca por la prueba de fuego (c) — la instancia INTERNA de
   `ax_substfc_forall` vía `pcc_axiom_inst3` + `prf_substfc_arith_open` — y sólo se definen los
   constructores que esa construcción pide.

   ⚠️ CERO axiomas: no hay `axiom`, ni `sorry`, ni `native_decide`. -/
import ROBINSON_PlusPlus.Meta

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.TcArithPrf ROBINSON_PlusPlus.Meta.CheckArith
open ROBINSON_PlusPlus.Meta.Sigma1Prf ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.MpCodePrf ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
open ROBINSON_PlusPlus.Meta.NumCodeClosedPrf ROBINSON_PlusPlus.Meta.EvalArithPrf
open ROBINSON_PlusPlus.Meta.EvalListPrf ROBINSON_PlusPlus.Meta.EvalLtPrf
open ROBINSON_PlusPlus.Meta.EvalNthcPrf ROBINSON_PlusPlus.Meta.NatArithPrf
open ROBINSON_PlusPlus.Meta.DotConsPrf ROBINSON_PlusPlus.Meta.DerivCondPrf
open ROBINSON_PlusPlus.Meta.CodeCtorKit ROBINSON_PlusPlus.Meta.BdAllIntroPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace CtorDesdeC

/-! ## §0. La pieza que FALTABA: `substtc` sobre un `funcc` de TRES argumentos -/

/-- `substtc` sobre un `funcc` de **tres** argumentos (el hueco de `prf_substtc_funcc1/2`). -/
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

/-- Gemelo para `liftc` (no lo pide (c), pero cierra el kit por simetría). -/
theorem prf_liftc_funcc3 (c sc x y z : Term) :
    Prf (liftc c (funcc sc (cons x (cons y (cons z nil))))
      =eq funcc sc (cons (liftc c x) (cons (liftc c y) (cons (liftc c z) nil)))) :=
  prf_eq_trans (prf_liftc_func c sc (cons x (cons y (cons z nil))))
    (prf_congr_funcc2
      (prf_eq_trans (prf_liftsc_cons c x (cons y (cons z nil)))
        (prf_congr_cons_tail
          (prf_eq_trans (prf_liftsc_cons c y (cons z nil))
            (prf_congr_cons_tail
              (prf_eq_trans (prf_liftsc_cons c z nil)
                (prf_congr_cons_tail (prf_liftsc_nil c))))))))

theorem prf_liftc_funcc2 (c sc x y : Term) :
    Prf (liftc c (funcc sc (cons x (cons y nil)))
      =eq funcc sc (cons (liftc c x) (cons (liftc c y) nil))) :=
  prf_eq_trans (prf_liftc_func c sc (cons x (cons y nil)))
    (prf_congr_funcc2
      (prf_eq_trans (prf_liftsc_cons c x (cons y nil))
        (prf_congr_cons_tail
          (prf_eq_trans (prf_liftsc_cons c y nil)
            (prf_congr_cons_tail (prf_liftsc_nil c))))))

/-! ## §1. Los constructores DOTADOS de la familia -/

/-- Constructor de código del término `substfc v s f`: `⟨1, ⌜substfc⌝, [v,s,f]⟩`. -/
def substfcT (v s f : Term) : Term :=
  funcc (strCode "substfc") (cons v (cons s (cons f nil)))

/-- Constructor de código del término `substtc v s t`. -/
def substtcT (v s t : Term) : Term :=
  funcc (strCode "substtc") (cons v (cons s (cons t nil)))

/-- Constructor de código del término `substtsc v s ts`. -/
def substtscT (v s ts : Term) : Term :=
  funcc (strCode "substtsc") (cons v (cons s (cons ts nil)))

/-- Constructor de código del término `liftc c t`. -/
def liftcT (c t : Term) : Term := funcc (strCode "liftc") (cons c (cons t nil))

/-- Constructor de código del término `liftfc c f`. -/
def liftfcT (c f : Term) : Term := funcc (strCode "liftfc") (cons c (cons f nil))

/-- Constructor de código del término `liftsc c ts`. -/
def liftscT (c ts : Term) : Term := funcc (strCode "liftsc") (cons c (cons ts nil))

/-! ### Los PUENTES con `termCode`, por `rfl` -/

theorem substfcT_termCode (v s f : Term) :
    substfcT (termCode v) (termCode s) (termCode f) = termCode (substfc v s f) := rfl
theorem substtcT_termCode (v s t : Term) :
    substtcT (termCode v) (termCode s) (termCode t) = termCode (substtc v s t) := rfl
theorem substtscT_termCode (v s ts : Term) :
    substtscT (termCode v) (termCode s) (termCode ts) = termCode (substtsc v s ts) := rfl
theorem liftcT_termCode (c t : Term) :
    liftcT (termCode c) (termCode t) = termCode (liftc c t) := rfl
theorem liftfcT_termCode (c f : Term) :
    liftfcT (termCode c) (termCode f) = termCode (liftfc c f) := rfl
theorem liftscT_termCode (c ts : Term) :
    liftscT (termCode c) (termCode ts) = termCode (liftsc c ts) := rfl

/-! ### Congruencias (en TODOS los argumentos) -/

theorem prf_congr_substfcT {v v' s s' f f' : Term}
    (hv : Prf (v =eq v')) (hs : Prf (s =eq s')) (hf : Prf (f =eq f')) :
    Prf (substfcT v s f =eq substfcT v' s' f') :=
  prf_congr_funcc2
    (prf_eq_trans (prf_congr_cons_head hv)
      (prf_congr_cons_tail
        (prf_eq_trans (prf_congr_cons_head hs)
          (prf_congr_cons_tail (prf_congr_cons_head hf)))))

theorem prf_congr_substtcT {v v' s s' t t' : Term}
    (hv : Prf (v =eq v')) (hs : Prf (s =eq s')) (ht : Prf (t =eq t')) :
    Prf (substtcT v s t =eq substtcT v' s' t') :=
  prf_congr_funcc2
    (prf_eq_trans (prf_congr_cons_head hv)
      (prf_congr_cons_tail
        (prf_eq_trans (prf_congr_cons_head hs)
          (prf_congr_cons_tail (prf_congr_cons_head ht)))))

theorem prf_congr_substtscT {v v' s s' t t' : Term}
    (hv : Prf (v =eq v')) (hs : Prf (s =eq s')) (ht : Prf (t =eq t')) :
    Prf (substtscT v s t =eq substtscT v' s' t') :=
  prf_congr_funcc2
    (prf_eq_trans (prf_congr_cons_head hv)
      (prf_congr_cons_tail
        (prf_eq_trans (prf_congr_cons_head hs)
          (prf_congr_cons_tail (prf_congr_cons_head ht)))))

theorem prf_congr_liftcT {c c' t t' : Term} (hc : Prf (c =eq c')) (ht : Prf (t =eq t')) :
    Prf (liftcT c t =eq liftcT c' t') :=
  prf_congr_funcc2
    (prf_eq_trans (prf_congr_cons_head hc) (prf_congr_cons_tail (prf_congr_cons_head ht)))

theorem prf_congr_liftfcT {c c' t t' : Term} (hc : Prf (c =eq c')) (ht : Prf (t =eq t')) :
    Prf (liftfcT c t =eq liftfcT c' t') :=
  prf_congr_funcc2
    (prf_eq_trans (prf_congr_cons_head hc) (prf_congr_cons_tail (prf_congr_cons_head ht)))

theorem prf_congr_liftscT {c c' t t' : Term} (hc : Prf (c =eq c')) (ht : Prf (t =eq t')) :
    Prf (liftscT c t =eq liftscT c' t') :=
  prf_congr_funcc2
    (prf_eq_trans (prf_congr_cons_head hc) (prf_congr_cons_tail (prf_congr_cons_head ht)))

/-! ### `substtc` atraviesa los constructores (nivel `v` ARBITRARIO) -/

theorem prf_substtc_substfcT (v W x y z : Term) :
    Prf (substtc v W (substfcT x y z)
      =eq substfcT (substtc v W x) (substtc v W y) (substtc v W z)) :=
  prf_substtc_funcc3 v W (strCode "substfc") x y z

theorem prf_substtc_substtcT (v W x y z : Term) :
    Prf (substtc v W (substtcT x y z)
      =eq substtcT (substtc v W x) (substtc v W y) (substtc v W z)) :=
  prf_substtc_funcc3 v W (strCode "substtc") x y z

theorem prf_substtc_substtscT (v W x y z : Term) :
    Prf (substtc v W (substtscT x y z)
      =eq substtscT (substtc v W x) (substtc v W y) (substtc v W z)) :=
  prf_substtc_funcc3 v W (strCode "substtsc") x y z

theorem prf_substtc_liftcT (v W x y : Term) :
    Prf (substtc v W (liftcT x y) =eq liftcT (substtc v W x) (substtc v W y)) :=
  prf_substtc_funcc2 v W (strCode "liftc") x y

theorem prf_substtc_liftfcT (v W x y : Term) :
    Prf (substtc v W (liftfcT x y) =eq liftfcT (substtc v W x) (substtc v W y)) :=
  prf_substtc_funcc2 v W (strCode "liftfc") x y

theorem prf_substtc_liftscT (v W x y : Term) :
    Prf (substtc v W (liftscT x y) =eq liftscT (substtc v W x) (substtc v W y)) :=
  prf_substtc_funcc2 v W (strCode "liftsc") x y

/-! ### `liftc` atraviesa los constructores -/

theorem prf_liftc_substfcT (c x y z : Term) :
    Prf (liftc c (substfcT x y z) =eq substfcT (liftc c x) (liftc c y) (liftc c z)) :=
  prf_liftc_funcc3 c (strCode "substfc") x y z

theorem prf_liftc_substtcT (c x y z : Term) :
    Prf (liftc c (substtcT x y z) =eq substtcT (liftc c x) (liftc c y) (liftc c z)) :=
  prf_liftc_funcc3 c (strCode "substtc") x y z

theorem prf_liftc_substtscT (c x y z : Term) :
    Prf (liftc c (substtscT x y z) =eq substtscT (liftc c x) (liftc c y) (liftc c z)) :=
  prf_liftc_funcc3 c (strCode "substtsc") x y z

theorem prf_liftc_liftcT (c x y : Term) :
    Prf (liftc c (liftcT x y) =eq liftcT (liftc c x) (liftc c y)) :=
  prf_liftc_funcc2 c (strCode "liftc") x y

theorem prf_liftc_liftfcT (c x y : Term) :
    Prf (liftc c (liftfcT x y) =eq liftfcT (liftc c x) (liftc c y)) :=
  prf_liftc_funcc2 c (strCode "liftfc") x y

theorem prf_liftc_liftscT (c x y : Term) :
    Prf (liftc c (liftscT x y) =eq liftscT (liftc c x) (liftc c y)) :=
  prf_liftc_funcc2 c (strCode "liftsc") x y

/-! ### Invariancia `substtc` (la forma `∀ W`, la que consumen los Leibniz internos) -/

theorem substtc_inv_substfcT {X Y Z : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y))
    (hZ : ∀ W, Prf (substtc zero W Z =eq Z)) :
    ∀ W, Prf (substtc zero W (substfcT X Y Z) =eq substfcT X Y Z) := fun W =>
  prf_eq_trans (prf_substtc_substfcT zero W X Y Z)
    (prf_congr_substfcT (hX W) (hY W) (hZ W))

theorem substtc_inv_substtcT {X Y Z : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y))
    (hZ : ∀ W, Prf (substtc zero W Z =eq Z)) :
    ∀ W, Prf (substtc zero W (substtcT X Y Z) =eq substtcT X Y Z) := fun W =>
  prf_eq_trans (prf_substtc_substtcT zero W X Y Z)
    (prf_congr_substtcT (hX W) (hY W) (hZ W))

theorem substtc_inv_substtscT {X Y Z : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y))
    (hZ : ∀ W, Prf (substtc zero W Z =eq Z)) :
    ∀ W, Prf (substtc zero W (substtscT X Y Z) =eq substtscT X Y Z) := fun W =>
  prf_eq_trans (prf_substtc_substtscT zero W X Y Z)
    (prf_congr_substtscT (hX W) (hY W) (hZ W))

theorem substtc_inv_liftcT {X Y : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y)) :
    ∀ W, Prf (substtc zero W (liftcT X Y) =eq liftcT X Y) := fun W =>
  prf_eq_trans (prf_substtc_liftcT zero W X Y) (prf_congr_liftcT (hX W) (hY W))

theorem substtc_inv_liftfcT {X Y : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y)) :
    ∀ W, Prf (substtc zero W (liftfcT X Y) =eq liftfcT X Y) := fun W =>
  prf_eq_trans (prf_substtc_liftfcT zero W X Y) (prf_congr_liftfcT (hX W) (hY W))

theorem substtc_inv_liftscT {X Y : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y)) :
    ∀ W, Prf (substtc zero W (liftscT X Y) =eq liftscT X Y) := fun W =>
  prf_eq_trans (prf_substtc_liftscT zero W X Y) (prf_congr_liftscT (hX W) (hY W))

/-! ### Conmutación con `liftTerm` / `substTerm` (nivel META, para los predicados inductivos) -/

theorem liftTerm_substfcT (k : Nat) (v s f : Term) :
    liftTerm k (substfcT v s f) = substfcT (liftTerm k v) (liftTerm k s) (liftTerm k f) := by
  simp only [substfcT, funcc, cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_strCode]

theorem substTerm_substfcT (k : Nat) (u v s f : Term) :
    substTerm k u (substfcT v s f)
      = substfcT (substTerm k u v) (substTerm k u s) (substTerm k u f) := by
  simp only [substfcT, funcc, cons, nil, zero, succ, substTerm, substTerms, substTerm_strCode]

theorem liftTerm_liftcT (k : Nat) (c t : Term) :
    liftTerm k (liftcT c t) = liftcT (liftTerm k c) (liftTerm k t) := by
  simp only [liftcT, funcc, cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_strCode]

theorem substTerm_liftcT (k : Nat) (u c t : Term) :
    substTerm k u (liftcT c t) = liftcT (substTerm k u c) (substTerm k u t) := by
  simp only [liftcT, funcc, cons, nil, zero, succ, substTerm, substTerms, substTerm_strCode]

/-! ## §2. Dos utilidades de nivel: `substtc` sobre código CERRADO y sobre `unT`, a nivel `v` -/

/-- `substtc` a nivel `v` **arbitrario** es la identidad sobre el código de un término CERRADO.
    (Se apoya en `substCodeT_closed`, que ya existe.) -/
theorem prf_substtc_termCode_closed (v : Nat) (W t : Term) (ht : ∀ c : Nat, liftTerm c t = t) :
    Prf (substtc (numeral v) W (termCode t) =eq termCode t) := by
  have h := prf_substtc_arith_open v W t
  rwa [substCodeT_closed v W t ht] at h

theorem prf_substtc_termCode_numeralM (v m : Nat) (W : Term) :
    Prf (substtc (numeral v) W (termCode (numeralM m)) =eq termCode (numeralM m)) :=
  prf_substtc_termCode_closed v W (numeralM m) (fun c => liftTerm_numeralM c m)

theorem prf_substtc_termCode_zero (v : Nat) (W : Term) :
    Prf (substtc (numeral v) W (termCode zero) =eq termCode zero) :=
  prf_substtc_termCode_closed v W zero (fun _ => rfl)

/-- `substtc` distribuye sobre `unT` **a nivel `v` arbitrario** (el kit sólo lo tenía en `zero`). -/
theorem prf_substtc_unT_at (m v : Nat) (W a : Term) :
    Prf (substtc (numeral v) W (unT m a) =eq unT m (substtc (numeral v) W a)) := by
  unfold unT consT
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  refine prf_congr_funcc2 ?_
  refine prf_eq_trans (prf_congr_cons_head (prf_substtc_termCode_numeralM v m W)) ?_
  refine prf_congr_cons_tail (prf_congr_cons_head ?_)
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  exact prf_congr_funcc2
    (prf_congr_cons_tail (prf_congr_cons_head (prf_substtc_termCode_zero v W)))

/-! ## §3. LA PRUEBA DE FUEGO (c): la instancia INTERNA de `ax_substfc_forall`

`ax_substfc_forall = forall_3 AXF_BODY` (definicional).  Instanciada con los testigos
`ȧ`, `ḃ`, `ḟ` y computados los TRES `substfc` externos, la instancia interna dice:

```text
⊢ Prov( ⌜ substfc(ȧ, ḃ, ⟨6, ḟ⟩) = ⟨6, substfc(σȧ, liftc(⌜0⌝, ḃ), ḟ)⟩ ⌝ )
```

Nótese que el `forallc` del axioma se codifica **exactamente** como `unT 6` del KIT: los códigos
de la familia y los del KIT son el mismo árbol. -/

/-- Cuerpo del axioma `ax_substfc_forall` (`ax_substfc_forall = forall_3 AXF_BODY`, por `rfl`). -/
def AXF_BODY : Formula :=
  substfc (.var 2) (.var 1) (forallc (.var 0))
    =eq forallc (substfc (succ (.var 2)) (liftc zero (.var 1)) (.var 0))

theorem AXF_BODY_ok : ax_substfc_forall = forall_3 AXF_BODY := rfl

/-- **(c) — el LADRILLO**: instancia de `ax_substfc_forall` **dentro de `Prov`**, con testigos
    dotados ABSTRACTOS `ȧ`, `ḃ`, `ḟ`. -/
theorem pcc_substfc_forall_dot (a b f : Term) :
    Prf (provFromCode (eqCodeFn
      (substfcT (tcFn a) (tcFn b) (unT 6 (tcFn f)))
      (unT 6 (substfcT (succcT (tcFn a)) (liftcT (termCode zero) (tcFn b)) (tcFn f))))) := by
  let W2 : Term := liftc zero (liftc zero (tcFn a))
  let W1 : Term := liftc zero (tcFn b)
  let W0 : Term := tcFn f
  -- (1) el `substfc` de nivel 2 se COMPUTA (`substCodeF 2 W2 AXF_BODY` es el código explícito)
  have hin : Prf (substfc (succ (succ zero)) W2 (formCode AXF_BODY)
      =eq eqCodeFn
        (substfcT W2 (varc (numeral 1)) (unT 6 (varc (numeral 0))))
        (unT 6 (substfcT (succcT W2) (liftcT (termCode zero) (varc (numeral 1)))
          (varc (numeral 0))))) :=
    prf_substfc_arith_open 2 W2 AXF_BODY
  -- (2) normaliza el testigo doblemente levantado: `W2 =eq ȧ`
  have hA2 : Prf (W2 =eq tcFn a) :=
    prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn a)) (prf_liftc_tcFn a)
  have hnorm : Prf (eqCodeFn
        (substfcT W2 (varc (numeral 1)) (unT 6 (varc (numeral 0))))
        (unT 6 (substfcT (succcT W2) (liftcT (termCode zero) (varc (numeral 1)))
          (varc (numeral 0))))
      =eq eqCodeFn
        (substfcT (tcFn a) (varc (numeral 1)) (unT 6 (varc (numeral 0))))
        (unT 6 (substfcT (succcT (tcFn a)) (liftcT (termCode zero) (varc (numeral 1)))
          (varc (numeral 0))))) :=
    prf_congr_eqCodeFn
      (prf_congr_substfcT hA2 (prf_refl _) (prf_refl _))
      (prf_congr_unT (prf_congr_substfcT (prf_congr_succcT hA2) (prf_refl _) (prf_refl _)))
  -- (3) el `substfc` de nivel 1 (testigo `liftc zero ḃ`), sobre el código explícito
  have hv1 : Prf (substtc (succ zero) W1 (varc (numeral 1)) =eq tcFn b) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (succ zero) W1 (numeral 1)) (prf_refl _))
      (prf_liftc_tcFn b)
  have hv0 : Prf (substtc (succ zero) W1 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (succ zero) W1 (numeral 0)) (prf_zero_lt_succ zero)
  have ha1 : Prf (substtc (succ zero) W1 (tcFn a) =eq tcFn a) := prf_substtc_tcFn_at 1 W1 a
  have hmid : Prf (substfc (succ zero) W1 (eqCodeFn
        (substfcT (tcFn a) (varc (numeral 1)) (unT 6 (varc (numeral 0))))
        (unT 6 (substfcT (succcT (tcFn a)) (liftcT (termCode zero) (varc (numeral 1)))
          (varc (numeral 0)))))
      =eq eqCodeFn
        (substfcT (tcFn a) (tcFn b) (unT 6 (varc (numeral 0))))
        (unT 6 (substfcT (succcT (tcFn a)) (liftcT (termCode zero) (tcFn b))
          (varc (numeral 0))))) := by
    refine prf_eq_trans (prf_substfc_eq (succ zero) W1 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substfcT (succ zero) W1 _ _ _) ?_
      refine prf_congr_substfcT ha1 hv1 ?_
      exact prf_eq_trans (prf_substtc_unT_at 6 1 W1 (varc (numeral 0))) (prf_congr_unT hv0)
    · refine prf_eq_trans (prf_substtc_unT_at 6 1 W1 _) ?_
      refine prf_congr_unT ?_
      refine prf_eq_trans (prf_substtc_substfcT (succ zero) W1 _ _ _) ?_
      refine prf_congr_substfcT ?_ ?_ hv0
      · exact prf_eq_trans (prf_substtc_succcT (succ zero) W1 (tcFn a)) (prf_congr_succcT ha1)
      · exact prf_eq_trans (prf_substtc_liftcT (succ zero) W1 _ _)
          (prf_congr_liftcT (prf_substtc_termCode_zero 1 W1) hv1)
  -- (4) el `substfc` EXTERNO (nivel 0, testigo `ḟ`)
  have hout : Prf (substfc zero W0 (eqCodeFn
        (substfcT (tcFn a) (tcFn b) (unT 6 (varc (numeral 0))))
        (unT 6 (substfcT (succcT (tcFn a)) (liftcT (termCode zero) (tcFn b))
          (varc (numeral 0)))))
      =eq eqCodeFn
        (substfcT (tcFn a) (tcFn b) (unT 6 (tcFn f)))
        (unT 6 (substfcT (succcT (tcFn a)) (liftcT (termCode zero) (tcFn b)) (tcFn f)))) := by
    refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_substfcT zero W0 _ _ _) ?_
      refine prf_congr_substfcT (prf_substtc_tcFn W0 a) (prf_substtc_tcFn W0 b) ?_
      exact prf_eq_trans (prf_substtc_unT_at 6 0 W0 (varc (numeral 0)))
        (prf_congr_unT (prf_substtc_varc0 W0))
    · refine prf_eq_trans (prf_substtc_unT_at 6 0 W0 _) ?_
      refine prf_congr_unT ?_
      refine prf_eq_trans (prf_substtc_substfcT zero W0 _ _ _) ?_
      refine prf_congr_substfcT ?_ ?_ (prf_substtc_varc0 W0)
      · exact prf_eq_trans (prf_substtc_succcT zero W0 (tcFn a))
          (prf_congr_succcT (prf_substtc_tcFn W0 a))
      · exact prf_eq_trans (prf_substtc_liftcT zero W0 _ _)
          (prf_congr_liftcT (prf_substtc_termCode_zero 0 W0) (prf_substtc_tcFn W0 b))
  -- (5) ensamblar
  have hchain : Prf (substfc zero W0 (substfc (succ zero) W1
      (substfc (succ (succ zero)) W2 (formCode AXF_BODY)))
      =eq eqCodeFn
        (substfcT (tcFn a) (tcFn b) (unT 6 (tcFn f)))
        (unT 6 (substfcT (succcT (tcFn a)) (liftcT (termCode zero) (tcFn b)) (tcFn f)))) :=
    prf_eq_trans (prf_congr_substfc_arg3
      (prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hmid)) hout
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst3 AXF_BODY (show ax_substfc_forall ∈ axioms by simp [axioms])
      (tcFn a) (tcFn b) (tcFn f))

end CtorDesdeC

#print axioms CtorDesdeC.prf_substtc_funcc3
#print axioms CtorDesdeC.pcc_substfc_forall_dot
