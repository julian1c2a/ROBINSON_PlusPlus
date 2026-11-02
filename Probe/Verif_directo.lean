/- # PASO 1 del frente ③ (`pcc_eval_substfc`): los SEIS constructores dotados de la familia
   sustitución/lift, con su kit completo, y la PRUEBA DE FUEGO.

   ESTRATEGIA 2 (DIRECTO): se copia el bloque de `nthcT` (`Meta/EvalNthcPrf.lean:64-75`,
   `:267`) una vez por constructor, sin buscar generalidad.

   ⚠️ CERO AXIOMAS: aquí NO se declara ningún `axiom`. `substfcT`/`liftcT`/… son
   CONSTRUCTORES DE CÓDIGO (`def`s sobre `funcc`), nada más. La ecuación
   `tcFn (substfc v s f) = substfcT (tcFn v) (tcFn s) (tcFn f)` NO se postula:
   el precedente `pcc_dot_cons` dice que su sitio es DENTRO de `Prov`.
-/
import ROBINSON_PlusPlus.Meta

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.TcArithPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.MpCodePrf
open ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
open ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
open ROBINSON_PlusPlus.Meta.EvalArithPrf
open ROBINSON_PlusPlus.Meta.EvalListPrf
open ROBINSON_PlusPlus.Meta.EvalNthcPrf
open ROBINSON_PlusPlus.Meta.EvalLtPrf
open ROBINSON_PlusPlus.Meta.NatArithPrf
open ROBINSON_PlusPlus.Meta.DotConsPrf
open ROBINSON_PlusPlus.Meta.CodeCtorKit
open ROBINSON_PlusPlus.Meta.DerivCondPrf

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace CtorDirecto

/-! ## 0 · Las piezas GENÉRICAS que faltaban

`prf_substtc_funcc1` (`EvalArithPrf:130`) y `prf_substtc_funcc2` (`:138`) existen; el
**ternario no**, y los tres constructores ternarios de abajo lo necesitan. Se añade también
la familia `liftc` (que sólo existía a nivel `funcc` pelado, `prf_liftc_func`). -/

/-- `substtc` sobre un `funcc` de **tres** argumentos. **La pieza que faltaba.** -/
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

/-- `liftc` sobre un `funcc` de **un** argumento. -/
theorem prf_liftc_funcc1 (c sc x : Term) :
    Prf (liftc c (funcc sc (cons x nil)) =eq funcc sc (cons (liftc c x) nil)) :=
  prf_eq_trans (prf_liftc_func c sc (cons x nil))
    (prf_congr_funcc2
      (prf_eq_trans (prf_liftsc_cons c x nil)
        (prf_congr_cons_tail (prf_liftsc_nil c))))

/-- `liftc` sobre un `funcc` de **dos** argumentos. -/
theorem prf_liftc_funcc2 (c sc x y : Term) :
    Prf (liftc c (funcc sc (cons x (cons y nil)))
      =eq funcc sc (cons (liftc c x) (cons (liftc c y) nil))) :=
  prf_eq_trans (prf_liftc_func c sc (cons x (cons y nil)))
    (prf_congr_funcc2
      (prf_eq_trans (prf_liftsc_cons c x (cons y nil))
        (prf_congr_cons_tail
          (prf_eq_trans (prf_liftsc_cons c y nil)
            (prf_congr_cons_tail (prf_liftsc_nil c))))))

/-- `liftc` sobre un `funcc` de **tres** argumentos. -/
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

/-- Congruencia genérica de `funcc` de 3 argumentos (la usan las tres congruencias ternarias). -/
theorem prf_congr_funcc3 {sc x x' y y' z z' : Term}
    (hx : Prf (x =eq x')) (hy : Prf (y =eq y')) (hz : Prf (z =eq z')) :
    Prf (funcc sc (cons x (cons y (cons z nil)))
      =eq funcc sc (cons x' (cons y' (cons z' nil)))) :=
  prf_congr_funcc2 (prf_eq_trans (prf_congr_cons_head hx)
    (prf_congr_cons_tail (prf_eq_trans (prf_congr_cons_head hy)
      (prf_congr_cons_tail (prf_congr_cons_head hz)))))

/-- **Invariancia de un código CERRADO a nivel ARBITRARIO.** `prf_substtc_arith_open` +
    `substCodeT_closed`; es la generalización en el nivel de `substtc_inv_termCode_of_tc`
    (que sólo vale en `zero`) y la necesitan los pasos bajo binder. -/
theorem substtc_inv_termCode_closed_at (k : Nat) (W t : Term) (ht : ∀ c : Nat, liftTerm c t = t) :
    Prf (substtc (numeral k) W (termCode t) =eq termCode t) := by
  have h := prf_substtc_arith_open k W t
  rw [substCodeT_closed k W t ht] at h
  exact h

/-- `substtc` distribuye sobre `unT` **a nivel arbitrario** (la del KIT es sólo nivel `zero`). -/
theorem prf_substtc_unT_at (m k : Nat) (W a : Term)
    (hm : ∀ c : Nat, liftTerm c (numeralM m) = numeralM m) :
    Prf (substtc (numeral k) W (unT m a) =eq unT m (substtc (numeral k) W a)) := by
  unfold unT
  refine prf_eq_trans (prf_substtc_consT (numeral k) W _ _) ?_
  refine prf_congr_consT (substtc_inv_termCode_closed_at k W (numeralM m) hm) ?_
  refine prf_eq_trans (prf_substtc_consT (numeral k) W _ _) ?_
  exact prf_congr_consT (prf_refl _) (substtc_inv_termCode_closed_at k W nil (fun _ => rfl))

/-! ## 1 · `substfcT` (ternario) -/

/-- Constructor de código del término `substfc v s f`: `⟨1, ⌜substfc⌝, [v,s,f]⟩`. -/
def substfcT (v s f : Term) : Term :=
  funcc (strCode "substfc") (cons v (cons s (cons f nil)))

/-- El PUENTE con `termCode`, por `rfl`. -/
theorem substfcT_termCode (v s f : Term) :
    substfcT (termCode v) (termCode s) (termCode f) = termCode (substfc v s f) := rfl

theorem prf_congr_substfcT {v v' s s' f f' : Term}
    (hv : Prf (v =eq v')) (hs : Prf (s =eq s')) (hf : Prf (f =eq f')) :
    Prf (substfcT v s f =eq substfcT v' s' f') := prf_congr_funcc3 hv hs hf

theorem prf_substtc_substfcT (v W x y z : Term) :
    Prf (substtc v W (substfcT x y z)
      =eq substfcT (substtc v W x) (substtc v W y) (substtc v W z)) :=
  prf_substtc_funcc3 v W (strCode "substfc") x y z

theorem prf_liftc_substfcT (c x y z : Term) :
    Prf (liftc c (substfcT x y z) =eq substfcT (liftc c x) (liftc c y) (liftc c z)) :=
  prf_liftc_funcc3 c (strCode "substfc") x y z

theorem substtc_inv_substfcT {X Y Z : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y))
    (hZ : ∀ W, Prf (substtc zero W Z =eq Z)) :
    ∀ W, Prf (substtc zero W (substfcT X Y Z) =eq substfcT X Y Z) :=
  fun W => prf_eq_trans (prf_substtc_substfcT zero W X Y Z)
    (prf_congr_substfcT (hX W) (hY W) (hZ W))

/-! ## 2 · `substtcT` (ternario) -/

def substtcT (v s t : Term) : Term :=
  funcc (strCode "substtc") (cons v (cons s (cons t nil)))

theorem substtcT_termCode (v s t : Term) :
    substtcT (termCode v) (termCode s) (termCode t) = termCode (substtc v s t) := rfl

theorem prf_congr_substtcT {v v' s s' t t' : Term}
    (hv : Prf (v =eq v')) (hs : Prf (s =eq s')) (ht : Prf (t =eq t')) :
    Prf (substtcT v s t =eq substtcT v' s' t') := prf_congr_funcc3 hv hs ht

theorem prf_substtc_substtcT (v W x y z : Term) :
    Prf (substtc v W (substtcT x y z)
      =eq substtcT (substtc v W x) (substtc v W y) (substtc v W z)) :=
  prf_substtc_funcc3 v W (strCode "substtc") x y z

theorem prf_liftc_substtcT (c x y z : Term) :
    Prf (liftc c (substtcT x y z) =eq substtcT (liftc c x) (liftc c y) (liftc c z)) :=
  prf_liftc_funcc3 c (strCode "substtc") x y z

theorem substtc_inv_substtcT {X Y Z : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y))
    (hZ : ∀ W, Prf (substtc zero W Z =eq Z)) :
    ∀ W, Prf (substtc zero W (substtcT X Y Z) =eq substtcT X Y Z) :=
  fun W => prf_eq_trans (prf_substtc_substtcT zero W X Y Z)
    (prf_congr_substtcT (hX W) (hY W) (hZ W))

/-! ## 3 · `substtscT` (ternario) -/

def substtscT (v s ts : Term) : Term :=
  funcc (strCode "substtsc") (cons v (cons s (cons ts nil)))

theorem substtscT_termCode (v s ts : Term) :
    substtscT (termCode v) (termCode s) (termCode ts) = termCode (substtsc v s ts) := rfl

theorem prf_congr_substtscT {v v' s s' ts ts' : Term}
    (hv : Prf (v =eq v')) (hs : Prf (s =eq s')) (hts : Prf (ts =eq ts')) :
    Prf (substtscT v s ts =eq substtscT v' s' ts') := prf_congr_funcc3 hv hs hts

theorem prf_substtc_substtscT (v W x y z : Term) :
    Prf (substtc v W (substtscT x y z)
      =eq substtscT (substtc v W x) (substtc v W y) (substtc v W z)) :=
  prf_substtc_funcc3 v W (strCode "substtsc") x y z

theorem prf_liftc_substtscT (c x y z : Term) :
    Prf (liftc c (substtscT x y z) =eq substtscT (liftc c x) (liftc c y) (liftc c z)) :=
  prf_liftc_funcc3 c (strCode "substtsc") x y z

theorem substtc_inv_substtscT {X Y Z : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y))
    (hZ : ∀ W, Prf (substtc zero W Z =eq Z)) :
    ∀ W, Prf (substtc zero W (substtscT X Y Z) =eq substtscT X Y Z) :=
  fun W => prf_eq_trans (prf_substtc_substtscT zero W X Y Z)
    (prf_congr_substtscT (hX W) (hY W) (hZ W))

/-! ## 4 · `liftcT` (binario) -/

def liftcT (c t : Term) : Term := funcc (strCode "liftc") (cons c (cons t nil))

theorem liftcT_termCode (c t : Term) :
    liftcT (termCode c) (termCode t) = termCode (liftc c t) := rfl

theorem prf_congr_liftcT {c c' t t' : Term} (hc : Prf (c =eq c')) (ht : Prf (t =eq t')) :
    Prf (liftcT c t =eq liftcT c' t') :=
  prf_congr_funcc2 (prf_eq_trans (prf_congr_cons_head hc)
    (prf_congr_cons_tail (prf_congr_cons_head ht)))

theorem prf_substtc_liftcT (v W x y : Term) :
    Prf (substtc v W (liftcT x y) =eq liftcT (substtc v W x) (substtc v W y)) :=
  prf_substtc_funcc2 v W (strCode "liftc") x y

theorem prf_liftc_liftcT (c x y : Term) :
    Prf (liftc c (liftcT x y) =eq liftcT (liftc c x) (liftc c y)) :=
  prf_liftc_funcc2 c (strCode "liftc") x y

theorem substtc_inv_liftcT {X Y : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y)) :
    ∀ W, Prf (substtc zero W (liftcT X Y) =eq liftcT X Y) :=
  fun W => prf_eq_trans (prf_substtc_liftcT zero W X Y) (prf_congr_liftcT (hX W) (hY W))

/-! ## 5 · `liftfcT` (binario) -/

def liftfcT (c f : Term) : Term := funcc (strCode "liftfc") (cons c (cons f nil))

theorem liftfcT_termCode (c f : Term) :
    liftfcT (termCode c) (termCode f) = termCode (liftfc c f) := rfl

theorem prf_congr_liftfcT {c c' f f' : Term} (hc : Prf (c =eq c')) (hf : Prf (f =eq f')) :
    Prf (liftfcT c f =eq liftfcT c' f') :=
  prf_congr_funcc2 (prf_eq_trans (prf_congr_cons_head hc)
    (prf_congr_cons_tail (prf_congr_cons_head hf)))

theorem prf_substtc_liftfcT (v W x y : Term) :
    Prf (substtc v W (liftfcT x y) =eq liftfcT (substtc v W x) (substtc v W y)) :=
  prf_substtc_funcc2 v W (strCode "liftfc") x y

theorem prf_liftc_liftfcT (c x y : Term) :
    Prf (liftc c (liftfcT x y) =eq liftfcT (liftc c x) (liftc c y)) :=
  prf_liftc_funcc2 c (strCode "liftfc") x y

theorem substtc_inv_liftfcT {X Y : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y)) :
    ∀ W, Prf (substtc zero W (liftfcT X Y) =eq liftfcT X Y) :=
  fun W => prf_eq_trans (prf_substtc_liftfcT zero W X Y) (prf_congr_liftfcT (hX W) (hY W))

/-! ## 6 · `liftscT` (binario) -/

def liftscT (c ts : Term) : Term := funcc (strCode "liftsc") (cons c (cons ts nil))

theorem liftscT_termCode (c ts : Term) :
    liftscT (termCode c) (termCode ts) = termCode (liftsc c ts) := rfl

theorem prf_congr_liftscT {c c' ts ts' : Term} (hc : Prf (c =eq c')) (hts : Prf (ts =eq ts')) :
    Prf (liftscT c ts =eq liftscT c' ts') :=
  prf_congr_funcc2 (prf_eq_trans (prf_congr_cons_head hc)
    (prf_congr_cons_tail (prf_congr_cons_head hts)))

theorem prf_substtc_liftscT (v W x y : Term) :
    Prf (substtc v W (liftscT x y) =eq liftscT (substtc v W x) (substtc v W y)) :=
  prf_substtc_funcc2 v W (strCode "liftsc") x y

theorem prf_liftc_liftscT (c x y : Term) :
    Prf (liftc c (liftscT x y) =eq liftscT (liftc c x) (liftc c y)) :=
  prf_liftc_funcc2 c (strCode "liftsc") x y

theorem substtc_inv_liftscT {X Y : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y)) :
    ∀ W, Prf (substtc zero W (liftscT X Y) =eq liftscT X Y) :=
  fun W => prf_eq_trans (prf_substtc_liftscT zero W X Y) (prf_congr_liftscT (hX W) (hY W))

end CtorDirecto

/-! ############ BLOQUE DE VERIFICACION ADVERSARIAL (no toca el fichero auditado) ############ -/

open CtorDirecto

section FootprintTodos

#print axioms CtorDirecto.prf_substtc_funcc3
#print axioms CtorDirecto.prf_liftc_funcc1
#print axioms CtorDirecto.prf_liftc_funcc2
#print axioms CtorDirecto.prf_liftc_funcc3
#print axioms CtorDirecto.prf_congr_funcc3
#print axioms CtorDirecto.substtc_inv_termCode_closed_at
#print axioms CtorDirecto.prf_substtc_unT_at
#print axioms CtorDirecto.substfcT
#print axioms CtorDirecto.substfcT_termCode
#print axioms CtorDirecto.prf_congr_substfcT
#print axioms CtorDirecto.prf_substtc_substfcT
#print axioms CtorDirecto.prf_liftc_substfcT
#print axioms CtorDirecto.substtc_inv_substfcT
#print axioms CtorDirecto.substtcT
#print axioms CtorDirecto.substtcT_termCode
#print axioms CtorDirecto.prf_congr_substtcT
#print axioms CtorDirecto.prf_substtc_substtcT
#print axioms CtorDirecto.prf_liftc_substtcT
#print axioms CtorDirecto.substtc_inv_substtcT
#print axioms CtorDirecto.substtscT
#print axioms CtorDirecto.substtscT_termCode
#print axioms CtorDirecto.prf_congr_substtscT
#print axioms CtorDirecto.prf_substtc_substtscT
#print axioms CtorDirecto.prf_liftc_substtscT
#print axioms CtorDirecto.substtc_inv_substtscT
#print axioms CtorDirecto.liftcT
#print axioms CtorDirecto.liftcT_termCode
#print axioms CtorDirecto.prf_congr_liftcT
#print axioms CtorDirecto.prf_substtc_liftcT
#print axioms CtorDirecto.prf_liftc_liftcT
#print axioms CtorDirecto.substtc_inv_liftcT
#print axioms CtorDirecto.liftfcT
#print axioms CtorDirecto.liftfcT_termCode
#print axioms CtorDirecto.prf_congr_liftfcT
#print axioms CtorDirecto.prf_substtc_liftfcT
#print axioms CtorDirecto.prf_liftc_liftfcT
#print axioms CtorDirecto.substtc_inv_liftfcT
#print axioms CtorDirecto.liftscT
#print axioms CtorDirecto.liftscT_termCode
#print axioms CtorDirecto.prf_congr_liftscT
#print axioms CtorDirecto.prf_substtc_liftscT
#print axioms CtorDirecto.prf_liftc_liftscT
#print axioms CtorDirecto.substtc_inv_liftscT

end FootprintTodos

/-! ## V1 · Los seis constructores DESPLEGADOS (que nadie ha amanado el `def`) -/

example (v s f : Term) :
    substfcT v s f = funcc (strCode "substfc") (cons v (cons s (cons f nil))) := rfl
example (v s t : Term) :
    substtcT v s t = funcc (strCode "substtc") (cons v (cons s (cons t nil))) := rfl
example (v s ts : Term) :
    substtscT v s ts = funcc (strCode "substtsc") (cons v (cons s (cons ts nil))) := rfl
example (c t : Term) : liftcT c t = funcc (strCode "liftc") (cons c (cons t nil)) := rfl
example (c f : Term) : liftfcT c f = funcc (strCode "liftfc") (cons c (cons f nil)) := rfl
example (c ts : Term) : liftscT c ts = funcc (strCode "liftsc") (cons c (cons ts nil)) := rfl

/-! ## V2 · Los puentes, RE-ENUNCIADOS POR MI y exigidos por `rfl` -/

example (v s f : Term) :
    substfcT (termCode v) (termCode s) (termCode f) = termCode (substfc v s f) := rfl
example (v s t : Term) :
    substtcT (termCode v) (termCode s) (termCode t) = termCode (substtc v s t) := rfl
example (v s ts : Term) :
    substtscT (termCode v) (termCode s) (termCode ts) = termCode (substtsc v s ts) := rfl
example (c t : Term) : liftcT (termCode c) (termCode t) = termCode (liftc c t) := rfl
example (c f : Term) : liftfcT (termCode c) (termCode f) = termCode (liftfc c f) := rfl
example (c ts : Term) : liftscT (termCode c) (termCode ts) = termCode (liftsc c ts) := rfl

/-! ## V3 · CONTRA-TEST: si el nombre fuese otro, el puente NO seria `rfl`.
     Si esto compilase, `rfl` estaria probando cualquier cosa. -/

example : True := by
  fail_if_success
    have : ∀ v s f : Term,
        funcc (strCode "substtc") (cons v (cons s (cons f nil))) = termCode (substfc v s f) :=
      fun _ _ _ => rfl
  fail_if_success
    have : ∀ c t : Term, funcc (strCode "liftfc") (cons c (cons t nil)) = termCode (liftc c t) :=
      fun _ _ => rfl
  trivial

/-! ## V3b · La hipotesis de `prf_substtc_unT_at` es SATISFACIBLE para `m` ABSTRACTO
     (no es un teorema vacio). -/

theorem V_numeralM_lift : ∀ (m : Nat) (c : Nat), liftTerm c (numeralM m) = numeralM m
  | 0,     _ => rfl
  | m + 1, c => by
      show liftTerm c (succ (numeralM m)) = succ (numeralM m)
      simp only [succ, liftTerm, liftTerms, V_numeralM_lift m c]

theorem V_unT_at_no_vacio (m k : Nat) (W a : Term) :
    Prf (substtc (numeral k) W (unT m a) =eq unT m (substtc (numeral k) W a)) :=
  prf_substtc_unT_at m k W a (V_numeralM_lift m)

#print axioms V_unT_at_no_vacio

/-! ## V4 · NO-VACUIDAD: las hipotesis de los `substtc_inv_*` SE CUMPLEN de verdad,
     y el lema entrega un `Prf` real sobre codigo CONCRETO. -/

theorem V_hyp_ok (t : Term) (ht : ∀ c : Nat, liftTerm c t = t) :
    ∀ W, Prf (substtc zero W (termCode t) =eq termCode t) :=
  fun W => substtc_inv_termCode_closed_at 0 W t ht

theorem V_inv_substfcT_concreto :
    ∀ W, Prf (substtc zero W
        (substfcT (termCode (numeralM 1)) (termCode (numeralM 2)) (termCode (numeralM 3)))
      =eq substfcT (termCode (numeralM 1)) (termCode (numeralM 2)) (termCode (numeralM 3))) :=
  substtc_inv_substfcT
    (V_hyp_ok (numeralM 1) (fun _ => rfl))
    (V_hyp_ok (numeralM 2) (fun _ => rfl))
    (V_hyp_ok (numeralM 3) (fun _ => rfl))

#print axioms V_inv_substfcT_concreto

/-! ## V5 · PRUEBA DE FUEGO (a): encadenado con `pcc_eq_trans_code`, lado izquierdo `substfcT`. -/

theorem V_fuego_a (A B C Y Z : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A))
    (hB : ∀ W, Prf (substtc zero W B =eq B))
    (hC : ∀ W, Prf (substtc zero W C =eq C))
    (h1 : Prf (provFromCode (eqc (substfcT A B C) Y)))
    (h2 : Prf (provFromCode (eqc Y Z))) :
    Prf (provFromCode (eqc (substfcT A B C) Z)) :=
  pcc_eq_trans_code (substfcT A B C) Y Z (substtc_inv_substfcT hA hB hC) h1 h2

theorem V_fuego_a_liftcT (A B Y Z : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A))
    (hB : ∀ W, Prf (substtc zero W B =eq B))
    (h1 : Prf (provFromCode (eqc (liftcT A B) Y)))
    (h2 : Prf (provFromCode (eqc Y Z))) :
    Prf (provFromCode (eqc (liftcT A B) Z)) :=
  pcc_eq_trans_code (liftcT A B) Y Z (substtc_inv_liftcT hA hB) h1 h2

#print axioms V_fuego_a
#print axioms V_fuego_a_liftcT

/-! ## V6 · PRUEBA DE FUEGO (b): composicion con el KIT (`pcc_congr_unT_code`). -/

theorem V_fuego_b (m : Nat) (A B C Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A))
    (hB : ∀ W, Prf (substtc zero W B =eq B))
    (hC : ∀ W, Prf (substtc zero W C =eq C)) :
    Prf (provFromCode (eqc (substfcT A B C) Y)
      ⇒ provFromCode (eqc (unT m (substfcT A B C)) (unT m Y))) :=
  pcc_congr_unT_code m (substfcT A B C) Y (substtc_inv_substfcT hA hB hC)

#print axioms V_fuego_b

/-! ## V7 · PRUEBA DE FUEGO (c): la instancia de `ax_substfc_forall` DENTRO de `Prov`.
     Se construye AQUI porque el fichero auditado NO la tiene. -/

theorem V_fuego_c_inst (w1 w2 w3 : Term) :
    Prf (provFromCode (substfc zero w3 (substfc (succ zero) (liftc zero w2)
      (substfc (succ (succ zero)) (liftc zero (liftc zero w1))
        (formCode (substfc (.var 2) (.var 1) (forallc (.var 0))
          =eq forallc (substfc (succ (.var 2)) (liftc zero (.var 1)) (.var 0)))))))) :=
  pcc_axiom_inst3 _ (show ax_substfc_forall ∈ axioms by simp [axioms, ax_substfc_forall]) w1 w2 w3

#print axioms V_fuego_c_inst
