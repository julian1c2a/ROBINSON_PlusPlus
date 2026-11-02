/-  ADVERSARIAL: puente KERNEL entre las 17 casillas que el probe B3B DUPLICA
    y sus homonimas de PRODUCCION (7 en EvalArithPrf, 10 en LiftcCodePrf).
    El agente declaro esto como "lectura, no kernel". Aqui se compila.        -/
import ROBINSON_PlusPlus.Meta.LiftcCodePrf

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

namespace BR




open ROBINSON_PlusPlus.Meta.EvalArithPrf (prf_substtc_funcc2 prf_substtc_funcc3 prf_congr_funcc3)

/-! ### Copias LITERALES tomadas de Probe/B3B_substfcex.lean -/

def substfcT  (v s f  : Term) : Term := funcc (strCode "substfc")  (cons v (cons s (cons f nil)))
def liftcT    (c t    : Term) : Term := funcc (strCode "liftc")    (cons c (cons t nil))
def liftscT   (c ts   : Term) : Term := funcc (strCode "liftsc")   (cons c (cons ts nil))

/-! ## PUENTE 1 · los tres `def` -/
example : @substfcT = @ROBINSON_PlusPlus.Meta.EvalArithPrf.substfcT := rfl
example : @liftcT   = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.liftcT   := rfl
example : @liftscT  = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.liftscT  := rfl

/-! ## PUENTE 2 · las 14 casillas restantes: se copia el ENUNCIADO del probe y se
    ofrece como prueba EXCLUSIVAMENTE la constante de PRODUCCION. Si el enunciado
    del probe divergiera del de produccion, esto NO compila. -/

theorem X_substfcT_termCode (v s f : Term) :
    substfcT (termCode v) (termCode s) (termCode f) = termCode (substfc v s f) :=
  ROBINSON_PlusPlus.Meta.EvalArithPrf.substfcT_termCode v s f
theorem X_liftcT_termCode (c t : Term) :
    liftcT (termCode c) (termCode t) = termCode (liftc c t) :=
  ROBINSON_PlusPlus.Meta.LiftcCodePrf.liftcT_termCode c t
theorem X_liftscT_termCode (c ts : Term) :
    liftscT (termCode c) (termCode ts) = termCode (liftsc c ts) :=
  ROBINSON_PlusPlus.Meta.LiftcCodePrf.liftscT_termCode c ts

theorem X_prf_congr_substfcT {v v' s s' f f' : Term}
    (hv : Prf (v =eq v')) (hs : Prf (s =eq s')) (hf : Prf (f =eq f')) :
    Prf (substfcT v s f =eq substfcT v' s' f') := ROBINSON_PlusPlus.Meta.EvalArithPrf.prf_congr_substfcT hv hs hf
theorem X_prf_congr_liftcT {c c' t t' : Term} (hc : Prf (c =eq c')) (ht : Prf (t =eq t')) :
    Prf (liftcT c t =eq liftcT c' t') := ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_congr_liftcT hc ht
theorem X_prf_congr_liftscT {c c' t t' : Term} (hc : Prf (c =eq c')) (ht : Prf (t =eq t')) :
    Prf (liftscT c t =eq liftscT c' t') := ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_congr_liftscT hc ht

theorem X_prf_substtc_substfcT (v W x y z : Term) :
    Prf (substtc v W (substfcT x y z)
      =eq substfcT (substtc v W x) (substtc v W y) (substtc v W z)) :=
  ROBINSON_PlusPlus.Meta.EvalArithPrf.prf_substtc_substfcT v W x y z
theorem X_prf_substtc_liftcT (v W x y : Term) :
    Prf (substtc v W (liftcT x y) =eq liftcT (substtc v W x) (substtc v W y)) :=
  ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_liftcT v W x y
theorem X_prf_substtc_liftscT (v W x y : Term) :
    Prf (substtc v W (liftscT x y) =eq liftscT (substtc v W x) (substtc v W y)) :=
  ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substtc_liftscT v W x y

theorem X_substtc_inv_substfcT {X Y Z : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y))
    (hZ : ∀ W, Prf (substtc zero W Z =eq Z)) :
    ∀ W, Prf (substtc zero W (substfcT X Y Z) =eq substfcT X Y Z) :=
  ROBINSON_PlusPlus.Meta.EvalArithPrf.substtc_inv_substfcT hX hY hZ
theorem X_substtc_inv_liftcT {X Y : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y)) :
    ∀ W, Prf (substtc zero W (liftcT X Y) =eq liftcT X Y) := ROBINSON_PlusPlus.Meta.LiftcCodePrf.substtc_inv_liftcT hX hY
theorem X_substtc_inv_liftscT {X Y : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y)) :
    ∀ W, Prf (substtc zero W (liftscT X Y) =eq liftscT X Y) := ROBINSON_PlusPlus.Meta.LiftcCodePrf.substtc_inv_liftscT hX hY

theorem X_liftTerm_substfcT (k : Nat) (v s f : Term) :
    liftTerm k (substfcT v s f) = substfcT (liftTerm k v) (liftTerm k s) (liftTerm k f) :=
  ROBINSON_PlusPlus.Meta.EvalArithPrf.liftTerm_substfcT k v s f
theorem X_substTerm_substfcT (k : Nat) (u v s f : Term) :
    substTerm k u (substfcT v s f)
      = substfcT (substTerm k u v) (substTerm k u s) (substTerm k u f) :=
  ROBINSON_PlusPlus.Meta.EvalArithPrf.substTerm_substfcT k u v s f

/-! ## PUENTE 3 · CONTROL NEGATIVO: el puente NO es vacuo. Un enunciado FALSEADO
    (cambio `liftc` por `liftfc` en la cadena) debe RECHAZARSE. -/
def liftfcT (c f : Term) : Term := funcc (strCode "liftfc") (cons c (cons f nil))
example : True := by
  fail_if_success (exact (rfl : @liftfcT = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.liftcT))
  trivial

end BR
