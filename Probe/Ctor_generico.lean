/-
  Probe/Ctor_generico.lean — PASO 1 del frente `substfc` (vía 2, CERO axiomas).

  Constructores de código DOTADOS de la familia sustitución/lift, por un helper GENÉRICO
  en la aridad (`fn1T`/`fn2T`/`fn3T`), más su kit (congruencia, `substtc`, `liftc`,
  invariancias, puente `_termCode` por `rfl`), y la prueba de fuego (a)/(b)/(c).

  NO se define ningún `axiom`. `substfcT` & cía. son CONSTRUCTORES DE CÓDIGO, nada más.
-/
import ROBINSON_PlusPlus.Meta

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ArithPrf ROBINSON_PlusPlus.Meta.TcArithPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.MpCodePrf
open ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
open ROBINSON_PlusPlus.Meta.EvalArithPrf ROBINSON_PlusPlus.Meta.EvalListPrf
open ROBINSON_PlusPlus.Meta.EvalLtPrf ROBINSON_PlusPlus.Meta.EvalNthcPrf
open ROBINSON_PlusPlus.Meta.DotConsPrf ROBINSON_PlusPlus.Meta.BdAllIntroPrf
open ROBINSON_PlusPlus.Meta.DerivCondPrf

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace CtorGenerico

/-! ## 0. LA PIEZA QUE FALTABA: `prf_substtc_funcc3` (y los tres gemelos `liftc`)

`prf_substtc_funcc1` (`EvalArithPrf:130`) y `prf_substtc_funcc2` (`:138`) existían; el ternario
no, y los tres constructores ternarios de la familia (`substfcT`/`substtcT`/`substtscT`) lo
necesitan. Mismo patrón que `funcc2`: un `prf_substtc_func` + un `prf_substtsc_cons` por argumento
+ el `prf_substtsc_nil` final. -/

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

/-- `liftc` sobre un `funcc` de **un** argumento (no existía ninguno de los tres). -/
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

/-! ## 1. EL HELPER GENÉRICO POR ARIDAD

Un constructor de código de un símbolo de función `s` de aridad `n` es SIEMPRE
`funcc ⌜s⌝ [a₁,…,aₙ]`. Así que todo el kit (congruencia, distribución de `substtc`/`liftc`,
invariancia, puente `_termCode`) se demuestra **una vez por aridad**, no una vez por símbolo. -/

/-- Constructor de código genérico, aridad 1. -/
def fn1T (s : String) (x : Term) : Term := funcc (strCode s) (cons x nil)
/-- Constructor de código genérico, aridad 2. -/
def fn2T (s : String) (x y : Term) : Term := funcc (strCode s) (cons x (cons y nil))
/-- Constructor de código genérico, aridad 3. -/
def fn3T (s : String) (x y z : Term) : Term :=
  funcc (strCode s) (cons x (cons y (cons z nil)))

/-! ### Puentes `_termCode` GENÉRICOS, por `rfl` -/

theorem fn1T_termCode (s : String) (a : Term) :
    fn1T s (termCode a) = termCode (Term.func s [a]) := rfl
theorem fn2T_termCode (s : String) (a b : Term) :
    fn2T s (termCode a) (termCode b) = termCode (Term.func s [a, b]) := rfl
theorem fn3T_termCode (s : String) (a b c : Term) :
    fn3T s (termCode a) (termCode b) (termCode c) = termCode (Term.func s [a, b, c]) := rfl

/-! ### Congruencia genérica -/

theorem prf_congr_fn1T {s : String} {x x' : Term} (hx : Prf (x =eq x')) :
    Prf (fn1T s x =eq fn1T s x') :=
  prf_congr_funcc2 (prf_congr_cons_head hx)

theorem prf_congr_fn2T {s : String} {x x' y y' : Term}
    (hx : Prf (x =eq x')) (hy : Prf (y =eq y')) :
    Prf (fn2T s x y =eq fn2T s x' y') :=
  prf_congr_funcc2
    (prf_eq_trans (prf_congr_cons_head hx) (prf_congr_cons_tail (prf_congr_cons_head hy)))

theorem prf_congr_fn3T {s : String} {x x' y y' z z' : Term}
    (hx : Prf (x =eq x')) (hy : Prf (y =eq y')) (hz : Prf (z =eq z')) :
    Prf (fn3T s x y z =eq fn3T s x' y' z') :=
  prf_congr_funcc2
    (prf_eq_trans (prf_congr_cons_head hx)
      (prf_congr_cons_tail
        (prf_eq_trans (prf_congr_cons_head hy)
          (prf_congr_cons_tail (prf_congr_cons_head hz)))))

/-! ### `substtc` y `liftc` atraviesan, genéricamente -/

theorem prf_substtc_fn1T (s : String) (v W x : Term) :
    Prf (substtc v W (fn1T s x) =eq fn1T s (substtc v W x)) :=
  prf_substtc_funcc1 v W (strCode s) x
theorem prf_substtc_fn2T (s : String) (v W x y : Term) :
    Prf (substtc v W (fn2T s x y) =eq fn2T s (substtc v W x) (substtc v W y)) :=
  prf_substtc_funcc2 v W (strCode s) x y
theorem prf_substtc_fn3T (s : String) (v W x y z : Term) :
    Prf (substtc v W (fn3T s x y z)
      =eq fn3T s (substtc v W x) (substtc v W y) (substtc v W z)) :=
  prf_substtc_funcc3 v W (strCode s) x y z

theorem prf_liftc_fn1T (s : String) (c x : Term) :
    Prf (liftc c (fn1T s x) =eq fn1T s (liftc c x)) :=
  prf_liftc_funcc1 c (strCode s) x
theorem prf_liftc_fn2T (s : String) (c x y : Term) :
    Prf (liftc c (fn2T s x y) =eq fn2T s (liftc c x) (liftc c y)) :=
  prf_liftc_funcc2 c (strCode s) x y
theorem prf_liftc_fn3T (s : String) (c x y z : Term) :
    Prf (liftc c (fn3T s x y z) =eq fn3T s (liftc c x) (liftc c y) (liftc c z)) :=
  prf_liftc_funcc3 c (strCode s) x y z

/-! ### Invariancias genéricas (la forma `∀ W`, que es lo que consumen los Leibniz internos) -/

theorem substtc_inv_fn1T {s : String} {X : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    ∀ W, Prf (substtc zero W (fn1T s X) =eq fn1T s X) :=
  fun W => prf_eq_trans (prf_substtc_fn1T s zero W X) (prf_congr_fn1T (hX W))

theorem substtc_inv_fn2T {s : String} {X Y : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y)) :
    ∀ W, Prf (substtc zero W (fn2T s X Y) =eq fn2T s X Y) :=
  fun W => prf_eq_trans (prf_substtc_fn2T s zero W X Y) (prf_congr_fn2T (hX W) (hY W))

theorem substtc_inv_fn3T {s : String} {X Y Z : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y))
    (hZ : ∀ W, Prf (substtc zero W Z =eq Z)) :
    ∀ W, Prf (substtc zero W (fn3T s X Y Z) =eq fn3T s X Y Z) :=
  fun W => prf_eq_trans (prf_substtc_fn3T s zero W X Y Z)
    (prf_congr_fn3T (hX W) (hY W) (hZ W))

theorem liftc_inv_fn1T {s : String} {X : Term}
    (hX : ∀ c, Prf (liftc c X =eq X)) :
    ∀ c, Prf (liftc c (fn1T s X) =eq fn1T s X) :=
  fun c => prf_eq_trans (prf_liftc_fn1T s c X) (prf_congr_fn1T (hX c))

theorem liftc_inv_fn2T {s : String} {X Y : Term}
    (hX : ∀ c, Prf (liftc c X =eq X)) (hY : ∀ c, Prf (liftc c Y =eq Y)) :
    ∀ c, Prf (liftc c (fn2T s X Y) =eq fn2T s X Y) :=
  fun c => prf_eq_trans (prf_liftc_fn2T s c X Y) (prf_congr_fn2T (hX c) (hY c))

theorem liftc_inv_fn3T {s : String} {X Y Z : Term}
    (hX : ∀ c, Prf (liftc c X =eq X)) (hY : ∀ c, Prf (liftc c Y =eq Y))
    (hZ : ∀ c, Prf (liftc c Z =eq Z)) :
    ∀ c, Prf (liftc c (fn3T s X Y Z) =eq fn3T s X Y Z) :=
  fun c => prf_eq_trans (prf_liftc_fn3T s c X Y Z) (prf_congr_fn3T (hX c) (hY c) (hZ c))

/-! ## 2. LOS SEIS CONSTRUCTORES, POR INSTANCIACIÓN

Cada uno es UNA línea, y su kit entero (5 lemas) son SEIS líneas. Sin el helper serían
6 × (1 def + 1 congr + 1 substtc + 1 liftc + 1 inv + 1 puente) ≈ 6 bloques de ~20 líneas. -/

/-- Constructor de código del término `substfc v s f`. -/
def substfcT  (v s f  : Term) : Term := fn3T "substfc"  v s f
/-- Constructor de código del término `substtc v s t`. -/
def substtcT  (v s t  : Term) : Term := fn3T "substtc"  v s t
/-- Constructor de código del término `substtsc v s ts`. -/
def substtscT (v s ts : Term) : Term := fn3T "substtsc" v s ts
/-- Constructor de código del término `liftc c t`. -/
def liftcT    (c t    : Term) : Term := fn2T "liftc"    c t
/-- Constructor de código del término `liftfc c f`. -/
def liftfcT   (c f    : Term) : Term := fn2T "liftfc"   c f
/-- Constructor de código del término `liftsc c ts`. -/
def liftscT   (c ts   : Term) : Term := fn2T "liftsc"   c ts

/-! ### Los puentes `_termCode`, todos por `rfl` -/

theorem substfcT_termCode (a b c : Term) :
    substfcT (termCode a) (termCode b) (termCode c) = termCode (substfc a b c) := rfl
theorem substtcT_termCode (a b c : Term) :
    substtcT (termCode a) (termCode b) (termCode c) = termCode (substtc a b c) := rfl
theorem substtscT_termCode (a b c : Term) :
    substtscT (termCode a) (termCode b) (termCode c) = termCode (substtsc a b c) := rfl
theorem liftcT_termCode (a b : Term) :
    liftcT (termCode a) (termCode b) = termCode (liftc a b) := rfl
theorem liftfcT_termCode (a b : Term) :
    liftfcT (termCode a) (termCode b) = termCode (liftfc a b) := rfl
theorem liftscT_termCode (a b : Term) :
    liftscT (termCode a) (termCode b) = termCode (liftsc a b) := rfl

/-! ### Congruencias -/

theorem prf_congr_substfcT {v v' s s' f f' : Term}
    (hv : Prf (v =eq v')) (hs : Prf (s =eq s')) (hf : Prf (f =eq f')) :
    Prf (substfcT v s f =eq substfcT v' s' f') := prf_congr_fn3T hv hs hf
theorem prf_congr_substtcT {v v' s s' t t' : Term}
    (hv : Prf (v =eq v')) (hs : Prf (s =eq s')) (ht : Prf (t =eq t')) :
    Prf (substtcT v s t =eq substtcT v' s' t') := prf_congr_fn3T hv hs ht
theorem prf_congr_substtscT {v v' s s' t t' : Term}
    (hv : Prf (v =eq v')) (hs : Prf (s =eq s')) (ht : Prf (t =eq t')) :
    Prf (substtscT v s t =eq substtscT v' s' t') := prf_congr_fn3T hv hs ht
theorem prf_congr_liftcT {c c' t t' : Term}
    (hc : Prf (c =eq c')) (ht : Prf (t =eq t')) :
    Prf (liftcT c t =eq liftcT c' t') := prf_congr_fn2T hc ht
theorem prf_congr_liftfcT {c c' t t' : Term}
    (hc : Prf (c =eq c')) (ht : Prf (t =eq t')) :
    Prf (liftfcT c t =eq liftfcT c' t') := prf_congr_fn2T hc ht
theorem prf_congr_liftscT {c c' t t' : Term}
    (hc : Prf (c =eq c')) (ht : Prf (t =eq t')) :
    Prf (liftscT c t =eq liftscT c' t') := prf_congr_fn2T hc ht

/-! ### Conmutación con `substtc` -/

theorem prf_substtc_substfcT (w W v s f : Term) :
    Prf (substtc w W (substfcT v s f)
      =eq substfcT (substtc w W v) (substtc w W s) (substtc w W f)) :=
  prf_substtc_fn3T _ w W v s f
theorem prf_substtc_substtcT (w W v s t : Term) :
    Prf (substtc w W (substtcT v s t)
      =eq substtcT (substtc w W v) (substtc w W s) (substtc w W t)) :=
  prf_substtc_fn3T _ w W v s t
theorem prf_substtc_substtscT (w W v s t : Term) :
    Prf (substtc w W (substtscT v s t)
      =eq substtscT (substtc w W v) (substtc w W s) (substtc w W t)) :=
  prf_substtc_fn3T _ w W v s t
theorem prf_substtc_liftcT (w W c t : Term) :
    Prf (substtc w W (liftcT c t) =eq liftcT (substtc w W c) (substtc w W t)) :=
  prf_substtc_fn2T _ w W c t
theorem prf_substtc_liftfcT (w W c t : Term) :
    Prf (substtc w W (liftfcT c t) =eq liftfcT (substtc w W c) (substtc w W t)) :=
  prf_substtc_fn2T _ w W c t
theorem prf_substtc_liftscT (w W c t : Term) :
    Prf (substtc w W (liftscT c t) =eq liftscT (substtc w W c) (substtc w W t)) :=
  prf_substtc_fn2T _ w W c t

/-! ### Conmutación con `liftc` -/

theorem prf_liftc_substfcT (k v s f : Term) :
    Prf (liftc k (substfcT v s f) =eq substfcT (liftc k v) (liftc k s) (liftc k f)) :=
  prf_liftc_fn3T _ k v s f
theorem prf_liftc_substtcT (k v s t : Term) :
    Prf (liftc k (substtcT v s t) =eq substtcT (liftc k v) (liftc k s) (liftc k t)) :=
  prf_liftc_fn3T _ k v s t
theorem prf_liftc_substtscT (k v s t : Term) :
    Prf (liftc k (substtscT v s t) =eq substtscT (liftc k v) (liftc k s) (liftc k t)) :=
  prf_liftc_fn3T _ k v s t
theorem prf_liftc_liftcT (k c t : Term) :
    Prf (liftc k (liftcT c t) =eq liftcT (liftc k c) (liftc k t)) := prf_liftc_fn2T _ k c t
theorem prf_liftc_liftfcT (k c t : Term) :
    Prf (liftc k (liftfcT c t) =eq liftfcT (liftc k c) (liftc k t)) := prf_liftc_fn2T _ k c t
theorem prf_liftc_liftscT (k c t : Term) :
    Prf (liftc k (liftscT c t) =eq liftscT (liftc k c) (liftc k t)) := prf_liftc_fn2T _ k c t

/-! ### Invariancias `substtc` (la forma que descarga la hipótesis `hX` de los Leibniz internos) -/

theorem substtc_inv_substfcT {V S F : Term}
    (hV : ∀ W, Prf (substtc zero W V =eq V)) (hS : ∀ W, Prf (substtc zero W S =eq S))
    (hF : ∀ W, Prf (substtc zero W F =eq F)) :
    ∀ W, Prf (substtc zero W (substfcT V S F) =eq substfcT V S F) := substtc_inv_fn3T hV hS hF
theorem substtc_inv_substtcT {V S T : Term}
    (hV : ∀ W, Prf (substtc zero W V =eq V)) (hS : ∀ W, Prf (substtc zero W S =eq S))
    (hT : ∀ W, Prf (substtc zero W T =eq T)) :
    ∀ W, Prf (substtc zero W (substtcT V S T) =eq substtcT V S T) := substtc_inv_fn3T hV hS hT
theorem substtc_inv_substtscT {V S T : Term}
    (hV : ∀ W, Prf (substtc zero W V =eq V)) (hS : ∀ W, Prf (substtc zero W S =eq S))
    (hT : ∀ W, Prf (substtc zero W T =eq T)) :
    ∀ W, Prf (substtc zero W (substtscT V S T) =eq substtscT V S T) := substtc_inv_fn3T hV hS hT
theorem substtc_inv_liftcT {C T : Term}
    (hC : ∀ W, Prf (substtc zero W C =eq C)) (hT : ∀ W, Prf (substtc zero W T =eq T)) :
    ∀ W, Prf (substtc zero W (liftcT C T) =eq liftcT C T) := substtc_inv_fn2T hC hT
theorem substtc_inv_liftfcT {C T : Term}
    (hC : ∀ W, Prf (substtc zero W C =eq C)) (hT : ∀ W, Prf (substtc zero W T =eq T)) :
    ∀ W, Prf (substtc zero W (liftfcT C T) =eq liftfcT C T) := substtc_inv_fn2T hC hT
theorem substtc_inv_liftscT {C T : Term}
    (hC : ∀ W, Prf (substtc zero W C =eq C)) (hT : ∀ W, Prf (substtc zero W T =eq T)) :
    ∀ W, Prf (substtc zero W (liftscT C T) =eq liftscT C T) := substtc_inv_fn2T hC hT

end CtorGenerico
