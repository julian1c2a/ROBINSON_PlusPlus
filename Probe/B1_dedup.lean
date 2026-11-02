import ROBINSON_PlusPlus.Meta.CodeWitnessPrf
import ROBINSON_PlusPlus.Meta.EvalRunFnPrf

/-
# B1 · AUDITORIA DE DUPLICACION de `sondeos/ReflectorDesdeConsumidor.lean`

Este fichero NO promueve nada. Solo PRUEBA, con puentes `rfl` / habitacion de tipos, en cual de
los tres cajones cae cada declaracion del sondeo:

  1. DUPLICADO EXACTO (ya en produccion, con este u otro nombre)
  2. CASI-DUPLICADO (produccion tiene el caso particular; el sondeo generaliza)
  3. GENUINAMENTE NUEVO

Las copias del sondeo viven en el namespace `Sonda` para poder enfrentarlas a produccion.
-/

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
open ROBINSON_PlusPlus.Meta.HilbertDeduction ROBINSON_PlusPlus.Meta.BoundedInPrf
open ROBINSON_PlusPlus.Meta.ChainPrf ROBINSON_PlusPlus.Meta.ChainOkBoundedPrf
open ROBINSON_PlusPlus.Meta.TrackedCorePrf ROBINSON_PlusPlus.Meta.LineWFSchemaPrf
open ROBINSON_PlusPlus.Meta.LineWFTrackedPrf ROBINSON_PlusPlus.Meta.EvalRunFnPrf
open ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace B1Dedup

/-! ## §0 · COPIA LITERAL de las definiciones del sondeo (namespace `Sonda`) -/

namespace Sonda

def liftcT (c t : Term) : Term := funcc (strCode "liftc") (cons c (cons t nil))
def liftscT (c ts : Term) : Term := funcc (strCode "liftsc") (cons c (cons ts nil))
def varcT (X : Term) : Term := unT 0 X
def funccT (X Y : Term) : Term := binT 1 X Y

def targetLift (s : Term) : Formula :=
  provFromCode (eqc (liftcT (termCode zero) (tcFn s)) (tcFn (liftc zero s)))
def targetLiftsc (b : Term) : Formula :=
  provFromCode (eqc (liftscT (termCode zero) (tcFn b)) (tcFn (liftsc zero b)))

def shapeUn (X : Term) (k : Nat) : Formula :=
  Formula.eq X (cons (numeralM k) (cons (nthc X (numeralM 1)) nil))
def shapeBin (X : Term) (k : Nat) : Formula :=
  Formula.eq X (cons (numeralM k)
    (cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil)))

def argsInBody (wT Y : Term) : Formula :=
  Formula.impl (lt (.var 0) (liftTerm 0 (lenc Y)))
    (In (nthc (liftTerm 0 Y) (.var 0)) (liftTerm 0 wT))
def argsIn (wT Y : Term) : Formula := Formula.forall (argsInBody wT Y)

def isTermCodeE1 (wT X : Term) : Formula :=
  lor (shapeUn X 0) (land (shapeBin X 1) (argsIn wT (nthc X (numeralM 2))))

/-- Copia literal del sondeo (§3). -/
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

theorem prf_substtc_binT_at (m v : Nat) (W a b : Term) :
    Prf (substtc (numeral v) W (binT m a b)
      =eq binT m (substtc (numeral v) W a) (substtc (numeral v) W b)) := by
  unfold binT consT
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  refine prf_congr_funcc2 ?_
  refine prf_eq_trans (prf_congr_cons_head (prf_substtc_termCode_numeralM v m W)) ?_
  refine prf_congr_cons_tail (prf_congr_cons_head ?_)
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  refine prf_congr_funcc2 ?_
  refine prf_congr_cons_tail (prf_congr_cons_head ?_)
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  exact prf_congr_funcc2
    (prf_congr_cons_tail (prf_congr_cons_head (prf_substtc_termCode_zero v W)))

/-- Copia literal del sondeo (§4). -/
theorem prf_substfc_atom2CodeFn (v t : Term) (s : String) (a b : Term) :
    Prf (substfc v t (atom2CodeFn s a b)
      =eq atom2CodeFn s (substtc v t a) (substtc v t b)) := by
  unfold atom2CodeFn
  refine prf_eq_trans (prf_substfc_atom v t (strCode s) (cons a (cons b nil))) ?_
  refine prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head ?_))
  refine prf_eq_trans (prf_substtsc_cons v t a (cons b nil)) ?_
  exact prf_congr_cons_tail
    (prf_eq_trans (prf_substtsc_cons v t b nil) (prf_congr_cons_tail (prf_substtsc_nil v t)))

theorem prf_substfc_ltCodeFn' (v t a b : Term) :
    Prf (substfc v t (ltCodeFn a b) =eq ltCodeFn (substtc v t a) (substtc v t b)) :=
  prf_substfc_atom2CodeFn v t lt_sym a b

/-- Copia literal del sondeo (§3): los envoltorios de `liftcT` sobre los genericos `funcc2`. -/
theorem prf_congr_liftcT {c c' t t' : Term} (hc : Prf (c =eq c')) (ht : Prf (t =eq t')) :
    Prf (liftcT c t =eq liftcT c' t') :=
  prf_congr_funcc2 (prf_eq_trans (prf_congr_cons_head hc)
    (prf_congr_cons_tail (prf_congr_cons_head ht)))

theorem prf_substtc_liftcT (v W x y : Term) :
    Prf (substtc v W (liftcT x y) =eq liftcT (substtc v W x) (substtc v W y)) :=
  prf_substtc_funcc2 v W (strCode "liftc") x y

theorem substtc_inv_liftcT {X Y : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y)) :
    ∀ W, Prf (substtc zero W (liftcT X Y) =eq liftcT X Y) := fun W =>
  prf_eq_trans (prf_substtc_liftcT zero W X Y) (prf_congr_liftcT (hX W) (hY W))

end Sonda

/-! ## §1 · CAJON 1 — COLISION DE NOMBRE CON PRODUCCION.

    Estas siete definiciones/lemas YA EXISTEN en produccion con **el mismo nombre**, en
    `Meta/CodeWitnessPrf.lean` (namespace `SinWTs`) y `Meta/EvalCarcNthcPrf.lean`.
    Promover el sondeo tal cual mete DOS CONSTANTES por cada una. -/

theorem br_shapeUn : @Sonda.shapeUn = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.shapeUn := rfl
theorem br_shapeBin :
    @Sonda.shapeBin = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.shapeBin := rfl
theorem br_argsInBody :
    @Sonda.argsInBody = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.argsInBody := rfl
theorem br_argsIn : @Sonda.argsIn = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.argsIn := rfl
theorem br_isTermCodeE1 :
    @Sonda.isTermCodeE1 = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.isTermCodeE1 := rfl

/-- `impT` del sondeo = `SinWTs.impT` de produccion (mismo enunciado, misma prueba). -/
theorem br_impT {A B C : Formula} (h1 : Prf (A ⇒ B)) (h2 : Prf (B ⇒ C)) : Prf (A ⇒ C) :=
  ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.impT h1 h2

/-- `prf_or_elim_imp` del sondeo = `SinWTs.prf_or_elim_imp` de produccion. -/
theorem br_prf_or_elim_imp {A B C : Formula} (h1 : Prf (A ⇒ C)) (h2 : Prf (B ⇒ C)) :
    Prf (lor A B ⇒ C) :=
  ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_or_elim_imp h1 h2

/-- `PrfH_eq_trans_code` del sondeo = el de `Meta/EvalCarcNthcPrf.lean:66`, byte a byte. -/
theorem br_PrfH_eq_trans_code {Γ : List Formula} (X Y Z : Term)
    (hX : ∀ W, Prf (substtc zero W X =eq X))
    (h1 : PrfH Γ (provFromCode (eqc X Y))) (h2 : PrfH Γ (provFromCode (eqc Y Z))) :
    PrfH Γ (provFromCode (eqc X Z)) :=
  ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf.PrfH_eq_trans_code X Y Z hX h1 h2

/-! ## §2 · CAJON 1 — DUPLICADO EXACTO CON **OTRO NOMBRE** en produccion. -/

/-- `eqc_eq_eqCodeFn` del sondeo es la SIMETRICA de `Sigma1AtomPrf.eqCodeFn_eq_eqc`
    (`Meta/Sigma1AtomPrf.lean:122`), que ya esta en produccion y EXPORTADA. -/
theorem br_eqc_eq_eqCodeFn (a b : Term) : eqc a b = eqCodeFn a b :=
  (eqCodeFn_eq_eqc a b).symm

/-- `iz_inv` del sondeo es LITERALMENTE `prf_substtc_termCode_nil`
    (`Meta/EvalRunFnPrf.lean:103`): `nil` es `zero` por definicion. -/
theorem br_iz_inv : ∀ W, Prf (substtc zero W (termCode zero) =eq termCode zero) :=
  prf_substtc_termCode_nil

/-- Y tambien sale de `substtc_inv_termCode_numeralM 0` (`Meta/LineWFSchemaPrf.lean:84`). -/
theorem br_iz_inv' : ∀ W, Prf (substtc zero W (termCode zero) =eq termCode zero) :=
  substtc_inv_termCode_numeralM 0

/-! ## §3 · CAJON 1 — `varcT` / `funccT` y su familia son ALIAS del KIT de produccion.

    El propio sondeo los DEFINE como `unT 0` / `binT 1`. Todo lo que prueba sobre ellos ya
    esta probado, generico en el tag, en `Meta/CodeCtorKit.lean`. -/

theorem br_varcT (X : Term) : Sonda.varcT X = unT 0 X := rfl
theorem br_funccT (X Y : Term) : Sonda.funccT X Y = binT 1 X Y := rfl

/-- `varcT_termCode` del sondeo ES `unT_termCode 0` (`numeralM 0` reduce a `zero`,
    y `varc x = cons zero (cons x nil)`). -/
theorem br_varcT_termCode (x : Term) : Sonda.varcT (termCode x) = termCode (varc x) :=
  unT_termCode 0 x

/-- `funccT_termCode` del sondeo ES `binT_termCode 1`. -/
theorem br_funccT_termCode (x y : Term) :
    Sonda.funccT (termCode x) (termCode y) = termCode (funcc x y) :=
  binT_termCode 1 x y

/-- `prf_congr_varcT` del sondeo ES `prf_congr_unT` (el sondeo ya lo escribe asi). -/
theorem br_prf_congr_varcT {X X' : Term} (h : Prf (X =eq X')) :
    Prf (Sonda.varcT X =eq Sonda.varcT X') := prf_congr_unT h

/-- `prf_congr_funccT` del sondeo ES `prf_congr_binT`. -/
theorem br_prf_congr_funccT {X X' Y Y' : Term} (hx : Prf (X =eq X')) (hy : Prf (Y =eq Y')) :
    Prf (Sonda.funccT X Y =eq Sonda.funccT X' Y') := prf_congr_binT hx hy

/-- `prf_substtc_varcT_at` / `prf_substtc_funccT_at` son las instancias `m = 0` / `m = 1` de
    `prf_substtc_unT_at` / `prf_substtc_binT_at`; el sondeo ya los escribe asi. -/
theorem br_prf_substtc_varcT_at (v : Nat) (W a : Term) :
    Prf (substtc (numeral v) W (Sonda.varcT a) =eq Sonda.varcT (substtc (numeral v) W a)) :=
  Sonda.prf_substtc_unT_at 0 v W a
theorem br_prf_substtc_funccT_at (v : Nat) (W a b : Term) :
    Prf (substtc (numeral v) W (Sonda.funccT a b)
      =eq Sonda.funccT (substtc (numeral v) W a) (substtc (numeral v) W b)) :=
  Sonda.prf_substtc_binT_at 1 v W a b

/-! ## §4 · CAJON 2 — CASI-DUPLICADOS: produccion tiene EL CASO `v = 0`.

    Aqui esta el peligro real: si entran los dos, el consumidor no sabe cual usar. La
    implicacion va en UNA sola direccion: SONDEO ⟹ PRODUCCION (el sondeo es MAS FUERTE). -/

/-- `prf_substtc_unT` de produccion (`CodeCtorKit.lean:100`) es la instancia `v = 0` del
    `prf_substtc_unT_at` del sondeo. Compila: luego produccion es un caso del sondeo. -/
theorem br_unT_at_implies_prod (m : Nat) (W a : Term) :
    Prf (substtc zero W (unT m a) =eq unT m (substtc zero W a)) :=
  Sonda.prf_substtc_unT_at m 0 W a

/-- El mismo enunciado, tal como lo da produccion. Los DOS terminos habitan el MISMO tipo. -/
theorem br_unT_prod (m : Nat) (W a : Term) :
    Prf (substtc zero W (unT m a) =eq unT m (substtc zero W a)) :=
  prf_substtc_unT m W a

/-- Idem para `binT`: `prf_substtc_binT` (`CodeCtorKit.lean:110`) es el caso `v = 0`. -/
theorem br_binT_at_implies_prod (m : Nat) (W a b : Term) :
    Prf (substtc zero W (binT m a b) =eq binT m (substtc zero W a) (substtc zero W b)) :=
  Sonda.prf_substtc_binT_at m 0 W a b
theorem br_binT_prod (m : Nat) (W a b : Term) :
    Prf (substtc zero W (binT m a b) =eq binT m (substtc zero W a) (substtc zero W b)) :=
  prf_substtc_binT m W a b

/-- `prf_substtc_termCode_numeralM` del sondeo, en `v = 0`, ES
    `substtc_inv_termCode_numeralM` de produccion (`Meta/LineWFSchemaPrf.lean:84`). -/
theorem br_tcNumeralM_at_implies_prod (m : Nat) (W : Term) :
    Prf (substtc zero W (termCode (numeralM m)) =eq termCode (numeralM m)) :=
  Sonda.prf_substtc_termCode_numeralM 0 m W
theorem br_tcNumeralM_prod (m : Nat) (W : Term) :
    Prf (substtc zero W (termCode (numeralM m)) =eq termCode (numeralM m)) :=
  substtc_inv_termCode_numeralM m W

/-- `prf_substtc_termCode_zero` del sondeo, en `v = 0`, ES `prf_substtc_termCode_nil`. -/
theorem br_tcZero_at_implies_prod (W : Term) :
    Prf (substtc zero W (termCode zero) =eq termCode zero) :=
  Sonda.prf_substtc_termCode_zero 0 W

/-- `prf_substtc_termCode_closed` no es mas que `prf_substtc_arith_open` + `substCodeT_closed`,
    AMBOS ya en produccion (`Meta/SubstCodeOpenPrf.lean:83 y 213`): es un envoltorio de 2 lineas.
    Prueba: se re-deriva aqui sin usar el sondeo. -/
theorem br_tcClosed_desde_produccion (v : Nat) (W t : Term) (ht : ∀ c : Nat, liftTerm c t = t) :
    Prf (substtc (numeral v) W (termCode t) =eq termCode t) := by
  have h := prf_substtc_arith_open v W t
  rwa [substCodeT_closed v W t ht] at h

/-! ## §5 · CAJON 2 — `pcc_congr_liftcT_arg2_code` es el patron de `pcc_congr_binT_2_code`.

    No es duplicado (el nodo es `funcc ⌜liftc⌝ …`, no un `binT`), pero es la MISMA construccion
    de Leibniz interno instanciada a otro constructor. Se deja constancia de que produccion ya
    tiene tres instancias del patron (`binT_1`, `binT_2`, `unT`) y de que el sondeo anade dos
    mas para `liftcT`/`liftscT` y dos mas para `consT`. -/

theorem br_patron_binT_2 (m : Nat) (A X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (binT m A X) (binT m A Y))) :=
  pcc_congr_binT_2_code m A X Y hA hX

/-- `funccT` = `binT 1`: la congruencia interna en el 2º argumento de `funccT` que el sondeo
    usaria YA la da produccion. (El sondeo, de hecho, usa `pcc_congr_binT_2_code 1` en
    `refl_caso_funcc`.) -/
theorem br_congr_funccT_arg2_ya_esta (A X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (Sonda.funccT A X) (Sonda.funccT A Y))) :=
  pcc_congr_binT_2_code 1 A X Y hA hX

/-! ## §6 · CAJON 3 — CONTROL: lo que NO esta en produccion.

    `liftcT` / `liftscT` NO son un `binT`: son nodos `funcc ⌜liftc⌝ [c,t]`. Se comprueba que el
    KIT NO los cubre — el `fail_if_success` falla si algun dia se hicieran defeq. -/

example (c t : Term) : True := by
  fail_if_success exact (rfl : Sonda.liftcT c t = binT 1 c t)
  fail_if_success exact (rfl : Sonda.liftcT c t = unT 1 c)
  trivial

/-- `consT` no es un `binT` de ningun tag: las congruencias `pcc_congr_consT_arg{1,2}_code` del
    sondeo no se obtienen del KIT. -/
example (A X : Term) : True := by
  fail_if_success exact (rfl : consT A X = binT 0 A X)
  fail_if_success exact (rfl : consT A X = binT 1 A X)
  trivial

/-- CONTROL NEGATIVO del sondeo, replicado: `targetLift` no es una reflexividad disfrazada. -/
example (s : Term) : True := by
  fail_if_success
    exact (rfl : Sonda.liftcT (termCode zero) (tcFn s) = tcFn (liftc zero s))
  trivial

/-! ## §7 · CAJON 3 CONFIRMADO — pero el sondeo SUBSUME dos lemas de produccion.

    `prf_substfc_atom2CodeFn` / `prf_substfc_ltCodeFn'` no estan en produccion (produccion solo
    tiene los dos casos con HUECO `varc ⌜v₀⌝` a nivel `zero`). Aqui se DERIVAN los dos de
    produccion desde el generico del sondeo: son consecuencias suyas, no duplicados, pero si
    entran los dos hay que decidir cual usa el consumidor. -/

/-- `Meta/D3InDotPrf.lean:195` (`prf_substfc_ltCodeFn_snd`) sale del generico del sondeo. -/
theorem br_ltCodeFn_snd_desde_sondeo (A K : Term)
    (hAinv : ∀ W, Prf (substtc zero W A =eq A)) :
    Prf (substfc zero K (ltCodeFn A (varc (numeral 0))) =eq ltCodeFn A K) :=
  prf_eq_trans (Sonda.prf_substfc_ltCodeFn' zero K A (varc (numeral 0)))
    (prf_congr_atom2CodeFn (hAinv K) (prf_substtc_varc0 K))

/-- `Meta/EvalBoundedPrf.lean:170` (`prf_substfc_ltCodeFn_varc0`) idem. -/
theorem br_ltCodeFn_varc0_desde_sondeo (B K : Term)
    (hBinv : ∀ W, Prf (substtc zero W B =eq B)) :
    Prf (substfc zero K (ltCodeFn (varc (numeral 0)) B) =eq ltCodeFn K B) :=
  prf_eq_trans (Sonda.prf_substfc_ltCodeFn' zero K (varc (numeral 0)) B)
    (prf_congr_atom2CodeFn (prf_substtc_varc0 K) (hBinv K))

/-! ## §8 · CAJON 3 — los envoltorios de `liftcT` son 1 LINEA sobre genericos de produccion.

    `prf_congr_funcc2` (`NumCodeClosedPrf`), `prf_substtc_funcc2` (`EvalArithPrf`) y
    `prf_congr_consT`/`prf_substtc_consT`/`substtc_inv_consT` (`DotConsPrf`) ya estan. Lo que
    el sondeo anade es el PLEGADO al nodo `funcc ⌜liftc⌝ [c,t]`, que no existe en produccion. -/

theorem br_liftcT_es_funcc2 (c t : Term) :
    Sonda.liftcT c t = funcc (strCode "liftc") (cons c (cons t nil)) := rfl

/-- Y `liftcT` NO es ningun `consT` ni ningun nodo del KIT: control negativo. -/
example (c t : Term) : True := by
  fail_if_success exact (rfl : Sonda.liftcT c t = consT c t)
  trivial

/-! ## §8b · LA COLAPSABILIDAD, PROBADA: `liftcT`, `liftscT` y `consT` son EL MISMO NODO
       `funcc ⌜s⌝ [x,y]` variando solo el simbolo. Diez lemas del sondeo son CINCO. -/

/-- El nodo generico: `liftcT = fn2 "liftc"`, `liftscT = fn2 "liftsc"`, `consT = fn2 cons_sym`. -/
def fn2 (s : String) (x y : Term) : Term := funcc (strCode s) (cons x (cons y nil))

theorem br_liftcT_fn2 (c t : Term) : Sonda.liftcT c t = fn2 "liftc" c t := rfl
theorem br_liftscT_fn2 (c t : Term) : Sonda.liftscT c t = fn2 "liftsc" c t := rfl
theorem br_consT_fn2 (x y : Term) : consT x y = fn2 cons_sym x y := rfl

theorem prf_congr_fn2 {s : String} {c c' t t' : Term}
    (hc : Prf (c =eq c')) (ht : Prf (t =eq t')) : Prf (fn2 s c t =eq fn2 s c' t') :=
  prf_congr_funcc2 (prf_eq_trans (prf_congr_cons_head hc)
    (prf_congr_cons_tail (prf_congr_cons_head ht)))

theorem prf_substtc_fn2 (s : String) (v W x y : Term) :
    Prf (substtc v W (fn2 s x y) =eq fn2 s (substtc v W x) (substtc v W y)) :=
  prf_substtc_funcc2 v W (strCode s) x y

theorem substtc_inv_fn2 {s : String} {X Y : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y)) :
    ∀ W, Prf (substtc zero W (fn2 s X Y) =eq fn2 s X Y) := fun W =>
  prf_eq_trans (prf_substtc_fn2 s zero W X Y) (prf_congr_fn2 (hX W) (hY W))

/-- **Congruencia interna generica en el 2º argumento** del nodo `funcc ⌜s⌝ [·,·]`.
    Misma prueba que `pcc_congr_binT_2_code`, con `s` abstracto. -/
theorem pcc_congr_fn2_arg2_code (s : String) (A X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (fn2 s A X) (fn2 s A Y))) := by
  let Ac : Term := eqc (fn2 s A X) (fn2 s A (varc (numeral 0)))
  have hcomp : ∀ w : Term, Prf (substfc zero w Ac =eq eqc (fn2 s A X) (fn2 s A w)) := by
    intro w
    refine prf_eq_trans (prf_substfc_eq zero w (fn2 s A X) (fn2 s A (varc (numeral 0)))) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_fn2 s zero w A X) (prf_congr_fn2 (hA w) (hX w))
    · exact prf_eq_trans (prf_substtc_fn2 s zero w A (varc (numeral 0)))
        (prf_congr_fn2 (hA w) (prf_substtc_varc0 w))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (fn2 s A X))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _))

/-- **Congruencia interna generica en el 1er argumento.** -/
theorem pcc_congr_fn2_arg1_code (s : String) (B X Y : Term)
    (hB : ∀ W, Prf (substtc zero W B =eq B)) (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (fn2 s X B) (fn2 s Y B))) := by
  let Ac : Term := eqc (fn2 s X B) (fn2 s (varc (numeral 0)) B)
  have hcomp : ∀ w : Term, Prf (substfc zero w Ac =eq eqc (fn2 s X B) (fn2 s w B)) := by
    intro w
    refine prf_eq_trans (prf_substfc_eq zero w (fn2 s X B) (fn2 s (varc (numeral 0)) B)) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_fn2 s zero w X B) (prf_congr_fn2 (hX w) (hB w))
    · exact prf_eq_trans (prf_substtc_fn2 s zero w (varc (numeral 0)) B)
        (prf_congr_fn2 (prf_substtc_varc0 w) (hB w))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (fn2 s X B))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _))

/-! ### Las CUATRO congruencias internas del sondeo, obtenidas de las DOS genericas. -/

theorem br_pcc_congr_liftcT_arg2_code (A X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y)
      ⇒ provFromCode (eqc (Sonda.liftcT A X) (Sonda.liftcT A Y))) :=
  pcc_congr_fn2_arg2_code "liftc" A X Y hA hX

theorem br_pcc_congr_liftscT_arg2_code (A X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y)
      ⇒ provFromCode (eqc (Sonda.liftscT A X) (Sonda.liftscT A Y))) :=
  pcc_congr_fn2_arg2_code "liftsc" A X Y hA hX

theorem br_pcc_congr_consT_arg2_code (A X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (consT A X) (consT A Y))) :=
  pcc_congr_fn2_arg2_code cons_sym A X Y hA hX

theorem br_pcc_congr_consT_arg1_code (B X Y : Term)
    (hB : ∀ W, Prf (substtc zero W B =eq B)) (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (consT X B) (consT Y B))) :=
  pcc_congr_fn2_arg1_code cons_sym B X Y hB hX

/-! ### Y las SEIS de fontaneria (`congr`/`substtc`/`inv` × `liftcT`/`liftscT`) son TRES. -/

theorem br_prf_congr_liftcT {c c' t t' : Term} (hc : Prf (c =eq c')) (ht : Prf (t =eq t')) :
    Prf (Sonda.liftcT c t =eq Sonda.liftcT c' t') := prf_congr_fn2 hc ht
theorem br_prf_congr_liftscT {c c' t t' : Term} (hc : Prf (c =eq c')) (ht : Prf (t =eq t')) :
    Prf (Sonda.liftscT c t =eq Sonda.liftscT c' t') := prf_congr_fn2 hc ht
theorem br_prf_substtc_liftcT (v W x y : Term) :
    Prf (substtc v W (Sonda.liftcT x y)
      =eq Sonda.liftcT (substtc v W x) (substtc v W y)) := prf_substtc_fn2 "liftc" v W x y
theorem br_prf_substtc_liftscT (v W x y : Term) :
    Prf (substtc v W (Sonda.liftscT x y)
      =eq Sonda.liftscT (substtc v W x) (substtc v W y)) := prf_substtc_fn2 "liftsc" v W x y
theorem br_substtc_inv_liftcT {X Y : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y)) :
    ∀ W, Prf (substtc zero W (Sonda.liftcT X Y) =eq Sonda.liftcT X Y) := substtc_inv_fn2 hX hY
theorem br_substtc_inv_liftscT {X Y : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y)) :
    ∀ W, Prf (substtc zero W (Sonda.liftscT X Y) =eq Sonda.liftscT X Y) := substtc_inv_fn2 hX hY

/-! ## §9 · CONTROL sobre `substTerm_termCode`: produccion tiene el de `termCodeM`, NO el de
       `termCode`. Si fueran defeq, el de produccion valdria; se comprueba que NO lo son. -/

example : True := by
  fail_if_success exact (rfl : @termCode = @termCodeM)
  trivial

example : True := by
  fail_if_success exact (rfl : @numeral = @numeralM)
  trivial

/-! ## §10 · CENSO DE DEPENDENCIAS del sondeo contra PRODUCCION.

    Cada `have _ :=` nombra una constante de produccion que `ReflectorDesdeConsumidor.lean`
    consume. Si este teorema compila con una lista de `import` dada, esa lista BASTA para el
    modulo de `Meta/`. -/

theorem br_censo_dependencias : True := by
  -- fontaneria de igualdad y de codigo
  have _ := @prf_eq_trans; have _ := @prf_eq_symm; have _ := @prf_refl; have _ := @prf_mp
  have _ := @prf_congr_cons_head; have _ := @prf_congr_cons_tail
  have _ := @prf_congr_funcc2; have _ := @prf_substtc_funcc1; have _ := @prf_substtc_funcc2
  have _ := @prf_congr_consT; have _ := @prf_substtc_consT; have _ := @substtc_inv_consT
  have _ := @prf_congr_eqCodeFn; have _ := @prf_congr_implc; have _ := @prf_congr_succcT
  have _ := @prf_congr_atom2CodeFn; have _ := @atom2CodeFn; have _ := @ltCodeFn
  have _ := @eqCodeFn; have _ := @eqCodeFn_eq_eqc; have _ := @succcT; have _ := @consT
  -- KIT
  have _ := @unT; have _ := @binT; have _ := @unT_termCode; have _ := @binT_termCode
  have _ := @prf_congr_unT; have _ := @prf_congr_binT
  have _ := @prf_substtc_unT; have _ := @prf_substtc_binT
  have _ := @substtc_inv_unT; have _ := @substtc_inv_binT
  have _ := @pcc_dot_un; have _ := @pcc_dot_bin
  have _ := @pcc_dot_un_symm; have _ := @pcc_dot_bin_symm
  have _ := @pcc_congr_binT_2_code
  -- substfc / substtc abiertos
  have _ := @prf_substfc_arith_open; have _ := @prf_substtc_arith_open
  have _ := @substCodeT_closed; have _ := @liftTerm_numeralM
  have _ := @prf_substfc_eq; have _ := @prf_substfc_impl; have _ := @prf_substfc_atom
  have _ := @prf_substtsc_cons; have _ := @prf_substtsc_nil
  have _ := @prf_substtc_var_eq; have _ := @prf_substtc_var_lt; have _ := @prf_substtc_varc0
  have _ := @prf_congr_substfc_arg3
  -- tcFn
  have _ := @prf_congr_tcFn; have _ := @prf_liftc_tcFn; have _ := @prf_substtc_tcFn
  have _ := @prf_substtc_tcFn_at; have _ := @substtc_inv_tcFn
  have _ := @prf_tc_zero; have _ := @prf_tc_succ'
  -- axiomas objeto de liftc/liftsc y su instanciacion dotada
  have _ := @ax_liftc_func; have _ := @ax_liftc_var_ge
  have _ := @ax_liftsc_nil; have _ := @ax_liftsc_cons
  have _ := @axioms; have _ := @forall_2; have _ := @forall_3
  have _ := @pcc_axiom_inst; have _ := @pcc_axiom_inst2; have _ := @pcc_axiom_inst3
  have _ := @pcc_mp_code_apply; have _ := @prf_provCode_congr
  have _ := @prf_provFromCode_eqCodeFn_refl
  have _ := @prf_liftc_var_ge; have _ := @prf_liftc_func
  have _ := @prf_liftsc_nil; have _ := @prf_liftsc_cons
  have _ := @prf_congr_liftc; have _ := @prf_zero_lt_succ
  -- reflexion del atomo `<` y cadenas dotadas
  have _ := @pcc_lt_tracked; have _ := @pcc_eq_trans_code
  have _ := @pcc_dot_cons; have _ := @pcc_dot_cons_symm
  -- deduccion / Hilbert con hipotesis
  have _ := @prf_deduction; have _ := @deduction_aux; have _ := @prf_to_prfH
  have _ := @prfH_hyp_self; have _ := @PrfH_leibniz_apply; have _ := @PrfH_leibniz_subst
  have _ := @PrfH_eq_symm; have _ := @PrfH_and_intro
  have _ := @PrfH_and_elim_left; have _ := @PrfH_and_elim_right
  -- codigos meta y sustitucion meta
  have _ := @termCode; have _ := @termsCode; have _ := @formCode
  have _ := @substFormula_provFromCode_open
  have _ := @substTerm_numeral; have _ := @substTerm_strCode
  -- vocabulario del predicado sin-wTs
  have _ := @nthc; have _ := @lenc
  have _ := @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.shapeUn
  have _ := @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.shapeBin
  have _ := @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.argsIn
  have _ := @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.isTermCodeE1
  have _ := @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.impT
  have _ := @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_or_elim_imp
  have _ := @ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf.PrfH_eq_trans_code
  have _ := @ROBINSON_PlusPlus.Meta.EvalRunFnPrf.prf_substtc_termCode_nil
  have _ := @ROBINSON_PlusPlus.Meta.LineWFSchemaPrf.substtc_inv_termCode_numeralM
  trivial

end B1Dedup

/-! ## §11 · FOOTPRINT: todos los puentes deben salir NET-0. -/

#print axioms B1Dedup.br_shapeUn
#print axioms B1Dedup.br_shapeBin
#print axioms B1Dedup.br_argsInBody
#print axioms B1Dedup.br_argsIn
#print axioms B1Dedup.br_isTermCodeE1
#print axioms B1Dedup.br_impT
#print axioms B1Dedup.br_prf_or_elim_imp
#print axioms B1Dedup.br_PrfH_eq_trans_code
#print axioms B1Dedup.br_eqc_eq_eqCodeFn
#print axioms B1Dedup.br_iz_inv
#print axioms B1Dedup.br_iz_inv'
#print axioms B1Dedup.br_varcT
#print axioms B1Dedup.br_funccT
#print axioms B1Dedup.br_varcT_termCode
#print axioms B1Dedup.br_funccT_termCode
#print axioms B1Dedup.br_prf_congr_varcT
#print axioms B1Dedup.br_prf_congr_funccT
#print axioms B1Dedup.br_prf_substtc_varcT_at
#print axioms B1Dedup.br_prf_substtc_funccT_at
#print axioms B1Dedup.br_unT_at_implies_prod
#print axioms B1Dedup.br_unT_prod
#print axioms B1Dedup.br_binT_at_implies_prod
#print axioms B1Dedup.br_binT_prod
#print axioms B1Dedup.br_tcNumeralM_at_implies_prod
#print axioms B1Dedup.br_tcNumeralM_prod
#print axioms B1Dedup.br_tcZero_at_implies_prod
#print axioms B1Dedup.br_tcClosed_desde_produccion
#print axioms B1Dedup.br_patron_binT_2
#print axioms B1Dedup.br_congr_funccT_arg2_ya_esta
#print axioms B1Dedup.br_ltCodeFn_snd_desde_sondeo
#print axioms B1Dedup.br_ltCodeFn_varc0_desde_sondeo
#print axioms B1Dedup.br_liftcT_es_funcc2
#print axioms B1Dedup.br_liftcT_fn2
#print axioms B1Dedup.br_liftscT_fn2
#print axioms B1Dedup.br_consT_fn2
#print axioms B1Dedup.br_pcc_congr_liftcT_arg2_code
#print axioms B1Dedup.br_pcc_congr_liftscT_arg2_code
#print axioms B1Dedup.br_pcc_congr_consT_arg2_code
#print axioms B1Dedup.br_pcc_congr_consT_arg1_code
#print axioms B1Dedup.br_prf_congr_liftcT
#print axioms B1Dedup.br_prf_congr_liftscT
#print axioms B1Dedup.br_prf_substtc_liftcT
#print axioms B1Dedup.br_prf_substtc_liftscT
#print axioms B1Dedup.br_substtc_inv_liftcT
#print axioms B1Dedup.br_substtc_inv_liftscT

-- CONTROL: la base sancionada que YA carga produccion, para comparar.
#print axioms ROBINSON_PlusPlus.Meta.DotConsPrf.pcc_dot_cons
#print axioms ROBINSON_PlusPlus.Meta.CodeCtorKit.pcc_congr_binT_2_code
#print axioms ROBINSON_PlusPlus.Meta.Sigma1AtomPrf.eqCodeFn_eq_eqc
