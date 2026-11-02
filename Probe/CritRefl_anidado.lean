/-
# VIA 2 — EL `∀` ANIDADO, DE FRENTE.  ¿es de verdad caro?

Se deja `argsIn` como esta (`bdAllCode` DENTRO de `bdAllCode`) y se intenta el reflector igual.

    lake env lean Probe/Refl_anidado.lean

Fichero AUTOCONTENIDO (`import ROBINSON_PlusPlus.Meta` y nada mas); lo que hace falta va COPIADO
de `sondeos/A3IsFCBTracked.lean` y `sondeos/ClausuraLiftSinWTs.lean`.

## LA PREGUNTA

`pcc_bdAll_intro` (Meta/BdAllIntroPrf.lean:316) tiene 8 obligaciones; las que tocan la estructura
del cuerpo son `hPl`, `hPs`, `hPsiId` y `hbody`.  Con un `bdAllCode` DENTRO del cuerpo, el descenso
de `substfc` cruza un `forallc`, y `ax_substfc_forall` SUBE el nivel y LIFTEA el sustituyendo:

    substfc v t (forallc a)  =  forallc (substfc (σv) (liftc 0 t) a)

## LA CLAVE (y por que NO rompe `hPsiId`)

Se escribe la imagen punteada con las DOS vistas explicitas: `X` (nivel 0) y `Xi` (nivel 1, la
misma con el hueco desplazado).  El hueco es `varc ⌜0⌝` fuera y `varc ⌜1⌝` dentro, y entonces

    liftc 0 (varc ⌜0⌝)              =eq varc ⌜1⌝            (prf_liftc_var_ge)
    substtc ⌜1⌝ (varc ⌜1⌝) (varc ⌜1⌝) =eq varc ⌜1⌝            (prf_substtc_var_eq)

o sea: el `liftc` del sustituyendo lleva el hueco EXACTAMENTE a la forma en que el hueco aparece
dentro del binder.  `hPsiId` sale, igual que en A3.

## VEREDICTO:  **NO HAY MURO**.  0 errores, 0 warnings, 0 `sorry`, 0 axiomas nuevos.

Las 8 obligaciones se descargan TODAS y sale el reflector entero:

    pcc_wfAll1_tracked (w) : Prf (wfAll1 w ⇒ provFromCode (wfAllB1Dot w))     -- w ABSTRACTO
    pcc_isTC1_tracked (w c) : Prf (isTC1 w c ⇒ provFromCode (isTC1Dot w c))
    pcc_isTC1_wz : Prf (provFromCode (isTC1Dot [⌜0⌝] ⌜0⌝))                    -- NO vacio,
                                                                              -- por la rama funcc

Footprint IDENTICO al de A3 (`prf_axiomsCodeT_eq`, la base sancionada).

### Lo que el `∀` anidado cuesta DE VERDAD (todo ruido, ningun muro)

1. **Escribir las DOS vistas** (`X` nivel 0 / `Xi` nivel 1) en la imagen punteada, en vez de
   escribir `liftc 0 X` y esperar que se compute: con `X` construido a base de `funcc`, `liftc`
   se computa, pero eso son lemas; poner la vista interna a mano lo evita ENTERO.
   ⚠️ Si `X` fuera ABSTRACTO (no un codigo construido) esto NO valdria: haria falta
   `substtc (σv) (liftc 0 s) (liftc 0 X) =eq liftc 0 (substtc v s X)`, que es induccion sobre
   codigos — el muro de siempre.  Aqui NO hace falta porque el nodo es `nthcT ẇ ⌜v⌝`.
2. **Una segunda aplicacion de `pcc_bdAll_intro`** para el `∀` interno.  `argsIn` tiene DOS
   parametros y `pcc_bdAll_intro` uno: se emparejan en `p = cons Y q` y se recuperan con
   `carc`/`cdrc` (que conmutan con `lift`/`subst` SINTACTICAMENTE).  ~30 lineas de ruido.
3. **La «desviacion 2» de A3 se vuelve OBLIGATORIA**: `pcc_bdAll_intro` entrega la cota en forma
   PURA (`tcFn (lenc Y)`) y la imagen anidada la necesita COMPUTADA (`lencT Ŷ`), porque dentro
   del `∀` externo la lista de argumentos depende del indice.  Se paga con UNA Leibniz interna
   cuyo hueco vive DENTRO del binder (`varc ⌜1⌝`) — `pcc_argsIn_tracked`.
   Todos los terminos que entran y salen de esa Leibniz son `liftc`-invariantes, y por eso
   funciona (`liftc_inv_lencT` / `liftc_inv_nthcT`).
4. **Las Leibniz siguen siendo UNA por nivel**: `substfc` cubre TODAS las ocurrencias del hueco,
   tambien las que estan bajo el binder interior (donde aparece como `⌜v₁⌝`).
-/
import ROBINSON_PlusPlus.Meta

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.BoundedInPrf ROBINSON_PlusPlus.Meta.BdAllIntroPrf
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.TrackedCorePrf
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf ROBINSON_PlusPlus.Meta.Sigma1CorePrf
open ROBINSON_PlusPlus.Meta.EvalListPrf ROBINSON_PlusPlus.Meta.EvalNthcPrf
open ROBINSON_PlusPlus.Meta.EvalLtPrf ROBINSON_PlusPlus.Meta.EvalBoundedPrf
open ROBINSON_PlusPlus.Meta.EvalArithPrf ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
open ROBINSON_PlusPlus.Meta.InAxiomsCodePrf ROBINSON_PlusPlus.Meta.Delta0ReflectPrf
open ROBINSON_PlusPlus.Meta.DerivCondPrf ROBINSON_PlusPlus.Meta.D3InDotPrf
open ROBINSON_PlusPlus.Meta.ChainPrf ROBINSON_PlusPlus.Meta.MpCodePrf

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace ReflAnidado

/-! ## 0 · Combinadores (copia de `sondeos/A3IsFCBTracked.lean` §0) -/

theorem impT {A B C : Formula} (h1 : Prf (A ⇒ B)) (h2 : Prf (B ⇒ C)) : Prf (A ⇒ C) := by
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH h2 _) (PrfH.mp _ _ _ (prf_to_prfH h1 _) (prfH_hyp_self _))

theorem prf_or_elim_imp {A B C : Formula} (h1 : Prf (A ⇒ C)) (h2 : Prf (B ⇒ C)) :
    Prf (lor A B ⇒ C) := by
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _
    (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prfᵢ.j3 A B C)) (prfH_hyp_self _))
    (prf_to_prfH h1 _)) (prf_to_prfH h2 _)

theorem prf_orL_imp (Ac Bc : Term) : Prf (provFromCode Ac ⇒ provFromCode (orc Ac Bc)) :=
  prf_mp (pcc_mp_code_open Ac (orc Ac Bc)) (pcc_j1_code Ac Bc)

theorem prf_orR_imp (Ac Bc : Term) : Prf (provFromCode Bc ⇒ provFromCode (orc Ac Bc)) :=
  prf_mp (pcc_mp_code_open Bc (orc Ac Bc)) (pcc_j2_code Ac Bc)

theorem prf_cdrc_cons (h t : Term) : Prf (cdrc (cons h t) =eq t) := by
  have hax : Prf ax_cdrc := prf_ax (by simp [axioms])
  have hh := prf_spec (prf_spec hax h) t
  simp [substFormula, substTerm, substTerms, cdrc, cons, FOL.substTerm_liftTerm] at hh
  exact hh

theorem prf_congr_forallc {a a' : Term} (h : Prf (a =eq a')) :
    Prf (forallc a =eq forallc a') := by
  unfold forallc; exact prf_congr_un h

/-! ## 1 · EL OBJETO — copia de `sondeos/ClausuraLiftSinWTs.lean` §1 (via SIN `wTs`).

    ⚠️ `argsIn` es un `∀` ACOTADO **dentro** del cuerpo de otro `∀` acotado. Eso es lo que se
    mide aqui. -/

def argsInBody (wT Y : Term) : Formula :=
  Formula.impl (lt (.var 0) (liftTerm 0 (lenc Y)))
    (In (nthc (liftTerm 0 Y) (.var 0)) (liftTerm 0 wT))

def argsIn (wT Y : Term) : Formula := Formula.forall (argsInBody wT Y)

def consOk (X : Term) : Formula := Formula.eq X (cons (carc X) (cdrc X))
def cOk (X : Term) (F : Formula) : Formula := land (consOk X) F

def varOkT (X : Term) : Formula :=
  land (Formula.eq (carc X) (numeralM 0)) (Formula.eq (lenc X) (numeralM 2))

def funcOkT1 (wT X : Term) : Formula :=
  land (land (Formula.eq (carc X) (numeralM 1)) (Formula.eq (lenc X) (numeralM 3)))
       (argsIn wT (nthc X (numeralM 2)))

/-- `X` es codigo de TERMINO, **un solo testigo** (forma `carc`/`lenc`, la que reflejamos). -/
def isTermCodeB1 (wT X : Term) : Formula :=
  lor (cOk X (varOkT X)) (cOk X (funcOkT1 wT X))

def wfAllB1Body (w : Term) : Formula :=
  Formula.impl (lt (.var 0) (liftTerm 0 (lenc w)))
    (isTermCodeB1 (liftTerm 0 w) (nthc (liftTerm 0 w) (.var 0)))

def wfAllB1 (w : Term) : Formula := Formula.forall (wfAllB1Body w)

/-! ## 2 · LA IMAGEN PUNTEADA — con el `bdAllCode` ANIDADO

    Las dos VISTAS: `X` es el nodo visto desde NIVEL 0 (hueco `varc ⌜0⌝`) y `Xi` el mismo nodo
    visto desde DENTRO del binder interno (hueco `varc ⌜1⌝`). Escribirlas las dos hace el codigo
    De Bruijn CORRECTO por construccion, y el descenso, mecanico. -/

noncomputable def shapeDot (X : Term) (k n : Nat) : Term :=
  andc (eqCodeFn (carcT X) (tcFn (numeralM k))) (eqCodeFn (lencT X) (tcFn (numeralM n)))

/-- **La imagen de `argsIn`** — un `bdAllCode` con la cota COMPUTADA. `Yi`/`Wi` son las vistas
    de la lista de argumentos y del testigo DESDE DENTRO del binder. -/
noncomputable def argsDotI (Yi Wi : Term) : Term :=
  bdAllCode (lencT Yi) (inFormCodeFn (nthcT Yi (varc (numeral 0))) Wi)

/-- Variante con la cota en forma PURA (la que entrega `pcc_bdAll_intro`). -/
noncomputable def argsDotB (B Yi Wi : Term) : Term :=
  bdAllCode B (inFormCodeFn (nthcT Yi (varc (numeral 0))) Wi)

noncomputable def funcDot (Wi X Xi : Term) : Term :=
  andc (shapeDot X 1 3) (argsDotI (nthcT Xi (tcFn (numeralM 2))) Wi)

noncomputable def isTCDot (Wi X Xi : Term) : Term := orc (shapeDot X 0 2) (funcDot Wi X Xi)

/-- **`PsiF`**: el cuerpo dotado del `∀` acotado EXTERNO. El hueco es `varc ⌜0⌝` fuera y
    `varc ⌜1⌝` dentro del `∀` interno. -/
noncomputable def PsiF (w : Term) : Term :=
  isTCDot (tcFn w) (nthcT (tcFn w) (varc (numeral 0))) (nthcT (tcFn w) (varc (numeral 1)))

noncomputable def wfAllB1Dot (w : Term) : Term := bdAllCode (tcFn (lenc w)) (PsiF w)

/-! ## 3 · PIEZAS DE NIVEL 1 (las que A3 sólo necesitaba de pasada) -/

theorem prf_substtc_varc0_at1 (V : Term) :
    Prf (substtc (succ zero) V (varc (numeral 0)) =eq varc (numeral 0)) :=
  prf_mp (prf_substtc_var_lt (succ zero) V (numeral 0)) (prf_gnum_lt (by omega : 0 < 1))

theorem prf_substtc_varc1_at1 (V : Term) :
    Prf (substtc (succ zero) V (varc (numeral 1)) =eq V) :=
  prf_mp (prf_substtc_var_eq (succ zero) V (numeral 1)) (prf_refl _)

/-- 🔑 **El hueco, liftado, ES el hueco de dentro**: `liftc 0 ⌜v₀⌝ =eq ⌜v₁⌝`. -/
theorem prf_liftc_varc0 : Prf (liftc zero (varc (numeral 0)) =eq varc (numeral 1)) :=
  prf_mp (prf_liftc_var_ge zero (numeral 0)) (prf_zero_lt_succ (numeral 0))

theorem substtc_inv_tcFn_at1 (w : Term) : ∀ V, Prf (substtc (succ zero) V (tcFn w) =eq tcFn w) :=
  fun V => prf_substtc_tcFn_at 1 V w

/-- `substfc` sobre el codigo de un atomo BINARIO, a nivel `v` ARBITRARIO. -/
theorem prf_substfc_atom2c (v t pc a b a' b' : Term)
    (ha : Prf (substtc v t a =eq a')) (hb : Prf (substtc v t b =eq b')) :
    Prf (substfc v t (atomc pc (cons a (cons b nil))) =eq atomc pc (cons a' (cons b' nil))) := by
  refine prf_eq_trans (prf_substfc_atom v t pc (cons a (cons b nil))) ?_
  show Prf (atomc pc (substtsc v t (cons a (cons b nil))) =eq atomc pc (cons a' (cons b' nil)))
  unfold atomc
  refine prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head ?_))
  refine prf_eq_trans (prf_substtsc_cons v t a (cons b nil)) ?_
  refine prf_eq_trans (prf_congr_cons_head ha) (prf_congr_cons_tail ?_)
  exact prf_eq_trans (prf_substtsc_cons v t b nil)
    (prf_eq_trans (prf_congr_cons_head hb) (prf_congr_cons_tail (prf_substtsc_nil v t)))

theorem prf_substfc_ltCode2 (v t A B A' B' : Term)
    (hA : Prf (substtc v t A =eq A')) (hB : Prf (substtc v t B =eq B')) :
    Prf (substfc v t (ltCodeFn A B) =eq ltCodeFn A' B') :=
  prf_substfc_atom2c v t (strCode lt_sym) A B A' B' hA hB

theorem prf_substfc_inCode2 (v t A B A' B' : Term)
    (hA : Prf (substtc v t A =eq A')) (hB : Prf (substtc v t B =eq B')) :
    Prf (substfc v t (inFormCodeFn A B) =eq inFormCodeFn A' B') :=
  prf_substfc_atom2c v t (strCode in_sym) A B A' B' hA hB

/-! ## 4 · **EL DESCENSO POR EL `∀` ANIDADO** — la medida central

    `substfc 0 s` atraviesa el `forallc` interior: sube a nivel `σ0` y liftea el sustituyendo.
    La hipotesis `ht1` normaliza ese `liftc 0 s`; las dos hipotesis restantes son el descenso
    A NIVEL 1 de las dos vistas internas. -/

theorem prf_substfc_argsDotB (s t1 B B' Yi Yi' Wi Wi' : Term)
    (ht1 : Prf (liftc zero s =eq t1))
    (hB : Prf (substtc (succ zero) t1 B =eq B'))
    (hY : Prf (substtc (succ zero) t1 Yi =eq Yi'))
    (hW : Prf (substtc (succ zero) t1 Wi =eq Wi')) :
    Prf (substfc zero s (argsDotB B Yi Wi) =eq argsDotB B' Yi' Wi') := by
  unfold argsDotB bdAllCode
  refine prf_eq_trans (prf_substfc_forall zero s _) (prf_congr_forallc ?_)
  refine prf_eq_trans (prf_congr_substfc_arg2 ht1) ?_
  refine prf_eq_trans (prf_substfc_impl (succ zero) t1 _ _) (prf_congr_implc ?_ ?_)
  · exact prf_substfc_ltCode2 (succ zero) t1 _ _ _ _ (prf_substtc_varc0_at1 t1) hB
  · refine prf_substfc_inCode2 (succ zero) t1 _ _ _ _ ?_ hW
    exact prf_eq_trans (prf_substtc_nthcT (succ zero) t1 Yi (varc (numeral 0)))
      (prf_congr_nthcT hY (prf_substtc_varc0_at1 t1))

theorem prf_substfc_argsDotI (s t1 Yi Yi' Wi Wi' : Term)
    (ht1 : Prf (liftc zero s =eq t1))
    (hY : Prf (substtc (succ zero) t1 Yi =eq Yi'))
    (hW : Prf (substtc (succ zero) t1 Wi =eq Wi')) :
    Prf (substfc zero s (argsDotI Yi Wi) =eq argsDotI Yi' Wi') :=
  prf_substfc_argsDotB s t1 (lencT Yi) (lencT Yi') Yi Yi' Wi Wi' ht1
    (prf_eq_trans (prf_substtc_lencT (succ zero) t1 Yi) (prf_congr_lencT hY)) hY hW

theorem prf_substfc_shapeDot (s X X' : Term) (k n : Nat)
    (hX : Prf (substtc zero s X =eq X')) :
    Prf (substfc zero s (shapeDot X k n) =eq shapeDot X' k n) := by
  unfold shapeDot
  refine prf_eq_trans (prf_substfc_and zero s _ _) (prf_congr_andc ?_ ?_)
  · refine prf_eq_trans (prf_substfc_eq zero s _ _) (prf_congr_eqCodeFn ?_ ?_)
    · exact prf_eq_trans (prf_substtc_carcT zero s X) (prf_congr_carcT hX)
    · exact substtc_inv_tcFn (numeralM k) s
  · refine prf_eq_trans (prf_substfc_eq zero s _ _) (prf_congr_eqCodeFn ?_ ?_)
    · exact prf_eq_trans (prf_substtc_lencT zero s X) (prf_congr_lencT hX)
    · exact substtc_inv_tcFn (numeralM n) s

/-- **EL DESCENSO ENTERO** por el nodo dotado, `∀` anidado incluido. -/
theorem prf_substfc_isTCDot (s t1 Wi Wi' X X' Xi Xi' : Term)
    (ht1 : Prf (liftc zero s =eq t1))
    (hW : Prf (substtc (succ zero) t1 Wi =eq Wi'))
    (hX : Prf (substtc zero s X =eq X'))
    (hXi : Prf (substtc (succ zero) t1 Xi =eq Xi')) :
    Prf (substfc zero s (isTCDot Wi X Xi) =eq isTCDot Wi' X' Xi') := by
  unfold isTCDot funcDot
  refine prf_eq_trans (prf_substfc_or zero s _ _)
    (prf_congr_orc (prf_substfc_shapeDot s X X' 0 2 hX) ?_)
  refine prf_eq_trans (prf_substfc_and zero s _ _)
    (prf_congr_andc (prf_substfc_shapeDot s X X' 1 3 hX) ?_)
  refine prf_substfc_argsDotI s t1 _ _ Wi Wi' ht1 ?_ hW
  exact prf_eq_trans (prf_substtc_nthcT (succ zero) t1 Xi (tcFn (numeralM 2)))
    (prf_congr_nthcT hXi (prf_substtc_tcFn_at 1 t1 (numeralM 2)))

/-! ## 5 · LAS 8 OBLIGACIONES DE `pcc_bdAll_intro` -/

theorem hbl_ok : ∀ (k : Nat) (q : Term), liftTerm k (lenc q) = lenc (liftTerm k q) := by
  intro k q; simp only [lenc, liftTerm, liftTerms]

theorem hbs_ok : ∀ (v : Nat) (t q : Term), substTerm v t (lenc q) = lenc (substTerm v t q) := by
  intro v t q; simp only [lenc, substTerm, substTerms]

theorem hPl_ok : ∀ (k : Nat) (q : Term), liftTerm k (PsiF q) = PsiF (liftTerm k q) := by
  intro k q
  simp only [PsiF, isTCDot, funcDot, shapeDot, argsDotI, bdAllCode, forallc, implc,
    ltCodeFn, atom2CodeFn, inFormCodeFn, eqCodeFn, andc, orc, carcT, lencT, nthcT, funcc, varc,
    tcFn, cons, nil, zero, succ, numeralM, liftTerm, liftTerms, liftTerm_numeral,
    liftTerm_strCode]

theorem hPs_ok : ∀ (v : Nat) (t q : Term), substTerm v t (PsiF q) = PsiF (substTerm v t q) := by
  intro v t q
  simp only [PsiF, isTCDot, funcDot, shapeDot, argsDotI, bdAllCode, forallc, implc,
    ltCodeFn, atom2CodeFn, inFormCodeFn, eqCodeFn, andc, orc, carcT, lencT, nthcT, funcc, varc,
    tcFn, cons, nil, zero, succ, numeralM, substTerm, substTerms, substTerm_numeral,
    substTerm_strCode]

/-- Copia literal de `sondeos/ClausuraLiftSinWTs.lean` §4. -/
theorem liftF_argsIn (k : Nat) (wT Y : Term) :
    liftFormula k (argsIn wT Y) = argsIn (liftTerm k wT) (liftTerm k Y) := by
  simp only [argsIn, argsInBody, liftFormula, lt, lenc, nthc, In, liftTerm, liftTerms,
    Nat.zero_lt_succ, reduceIte, if_true, ← FOL.liftTerm_comm_zero]

theorem substF_argsIn (v : Nat) (s wT Y : Term) :
    substFormula v s (argsIn wT Y) = argsIn (substTerm v s wT) (substTerm v s Y) := by
  have hz : (0 = v + 1) = False := eq_false (by omega)
  have hz2 : (0 > v + 1) = False := eq_false (by omega)
  simp only [argsIn, argsInBody, substFormula, substTerm, substTerms, lt, lenc, nthc, In,
    liftTerm, liftTerms, hz, hz2, if_false, Nat.zero_lt_succ, reduceIte, if_true,
    FOL.substTerm_lift_comm_zero]

theorem liftF_isTermCodeB1 (k : Nat) (wT X : Term) :
    liftFormula k (isTermCodeB1 wT X) = isTermCodeB1 (liftTerm k wT) (liftTerm k X) := by
  simp only [isTermCodeB1, cOk, consOk, varOkT, funcOkT1, land, lor, liftFormula, liftF_argsIn,
    carc, cdrc, lenc, nthc, cons, nil, zero, liftTerm, liftTerms, liftTerm_numeralM]

theorem substF_isTermCodeB1 (v : Nat) (t wT X : Term) :
    substFormula v t (isTermCodeB1 wT X) = isTermCodeB1 (substTerm v t wT) (substTerm v t X) := by
  simp only [isTermCodeB1, cOk, consOk, varOkT, funcOkT1, land, lor, substFormula, substF_argsIn,
    carc, cdrc, lenc, nthc, cons, nil, zero, substTerm, substTerms, substTerm_numeralM]

theorem hCl_ok : ∀ (k : Nat) (q : Term), liftFormula k (wfAllB1 q) = wfAllB1 (liftTerm k q) := by
  intro k q
  simp only [wfAllB1, wfAllB1Body, liftFormula, liftF_isTermCodeB1, lt, lenc, nthc,
    liftTerm, liftTerms, Nat.zero_lt_succ, reduceIte, if_true, ← FOL.liftTerm_comm_zero]

theorem hCs_ok : ∀ (v : Nat) (t q : Term),
    substFormula v t (wfAllB1 q) = wfAllB1 (substTerm v t q) := by
  intro v t q
  have h1 : ¬ ((0 : Nat) = v + 1) := by omega
  have h2 : ¬ ((0 : Nat) > v + 1) := by omega
  simp only [wfAllB1, wfAllB1Body, substFormula, substF_isTermCodeB1, lt, lenc, nthc,
    substTerm, substTerms, liftTerm, liftTerms, if_neg h1, if_neg h2,
    FOL.substTerm_lift_comm_zero]

/-- 🔑 **`hPsiId`** — sustituir el hueco por si mismo es la identidad, TAMBIEN con el `∀`
    anidado: `liftc 0 ⌜v₀⌝ = ⌜v₁⌝` es exactamente el hueco de dentro. -/
theorem hPsiId_ok : ∀ q : Term,
    Prf (substfc zero (varc (numeral 0)) (PsiF q) =eq PsiF q) := by
  intro q
  refine prf_substfc_isTCDot (varc (numeral 0)) (varc (numeral 1)) (tcFn q) (tcFn q)
    _ _ _ _ prf_liftc_varc0 (substtc_inv_tcFn_at1 q _) ?_ ?_
  · exact prf_eq_trans (prf_substtc_nthcT zero (varc (numeral 0)) (tcFn q) (varc (numeral 0)))
      (prf_congr_nthcT (substtc_inv_tcFn q _) (prf_substtc_varc0 (varc (numeral 0))))
  · exact prf_eq_trans
      (prf_substtc_nthcT (succ zero) (varc (numeral 1)) (tcFn q) (varc (numeral 1)))
      (prf_congr_nthcT (substtc_inv_tcFn_at1 q _) (prf_substtc_varc1_at1 (varc (numeral 1))))

/-- El descenso instanciado en el testigo real `s = ı̇`: las dos vistas COLAPSAN (el sustituyendo
    es cerrado, luego `liftc 0` lo deja igual). -/
theorem prf_substfc_PsiF_at (w i : Term) :
    Prf (substfc zero (tcFn i) (PsiF w)
      =eq isTCDot (tcFn w) (nthcT (tcFn w) (tcFn i)) (nthcT (tcFn w) (tcFn i))) := by
  refine prf_substfc_isTCDot (tcFn i) (tcFn i) (tcFn w) (tcFn w) _ _ _ _
    (prf_liftc_tcFn i) (substtc_inv_tcFn_at1 w _) ?_ ?_
  · exact prf_eq_trans (prf_substtc_nthcT zero (tcFn i) (tcFn w) (varc (numeral 0)))
      (prf_congr_nthcT (substtc_inv_tcFn w _) (prf_substtc_varc0 (tcFn i)))
  · exact prf_eq_trans (prf_substtc_nthcT (succ zero) (tcFn i) (tcFn w) (varc (numeral 1)))
      (prf_congr_nthcT (substtc_inv_tcFn_at1 w _) (prf_substtc_varc1_at1 (tcFn i)))

/-! ## 6 · EL ÁTOMO `In` (copia literal de `sondeos/A3IsFCBTracked.lean` §4) -/

theorem prf_substfc_inDot (s A A' W : Term)
    (hA : Prf (substtc zero s A =eq A')) (hW : ∀ V, Prf (substtc zero V W =eq W)) :
    Prf (substfc zero s (inFormCodeFn A W) =eq inFormCodeFn A' W) :=
  prf_substfc_inCode2 zero s A W A' W hA (hW s)

noncomputable def bdInB (w : Term) : Term := lencT (liftc zero (tcFn w))
noncomputable def bdInPhic (x w : Term) : Term :=
  eqCodeFn (nthcT (liftc zero (tcFn w)) (varc (numeral 0))) (liftc zero (tcFn x))
noncomputable def bdInDot (x w : Term) : Term := bdExCode (bdInB w) (bdInPhic x w)

theorem substtc_inv_bdInB (w : Term) : ∀ W, Prf (substtc zero W (bdInB w) =eq bdInB w) :=
  substtc_inv_lencT (substtc_inv_liftc_tcFn w)

theorem liftTerm_bdInDot (c : Nat) (x w : Term) :
    liftTerm c (bdInDot x w) = bdInDot (liftTerm c x) (liftTerm c w) := by
  unfold bdInDot bdInB bdInPhic bdExCode
  simp only [exc, andc, ltCodeFn, atom2CodeFn, eqCodeFn, lencT, nthcT, funcc, varc, liftc, tcFn,
    cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_numeral, liftTerm_strCode]

theorem pcc_boundedIn_tracked (x w : Term) :
    Prf (boundedIn x w ⇒ provFromCode (bdInDot x w)) := by
  refine prf_deduction ?_
  have hex : PrfH [boundedIn x w] (boundedIn x w) := prfH_hyp_self _
  refine PrfH_ex_elim hex ?_
  rw [liftFormula_provFromCode_open, liftTerm_bdInDot]
  let X : Term := liftTerm 0 x
  let W : Term := liftTerm 0 w
  let exBody : Formula := land (lt (.var 0) (liftTerm 0 (lenc w)))
    (Formula.eq (nthc (liftTerm 0 w) (.var 0)) (liftTerm 0 x))
  let Γ' : List Formula := [exBody, liftFormula 0 (boundedIn x w)]
  show PrfH Γ' (provFromCode (bdInDot X W))
  have hC : PrfH Γ' exBody := PrfH.hyp _ _ (List.Mem.head _)
  have hlt : PrfH Γ' (lt (.var 0) (lenc W)) := PrfH_and_elim_left hC
  have hbody : PrfH Γ' (Formula.eq (nthc W (.var 0)) X) := PrfH_and_elim_right hC
  have hlt1 : PrfH Γ' (provFromCode (ltCodeFn (tcFn (.var 0)) (tcFn (lenc W)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_lt_tracked (.var 0) (lenc W)) _) hlt
  have hBeq : Prf (provFromCode (eqc (bdInB W) (tcFn (lenc W)))) :=
    prf_mp (prf_provCode_congr
      (prf_congr_eqCodeFn (prf_congr_lencT (prf_eq_symm (prf_liftc_tcFn W))) (prf_refl _)))
      (pcc_eval_lenc W)
  have hBsym : PrfH Γ' (provFromCode (eqc (tcFn (lenc W)) (bdInB W))) :=
    PrfH_eq_symm_code _ _ (substtc_inv_bdInB W) (prf_to_prfH hBeq _)
  have hcompLt : ∀ t : Term, Prf (substfc zero t (ltCodeFn (tcFn (.var 0)) (varc (numeral 0)))
      =eq ltCodeFn (tcFn (.var 0)) t) := fun t =>
    prf_substfc_ltCodeFn_snd (tcFn (.var 0)) t (substtc_inv_tcFn (.var 0))
  have hA1 : PrfH Γ' (provFromCode (substfc zero (tcFn (lenc W))
      (ltCodeFn (tcFn (.var 0)) (varc (numeral 0))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_eq_symm (hcompLt _))) _) hlt1
  have hA2 : PrfH Γ' (provFromCode (substfc zero (bdInB W)
      (ltCodeFn (tcFn (.var 0)) (varc (numeral 0))))) :=
    PrfH_leibniz_apply _ _ _ hBsym hA1
  have hltB : PrfH Γ' (provFromCode (ltCodeFn (tcFn (.var 0)) (bdInB W))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcompLt _)) _) hA2
  have hev : PrfH Γ' (provFromCode (eqCodeFn (nthcT (tcFn W) (tcFn (.var 0)))
      (tcFn (nthc W (.var 0))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_nthc W (.var 0)) _) hlt
  have hcodeq : PrfH Γ' (eqCodeFn (nthcT (tcFn W) (tcFn (.var 0))) (tcFn (nthc W (.var 0)))
      =eq eqCodeFn (nthcT (liftc zero (tcFn W)) (tcFn (.var 0))) (liftc zero (tcFn X))) :=
    PrfH_congr_eqCodeFn
      (prf_to_prfH (prf_congr_nthcT (prf_eq_symm (prf_liftc_tcFn W)) (prf_refl _)) _)
      (PrfH_eq_trans (PrfH_congr_tcFn hbody) (prf_to_prfH (prf_eq_symm (prf_liftc_tcFn X)) _))
  have hphi0 : PrfH Γ' (provFromCode (eqCodeFn (nthcT (liftc zero (tcFn W)) (tcFn (.var 0)))
      (liftc zero (tcFn X)))) := PrfH_provCode_congr hcodeq hev
  have hcompPhi : Prf (substfc zero (tcFn (.var 0)) (bdInPhic X W)
      =eq eqCodeFn (nthcT (liftc zero (tcFn W)) (tcFn (.var 0))) (liftc zero (tcFn X))) := by
    unfold bdInPhic
    refine prf_eq_trans (prf_substfc_eq zero (tcFn (.var 0)) _ _) ?_
    refine prf_congr_eqCodeFn ?_ (substtc_inv_liftc_tcFn X (tcFn (.var 0)))
    refine prf_eq_trans (prf_substtc_nthcT zero (tcFn (.var 0)) _ _) ?_
    exact prf_congr_nthcT (substtc_inv_liftc_tcFn W (tcFn (.var 0)))
      (prf_substtc_varc0 (tcFn (.var 0)))
  have hphi : PrfH Γ' (provFromCode (substfc zero (tcFn (.var 0)) (bdInPhic X W))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_eq_symm hcompPhi)) _) hphi0
  exact PrfH_bdEx_intro_open (bdInB W) (bdInPhic X W) (tcFn (.var 0))
    (substtc_inv_bdInB W) hltB hphi

def phiInBwd : Formula := Formula.impl (boundedIn (.var 1) (.var 0)) (In (.var 1) (.var 0))

theorem InBwd : Prf (forall_2 phiInBwd) :=
  Prf.gen _ (Prf.gen _ (prf_In_of_boundedIn (.var 1) (.var 0)))

theorem pcc_InBwd_computed (x w : Term) :
    Prf (provFromCode (implc (bdInDot x w) (inFormCodeFn (tcFn x) (tcFn w)))) := by
  let A : Term := tcFn x
  let B : Term := tcFn w
  let W : Term := liftc zero A
  have h0 : Prf (provFromCode (substfc zero B (substfc (succ zero) W (formCode phiInBwd)))) :=
    pcc_thm_inst2 phiInBwd InBwd A B
  have hin : Prf (substfc (succ zero) W (formCode phiInBwd)
      =eq implc (exc (andc (ltCodeFn (varc (numeral 0)) (lencT (varc (numeral 1))))
                           (eqCodeFn (nthcT (varc (numeral 1)) (varc (numeral 0)))
                                     (liftc zero W))))
                (inFormCodeFn W (varc (numeral 0)))) :=
    prf_substfc_arith_open 1 W phiInBwd
  have h1 := prf_mp (prf_provCode_congr (prf_congr_substfc3 hin)) h0
  have hv1 : ∀ t : Term, Prf (substtc (succ zero) t (varc (numeral 1)) =eq t) := fun t =>
    prf_mp (prf_substtc_var_eq (succ zero) t (numeral 1)) (prf_refl _)
  have hWnorm : ∀ t : Term, Prf (substtc (succ zero) t (liftc zero W) =eq liftc zero A) := by
    intro t
    refine prf_eq_trans (prf_congr_substtc3 (prf_congr_liftc (prf_liftc_tcFn x))) ?_
    refine prf_eq_trans (prf_congr_substtc3 (prf_liftc_tcFn x)) ?_
    exact prf_eq_trans (prf_substtc_tcFn_at 1 t x) (prf_eq_symm (prf_liftc_tcFn x))
  have hout : Prf (substfc zero B
      (implc (exc (andc (ltCodeFn (varc (numeral 0)) (lencT (varc (numeral 1))))
                        (eqCodeFn (nthcT (varc (numeral 1)) (varc (numeral 0)))
                                  (liftc zero W))))
             (inFormCodeFn W (varc (numeral 0))))
      =eq implc (bdInDot x w) (inFormCodeFn A B)) := by
    refine prf_eq_trans (prf_substfc_impl zero B _ _) (prf_congr_implc ?_ ?_)
    · refine prf_eq_trans (prf_substfc_ex zero B _) (prf_congr_exc ?_)
      refine prf_eq_trans (prf_substfc_and (succ zero) (liftc zero B) _ _)
        (prf_congr_andc ?_ ?_)
      · refine prf_substfc_ltCode2 (succ zero) (liftc zero B) _ _ _ _
          (prf_substtc_varc0_at1 (liftc zero B)) ?_
        exact prf_eq_trans (prf_substtc_lencT (succ zero) (liftc zero B) (varc (numeral 1)))
          (prf_congr_lencT (hv1 (liftc zero B)))
      · refine prf_eq_trans (prf_substfc_eq (succ zero) (liftc zero B) _ _)
          (prf_congr_eqCodeFn ?_ (hWnorm (liftc zero B)))
        exact prf_eq_trans (prf_substtc_nthcT (succ zero) (liftc zero B) _ _)
          (prf_congr_nthcT (hv1 (liftc zero B)) (prf_substtc_varc0_at1 (liftc zero B)))
    · refine prf_substfc_inCode2 zero B _ _ _ _ ?_ (prf_substtc_varc0 B)
      exact prf_eq_trans (substtc_inv_liftc_tcFn x B) (prf_liftc_tcFn x)
  exact prf_mp (prf_provCode_congr hout) h1

/-- **Reflexión del `In` como ÁTOMO**, con `x` y `w` ABSTRACTOS. -/
theorem pcc_In_atom_tracked (x w : Term) :
    Prf (In x w ⇒ provFromCode (inFormCodeFn (tcFn x) (tcFn w))) := by
  refine prf_deduction ?_
  have hbd : PrfH [In x w] (boundedIn x w) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_and_elim_left (prf_In_iff_boundedIn x w)) _)
      (prfH_hyp_self _)
  have h1 : PrfH [In x w] (provFromCode (bdInDot x w)) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_boundedIn_tracked x w) _) hbd
  exact PrfH_mp_code_apply (prf_to_prfH (pcc_InBwd_computed x w) _) h1

theorem PrfH_in_transport {Γ : List Formula} (u v W : Term)
    (hW : ∀ V, Prf (substtc zero V W =eq W))
    (heq : PrfH Γ (provFromCode (eqc u v)))
    (h : PrfH Γ (provFromCode (inFormCodeFn u W))) :
    PrfH Γ (provFromCode (inFormCodeFn v W)) := by
  let Cin : Term := inFormCodeFn (varc (numeral 0)) W
  have hcomp : ∀ t : Term, Prf (substfc zero t Cin =eq inFormCodeFn t W) := fun t =>
    prf_substfc_inDot t (varc (numeral 0)) t W (prf_substtc_varc0 t) hW
  have h1 : PrfH Γ (provFromCode (substfc zero u Cin)) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_eq_symm (hcomp u))) _) h
  have h2 : PrfH Γ (provFromCode (substfc zero v Cin)) := PrfH_leibniz_apply Cin u v heq h1
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp v)) _) h2

/-! ## 7 · Congruencias objeto y clausura de `liftc` sobre los códigos que usamos -/

theorem prf_congr_lenc {t₁ t₂ : Term} (h : Prf (t₁ =eq t₂)) : Prf (lenc t₁ =eq lenc t₂) := by
  let f : Formula := Formula.eq (lenc (liftTerm 0 t₁)) (lenc (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (lenc t₁) (lenc s) := by
    intro s
    simp only [f, lenc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact prfH_nil_to_prf
    ((hS t₂) ▸ PrfH_leibniz_subst (A := f) (prf_to_prfH h [])
      ((hS t₁) ▸ prf_to_prfH (prf_refl (lenc t₁)) [])) rfl

theorem prf_congr_atom2c {pc a a' b b' : Term} (ha : Prf (a =eq a')) (hb : Prf (b =eq b')) :
    Prf (atomc pc (cons a (cons b nil)) =eq atomc pc (cons a' (cons b' nil))) := by
  unfold atomc
  exact prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head
    (prf_eq_trans (prf_congr_cons_head ha) (prf_congr_cons_tail (prf_congr_cons_head hb)))))

theorem prf_congr_argsDotB {B B' Yi Yi' Wi Wi' : Term}
    (hB : Prf (B =eq B')) (hY : Prf (Yi =eq Yi')) (hW : Prf (Wi =eq Wi')) :
    Prf (argsDotB B Yi Wi =eq argsDotB B' Yi' Wi') := by
  unfold argsDotB bdAllCode
  exact prf_congr_forallc (prf_congr_implc
    (prf_congr_atom2c (prf_refl _) hB)
    (prf_congr_atom2c (prf_congr_nthcT hY (prf_refl _)) hW))

/-- `liftc zero` deja fijo un código construido con `funcc` sobre argumentos fijos. -/
theorem liftc_inv_un {sc A : Term} (hA : Prf (liftc zero A =eq A)) :
    Prf (liftc zero (funcc sc (cons A nil)) =eq funcc sc (cons A nil)) := by
  refine prf_eq_trans (prf_liftc_func zero sc (cons A nil)) (prf_congr_funcc2 ?_)
  exact prf_eq_trans (prf_liftsc_cons zero A nil)
    (prf_eq_trans (prf_congr_cons_head hA) (prf_congr_cons_tail (prf_liftsc_nil zero)))

theorem liftc_inv_bin {sc A B : Term} (hA : Prf (liftc zero A =eq A))
    (hB : Prf (liftc zero B =eq B)) :
    Prf (liftc zero (funcc sc (cons A (cons B nil))) =eq funcc sc (cons A (cons B nil))) := by
  refine prf_eq_trans (prf_liftc_func zero sc (cons A (cons B nil))) (prf_congr_funcc2 ?_)
  refine prf_eq_trans (prf_liftsc_cons zero A (cons B nil)) ?_
  refine prf_eq_trans (prf_congr_cons_head hA) (prf_congr_cons_tail ?_)
  exact prf_eq_trans (prf_liftsc_cons zero B nil)
    (prf_eq_trans (prf_congr_cons_head hB) (prf_congr_cons_tail (prf_liftsc_nil zero)))

theorem liftc_inv_lencT {A : Term} (hA : Prf (liftc zero A =eq A)) :
    Prf (liftc zero (lencT A) =eq lencT A) := liftc_inv_un hA

theorem liftc_inv_nthcT {A B : Term} (hA : Prf (liftc zero A =eq A))
    (hB : Prf (liftc zero B =eq B)) :
    Prf (liftc zero (nthcT A B) =eq nthcT A B) := liftc_inv_bin hA hB

/-! ## 8 · **EL REFLECTOR INTERNO** — segunda aplicación de `pcc_bdAll_intro`

    `argsIn` tiene DOS parámetros (testigo y lista) y `pcc_bdAll_intro` sólo uno: se emparejan
    en `p = cons Y q` y se recuperan con `carc`/`cdrc` (que conmutan con `lift`/`subst`
    sintácticamente). Es RUIDO, no un muro. -/

def argsCF (p : Term) : Formula := argsIn (cdrc p) (carc p)
def argsBnd (p : Term) : Term := lenc (carc p)
noncomputable def argsPsi (p : Term) : Term :=
  inFormCodeFn (nthcT (tcFn (carc p)) (varc (numeral 0))) (tcFn (cdrc p))

theorem argsCF_l : ∀ (k : Nat) (p : Term), liftFormula k (argsCF p) = argsCF (liftTerm k p) := by
  intro k p
  simp only [argsCF, liftF_argsIn, carc, cdrc, liftTerm, liftTerms]

theorem argsCF_s : ∀ (v : Nat) (t p : Term),
    substFormula v t (argsCF p) = argsCF (substTerm v t p) := by
  intro v t p
  simp only [argsCF, substF_argsIn, carc, cdrc, substTerm, substTerms]

theorem argsBnd_l : ∀ (k : Nat) (p : Term), liftTerm k (argsBnd p) = argsBnd (liftTerm k p) := by
  intro k p; simp only [argsBnd, lenc, carc, liftTerm, liftTerms]

theorem argsBnd_s : ∀ (v : Nat) (t p : Term),
    substTerm v t (argsBnd p) = argsBnd (substTerm v t p) := by
  intro v t p; simp only [argsBnd, lenc, carc, substTerm, substTerms]

theorem argsPsi_l : ∀ (k : Nat) (p : Term), liftTerm k (argsPsi p) = argsPsi (liftTerm k p) := by
  intro k p
  simp only [argsPsi, inFormCodeFn, nthcT, funcc, varc, tcFn, carc, cdrc, cons, nil, zero, succ,
    liftTerm, liftTerms, liftTerm_numeral, liftTerm_strCode]

theorem argsPsi_s : ∀ (v : Nat) (t p : Term),
    substTerm v t (argsPsi p) = argsPsi (substTerm v t p) := by
  intro v t p
  simp only [argsPsi, inFormCodeFn, nthcT, funcc, varc, tcFn, carc, cdrc, cons, nil, zero, succ,
    substTerm, substTerms, substTerm_numeral, substTerm_strCode]

theorem argsPsi_id : ∀ p : Term,
    Prf (substfc zero (varc (numeral 0)) (argsPsi p) =eq argsPsi p) := by
  intro p
  refine prf_substfc_inCode2 zero (varc (numeral 0)) _ _ _ _ ?_
    (substtc_inv_tcFn (cdrc p) _)
  exact prf_eq_trans
    (prf_substtc_nthcT zero (varc (numeral 0)) (tcFn (carc p)) (varc (numeral 0)))
    (prf_congr_nthcT (substtc_inv_tcFn (carc p) _) (prf_substtc_varc0 (varc (numeral 0))))

theorem PrfH_inst_argsIn {Γ : List Formula} (wT Y i : Term) (h : PrfH Γ (argsIn wT Y)) :
    PrfH Γ (Formula.impl (lt i (lenc Y)) (In (nthc Y i) wT)) := by
  have hi := PrfH_spec h i
  simpa only [argsInBody, lt, lenc, nthc, In, substFormula, substTerm, substTerms,
    FOL.substTerm_liftTerm, if_true] using hi

theorem argsPsi_body : ∀ p i : Term, Prf (argsCF p ⇒ (lt i (argsBnd p)
    ⇒ provFromCode (substfc zero (tcFn i) (argsPsi p)))) := by
  intro p i
  refine prf_deduction (deduction_aux ?_ (lt i (argsBnd p)) [argsCF p] rfl)
  let Γ : List Formula := [lt i (argsBnd p), argsCF p]
  have hlt : PrfH Γ (lt i (lenc (carc p))) := PrfH.hyp _ _ (List.Mem.head _)
  have hargs : PrfH Γ (argsCF p) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hin : PrfH Γ (In (nthc (carc p) i) (cdrc p)) :=
    PrfH.mp _ _ _ (PrfH_inst_argsIn (cdrc p) (carc p) i hargs) hlt
  have hat : PrfH Γ (provFromCode (inFormCodeFn (tcFn (nthc (carc p) i)) (tcFn (cdrc p)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_In_atom_tracked (nthc (carc p) i) (cdrc p)) _) hin
  have hev : PrfH Γ (provFromCode (eqCodeFn (nthcT (tcFn (carc p)) (tcFn i))
      (tcFn (nthc (carc p) i)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_nthc (carc p) i) _) hlt
  have hevS : PrfH Γ (provFromCode (eqCodeFn (tcFn (nthc (carc p) i))
      (nthcT (tcFn (carc p)) (tcFn i)))) :=
    PrfH_eq_symm_code _ _
      (substtc_inv_nthcT (substtc_inv_tcFn (carc p)) (substtc_inv_tcFn i)) hev
  have hres : PrfH Γ (provFromCode (inFormCodeFn (nthcT (tcFn (carc p)) (tcFn i))
      (tcFn (cdrc p)))) :=
    PrfH_in_transport _ _ _ (substtc_inv_tcFn (cdrc p)) hevS hat
  refine PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_eq_symm ?_)) _) hres
  refine prf_substfc_inCode2 zero (tcFn i) _ _ _ _ ?_ (substtc_inv_tcFn (cdrc p) _)
  exact prf_eq_trans (prf_substtc_nthcT zero (tcFn i) (tcFn (carc p)) (varc (numeral 0)))
    (prf_congr_nthcT (substtc_inv_tcFn (carc p) _) (prf_substtc_varc0 (tcFn i)))

/-- El reflector interno EN LA FORMA EMPAREJADA. -/
theorem pcc_argsIn_tracked_pair (p : Term) :
    Prf (argsCF p ⇒ provFromCode (bdAllCode (tcFn (argsBnd p)) (argsPsi p))) :=
  pcc_bdAll_intro argsCF argsBnd argsPsi p argsCF_l argsCF_s argsBnd_l argsBnd_s
    argsPsi_l argsPsi_s argsPsi_id argsPsi_body

theorem PrfH_congr_argsIn_snd {Γ : List Formula} {wT Y₁ Y₂ : Term} (h : PrfH Γ (Y₁ =eq Y₂))
    (ha : PrfH Γ (argsIn wT Y₁)) : PrfH Γ (argsIn wT Y₂) := by
  have hS : ∀ s : Term, substFormula 0 s (argsIn (liftTerm 0 wT) (.var 0)) = argsIn wT s := by
    intro s; simp only [substF_argsIn, substTerm, FOL.substTerm_liftTerm, if_true]
  exact (hS Y₂) ▸ PrfH_leibniz_subst (A := argsIn (liftTerm 0 wT) (.var 0)) h ((hS Y₁) ▸ ha)

theorem PrfH_congr_argsIn_fst {Γ : List Formula} {wT₁ wT₂ Y : Term} (h : PrfH Γ (wT₁ =eq wT₂))
    (ha : PrfH Γ (argsIn wT₁ Y)) : PrfH Γ (argsIn wT₂ Y) := by
  have hS : ∀ s : Term, substFormula 0 s (argsIn (.var 0) (liftTerm 0 Y)) = argsIn s Y := by
    intro s; simp only [substF_argsIn, substTerm, FOL.substTerm_liftTerm, if_true]
  exact (hS wT₂) ▸ PrfH_leibniz_subst (A := argsIn (.var 0) (liftTerm 0 Y)) h ((hS wT₁) ▸ ha)

/-- **EL REFLECTOR INTERNO**, desemparejado: `q` e `Y` ABSTRACTOS, cota en forma PURA. -/
theorem pcc_argsIn_tracked_pure (q Y : Term) :
    Prf (argsIn q Y ⇒ provFromCode (argsDotB (tcFn (lenc Y)) (tcFn Y) (tcFn q))) := by
  refine prf_deduction ?_
  let p : Term := cons Y q
  have hc : Prf (carc p =eq Y) := prf_carc_cons Y q
  have hd : Prf (cdrc p =eq q) := prf_cdrc_cons Y q
  have h0 : PrfH [argsIn q Y] (argsIn q Y) := prfH_hyp_self _
  have h1 : PrfH [argsIn q Y] (argsCF p) :=
    PrfH_congr_argsIn_fst (prf_to_prfH (prf_eq_symm hd) _)
      (PrfH_congr_argsIn_snd (prf_to_prfH (prf_eq_symm hc) _) h0)
  have h2 : PrfH [argsIn q Y] (provFromCode (bdAllCode (tcFn (argsBnd p)) (argsPsi p))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_argsIn_tracked_pair p) _) h1
  refine PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr ?_) _) h2
  exact prf_congr_argsDotB (prf_congr_tcFn (prf_congr_lenc hc)) (prf_congr_tcFn hc)
    (prf_congr_tcFn hd)

/-- La CONVERSIÓN DE LA COTA (`tcFn (lenc Y)` ⇝ `lencT (tcFn Y)`) **dentro** del `∀` interno:
    una Leibniz interna con el hueco en `varc ⌜1⌝` (o sea, dentro del binder). -/
theorem pcc_argsIn_tracked (q Y : Term) :
    Prf (argsIn q Y ⇒ provFromCode (argsDotI (tcFn Y) (tcFn q))) := by
  refine prf_deduction ?_
  have h0 : PrfH [argsIn q Y] (provFromCode (argsDotB (tcFn (lenc Y)) (tcFn Y) (tcFn q))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_argsIn_tracked_pure q Y) _) (prfH_hyp_self _)
  -- contexto de Leibniz: la cota es el hueco, y VIVE DENTRO del binder (`varc ⌜1⌝`)
  let C : Term := argsDotB (varc (numeral 1)) (tcFn Y) (tcFn q)
  have hcomp : ∀ t : Term, Prf (liftc zero t =eq t) →
      Prf (substfc zero t C =eq argsDotB t (tcFn Y) (tcFn q)) := by
    intro t ht
    exact prf_substfc_argsDotB t t _ _ _ _ _ _ ht (prf_substtc_varc1_at1 t)
      (substtc_inv_tcFn_at1 Y t) (substtc_inv_tcFn_at1 q t)
  have hL1 : Prf (liftc zero (tcFn (lenc Y)) =eq tcFn (lenc Y)) := prf_liftc_tcFn (lenc Y)
  have hL2 : Prf (liftc zero (lencT (tcFn Y)) =eq lencT (tcFn Y)) :=
    liftc_inv_lencT (prf_liftc_tcFn Y)
  have heq : PrfH [argsIn q Y]
      (provFromCode (eqc (tcFn (lenc Y)) (lencT (tcFn Y)))) :=
    PrfH_eq_symm_code _ _ (substtc_inv_lencT (substtc_inv_tcFn Y))
      (prf_to_prfH (pcc_eval_lenc Y) _)
  have h1 : PrfH [argsIn q Y] (provFromCode (substfc zero (tcFn (lenc Y)) C)) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_eq_symm (hcomp _ hL1))) _) h0
  have h2 : PrfH [argsIn q Y] (provFromCode (substfc zero (lencT (tcFn Y)) C)) :=
    PrfH_leibniz_apply C _ _ heq h1
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp _ hL2)) _) h2

/-! ## 9 · La reflexión PURA del nodo (`X` abstracto, hueco todavía `tcFn X`) -/

theorem pcc_carcD_bridge_cons (X : Term) :
    Prf (consOk X ⇒ provFromCode (eqCodeFn (carcT (tcFn X)) (tcFn (carc X)))) := by
  refine prf_deduction ?_
  have hcons := prfH_hyp_self (consOk X)
  exact PrfH_provCode_congr
    (PrfH_congr_eqCodeFn (PrfH_congr_carcT (PrfH_congr_tcFn (PrfH_eq_symm hcons)))
      (prf_to_prfH (prf_refl _) _))
    (prf_to_prfH (pcc_eval_carc (carc X) (cdrc X)) _)

theorem pcc_shape_tracked (X : Term) (k n : Nat) :
    Prf (consOk X ⇒ (land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM n))
      ⇒ provFromCode (shapeDot (tcFn X) k n))) := by
  refine prf_deduction (deduction_aux ?_
    (land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM n)))
    [consOk X] rfl)
  let Γ : List Formula :=
    [land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM n)), consOk X]
  show PrfH Γ (provFromCode (shapeDot (tcFn X) k n))
  have hsh : PrfH Γ
      (land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM n))) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hcons : PrfH Γ (consOk X) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hcarc : PrfH Γ (provFromCode (eqCodeFn (carcT (tcFn X)) (tcFn (carc X)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_carcD_bridge_cons X) _) hcons
  have hcarc2 : PrfH Γ (provFromCode (eqCodeFn (tcFn (carc X)) (tcFn (numeralM k)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eq_tracked (carc X) (numeralM k)) _)
      (PrfH_and_elim_left hsh)
  have hA : PrfH Γ (provFromCode (eqCodeFn (carcT (tcFn X)) (tcFn (numeralM k)))) :=
    PrfH_eq_trans_code _ _ _ (substtc_inv_carcT (substtc_inv_tcFn X)) hcarc hcarc2
  have hlen : PrfH Γ (provFromCode (eqCodeFn (lencT (tcFn X)) (tcFn (lenc X)))) :=
    prf_to_prfH (pcc_eval_lenc X) Γ
  have hlen2 : PrfH Γ (provFromCode (eqCodeFn (tcFn (lenc X)) (tcFn (numeralM n)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eq_tracked (lenc X) (numeralM n)) _)
      (PrfH_and_elim_right hsh)
  have hB : PrfH Γ (provFromCode (eqCodeFn (lencT (tcFn X)) (tcFn (numeralM n)))) :=
    PrfH_eq_trans_code _ _ _ (substtc_inv_lencT (substtc_inv_tcFn X)) hlen hlen2
  exact PrfH_and_intro_code _ _ hA hB

theorem pcc_varOkT_case (X : Term) :
    Prf (cOk X (varOkT X) ⇒ provFromCode (shapeDot (tcFn X) 0 2)) := by
  refine prf_deduction ?_
  have h := prfH_hyp_self (cOk X (varOkT X))
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (pcc_shape_tracked X 0 2) _)
    (PrfH_and_elim_left h)) (PrfH_and_elim_right h)

/-- El caso `funcc` — el que lleva el `∀` ANIDADO. Dos transportes: la cota (ya hecha en
    `pcc_argsIn_tracked`) y la lista de argumentos (`tcFn Y ⇝ nthcT Ẋ 2̇`). -/
theorem pcc_funcOkT1_case (q X : Term) :
    Prf (cOk X (funcOkT1 q X) ⇒ provFromCode (funcDot (tcFn q) (tcFn X) (tcFn X))) := by
  refine prf_deduction ?_
  let Γ : List Formula := [cOk X (funcOkT1 q X)]
  have h := prfH_hyp_self (cOk X (funcOkT1 q X))
  have hcons : PrfH Γ (consOk X) := PrfH_and_elim_left h
  have hf := PrfH_and_elim_right h
  have hsh := PrfH_and_elim_left hf
  have hargs : PrfH Γ (argsIn q (nthc X (numeralM 2))) := PrfH_and_elim_right hf
  have hlen : PrfH Γ (Formula.eq (lenc X) (numeralM 3)) := PrfH_and_elim_right hsh
  have h1 : PrfH Γ (provFromCode (shapeDot (tcFn X) 1 3)) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (pcc_shape_tracked X 1 3) _) hcons) hsh
  -- la reflexión del `∀` interno, con la lista de argumentos en forma PURA
  have h2 : PrfH Γ (provFromCode (argsDotI (tcFn (nthc X (numeralM 2))) (tcFn q))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_argsIn_tracked q (nthc X (numeralM 2))) _) hargs
  -- transporte `tcFn (nthc X 2̄) ⇝ nthcT (tcFn X) 2̇` (una sola Leibniz, cubre cota Y cuerpo)
  have hlt : PrfH Γ (lt (numeralM 2) (lenc X)) :=
    ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2 (PrfH_eq_symm hlen)
      (prf_to_prfH (prf_lt_numeralM (by omega : 2 < 3)) _)
  have hev : PrfH Γ (provFromCode (eqCodeFn (nthcT (tcFn X) (tcFn (numeralM 2)))
      (tcFn (nthc X (numeralM 2))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_nthc X (numeralM 2)) _) hlt
  have hevS : PrfH Γ (provFromCode (eqc (tcFn (nthc X (numeralM 2)))
      (nthcT (tcFn X) (tcFn (numeralM 2))))) :=
    PrfH_eq_symm_code _ _
      (substtc_inv_nthcT (substtc_inv_tcFn X) (substtc_inv_tcFn (numeralM 2))) hev
  let C : Term := argsDotI (varc (numeral 1)) (tcFn q)
  have hcomp : ∀ t : Term, Prf (liftc zero t =eq t) →
      Prf (substfc zero t C =eq argsDotI t (tcFn q)) := fun t ht =>
    prf_substfc_argsDotI t t _ _ _ _ ht (prf_substtc_varc1_at1 t) (substtc_inv_tcFn_at1 q t)
  have hA : PrfH Γ (provFromCode (substfc zero (tcFn (nthc X (numeralM 2))) C)) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr
      (prf_eq_symm (hcomp _ (prf_liftc_tcFn (nthc X (numeralM 2)))))) _) h2
  have hB : PrfH Γ (provFromCode (substfc zero (nthcT (tcFn X) (tcFn (numeralM 2))) C)) :=
    PrfH_leibniz_apply C _ _ hevS hA
  have h3 : PrfH Γ (provFromCode (argsDotI (nthcT (tcFn X) (tcFn (numeralM 2))) (tcFn q))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr
      (hcomp _ (liftc_inv_nthcT (prf_liftc_tcFn X) (prf_liftc_tcFn (numeralM 2))))) _) hB
  exact PrfH_and_intro_code _ _ h1 h3

/-- **La reflexión PURA del nodo**, con `q` y `X` ABSTRACTOS. -/
theorem pcc_isTermCodeB1_pure (q X : Term) :
    Prf (isTermCodeB1 q X ⇒ provFromCode (isTCDot (tcFn q) (tcFn X) (tcFn X))) :=
  prf_or_elim_imp
    (impT (pcc_varOkT_case X) (prf_orL_imp (shapeDot (tcFn X) 0 2) _))
    (impT (pcc_funcOkT1_case q X) (prf_orR_imp (shapeDot (tcFn X) 0 2) _))

/-! ## 10 · `hbody` y **EL REFLECTOR** -/

theorem hbody_ok : ∀ q i : Term, Prf (wfAllB1 q ⇒ (lt i (lenc q)
    ⇒ provFromCode (substfc zero (tcFn i) (PsiF q)))) := by
  intro q i
  refine prf_deduction (deduction_aux ?_ (lt i (lenc q)) [wfAllB1 q] rfl)
  let Γ : List Formula := [lt i (lenc q), wfAllB1 q]
  have hlt : PrfH Γ (lt i (lenc q)) := PrfH.hyp _ _ (List.Mem.head _)
  have hwf : PrfH Γ (wfAllB1 q) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hsubst : substFormula 0 i (wfAllB1Body q)
      = Formula.impl (lt i (lenc q)) (isTermCodeB1 q (nthc q i)) := by
    simp only [wfAllB1Body, substFormula, substF_isTermCodeB1, lt, lenc, nthc,
      substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  have h0 := PrfH_spec hwf i
  rw [hsubst] at h0
  have hnode : PrfH Γ (isTermCodeB1 q (nthc q i)) := PrfH.mp _ _ _ h0 hlt
  have hpure : PrfH Γ (provFromCode (isTCDot (tcFn q) (tcFn (nthc q i)) (tcFn (nthc q i)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_isTermCodeB1_pure q (nthc q i)) _) hnode
  -- UNA Leibniz: el hueco es `⌜v₀⌝` fuera y `⌜v₁⌝` dentro del `∀` anidado
  have hev : PrfH Γ (provFromCode (eqCodeFn (nthcT (tcFn q) (tcFn i)) (tcFn (nthc q i)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_nthc q i) _) hlt
  have hevS : PrfH Γ (provFromCode (eqc (tcFn (nthc q i)) (nthcT (tcFn q) (tcFn i)))) :=
    PrfH_eq_symm_code _ _
      (substtc_inv_nthcT (substtc_inv_tcFn q) (substtc_inv_tcFn i)) hev
  let Cx : Term := isTCDot (tcFn q) (varc (numeral 0)) (varc (numeral 1))
  have hcomp : ∀ t : Term, Prf (liftc zero t =eq t) →
      Prf (substfc zero t Cx =eq isTCDot (tcFn q) t t) := fun t ht =>
    prf_substfc_isTCDot t t (tcFn q) (tcFn q) _ _ _ _ ht (substtc_inv_tcFn_at1 q t)
      (prf_substtc_varc0 t) (prf_substtc_varc1_at1 t)
  have hA : PrfH Γ (provFromCode (substfc zero (tcFn (nthc q i)) Cx)) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr
      (prf_eq_symm (hcomp _ (prf_liftc_tcFn (nthc q i))))) _) hpure
  have hB : PrfH Γ (provFromCode (substfc zero (nthcT (tcFn q) (tcFn i)) Cx)) :=
    PrfH_leibniz_apply Cx _ _ hevS hA
  have h3 : PrfH Γ (provFromCode (isTCDot (tcFn q) (nthcT (tcFn q) (tcFn i))
      (nthcT (tcFn q) (tcFn i)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr
      (hcomp _ (liftc_inv_nthcT (prf_liftc_tcFn q) (prf_liftc_tcFn i)))) _) hB
  exact PrfH.mp _ _ _
    (prf_to_prfH (prf_provCode_congr (prf_eq_symm (prf_substfc_PsiF_at q i))) _) h3

/-- **EL REFLECTOR CON EL `∀` ANIDADO**: `w` ABSTRACTO, cero axiomas nuevos. -/
theorem pcc_wfAllB1_tracked (w : Term) : Prf (wfAllB1 w ⇒ provFromCode (wfAllB1Dot w)) :=
  pcc_bdAll_intro wfAllB1 lenc PsiF w hCl_ok hCs_ok hbl_ok hbs_ok hPl_ok hPs_ok
    hPsiId_ok hbody_ok

/-! ## 11 · ATERRIZAJE en el predicado REAL de la vía (forma ECUACIONAL, `sondeos/ClausuraLiftSinWTs.lean`)

    Copias literales del sondeo: la forma ecuacional FORTALECE la forma `carc`/`lenc`, luego el
    reflector de arriba vale tal cual para `wfAll1`. -/

theorem prf_lorL (A B : Formula) : Prf (Formula.impl A (lor A B)) := Prf.incl (Prfᵢ.j1 A B)
theorem prf_lorR (A B : Formula) : Prf (Formula.impl B (lor A B)) := Prf.incl (Prfᵢ.j2 A B)

def shapeUn (X : Term) (k : Nat) : Formula :=
  Formula.eq X (cons (numeralM k) (cons (nthc X (numeralM 1)) nil))

def shapeBin (X : Term) (k : Nat) : Formula :=
  Formula.eq X (cons (numeralM k)
    (cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil)))

def isTermCodeE1 (wT X : Term) : Formula :=
  lor (shapeUn X 0) (land (shapeBin X 1) (argsIn wT (nthc X (numeralM 2))))

def wfAll1Body (w : Term) : Formula :=
  Formula.impl (lt (.var 0) (liftTerm 0 (lenc w)))
    (isTermCodeE1 (liftTerm 0 w) (nthc (liftTerm 0 w) (.var 0)))

def wfAll1 (w : Term) : Formula := Formula.forall (wfAll1Body w)

theorem prf_shape_strengthens (X C : Term) (k n : Nat)
    (hcarc : Prf (carc C =eq numeralM k))
    (hlenc : Prf (lenc C =eq numeralM n))
    (hcons : Prf (consOk C)) :
    Prf (Formula.impl (Formula.eq X C)
      (land (consOk X) (land (Formula.eq (carc X) (numeralM k))
                             (Formula.eq (lenc X) (numeralM n))))) := by
  refine prf_deduction ?_
  let f : Formula :=
    land (Formula.eq (.var 0) (cons (carc (.var 0)) (cdrc (.var 0))))
         (land (Formula.eq (carc (.var 0)) (numeralM k))
               (Formula.eq (lenc (.var 0)) (numeralM n)))
  have hS : ∀ s : Term, substFormula 0 s f =
      land (consOk s) (land (Formula.eq (carc s) (numeralM k))
                            (Formula.eq (lenc s) (numeralM n))) := by
    intro s
    simp only [f, consOk, land, carc, cdrc, lenc, cons, substFormula, substTerm, substTerms,
      substTerm_numeralM, if_true]
  have hbase : PrfH [Formula.eq X C] (substFormula 0 C f) := by
    rw [hS]
    exact prf_to_prfH (prf_and_intro hcons (prf_and_intro hcarc hlenc)) _
  have hres : PrfH [Formula.eq X C] (substFormula 0 X f) :=
    PrfH_leibniz_subst (A := f) (PrfH_eq_symm (prfH_hyp_self (Formula.eq X C))) hbase
  rw [hS] at hres
  exact hres

theorem prf_consOk_cons (a b : Term) : Prf (consOk (cons a b)) :=
  prf_eq_trans (prf_congr_cons_head (prf_eq_symm (prf_carc_cons a b)))
    (prf_congr_cons_tail (prf_eq_symm (prf_cdrc_cons a b)))

theorem prf_lenc_c1 (a : Term) : Prf (lenc (cons a nil) =eq numeralM 1) :=
  prf_eq_trans (prf_lenc_cons a nil) (prf_eq_congr_succ prf_lenc_nil)

theorem prf_lenc_c2 (a b : Term) : Prf (lenc (cons a (cons b nil)) =eq numeralM 2) :=
  prf_eq_trans (prf_lenc_cons a (cons b nil)) (prf_eq_congr_succ (prf_lenc_c1 b))

theorem prf_lenc_c3 (a b c : Term) :
    Prf (lenc (cons a (cons b (cons c nil))) =eq numeralM 3) :=
  prf_eq_trans (prf_lenc_cons a (cons b (cons c nil))) (prf_eq_congr_succ (prf_lenc_c2 b c))

theorem prf_shapeUn_str (X : Term) (k : Nat) :
    Prf (Formula.impl (shapeUn X k)
      (land (consOk X) (land (Formula.eq (carc X) (numeralM k))
                             (Formula.eq (lenc X) (numeralM 2))))) :=
  prf_shape_strengthens X _ k 2 (prf_carc_cons _ _) (prf_lenc_c2 _ _) (prf_consOk_cons _ _)

theorem prf_shapeBin_str (X : Term) (k : Nat) :
    Prf (Formula.impl (shapeBin X k)
      (land (consOk X) (land (Formula.eq (carc X) (numeralM k))
                             (Formula.eq (lenc X) (numeralM 3))))) :=
  prf_shape_strengthens X _ k 3 (prf_carc_cons _ _) (prf_lenc_c3 _ _ _) (prf_consOk_cons _ _)

theorem prf_str_and (X : Term) (k n : Nat) (S M : Formula)
    (hstr : Prf (Formula.impl S (land (consOk X)
      (land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM n)))))) :
    Prf (Formula.impl (land S M)
      (cOk X (land (land (Formula.eq (carc X) (numeralM k))
                         (Formula.eq (lenc X) (numeralM n))) M))) := by
  refine prf_deduction ?_
  let Γ : List Formula := [land S M]
  have hh : PrfH Γ (land S M) := prfH_hyp_self _
  have hs : PrfH Γ (land (consOk X) (land (Formula.eq (carc X) (numeralM k))
      (Formula.eq (lenc X) (numeralM n)))) :=
    PrfH.mp _ _ _ (prf_to_prfH hstr _) (PrfH_and_elim_left hh)
  exact PrfH_and_intro (PrfH_and_elim_left hs)
    (PrfH_and_intro (PrfH_and_elim_right hs) (PrfH_and_elim_right hh))

theorem prf_isTermCodeE1_str (wT X : Term) :
    Prf (Formula.impl (isTermCodeE1 wT X) (isTermCodeB1 wT X)) := by
  unfold isTermCodeE1 isTermCodeB1
  refine prf_or_elim_imp (impT (prf_shapeUn_str X 0) (prf_lorL _ _)) ?_
  exact impT (prf_str_and X 1 3 _ _ (prf_shapeBin_str X 1)) (prf_lorR _ _)

theorem liftF_isTermCodeE1 (k : Nat) (wT X : Term) :
    liftFormula k (isTermCodeE1 wT X) = isTermCodeE1 (liftTerm k wT) (liftTerm k X) := by
  simp only [isTermCodeE1, shapeUn, shapeBin, lor, land, liftFormula, liftF_argsIn,
    nthc, cons, nil, zero, liftTerm, liftTerms, liftTerm_numeralM]

theorem liftF_wfAll1 (k : Nat) (w : Term) :
    liftFormula k (wfAll1 w) = wfAll1 (liftTerm k w) := by
  simp only [wfAll1, wfAll1Body, liftFormula, liftF_isTermCodeE1, lt, lenc, nthc,
    liftTerm, liftTerms, Nat.zero_lt_succ, reduceIte, if_true, ← FOL.liftTerm_comm_zero]

theorem substF_wfAll1Body (w i : Term) :
    substFormula 0 i (wfAll1Body w)
      = Formula.impl (lt i (lenc w)) (isTermCodeE1 w (nthc w i)) := by
  simp only [wfAll1Body, isTermCodeE1, shapeUn, shapeBin, lor, land, substFormula, substF_argsIn,
    lt, lenc, nthc, cons, nil, zero, substTerm, substTerms, substTerm_numeralM,
    FOL.substTerm_liftTerm, if_true]

/-- La forma ECUACIONAL implica la forma `carc`/`lenc`, tambien BAJO el `∀` externo. -/
theorem prf_wfAll1_to_B1 (w : Term) : Prf (Formula.impl (wfAll1 w) (wfAllB1 w)) := by
  refine prf_mp (Prf.qconf (wfAll1 w) (wfAllB1Body w)) (Prf.gen _ ?_)
  rw [liftF_wfAll1]
  have hlw : lenc (liftTerm 0 w) = liftTerm 0 (lenc w) := by
    simp only [lenc, liftTerm, liftTerms]
  unfold wfAllB1Body
  refine prf_deduction (deduction_aux ?_ (lt (.var 0) (liftTerm 0 (lenc w)))
    [wfAll1 (liftTerm 0 w)] rfl)
  let Γ : List Formula := [lt (.var 0) (liftTerm 0 (lenc w)), wfAll1 (liftTerm 0 w)]
  have hlt : PrfH Γ (lt (.var 0) (liftTerm 0 (lenc w))) := PrfH.hyp _ _ (List.Mem.head _)
  have hw : PrfH Γ (wfAll1 (liftTerm 0 w)) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have h0 := PrfH_spec hw (.var 0)
  rw [substF_wfAll1Body] at h0
  have hlt2 : PrfH Γ (lt (.var 0) (lenc (liftTerm 0 w))) := by rw [hlw]; exact hlt
  exact PrfH.mp _ _ _
    (prf_to_prfH (prf_isTermCodeE1_str (liftTerm 0 w) (nthc (liftTerm 0 w) (.var 0))) _)
    (PrfH.mp _ _ _ h0 hlt2)

/-- **EL REFLECTOR DE LA VIA 2, sobre el predicado REAL** — `∀` ANIDADO incluido. -/
theorem pcc_wfAll1_tracked (w : Term) : Prf (wfAll1 w ⇒ provFromCode (wfAllB1Dot w)) :=
  impT (prf_wfAll1_to_B1 w) (pcc_wfAllB1_tracked w)

/-- Y el reconocedor entero `isTC1 w c = wfAll1 w ∧ c ∈ w`. -/
def isTC1 (w c : Term) : Formula := land (wfAll1 w) (In c w)

noncomputable def isTC1Dot (w c : Term) : Term :=
  andc (wfAllB1Dot w) (inFormCodeFn (tcFn c) (tcFn w))

theorem pcc_isTC1_tracked (w c : Term) : Prf (isTC1 w c ⇒ provFromCode (isTC1Dot w c)) := by
  refine prf_deduction ?_
  have h := prfH_hyp_self (isTC1 w c)
  exact PrfH_and_intro_code _ _
    (PrfH.mp _ _ _ (prf_to_prfH (pcc_wfAll1_tracked w) _) (PrfH_and_elim_left h))
    (PrfH.mp _ _ _ (prf_to_prfH (pcc_In_atom_tracked c w) _) (PrfH_and_elim_right h))

/-! ## 12 · NO VACUIDAD — una instancia CERRADA que pasa **por la rama del `∀` ANIDADO**

    Testigo `w = [⌜0⌝]`, código `c = ⌜0⌝ = funcc ⌜"0"⌝ nil`: el nodo es un `funcc`, luego el
    disyunto que se usa es el que lleva `argsIn` — el `∀` anidado. (Su lista de argumentos es
    `nil`, o sea el `∀` interno es vacuo, pero el CÓDIGO que se produce es el `bdAllCode`
    anidado de verdad.) -/

theorem substF_isTermCodeE1 (v : Nat) (t wT X : Term) :
    substFormula v t (isTermCodeE1 wT X)
      = isTermCodeE1 (substTerm v t wT) (substTerm v t X) := by
  simp only [isTermCodeE1, shapeUn, shapeBin, lor, land, substFormula, substF_argsIn,
    nthc, cons, nil, zero, substTerm, substTerms, substTerm_numeralM]

theorem PrfH_congr_isTermCodeE1 {Γ : List Formula} {wT X₁ X₂ : Term} (h : PrfH Γ (X₁ =eq X₂))
    (ha : PrfH Γ (isTermCodeE1 wT X₁)) : PrfH Γ (isTermCodeE1 wT X₂) := by
  have hS : ∀ s : Term,
      substFormula 0 s (isTermCodeE1 (liftTerm 0 wT) (.var 0)) = isTermCodeE1 wT s := by
    intro s; simp only [substF_isTermCodeE1, substTerm, FOL.substTerm_liftTerm, if_true]
  exact (hS X₂) ▸ PrfH_leibniz_subst (A := isTermCodeE1 (liftTerm 0 wT) (.var 0)) h ((hS X₁) ▸ ha)

theorem PrfH_congr_nthc_idx {Γ : List Formula} {w i₁ i₂ : Term} (h : PrfH Γ (i₁ =eq i₂)) :
    PrfH Γ (nthc w i₁ =eq nthc w i₂) := by
  let f : Formula :=
    Formula.eq (nthc (liftTerm 0 w) (liftTerm 0 i₁)) (nthc (liftTerm 0 w) (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (nthc w i₁) (nthc w s) := by
    intro s
    simp only [f, nthc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS i₂) ▸ PrfH_leibniz_subst (A := f) h ((hS i₁) ▸ prf_to_prfH (prf_refl (nthc w i₁)) Γ)

theorem prf_nthc_c1 (a b c : Term) : Prf (nthc (cons a (cons b c)) (numeralM 1) =eq b) :=
  prf_eq_trans (prf_nthc_succ a (cons b c) (numeralM 0)) (prf_nthc_zero b c)

theorem prf_nthc_c2 (a b c d : Term) :
    Prf (nthc (cons a (cons b (cons c d))) (numeralM 2) =eq c) :=
  prf_eq_trans (prf_nthc_succ a (cons b (cons c d)) (numeralM 1)) (prf_nthc_c1 b c d)

/-- El `∀` acotado sobre la lista VACIA es vacuamente verdadero. -/
theorem prf_argsIn_nil (q : Term) : Prf (argsIn q nil) := by
  have hnil : liftTerm 0 nil = nil := by simp only [nil, zero, liftTerm, liftTerms]
  have hlen : liftTerm 0 (lenc nil) = lenc nil := by
    simp only [lenc, nil, zero, liftTerm, liftTerms]
  refine Prf.gen _ ?_
  unfold argsInBody
  rw [hnil, hlen]
  refine prf_deduction ?_
  have hlt : PrfH [lt (.var 0) (lenc nil)] (lt (.var 0) zero) :=
    ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
      (prf_to_prfH prf_lenc_nil _) (prfH_hyp_self _)
  exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prfᵢ.efq _))
    (PrfH.mp _ _ _ (prf_to_prfH (prf_not_lt_zero (.var 0)) _) hlt)

/-- `⌜0⌝` como código de TERMINO: `funcc ⌜"0"⌝ nil` (símbolo nulario, lista de args vacía). -/
def Xz : Term := funcc (strCode "0") nil
def wz : Term := cons Xz nil

theorem prf_nthc_Xz_1 : Prf (nthc Xz (numeralM 1) =eq strCode "0") :=
  prf_nthc_c1 (succ zero) (strCode "0") (cons nil nil)

theorem prf_nthc_Xz_2 : Prf (nthc Xz (numeralM 2) =eq nil) :=
  prf_nthc_c2 (succ zero) (strCode "0") nil nil

theorem prf_shapeBin_Xz : Prf (shapeBin Xz 1) := by
  refine prf_eq_symm ?_
  exact prf_congr_cons_tail (prf_eq_trans (prf_congr_cons_head prf_nthc_Xz_1)
    (prf_congr_cons_tail (prf_congr_cons_head prf_nthc_Xz_2)))

theorem prf_isTermCodeE1_Xz (q : Term) : Prf (isTermCodeE1 q Xz) := by
  refine prf_mp (prf_lorR _ _) (prf_and_intro prf_shapeBin_Xz ?_)
  refine prfH_nil_to_prf (PrfH_congr_argsIn_snd (prf_to_prfH (prf_eq_symm prf_nthc_Xz_2) [])
    (prf_to_prfH (prf_argsIn_nil q) [])) rfl

theorem prf_wfAll1_wz : Prf (wfAll1 wz) := by
  have hlift : liftTerm 0 wz = wz := by
    simp only [wz, Xz, funcc, cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_strCode]
  refine Prf.gen _ ?_
  unfold wfAll1Body
  rw [hlift]
  refine prf_deduction ?_
  have hlen : Prf (lenc wz =eq numeralM 1) := prf_lenc_c1 Xz
  have hlt1 : PrfH [lt (.var 0) (liftTerm 0 (lenc wz))] (lt (.var 0) (succ zero)) := by
    have hl : liftTerm 0 (lenc wz) = lenc wz := by
      simp only [lenc, wz, Xz, funcc, cons, nil, zero, succ, liftTerm, liftTerms,
        liftTerm_strCode]
    rw [hl] at *
    exact ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
      (prf_to_prfH hlen _) (prfH_hyp_self _)
  have hsplit : PrfH [lt (.var 0) (liftTerm 0 (lenc wz))]
      (lor (lt (.var 0) zero) (Formula.eq (.var 0) zero)) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_lt_succ_split (.var 0) zero) _) hlt1
  refine PrfH_or_elim hsplit ?brA ?brB
  case brA =>
    exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prfᵢ.efq _))
      (PrfH.mp _ _ _ (prf_to_prfH (prf_not_lt_zero (.var 0)) _) (PrfH.hyp _ _ (List.Mem.head _)))
  case brB =>
    have hi : PrfH (Formula.eq (.var 0) zero :: [lt (.var 0) (liftTerm 0 (lenc wz))])
        (Formula.eq (.var 0) zero) := PrfH.hyp _ _ (List.Mem.head _)
    have hX : PrfH (Formula.eq (.var 0) zero :: [lt (.var 0) (liftTerm 0 (lenc wz))])
        (Formula.eq (nthc wz (.var 0)) Xz) :=
      PrfH_eq_trans (PrfH_congr_nthc_idx (w := wz) hi)
        (prf_to_prfH (prf_nthc_zero Xz nil) _)
    exact PrfH_congr_isTermCodeE1 (PrfH_eq_symm hX)
      (prf_to_prfH (prf_isTermCodeE1_Xz wz) _)

theorem prf_isTC1_wz : Prf (isTC1 wz Xz) :=
  prf_and_intro prf_wfAll1_wz (prf_in_cons_head Xz nil)

/-- **INSTANCIA CERRADA, extremo a extremo, POR LA RAMA DEL `∀` ANIDADO**:
    `⊢ Prov(⌜ isTC1([⌜0⌝], ⌜0⌝) ⌝)`. Certifica que el reflector NO es vacío. -/
theorem pcc_isTC1_wz : Prf (provFromCode (isTC1Dot wz Xz)) :=
  prf_mp (pcc_isTC1_tracked wz Xz) prf_isTC1_wz


/-! ## 13 · CRIT-A — NO VACUIDAD **FUERTE**: instancia cerrada con lista de argumentos NO VACIA.

    La instancia del agente (`wz = [0c]`) tiene lista de argumentos `nil`: el forall INTERNO es
    VACUO y `pcc_bdAll_intro` interno solo ejerce su CASO BASE. Aqui se hace con
    `Sz = S(0) = funcc (strCode "S") [Xz]`, cuya lista de argumentos es `[Xz]` (longitud 1):
    el forall interno tiene que probar de verdad `Xz IN w`. -/

theorem PrfH_congr_In_fst {G : List Formula} {a b q : Term} (h : PrfH G (a =eq b))
    (ha : PrfH G (In a q)) : PrfH G (In b q) := by
  have hS : ∀ s : Term, substFormula 0 s (In (.var 0) (liftTerm 0 q)) = In s q := by
    intro s
    simp only [In, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b) ▸ PrfH_leibniz_subst (A := In (.var 0) (liftTerm 0 q)) h ((hS a) ▸ ha)

/-- El forall acotado interno sobre una lista de UN elemento: NO es vacuo. -/
theorem prf_argsIn_singleton (q a : Term)
    (hq : liftTerm 0 q = q) (ha : liftTerm 0 a = a)
    (h : Prf (In a q)) : Prf (argsIn q (cons a nil)) := by
  have hl : liftTerm 0 (lenc (cons a nil)) = lenc (cons a nil) := by
    simp only [lenc, cons, nil, zero, liftTerm, liftTerms, ha]
  have hc : liftTerm 0 (cons a nil) = cons a nil := by
    simp only [cons, nil, zero, liftTerm, liftTerms, ha]
  refine Prf.gen _ ?_
  unfold argsInBody
  rw [hl, hc, hq]
  refine prf_deduction ?_
  have hlen : Prf (lenc (cons a nil) =eq numeralM 1) := prf_lenc_c1 a
  have hlt1 : PrfH [lt (.var 0) (lenc (cons a nil))] (lt (.var 0) (succ zero)) :=
    ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2 (prf_to_prfH hlen _) (prfH_hyp_self _)
  have hsplit : PrfH [lt (.var 0) (lenc (cons a nil))]
      (lor (lt (.var 0) zero) (Formula.eq (.var 0) zero)) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_lt_succ_split (.var 0) zero) _) hlt1
  refine PrfH_or_elim hsplit ?brA ?brB
  case brA =>
    exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prfᵢ.efq _))
      (PrfH.mp _ _ _ (prf_to_prfH (prf_not_lt_zero (.var 0)) _) (PrfH.hyp _ _ (List.Mem.head _)))
  case brB =>
    have hi : PrfH (Formula.eq (.var 0) zero :: [lt (.var 0) (lenc (cons a nil))])
        (Formula.eq (.var 0) zero) := PrfH.hyp _ _ (List.Mem.head _)
    have hX : PrfH (Formula.eq (.var 0) zero :: [lt (.var 0) (lenc (cons a nil))])
        (Formula.eq (nthc (cons a nil) (.var 0)) a) :=
      PrfH_eq_trans (PrfH_congr_nthc_idx (w := cons a nil) hi)
        (prf_to_prfH (prf_nthc_zero a nil) _)
    exact PrfH_congr_In_fst (PrfH_eq_symm hX) (prf_to_prfH h _)

/-- `S(0)` — codigo de termino con lista de argumentos `[Xz]`, NO vacia. -/
def Sz : Term := funcc (strCode "S") (cons Xz nil)
def w2 : Term := cons Xz (cons Sz nil)

theorem lift_Xz : liftTerm 0 Xz = Xz := by
  simp only [Xz, funcc, cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_strCode]

theorem lift_w2 : liftTerm 0 w2 = w2 := by
  simp only [w2, Sz, Xz, funcc, cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_strCode]

theorem lift_lenc_w2 : liftTerm 0 (lenc w2) = lenc w2 := by
  simp only [lenc, w2, Sz, Xz, funcc, cons, nil, zero, succ, liftTerm, liftTerms,
    liftTerm_strCode]

theorem prf_nthc_Sz_1 : Prf (nthc Sz (numeralM 1) =eq strCode "S") :=
  prf_nthc_c1 (succ zero) (strCode "S") (cons (cons Xz nil) nil)

theorem prf_nthc_Sz_2 : Prf (nthc Sz (numeralM 2) =eq cons Xz nil) :=
  prf_nthc_c2 (succ zero) (strCode "S") (cons Xz nil) nil

theorem prf_shapeBin_Sz : Prf (shapeBin Sz 1) := by
  refine prf_eq_symm ?_
  exact prf_congr_cons_tail (prf_eq_trans (prf_congr_cons_head prf_nthc_Sz_1)
    (prf_congr_cons_tail (prf_congr_cons_head prf_nthc_Sz_2)))

/-- El nodo `S(0)` pasa por la rama `funcc` **con `argsIn` NO VACUO**. -/
theorem prf_isTermCodeE1_Sz : Prf (isTermCodeE1 w2 Sz) := by
  refine prf_mp (prf_lorR _ _) (prf_and_intro prf_shapeBin_Sz ?_)
  have hargs : Prf (argsIn w2 (cons Xz nil)) :=
    prf_argsIn_singleton w2 Xz lift_w2 lift_Xz (prf_in_cons_head Xz (cons Sz nil))
  exact prfH_nil_to_prf (PrfH_congr_argsIn_snd (prf_to_prfH (prf_eq_symm prf_nthc_Sz_2) [])
    (prf_to_prfH hargs [])) rfl

theorem prf_wfAll1_w2 : Prf (wfAll1 w2) := by
  refine Prf.gen _ ?_
  unfold wfAll1Body
  rw [lift_w2, lift_lenc_w2]
  refine prf_deduction ?_
  have hlen : Prf (lenc w2 =eq numeralM 2) := prf_lenc_c2 Xz Sz
  have hlt2 : PrfH [lt (.var 0) (lenc w2)] (lt (.var 0) (succ (succ zero))) :=
    ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2 (prf_to_prfH hlen _) (prfH_hyp_self _)
  have hs1 : PrfH [lt (.var 0) (lenc w2)]
      (lor (lt (.var 0) (succ zero)) (Formula.eq (.var 0) (succ zero))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_lt_succ_split (.var 0) (succ zero)) _) hlt2
  refine PrfH_or_elim hs1 ?caseA ?caseB
  case caseA =>
    have h1 : PrfH (lt (.var 0) (succ zero) :: [lt (.var 0) (lenc w2)])
        (lt (.var 0) (succ zero)) := PrfH.hyp _ _ (List.Mem.head _)
    have hs2 : PrfH (lt (.var 0) (succ zero) :: [lt (.var 0) (lenc w2)])
        (lor (lt (.var 0) zero) (Formula.eq (.var 0) zero)) :=
      PrfH.mp _ _ _ (prf_to_prfH (prf_lt_succ_split (.var 0) zero) _) h1
    refine PrfH_or_elim hs2 ?_ ?_
    · exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prfᵢ.efq _))
        (PrfH.mp _ _ _ (prf_to_prfH (prf_not_lt_zero (.var 0)) _)
          (PrfH.hyp _ _ (List.Mem.head _)))
    · have hi : PrfH (Formula.eq (.var 0) zero :: lt (.var 0) (succ zero)
            :: [lt (.var 0) (lenc w2)]) (Formula.eq (.var 0) zero) :=
        PrfH.hyp _ _ (List.Mem.head _)
      have hX : PrfH (Formula.eq (.var 0) zero :: lt (.var 0) (succ zero)
            :: [lt (.var 0) (lenc w2)]) (Formula.eq (nthc w2 (.var 0)) Xz) :=
        PrfH_eq_trans (PrfH_congr_nthc_idx (w := w2) hi)
          (prf_to_prfH (prf_nthc_zero Xz (cons Sz nil)) _)
      exact PrfH_congr_isTermCodeE1 (PrfH_eq_symm hX)
        (prf_to_prfH (prf_isTermCodeE1_Xz w2) _)
  case caseB =>
    have hi : PrfH (Formula.eq (.var 0) (succ zero) :: [lt (.var 0) (lenc w2)])
        (Formula.eq (.var 0) (succ zero)) := PrfH.hyp _ _ (List.Mem.head _)
    have hX : PrfH (Formula.eq (.var 0) (succ zero) :: [lt (.var 0) (lenc w2)])
        (Formula.eq (nthc w2 (.var 0)) Sz) :=
      PrfH_eq_trans (PrfH_congr_nthc_idx (w := w2) hi)
        (prf_to_prfH (prf_nthc_c1 Xz Sz nil) _)
    exact PrfH_congr_isTermCodeE1 (PrfH_eq_symm hX)
      (prf_to_prfH prf_isTermCodeE1_Sz _)

theorem prf_isTC1_w2 : Prf (isTC1 w2 Sz) :=
  prf_and_intro prf_wfAll1_w2 (prf_in_cons_tail Xz (prf_in_cons_head Sz nil))

/-- **CRIT-A**: instancia cerrada extremo a extremo con el forall INTERNO **NO VACUO**. -/
theorem crit_pcc_isTC1_w2 : Prf (provFromCode (isTC1Dot w2 Sz)) :=
  prf_mp (pcc_isTC1_tracked w2 Sz) prf_isTC1_w2

/-! ## 14 · CRIT-B — LA DISCRIMINACION (copia de `sondeos/ClausuraLiftSinWTs.lean` §2,
    aplicada al antecedente REAL del reflector, `isTermCodeE1`). -/

theorem crit_num_ne : ∀ (m n : Nat), m ≠ n →
    Prf (Formula.impl (Formula.eq (numeralM m) (numeralM n)) Formula.bottom)
  | 0,     0,     h => absurd rfl h
  | 0,     _ + 1, _ =>
      prf_deduction (PrfH.mp _ _ _ (prf_to_prfH (prf_succ_ne_zero (numeralM _)) _)
        (PrfH_eq_symm (prfH_hyp_self _)))
  | m + 1, 0,     _ => prf_succ_ne_zero (numeralM m)
  | m + 1, n + 1, h =>
      impT (prf_succ_inj (numeralM m) (numeralM n)) (crit_num_ne m n (fun e => h (by omega)))

theorem crit_tag_absurd (X : Term) (k m : Nat) (hkm : k ≠ m)
    (hX : Prf (carc X =eq numeralM k)) :
    Prf (Formula.impl (Formula.eq (carc X) (numeralM m)) Formula.bottom) :=
  prf_deduction (PrfH.mp _ _ _ (prf_to_prfH (crit_num_ne k m hkm) _)
    (PrfH_eq_trans (prf_to_prfH (prf_eq_symm hX) _) (prfH_hyp_self _)))

theorem crit_cOk2_absurd (X : Term) (k m : Nat) (hkm : k ≠ m)
    (hX : Prf (carc X =eq numeralM k)) (G : Formula) :
    Prf (Formula.impl (cOk X (land (Formula.eq (carc X) (numeralM m)) G)) Formula.bottom) :=
  prf_deduction (PrfH.mp _ _ _ (prf_to_prfH (crit_tag_absurd X k m hkm hX) _)
    (PrfH_and_elim_left (PrfH_and_elim_right (prfH_hyp_self _))))

theorem crit_cOk3_absurd (X : Term) (k m : Nat) (hkm : k ≠ m)
    (hX : Prf (carc X =eq numeralM k)) (G H : Formula) :
    Prf (Formula.impl (cOk X (land (land (Formula.eq (carc X) (numeralM m)) G) H))
      Formula.bottom) :=
  prf_deduction (PrfH.mp _ _ _ (prf_to_prfH (crit_tag_absurd X k m hkm hX) _)
    (PrfH_and_elim_left (PrfH_and_elim_left (PrfH_and_elim_right (prfH_hyp_self _)))))

theorem crit_isTermCodeB1_rejects (wT X : Term) (k : Nat) (hk0 : k ≠ 0) (hk1 : k ≠ 1)
    (hX : Prf (carc X =eq numeralM k)) :
    Prf (Formula.impl (isTermCodeB1 wT X) Formula.bottom) :=
  prf_or_elim_imp
    (crit_cOk2_absurd X k 0 hk0 hX (Formula.eq (lenc X) (numeralM 2)))
    (crit_cOk3_absurd X k 1 hk1 hX (Formula.eq (lenc X) (numeralM 3))
      (argsIn wT (nthc X (numeralM 2))))

/-- **CRIT-B**: el antecedente REAL (`isTermCodeE1`, forma ecuacional) sigue RECHAZANDO
    todo codigo de FORMULA. -/
theorem crit_isTermCodeE1_rejects (wT X : Term) (k : Nat) (hk0 : k ≠ 0) (hk1 : k ≠ 1)
    (hX : Prf (carc X =eq numeralM k)) :
    Prf (Formula.impl (isTermCodeE1 wT X) Formula.bottom) :=
  impT (prf_isTermCodeE1_str wT X) (crit_isTermCodeB1_rejects wT X k hk0 hk1 hX)

theorem crit_E1_rejects_atomc (wT p ts : Term) :
    Prf (Formula.impl (isTermCodeE1 wT (atomc p ts)) Formula.bottom) :=
  crit_isTermCodeE1_rejects wT (atomc p ts) 3 (by decide) (by decide) (prf_carc_cons _ _)

theorem crit_E1_rejects_eqc (wT a b : Term) :
    Prf (Formula.impl (isTermCodeE1 wT (eqc a b)) Formula.bottom) :=
  crit_isTermCodeE1_rejects wT (eqc a b) 4 (by decide) (by decide) (prf_carc_cons _ _)

theorem crit_E1_rejects_implc (wT a b : Term) :
    Prf (Formula.impl (isTermCodeE1 wT (implc a b)) Formula.bottom) :=
  crit_isTermCodeE1_rejects wT (implc a b) 5 (by decide) (by decide) (prf_carc_cons _ _)

theorem crit_E1_rejects_forallc (wT a : Term) :
    Prf (Formula.impl (isTermCodeE1 wT (forallc a)) Formula.bottom) :=
  crit_isTermCodeE1_rejects wT (forallc a) 6 (by decide) (by decide) (prf_carc_cons _ _)

end ReflAnidado

#check @ReflAnidado.crit_pcc_isTC1_w2
#check @ReflAnidado.crit_E1_rejects_atomc
#print axioms ReflAnidado.prf_argsIn_singleton
#print axioms ReflAnidado.prf_wfAll1_w2
#print axioms ReflAnidado.crit_pcc_isTC1_w2
#print axioms ReflAnidado.crit_E1_rejects_atomc
#print axioms ReflAnidado.crit_E1_rejects_forallc

namespace ReflAnidadoCritC
open ReflAnidado

/-! ## 15 · CRIT-C — CERTIFICADO MECANICO de la ESTRUCTURA ANIDADA y del CODIGO De BRUIJN.

    El agente dice que el corrector De Bruijn «hay que leerlo por inspeccion de la definicion,
    no esta certificado por un teorema aparte». Aqui SI se certifica: por `rfl`, la imagen
    punteada es LITERALMENTE un `forallc` DENTRO de un `forallc`, con el hueco en `varc 0` en la
    vista externa y en `varc 1` en la interna, tal y como se afirma. Si el `forall` anidado
    hubiera sido aplanado o el codigo De Bruijn fuera otro, este `rfl` NO cerraria. -/

theorem crit_wfAllB1Dot_es_forall_anidado (w : Term) :
    wfAllB1Dot w
      = forallc (implc (ltCodeFn (varc (numeral 0)) (tcFn (lenc w)))
          (orc
            -- vista de NIVEL 0: el hueco externo es `varc 0`
            (andc (eqCodeFn (carcT (nthcT (tcFn w) (varc (numeral 0)))) (tcFn (numeralM 0)))
                  (eqCodeFn (lencT (nthcT (tcFn w) (varc (numeral 0)))) (tcFn (numeralM 2))))
            (andc
              (andc (eqCodeFn (carcT (nthcT (tcFn w) (varc (numeral 0)))) (tcFn (numeralM 1)))
                    (eqCodeFn (lencT (nthcT (tcFn w) (varc (numeral 0)))) (tcFn (numeralM 3))))
              -- ***EL SEGUNDO `forallc`, DENTRO DEL PRIMERO***
              (forallc (implc
                (ltCodeFn (varc (numeral 0))
                  -- la cota vive DENTRO del binder interno: hueco externo desplazado a `varc 1`
                  (lencT (nthcT (nthcT (tcFn w) (varc (numeral 1))) (tcFn (numeralM 2)))))
                (inFormCodeFn
                  (nthcT (nthcT (nthcT (tcFn w) (varc (numeral 1))) (tcFn (numeralM 2)))
                         (varc (numeral 0)))
                  (tcFn w))))))) := rfl

/-- Y el reconocedor entero lleva ese `forallc` anidado dentro de su primer conyunto. -/
theorem crit_isTC1Dot_shape (w c : Term) :
    isTC1Dot w c = andc (wfAllB1Dot w) (inFormCodeFn (tcFn c) (tcFn w)) := rfl

end ReflAnidadoCritC

#print axioms ReflAnidadoCritC.crit_wfAllB1Dot_es_forall_anidado
