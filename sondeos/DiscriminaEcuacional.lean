/-
# ✅ PILOTO POSITIVO — la PARTICIÓN EN TRES sale por TESTIGO, y sale COMPLETA

Fichero AUTOCONTENIDO (`import ROBINSON_PlusPlus.Meta` y nada más).

    lake env lean Probe/PilotoParticion.lean      (0 errores, 0 warnings, 0 sorry)

## Qué se pedía y qué salió

Se pedía el **par mutuo de términos** (`isTermCodeB` / `isTermsCodeB`) por la vía (2)
(testigo de parseo, CERO axiomas objeto nuevos), porque `sondeos/SubCodesCritica.lean`
compiló `prf_isFC_junk` y dejó viva R‑6: `nodeOk` FUSIONA las formas de código de FÓRMULA
(tags 2..9) con las de TÉRMINO (tags 0,1), así que la inducción interna de
`pcc_eval_substfc` se atasca.

Salió el par **y además el tercer predicado**, con reflector y testigo:

| pieza | enunciado | footprint |
|---|---|---|
| `prf_isTCB_subCodesT` | hito (i) del par, términos | net‑0 |
| `prf_isTsCB_subCodesTs` | hito (i) del par, listas | net‑0 |
| `pcc_isTCB_tracked` | reflector del par, `p` y `c` ABSTRACTOS | + `prf_axiomsCodeT_eq` |
| `pcc_isFormCodeB_pure` | los 8 disyuntos de FÓRMULA | + `prf_axiomsCodeT_eq` |
| `pcc_wfAllF_tracked` | reflector de la familia F, genérico en el accesor | + `prf_axiomsCodeT_eq` |
| **`pcc_isFCB3_tracked`** | **reflector de la PARTICIÓN COMPLETA** (3 predicados, 3 listas) | + `prf_axiomsCodeT_eq` |
| **`prf_isFCB3_fcodes`** | **hito (i) de la terna**: toda `φ` tiene testigo TIPADO | **net‑0** |
| `pcc_isFCB3_fcodes` | la composición: `⊢ Prov(⌜isFCB3(terna φ, ⌜φ⌝)⌝)` | + `prf_axiomsCodeT_eq` |

`prf_axiomsCodeT_eq` es la base ya sancionada; aparece sólo donde interviene `provFromCode`.

## Los tres hallazgos estructurales

1. **La mutualidad obliga a EMPAQUETAR los testigos en UN término.**
   `pcc_bdAll_intro` toma `CF : Term → Formula`, `bndF PsiF : Term → Term` y pide
   naturalidad en **un solo** término. Dejar la segunda lista como parámetro libre
   abstracto ROMPE `hCl` (`liftFormula k (wfAllT q wTs) = wfAllT (liftTerm k q) wTs` es
   FALSO para `wTs` no cerrado). ⇒ `p := cons wT wTs`, y se proyecta con `carc`/`cdrc`
   **a nivel META** — nunca dentro de `Prov`, así que no hace falta `pcc_eval_carc`
   sobre `p` y no reaparece la enmienda R‑A3‑1 a este nivel.

2. **La mutualidad NO se propaga al reflector.** Cada familia refleja su propio `wfAll`
   con su propio `pcc_bdAll_intro`; las listas cruzadas entran sólo como ÁTOMOS `In`, y
   `pcc_In_atom_tracked` ya tenía la lista como parámetro LIBRE. Coste de la mutualidad
   en el reflector: **cero**. No hay recursión mutua a nivel de `Prov`.

3. **Escribirlo GENÉRICO EN EL ACCESOR lo hace reutilizable de balde** (§17). Lo único
   que `pcc_bdAll_intro` pide de un accesor es `Nat1` (naturalidad en lift/subst).
   Con eso, pasar del paquete de DOS al de TRES **no cuesta ninguna prueba nueva**:
   `wfAllT = wfAllTgen carc cdrc` es `rfl` (§17 lo comprueba), y §18 recupera los
   reflectores del par en una línea cada uno.

## Diferencias declaradas respecto a `sondeos/A3IsFCBTracked.lean`

* `consOk` **caso a caso**, y el disyunto `X = nil` de `isTermsCodeB` va **DESNUDO**
  (lección de `sondeos/A3ConsOkRefuta.lean`). §19 lo comprueba: el testigo real de
  cualquier `φ` con símbolos contiene `nil = termsCodeM []`.
* `binOkF` admite **DOS listas distintas**, una por casilla (`eq t u` va contra `wT`,
  `impl a b` contra `wF`). El `binOk` de A3 no podía: sólo había UNA lista fusionada.
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

namespace PilotoParticion

/-! ## 0 · Combinadores lógicos (copia LITERAL de `sondeos/A3IsFCBTracked.lean` §0) -/

theorem impT {A B C : Formula} (h1 : Prf (A ⇒ B)) (h2 : Prf (B ⇒ C)) : Prf (A ⇒ C) := by
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH h2 _) (PrfH.mp _ _ _ (prf_to_prfH h1 _) (prfH_hyp_self _))

theorem prf_or_elim_imp {A B C : Formula} (h1 : Prf (A ⇒ C)) (h2 : Prf (B ⇒ C)) :
    Prf (lor A B ⇒ C) := by
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _
    (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.j3 A B C)) (prfH_hyp_self _))
    (prf_to_prfH h1 _)) (prf_to_prfH h2 _)

theorem prf_orL_imp (Ac Bc : Term) : Prf (provFromCode Ac ⇒ provFromCode (orc Ac Bc)) :=
  prf_mp (pcc_mp_code_open Ac (orc Ac Bc)) (pcc_j1_code Ac Bc)

theorem prf_orR_imp (Ac Bc : Term) : Prf (provFromCode Bc ⇒ provFromCode (orc Ac Bc)) :=
  prf_mp (pcc_mp_code_open Bc (orc Ac Bc)) (pcc_j2_code Ac Bc)

theorem prf_orL {A B : Formula} (h : Prf A) : Prf (lor A B) :=
  prf_mp (Prf.incl (Prf₀.j1 A B)) h

theorem prf_orR {A B : Formula} (h : Prf B) : Prf (lor A B) :=
  prf_mp (Prf.incl (Prf₀.j2 A B)) h

/-! ## 1 · EL PAR OBJETO — vocabulario EXISTENTE, cero axiomas

    ⚠️ `consOk` **CASO A CASO** (lección de `sondeos/A3ConsOkRefuta.lean`): el disyunto
    `X = nil` de `isTermsCodeB` va **DESNUDO**. Ponerlo global mataría el testigo real,
    porque `termsCodeM [] = nil` es un nodo obligatorio de toda lista de argumentos. -/

def consOk (X : Term) : Formula := Formula.eq X (cons (carc X) (cdrc X))

def cOk (X : Term) (F : Formula) : Formula := land (consOk X) F

/-- tag 0 (`varc`): `lenc = 2` y la casilla 1 es un NUMERAL — **sin pertenencia**. -/
def varOkT (X : Term) : Formula :=
  land (Formula.eq (carc X) (numeralM 0)) (Formula.eq (lenc X) (numeralM 2))

/-- tag 1 (`funcc`): `lenc = 3`, casilla 1 OPACA (cadena), casilla 2 **en `wTs`**. -/
def funcOkT (wTs X : Term) : Formula :=
  land (land (Formula.eq (carc X) (numeralM 1)) (Formula.eq (lenc X) (numeralM 3)))
       (In (nthc X (numeralM 2)) wTs)

/-- `X` es código de TÉRMINO. Consulta **`wTs`** (mutualidad). -/
def isTermCodeB (wT wTs X : Term) : Formula :=
  lor (cOk X (varOkT X)) (cOk X (funcOkT wTs X))

/-- `X` es código de LISTA DE TÉRMINOS. Consulta **`wT`** (mutualidad) y `wTs`. -/
def isTermsCodeB (wT wTs X : Term) : Formula :=
  lor (Formula.eq X nil)
      (cOk X (land (In (carc X) wT) (In (cdrc X) wTs)))

/-! ### El EMPAQUETADO — la única concesión estructural que impone la mutualidad

    `pcc_bdAll_intro` toma `CF : Term → Formula`, `bndF PsiF : Term → Term` y pide
    NATURALIDAD en **un solo** término (`hCl/hCs/hbl/hbs/hPl/hPs`). Con **dos** listas
    testigo, dejar la segunda como parámetro libre abstracto ROMPE esas hipótesis
    (`liftFormula k (wfAllT q wTs) = wfAllT (liftTerm k q) wTs` es FALSO si `wTs` no es
    cerrado). ⇒ hay que empaquetar el par en **un** término `p := cons wT wTs` y
    proyectar con `carc`/`cdrc` **a nivel META** (nunca dentro de `Prov`). -/

def bndT  (p : Term) : Term := lenc (carc p)
def bndTs (p : Term) : Term := lenc (cdrc p)

def wfAllT (p : Term) : Formula :=
  Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (bndT p)))
    (isTermCodeB (liftTerm 0 (carc p)) (liftTerm 0 (cdrc p))
      (nthc (liftTerm 0 (carc p)) (.var 0))))

def wfAllTs (p : Term) : Formula :=
  Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (bndTs p)))
    (isTermsCodeB (liftTerm 0 (carc p)) (liftTerm 0 (cdrc p))
      (nthc (liftTerm 0 (cdrc p)) (.var 0))))

def pairOk (p : Term) : Formula := land (wfAllT p) (wfAllTs p)

/-- `p` es un par de testigos VÁLIDO y `c` está en la mitad de TÉRMINOS. -/
def isTCB (p c : Term) : Formula := land (pairOk p) (In c (carc p))

/-- Idem, con `c` en la mitad de LISTAS. -/
def isTsCB (p c : Term) : Formula := land (pairOk p) (In c (cdrc p))

/-! ## 2 · Congruencias objeto que hacen falta -/

theorem prf_cdrc_cons (h t : Term) : Prf (cdrc (cons h t) =eq t) := by
  have hax : Prf ax_cdrc := prf_ax (by simp [axioms])
  have hh := prf_spec (prf_spec hax h) t
  simp [substFormula, substTerm, substTerms, cdrc, cons, FOL.substTerm_liftTerm] at hh
  exact hh

theorem prf_consOk_cons (a b : Term) : Prf (consOk (cons a b)) :=
  prf_eq_trans (prf_congr_cons_head (prf_eq_symm (prf_carc_cons a b)))
    (prf_congr_cons_tail (prf_eq_symm (prf_cdrc_cons a b)))

theorem prf_congr_lenc {t₁ t₂ : Term} (h : Prf (t₁ =eq t₂)) : Prf (lenc t₁ =eq lenc t₂) := by
  let f : Formula := Formula.eq (lenc (liftTerm 0 t₁)) (lenc (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (lenc t₁) (lenc s) := by
    intro s
    simp only [f, lenc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact prfH_nil_to_prf
    ((hS t₂) ▸ PrfH_leibniz_subst (A := f) (prf_to_prfH h [])
      ((hS t₁) ▸ prf_to_prfH (prf_refl (lenc t₁)) [])) rfl

/-- Congruencia de `nthc` en la LISTA (1er argumento). -/
theorem prf_congr_nthc_lst {w₁ w₂ : Term} (i : Term) (h : Prf (w₁ =eq w₂)) :
    Prf (nthc w₁ i =eq nthc w₂ i) := by
  let f : Formula := Formula.eq (nthc (liftTerm 0 w₁) (liftTerm 0 i)) (nthc (.var 0) (liftTerm 0 i))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (nthc w₁ i) (nthc s i) := by
    intro s
    simp only [f, nthc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact prfH_nil_to_prf
    ((hS w₂) ▸ PrfH_leibniz_subst (A := f) (prf_to_prfH h [])
      ((hS w₁) ▸ prf_to_prfH (prf_refl (nthc w₁ i)) [])) rfl

/-- Leibniz en el 1er argumento de `In`. -/
theorem prf_congr_In_left {u v w : Term} (h : Prf (u =eq v)) (hin : Prf (In u w)) :
    Prf (In v w) := by
  let f : Formula := In (.var 0) (liftTerm 0 w)
  have hS : ∀ s : Term, substFormula 0 s f = In s w := by
    intro s
    simp only [f, In, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact prfH_nil_to_prf
    ((hS v) ▸ PrfH_leibniz_subst (A := f) (prf_to_prfH h []) ((hS u) ▸ prf_to_prfH hin [])) rfl

/-- Leibniz en el 2º argumento de `In` (**nuevo**: lo pide el empaquetado `carc p`/`cdrc p`). -/
theorem prf_congr_In_right {u w w' : Term} (h : Prf (w =eq w')) (hin : Prf (In u w)) :
    Prf (In u w') := by
  let f : Formula := In (liftTerm 0 u) (.var 0)
  have hS : ∀ s : Term, substFormula 0 s f = In u s := by
    intro s
    simp only [f, In, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact prfH_nil_to_prf
    ((hS w') ▸ PrfH_leibniz_subst (A := f) (prf_to_prfH h []) ((hS w) ▸ prf_to_prfH hin [])) rfl

/-- **UNA** Leibniz cubre los 2 disyuntos: el hueco `X` aparece 5 veces y se sustituyen todas. -/
theorem prf_congr_isTermCodeB {wT wTs X₁ X₂ : Term} (h : Prf (X₁ =eq X₂))
    (hN : Prf (isTermCodeB wT wTs X₁)) : Prf (isTermCodeB wT wTs X₂) := by
  let f : Formula := isTermCodeB (liftTerm 0 wT) (liftTerm 0 wTs) (.var 0)
  have hS : ∀ s : Term, substFormula 0 s f = isTermCodeB wT wTs s := by
    intro s
    simp only [f, isTermCodeB, cOk, consOk, varOkT, funcOkT, land, lor, In,
      carc, cdrc, lenc, nthc, cons, nil, zero, substFormula, substTerm, substTerms,
      FOL.substTerm_liftTerm, substTerm_numeralM, if_true]
  exact prfH_nil_to_prf
    ((hS X₂) ▸ PrfH_leibniz_subst (A := f) (prf_to_prfH h []) ((hS X₁) ▸ prf_to_prfH hN [])) rfl

theorem prf_congr_isTermsCodeB {wT wTs X₁ X₂ : Term} (h : Prf (X₁ =eq X₂))
    (hN : Prf (isTermsCodeB wT wTs X₁)) : Prf (isTermsCodeB wT wTs X₂) := by
  let f : Formula := isTermsCodeB (liftTerm 0 wT) (liftTerm 0 wTs) (.var 0)
  have hS : ∀ s : Term, substFormula 0 s f = isTermsCodeB wT wTs s := by
    intro s
    simp only [f, isTermsCodeB, cOk, consOk, land, lor, In,
      carc, cdrc, cons, nil, zero, substFormula, substTerm, substTerms,
      FOL.substTerm_liftTerm, if_true]
  exact prfH_nil_to_prf
    ((hS X₂) ▸ PrfH_leibniz_subst (A := f) (prf_to_prfH h []) ((hS X₁) ▸ prf_to_prfH hN [])) rfl

/-! ## 3 · `∀` acotado con cota ABSTRACTA igual a un numeral

    Generalización de `prf_bdAll_numeral` (`sondeos/ParseWitness.lean` §2): la cota es un
    término cerrado `b` con `⊢ b = n̄`. Lo pide el empaquetado, porque la cota real es
    `lenc (carc p)`, no `lenc (objList L)`. -/

theorem substTerm_numeralM' (v : Nat) (s : Term) : ∀ n : Nat,
    substTerm v s (numeralM n) = numeralM n
  | 0     => by simp only [numeralM, zero, substTerm, substTerms]
  | n + 1 => by
      simp only [numeralM, succ, substTerm, substTerms, substTerm_numeralM' v s n]

theorem prf_bdAll_numeral (Φ : Formula) (hΦ : substFormula 0 (.var 0) Φ = Φ) : ∀ (n : Nat),
    (∀ k : Nat, k < n → Prf (substFormula 0 (numeralM k) Φ)) →
      Prf (Formula.forall (Formula.impl (lt (.var 0) (numeralM n)) Φ))
  | 0, _ => by
      refine Prf.gen _ (prf_deduction ?_)
      exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.efq Φ))
        (PrfH.mp _ _ _ (prf_to_prfH (prf_not_lt_zero (.var 0)) _)
          (PrfH.hyp _ _ (List.Mem.head _)))
  | n + 1, h => by
      have ih := prf_bdAll_numeral Φ hΦ n (fun k hk => h k (Nat.lt_succ_of_lt hk))
      have hself : substFormula 0 (.var 0) (Formula.impl (lt (.var 0) (numeralM n)) Φ)
          = Formula.impl (lt (.var 0) (numeralM n)) Φ := by
        simp only [substFormula, lt, substTerm, substTerms, substTerm_numeralM, hΦ, if_true]
      refine Prf.gen _ (prf_deduction ?_)
      have hsplit : PrfH [lt (.var 0) (numeralM (n + 1))]
          (lor (lt (.var 0) (numeralM n)) (Formula.eq (.var 0) (numeralM n))) :=
        PrfH.mp _ _ _ (prf_to_prfH (prf_lt_succ_split (.var 0) (numeralM n)) _)
          (PrfH.hyp _ _ (List.Mem.head _))
      refine PrfH_or_elim hsplit ?brA ?brB
      case brA =>
        exact PrfH.mp _ _ _ (prf_to_prfH (hself ▸ prf_spec ih (.var 0)) _)
          (PrfH.hyp _ _ (List.Mem.head _))
      case brB =>
        have hinst : Prf (substFormula 0 (numeralM n) Φ) := h n (Nat.lt_succ_self n)
        have heq : PrfH (Formula.eq (.var 0) (numeralM n) :: [lt (.var 0) (numeralM (n + 1))])
            (Formula.eq (numeralM n) (.var 0)) :=
          PrfH_eq_symm (PrfH.hyp _ _ (List.Mem.head _))
        have := PrfH_leibniz_subst (A := Φ) heq (prf_to_prfH hinst _)
        rwa [hΦ] at this

/-- **NUEVO**: el `∀` acotado con cota `b` ABSTRACTA (pero `⊢ b = n̄`). -/
theorem prf_bdAll_of_bound (Φ : Formula) (b : Term) (n : Nat)
    (hΦ : substFormula 0 (.var 0) Φ = Φ)
    (hb : Prf (Formula.eq b (numeralM n)))
    (h : ∀ k : Nat, k < n → Prf (substFormula 0 (numeralM k) Φ)) :
    Prf (Formula.forall (Formula.impl (lt (.var 0) b) Φ)) := by
  have key : Prf (Formula.forall (Formula.impl (lt (.var 0) (numeralM n)) Φ)) :=
    prf_bdAll_numeral Φ hΦ n h
  have hself : substFormula 0 (.var 0) (Formula.impl (lt (.var 0) (numeralM n)) Φ)
      = Formula.impl (lt (.var 0) (numeralM n)) Φ := by
    simp only [substFormula, lt, substTerm, substTerms, substTerm_numeralM, hΦ, if_true]
  refine Prf.gen _ (prf_deduction ?_)
  exact PrfH.mp _ _ _ (prf_to_prfH (hself ▸ prf_spec key (.var 0)) _)
    (ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
      (prf_to_prfH hb _) (PrfH.hyp _ _ (List.Mem.head _)))

/-! ## 4 · Normalización de `substFormula` sobre el par -/

theorem substF_isTermCodeB (v : Nat) (s A B X : Term) :
    substFormula v s (isTermCodeB A B X)
      = isTermCodeB (substTerm v s A) (substTerm v s B) (substTerm v s X) := by
  simp only [isTermCodeB, cOk, consOk, varOkT, funcOkT, land, lor, In,
    carc, cdrc, lenc, nthc, cons, nil, zero, substFormula, substTerm, substTerms,
    substTerm_numeralM]

theorem substF_isTermsCodeB (v : Nat) (s A B X : Term) :
    substFormula v s (isTermsCodeB A B X)
      = isTermsCodeB (substTerm v s A) (substTerm v s B) (substTerm v s X) := by
  simp only [isTermsCodeB, cOk, consOk, land, lor, In,
    carc, cdrc, cons, nil, zero, substFormula, substTerm, substTerms]

/-- Forma normal de `wfAllT p` para `p` CERRADO. -/
theorem wfAllT_closed (p : Term) (hpl : liftTerm 0 p = p) :
    wfAllT p = Formula.forall (Formula.impl (lt (.var 0) (bndT p))
      (isTermCodeB (carc p) (cdrc p) (nthc (carc p) (.var 0)))) := by
  simp only [wfAllT, bndT, lenc, carc, cdrc, nthc, liftTerm, liftTerms, hpl]

theorem wfAllTs_closed (p : Term) (hpl : liftTerm 0 p = p) :
    wfAllTs p = Formula.forall (Formula.impl (lt (.var 0) (bndTs p))
      (isTermsCodeB (carc p) (cdrc p) (nthc (cdrc p) (.var 0)))) := by
  simp only [wfAllTs, bndTs, lenc, carc, cdrc, nthc, liftTerm, liftTerms, hpl]

/-- **El ensamblaje objeto del par**, con `p` CERRADO y las dos longitudes conocidas. -/
theorem prf_pairOk_gen (p : Term) (nA nB : Nat)
    (hps : ∀ (v : Nat) (s : Term), substTerm v s p = p)
    (hpl : ∀ c : Nat, liftTerm c p = p)
    (hlenA : Prf (Formula.eq (lenc (carc p)) (numeralM nA)))
    (hlenB : Prf (Formula.eq (lenc (cdrc p)) (numeralM nB)))
    (hnA : ∀ k : Nat, k < nA →
      Prf (isTermCodeB (carc p) (cdrc p) (nthc (carc p) (numeralM k))))
    (hnB : ∀ k : Nat, k < nB →
      Prf (isTermsCodeB (carc p) (cdrc p) (nthc (cdrc p) (numeralM k)))) :
    Prf (pairOk p) := by
  have hcA : ∀ (v : Nat) (s : Term), substTerm v s (carc p) = carc p := by
    intro v s; simp only [carc, substTerm, substTerms, hps]
  have hcB : ∀ (v : Nat) (s : Term), substTerm v s (cdrc p) = cdrc p := by
    intro v s; simp only [cdrc, substTerm, substTerms, hps]
  refine prf_and_intro ?_ ?_
  · rw [wfAllT_closed p (hpl 0)]
    refine prf_bdAll_of_bound _ (bndT p) nA ?_ hlenA ?_
    · simp only [substF_isTermCodeB, nthc, substTerm, substTerms, hcA, hcB, if_true]
    · intro k hk
      have := hnA k hk
      simpa only [substF_isTermCodeB, nthc, substTerm, substTerms, hcA, hcB,
        substTerm_numeralM, if_true, reduceIte] using this
  · rw [wfAllTs_closed p (hpl 0)]
    refine prf_bdAll_of_bound _ (bndTs p) nB ?_ hlenB ?_
    · simp only [substF_isTermsCodeB, nthc, substTerm, substTerms, hcA, hcB, if_true]
    · intro k hk
      have := hnB k hk
      simpa only [substF_isTermsCodeB, nthc, substTerm, substTerms, hcA, hcB,
        substTerm_numeralM, if_true, reduceIte] using this

/-! ## 5 · LA IMAGEN PUNTEADA del par

    Formulación **(d)** de A3: el `In` va como ÁTOMO (`inFormCodeFn`), no como su despliegue
    `∃`-acotado. ⇒ el cuerpo del `∀` acotado NO tiene binders y todo el descenso de `substfc`
    vive en NIVEL 0. -/

noncomputable def shapeDot (X : Term) (k n : Nat) : Term :=
  andc (eqCodeFn (carcT X) (tcFn (numeralM k))) (eqCodeFn (lencT X) (tcFn (numeralM n)))

noncomputable def varDotT (X : Term) : Term := shapeDot X 0 2

noncomputable def funcDotT (WTs X : Term) : Term :=
  andc (shapeDot X 1 3) (inFormCodeFn (nthcT X (tcFn (numeralM 2))) WTs)

noncomputable def isTermCodeDot (WT WTs X : Term) : Term :=
  orc (varDotT X) (funcDotT WTs X)

noncomputable def isTermsCodeDot (WT WTs X : Term) : Term :=
  orc (eqCodeFn X (tcFn nil))
      (andc (inFormCodeFn (carcT X) WT) (inFormCodeFn (cdrcT X) WTs))

/-- `PsiT p`: el cuerpo dotado de `wfAllT`, con el hueco `⌜v₀⌝` en el ÍNDICE. -/
noncomputable def PsiT (p : Term) : Term :=
  isTermCodeDot (tcFn (carc p)) (tcFn (cdrc p)) (nthcT (tcFn (carc p)) (varc (numeral 0)))

/-- `PsiTs p`: idem para `wfAllTs` — **indexa sobre la OTRA lista** (`cdrc p`). -/
noncomputable def PsiTs (p : Term) : Term :=
  isTermsCodeDot (tcFn (carc p)) (tcFn (cdrc p)) (nthcT (tcFn (cdrc p)) (varc (numeral 0)))

noncomputable def isTCBDot (p c : Term) : Term :=
  andc (andc (bdAllCode (tcFn (bndT p)) (PsiT p)) (bdAllCode (tcFn (bndTs p)) (PsiTs p)))
       (inFormCodeFn (tcFn c) (tcFn (carc p)))

noncomputable def isTsCBDot (p c : Term) : Term :=
  andc (andc (bdAllCode (tcFn (bndT p)) (PsiT p)) (bdAllCode (tcFn (bndTs p)) (PsiTs p)))
       (inFormCodeFn (tcFn c) (tcFn (cdrc p)))

/-! ## 6 · EL DESCENSO de `substfc zero s` (copia de A3 §3, recortada a 2+2 disyuntos) -/

theorem prf_substfc_inDot (s A A' W : Term)
    (hA : Prf (substtc zero s A =eq A')) (hW : ∀ V, Prf (substtc zero V W =eq W)) :
    Prf (substfc zero s (inFormCodeFn A W) =eq inFormCodeFn A' W) := by
  show Prf (substfc zero s (atomc (strCode in_sym) (cons A (cons W nil)))
    =eq atomc (strCode in_sym) (cons A' (cons W nil)))
  refine prf_eq_trans (prf_substfc_atom zero s (strCode in_sym) (cons A (cons W nil))) ?_
  refine prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head ?_))
  refine prf_eq_trans (prf_substtsc_cons zero s A (cons W nil)) ?_
  refine prf_eq_trans (prf_congr_cons_head hA) ?_
  refine prf_congr_cons_tail ?_
  exact prf_eq_trans (prf_substtsc_cons zero s W nil)
    (prf_eq_trans (prf_congr_cons_head (hW s)) (prf_congr_cons_tail (prf_substtsc_nil zero s)))

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

theorem prf_substtc_child (s X X' : Term) (k : Nat)
    (hX : Prf (substtc zero s X =eq X')) :
    Prf (substtc zero s (nthcT X (tcFn (numeralM k))) =eq nthcT X' (tcFn (numeralM k))) :=
  prf_eq_trans (prf_substtc_nthcT zero s X (tcFn (numeralM k)))
    (prf_congr_nthcT hX (substtc_inv_tcFn (numeralM k) s))

theorem prf_substfc_funcDotT (s WTs X X' : Term)
    (hW : ∀ V, Prf (substtc zero V WTs =eq WTs)) (hX : Prf (substtc zero s X =eq X')) :
    Prf (substfc zero s (funcDotT WTs X) =eq funcDotT WTs X') := by
  unfold funcDotT
  exact prf_eq_trans (prf_substfc_and zero s _ _)
    (prf_congr_andc (prf_substfc_shapeDot s X X' 1 3 hX)
      (prf_substfc_inDot s _ _ WTs (prf_substtc_child s X X' 2 hX) hW))

/-- **EL DESCENSO (términos)**: `substfc zero s` atraviesa los 2 disyuntos. -/
theorem prf_substfc_isTermCodeDot_gen (s WT WTs X X' : Term)
    (hWs : ∀ V, Prf (substtc zero V WTs =eq WTs)) (hX : Prf (substtc zero s X =eq X')) :
    Prf (substfc zero s (isTermCodeDot WT WTs X) =eq isTermCodeDot WT WTs X') := by
  unfold isTermCodeDot varDotT
  exact prf_eq_trans (prf_substfc_or zero s _ _)
    (prf_congr_orc (prf_substfc_shapeDot s X X' 0 2 hX)
      (prf_substfc_funcDotT s WTs X X' hWs hX))

/-- **EL DESCENSO (listas)**: aquí SÍ intervienen las DOS listas testigo. -/
theorem prf_substfc_isTermsCodeDot_gen (s WT WTs X X' : Term)
    (hWT : ∀ V, Prf (substtc zero V WT =eq WT))
    (hWs : ∀ V, Prf (substtc zero V WTs =eq WTs)) (hX : Prf (substtc zero s X =eq X')) :
    Prf (substfc zero s (isTermsCodeDot WT WTs X) =eq isTermsCodeDot WT WTs X') := by
  unfold isTermsCodeDot
  refine prf_eq_trans (prf_substfc_or zero s _ _) (prf_congr_orc ?_ ?_)
  · exact prf_eq_trans (prf_substfc_eq zero s _ _)
      (prf_congr_eqCodeFn hX (substtc_inv_tcFn nil s))
  · refine prf_eq_trans (prf_substfc_and zero s _ _) (prf_congr_andc ?_ ?_)
    · exact prf_substfc_inDot s _ _ WT
        (prf_eq_trans (prf_substtc_carcT zero s X) (prf_congr_carcT hX)) hWT
    · exact prf_substfc_inDot s _ _ WTs
        (prf_eq_trans (prf_substtc_cdrcT zero s X) (prf_congr_cdrcT hX)) hWs

theorem prf_substfc_PsiT (p s : Term) :
    Prf (substfc zero s (PsiT p)
      =eq isTermCodeDot (tcFn (carc p)) (tcFn (cdrc p)) (nthcT (tcFn (carc p)) s)) :=
  prf_substfc_isTermCodeDot_gen s _ _ _ _ (substtc_inv_tcFn (cdrc p))
    (prf_eq_trans (prf_substtc_nthcT zero s (tcFn (carc p)) (varc (numeral 0)))
      (prf_congr_nthcT (substtc_inv_tcFn (carc p) s) (prf_substtc_varc0 s)))

theorem prf_substfc_PsiTs (p s : Term) :
    Prf (substfc zero s (PsiTs p)
      =eq isTermsCodeDot (tcFn (carc p)) (tcFn (cdrc p)) (nthcT (tcFn (cdrc p)) s)) :=
  prf_substfc_isTermsCodeDot_gen s _ _ _ _ (substtc_inv_tcFn (carc p)) (substtc_inv_tcFn (cdrc p))
    (prf_eq_trans (prf_substtc_nthcT zero s (tcFn (cdrc p)) (varc (numeral 0)))
      (prf_congr_nthcT (substtc_inv_tcFn (cdrc p) s) (prf_substtc_varc0 s)))

/-! ## 7 · El reflector del ÁTOMO `In` — copia LITERAL de `sondeos/A3IsFCBTracked.lean` §4 -/

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

theorem prf_substtc_varc0_at1 (V : Term) :
    Prf (substtc (succ zero) V (varc (numeral 0)) =eq varc (numeral 0)) :=
  prf_mp (prf_substtc_var_lt (succ zero) V (numeral 0)) (prf_gnum_lt (by omega : 0 < 1))

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
      · show Prf (substfc (succ zero) (liftc zero B)
            (atomc (strCode lt_sym) (cons (varc (numeral 0)) (cons (lencT (varc (numeral 1))) nil)))
          =eq atomc (strCode lt_sym) (cons (varc (numeral 0)) (cons (bdInB w) nil)))
        refine prf_eq_trans (prf_substfc_atom (succ zero) (liftc zero B) (strCode lt_sym) _) ?_
        refine prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head ?_))
        have hlen : Prf (substtc (succ zero) (liftc zero B) (lencT (varc (numeral 1)))
            =eq bdInB w) :=
          prf_eq_trans (prf_substtc_lencT (succ zero) (liftc zero B) (varc (numeral 1)))
            (prf_congr_lencT (hv1 (liftc zero B)))
        refine prf_eq_trans (prf_substtsc_cons (succ zero) (liftc zero B) _ _) ?_
        refine prf_eq_trans (prf_congr_cons_head (prf_substtc_varc0_at1 (liftc zero B))) ?_
        refine prf_congr_cons_tail ?_
        exact prf_eq_trans (prf_substtsc_cons (succ zero) (liftc zero B) _ _)
          (prf_eq_trans (prf_congr_cons_head hlen)
            (prf_congr_cons_tail (prf_substtsc_nil (succ zero) (liftc zero B))))
      · refine prf_eq_trans (prf_substfc_eq (succ zero) (liftc zero B) _ _)
          (prf_congr_eqCodeFn ?_ (hWnorm (liftc zero B)))
        exact prf_eq_trans (prf_substtc_nthcT (succ zero) (liftc zero B) _ _)
          (prf_congr_nthcT (hv1 (liftc zero B)) (prf_substtc_varc0_at1 (liftc zero B)))
    · show Prf (substfc zero B (atomc (strCode in_sym) (cons W (cons (varc (numeral 0)) nil)))
        =eq atomc (strCode in_sym) (cons A (cons B nil)))
      refine prf_eq_trans (prf_substfc_atom zero B (strCode in_sym) _) ?_
      refine prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head ?_))
      refine prf_eq_trans (prf_substtsc_cons zero B W (cons (varc (numeral 0)) nil)) ?_
      refine prf_eq_trans (prf_congr_cons_head
        (prf_eq_trans (substtc_inv_liftc_tcFn x B) (prf_liftc_tcFn x))) ?_
      refine prf_congr_cons_tail ?_
      exact prf_eq_trans (prf_substtsc_cons zero B (varc (numeral 0)) nil)
        (prf_eq_trans (prf_congr_cons_head (prf_substtc_varc0 B))
          (prf_congr_cons_tail (prf_substtsc_nil zero B)))
  exact prf_mp (prf_provCode_congr hout) h1

/-- **Reflexión del `In` como ÁTOMO**, con `x` y `w` ABSTRACTOS.
    ⚠️ Esta pieza acepta la lista testigo como parámetro LIBRE ⇒ se reusa TAL CUAL para
    las DOS listas del par. La mutualidad no cuesta nada aquí. -/
theorem pcc_In_atom_tracked (x w : Term) :
    Prf (In x w ⇒ provFromCode (inFormCodeFn (tcFn x) (tcFn w))) := by
  refine prf_deduction ?_
  have hbd : PrfH [In x w] (boundedIn x w) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_and_elim_left (prf_In_iff_boundedIn x w)) _)
      (prfH_hyp_self _)
  have h1 : PrfH [In x w] (provFromCode (bdInDot x w)) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_boundedIn_tracked x w) _) hbd
  exact PrfH_mp_code_apply (prf_to_prfH (pcc_InBwd_computed x w) _) h1

/-! ## 8 · Puentes `carcT`/`cdrcT` desgatillados por `consOk`, y transporte en `In`
       (copia de `sondeos/A3IsFCBTracked.lean` §5) -/

theorem PrfH_congr_cdrcT {Γ : List Formula} {x y : Term} (h : PrfH Γ (x =eq y)) :
    PrfH Γ (cdrcT x =eq cdrcT y) := by
  unfold cdrcT funcc
  exact PrfH_congr_cons_tail (PrfH_congr_cons_tail (PrfH_congr_cons_head (PrfH_congr_cons_head h)))

theorem pcc_carcD_bridge_cons (X : Term) :
    Prf (consOk X ⇒ provFromCode (eqCodeFn (carcT (tcFn X)) (tcFn (carc X)))) := by
  refine prf_deduction ?_
  have hcons := prfH_hyp_self (consOk X)
  exact PrfH_provCode_congr
    (PrfH_congr_eqCodeFn (PrfH_congr_carcT (PrfH_congr_tcFn (PrfH_eq_symm hcons)))
      (prf_to_prfH (prf_refl _) _))
    (prf_to_prfH (pcc_eval_carc (carc X) (cdrc X)) _)

theorem pcc_cdrcD_bridge_cons (X : Term) :
    Prf (consOk X ⇒ provFromCode (eqCodeFn (cdrcT (tcFn X)) (tcFn (cdrc X)))) := by
  refine prf_deduction ?_
  have hcons := prfH_hyp_self (consOk X)
  exact PrfH_provCode_congr
    (PrfH_congr_eqCodeFn (PrfH_congr_cdrcT (PrfH_congr_tcFn (PrfH_eq_symm hcons)))
      (prf_to_prfH (prf_refl _) _))
    (prf_to_prfH (pcc_eval_cdrc (carc X) (cdrc X)) _)

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

/-! ## 9 · Los CUATRO disyuntos (2 + 2) — copia de A3 §6 con `q` libre -/

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

theorem pcc_child_tracked (q X : Term) (j n : Nat) (hjn : j < n) :
    Prf (Formula.eq (lenc X) (numeralM n) ⇒ (In (nthc X (numeralM j)) q ⇒
      provFromCode (inFormCodeFn (nthcT (tcFn X) (tcFn (numeralM j))) (tcFn q)))) := by
  refine prf_deduction (deduction_aux ?_ (In (nthc X (numeralM j)) q)
    [Formula.eq (lenc X) (numeralM n)] rfl)
  have hin : PrfH [In (nthc X (numeralM j)) q, Formula.eq (lenc X) (numeralM n)]
      (In (nthc X (numeralM j)) q) := PrfH.hyp _ _ (List.Mem.head _)
  have hlen : PrfH [In (nthc X (numeralM j)) q, Formula.eq (lenc X) (numeralM n)]
      (Formula.eq (lenc X) (numeralM n)) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hlt : PrfH _ (lt (numeralM j) (lenc X)) :=
    ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2 (PrfH_eq_symm hlen)
      (prf_to_prfH (prf_lt_numeralM hjn) _)
  have hev : PrfH _ (provFromCode (eqCodeFn (nthcT (tcFn X) (tcFn (numeralM j)))
      (tcFn (nthc X (numeralM j))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_nthc X (numeralM j)) _) hlt
  have hevS : PrfH _ (provFromCode (eqCodeFn (tcFn (nthc X (numeralM j)))
      (nthcT (tcFn X) (tcFn (numeralM j))))) :=
    PrfH_eq_symm_code _ _
      (substtc_inv_nthcT (substtc_inv_tcFn X) (substtc_inv_tcFn (numeralM j))) hev
  have hat : PrfH _ (provFromCode (inFormCodeFn (tcFn (nthc X (numeralM j))) (tcFn q))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_In_atom_tracked (nthc X (numeralM j)) q) _) hin
  exact PrfH_in_transport _ _ _ (substtc_inv_tcFn q) hevS hat

theorem pcc_carcIn_tracked (q X : Term) :
    Prf (consOk X ⇒ (In (carc X) q ⇒
      provFromCode (inFormCodeFn (carcT (tcFn X)) (tcFn q)))) := by
  refine prf_deduction (deduction_aux ?_ (In (carc X) q) [consOk X] rfl)
  have hin : PrfH [In (carc X) q, consOk X] (In (carc X) q) := PrfH.hyp _ _ (List.Mem.head _)
  have hcons : PrfH [In (carc X) q, consOk X] (consOk X) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hbr := PrfH.mp _ _ _ (prf_to_prfH (pcc_carcD_bridge_cons X) _) hcons
  have hbrS : PrfH _ (provFromCode (eqCodeFn (tcFn (carc X)) (carcT (tcFn X)))) :=
    PrfH_eq_symm_code _ _ (substtc_inv_carcT (substtc_inv_tcFn X)) hbr
  have hat : PrfH _ (provFromCode (inFormCodeFn (tcFn (carc X)) (tcFn q))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_In_atom_tracked (carc X) q) _) hin
  exact PrfH_in_transport _ _ _ (substtc_inv_tcFn q) hbrS hat

theorem pcc_cdrcIn_tracked (q X : Term) :
    Prf (consOk X ⇒ (In (cdrc X) q ⇒
      provFromCode (inFormCodeFn (cdrcT (tcFn X)) (tcFn q)))) := by
  refine prf_deduction (deduction_aux ?_ (In (cdrc X) q) [consOk X] rfl)
  have hin : PrfH [In (cdrc X) q, consOk X] (In (cdrc X) q) := PrfH.hyp _ _ (List.Mem.head _)
  have hcons : PrfH [In (cdrc X) q, consOk X] (consOk X) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hbr := PrfH.mp _ _ _ (prf_to_prfH (pcc_cdrcD_bridge_cons X) _) hcons
  have hbrS : PrfH _ (provFromCode (eqCodeFn (tcFn (cdrc X)) (cdrcT (tcFn X)))) :=
    PrfH_eq_symm_code _ _ (substtc_inv_cdrcT (substtc_inv_tcFn X)) hbr
  have hat : PrfH _ (provFromCode (inFormCodeFn (tcFn (cdrc X)) (tcFn q))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_In_atom_tracked (cdrc X) q) _) hin
  exact PrfH_in_transport _ _ _ (substtc_inv_tcFn q) hbrS hat

/-! ### Los cuatro moldes de disyunto -/

theorem pcc_varOkT_case (X : Term) :
    Prf (cOk X (varOkT X) ⇒ provFromCode (varDotT (tcFn X))) := by
  refine prf_deduction ?_
  have h := prfH_hyp_self (cOk X (varOkT X))
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (pcc_shape_tracked X 0 2) _)
    (PrfH_and_elim_left h)) (PrfH_and_elim_right h)

theorem pcc_funcOkT_case (q X : Term) :
    Prf (cOk X (funcOkT q X) ⇒ provFromCode (funcDotT (tcFn q) (tcFn X))) := by
  refine prf_deduction ?_
  have h := prfH_hyp_self (cOk X (funcOkT q X))
  have hcons := PrfH_and_elim_left h
  have hsb := PrfH_and_elim_right h
  have hsh := PrfH_and_elim_left hsb
  have hmem := PrfH_and_elim_right hsb
  have h1 := PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (pcc_shape_tracked X 1 3) _) hcons) hsh
  have h2 := PrfH.mp _ _ _ (PrfH.mp _ _ _
    (prf_to_prfH (pcc_child_tracked q X 2 3 (by omega)) _) (PrfH_and_elim_right hsh)) hmem
  exact PrfH_and_intro_code _ _ h1 h2

theorem pcc_nilCase (X : Term) :
    Prf (Formula.eq X nil ⇒ provFromCode (eqCodeFn (tcFn X) (tcFn nil))) :=
  pcc_eq_tracked X nil

/-- ⚠️ **Aquí vive toda la mutualidad**: `carc X` va contra `qT` y `cdrc X` contra `qTs`.
    `pcc_carcIn_tracked`/`pcc_cdrcIn_tracked` ya tenían la lista como parámetro LIBRE ⇒
    se instancian con listas DISTINTAS sin tocar una línea. -/
theorem pcc_consCase2 (qT qTs X : Term) :
    Prf (cOk X (land (In (carc X) qT) (In (cdrc X) qTs)) ⇒
      provFromCode (andc (inFormCodeFn (carcT (tcFn X)) (tcFn qT))
                         (inFormCodeFn (cdrcT (tcFn X)) (tcFn qTs)))) := by
  refine prf_deduction ?_
  have h := prfH_hyp_self (cOk X (land (In (carc X) qT) (In (cdrc X) qTs)))
  have hcons := PrfH_and_elim_left h
  have hmem := PrfH_and_elim_right h
  have h1 := PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (pcc_carcIn_tracked qT X) _) hcons)
    (PrfH_and_elim_left hmem)
  have h2 := PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (pcc_cdrcIn_tracked qTs X) _) hcons)
    (PrfH_and_elim_right hmem)
  exact PrfH_and_intro_code _ _ h1 h2

/-! ## 10 · Los dos reflectores PUROS del par -/

theorem pcc_isTermCodeB_pure (qT qTs X : Term) :
    Prf (isTermCodeB qT qTs X ⇒ provFromCode (isTermCodeDot (tcFn qT) (tcFn qTs) (tcFn X))) :=
  prf_or_elim_imp
    (impT (pcc_varOkT_case X) (prf_orL_imp (varDotT (tcFn X)) (funcDotT (tcFn qTs) (tcFn X))))
    (impT (pcc_funcOkT_case qTs X)
      (prf_orR_imp (varDotT (tcFn X)) (funcDotT (tcFn qTs) (tcFn X))))

theorem pcc_isTermsCodeB_pure (qT qTs X : Term) :
    Prf (isTermsCodeB qT qTs X ⇒ provFromCode (isTermsCodeDot (tcFn qT) (tcFn qTs) (tcFn X))) :=
  prf_or_elim_imp
    (impT (pcc_nilCase X) (prf_orL_imp (eqCodeFn (tcFn X) (tcFn nil)) _))
    (impT (pcc_consCase2 qT qTs X) (prf_orR_imp (eqCodeFn (tcFn X) (tcFn nil)) _))

/-! ## 11–12 · (VACÍO A PROPÓSITO) — los reflectores del par bajan a §18

    Las 8 obligaciones concretas de `pcc_bdAll_intro` para el par `(carc, cdrc)` **se han
    borrado de aquí**: §17 las prueba GENÉRICAS en el accesor y §18 las instancia en una
    línea. Ésa es la medición central del piloto — pasar de UN paquete de testigos a otro
    no cuesta ninguna prueba nueva, sólo cambiar `aT`/`aTs`. -/

/-! ## 13 · HITO (i) — EL TESTIGO. Dos listas, cuatro funciones, dos inducciones mutuas

    `subCodes` de `sondeos/SubCodesWitness.lean` producía **UNA** lista fusionada. Aquí hay
    que PARTIRLA: `tcodes⋆` recoge los códigos de TÉRMINO y `lcodes⋆` los de LISTA. Son dos
    bloques `mutual` de dos funciones cada uno (no cuatro mutuamente recursivas: el corte
    limpio es que la recursión de cada familia nunca llama a la otra — sólo la **hipótesis**
    de inclusión cruza). -/

mutual
def tcodesT : Term → List Term
  | .var n     => [termCodeM (.var n)]
  | .func s ts => termCodeM (.func s ts) :: tcodesTs ts
def tcodesTs : List Term → List Term
  | []      => []
  | t :: ts => tcodesT t ++ tcodesTs ts
end

mutual
def lcodesT : Term → List Term
  | .var _     => []
  | .func _ ts => lcodesTs ts
def lcodesTs : List Term → List Term
  | []      => [nil]
  | t :: ts => termsCodeM (t :: ts) :: (lcodesT t ++ lcodesTs ts)
end

theorem mem_self_tcodesT (t : Term) : List.Mem (termCodeM t) (tcodesT t) := by
  cases t with
  | var n     => simp only [tcodesT]; exact List.Mem.head _
  | func s ts => simp only [tcodesT]; exact List.Mem.head _

theorem mem_self_lcodesTs : ∀ ts : List Term, List.Mem (termsCodeM ts) (lcodesTs ts)
  | []     => by simp only [lcodesTs, termsCodeM]; exact List.Mem.head _
  | _ :: _ => by simp only [lcodesTs]; exact List.Mem.head _

/-! ### Clausura De Bruijn -/

def CodeClosed (x : Term) : Prop :=
  (∀ c : Nat, liftTerm c x = x) ∧ (∀ (v : Nat) (s : Term), substTerm v s x = x)

theorem closed_termCodeM (t : Term) : CodeClosed (termCodeM t) :=
  ⟨fun c => liftTerm_termCodeM c t, fun v s => substTerm_termCodeM v s t⟩

theorem closed_termsCodeM (ts : List Term) : CodeClosed (termsCodeM ts) :=
  ⟨fun c => liftTerm_termsCodeM c ts, fun v s => substTerm_termsCodeM v s ts⟩

theorem closed_nil : CodeClosed nil :=
  ⟨fun c => liftTerm_nil c, fun v s => substTerm_nil v s⟩

mutual
theorem closed_mem_tcodesT : ∀ (t x : Term), List.Mem x (tcodesT t) → CodeClosed x
  | .var n, x, h => by
      simp only [tcodesT] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_termCodeM (.var n)
      · cases h'
  | .func s ts, x, h => by
      simp only [tcodesT] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_termCodeM (.func s ts)
      · exact closed_mem_tcodesTs ts x h'
theorem closed_mem_tcodesTs : ∀ (ts : List Term) (x : Term),
    List.Mem x (tcodesTs ts) → CodeClosed x
  | [], x, h => by simp only [tcodesTs] at h; cases h
  | t :: ts, x, h => by
      simp only [tcodesTs] at h
      rcases List.mem_append.mp h with hA | hB
      · exact closed_mem_tcodesT t x hA
      · exact closed_mem_tcodesTs ts x hB
end

mutual
theorem closed_mem_lcodesT : ∀ (t x : Term), List.Mem x (lcodesT t) → CodeClosed x
  | .var n, x, h => by simp only [lcodesT] at h; cases h
  | .func s ts, x, h => by simp only [lcodesT] at h; exact closed_mem_lcodesTs ts x h
theorem closed_mem_lcodesTs : ∀ (ts : List Term) (x : Term),
    List.Mem x (lcodesTs ts) → CodeClosed x
  | [], x, h => by
      simp only [lcodesTs] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_nil
      · cases h'
  | t :: ts, x, h => by
      simp only [lcodesTs] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_termsCodeM (t :: ts)
      · rcases List.mem_append.mp h' with hA | hB
        · exact closed_mem_lcodesT t x hA
        · exact closed_mem_lcodesTs ts x hB
end

/-! ### El puente `objList` ⇄ meta (copia de `sondeos/ParseWitness.lean` §3) -/

theorem liftTerm_objList (c : Nat) : ∀ (L : List Term),
    (∀ x : Term, List.Mem x L → liftTerm c x = x) → liftTerm c (objList L) = objList L
  | [],      _ => rfl
  | e :: es, h => by
      simp only [objList, cons, liftTerm, liftTerms, h e (List.Mem.head _),
        liftTerm_objList c es (fun x hx => h x (List.Mem.tail _ hx))]

theorem substTerm_objList (v : Nat) (s : Term) : ∀ (L : List Term),
    (∀ x : Term, List.Mem x L → substTerm v s x = x) → substTerm v s (objList L) = objList L
  | [],      _ => rfl
  | e :: es, h => by
      simp only [objList, cons, substTerm, substTerms, h e (List.Mem.head _),
        substTerm_objList v s es (fun x hx => h x (List.Mem.tail _ hx))]

theorem prf_lenc_objList : ∀ L : List Term,
    Prf (Formula.eq (lenc (objList L)) (numeralM L.length))
  | []      => prf_lenc_nil
  | e :: es =>
      prf_eq_trans (prf_lenc_cons e (objList es)) (prf_eq_congr_succ (prf_lenc_objList es))

theorem prf_nthc_objList : ∀ (L : List Term) (k : Nat) (x : Term), L[k]? = some x →
    Prf (Formula.eq (nthc (objList L) (numeralM k)) x)
  | [],      k,     x, h => by simp at h
  | e :: es, 0,     x, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact prf_nthc_zero e (objList es)
  | e :: es, k + 1, x, h => by
      simp only [List.getElem?_cons_succ] at h
      exact prf_eq_trans (prf_nthc_succ e (objList es) (numeralM k))
        (prf_nthc_objList es k x h)

theorem prf_In_objList : ∀ (L : List Term) (x : Term), List.Mem x L → Prf (In x (objList L))
  | [],      x, h => by cases h
  | e :: es, x, h => by
      rcases List.mem_cons.mp h with rfl | h'
      · exact prf_in_cons_head x (objList es)
      · exact prf_in_cons_tail e (prf_In_objList es x h')

theorem mem_of_getElem? : ∀ (L : List Term) (k : Nat) (x : Term), L[k]? = some x → List.Mem x L
  | [],      k,     x, h => by simp at h
  | e :: es, 0,     x, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact List.Mem.head _
  | e :: es, k + 1, x, h => by
      simp only [List.getElem?_cons_succ] at h
      exact List.Mem.tail _ (mem_of_getElem? es k x h)

/-! ### Aritmética de listas concretas y los CUATRO moldes de nodo -/

theorem prf_lenc_c1 (a : Term) : Prf (lenc (cons a nil) =eq numeralM 1) :=
  prf_eq_trans (prf_lenc_cons a nil) (prf_eq_congr_succ prf_lenc_nil)

theorem prf_lenc_c2 (a b : Term) : Prf (lenc (cons a (cons b nil)) =eq numeralM 2) :=
  prf_eq_trans (prf_lenc_cons a (cons b nil)) (prf_eq_congr_succ (prf_lenc_c1 b))

theorem prf_lenc_c3 (a b c : Term) :
    Prf (lenc (cons a (cons b (cons c nil))) =eq numeralM 3) :=
  prf_eq_trans (prf_lenc_cons a (cons b (cons c nil))) (prf_eq_congr_succ (prf_lenc_c2 b c))

theorem prf_nthc_c1 (a b c : Term) : Prf (nthc (cons a (cons b c)) (numeralM 1) =eq b) :=
  prf_eq_trans (prf_nthc_succ a (cons b c) (numeralM 0)) (prf_nthc_zero b c)

theorem prf_nthc_c2 (a b c d : Term) :
    Prf (nthc (cons a (cons b (cons c d))) (numeralM 2) =eq c) :=
  prf_eq_trans (prf_nthc_succ a (cons b (cons c d)) (numeralM 1)) (prf_nthc_c1 b c d)

theorem prf_cOk_varOkT (a : Term) :
    Prf (cOk (cons (numeralM 0) (cons a nil)) (varOkT (cons (numeralM 0) (cons a nil)))) :=
  prf_and_intro (prf_consOk_cons _ _)
    (prf_and_intro (prf_carc_cons (numeralM 0) (cons a nil)) (prf_lenc_c2 (numeralM 0) a))

theorem prf_cOk_funcOkT (w S C : Term) (hC : Prf (In C w)) :
    Prf (cOk (cons (numeralM 1) (cons S (cons C nil)))
             (funcOkT w (cons (numeralM 1) (cons S (cons C nil))))) :=
  prf_and_intro (prf_consOk_cons _ _)
    (prf_and_intro
      (prf_and_intro (prf_carc_cons (numeralM 1) (cons S (cons C nil)))
        (prf_lenc_c3 (numeralM 1) S C))
      (prf_congr_In_left (prf_eq_symm (prf_nthc_c2 (numeralM 1) S C nil)) hC))

theorem prf_cOk_consCase2 (wT wTs A B : Term) (hA : Prf (In A wT)) (hB : Prf (In B wTs)) :
    Prf (cOk (cons A B) (land (In (carc (cons A B)) wT) (In (cdrc (cons A B)) wTs))) :=
  prf_and_intro (prf_consOk_cons A B)
    (prf_and_intro
      (prf_congr_In_left (prf_eq_symm (prf_carc_cons A B)) hA)
      (prf_congr_In_left (prf_eq_symm (prf_cdrc_cons A B)) hB))

theorem isTermCodeB_L (wT wTs X : Term) (h : Prf (cOk X (varOkT X))) :
    Prf (isTermCodeB wT wTs X) := prf_orL h
theorem isTermCodeB_R (wT wTs X : Term) (h : Prf (cOk X (funcOkT wTs X))) :
    Prf (isTermCodeB wT wTs X) := prf_orR h
theorem isTermsCodeB_L (wT wTs X : Term) (h : Prf (Formula.eq X nil)) :
    Prf (isTermsCodeB wT wTs X) := prf_orL h
theorem isTermsCodeB_R (wT wTs X : Term)
    (h : Prf (cOk X (land (In (carc X) wT) (In (cdrc X) wTs)))) :
    Prf (isTermsCodeB wT wTs X) := prf_orR h

/-! ### LAS DOS INDUCCIONES MUTUAS

    ⚠️ **Mejora sobre `sondeos/SubCodesWitness.lean`**: allí las listas testigo eran
    `objList W` (META). Aquí son **términos ABSTRACTOS** `WT`, `WTs` con un **oráculo de
    pertenencia**. Eso hace el transporte al par empaquetado (`carc p`, `cdrc p`) gratuito:
    basta componer el oráculo con `prf_congr_In_right`. -/

mutual
theorem okT_tcodesT : ∀ (t : Term) (WT WTs : Term),
    (∀ y : Term, List.Mem y (tcodesT t) → Prf (In y WT)) →
    (∀ y : Term, List.Mem y (lcodesT t) → Prf (In y WTs)) →
    ∀ x : Term, List.Mem x (tcodesT t) → Prf (isTermCodeB WT WTs x)
  | .var n, WT, WTs, _, _, x, hx => by
      simp only [tcodesT] at hx
      rcases List.mem_cons.mp hx with rfl | h'
      · exact isTermCodeB_L _ _ _ (prf_cOk_varOkT (numeralM n))
      · cases h'
  | .func s ts, WT, WTs, hT, hTs, x, hx => by
      have hTs' : ∀ y : Term, List.Mem y (lcodesTs ts) → Prf (In y WTs) := by
        intro y hy; exact hTs y (by simp only [lcodesT]; exact hy)
      have hmem : Prf (In (termsCodeM ts) WTs) := hTs' _ (mem_self_lcodesTs ts)
      simp only [tcodesT] at hx
      rcases List.mem_cons.mp hx with rfl | h'
      · exact isTermCodeB_R _ _ _ (prf_cOk_funcOkT WTs (strCodeM s) (termsCodeM ts) hmem)
      · exact okT_tcodesTs ts WT WTs
          (fun y hy => hT y (by simp only [tcodesT]; exact List.Mem.tail _ hy)) hTs' x h'
theorem okT_tcodesTs : ∀ (ts : List Term) (WT WTs : Term),
    (∀ y : Term, List.Mem y (tcodesTs ts) → Prf (In y WT)) →
    (∀ y : Term, List.Mem y (lcodesTs ts) → Prf (In y WTs)) →
    ∀ x : Term, List.Mem x (tcodesTs ts) → Prf (isTermCodeB WT WTs x)
  | [], WT, WTs, _, _, x, hx => by simp only [tcodesTs] at hx; cases hx
  | t :: ts, WT, WTs, hT, hTs, x, hx => by
      simp only [tcodesTs] at hx
      rcases List.mem_append.mp hx with hA | hB
      · exact okT_tcodesT t WT WTs
          (fun y hy => hT y (by simp only [tcodesTs]; exact List.mem_append.mpr (Or.inl hy)))
          (fun y hy => hTs y (by
            simp only [lcodesTs]
            exact List.Mem.tail _ (List.mem_append.mpr (Or.inl hy)))) x hA
      · exact okT_tcodesTs ts WT WTs
          (fun y hy => hT y (by simp only [tcodesTs]; exact List.mem_append.mpr (Or.inr hy)))
          (fun y hy => hTs y (by
            simp only [lcodesTs]
            exact List.Mem.tail _ (List.mem_append.mpr (Or.inr hy)))) x hB
end

mutual
theorem okTs_lcodesT : ∀ (t : Term) (WT WTs : Term),
    (∀ y : Term, List.Mem y (tcodesT t) → Prf (In y WT)) →
    (∀ y : Term, List.Mem y (lcodesT t) → Prf (In y WTs)) →
    ∀ x : Term, List.Mem x (lcodesT t) → Prf (isTermsCodeB WT WTs x)
  | .var n, WT, WTs, _, _, x, hx => by simp only [lcodesT] at hx; cases hx
  | .func s ts, WT, WTs, hT, hTs, x, hx => by
      simp only [lcodesT] at hx
      exact okTs_lcodesTs ts WT WTs
        (fun y hy => hT y (by simp only [tcodesT]; exact List.Mem.tail _ hy))
        (fun y hy => hTs y (by simp only [lcodesT]; exact hy)) x hx
theorem okTs_lcodesTs : ∀ (ts : List Term) (WT WTs : Term),
    (∀ y : Term, List.Mem y (tcodesTs ts) → Prf (In y WT)) →
    (∀ y : Term, List.Mem y (lcodesTs ts) → Prf (In y WTs)) →
    ∀ x : Term, List.Mem x (lcodesTs ts) → Prf (isTermsCodeB WT WTs x)
  | [], WT, WTs, _, _, x, hx => by
      simp only [lcodesTs] at hx
      rcases List.mem_cons.mp hx with rfl | h'
      · exact isTermsCodeB_L _ _ _ (prf_refl nil)
      · cases h'
  | t :: ts, WT, WTs, hT, hTs, x, hx => by
      have ht : Prf (In (termCodeM t) WT) :=
        hT _ (by simp only [tcodesTs]
                 exact List.mem_append.mpr (Or.inl (mem_self_tcodesT t)))
      have hts : Prf (In (termsCodeM ts) WTs) :=
        hTs _ (by simp only [lcodesTs]
                  exact List.Mem.tail _ (List.mem_append.mpr (Or.inr (mem_self_lcodesTs ts))))
      simp only [lcodesTs] at hx
      rcases List.mem_cons.mp hx with rfl | h'
      · exact isTermsCodeB_R _ _ _
          (prf_cOk_consCase2 WT WTs (termCodeM t) (termsCodeM ts) ht hts)
      · rcases List.mem_append.mp h' with hA | hB
        · exact okTs_lcodesT t WT WTs
            (fun y hy => hT y (by simp only [tcodesTs]
                                  exact List.mem_append.mpr (Or.inl hy)))
            (fun y hy => hTs y (by
              simp only [lcodesTs]
              exact List.Mem.tail _ (List.mem_append.mpr (Or.inl hy)))) x hA
        · exact okTs_lcodesTs ts WT WTs
            (fun y hy => hT y (by simp only [tcodesTs]
                                  exact List.mem_append.mpr (Or.inr hy)))
            (fun y hy => hTs y (by
              simp only [lcodesTs]
              exact List.Mem.tail _ (List.mem_append.mpr (Or.inr hy)))) x hB
end

/-! ## 14 · EL ENSAMBLAJE del testigo empaquetado -/

/-- El par de testigos como UN término: `⟨lista de códigos de término, lista de códigos de
    lista⟩`. -/
def pairOf (LT LTs : List Term) : Term := cons (objList LT) (objList LTs)

/-- **El ensamblaje genérico**: de las dos inducciones mutuas a `pairOk` del par empaquetado. -/
theorem prf_pairOk_pairOf (LT LTs : List Term)
    (hclT : ∀ x : Term, List.Mem x LT → CodeClosed x)
    (hclTs : ∀ x : Term, List.Mem x LTs → CodeClosed x)
    (hnT : ∀ (WT WTs : Term),
      (∀ y : Term, List.Mem y LT → Prf (In y WT)) →
      (∀ y : Term, List.Mem y LTs → Prf (In y WTs)) →
      ∀ x : Term, List.Mem x LT → Prf (isTermCodeB WT WTs x))
    (hnTs : ∀ (WT WTs : Term),
      (∀ y : Term, List.Mem y LT → Prf (In y WT)) →
      (∀ y : Term, List.Mem y LTs → Prf (In y WTs)) →
      ∀ x : Term, List.Mem x LTs → Prf (isTermsCodeB WT WTs x)) :
    Prf (pairOk (pairOf LT LTs)) := by
  let p : Term := pairOf LT LTs
  have hAl : ∀ c : Nat, liftTerm c (objList LT) = objList LT :=
    fun c => liftTerm_objList c LT (fun x hx => (hclT x hx).1 c)
  have hAs : ∀ (v : Nat) (s : Term), substTerm v s (objList LT) = objList LT :=
    fun v s => substTerm_objList v s LT (fun x hx => (hclT x hx).2 v s)
  have hBl : ∀ c : Nat, liftTerm c (objList LTs) = objList LTs :=
    fun c => liftTerm_objList c LTs (fun x hx => (hclTs x hx).1 c)
  have hBs : ∀ (v : Nat) (s : Term), substTerm v s (objList LTs) = objList LTs :=
    fun v s => substTerm_objList v s LTs (fun x hx => (hclTs x hx).2 v s)
  have hpl : ∀ c : Nat, liftTerm c p = p := by
    intro c; simp only [p, pairOf, cons, liftTerm, liftTerms, hAl, hBl]
  have hps : ∀ (v : Nat) (s : Term), substTerm v s p = p := by
    intro v s; simp only [p, pairOf, cons, substTerm, substTerms, hAs, hBs]
  have hcarc : Prf (carc p =eq objList LT) := prf_carc_cons _ _
  have hcdrc : Prf (cdrc p =eq objList LTs) := prf_cdrc_cons _ _
  -- los dos ORÁCULOS de pertenencia, ya transportados a `carc p` / `cdrc p`
  have oT : ∀ y : Term, List.Mem y LT → Prf (In y (carc p)) :=
    fun y hy => prf_congr_In_right (prf_eq_symm hcarc) (prf_In_objList LT y hy)
  have oTs : ∀ y : Term, List.Mem y LTs → Prf (In y (cdrc p)) :=
    fun y hy => prf_congr_In_right (prf_eq_symm hcdrc) (prf_In_objList LTs y hy)
  refine prf_pairOk_gen p LT.length LTs.length hps hpl
    (prf_eq_trans (prf_congr_lenc hcarc) (prf_lenc_objList LT))
    (prf_eq_trans (prf_congr_lenc hcdrc) (prf_lenc_objList LTs)) ?_ ?_
  · intro k hk
    obtain ⟨x, hx⟩ : ∃ x, LT[k]? = some x := ⟨LT[k], getElem?_pos LT k hk⟩
    have hnth : Prf (nthc (carc p) (numeralM k) =eq x) :=
      prf_eq_trans (prf_congr_nthc_lst (numeralM k) hcarc) (prf_nthc_objList LT k x hx)
    exact prf_congr_isTermCodeB (prf_eq_symm hnth)
      (hnT (carc p) (cdrc p) oT oTs x (mem_of_getElem? LT k x hx))
  · intro k hk
    obtain ⟨x, hx⟩ : ∃ x, LTs[k]? = some x := ⟨LTs[k], getElem?_pos LTs k hk⟩
    have hnth : Prf (nthc (cdrc p) (numeralM k) =eq x) :=
      prf_eq_trans (prf_congr_nthc_lst (numeralM k) hcdrc) (prf_nthc_objList LTs k x hx)
    exact prf_congr_isTermsCodeB (prf_eq_symm hnth)
      (hnTs (carc p) (cdrc p) oT oTs x (mem_of_getElem? LTs k x hx))

/-- El par testigo de un TÉRMINO. -/
def pairT (t : Term) : Term := pairOf (tcodesT t) (lcodesT t)

/-- El par testigo de una LISTA de términos. -/
def pairTs (ts : List Term) : Term := pairOf (tcodesTs ts) (lcodesTs ts)

theorem prf_pairOk_pairT (t : Term) : Prf (pairOk (pairT t)) :=
  prf_pairOk_pairOf (tcodesT t) (lcodesT t)
    (closed_mem_tcodesT t) (closed_mem_lcodesT t)
    (fun WT WTs hT hTs x hx => okT_tcodesT t WT WTs hT hTs x hx)
    (fun WT WTs hT hTs x hx => okTs_lcodesT t WT WTs hT hTs x hx)

theorem prf_pairOk_pairTs (ts : List Term) : Prf (pairOk (pairTs ts)) :=
  prf_pairOk_pairOf (tcodesTs ts) (lcodesTs ts)
    (closed_mem_tcodesTs ts) (closed_mem_lcodesTs ts)
    (fun WT WTs hT hTs x hx => okT_tcodesTs ts WT WTs hT hTs x hx)
    (fun WT WTs hT hTs x hx => okTs_lcodesTs ts WT WTs hT hTs x hx)

/-- **HITO (i), términos**: el par `(tcodesT t, lcodesT t)` es un testigo VÁLIDO y contiene
    `termCodeM t`. Enunciado sin ningún antecedente objeto: `Prf` desnudo. -/
theorem prf_isTCB_subCodesT (t : Term) : Prf (isTCB (pairT t) (termCodeM t)) :=
  prf_and_intro (prf_pairOk_pairT t)
    (prf_congr_In_right (prf_eq_symm (prf_carc_cons _ _))
      (prf_In_objList _ _ (mem_self_tcodesT t)))

/-- **HITO (i), listas** (la gemela). -/
theorem prf_isTsCB_subCodesTs (ts : List Term) :
    Prf (isTsCB (pairTs ts) (termsCodeM ts)) :=
  prf_and_intro (prf_pairOk_pairTs ts)
    (prf_congr_In_right (prf_eq_symm (prf_cdrc_cons _ _))
      (prf_In_objList _ _ (mem_self_lcodesTs ts)))

/-! ## 16 · LO QUE EL PAR PARTIDO SÍ HACE Y `nodeOk` NO: **DISCRIMINA**

    `sondeos/SubCodesCritica.lean` compiló `prf_isFC_junk : ⊢ isFC (implc ⌜x₀⌝ₜ ⌜x₀⌝ₜ)`.
    Con el par partido eso ya no puede pasar por construcción: `isTermCodeB` sólo admite
    `carc X ∈ {0̄, 1̄}` (tags de TÉRMINO). El testigo de `⌜x₀ ⇒ x₀⌝` no existe **por diseño**,
    porque el tag 5 no es ninguno de los dos disyuntos. -/

/-- El testigo de un término tiene `nil` (= `termsCodeM []`) en la mitad de LISTAS: el
    disyunto DESNUDO es OBLIGATORIO, exactamente como en A3. -/
example : List.Mem nil (lcodesTs ([] : List Term)) := List.Mem.head _

/-! # ═══════════════════════════════════════════════════════════════════════════
    ## 17 · EL TERCER PREDICADO: `isFormCodeB` (8 disyuntos) ENCIMA DEL PAR
    ═══════════════════════════════════════════════════════════════════════════

    Se escribe **GENÉRICO EN LOS ACCESORES** `aF aT aTs : Term → Term`. Con eso:

    * el paquete deja de estar cableado: sirve el par `(carc, cdrc)` de §1 y sirve la
      TERNA `(carc, carc ∘ cdrc, cdrc ∘ cdrc)` sin tocar una línea;
    * queda **demostrado** (no estimado) que reinstanciar las familias T/Ts sobre el
      paquete de tres es una re‑parametrización, no trabajo nuevo.

    Lo único que `pcc_bdAll_intro` pide de un accesor es NATURALIDAD (`hal`, `has`). -/

def nulOkF (X : Term) : Formula :=
  land (Formula.eq (carc X) (numeralM 2)) (Formula.eq (lenc X) (numeralM 1))

def unOkF (w X : Term) (k : Nat) : Formula :=
  land (land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM 2)))
       (In (nthc X (numeralM 1)) w)

/-- ⚠️ **DOS testigos distintos**, uno por casilla: `eq t u` pide `wT` en las dos, pero
    `atom`/`impl`/… piden listas diferentes. Ésta es la generalización que `binOk` de A3
    no tenía (allí todo iba contra la ÚNICA lista fusionada). -/
def binOkF (wA wB X : Term) (k : Nat) : Formula :=
  land (land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM 3)))
       (land (In (nthc X (numeralM 1)) wA) (In (nthc X (numeralM 2)) wB))

def strBinOkF (w X : Term) (k : Nat) : Formula :=
  land (land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM 3)))
       (In (nthc X (numeralM 2)) w)

def lorAll : Formula → List Formula → Formula
  | a, []      => a
  | a, b :: bs => lor a (lorAll b bs)

/-- `X` es código de FÓRMULA: los 8 tags 2..9, cada casilla contra la lista que le toca. -/
def isFormCodeB (wF wT wTs X : Term) : Formula :=
  lorAll (cOk X (nulOkF X))
    [ cOk X (strBinOkF wTs X 3)      -- atom p ts   : casilla 2 es LISTA DE TÉRMINOS
    , cOk X (binOkF wT wT X 4)       -- eq t u      : dos TÉRMINOS
    , cOk X (binOkF wF wF X 5)       -- impl a b
    , cOk X (unOkF  wF X 6)          -- ∀ a
    , cOk X (binOkF wF wF X 7)       -- ∧ a b
    , cOk X (binOkF wF wF X 8)       -- ∨ a b
    , cOk X (unOkF  wF X 9) ]        -- ∃ a

noncomputable def unDotF (W X : Term) (k : Nat) : Term :=
  andc (shapeDot X k 2) (inFormCodeFn (nthcT X (tcFn (numeralM 1))) W)

noncomputable def binDotF (WA WB X : Term) (k : Nat) : Term :=
  andc (shapeDot X k 3)
    (andc (inFormCodeFn (nthcT X (tcFn (numeralM 1))) WA)
          (inFormCodeFn (nthcT X (tcFn (numeralM 2))) WB))

noncomputable def strBinDotF (W X : Term) (k : Nat) : Term :=
  andc (shapeDot X k 3) (inFormCodeFn (nthcT X (tcFn (numeralM 2))) W)

def lorAllc : Term → List Term → Term
  | a, []      => a
  | a, b :: bs => orc a (lorAllc b bs)

noncomputable def isFormCodeDot (WF WT WTs X : Term) : Term :=
  lorAllc (shapeDot X 2 1)
    [ strBinDotF WTs X 3
    , binDotF WT WT X 4
    , binDotF WF WF X 5
    , unDotF  WF X 6
    , binDotF WF WF X 7
    , binDotF WF WF X 8
    , unDotF  WF X 9 ]

/-! ### El descenso de `substfc` por los 8 disyuntos -/

theorem prf_substfc_unDotF (s W X X' : Term) (k : Nat)
    (hW : ∀ V, Prf (substtc zero V W =eq W)) (hX : Prf (substtc zero s X =eq X')) :
    Prf (substfc zero s (unDotF W X k) =eq unDotF W X' k) := by
  unfold unDotF
  exact prf_eq_trans (prf_substfc_and zero s _ _)
    (prf_congr_andc (prf_substfc_shapeDot s X X' k 2 hX)
      (prf_substfc_inDot s _ _ W (prf_substtc_child s X X' 1 hX) hW))

theorem prf_substfc_binDotF (s WA WB X X' : Term) (k : Nat)
    (hA : ∀ V, Prf (substtc zero V WA =eq WA)) (hB : ∀ V, Prf (substtc zero V WB =eq WB))
    (hX : Prf (substtc zero s X =eq X')) :
    Prf (substfc zero s (binDotF WA WB X k) =eq binDotF WA WB X' k) := by
  unfold binDotF
  refine prf_eq_trans (prf_substfc_and zero s _ _)
    (prf_congr_andc (prf_substfc_shapeDot s X X' k 3 hX) ?_)
  exact prf_eq_trans (prf_substfc_and zero s _ _)
    (prf_congr_andc (prf_substfc_inDot s _ _ WA (prf_substtc_child s X X' 1 hX) hA)
      (prf_substfc_inDot s _ _ WB (prf_substtc_child s X X' 2 hX) hB))

theorem prf_substfc_strBinDotF (s W X X' : Term) (k : Nat)
    (hW : ∀ V, Prf (substtc zero V W =eq W)) (hX : Prf (substtc zero s X =eq X')) :
    Prf (substfc zero s (strBinDotF W X k) =eq strBinDotF W X' k) := by
  unfold strBinDotF
  exact prf_eq_trans (prf_substfc_and zero s _ _)
    (prf_congr_andc (prf_substfc_shapeDot s X X' k 3 hX)
      (prf_substfc_inDot s _ _ W (prf_substtc_child s X X' 2 hX) hW))

theorem prf_substfc_isFormCodeDot_gen (s WF WT WTs X X' : Term)
    (hF : ∀ V, Prf (substtc zero V WF =eq WF))
    (hT : ∀ V, Prf (substtc zero V WT =eq WT))
    (hTs : ∀ V, Prf (substtc zero V WTs =eq WTs))
    (hX : Prf (substtc zero s X =eq X')) :
    Prf (substfc zero s (isFormCodeDot WF WT WTs X) =eq isFormCodeDot WF WT WTs X') := by
  unfold isFormCodeDot lorAllc
  refine prf_eq_trans (prf_substfc_or zero s _ _)
    (prf_congr_orc (prf_substfc_shapeDot s X X' 2 1 hX) ?_)
  refine prf_eq_trans (prf_substfc_or zero s _ _)
    (prf_congr_orc (prf_substfc_strBinDotF s WTs X X' 3 hTs hX) ?_)
  refine prf_eq_trans (prf_substfc_or zero s _ _)
    (prf_congr_orc (prf_substfc_binDotF s WT WT X X' 4 hT hT hX) ?_)
  refine prf_eq_trans (prf_substfc_or zero s _ _)
    (prf_congr_orc (prf_substfc_binDotF s WF WF X X' 5 hF hF hX) ?_)
  refine prf_eq_trans (prf_substfc_or zero s _ _)
    (prf_congr_orc (prf_substfc_unDotF s WF X X' 6 hF hX) ?_)
  refine prf_eq_trans (prf_substfc_or zero s _ _)
    (prf_congr_orc (prf_substfc_binDotF s WF WF X X' 7 hF hF hX) ?_)
  refine prf_eq_trans (prf_substfc_or zero s _ _)
    (prf_congr_orc (prf_substfc_binDotF s WF WF X X' 8 hF hF hX) ?_)
  exact prf_substfc_unDotF s WF X X' 9 hF hX

/-! ### Los cuatro moldes de disyunto, dotados -/

theorem pcc_nulOkF_case (X : Term) :
    Prf (cOk X (nulOkF X) ⇒ provFromCode (shapeDot (tcFn X) 2 1)) := by
  refine prf_deduction ?_
  have h := prfH_hyp_self (cOk X (nulOkF X))
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (pcc_shape_tracked X 2 1) _)
    (PrfH_and_elim_left h)) (PrfH_and_elim_right h)

theorem pcc_unOkF_case (q X : Term) (k : Nat) :
    Prf (cOk X (unOkF q X k) ⇒ provFromCode (unDotF (tcFn q) (tcFn X) k)) := by
  refine prf_deduction ?_
  have h := prfH_hyp_self (cOk X (unOkF q X k))
  have hcons := PrfH_and_elim_left h
  have hun := PrfH_and_elim_right h
  have hsh := PrfH_and_elim_left hun
  have hmem := PrfH_and_elim_right hun
  have h1 := PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (pcc_shape_tracked X k 2) _) hcons) hsh
  have h2 := PrfH.mp _ _ _ (PrfH.mp _ _ _
    (prf_to_prfH (pcc_child_tracked q X 1 2 (by omega)) _) (PrfH_and_elim_right hsh)) hmem
  exact PrfH_and_intro_code _ _ h1 h2

theorem pcc_binOkF_case (qA qB X : Term) (k : Nat) :
    Prf (cOk X (binOkF qA qB X k) ⇒ provFromCode (binDotF (tcFn qA) (tcFn qB) (tcFn X) k)) := by
  refine prf_deduction ?_
  have h := prfH_hyp_self (cOk X (binOkF qA qB X k))
  have hcons := PrfH_and_elim_left h
  have hbin := PrfH_and_elim_right h
  have hsh := PrfH_and_elim_left hbin
  have hmem := PrfH_and_elim_right hbin
  have h1 := PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (pcc_shape_tracked X k 3) _) hcons) hsh
  have h2 := PrfH.mp _ _ _ (PrfH.mp _ _ _
    (prf_to_prfH (pcc_child_tracked qA X 1 3 (by omega)) _) (PrfH_and_elim_right hsh))
    (PrfH_and_elim_left hmem)
  have h3 := PrfH.mp _ _ _ (PrfH.mp _ _ _
    (prf_to_prfH (pcc_child_tracked qB X 2 3 (by omega)) _) (PrfH_and_elim_right hsh))
    (PrfH_and_elim_right hmem)
  exact PrfH_and_intro_code _ _ h1 (PrfH_and_intro_code _ _ h2 h3)

theorem pcc_strBinOkF_case (q X : Term) (k : Nat) :
    Prf (cOk X (strBinOkF q X k) ⇒ provFromCode (strBinDotF (tcFn q) (tcFn X) k)) := by
  refine prf_deduction ?_
  have h := prfH_hyp_self (cOk X (strBinOkF q X k))
  have hcons := PrfH_and_elim_left h
  have hsb := PrfH_and_elim_right h
  have hsh := PrfH_and_elim_left hsb
  have hmem := PrfH_and_elim_right hsb
  have h1 := PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (pcc_shape_tracked X k 3) _) hcons) hsh
  have h2 := PrfH.mp _ _ _ (PrfH.mp _ _ _
    (prf_to_prfH (pcc_child_tracked q X 2 3 (by omega)) _) (PrfH_and_elim_right hsh)) hmem
  exact PrfH_and_intro_code _ _ h1 h2

/-- **El ensamblaje de los 8 disyuntos** (el mismo patrón que A3 con 12, recortado). -/
theorem pcc_isFormCodeB_pure (qF qT qTs X : Term) :
    Prf (isFormCodeB qF qT qTs X ⇒
      provFromCode (isFormCodeDot (tcFn qF) (tcFn qT) (tcFn qTs) (tcFn X))) := by
  have s7 : Prf (cOk X (unOkF qF X 9) ⇒ provFromCode (unDotF (tcFn qF) (tcFn X) 9)) :=
    pcc_unOkF_case qF X 9
  have s6 := prf_or_elim_imp
    (impT (pcc_binOkF_case qF qF X 8) (prf_orL_imp (binDotF (tcFn qF) (tcFn qF) (tcFn X) 8) _))
    (impT s7 (prf_orR_imp (binDotF (tcFn qF) (tcFn qF) (tcFn X) 8) _))
  have s5 := prf_or_elim_imp
    (impT (pcc_binOkF_case qF qF X 7) (prf_orL_imp (binDotF (tcFn qF) (tcFn qF) (tcFn X) 7) _))
    (impT s6 (prf_orR_imp (binDotF (tcFn qF) (tcFn qF) (tcFn X) 7) _))
  have s4 := prf_or_elim_imp
    (impT (pcc_unOkF_case qF X 6) (prf_orL_imp (unDotF (tcFn qF) (tcFn X) 6) _))
    (impT s5 (prf_orR_imp (unDotF (tcFn qF) (tcFn X) 6) _))
  have s3 := prf_or_elim_imp
    (impT (pcc_binOkF_case qF qF X 5) (prf_orL_imp (binDotF (tcFn qF) (tcFn qF) (tcFn X) 5) _))
    (impT s4 (prf_orR_imp (binDotF (tcFn qF) (tcFn qF) (tcFn X) 5) _))
  have s2 := prf_or_elim_imp
    (impT (pcc_binOkF_case qT qT X 4) (prf_orL_imp (binDotF (tcFn qT) (tcFn qT) (tcFn X) 4) _))
    (impT s3 (prf_orR_imp (binDotF (tcFn qT) (tcFn qT) (tcFn X) 4) _))
  have s1 := prf_or_elim_imp
    (impT (pcc_strBinOkF_case qTs X 3) (prf_orL_imp (strBinDotF (tcFn qTs) (tcFn X) 3) _))
    (impT s2 (prf_orR_imp (strBinDotF (tcFn qTs) (tcFn X) 3) _))
  exact prf_or_elim_imp
    (impT (pcc_nulOkF_case X) (prf_orL_imp (shapeDot (tcFn X) 2 1) _))
    (impT s1 (prf_orR_imp (shapeDot (tcFn X) 2 1) _))

/-! ### La capa `wfAll`, GENÉRICA en los tres accesores -/

def bndFF (aF : Term → Term) (p : Term) : Term := lenc (aF p)

def wfAllF (aF aT aTs : Term → Term) (p : Term) : Formula :=
  Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (bndFF aF p)))
    (isFormCodeB (liftTerm 0 (aF p)) (liftTerm 0 (aT p)) (liftTerm 0 (aTs p))
      (nthc (liftTerm 0 (aF p)) (.var 0))))

noncomputable def PsiFF (aF aT aTs : Term → Term) (p : Term) : Term :=
  isFormCodeDot (tcFn (aF p)) (tcFn (aT p)) (tcFn (aTs p))
    (nthcT (tcFn (aF p)) (varc (numeral 0)))

theorem prf_substfc_PsiFat (A B C s : Term) :
    Prf (substfc zero s (isFormCodeDot (tcFn A) (tcFn B) (tcFn C)
          (nthcT (tcFn A) (varc (numeral 0))))
      =eq isFormCodeDot (tcFn A) (tcFn B) (tcFn C) (nthcT (tcFn A) s)) :=
  prf_substfc_isFormCodeDot_gen s _ _ _ _ _
    (substtc_inv_tcFn A) (substtc_inv_tcFn B) (substtc_inv_tcFn C)
    (prf_eq_trans (prf_substtc_nthcT zero s (tcFn A) (varc (numeral 0)))
      (prf_congr_nthcT (substtc_inv_tcFn A s) (prf_substtc_varc0 s)))

theorem prf_substfc_PsiFF (aF aT aTs : Term → Term) (p s : Term) :
    Prf (substfc zero s (PsiFF aF aT aTs p)
      =eq isFormCodeDot (tcFn (aF p)) (tcFn (aT p)) (tcFn (aTs p)) (nthcT (tcFn (aF p)) s)) :=
  prf_substfc_PsiFat (aF p) (aT p) (aTs p) s

/-- **NATURALIDAD**: lo único que `pcc_bdAll_intro` pide de un accesor. -/
structure Nat1 (a : Term → Term) : Prop where
  lift : ∀ (k : Nat) (q : Term), liftTerm k (a q) = a (liftTerm k q)
  subst : ∀ (v : Nat) (t q : Term), substTerm v t (a q) = a (substTerm v t q)

theorem nat1_carc : Nat1 carc :=
  ⟨fun k q => by simp only [carc, liftTerm, liftTerms],
   fun v t q => by simp only [carc, substTerm, substTerms]⟩

theorem nat1_cdrc : Nat1 cdrc :=
  ⟨fun k q => by simp only [cdrc, liftTerm, liftTerms],
   fun v t q => by simp only [cdrc, substTerm, substTerms]⟩

theorem hbl_F (aF : Term → Term) (hF : Nat1 aF) :
    ∀ (k : Nat) (q : Term), liftTerm k (bndFF aF q) = bndFF aF (liftTerm k q) := by
  intro k q; simp only [bndFF, lenc, liftTerm, liftTerms, hF.lift]

theorem hbs_F (aF : Term → Term) (hF : Nat1 aF) :
    ∀ (v : Nat) (t q : Term), substTerm v t (bndFF aF q) = bndFF aF (substTerm v t q) := by
  intro v t q; simp only [bndFF, lenc, substTerm, substTerms, hF.subst]

theorem hPl_F (aF aT aTs : Term → Term) (hF : Nat1 aF) (hT : Nat1 aT) (hTs : Nat1 aTs) :
    ∀ (k : Nat) (q : Term), liftTerm k (PsiFF aF aT aTs q) = PsiFF aF aT aTs (liftTerm k q) := by
  intro k q
  simp only [PsiFF, isFormCodeDot, lorAllc, shapeDot, unDotF, binDotF, strBinDotF,
    inFormCodeFn, eqCodeFn, andc, orc, carcT, cdrcT, lencT, nthcT, funcc, varc, tcFn,
    cons, nil, zero, succ, numeralM, liftTerm, liftTerms, liftTerm_numeral, liftTerm_strCode,
    hF.lift, hT.lift, hTs.lift]

theorem hPs_F (aF aT aTs : Term → Term) (hF : Nat1 aF) (hT : Nat1 aT) (hTs : Nat1 aTs) :
    ∀ (v : Nat) (t q : Term),
      substTerm v t (PsiFF aF aT aTs q) = PsiFF aF aT aTs (substTerm v t q) := by
  intro v t q
  simp only [PsiFF, isFormCodeDot, lorAllc, shapeDot, unDotF, binDotF, strBinDotF,
    inFormCodeFn, eqCodeFn, andc, orc, carcT, cdrcT, lencT, nthcT, funcc, varc, tcFn,
    cons, nil, zero, succ, numeralM, substTerm, substTerms, substTerm_numeral, substTerm_strCode,
    hF.subst, hT.subst, hTs.subst]

theorem hCl_F (aF aT aTs : Term → Term) (hF : Nat1 aF) (hT : Nat1 aT) (hTs : Nat1 aTs) :
    ∀ (k : Nat) (q : Term),
      liftFormula k (wfAllF aF aT aTs q) = wfAllF aF aT aTs (liftTerm k q) := by
  intro k q
  simp only [wfAllF, bndFF, isFormCodeB, lorAll, cOk, consOk, nulOkF, unOkF, binOkF, strBinOkF,
    land, lor, In, lt, carc, cdrc, lenc, nthc, cons, nil, zero, liftFormula, liftTerm, liftTerms,
    liftTerm_numeralM, if_pos (Nat.zero_lt_succ k), ← FOL.liftTerm_comm_zero,
    hF.lift, hT.lift, hTs.lift]

theorem hCs_F (aF aT aTs : Term → Term) (hF : Nat1 aF) (hT : Nat1 aT) (hTs : Nat1 aTs) :
    ∀ (v : Nat) (t q : Term),
      substFormula v t (wfAllF aF aT aTs q) = wfAllF aF aT aTs (substTerm v t q) := by
  intro v t q
  have h1 : ¬ ((0 : Nat) = v + 1) := by omega
  have h2 : ¬ ((0 : Nat) > v + 1) := by omega
  simp only [wfAllF, bndFF, isFormCodeB, lorAll, cOk, consOk, nulOkF, unOkF, binOkF, strBinOkF,
    land, lor, In, lt, carc, cdrc, lenc, nthc, cons, nil, zero, substFormula, substTerm, substTerms,
    substTerm_numeralM, FOL.substTerm_lift_comm_zero, if_neg h1, if_neg h2,
    hF.subst, hT.subst, hTs.subst]

theorem hPsiId_F (aF aT aTs : Term → Term) : ∀ q : Term,
    Prf (substfc zero (varc (numeral 0)) (PsiFF aF aT aTs q) =eq PsiFF aF aT aTs q) :=
  fun q => prf_substfc_PsiFF aF aT aTs q (varc (numeral 0))

/-- El `hbody` de la familia F, escrito sobre TRES TÉRMINOS sueltos: así el accesor
    desaparece de la prueba y `hbody_F` es una instanciación de una línea. -/
theorem hbody_F_core (A B C i : Term) :
    Prf (Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (lenc A)))
          (isFormCodeB (liftTerm 0 A) (liftTerm 0 B) (liftTerm 0 C)
            (nthc (liftTerm 0 A) (.var 0))))
      ⇒ (lt i (lenc A) ⇒ provFromCode (substfc zero (tcFn i)
          (isFormCodeDot (tcFn A) (tcFn B) (tcFn C) (nthcT (tcFn A) (varc (numeral 0))))))) := by
  refine prf_deduction (deduction_aux ?_ (lt i (lenc A))
    [Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (lenc A)))
      (isFormCodeB (liftTerm 0 A) (liftTerm 0 B) (liftTerm 0 C)
        (nthc (liftTerm 0 A) (.var 0))))] rfl)
  have hlt := PrfH.hyp [lt i (lenc A),
    Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (lenc A)))
      (isFormCodeB (liftTerm 0 A) (liftTerm 0 B) (liftTerm 0 C)
        (nthc (liftTerm 0 A) (.var 0))))] _ (List.Mem.head _)
  have hwf := PrfH.hyp [lt i (lenc A),
    Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (lenc A)))
      (isFormCodeB (liftTerm 0 A) (liftTerm 0 B) (liftTerm 0 C)
        (nthc (liftTerm 0 A) (.var 0))))] _ (List.Mem.tail _ (List.Mem.head _))
  have hsubst : substFormula 0 i (Formula.impl (lt (.var 0) (liftTerm 0 (lenc A)))
      (isFormCodeB (liftTerm 0 A) (liftTerm 0 B) (liftTerm 0 C) (nthc (liftTerm 0 A) (.var 0))))
      = Formula.impl (lt i (lenc A)) (isFormCodeB A B C (nthc A i)) := by
    simp only [isFormCodeB, lorAll, cOk, consOk, nulOkF, unOkF, binOkF, strBinOkF,
      land, lor, In, lt, carc, cdrc, lenc, nthc, cons, nil, zero, substFormula, substTerm,
      substTerms, substTerm_numeralM, FOL.substTerm_liftTerm, if_true]
  have h0 := PrfH.mp _ _ _ (PrfH.incl0 _ _
    (Prf₀.q1 (Formula.impl (lt (.var 0) (liftTerm 0 (lenc A)))
      (isFormCodeB (liftTerm 0 A) (liftTerm 0 B) (liftTerm 0 C)
        (nthc (liftTerm 0 A) (.var 0)))) i)) hwf
  rw [hsubst] at h0
  have hnode := PrfH.mp _ _ _ h0 hlt
  have hpure := PrfH.mp _ _ _
    (prf_to_prfH (pcc_isFormCodeB_pure A B C (nthc A i)) _) hnode
  have hev := PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_nthc A i) _) hlt
  have hevS := PrfH_eq_symm_code _ _
    (substtc_inv_nthcT (substtc_inv_tcFn A) (substtc_inv_tcFn i)) hev
  have hCC : ∀ t : Term,
      Prf (substfc zero t (isFormCodeDot (tcFn A) (tcFn B) (tcFn C) (varc (numeral 0)))
        =eq isFormCodeDot (tcFn A) (tcFn B) (tcFn C) t) :=
    fun t => prf_substfc_isFormCodeDot_gen t (tcFn A) (tcFn B) (tcFn C) (varc (numeral 0)) t
      (substtc_inv_tcFn A) (substtc_inv_tcFn B) (substtc_inv_tcFn C) (prf_substtc_varc0 t)
  have h1 := PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_eq_symm (hCC _))) _) hpure
  have h2 := PrfH_leibniz_apply _ _ _ hevS h1
  have h3 := PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hCC _)) _) h2
  exact PrfH.mp _ _ _
    (prf_to_prfH (prf_provCode_congr (prf_eq_symm (prf_substfc_PsiFat A B C (tcFn i)))) _) h3

theorem hbody_F (aF aT aTs : Term → Term) : ∀ q i : Term,
    Prf (wfAllF aF aT aTs q ⇒ (lt i (bndFF aF q)
      ⇒ provFromCode (substfc zero (tcFn i) (PsiFF aF aT aTs q)))) :=
  fun q i => hbody_F_core (aF q) (aT q) (aTs q) i

/-- **EL TERCER REFLECTOR**, genérico en los accesores. -/
theorem pcc_wfAllF_tracked (aF aT aTs : Term → Term)
    (hF : Nat1 aF) (hT : Nat1 aT) (hTs : Nat1 aTs) (p : Term) :
    Prf (wfAllF aF aT aTs p ⇒
      provFromCode (bdAllCode (tcFn (bndFF aF p)) (PsiFF aF aT aTs p))) :=
  pcc_bdAll_intro (wfAllF aF aT aTs) (bndFF aF) (PsiFF aF aT aTs) p
    (hCl_F aF aT aTs hF hT hTs) (hCs_F aF aT aTs hF hT hTs)
    (hbl_F aF hF) (hbs_F aF hF)
    (hPl_F aF aT aTs hF hT hTs) (hPs_F aF aT aTs hF hT hTs)
    (hPsiId_F aF aT aTs) (hbody_F aF aT aTs)

/-! ### Las familias T / Ts, GENÉRICAS en los accesores

    Esto es la **re‑parametrización**, y se comprueba abajo que es *literalmente* la misma
    definición: `wfAllT = wfAllTgen carc cdrc` por `rfl`. Es decir, pasar del paquete de
    DOS al de TRES **no cuesta ninguna prueba nueva**: sólo cambia el accesor. -/

def bndTgen  (aT  : Term → Term) (p : Term) : Term := lenc (aT p)
def bndTsgen (aTs : Term → Term) (p : Term) : Term := lenc (aTs p)

def wfAllTgen (aT aTs : Term → Term) (p : Term) : Formula :=
  Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (bndTgen aT p)))
    (isTermCodeB (liftTerm 0 (aT p)) (liftTerm 0 (aTs p)) (nthc (liftTerm 0 (aT p)) (.var 0))))

def wfAllTsgen (aT aTs : Term → Term) (p : Term) : Formula :=
  Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (bndTsgen aTs p)))
    (isTermsCodeB (liftTerm 0 (aT p)) (liftTerm 0 (aTs p)) (nthc (liftTerm 0 (aTs p)) (.var 0))))

noncomputable def PsiTgen (aT aTs : Term → Term) (p : Term) : Term :=
  isTermCodeDot (tcFn (aT p)) (tcFn (aTs p)) (nthcT (tcFn (aT p)) (varc (numeral 0)))

noncomputable def PsiTsgen (aT aTs : Term → Term) (p : Term) : Term :=
  isTermsCodeDot (tcFn (aT p)) (tcFn (aTs p)) (nthcT (tcFn (aTs p)) (varc (numeral 0)))

/-- ✅ La versión de §1 **ES** la genérica instanciada. Cero duplicación de contenido. -/
example : wfAllT = wfAllTgen carc cdrc := rfl
example : wfAllTs = wfAllTsgen carc cdrc := rfl
example : PsiT = PsiTgen carc cdrc := rfl
example : PsiTs = PsiTsgen carc cdrc := rfl

theorem prf_substfc_PsiTgen (aT aTs : Term → Term) (p s : Term) :
    Prf (substfc zero s (PsiTgen aT aTs p)
      =eq isTermCodeDot (tcFn (aT p)) (tcFn (aTs p)) (nthcT (tcFn (aT p)) s)) :=
  prf_substfc_isTermCodeDot_gen s _ _ _ _ (substtc_inv_tcFn (aTs p))
    (prf_eq_trans (prf_substtc_nthcT zero s (tcFn (aT p)) (varc (numeral 0)))
      (prf_congr_nthcT (substtc_inv_tcFn (aT p) s) (prf_substtc_varc0 s)))

theorem prf_substfc_PsiTsgen (aT aTs : Term → Term) (p s : Term) :
    Prf (substfc zero s (PsiTsgen aT aTs p)
      =eq isTermsCodeDot (tcFn (aT p)) (tcFn (aTs p)) (nthcT (tcFn (aTs p)) s)) :=
  prf_substfc_isTermsCodeDot_gen s _ _ _ _
    (substtc_inv_tcFn (aT p)) (substtc_inv_tcFn (aTs p))
    (prf_eq_trans (prf_substtc_nthcT zero s (tcFn (aTs p)) (varc (numeral 0)))
      (prf_congr_nthcT (substtc_inv_tcFn (aTs p) s) (prf_substtc_varc0 s)))

theorem hbl_Tg (aT : Term → Term) (hT : Nat1 aT) :
    ∀ (k : Nat) (q : Term), liftTerm k (bndTgen aT q) = bndTgen aT (liftTerm k q) := by
  intro k q; simp only [bndTgen, lenc, liftTerm, liftTerms, hT.lift]

theorem hbs_Tg (aT : Term → Term) (hT : Nat1 aT) :
    ∀ (v : Nat) (t q : Term), substTerm v t (bndTgen aT q) = bndTgen aT (substTerm v t q) := by
  intro v t q; simp only [bndTgen, lenc, substTerm, substTerms, hT.subst]

theorem hbl_Tsg (aTs : Term → Term) (hTs : Nat1 aTs) :
    ∀ (k : Nat) (q : Term), liftTerm k (bndTsgen aTs q) = bndTsgen aTs (liftTerm k q) := by
  intro k q; simp only [bndTsgen, lenc, liftTerm, liftTerms, hTs.lift]

theorem hbs_Tsg (aTs : Term → Term) (hTs : Nat1 aTs) :
    ∀ (v : Nat) (t q : Term),
      substTerm v t (bndTsgen aTs q) = bndTsgen aTs (substTerm v t q) := by
  intro v t q; simp only [bndTsgen, lenc, substTerm, substTerms, hTs.subst]

theorem hPl_Tg (aT aTs : Term → Term) (hT : Nat1 aT) (hTs : Nat1 aTs) :
    ∀ (k : Nat) (q : Term), liftTerm k (PsiTgen aT aTs q) = PsiTgen aT aTs (liftTerm k q) := by
  intro k q
  simp only [PsiTgen, isTermCodeDot, varDotT, funcDotT, shapeDot, inFormCodeFn, eqCodeFn,
    andc, orc, carcT, cdrcT, lencT, nthcT, funcc, varc, tcFn,
    cons, nil, zero, succ, numeralM, liftTerm, liftTerms, liftTerm_numeral, liftTerm_strCode,
    hT.lift, hTs.lift]

theorem hPs_Tg (aT aTs : Term → Term) (hT : Nat1 aT) (hTs : Nat1 aTs) :
    ∀ (v : Nat) (t q : Term),
      substTerm v t (PsiTgen aT aTs q) = PsiTgen aT aTs (substTerm v t q) := by
  intro v t q
  simp only [PsiTgen, isTermCodeDot, varDotT, funcDotT, shapeDot, inFormCodeFn, eqCodeFn,
    andc, orc, carcT, cdrcT, lencT, nthcT, funcc, varc, tcFn,
    cons, nil, zero, succ, numeralM, substTerm, substTerms, substTerm_numeral, substTerm_strCode,
    hT.subst, hTs.subst]

theorem hPl_Tsg (aT aTs : Term → Term) (hT : Nat1 aT) (hTs : Nat1 aTs) :
    ∀ (k : Nat) (q : Term), liftTerm k (PsiTsgen aT aTs q) = PsiTsgen aT aTs (liftTerm k q) := by
  intro k q
  simp only [PsiTsgen, isTermsCodeDot, inFormCodeFn, eqCodeFn,
    andc, orc, carcT, cdrcT, lencT, nthcT, funcc, varc, tcFn,
    cons, nil, zero, succ, numeralM, liftTerm, liftTerms, liftTerm_numeral, liftTerm_strCode,
    hT.lift, hTs.lift]

theorem hPs_Tsg (aT aTs : Term → Term) (hT : Nat1 aT) (hTs : Nat1 aTs) :
    ∀ (v : Nat) (t q : Term),
      substTerm v t (PsiTsgen aT aTs q) = PsiTsgen aT aTs (substTerm v t q) := by
  intro v t q
  simp only [PsiTsgen, isTermsCodeDot, inFormCodeFn, eqCodeFn,
    andc, orc, carcT, cdrcT, lencT, nthcT, funcc, varc, tcFn,
    cons, nil, zero, succ, numeralM, substTerm, substTerms, substTerm_numeral, substTerm_strCode,
    hT.subst, hTs.subst]

theorem hCl_Tg (aT aTs : Term → Term) (hT : Nat1 aT) (hTs : Nat1 aTs) :
    ∀ (k : Nat) (q : Term),
      liftFormula k (wfAllTgen aT aTs q) = wfAllTgen aT aTs (liftTerm k q) := by
  intro k q
  simp only [wfAllTgen, bndTgen, isTermCodeB, cOk, consOk, varOkT, funcOkT, land, lor, In, lt,
    carc, cdrc, lenc, nthc, cons, nil, zero, liftFormula, liftTerm, liftTerms,
    liftTerm_numeralM, if_pos (Nat.zero_lt_succ k), ← FOL.liftTerm_comm_zero,
    hT.lift, hTs.lift]

theorem hCs_Tg (aT aTs : Term → Term) (hT : Nat1 aT) (hTs : Nat1 aTs) :
    ∀ (v : Nat) (t q : Term),
      substFormula v t (wfAllTgen aT aTs q) = wfAllTgen aT aTs (substTerm v t q) := by
  intro v t q
  have h1 : ¬ ((0 : Nat) = v + 1) := by omega
  have h2 : ¬ ((0 : Nat) > v + 1) := by omega
  simp only [wfAllTgen, bndTgen, isTermCodeB, cOk, consOk, varOkT, funcOkT, land, lor, In, lt,
    carc, cdrc, lenc, nthc, cons, nil, zero, substFormula, substTerm, substTerms,
    substTerm_numeralM, FOL.substTerm_lift_comm_zero, if_neg h1, if_neg h2,
    hT.subst, hTs.subst]

theorem hCl_Tsg (aT aTs : Term → Term) (hT : Nat1 aT) (hTs : Nat1 aTs) :
    ∀ (k : Nat) (q : Term),
      liftFormula k (wfAllTsgen aT aTs q) = wfAllTsgen aT aTs (liftTerm k q) := by
  intro k q
  simp only [wfAllTsgen, bndTsgen, isTermsCodeB, cOk, consOk, land, lor, In, lt,
    carc, cdrc, lenc, nthc, cons, nil, zero, liftFormula, liftTerm, liftTerms,
    liftTerm_numeralM, if_pos (Nat.zero_lt_succ k), ← FOL.liftTerm_comm_zero,
    hT.lift, hTs.lift]

theorem hCs_Tsg (aT aTs : Term → Term) (hT : Nat1 aT) (hTs : Nat1 aTs) :
    ∀ (v : Nat) (t q : Term),
      substFormula v t (wfAllTsgen aT aTs q) = wfAllTsgen aT aTs (substTerm v t q) := by
  intro v t q
  have h1 : ¬ ((0 : Nat) = v + 1) := by omega
  have h2 : ¬ ((0 : Nat) > v + 1) := by omega
  simp only [wfAllTsgen, bndTsgen, isTermsCodeB, cOk, consOk, land, lor, In, lt,
    carc, cdrc, lenc, nthc, cons, nil, zero, substFormula, substTerm, substTerms,
    substTerm_numeralM, FOL.substTerm_lift_comm_zero, if_neg h1, if_neg h2,
    hT.subst, hTs.subst]

/-- ⚠️ **CERO prueba nueva**: el `hbody` genérico ES el concreto de §11 con los accesores
    aplicados. Se comprueba abajo que `hbody_T` y `hbody_Tg carc cdrc` tienen el mismo tipo. -/
theorem hbody_Tg (aT aTs : Term → Term) : ∀ q i : Term,
    Prf (wfAllTgen aT aTs q ⇒ (lt i (bndTgen aT q)
      ⇒ provFromCode (substfc zero (tcFn i) (PsiTgen aT aTs q)))) := by
  intro q i
  refine prf_deduction (deduction_aux ?_ (lt i (bndTgen aT q)) [wfAllTgen aT aTs q] rfl)
  have hlt : PrfH [lt i (bndTgen aT q), wfAllTgen aT aTs q] (lt i (lenc (aT q))) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hwf : PrfH [lt i (bndTgen aT q), wfAllTgen aT aTs q] (wfAllTgen aT aTs q) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hsubst : substFormula 0 i (Formula.impl (lt (.var 0) (liftTerm 0 (bndTgen aT q)))
      (isTermCodeB (liftTerm 0 (aT q)) (liftTerm 0 (aTs q)) (nthc (liftTerm 0 (aT q)) (.var 0))))
      = Formula.impl (lt i (bndTgen aT q))
          (isTermCodeB (aT q) (aTs q) (nthc (aT q) i)) := by
    simp only [bndTgen, isTermCodeB, cOk, consOk, varOkT, funcOkT, land, lor, In, lt,
      carc, cdrc, lenc, nthc, cons, nil, zero, substFormula, substTerm, substTerms,
      substTerm_numeralM, FOL.substTerm_liftTerm, if_true]
  have h0 := PrfH.mp _ _ _ (PrfH.incl0 [lt i (bndTgen aT q), wfAllTgen aT aTs q] _
    (Prf₀.q1 (Formula.impl (lt (.var 0) (liftTerm 0 (bndTgen aT q)))
      (isTermCodeB (liftTerm 0 (aT q)) (liftTerm 0 (aTs q))
        (nthc (liftTerm 0 (aT q)) (.var 0)))) i)) hwf
  rw [hsubst] at h0
  have hnode := PrfH.mp _ _ _ h0 hlt
  have hpure := PrfH.mp _ _ _
    (prf_to_prfH (pcc_isTermCodeB_pure (aT q) (aTs q) (nthc (aT q) i)) _) hnode
  have hev := PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_nthc (aT q) i) _) hlt
  have hevS := PrfH_eq_symm_code _ _
    (substtc_inv_nthcT (substtc_inv_tcFn (aT q)) (substtc_inv_tcFn i)) hev
  have hCC : ∀ t : Term,
      Prf (substfc zero t (isTermCodeDot (tcFn (aT q)) (tcFn (aTs q)) (varc (numeral 0)))
        =eq isTermCodeDot (tcFn (aT q)) (tcFn (aTs q)) t) :=
    fun t => prf_substfc_isTermCodeDot_gen t (tcFn (aT q)) (tcFn (aTs q)) (varc (numeral 0)) t
      (substtc_inv_tcFn (aTs q)) (prf_substtc_varc0 t)
  have h1 := PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_eq_symm (hCC _))) _) hpure
  have h2 := PrfH_leibniz_apply _ _ _ hevS h1
  have h3 := PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hCC _)) _) h2
  exact PrfH.mp _ _ _
    (prf_to_prfH (prf_provCode_congr (prf_eq_symm (prf_substfc_PsiTgen aT aTs q (tcFn i)))) _) h3

theorem hbody_Tsg (aT aTs : Term → Term) : ∀ q i : Term,
    Prf (wfAllTsgen aT aTs q ⇒ (lt i (bndTsgen aTs q)
      ⇒ provFromCode (substfc zero (tcFn i) (PsiTsgen aT aTs q)))) := by
  intro q i
  refine prf_deduction (deduction_aux ?_ (lt i (bndTsgen aTs q)) [wfAllTsgen aT aTs q] rfl)
  have hlt : PrfH [lt i (bndTsgen aTs q), wfAllTsgen aT aTs q] (lt i (lenc (aTs q))) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hwf : PrfH [lt i (bndTsgen aTs q), wfAllTsgen aT aTs q] (wfAllTsgen aT aTs q) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hsubst : substFormula 0 i (Formula.impl (lt (.var 0) (liftTerm 0 (bndTsgen aTs q)))
      (isTermsCodeB (liftTerm 0 (aT q)) (liftTerm 0 (aTs q))
        (nthc (liftTerm 0 (aTs q)) (.var 0))))
      = Formula.impl (lt i (bndTsgen aTs q))
          (isTermsCodeB (aT q) (aTs q) (nthc (aTs q) i)) := by
    simp only [bndTsgen, isTermsCodeB, cOk, consOk, land, lor, In, lt,
      carc, cdrc, lenc, nthc, cons, nil, zero, substFormula, substTerm, substTerms,
      FOL.substTerm_liftTerm, if_true]
  have h0 := PrfH.mp _ _ _ (PrfH.incl0 [lt i (bndTsgen aTs q), wfAllTsgen aT aTs q] _
    (Prf₀.q1 (Formula.impl (lt (.var 0) (liftTerm 0 (bndTsgen aTs q)))
      (isTermsCodeB (liftTerm 0 (aT q)) (liftTerm 0 (aTs q))
        (nthc (liftTerm 0 (aTs q)) (.var 0)))) i)) hwf
  rw [hsubst] at h0
  have hnode := PrfH.mp _ _ _ h0 hlt
  have hpure := PrfH.mp _ _ _
    (prf_to_prfH (pcc_isTermsCodeB_pure (aT q) (aTs q) (nthc (aTs q) i)) _) hnode
  have hev := PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_nthc (aTs q) i) _) hlt
  have hevS := PrfH_eq_symm_code _ _
    (substtc_inv_nthcT (substtc_inv_tcFn (aTs q)) (substtc_inv_tcFn i)) hev
  have hCC : ∀ t : Term,
      Prf (substfc zero t (isTermsCodeDot (tcFn (aT q)) (tcFn (aTs q)) (varc (numeral 0)))
        =eq isTermsCodeDot (tcFn (aT q)) (tcFn (aTs q)) t) :=
    fun t => prf_substfc_isTermsCodeDot_gen t (tcFn (aT q)) (tcFn (aTs q)) (varc (numeral 0)) t
      (substtc_inv_tcFn (aT q)) (substtc_inv_tcFn (aTs q)) (prf_substtc_varc0 t)
  have h1 := PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_eq_symm (hCC _))) _) hpure
  have h2 := PrfH_leibniz_apply _ _ _ hevS h1
  have h3 := PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hCC _)) _) h2
  exact PrfH.mp _ _ _
    (prf_to_prfH (prf_provCode_congr (prf_eq_symm (prf_substfc_PsiTsgen aT aTs q (tcFn i)))) _) h3

theorem pcc_wfAllTgen_tracked (aT aTs : Term → Term) (hT : Nat1 aT) (hTs : Nat1 aTs) (p : Term) :
    Prf (wfAllTgen aT aTs p ⇒
      provFromCode (bdAllCode (tcFn (bndTgen aT p)) (PsiTgen aT aTs p))) :=
  pcc_bdAll_intro (wfAllTgen aT aTs) (bndTgen aT) (PsiTgen aT aTs) p
    (hCl_Tg aT aTs hT hTs) (hCs_Tg aT aTs hT hTs) (hbl_Tg aT hT) (hbs_Tg aT hT)
    (hPl_Tg aT aTs hT hTs) (hPs_Tg aT aTs hT hTs)
    (fun q => prf_substfc_PsiTgen aT aTs q (varc (numeral 0))) (hbody_Tg aT aTs)

theorem pcc_wfAllTsgen_tracked (aT aTs : Term → Term) (hT : Nat1 aT) (hTs : Nat1 aTs) (p : Term) :
    Prf (wfAllTsgen aT aTs p ⇒
      provFromCode (bdAllCode (tcFn (bndTsgen aTs p)) (PsiTsgen aT aTs p))) :=
  pcc_bdAll_intro (wfAllTsgen aT aTs) (bndTsgen aTs) (PsiTsgen aT aTs) p
    (hCl_Tsg aT aTs hT hTs) (hCs_Tsg aT aTs hT hTs) (hbl_Tsg aTs hTs) (hbs_Tsg aTs hTs)
    (hPl_Tsg aT aTs hT hTs) (hPs_Tsg aT aTs hT hTs)
    (fun q => prf_substfc_PsiTsgen aT aTs q (varc (numeral 0))) (hbody_Tsg aT aTs)

/-! ### La TERNA: `p = ⟨wF, wT, wTs⟩` con `carc`, `carc∘cdrc`, `cdrc∘cdrc` -/

def acF  : Term → Term := carc
def acT  : Term → Term := fun p => carc (cdrc p)
def acTs : Term → Term := fun p => cdrc (cdrc p)

theorem nat1_acF : Nat1 acF :=
  ⟨fun k q => by simp only [acF, carc, liftTerm, liftTerms],
   fun v t q => by simp only [acF, carc, substTerm, substTerms]⟩

theorem nat1_acT : Nat1 acT :=
  ⟨fun k q => by simp only [acT, carc, cdrc, liftTerm, liftTerms],
   fun v t q => by simp only [acT, carc, cdrc, substTerm, substTerms]⟩

theorem nat1_acTs : Nat1 acTs :=
  ⟨fun k q => by simp only [acTs, cdrc, liftTerm, liftTerms],
   fun v t q => by simp only [acTs, cdrc, substTerm, substTerms]⟩

/-- Buena formación COMPLETA de la terna: las tres familias sobre EL MISMO paquete. -/
def tripleOk (p : Term) : Formula :=
  land (wfAllF acF acT acTs p)
       (land (wfAllTgen acT acTs p) (wfAllTsgen acT acTs p))

/-- El testigo completo: `c` es código de FÓRMULA con testigo `p`. -/
def isFCB3 (p c : Term) : Formula := land (tripleOk p) (In c (acF p))

noncomputable def tripleOkDot (p : Term) : Term :=
  andc (bdAllCode (tcFn (bndFF acF p)) (PsiFF acF acT acTs p))
    (andc (bdAllCode (tcFn (bndTgen acT p)) (PsiTgen acT acTs p))
          (bdAllCode (tcFn (bndTsgen acTs p)) (PsiTsgen acT acTs p)))

noncomputable def isFCB3Dot (p c : Term) : Term :=
  andc (tripleOkDot p) (inFormCodeFn (tcFn c) (tcFn (acF p)))

/-- **EL REFLECTOR DE LA PARTICIÓN COMPLETA** (3 predicados, 3 listas testigo, 1 paquete),
    con `p` y `c` ABSTRACTOS. -/
theorem pcc_isFCB3_tracked (p c : Term) : Prf (isFCB3 p c ⇒ provFromCode (isFCB3Dot p c)) := by
  refine prf_deduction ?_
  have h := prfH_hyp_self (isFCB3 p c)
  have htr := PrfH_and_elim_left h
  have hTT := PrfH_and_elim_right htr
  exact PrfH_and_intro_code _ _
    (PrfH_and_intro_code _ _
      (PrfH.mp _ _ _ (prf_to_prfH (pcc_wfAllF_tracked acF acT acTs
        nat1_acF nat1_acT nat1_acTs p) _) (PrfH_and_elim_left htr))
      (PrfH_and_intro_code _ _
        (PrfH.mp _ _ _ (prf_to_prfH (pcc_wfAllTgen_tracked acT acTs
          nat1_acT nat1_acTs p) _) (PrfH_and_elim_left hTT))
        (PrfH.mp _ _ _ (prf_to_prfH (pcc_wfAllTsgen_tracked acT acTs
          nat1_acT nat1_acTs p) _) (PrfH_and_elim_right hTT))))
    (PrfH.mp _ _ _ (prf_to_prfH (pcc_In_atom_tracked c (acF p)) _) (PrfH_and_elim_right h))

/-! ## 18 · LOS REFLECTORES DEL PAR, por INSTANCIACIÓN del genérico

    Aquí se cobra el diseño de §17: los reflectores del par salen de UNA línea cada uno,
    porque `wfAllT = wfAllTgen carc cdrc`, `bndT = bndTgen carc` y `PsiT = PsiTgen carc cdrc`
    son `rfl`. Las 8 obligaciones + `hbody` ya no se vuelven a probar. -/

theorem pcc_wfAllT_tracked (p : Term) :
    Prf (wfAllT p ⇒ provFromCode (bdAllCode (tcFn (bndT p)) (PsiT p))) :=
  pcc_wfAllTgen_tracked carc cdrc nat1_carc nat1_cdrc p

theorem pcc_wfAllTs_tracked (p : Term) :
    Prf (wfAllTs p ⇒ provFromCode (bdAllCode (tcFn (bndTs p)) (PsiTs p))) :=
  pcc_wfAllTsgen_tracked carc cdrc nat1_carc nat1_cdrc p

/-- **EL REFLECTOR DEL PAR**, con `p` y `c` **ABSTRACTOS**. -/
theorem pcc_isTCB_tracked (p c : Term) : Prf (isTCB p c ⇒ provFromCode (isTCBDot p c)) := by
  refine prf_deduction ?_
  have h := prfH_hyp_self (isTCB p c)
  have hpair := PrfH_and_elim_left h
  exact PrfH_and_intro_code _ _
    (PrfH_and_intro_code _ _
      (PrfH.mp _ _ _ (prf_to_prfH (pcc_wfAllT_tracked p) _) (PrfH_and_elim_left hpair))
      (PrfH.mp _ _ _ (prf_to_prfH (pcc_wfAllTs_tracked p) _) (PrfH_and_elim_right hpair)))
    (PrfH.mp _ _ _ (prf_to_prfH (pcc_In_atom_tracked c (carc p)) _) (PrfH_and_elim_right h))

/-- Gemelo para la mitad de LISTAS. -/
theorem pcc_isTsCB_tracked (p c : Term) : Prf (isTsCB p c ⇒ provFromCode (isTsCBDot p c)) := by
  refine prf_deduction ?_
  have h := prfH_hyp_self (isTsCB p c)
  have hpair := PrfH_and_elim_left h
  exact PrfH_and_intro_code _ _
    (PrfH_and_intro_code _ _
      (PrfH.mp _ _ _ (prf_to_prfH (pcc_wfAllT_tracked p) _) (PrfH_and_elim_left hpair))
      (PrfH.mp _ _ _ (prf_to_prfH (pcc_wfAllTs_tracked p) _) (PrfH_and_elim_right hpair)))
    (PrfH.mp _ _ _ (prf_to_prfH (pcc_In_atom_tracked c (cdrc p)) _) (PrfH_and_elim_right h))
/-! ## 18b · NO VACUIDAD del PAR, extremo a extremo: hito (i) COMPUESTO con el reflector -/

/-- `⊢ Prov(⌜ isTCB(par(t), ⌜t⌝ₜ) ⌝)` para todo término `t` **meta**. -/
theorem pcc_isTCB_subCodesT (t : Term) :
    Prf (provFromCode (isTCBDot (pairT t) (termCodeM t))) :=
  prf_mp (pcc_isTCB_tracked (pairT t) (termCodeM t)) (prf_isTCB_subCodesT t)

theorem pcc_isTsCB_subCodesTs (ts : List Term) :
    Prf (provFromCode (isTsCBDot (pairTs ts) (termsCodeM ts))) :=
  prf_mp (pcc_isTsCB_tracked (pairTs ts) (termsCodeM ts)) (prf_isTsCB_subCodesTs ts)

/-! # ═══════════════════════════════════════════════════════════════════════════
    ## 19 · HITO (i) PARA LA TERNA — el testigo de FÓRMULAS, y la NO VACUIDAD
    ═══════════════════════════════════════════════════════════════════════════

    ⚠️ Éste es el control que A3 se saltó y que mató a 2 de sus 4 intentos: un reflector
    puede ser **verdadero y VACÍO** si el antecedente objeto no tiene testigos reales.
    Aquí se construye el testigo explícito de toda `φ` y se compone con §17. -/

theorem prf_cOk_nulOkF :
    Prf (cOk (cons (numeralM 2) nil) (nulOkF (cons (numeralM 2) nil))) :=
  prf_and_intro (prf_consOk_cons _ _)
    (prf_and_intro (prf_carc_cons (numeralM 2) nil) (prf_lenc_c1 (numeralM 2)))

theorem prf_cOk_unOkF (w : Term) (k : Nat) (A : Term) (hA : Prf (In A w)) :
    Prf (cOk (cons (numeralM k) (cons A nil))
             (unOkF w (cons (numeralM k) (cons A nil)) k)) :=
  prf_and_intro (prf_consOk_cons _ _)
    (prf_and_intro
      (prf_and_intro (prf_carc_cons (numeralM k) (cons A nil)) (prf_lenc_c2 (numeralM k) A))
      (prf_congr_In_left (prf_eq_symm (prf_nthc_c1 (numeralM k) A nil)) hA))

theorem prf_cOk_binOkF (wA wB : Term) (k : Nat) (A B : Term)
    (hA : Prf (In A wA)) (hB : Prf (In B wB)) :
    Prf (cOk (cons (numeralM k) (cons A (cons B nil)))
             (binOkF wA wB (cons (numeralM k) (cons A (cons B nil))) k)) :=
  prf_and_intro (prf_consOk_cons _ _)
    (prf_and_intro
      (prf_and_intro (prf_carc_cons (numeralM k) (cons A (cons B nil)))
        (prf_lenc_c3 (numeralM k) A B))
      (prf_and_intro
        (prf_congr_In_left (prf_eq_symm (prf_nthc_c1 (numeralM k) A (cons B nil))) hA)
        (prf_congr_In_left (prf_eq_symm (prf_nthc_c2 (numeralM k) A B nil)) hB)))

theorem prf_cOk_strBinOkF (w : Term) (k : Nat) (S C : Term) (hC : Prf (In C w)) :
    Prf (cOk (cons (numeralM k) (cons S (cons C nil)))
             (strBinOkF w (cons (numeralM k) (cons S (cons C nil))) k)) :=
  prf_and_intro (prf_consOk_cons _ _)
    (prf_and_intro
      (prf_and_intro (prf_carc_cons (numeralM k) (cons S (cons C nil)))
        (prf_lenc_c3 (numeralM k) S C))
      (prf_congr_In_left (prf_eq_symm (prf_nthc_c2 (numeralM k) S C nil)) hC))

theorem prf_lorAll_head : ∀ (a : Formula) (bs : List Formula), Prf a → Prf (lorAll a bs)
  | _, [],     h => h
  | _, _ :: _, h => prf_orL h

theorem prf_lorAll_tail (a b : Formula) (bs : List Formula) (h : Prf (lorAll b bs)) :
    Prf (lorAll a (b :: bs)) := prf_orR h

theorem isFC_i0 (wF wT wTs X : Term) (h : Prf (cOk X (nulOkF X))) :
    Prf (isFormCodeB wF wT wTs X) := prf_lorAll_head _ _ h
theorem isFC_i1 (wF wT wTs X : Term) (h : Prf (cOk X (strBinOkF wTs X 3))) :
    Prf (isFormCodeB wF wT wTs X) := prf_lorAll_tail _ _ _ (prf_lorAll_head _ _ h)
theorem isFC_i2 (wF wT wTs X : Term) (h : Prf (cOk X (binOkF wT wT X 4))) :
    Prf (isFormCodeB wF wT wTs X) :=
  prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _ (prf_lorAll_head _ _ h))
theorem isFC_i3 (wF wT wTs X : Term) (h : Prf (cOk X (binOkF wF wF X 5))) :
    Prf (isFormCodeB wF wT wTs X) :=
  prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _ (prf_lorAll_head _ _ h)))
theorem isFC_i4 (wF wT wTs X : Term) (h : Prf (cOk X (unOkF wF X 6))) :
    Prf (isFormCodeB wF wT wTs X) :=
  prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _
    (prf_lorAll_tail _ _ _ (prf_lorAll_head _ _ h))))
theorem isFC_i5 (wF wT wTs X : Term) (h : Prf (cOk X (binOkF wF wF X 7))) :
    Prf (isFormCodeB wF wT wTs X) :=
  prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _
    (prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _ (prf_lorAll_head _ _ h)))))
theorem isFC_i6 (wF wT wTs X : Term) (h : Prf (cOk X (binOkF wF wF X 8))) :
    Prf (isFormCodeB wF wT wTs X) :=
  prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _
    (prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _
      (prf_lorAll_head _ _ h))))))
theorem isFC_i7 (wF wT wTs X : Term) (h : Prf (cOk X (unOkF wF X 9))) :
    Prf (isFormCodeB wF wT wTs X) :=
  prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _
    (prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _ (prf_lorAll_tail _ _ _
      (prf_lorAll_tail _ _ _ (prf_lorAll_head _ _ h)))))))

/-! ### Los TRES colectores sobre `Formula` -/

def fcodes : Formula → List Term
  | .bottom          => [formCodeM Formula.bottom]
  | .atom p ts       => [formCodeM (.atom p ts)]
  | .eq t u          => [formCodeM (.eq t u)]
  | .impl a b        => formCodeM (.impl a b) :: (fcodes a ++ fcodes b)
  | Formula.forall a => formCodeM (Formula.forall a) :: fcodes a
  | .and a b         => formCodeM (.and a b) :: (fcodes a ++ fcodes b)
  | .or a b          => formCodeM (.or a b) :: (fcodes a ++ fcodes b)
  | .ex a            => formCodeM (.ex a) :: fcodes a

def ftcodes : Formula → List Term
  | .bottom          => []
  | .atom _ ts       => tcodesTs ts
  | .eq t u          => tcodesT t ++ tcodesT u
  | .impl a b        => ftcodes a ++ ftcodes b
  | Formula.forall a => ftcodes a
  | .and a b         => ftcodes a ++ ftcodes b
  | .or a b          => ftcodes a ++ ftcodes b
  | .ex a            => ftcodes a

def flcodes : Formula → List Term
  | .bottom          => []
  | .atom _ ts       => lcodesTs ts
  | .eq t u          => lcodesT t ++ lcodesT u
  | .impl a b        => flcodes a ++ flcodes b
  | Formula.forall a => flcodes a
  | .and a b         => flcodes a ++ flcodes b
  | .or a b          => flcodes a ++ flcodes b
  | .ex a            => flcodes a

theorem mem_self_fcodes (φ : Formula) : List.Mem (formCodeM φ) (fcodes φ) := by
  cases φ <;> (simp only [fcodes]; exact List.Mem.head _)

theorem closed_formCodeM (φ : Formula) : CodeClosed (formCodeM φ) :=
  ⟨fun c => liftTerm_formCodeM c φ, fun v s => substTerm_formCodeM v s φ⟩

theorem closed_mem_fcodes : ∀ (φ : Formula) (x : Term), List.Mem x (fcodes φ) → CodeClosed x
  | .bottom, x, h => by
      simp only [fcodes] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_formCodeM Formula.bottom
      · cases h'
  | .atom p ts, x, h => by
      simp only [fcodes] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_formCodeM (.atom p ts)
      · cases h'
  | .eq t u, x, h => by
      simp only [fcodes] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_formCodeM (.eq t u)
      · cases h'
  | .impl a b, x, h => by
      simp only [fcodes] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_formCodeM (.impl a b)
      · rcases List.mem_append.mp h' with hA | hB
        · exact closed_mem_fcodes a x hA
        · exact closed_mem_fcodes b x hB
  | Formula.forall a, x, h => by
      simp only [fcodes] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_formCodeM (Formula.forall a)
      · exact closed_mem_fcodes a x h'
  | .and a b, x, h => by
      simp only [fcodes] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_formCodeM (.and a b)
      · rcases List.mem_append.mp h' with hA | hB
        · exact closed_mem_fcodes a x hA
        · exact closed_mem_fcodes b x hB
  | .or a b, x, h => by
      simp only [fcodes] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_formCodeM (.or a b)
      · rcases List.mem_append.mp h' with hA | hB
        · exact closed_mem_fcodes a x hA
        · exact closed_mem_fcodes b x hB
  | .ex a, x, h => by
      simp only [fcodes] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_formCodeM (.ex a)
      · exact closed_mem_fcodes a x h'

theorem closed_mem_ftcodes : ∀ (φ : Formula) (x : Term), List.Mem x (ftcodes φ) → CodeClosed x
  | .bottom, x, h => by simp only [ftcodes] at h; cases h
  | .atom p ts, x, h => by simp only [ftcodes] at h; exact closed_mem_tcodesTs ts x h
  | .eq t u, x, h => by
      simp only [ftcodes] at h
      rcases List.mem_append.mp h with hA | hB
      · exact closed_mem_tcodesT t x hA
      · exact closed_mem_tcodesT u x hB
  | .impl a b, x, h => by
      simp only [ftcodes] at h
      rcases List.mem_append.mp h with hA | hB
      · exact closed_mem_ftcodes a x hA
      · exact closed_mem_ftcodes b x hB
  | Formula.forall a, x, h => by simp only [ftcodes] at h; exact closed_mem_ftcodes a x h
  | .and a b, x, h => by
      simp only [ftcodes] at h
      rcases List.mem_append.mp h with hA | hB
      · exact closed_mem_ftcodes a x hA
      · exact closed_mem_ftcodes b x hB
  | .or a b, x, h => by
      simp only [ftcodes] at h
      rcases List.mem_append.mp h with hA | hB
      · exact closed_mem_ftcodes a x hA
      · exact closed_mem_ftcodes b x hB
  | .ex a, x, h => by simp only [ftcodes] at h; exact closed_mem_ftcodes a x h

theorem closed_mem_flcodes : ∀ (φ : Formula) (x : Term), List.Mem x (flcodes φ) → CodeClosed x
  | .bottom, x, h => by simp only [flcodes] at h; cases h
  | .atom p ts, x, h => by simp only [flcodes] at h; exact closed_mem_lcodesTs ts x h
  | .eq t u, x, h => by
      simp only [flcodes] at h
      rcases List.mem_append.mp h with hA | hB
      · exact closed_mem_lcodesT t x hA
      · exact closed_mem_lcodesT u x hB
  | .impl a b, x, h => by
      simp only [flcodes] at h
      rcases List.mem_append.mp h with hA | hB
      · exact closed_mem_flcodes a x hA
      · exact closed_mem_flcodes b x hB
  | Formula.forall a, x, h => by simp only [flcodes] at h; exact closed_mem_flcodes a x h
  | .and a b, x, h => by
      simp only [flcodes] at h
      rcases List.mem_append.mp h with hA | hB
      · exact closed_mem_flcodes a x hA
      · exact closed_mem_flcodes b x hB
  | .or a b, x, h => by
      simp only [flcodes] at h
      rcases List.mem_append.mp h with hA | hB
      · exact closed_mem_flcodes a x hA
      · exact closed_mem_flcodes b x hB
  | .ex a, x, h => by simp only [flcodes] at h; exact closed_mem_flcodes a x h

/-! ### Las TRES inducciones sobre `Formula` (los oráculos son TÉRMINOS abstractos) -/

theorem okT_ftcodes : ∀ (φ : Formula) (WT WTs : Term),
    (∀ y : Term, List.Mem y (ftcodes φ) → Prf (In y WT)) →
    (∀ y : Term, List.Mem y (flcodes φ) → Prf (In y WTs)) →
    ∀ x : Term, List.Mem x (ftcodes φ) → Prf (isTermCodeB WT WTs x)
  | .bottom, _, _, _, _, x, hx => by simp only [ftcodes] at hx; cases hx
  | .atom p ts, WT, WTs, hT, hTs, x, hx => by
      simp only [ftcodes] at hx
      exact okT_tcodesTs ts WT WTs (fun y hy => hT y (by simp only [ftcodes]; exact hy))
        (fun y hy => hTs y (by simp only [flcodes]; exact hy)) x hx
  | .eq t u, WT, WTs, hT, hTs, x, hx => by
      simp only [ftcodes] at hx
      rcases List.mem_append.mp hx with hA | hB
      · exact okT_tcodesT t WT WTs
          (fun y hy => hT y (by simp only [ftcodes]; exact List.mem_append.mpr (Or.inl hy)))
          (fun y hy => hTs y (by simp only [flcodes]; exact List.mem_append.mpr (Or.inl hy)))
          x hA
      · exact okT_tcodesT u WT WTs
          (fun y hy => hT y (by simp only [ftcodes]; exact List.mem_append.mpr (Or.inr hy)))
          (fun y hy => hTs y (by simp only [flcodes]; exact List.mem_append.mpr (Or.inr hy)))
          x hB
  | .impl a b, WT, WTs, hT, hTs, x, hx => by
      simp only [ftcodes] at hx
      rcases List.mem_append.mp hx with hA | hB
      · exact okT_ftcodes a WT WTs
          (fun y hy => hT y (by simp only [ftcodes]; exact List.mem_append.mpr (Or.inl hy)))
          (fun y hy => hTs y (by simp only [flcodes]; exact List.mem_append.mpr (Or.inl hy)))
          x hA
      · exact okT_ftcodes b WT WTs
          (fun y hy => hT y (by simp only [ftcodes]; exact List.mem_append.mpr (Or.inr hy)))
          (fun y hy => hTs y (by simp only [flcodes]; exact List.mem_append.mpr (Or.inr hy)))
          x hB
  | Formula.forall a, WT, WTs, hT, hTs, x, hx => by
      simp only [ftcodes] at hx
      exact okT_ftcodes a WT WTs (fun y hy => hT y (by simp only [ftcodes]; exact hy))
        (fun y hy => hTs y (by simp only [flcodes]; exact hy)) x hx
  | .and a b, WT, WTs, hT, hTs, x, hx => by
      simp only [ftcodes] at hx
      rcases List.mem_append.mp hx with hA | hB
      · exact okT_ftcodes a WT WTs
          (fun y hy => hT y (by simp only [ftcodes]; exact List.mem_append.mpr (Or.inl hy)))
          (fun y hy => hTs y (by simp only [flcodes]; exact List.mem_append.mpr (Or.inl hy)))
          x hA
      · exact okT_ftcodes b WT WTs
          (fun y hy => hT y (by simp only [ftcodes]; exact List.mem_append.mpr (Or.inr hy)))
          (fun y hy => hTs y (by simp only [flcodes]; exact List.mem_append.mpr (Or.inr hy)))
          x hB
  | .or a b, WT, WTs, hT, hTs, x, hx => by
      simp only [ftcodes] at hx
      rcases List.mem_append.mp hx with hA | hB
      · exact okT_ftcodes a WT WTs
          (fun y hy => hT y (by simp only [ftcodes]; exact List.mem_append.mpr (Or.inl hy)))
          (fun y hy => hTs y (by simp only [flcodes]; exact List.mem_append.mpr (Or.inl hy)))
          x hA
      · exact okT_ftcodes b WT WTs
          (fun y hy => hT y (by simp only [ftcodes]; exact List.mem_append.mpr (Or.inr hy)))
          (fun y hy => hTs y (by simp only [flcodes]; exact List.mem_append.mpr (Or.inr hy)))
          x hB
  | .ex a, WT, WTs, hT, hTs, x, hx => by
      simp only [ftcodes] at hx
      exact okT_ftcodes a WT WTs (fun y hy => hT y (by simp only [ftcodes]; exact hy))
        (fun y hy => hTs y (by simp only [flcodes]; exact hy)) x hx

theorem okTs_flcodes : ∀ (φ : Formula) (WT WTs : Term),
    (∀ y : Term, List.Mem y (ftcodes φ) → Prf (In y WT)) →
    (∀ y : Term, List.Mem y (flcodes φ) → Prf (In y WTs)) →
    ∀ x : Term, List.Mem x (flcodes φ) → Prf (isTermsCodeB WT WTs x)
  | .bottom, _, _, _, _, x, hx => by simp only [flcodes] at hx; cases hx
  | .atom p ts, WT, WTs, hT, hTs, x, hx => by
      simp only [flcodes] at hx
      exact okTs_lcodesTs ts WT WTs (fun y hy => hT y (by simp only [ftcodes]; exact hy))
        (fun y hy => hTs y (by simp only [flcodes]; exact hy)) x hx
  | .eq t u, WT, WTs, hT, hTs, x, hx => by
      simp only [flcodes] at hx
      rcases List.mem_append.mp hx with hA | hB
      · exact okTs_lcodesT t WT WTs
          (fun y hy => hT y (by simp only [ftcodes]; exact List.mem_append.mpr (Or.inl hy)))
          (fun y hy => hTs y (by simp only [flcodes]; exact List.mem_append.mpr (Or.inl hy)))
          x hA
      · exact okTs_lcodesT u WT WTs
          (fun y hy => hT y (by simp only [ftcodes]; exact List.mem_append.mpr (Or.inr hy)))
          (fun y hy => hTs y (by simp only [flcodes]; exact List.mem_append.mpr (Or.inr hy)))
          x hB
  | .impl a b, WT, WTs, hT, hTs, x, hx => by
      simp only [flcodes] at hx
      rcases List.mem_append.mp hx with hA | hB
      · exact okTs_flcodes a WT WTs
          (fun y hy => hT y (by simp only [ftcodes]; exact List.mem_append.mpr (Or.inl hy)))
          (fun y hy => hTs y (by simp only [flcodes]; exact List.mem_append.mpr (Or.inl hy)))
          x hA
      · exact okTs_flcodes b WT WTs
          (fun y hy => hT y (by simp only [ftcodes]; exact List.mem_append.mpr (Or.inr hy)))
          (fun y hy => hTs y (by simp only [flcodes]; exact List.mem_append.mpr (Or.inr hy)))
          x hB
  | Formula.forall a, WT, WTs, hT, hTs, x, hx => by
      simp only [flcodes] at hx
      exact okTs_flcodes a WT WTs (fun y hy => hT y (by simp only [ftcodes]; exact hy))
        (fun y hy => hTs y (by simp only [flcodes]; exact hy)) x hx
  | .and a b, WT, WTs, hT, hTs, x, hx => by
      simp only [flcodes] at hx
      rcases List.mem_append.mp hx with hA | hB
      · exact okTs_flcodes a WT WTs
          (fun y hy => hT y (by simp only [ftcodes]; exact List.mem_append.mpr (Or.inl hy)))
          (fun y hy => hTs y (by simp only [flcodes]; exact List.mem_append.mpr (Or.inl hy)))
          x hA
      · exact okTs_flcodes b WT WTs
          (fun y hy => hT y (by simp only [ftcodes]; exact List.mem_append.mpr (Or.inr hy)))
          (fun y hy => hTs y (by simp only [flcodes]; exact List.mem_append.mpr (Or.inr hy)))
          x hB
  | .or a b, WT, WTs, hT, hTs, x, hx => by
      simp only [flcodes] at hx
      rcases List.mem_append.mp hx with hA | hB
      · exact okTs_flcodes a WT WTs
          (fun y hy => hT y (by simp only [ftcodes]; exact List.mem_append.mpr (Or.inl hy)))
          (fun y hy => hTs y (by simp only [flcodes]; exact List.mem_append.mpr (Or.inl hy)))
          x hA
      · exact okTs_flcodes b WT WTs
          (fun y hy => hT y (by simp only [ftcodes]; exact List.mem_append.mpr (Or.inr hy)))
          (fun y hy => hTs y (by simp only [flcodes]; exact List.mem_append.mpr (Or.inr hy)))
          x hB
  | .ex a, WT, WTs, hT, hTs, x, hx => by
      simp only [flcodes] at hx
      exact okTs_flcodes a WT WTs (fun y hy => hT y (by simp only [ftcodes]; exact hy))
        (fun y hy => hTs y (by simp only [flcodes]; exact hy)) x hx

theorem okF_fcodes : ∀ (φ : Formula) (WF WT WTs : Term),
    (∀ y : Term, List.Mem y (fcodes φ) → Prf (In y WF)) →
    (∀ y : Term, List.Mem y (ftcodes φ) → Prf (In y WT)) →
    (∀ y : Term, List.Mem y (flcodes φ) → Prf (In y WTs)) →
    ∀ x : Term, List.Mem x (fcodes φ) → Prf (isFormCodeB WF WT WTs x)
  | .bottom, WF, WT, WTs, _, _, _, x, hx => by
      simp only [fcodes] at hx
      rcases List.mem_cons.mp hx with rfl | h'
      · exact isFC_i0 _ _ _ _ prf_cOk_nulOkF
      · cases h'
  | .atom p ts, WF, WT, WTs, _, _, hTs, x, hx => by
      have hmem : Prf (In (termsCodeM ts) WTs) :=
        hTs _ (by simp only [flcodes]; exact mem_self_lcodesTs ts)
      simp only [fcodes] at hx
      rcases List.mem_cons.mp hx with rfl | h'
      · exact isFC_i1 _ _ _ _ (prf_cOk_strBinOkF WTs 3 (strCodeM p) (termsCodeM ts) hmem)
      · cases h'
  | .eq t u, WF, WT, WTs, _, hT, _, x, hx => by
      have h1 : Prf (In (termCodeM t) WT) :=
        hT _ (by simp only [ftcodes]; exact List.mem_append.mpr (Or.inl (mem_self_tcodesT t)))
      have h2 : Prf (In (termCodeM u) WT) :=
        hT _ (by simp only [ftcodes]; exact List.mem_append.mpr (Or.inr (mem_self_tcodesT u)))
      simp only [fcodes] at hx
      rcases List.mem_cons.mp hx with rfl | h'
      · exact isFC_i2 _ _ _ _ (prf_cOk_binOkF WT WT 4 (termCodeM t) (termCodeM u) h1 h2)
      · cases h'
  | .impl a b, WF, WT, WTs, hF, hT, hTs, x, hx => by
      have ha : Prf (In (formCodeM a) WF) :=
        hF _ (by simp only [fcodes]
                 exact List.Mem.tail _ (List.mem_append.mpr (Or.inl (mem_self_fcodes a))))
      have hb : Prf (In (formCodeM b) WF) :=
        hF _ (by simp only [fcodes]
                 exact List.Mem.tail _ (List.mem_append.mpr (Or.inr (mem_self_fcodes b))))
      simp only [fcodes] at hx
      rcases List.mem_cons.mp hx with rfl | h'
      · exact isFC_i3 _ _ _ _ (prf_cOk_binOkF WF WF 5 (formCodeM a) (formCodeM b) ha hb)
      · rcases List.mem_append.mp h' with hA | hB
        · exact okF_fcodes a WF WT WTs
            (fun y hy => hF y (by simp only [fcodes]
                                  exact List.Mem.tail _ (List.mem_append.mpr (Or.inl hy))))
            (fun y hy => hT y (by simp only [ftcodes]; exact List.mem_append.mpr (Or.inl hy)))
            (fun y hy => hTs y (by simp only [flcodes]; exact List.mem_append.mpr (Or.inl hy)))
            x hA
        · exact okF_fcodes b WF WT WTs
            (fun y hy => hF y (by simp only [fcodes]
                                  exact List.Mem.tail _ (List.mem_append.mpr (Or.inr hy))))
            (fun y hy => hT y (by simp only [ftcodes]; exact List.mem_append.mpr (Or.inr hy)))
            (fun y hy => hTs y (by simp only [flcodes]; exact List.mem_append.mpr (Or.inr hy)))
            x hB
  | Formula.forall a, WF, WT, WTs, hF, hT, hTs, x, hx => by
      have ha : Prf (In (formCodeM a) WF) :=
        hF _ (by simp only [fcodes]; exact List.Mem.tail _ (mem_self_fcodes a))
      simp only [fcodes] at hx
      rcases List.mem_cons.mp hx with rfl | h'
      · exact isFC_i4 _ _ _ _ (prf_cOk_unOkF WF 6 (formCodeM a) ha)
      · exact okF_fcodes a WF WT WTs
          (fun y hy => hF y (by simp only [fcodes]; exact List.Mem.tail _ hy))
          (fun y hy => hT y (by simp only [ftcodes]; exact hy))
          (fun y hy => hTs y (by simp only [flcodes]; exact hy)) x h'
  | .and a b, WF, WT, WTs, hF, hT, hTs, x, hx => by
      have ha : Prf (In (formCodeM a) WF) :=
        hF _ (by simp only [fcodes]
                 exact List.Mem.tail _ (List.mem_append.mpr (Or.inl (mem_self_fcodes a))))
      have hb : Prf (In (formCodeM b) WF) :=
        hF _ (by simp only [fcodes]
                 exact List.Mem.tail _ (List.mem_append.mpr (Or.inr (mem_self_fcodes b))))
      simp only [fcodes] at hx
      rcases List.mem_cons.mp hx with rfl | h'
      · exact isFC_i5 _ _ _ _ (prf_cOk_binOkF WF WF 7 (formCodeM a) (formCodeM b) ha hb)
      · rcases List.mem_append.mp h' with hA | hB
        · exact okF_fcodes a WF WT WTs
            (fun y hy => hF y (by simp only [fcodes]
                                  exact List.Mem.tail _ (List.mem_append.mpr (Or.inl hy))))
            (fun y hy => hT y (by simp only [ftcodes]; exact List.mem_append.mpr (Or.inl hy)))
            (fun y hy => hTs y (by simp only [flcodes]; exact List.mem_append.mpr (Or.inl hy)))
            x hA
        · exact okF_fcodes b WF WT WTs
            (fun y hy => hF y (by simp only [fcodes]
                                  exact List.Mem.tail _ (List.mem_append.mpr (Or.inr hy))))
            (fun y hy => hT y (by simp only [ftcodes]; exact List.mem_append.mpr (Or.inr hy)))
            (fun y hy => hTs y (by simp only [flcodes]; exact List.mem_append.mpr (Or.inr hy)))
            x hB
  | .or a b, WF, WT, WTs, hF, hT, hTs, x, hx => by
      have ha : Prf (In (formCodeM a) WF) :=
        hF _ (by simp only [fcodes]
                 exact List.Mem.tail _ (List.mem_append.mpr (Or.inl (mem_self_fcodes a))))
      have hb : Prf (In (formCodeM b) WF) :=
        hF _ (by simp only [fcodes]
                 exact List.Mem.tail _ (List.mem_append.mpr (Or.inr (mem_self_fcodes b))))
      simp only [fcodes] at hx
      rcases List.mem_cons.mp hx with rfl | h'
      · exact isFC_i6 _ _ _ _ (prf_cOk_binOkF WF WF 8 (formCodeM a) (formCodeM b) ha hb)
      · rcases List.mem_append.mp h' with hA | hB
        · exact okF_fcodes a WF WT WTs
            (fun y hy => hF y (by simp only [fcodes]
                                  exact List.Mem.tail _ (List.mem_append.mpr (Or.inl hy))))
            (fun y hy => hT y (by simp only [ftcodes]; exact List.mem_append.mpr (Or.inl hy)))
            (fun y hy => hTs y (by simp only [flcodes]; exact List.mem_append.mpr (Or.inl hy)))
            x hA
        · exact okF_fcodes b WF WT WTs
            (fun y hy => hF y (by simp only [fcodes]
                                  exact List.Mem.tail _ (List.mem_append.mpr (Or.inr hy))))
            (fun y hy => hT y (by simp only [ftcodes]; exact List.mem_append.mpr (Or.inr hy)))
            (fun y hy => hTs y (by simp only [flcodes]; exact List.mem_append.mpr (Or.inr hy)))
            x hB
  | .ex a, WF, WT, WTs, hF, hT, hTs, x, hx => by
      have ha : Prf (In (formCodeM a) WF) :=
        hF _ (by simp only [fcodes]; exact List.Mem.tail _ (mem_self_fcodes a))
      simp only [fcodes] at hx
      rcases List.mem_cons.mp hx with rfl | h'
      · exact isFC_i7 _ _ _ _ (prf_cOk_unOkF WF 9 (formCodeM a) ha)
      · exact okF_fcodes a WF WT WTs
          (fun y hy => hF y (by simp only [fcodes]; exact List.Mem.tail _ hy))
          (fun y hy => hT y (by simp only [ftcodes]; exact hy))
          (fun y hy => hTs y (by simp only [flcodes]; exact hy)) x h'

/-! ### El ensamblaje de la TERNA -/

theorem substF_isFormCodeB (v : Nat) (s A B C X : Term) :
    substFormula v s (isFormCodeB A B C X)
      = isFormCodeB (substTerm v s A) (substTerm v s B) (substTerm v s C) (substTerm v s X) := by
  simp only [isFormCodeB, lorAll, cOk, consOk, nulOkF, unOkF, binOkF, strBinOkF, land, lor, In,
    carc, cdrc, lenc, nthc, cons, nil, zero, substFormula, substTerm, substTerms,
    substTerm_numeralM]

theorem prf_congr_isFormCodeB {wF wT wTs X₁ X₂ : Term} (h : Prf (X₁ =eq X₂))
    (hN : Prf (isFormCodeB wF wT wTs X₁)) : Prf (isFormCodeB wF wT wTs X₂) := by
  let f : Formula := isFormCodeB (liftTerm 0 wF) (liftTerm 0 wT) (liftTerm 0 wTs) (.var 0)
  have hS : ∀ s : Term, substFormula 0 s f = isFormCodeB wF wT wTs s := by
    intro s
    simp only [f, substF_isFormCodeB, FOL.substTerm_liftTerm, substTerm, if_true]
  exact prfH_nil_to_prf
    ((hS X₂) ▸ PrfH_leibniz_subst (A := f) (prf_to_prfH h []) ((hS X₁) ▸ prf_to_prfH hN [])) rfl

theorem wfAllF_closed_at (p : Term) (h1 : liftTerm 0 (acF p) = acF p)
    (h2 : liftTerm 0 (acT p) = acT p) (h3 : liftTerm 0 (acTs p) = acTs p) :
    wfAllF acF acT acTs p = Formula.forall (Formula.impl (lt (.var 0) (bndFF acF p))
      (isFormCodeB (acF p) (acT p) (acTs p) (nthc (acF p) (.var 0)))) := by
  simp only [wfAllF, bndFF, lenc, nthc, liftTerm, liftTerms, h1, h2, h3]

theorem wfAllTgen_closed_at (aT aTs : Term → Term) (p : Term)
    (h1 : liftTerm 0 (aT p) = aT p) (h2 : liftTerm 0 (aTs p) = aTs p) :
    wfAllTgen aT aTs p = Formula.forall (Formula.impl (lt (.var 0) (bndTgen aT p))
      (isTermCodeB (aT p) (aTs p) (nthc (aT p) (.var 0)))) := by
  simp only [wfAllTgen, bndTgen, lenc, nthc, liftTerm, liftTerms, h1, h2]

theorem wfAllTsgen_closed_at (aT aTs : Term → Term) (p : Term)
    (h1 : liftTerm 0 (aT p) = aT p) (h2 : liftTerm 0 (aTs p) = aTs p) :
    wfAllTsgen aT aTs p = Formula.forall (Formula.impl (lt (.var 0) (bndTsgen aTs p))
      (isTermsCodeB (aT p) (aTs p) (nthc (aTs p) (.var 0)))) := by
  simp only [wfAllTsgen, bndTsgen, lenc, nthc, liftTerm, liftTerms, h1, h2]

theorem prf_tripleOk_gen (p : Term) (nF nT nTs : Nat)
    (hps : ∀ (v : Nat) (s : Term), substTerm v s p = p)
    (hpl : ∀ c : Nat, liftTerm c p = p)
    (hlF : Prf (Formula.eq (lenc (acF p)) (numeralM nF)))
    (hlT : Prf (Formula.eq (lenc (acT p)) (numeralM nT)))
    (hlTs : Prf (Formula.eq (lenc (acTs p)) (numeralM nTs)))
    (hnF : ∀ k : Nat, k < nF →
      Prf (isFormCodeB (acF p) (acT p) (acTs p) (nthc (acF p) (numeralM k))))
    (hnT : ∀ k : Nat, k < nT →
      Prf (isTermCodeB (acT p) (acTs p) (nthc (acT p) (numeralM k))))
    (hnTs : ∀ k : Nat, k < nTs →
      Prf (isTermsCodeB (acT p) (acTs p) (nthc (acTs p) (numeralM k)))) :
    Prf (tripleOk p) := by
  have e1 : ∀ (v : Nat) (s : Term), substTerm v s (acF p) = acF p := by
    intro v s; simp only [acF, carc, substTerm, substTerms, hps]
  have e2 : ∀ (v : Nat) (s : Term), substTerm v s (acT p) = acT p := by
    intro v s; simp only [acT, carc, cdrc, substTerm, substTerms, hps]
  have e3 : ∀ (v : Nat) (s : Term), substTerm v s (acTs p) = acTs p := by
    intro v s; simp only [acTs, cdrc, substTerm, substTerms, hps]
  have l1 : liftTerm 0 (acF p) = acF p := by simp only [acF, carc, liftTerm, liftTerms, hpl]
  have l2 : liftTerm 0 (acT p) = acT p := by
    simp only [acT, carc, cdrc, liftTerm, liftTerms, hpl]
  have l3 : liftTerm 0 (acTs p) = acTs p := by simp only [acTs, cdrc, liftTerm, liftTerms, hpl]
  refine prf_and_intro ?_ (prf_and_intro ?_ ?_)
  · rw [wfAllF_closed_at p l1 l2 l3]
    refine prf_bdAll_of_bound _ (bndFF acF p) nF ?_ hlF ?_
    · simp only [substF_isFormCodeB, nthc, substTerm, substTerms, e1, e2, e3, if_true]
    · intro k hk
      simpa only [substF_isFormCodeB, nthc, substTerm, substTerms, e1, e2, e3,
        substTerm_numeralM, if_true, reduceIte] using hnF k hk
  · rw [wfAllTgen_closed_at acT acTs p l2 l3]
    refine prf_bdAll_of_bound _ (bndTgen acT p) nT ?_ hlT ?_
    · simp only [substF_isTermCodeB, nthc, substTerm, substTerms, e2, e3, if_true]
    · intro k hk
      simpa only [substF_isTermCodeB, nthc, substTerm, substTerms, e2, e3,
        substTerm_numeralM, if_true, reduceIte] using hnT k hk
  · rw [wfAllTsgen_closed_at acT acTs p l2 l3]
    refine prf_bdAll_of_bound _ (bndTsgen acTs p) nTs ?_ hlTs ?_
    · simp only [substF_isTermsCodeB, nthc, substTerm, substTerms, e2, e3, if_true]
    · intro k hk
      simpa only [substF_isTermsCodeB, nthc, substTerm, substTerms, e2, e3,
        substTerm_numeralM, if_true, reduceIte] using hnTs k hk

theorem prf_congr_carc {t₁ t₂ : Term} (h : Prf (t₁ =eq t₂)) : Prf (carc t₁ =eq carc t₂) := by
  let f : Formula := Formula.eq (carc (liftTerm 0 t₁)) (carc (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (carc t₁) (carc s) := by
    intro s
    simp only [f, carc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact prfH_nil_to_prf
    ((hS t₂) ▸ PrfH_leibniz_subst (A := f) (prf_to_prfH h [])
      ((hS t₁) ▸ prf_to_prfH (prf_refl (carc t₁)) [])) rfl

theorem prf_congr_cdrc {t₁ t₂ : Term} (h : Prf (t₁ =eq t₂)) : Prf (cdrc t₁ =eq cdrc t₂) := by
  let f : Formula := Formula.eq (cdrc (liftTerm 0 t₁)) (cdrc (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (cdrc t₁) (cdrc s) := by
    intro s
    simp only [f, cdrc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact prfH_nil_to_prf
    ((hS t₂) ▸ PrfH_leibniz_subst (A := f) (prf_to_prfH h [])
      ((hS t₁) ▸ prf_to_prfH (prf_refl (cdrc t₁)) [])) rfl

/-- El paquete de TRES listas. -/
def tripleOf (LF LT LTs : List Term) : Term :=
  cons (objList LF) (cons (objList LT) (objList LTs))

def tripleF (φ : Formula) : Term := tripleOf (fcodes φ) (ftcodes φ) (flcodes φ)

/-- El ensamblaje genérico de la TERNA (⚠️ sin `let`: los `let` rompen el `simp only`
    porque el objetivo aparece zeta-expandido y las hipótesis no). -/
theorem prf_isFCB3_of (LF LT LTs : List Term) (c : Term)
    (hclF : ∀ x : Term, List.Mem x LF → CodeClosed x)
    (hclT : ∀ x : Term, List.Mem x LT → CodeClosed x)
    (hclTs : ∀ x : Term, List.Mem x LTs → CodeClosed x)
    (hc : List.Mem c LF)
    (hnF : ∀ WF WT WTs : Term,
      (∀ y : Term, List.Mem y LF → Prf (In y WF)) →
      (∀ y : Term, List.Mem y LT → Prf (In y WT)) →
      (∀ y : Term, List.Mem y LTs → Prf (In y WTs)) →
      ∀ x : Term, List.Mem x LF → Prf (isFormCodeB WF WT WTs x))
    (hnT : ∀ WT WTs : Term,
      (∀ y : Term, List.Mem y LT → Prf (In y WT)) →
      (∀ y : Term, List.Mem y LTs → Prf (In y WTs)) →
      ∀ x : Term, List.Mem x LT → Prf (isTermCodeB WT WTs x))
    (hnTs : ∀ WT WTs : Term,
      (∀ y : Term, List.Mem y LT → Prf (In y WT)) →
      (∀ y : Term, List.Mem y LTs → Prf (In y WTs)) →
      ∀ x : Term, List.Mem x LTs → Prf (isTermsCodeB WT WTs x)) :
    Prf (isFCB3 (tripleOf LF LT LTs) c) := by
  have hFl : ∀ k : Nat, liftTerm k (objList LF) = objList LF :=
    fun k => liftTerm_objList k LF (fun x hx => (hclF x hx).1 k)
  have hFs : ∀ (v : Nat) (s : Term), substTerm v s (objList LF) = objList LF :=
    fun v s => substTerm_objList v s LF (fun x hx => (hclF x hx).2 v s)
  have hTl : ∀ k : Nat, liftTerm k (objList LT) = objList LT :=
    fun k => liftTerm_objList k LT (fun x hx => (hclT x hx).1 k)
  have hTs2 : ∀ (v : Nat) (s : Term), substTerm v s (objList LT) = objList LT :=
    fun v s => substTerm_objList v s LT (fun x hx => (hclT x hx).2 v s)
  have hLl : ∀ k : Nat, liftTerm k (objList LTs) = objList LTs :=
    fun k => liftTerm_objList k LTs (fun x hx => (hclTs x hx).1 k)
  have hLs : ∀ (v : Nat) (s : Term), substTerm v s (objList LTs) = objList LTs :=
    fun v s => substTerm_objList v s LTs (fun x hx => (hclTs x hx).2 v s)
  have hpl : ∀ k : Nat, liftTerm k (tripleOf LF LT LTs) = tripleOf LF LT LTs := by
    intro k; simp only [tripleOf, cons, liftTerm, liftTerms, hFl, hTl, hLl]
  have hps : ∀ (v : Nat) (s : Term),
      substTerm v s (tripleOf LF LT LTs) = tripleOf LF LT LTs := by
    intro v s; simp only [tripleOf, cons, substTerm, substTerms, hFs, hTs2, hLs]
  -- las tres proyecciones del paquete
  have pF : Prf (acF (tripleOf LF LT LTs) =eq objList LF) := prf_carc_cons _ _
  have pcd : Prf (cdrc (tripleOf LF LT LTs) =eq cons (objList LT) (objList LTs)) :=
    prf_cdrc_cons _ _
  have pT : Prf (acT (tripleOf LF LT LTs) =eq objList LT) :=
    prf_eq_trans (prf_congr_carc pcd) (prf_carc_cons _ _)
  have pTs : Prf (acTs (tripleOf LF LT LTs) =eq objList LTs) :=
    prf_eq_trans (prf_congr_cdrc pcd) (prf_cdrc_cons _ _)
  -- los tres oráculos
  have oF : ∀ y : Term, List.Mem y LF → Prf (In y (acF (tripleOf LF LT LTs))) :=
    fun y hy => prf_congr_In_right (prf_eq_symm pF) (prf_In_objList LF y hy)
  have oT : ∀ y : Term, List.Mem y LT → Prf (In y (acT (tripleOf LF LT LTs))) :=
    fun y hy => prf_congr_In_right (prf_eq_symm pT) (prf_In_objList LT y hy)
  have oTs : ∀ y : Term, List.Mem y LTs → Prf (In y (acTs (tripleOf LF LT LTs))) :=
    fun y hy => prf_congr_In_right (prf_eq_symm pTs) (prf_In_objList LTs y hy)
  refine prf_and_intro (prf_tripleOk_gen (tripleOf LF LT LTs)
    LF.length LT.length LTs.length hps hpl
    (prf_eq_trans (prf_congr_lenc pF) (prf_lenc_objList LF))
    (prf_eq_trans (prf_congr_lenc pT) (prf_lenc_objList LT))
    (prf_eq_trans (prf_congr_lenc pTs) (prf_lenc_objList LTs)) ?_ ?_ ?_) (oF c hc)
  · intro k hk
    obtain ⟨x, hx⟩ : ∃ x, LF[k]? = some x := ⟨LF[k], getElem?_pos LF k hk⟩
    exact prf_congr_isFormCodeB
      (prf_eq_symm (prf_eq_trans (prf_congr_nthc_lst (numeralM k) pF)
        (prf_nthc_objList LF k x hx)))
      (hnF _ _ _ oF oT oTs x (mem_of_getElem? LF k x hx))
  · intro k hk
    obtain ⟨x, hx⟩ : ∃ x, LT[k]? = some x := ⟨LT[k], getElem?_pos LT k hk⟩
    exact prf_congr_isTermCodeB
      (prf_eq_symm (prf_eq_trans (prf_congr_nthc_lst (numeralM k) pT)
        (prf_nthc_objList LT k x hx)))
      (hnT _ _ oT oTs x (mem_of_getElem? LT k x hx))
  · intro k hk
    obtain ⟨x, hx⟩ : ∃ x, LTs[k]? = some x := ⟨LTs[k], getElem?_pos LTs k hk⟩
    exact prf_congr_isTermsCodeB
      (prf_eq_symm (prf_eq_trans (prf_congr_nthc_lst (numeralM k) pTs)
        (prf_nthc_objList LTs k x hx)))
      (hnTs _ _ oT oTs x (mem_of_getElem? LTs k x hx))

/-- **HITO (i) DE LA TERNA**: toda `φ` tiene un testigo de parseo COMPLETO y TIPADO. -/
theorem prf_isFCB3_fcodes (φ : Formula) : Prf (isFCB3 (tripleF φ) (formCodeM φ)) :=
  prf_isFCB3_of (fcodes φ) (ftcodes φ) (flcodes φ) (formCodeM φ)
    (closed_mem_fcodes φ) (closed_mem_ftcodes φ) (closed_mem_flcodes φ)
    (mem_self_fcodes φ)
    (fun WF WT WTs hF hT hTs x hx => okF_fcodes φ WF WT WTs hF hT hTs x hx)
    (fun WT WTs hT hTs x hx => okT_ftcodes φ WT WTs hT hTs x hx)
    (fun WT WTs hT hTs x hx => okTs_flcodes φ WT WTs hT hTs x hx)

/-- **NO VACUIDAD, extremo a extremo**: `⊢ Prov(⌜ isFCB3(terna(φ), ⌜φ⌝) ⌝)` para toda `φ`. -/
theorem pcc_isFCB3_fcodes (φ : Formula) :
    Prf (provFromCode (isFCB3Dot (tripleF φ) (formCodeM φ))) :=
  prf_mp (pcc_isFCB3_tracked (tripleF φ) (formCodeM φ)) (prf_isFCB3_fcodes φ)

end PilotoParticion
namespace CritPiloto

/-! ## 0 · Copia LITERAL del piloto -/

theorem impT {A B C : Formula} (h1 : Prf (A ⇒ B)) (h2 : Prf (B ⇒ C)) : Prf (A ⇒ C) := by
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH h2 _) (PrfH.mp _ _ _ (prf_to_prfH h1 _) (prfH_hyp_self _))

theorem prf_or_elim_imp {A B C : Formula} (h1 : Prf (A ⇒ C)) (h2 : Prf (B ⇒ C)) :
    Prf (lor A B ⇒ C) := by
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _
    (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.j3 A B C)) (prfH_hyp_self _))
    (prf_to_prfH h1 _)) (prf_to_prfH h2 _)

theorem prf_orL {A B : Formula} (h : Prf A) : Prf (lor A B) :=
  prf_mp (Prf.incl (Prf₀.j1 A B)) h

theorem prf_cdrc_cons (h t : Term) : Prf (cdrc (cons h t) =eq t) := by
  have hax : Prf ax_cdrc := prf_ax (by simp [axioms])
  have hh := prf_spec (prf_spec hax h) t
  simp [substFormula, substTerm, substTerms, cdrc, cons, FOL.substTerm_liftTerm] at hh
  exact hh

def consOk (X : Term) : Formula := Formula.eq X (cons (carc X) (cdrc X))

def cOk (X : Term) (F : Formula) : Formula := land (consOk X) F

def varOkT (X : Term) : Formula :=
  land (Formula.eq (carc X) (numeralM 0)) (Formula.eq (lenc X) (numeralM 2))

def funcOkT (wTs X : Term) : Formula :=
  land (land (Formula.eq (carc X) (numeralM 1)) (Formula.eq (lenc X) (numeralM 3)))
       (In (nthc X (numeralM 2)) wTs)

def isTermCodeB (wT wTs X : Term) : Formula :=
  lor (cOk X (varOkT X)) (cOk X (funcOkT wTs X))

def isTermsCodeB (wT wTs X : Term) : Formula :=
  lor (Formula.eq X nil)
      (cOk X (land (In (carc X) wT) (In (cdrc X) wTs)))

def bndT  (p : Term) : Term := lenc (carc p)
def bndTs (p : Term) : Term := lenc (cdrc p)

def wfAllT (p : Term) : Formula :=
  Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (bndT p)))
    (isTermCodeB (liftTerm 0 (carc p)) (liftTerm 0 (cdrc p))
      (nthc (liftTerm 0 (carc p)) (.var 0))))

def wfAllTs (p : Term) : Formula :=
  Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (bndTs p)))
    (isTermsCodeB (liftTerm 0 (carc p)) (liftTerm 0 (cdrc p))
      (nthc (liftTerm 0 (cdrc p)) (.var 0))))

def pairOk (p : Term) : Formula := land (wfAllT p) (wfAllTs p)

def isTCB (p c : Term) : Formula := land (pairOk p) (In c (carc p))

def nulOkF (X : Term) : Formula :=
  land (Formula.eq (carc X) (numeralM 2)) (Formula.eq (lenc X) (numeralM 1))

def unOkF (w X : Term) (k : Nat) : Formula :=
  land (land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM 2)))
       (In (nthc X (numeralM 1)) w)

def binOkF (wA wB X : Term) (k : Nat) : Formula :=
  land (land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM 3)))
       (land (In (nthc X (numeralM 1)) wA) (In (nthc X (numeralM 2)) wB))

def strBinOkF (w X : Term) (k : Nat) : Formula :=
  land (land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM 3)))
       (In (nthc X (numeralM 2)) w)

def lorAll : Formula → List Formula → Formula
  | a, []      => a
  | a, b :: bs => lor a (lorAll b bs)

def isFormCodeB (wF wT wTs X : Term) : Formula :=
  lorAll (cOk X (nulOkF X))
    [ cOk X (strBinOkF wTs X 3)
    , cOk X (binOkF wT wT X 4)
    , cOk X (binOkF wF wF X 5)
    , cOk X (unOkF  wF X 6)
    , cOk X (binOkF wF wF X 7)
    , cOk X (binOkF wF wF X 8)
    , cOk X (unOkF  wF X 9) ]

def acF  : Term → Term := carc
def acT  : Term → Term := fun p => carc (cdrc p)
def acTs : Term → Term := fun p => cdrc (cdrc p)

def bndFF (aF : Term → Term) (p : Term) : Term := lenc (aF p)

def wfAllF (aF aT aTs : Term → Term) (p : Term) : Formula :=
  Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (bndFF aF p)))
    (isFormCodeB (liftTerm 0 (aF p)) (liftTerm 0 (aT p)) (liftTerm 0 (aTs p))
      (nthc (liftTerm 0 (aF p)) (.var 0))))

def bndTgen  (aT  : Term → Term) (p : Term) : Term := lenc (aT p)
def bndTsgen (aTs : Term → Term) (p : Term) : Term := lenc (aTs p)

def wfAllTgen (aT aTs : Term → Term) (p : Term) : Formula :=
  Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (bndTgen aT p)))
    (isTermCodeB (liftTerm 0 (aT p)) (liftTerm 0 (aTs p)) (nthc (liftTerm 0 (aT p)) (.var 0))))

def wfAllTsgen (aT aTs : Term → Term) (p : Term) : Formula :=
  Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (bndTsgen aTs p)))
    (isTermsCodeB (liftTerm 0 (aT p)) (liftTerm 0 (aTs p)) (nthc (liftTerm 0 (aTs p)) (.var 0))))

def tripleOk (p : Term) : Formula :=
  land (wfAllF acF acT acTs p)
       (land (wfAllTgen acT acTs p) (wfAllTsgen acT acTs p))

def isFCB3 (p c : Term) : Formula := land (tripleOk p) (In c (acF p))

def CodeClosed (x : Term) : Prop :=
  (∀ c : Nat, liftTerm c x = x) ∧ (∀ (v : Nat) (s : Term), substTerm v s x = x)

theorem closed_termCodeM (t : Term) : CodeClosed (termCodeM t) :=
  ⟨fun c => liftTerm_termCodeM c t, fun v s => substTerm_termCodeM v s t⟩

theorem substF_isTermCodeB (v : Nat) (s A B X : Term) :
    substFormula v s (isTermCodeB A B X)
      = isTermCodeB (substTerm v s A) (substTerm v s B) (substTerm v s X) := by
  simp only [isTermCodeB, cOk, consOk, varOkT, funcOkT, land, lor, In,
    carc, cdrc, lenc, nthc, cons, nil, zero, substFormula, substTerm, substTerms,
    substTerm_numeralM]

theorem substF_isFormCodeB (v : Nat) (s A B C X : Term) :
    substFormula v s (isFormCodeB A B C X)
      = isFormCodeB (substTerm v s A) (substTerm v s B) (substTerm v s C) (substTerm v s X) := by
  simp only [isFormCodeB, lorAll, cOk, consOk, nulOkF, unOkF, binOkF, strBinOkF, land, lor, In,
    carc, cdrc, lenc, nthc, cons, nil, zero, substFormula, substTerm, substTerms,
    substTerm_numeralM]

theorem wfAllT_closed (p : Term) (hpl : liftTerm 0 p = p) :
    wfAllT p = Formula.forall (Formula.impl (lt (.var 0) (bndT p))
      (isTermCodeB (carc p) (cdrc p) (nthc (carc p) (.var 0)))) := by
  simp only [wfAllT, bndT, lenc, carc, cdrc, nthc, liftTerm, liftTerms, hpl]

theorem wfAllF_closed_at (p : Term) (h1 : liftTerm 0 (acF p) = acF p)
    (h2 : liftTerm 0 (acT p) = acT p) (h3 : liftTerm 0 (acTs p) = acTs p) :
    wfAllF acF acT acTs p = Formula.forall (Formula.impl (lt (.var 0) (bndFF acF p))
      (isFormCodeB (acF p) (acT p) (acTs p) (nthc (acF p) (.var 0)))) := by
  simp only [wfAllF, bndFF, lenc, nthc, liftTerm, liftTerms, h1, h2, h3]

theorem prf_nthc_c1 (a b c : Term) : Prf (nthc (cons a (cons b c)) (numeralM 1) =eq b) :=
  prf_eq_trans (prf_nthc_succ a (cons b c) (numeralM 0)) (prf_nthc_zero b c)

/-! ## C1 · Distinción de numerales (Peano 2 + 3, ya en producción) -/

theorem crit_num_ne : ∀ (m n : Nat), m ≠ n →
    Prf (Formula.impl (Formula.eq (numeralM m) (numeralM n)) Formula.bottom)
  | 0,     0,     h => absurd rfl h
  | 0,     _ + 1, _ =>
      prf_deduction (PrfH.mp _ _ _ (prf_to_prfH (prf_succ_ne_zero (numeralM _)) _)
        (PrfH_eq_symm (prfH_hyp_self _)))
  | m + 1, 0,     _ => prf_succ_ne_zero (numeralM m)
  | m + 1, n + 1, h =>
      impT (prf_succ_inj (numeralM m) (numeralM n)) (crit_num_ne m n (fun e => h (by omega)))

/-! ## C2 · Absurdo por TAG -/

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

/-! ## C3 · `isTermCodeB` RECHAZA todo nodo cuyo tag no sea 0 ni 1 -/

theorem crit_isTermCodeB_rejects (wT wTs X : Term) (k : Nat) (hk0 : k ≠ 0) (hk1 : k ≠ 1)
    (hX : Prf (carc X =eq numeralM k)) :
    Prf (Formula.impl (isTermCodeB wT wTs X) Formula.bottom) :=
  prf_or_elim_imp
    (crit_cOk2_absurd X k 0 hk0 hX (Formula.eq (lenc X) (numeralM 2)))
    (crit_cOk3_absurd X k 1 hk1 hX (Formula.eq (lenc X) (numeralM 3))
      (In (nthc X (numeralM 2)) wTs))

/-- **EL JUNK DE `sondeos/SubCodesCritica.lean`, REFUTADO en el nivel del disyunto.** -/
theorem crit_isTermCodeB_rejects_implc (wT wTs a b : Term) :
    Prf (Formula.impl (isTermCodeB wT wTs (implc a b)) Formula.bottom) :=
  crit_isTermCodeB_rejects wT wTs (implc a b) 5 (by decide) (by decide) (prf_carc_cons _ _)

theorem crit_isTermCodeB_rejects_botc (wT wTs : Term) :
    Prf (Formula.impl (isTermCodeB wT wTs botc) Formula.bottom) :=
  crit_isTermCodeB_rejects wT wTs botc 2 (by decide) (by decide) (prf_carc_cons _ _)

theorem crit_isTermCodeB_rejects_atomc (wT wTs p ts : Term) :
    Prf (Formula.impl (isTermCodeB wT wTs (atomc p ts)) Formula.bottom) :=
  crit_isTermCodeB_rejects wT wTs (atomc p ts) 3 (by decide) (by decide) (prf_carc_cons _ _)

theorem crit_isTermCodeB_rejects_eqc (wT wTs a b : Term) :
    Prf (Formula.impl (isTermCodeB wT wTs (eqc a b)) Formula.bottom) :=
  crit_isTermCodeB_rejects wT wTs (eqc a b) 4 (by decide) (by decide) (prf_carc_cons _ _)

theorem crit_isTermCodeB_rejects_forallc (wT wTs a : Term) :
    Prf (Formula.impl (isTermCodeB wT wTs (forallc a)) Formula.bottom) :=
  crit_isTermCodeB_rejects wT wTs (forallc a) 6 (by decide) (by decide) (prf_carc_cons _ _)

theorem crit_isTermCodeB_rejects_andc (wT wTs a b : Term) :
    Prf (Formula.impl (isTermCodeB wT wTs (andc a b)) Formula.bottom) :=
  crit_isTermCodeB_rejects wT wTs (andc a b) 7 (by decide) (by decide) (prf_carc_cons _ _)

theorem crit_isTermCodeB_rejects_orc (wT wTs a b : Term) :
    Prf (Formula.impl (isTermCodeB wT wTs (orc a b)) Formula.bottom) :=
  crit_isTermCodeB_rejects wT wTs (orc a b) 8 (by decide) (by decide) (prf_carc_cons _ _)

theorem crit_isTermCodeB_rejects_exc (wT wTs a : Term) :
    Prf (Formula.impl (isTermCodeB wT wTs (exc a)) Formula.bottom) :=
  crit_isTermCodeB_rejects wT wTs (exc a) 9 (by decide) (by decide) (prf_carc_cons _ _)

/-! ## C4 · `isFormCodeB` RECHAZA todo nodo cuyo tag no esté en 2..9 -/

theorem crit_isFormCodeB_rejects (wF wT wTs X : Term) (k : Nat)
    (h2 : k ≠ 2) (h3 : k ≠ 3) (h4 : k ≠ 4) (h5 : k ≠ 5)
    (h6 : k ≠ 6) (h7 : k ≠ 7) (h8 : k ≠ 8) (h9 : k ≠ 9)
    (hX : Prf (carc X =eq numeralM k)) :
    Prf (Formula.impl (isFormCodeB wF wT wTs X) Formula.bottom) := by
  simp only [isFormCodeB, lorAll]
  exact prf_or_elim_imp (crit_cOk2_absurd X k 2 h2 hX _)
   (prf_or_elim_imp (crit_cOk3_absurd X k 3 h3 hX _ _)
    (prf_or_elim_imp (crit_cOk3_absurd X k 4 h4 hX _ _)
     (prf_or_elim_imp (crit_cOk3_absurd X k 5 h5 hX _ _)
      (prf_or_elim_imp (crit_cOk3_absurd X k 6 h6 hX _ _)
       (prf_or_elim_imp (crit_cOk3_absurd X k 7 h7 hX _ _)
        (prf_or_elim_imp (crit_cOk3_absurd X k 8 h8 hX _ _)
                         (crit_cOk3_absurd X k 9 h9 hX _ _)))))))

/-- **`isFormCodeB` rechaza los códigos de TÉRMINO** (tags 0 y 1). -/
theorem crit_isFormCodeB_rejects_varc (wF wT wTs n : Term) :
    Prf (Formula.impl (isFormCodeB wF wT wTs (varc n)) Formula.bottom) :=
  crit_isFormCodeB_rejects wF wT wTs (varc n) 0
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (prf_carc_cons _ _)

theorem crit_isFormCodeB_rejects_funcc (wF wT wTs s ts : Term) :
    Prf (Formula.impl (isFormCodeB wF wT wTs (funcc s ts)) Formula.bottom) :=
  crit_isFormCodeB_rejects wF wT wTs (funcc s ts) 1
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (prf_carc_cons _ _)

/-! ## C5 · Congruencias `PrfH` que hacen falta para bajar al PAQUETE -/

theorem PrfH_congr_isTermCodeB {Γ : List Formula} {wT wTs X₁ X₂ : Term}
    (h : PrfH Γ (X₁ =eq X₂)) (hN : PrfH Γ (isTermCodeB wT wTs X₁)) :
    PrfH Γ (isTermCodeB wT wTs X₂) := by
  have hS : ∀ s : Term,
      substFormula 0 s (isTermCodeB (liftTerm 0 wT) (liftTerm 0 wTs) (.var 0))
        = isTermCodeB wT wTs s := by
    intro s
    simp only [substF_isTermCodeB, FOL.substTerm_liftTerm, substTerm, if_true]
  exact (hS X₂) ▸ PrfH_leibniz_subst
    (A := isTermCodeB (liftTerm 0 wT) (liftTerm 0 wTs) (.var 0)) h ((hS X₁) ▸ hN)

theorem PrfH_congr_isFormCodeB {Γ : List Formula} {wF wT wTs X₁ X₂ : Term}
    (h : PrfH Γ (X₁ =eq X₂)) (hN : PrfH Γ (isFormCodeB wF wT wTs X₁)) :
    PrfH Γ (isFormCodeB wF wT wTs X₂) := by
  have hS : ∀ s : Term,
      substFormula 0 s
        (isFormCodeB (liftTerm 0 wF) (liftTerm 0 wT) (liftTerm 0 wTs) (.var 0))
        = isFormCodeB wF wT wTs s := by
    intro s
    simp only [substF_isFormCodeB, FOL.substTerm_liftTerm, substTerm, if_true]
  exact (hS X₂) ▸ PrfH_leibniz_subst
    (A := isFormCodeB (liftTerm 0 wF) (liftTerm 0 wT) (liftTerm 0 wTs) (.var 0)) h ((hS X₁) ▸ hN)

theorem PrfH_congr_In_left {Γ : List Formula} {u v w : Term} (h : PrfH Γ (u =eq v))
    (hin : PrfH Γ (In u w)) : PrfH Γ (In v w) := by
  have hS : ∀ s : Term, substFormula 0 s (In (.var 0) (liftTerm 0 w)) = In s w := by
    intro s
    simp only [In, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS v) ▸ PrfH_leibniz_subst (A := In (.var 0) (liftTerm 0 w)) h ((hS u) ▸ hin)

/-! ## C6 · Instanciación del `∀` acotado en un término CUALQUIERA -/

theorem crit_spec_body (A B : Term)
    (hAs : ∀ (v : Nat) (s : Term), substTerm v s A = A)
    (hBs : ∀ (v : Nat) (s : Term), substTerm v s B = B)
    (h : Prf (Formula.forall (Formula.impl (lt (.var 0) (lenc A))
              (isTermCodeB A B (nthc A (.var 0)))))) (i : Term) :
    Prf (Formula.impl (lt i (lenc A)) (isTermCodeB A B (nthc A i))) := by
  have hh := prf_spec h i
  simpa only [substFormula, lt, substF_isTermCodeB, nthc, lenc, substTerm, substTerms,
    hAs, hBs, if_true, reduceIte] using hh

theorem crit_spec_bodyF (A B C : Term)
    (hAs : ∀ (v : Nat) (s : Term), substTerm v s A = A)
    (hBs : ∀ (v : Nat) (s : Term), substTerm v s B = B)
    (hCs : ∀ (v : Nat) (s : Term), substTerm v s C = C)
    (h : Prf (Formula.forall (Formula.impl (lt (.var 0) (lenc A))
              (isFormCodeB A B C (nthc A (.var 0)))))) (i : Term) :
    Prf (Formula.impl (lt i (lenc A)) (isFormCodeB A B C (nthc A i))) := by
  have hh := prf_spec h i
  simpa only [substFormula, lt, substF_isFormCodeB, nthc, lenc, substTerm, substTerms,
    hAs, hBs, hCs, if_true, reduceIte] using hh

/-! ## C7 · EL RESULTADO FUERTE — el PAQUETE discrimina: un testigo VÁLIDO no puede
       contener un código de FÓRMULA en su mitad de TÉRMINOS. -/

theorem crit_In_rejects_of_pairOk (p c : Term)
    (hpl : ∀ n : Nat, liftTerm n p = p)
    (hps : ∀ (v : Nat) (s : Term), substTerm v s p = p)
    (hcl : ∀ n : Nat, liftTerm n c = c)
    (k : Nat) (hk0 : k ≠ 0) (hk1 : k ≠ 1) (hck : Prf (carc c =eq numeralM k))
    (hwf : Prf (pairOk p)) :
    Prf (Formula.impl (In c (carc p)) Formula.bottom) := by
  have hAl : ∀ n : Nat, liftTerm n (carc p) = carc p := by
    intro n; simp only [carc, liftTerm, liftTerms, hpl]
  have hAs : ∀ (v : Nat) (s : Term), substTerm v s (carc p) = carc p := by
    intro v s; simp only [carc, substTerm, substTerms, hps]
  have hBs : ∀ (v : Nat) (s : Term), substTerm v s (cdrc p) = cdrc p := by
    intro v s; simp only [cdrc, substTerm, substTerms, hps]
  have hwfT : Prf (Formula.forall (Formula.impl (lt (.var 0) (lenc (carc p)))
      (isTermCodeB (carc p) (cdrc p) (nthc (carc p) (.var 0))))) := by
    have h0 := prf_and_elim_left hwf
    rwa [wfAllT_closed p (hpl 0)] at h0
  have hbdEq : boundedIn c (carc p)
      = Formula.ex (land (lt (.var 0) (lenc (carc p)))
          (Formula.eq (nthc (carc p) (.var 0)) c)) := by
    simp only [boundedIn, lenc, nthc, liftTerm, liftTerms, hAl, hcl]
  have hex : Prf (Formula.impl (Formula.ex (land (lt (.var 0) (lenc (carc p)))
          (Formula.eq (nthc (carc p) (.var 0)) c))) Formula.bottom) := by
    refine prf_ex_elim_imp ?_
    have hyp := prfH_hyp_self (land (lt (.var 0) (lenc (carc p)))
          (Formula.eq (nthc (carc p) (.var 0)) c))
    have hlt := PrfH_and_elim_left hyp
    have heq := PrfH_and_elim_right hyp
    have hitc := PrfH.mp _ _ _
      (prf_to_prfH (crit_spec_body (carc p) (cdrc p) hAs hBs hwfT (.var 0)) _) hlt
    exact PrfH.mp _ _ _
      (prf_to_prfH (crit_isTermCodeB_rejects (carc p) (cdrc p) c k hk0 hk1 hck) _)
      (PrfH_congr_isTermCodeB heq hitc)
  have hbd : Prf (Formula.impl (boundedIn c (carc p)) Formula.bottom) := by
    rw [hbdEq]; exact hex
  exact impT (prf_boundedIn_of_In c (carc p)) hbd

/-- **`isTCB p c` con `c` código de FÓRMULA es REFUTABLE** (para `p`, `c` cerrados). -/
theorem crit_isTCB_junk_refuted (p c : Term)
    (hpl : ∀ n : Nat, liftTerm n p = p)
    (hps : ∀ (v : Nat) (s : Term), substTerm v s p = p)
    (hcl : ∀ n : Nat, liftTerm n c = c)
    (k : Nat) (hk0 : k ≠ 0) (hk1 : k ≠ 1) (hck : Prf (carc c =eq numeralM k))
    (hjunk : Prf (isTCB p c)) : Prf Formula.bottom :=
  prf_mp (crit_In_rejects_of_pairOk p c hpl hps hcl k hk0 hk1 hck (prf_and_elim_left hjunk))
    (prf_and_elim_right hjunk)

theorem crit_closed_implc {a b : Term} (ha : CodeClosed a) (hb : CodeClosed b) :
    CodeClosed (implc a b) := by
  refine ⟨fun n => ?_, fun v s => ?_⟩
  · simp only [implc, cons, nil, zero, succ, liftTerm, liftTerms, ha.1, hb.1]
  · simp only [implc, cons, nil, zero, succ, substTerm, substTerms, ha.2, hb.2]

/-- **EL JUNK EXACTO de `sondeos/SubCodesCritica.lean`** (`implc ⌜x₀⌝ₜ ⌜x₀⌝ₜ`) es REFUTABLE
    dentro del par partido, para CUALQUIER testigo cerrado `p`. -/
theorem crit_junk_SubCodesCritica (p : Term)
    (hpl : ∀ n : Nat, liftTerm n p = p)
    (hps : ∀ (v : Nat) (s : Term), substTerm v s p = p)
    (hjunk : Prf (isTCB p (implc (termCodeM (.var 0)) (termCodeM (.var 0))))) :
    Prf Formula.bottom :=
  crit_isTCB_junk_refuted p _ hpl hps
    (crit_closed_implc (closed_termCodeM _) (closed_termCodeM _)).1
    5 (by decide) (by decide) (prf_carc_cons _ _) hjunk

/-! ## C8 · La cara de FÓRMULA: un testigo VÁLIDO no puede contener un código de TÉRMINO
       en su lista de FÓRMULAS. Esto es lo que mata `prf_isFC_junk`. -/

theorem crit_In_F_rejects_of_tripleOk (p c : Term)
    (hpl : ∀ n : Nat, liftTerm n p = p)
    (hps : ∀ (v : Nat) (s : Term), substTerm v s p = p)
    (hcl : ∀ n : Nat, liftTerm n c = c)
    (k : Nat) (h2 : k ≠ 2) (h3 : k ≠ 3) (h4 : k ≠ 4) (h5 : k ≠ 5)
    (h6 : k ≠ 6) (h7 : k ≠ 7) (h8 : k ≠ 8) (h9 : k ≠ 9)
    (hck : Prf (carc c =eq numeralM k))
    (hwf : Prf (tripleOk p)) :
    Prf (Formula.impl (In c (acF p)) Formula.bottom) := by
  have l1 : ∀ n : Nat, liftTerm n (acF p) = acF p := by
    intro n; simp only [acF, carc, liftTerm, liftTerms, hpl]
  have l2 : liftTerm 0 (acT p) = acT p := by
    simp only [acT, carc, cdrc, liftTerm, liftTerms, hpl]
  have l3 : liftTerm 0 (acTs p) = acTs p := by
    simp only [acTs, cdrc, liftTerm, liftTerms, hpl]
  have e1 : ∀ (v : Nat) (s : Term), substTerm v s (acF p) = acF p := by
    intro v s; simp only [acF, carc, substTerm, substTerms, hps]
  have e2 : ∀ (v : Nat) (s : Term), substTerm v s (acT p) = acT p := by
    intro v s; simp only [acT, carc, cdrc, substTerm, substTerms, hps]
  have e3 : ∀ (v : Nat) (s : Term), substTerm v s (acTs p) = acTs p := by
    intro v s; simp only [acTs, cdrc, substTerm, substTerms, hps]
  have hwfF : Prf (Formula.forall (Formula.impl (lt (.var 0) (lenc (acF p)))
      (isFormCodeB (acF p) (acT p) (acTs p) (nthc (acF p) (.var 0))))) := by
    have h0 := prf_and_elim_left hwf
    rwa [wfAllF_closed_at p (l1 0) l2 l3] at h0
  have hbdEq : boundedIn c (acF p)
      = Formula.ex (land (lt (.var 0) (lenc (acF p)))
          (Formula.eq (nthc (acF p) (.var 0)) c)) := by
    simp only [boundedIn, lenc, nthc, liftTerm, liftTerms, l1, hcl]
  have hex : Prf (Formula.impl (Formula.ex (land (lt (.var 0) (lenc (acF p)))
          (Formula.eq (nthc (acF p) (.var 0)) c))) Formula.bottom) := by
    refine prf_ex_elim_imp ?_
    have hyp := prfH_hyp_self (land (lt (.var 0) (lenc (acF p)))
          (Formula.eq (nthc (acF p) (.var 0)) c))
    have hlt := PrfH_and_elim_left hyp
    have heq := PrfH_and_elim_right hyp
    have hifc := PrfH.mp _ _ _
      (prf_to_prfH (crit_spec_bodyF (acF p) (acT p) (acTs p) e1 e2 e3 hwfF (.var 0)) _) hlt
    exact PrfH.mp _ _ _
      (prf_to_prfH (crit_isFormCodeB_rejects (acF p) (acT p) (acTs p) c k
        h2 h3 h4 h5 h6 h7 h8 h9 hck) _)
      (PrfH_congr_isFormCodeB heq hifc)
  have hbd : Prf (Formula.impl (boundedIn c (acF p)) Formula.bottom) := by
    rw [hbdEq]; exact hex
  exact impT (prf_boundedIn_of_In c (acF p)) hbd

/-- De `isFormCodeB … (implc a b)` sale que la casilla 1 (`a`) está en la lista de FÓRMULAS. -/
theorem crit_isFormCodeB_implc_child1 (wF wT wTs a b : Term) :
    Prf (Formula.impl (isFormCodeB wF wT wTs (implc a b)) (In a wF)) := by
  have hc : Prf (carc (implc a b) =eq numeralM 5) := prf_carc_cons _ _
  have bad3 : ∀ (m : Nat), m ≠ 5 → ∀ G H : Formula,
      Prf (Formula.impl
        (cOk (implc a b) (land (land (Formula.eq (carc (implc a b)) (numeralM m)) G) H))
        (In a wF)) := fun m hm G H =>
    impT (crit_cOk3_absurd (implc a b) 5 m (fun e => hm e.symm) hc G H)
      (Prf.incl (Prf₀.efq (In a wF)))
  have bad2 : ∀ (m : Nat), m ≠ 5 → ∀ G : Formula,
      Prf (Formula.impl
        (cOk (implc a b) (land (Formula.eq (carc (implc a b)) (numeralM m)) G)) (In a wF)) :=
    fun m hm G =>
      impT (crit_cOk2_absurd (implc a b) 5 m (fun e => hm e.symm) hc G)
        (Prf.incl (Prf₀.efq (In a wF)))
  have good : Prf (Formula.impl (cOk (implc a b) (binOkF wF wF (implc a b) 5)) (In a wF)) := by
    refine prf_deduction ?_
    have hyp := prfH_hyp_self (cOk (implc a b) (binOkF wF wF (implc a b) 5))
    have hin := PrfH_and_elim_left (PrfH_and_elim_right (PrfH_and_elim_right hyp))
    have hnth : Prf (nthc (implc a b) (numeralM 1) =eq a) :=
      prf_nthc_c1 (numeralM 5) a (cons b nil)
    exact PrfH_congr_In_left (prf_to_prfH hnth _) hin
  simp only [isFormCodeB, lorAll]
  exact prf_or_elim_imp (bad2 2 (by decide) _)
   (prf_or_elim_imp (bad3 3 (by decide) _ _)
    (prf_or_elim_imp (bad3 4 (by decide) _ _)
     (prf_or_elim_imp good
      (prf_or_elim_imp (bad3 6 (by decide) _ _)
       (prf_or_elim_imp (bad3 7 (by decide) _ _)
        (prf_or_elim_imp (bad3 8 (by decide) _ _) (bad3 9 (by decide) _ _)))))))

theorem crit_closed_varc {n : Term} (hn : CodeClosed n) : CodeClosed (varc n) := by
  refine ⟨fun m => ?_, fun v s => ?_⟩
  · simp only [varc, cons, nil, zero, liftTerm, liftTerms, hn.1]
  · simp only [varc, cons, nil, zero, substTerm, substTerms, hn.2]

/-- **`prf_isFC_junk` REFUTADO en la partición.** El junk exacto de
    `sondeos/SubCodesCritica.lean` — una `implc` cuyas dos hijas son códigos de TÉRMINO —
    ya no es "no construible por diseño": de él sale `⊥`, para CUALQUIER testigo cerrado. -/
theorem crit_isFC_junk_REFUTED (p n : Term)
    (hpl : ∀ m : Nat, liftTerm m p = p)
    (hps : ∀ (v : Nat) (s : Term), substTerm v s p = p)
    (hn : CodeClosed n)
    (hwf : Prf (tripleOk p))
    (hjunk : Prf (isFormCodeB (acF p) (acT p) (acTs p) (implc (varc n) (varc n)))) :
    Prf Formula.bottom :=
  prf_mp
    (crit_In_F_rejects_of_tripleOk p (varc n) hpl hps (crit_closed_varc hn).1 0
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (prf_carc_cons _ _) hwf)
    (prf_mp (crit_isFormCodeB_implc_child1 (acF p) (acT p) (acTs p) (varc n) (varc n)) hjunk)

/-- Y por tanto también desde el predicado EXPORTADO `isFCB3`. -/
theorem crit_isFCB3_no_termcode (p n : Term)
    (hpl : ∀ m : Nat, liftTerm m p = p)
    (hps : ∀ (v : Nat) (s : Term), substTerm v s p = p)
    (hn : CodeClosed n)
    (hjunk : Prf (isFCB3 p (varc n))) : Prf Formula.bottom :=
  prf_mp
    (crit_In_F_rejects_of_tripleOk p (varc n) hpl hps (crit_closed_varc hn).1 0
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (prf_carc_cons _ _)
      (prf_and_elim_left hjunk))
    (prf_and_elim_right hjunk)

/-! ## C9 · CONTRACARA HONESTA: lo que el reconocedor NO fija (la carga NO está tipada) -/

/-- `varOkT` no obliga a que la casilla 1 sea un NUMERAL: `varc <cualquier cosa>` pasa.
    Es el mismo hueco que en A3 y NO lo repara la partición. -/
theorem crit_varOkT_payload_libre (wT wTs X : Term) :
    Prf (isTermCodeB wT wTs (varc X)) :=
  prf_orL (prf_and_intro (prf_eq_trans
      (prf_congr_cons_head (prf_eq_symm (prf_carc_cons zero (cons X nil))))
      (prf_congr_cons_tail (prf_eq_symm (prf_cdrc_cons zero (cons X nil)))))
    (prf_and_intro (prf_carc_cons zero (cons X nil))
      (prf_eq_trans (prf_lenc_cons zero (cons X nil))
        (prf_eq_congr_succ (prf_eq_trans (prf_lenc_cons X nil)
          (prf_eq_congr_succ prf_lenc_nil))))))

end CritPiloto

/-! ## C10 · IDENTIDAD DE TERMINOS: las definiciones copiadas SON las del piloto. -/

example : PilotoParticion.isTermCodeB  = CritPiloto.isTermCodeB  := rfl
example : PilotoParticion.isTermsCodeB = CritPiloto.isTermsCodeB := rfl
example : PilotoParticion.isFormCodeB  = CritPiloto.isFormCodeB  := rfl
example : PilotoParticion.wfAllT       = CritPiloto.wfAllT       := rfl
example : PilotoParticion.pairOk       = CritPiloto.pairOk       := rfl
example : PilotoParticion.isTCB        = CritPiloto.isTCB        := rfl
example : PilotoParticion.tripleOk     = CritPiloto.tripleOk     := rfl
example : PilotoParticion.isFCB3       = CritPiloto.isFCB3       := rfl
example : PilotoParticion.acF          = CritPiloto.acF          := rfl
example : PilotoParticion.cOk          = CritPiloto.cOk          := rfl
example : PilotoParticion.varOkT       = CritPiloto.varOkT       := rfl
example : PilotoParticion.funcOkT      = CritPiloto.funcOkT      := rfl
example : PilotoParticion.wfAllF       = CritPiloto.wfAllF       := rfl

/- El testigo REAL de una formula satisface el predicado, y a la vez el junk lo REFUTA:
   las dos cosas a la vez, sobre las MISMAS definiciones. -/
#print axioms CritPiloto.crit_isTermCodeB_rejects_implc
#print axioms CritPiloto.crit_isFormCodeB_rejects_varc
#print axioms CritPiloto.crit_junk_SubCodesCritica
#print axioms CritPiloto.crit_isFC_junk_REFUTED
#print axioms CritPiloto.crit_isFCB3_no_termcode
#print axioms CritPiloto.crit_varOkT_payload_libre
#print axioms PilotoParticion.prf_isFCB3_fcodes

/-! ══════════════════════════════════════════════════════════════════════════════════════════
    # CERRAR ② — la DISCRIMINACIÓN sin hipótesis de CLAUSURA

    `sondeos/TestigoAbierto.lean` midió que la clausura del testigo es un **artefacto de la ruta
    de prueba**: `wfAllT` ya lleva el lift explícito, y `wfAllT_closed` sólo existe para quitarlo.

    Aquí se cierra: se rehace la cadena entera de discriminación **llevando** el lift en vez de
    quitarlo. La maniobra es hacer el `∃`-elim **en `PrfH`**, para que el contexto y el testigo
    se lifteen **a la vez** y no haya desajuste.
    ══════════════════════════════════════════════════════════════════════════════════════════ -/

namespace CerrarDos

open CritPiloto

/-! ## 1 · Conmutación de `liftFormula` con los predicados (lo que faltaba) -/

theorem liftF_isTermCodeB (k : Nat) (A B X : Term) :
    liftFormula k (isTermCodeB A B X)
      = isTermCodeB (liftTerm k A) (liftTerm k B) (liftTerm k X) := by
  simp only [isTermCodeB, cOk, consOk, varOkT, funcOkT, land, lor, In,
    carc, cdrc, lenc, nthc, cons, nil, zero, liftFormula, liftTerm, liftTerms,
    liftTerm_numeralM]

theorem liftF_isTermsCodeB (k : Nat) (A B X : Term) :
    liftFormula k (isTermsCodeB A B X)
      = isTermsCodeB (liftTerm k A) (liftTerm k B) (liftTerm k X) := by
  simp only [isTermsCodeB, cOk, consOk, land, lor, In,
    carc, cdrc, cons, nil, zero, liftFormula, liftTerm, liftTerms]

theorem liftF_wfAllT (k : Nat) (p : Term) :
    liftFormula k (wfAllT p) = wfAllT (liftTerm k p) := by
  simp only [wfAllT, bndT, liftFormula, liftF_isTermCodeB, lt, lenc, carc, cdrc, nthc,
    liftTerm, liftTerms, Nat.zero_lt_succ, reduceIte, if_true, ← FOL.liftTerm_comm_zero]

theorem liftF_wfAllTs (k : Nat) (p : Term) :
    liftFormula k (wfAllTs p) = wfAllTs (liftTerm k p) := by
  simp only [wfAllTs, bndTs, liftFormula, liftF_isTermsCodeB, lt, lenc, carc, cdrc, nthc,
    liftTerm, liftTerms, Nat.zero_lt_succ, reduceIte, if_true, ← FOL.liftTerm_comm_zero]

theorem liftF_pairOk (k : Nat) (p : Term) :
    liftFormula k (pairOk p) = pairOk (liftTerm k p) := by
  simp only [pairOk, land, liftFormula, liftF_wfAllT, liftF_wfAllTs]

/-! ## 2 · Instanciación con testigo ABIERTO (el resultado de `TestigoAbierto`, en `PrfH`) -/

theorem PrfH_inst_wfAllT_open {Γ : List Formula} (p k : Term) (h : PrfH Γ (wfAllT p)) :
    PrfH Γ (Formula.impl (lt k (bndT p))
      (isTermCodeB (carc p) (cdrc p) (nthc (carc p) k))) := by
  have hi := PrfH_spec h k
  simpa only [wfAllT, bndT, isTermCodeB, cOk, consOk, varOkT, funcOkT, lt, lenc, carc, cdrc,
    nthc, land, lor, In, cons, nil, zero, substFormula, substTerm, substTerms,
    FOL.substTerm_liftTerm, substTerm_numeralM, if_true] using hi

/-! ## 3 · EL RESULTADO — la discriminación SIN clausura

    Compárese con `CritPiloto.crit_In_rejects_of_pairOk`, que pedía
      `hpl : ∀ n, liftTerm n p = p`, `hps : ∀ v s, substTerm v s p = p`, `hcl : ∀ n, liftTerm n c = c`.
    Aquí **no hay ninguna**: `p` y `c` son abstractos y pueden ser `#0`. -/

/-- ⚠️ **La maniobra**: no existe lema de lifting de DERIVACIONES
    (`PrfH Γ A → PrfH (Γ.map (liftFormula 0)) (liftFormula 0 A)`). Así que el testigo `pairOk p`
    NO va como hipótesis externa, sino **dentro del objetivo** del `∃`-elim: ahí el `liftFormula 0`
    lo aplico yo con `liftF_pairOk`, y dentro del cuerpo aparece como `pairOk ↑p`, ya en la forma
    buena. El lift cae en el sitio que controlo.

    **`p` NO lleva NINGUNA hipótesis** — puede ser `#0`. `c` sí conserva la suya, y es legítimo:
    el `c` del caso de uso es un código construido (`nthc X 2̄`, `implc a b`), no una variable. -/
theorem prf_crit_In_rejects_openP (p c : Term) (k : Nat)
    (hk0 : k ≠ 0) (hk1 : k ≠ 1)
    (hcl : ∀ n : Nat, liftTerm n c = c)
    (hck : Prf (carc c =eq numeralM k)) :
    Prf (Formula.impl (boundedIn c (carc p))
      (Formula.impl (pairOk p) Formula.bottom)) := by
  refine prf_ex_elim_imp ?_
  rw [liftFormula, liftF_pairOk, liftFormula]
  refine deduction_aux ?_ (pairOk (liftTerm 0 p)) _ rfl
  let A : Formula :=
    land (lt (.var 0) (liftTerm 0 (lenc (carc p))))
         (Formula.eq (nthc (liftTerm 0 (carc p)) (.var 0)) (liftTerm 0 c))
  let Γ' : List Formula := [pairOk (liftTerm 0 p), A]
  have hwf' : PrfH Γ' (pairOk (liftTerm 0 p)) := PrfH.hyp _ _ (List.Mem.head _)
  have hbody : PrfH Γ' A := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hlt : PrfH Γ' (lt (.var 0) (bndT (liftTerm 0 p))) := PrfH_and_elim_left hbody
  have heq : PrfH Γ' (Formula.eq (nthc (carc (liftTerm 0 p)) (.var 0)) c) := by
    have h := PrfH_and_elim_right hbody
    rwa [hcl 0] at h
  have hitc : PrfH Γ' (isTermCodeB (carc (liftTerm 0 p)) (cdrc (liftTerm 0 p))
      (nthc (carc (liftTerm 0 p)) (.var 0))) :=
    PrfH.mp _ _ _ (PrfH_inst_wfAllT_open (liftTerm 0 p) (.var 0)
      (PrfH_and_elim_left hwf')) hlt
  have hitc' : PrfH Γ' (isTermCodeB (carc (liftTerm 0 p)) (cdrc (liftTerm 0 p)) c) :=
    PrfH_congr_isTermCodeB heq hitc
  exact PrfH.mp _ _ _
    (prf_to_prfH (crit_isTermCodeB_rejects (carc (liftTerm 0 p)) (cdrc (liftTerm 0 p))
      c k hk0 hk1 hck) _) hitc'

/-- **La discriminación, partiendo de `In` y SIN clausura sobre el testigo `p`.** -/
theorem prf_crit_In_rejects_open (p c : Term) (k : Nat)
    (hk0 : k ≠ 0) (hk1 : k ≠ 1)
    (hcl : ∀ n : Nat, liftTerm n c = c)
    (hck : Prf (carc c =eq numeralM k)) :
    Prf (Formula.impl (In c (carc p)) (Formula.impl (pairOk p) Formula.bottom)) :=
  impT (prf_boundedIn_of_In c (carc p)) (prf_crit_In_rejects_openP p c k hk0 hk1 hcl hck)

/-! ## 4 · LOS TITULARES, re-enunciados SIN clausura sobre el testigo -/

/-- **`isTCB p c` con `c` código de FÓRMULA es REFUTABLE — para CUALQUIER testigo `p`.**
    Compárese con `CritPiloto.crit_isTCB_junk_refuted`, que pedía `hpl` y `hps` sobre `p`. -/
theorem crit_isTCB_junk_refuted_open (p c : Term)
    (hcl : ∀ n : Nat, liftTerm n c = c)
    (k : Nat) (hk0 : k ≠ 0) (hk1 : k ≠ 1) (hck : Prf (carc c =eq numeralM k))
    (hjunk : Prf (isTCB p c)) : Prf Formula.bottom :=
  prf_mp (prf_mp (prf_crit_In_rejects_open p c k hk0 hk1 hcl hck)
    (prf_and_elim_right hjunk)) (prf_and_elim_left hjunk)

/-- **EL JUNK EXACTO de `sondeos/SubCodesCritica.lean`** (`implc ⌜x₀⌝ₜ ⌜x₀⌝ₜ`) es REFUTABLE
    con testigo **ARBITRARIO** — `p` sin una sola hipótesis, luego vale para el `#0` del `∃`-elim. -/
theorem crit_junk_SubCodesCritica_open (p : Term)
    (hjunk : Prf (isTCB p (implc (termCodeM (.var 0)) (termCodeM (.var 0))))) :
    Prf Formula.bottom :=
  crit_isTCB_junk_refuted_open p _
    (crit_closed_implc (closed_termCodeM _) (closed_termCodeM _)).1
    5 (by decide) (by decide) (prf_carc_cons _ _) hjunk

/-- Y con el testigo LITERALMENTE `#0`, que es lo que entrega el `∃`-elim y lo que
    `liftTerm 0 #0 = #1` hacía imposible antes. -/
theorem crit_junk_var0_witness
    (hjunk : Prf (isTCB (.var 0) (implc (termCodeM (.var 0)) (termCodeM (.var 0))))) :
    Prf Formula.bottom :=
  crit_junk_SubCodesCritica_open (.var 0) hjunk

/-! ## 5 · LA CARA DE FÓRMULA — la misma maniobra sobre `wfAllF`/`tripleOk`

    `acF = carc`, `acT = carc ∘ cdrc`, `acTs = cdrc ∘ cdrc`: puros accesores estructurales,
    luego conmutan con `liftTerm` **sin ninguna hipótesis sobre `p`**. -/

theorem liftT_acF (k : Nat) (p : Term) : liftTerm k (acF p) = acF (liftTerm k p) := by
  simp only [acF, carc, liftTerm, liftTerms]
theorem liftT_acT (k : Nat) (p : Term) : liftTerm k (acT p) = acT (liftTerm k p) := by
  simp only [acT, carc, cdrc, liftTerm, liftTerms]
theorem liftT_acTs (k : Nat) (p : Term) : liftTerm k (acTs p) = acTs (liftTerm k p) := by
  simp only [acTs, cdrc, liftTerm, liftTerms]

theorem liftF_isFormCodeB (k : Nat) (A B C X : Term) :
    liftFormula k (isFormCodeB A B C X)
      = isFormCodeB (liftTerm k A) (liftTerm k B) (liftTerm k C) (liftTerm k X) := by
  simp only [isFormCodeB, lorAll, cOk, consOk, nulOkF, unOkF, binOkF, strBinOkF, land, lor, In,
    carc, cdrc, lenc, nthc, cons, nil, zero, liftFormula, liftTerm, liftTerms, liftTerm_numeralM]

theorem liftF_wfAllF (k : Nat) (p : Term) :
    liftFormula k (wfAllF acF acT acTs p) = wfAllF acF acT acTs (liftTerm k p) := by
  simp only [wfAllF, bndFF, liftFormula, liftF_isFormCodeB, lt, lenc, nthc,
    liftT_acF, liftT_acT, liftT_acTs, acF, acT, acTs, carc, cdrc,
    liftTerm, liftTerms, Nat.zero_lt_succ, reduceIte, if_true, ← FOL.liftTerm_comm_zero]

theorem liftF_wfAllTgen (k : Nat) (p : Term) :
    liftFormula k (wfAllTgen acT acTs p) = wfAllTgen acT acTs (liftTerm k p) := by
  simp only [wfAllTgen, bndTgen, liftFormula, liftF_isTermCodeB, lt, lenc, nthc,
    liftT_acT, liftT_acTs, acT, acTs, carc, cdrc,
    liftTerm, liftTerms, Nat.zero_lt_succ, reduceIte, if_true, ← FOL.liftTerm_comm_zero]

theorem liftF_wfAllTsgen (k : Nat) (p : Term) :
    liftFormula k (wfAllTsgen acT acTs p) = wfAllTsgen acT acTs (liftTerm k p) := by
  simp only [wfAllTsgen, bndTsgen, liftFormula, liftF_isTermsCodeB, lt, lenc, nthc,
    liftT_acT, liftT_acTs, acT, acTs, carc, cdrc,
    liftTerm, liftTerms, Nat.zero_lt_succ, reduceIte, if_true, ← FOL.liftTerm_comm_zero]

theorem liftF_tripleOk (k : Nat) (p : Term) :
    liftFormula k (tripleOk p) = tripleOk (liftTerm k p) := by
  simp only [tripleOk, land, liftFormula, liftF_wfAllF, liftF_wfAllTgen, liftF_wfAllTsgen]

theorem PrfH_inst_wfAllF_open {Γ : List Formula} (p k : Term)
    (h : PrfH Γ (wfAllF acF acT acTs p)) :
    PrfH Γ (Formula.impl (lt k (bndFF acF p))
      (isFormCodeB (acF p) (acT p) (acTs p) (nthc (acF p) k))) := by
  have hi := PrfH_spec h k
  simpa only [wfAllF, bndFF, isFormCodeB, lorAll, cOk, consOk, nulOkF, unOkF, binOkF, strBinOkF,
    acF, acT, acTs, lt, lenc, carc, cdrc, nthc, land, lor, In, cons, nil, zero,
    substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, substTerm_numeralM,
    if_true] using hi

/-- **La discriminación de la cara de FÓRMULA, SIN clausura sobre el testigo `p`.** -/
theorem prf_crit_In_F_rejects_openP (p c : Term) (k : Nat)
    (h2 : k ≠ 2) (h3 : k ≠ 3) (h4 : k ≠ 4) (h5 : k ≠ 5)
    (h6 : k ≠ 6) (h7 : k ≠ 7) (h8 : k ≠ 8) (h9 : k ≠ 9)
    (hcl : ∀ n : Nat, liftTerm n c = c)
    (hck : Prf (carc c =eq numeralM k)) :
    Prf (Formula.impl (boundedIn c (acF p))
      (Formula.impl (tripleOk p) Formula.bottom)) := by
  refine prf_ex_elim_imp ?_
  rw [liftFormula, liftF_tripleOk, liftFormula]
  refine deduction_aux ?_ (tripleOk (liftTerm 0 p)) _ rfl
  let A : Formula :=
    land (lt (.var 0) (liftTerm 0 (lenc (acF p))))
         (Formula.eq (nthc (liftTerm 0 (acF p)) (.var 0)) (liftTerm 0 c))
  let Γ' : List Formula := [tripleOk (liftTerm 0 p), A]
  have hwf' : PrfH Γ' (tripleOk (liftTerm 0 p)) := PrfH.hyp _ _ (List.Mem.head _)
  have hbody : PrfH Γ' A := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hlt : PrfH Γ' (lt (.var 0) (bndFF acF (liftTerm 0 p))) := PrfH_and_elim_left hbody
  have heq : PrfH Γ' (Formula.eq (nthc (acF (liftTerm 0 p)) (.var 0)) c) := by
    have h := PrfH_and_elim_right hbody
    rwa [hcl 0] at h
  have hifc : PrfH Γ' (isFormCodeB (acF (liftTerm 0 p)) (acT (liftTerm 0 p))
      (acTs (liftTerm 0 p)) (nthc (acF (liftTerm 0 p)) (.var 0))) :=
    PrfH.mp _ _ _ (PrfH_inst_wfAllF_open (liftTerm 0 p) (.var 0)
      (PrfH_and_elim_left hwf')) hlt
  have hifc' : PrfH Γ' (isFormCodeB (acF (liftTerm 0 p)) (acT (liftTerm 0 p))
      (acTs (liftTerm 0 p)) c) := PrfH_congr_isFormCodeB heq hifc
  exact PrfH.mp _ _ _
    (prf_to_prfH (crit_isFormCodeB_rejects (acF (liftTerm 0 p)) (acT (liftTerm 0 p))
      (acTs (liftTerm 0 p)) c k h2 h3 h4 h5 h6 h7 h8 h9 hck) _) hifc'

/-- **`isFCB3 p (varc n)` es REFUTABLE con testigo ARBITRARIO** — el otro titular,
    sin `hpl`/`hps`. Es lo que mata `prf_isFC_junk` de `sondeos/SubCodesCritica.lean`. -/
theorem prf_crit_In_F_rejects_open (p c : Term) (k : Nat)
    (h2 : k ≠ 2) (h3 : k ≠ 3) (h4 : k ≠ 4) (h5 : k ≠ 5)
    (h6 : k ≠ 6) (h7 : k ≠ 7) (h8 : k ≠ 8) (h9 : k ≠ 9)
    (hcl : ∀ n : Nat, liftTerm n c = c)
    (hck : Prf (carc c =eq numeralM k)) :
    Prf (Formula.impl (In c (acF p)) (Formula.impl (tripleOk p) Formula.bottom)) :=
  impT (prf_boundedIn_of_In c (acF p))
    (prf_crit_In_F_rejects_openP p c k h2 h3 h4 h5 h6 h7 h8 h9 hcl hck)

theorem crit_isFCB3_no_termcode_open (p n : Term) (hn : CodeClosed n)
    (hjunk : Prf (isFCB3 p (varc n))) : Prf Formula.bottom := by
  have hcl : ∀ m : Nat, liftTerm m (varc n) = varc n := by
    intro m; simp only [varc, cons, nil, zero, succ, liftTerm, liftTerms, hn.1]
  exact prf_mp (prf_mp (prf_crit_In_F_rejects_open p (varc n) 0
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hcl (prf_carc_cons _ _))
    (prf_and_elim_right hjunk)) (prf_and_elim_left hjunk)

/-- Con el testigo LITERALMENTE `#0`. -/
theorem crit_isFCB3_no_termcode_var0 (n : Term) (hn : CodeClosed n)
    (hjunk : Prf (isFCB3 (.var 0) (varc n))) : Prf Formula.bottom :=
  crit_isFCB3_no_termcode_open (.var 0) n hn hjunk

end CerrarDos

#print axioms CerrarDos.prf_crit_In_F_rejects_openP
#print axioms CerrarDos.crit_isFCB3_no_termcode_open
#print axioms CerrarDos.crit_isFCB3_no_termcode_var0
#print axioms CerrarDos.crit_isTCB_junk_refuted_open
#print axioms CerrarDos.crit_junk_SubCodesCritica_open
#print axioms CerrarDos.crit_junk_var0_witness
#print axioms CerrarDos.liftF_wfAllT
#print axioms CerrarDos.liftF_pairOk
#print axioms CerrarDos.PrfH_inst_wfAllT_open
#print axioms CerrarDos.prf_crit_In_rejects_openP
#print axioms CerrarDos.prf_crit_In_rejects_open

/-! ══════════════════════════════════════════════════════════════════════════════════════════
    # PASO ① — REVALIDAR LA DISCRIMINACIÓN CONTRA LA FORMA ECUACIONAL

    La forma ECUACIONAL (`X ≐ cons k̄ …`, en lugar de `carc X ≐ k̄ ∧ lenc X ≐ n̄`) **cambia el
    predicado**, y nadie había comprobado que la discriminación sobreviva. `ClausuraFormaEcuacional`
    sostiene que sí por ser un FORTALECIMIENTO, pero sólo lo probó para **un** disyunto (`implc`).

    🔑 **Y no hacen falta 12 lemas, ni 3: basta UNO.** La Leibniz transporta desde la forma
    concreta `C` a `X` sin mirar qué constructor es, así que el fortalecimiento se prueba **una vez**
    y los 12 disyuntos son instancias con distinto `C`, `k` y `n`.
    ══════════════════════════════════════════════════════════════════════════════════════════ -/

namespace PasoUno

open CritPiloto

/-! ## 1 · EL fortalecimiento genérico — UNO para los doce -/

/-- **`X ≐ C` transporta a `X` todo lo que se sepa de `C`.** `C` es la forma concreta
    (`cons k̄ nil`, `cons k̄ (cons A nil)`, `cons k̄ (cons A (cons B nil))`); `X` es abstracto. -/
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

/-! ## 2 · Las TRES formas ecuacionales, y su fortalecimiento como instancia -/

def shapeNul (X : Term) (k : Nat) : Formula :=
  Formula.eq X (cons (numeralM k) nil)

def shapeUn (X : Term) (k : Nat) : Formula :=
  Formula.eq X (cons (numeralM k) (cons (nthc X (numeralM 1)) nil))

def shapeBin (X : Term) (k : Nat) : Formula :=
  Formula.eq X (cons (numeralM k)
    (cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil)))

theorem prf_shapeNul_str (X : Term) (k : Nat) :
    Prf (Formula.impl (shapeNul X k)
      (land (consOk X) (land (Formula.eq (carc X) (numeralM k))
                             (Formula.eq (lenc X) (numeralM 1))))) :=
  prf_shape_strengthens X _ k 1 (prf_carc_cons _ _)
    (PilotoParticion.prf_lenc_c1 _) (PilotoParticion.prf_consOk_cons _ _)

theorem prf_shapeUn_str (X : Term) (k : Nat) :
    Prf (Formula.impl (shapeUn X k)
      (land (consOk X) (land (Formula.eq (carc X) (numeralM k))
                             (Formula.eq (lenc X) (numeralM 2))))) :=
  prf_shape_strengthens X _ k 2 (prf_carc_cons _ _)
    (PilotoParticion.prf_lenc_c2 _ _) (PilotoParticion.prf_consOk_cons _ _)

theorem prf_shapeBin_str (X : Term) (k : Nat) :
    Prf (Formula.impl (shapeBin X k)
      (land (consOk X) (land (Formula.eq (carc X) (numeralM k))
                             (Formula.eq (lenc X) (numeralM 3))))) :=
  prf_shape_strengthens X _ k 3 (prf_carc_cons _ _)
    (PilotoParticion.prf_lenc_c3 _ _ _) (PilotoParticion.prf_consOk_cons _ _)

/-! ## 3 · ⚠️ NO ES FORTALECIMIENTO VACUO: los códigos REALES la satisfacen -/

theorem prf_shapeNul_real (k : Nat) : Prf (shapeNul (cons (numeralM k) nil) k) :=
  prf_refl _

theorem prf_shapeUn_real (k : Nat) (a : Term) :
    Prf (shapeUn (cons (numeralM k) (cons a nil)) k) :=
  prf_eq_symm (prf_congr_cons_tail (prf_congr_cons_head
    (PilotoParticion.prf_nthc_c1 (numeralM k) a nil)))

theorem prf_shapeBin_real (k : Nat) (a b : Term) :
    Prf (shapeBin (cons (numeralM k) (cons a (cons b nil))) k) :=
  prf_eq_symm (prf_congr_cons_tail (prf_eq_trans
    (prf_congr_cons_head (PilotoParticion.prf_nthc_c1 (numeralM k) a (cons b nil)))
    (prf_congr_cons_tail (prf_congr_cons_head
      (PilotoParticion.prf_nthc_c2 (numeralM k) a b nil)))))

/-! ## 4 · Los predicados en forma ECUACIONAL, y su fortalecimiento

    ⚠️ `isTermsCodeB` **ya está en forma ecuacional**: sus dos disyuntos son `X ≐ nil` y
    `cOk X …`, y `consOk X` **es** `X ≐ cons (carc X) (cdrc X)`. No hay nada que reformular. -/

/-- Or-intro OBJETO como implicación (el `prf_orL_imp` del fichero es el INTERNO, sobre `orc`). -/
theorem prf_lorL (A B : Formula) : Prf (Formula.impl A (lor A B)) := Prf.incl (Prf₀.j1 A B)
theorem prf_lorR (A B : Formula) : Prf (Formula.impl B (lor A B)) := Prf.incl (Prf₀.j2 A B)

def isTermCodeE (wT wTs X : Term) : Formula :=
  lor (shapeUn X 0) (land (shapeBin X 1) (In (nthc X (numeralM 2)) wTs))

def isFormCodeE (wF wT wTs X : Term) : Formula :=
  lorAll (shapeNul X 2)
    [ land (shapeBin X 3) (In (nthc X (numeralM 2)) wTs)
    , land (shapeBin X 4) (land (In (nthc X (numeralM 1)) wT) (In (nthc X (numeralM 2)) wT))
    , land (shapeBin X 5) (land (In (nthc X (numeralM 1)) wF) (In (nthc X (numeralM 2)) wF))
    , land (shapeUn  X 6) (In (nthc X (numeralM 1)) wF)
    , land (shapeBin X 7) (land (In (nthc X (numeralM 1)) wF) (In (nthc X (numeralM 2)) wF))
    , land (shapeBin X 8) (land (In (nthc X (numeralM 1)) wF) (In (nthc X (numeralM 2)) wF))
    , land (shapeUn  X 9) (In (nthc X (numeralM 1)) wF) ]

/-- Reensamblado: de `shape ∧ M` con el fortalecimiento sale la forma `cOk X ((tag ∧ len) ∧ M)`. -/
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

/-- **La forma ecuacional FORTALECE `isTermCodeB`.** -/
theorem prf_isTermCodeE_str (wT wTs X : Term) :
    Prf (Formula.impl (isTermCodeE wT wTs X) (isTermCodeB wT wTs X)) := by
  unfold isTermCodeE isTermCodeB
  refine prf_or_elim_imp (impT (prf_shapeUn_str X 0) (prf_lorL _ _)) ?_
  exact impT (prf_str_and X 1 3 _ _ (prf_shapeBin_str X 1)) (prf_lorR _ _)

/-- **La forma ecuacional FORTALECE `isFormCodeB`**, los 8 disyuntos. -/
theorem prf_isFormCodeE_str (wF wT wTs X : Term) :
    Prf (Formula.impl (isFormCodeE wF wT wTs X) (isFormCodeB wF wT wTs X)) := by
  unfold isFormCodeE isFormCodeB lorAll
  refine prf_or_elim_imp (impT (prf_shapeNul_str X 2) (prf_lorL _ _)) ?_
  refine impT ?_ (prf_lorR _ _)
  refine prf_or_elim_imp (impT (prf_str_and X 3 3 _ _ (prf_shapeBin_str X 3)) (prf_lorL _ _)) ?_
  refine impT ?_ (prf_lorR _ _)
  refine prf_or_elim_imp (impT (prf_str_and X 4 3 _ _ (prf_shapeBin_str X 4)) (prf_lorL _ _)) ?_
  refine impT ?_ (prf_lorR _ _)
  refine prf_or_elim_imp (impT (prf_str_and X 5 3 _ _ (prf_shapeBin_str X 5)) (prf_lorL _ _)) ?_
  refine impT ?_ (prf_lorR _ _)
  refine prf_or_elim_imp (impT (prf_str_and X 6 2 _ _ (prf_shapeUn_str X 6)) (prf_lorL _ _)) ?_
  refine impT ?_ (prf_lorR _ _)
  refine prf_or_elim_imp (impT (prf_str_and X 7 3 _ _ (prf_shapeBin_str X 7)) (prf_lorL _ _)) ?_
  refine impT ?_ (prf_lorR _ _)
  refine prf_or_elim_imp (impT (prf_str_and X 8 3 _ _ (prf_shapeBin_str X 8)) (prf_lorL _ _)) ?_
  refine impT ?_ (prf_lorR _ _)
  exact prf_str_and X 9 2 _ _ (prf_shapeUn_str X 9)

/-! ## 5 · ✅ LA REVALIDACIÓN — la discriminación SOBREVIVE a la forma ecuacional -/

/-- `isTermCodeE` RECHAZA todo nodo cuyo tag no sea 0 ni 1 — igual que la forma vieja. -/
theorem crit_isTermCodeE_rejects (wT wTs X : Term) (k : Nat) (hk0 : k ≠ 0) (hk1 : k ≠ 1)
    (hX : Prf (carc X =eq numeralM k)) :
    Prf (Formula.impl (isTermCodeE wT wTs X) Formula.bottom) :=
  impT (prf_isTermCodeE_str wT wTs X) (crit_isTermCodeB_rejects wT wTs X k hk0 hk1 hX)

/-- **EL JUNK, refutado también en forma ECUACIONAL.** Es el `implc ⌜x₀⌝ₜ ⌜x₀⌝ₜ` de
    `sondeos/SubCodesCritica.lean`, que el predicado FUSIONADO aceptaba. -/
theorem crit_isTermCodeE_rejects_implc (wT wTs a b : Term) :
    Prf (Formula.impl (isTermCodeE wT wTs (implc a b)) Formula.bottom) :=
  crit_isTermCodeE_rejects wT wTs (implc a b) 5 (by decide) (by decide) (prf_carc_cons _ _)

/-- `isFormCodeE` RECHAZA todo nodo cuyo tag no esté en 2..9. -/
theorem crit_isFormCodeE_rejects (wF wT wTs X : Term) (k : Nat)
    (h2 : k ≠ 2) (h3 : k ≠ 3) (h4 : k ≠ 4) (h5 : k ≠ 5)
    (h6 : k ≠ 6) (h7 : k ≠ 7) (h8 : k ≠ 8) (h9 : k ≠ 9)
    (hX : Prf (carc X =eq numeralM k)) :
    Prf (Formula.impl (isFormCodeE wF wT wTs X) Formula.bottom) :=
  impT (prf_isFormCodeE_str wF wT wTs X)
    (crit_isFormCodeB_rejects wF wT wTs X k h2 h3 h4 h5 h6 h7 h8 h9 hX)

/-- **Un código de VARIABLE (tag 0) NO pasa por `isFormCodeE`** — la otra mitad de la
    discriminación, la que mata `prf_isFC_junk`. -/
theorem crit_isFormCodeE_rejects_varc (wF wT wTs n : Term) :
    Prf (Formula.impl (isFormCodeE wF wT wTs (varc n)) Formula.bottom) :=
  crit_isFormCodeE_rejects wF wT wTs (varc n) 0
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (prf_carc_cons _ _)

end PasoUno

#print axioms PasoUno.prf_isTermCodeE_str
#print axioms PasoUno.prf_isFormCodeE_str
#print axioms PasoUno.crit_isTermCodeE_rejects_implc
#print axioms PasoUno.crit_isFormCodeE_rejects_varc
#print axioms PasoUno.prf_shape_strengthens
#print axioms PasoUno.prf_shapeNul_str
#print axioms PasoUno.prf_shapeUn_str
#print axioms PasoUno.prf_shapeBin_str
#print axioms PasoUno.prf_shapeBin_real
