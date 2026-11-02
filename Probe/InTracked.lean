/-
✅ SONDEO POSITIVO (2026-08-24) — **A1 y A2: el REFLECTOR de la vía (2) EXISTE**.

Contexto: elegida la vía por testigo de parseo (`sondeos/ParseWitness.lean`), la pregunta que
decide si llega a los 7 tags es si `isFCB` se **refleja** dentro de `Prov`. Al planificarlo
identifiqué **un solo hueco**: no había reflector `tracked` del átomo `In` sobre lista
**ABSTRACTA** (`pcc_In_lfc_tracked` recurre sobre lista META; `pcc_in_objList_of_mem` también).
Este sondeo lo tapa y mide el eslabón siguiente.

## Lo que está COMPILADO aquí — footprint SANCIONADO

`[propext, Classical.choice, Quot.sound, prf_axiomsCodeT_eq]`, el de todo lo que toca `provFromCode`.

| pieza | qué asegura |
|---|---|
| **`pcc_boundedIn_tracked (x w)`** | **A1**: `boundedIn x w ⇒ Prov(⌜∃i<lencT ẇ. nthcT ẇ i = ẋ⌝)`, con `x` y `w` **ABSTRACTOS** |
| **`pcc_In_tracked (x w)`** | A1 desde el átomo `In`, vía `prf_In_iff_boundedIn` (que vale para `L` abstracta) |
| **`pcc_binOk_tracked (w X k)`** | **A2, caso MÁXIMO**: dos `=eq` + dos `In`. Si éste refleja, reflejan los 12 |

## Por qué A1 salió, y por qué es MÁS SIMPLE que su precedente

Molde: `pcc_bddCarcDot_reflect` (`D3InDotPrf.lean:334`), el núcleo de `hI_dot`. Cinco pasos:
`PrfH_ex_elim` del `∃` acotado (el testigo pasa a ser `#0` y `w` se liftea) · `pcc_lt_tracked`
para la cota, transportada con **simetría INTERNA** (`PrfH_eq_symm_code`, porque Leibniz va al
revés) contra `pcc_eval_lenc` · `pcc_eval_nthc` para el cuerpo · `PrfH_bdEx_intro_open` con
testigo `K = tcFn #0` · y `prf_substtc_varc0` cerrando el hueco `⌜v₀⌝`.

Dos cosas lo abaratan frente al precedente:
* **`pcc_eval_nthc` es INCONDICIONAL** salvo `i < lenc p` — y eso es justo lo que da el `∃`
  acotado. (`pcc_eval_carc_nthc`, el del precedente, consume además `chainOk nil p`; ese
  `chainOk` viene del `carc`, no del `nthc`.) Nuestro testigo de parseo **no es una cadena de
  prueba**, así que ese requisito habría sido un problema real. No lo es.
* **No hay cruce de FRONTERA numeral**: el precedente necesitaba `pcc_to_formCode_imp` porque su
  `φ` era concreto (`termCode (formCode φ)`); con `x` abstracto no hay frontera que cruzar.

## A2: el caso máximo, y por qué subsume a los 12

`binOk` = dos `=eq` (tag y longitud) + dos `In`. Los `=eq` los da **`pcc_eq_tracked`**, que es
**general** (argumentos abstractos); los `In`, A1; y `PrfH_and_intro_code` ensambla dentro.
`unOk`/`strBinOk` son sub-casos, `nulOk`/`varOk` son sólo los dos `=eq`, el caso `nil` es un
`=eq`, y el caso `cons` son sólo dos `In`. **No queda mecanismo sin medir.**

⚠️ Los `=eq` salen en la forma `eqCodeFn (tcFn (carc X)) …` (reflexión pura), no
`carcT (tcFn X)`. Convertir una en otra es **evaluación provable**, y las tres piezas están en
producción: `pcc_eval_carc`, `pcc_eval_lenc`, `pcc_eval_nthc`.

## A3 — lo que falta: NO tiene hueco de herramienta

`isFCB w c = wfAll w ∧ In c w`. El segundo es A1. El primero es un `∀` acotado, y su
introducción **está completa en producción**: `pcc_bdAll_intro` (§40, `BdAllIntroPrf.lean:316`),
construida precisamente para esta forma. Su `hbody` es, literalmente,
«de `wfAll q` y `i < lenc q` sale la reflexión del nodo» = `prf_spec` + MP + **A2**.

Comprobado además el punto que sí podía morder: `substfc` tiene que atravesar el `orc` de los 12
disyuntos **y el `exc`** de `bdInDot` (un binder). **Las 8 ecuaciones existen como teoremas
`Prf`** (`ArithPrf.lean:298‑347`), `prf_substfc_or` y `prf_substfc_ex` incluidas. Al cruzar el
`exc` los índices se desplazan (`succ`/`liftc`) ⇒ hay **dos niveles De Bruijn** que gestionar;
es trabajo real, pero con precedente directo (`prf_substfc_exBodyc`, `EvalLtPrf.lean:236`;
`prf_substfc_ltCodeFn_varc0`, `EvalBoundedPrf.lean:170`).

⇒ A3 es **descargar parámetros**, no resolver un problema abierto.

## Cómo re-ejecutarlo

    lake env lean sondeos/InTracked.lean
-/
import ROBINSON_PlusPlus.Meta

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.BoundedInPrf
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.TrackedCorePrf
open ROBINSON_PlusPlus.Meta.Delta0ReflectPrf ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.EvalListPrf ROBINSON_PlusPlus.Meta.EvalNthcPrf
open ROBINSON_PlusPlus.Meta.EvalLtPrf ROBINSON_PlusPlus.Meta.EvalBoundedPrf
open ROBINSON_PlusPlus.Meta.EvalArithPrf ROBINSON_PlusPlus.Meta.D3InDotPrf
open ROBINSON_PlusPlus.Meta.NumCodeClosedPrf ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.DerivCondPrf

namespace InTracked

/-- Cota dotada del `∃` acotado de `boundedIn`: `lencT (liftc 0 ẇ)`. -/
noncomputable def bdInB (w : Term) : Term := lencT (liftc zero (tcFn w))

/-- Cuerpo dotado: `nthcT (liftc 0 ẇ) ⌜v₀⌝ = liftc 0 ẋ`. -/
noncomputable def bdInPhic (x w : Term) : Term :=
  eqCodeFn (nthcT (liftc zero (tcFn w)) (varc (numeral 0))) (liftc zero (tcFn x))

/-- El código dotado de `boundedIn x w`. -/
noncomputable def bdInDot (x w : Term) : Term := bdExCode (bdInB w) (bdInPhic x w)

theorem liftTerm_bdInDot (c : Nat) (x w : Term) :
    liftTerm c (bdInDot x w) = bdInDot (liftTerm c x) (liftTerm c w) := by
  unfold bdInDot bdInB bdInPhic bdExCode
  simp only [exc, andc, ltCodeFn, atom2CodeFn, eqCodeFn, lencT, nthcT, funcc, varc, liftc, tcFn,
    cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_numeral, liftTerm_strCode]

theorem substtc_inv_bdInB (w : Term) : ∀ W, Prf (substtc zero W (bdInB w) =eq bdInB w) :=
  substtc_inv_lencT (substtc_inv_liftc_tcFn w)

/-- **A1**: reflexión punteada del `∃` acotado `boundedIn`, con `x` y `w` **ABSTRACTOS**.
    Más simple que el precedente: sin `carc` y sin cruce de frontera numeral. -/
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
  -- COTA: `pcc_lt_tracked` + `pcc_eval_lenc`, con simetría INTERNA (Leibniz va al revés)
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
  -- CUERPO: `pcc_eval_nthc` (sólo pide `i < lenc p`, NO `chainOk`) + congruencia OBJETO
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

/-- **A1'**: la misma reflexión partiendo del átomo `In` (vía `prf_In_iff_boundedIn`). -/
theorem pcc_In_tracked (x w : Term) :
    Prf (In x w ⇒ provFromCode (bdInDot x w)) := by
  refine prf_deduction ?_
  have hin : PrfH [In x w] (In x w) := prfH_hyp_self _
  have hbd : PrfH [In x w] (boundedIn x w) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_and_elim_left (prf_In_iff_boundedIn x w)) _) hin
  exact PrfH.mp _ _ _ (prf_to_prfH (pcc_boundedIn_tracked x w) _) hbd

/-! ## A2 · el caso MÁXIMO de `nodeOk`: `binOk` (dos `=eq` + dos `In`)

    Si éste refleja, reflejan todos: `unOk`/`strBinOk` son sub-casos, `nulOk`/`varOk` son sólo
    los dos `=eq`, y el caso `cons` de las listas son sólo los dos `In`. -/

def binOk (w X : Term) (k : Nat) : Formula :=
  land (land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM 3)))
       (land (In (nthc X (numeralM 1)) w) (In (nthc X (numeralM 2)) w))

/-- Imagen punteada de `binOk`. Los `=eq` salen como `tcFn`-de-la-parte (reflexión pura);
    convertirlos a `carcT (tcFn X)` etc. es después, y ya existe (`pcc_eval_carc/lenc/nthc`). -/
noncomputable def binOkDot (w X : Term) (k : Nat) : Term :=
  andc (andc (eqCodeFn (tcFn (carc X)) (tcFn (numeralM k)))
             (eqCodeFn (tcFn (lenc X)) (tcFn (numeralM 3))))
       (andc (bdInDot (nthc X (numeralM 1)) w) (bdInDot (nthc X (numeralM 2)) w))

theorem pcc_binOk_tracked (w X : Term) (k : Nat) :
    Prf (binOk w X k ⇒ provFromCode (binOkDot w X k)) := by
  refine prf_deduction ?_
  have h : PrfH [binOk w X k] (binOk w X k) := prfH_hyp_self _
  have hsh : PrfH [binOk w X k]
      (land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM 3))) :=
    PrfH_and_elim_left h
  have hmem : PrfH [binOk w X k]
      (land (In (nthc X (numeralM 1)) w) (In (nthc X (numeralM 2)) w)) :=
    PrfH_and_elim_right h
  -- los dos `=eq`: `pcc_eq_tracked` es GENERAL (argumentos abstractos)
  have hd1 : PrfH [binOk w X k] (provFromCode (eqCodeFn (tcFn (carc X)) (tcFn (numeralM k)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eq_tracked (carc X) (numeralM k)) _) (PrfH_and_elim_left hsh)
  have hd2 : PrfH [binOk w X k] (provFromCode (eqCodeFn (tcFn (lenc X)) (tcFn (numeralM 3)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eq_tracked (lenc X) (numeralM 3)) _) (PrfH_and_elim_right hsh)
  -- los dos `In`: A1
  have hd3 : PrfH [binOk w X k] (provFromCode (bdInDot (nthc X (numeralM 1)) w)) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_In_tracked (nthc X (numeralM 1)) w) _) (PrfH_and_elim_left hmem)
  have hd4 : PrfH [binOk w X k] (provFromCode (bdInDot (nthc X (numeralM 2)) w)) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_In_tracked (nthc X (numeralM 2)) w) _)
      (PrfH_and_elim_right hmem)
  -- `∧`-intro INTERNO ×3
  exact PrfH_and_intro_code _ _ (PrfH_and_intro_code _ _ hd1 hd2)
    (PrfH_and_intro_code _ _ hd3 hd4)

end InTracked

#print axioms InTracked.pcc_boundedIn_tracked
#print axioms InTracked.pcc_In_tracked
#print axioms InTracked.pcc_binOk_tracked
