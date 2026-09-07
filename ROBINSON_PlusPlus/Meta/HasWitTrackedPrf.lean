import ROBINSON_PlusPlus.Meta.TrackedAtomsPrf
import ROBINSON_PlusPlus.Meta.LineWFGuardPrf
/-!
# `Meta/HasWitTrackedPrf.lean` — el descenso de `DEUDA_hGuardT` hasta UNA obligación

`Meta/LineWFGuardPrf.lean` dejó la deuda de ADR‑020 en **dos** lemas genéricos,
`DEUDA_hGuardT` y `DEUDA_hGuardF`. Este módulo baja el primero un escalón más y, sobre todo,
**mide dónde está el contenido**.

## El descenso

    hasWit c   =  ∃w. isTC1 w ↑c                            (`Minimal/Axioms.lean:1052`)
    isTC1 w c  =  wfAll1 w ∧ In c w                         (`Minimal/Axioms.lean:1049`)

⭐ Esa segunda línea es **exactamente** la forma `isFCB w c = wfAll w ∧ In c w` que
`sondeos/A3IsFCBTracked.lean` reflejó entera (`pcc_isFCB_tracked`), y por eso el escalón sale
en cuatro líneas apoyado en el kit genérico que ya está en producción
(`Meta/TrackedAtomsPrf.lean`): la mitad derecha es `pcc_In_atom_tracked`, con `c` y `w`
**abstractos**.

⇒ Queda **una** obligación de contenido para esta mitad: reflejar el `∀` acotado `wfAll1`.

## Dónde estaba la dificultad — y por qué resultó no serlo

`wfAll1 w = ∀i < lenc w. isTermCodeE1 w (nthc w i)`, y se ataca con `pcc_bdAll_intro`
(`Meta/BdAllIntroPrf.lean:313`), cuya aplicación completa está ejercitada en aquel sondeo
(`pcc_wfAll_tracked`, ocho obligaciones administrativas descargadas). Pero:

> ⚠️ **aquel `nodeOk` estaba diseñado para NO tener binders dentro del `∀` acotado** — el
> sondeo eligió a propósito meter el `In` como **átomo** y no como su despliegue `∃`‑acotado,
> «así el cuerpo del `∀` acotado no tiene ningún binder y todo el descenso de `substfc` vive en
> nivel 0» (`sondeos/A3IsFCBTracked.lean` §2).
>
> `isTermCodeE1 wT X = shapeUn X 0 ∨ (shapeBin X 1 ∧ argsIn wT (nthc X 2))` **no tiene esa
> propiedad**: `argsIn` es un `∀` acotado **anidado**.
>
> ✅ **Y esto ya NO es un obstáculo: §4 lo resuelve** (`pcc_argsIn_pair_tracked`), sin
> reformular `isTermCodeE1` y por tanto **sin tocar `Minimal/Axioms.lean`**. La lectura de que
> era un muro venía de leer «`∀` anidado» como «hay que meterse bajo un binder», y no lo es:
> `pcc_bdAll_intro` es un lema del META‑nivel.

La mitad `hasWitF` (`DEUDA_hGuardF`) es estrictamente peor: `isFormCodeE2` tiene **ocho**
cláusulas y **dos** listas testigo, y `hasWitF` lleva un `∃∃`.
-/

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf ROBINSON_PlusPlus.Meta.Sigma1CorePrf
open ROBINSON_PlusPlus.Meta.DerivCondPrf ROBINSON_PlusPlus.Meta.TrackedAtomsPrf
open ROBINSON_PlusPlus.Meta.ChainPrf ROBINSON_PlusPlus.Meta.BdAllIntroPrf

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.HasWitTrackedPrf

/-! ## §1 · LA FORMA, COMPROBADA CONTRA EL ORIGINAL

Regla de método de §3.41.4: una abstracción de una forma medida se acompaña de un `rfl` por
instancia real. Si `Minimal/Axioms.lean` cambiara la forma de la guarda, estos dos dejan de
compilar. -/

/-- `isTC1` **es** una conjunción `∀‑acotado ∧ átomo`: la forma que `pcc_isFCB_tracked` refleja. -/
example (w c : Term) : isTC1 w c = land (wfAll1 w) (In c w) := rfl

/-- Y `hasWit` es ese `isTC1` bajo un `∃` sin cota, con el código lifteado. -/
example (c : Term) : hasWit c = Formula.ex (isTC1 (.var 0) (liftTerm 0 c)) := rfl

/-! ## §2 · LA OBLIGACIÓN DE CONTENIDO, ENUNCIADA

Idioma de `Meta/Sigma1BoundedPrf.lean`, `Meta/LineWFGuardPrf.lean` y
`Meta/D3ChainDotPrf.lean`: la deuda **se enuncia, no se postula**. Cero `axiom`.

Se deja **genérica en la imagen punteada** `WD` en vez de fijar un `wfAll1Dot` concreto: quien
la pruebe elegirá la imagen que le salga natural del `pcc_bdAll_intro`, y este módulo no debe
prejuzgarla. -/

/-- **La obligación**: reflejar el `∀` acotado `wfAll1` con el testigo `w` **abstracto**,
    entregando alguna imagen punteada `WD w`. -/
abbrev DEUDA_wfAll1_tracked (WD : Term → Term) : Prop :=
  ∀ w : Term, Prf (wfAll1 w ⇒ provFromCode (WD w))

/-! ## §3 · EL ESCALÓN: `isTC1` REFLEJADO, MÓDULO ESA OBLIGACIÓN -/

/-- ⭐ **La plantilla `isFCB` de A3, portada a `isTC1`.**

    La mitad derecha —el átomo `In c w` con **los dos argumentos abstractos**— la paga
    `pcc_In_atom_tracked`, que ya está en producción. La izquierda es la obligación. -/
theorem pcc_isTC1_tracked_of {WD : Term → Term} (hwf : DEUDA_wfAll1_tracked WD) (w c : Term) :
    Prf (isTC1 w c ⇒ provFromCode (andc (WD w) (inFormCodeFn (tcFn c) (tcFn w)))) := by
  refine prf_deduction ?_
  have h := prfH_hyp_self (isTC1 w c)
  exact PrfH_and_intro_code _ _
    (PrfH.mp _ _ _ (prf_to_prfH (hwf w) _) (PrfH_and_elim_left h))
    (PrfH.mp _ _ _ (prf_to_prfH (pcc_In_atom_tracked c w) _) (PrfH_and_elim_right h))

/-! ## §4 · ⭐ EL `∀` ACOTADO ANIDADO: `argsIn`, REFLEJADO

Aquí se ataca lo que §3 declaró «el contenido que falta». Y resulta que **no hace falta
reformular `isTermCodeE1`**: el anidamiento no es un muro.

🔑 **Por qué.** `pcc_bdAll_intro` es un lema del META‑nivel: sus hipótesis están cuantificadas
sobre `q` e `i` **en Lean**, no bajo un binder objeto. Así que anidar dos `∀` acotados en la
FÓRMULA no obliga a anidar nada en Lean: son dos aplicaciones independientes, y el cuerpo de la
interior es `pcc_child_tracked_at`, que ya está probado.

⚠️ **La única fricción real es administrativa**: `pcc_bdAll_intro` pide que la condición `CF`
sea **natural en UN solo parámetro** (`liftFormula k (CF q) = CF (liftTerm k q)`), y
`argsIn wT Y` tiene **dos** términos libres. Se empaquetan en uno con `cons`, y se leen con
`carc`/`cdrc` — que son naturales por construcción (`carc p = Term.func "carc" [p]`). Es la
misma razón por la que el kit trae los puentes `pcc_carcD_bridge_cons`/`pcc_cdrcD_bridge_cons`.
-/

/-- La imagen punteada del cuerpo de `argsIn`: el átomo `In` con la casilla en `#0`. -/
def argsInPsi (p : Term) : Term :=
  inFormCodeFn (nthcT (tcFn (cdrc p)) (varc (numeral 0))) (tcFn (carc p))

/-- `argsIn` con sus **dos** argumentos empaquetados en UN parámetro (`p = cons wT Y`). -/
def argsInPair (p : Term) : Formula := argsIn (carc p) (cdrc p)

theorem liftF_argsInPair (k : Nat) (q : Term) :
    liftFormula k (argsInPair q) = argsInPair (liftTerm k q) := by
  simp only [argsInPair, liftF_argsIn, carc, cdrc, liftTerm, liftTerms]

theorem substF_argsInPair (v : Nat) (s q : Term) :
    substFormula v s (argsInPair q) = argsInPair (substTerm v s q) := by
  simp only [argsInPair, substF_argsIn, carc, cdrc, substTerm, substTerms]

theorem liftT_argsInBnd (k : Nat) (q : Term) :
    liftTerm k (lenc (cdrc q)) = lenc (cdrc (liftTerm k q)) := by
  simp only [lenc, cdrc, liftTerm, liftTerms]

theorem substT_argsInBnd (v : Nat) (s q : Term) :
    substTerm v s (lenc (cdrc q)) = lenc (cdrc (substTerm v s q)) := by
  simp only [lenc, cdrc, substTerm, substTerms]

theorem liftT_argsInPsi (k : Nat) (q : Term) :
    liftTerm k (argsInPsi q) = argsInPsi (liftTerm k q) := by
  simp only [argsInPsi, inFormCodeFn, nthcT, tcFn, carc, cdrc, varc, funcc, cons, nil,
    zero, succ, liftTerm, liftTerms, liftTerm_numeral, liftTerm_strCode]

theorem substT_argsInPsi (v : Nat) (s q : Term) :
    substTerm v s (argsInPsi q) = argsInPsi (substTerm v s q) := by
  simp only [argsInPsi, inFormCodeFn, nthcT, tcFn, carc, cdrc, varc, funcc, cons, nil,
    zero, succ, substTerm, substTerms, substTerm_numeral, substTerm_strCode]

/-- El `substfc` del cuerpo en un índice `s` cualquiera: sólo toca la casilla. -/
theorem prf_substfc_argsInPsi (q s : Term) :
    Prf (substfc zero s (argsInPsi q)
      =eq inFormCodeFn (nthcT (tcFn (cdrc q)) s) (tcFn (carc q))) :=
  prf_substfc_inDot s _ _ _
    (prf_eq_trans (prf_substtc_nthcT zero s (tcFn (cdrc q)) (varc (numeral 0)))
      (prf_congr_nthcT (substtc_inv_tcFn (cdrc q) s) (prf_substtc_varc0 s)))
    (fun V => substtc_inv_tcFn (carc q) V)

/-- La obligación `hPsiId` de `pcc_bdAll_intro`, para este cuerpo. -/
theorem prf_argsInPsi_id (q : Term) :
    Prf (substfc zero (varc (numeral 0)) (argsInPsi q) =eq argsInPsi q) :=
  prf_substfc_argsInPsi q (varc (numeral 0))

/-- El cuerpo, en la forma EXACTA que pide `hbody`: de la condición y la cota sale el código. -/
theorem prf_argsIn_body (q i : Term) :
    Prf (argsInPair q ⇒ (lt i (lenc (cdrc q)) ⇒
      provFromCode (substfc zero (tcFn i) (argsInPsi q)))) := by
  refine prf_deduction (deduction_aux ?_ (lt i (lenc (cdrc q))) [argsInPair q] rfl)
  have hall : PrfH [lt i (lenc (cdrc q)), argsInPair q] (argsInPair q) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hlt : PrfH [lt i (lenc (cdrc q)), argsInPair q] (lt i (lenc (cdrc q))) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hspec := PrfH_spec hall i
  have heq : substFormula 0 i (argsInBody (carc q) (cdrc q))
      = Formula.impl (lt i (lenc (cdrc q))) (In (nthc (cdrc q) i) (carc q)) := by
    simp only [argsInBody, substFormula, substTerm, substTerms, lt, lenc, nthc, In,
      FOL.substTerm_liftTerm, if_true]
  rw [argsInPair, argsIn, heq] at hspec
  have hin : PrfH _ (In (nthc (cdrc q) i) (carc q)) := PrfH.mp _ _ _ hspec hlt
  have hchild := PrfH.mp _ _ _
    (PrfH.mp _ _ _ (prf_to_prfH (pcc_child_tracked_at (carc q) (cdrc q) i) _) hlt) hin
  exact PrfH.mp _ _ _
    (prf_to_prfH (prf_provCode_congr (prf_eq_symm (prf_substfc_argsInPsi q (tcFn i)))) _) hchild

/-- ⭐ **`argsIn` REFLEJADO**, con los dos argumentos abstractos (empaquetados). Es el `∀`
    acotado **anidado** que §3 daba como el contenido que faltaba, y sale de `pcc_bdAll_intro`
    sin reformular nada. -/
theorem pcc_argsIn_pair_tracked (p : Term) :
    Prf (argsInPair p ⇒
      provFromCode (bdAllCode (tcFn (lenc (cdrc p))) (argsInPsi p))) :=
  pcc_bdAll_intro argsInPair (fun q => lenc (cdrc q)) argsInPsi p
    liftF_argsInPair substF_argsInPair liftT_argsInBnd substT_argsInBnd
    liftT_argsInPsi substT_argsInPsi prf_argsInPsi_id (fun _ => by hw_auto) prf_argsIn_body

/-- La misma, desempaquetada: `wT` e `Y` abstractos y separados. -/
theorem pcc_argsIn_tracked (wT Y : Term) :
    Prf (argsInPair (cons wT Y) ⇒
      provFromCode (bdAllCode (tcFn (lenc (cdrc (cons wT Y)))) (argsInPsi (cons wT Y)))) :=
  pcc_argsIn_pair_tracked (cons wT Y)

end ROBINSON_PlusPlus.Meta.HasWitTrackedPrf

/-! ## `export` — por PROPÓSITO DECLARADO

El consumidor previsto es **C3**: quien pruebe `DEUDA_wfAll1_tracked` obtiene el reflector de
`isTC1` sin una línea más, y de ahí sale la mitad `hasWit` de `DEUDA_hGuardT` con el paso `∃`
(`pcc_exIntro_code_open`) y la fontanería `condD`. Nada lo consume todavía, y se dice en vez de
fingir una medición de consumo. -/
export ROBINSON_PlusPlus.Meta.HasWitTrackedPrf (
  DEUDA_wfAll1_tracked pcc_isTC1_tracked_of
  argsInPsi argsInPair liftF_argsInPair substF_argsInPair
  liftT_argsInBnd substT_argsInBnd liftT_argsInPsi substT_argsInPsi
  prf_substfc_argsInPsi prf_argsInPsi_id prf_argsIn_body
  pcc_argsIn_pair_tracked pcc_argsIn_tracked
)

#print axioms ROBINSON_PlusPlus.Meta.HasWitTrackedPrf.pcc_isTC1_tracked_of
#print axioms ROBINSON_PlusPlus.Meta.HasWitTrackedPrf.pcc_argsIn_pair_tracked
