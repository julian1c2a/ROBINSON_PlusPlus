import ROBINSON_PlusPlus.Meta.TrackedAtomsPrf
import ROBINSON_PlusPlus.Meta.LineWFGuardPrf
import ROBINSON_PlusPlus.Meta.LiftcCodePrf
/-!
# `Meta/HasWitTrackedPrf.lean` — `DEUDA_hGuardT`, PROBADA

`Meta/LineWFGuardPrf.lean` dejó la deuda de ADR‑020 en **dos** lemas genéricos,
`DEUDA_hGuardT` y `DEUDA_hGuardF`. Este módulo **cierra el primero**:

    pcc_hGuardT (i n : Nat) (t : Term) (hin : i < n) : DEUDA_hGuardT i n t   (§12)

Footprint = la base sancionada; net‑0 puro. La mitad `hasWitF` la cierra
`Meta/HasWitFTrackedPrf.lean` (§3.46). ⚠️ La cota `i < n` **no es un artefacto**: el puente
`(nthc t ı̇)˙ → nthcT ṫ ı̄` es `pcc_eval_nthc`, que la exige.

Las secciones §1‑§11 son el descenso, y siguen siendo el mapa de dónde está el contenido.

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
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs ROBINSON_PlusPlus.Meta.LiftcCodePrf
open ROBINSON_PlusPlus.Meta.EvalNthcPrf ROBINSON_PlusPlus.Meta.EvalListPrf

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
theorem pcc_isTC1_tracked_of [AnclaEq] {WD : Term → Term} (hwf : DEUDA_wfAll1_tracked WD) (w c : Term) :
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
theorem prf_argsIn_body [AnclaEq] (q i : Term) :
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
theorem pcc_argsIn_pair_tracked [AnclaEq] (p : Term) :
    Prf (argsInPair p ⇒
      provFromCode (bdAllCode (tcFn (lenc (cdrc p))) (argsInPsi p))) :=
  pcc_bdAll_intro argsInPair (fun q => lenc (cdrc q)) argsInPsi p
    liftF_argsInPair substF_argsInPair liftT_argsInBnd substT_argsInBnd
    liftT_argsInPsi substT_argsInPsi prf_argsInPsi_id (fun _ => by hw_auto) prf_argsIn_body

/-- La misma, desempaquetada: `wT` e `Y` abstractos y separados. -/
theorem pcc_argsIn_tracked [AnclaEq] (wT Y : Term) :
    Prf (argsInPair (cons wT Y) ⇒
      provFromCode (bdAllCode (tcFn (lenc (cdrc (cons wT Y)))) (argsInPsi (cons wT Y)))) :=
  pcc_argsIn_pair_tracked (cons wT Y)


/-! ## §5 · EL RECORRIDO DE LOS DOS DISYUNTOS DE `isTermCodeE1`

    isTermCodeE1 wT X = shapeUn X 0 ∨ (shapeBin X 1 ∧ argsIn wT (nthc X 2))

Cada mitad se refleja con piezas que ya están: la **forma** con `pcc_shape_tracked` (previa
conversión posicional→ecuacional por `prf_shapeUn_str`/`prf_shapeBin_str`) y la **pertenencia**
con `pcc_argsIn_pair_tracked` de §4. El `∨` y el `∧` los ensamblan `pcc_reflect_or` y
`pcc_reflect_and`. -/

/-- Congruencia de `argsIn` en su **primer** argumento (el testigo). Producción tenía sólo la
    del segundo (`PrfH_congr_argsIn`); ésta hace falta para el puente al par de §4. -/
theorem PrfH_congr_argsIn_wit {Γ : List Formula} {wT₁ wT₂ Y : Term}
    (h : PrfH Γ (wT₁ =eq wT₂)) (ha : PrfH Γ (argsIn wT₁ Y)) : PrfH Γ (argsIn wT₂ Y) := by
  have hS : ∀ s : Term, substFormula 0 s (argsIn (.var 0) (liftTerm 0 Y)) = argsIn s Y := by
    intro s
    simp only [substF_argsIn, substTerm, FOL.substTerm_liftTerm, if_true]
  exact (hS wT₂) ▸ PrfH_leibniz_subst (A := argsIn (.var 0) (liftTerm 0 Y)) h ((hS wT₁) ▸ ha)

/-- **El puente al par de §4**: `argsIn wT Y` es `argsInPair (cons wT Y)` módulo las dos
    ecuaciones objeto `carc (cons a b) = a` y `cdrc (cons a b) = b`. -/
theorem prf_argsIn_to_pair (wT Y : Term) :
    Prf (argsIn wT Y ⇒ argsInPair (cons wT Y)) := by
  refine prf_deduction ?_
  have h : PrfH [argsIn wT Y] (argsIn wT Y) := prfH_hyp_self _
  have h1 : PrfH [argsIn wT Y] (argsIn (carc (cons wT Y)) Y) :=
    PrfH_congr_argsIn_wit (prf_to_prfH (prf_eq_symm (prf_carc_cons wT Y)) _) h
  exact PrfH_congr_argsIn (prf_to_prfH (prf_eq_symm (prf_cdrc_cons wT Y)) _) h1

/-- La imagen punteada de `argsIn`, tal como sale de §4. -/
def argsInDot (wT Y : Term) : Term :=
  bdAllCode (tcFn (lenc (cdrc (cons wT Y)))) (argsInPsi (cons wT Y))

/-- `argsIn` reflejado con sus dos argumentos **separados**. -/
theorem pcc_argsIn_tracked' [AnclaEq] (wT Y : Term) :
    Prf (argsIn wT Y ⇒ provFromCode (argsInDot wT Y)) :=
  impT (prf_argsIn_to_pair wT Y) (pcc_argsIn_pair_tracked (cons wT Y))

/-- La forma, de la versión posicional directamente al código: junta
    `prf_shape*_str` con `pcc_shape_tracked` descurrificando la conjunción. -/
theorem pcc_shape_of_str [AnclaEq] (X : Term) (k n : Nat) (S : Formula)
    (hstr : Prf (Formula.impl S (land (consOk X)
      (land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM n)))))) :
    Prf (S ⇒ provFromCode (shapeDot (tcFn X) k n)) := by
  refine prf_deduction ?_
  have hs : PrfH [S] (land (consOk X) (land (Formula.eq (carc X) (numeralM k))
      (Formula.eq (lenc X) (numeralM n)))) :=
    PrfH.mp _ _ _ (prf_to_prfH hstr _) (prfH_hyp_self _)
  exact PrfH.mp _ _ _
    (PrfH.mp _ _ _ (prf_to_prfH (pcc_shape_tracked X k n) _) (PrfH_and_elim_left hs))
    (PrfH_and_elim_right hs)

/-! ### ⭐ LA IMAGEN DE LA FORMA QUE EXIGE `condD`, y por qué `shapeDot` no vale

⚠️ Aquí se corrige una elección que §5 hizo **antes de medir el destino**. `pcc_shape_of_str`
entrega `shapeDot` —`carc X = k̇ ∧ lenc X = ṅ`—, que es una imagen legítima de la forma… pero
`condD C t = substfc 0 ṫ (formCode C)` **no admite elegir imagen**: la impone `formCode`, y
`formCode (shapeUn X k)` es la **ECUACIÓN POSICIONAL** `Ẋ = ⟨k̄, nthcT Ẋ 1̄⟩`. Las dos fórmulas
son equivalentes en la teoría objeto, pero son **códigos distintos**, y `pcc_lineWF_tracked_of_schema`
recompone el `⇔` con el código, no con la equivalencia.

La ecuación la produce `pcc_shape_tree` (`Meta/TrackedAtomsPrf.lean`), componiendo dos piezas
que `Meta/CodeTreeReflect.lean` ya tenía probadas **por inducción sobre el árbol**. -/

/-- Los dos árboles de `isTermCodeE1`… -/
def treeUn1 (k : Nat) : CTree := .un k (.leaf 1)
def treeBin1 (k : Nat) : CTree := .bin k (.leaf 1) (.leaf 2)

/-- …y la comprobación de que **son** sus formas (regla de método: la abstracción se casa con
    el original por `rfl`). -/
example (X : Term) (k : Nat) : shapeUn X k = (X =eq (treeUn1 k).objAt X) := rfl
example (X : Term) (k : Nat) : shapeBin X k = (X =eq (treeBin1 k).objAt X) := rfl

/-- La imagen `formCode` de `shapeUn`, con el nodo como CÓDIGO. -/
noncomputable def shapeFCun (ND : Term) (k : Nat) : Term :=
  eqCodeFn ND (unT k (nthcT ND (termCode (numeralM 1))))

/-- La imagen `formCode` de `shapeBin`, con el nodo como CÓDIGO. -/
noncomputable def shapeFCbin (ND : Term) (k : Nat) : Term :=
  eqCodeFn ND (binT k (nthcT ND (termCode (numeralM 1))) (nthcT ND (termCode (numeralM 2))))

/-- ⭐ **La comprobación que decide todo esto**: son literalmente lo que `formCode` produce. -/
example (X : Term) (k : Nat) : formCode (shapeUn X k) = shapeFCun (termCode X) k := rfl
example (X : Term) (k : Nat) : formCode (shapeBin X k) = shapeFCbin (termCode X) k := rfl

/-- Y son lo que `pcc_shape_tree` entrega sobre el término objeto. -/
example (X : Term) (k : Nat) : (treeUn1 k).dotN X = unT k (nthcT (tcFn X) (termCode (numeralM 1))) := rfl
example (X : Term) (k : Nat) :
    (treeBin1 k).dotN X
      = binT k (nthcT (tcFn X) (termCode (numeralM 1))) (nthcT (tcFn X) (termCode (numeralM 2))) := rfl

/-- La forma UNARIA, reflejada a su código `formCode` sobre el término objeto. -/
theorem pcc_shapeUn_fc [AnclaEq] (X : Term) (k : Nat) :
    Prf (shapeUn X k ⇒ provFromCode (shapeFCun (tcFn X) k)) :=
  pcc_shape_tree X (treeUn1 k) Nat.le.refl _
    (prf_deduction (prfH_hyp_self _))
    (prf_deduction (PrfH_and_elim_right (PrfH_and_elim_right
      (PrfH.mp _ _ _ (prf_to_prfH (prf_shapeUn_str X k) _) (prfH_hyp_self _)))))

/-- La forma BINARIA, ídem. -/
theorem pcc_shapeBin_fc [AnclaEq] (X : Term) (k : Nat) :
    Prf (shapeBin X k ⇒ provFromCode (shapeFCbin (tcFn X) k)) :=
  pcc_shape_tree X (treeBin1 k) Nat.le.refl _
    (prf_deduction (prfH_hyp_self _))
    (prf_deduction (PrfH_and_elim_right (PrfH_and_elim_right
      (PrfH.mp _ _ _ (prf_to_prfH (prf_shapeBin_str X k) _) (prfH_hyp_self _)))))

/-! #### El transporte del NODO en la forma, con el hueco a nivel `⌜v₀⌝` -/

noncomputable def shapeUnCtx (k : Nat) : Term :=
  eqCodeFn (varc (numeral 0)) (unT k (nthcT (varc (numeral 0)) (termCode (numeralM 1))))

noncomputable def shapeBinCtx (k : Nat) : Term :=
  eqCodeFn (varc (numeral 0)) (binT k (nthcT (varc (numeral 0)) (termCode (numeralM 1)))
    (nthcT (varc (numeral 0)) (termCode (numeralM 2))))

theorem prf_substfc_shapeUnCtx (k : Nat) (U : Term) :
    Prf (substfc zero U (shapeUnCtx k) =eq shapeFCun U k) := by
  unfold shapeUnCtx shapeFCun
  refine prf_eq_trans (prf_substfc_eq zero U _ _) ?_
  refine prf_congr_eqCodeFn (prf_substtc_varc0 U) ?_
  refine prf_eq_trans (prf_substtc_unT k U _) (prf_congr_unT ?_)
  exact prf_eq_trans (prf_substtc_nthcT zero U _ _)
    (prf_congr_nthcT (prf_substtc_varc0 U) (substtc_inv_termCode_numeralM 1 U))

theorem prf_substfc_shapeBinCtx (k : Nat) (U : Term) :
    Prf (substfc zero U (shapeBinCtx k) =eq shapeFCbin U k) := by
  unfold shapeBinCtx shapeFCbin
  refine prf_eq_trans (prf_substfc_eq zero U _ _) ?_
  refine prf_congr_eqCodeFn (prf_substtc_varc0 U) ?_
  refine prf_eq_trans (prf_substtc_binT k U _ _) (prf_congr_binT ?_ ?_)
  · exact prf_eq_trans (prf_substtc_nthcT zero U _ _)
      (prf_congr_nthcT (prf_substtc_varc0 U) (substtc_inv_termCode_numeralM 1 U))
  · exact prf_eq_trans (prf_substtc_nthcT zero U _ _)
      (prf_congr_nthcT (prf_substtc_varc0 U) (substtc_inv_termCode_numeralM 2 U))

theorem PrfH_shapeFCun_transport {Γ : List Formula} (k : Nat) (U U' : Term)
    (hU : PrfH Γ (provFromCode (eqCodeFn U U')))
    (h : PrfH Γ (provFromCode (shapeFCun U k)))
    (hwC : Prf (hasWitF (shapeUnCtx k)) := by hw_auto)
    (hwU : Prf (hasWit U) := by hw_auto) (hwU' : Prf (hasWit U') := by hw_auto) :
    PrfH Γ (provFromCode (shapeFCun U' k)) := by
  have h0 : PrfH Γ (provFromCode (substfc zero U (shapeUnCtx k))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr
      (prf_eq_symm (prf_substfc_shapeUnCtx k U))) _) h
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_substfc_shapeUnCtx k U')) _)
    (PrfH_leibniz_apply _ U U' hU h0 hwC hwU hwU')

theorem PrfH_shapeFCbin_transport {Γ : List Formula} (k : Nat) (U U' : Term)
    (hU : PrfH Γ (provFromCode (eqCodeFn U U')))
    (h : PrfH Γ (provFromCode (shapeFCbin U k)))
    (hwC : Prf (hasWitF (shapeBinCtx k)) := by hw_auto)
    (hwU : Prf (hasWit U) := by hw_auto) (hwU' : Prf (hasWit U') := by hw_auto) :
    PrfH Γ (provFromCode (shapeFCbin U' k)) := by
  have h0 : PrfH Γ (provFromCode (substfc zero U (shapeBinCtx k))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr
      (prf_eq_symm (prf_substfc_shapeBinCtx k U))) _) h
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_substfc_shapeBinCtx k U')) _)
    (PrfH_leibniz_apply _ U U' hU h0 hwC hwU hwU')

/-- `liftc` sobre `termCode ⌜m⌝`: es un código CERRADO, y el puente `prf_tc_numeralM` lo
    reduce al caso `tcFn` que producción ya tiene. -/
theorem prf_liftc_termCode_numeralM (m : Nat) :
    Prf (liftc zero (termCode (numeralM m)) =eq termCode (numeralM m)) :=
  prf_eq_trans (NumCodeClosedPrf.prf_congr_liftc (prf_eq_symm (prf_tc_numeralM m)))
    (prf_eq_trans (prf_liftc_tcFn (numeralM m)) (prf_tc_numeralM m))

/-- `substfc` sobre la forma UNARIA, a nivel ARBITRARIO. -/
theorem prf_substfc_shapeFCun_at (v : Nat) (s X X' : Term) (k : Nat)
    (hX : Prf (substtc (numeral v) s X =eq X')) :
    Prf (substfc (numeral v) s (shapeFCun X k) =eq shapeFCun X' k) := by
  unfold shapeFCun
  refine prf_eq_trans (prf_substfc_eq _ s _ _) (prf_congr_eqCodeFn hX ?_)
  refine prf_eq_trans (prf_substtc_unT_at k v s _) (prf_congr_unT ?_)
  exact prf_eq_trans (prf_substtc_nthcT _ s _ _)
    (prf_congr_nthcT hX (prf_substtc_termCode_numeralM v 1 s))

/-- `substfc` sobre la forma BINARIA, a nivel ARBITRARIO. -/
theorem prf_substfc_shapeFCbin_at (v : Nat) (s X X' : Term) (k : Nat)
    (hX : Prf (substtc (numeral v) s X =eq X')) :
    Prf (substfc (numeral v) s (shapeFCbin X k) =eq shapeFCbin X' k) := by
  unfold shapeFCbin
  refine prf_eq_trans (prf_substfc_eq _ s _ _) (prf_congr_eqCodeFn hX ?_)
  refine prf_eq_trans
    (prf_substtc_binK_at (numeralM k) (fun c => liftTerm_numeralM c k) v s _ _)
    (prf_congr_binT ?_ ?_)
  · exact prf_eq_trans (prf_substtc_nthcT _ s _ _)
      (prf_congr_nthcT hX (prf_substtc_termCode_numeralM v 1 s))
  · exact prf_eq_trans (prf_substtc_nthcT _ s _ _)
      (prf_congr_nthcT hX (prf_substtc_termCode_numeralM v 2 s))

/-- **La imagen punteada de `isTermCodeE1`**, disyunto a disyunto. -/
noncomputable def isTermCodeE1Dot (wT X : Term) : Term :=
  orc (shapeFCun (tcFn X) 0)
      (andc (shapeFCbin (tcFn X) 1) (argsInDot wT (nthc X (numeralM 2))))

/-- ⭐ **EL RECORRIDO DE LOS DOS DISYUNTOS, REFLEJADO**, con `wT` y `X` **abstractos**.

    ⚠️ **Ojo a la forma de la imagen**: aquí `X` es el término OBJETO y el código sale como
    `tcFn X`. Para alimentar el `pcc_bdAll_intro` EXTERIOR hace falta la variante sobre
    CÓDIGOS —con el hueco del índice en `varc 0`, o sea `nthcT (tcFn w) (varc 0)` en vez de
    `tcFn (nthc w i)`—, que es como `sondeos/A3IsFCBTracked.lean:205` define su `PsiF`.
    ⚠️ Y hay **dos** restricciones sobre esa imagen, las dos forzadas (§3.43.5):
    (1) el índice sólo puede aparecer como `varc 0` en una ranura de código, porque `hbody`
        lo mete con `substfc zero (tcFn i) ·` ⇒ aguas abajo, accesores **dotados**;
    (2) `bdAllCode` mete la cota **dentro** del `forallc`, así que un `∀` acotado anidado
        —el que trae `argsIn`— obliga a desplazar el índice exterior (`prf_substfc_forall`
        baja a `succ v` y `liftc`‑a el sustituyendo). A3 nunca tocó (2): su `PsiF` **no tiene
        binders**, por el diseño de su §2. -/
theorem pcc_isTermCodeE1_tracked [AnclaEq] (wT X : Term) :
    Prf (isTermCodeE1 wT X ⇒ provFromCode (isTermCodeE1Dot wT X)) := by
  refine pcc_reflect_or _ _ _ _ (pcc_shapeUn_fc X 0) ?_
  exact pcc_reflect_and _ _ _ _ (pcc_shapeBin_fc X 1)
    (pcc_argsIn_tracked' wT (nthc X (numeralM 2)))


/-! ## §6 · ⭐ LA CONMUTACIÓN `substtc`/`liftc` PARA EL `Z` QUE APARECE — sin el lema general

§3.43.6 midió que el `pcc_bdAll_intro` **exterior** necesitaba

    substtc (σv) (liftc 0 t) (liftc 0 Z)  =eq  liftc 0 (substtc v t Z)

con `Z` **arbitrario** —el lema de sustitución/lift a nivel de código, que no existe y sería una
inducción objeto nueva—. **No hace falta.** Los `Z` que aparecen de verdad son códigos de
**forma conocida** (`nthcT` sobre `tcFn` y el hueco), y para ésos basta con que `liftc` sepa
atravesar sus constructores: eso es el kit de `Meta/TrackedAtomsPrf.lean`, cinco líneas por
constructor sobre axiomas que ya estaban.

Aquí se hace la cuenta entera para el `Z` del cuerpo de `wfAll1`, que es el caso que bloqueaba. -/

/-- El `Z` del cuerpo de `wfAll1`: la casilla 2 del nodo `i`‑ésimo del testigo, con el hueco
    del índice en `⌜v₀⌝`. -/
noncomputable def wfAll1Args (w : Term) : Term :=
  nthcT (nthcT (tcFn w) (varc (numeral 0))) (termCode (numeralM 2))

/-- `liftc` sobre él: el hueco pasa de `⌜v₀⌝` a `⌜v₁⌝` y todo lo demás es cerrado. -/
theorem prf_liftc_wfAll1Args (w : Term) :
    Prf (liftc zero (wfAll1Args w)
      =eq nthcT (nthcT (tcFn w) (varc (succ (numeral 0)))) (termCode (numeralM 2))) := by
  refine prf_eq_trans (prf_liftc_nthcT zero _ _) ?_
  refine prf_congr_nthcT ?_ (prf_liftc_termCode_numeralM 2)
  exact prf_eq_trans (prf_liftc_nthcT zero _ _)
    (prf_congr_nthcT (prf_liftc_tcFn w) prf_liftc_varc0)

/-- ⭐ **LA CONMUTACIÓN, HECHA Y GENÉRICA.** Bajar el `substfc` por dentro del binder ya no
    está bloqueado: el `substtc` de nivel 1 sobre el `Z` lifteado devuelve el `Z` con el hueco
    relleno. Se enuncia con el sustituyendo `s` y su lift `s'` **separados** porque los dos
    consumidores lo usan de forma distinta: `hbody` con `s := ⌜i⌝` (y `s' = s`, cerrado) y
    `hPsiId` con `s := ⌜v₀⌝` (y `s' = ⌜v₁⌝`). -/
theorem prf_substtc_liftc_wfAll1Args_gen (w s s' : Term) (hs : Prf (liftc zero s =eq s')) :
    Prf (substtc (succ zero) (liftc zero s) (liftc zero (wfAll1Args w))
      =eq nthcT (nthcT (tcFn w) s') (termCode (numeralM 2))) := by
  refine prf_eq_trans (prf_congr_substtc3 (prf_liftc_wfAll1Args w)) ?_
  refine prf_eq_trans (prf_substtc_nthcT (succ zero) _ _ _) ?_
  refine prf_congr_nthcT ?_ (prf_substtc_termCode_numeralM 1 2 _)
  refine prf_eq_trans (prf_substtc_nthcT (succ zero) _ _ _) ?_
  refine prf_congr_nthcT (prf_substtc_tcFn_at 1 _ w) ?_
  exact prf_eq_trans
    (prf_mp (prf_substtc_var_eq (succ zero) (liftc zero s) (succ (numeral 0))) (prf_refl _)) hs

/-- La instancia que consume `hbody`: el sustituyendo es `⌜i⌝`, que es CERRADO. -/
theorem prf_substtc_liftc_wfAll1Args (w s : Term) :
    Prf (substtc (succ zero) (liftc zero (tcFn s)) (liftc zero (wfAll1Args w))
      =eq nthcT (nthcT (tcFn w) (tcFn s)) (termCode (numeralM 2))) :=
  prf_substtc_liftc_wfAll1Args_gen w (tcFn s) (tcFn s) (prf_liftc_tcFn s)


/-! ## §7 · EL `pcc_bdAll_intro` EXTERIOR: `PsiF` y sus obligaciones

`CF := wfAll1` es natural en **un** parámetro (`liftF_wfAll1`, `substF_wfAll1`), así que aquí
no hay que empaquetar nada — a diferencia del `argsIn` de §4. El cuerpo `PsiF` se escribe con
accesores **dotados** y el hueco del índice en `⌜v₀⌝` (§3.43.5), y con los trozos que van
dentro del `bdAllCode` interno pre‑`liftc`‑ados (§3.43.8). `tcFn w` **no** necesita `liftc`:
es cerrado. -/

/-- El cuerpo del `∀` acotado EXTERIOR. Lleva **dos** huecos porque el índice aparece a **dos
    niveles**: `s` fuera del `bdAllCode` interno y `s'` dentro (donde De Bruijn lo desplaza).
    Escribir `⌜v₁⌝` explícitamente —en vez de `liftc 0 ⌜v₀⌝`— es lo que hace que `hPsiId`
    salga por definición y que una sola keystone sirva a los dos consumidores. -/
noncomputable def wfAll1PsiAtC (WD WD' s s' : Term) : Term :=
  orc (shapeFCun (nthcT WD s) 0)
      (andc (shapeFCbin (nthcT WD s) 1)
        (bdAllCode (lencT (nthcT (nthcT WD' s') (termCode (numeralM 2))))
          (inFormCodeFn
            (nthcT (nthcT (nthcT WD' s') (termCode (numeralM 2))) (varc (numeral 0)))
            WD')))

/-- La misma, con el testigo como TÉRMINO objeto (es `wfAll1PsiAtC (tcFn w)` por definición). -/
noncomputable def wfAll1PsiAt (w s s' : Term) : Term := wfAll1PsiAtC (tcFn w) (tcFn w) s s'

/-- El cuerpo, paramétrico en el CÓDIGO del testigo. -/
noncomputable def wfAll1PsiC (WD : Term) : Term :=
  wfAll1PsiAtC WD WD (varc (numeral 0)) (varc (succ (numeral 0)))

/-- El `PsiF` que consume `pcc_bdAll_intro`: el hueco es `⌜v₀⌝` fuera y `⌜v₁⌝` dentro. -/
noncomputable def wfAll1Psi (w : Term) : Term := wfAll1PsiC (tcFn w)

/-- La imagen de `wfAll1` **paramétrica en el código del testigo**, con la cota ya en forma de
    accesor dotado (`lencT WD`, no `tcFn (lenc w)`). Es la que admite el hueco del `∃`. -/
noncomputable def wfAll1DotC (WD : Term) : Term := bdAllCode (lencT WD) (wfAll1PsiC WD)

/-- La imagen punteada de `wfAll1` (lo que `pcc_bdAll_intro` entrega, literalmente). -/
noncomputable def wfAll1Dot (w : Term) : Term := bdAllCode (tcFn (lenc w)) (wfAll1Psi w)

/-! ### Las obligaciones ADMINISTRATIVAS -/

theorem hCl_wfAll1 : ∀ (k : Nat) (q : Term), liftFormula k (wfAll1 q) = wfAll1 (liftTerm k q) :=
  fun k q => liftF_wfAll1 k q

theorem hCs_wfAll1 :
    ∀ (v : Nat) (s q : Term), substFormula v s (wfAll1 q) = wfAll1 (substTerm v s q) :=
  fun v s q => substF_wfAll1 v s q

theorem hbl_lenc : ∀ (k : Nat) (q : Term), liftTerm k (lenc q) = lenc (liftTerm k q) := by
  intro k q; simp only [lenc, liftTerm, liftTerms]

theorem hbs_lenc : ∀ (v : Nat) (s q : Term), substTerm v s (lenc q) = lenc (substTerm v s q) := by
  intro v s q; simp only [lenc, substTerm, substTerms]

theorem hPl_wfAll1Psi :
    ∀ (k : Nat) (q : Term), liftTerm k (wfAll1Psi q) = wfAll1Psi (liftTerm k q) := by
  intro k q
  simp only [wfAll1Psi, wfAll1PsiC, wfAll1PsiAtC, shapeFCun, shapeFCbin, unT, binT, consT,
    bdAllCode, inFormCodeFn, ltCodeFn, atom2CodeFn,
    eqCodeFn, andc, orc, implc, forallc, carcT, lencT, nthcT, varc, liftc, funcc, tcFn,
    cons, nil, zero, succ, numeralM, liftTerm, liftTerms, liftTerm_numeral, liftTerm_strCode,
    liftTerm_termCode]

theorem hPs_wfAll1Psi :
    ∀ (v : Nat) (s q : Term), substTerm v s (wfAll1Psi q) = wfAll1Psi (substTerm v s q) := by
  intro v s q
  simp only [wfAll1Psi, wfAll1PsiC, wfAll1PsiAtC, shapeFCun, shapeFCbin, unT, binT, consT,
    bdAllCode, inFormCodeFn, ltCodeFn, atom2CodeFn,
    eqCodeFn, andc, orc, implc, forallc, carcT, lencT, nthcT, varc, liftc, funcc, tcFn,
    cons, nil, zero, succ, numeralM, substTerm, substTerms, substTerm_numeral, substTerm_strCode,
    substTerm_termCode]


/-! ### ⭐ LA KEYSTONE: cómo baja `substfc` por el cuerpo -/

/-- `substtc` sobre la casilla del nodo, en el nivel 0 (fuera del binder). -/
theorem prf_substtc_node0 (w s : Term) :
    Prf (substtc zero s (nthcT (tcFn w) (varc (numeral 0))) =eq nthcT (tcFn w) s) :=
  prf_eq_trans (prf_substtc_nthcT zero s _ _)
    (prf_congr_nthcT (substtc_inv_tcFn w s) (prf_substtc_varc0 s))

/-- `substtc` sobre la lista de argumentos, en el nivel 1 (dentro del binder). -/
theorem prf_substtc_args1 (w s s' : Term) (hs : Prf (liftc zero s =eq s')) :
    Prf (substtc (succ zero) (liftc zero s)
          (nthcT (nthcT (tcFn w) (varc (succ (numeral 0)))) (termCode (numeralM 2)))
      =eq nthcT (nthcT (tcFn w) s') (termCode (numeralM 2))) := by
  refine prf_eq_trans (prf_substtc_nthcT (succ zero) _ _ _) ?_
  refine prf_congr_nthcT ?_ (prf_substtc_termCode_numeralM 1 2 _)
  refine prf_eq_trans (prf_substtc_nthcT (succ zero) _ _ _) ?_
  refine prf_congr_nthcT (prf_substtc_tcFn_at 1 _ w) ?_
  exact prf_eq_trans
    (prf_mp (prf_substtc_var_eq (succ zero) (liftc zero s) (succ (numeral 0))) (prf_refl _)) hs

/-- ⭐ **LA KEYSTONE.** `substfc` baja por los dos niveles del cuerpo: el hueco exterior recibe
    `s`, y el interior —desplazado por De Bruijn— recibe `s'`, el lift de `s`. -/
theorem prf_substfc_wfAll1Psi (w s s' : Term) (hs : Prf (liftc zero s =eq s')) :
    Prf (substfc zero s (wfAll1Psi w) =eq wfAll1PsiAt w s s') := by
  have hnode := prf_substtc_node0 w s
  have hargs := prf_substtc_args1 w s s' hs
  refine prf_eq_trans (prf_substfc_or zero s _ _) (prf_congr_orc ?_ ?_)
  · exact prf_substfc_shapeFCun_at 0 s _ _ 0 hnode
  refine prf_eq_trans (prf_substfc_and zero s _ _) (prf_congr_andc ?_ ?_)
  · exact prf_substfc_shapeFCbin_at 0 s _ _ 1 hnode
  -- el `bdAllCode` interno: se entra en el binder y el nivel sube a `σ0`
  refine prf_eq_trans (prf_substfc_forall zero s _) (prf_congr_forallc ?_)
  refine prf_eq_trans (prf_substfc_impl (succ zero) (liftc zero s) _ _)
    (prf_congr_implc ?_ ?_)
  · -- la cota: `⌜v₀⌝ < lencT …`
    refine prf_eq_trans (prf_substfc_atom2CodeFn (succ zero) (liftc zero s) lt_sym _ _) ?_
    refine prf_congr_atom2CodeFn ?_ ?_
    · exact prf_mp (prf_substtc_var_lt (succ zero) (liftc zero s) (numeral 0))
        (prf_zero_lt_succ zero)
    · exact prf_eq_trans (prf_substtc_lencT (succ zero) _ _) (prf_congr_lencT hargs)
  · -- el cuerpo: `nthcT … ⌜v₀⌝ ∈ ẇ`
    refine prf_eq_trans (prf_substfc_atom2CodeFn (succ zero) (liftc zero s) in_sym _ _) ?_
    refine prf_congr_atom2CodeFn ?_ (prf_substtc_tcFn_at 1 _ w)
    refine prf_eq_trans (prf_substtc_nthcT (succ zero) _ _ _) ?_
    exact prf_congr_nthcT hargs
      (prf_mp (prf_substtc_var_lt (succ zero) (liftc zero s) (numeral 0))
        (prf_zero_lt_succ zero))

/-- La obligación `hPsiId`: sale de la keystone con `s := ⌜v₀⌝`, cuyo lift es `⌜v₁⌝`. -/
theorem hPsiId_wfAll1Psi (w : Term) :
    Prf (substfc zero (varc (numeral 0)) (wfAll1Psi w) =eq wfAll1Psi w) :=
  prf_substfc_wfAll1Psi w (varc (numeral 0)) (varc (succ (numeral 0))) prf_liftc_varc0


/-! ### El ENSAMBLAJE: `pcc_bdAll_intro` instanciado, módulo `hbody` -/

/-- La obligación `hwPsi` de ADR-020: el cuerpo tiene testigo. La paga `hw_auto`. -/
theorem hwPsi_wfAll1Psi (w : Term) : Prf (hasWitF (wfAll1Psi w)) := by hw_auto

/-- ⭐ **EL `pcc_bdAll_intro` EXTERIOR, INSTANCIADO.** Ocho de las nueve obligaciones están
    descargadas aquí; la novena, `hbody`, es lo único que queda de esta mitad de C3‑T.

    `CF := wfAll1` es natural en **un** parámetro, así que —a diferencia del `argsIn` de §4— no
    hubo que empaquetar nada con `cons`. -/
theorem pcc_wfAll1_tracked_of_hbody [AnclaEq]
    (hbody : ∀ q i : Term, Prf (wfAll1 q ⇒ (lt i (lenc q) ⇒
      provFromCode (substfc zero (tcFn i) (wfAll1Psi q)))))
    (w : Term) : Prf (wfAll1 w ⇒ provFromCode (wfAll1Dot w)) :=
  pcc_bdAll_intro wfAll1 lenc wfAll1Psi w
    hCl_wfAll1 hCs_wfAll1 hbl_lenc hbs_lenc hPl_wfAll1Psi hPs_wfAll1Psi
    hPsiId_wfAll1Psi hwPsi_wfAll1Psi hbody

/-- **Y con ella, `DEUDA_wfAll1_tracked`**: la obligación genérica de §2 queda reducida a
    `hbody`, con la imagen punteada ya elegida (`wfAll1Dot`). -/
theorem DEUDA_wfAll1_of_hbody [AnclaEq]
    (hbody : ∀ q i : Term, Prf (wfAll1 q ⇒ (lt i (lenc q) ⇒
      provFromCode (substfc zero (tcFn i) (wfAll1Psi q))))) :
    DEUDA_wfAll1_tracked wfAll1Dot :=
  fun w => pcc_wfAll1_tracked_of_hbody hbody w

/-- ⭐⭐ **Y con ella, el reflector de `isTC1` — el objetivo de §3, ya sin la hipótesis
    genérica**: de `hbody` sale directamente, con la imagen concreta. -/
theorem pcc_isTC1_tracked_of_hbody [AnclaEq]
    (hbody : ∀ q i : Term, Prf (wfAll1 q ⇒ (lt i (lenc q) ⇒
      provFromCode (substfc zero (tcFn i) (wfAll1Psi q)))))
    (w c : Term) :
    Prf (isTC1 w c ⇒ provFromCode (andc (wfAll1Dot w) (inFormCodeFn (tcFn c) (tcFn w)))) :=
  pcc_isTC1_tracked_of (DEUDA_wfAll1_of_hbody hbody) w c


/-! ## §8 · `hbody`: llevar el recorrido de §5 a la forma de CÓDIGOS

§5 refleja `isTermCodeE1` entregando la imagen sobre el **término objeto** (`tcFn X`); `hbody`
la pide sobre **códigos** (`nthcT ẇ ⌜i⌝`). El transporte tiene dos mitades:

* lo que es **igualdad OBJETO** de códigos (los `carc`/`cdrc` de un `cons`) se mueve con
  `prf_provCode_congr`, sin entrar en `Prov`;
* lo que **sólo vale dentro de `Prov`** (`pcc_eval_lenc`, `pcc_eval_nthc`) necesita Leibniz — y
  como las ocurrencias están **bajo el binder** del `bdAllCode`, con el hueco a nivel `⌜v₁⌝`
  (`Meta/TrackedAtomsPrf.lean`). -/

/-- La imagen de `argsIn` en forma de CÓDIGOS: la lista y el testigo entran como códigos. -/
noncomputable def argsInDotC (YD W : Term) : Term :=
  bdAllCode (lencT YD) (inFormCodeFn (nthcT YD (varc (numeral 0))) W)

/-- El contexto de Leibniz con el hueco de la LISTA a nivel `⌜v₁⌝`: aparece **dos veces**
    (en la cota y en el cuerpo) y una sola sustitución rellena las dos. -/
noncomputable def argsInCtx (W : Term) : Term :=
  bdAllCode (lencT (varc (succ (numeral 0))))
    (inFormCodeFn (nthcT (varc (succ (numeral 0))) (varc (numeral 0))) W)

theorem prf_substfc_argsInCtx (q s : Term) :
    Prf (substfc zero s (argsInCtx (tcFn q)) =eq argsInDotC (liftc zero s) (tcFn q)) := by
  unfold argsInCtx argsInDotC bdAllCode
  refine prf_eq_trans (prf_substfc_forall zero s _) (prf_congr_forallc ?_)
  refine prf_eq_trans (prf_substfc_impl (succ zero) (liftc zero s) _ _)
    (prf_congr_implc ?_ ?_)
  · refine prf_eq_trans (prf_substfc_atom2CodeFn (succ zero) (liftc zero s) lt_sym _ _) ?_
    refine prf_congr_atom2CodeFn
      (prf_mp (prf_substtc_var_lt (succ zero) (liftc zero s) (numeral 0)) (prf_zero_lt_succ zero))
      ?_
    exact prf_eq_trans (prf_substtc_lencT (succ zero) _ _)
      (prf_congr_lencT
        (prf_mp (prf_substtc_var_eq (succ zero) (liftc zero s) (succ (numeral 0)))
          (prf_refl _)))
  · refine prf_eq_trans (prf_substfc_atom2CodeFn (succ zero) (liftc zero s) in_sym _ _) ?_
    refine prf_congr_atom2CodeFn ?_ (prf_substtc_tcFn_at 1 _ q)
    refine prf_eq_trans (prf_substtc_nthcT (succ zero) _ _ _) ?_
    exact prf_congr_nthcT
      (prf_mp (prf_substtc_var_eq (succ zero) (liftc zero s) (succ (numeral 0))) (prf_refl _))
      (prf_mp (prf_substtc_var_lt (succ zero) (liftc zero s) (numeral 0)) (prf_zero_lt_succ zero))

/-- ⭐ **El transporte de la LISTA dentro de `Prov`**, con las dos ocurrencias a la vez. -/
theorem PrfH_argsInDotC_transport {Γ : List Formula} (q YD YD' : Term)
    (hY : PrfH Γ (provFromCode (eqCodeFn YD YD')))
    (h : PrfH Γ (provFromCode (argsInDotC YD (tcFn q))))
    (hcY : Prf (liftc zero YD =eq YD)) (hcY' : Prf (liftc zero YD' =eq YD'))
    (hwY : Prf (hasWit YD) := by hw_auto) (hwY' : Prf (hasWit YD') := by hw_auto)
    (hwC : Prf (hasWitF (argsInCtx (tcFn q))) := by hw_auto) :
    PrfH Γ (provFromCode (argsInDotC YD' (tcFn q))) := by
  have hcong : ∀ u u' : Term, Prf (u =eq u') →
      Prf (argsInDotC u (tcFn q) =eq argsInDotC u' (tcFn q)) := by
    intro u u' hu
    exact prf_congr_bdAllCode (prf_congr_lencT hu)
      (prf_congr_atom2CodeFn (prf_congr_nthcT hu (prf_refl _)) (prf_refl _))
  have h0 : PrfH Γ (provFromCode (substfc zero YD (argsInCtx (tcFn q)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_eq_symm
      (prf_eq_trans (prf_substfc_argsInCtx q YD) (hcong _ _ hcY)))) _) h
  have h1 : PrfH Γ (provFromCode (substfc zero YD' (argsInCtx (tcFn q)))) :=
    PrfH_leibniz_apply _ YD YD' hY h0 hwC hwY hwY'
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr
    (prf_eq_trans (prf_substfc_argsInCtx q YD') (hcong _ _ hcY'))) _) h1


/-- El cuerpo del `argsIn` dotado es invariante bajo `substfc` de NIVEL 1: su única variable
    de código es `⌜v₀⌝`, que vive en el nivel 0. -/
theorem prf_substfc_argsInBody_inv (q Y : Term) : ∀ u : Term,
    Prf (substfc (succ zero) u (inFormCodeFn (nthcT (tcFn Y) (varc (numeral 0))) (tcFn q))
      =eq inFormCodeFn (nthcT (tcFn Y) (varc (numeral 0))) (tcFn q)) := by
  intro u
  refine prf_eq_trans (prf_substfc_atom2CodeFn (succ zero) u in_sym _ _) ?_
  refine prf_congr_atom2CodeFn ?_ (prf_substtc_tcFn_at 1 u q)
  refine prf_eq_trans (prf_substtc_nthcT (succ zero) u _ _) ?_
  exact prf_congr_nthcT (prf_substtc_tcFn_at 1 u Y)
    (prf_mp (prf_substtc_var_lt (succ zero) u (numeral 0)) (prf_zero_lt_succ zero))

/-- ⭐ **`argsIn` reflejado EN FORMA DE CÓDIGOS.** Es `pcc_argsIn_tracked'` (§4) con dos
    transportes: los `carc`/`cdrc` del `cons` son igualdad **objeto** y se mueven con
    `prf_provCode_congr`; el paso de `(lenc Y)˙` a `lencT Ẏ` **sólo vale dentro de `Prov`**
    (`pcc_eval_lenc`) y va por `PrfH_bdAllCode_congr_bnd`, con el hueco bajo el binder. -/
theorem pcc_argsIn_trackedC [AnclaEq] (q Y : Term) :
    Prf (argsIn q Y ⇒ provFromCode (argsInDotC (tcFn Y) (tcFn q))) := by
  refine prf_deduction ?_
  have h0 : PrfH [argsIn q Y] (provFromCode (argsInDot q Y)) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_argsIn_tracked' q Y) _) (prfH_hyp_self _)
  -- (i) los `carc`/`cdrc` del `cons`: igualdad OBJETO
  have hc : Prf (tcFn (carc (cons q Y)) =eq tcFn q) := prf_congr_tcFn (prf_carc_cons q Y)
  have hd : Prf (tcFn (cdrc (cons q Y)) =eq tcFn Y) := prf_congr_tcFn (prf_cdrc_cons q Y)
  have hl : Prf (tcFn (lenc (cdrc (cons q Y))) =eq tcFn (lenc Y)) :=
    prf_congr_tcFn (prf_congr_lenc (prf_cdrc_cons q Y))
  have hmeta : Prf (argsInDot q Y
      =eq bdAllCode (tcFn (lenc Y))
            (inFormCodeFn (nthcT (tcFn Y) (varc (numeral 0))) (tcFn q))) := by
    unfold argsInDot argsInPsi
    exact prf_congr_bdAllCode hl
      (prf_congr_atom2CodeFn (prf_congr_nthcT hd (prf_refl _)) hc)
  have h1 : PrfH [argsIn q Y] (provFromCode (bdAllCode (tcFn (lenc Y))
      (inFormCodeFn (nthcT (tcFn Y) (varc (numeral 0))) (tcFn q)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr hmeta) _) h0
  -- (ii) la cota, DENTRO de `Prov`
  have hbnd : PrfH [argsIn q Y]
      (provFromCode (eqCodeFn (tcFn (lenc Y)) (lencT (tcFn Y)))) :=
    PrfH_eq_symm_code _ _ (substtc_inv_lencT (substtc_inv_tcFn Y))
      (prf_to_prfH (pcc_eval_lenc Y) _) (by hw_auto) (by hw_auto)
  exact PrfH_bdAllCode_congr_bnd _ _ _ (prf_substfc_argsInBody_inv q Y)
    (prf_liftc_tcFn (lenc Y))
    (prf_eq_trans (prf_liftc_lencT zero (tcFn Y)) (prf_congr_lencT (prf_liftc_tcFn Y)))
    hbnd h1


/-- El recorrido de `isTermCodeE1`, con la imagen ya en forma de **CÓDIGOS**: el nodo entra
    como `ND` (un código) en vez de como `tcFn X`. Es lo que pide `hbody`. -/
noncomputable def isTermCodeE1DotC (q ND : Term) : Term :=
  orc (shapeFCun ND 0)
      (andc (shapeFCbin ND 1) (argsInDotC (nthcT ND (termCode (numeralM 2))) (tcFn q)))

/-- ⭐ **EL RECORRIDO EN FORMA DE CÓDIGOS.**

    ⚠️ La ecuación `ND = Ẋ` entra como **antecedente OBJETO**, no como hipótesis Lean: en el
    punto de uso sólo se tiene bajo el contexto (viene de `pcc_eval_nthc` con la cota), y el
    proyecto **no tiene debilitamiento de contexto** para `PrfH` (deuda B6b). Metiéndola en el
    antecedente, el `or`-elim la conserva en su rama.

    Y cada disyunto se transporta **dentro de su rama**, que es donde están las hipótesis: la
    cota `2̇ < lenc X` que necesita `pcc_eval_nthc` sólo existe en la rama `shapeBin`. -/
theorem pcc_isTermCodeE1_trackedC [AnclaEq] (q X ND : Term)
    (hNDinv : ∀ W, Prf (substtc zero W ND =eq ND))
    (hNDlift : Prf (liftc zero ND =eq ND))
    (hwND : Prf (hasWit ND) := by hw_auto) :
    Prf (provFromCode (eqCodeFn ND (tcFn X)) ⇒
      (isTermCodeE1 q X ⇒ provFromCode (isTermCodeE1DotC q ND))) := by
  refine prf_deduction (deduction_aux ?_ (isTermCodeE1 q X)
    [provFromCode (eqCodeFn ND (tcFn X))] rfl)
  have hE1 : PrfH [isTermCodeE1 q X, provFromCode (eqCodeFn ND (tcFn X))]
      (isTermCodeE1 q X) := PrfH.hyp _ _ (List.Mem.head _)
  refine PrfH_or_elim hE1 ?_ ?_
  · -- rama UNARIA
    have hND : PrfH [shapeUn X 0, isTermCodeE1 q X, provFromCode (eqCodeFn ND (tcFn X))]
        (provFromCode (eqCodeFn ND (tcFn X))) :=
      PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    have hsym : PrfH [shapeUn X 0, isTermCodeE1 q X, provFromCode (eqCodeFn ND (tcFn X))]
        (provFromCode (eqCodeFn (tcFn X) ND)) :=
      PrfH_eq_symm_code _ _ hNDinv hND (by hw_auto) (by hw_auto)
    have hsh : PrfH [shapeUn X 0, isTermCodeE1 q X, provFromCode (eqCodeFn ND (tcFn X))]
        (shapeUn X 0) := PrfH.hyp _ _ (List.Mem.head _)
    have h0 : PrfH [shapeUn X 0, isTermCodeE1 q X, provFromCode (eqCodeFn ND (tcFn X))]
        (provFromCode (shapeFCun (tcFn X) 0)) :=
      PrfH.mp _ _ _ (prf_to_prfH (pcc_shapeUn_fc X 0) _) hsh
    exact PrfH_orL_code _ _ (PrfH_shapeFCun_transport 0 (tcFn X) ND hsym h0)
  · -- rama BINARIA
    have hND : PrfH [land (shapeBin X 1) (argsIn q (nthc X (numeralM 2))),
        isTermCodeE1 q X, provFromCode (eqCodeFn ND (tcFn X))]
        (provFromCode (eqCodeFn ND (tcFn X))) :=
      PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    have hsym : PrfH [land (shapeBin X 1) (argsIn q (nthc X (numeralM 2))), isTermCodeE1 q X,
        provFromCode (eqCodeFn ND (tcFn X))]
        (provFromCode (eqCodeFn (tcFn X) ND)) :=
      PrfH_eq_symm_code _ _ hNDinv hND (by hw_auto) (by hw_auto)
    have hand : PrfH [land (shapeBin X 1) (argsIn q (nthc X (numeralM 2))), isTermCodeE1 q X,
        provFromCode (eqCodeFn ND (tcFn X))]
        (land (shapeBin X 1) (argsIn q (nthc X (numeralM 2)))) :=
      PrfH.hyp _ _ (List.Mem.head _)
    have hsb : PrfH [land (shapeBin X 1) (argsIn q (nthc X (numeralM 2))), isTermCodeE1 q X,
        provFromCode (eqCodeFn ND (tcFn X))]
        (shapeBin X 1) := PrfH_and_elim_left hand
    have hargs : PrfH [land (shapeBin X 1) (argsIn q (nthc X (numeralM 2))), isTermCodeE1 q X,
        provFromCode (eqCodeFn ND (tcFn X))]
        (argsIn q (nthc X (numeralM 2))) := PrfH_and_elim_right hand
    have hstr : PrfH [land (shapeBin X 1) (argsIn q (nthc X (numeralM 2))), isTermCodeE1 q X,
        provFromCode (eqCodeFn ND (tcFn X))]
        (land (consOk X) (land (Formula.eq (carc X) (numeralM 1))
        (Formula.eq (lenc X) (numeralM 3)))) :=
      PrfH.mp _ _ _ (prf_to_prfH (prf_shapeBin_str X 1) _) hsb
    have hlt2 : PrfH [land (shapeBin X 1) (argsIn q (nthc X (numeralM 2))), isTermCodeE1 q X,
        provFromCode (eqCodeFn ND (tcFn X))]
        (lt (numeralM 2) (lenc X)) :=
      PrfH_lt_subst2
        (PrfH_eq_symm (PrfH_and_elim_right (PrfH_and_elim_right hstr)))
        (prf_to_prfH (prf_lt_numeralM (by omega : 2 < 3)) _)
    have hsh0 : PrfH [land (shapeBin X 1) (argsIn q (nthc X (numeralM 2))), isTermCodeE1 q X,
        provFromCode (eqCodeFn ND (tcFn X))]
        (provFromCode (shapeFCbin (tcFn X) 1)) :=
      PrfH.mp _ _ _ (prf_to_prfH (pcc_shapeBin_fc X 1) _) hsb
    have hshD : PrfH [land (shapeBin X 1) (argsIn q (nthc X (numeralM 2))), isTermCodeE1 q X,
        provFromCode (eqCodeFn ND (tcFn X))]
        (provFromCode (shapeFCbin ND 1)) :=
      PrfH_shapeFCbin_transport 1 (tcFn X) ND hsym hsh0
    have hA0 : PrfH [land (shapeBin X 1) (argsIn q (nthc X (numeralM 2))), isTermCodeE1 q X,
        provFromCode (eqCodeFn ND (tcFn X))]
        (provFromCode (argsInDotC (tcFn (nthc X (numeralM 2))) (tcFn q))) :=
      PrfH.mp _ _ _ (prf_to_prfH (pcc_argsIn_trackedC q (nthc X (numeralM 2))) _) hargs
    have hev : PrfH [land (shapeBin X 1) (argsIn q (nthc X (numeralM 2))), isTermCodeE1 q X,
        provFromCode (eqCodeFn ND (tcFn X))]
        (provFromCode (eqCodeFn (nthcT (tcFn X) (termCode (numeralM 2)))
        (tcFn (nthc X (numeralM 2))))) :=
      PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_congr_eqCodeFn
          (prf_congr_nthcT (prf_refl _) (prf_tc_numeralM 2)) (prf_refl _))) _)
        (PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_nthc X (numeralM 2)) _) hlt2)
    have hcg : PrfH [land (shapeBin X 1) (argsIn q (nthc X (numeralM 2))), isTermCodeE1 q X,
        provFromCode (eqCodeFn ND (tcFn X))]
        (provFromCode (eqCodeFn (nthcT ND (termCode (numeralM 2)))
        (nthcT (tcFn X) (termCode (numeralM 2))))) :=
      PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_nthcT_arg1_code (termCode (numeralM 2)) ND (tcFn X)
        (prf_substtc_termCode_numeralM 0 2) hNDinv) _) hND
    have hfwd : PrfH [land (shapeBin X 1) (argsIn q (nthc X (numeralM 2))), isTermCodeE1 q X,
        provFromCode (eqCodeFn ND (tcFn X))]
        (provFromCode (eqCodeFn (nthcT ND (termCode (numeralM 2)))
        (tcFn (nthc X (numeralM 2))))) :=
      PrfH_eq_trans_code _ _ _
        (substtc_inv_nthcT hNDinv (prf_substtc_termCode_numeralM 0 2))
        hcg hev (by hw_auto) (by hw_auto) (by hw_auto)
    have hchain : PrfH [land (shapeBin X 1) (argsIn q (nthc X (numeralM 2))), isTermCodeE1 q X,
        provFromCode (eqCodeFn ND (tcFn X))]
        (provFromCode (eqCodeFn (tcFn (nthc X (numeralM 2)))
        (nthcT ND (termCode (numeralM 2))))) :=
      PrfH_eq_symm_code _ _ (substtc_inv_nthcT hNDinv (prf_substtc_termCode_numeralM 0 2))
        hfwd (by hw_auto) (by hw_auto)
    have hAD : PrfH [land (shapeBin X 1) (argsIn q (nthc X (numeralM 2))), isTermCodeE1 q X,
        provFromCode (eqCodeFn ND (tcFn X))]
        (provFromCode (argsInDotC (nthcT ND (termCode (numeralM 2))) (tcFn q))) :=
      PrfH_argsInDotC_transport q _ _ hchain hA0
        (prf_liftc_tcFn (nthc X (numeralM 2)))
        (prf_eq_trans (prf_liftc_nthcT zero ND (termCode (numeralM 2)))
          (prf_congr_nthcT hNDlift (prf_liftc_termCode_numeralM 2)))
    exact PrfH_orR_code _ _ (PrfH_and_intro_code _ _ hshD hAD)


/-- ⭐⭐ **`hbody`, LA NOVENA OBLIGACIÓN.** De `wfAll1 q` y la cota sale el cuerpo dotado con el
    hueco relleno. Junta todo: instancia el `∀` objeto, saca la ecuación del nodo de
    `pcc_eval_nthc`, aplica el recorrido en forma de códigos y transporta con la keystone. -/
theorem hbody_wfAll1 [AnclaEq] : ∀ q i : Term, Prf (wfAll1 q ⇒ (lt i (lenc q) ⇒
    provFromCode (substfc zero (tcFn i) (wfAll1Psi q)))) := by
  intro q i
  refine prf_deduction (deduction_aux ?_ (lt i (lenc q)) [wfAll1 q] rfl)
  have hlt : PrfH [lt i (lenc q), wfAll1 q] (lt i (lenc q)) := PrfH.hyp _ _ (List.Mem.head _)
  have hwf : PrfH [lt i (lenc q), wfAll1 q] (wfAll1 q) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hND : PrfH [lt i (lenc q), wfAll1 q]
      (provFromCode (eqCodeFn (nthcT (tcFn q) (tcFn i)) (tcFn (nthc q i)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_nthc q i) _) hlt
  have hspec := PrfH_spec hwf i
  have heq : substFormula 0 i (wfAll1Body q)
      = Formula.impl (lt i (lenc q)) (isTermCodeE1 q (nthc q i)) := by
    simp only [wfAll1Body, substFormula, substTerm, substTerms, lt, lenc, nthc,
      substF_isTermCodeE1, FOL.substTerm_liftTerm, if_true]
  rw [wfAll1, heq] at hspec
  have hE1 : PrfH [lt i (lenc q), wfAll1 q] (isTermCodeE1 q (nthc q i)) :=
    PrfH.mp _ _ _ hspec hlt
  have hNDinv : ∀ W, Prf (substtc zero W (nthcT (tcFn q) (tcFn i)) =eq nthcT (tcFn q) (tcFn i)) :=
    substtc_inv_nthcT (substtc_inv_tcFn q) (substtc_inv_tcFn i)
  have hNDlift : Prf (liftc zero (nthcT (tcFn q) (tcFn i)) =eq nthcT (tcFn q) (tcFn i)) :=
    prf_eq_trans (prf_liftc_nthcT zero (tcFn q) (tcFn i))
      (prf_congr_nthcT (prf_liftc_tcFn q) (prf_liftc_tcFn i))
  have hC : PrfH [lt i (lenc q), wfAll1 q]
      (provFromCode (isTermCodeE1DotC q (nthcT (tcFn q) (tcFn i)))) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH
      (pcc_isTermCodeE1_trackedC q (nthc q i) (nthcT (tcFn q) (tcFn i)) hNDinv hNDlift) _)
      hND) hE1
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_eq_symm
    (prf_substfc_wfAll1Psi q (tcFn i) (tcFn i) (prf_liftc_tcFn i)))) _) hC

/-! ## §9 · ⭐⭐⭐ `DEUDA_wfAll1_tracked`, PROBADA — y con ella el reflector de `isTC1` -/

theorem pcc_wfAll1_tracked [AnclaEq] (w : Term) : Prf (wfAll1 w ⇒ provFromCode (wfAll1Dot w)) :=
  pcc_wfAll1_tracked_of_hbody hbody_wfAll1 w

theorem DEUDA_wfAll1_tracked_proved [AnclaEq] : DEUDA_wfAll1_tracked wfAll1Dot :=
  DEUDA_wfAll1_of_hbody hbody_wfAll1

/-- ⭐⭐⭐ **EL REFLECTOR DE `isTC1`, SIN HIPÓTESIS**: `isTC1 w c ⇒ Prov(⌜isTC1 ẇ ċ⌝)`, con
    **`w` y `c` abstractos**. Es la mitad `wfAll1` de `DEUDA_hGuardT`, cerrada. -/
theorem pcc_isTC1_tracked [AnclaEq] (w c : Term) :
    Prf (isTC1 w c ⇒ provFromCode (andc (wfAll1Dot w) (inFormCodeFn (tcFn c) (tcFn w)))) :=
  pcc_isTC1_tracked_of DEUDA_wfAll1_tracked_proved w c


/-! ## §10 · LA COTA EN FORMA DE ACCESOR DOTADO: `wfAll1DotC`

`pcc_bdAll_intro` entrega la cota como `(lenc w)˙`; el `condD` de ADR‑020 la pide como
`lencT ẇ` — porque `formCode (wfAll1 #0)` codifica `lenc #1` como `lencT ⌜v₁⌝` y `substfc`
rellena el hueco con `ẇ`, **sin** volver a meter el `lenc` dentro del punto.

El salto de `(lenc w)˙` a `lencT ẇ` es `pcc_eval_lenc`, y **sólo vale dentro de `Prov`**: va
por `PrfH_bdAllCode_congr_bnd`, exactamente como `pcc_argsIn_trackedC` (§8) hace con su lista.
La obligación que ese lema pide —que el cuerpo sea invariante bajo `substfc` de NIVEL 1— es
`hPinv_wfAll1Psi`: el cuerpo sólo tiene `⌜v₀⌝` fuera del `bdAllCode` interno y `⌜v₀⌝`/`⌜v₁⌝`
dentro (niveles 0 y, bajo el binder, 0 y 1), así que el nivel 1 exterior no toca nada. -/

/-- **El cuerpo de `wfAll1` es invariante bajo `substfc` de nivel 1.**

    Es la obligación `hPinv` de `PrfH_bdAllCode_congr_bnd`. Fuera del `bdAllCode` interno sólo
    aparece `⌜v₀⌝` (nivel 0 < 1); dentro, el binder sube el nivel a 2 y allí viven `⌜v₀⌝` (el
    índice interno) y `⌜v₁⌝` (el externo desplazado), los dos por debajo de 2. -/
theorem hPinv_wfAll1Psi (w : Term) : ∀ u : Term,
    Prf (substfc (succ zero) u (wfAll1Psi w) =eq wfAll1Psi w) := by
  intro u
  have hnode : Prf (substtc (succ zero) u (nthcT (tcFn w) (varc (numeral 0)))
      =eq nthcT (tcFn w) (varc (numeral 0))) :=
    prf_eq_trans (prf_substtc_nthcT (succ zero) u _ _)
      (prf_congr_nthcT (prf_substtc_tcFn_at 1 u w)
        (prf_mp (prf_substtc_var_lt (succ zero) u (numeral 0)) (prf_zero_lt_succ zero)))
  have hargs : Prf (substtc (succ (succ zero)) (liftc zero u)
      (nthcT (nthcT (tcFn w) (varc (succ (numeral 0)))) (termCode (numeralM 2)))
      =eq nthcT (nthcT (tcFn w) (varc (succ (numeral 0)))) (termCode (numeralM 2))) := by
    refine prf_eq_trans (prf_substtc_nthcT (succ (succ zero)) _ _ _) ?_
    refine prf_congr_nthcT ?_ (prf_substtc_termCode_numeralM 2 2 _)
    refine prf_eq_trans (prf_substtc_nthcT (succ (succ zero)) _ _ _) ?_
    exact prf_congr_nthcT (prf_substtc_tcFn_at 2 _ w)
      (prf_mp (prf_substtc_var_lt (succ (succ zero)) _ (succ (numeral 0)))
        (prf_lt_succ_self (succ zero)))
  unfold wfAll1Psi wfAll1PsiC wfAll1PsiAtC
  refine prf_eq_trans (prf_substfc_or (succ zero) u _ _) (prf_congr_orc ?_ ?_)
  · exact prf_substfc_shapeFCun_at 1 u _ _ 0 hnode
  refine prf_eq_trans (prf_substfc_and (succ zero) u _ _) (prf_congr_andc ?_ ?_)
  · exact prf_substfc_shapeFCbin_at 1 u _ _ 1 hnode
  refine prf_eq_trans (prf_substfc_forall (succ zero) u _) (prf_congr_forallc ?_)
  refine prf_eq_trans (prf_substfc_impl (succ (succ zero)) (liftc zero u) _ _)
    (prf_congr_implc ?_ ?_)
  · refine prf_eq_trans
      (prf_substfc_atom2CodeFn (succ (succ zero)) (liftc zero u) lt_sym _ _) ?_
    refine prf_congr_atom2CodeFn
      (prf_mp (prf_substtc_var_lt (succ (succ zero)) _ (numeral 0))
        (prf_zero_lt_succ (succ zero))) ?_
    exact prf_eq_trans (prf_substtc_lencT (succ (succ zero)) _ _) (prf_congr_lencT hargs)
  · refine prf_eq_trans
      (prf_substfc_atom2CodeFn (succ (succ zero)) (liftc zero u) in_sym _ _) ?_
    refine prf_congr_atom2CodeFn ?_ (prf_substtc_tcFn_at 2 _ w)
    refine prf_eq_trans (prf_substtc_nthcT (succ (succ zero)) _ _ _) ?_
    exact prf_congr_nthcT hargs
      (prf_mp (prf_substtc_var_lt (succ (succ zero)) _ (numeral 0))
        (prf_zero_lt_succ (succ zero)))

/-- ⭐ **`wfAll1` reflejado con la cota ya DOTADA.** Misma prueba que `pcc_argsIn_trackedC`:
    `pcc_eval_lenc` dentro de `Prov` y `PrfH_bdAllCode_congr_bnd` para meterlo bajo el binder. -/
theorem pcc_wfAll1_trackedC [AnclaEq] (w : Term) :
    Prf (wfAll1 w ⇒ provFromCode (wfAll1DotC (tcFn w))) := by
  refine prf_deduction ?_
  have h0 : PrfH [wfAll1 w] (provFromCode (wfAll1Dot w)) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_wfAll1_tracked w) _) (prfH_hyp_self _)
  have hbnd : PrfH [wfAll1 w] (provFromCode (eqCodeFn (tcFn (lenc w)) (lencT (tcFn w)))) :=
    PrfH_eq_symm_code _ _ (substtc_inv_lencT (substtc_inv_tcFn w))
      (prf_to_prfH (pcc_eval_lenc w) _) (by hw_auto) (by hw_auto)
  exact PrfH_bdAllCode_congr_bnd _ _ _ (hPinv_wfAll1Psi w)
    (prf_liftc_tcFn (lenc w))
    (prf_eq_trans (prf_liftc_lencT zero (tcFn w)) (prf_congr_lencT (prf_liftc_tcFn w)))
    hbnd h0


/-! ## §11 · ⭐ EL PASO `∃`: DE `isTC1` A `hasWit`, CON EL HUECO DEL TESTIGO

`hasWit c = ∃x. isTC1 x c` (`Minimal/Axioms.lean:1052`), así que subir §9 por el `∃` es
`pcc_exIntro_code_open` (`Meta/Delta0ReflectPrf.lean:74`) — la variante **abierta**, que no
exige clausurar `Ac`.

⭐ **Lo que hay que modelar bien es el hueco.** Bajo el `∃`, el testigo es una **VARIABLE DE
CÓDIGO QUE SE DESPLAZA**: `⌜v₀⌝` en el cuerpo, `⌜v₁⌝` dentro del `∀` de `wfAll1`, y `⌜v₂⌝`
dentro del `∀` anidado de `argsIn`. Por eso `wfAll1PsiAtC` lleva **dos** ranuras de testigo
(`WD` y `WD'`) y no una: con testigo cerrado (`tcFn w`) coinciden, con el hueco del `∃` no. -/

/-- La imagen de `wfAll1` con las **dos** ranuras del testigo separadas. Con testigo cerrado es
    `wfAll1DotC` (por `rfl`); con el hueco del `∃` es `wfAll1DotAtC ⌜v₁⌝ ⌜v₂⌝`. -/
noncomputable def wfAll1DotAtC (WD WD' : Term) : Term :=
  bdAllCode (lencT WD) (wfAll1PsiAtC WD WD' (varc (numeral 0)) (varc (numeral 1)))

example (WD : Term) : wfAll1DotC WD = wfAll1DotAtC WD WD := rfl

/-- ⭐ **EL CUERPO DEL `∃`**, con el testigo como hueco `⌜v₀⌝` y la casilla `I` del testigo de
    línea `T` ya en forma de accesor dotado. Es el `Ac` de `pcc_exIntro_code_open`. -/
noncomputable def hasWitAc (T I : Term) : Term :=
  andc (wfAll1DotAtC (varc (numeral 1)) (varc (numeral 2)))
       (inFormCodeFn (nthcT T I) (varc (numeral 0)))

/-- ⭐ **LA KEYSTONE DEL `∃`, GENERALIZADA** — a nivel arbitrario y con las dos ranuras de
    testigo abiertas. La necesita C3‑F, donde el `∃∃` obliga a rellenar los huecos **en dos
    pasadas** (primero `wF` a nivel 1, luego `wT` a nivel 0) y por tanto a niveles distintos de
    `zero`. `prf_substfc_wfAll1DotAtC` es su instancia `v = 0` con testigo cerrado. -/
theorem prf_substfc_wfAll1DotAtC_gen (v : Nat) (s WD WD' RD RD' : Term)
    (hD : Prf (substtc (numeral (v + 1)) (liftc zero s) WD =eq RD))
    (hD' : Prf (substtc (numeral (v + 2)) (liftc zero (liftc zero s)) WD' =eq RD')) :
    Prf (substfc (numeral v) s (wfAll1DotAtC WD WD') =eq wfAll1DotAtC RD RD') := by
  have hi1 : Prf (substtc (numeral (v + 1)) (liftc zero s) (varc (numeral 0))
      =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt _ _ (numeral 0)) (prf_gnum_lt (by omega : 0 < v + 1))
  have hi2 : Prf (substtc (numeral (v + 2)) (liftc zero (liftc zero s)) (varc (numeral 0))
      =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt _ _ (numeral 0)) (prf_gnum_lt (by omega : 0 < v + 2))
  have hj2 : Prf (substtc (numeral (v + 2)) (liftc zero (liftc zero s)) (varc (numeral 1))
      =eq varc (numeral 1)) :=
    prf_mp (prf_substtc_var_lt _ _ (numeral 1)) (prf_gnum_lt (by omega : 1 < v + 2))
  have hnode : Prf (substtc (numeral (v + 1)) (liftc zero s) (nthcT WD (varc (numeral 0)))
      =eq nthcT RD (varc (numeral 0))) :=
    prf_eq_trans (prf_substtc_nthcT _ _ _ _) (prf_congr_nthcT hD hi1)
  have hargs : Prf (substtc (numeral (v + 2)) (liftc zero (liftc zero s))
      (nthcT (nthcT WD' (varc (numeral 1))) (termCode (numeralM 2)))
      =eq nthcT (nthcT RD' (varc (numeral 1))) (termCode (numeralM 2))) := by
    refine prf_eq_trans (prf_substtc_nthcT _ _ _ _) ?_
    exact prf_congr_nthcT
      (prf_eq_trans (prf_substtc_nthcT _ _ _ _) (prf_congr_nthcT hD' hj2))
      (prf_substtc_termCode_numeralM (v + 2) 2 _)
  unfold wfAll1DotAtC wfAll1PsiAtC
  refine prf_eq_trans (prf_substfc_forall _ s _) (prf_congr_forallc ?_)
  refine prf_eq_trans (prf_substfc_impl _ (liftc zero s) _ _) (prf_congr_implc ?_ ?_)
  · exact prf_eq_trans (prf_substfc_atom2CodeFn _ (liftc zero s) lt_sym _ _)
      (prf_congr_atom2CodeFn hi1
        (prf_eq_trans (prf_substtc_lencT _ _ _) (prf_congr_lencT hD)))
  refine prf_eq_trans (prf_substfc_or _ (liftc zero s) _ _) (prf_congr_orc ?_ ?_)
  · exact prf_substfc_shapeFCun_at (v + 1) (liftc zero s) _ _ 0 hnode
  refine prf_eq_trans (prf_substfc_and _ (liftc zero s) _ _) (prf_congr_andc ?_ ?_)
  · exact prf_substfc_shapeFCbin_at (v + 1) (liftc zero s) _ _ 1 hnode
  refine prf_eq_trans (prf_substfc_forall _ (liftc zero s) _) (prf_congr_forallc ?_)
  refine prf_eq_trans (prf_substfc_impl _ (liftc zero (liftc zero s)) _ _)
    (prf_congr_implc ?_ ?_)
  · exact prf_eq_trans
      (prf_substfc_atom2CodeFn _ (liftc zero (liftc zero s)) lt_sym _ _)
      (prf_congr_atom2CodeFn hi2
        (prf_eq_trans (prf_substtc_lencT _ _ _) (prf_congr_lencT hargs)))
  · exact prf_eq_trans
      (prf_substfc_atom2CodeFn _ (liftc zero (liftc zero s)) in_sym _ _)
      (prf_congr_atom2CodeFn
        (prf_eq_trans (prf_substtc_nthcT _ _ _ _) (prf_congr_nthcT hargs hi2)) hD')

/-- ⭐ **LA KEYSTONE DEL `∃`**: rellenar el hueco baja por los TRES niveles a la vez. El
    testigo entra como `U` fuera, `liftc 0 U` bajo el `∀` de `wfAll1` y `liftc 0 (liftc 0 U)`
    bajo el de `argsIn`; con `U` cerrado los dos `liftc` se colapsan y queda `wfAll1DotC U`.
    Es la instancia `v = 0` de `prf_substfc_wfAll1DotAtC_gen`. -/
theorem prf_substfc_wfAll1DotAtC (U : Term) (hU : Prf (liftc zero U =eq U)) :
    Prf (substfc zero U (wfAll1DotAtC (varc (numeral 1)) (varc (numeral 2)))
      =eq wfAll1DotC U) :=
  prf_substfc_wfAll1DotAtC_gen 0 U (varc (numeral 1)) (varc (numeral 2)) U U
    (prf_eq_trans
      (prf_mp (prf_substtc_var_eq (numeral 1) (liftc zero U) (numeral 1)) (prf_refl _)) hU)
    (prf_eq_trans
      (prf_mp (prf_substtc_var_eq (numeral 2) (liftc zero (liftc zero U)) (numeral 2))
        (prf_refl _))
      (prf_eq_trans (NumCodeClosedPrf.prf_congr_liftc hU) hU))

/-- Y con el `In` al lado: el cuerpo entero, con el hueco relleno. -/
theorem prf_substfc_hasWitAc (T I U : Term) (hU : Prf (liftc zero U =eq U))
    (hT : ∀ W, Prf (substtc zero W T =eq T)) (hI : ∀ W, Prf (substtc zero W I =eq I)) :
    Prf (substfc zero U (hasWitAc T I)
      =eq andc (wfAll1DotC U) (inFormCodeFn (nthcT T I) U)) := by
  unfold hasWitAc
  refine prf_eq_trans (prf_substfc_and zero U _ _)
    (prf_congr_andc (prf_substfc_wfAll1DotAtC U hU) ?_)
  refine prf_eq_trans (prf_substfc_atom2CodeFn zero U in_sym _ _) ?_
  exact prf_congr_atom2CodeFn
    (prf_eq_trans (prf_substtc_nthcT zero U _ _) (prf_congr_nthcT (hT U) (hI U)))
    (prf_substtc_varc0 U)

/-- `liftTerm` atraviesa el cuerpo del ∃: todo lo demas es codigo CERRADO. Es lo que necesita
    la guarda `hwA` de `pcc_exIntro_code_open`, que la pide bajo el lift. -/
theorem liftTerm_hasWitAc (c : Nat) (T I : Term) :
    liftTerm c (hasWitAc T I) = hasWitAc (liftTerm c T) (liftTerm c I) := by
  simp only [hasWitAc, wfAll1DotAtC, wfAll1PsiAtC, shapeFCun, shapeFCbin, unT, binT, consT,
    bdAllCode, inFormCodeFn, ltCodeFn, atom2CodeFn, eqCodeFn, andc, orc, implc, forallc,
    lencT, nthcT, varc, funcc, cons, nil, zero, succ, numeralM,
    liftTerm, liftTerms, liftTerm_numeral, liftTerm_strCode, liftTerm_termCode]

/-- ⭐⭐ **EL CUERPO DEL `∃`, REFLEJADO Y CERRADO POR `∃`-intro.**

    Las dos mitades son §10 (`pcc_wfAll1_trackedC`, con la cota ya dotada) y
    `pcc_In_atom_tracked`; el único transporte es de `(nthc t ı̇)˙` a `nthcT ṫ ı̄`, que es
    `pcc_eval_nthc` y **por eso pide la cota** `ı̇ < lenc t` — la que `Hcond` trae de
    `lenc t = ṅ`. -/
theorem pcc_isTC1_exc_body [AnclaEq] (t : Term) (i : Nat) :
    Prf (isTC1 (.var 0) (nthc t (numeralM i)) ⇒
      (lt (numeralM i) (lenc t) ⇒
        provFromCode (exc (hasWitAc (tcFn t) (termCode (numeralM i)))))) := by
  refine prf_deduction (deduction_aux ?_ (lt (numeralM i) (lenc t))
    [isTC1 (.var 0) (nthc t (numeralM i))] rfl)
  have hlt : PrfH [lt (numeralM i) (lenc t), isTC1 (.var 0) (nthc t (numeralM i))]
      (lt (numeralM i) (lenc t)) := PrfH.hyp _ _ (List.Mem.head _)
  have hTC : PrfH [lt (numeralM i) (lenc t), isTC1 (.var 0) (nthc t (numeralM i))]
      (isTC1 (.var 0) (nthc t (numeralM i))) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hL : PrfH [lt (numeralM i) (lenc t), isTC1 (.var 0) (nthc t (numeralM i))]
      (provFromCode (wfAll1DotC (tcFn (.var 0)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_wfAll1_trackedC (.var 0)) _) (PrfH_and_elim_left hTC)
  have hR0 : PrfH [lt (numeralM i) (lenc t), isTC1 (.var 0) (nthc t (numeralM i))]
      (provFromCode (inFormCodeFn (tcFn (nthc t (numeralM i))) (tcFn (.var 0)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_In_atom_tracked (nthc t (numeralM i)) (.var 0)) _)
      (PrfH_and_elim_right hTC)
  have hev : PrfH [lt (numeralM i) (lenc t), isTC1 (.var 0) (nthc t (numeralM i))]
      (provFromCode (eqCodeFn (nthcT (tcFn t) (termCode (numeralM i)))
        (tcFn (nthc t (numeralM i))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_congr_eqCodeFn
        (prf_congr_nthcT (prf_refl _) (prf_tc_numeralM i)) (prf_refl _))) _)
      (PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_nthc t (numeralM i)) _) hlt)
  have hsym : PrfH [lt (numeralM i) (lenc t), isTC1 (.var 0) (nthc t (numeralM i))]
      (provFromCode (eqCodeFn (tcFn (nthc t (numeralM i)))
        (nthcT (tcFn t) (termCode (numeralM i))))) :=
    PrfH_eq_symm_code _ _
      (substtc_inv_nthcT (substtc_inv_tcFn t) (prf_substtc_termCode_numeralM 0 i))
      hev (by hw_auto) (by hw_auto)
  have hR : PrfH [lt (numeralM i) (lenc t), isTC1 (.var 0) (nthc t (numeralM i))]
      (provFromCode (inFormCodeFn (nthcT (tcFn t) (termCode (numeralM i))) (tcFn (.var 0)))) :=
    PrfH_in_transport _ _ _ (substtc_inv_tcFn (.var 0)) hsym hR0
  have hAnd := PrfH_and_intro_code _ _ hL hR
  have hsub : PrfH [lt (numeralM i) (lenc t), isTC1 (.var 0) (nthc t (numeralM i))]
      (provFromCode (substfc zero (tcFn (.var 0))
        (hasWitAc (tcFn t) (termCode (numeralM i))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_eq_symm
      (prf_substfc_hasWitAc (tcFn t) (termCode (numeralM i)) (tcFn (.var 0))
        (prf_liftc_tcFn (.var 0)) (substtc_inv_tcFn t)
        (prf_substtc_termCode_numeralM 0 i)))) _) hAnd
  exact PrfH.mp _ _ _ (prf_to_prfH (pcc_exIntro_code_open
    (hasWitAc (tcFn t) (termCode (numeralM i))) (tcFn (.var 0))
    (by simp only [liftTerm_hasWitAc, liftTerm_tcFn, liftTerm_termCode]; hw_auto)
    (by simp only [liftTerm_tcFn]; hw_auto)) _) hsub


/-- ⭐⭐⭐ **`hasWit` REFLEJADO**, con `t` abstracto: la mitad de `DEUDA_hGuardT` que no es
    fontanería de `condD`. El `∃` objeto se elimina con `prf_ex_elim_imp`, y lo único que hay
    que cuidar es que el lift atraviese la imagen — que lo hace, porque salvo `ṫ` todo el
    cuerpo es código cerrado (`liftTerm_hasWitAc`). -/
theorem pcc_hasWit_exc [AnclaEq] (t : Term) (i : Nat) :
    Prf (hasWit (nthc t (numeralM i)) ⇒
      (lt (numeralM i) (lenc t) ⇒
        provFromCode (exc (hasWitAc (tcFn t) (termCode (numeralM i)))))) := by
  unfold hasWit
  refine prf_ex_elim_imp ?_
  refine PrfH.mp _ _ _ ?_ (prfH_hyp_self _)
  simpa only [liftFormula, liftFormula_provFromCode_open, liftTerm_exc_open,
    liftTerm_hasWitAc, liftTerm_tcFn, liftTerm_termCode, isTC1, land, wfAll1, wfAll1Body,
    lt, lenc, nthc, liftTerm, liftTerms, liftTerm_numeralM, cons, nil, zero, succ,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceGT, reduceIte, if_true]
    using prf_to_prfH (pcc_isTC1_exc_body (liftTerm 0 t) i)
      [isTC1 (.var 0) (liftTerm 0 (nthc t (numeralM i)))]


/-! ## §12 · LA FONTANERÍA `condD`, Y `DEUDA_hGuardT` CERRADA

`condD C t = substfc 0 ṫ (formCode C)` — un `substfc` **objeto** sobre un código literal.
`prf_substfc_arith_open` (`Meta/SubstCodeOpenPrf.lean:138`) lo convierte en la función META
`substCodeF`, y a partir de ahí ya no hay teoría: es una igualdad de términos que sale por
`rfl`, porque cada cláusula de `substCodeF` cae sobre su constructor de código.

⚠️ El único punto donde `rfl` no llega es el **índice de casilla**: `numeralM i` con `i`
variable no reduce, y hace falta `substCodeT_closed` (que es un teorema, no una defeq). Por eso
el `rfl` se enuncia con el índice ABSTRACTO y la instancia se cierra con un `rw`. -/

/-- ⭐ **`condD` de la guarda, COMPUTADO** — con el índice abstracto, por `rfl`. -/
theorem substCodeF_hasWit_nthc (t I : Term) :
    substCodeF 0 (tcFn t) (hasWit (nthc (.var 0) I))
      = exc (hasWitAc (liftc zero (tcFn t))
              (substCodeT 1 (liftc zero (tcFn t)) (liftTerm 0 I))) := rfl

/-- Congruencia de `hasWitAc` en la ranura de la LÍNEA. -/
theorem prf_congr_hasWitAc_T {T T' I : Term} (h : Prf (T =eq T')) :
    Prf (hasWitAc T I =eq hasWitAc T' I) := by
  unfold hasWitAc
  exact prf_congr_andc (prf_refl _)
    (prf_congr_atom2CodeFn (prf_congr_nthcT h (prf_refl _)) (prf_refl _))

/-- ⭐ **La alineación**: el código que `condD` impone **es** la imagen que §11 produce.
    El `liftc` que `substCodeF` deja al entrar en el `∃` se colapsa con `prf_liftc_tcFn`. -/
theorem prf_condD_hasWit_eq (t : Term) (i : Nat) :
    Prf (condD (hasWit (nthc (.var 0) (numeralM i))) t
      =eq exc (hasWitAc (tcFn t) (termCode (numeralM i)))) := by
  have h : substCodeF 0 (tcFn t) (hasWit (nthc (.var 0) (numeralM i)))
      = exc (hasWitAc (liftc zero (tcFn t)) (termCode (numeralM i))) := by
    rw [substCodeF_hasWit_nthc, liftTerm_numeralM,
      substCodeT_closed 1 (liftc zero (tcFn t)) (numeralM i) (fun c => liftTerm_numeralM c i)]
  refine prf_eq_trans ?_ (prf_congr_exc (prf_congr_hasWitAc_T (prf_liftc_tcFn t)))
  show Prf (substfc zero (tcFn t) (formCode (hasWit (nthc (.var 0) (numeralM i)))) =eq _)
  rw [← h]
  exact prf_substfc_arith_open 0 (tcFn t) _

/-- ⭐⭐⭐ **`DEUDA_hGuardT` PROBADA**, para toda casilla `i` bajo la longitud canónica `n`.

    La cota `i < n` **no es un artefacto**: el transporte `(nthc t ı̇)˙ → nthcT ṫ ı̄` es
    `pcc_eval_nthc`, y sin la cota ese paso no existe. `Hcond` ya trae `lenc t = ṅ`, así que la
    única condición que se añade es aritmética y la cumplen las cuatro casillas reales. -/
theorem pcc_hGuardT [AnclaEq] (i n : Nat) (t : Term) (hin : i < n) :
    ROBINSON_PlusPlus.Meta.LineWFGuardPrf.DEUDA_hGuardT i n t := by
  show Prf (lineWF t ⇒ ((lenc t =eq numeralM n) ⇒
    (substFormula 0 t (hasWit (nthc (.var 0) (numeralM i))) ⇒
      provFromCode (condD (hasWit (nthc (.var 0) (numeralM i))) t))))
  have hsub : substFormula 0 t (hasWit (nthc (.var 0) (numeralM i)))
      = hasWit (nthc t (numeralM i)) := by
    simp only [substF_hasWit, nthc, substTerm, substTerms, substTerm_numeralM,
      FOL.substTerm_liftTerm, if_true]
  rw [hsub]
  refine prf_deduction (deduction_aux (deduction_aux ?_
    (hasWit (nthc t (numeralM i))) [lenc t =eq numeralM n, lineWF t] rfl)
    (lenc t =eq numeralM n) [lineWF t] rfl)
  have hhw : PrfH [hasWit (nthc t (numeralM i)), lenc t =eq numeralM n, lineWF t]
      (hasWit (nthc t (numeralM i))) := PrfH.hyp _ _ (List.Mem.head _)
  have hlenc : PrfH [hasWit (nthc t (numeralM i)), lenc t =eq numeralM n, lineWF t]
      (lenc t =eq numeralM n) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hlt : PrfH [hasWit (nthc t (numeralM i)), lenc t =eq numeralM n, lineWF t]
      (lt (numeralM i) (lenc t)) :=
    PrfH_lt_subst2 (PrfH_eq_symm hlenc)
      (prf_to_prfH (prf_lt_numeralM hin) _)
  have hexc : PrfH [hasWit (nthc t (numeralM i)), lenc t =eq numeralM n, lineWF t]
      (provFromCode (exc (hasWitAc (tcFn t) (termCode (numeralM i))))) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (pcc_hasWit_exc t i) _) hhw) hlt
  exact PrfH.mp _ _ _
    (prf_to_prfH (prf_provCode_congr (prf_eq_symm (prf_condD_hasWit_eq t i))) _) hexc

/-- **Las CUATRO casillas `hasWit` de los 7 esquemas, con su longitud canónica**: todas cumplen
    `i < n`, así que `pcc_hGuardT` las cubre todas. (Tags 9, 10 y 13; los otros cuatro tags no
    llevan ninguna casilla `wit`.) -/
example : [(3,4), (3,4), (3,5), (4,5)].all (fun p => decide (p.1 < p.2)) = true := by decide


/-- ⭐⭐ **MEDIA CASCADA, DESCARGADA.** `hGuard_of_deudas` (`Meta/LineWFGuardPrf.lean`) pedía las
    DOS deudas; la mitad `wit` ya no es hipótesis. Lo único que se añade es que los índices de
    las casillas `wit` de la lista caigan bajo la longitud canónica — cosa que cumplen las
    cuatro reales, y que la cota de `pcc_eval_nthc` hace inevitable. -/
theorem hGuard_of_deudaF [AnclaEq] (t : Term) (n : Nat) (C : Formula)
    (hC : ROBINSON_PlusPlus.Meta.LineWFGuardPrf.Hcond n t C)
    (hF : ∀ i, ROBINSON_PlusPlus.Meta.LineWFGuardPrf.DEUDA_hGuardF i n t)
    (gs : List ROBINSON_PlusPlus.Meta.LineWFGuardPrf.GuardSlot)
    (hgs : ∀ i, List.Mem (ROBINSON_PlusPlus.Meta.LineWFGuardPrf.GuardSlot.wit i) gs → i < n) :
    ROBINSON_PlusPlus.Meta.LineWFGuardPrf.Hcond n t
      (ROBINSON_PlusPlus.Meta.LineWFGuardPrf.guardedCond gs C) :=
  ROBINSON_PlusPlus.Meta.LineWFGuardPrf.hcond_absorbe_cascade t n C hC gs
    (fun g hg => by
      cases g with
      | wit i => exact pcc_hGuardT i n t (hgs i hg)
      | witF i => exact hF i)

end ROBINSON_PlusPlus.Meta.HasWitTrackedPrf

/-! ## `export` — por PROPÓSITO DECLARADO

El consumidor previsto es **C3**: quien pruebe `DEUDA_wfAll1_tracked` obtiene el reflector de
`isTC1` sin una línea más, y de ahí sale la mitad `hasWit` de `DEUDA_hGuardT` con el paso `∃`
(`pcc_exIntro_code_open`) y la fontanería `condD`. Nada lo consume todavía, y se dice en vez de
fingir una medición de consumo. -/
export ROBINSON_PlusPlus.Meta.HasWitTrackedPrf (
  DEUDA_wfAll1_tracked pcc_isTC1_tracked_of
  PrfH_congr_argsIn_wit prf_argsIn_to_pair argsInDot pcc_argsIn_tracked'
  pcc_shape_of_str isTermCodeE1Dot pcc_isTermCodeE1_tracked
  treeUn1 treeBin1 shapeFCun shapeFCbin pcc_shapeUn_fc pcc_shapeBin_fc
  shapeUnCtx shapeBinCtx prf_substfc_shapeUnCtx prf_substfc_shapeBinCtx
  PrfH_shapeFCun_transport PrfH_shapeFCbin_transport
  prf_liftc_termCode_numeralM prf_substfc_shapeFCun_at prf_substfc_shapeFCbin_at
  wfAll1Args prf_liftc_wfAll1Args prf_substtc_liftc_wfAll1Args_gen
  prf_substtc_liftc_wfAll1Args
  wfAll1PsiAt wfAll1Psi wfAll1Dot
  hCl_wfAll1 hCs_wfAll1 hbl_lenc hbs_lenc hPl_wfAll1Psi hPs_wfAll1Psi
  prf_substtc_node0 prf_substtc_args1 prf_substfc_wfAll1Psi hPsiId_wfAll1Psi hwPsi_wfAll1Psi
  pcc_wfAll1_tracked_of_hbody DEUDA_wfAll1_of_hbody pcc_isTC1_tracked_of_hbody
  wfAll1PsiAtC wfAll1PsiC wfAll1DotC hPinv_wfAll1Psi pcc_wfAll1_trackedC
  wfAll1DotAtC hasWitAc prf_substfc_wfAll1DotAtC_gen prf_substfc_wfAll1DotAtC prf_substfc_hasWitAc liftTerm_hasWitAc pcc_isTC1_exc_body pcc_hasWit_exc
  substCodeF_hasWit_nthc prf_congr_hasWitAc_T prf_condD_hasWit_eq pcc_hGuardT hGuard_of_deudaF
  argsInPsi argsInPair liftF_argsInPair substF_argsInPair
  liftT_argsInBnd substT_argsInBnd liftT_argsInPsi substT_argsInPsi
  prf_substfc_argsInPsi prf_argsInPsi_id prf_argsIn_body
  pcc_argsIn_pair_tracked pcc_argsIn_tracked
)

#print axioms ROBINSON_PlusPlus.Meta.HasWitTrackedPrf.pcc_wfAll1_trackedC
#print axioms ROBINSON_PlusPlus.Meta.HasWitTrackedPrf.pcc_hasWit_exc
#print axioms ROBINSON_PlusPlus.Meta.HasWitTrackedPrf.pcc_hGuardT
#print axioms ROBINSON_PlusPlus.Meta.HasWitTrackedPrf.hGuard_of_deudaF
#print axioms ROBINSON_PlusPlus.Meta.HasWitTrackedPrf.pcc_isTC1_tracked_of
#print axioms ROBINSON_PlusPlus.Meta.HasWitTrackedPrf.pcc_argsIn_pair_tracked
#print axioms ROBINSON_PlusPlus.Meta.HasWitTrackedPrf.pcc_isTermCodeE1_tracked
