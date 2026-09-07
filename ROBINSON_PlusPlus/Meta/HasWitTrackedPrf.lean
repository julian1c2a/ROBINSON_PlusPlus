import ROBINSON_PlusPlus.Meta.TrackedAtomsPrf
import ROBINSON_PlusPlus.Meta.LineWFGuardPrf
import ROBINSON_PlusPlus.Meta.LiftcCodePrf
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
theorem pcc_argsIn_tracked' (wT Y : Term) :
    Prf (argsIn wT Y ⇒ provFromCode (argsInDot wT Y)) :=
  impT (prf_argsIn_to_pair wT Y) (pcc_argsIn_pair_tracked (cons wT Y))

/-- La forma, de la versión posicional directamente al código: junta
    `prf_shape*_str` con `pcc_shape_tracked` descurrificando la conjunción. -/
theorem pcc_shape_of_str (X : Term) (k n : Nat) (S : Formula)
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

/-- **La imagen punteada de `isTermCodeE1`**, disyunto a disyunto. -/
noncomputable def isTermCodeE1Dot (wT X : Term) : Term :=
  orc (shapeDot (tcFn X) 0 2)
      (andc (shapeDot (tcFn X) 1 3) (argsInDot wT (nthc X (numeralM 2))))

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
theorem pcc_isTermCodeE1_tracked (wT X : Term) :
    Prf (isTermCodeE1 wT X ⇒ provFromCode (isTermCodeE1Dot wT X)) := by
  refine pcc_reflect_or _ _ _ _ (pcc_shape_of_str X 0 2 _ (prf_shapeUn_str X 0)) ?_
  exact pcc_reflect_and _ _ _ _
    (pcc_shape_of_str X 1 3 _ (prf_shapeBin_str X 1))
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
  nthcT (nthcT (tcFn w) (varc (numeral 0))) (tcFn (numeralM 2))

/-- `liftc` sobre él: el hueco pasa de `⌜v₀⌝` a `⌜v₁⌝` y todo lo demás es cerrado. -/
theorem prf_liftc_wfAll1Args (w : Term) :
    Prf (liftc zero (wfAll1Args w)
      =eq nthcT (nthcT (tcFn w) (varc (succ (numeral 0)))) (tcFn (numeralM 2))) := by
  refine prf_eq_trans (prf_liftc_nthcT zero _ _) ?_
  refine prf_congr_nthcT ?_ (prf_liftc_tcFn (numeralM 2))
  exact prf_eq_trans (prf_liftc_nthcT zero _ _)
    (prf_congr_nthcT (prf_liftc_tcFn w) prf_liftc_varc0)

/-- ⭐ **LA CONMUTACIÓN, HECHA Y GENÉRICA.** Bajar el `substfc` por dentro del binder ya no
    está bloqueado: el `substtc` de nivel 1 sobre el `Z` lifteado devuelve el `Z` con el hueco
    relleno. Se enuncia con el sustituyendo `s` y su lift `s'` **separados** porque los dos
    consumidores lo usan de forma distinta: `hbody` con `s := ⌜i⌝` (y `s' = s`, cerrado) y
    `hPsiId` con `s := ⌜v₀⌝` (y `s' = ⌜v₁⌝`). -/
theorem prf_substtc_liftc_wfAll1Args_gen (w s s' : Term) (hs : Prf (liftc zero s =eq s')) :
    Prf (substtc (succ zero) (liftc zero s) (liftc zero (wfAll1Args w))
      =eq nthcT (nthcT (tcFn w) s') (tcFn (numeralM 2))) := by
  refine prf_eq_trans (prf_congr_substtc3 (prf_liftc_wfAll1Args w)) ?_
  refine prf_eq_trans (prf_substtc_nthcT (succ zero) _ _ _) ?_
  refine prf_congr_nthcT ?_ (prf_substtc_tcFn_at 1 _ (numeralM 2))
  refine prf_eq_trans (prf_substtc_nthcT (succ zero) _ _ _) ?_
  refine prf_congr_nthcT (prf_substtc_tcFn_at 1 _ w) ?_
  exact prf_eq_trans
    (prf_mp (prf_substtc_var_eq (succ zero) (liftc zero s) (succ (numeral 0))) (prf_refl _)) hs

/-- La instancia que consume `hbody`: el sustituyendo es `⌜i⌝`, que es CERRADO. -/
theorem prf_substtc_liftc_wfAll1Args (w s : Term) :
    Prf (substtc (succ zero) (liftc zero (tcFn s)) (liftc zero (wfAll1Args w))
      =eq nthcT (nthcT (tcFn w) (tcFn s)) (tcFn (numeralM 2))) :=
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
noncomputable def wfAll1PsiAt (w s s' : Term) : Term :=
  orc (shapeDot (nthcT (tcFn w) s) 0 2)
      (andc (shapeDot (nthcT (tcFn w) s) 1 3)
        (bdAllCode (lencT (nthcT (nthcT (tcFn w) s') (tcFn (numeralM 2))))
          (inFormCodeFn
            (nthcT (nthcT (nthcT (tcFn w) s') (tcFn (numeralM 2))) (varc (numeral 0)))
            (tcFn w))))

/-- El `PsiF` que consume `pcc_bdAll_intro`: el hueco es `⌜v₀⌝` fuera y `⌜v₁⌝` dentro. -/
noncomputable def wfAll1Psi (w : Term) : Term :=
  wfAll1PsiAt w (varc (numeral 0)) (varc (succ (numeral 0)))

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
  simp only [wfAll1Psi, wfAll1PsiAt, shapeDot, bdAllCode, inFormCodeFn, ltCodeFn, atom2CodeFn,
    eqCodeFn, andc, orc, implc, forallc, carcT, lencT, nthcT, varc, liftc, funcc, tcFn,
    cons, nil, zero, succ, numeralM, liftTerm, liftTerms, liftTerm_numeral, liftTerm_strCode]

theorem hPs_wfAll1Psi :
    ∀ (v : Nat) (s q : Term), substTerm v s (wfAll1Psi q) = wfAll1Psi (substTerm v s q) := by
  intro v s q
  simp only [wfAll1Psi, wfAll1PsiAt, shapeDot, bdAllCode, inFormCodeFn, ltCodeFn, atom2CodeFn,
    eqCodeFn, andc, orc, implc, forallc, carcT, lencT, nthcT, varc, liftc, funcc, tcFn,
    cons, nil, zero, succ, numeralM, substTerm, substTerms, substTerm_numeral, substTerm_strCode]


/-! ### ⭐ LA KEYSTONE: cómo baja `substfc` por el cuerpo -/

/-- `substtc` sobre la casilla del nodo, en el nivel 0 (fuera del binder). -/
theorem prf_substtc_node0 (w s : Term) :
    Prf (substtc zero s (nthcT (tcFn w) (varc (numeral 0))) =eq nthcT (tcFn w) s) :=
  prf_eq_trans (prf_substtc_nthcT zero s _ _)
    (prf_congr_nthcT (substtc_inv_tcFn w s) (prf_substtc_varc0 s))

/-- `substtc` sobre la lista de argumentos, en el nivel 1 (dentro del binder). -/
theorem prf_substtc_args1 (w s s' : Term) (hs : Prf (liftc zero s =eq s')) :
    Prf (substtc (succ zero) (liftc zero s)
          (nthcT (nthcT (tcFn w) (varc (succ (numeral 0)))) (tcFn (numeralM 2)))
      =eq nthcT (nthcT (tcFn w) s') (tcFn (numeralM 2))) := by
  refine prf_eq_trans (prf_substtc_nthcT (succ zero) _ _ _) ?_
  refine prf_congr_nthcT ?_ (prf_substtc_tcFn_at 1 _ (numeralM 2))
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
  · exact prf_substfc_shapeDot s _ _ 0 2 hnode
  refine prf_eq_trans (prf_substfc_and zero s _ _) (prf_congr_andc ?_ ?_)
  · exact prf_substfc_shapeDot s _ _ 1 3 hnode
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
theorem pcc_wfAll1_tracked_of_hbody
    (hbody : ∀ q i : Term, Prf (wfAll1 q ⇒ (lt i (lenc q) ⇒
      provFromCode (substfc zero (tcFn i) (wfAll1Psi q)))))
    (w : Term) : Prf (wfAll1 w ⇒ provFromCode (wfAll1Dot w)) :=
  pcc_bdAll_intro wfAll1 lenc wfAll1Psi w
    hCl_wfAll1 hCs_wfAll1 hbl_lenc hbs_lenc hPl_wfAll1Psi hPs_wfAll1Psi
    hPsiId_wfAll1Psi hwPsi_wfAll1Psi hbody

/-- **Y con ella, `DEUDA_wfAll1_tracked`**: la obligación genérica de §2 queda reducida a
    `hbody`, con la imagen punteada ya elegida (`wfAll1Dot`). -/
theorem DEUDA_wfAll1_of_hbody
    (hbody : ∀ q i : Term, Prf (wfAll1 q ⇒ (lt i (lenc q) ⇒
      provFromCode (substfc zero (tcFn i) (wfAll1Psi q))))) :
    DEUDA_wfAll1_tracked wfAll1Dot :=
  fun w => pcc_wfAll1_tracked_of_hbody hbody w

/-- ⭐⭐ **Y con ella, el reflector de `isTC1` — el objetivo de §3, ya sin la hipótesis
    genérica**: de `hbody` sale directamente, con la imagen concreta. -/
theorem pcc_isTC1_tracked_of_hbody
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
theorem pcc_argsIn_trackedC (q Y : Term) :
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
  orc (shapeDot ND 0 2)
      (andc (shapeDot ND 1 3) (argsInDotC (nthcT ND (tcFn (numeralM 2))) (tcFn q)))

/-- ⭐ **EL RECORRIDO EN FORMA DE CÓDIGOS.**

    ⚠️ La ecuación `ND = Ẋ` entra como **antecedente OBJETO**, no como hipótesis Lean: en el
    punto de uso sólo se tiene bajo el contexto (viene de `pcc_eval_nthc` con la cota), y el
    proyecto **no tiene debilitamiento de contexto** para `PrfH` (deuda B6b). Metiéndola en el
    antecedente, el `or`-elim la conserva en su rama.

    Y cada disyunto se transporta **dentro de su rama**, que es donde están las hipótesis: la
    cota `2̇ < lenc X` que necesita `pcc_eval_nthc` sólo existe en la rama `shapeBin`. -/
theorem pcc_isTermCodeE1_trackedC (q X ND : Term)
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
        (provFromCode (shapeDot (tcFn X) 0 2)) :=
      PrfH.mp _ _ _ (prf_to_prfH (pcc_shape_of_str X 0 2 _ (prf_shapeUn_str X 0)) _) hsh
    exact PrfH_orL_code _ _
      (PrfH_shapeDot_transport (tcFn X) ND 0 2 (substtc_inv_tcFn X) hNDinv hsym h0)
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
      ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
        (PrfH_eq_symm (PrfH_and_elim_right (PrfH_and_elim_right hstr)))
        (prf_to_prfH (prf_lt_numeralM (by omega : 2 < 3)) _)
    have hsh0 : PrfH [land (shapeBin X 1) (argsIn q (nthc X (numeralM 2))), isTermCodeE1 q X,
        provFromCode (eqCodeFn ND (tcFn X))]
        (provFromCode (shapeDot (tcFn X) 1 3)) :=
      PrfH.mp _ _ _ (prf_to_prfH (pcc_shape_of_str X 1 3 _ (prf_shapeBin_str X 1)) _) hsb
    have hshD : PrfH [land (shapeBin X 1) (argsIn q (nthc X (numeralM 2))), isTermCodeE1 q X,
        provFromCode (eqCodeFn ND (tcFn X))]
        (provFromCode (shapeDot ND 1 3)) :=
      PrfH_shapeDot_transport (tcFn X) ND 1 3 (substtc_inv_tcFn X) hNDinv hsym hsh0
    have hA0 : PrfH [land (shapeBin X 1) (argsIn q (nthc X (numeralM 2))), isTermCodeE1 q X,
        provFromCode (eqCodeFn ND (tcFn X))]
        (provFromCode (argsInDotC (tcFn (nthc X (numeralM 2))) (tcFn q))) :=
      PrfH.mp _ _ _ (prf_to_prfH (pcc_argsIn_trackedC q (nthc X (numeralM 2))) _) hargs
    have hev : PrfH [land (shapeBin X 1) (argsIn q (nthc X (numeralM 2))), isTermCodeE1 q X,
        provFromCode (eqCodeFn ND (tcFn X))]
        (provFromCode (eqCodeFn (nthcT (tcFn X) (tcFn (numeralM 2)))
        (tcFn (nthc X (numeralM 2))))) :=
      PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_nthc X (numeralM 2)) _) hlt2
    have hcg : PrfH [land (shapeBin X 1) (argsIn q (nthc X (numeralM 2))), isTermCodeE1 q X,
        provFromCode (eqCodeFn ND (tcFn X))]
        (provFromCode (eqCodeFn (nthcT ND (tcFn (numeralM 2)))
        (nthcT (tcFn X) (tcFn (numeralM 2))))) :=
      PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_nthcT_arg1_code (tcFn (numeralM 2)) ND (tcFn X)
        (substtc_inv_tcFn (numeralM 2)) hNDinv) _) hND
    have hfwd : PrfH [land (shapeBin X 1) (argsIn q (nthc X (numeralM 2))), isTermCodeE1 q X,
        provFromCode (eqCodeFn ND (tcFn X))]
        (provFromCode (eqCodeFn (nthcT ND (tcFn (numeralM 2)))
        (tcFn (nthc X (numeralM 2))))) :=
      PrfH_eq_trans_code _ _ _ (substtc_inv_nthcT hNDinv (substtc_inv_tcFn (numeralM 2)))
        hcg hev (by hw_auto) (by hw_auto) (by hw_auto)
    have hchain : PrfH [land (shapeBin X 1) (argsIn q (nthc X (numeralM 2))), isTermCodeE1 q X,
        provFromCode (eqCodeFn ND (tcFn X))]
        (provFromCode (eqCodeFn (tcFn (nthc X (numeralM 2)))
        (nthcT ND (tcFn (numeralM 2))))) :=
      PrfH_eq_symm_code _ _ (substtc_inv_nthcT hNDinv (substtc_inv_tcFn (numeralM 2)))
        hfwd (by hw_auto) (by hw_auto)
    have hAD : PrfH [land (shapeBin X 1) (argsIn q (nthc X (numeralM 2))), isTermCodeE1 q X,
        provFromCode (eqCodeFn ND (tcFn X))]
        (provFromCode (argsInDotC (nthcT ND (tcFn (numeralM 2))) (tcFn q))) :=
      PrfH_argsInDotC_transport q _ _ hchain hA0
        (prf_liftc_tcFn (nthc X (numeralM 2)))
        (prf_eq_trans (prf_liftc_nthcT zero ND (tcFn (numeralM 2)))
          (prf_congr_nthcT hNDlift (prf_liftc_tcFn (numeralM 2))))
    exact PrfH_orR_code _ _ (PrfH_and_intro_code _ _ hshD hAD)


/-- ⭐⭐ **`hbody`, LA NOVENA OBLIGACIÓN.** De `wfAll1 q` y la cota sale el cuerpo dotado con el
    hueco relleno. Junta todo: instancia el `∀` objeto, saca la ecuación del nodo de
    `pcc_eval_nthc`, aplica el recorrido en forma de códigos y transporta con la keystone. -/
theorem hbody_wfAll1 : ∀ q i : Term, Prf (wfAll1 q ⇒ (lt i (lenc q) ⇒
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

theorem pcc_wfAll1_tracked (w : Term) : Prf (wfAll1 w ⇒ provFromCode (wfAll1Dot w)) :=
  pcc_wfAll1_tracked_of_hbody hbody_wfAll1 w

theorem DEUDA_wfAll1_tracked_proved : DEUDA_wfAll1_tracked wfAll1Dot :=
  DEUDA_wfAll1_of_hbody hbody_wfAll1

/-- ⭐⭐⭐ **EL REFLECTOR DE `isTC1`, SIN HIPÓTESIS**: `isTC1 w c ⇒ Prov(⌜isTC1 ẇ ċ⌝)`, con
    **`w` y `c` abstractos**. Es la mitad `wfAll1` de `DEUDA_hGuardT`, cerrada. -/
theorem pcc_isTC1_tracked (w c : Term) :
    Prf (isTC1 w c ⇒ provFromCode (andc (wfAll1Dot w) (inFormCodeFn (tcFn c) (tcFn w)))) :=
  pcc_isTC1_tracked_of DEUDA_wfAll1_tracked_proved w c

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
  wfAll1Args prf_liftc_wfAll1Args prf_substtc_liftc_wfAll1Args_gen
  prf_substtc_liftc_wfAll1Args
  wfAll1PsiAt wfAll1Psi wfAll1Dot
  hCl_wfAll1 hCs_wfAll1 hbl_lenc hbs_lenc hPl_wfAll1Psi hPs_wfAll1Psi
  prf_substtc_node0 prf_substtc_args1 prf_substfc_wfAll1Psi hPsiId_wfAll1Psi hwPsi_wfAll1Psi
  pcc_wfAll1_tracked_of_hbody DEUDA_wfAll1_of_hbody pcc_isTC1_tracked_of_hbody
  argsInPsi argsInPair liftF_argsInPair substF_argsInPair
  liftT_argsInBnd substT_argsInBnd liftT_argsInPsi substT_argsInPsi
  prf_substfc_argsInPsi prf_argsInPsi_id prf_argsIn_body
  pcc_argsIn_pair_tracked pcc_argsIn_tracked
)

#print axioms ROBINSON_PlusPlus.Meta.HasWitTrackedPrf.pcc_isTC1_tracked_of
#print axioms ROBINSON_PlusPlus.Meta.HasWitTrackedPrf.pcc_argsIn_pair_tracked
#print axioms ROBINSON_PlusPlus.Meta.HasWitTrackedPrf.pcc_isTermCodeE1_tracked
