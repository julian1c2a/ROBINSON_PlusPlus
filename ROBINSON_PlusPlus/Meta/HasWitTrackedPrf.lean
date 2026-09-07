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
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs

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

/-- ⭐ **LA CONMUTACIÓN, HECHA.** Bajar el `substfc` por dentro del binder ya no está
    bloqueado: el `substtc` de nivel 1 sobre el `Z` lifteado devuelve el `Z` con el hueco
    relleno, que es exactamente lo que pide `hbody`. -/
theorem prf_substtc_liftc_wfAll1Args (w s : Term) :
    Prf (substtc (succ zero) (liftc zero (tcFn s)) (liftc zero (wfAll1Args w))
      =eq nthcT (nthcT (tcFn w) (tcFn s)) (tcFn (numeralM 2))) := by
  refine prf_eq_trans (prf_congr_substtc3 (prf_liftc_wfAll1Args w)) ?_
  refine prf_eq_trans (prf_substtc_nthcT (succ zero) _ _ _) ?_
  refine prf_congr_nthcT ?_ (prf_substtc_tcFn_at 1 _ (numeralM 2))
  refine prf_eq_trans (prf_substtc_nthcT (succ zero) _ _ _) ?_
  refine prf_congr_nthcT (prf_substtc_tcFn_at 1 _ w) ?_
  exact prf_eq_trans
    (prf_mp (prf_substtc_var_eq (succ zero) (liftc zero (tcFn s)) (succ (numeral 0)))
      (prf_refl _))
    (prf_liftc_tcFn s)

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
  wfAll1Args prf_liftc_wfAll1Args prf_substtc_liftc_wfAll1Args
  argsInPsi argsInPair liftF_argsInPair substF_argsInPair
  liftT_argsInBnd substT_argsInBnd liftT_argsInPsi substT_argsInPsi
  prf_substfc_argsInPsi prf_argsInPsi_id prf_argsIn_body
  pcc_argsIn_pair_tracked pcc_argsIn_tracked
)

#print axioms ROBINSON_PlusPlus.Meta.HasWitTrackedPrf.pcc_isTC1_tracked_of
#print axioms ROBINSON_PlusPlus.Meta.HasWitTrackedPrf.pcc_argsIn_pair_tracked
#print axioms ROBINSON_PlusPlus.Meta.HasWitTrackedPrf.pcc_isTermCodeE1_tracked
