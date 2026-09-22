/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.VerifierSound
import ROBINSON_PlusPlus.Meta.D3BodyPrf
import ROBINSON_PlusPlus.Meta.LineWFCases
import ROBINSON_PlusPlus.Meta.AxiomListCode
import ROBINSON_PlusPlus.Meta.Sigma1CorePrf
import ROBINSON_PlusPlus.Meta.CodeWitnessPrf
import ROBINSON_PlusPlus.Meta.ChainDecode
import ROBINSON_PlusPlus.Full.Lists

/-!
# MÓDULOS C/D de `NegVerifier` — **`DEUDA_inNeg` SALDADA**, y el puente de `DEUDA_chainNeg`

`Meta/VerifierSound.lean` dejó `NegVerifier` reducido a **dos** obligaciones enunciadas. Aquí se
**paga una** y se construye el **núcleo reutilizable** de la otra.

## §1 · El PUENTE: de una línea refutada a la cadena refutada

    derives_chainOk_neg_of_line (l k x) (hk : l[k]? = some x)
      (hne : axioms ⊢ ¬ lineWF x) : axioms ⊢ ¬ chainOk nil ⟦l⟧

Es la mitad **reutilizable** de `DEUDA_chainNeg`, y sale de piezas que ya estaban:
`prf_lineWF_of_chainOk` (la que D3 usó en su mitad (a)), `prf_nthc_objList`, `prf_lenc_objList` y
`gnum_lt`. ⇒ **`DEUDA_chainNeg` queda reducida a**: *«el decodificador META rechaza ⟹ hay una línea
cuyo `lineWF` la teoría refuta»*.

## §2 · Las CABEZAS de una cadena aceptada SON los códigos de sus conclusiones

    decode_heads (l acc rs L) : decodeChainAux acc ⟦l⟧ = some rs → checkAux rs acc = some L →
      ∃ fs, L = acc ++ fs ∧ Prf (⟦l.map carc⟧ ≐ listFormCodeM fs)

🔑 **La pieza que lo hace posible es `decodeForm_inj`** —el decodificador es una **sección**—:
si `decodeLine` acepta, la cabeza del término **era** `formCodeM f`. Se extrae en dos lemas
(`decodeLine_stepConcl`, `decodeLine_carc`) y la inducción sobre la cadena hace el resto.

## §3 · 🏁 `DEUDA_inNeg`, SALDADA

    deuda_inNeg : DEUDA_inNeg

La cadena entera: `runFn nil ⟦l⟧ ≐ ⟦l.map carc⟧` (`prf_runFn_objList` + `prf_concat_nil_eq`)
`≐ listFormCodeM fs` (§2), y ahí manda **`prf_not_In_listFormCodeM`**, que ya existía y cuyo
docstring decía exactamente *«la refutación que necesita `NegVerifier`»*.

⚠️ **Nada de esto usa el ancla de codificación**: el footprint **de `deuda_inNeg`** no cita
`AnclaEq` ni `ax_axiomsCodeT_eq`.
⛔ **ÁMBITO, añadido el 2026‑09‑21 (M‑13)**: la frase de arriba valía — y sigue valiendo — para
`deuda_inNeg`, pero estaba escrita **sin etiqueta de ámbito** en la cabecera del **MÓDULO**. El
cierre de (d) (§2ter) **sí** entra por `axiomsCodeT`, así que su footprint cita
`ax_axiomsCodeT_eq`, y sin la etiqueta esta frase se habría vuelto falsa **sola**.
🔑 *Una cifra sin ámbito se lee como global, y caduca en cuanto el módulo crece.*

## ⬜ Lo que queda de `DEUDA_chainNeg`, medido

Con `StdChain` estrechada ([ADR‑022](../../DECISIONS.md)) toda línea es `⟨⌜f⌝, k̄, args⟩` con args
`formCode`/`termCode`, así que **las causas de rechazo del decodificador son cinco, y se pueden
enumerar**:

| # | por qué rechaza | ¿hay maquinaria? |
|---|---|---|
| (a) | **tag fuera de rango** (`k ≥ 21`) | 🔶 `prf_tagDisj_absurd` acota el tag por 20 |
| (b) | **aridad equivocada** | 🏁 **CERRADA 2026‑09‑21**, `derives_lineWF_neg_of_arity` + los **21** `prf_lenc_*` |
| (c) | **la conclusión no casa** (`stepConcl ≠ f`) | 🏁 **CERRADA 2026‑09‑22**, `derives_lineWF_neg_of_concl` + los **19** `tc_*` |
| (d) | **`thy` con `f ∉ axioms`** | 🏁 **CERRADA 2026‑09‑21**, `derives_lineWF_neg_thy_of_decode` — la ✅ anterior era **falsa** (ver 3 abajo) |
| (e) | **`mp`/`gen` sin premisas en el acumulador** | 🏁 **CERRADA 2026‑09‑22** (§2quater + §2quinquies): el genérico `derives_chainOk_neg_of_prem_code` y las **tres** instancias |
| (f) | **tipo de ARGUMENTO** — la **SEXTA**, que esta enumeración no tenía | 🏁 **refutadores CERRADOS 2026‑09‑22** (`Meta/CodeDistinct.lean` + §1quinquies); ⬜ queda el análisis de `StdArgs` por tag, que es **reparto**, no cierre |

⛔⛔ **RECTIFICADO el 2026-09-21, y las dos afirmaciones de arriba eran FALSAS** (panel
adversarial, ADR-075):

1. ⛔ **«Las causas son CINCO» — son SEIS.** Falta el **desajuste de TIPO** de argumento (no de
   aridad): `decodeTerm` y `decodeForm` tienen rangos de tag **disjuntos**
   (`Meta/CodeDecode.lean:80,115`) y `StdArgs` (`Meta/OmegaReflect.lean:148`) sólo exige que cada
   argumento sea `formCode _` **o** `termCode _`, **sin decir cuál**. ⭐ Pero no es un muro: los
   tags 9/10 llevan las guardas `hasWitF`/`hasWit` **dentro** desde ADR-020, y
   `crit_isTC1_junk_refuted_open` (`Meta/CodeWitnessPrf.lean:1168`) las refuta.
   🔑 *Un `lineWF` más fuerte es más fácil de refutar* — ya estaba escrito en
   `Meta/LineWFCases.lean:99`.
2. ⛔⛔ **«(a)–(d) componen con §1 y cierran» — FALSO.** El puente de §1 exige una `k` y una `x`
   **concretas**, y **no existe** ningún lema que vaya de `decodeChainAux … = none` a esa `k`
   (`grep` de `firstBad|badIdx|failIdx|takeWhile|List.take` en todo RPP: **vacío**). Ese
   **front-end** les falta a **las SEIS** causas, no sólo a (e).
   🔑 *Una afirmación de estado que viaja a una cabecera sin que nadie la compile.*
   🏁 **CERRADO el 2026‑09‑21** (ADR‑078), y las dos piezas son **net‑0 puras**: el front‑end
   es `decodeChainAux_none_first` (§2bis) y el despachador entero es `dispatcher` (§4).
   ⭐ Y el **riesgo declarado de la vía también se cayó**: el aviso de `whnf` de `Meta/ChainDecode.lean:44`
   describe un `match` sobre `Term` que **`peelArgs` ya había abandonado**; el split de 21 tags
   sobre `Nat` cuesta **4,5 s** (`sondeos/DespachadorCoste.lean`).
3. ⛔⛔ **La ✅ de (d) era FALSA — y sobre una instancia ALCANZABLE** (ADR‑076). El lema que
   citaba, `derives_lineWF_neg_thy_of_not_prf`, pide **`¬ Prf φ`**, y el decodificador sólo
   entrega **`φ ∉ axioms`**: `decodeRuleTag acc f 15 args` **es** `(findIdx f axioms).map
   Rule.thy` (`Meta/ChainDecode.lean:164`). `prf_ax : f ∈ axioms → Prf f` va en **un solo
   sentido**, y como `axioms` son **141** fórmulas mientras `Prf` es infinito, **existen `f` con
   `Prf f` y `f ∉ axioms`** — sobre ésas el lema no se podía aplicar. ⭐ El arreglo no fue
   clonar: `neg_In_axiomsCodeT` se **generalizó en su sitio** (su primer paso era justo el que
   sobraba) y el antiguo quedó de corolario, lo mismo en `LineWFCases`.
   🔑 *Una ✅ que nombra un lema no dice que ese lema ACEPTE la hipótesis que le va a llegar.*

⭐ Y (e) **no** es «la única sin maquinaria»: su estructura son **dos lemas** (§1bis, aterrizados),
y su cadena está **escrita en positivo** en `Meta/Representability2Prf.lean:307-337` — *el sujeto
cambia, la prueba no*. Lo que de verdad queda es el **front-end** y el **cambio de cota**
`boundedCarcLt y ⟦l⟧ k̄ → boundedCarcIn y ⟦l.take k⟧`, cuyos dos sentidos hacia `In` ya existen
(`Meta/RunFnBoundedPrf.lean:225` y `:246`).
-/

open FOL
open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.CodeArith
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf
open ROBINSON_PlusPlus.Meta.CheckArith
open ROBINSON_PlusPlus.Meta.D3BodyPrf
-- (§1bis, el puente del caso (e)) la capa acotada y la deduccion
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ChainOkBoundedPrf
open ROBINSON_PlusPlus.Meta.ChainPrf
-- (§1ter, los cierres de (a) y (b)) todos alcanzables por transitividad
open ROBINSON_PlusPlus.Meta.OmegaReflect
open ROBINSON_PlusPlus.Meta.SubstTreeReflect
open ROBINSON_PlusPlus.Meta.LineWFAssemblePrf
open ROBINSON_PlusPlus.Meta.NumListPrf
open ROBINSON_PlusPlus.Meta.PremsOfTagPrf
open ROBINSON_PlusPlus.Meta.LineWFCases
open ROBINSON_PlusPlus.Meta.VerifierSound
open ROBINSON_PlusPlus.Meta.CodeDecode
open ROBINSON_PlusPlus.Meta.ChainDecode
open ROBINSON_PlusPlus.Meta.HilbertSeq
open ROBINSON_PlusPlus.Meta.Sigma1CorePrf
open ROBINSON_PlusPlus.Meta.AxiomListCode

namespace ROBINSON_PlusPlus.Meta.ChainNegPrf

/-! ## §0 · Los dos Leibniz a nivel `⊢` que hacen falta (molde de `Full.eq_subst_in`) -/

theorem derives_lt_congr_right {Γ : List Formula} {a t₁ t₂ : Term}
    (h : Γ ⊢ (t₁ =eq t₂)) (hp : Γ ⊢ lt a t₁) : Γ ⊢ lt a t₂ := by
  let f : Formula := lt (liftTerm 0 a) (.var 0)
  have hS : ∀ s : Term, substFormula 0 s f = lt a s := by
    intro s
    simp only [f, substFormula, lt, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ Derives.subst Γ t₁ t₂ f h ((hS t₁) ▸ hp)

theorem derives_lineWF_congr {Γ : List Formula} {t₁ t₂ : Term}
    (h : Γ ⊢ (t₁ =eq t₂)) (hp : Γ ⊢ lineWF t₁) : Γ ⊢ lineWF t₂ := by
  let f : Formula := lineWF (.var 0)
  have hS : ∀ s : Term, substFormula 0 s f = lineWF s := by
    intro s
    simp only [f, substFormula, lineWF, substTerm, substTerms, if_true]
  exact (hS t₂) ▸ Derives.subst Γ t₁ t₂ f h ((hS t₁) ▸ hp)

/-! ## §1 · EL PUENTE: de una línea refutada a la cadena refutada -/

theorem derives_chainOk_neg_of_line (l : List Term) (k : Nat) (x : Term)
    (hk : l[k]? = some x) (hne : axioms ⊢ neg (lineWF x)) :
    axioms ⊢ neg (chainOk nil (objList l)) := by
  refine FOL.MetaRules.raa (fun hch => ?_)
  -- (1) la cota: k < longitud
  have hklt : k < l.length := by
    rcases List.getElem?_eq_some_iff.mp hk with ⟨hb, _⟩
    exact hb
  have hlt0 : axioms ⊢ lt (numeralM k) (numeralM l.length) := by
    have := gnum_lt (a := k) (b := l.length) hklt
    simpa only [numeralM_eq] using this
  -- (2) transportar la cota a `lenc ⟦l⟧`
  have hlen : axioms ⊢ (lenc (objList l) =eq numeralM l.length) :=
    prf_to_derives (SinWTs.prf_lenc_objList l)
  have hlt : axioms ⊢ lt (numeralM k) (lenc (objList l)) :=
    derives_lt_congr_right (FOL.derive_eq_symm hlen) hlt0
  -- (3) chainOk ⇒ lineWF (nthc ⟦l⟧ k̄)
  have hwf : axioms ⊢ lineWF (nthc (objList l) (numeralM k)) :=
    FOL.MetaRules.mp
      (FOL.MetaRules.mp (prf_to_derives (prf_lineWF_of_chainOk (objList l) (numeralM k))) hch)
      hlt
  -- (4) `nthc ⟦l⟧ k̄ = x` ⇒ lineWF x
  have hnth : axioms ⊢ (nthc (objList l) (numeralM k) =eq x) :=
    prf_to_derives (SinWTs.prf_nthc_objList l k x hk)
  have hwfx : axioms ⊢ lineWF x := derives_lineWF_congr hnth hwf
  exact FOL.MetaRules.mp hne hwfx


/-! ## §1bis · EL PUENTE DEL CASO (e) — por la OTRA mitad de la línea

⭐⭐ **`lineOkB` es un `land` de DOS conjuntos**, y §1 sólo ataca el primero:

    lineOkB c p i := land (lineWF (nthc p i)) (boundedPremsIn c p i (premsOf (nthc p i)))

`prf_lineWF_of_chainOk` (`Meta/D3BodyPrf.lean:78`) deriva `lineOkB nil q i` entero y termina en
`PrfH_and_elim_left`. ⇒ **el caso (e) es la MISMA derivación con `and_elim_right`**, y su puente
es el gemelo literal de `derives_chainOk_neg_of_line`.

🔑 *Y el docstring de `prf_lineWF_of_chainOk` ya lo decía —«lo consumen **las dos** mitades de
`hbody`»—: la maquinaria que la cabecera daba por inexistente estaba a una palabra.* Van **siete**
de «antes de construir, buscar».

⭐ **Por qué por la forma Δ₀ y no por `allIn`.** La otra descomposición (`lineOk c line :=
lineWF line ∧ allIn c (premsOf line)`, `Minimal/Axioms.lean:803`) obliga a pelar
`prf_chainOk_cons` **`k` veces** — y `k` es **simbólica**, así que eso no es pelar: es una
inducción nueva, más una distributividad `⟦a++b⟧ ≐ concat ⟦a⟧ ⟦b⟧` que **no existe** en el árbol.
`chainOkB` es `∀ i < lenc p`, así que la línea `k` sale por **instanciación**.
🔑 *La forma Δ₀ se construyó para que el acumulador desapareciera; la negación de (e) es donde eso
paga.*

⬜ **Lo que estas dos piezas NO hacen**, y hay que decirlo: dan la ESTRUCTURA del caso (e), no su
alimentador. Falta producir la hipótesis `⊢ ¬ boundedPremsIn …` a partir del hecho decidible, y
eso pide (i) el **cambio de cota** `boundedCarcLt y ⟦l⟧ k̄ → boundedCarcIn y ⟦l.take k⟧` y (ii) un
**front-end** `decodeChainAux … = none → ∃ k` que **no existe y que necesitan las SEIS causas**,
no sólo (e). -/

/-- ⭐ **De la cadena sale la ACOTACIÓN DE PREMISAS de la línea `i`-ésima.**
Gemelo exacto de `prf_lineWF_of_chainOk` (`Meta/D3BodyPrf.lean:78`): misma derivación, y donde
aquélla toma `and_elim_left` ésta toma `and_elim_right`. -/
theorem prf_boundedPremsIn_of_chainOk (q i : Term) :
    Prf (chainOk nil q ⇒ (lt i (lenc q) ⇒
      boundedPremsIn nil q i (premsOf (nthc q i)))) := by
  refine prf_deduction (deduction_aux ?_ (lt i (lenc q)) [chainOk nil q] rfl)
  have hch : PrfH [lt i (lenc q), chainOk nil q] (chainOk nil q) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hlt : PrfH [lt i (lenc q), chainOk nil q] (lt i (lenc q)) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hB : PrfH [lt i (lenc q), chainOk nil q] (chainOkB nil q) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_and_elim_left (prf_chainOk_iff_chainOkB nil q)) _) hch
  have hB' : PrfH [lt i (lenc q), chainOk nil q]
      (Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (lenc q)))
        (lineOkB (liftTerm 0 nil) (liftTerm 0 q) (.var 0)))) := hB
  have hspec := PrfH_spec hB' i
  have heq : substFormula 0 i (Formula.impl (lt (.var 0) (liftTerm 0 (lenc q)))
      (lineOkB (liftTerm 0 nil) (liftTerm 0 q) (.var 0)))
      = Formula.impl (lt i (lenc q)) (lineOkB nil q i) := by
    simp only [substFormula, substFormula_lineOkB, lt, lenc, nil, zero, substTerm, substTerms,
      FOL.substTerm_liftTerm, if_true]
  rw [heq] at hspec
  exact PrfH_and_elim_right (PrfH.mp _ _ _ hspec hlt)

/-- ⭐⭐ **EL PUENTE DEL CASO (e)**: de «las premisas de la línea `k` no están acotadas» a
«la cadena se refuta». Gemelo exacto de `derives_chainOk_neg_of_line` (§1), y con el mismo
footprint. -/
theorem derives_chainOk_neg_of_prems (l : List Term) (k : Nat)
    (hk : k < l.length)
    (hne : axioms ⊢ neg (boundedPremsIn nil (objList l) (numeralM k)
              (premsOf (nthc (objList l) (numeralM k))))) :
    axioms ⊢ neg (chainOk nil (objList l)) := by
  refine FOL.MetaRules.raa (fun hch => ?_)
  have hlt0 : axioms ⊢ lt (numeralM k) (numeralM l.length) := by
    have := gnum_lt (a := k) (b := l.length) hk
    simpa only [numeralM_eq] using this
  have hlen : axioms ⊢ (lenc (objList l) =eq numeralM l.length) :=
    prf_to_derives (SinWTs.prf_lenc_objList l)
  have hlt : axioms ⊢ lt (numeralM k) (lenc (objList l)) :=
    derives_lt_congr_right (FOL.derive_eq_symm hlen) hlt0
  have hbp : axioms ⊢ boundedPremsIn nil (objList l) (numeralM k)
      (premsOf (nthc (objList l) (numeralM k))) :=
    FOL.MetaRules.mp
      (FOL.MetaRules.mp
        (prf_to_derives (prf_boundedPremsIn_of_chainOk (objList l) (numeralM k))) hch)
      hlt
  exact FOL.MetaRules.mp hne hbp


/-- ⭐⭐ **LA REFUTACIÓN DE LA COTA.** Si ninguna de las `k` primeras líneas concluye `y`,
la teoría **refuta** que alguna de ellas lo haga.

⭐ **Y esto disuelve el paso que yo mismo había planificado.** El plan decía: «cambiar la cota»
(`boundedCarcLt y ⟦l⟧ k̄ → boundedCarcIn y ⟦l.take k⟧`) para poder encadenar con los dos sentidos
`boundedCarcIn ⇔ In _ (runFn nil p)` (`Meta/RunFnBoundedPrf.lean:225`, `:246`) y rematar con
`prf_not_In_listFormCodeM`. **No hace falta nada de eso**: `prf_boundedCarcLt_zero` (la base) y
`prf_boundedCarcLt_cons_succ_iff` (el paso) ya estaban en `Meta/ChainOkBoundedPrf.lean:428` y
`:167`, y la refutación sale por **inducción directa** en veinte líneas — sin `l.take k`, sin
`boundedCarcIn` y sin el puente a `In`.

🔑 *Van OCHO de «antes de construir, buscar», y ésta disolvió un paso que había propuesto yo
mismo el día anterior.*

⚠️ La hipótesis `Nat.le k l.length` **no es decoración**: sin ella queda el caso `boundedCarcLt y
nil (σ j)`, que habría que refutar aparte. Y va como `Nat.le` explícito porque `≤` resuelve al
símbolo OBJETO `le` (trampa §de notación). -/
theorem derives_not_boundedCarcLt (y : Term) :
    ∀ (k : Nat) (l : List Term), Nat.le k l.length →
      (∀ j x, j < k → l[j]? = some x → axioms ⊢ neg (Formula.eq (carc x) y)) →
      axioms ⊢ neg (boundedCarcLt y (objList l) (numeralM k))
  | 0, l, _, _ => by
      exact prf_to_derives (prf_boundedCarcLt_zero y (objList l))
  | _ + 1, [], hk, _ => by
      exact absurd hk (by simp)
  | k + 1, a :: as, hk, h => by
      have hhead : axioms ⊢ neg (Formula.eq (carc a) y) :=
        h 0 a (Nat.succ_pos k) rfl
      have htail : axioms ⊢ neg (boundedCarcLt y (objList as) (numeralM k)) :=
        derives_not_boundedCarcLt y k as (Nat.le_of_succ_le_succ hk)
          (fun j x hj hx => h (j + 1) x (Nat.succ_lt_succ hj) hx)
      show axioms ⊢ neg (boundedCarcLt y (cons a (objList as)) (succ (numeralM k)))
      refine FOL.MetaRules.raa (fun hb => ?_)
      have hsplit : axioms ⊢
          lor (Formula.eq (carc a) y) (boundedCarcLt y (objList as) (numeralM k)) :=
        FOL.MetaRules.mp
          (prf_to_derives (prf_and_elim_left
            (prf_boundedCarcLt_cons_succ_iff y a (objList as) (numeralM k)))) hb
      exact FOL.MetaRules.or_elim hsplit
        (fun hl => FOL.MetaRules.mp hhead hl)
        (fun hr => FOL.MetaRules.mp htail hr)


/-! ## §1ter · LOS CIERRES DE (a) y (b)

⚠️ La cabecera de este módulo marcaba **(a)** y **(b)** con 🔶 «hay maquinaria». Medido: (a)
estaba **hecha** y (b) a dos envoltorios. Van **seis** estimaciones altas seguidas en esta vía.
🔑 *El proyecto tiene mucha más maquinaria construida de la que su propio índice refleja; lo que
falta no es capacidad, es el mapa.* -/

/-- ⭐ Un `StdArgs` **ES** un `objList`. Fontanería de forma, y la necesitan **las SEIS** causas:
sin ella no encaja la forma `cons concl (cons k̄ (objList args))` que piden los cierres con la
forma `cons ⌜f⌝ (cons k̄ as)` que da `StdLine`. -/
theorem stdArgs_objList : ∀ {as : Term}, StdArgs as → as = objList (peelArgs as)
  | _, StdArgs.nil => rfl
  | _, StdArgs.form _ h => by
      simp only [peelArgs_cons, objList]
      rw [← stdArgs_objList h]
  | _, StdArgs.term _ h => by
      simp only [peelArgs_cons, objList]
      rw [← stdArgs_objList h]

/-! ### ⭐⭐⭐ LA INVERSIÓN DE `StdArgs` — la pieza que comparten las 21 ramas del reparto

`StdArgs` (`Meta/OmegaReflect.lean:148`) vive sobre `Term`; el reparto (§4) trabaja sobre la
**lista pelada** `peelArgs as`. `stdArgs_objList` (arriba) da la ida a nivel de término; lo que
falta es el gemelo a nivel de **lista**, que es el que se puede **destruir por casos**.

⭐⭐ **Y no es fontanería: es lo que convierte `decodeRuleTag … = none` en la tabla de causas.**
Con la aridad correcta y los tipos correctos, `decodeRuleTag` **decodifica** (abajo,
`decodeRuleTag_p1_some`). Ergo, para un tag estructural, `= none` **implica** aridad equivocada
(b) **o** tipo equivocado (f), y no hay tercera opción. La dicotomía de abajo es esa implicación,
y es la **plantilla de las diecinueve ramas**.

🔑 *Un inductivo sobre `Term` se invierte mal; el mismo inductivo sobre `List Term` se destruye
con `cases`. La inversión no es un lema, es un cambio de soporte.* -/

/-- Versión a nivel de **LISTA** de `StdArgs`. -/
inductive StdArgList : List Term → Prop
  | nil : StdArgList []
  | form (A : Formula) {l : List Term} : StdArgList l → StdArgList (formCode A :: l)
  | term (u : Term) {l : List Term} : StdArgList l → StdArgList (termCode u :: l)

theorem peelArgs_objList : ∀ l : List Term, peelArgs (objList l) = l
  | [] => rfl
  | a :: l => by
      show peelArgs (cons a (objList l)) = a :: l
      rw [peelArgs_cons, peelArgs_objList l]

/-- ⭐⭐ **LA INVERSIÓN**: los argumentos pelados de una lista estándar forman una lista estándar
de argumentos. -/
theorem stdArgs_peel : ∀ {as : Term}, StdArgs as → StdArgList (peelArgs as)
  | _, StdArgs.nil => by rw [peelArgs_nil]; exact StdArgList.nil
  | _, StdArgs.form A h => by rw [peelArgs_cons]; exact StdArgList.form A (stdArgs_peel h)
  | _, StdArgs.term u h => by rw [peelArgs_cons]; exact StdArgList.term u (stdArgs_peel h)

/-- Y la vuelta, que es la que reconstruye el término que piden los cierres. -/
theorem stdArgList_objList : ∀ {l : List Term}, StdArgList l → StdArgs (objList l)
  | _, StdArgList.nil => StdArgs.nil
  | _, StdArgList.form A h => StdArgs.form A (stdArgList_objList h)
  | _, StdArgList.term u h => StdArgs.term u (stdArgList_objList h)

/-- ⭐ **El destructor de UN paso**: la cabeza es código de fórmula o de término, y la cola sigue
siendo estándar. Iterándolo se llega a cualquier aridad, sin un lema por aridad. -/
theorem stdArgList_cons {a : Term} {l : List Term} (h : StdArgList (a :: l)) :
    And (Or (∃ A, a = formCode A) (∃ u, a = termCode u)) (StdArgList l) := by
  cases h with
  | form A h' => exact ⟨Or.inl ⟨A, rfl⟩, h'⟩
  | term u h' => exact ⟨Or.inr ⟨u, rfl⟩, h'⟩

/-- Con aridad y tipos correctos, el tag 0 **decodifica**. -/
theorem decodeRuleTag_p1_some (acc : List Formula) (f A B : Formula) :
    decodeRuleTag acc f 0 [formCode A, formCode B] = some (Rule.p1 A B) := by
  simp [decodeRuleTag, decodeForm_formCode]

/-- Ídem con un argumento de **término**: el tag 9. -/
theorem decodeRuleTag_q1_some (acc : List Formula) (f A : Formula) (t : Term) :
    decodeRuleTag acc f 9 [formCode A, termCode t] = some (Rule.q1 A t) := by
  simp [decodeRuleTag, decodeForm_formCode, decodeTerm_termCode]

/-- ⭐⭐⭐ **LA DICOTOMÍA, plantilla de las diecinueve ramas**: para un tag estructural,
`decodeRuleTag … = none` sobre argumentos estándar significa **aridad equivocada** (causa (b))
**o** **tipo equivocado** (causa (f)). No hay tercera opción, y por eso el reparto no tiene que
razonar: sólo destruir.

⚠️ El caso `[_]` va con `simp` y no con `decide`: con una variable libre dentro, `decide` se
niega («Expected type must not contain free variables») aunque la longitud sea computable. -/
theorem tag0_none_dichotomy {acc : List Formula} {f : Formula} {args : List Term}
    (hs : StdArgList args) (h : decodeRuleTag acc f 0 args = none) :
    Or (args.length ≠ 2)
       (∃ a b, And (args = [a, b])
         (Or (∃ u, a = termCode u) (∃ u, b = termCode u))) := by
  match args, hs with
  | [], _ => exact Or.inl (by decide)
  | [_], _ => exact Or.inl (by simp)
  | [a, b], hs =>
      obtain ⟨ha, hs'⟩ := stdArgList_cons hs
      obtain ⟨hb, _⟩ := stdArgList_cons hs'
      rcases ha with ⟨A, rfl⟩ | ⟨u, rfl⟩
      · rcases hb with ⟨B, rfl⟩ | ⟨u, rfl⟩
        · rw [decodeRuleTag_p1_some acc f A B] at h; exact absurd h (by simp)
        · exact Or.inr ⟨_, _, rfl, Or.inr ⟨u, rfl⟩⟩
      · exact Or.inr ⟨_, _, rfl, Or.inl ⟨u, rfl⟩⟩
  | _ :: _ :: _ :: _, _ => exact Or.inl (by simp)

/-- El tag de una línea CONCRETA se computa: `lineTag ⟨c, k̄, as⟩ = k̄`. -/
theorem prf_lineTag_cons (concl as : Term) (k : Nat) :
    Prf (Formula.eq (lineTag (cons concl (cons (numeralM k) as))) (numeralM k)) := by
  show Prf (Formula.eq (nthc (cons concl (cons (numeralM k) as)) (succ zero)) (numeralM k))
  exact prf_eq_trans (prf_nthc_succ concl (cons (numeralM k) as) zero)
    (prf_nthc_zero (numeralM k) as)

/-- ⭐⭐ **EL CIERRE DE (a)**: con el tag fuera de rango, la teoría refuta `lineWF`.

⭐ `pcc_tag_vacuous` (`Meta/SubstTreeReflect.lean:1147`) **ya ERA el cierre**, no una acotación:
da `Prf (lineWF t ⇒ ((lineTag t ≐ k̄) ⇒ C))` con `C` **arbitraria** y sin `[AnclaEq]`. Como
`neg φ = Formula.impl φ Formula.bottom` **por definición**, tomar `C := ⊥` no cuesta ni una línea
de conversión. `concl` y `as` quedan **arbitrarios**. -/
theorem derives_lineWF_neg_of_tag_big (concl as : Term) {k : Nat} (hk : 20 < k) :
    axioms ⊢ neg (lineWF (cons concl (cons (numeralM k) as))) :=
  prf_to_derives
    (prf_mp (prf_swap_imp (pcc_tag_vacuous _ Formula.bottom hk))
            (prf_lineTag_cons concl as k))

/-- Desigualdad de numerales a nivel `⊢`. -/
theorem derives_numeralM_ne {m n : Nat} (h : m ≠ n) :
    axioms ⊢ neg (Formula.eq (numeralM m) (numeralM n)) := by
  have hx := gnum_ne h
  simpa only [numeralM_eq] using hx

/-- ⭐⭐ **EL MOTOR DE (b)**: si `lineWF` obliga a una longitud `n` y la línea mide `m ≠ n`, la
teoría refuta `lineWF`. Vale igual para los veinte tags y para `mp`.
⚠️ Arrastra `ex_elim` además de `raa`/`imp_intro`, por `gnum_ne`. -/
theorem derives_lineWF_neg_of_lenc_imp {x : Term} {n m : Nat}
    (himp : Prf (lineWF x ⇒ (Formula.eq (lenc x) (numeralM n))))
    (hlen : Prf (Formula.eq (lenc x) (numeralM m))) (hnm : m ≠ n) :
    axioms ⊢ neg (lineWF x) := by
  refine FOL.MetaRules.raa (fun hw => ?_)
  have h1 : axioms ⊢ (Formula.eq (lenc x) (numeralM n)) :=
    FOL.MetaRules.mp (prf_to_derives himp) hw
  have h2 : axioms ⊢ (Formula.eq (lenc x) (numeralM m)) := prf_to_derives hlen
  have h3 : axioms ⊢ (Formula.eq (numeralM m) (numeralM n)) :=
    FOL.derive_eq_trans (FOL.derive_eq_symm h2) h1
  exact FOL.MetaRules.mp (derives_numeralM_ne hnm) h3

/-- Envoltorio de longitud para los **veinte** tags con condición estructural.
⭐ Gemelo de `prf_premsOf_tag_and` (`Meta/PremsOfTagPrf.lean:144`): el mapa del panel declaraba
esta familia «LA pieza cara, no existe nada parecido» (85‑125 l.); **`prf_lenc_of_tag` ya estaba
escrito** (`:66`) y esto son cuatro líneas. -/
theorem prf_lenc_tag_and {k m : Nat} {C : Formula} (t : Term)
    (hax : Prf (Formula.forall (Formula.impl (tagF k)
      (lwfVar ⇔ Formula.and (lencF (m + 2)) C)))) :
    Prf (lineWF t ⇒ ((Formula.eq (nthc t (succ zero)) (numeralM k)) ⇒
      (Formula.eq (lenc t) (numeralM (m + 2))))) :=
  prf_lenc_of_tag t hax
    (by
      have hsub : substFormula 0 t (Formula.and (lencF (m + 2)) C)
          = Formula.and (Formula.eq (lenc t) (numeralM (m + 2))) (substFormula 0 t C) := by
        simp only [substFormula, substFormula_lencF]
      rw [hsub]
      exact prf_deduction (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c2 _ _)) (prfH_hyp_self _)))

/-- Envoltorio de longitud para `mp` (16), el **único** sin condición estructural. -/
theorem prf_lenc_tag_plain {k m : Nat} (t : Term)
    (hax : Prf (Formula.forall (Formula.impl (tagF k) (lwfVar ⇔ lencF (m + 2))))) :
    Prf (lineWF t ⇒ ((Formula.eq (nthc t (succ zero)) (numeralM k)) ⇒
      (Formula.eq (lenc t) (numeralM (m + 2))))) :=
  prf_lenc_of_tag t hax
    (by rw [substFormula_lencF]; exact prf_deduction (prfH_hyp_self _))

/-- Tag 0 (`p1`), aridad 2 ⇒ `lenc = 4`. **El molde de los veinte**: una línea por rama. -/
theorem prf_lenc_p1 (t : Term) :
    Prf (lineWF t ⇒ ((Formula.eq (nthc t (succ zero)) (numeralM 0)) ⇒
      (Formula.eq (lenc t) (numeralM 4)))) :=
  prf_lenc_tag_and (k := 0) (m := 2) t
    (prf_ax (show ax_lineWF_p1 ∈ axioms by simp [axioms]))

/-- Tag 16 (`mp`), **el molde del envoltorio `plain`**. -/
theorem prf_lenc_mp (t : Term) :
    Prf (lineWF t ⇒ ((Formula.eq (nthc t (succ zero)) (numeralM 16)) ⇒
      (Formula.eq (lenc t) (numeralM 3)))) :=
  prf_lenc_tag_plain (k := 16) (m := 1) t
    (prf_ax (show ax_lineWF_mp ∈ axioms by simp [axioms]))


/-! ### Las diecinueve ramas restantes de (b)

⚠️ **Estas diecinueve estuvieron cotizadas como «19 líneas, ESTIMADO» durante tres mensajes.**
Ahora están medidas: los diecinueve `prf_ax` salen con el envoltorio `_and`, ninguno necesita el
`plain`, y el fichero entero elabora en **4,7 s**. La tabla de aridades se sacó del propio
`Minimal/Axioms.lean` con un `awk`, no de memoria — el único sitio donde podía haber un error era
la pareja (tag, lenc) de cada esquema, y ésa la dice el axioma.
🔑 *Una tanda mecánica se ESCRIBE, no se cotiza: cotizarla cuesta más que hacerla.* -/

/-- Tag 1 (`p2`) ⇒ `lenc = 5`. -/
theorem prf_lenc_p2 (t : Term) :
    Prf (lineWF t ⇒ ((Formula.eq (nthc t (succ zero)) (numeralM 1)) ⇒
      (Formula.eq (lenc t) (numeralM 5)))) :=
  prf_lenc_tag_and (k := 1) (m := 3) t
    (prf_ax (show ax_lineWF_p2 ∈ axioms by simp [axioms]))

/-- Tag 2 (`c1`) ⇒ `lenc = 4`. -/
theorem prf_lenc_c1 (t : Term) :
    Prf (lineWF t ⇒ ((Formula.eq (nthc t (succ zero)) (numeralM 2)) ⇒
      (Formula.eq (lenc t) (numeralM 4)))) :=
  prf_lenc_tag_and (k := 2) (m := 2) t
    (prf_ax (show ax_lineWF_c1 ∈ axioms by simp [axioms]))

/-- Tag 3 (`c2`) ⇒ `lenc = 4`. -/
theorem prf_lenc_c2 (t : Term) :
    Prf (lineWF t ⇒ ((Formula.eq (nthc t (succ zero)) (numeralM 3)) ⇒
      (Formula.eq (lenc t) (numeralM 4)))) :=
  prf_lenc_tag_and (k := 3) (m := 2) t
    (prf_ax (show ax_lineWF_c2 ∈ axioms by simp [axioms]))

/-- Tag 4 (`c3`) ⇒ `lenc = 4`. -/
theorem prf_lenc_c3 (t : Term) :
    Prf (lineWF t ⇒ ((Formula.eq (nthc t (succ zero)) (numeralM 4)) ⇒
      (Formula.eq (lenc t) (numeralM 4)))) :=
  prf_lenc_tag_and (k := 4) (m := 2) t
    (prf_ax (show ax_lineWF_c3 ∈ axioms by simp [axioms]))

/-- Tag 5 (`j1`) ⇒ `lenc = 4`. -/
theorem prf_lenc_j1 (t : Term) :
    Prf (lineWF t ⇒ ((Formula.eq (nthc t (succ zero)) (numeralM 5)) ⇒
      (Formula.eq (lenc t) (numeralM 4)))) :=
  prf_lenc_tag_and (k := 5) (m := 2) t
    (prf_ax (show ax_lineWF_j1 ∈ axioms by simp [axioms]))

/-- Tag 6 (`j2`) ⇒ `lenc = 4`. -/
theorem prf_lenc_j2 (t : Term) :
    Prf (lineWF t ⇒ ((Formula.eq (nthc t (succ zero)) (numeralM 6)) ⇒
      (Formula.eq (lenc t) (numeralM 4)))) :=
  prf_lenc_tag_and (k := 6) (m := 2) t
    (prf_ax (show ax_lineWF_j2 ∈ axioms by simp [axioms]))

/-- Tag 7 (`j3`) ⇒ `lenc = 5`. -/
theorem prf_lenc_j3 (t : Term) :
    Prf (lineWF t ⇒ ((Formula.eq (nthc t (succ zero)) (numeralM 7)) ⇒
      (Formula.eq (lenc t) (numeralM 5)))) :=
  prf_lenc_tag_and (k := 7) (m := 3) t
    (prf_ax (show ax_lineWF_j3 ∈ axioms by simp [axioms]))

/-- Tag 8 (`efq`) ⇒ `lenc = 3`. -/
theorem prf_lenc_efq (t : Term) :
    Prf (lineWF t ⇒ ((Formula.eq (nthc t (succ zero)) (numeralM 8)) ⇒
      (Formula.eq (lenc t) (numeralM 3)))) :=
  prf_lenc_tag_and (k := 8) (m := 1) t
    (prf_ax (show ax_lineWF_efq ∈ axioms by simp [axioms]))

/-- Tag 9 (`q1`) ⇒ `lenc = 4`. -/
theorem prf_lenc_q1 (t : Term) :
    Prf (lineWF t ⇒ ((Formula.eq (nthc t (succ zero)) (numeralM 9)) ⇒
      (Formula.eq (lenc t) (numeralM 4)))) :=
  prf_lenc_tag_and (k := 9) (m := 2) t
    (prf_ax (show ax_lineWF_q1 ∈ axioms by simp [axioms]))

/-- Tag 10 (`q2`) ⇒ `lenc = 4`. -/
theorem prf_lenc_q2 (t : Term) :
    Prf (lineWF t ⇒ ((Formula.eq (nthc t (succ zero)) (numeralM 10)) ⇒
      (Formula.eq (lenc t) (numeralM 4)))) :=
  prf_lenc_tag_and (k := 10) (m := 2) t
    (prf_ax (show ax_lineWF_q2 ∈ axioms by simp [axioms]))

/-- Tag 11 (`q3`) ⇒ `lenc = 4`. -/
theorem prf_lenc_q3 (t : Term) :
    Prf (lineWF t ⇒ ((Formula.eq (nthc t (succ zero)) (numeralM 11)) ⇒
      (Formula.eq (lenc t) (numeralM 4)))) :=
  prf_lenc_tag_and (k := 11) (m := 2) t
    (prf_ax (show ax_lineWF_q3 ∈ axioms by simp [axioms]))

/-- Tag 12 (`eqrefl`) ⇒ `lenc = 3`. -/
theorem prf_lenc_eqrefl (t : Term) :
    Prf (lineWF t ⇒ ((Formula.eq (nthc t (succ zero)) (numeralM 12)) ⇒
      (Formula.eq (lenc t) (numeralM 3)))) :=
  prf_lenc_tag_and (k := 12) (m := 1) t
    (prf_ax (show ax_lineWF_eqrefl ∈ axioms by simp [axioms]))

/-- Tag 13 (`leibniz`) ⇒ `lenc = 5`. -/
theorem prf_lenc_leibniz (t : Term) :
    Prf (lineWF t ⇒ ((Formula.eq (nthc t (succ zero)) (numeralM 13)) ⇒
      (Formula.eq (lenc t) (numeralM 5)))) :=
  prf_lenc_tag_and (k := 13) (m := 3) t
    (prf_ax (show ax_lineWF_leibniz ∈ axioms by simp [axioms]))

/-- Tag 14 (`p3`) ⇒ `lenc = 3`. -/
theorem prf_lenc_p3 (t : Term) :
    Prf (lineWF t ⇒ ((Formula.eq (nthc t (succ zero)) (numeralM 14)) ⇒
      (Formula.eq (lenc t) (numeralM 3)))) :=
  prf_lenc_tag_and (k := 14) (m := 1) t
    (prf_ax (show ax_lineWF_p3 ∈ axioms by simp [axioms]))

/-- Tag 15 (`thy`) ⇒ `lenc = 2`. -/
theorem prf_lenc_thy (t : Term) :
    Prf (lineWF t ⇒ ((Formula.eq (nthc t (succ zero)) (numeralM 15)) ⇒
      (Formula.eq (lenc t) (numeralM 2)))) :=
  prf_lenc_tag_and (k := 15) (m := 0) t
    (prf_ax (show ax_lineWF_thy ∈ axioms by simp [axioms]))

/-- Tag 17 (`gen`) ⇒ `lenc = 3`. -/
theorem prf_lenc_gen (t : Term) :
    Prf (lineWF t ⇒ ((Formula.eq (nthc t (succ zero)) (numeralM 17)) ⇒
      (Formula.eq (lenc t) (numeralM 3)))) :=
  prf_lenc_tag_and (k := 17) (m := 1) t
    (prf_ax (show ax_lineWF_gen ∈ axioms by simp [axioms]))

/-- Tag 18 (`ind`) ⇒ `lenc = 3`. -/
theorem prf_lenc_ind (t : Term) :
    Prf (lineWF t ⇒ ((Formula.eq (nthc t (succ zero)) (numeralM 18)) ⇒
      (Formula.eq (lenc t) (numeralM 3)))) :=
  prf_lenc_tag_and (k := 18) (m := 1) t
    (prf_ax (show ax_lineWF_ind ∈ axioms by simp [axioms]))

/-- Tag 19 (`qconf`) ⇒ `lenc = 4`. -/
theorem prf_lenc_qconf (t : Term) :
    Prf (lineWF t ⇒ ((Formula.eq (nthc t (succ zero)) (numeralM 19)) ⇒
      (Formula.eq (lenc t) (numeralM 4)))) :=
  prf_lenc_tag_and (k := 19) (m := 2) t
    (prf_ax (show ax_lineWF_qconf ∈ axioms by simp [axioms]))

/-- Tag 20 (`listInd`) ⇒ `lenc = 3`. -/
theorem prf_lenc_listInd (t : Term) :
    Prf (lineWF t ⇒ ((Formula.eq (nthc t (succ zero)) (numeralM 20)) ⇒
      (Formula.eq (lenc t) (numeralM 3)))) :=
  prf_lenc_tag_and (k := 20) (m := 1) t
    (prf_ax (show ax_lineWF_listInd ∈ axioms by simp [axioms]))

/-- ⭐⭐⭐ **EL CIERRE DE (b)**: la línea mide `args.length + 2` —eso lo dice `prf_lenc_objList`—,
el tag exige `n` —eso lo dicen los veintiún `prf_lenc_*` de arriba—, y si no coinciden la teoría
**refuta** `lineWF`.

⭐ Nótese que `himp` se toma como hipótesis en vez de despacharse aquí por tag: así este lema es
**uno solo para los veintiún tags**, y el despachador (§4) le pasa el `prf_lenc_*` que toque. -/
theorem derives_lineWF_neg_of_arity (f : Formula) (k n : Nat) (args : List Term)
    (himp : Prf (lineWF (objList (formCode f :: numeralM k :: args)) ⇒
      ((Formula.eq (nthc (objList (formCode f :: numeralM k :: args)) (succ zero)) (numeralM k)) ⇒
       (Formula.eq (lenc (objList (formCode f :: numeralM k :: args))) (numeralM n)))))
    (hne : args.length + 2 ≠ n) :
    axioms ⊢ neg (lineWF (objList (formCode f :: numeralM k :: args))) := by
  have htag : Prf (Formula.eq
      (nthc (objList (formCode f :: numeralM k :: args)) (succ zero)) (numeralM k)) :=
    prf_lineTag_cons (formCode f) (objList args) k
  have hlen : Prf (Formula.eq (lenc (objList (formCode f :: numeralM k :: args)))
      (numeralM (args.length + 2))) := by
    have := SinWTs.prf_lenc_objList (formCode f :: numeralM k :: args)
    simpa using this
  exact derives_lineWF_neg_of_lenc_imp (prf_mp (prf_swap_imp himp) htag) hlen hne


/-! ## §1quater · 🏁 EL CIERRE DE LA CAUSA **(c′)** — la conclusión no casa

⭐⭐ **Un solo cierre para los diecinueve tags estructurales**, y el reparto se queda fuera.
La forma que lo permite es `TagCode`: en vez de pedir la igualdad de Lean
`tagConcl k args = some ⌜c⌝` —que **sólo vale para doce de los diecinueve**, porque `substfc` y
`liftfc` son símbolos OBJETO y no reducen—, se pide el par «la ecuación literal de `tagConcl`
**más** una igualdad DEMOSTRABLE hasta el código». Los doce fáciles ponen `prf_refl`; los siete
duros ponen su reconstrucción aritmética.

⛔⛔ **Y de esos siete, CINCO ya estaban escritos** (`prf_q1_concl_code`, `prf_q2_concl_code`,
`prf_leibniz_concl_code`, `prf_ind_concl_code`, `prf_listInd_concl_code`, en
`Meta/ArithPrf.lean:470-540`), **exportados a la raíz**, y entre ellos los **dos que yo había
marcado como los más gnarly** (`ind` y `listInd`). Los re-derivé antes de encontrarlos, y las
re-derivaciones salieron **línea por línea idénticas**. Van **ONCE** de «antes de construir,
buscar».
🔑 *Cuando la re-derivación sale idéntica a la primera, no es que el problema fuera fácil: es que
ya estaba resuelto y no se buscó.*

⭐ Lo que de verdad faltaba eran **dos**: `q3` (11) y `qconf` (19), los del `liftfc` — y son dos
líneas cada uno. -/

/-- **El tag `k` con argumentos `args` reconstruye el CÓDIGO de `c`.**
El par, y no la igualdad de Lean, porque `substfc`/`liftfc` **no reducen**: para doce tags la
segunda componente es `prf_refl`, para siete es una reconstrucción aritmética. -/
def TagCode (k : Nat) (args : List Term) (c : Formula) : Prop :=
  ∃ e, And (tagConcl k args = some e) (Prf (e =eq formCode c))

/-- Si el código reconstruido es el de `c` y `f ≠ c`, la teoría refuta que sean iguales. -/
theorem derives_neg_eq_of_code_ne {f c : Formula} {e : Term}
    (hcode : Prf (e =eq formCode c)) (hne : f ≠ c) :
    axioms ⊢ neg (formCode f =eq e) := by
  refine FOL.MetaRules.raa (fun heq => ?_)
  exact FOL.MetaRules.mp (formCode_ne hne)
    (FOL.derive_eq_trans heq (prf_to_derives hcode))

/-- ⭐⭐⭐ **EL CIERRE DE (c′)**, uno para los diecinueve tags estructurales: si la línea dice
concluir `f` y el tag reconstruye `c ≠ f`, la teoría **refuta** `lineWF`.

⚠️ `htc` entra como hipótesis en vez de despacharse por tag aquí dentro — igual que en
`derives_lineWF_neg_of_arity` (§1ter) y `derives_chainOk_neg_of_prem_line` (§2quater):
*el reparto vive en el despachador (§4), no dentro de cada cierre*. -/
theorem derives_lineWF_neg_of_concl {f c : Formula} {k : Nat} {args : List Term}
    (htc : TagCode k args c) (hne : f ≠ c) :
    axioms ⊢ neg (lineWF (cons (formCode f) (cons (numeralM k) (objList args)))) := by
  obtain ⟨e, h1, h2⟩ := htc
  exact derives_lineWF_neg_of_tag k (formCode f) args e h1
    (derives_neg_eq_of_code_ne h2 hne)

/-! ### Los DOCE tags cuyo código sale por `rfl` -/

theorem tc_p1 (A B : Formula) : TagCode 0 [formCode A, formCode B] (A ⇒ (B ⇒ A)) :=
  ⟨_, rfl, prf_refl _⟩

theorem tc_p2 (A B C : Formula) :
    TagCode 1 [formCode A, formCode B, formCode C]
      ((A ⇒ (B ⇒ C)) ⇒ ((A ⇒ B) ⇒ (A ⇒ C))) := ⟨_, rfl, prf_refl _⟩

theorem tc_c1 (A B : Formula) :
    TagCode 2 [formCode A, formCode B] (A ⇒ (B ⇒ Formula.and A B)) := ⟨_, rfl, prf_refl _⟩

theorem tc_c2 (A B : Formula) :
    TagCode 3 [formCode A, formCode B] (Formula.and A B ⇒ A) := ⟨_, rfl, prf_refl _⟩

theorem tc_c3 (A B : Formula) :
    TagCode 4 [formCode A, formCode B] (Formula.and A B ⇒ B) := ⟨_, rfl, prf_refl _⟩

theorem tc_j1 (A B : Formula) :
    TagCode 5 [formCode A, formCode B] (A ⇒ Formula.or A B) := ⟨_, rfl, prf_refl _⟩

theorem tc_j2 (A B : Formula) :
    TagCode 6 [formCode A, formCode B] (B ⇒ Formula.or A B) := ⟨_, rfl, prf_refl _⟩

theorem tc_j3 (A B C : Formula) :
    TagCode 7 [formCode A, formCode B, formCode C]
      (Formula.or A B ⇒ ((A ⇒ C) ⇒ ((B ⇒ C) ⇒ C))) := ⟨_, rfl, prf_refl _⟩

theorem tc_efq (A : Formula) :
    TagCode 8 [formCode A] (Formula.bottom ⇒ A) := ⟨_, rfl, prf_refl _⟩

/-- ⚠️ Éste lleva `termCode`, no `formCode`, y aun así es `rfl`. -/
theorem tc_eqrefl (t : Term) : TagCode 12 [termCode t] (Formula.eq t t) :=
  ⟨_, rfl, prf_refl _⟩

theorem tc_p3 (A : Formula) :
    TagCode 14 [formCode A] (((A ⇒ Formula.bottom) ⇒ Formula.bottom) ⇒ A) :=
  ⟨_, rfl, prf_refl _⟩

/-- ⚠️ `gen` (17) **sí** está en `tagConcl`; los que no están son `thy` (15) y `mp` (16). -/
theorem tc_gen (A : Formula) : TagCode 17 [formCode A] (Formula.forall A) :=
  ⟨_, rfl, prf_refl _⟩

/-! ### Los SIETE con `substfc`/`liftfc`

⭐ Cinco son **una línea**, porque su reconstrucción estaba ya en `Meta/ArithPrf.lean`. -/

theorem tc_q1 (A : Formula) (t : Term) :
    TagCode 9 [formCode A, termCode t] (Formula.forall A ⇒ substFormula 0 t A) :=
  ⟨_, rfl, prf_q1_concl_code A t⟩

theorem tc_q2 (A : Formula) (t : Term) :
    TagCode 10 [formCode A, termCode t] (substFormula 0 t A ⇒ Formula.ex A) :=
  ⟨_, rfl, prf_q2_concl_code A t⟩

theorem tc_leibniz (A : Formula) (t₁ t₂ : Term) :
    TagCode 13 [formCode A, termCode t₁, termCode t₂]
      (Formula.eq t₁ t₂ ⇒ (substFormula 0 t₁ A ⇒ substFormula 0 t₂ A)) :=
  ⟨_, rfl, prf_leibniz_concl_code A t₁ t₂⟩

/-- ⚠️ Los dos `rw [termCodeM_eq]` son todo lo que separa la forma de `tagConcl` (que usa
`termCodeM`) de la de `ArithPrf` (que usa `termCode`). -/
theorem tc_ind (A : Formula) :
    TagCode 18 [formCode A] (ROBINSON_PlusPlus.Full.inductionFormula A) := by
  refine ⟨_, rfl, ?_⟩
  rw [ROBINSON_PlusPlus.Meta.Representability.termCodeM_eq,
      ROBINSON_PlusPlus.Meta.Representability.termCodeM_eq]
  exact prf_ind_concl_code A

theorem tc_listInd (A : Formula) :
    TagCode 20 [formCode A] (listInductionFormula A) := by
  refine ⟨_, rfl, ?_⟩
  rw [ROBINSON_PlusPlus.Meta.Representability.termCodeM_eq,
      ROBINSON_PlusPlus.Meta.Representability.termCodeM_eq]
  exact prf_listInd_concl_code A

/-- ⭐ **Uno de los dos que NO estaban**: el `liftfc` va en el consecuente del `∀`. -/
theorem tc_q3 (A B : Formula) :
    TagCode 11 [formCode A, formCode B]
      (Formula.forall (A ⇒ liftFormula 0 B) ⇒ (Formula.ex A ⇒ B)) :=
  ⟨_, rfl, prf_congr_bin1 (prf_congr_un (prf_congr_bin2 (prf_liftFormula_arith 0 B)))⟩

/-- ⭐ **El otro**: aquí el `liftfc` va en el ANTECEDENTE. Es la única diferencia con `tc_q3`,
y es la que ninguna de las dos habría heredado de la otra. -/
theorem tc_qconf (P C : Formula) :
    TagCode 19 [formCode P, formCode C] (confinementFormula P C) :=
  ⟨_, rfl, prf_congr_bin1 (prf_congr_un (prf_congr_bin1 (prf_liftFormula_arith 0 P)))⟩


/-! ## §1quinquies · 🏁 LOS CIERRES DE LA CAUSA **(f)** — el tipo de argumento

⭐⭐ **La sexta causa** (ADR‑075): `StdArgs` sólo exige que cada argumento sea `formCode _` **o**
`termCode _`, **sin decir cuál**, así que una línea estándar puede llevar un código de término
donde el tag espera uno de fórmula. El decodificador entonces falla en `decodeForm`.

⭐ Lo que la cierra es **álgebra de códigos**, y vive donde le toca: `Meta/CodeDistinct.lean`,
al lado de `formCode_ne`. El hecho de fondo cabe en una línea — los tags de cabeza son
**disjuntos**, `termCode` usa 0/1 y `formCode` usa 2…9 — y de él salen las siete ranuras.
🔑 *La mitad cara aparente —«¿y si el tag SÍ coincide?»— sólo ocurre en un constructor por
lema, y ahí se desciende una capa y se vuelve al mismo hecho de una línea.*

⚠️ **Lo que aquí se aterriza son DOS cierres, no diecinueve**, y es deliberado: cada tag
necesita saber **qué ranura** lleva el argumento del tipo equivocado, y eso es un análisis de
`StdArgs` que pertenece al **reparto** (§4), no al cierre. Los dos de abajo fijan el patrón de
las **dos direcciones** del desajuste: un `termCode` donde va fórmula (`p1`) y un `formCode`
donde va término (`eqrefl`). -/

/-- **(f) para `p1`**: código de TÉRMINO en el primer slot, que es de fórmula. -/
theorem derives_lineWF_neg_p1_badtype (f : Formula) (u cB : Term) :
    axioms ⊢ neg (lineWF (cons (formCode f) (cons (numeralM 0)
      (objList [termCode u, cB])))) :=
  derives_lineWF_neg_of_tag 0 (formCode f) [termCode u, cB] _ rfl
    (formCode_ne_implc_tc_1 f u _)

/-- **(f) para `eqrefl`**, en la dirección CONTRARIA: código de FÓRMULA en un slot de término. -/
theorem derives_lineWF_neg_eqrefl_badtype (f : Formula) (A : Formula) :
    axioms ⊢ neg (lineWF (cons (formCode f) (cons (numeralM 12)
      (objList [formCode A])))) :=
  derives_lineWF_neg_of_tag 12 (formCode f) [formCode A] _ rfl
    (formCode_ne_eqc_fc_1 f A _)


/-! ## §2 · `DEUDA_inNeg`: las CABEZAS de una cadena aceptada SON los códigos de sus conclusiones -/

/-- Lo que `decodeLine` garantiza, extraído: la regla CONCLUYE la cabeza. -/
theorem decodeLine_stepConcl {acc : List Formula} {line : Term} {f : Formula} {r : Rule}
    (h : decodeLine acc line = some (f, r)) : stepConcl acc r = some f := by
  cases line with
  | var n => simp [decodeLine] at h
  | func cs args =>
      cases args with
      | nil => simp [decodeLine] at h
      | cons a as =>
          cases as with
          | nil => simp [decodeLine] at h
          | cons b bs =>
              cases bs with
              | cons _ _ => simp [decodeLine] at h
              | nil =>
                  simp only [decodeLine] at h
                  split at h
                  · rcases hf : decodeForm a with _ | f'
                    · rw [hf] at h; simp at h
                    · rw [hf] at h; simp only [Option.bind] at h
                      rcases hr : decodeRule acc f' b with _ | r'
                      · rw [hr] at h; simp at h
                      · rw [hr] at h; simp only [Option.bind] at h
                        split at h
                        · simp only [Option.some.injEq, Prod.mk.injEq] at h
                          obtain ⟨h1, h2⟩ := h; subst h1; subst h2; assumption
                        · simp at h
                  · simp at h

/-- Y la otra mitad: la CABEZA del término es el código de la fórmula decodificada. -/
theorem decodeLine_carc {acc : List Formula} {line : Term} {f : Formula} {r : Rule}
    (h : decodeLine acc line = some (f, r)) : Prf (carc line =eq formCodeM f) := by
  cases line with
  | var n => simp [decodeLine] at h
  | func cs args =>
      cases args with
      | nil => simp [decodeLine] at h
      | cons a as =>
          cases as with
          | nil => simp [decodeLine] at h
          | cons b bs =>
              cases bs with
              | cons _ _ => simp [decodeLine] at h
              | nil =>
                  simp only [decodeLine] at h
                  split at h
                  · next hcs =>
                      rcases hf : decodeForm a with _ | f'
                      · rw [hf] at h; simp at h
                      · rw [hf] at h; simp only [Option.bind] at h
                        rcases hr : decodeRule acc f' b with _ | r'
                        · rw [hr] at h; simp at h
                        · rw [hr] at h; simp only [Option.bind] at h
                          split at h
                          · simp only [Option.some.injEq, Prod.mk.injEq] at h
                            obtain ⟨h1, _⟩ := h
                            have ha : a = formCodeM f' := decodeForm_inj hf
                            have hsym : cs = cons_sym := by simpa using hcs
                            subst hsym; subst ha; rw [← h1]
                            exact prf_carc_cons _ b
                          · simp at h
                  · simp at h

theorem decode_heads : ∀ (l : List Term) (acc : List Formula) (rs : List Rule) (L : List Formula),
    decodeChainAux acc (objList l) = some rs → checkAux rs acc = some L →
    ∃ fs : List Formula, And (L = acc ++ fs)
      (Prf (objList (l.map carc) =eq listFormCodeM fs))
  | [], acc, rs, L, hd, hc => by
      simp only [objList, nil, zero, decodeChainAux, beq_self_eq_true, if_true,
        Option.some.injEq] at hd
      subst hd
      simp only [checkAux, Option.some.injEq] at hc
      subst hc
      exact ⟨[], by simp, by simpa [objList, listFormCodeM] using prf_refl nil⟩
  | line :: rest, acc, rs, L, hd, hc => by
      simp only [objList, cons, decodeChainAux, beq_self_eq_true, if_true] at hd
      rcases hdl : decodeLine acc line with _ | fr
      · rw [hdl] at hd; simp at hd
      · rw [hdl] at hd
        simp only [Option.bind] at hd
        rcases hrec : decodeChainAux (acc ++ [fr.1]) (objList rest) with _ | rs'
        · rw [hrec] at hd; simp at hd
        · rw [hrec] at hd
          simp only [Option.map, Option.some.injEq] at hd
          subst hd
          -- `stepConcl acc fr.2 = some fr.1` viene de `decodeLine`
          have hstep : stepConcl acc fr.2 = some fr.1 := decodeLine_stepConcl hdl
          simp only [checkAux, hstep] at hc
          obtain ⟨fs, hL, heq⟩ := decode_heads rest (acc ++ [fr.1]) rs' L hrec hc
          refine ⟨fr.1 :: fs, by simpa using hL, ?_⟩
          -- la CABEZA: `carc line = formCodeM fr.1`
          have hcarc : Prf (carc line =eq formCodeM fr.1) := decodeLine_carc hdl
          show Prf (cons (carc line) (objList (rest.map carc))
                      =eq cons (formCodeM fr.1) (listFormCodeM fs))
          exact prf_eq_trans (prf_congr_cons_head hcarc) (prf_congr_cons_tail heq)


/-! ## §2bis · EL FRONT-END — de «el decodificador rechaza» a la línea CULPABLE

⛔ La cabecera de este módulo afirmaba que «(a)–(d) componen con §1 y cierran». **Era falso**:
el puente de §1 exige una `k` y una `x` **concretas**, y no había nada que fuera de
`decodeChainAux … = none` a esa `k` (`grep` de `firstBad|badIdx|failIdx|takeWhile`: vacío).
Ésta es esa pieza, y **la necesitan las SEIS causas**, no sólo (e).

⭐ Es el **gemelo negativo de `decode_heads`** (§2): la misma inducción sobre la lista, con los
existenciales cambiados. `decode_heads` recorre una cadena que SÍ decodifica y saca sus cabezas;
ésta recorre una que NO y saca la primera línea que falla, con el prefijo que sí decodificó y su
acumulador. 🔑 *El sujeto cambia, la inducción no.*

📏 **30 líneas medidas**, contra 70–100 ESTIMADAS por el panel. -/

/-- ⭐⭐ **EL FRONT-END**: si el decodificador rechaza la cadena, hay una **PRIMERA** línea `k`
que lo hace; el prefijo anterior decodifica (`rs`) y su acumulador es `L`. -/
theorem decodeChainAux_none_first : ∀ (l : List Term) (acc : List Formula),
    decodeChainAux acc (objList l) = none →
    ∃ (k : Nat) (x : Term) (rs : List Rule) (L : List Formula),
      And (l[k]? = some x)
     (And (decodeChainAux acc (objList (l.take k)) = some rs)
     (And (checkAux rs acc = some L)
          (decodeLine L x = none)))
  | [], acc, hd => by
      -- ⛔ imposible: la cadena vacía SIEMPRE decodifica (`objList [] = nil`)
      simp [objList, nil, zero, decodeChainAux] at hd
  | line :: rest, acc, hd => by
      simp only [objList, cons, decodeChainAux, beq_self_eq_true, if_true] at hd
      rcases hdl : decodeLine acc line with _ | fr
      · -- ⭐ la PRIMERA línea ya falla ⇒ `k = 0`, prefijo vacío, acumulador `acc`
        exact ⟨0, line, [], acc, rfl,
          by simp [objList, nil, zero, decodeChainAux],
          by simp [checkAux], hdl⟩
      · rw [hdl] at hd
        simp only [Option.bind] at hd
        rcases hrec : decodeChainAux (acc ++ [fr.1]) (objList rest) with _ | rs'
        · -- la recursión falla ⇒ la primera mala está en `rest`
          obtain ⟨k, x, rs, L, hx, hpre, hchk, hnone⟩ :=
            decodeChainAux_none_first rest (acc ++ [fr.1]) hrec
          refine ⟨k + 1, x, fr.2 :: rs, L, hx, ?_, ?_, hnone⟩
          · show decodeChainAux acc (objList (line :: rest.take k)) = some (fr.2 :: rs)
            simp only [objList, cons, decodeChainAux, beq_self_eq_true, if_true, hdl,
              Option.bind, hpre, Option.map]
          · -- `checkAux (fr.2 :: rs) acc`: la cabeza pasa por `stepConcl`
            have hstep : stepConcl acc fr.2 = some fr.1 := decodeLine_stepConcl hdl
            simp only [checkAux, hstep]
            exact hchk
        · rw [hrec] at hd; simp at hd


/-- ⭐⭐ **Cada línea del prefijo concluye algo que está en el acumulador.** Es el refinamiento
de `decode_heads`: aquélla da la igualdad a nivel de LISTA, ésta **elemento a elemento**.

⭐ La clave del abaratamiento fue enunciarlo por **PERTENENCIA** y no por índices: lo único que
se le pide luego a `f` es `f ≠ g`, y eso sale de `f ∈ L` con `g ∉ L`, sin cuadrar ningún
desplazamiento `acc.length + j`. 🔑 *Cuando un enunciado por índices se atasca, mirar si la
pertenencia basta.*

⚠️ Y va con `List.Mem` explícito porque `∈` resuelve al símbolo OBJETO — la misma trampa que
`≤`/`le`, y la que `prf_not_In_listFormCodeM` ya esquivaba así. -/
theorem decodeChainAux_carc_mem :
    ∀ (l : List Term) (acc : List Formula) (rs : List Rule) (L : List Formula),
      decodeChainAux acc (objList l) = some rs → checkAux rs acc = some L →
      ∀ x, List.Mem x l → ∃ f, And (List.Mem f L) (Prf (Formula.eq (carc x) (formCodeM f)))
  | [], _, _, _, _, _, _, hx => by cases hx
  | line :: rest, acc, rs, L, hd, hc, x, hx => by
      simp only [objList, cons, decodeChainAux, beq_self_eq_true, if_true] at hd
      rcases hdl : decodeLine acc line with _ | fr
      · rw [hdl] at hd; simp at hd
      · rw [hdl] at hd
        simp only [Option.bind] at hd
        rcases hrec : decodeChainAux (acc ++ [fr.1]) (objList rest) with _ | rs'
        · rw [hrec] at hd; simp at hd
        · rw [hrec] at hd
          simp only [Option.map, Option.some.injEq] at hd
          subst hd
          have hstep : stepConcl acc fr.2 = some fr.1 := decodeLine_stepConcl hdl
          simp only [checkAux, hstep] at hc
          obtain ⟨fs, hL, _⟩ := decode_heads rest (acc ++ [fr.1]) rs' L hrec hc
          cases hx with
          | head =>
              refine ⟨fr.1, ?_, decodeLine_carc hdl⟩
              rw [hL]
              exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr (List.Mem.head _))))
          | tail _ hm =>
              exact decodeChainAux_carc_mem rest (acc ++ [fr.1]) rs' L hrec hc x hm


/-- ⭐⭐ **EL FRONT-END DE LA LÍNEA**: una línea estándar que no decodifica falla o bien porque
la **REGLA** no sale, o bien porque la **CONCLUSIÓN no casa**. Lo primero cubre (a), (b), (d),
(e) y (f); lo segundo **es exactamente (c)**.

⭐⭐ Y esquiva el único riesgo que el panel marcó como posiblemente caro. Decía que habría que
**invertir el `match` de 21 formas** de `decodeRuleTag`, lo que según la cabecera de
`Meta/ChainDecode.lean:44` **revienta el `whnf`** (por eso existe `peelArgs`). **No hace falta
invertirlo**: basta separar los **dos `bind`** de `decodeLine`, y el resultado ya apunta a
`decodeRuleTag` con el tag y los argumentos pelados. Cada causa analiza desde ahí, con el tag
ya en la mano.
🔑 *El case-split de 21 formas no había que hacerlo: había que no llegar a necesitarlo.* Es la
misma forma que `LeibnizPrin`/`eqAx` en el Hauptsatz — lo que desbloquea no es esfuerzo, es
dónde se pone el corte.

⚠️ Nota de proceso, por si alguien «limpia» esta prueba: el linter marca como *argumento no
usado* un `simp only` que **sí** hace la reducción iota. Quitarlo rompe la prueba.
*Un aviso de «no usado» no es una medición de que sobre.* -/
theorem decodeLine_none_cases {acc : List Formula} {f : Formula} {k : Nat} {as : Term}
    (h : decodeLine acc (cons (formCode f) (cons (numeralM k) as)) = none) :
    Or (decodeRuleTag acc f k (peelArgs as) = none)
       (∃ r, And (decodeRuleTag acc f k (peelArgs as) = some r)
                 (stepConcl acc r ≠ some f)) := by
  simp only [decodeLine, cons, beq_self_eq_true, if_true, decodeForm_formCode,
    Option.bind, decodeRule, peelArgs, decodeNat_numeralM] at h
  rcases hr : decodeRuleTag acc f k (peelArgs as) with _ | r
  · exact Or.inl rfl
  · refine Or.inr ⟨r, rfl, ?_⟩
    by_cases hs : stepConcl acc r = some f
    · rw [hr] at h; simp [hs] at h
    · exact hs


/-! ## §2ter · 🏁 el cierre de la causa **(d)**, de punta a punta -/

/-- ⭐⭐ **(d), DE PUNTA A PUNTA**: si el decodificador rechaza una línea `thy`, la teoría
**refuta** esa línea. Es la primera de las seis causas que queda cerrada desde el `= none` del
verificador hasta un `axioms ⊢ neg (lineWF …)`.

La cadena entera son **tres eslabones**, y los tres o existían o salían de generalizar algo que
existía: `decodeRuleTag … 15 … = none` ⇒ `findIdx f axioms = none`
(`Meta/ChainDecode.lean:164`, por `rfl`) ⇒ `f ∉ axioms` (`not_mem_of_findIdx_none`) ⇒ la
refutación (`derives_lineWF_neg_thy_of_not_mem`, vía `neg_In_axiomsCodeT_of_not_mem`).

⚠️ Footprint: **cita `ax_axiomsCodeT_eq`**, a diferencia de `deuda_inNeg` (§3). Es esperable —
`axiomsCodeT` es precisamente lo que el ancla fija. -/
theorem derives_lineWF_neg_thy_of_decode {acc : List Formula} {f : Formula} {args : List Term}
    (h : decodeRuleTag acc f 15 args = none) :
    axioms ⊢ neg (lineWF (cons (formCode f) (cons (numeralM 15) nil))) := by
  refine derives_lineWF_neg_thy_of_not_mem f (not_mem_of_findIdx_none ?_)
  rcases hj : findIdx f axioms with _ | j
  · rfl
  · rw [show decodeRuleTag acc f 15 args = (findIdx f axioms).map Rule.thy from rfl, hj] at h
    simp at h


/-! ## §2quater · 🏁 EL CIERRE DE LA CAUSA **(e)**

⭐⭐⭐ **(e) era «la única sin maquinaria» y ha salido de cinco lemas, cuatro de ellos de diez
líneas.** La pieza que lo hace barato es la de en medio: para **refutar** un `∀ j < lenc L` basta
**UN índice malo**, así que se **instancia** — no se induce sobre `L`. La inducción sólo hace
falta en la otra dirección (la cota de líneas), y ésa es `derives_not_boundedCarcLt` (§1bis).

🔑 *Refutar un acotado es exhibir un testigo; sólo PROBARLO obliga a recorrerlo entero.*
-/

/-- Refutar una disyunción es refutar sus dos lados. -/
theorem derives_neg_lor {A B : Formula} (ha : axioms ⊢ neg A) (hb : axioms ⊢ neg B) :
    axioms ⊢ neg (lor A B) :=
  FOL.MetaRules.raa (fun h => FOL.MetaRules.or_elim h
    (fun x => FOL.MetaRules.mp ha x) (fun x => FOL.MetaRules.mp hb x))

/-- Transporte de la refutación de la cota por su **primer** argumento (el término buscado).
    Hace falta porque `boundedPremsIn` menciona la premisa como `nthc L m̄` —sintácticamente—,
    y no como el código concreto que el motor de abajo refuta. -/
theorem derives_not_boundedCarcLt_congr (y z p b : Term)
    (h : axioms ⊢ (y =eq z)) (hn : axioms ⊢ neg (boundedCarcLt z p b)) :
    axioms ⊢ neg (boundedCarcLt y p b) := by
  have key : ∀ t : Term,
      substFormula 0 t (neg (boundedCarcLt (.var 0) (liftTerm 0 p) (liftTerm 0 b)))
      = neg (boundedCarcLt t p b) := by
    intro t
    simp [neg, substFormula, substFormula_boundedCarcLt, substTerm, FOL.substTerm_liftTerm]
  have h0 : axioms ⊢
      substFormula 0 z (neg (boundedCarcLt (.var 0) (liftTerm 0 p) (liftTerm 0 b))) := by
    rw [key]; exact hn
  have hsub := Derives.subst axioms z y
    (neg (boundedCarcLt (.var 0) (liftTerm 0 p) (liftTerm 0 b))) (FOL.derive_eq_symm h) h0
  rwa [key] at hsub

/-- ⭐⭐ **EL MOTOR DE (e)**: si `φ` no está en el acumulador que el decodificador hiló con las `k`
primeras líneas, entonces **ninguna de esas `k` líneas concluye `⌜φ⌝`** — y la teoría lo demuestra.

⭐ Sale de encajar dos cosas que ya estaban: `decodeChainAux_carc_mem` (§2bis) dice, para cada
línea del prefijo, **qué** fórmula del acumulador es su `carc`; y `formCode_ne` separa los códigos
de dos fórmulas distintas. El paso de `φ ∉ L` a «distinta de cada una» es un `▸`. -/
theorem derives_not_boundedCarcLt_of_not_mem
    (l : List Term) (k : Nat) (hk : Nat.le k l.length)
    (acc : List Formula) (rs : List Rule) (L : List Formula)
    (hd : decodeChainAux acc (objList (l.take k)) = some rs) (hc : checkAux rs acc = some L)
    (φ : Formula) (hnm : ¬ List.Mem φ L) :
    axioms ⊢ neg (boundedCarcLt (formCode φ) (objList l) (numeralM k)) := by
  refine derives_not_boundedCarcLt (formCode φ) k l hk ?_
  intro j x hj hx
  have hxt : (l.take k)[j]? = some x := by
    rw [List.getElem?_take, if_pos hj]; exact hx
  obtain ⟨f, hfL, hcarc⟩ :=
    decodeChainAux_carc_mem (l.take k) acc rs L hd hc x (List.mem_of_getElem? hxt)
  have hne : φ ≠ f := fun e => hnm (e ▸ hfL)
  refine FOL.MetaRules.raa (fun heq => ?_)
  have h1 : axioms ⊢ (formCode φ =eq formCodeM f) :=
    FOL.derive_eq_trans (FOL.derive_eq_symm heq) (prf_to_derives hcarc)
  rw [ROBINSON_PlusPlus.Meta.Representability.formCodeM_eq] at h1
  exact FOL.MetaRules.mp (formCode_ne hne) h1

/-- ⭐⭐ **REFUTAR EL ∀ ACOTADO POR INSTANCIACIÓN**, no por inducción sobre `L`.

⚠️ Es aquí donde (e) deja de ser caro. `prf_boundedPremsIn_cons_succ_iff` invitaba a recorrer `L`
entero; no hace falta: `boundedPremsIn` **es** un `Formula.forall`, y `spec` da la instancia en el
índice malo. Lo demás es un *modus ponens* contra la cota. -/
theorem derives_not_boundedPremsIn_of_index (p i L : Term) (m : Nat)
    (hlt : axioms ⊢ lt (numeralM m) (lenc L))
    (hne : axioms ⊢ neg (lor (In (nthc L (numeralM m)) nil)
                             (boundedCarcLt (nthc L (numeralM m)) p i))) :
    axioms ⊢ neg (boundedPremsIn nil p i L) := by
  refine FOL.MetaRules.raa (fun hbp => ?_)
  have hspec := spec hbp (numeralM m)
  have heq : substFormula 0 (numeralM m)
      (Formula.impl (lt (.var 0) (liftTerm 0 (lenc L)))
        (lor (In (nthc (liftTerm 0 L) (.var 0)) (liftTerm 0 nil))
             (boundedCarcLt (nthc (liftTerm 0 L) (.var 0)) (liftTerm 0 p) (liftTerm 0 i))))
      = Formula.impl (lt (numeralM m) (lenc L))
          (lor (In (nthc L (numeralM m)) nil)
               (boundedCarcLt (nthc L (numeralM m)) p i)) := by
    simp only [substFormula, substFormula_boundedCarcLt, lt, lenc, nthc, In, lor, nil, zero,
      substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  rw [heq] at hspec
  exact FOL.MetaRules.mp hne (FOL.MetaRules.mp hspec hlt)

/-- ⭐⭐⭐ **EL CIERRE DE (e)**: una línea cuya premisa `m`-ésima no la concluye ninguna línea
anterior **refuta la cadena entera**.

⭐ El lado `In _ nil` del `lor` sale **gratis**: el acumulador de arranque es `nil` y
`prf_not_in_nil_D` lleva ahí desde `Meta/AxiomListCode.lean`. La forma Δ₀ pagó justo aquí lo que
prometía: **el acumulador ha desaparecido**, y por eso ese lado es trivial.

⚠️ Éste habla de `nthc` sobre la cadena. El que consume el ensamblaje es el de **más abajo**,
`derives_chainOk_neg_of_prem_line`, que toma la **línea concreta** y hace ese transporte por dentro. -/
theorem derives_chainOk_neg_of_prem (l : List Term) (k m : Nat) (hk : k < l.length)
    (hlt : axioms ⊢ lt (numeralM m) (lenc (premsOf (nthc (objList l) (numeralM k)))))
    (hnb : axioms ⊢ neg (boundedCarcLt
             (nthc (premsOf (nthc (objList l) (numeralM k))) (numeralM m))
             (objList l) (numeralM k))) :
    axioms ⊢ neg (chainOk nil (objList l)) :=
  derives_chainOk_neg_of_prems l k hk
    (derives_not_boundedPremsIn_of_index (objList l) (numeralM k)
      (premsOf (nthc (objList l) (numeralM k))) m hlt
      (derives_neg_lor (prf_not_in_nil_D _) hnb))


/-- Transporte del enunciado **entero** por la línea, en **UNA** sustitución.

⭐ No hacen falta congruencias de `premsOf`, de `lenc` ni de `nthc` por separado: el molde
`Derives.subst` con `F := neg (boundedPremsIn … (premsOf #0))` las hace **todas a la vez**,
porque `#0` está debajo de las tres. Es el mismo molde que `derives_lineWF_congr` (§0).
🔑 *Una congruencia por CADA capa es el error; la sustitución es UNA, en la variable de dentro.* -/
theorem derives_not_boundedPremsIn_congr {t₁ t₂ p i : Term}
    (h : axioms ⊢ (t₁ =eq t₂))
    (hn : axioms ⊢ neg (boundedPremsIn nil p i (premsOf t₁))) :
    axioms ⊢ neg (boundedPremsIn nil p i (premsOf t₂)) := by
  have key : ∀ s : Term,
      substFormula 0 s (neg (boundedPremsIn (liftTerm 0 nil) (liftTerm 0 p) (liftTerm 0 i)
        (premsOf (.var 0))))
      = neg (boundedPremsIn nil p i (premsOf s)) := by
    intro s
    simp only [neg, substFormula, substFormula_boundedPremsIn, premsOf, substTerm, substTerms,
      nil, zero, FOL.substTerm_liftTerm, if_true]
  have h0 : axioms ⊢ substFormula 0 t₁ (neg (boundedPremsIn (liftTerm 0 nil) (liftTerm 0 p)
      (liftTerm 0 i) (premsOf (.var 0)))) := by rw [key]; exact hn
  have hsub := Derives.subst axioms t₁ t₂ _ h h0
  rwa [key] at hsub

/-- ⭐⭐⭐ **(e) SOBRE LA LÍNEA CONCRETA** — el **gemelo exacto** de `derives_chainOk_neg_of_line`
(§1), y la forma que de verdad consume el ensamblaje: toma la línea `x` tal como la entrega
`decodeChainAux_none_first` (§2bis) y hace el transporte a `nthc ⟦l⟧ k̄` **por dentro**.

⬜ Lo único que le queda a (e) es, por cada regla con premisas, la forma de `premsOf x`:
`prf_premsOf_mp` y `prf_premsOf_gen` (`Meta/PremsOfTagPrf.lean`) la dan **en positivo**, y de ahí
salen las dos hipótesis de abajo. **Eso ya no es lógica, es aritmética de listas-código.** -/
theorem derives_chainOk_neg_of_prem_line (l : List Term) (k m : Nat) (x : Term)
    (hk : l[k]? = some x)
    (hlt : axioms ⊢ lt (numeralM m) (lenc (premsOf x)))
    (hnb : axioms ⊢ neg (boundedCarcLt (nthc (premsOf x) (numeralM m))
                            (objList l) (numeralM k))) :
    axioms ⊢ neg (chainOk nil (objList l)) := by
  have hklt : k < l.length := by
    rcases List.getElem?_eq_some_iff.mp hk with ⟨hb, _⟩; exact hb
  have hnth : axioms ⊢ (nthc (objList l) (numeralM k) =eq x) :=
    prf_to_derives (SinWTs.prf_nthc_objList l k x hk)
  refine derives_chainOk_neg_of_prems l k hklt ?_
  refine derives_not_boundedPremsIn_congr (FOL.derive_eq_symm hnth) ?_
  exact derives_not_boundedPremsIn_of_index (objList l) (numeralM k) (premsOf x) m hlt
    (derives_neg_lor (prf_not_in_nil_D _) hnb)


/-! ## §2quinquies · 🏁 (e), INSTANCIADA en `mp` y `gen`

⭐⭐ **La pieza que lo hace posible es que `ax_premsOf_mp` y `ax_premsOf_gen` están enunciados
sobre la línea CONCRETA y son INCONDICIONALES**: no piden `lineWF`. Los envoltorios
`prf_premsOf_mp`/`prf_premsOf_gen` (`Meta/PremsOfTagPrf.lean:363`, `:376`) sí lo piden —porque
trabajan sobre una línea ABSTRACTA, con accesores— y ahí habría hecho falta meterse dentro del
`raa`. Sobre una línea estándar, que es la que el despachador entrega, se va directo al axioma.

🔑 *Un esquema con accesores vale para una línea abstracta y cuesta una hipótesis; el mismo
esquema en forma explícita vale sólo para la línea concreta y no cuesta ninguna. Cuando se tiene
la línea, la forma explícita es la barata.* -/

/-- `premsOf` de una línea `mp` ESTÁNDAR, sin pasar por `lineWF`. -/
theorem prf_premsOf_mp_line (cf cfj : Term) :
    Prf (premsOf (cons cf (cons (numeralM 16) (cons cfj nil)))
          =eq cons (implc cfj cf) (cons cfj nil)) := by
  have h := prf_spec (prf_spec
    (prf_ax (show ax_premsOf_mp ∈ axioms by simp [axioms])) cf) cfj
  simpa [ax_premsOf_mp, premsOf, implc, cons, nil, numeralM, succ, zero,
    substFormula, substTerm, substTerms, substTerm_numeralM, FOL.substTerm_liftTerm,
    FOL.substTerm_liftLift] using h

/-- `premsOf` de una línea `gen` ESTÁNDAR, sin pasar por `lineWF`. -/
theorem prf_premsOf_gen_line (cf cg : Term) :
    Prf (premsOf (cons cf (cons (numeralM 17) (cons cg nil))) =eq cons cg nil) := by
  have h := prf_spec (prf_spec
    (prf_ax (show ax_premsOf_gen ∈ axioms by simp [axioms])) cf) cg
  simpa [ax_premsOf_gen, premsOf, cons, nil, numeralM, succ, zero,
    substFormula, substTerm, substTerms, substTerm_numeralM, FOL.substTerm_liftTerm,
    FOL.substTerm_liftLift] using h

/-- Longitud de una lista-código de **dos** elementos. -/
theorem prf_lenc_two (a b : Term) : Prf (lenc (cons a (cons b nil)) =eq numeralM 2) := by
  refine prf_eq_trans (prf_lenc_cons a (cons b nil)) (prf_eq_congr_succ ?_)
  exact prf_eq_trans (prf_lenc_cons b nil) (prf_eq_congr_succ prf_lenc_nil)

/-- Longitud de una lista-código de **un** elemento. -/
theorem prf_lenc_one (a : Term) : Prf (lenc (cons a nil) =eq numeralM 1) :=
  prf_eq_trans (prf_lenc_cons a nil) (prf_eq_congr_succ prf_lenc_nil)

/-- Segundo elemento de una lista-código de dos. -/
theorem prf_nthc_two_1 (a b : Term) :
    Prf (nthc (cons a (cons b nil)) (numeralM 1) =eq b) :=
  prf_eq_trans (prf_nthc_succ a (cons b nil) zero) (prf_nthc_zero b nil)

/-- ⭐⭐⭐ **EL CIERRE GENÉRICO DE (e)**: si la premisa `m`-ésima de la línea `k` es `⌜φ⌝` y `φ`
**no** está en el acumulador que el decodificador hiló con las `k` primeras líneas, la cadena
entera queda refutada.

⭐ No menciona regla ninguna: `mp` y `gen` sólo se distinguen por las dos ecuaciones que se le
pasan (`hlen` y `hnth`). El reparto, otra vez, vive en el despachador (§4). -/
theorem derives_chainOk_neg_of_prem_code
    (l : List Term) (k m n : Nat) (x : Term) (φ : Formula)
    (hk : l[k]? = some x) (hmn : m < n)
    (acc : List Formula) (rs : List Rule) (L : List Formula)
    (hd : decodeChainAux acc (objList (l.take k)) = some rs) (hc : checkAux rs acc = some L)
    (hnm : ¬ List.Mem φ L)
    (hlen : Prf (lenc (premsOf x) =eq numeralM n))
    (hnth : Prf (nthc (premsOf x) (numeralM m) =eq formCode φ)) :
    axioms ⊢ neg (chainOk nil (objList l)) := by
  have hklt : k < l.length := by
    rcases List.getElem?_eq_some_iff.mp hk with ⟨hb, _⟩; exact hb
  have hlt0 : axioms ⊢ lt (numeralM m) (numeralM n) := by
    have := gnum_lt (a := m) (b := n) hmn
    simpa only [numeralM_eq] using this
  have hlt : axioms ⊢ lt (numeralM m) (lenc (premsOf x)) :=
    derives_lt_congr_right (FOL.derive_eq_symm (prf_to_derives hlen)) hlt0
  refine derives_chainOk_neg_of_prem_line l k m x hk hlt ?_
  exact derives_not_boundedCarcLt_congr _ (formCode φ) _ _ (prf_to_derives hnth)
    (derives_not_boundedCarcLt_of_not_mem l k (Nat.le_of_lt hklt) acc rs L hd hc φ hnm)

/-- **(e) para `mp`, premisa MAYOR** (`fj ⇒ f`, índice 0). -/
theorem derives_chainOk_neg_mp_major (l : List Term) (k : Nat) (f fj : Formula)
    (hk : l[k]? = some (cons (formCode f) (cons (numeralM 16) (cons (formCode fj) nil))))
    (acc : List Formula) (rs : List Rule) (L : List Formula)
    (hd : decodeChainAux acc (objList (l.take k)) = some rs) (hc : checkAux rs acc = some L)
    (hnm : ¬ List.Mem (Formula.impl fj f) L) :
    axioms ⊢ neg (chainOk nil (objList l)) := by
  have hp := prf_premsOf_mp_line (formCode f) (formCode fj)
  refine derives_chainOk_neg_of_prem_code l k 0 2 _ (Formula.impl fj f) hk (by decide)
    acc rs L hd hc hnm ?_ ?_
  · exact prf_eq_trans (SinWTs.prf_congr_lenc hp) (prf_lenc_two _ _)
  · exact prf_eq_trans (SinWTs.prf_congr_nthc_lst _ hp) (prf_nthc_zero _ _)

/-- **(e) para `mp`, premisa MENOR** (`fj`, índice 1). -/
theorem derives_chainOk_neg_mp_minor (l : List Term) (k : Nat) (f fj : Formula)
    (hk : l[k]? = some (cons (formCode f) (cons (numeralM 16) (cons (formCode fj) nil))))
    (acc : List Formula) (rs : List Rule) (L : List Formula)
    (hd : decodeChainAux acc (objList (l.take k)) = some rs) (hc : checkAux rs acc = some L)
    (hnm : ¬ List.Mem fj L) :
    axioms ⊢ neg (chainOk nil (objList l)) := by
  have hp := prf_premsOf_mp_line (formCode f) (formCode fj)
  refine derives_chainOk_neg_of_prem_code l k 1 2 _ fj hk (by decide)
    acc rs L hd hc hnm ?_ ?_
  · exact prf_eq_trans (SinWTs.prf_congr_lenc hp) (prf_lenc_two _ _)
  · exact prf_eq_trans (SinWTs.prf_congr_nthc_lst _ hp) (prf_nthc_two_1 _ _)

/-- **(e) para `gen`** (premisa única, índice 0). -/
theorem derives_chainOk_neg_gen (l : List Term) (k : Nat) (f g : Formula)
    (hk : l[k]? = some (cons (formCode f) (cons (numeralM 17) (cons (formCode g) nil))))
    (acc : List Formula) (rs : List Rule) (L : List Formula)
    (hd : decodeChainAux acc (objList (l.take k)) = some rs) (hc : checkAux rs acc = some L)
    (hnm : ¬ List.Mem g L) :
    axioms ⊢ neg (chainOk nil (objList l)) := by
  have hp := prf_premsOf_gen_line (formCode f) (formCode g)
  refine derives_chainOk_neg_of_prem_code l k 0 1 _ g hk (by decide)
    acc rs L hd hc hnm ?_ ?_
  · exact prf_eq_trans (SinWTs.prf_congr_lenc hp) (prf_lenc_one _)
  · exact prf_eq_trans (SinWTs.prf_congr_nthc_lst _ hp) (prf_nthc_zero _ _)


/-! ## §3 · 🏁 `DEUDA_inNeg`, SALDADA -/

/-- Transporte de una NO‑pertenencia por igualdad del contenedor. -/
theorem derives_not_In_congr {x t₁ t₂ : Term}
    (h : axioms ⊢ (t₁ =eq t₂)) (hne : axioms ⊢ neg (In x t₂)) :
    axioms ⊢ neg (In x t₁) :=
  FOL.MetaRules.raa (fun hin =>
    FOL.MetaRules.mp hne (ROBINSON_PlusPlus.Full.eq_subst_in h hin))

theorem deuda_inNeg : ROBINSON_PlusPlus.Meta.VerifierSound.DEUDA_inNeg := by
  intro φ l L _hstd hcd hnm
  -- desarmar `conclsDec`
  unfold ROBINSON_PlusPlus.Meta.VerifierSound.conclsDec at hcd
  rcases hdec : decodeChain (objList l) with _ | rs
  · rw [hdec] at hcd; simp at hcd
  · rw [hdec] at hcd
    simp only [Option.bind] at hcd
    -- las cabezas SON los códigos de las conclusiones
    obtain ⟨fs, hL, heads⟩ := decode_heads l [] rs L hdec hcd
    simp only [List.nil_append] at hL
    have hnm' : ¬ List.Mem φ fs := by rw [hL] at hnm; exact hnm
    -- `runFn nil ⟦l⟧ = ⟦l.map carc⟧ = listFormCodeM fs`
    have hrun : Prf (runFn nil (objList l) =eq objList (l.map carc)) :=
      prf_eq_trans (prf_runFn_objList l nil) (prf_concat_nil_eq _)
    have hchain : axioms ⊢ (runFn nil (objList l) =eq listFormCodeM fs) :=
      prf_to_derives (prf_eq_trans hrun heads)
    exact derives_not_In_congr hchain (prf_not_In_listFormCodeM φ fs hnm')

/-! ## §4 · 🏁 EL DESPACHADOR — de `chainOkDec l = false` a la TABLA DE CAUSAS

⭐⭐⭐ **Esto era lo que se daba por el riesgo de la vía, y la medición lo refuta.**

La cabecera de `Meta/ChainDecode.lean:44` avisa de que *«un `match` sobre `Term` con las 21 formas
anidadas revienta el `whnf` (`String.decEq` en el discriminante)»*, y de ahí salió la idea de que
repartir entre las seis causas sería caro. **No aplica al despachador**: `peelArgs` ya movió el
`match` de `Term` a `(tag : Nat, args : List Term)`, y un split de 21 ramas sobre un `Nat`
elabora en **4,5 s** y sale **net‑0 puro** (medido, `sondeos/DespachadorCoste.lean`).

🔑 *El aviso de rendimiento era CIERTO y estaba en el sitio equivocado: describía la vía que
`peelArgs` ya había abandonado.* Una nota de riesgo sobrevive al rediseño que la deja sin objeto.

⚠️ Lo que este lema **no** hace: elegir el cierre. Eso es la tabla de causas, y son (b), (c′) y
(f) más la forma de `premsOf` por regla en (e). Lo que sí hace es dejarlas **a todas** con la
misma entrada: la línea mala, ya descompuesta, con su prefijo decodificado y el acumulador que
el verificador tenía en ese punto. -/

/-- ⭐⭐⭐ **EL DESPACHADOR.** Todo lo que hay entre `chainOkDec l = false` y la tabla de causas,
en un solo enunciado: la **primera** línea que el verificador rechaza, ya partida en
`⟨⌜f⌝, tag, as⟩` con `StdArgs as`, junto con el prefijo decodificado (`rs`), el acumulador de
conclusiones en ese punto (`L`) y el **corte regla‑vs‑conclusión** hecho.

Compone cuatro piezas y no prueba nada por su cuenta:
`chainOkDec`/`decodeChain` (definiciones) → `decodeChainAux_none_first` (§2bis, el front‑end) →
`StdChain`/`StdLine` (ADR‑022, la forma) → `decodeLine_none_cases` (§2bis, el corte).

⭐ Las **seis** causas consumen exactamente esta salida:
* el `Or.inr` **es** (c′) —`stepConcl ≠ f`—, con `tag` y argumentos ya en la mano;
* el `Or.inl` reparte (a) (`tag > 20`), (b) (aridad), (d) (`tag = 15`), (e) (`tag ∈ {16,17}`)
  y (f) (tipo de argumento);
* y `L` es justo el acumulador que pide `derives_not_boundedCarcLt_of_not_mem` (§2quater). -/
theorem dispatcher (l : List Term) (hstd : StdChain l) (hdec : chainOkDec l = false) :
    ∃ (k : Nat) (f : Formula) (tag : Nat) (as : Term) (rs : List Rule) (L : List Formula),
      And (l[k]? = some (cons (formCode f) (cons (numeralM tag) as)))
     (And (StdArgs as)
     (And (decodeChainAux [] (objList (l.take k)) = some rs)
     (And (checkAux rs [] = some L)
          (Or (decodeRuleTag L f tag (peelArgs as) = none)
              (∃ r, And (decodeRuleTag L f tag (peelArgs as) = some r)
                        (stepConcl L r ≠ some f)))))) := by
  -- (1) el decisor falla ⇒ la cadena no decodifica
  have hnone : decodeChainAux [] (objList l) = none := by
    simp only [chainOkDec, decodeChain, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none]
      at hdec
    exact hdec
  -- (2) el FRONT-END da la PRIMERA línea mala
  obtain ⟨k, x, rs, L, hx, hd, hc, hline⟩ := decodeChainAux_none_first l [] hnone
  -- (3) `StdChain` da su FORMA
  obtain ⟨f, tag, as, hshape, hargs⟩ := hstd x (List.mem_of_getElem? hx)
  subst hshape
  -- (4) el corte regla-vs-conclusión
  exact ⟨k, f, tag, as, rs, L, hx, hargs, hd, hc, decodeLine_none_cases hline⟩


/-! ## §5 · 🏁 EL REPARTO — las RAMAS, y por qué son seis y no veintiuna

⭐⭐ **La sorpresa del reparto es que casi no depende del tag.** El `dispatcher` (§4) entrega
siempre la misma tupla, y cada causa consume esa tupla de **una** forma; lo único que cambia de
un tag a otro es **qué lema de la tabla se le pasa**, no la estructura de la rama.

| rama | qué le queda por tag |
|---|---|
| (a) `rama_tag_grande` | ⭐ **nada** — no menciona el tag |
| (b) `rama_aridad` | el `prf_lenc_*` que toque — los **21** están (§1ter) |
| (c′) `rama_concl` | el `TagCode` que toque — los **19** están (§1quater) |
| (d) `rama_thy` | ⭐ **nada** |
| (e) `mp`/`gen` | ⭐ **nada**: `derives_chainOk_neg_mp_major`/`_minor`/`_gen` (§2quinquies) **ya son** la rama |
| (f) `rama_tipo_*` | el refutador de `Meta/CodeDistinct.lean` que toque |

🔑 *El reparto no es un `case` de veintiuna ramas: es un `case` de seis, con una TABLA dentro.*
Y eso es exactamente lo que compró la inversión de `StdArgs` (§1ter): el análisis por tag se hace
**destruyendo**, no razonando.

⬜ **Lo que queda para ensamblar `DEUDA_chainNeg` entero**: el `match` sobre `tag` que elige rama
y pasa la entrada de la tabla. Las seis ramas ya no tienen incógnitas, y el split de 21 está
medido en **4,5 s** (ADR‑078). -/

/-! ### Las DICOTOMÍAS por FORMA — **los 21 tags sólo tienen SEIS formas de argumentos**

⭐⭐ Aquí es donde el reparto deja de escalar con el número de tags. `decodeRuleTag` distingue
veintiún tags, pero sus **listas de argumentos** sólo tienen seis formas:

| forma | tags |
|---|---|
| `[F]` | 8, 14, 16, 17, 18, 20 |
| `[T]` | 12 |
| `[F,F]` | 0, 2, 3, 4, 5, 6, 11, 19 |
| `[F,F,F]` | 1, 7 |
| `[F,T]` | 9, 10 |
| `[F,T,T]` | 13 |
| *(cualquiera)* | 15 — `thy`, que no mira los argumentos |

Y cada lema de abajo toma **como hipótesis** el hecho «con esta forma, el tag decodifica», que por
tag es un `rfl`. ⇒ **seis lemas, veintiuna instancias de una línea**, en vez de veintiún lemas.

🔑 *Cuando un `case` de N ramas se repite, mira si las ramas no serán M formas con N instancias.*
Es la misma jugada que ADR‑089 («seis ramas, no veintiuna») un nivel más abajo. -/

/-- Forma **[F]**: un argumento, de fórmula. -/
theorem dico_F {acc : List Formula} {f : Formula} {args : List Term} (k : Nat)
    (hsome : ∀ A : Formula, decodeRuleTag acc f k [formCode A] ≠ none)
    (hs : StdArgList args) (h : decodeRuleTag acc f k args = none) :
    Or (args.length ≠ 1) (∃ a, And (args = [a]) (∃ u, a = termCode u)) := by
  match args, hs with
  | [], _ => exact Or.inl (by decide)
  | [a], hs =>
      obtain ⟨ha, _⟩ := stdArgList_cons hs
      rcases ha with ⟨A, rfl⟩ | ⟨u, rfl⟩
      · exact absurd h (hsome A)
      · exact Or.inr ⟨_, rfl, ⟨u, rfl⟩⟩
  | _ :: _ :: _, _ => exact Or.inl (by simp)

/-- Forma **[T]**: un argumento, de término (tag 12). -/
theorem dico_T {acc : List Formula} {f : Formula} {args : List Term} (k : Nat)
    (hsome : ∀ t : Term, decodeRuleTag acc f k [termCode t] ≠ none)
    (hs : StdArgList args) (h : decodeRuleTag acc f k args = none) :
    Or (args.length ≠ 1) (∃ a, And (args = [a]) (∃ A, a = formCode A)) := by
  match args, hs with
  | [], _ => exact Or.inl (by decide)
  | [a], hs =>
      obtain ⟨ha, _⟩ := stdArgList_cons hs
      rcases ha with ⟨A, rfl⟩ | ⟨u, rfl⟩
      · exact Or.inr ⟨_, rfl, ⟨A, rfl⟩⟩
      · exact absurd h (hsome u)
  | _ :: _ :: _, _ => exact Or.inl (by simp)

/-- Forma **[F,F]**: ocho tags (0, 2, 3, 4, 5, 6, 11, 19). -/
theorem dico_FF {acc : List Formula} {f : Formula} {args : List Term} (k : Nat)
    (hsome : ∀ A B : Formula, decodeRuleTag acc f k [formCode A, formCode B] ≠ none)
    (hs : StdArgList args) (h : decodeRuleTag acc f k args = none) :
    Or (args.length ≠ 2)
       (∃ a b, And (args = [a, b])
         (Or (∃ u, a = termCode u) (∃ u, b = termCode u))) := by
  match args, hs with
  | [], _ => exact Or.inl (by decide)
  | [_], _ => exact Or.inl (by simp)
  | [a, b], hs =>
      obtain ⟨ha, hs'⟩ := stdArgList_cons hs
      obtain ⟨hb, _⟩ := stdArgList_cons hs'
      rcases ha with ⟨A, rfl⟩ | ⟨u, rfl⟩
      · rcases hb with ⟨B, rfl⟩ | ⟨u, rfl⟩
        · exact absurd h (hsome A B)
        · exact Or.inr ⟨_, _, rfl, Or.inr ⟨u, rfl⟩⟩
      · exact Or.inr ⟨_, _, rfl, Or.inl ⟨u, rfl⟩⟩
  | _ :: _ :: _ :: _, _ => exact Or.inl (by simp)

/-- Forma **[F,T]**: los dos tags de cuantificador con testigo (9, 10). -/
theorem dico_FT {acc : List Formula} {f : Formula} {args : List Term} (k : Nat)
    (hsome : ∀ (A : Formula) (t : Term),
      decodeRuleTag acc f k [formCode A, termCode t] ≠ none)
    (hs : StdArgList args) (h : decodeRuleTag acc f k args = none) :
    Or (args.length ≠ 2)
       (∃ a b, And (args = [a, b])
         (Or (∃ u, a = termCode u) (∃ B, b = formCode B))) := by
  match args, hs with
  | [], _ => exact Or.inl (by decide)
  | [_], _ => exact Or.inl (by simp)
  | [a, b], hs =>
      obtain ⟨ha, hs'⟩ := stdArgList_cons hs
      obtain ⟨hb, _⟩ := stdArgList_cons hs'
      rcases ha with ⟨A, rfl⟩ | ⟨u, rfl⟩
      · rcases hb with ⟨B, rfl⟩ | ⟨t, rfl⟩
        · exact Or.inr ⟨_, _, rfl, Or.inr ⟨B, rfl⟩⟩
        · exact absurd h (hsome A t)
      · exact Or.inr ⟨_, _, rfl, Or.inl ⟨u, rfl⟩⟩
  | _ :: _ :: _ :: _, _ => exact Or.inl (by simp)

/-! ### Las dos formas que faltaban, y los DIECIOCHO `decodes_*`

⭐⭐ **Y aquí sale el corte estructural del reparto.** El hecho «con la forma correcta, el tag
decodifica» es cierto para **dieciocho** tags y **FALSO para tres**: 15 (`thy`), 16 (`mp`) y
17 (`gen`) consultan el CONTEXTO (`findIdx` sobre `axioms` o sobre el acumulador), así que pueden
fallar con la forma perfecta.

⇒ **ésos tres son exactamente las causas (d) y (e)**, y los otros dieciocho son exactamente los
que pasan por las dicotomías hacia (b) y (f). El corte no se eligió: **lo dicta `decodeRuleTag`**.

🔑 *Un tag que consulta el contexto no puede refutarse por la FORMA; uno que no lo consulta, sí.* -/

/-- Forma **[F,F,F]**: tags 1 (`p2`) y 7 (`j3`). -/
theorem dico_FFF {acc : List Formula} {f : Formula} {args : List Term} (k : Nat)
    (hsome : ∀ A B C : Formula,
      decodeRuleTag acc f k [formCode A, formCode B, formCode C] ≠ none)
    (hs : StdArgList args) (h : decodeRuleTag acc f k args = none) :
    Or (args.length ≠ 3)
       (∃ a b c, And (args = [a, b, c])
         (Or (∃ u, a = termCode u) (Or (∃ u, b = termCode u) (∃ u, c = termCode u)))) := by
  match args, hs with
  | [], _ => exact Or.inl (by decide)
  | [_], _ => exact Or.inl (by simp)
  | [_, _], _ => exact Or.inl (by simp)
  | [a, b, c], hs =>
      obtain ⟨ha, hs1⟩ := stdArgList_cons hs
      obtain ⟨hb, hs2⟩ := stdArgList_cons hs1
      obtain ⟨hc, _⟩ := stdArgList_cons hs2
      rcases ha with ⟨A, rfl⟩ | ⟨u, rfl⟩
      · rcases hb with ⟨B, rfl⟩ | ⟨u, rfl⟩
        · rcases hc with ⟨C, rfl⟩ | ⟨u, rfl⟩
          · exact absurd h (hsome A B C)
          · exact Or.inr ⟨_, _, _, rfl, Or.inr (Or.inr ⟨u, rfl⟩)⟩
        · exact Or.inr ⟨_, _, _, rfl, Or.inr (Or.inl ⟨u, rfl⟩)⟩
      · exact Or.inr ⟨_, _, _, rfl, Or.inl ⟨u, rfl⟩⟩
  | _ :: _ :: _ :: _ :: _, _ => exact Or.inl (by simp)

/-- Forma **[F,T,T]**: tag 13 (`leibniz`), el único con dos testigos de término. -/
theorem dico_FTT {acc : List Formula} {f : Formula} {args : List Term} (k : Nat)
    (hsome : ∀ (A : Formula) (t1 t2 : Term),
      decodeRuleTag acc f k [formCode A, termCode t1, termCode t2] ≠ none)
    (hs : StdArgList args) (h : decodeRuleTag acc f k args = none) :
    Or (args.length ≠ 3)
       (∃ a b c, And (args = [a, b, c])
         (Or (∃ u, a = termCode u) (Or (∃ B, b = formCode B) (∃ B, c = formCode B)))) := by
  match args, hs with
  | [], _ => exact Or.inl (by decide)
  | [_], _ => exact Or.inl (by simp)
  | [_, _], _ => exact Or.inl (by simp)
  | [a, b, c], hs =>
      obtain ⟨ha, hs1⟩ := stdArgList_cons hs
      obtain ⟨hb, hs2⟩ := stdArgList_cons hs1
      obtain ⟨hc, _⟩ := stdArgList_cons hs2
      rcases ha with ⟨A, rfl⟩ | ⟨u, rfl⟩
      · rcases hb with ⟨B, rfl⟩ | ⟨t1, rfl⟩
        · exact Or.inr ⟨_, _, _, rfl, Or.inr (Or.inl ⟨B, rfl⟩)⟩
        · rcases hc with ⟨B, rfl⟩ | ⟨t2, rfl⟩
          · exact Or.inr ⟨_, _, _, rfl, Or.inr (Or.inr ⟨B, rfl⟩)⟩
          · exact absurd h (hsome A t1 t2)
      · exact Or.inr ⟨_, _, _, rfl, Or.inl ⟨u, rfl⟩⟩
  | _ :: _ :: _ :: _ :: _, _ => exact Or.inl (by simp)


/-! Los **dieciocho** `decodes_*`: cada uno es **una línea**.

⚠️ `decodeRuleTag_p1_some` y `_q1_some` (arriba) son la versión **fuerte** (`= some r`),
que se dejó como ejemplo trabajado; ésta es la débil (`≠ none`), que es la que las
dicotomías consumen y la que sale uniforme para los dieciocho. -/

section Decodes
variable (acc : List Formula) (f : Formula)
theorem decodes_efq (A : Formula) : decodeRuleTag acc f 8 [formCode A] ≠ none := by
  simp [decodeRuleTag, decodeForm_formCode]

theorem decodes_p3 (A : Formula) : decodeRuleTag acc f 14 [formCode A] ≠ none := by
  simp [decodeRuleTag, decodeForm_formCode]

theorem decodes_ind (A : Formula) : decodeRuleTag acc f 18 [formCode A] ≠ none := by
  simp [decodeRuleTag, decodeForm_formCode]

theorem decodes_listInd (A : Formula) : decodeRuleTag acc f 20 [formCode A] ≠ none := by
  simp [decodeRuleTag, decodeForm_formCode]

theorem decodes_eqrefl (t : Term) : decodeRuleTag acc f 12 [termCode t] ≠ none := by
  simp [decodeRuleTag, decodeTerm_termCode]

theorem decodes_p1 (A B : Formula) :
    decodeRuleTag acc f 0 [formCode A, formCode B] ≠ none := by
  simp [decodeRuleTag, decodeForm_formCode]

theorem decodes_c1 (A B : Formula) :
    decodeRuleTag acc f 2 [formCode A, formCode B] ≠ none := by
  simp [decodeRuleTag, decodeForm_formCode]

theorem decodes_c2 (A B : Formula) :
    decodeRuleTag acc f 3 [formCode A, formCode B] ≠ none := by
  simp [decodeRuleTag, decodeForm_formCode]

theorem decodes_c3 (A B : Formula) :
    decodeRuleTag acc f 4 [formCode A, formCode B] ≠ none := by
  simp [decodeRuleTag, decodeForm_formCode]

theorem decodes_j1 (A B : Formula) :
    decodeRuleTag acc f 5 [formCode A, formCode B] ≠ none := by
  simp [decodeRuleTag, decodeForm_formCode]

theorem decodes_j2 (A B : Formula) :
    decodeRuleTag acc f 6 [formCode A, formCode B] ≠ none := by
  simp [decodeRuleTag, decodeForm_formCode]

theorem decodes_q3 (A B : Formula) :
    decodeRuleTag acc f 11 [formCode A, formCode B] ≠ none := by
  simp [decodeRuleTag, decodeForm_formCode]

theorem decodes_qconf (A B : Formula) :
    decodeRuleTag acc f 19 [formCode A, formCode B] ≠ none := by
  simp [decodeRuleTag, decodeForm_formCode]

theorem decodes_p2 (A B C : Formula) :
    decodeRuleTag acc f 1 [formCode A, formCode B, formCode C] ≠ none := by
  simp [decodeRuleTag, decodeForm_formCode]

theorem decodes_j3 (A B C : Formula) :
    decodeRuleTag acc f 7 [formCode A, formCode B, formCode C] ≠ none := by
  simp [decodeRuleTag, decodeForm_formCode]

theorem decodes_q1 (A : Formula) (t : Term) :
    decodeRuleTag acc f 9 [formCode A, termCode t] ≠ none := by
  simp [decodeRuleTag, decodeForm_formCode, decodeTerm_termCode]

theorem decodes_q2 (A : Formula) (t : Term) :
    decodeRuleTag acc f 10 [formCode A, termCode t] ≠ none := by
  simp [decodeRuleTag, decodeForm_formCode, decodeTerm_termCode]

theorem decodes_leibniz (A : Formula) (t1 t2 : Term) :
    decodeRuleTag acc f 13 [formCode A, termCode t1, termCode t2] ≠ none := by
  simp [decodeRuleTag, decodeForm_formCode, decodeTerm_termCode]

end Decodes


/-- ⭐ **RAMA (a)**: el tag se sale de rango. **No depende del tag** y cierra sola. -/
theorem rama_tag_grande (l : List Term) (k tag : Nat) (f : Formula) (as : Term)
    (hk : l[k]? = some (cons (formCode f) (cons (numeralM tag) as)))
    (hbig : 20 < tag) :
    axioms ⊢ neg (chainOk nil (objList l)) :=
  derives_chainOk_neg_of_line l k _ hk (derives_lineWF_neg_of_tag_big (formCode f) as hbig)

/-- ⭐⭐ **RAMA (c′)**: la conclusión no casa. La forma es general; lo único por tag es el
`TagCode`, y los diecinueve están escritos.

⚠️ El `rw [hobj]` es lo que la inversión de `StdArgs` hace posible: convierte la `as` abstracta
que da `StdLine` en el `objList` que piden los cierres. -/
theorem rama_concl (l : List Term) (k tag : Nat) (f c : Formula) (as : Term)
    (hk : l[k]? = some (cons (formCode f) (cons (numeralM tag) as)))
    (hargs : StdArgs as)
    (htc : TagCode tag (peelArgs as) c) (hne : f ≠ c) :
    axioms ⊢ neg (chainOk nil (objList l)) := by
  have hobj : as = objList (peelArgs as) := stdArgs_objList hargs
  refine derives_chainOk_neg_of_line l k _ hk ?_
  rw [hobj]
  exact derives_lineWF_neg_of_concl htc hne

/-- ⭐ **RAMA (d)**: `thy` sin argumentos. -/
theorem rama_thy (l : List Term) (k : Nat) (f : Formula) (args : List Term) (L : List Formula)
    (hk : l[k]? = some (cons (formCode f) (cons (numeralM 15) nil)))
    (hnone : decodeRuleTag L f 15 args = none) :
    axioms ⊢ neg (chainOk nil (objList l)) :=
  derives_chainOk_neg_of_line l k _ hk (derives_lineWF_neg_thy_of_decode hnone)

/-- ⭐⭐ **RAMA (b)**: la aridad no casa. General sobre el tag; lo único por tag es el
`prf_lenc_*`, y los veintiuno están escritos. -/
theorem rama_aridad (l : List Term) (k tag n : Nat) (f : Formula) (args : List Term)
    (hk : l[k]? = some (cons (formCode f) (cons (numeralM tag) (objList args))))
    (himp : Prf (lineWF (objList (formCode f :: numeralM tag :: args)) ⇒
      ((Formula.eq (nthc (objList (formCode f :: numeralM tag :: args)) (succ zero))
          (numeralM tag)) ⇒
       (Formula.eq (lenc (objList (formCode f :: numeralM tag :: args))) (numeralM n)))))
    (hne : args.length + 2 ≠ n) :
    axioms ⊢ neg (chainOk nil (objList l)) := by
  refine derives_chainOk_neg_of_line l k _ hk ?_
  show axioms ⊢ neg (lineWF (objList (formCode f :: numeralM tag :: args)))
  exact derives_lineWF_neg_of_arity f tag n args himp hne

/-- ⭐ **RAMA (f)**: un código de TÉRMINO donde el tag espera uno de fórmula (`p1`, slot 0).
Es la plantilla; las demás ranuras cambian **sólo** el refutador de `Meta/CodeDistinct.lean`. -/
theorem rama_tipo_p1 (l : List Term) (k : Nat) (f : Formula) (u cB : Term)
    (hk : l[k]? = some (cons (formCode f) (cons (numeralM 0) (objList [termCode u, cB])))) :
    axioms ⊢ neg (chainOk nil (objList l)) :=
  derives_chainOk_neg_of_line l k _ hk (derives_lineWF_neg_p1_badtype f u cB)

/-- ⭐ **RAMA (f), la dirección contraria**: un código de FÓRMULA en un slot de término. -/
theorem rama_tipo_eqrefl (l : List Term) (k : Nat) (f A : Formula)
    (hk : l[k]? = some (cons (formCode f) (cons (numeralM 12) (objList [formCode A])))) :
    axioms ⊢ neg (chainOk nil (objList l)) :=
  derives_chainOk_neg_of_line l k _ hk (derives_lineWF_neg_eqrefl_badtype f A)


/-! ### 🏁 EL CIERRE DE UN TAG, DE PUNTA A PUNTA — la plantilla de los dieciocho

⭐⭐ `cierra_tag0` va de la **tupla que entrega `dispatcher`** hasta
`axioms ⊢ neg (chainOk nil ⟦l⟧)`, cubriendo **las tres causas que ese tag puede disparar**:
(b) aridad, (f) tipo y (c′) conclusión. Es el único sitio donde se ve la máquina entera
funcionando junta, y **mide el coste por tag en vez de estimarlo**.

⭐ Lo que hizo falta de NUEVO para cerrarlo entero fueron **dos lemas compartidos** —que el
decodificador RECHAZA el tipo equivocado— y **un refutador propio del tag**. Los dos primeros
sirven a los dieciocho; el tercero es lo único que se repite.

🔑 *El refutador de una ranura profunda se COMPONE del de la ranura de fuera, un nivel más
adentro* (`neg_p1_slot2` es `formCode_ne_implc_tc_1` bajo dos `cons_ne_tail`). Por eso (f) no
necesita un lema base por ranura: necesita un ENSAMBLAJE por tag. -/

/-- ⭐ El decodificador RECHAZA el tipo equivocado: `decodeForm` mira tags 2..9, `termCode` usa
    0/1. Gemelo, del lado del DECODIFICADOR, de `formCode_ne_termCode`. -/
theorem decodeForm_termCode (t : Term) : decodeForm (termCode t) = none := by
  cases t <;> simp [decodeForm, termCode, cons, ← numeralM_eq, decodeNat_numeralM]

theorem decodeTerm_formCode (A : Formula) : decodeTerm (formCode A) = none := by
  cases A <;> simp [decodeTerm, formCode, cons, ← numeralM_eq, decodeNat_numeralM]

/-- (f) para `p1` en el slot 2: el refutador se COMPONE del de slot 1, un nivel más adentro. -/
theorem neg_p1_slot2 (f : Formula) (a u : Term) :
    axioms ⊢ neg (formCode f =eq implc a (implc (termCode u) a)) := by
  cases f with
  | impl x y =>
      exact cons_ne_tail (cons_ne_tail (cons_ne_head (formCode_ne_implc_tc_1 y u a)))
  | _ => exact formCode_ne_cons_of_tag _ (n := 5) _ (by simp only [formTag]; decide)

/-- ⭐⭐⭐ **EL CIERRE DEL TAG 0**, desde la tupla que da `dispatcher`. -/
theorem cierra_tag0 (l : List Term) (k : Nat) (f : Formula) (as : Term) (L : List Formula)
    (hk : l[k]? = some (cons (formCode f) (cons (numeralM 0) as)))
    (hargs : StdArgs as)
    (hcase : Or (decodeRuleTag L f 0 (peelArgs as) = none)
                (∃ r, And (decodeRuleTag L f 0 (peelArgs as) = some r)
                          (stepConcl L r ≠ some f))) :
    axioms ⊢ neg (chainOk nil (objList l)) := by
  have hobj : as = objList (peelArgs as) := stdArgs_objList hargs
  have hsl : StdArgList (peelArgs as) := stdArgs_peel hargs
  rcases hcase with hnone | ⟨r, hr, hne⟩
  · -- (b) o (f)
    rcases dico_FF 0 (decodes_p1 L f) hsl hnone with hlen | ⟨a, b, heq, hbad⟩
    · -- (b) ARIDAD
      refine rama_aridad l k 0 4 f (peelArgs as) (by rw [← hobj]; exact hk) ?_ (by omega)
      exact prf_lenc_p1 _
    · -- (f) TIPO
      refine derives_chainOk_neg_of_line l k _ hk ?_
      rw [hobj, heq]
      rcases hbad with ⟨u, rfl⟩ | ⟨u, rfl⟩
      · exact derives_lineWF_neg_p1_badtype f u b
      · exact derives_lineWF_neg_of_tag 0 (formCode f) [a, termCode u] _ rfl
          (neg_p1_slot2 f a u)
  · -- (c′) LA CONCLUSIÓN NO CASA
    match hpa : peelArgs as, hsl with
    | [], _ => rw [hpa] at hr; simp [decodeRuleTag] at hr
    | [_], _ => rw [hpa] at hr; simp [decodeRuleTag] at hr
    | [a, b], hs =>
        obtain ⟨ha, hs'⟩ := stdArgList_cons hs
        obtain ⟨hb, _⟩ := stdArgList_cons hs'
        rcases ha with ⟨A, rfl⟩ | ⟨u, rfl⟩
        · rcases hb with ⟨B, rfl⟩ | ⟨u, rfl⟩
          · rw [hpa, decodeRuleTag_p1_some L f A B] at hr
            simp only [Option.some.injEq] at hr
            subst hr
            simp only [stepConcl, ne_eq, Option.some.injEq] at hne
            refine rama_concl l k 0 f (A ⇒ (B ⇒ A)) as hk hargs ?_ (fun h => hne h.symm)
            rw [hpa]; exact tc_p1 A B
          · rw [hpa] at hr; simp [decodeRuleTag, decodeForm_termCode] at hr
        · rw [hpa] at hr; simp [decodeRuleTag, decodeForm_termCode] at hr
    | _ :: _ :: _ :: _, _ => rw [hpa] at hr; simp [decodeRuleTag] at hr


end ROBINSON_PlusPlus.Meta.ChainNegPrf

/-! ## `export` — por CONSUMO: el módulo F (ensamblaje) necesita `deuda_inNeg` y el puente. -/
export ROBINSON_PlusPlus.Meta.ChainNegPrf (
  derives_lt_congr_right derives_lineWF_congr
  derives_chainOk_neg_of_line
  prf_boundedPremsIn_of_chainOk derives_chainOk_neg_of_prems derives_not_boundedCarcLt
  decodeChainAux_none_first decodeChainAux_carc_mem decodeLine_none_cases
  derives_lineWF_neg_thy_of_decode
  derives_neg_lor derives_not_boundedCarcLt_congr
  derives_not_boundedCarcLt_of_not_mem derives_not_boundedPremsIn_of_index
  derives_chainOk_neg_of_prem
  derives_not_boundedPremsIn_congr derives_chainOk_neg_of_prem_line
  prf_premsOf_mp_line prf_premsOf_gen_line prf_lenc_two prf_lenc_one prf_nthc_two_1
  derives_chainOk_neg_of_prem_code
  derives_chainOk_neg_mp_major derives_chainOk_neg_mp_minor derives_chainOk_neg_gen
  stdArgs_objList
  StdArgList peelArgs_objList stdArgs_peel stdArgList_objList stdArgList_cons
  decodeRuleTag_p1_some decodeRuleTag_q1_some tag0_none_dichotomy
  prf_lineTag_cons derives_lineWF_neg_of_tag_big
  derives_numeralM_ne derives_lineWF_neg_of_lenc_imp
  prf_lenc_tag_and prf_lenc_tag_plain prf_lenc_p1 prf_lenc_mp
  prf_lenc_p2 prf_lenc_c1 prf_lenc_c2 prf_lenc_c3 prf_lenc_j1 prf_lenc_j2 prf_lenc_j3
  prf_lenc_efq prf_lenc_q1 prf_lenc_q2 prf_lenc_q3 prf_lenc_eqrefl prf_lenc_leibniz prf_lenc_p3
  prf_lenc_thy prf_lenc_gen prf_lenc_ind prf_lenc_qconf prf_lenc_listInd
  derives_lineWF_neg_of_arity
  TagCode derives_neg_eq_of_code_ne derives_lineWF_neg_of_concl
  derives_lineWF_neg_p1_badtype derives_lineWF_neg_eqrefl_badtype
  tc_p1 tc_p2 tc_c1 tc_c2 tc_c3 tc_j1 tc_j2 tc_j3 tc_efq tc_eqrefl tc_p3 tc_gen tc_q1 tc_q2
  tc_leibniz tc_ind tc_listInd tc_q3 tc_qconf
  decodeLine_stepConcl decodeLine_carc decode_heads
  derives_not_In_congr deuda_inNeg
  dispatcher
  rama_tag_grande rama_concl rama_thy rama_aridad
  rama_tipo_p1 rama_tipo_eqrefl
  dico_F dico_T dico_FF dico_FT
  dico_FFF dico_FTT
  decodeForm_termCode decodeTerm_formCode neg_p1_slot2 cierra_tag0
  decodes_efq decodes_p3 decodes_ind decodes_listInd decodes_eqrefl decodes_p1 decodes_c1
  decodes_c2 decodes_c3 decodes_j1 decodes_j2 decodes_q3 decodes_qconf decodes_p2 decodes_j3
  decodes_q1 decodes_q2 decodes_leibniz
)

/-! ## FOOTPRINT -/
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.deuda_inNeg
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.dispatcher
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.rama_tag_grande
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.rama_concl
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.rama_aridad
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.rama_tipo_p1
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.dico_FF
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.dico_FT
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.dico_FFF
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.dico_FTT
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.decodes_leibniz
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.decodeForm_termCode
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.cierra_tag0
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.derives_chainOk_neg_of_line
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.prf_boundedPremsIn_of_chainOk
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.derives_chainOk_neg_of_prems
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.derives_not_boundedCarcLt
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.decodeChainAux_none_first
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.decodeChainAux_carc_mem
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.decodeLine_none_cases
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.derives_lineWF_neg_thy_of_decode
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.derives_not_boundedCarcLt_congr
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.derives_not_boundedCarcLt_of_not_mem
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.derives_not_boundedPremsIn_of_index
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.derives_chainOk_neg_of_prem
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.derives_not_boundedPremsIn_congr
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.derives_chainOk_neg_of_prem_line
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.prf_premsOf_mp_line
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.derives_chainOk_neg_of_prem_code
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.derives_chainOk_neg_mp_major
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.derives_chainOk_neg_gen
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.stdArgs_objList
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.stdArgs_peel
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.stdArgList_cons
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.tag0_none_dichotomy
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.derives_lineWF_neg_of_tag_big
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.derives_lineWF_neg_of_lenc_imp
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.prf_lenc_p1
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.prf_lenc_mp
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.prf_lenc_thy
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.prf_lenc_listInd
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.derives_lineWF_neg_of_arity
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.derives_lineWF_neg_of_concl
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.derives_lineWF_neg_p1_badtype
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.derives_lineWF_neg_eqrefl_badtype
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.tc_p1
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.tc_ind
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.tc_listInd
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.tc_qconf
