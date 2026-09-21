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
| (c) | **la conclusión no casa** (`stepConcl ≠ f`) | ✅ **`derives_lineWF_neg_of_tag`** + `formCode_ne` — es el grueso, y está |
| (d) | **`thy` con `f ∉ axioms`** | 🏁 **CERRADA 2026‑09‑21**, `derives_lineWF_neg_thy_of_decode` — la ✅ anterior era **falsa** (ver 3 abajo) |
| (e) | **`mp`/`gen` sin premisas en el acumulador** | 🏁 **CERRADA 2026‑09‑21** (§2quater, `derives_chainOk_neg_of_prem`) — no va por `lineWF` sino por `premsOf ⊆ conclusiones anteriores`. ⬜ falta sólo el **transporte** a `mp`/`gen` |

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
  stdArgs_objList prf_lineTag_cons derives_lineWF_neg_of_tag_big
  derives_numeralM_ne derives_lineWF_neg_of_lenc_imp
  prf_lenc_tag_and prf_lenc_tag_plain prf_lenc_p1 prf_lenc_mp
  prf_lenc_p2 prf_lenc_c1 prf_lenc_c2 prf_lenc_c3 prf_lenc_j1 prf_lenc_j2 prf_lenc_j3
  prf_lenc_efq prf_lenc_q1 prf_lenc_q2 prf_lenc_q3 prf_lenc_eqrefl prf_lenc_leibniz prf_lenc_p3
  prf_lenc_thy prf_lenc_gen prf_lenc_ind prf_lenc_qconf prf_lenc_listInd
  derives_lineWF_neg_of_arity
  decodeLine_stepConcl decodeLine_carc decode_heads
  derives_not_In_congr deuda_inNeg
  dispatcher
)

/-! ## FOOTPRINT -/
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.deuda_inNeg
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.dispatcher
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
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.stdArgs_objList
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.derives_lineWF_neg_of_tag_big
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.derives_lineWF_neg_of_lenc_imp
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.prf_lenc_p1
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.prf_lenc_mp
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.prf_lenc_thy
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.prf_lenc_listInd
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.derives_lineWF_neg_of_arity
