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

⚠️ **Nada de esto usa el ancla de codificación**: el footprint no cita `AnclaEq` ni
`ax_axiomsCodeT_eq`.

## ⬜ Lo que queda de `DEUDA_chainNeg`, medido

Con `StdChain` estrechada ([ADR‑022](../../DECISIONS.md)) toda línea es `⟨⌜f⌝, k̄, args⟩` con args
`formCode`/`termCode`, así que **las causas de rechazo del decodificador son cinco, y se pueden
enumerar**:

| # | por qué rechaza | ¿hay maquinaria? |
|---|---|---|
| (a) | **tag fuera de rango** (`k ≥ 21`) | 🔶 `prf_tagDisj_absurd` acota el tag por 20 |
| (b) | **aridad equivocada** | 🔶 los 21 `ax_lineWF_*` llevan `lenc = n̄`; es `gnum_ne` |
| (c) | **la conclusión no casa** (`stepConcl ≠ f`) | ✅ **`derives_lineWF_neg_of_tag`** + `formCode_ne` — es el grueso, y está |
| (d) | **`thy` con `f ∉ axioms`** | ✅ `derives_lineWF_neg_thy_of_not_prf` |
| (e) | **`mp`/`gen` sin premisas en el acumulador** | ⛔ **la única sin maquinaria**: no va por `lineWF` sino por el conjunto `premsOf ⊆ conclusiones anteriores` de `chainOk` |

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

end ROBINSON_PlusPlus.Meta.ChainNegPrf

/-! ## `export` — por CONSUMO: el módulo F (ensamblaje) necesita `deuda_inNeg` y el puente. -/
export ROBINSON_PlusPlus.Meta.ChainNegPrf (
  derives_lt_congr_right derives_lineWF_congr
  derives_chainOk_neg_of_line
  prf_boundedPremsIn_of_chainOk derives_chainOk_neg_of_prems derives_not_boundedCarcLt
  decodeChainAux_none_first decodeChainAux_carc_mem
  stdArgs_objList prf_lineTag_cons derives_lineWF_neg_of_tag_big
  derives_numeralM_ne derives_lineWF_neg_of_lenc_imp
  prf_lenc_tag_and prf_lenc_tag_plain prf_lenc_p1 prf_lenc_mp
  decodeLine_stepConcl decodeLine_carc decode_heads
  derives_not_In_congr deuda_inNeg
)

/-! ## FOOTPRINT -/
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.deuda_inNeg
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.derives_chainOk_neg_of_line
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.prf_boundedPremsIn_of_chainOk
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.derives_chainOk_neg_of_prems
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.derives_not_boundedCarcLt
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.decodeChainAux_none_first
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.decodeChainAux_carc_mem
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.stdArgs_objList
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.derives_lineWF_neg_of_tag_big
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.derives_lineWF_neg_of_lenc_imp
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.prf_lenc_p1
#print axioms ROBINSON_PlusPlus.Meta.ChainNegPrf.prf_lenc_mp
