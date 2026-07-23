/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.NatArithPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.NatArithPrf

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace ROBINSON_PlusPlus.Meta.NatOrderPrf

/-!
## META — NIVEL D real: ORDEN (`≤`) y asociatividad de `+` en `Prf`

Entregable **i‑a** de la ruta (1a) (`NEXT-STEPS.md`): la aritmética de orden existe hoy sólo a
nivel `⊢` (`Minimal/Theorems/Block3‑5`) y **no puede importarse** desde allí — no hay puente
`⊢ → Prf` (`Derives` tiene la ω‑regla; sólo existe `prf_to_derives`). Se re‑prueba en `Prf`, como
en su día se hizo con `Meta/ArithPrf.lean`.

**Destino:** monotonía del emparejamiento de Cantor ⟹ `sub‑código < código` ⟹ inducción fuerte
⟹ `pcc_eval_substfc` ⟹ los 7 tags de `lineWF` que faltan.

**Recordatorios del terreno** (`Minimal/Axioms.lean`):
* `add` recurre **por la derecha**: `a + 0 = a`, `a + σb = σ(a + b)`.
* `lt a b :⇔ ∃k. a + σk = b` (`ax13_lt_def`).
* `le a b := lt a b ∨ a =eq b` — **no es primitivo**: cada lema de `≤` arrastra el manejo de la
  disyunción interna.
-/

/-! ### Congruencias de `+` (vía Leibniz)

No existían: `ArithPrf` sólo tenía `prf_eq_congr_succ`/`_pred`. Mismo patrón (contexto de un
hueco + `prf_leibniz_subst`). -/

/-- Congruencia de `+` en el **primer** argumento. -/
theorem prf_eq_congr_add1 {t₁ t₂ : Term} (c : Term) (h : Prf (t₁ =eq t₂)) :
    Prf (add t₁ c =eq add t₂ c) := by
  let f : Formula := Formula.eq (add (liftTerm 0 t₁) (liftTerm 0 c)) (add (.var 0) (liftTerm 0 c))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (add t₁ c) (add s c) := by
    intro s
    simp only [f, substFormula, add, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ prf_leibniz_subst (A := f) h ((hS t₁) ▸ prf_refl (add t₁ c))

/-- Congruencia de `+` en el **segundo** argumento. -/
theorem prf_eq_congr_add2 {t₁ t₂ : Term} (c : Term) (h : Prf (t₁ =eq t₂)) :
    Prf (add c t₁ =eq add c t₂) := by
  let f : Formula := Formula.eq (add (liftTerm 0 c) (liftTerm 0 t₁)) (add (liftTerm 0 c) (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (add c t₁) (add c s) := by
    intro s
    simp only [f, substFormula, add, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ prf_leibniz_subst (A := f) h ((hS t₁) ▸ prf_refl (add c t₁))

/-- Congruencia de `+` en el segundo argumento, en contexto. -/
theorem PrfH_eq_congr_add2 {Γ : List Formula} {t₁ t₂ : Term} (c : Term)
    (h : PrfH Γ (t₁ =eq t₂)) : PrfH Γ (add c t₁ =eq add c t₂) := by
  let f : Formula := Formula.eq (add (liftTerm 0 c) (liftTerm 0 t₁)) (add (liftTerm 0 c) (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (add c t₁) (add c s) := by
    intro s
    simp only [f, substFormula, add, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ PrfH_leibniz_subst (A := f) h ((hS t₁) ▸ prf_to_prfH (prf_refl (add c t₁)) Γ)

/-! ### Asociatividad de `+`

⚠️ **CORRECCIÓN (2026‑07‑23).** La primera versión de este lema se probó **por inducción**, lo cual
era **trabajo innecesario**: `ax7_add_assoc` es un **axioma de la teoría** (está en la lista
`axioms`, `Minimal/Axioms.lean:1205`), igual que `ax6_add_comm`, y las leyes de `mul` (`ax8`–`ax12`).
Lo que hay que probar por inducción es sólo lo que **no** es axioma (p. ej. `0 + n = n`, porque
`add` recurre por la derecha). Se deja la instanciación directa. -/

/-- **Asociatividad de `+`** en `Prf` — instancia de `ax7_add_assoc`. -/
theorem prf_add_assoc (a b c : Term) :
    Prf (add (add a b) c =eq add a (add b c)) := by
  have hh := prf_spec (prf_spec (prf_spec
    (prf_ax (show ax7_add_assoc ∈ axioms by simp [axioms])) a) b) c
  simp [ax7_add_assoc, substFormula, substTerm, substTerms, add,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-- **Conmutatividad de `+`** en `Prf` — instancia de `ax6_add_comm`. -/
theorem prf_add_comm (a b : Term) : Prf (add a b =eq add b a) := by
  have hh := prf_spec (prf_spec
    (prf_ax (show ax6_add_comm ∈ axioms by simp [axioms])) a) b
  simp [ax6_add_comm, substFormula, substTerm, substTerms, add,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-! ### Introducción de `≤`

`le a b` **es** `lt a b ∨ a =eq b`, así que la introducción son las dos reglas de la disyunción
(`j1`/`j2`) y la reflexividad sale de la rama derecha. -/

/-- `a < b ⟹ a ≤ b`. -/
theorem prf_le_of_lt (a b : Term) : Prf (lt a b ⇒ le a b) :=
  Prf.incl (Prf₀.j1 (lt a b) (Formula.eq a b))

/-- `a = b ⟹ a ≤ b`. -/
theorem prf_le_of_eq (a b : Term) : Prf ((a =eq b) ⇒ le a b) :=
  Prf.incl (Prf₀.j2 (lt a b) (Formula.eq a b))

/-- **Reflexividad de `≤`**. -/
theorem prf_le_refl (a : Term) : Prf (le a a) :=
  prf_mp (prf_le_of_eq a a) (prf_refl a)

/-! ### `<` estricto contra `+`

`a < a + σk` es inmediato: el testigo de `∃k. a + σk = b` es el propio `k` y la ecuación es
reflexividad. Es la semilla de la monotonía de Cantor. -/

/-- **`a < a + σk`** — testigo directo. -/
theorem prf_lt_add_succ (a k : Term) : Prf (lt a (add a (succ k))) :=
  prf_lt_intro a (add a (succ k)) k (prf_refl _)

/-- Congruencia de `+` en el primer argumento, en contexto. -/
theorem PrfH_eq_congr_add1 {Γ : List Formula} {t₁ t₂ : Term} (c : Term)
    (h : PrfH Γ (t₁ =eq t₂)) : PrfH Γ (add t₁ c =eq add t₂ c) := by
  let f : Formula := Formula.eq (add (liftTerm 0 t₁) (liftTerm 0 c)) (add (.var 0) (liftTerm 0 c))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (add t₁ c) (add s c) := by
    intro s
    simp only [f, substFormula, add, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ PrfH_leibniz_subst (A := f) h ((hS t₁) ▸ prf_to_prfH (prf_refl (add t₁ c)) Γ)

/-- Sustitución en el primer argumento de `≤`, en contexto. -/
theorem PrfH_le_subst1 {Γ : List Formula} {a₁ a₂ b : Term} (h : PrfH Γ (a₁ =eq a₂))
    (hle : PrfH Γ (le a₁ b)) : PrfH Γ (le a₂ b) := by
  let f : Formula := le (.var 0) (liftTerm 0 b)
  have hS : ∀ s : Term, substFormula 0 s f = le s b := by
    intro s
    simp only [f, le, lt, lor, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS a₂) ▸ PrfH_leibniz_subst (A := f) h ((hS a₁) ▸ hle)

/-- Sustitución en el 1er argumento de `≤`, a nivel `Prf`. -/
theorem prf_le_subst1 {a₁ a₂ b : Term} (h : Prf (a₁ =eq a₂)) (hle : Prf (le a₁ b)) :
    Prf (le a₂ b) := by
  let f : Formula := le (.var 0) (liftTerm 0 b)
  have hS : ∀ s : Term, substFormula 0 s f = le s b := by
    intro s
    simp only [f, le, lt, lor, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS a₂) ▸ prf_leibniz_subst (A := f) h ((hS a₁) ▸ hle)

/-- Sustitución en el 2º argumento de `≤`, a nivel `Prf`. -/
theorem prf_le_subst2 {a b₁ b₂ : Term} (h : Prf (b₁ =eq b₂)) (hle : Prf (le a b₁)) :
    Prf (le a b₂) := by
  let f : Formula := le (liftTerm 0 a) (.var 0)
  have hS : ∀ s : Term, substFormula 0 s f = le a s := by
    intro s
    simp only [f, le, lt, lor, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b₂) ▸ prf_leibniz_subst (A := f) h ((hS b₁) ▸ hle)

/-- Sustitución en el segundo argumento de `≤`, en contexto. -/
theorem PrfH_le_subst2 {Γ : List Formula} {a b₁ b₂ : Term} (h : PrfH Γ (b₁ =eq b₂))
    (hle : PrfH Γ (le a b₁)) : PrfH Γ (le a b₂) := by
  let f : Formula := le (liftTerm 0 a) (.var 0)
  have hS : ∀ s : Term, substFormula 0 s f = le a s := by
    intro s
    simp only [f, le, lt, lor, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b₂) ▸ PrfH_leibniz_subst (A := f) h ((hS b₁) ▸ hle)

/-- Sustitución en el 1er argumento de `<`, en contexto. ⚠️ Copia local: el original vive en
    `Meta/BoundedInPrf.lean`, que es **posterior** a este módulo en la cadena de imports. -/
theorem PrfH_lt_subst1 {Γ : List Formula} {a₁ a₂ b : Term} (h : PrfH Γ (a₁ =eq a₂))
    (hlt : PrfH Γ (lt a₁ b)) : PrfH Γ (lt a₂ b) := by
  let f : Formula := lt (.var 0) (liftTerm 0 b)
  have hS : ∀ s : Term, substFormula 0 s f = lt s b := by
    intro s; simp only [f, lt, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS a₂) ▸ PrfH_leibniz_subst (A := f) h ((hS a₁) ▸ hlt)

/-- Sustitución en el 2º argumento de `<`, en contexto (misma nota que arriba). -/
theorem PrfH_lt_subst2 {Γ : List Formula} {a b₁ b₂ : Term} (h : PrfH Γ (b₁ =eq b₂))
    (hlt : PrfH Γ (lt a b₁)) : PrfH Γ (lt a b₂) := by
  let f : Formula := lt (liftTerm 0 a) (.var 0)
  have hS : ∀ s : Term, substFormula 0 s f = lt a s := by
    intro s; simp only [f, lt, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS b₂) ▸ PrfH_leibniz_subst (A := f) h ((hS b₁) ▸ hlt)

/-! ### Transitividad

⚠️ **Descomposición elegida.** La vía directa (eliminar los DOS `∃` de `lt a b` y `lt b c`)
obliga a anidar `PrfH_ex_elim`, que **levanta el contexto** (`Γ.map (liftFormula 0)`) y vuelve
las hipótesis inmanejables. En su lugar cada lema elimina **un solo** `∃`, y para eso la
transitividad se prueba primero **con los argumentos INTERCAMBIADOS** (`lt b c ⇒ (lt a b ⇒ …)`),
de modo que el `∃` a eliminar sea el del antecedente EXTERNO y valga `prf_ex_elim_imp` (que opera
sobre `Prf` cerrado). El orden usual se recupera al final permutando. -/

/-- `σk + σj = σ(k + σj)` — el reagrupamiento de testigos que pide la transitividad.
    (`σk + σj = σ(σk + j) = σ(σ(k+j))` y `σ(k + σj) = σ(σ(k+j))`.) -/
theorem prf_succ_add_succ (k j : Term) :
    Prf (add (succ k) (succ j) =eq succ (add k (succ j))) :=
  prf_eq_trans
    (prf_eq_trans (prf_add_succ_t (succ k) j) (prf_eq_congr_succ (prf_add_succ_left k j)))
    (prf_eq_symm (prf_eq_congr_succ (prf_add_succ_t k j)))

/-- **`a < b ⟹ a < b + σj`** (una sola eliminación de `∃`). Testigo: `k + σj`, usando
    `prf_succ_add_succ` y la asociatividad. -/
theorem prf_lt_add_succ_of_lt (a b j : Term) :
    Prf (lt a b ⇒ lt a (add b (succ j))) := by
  have himp : Prf (Formula.ex (Formula.eq (add (liftTerm 0 a) (succ (.var 0))) (liftTerm 0 b))
      ⇒ lt a (add b (succ j))) := by
    refine prf_ex_elim_imp ?_
    show PrfH [Formula.eq (add (liftTerm 0 a) (succ (.var 0))) (liftTerm 0 b)]
      (lt (liftTerm 0 a) (add (liftTerm 0 b) (succ (liftTerm 0 j))))
    refine PrfH_lt_intro (liftTerm 0 a) (add (liftTerm 0 b) (succ (liftTerm 0 j)))
      (add (.var 0) (succ (liftTerm 0 j))) ?_
    -- `↑a + σ(#0 + σ↑j) = ↑a + (σ#0 + σ↑j) = (↑a + σ#0) + σ↑j = ↑b + σ↑j`
    refine PrfH_eq_trans (prf_to_prfH (prf_eq_congr_add2 (liftTerm 0 a)
      (prf_eq_symm (prf_succ_add_succ (.var 0) (liftTerm 0 j)))) _) ?_
    refine PrfH_eq_trans (prf_to_prfH (prf_eq_symm
      (prf_add_assoc (liftTerm 0 a) (succ (.var 0)) (succ (liftTerm 0 j)))) _) ?_
    exact PrfH_eq_congr_add1 (succ (liftTerm 0 j))
      (prfH_hyp_self (Formula.eq (add (liftTerm 0 a) (succ (.var 0))) (liftTerm 0 b)))
  exact prf_deduction
    (PrfH.mp _ _ _ (prf_to_prfH himp _) (PrfH_iff_mp (prf_lt_iff a b) (prfH_hyp_self _)))

/-- **Transitividad de `<`, con los argumentos intercambiados** (forma en que sale con una sola
    eliminación de `∃`; ver la nota de la sección). -/
theorem prf_lt_trans_swap (a b c : Term) : Prf (lt b c ⇒ (lt a b ⇒ lt a c)) := by
  have himp : Prf (Formula.ex (Formula.eq (add (liftTerm 0 b) (succ (.var 0))) (liftTerm 0 c))
      ⇒ (lt a b ⇒ lt a c)) := by
    refine prf_ex_elim_imp ?_
    show PrfH [Formula.eq (add (liftTerm 0 b) (succ (.var 0))) (liftTerm 0 c)]
      (lt (liftTerm 0 a) (liftTerm 0 b) ⇒ lt (liftTerm 0 a) (liftTerm 0 c))
    refine deduction_aux ?_ (lt (liftTerm 0 a) (liftTerm 0 b)) _ rfl
    -- Γ = [lt ↑a ↑b, ↑b + σ#0 = ↑c] — hay que escribirlo: los `_` no lo infieren
    let Δ : List Formula := [lt (liftTerm 0 a) (liftTerm 0 b),
      Formula.eq (add (liftTerm 0 b) (succ (.var 0))) (liftTerm 0 c)]
    have hab : PrfH Δ (lt (liftTerm 0 a) (liftTerm 0 b)) := PrfH.hyp _ _ (List.Mem.head _)
    have heq : PrfH Δ (add (liftTerm 0 b) (succ (.var 0)) =eq liftTerm 0 c) :=
      PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
    have hstep : PrfH Δ (lt (liftTerm 0 a) (add (liftTerm 0 b) (succ (.var 0)))) :=
      PrfH.mp _ _ _ (prf_to_prfH (prf_lt_add_succ_of_lt (liftTerm 0 a) (liftTerm 0 b) (.var 0)) _)
        hab
    exact PrfH_lt_subst2 heq hstep
  exact prf_deduction
    (PrfH.mp _ _ _ (prf_to_prfH himp _) (PrfH_iff_mp (prf_lt_iff b c) (prfH_hyp_self _)))

/-- **Transitividad de `<`** en el orden usual. -/
theorem prf_lt_trans (a b c : Term) : Prf (lt a b ⇒ (lt b c ⇒ lt a c)) := by
  refine prf_deduction (deduction_aux ?_ (lt b c) [lt a b] rfl)
  exact PrfH.mp _ _ _
    (PrfH.mp _ _ _ (prf_to_prfH (prf_lt_trans_swap a b c) _) (PrfH.hyp _ _ (List.Mem.head _)))
    (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))

/-! ### Transitividad mixta y de `≤`

`le` es una disyunción, así que cada lema hace `PrfH_or_elim` sobre ella: la rama `<` usa la
transitividad estricta y la rama `=` reescribe con Leibniz. -/

/-- **`a < b ⟹ b ≤ c ⟹ a < c`**. -/
theorem prf_lt_le_trans (a b c : Term) : Prf (lt a b ⇒ (le b c ⇒ lt a c)) := by
  refine prf_deduction (deduction_aux ?_ (le b c) [lt a b] rfl)
  have hle : PrfH [le b c, lt a b] (lor (lt b c) (Formula.eq b c)) := PrfH.hyp _ _ (List.Mem.head _)
  -- tras `or_elim` el contexto es `X :: [le b c, lt a b]`, luego `lt a b` está a distancia 2
  refine PrfH_or_elim hle ?_ ?_
  · exact PrfH.mp _ _ _
      (PrfH.mp _ _ _ (prf_to_prfH (prf_lt_trans a b c) _)
        (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
      (PrfH.hyp _ _ (List.Mem.head _))
  · exact PrfH_lt_subst2 (PrfH.hyp _ _ (List.Mem.head _))
      (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

/-- **`a ≤ b ⟹ b < c ⟹ a < c`**. -/
theorem prf_le_lt_trans (a b c : Term) : Prf (le a b ⇒ (lt b c ⇒ lt a c)) := by
  refine prf_deduction (deduction_aux ?_ (lt b c) [le a b] rfl)
  have hle : PrfH [lt b c, le a b] (lor (lt a b) (Formula.eq a b)) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  refine PrfH_or_elim hle ?_ ?_
  · exact PrfH.mp _ _ _
      (PrfH.mp _ _ _ (prf_to_prfH (prf_lt_trans a b c) _) (PrfH.hyp _ _ (List.Mem.head _)))
      (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
  · exact PrfH_lt_subst1 (PrfH_eq_symm (PrfH.hyp _ _ (List.Mem.head _)))
      (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))

/-- **Transitividad de `≤`**. -/
theorem prf_le_trans (a b c : Term) : Prf (le a b ⇒ (le b c ⇒ le a c)) := by
  refine prf_deduction (deduction_aux ?_ (le b c) [le a b] rfl)
  have hab : PrfH [le b c, le a b] (lor (lt a b) (Formula.eq a b)) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  refine PrfH_or_elim hab ?_ ?_
  · -- rama `a < b`: con `b ≤ c` da `a < c`, luego `a ≤ c`
    have h1 : PrfH (lt a b :: [le b c, le a b]) (lt a c) :=
      PrfH.mp _ _ _
        (PrfH.mp _ _ _ (prf_to_prfH (prf_lt_le_trans a b c) _) (PrfH.hyp _ _ (List.Mem.head _)))
        (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
    exact PrfH.mp _ _ _ (prf_to_prfH (prf_le_of_lt a c) _) h1
  · -- rama `a = b`: reescribe `b ≤ c` a `a ≤ c`
    exact PrfH_le_subst1 (PrfH_eq_symm (PrfH.hyp _ _ (List.Mem.head _)))
      (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))

end ROBINSON_PlusPlus.Meta.NatOrderPrf

export ROBINSON_PlusPlus.Meta.NatOrderPrf (
  prf_eq_congr_add1 prf_eq_congr_add2 PrfH_eq_congr_add2
  prf_add_assoc prf_add_comm
  PrfH_eq_congr_add1 PrfH_le_subst1 PrfH_le_subst2 prf_le_subst1 prf_le_subst2 PrfH_lt_subst1 PrfH_lt_subst2
  prf_le_of_lt prf_le_of_eq prf_le_refl
  prf_lt_add_succ prf_succ_add_succ prf_lt_add_succ_of_lt
  prf_lt_trans_swap prf_lt_trans prf_lt_le_trans prf_le_lt_trans prf_le_trans
)
