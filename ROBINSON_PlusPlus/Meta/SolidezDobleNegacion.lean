/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.SolidezPrf
import ROBINSON_PlusPlus.Meta.ModeloCodigo

/-!
# `Meta/SolidezDobleNegacion.lean` — la solidez de `Prf` SIN lógica clásica: la semántica doble‑negada (ADR‑191)

`prf_sound` (`Meta/SolidezPrf.lean`) lee las fórmulas en `Prop` con `evalFormula`, y la regla `p3` (¬¬A ⇒ A) pide
entonces `Classical.byContradiction`: era el `Classical.choice` de los titulares de las clases (ii) y (iii) (T61,
ADR‑189). Aquí se leen por la traducción de Gödel–Gentzen, `gg`: los átomos y la igualdad, doblemente negados; `∨` y
`∃`, por sus duales negativos; lo demás, igual. Toda `evalFormula M v (gg φ)` es ESTABLE (`gg_estable`: de su doble
negación se sigue), y con eso `p3` —y todo `Prf`— es sólido sin lógica clásica (`prf_sound_dn`).

* **§1 · `gg`**, y que conmuta con la sustitución y el lift (`gg_subst`, `gg_lift`).
* **§2 · La estabilidad** (`gg_estable`), por inducción sobre la fórmula.
* **§3 · La solidez**: `EstandarDN M` —`0`, `σ` y `::` estándar, y los 120 verdaderos LEÍDOS POR `gg`—, y
  `prfI_sound_dn`, `prf_sound_dn`, `consistentH_dn`. Es `prf_sound` caso por caso, con `gg_estable` donde aquél usaba
  la lógica clásica (`p3`) o la forma positiva de `∨`/`∃` (`j3`, `q3`, `leibniz`).
* **§4 · De la lectura clásica a la doble‑negada** (`transfer`), según la POLARIDAD que calcula `clas`: `P` (de `φ` a
  `gg φ`), `N` (de `gg φ` a `¬¬φ`) y `S` (de `gg φ` a `φ`). Sólo `S` pide algo del modelo: que los átomos que caen en
  su posición, y las disyunciones que decide, sean decidibles; `∃` en posición `S` no pasa nunca (sería Markov).
* **§5 · Los 120**: pasan con `P` pidiendo decidible sólo `∈` de aridad 2 (`axiomas_clas`, comprobado por el núcleo;
  sin decidibilidad no pasan siete: los `lineWF` de la sustitución, por las guardas). En todo modelo estándar `∈` es
  el de verdad (`M_mem`, bajado aquí de `Meta/RigidezEstandar.lean`), así que `estandarDN_de : Estandar M →
  EstandarDN M`, y `consistentH_de` —el de `SolidezPrf`, con el mismo enunciado— ya no pasa por `p3` en `Prop`.

`prf_sound` se queda, con su `Classical.choice`: su enunciado es la solidez para la lectura en `Prop`, y ésa pide la
lógica clásica (daría el tercio excluso de toda fórmula aritmética).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSimpArgs false

-- ⚠️ `open` acotado: con `Minimal.Axioms` abierto, `∧`, `∨` y `∈` resuelven a los símbolos OBJETO (`land`, `lor`,
-- `In`); aquí se abre sólo en las secciones que lo necesitan, y se escribe `And`, `Or` y `List.Mem`.
open FOL FOL.Metamath.Semantics

namespace ROBINSON_PlusPlus.Meta.SolidezDobleNegacion

/-! ## §1 · La traducción de Gödel–Gentzen -/

/-- **`gg`**: los átomos y la igualdad, doblemente negados; `A ∨ B` como `¬(¬A ∧ ¬B)`; `∃A` como `¬∀¬A`; lo demás,
    igual. -/
def gg : Formula → Formula
  | .bottom => .bottom
  | .atom p ts => neg (neg (.atom p ts))
  | .eq t u => neg (neg (.eq t u))
  | .impl A B => .impl (gg A) (gg B)
  | .forall A => .forall (gg A)
  | .and A B => .and (gg A) (gg B)
  | .or A B => neg (.and (neg (gg A)) (neg (gg B)))
  | .ex A => neg (.forall (neg (gg A)))

theorem gg_subst : ∀ (φ : Formula) (k : Nat) (t : Term), gg (substFormula k t φ) = substFormula k t (gg φ)
  | .bottom, _, _ => rfl
  | .atom _ _, _, _ => rfl
  | .eq _ _, _, _ => rfl
  | .impl A B, k, t => by show Formula.impl (gg (substFormula k t A)) (gg (substFormula k t B)) = _; rw [gg_subst A k t, gg_subst B k t]; rfl
  | .forall A, k, t => congrArg Formula.forall (gg_subst A (k + 1) (liftTerm 0 t))
  | .and A B, k, t => by show Formula.and (gg (substFormula k t A)) (gg (substFormula k t B)) = _; rw [gg_subst A k t, gg_subst B k t]; rfl
  | .or A B, k, t => by
      show neg (Formula.and (neg (gg (substFormula k t A))) (neg (gg (substFormula k t B)))) = _
      rw [gg_subst A k t, gg_subst B k t]; rfl
  | .ex A, k, t => by
      show neg (Formula.forall (neg (gg (substFormula (k + 1) (liftTerm 0 t) A)))) = _
      rw [gg_subst A (k + 1) (liftTerm 0 t)]; rfl

theorem gg_lift : ∀ (φ : Formula) (c : Nat), gg (liftFormula c φ) = liftFormula c (gg φ)
  | .bottom, _ => rfl
  | .atom _ _, _ => rfl
  | .eq _ _, _ => rfl
  | .impl A B, c => by show Formula.impl (gg (liftFormula c A)) (gg (liftFormula c B)) = _; rw [gg_lift A c, gg_lift B c]; rfl
  | .forall A, c => congrArg Formula.forall (gg_lift A (c + 1))
  | .and A B, c => by show Formula.and (gg (liftFormula c A)) (gg (liftFormula c B)) = _; rw [gg_lift A c, gg_lift B c]; rfl
  | .or A B, c => by
      show neg (Formula.and (neg (gg (liftFormula c A))) (neg (gg (liftFormula c B)))) = _
      rw [gg_lift A c, gg_lift B c]; rfl
  | .ex A, c => by
      show neg (Formula.forall (neg (gg (liftFormula (c + 1) A)))) = _
      rw [gg_lift A (c + 1)]; rfl

/-! ## §2 · Toda fórmula traducida es ESTABLE -/

theorem gg_estable {D : Type} (M : Model D) : ∀ (φ : Formula) (v : Nat → D),
    ¬¬ evalFormula M v (gg φ) → evalFormula M v (gg φ)
  | .bottom, _, h => h id
  | .atom _ _, _, h => fun hn => h (fun hh => hh hn)
  | .eq _ _, _, h => fun hn => h (fun hh => hh hn)
  | .impl _ B, v, h => fun hA => gg_estable M B v (fun hnB => h (fun hAB => hnB (hAB hA)))
  | .forall A, v, h => fun d => gg_estable M A (shiftEnv v d) (fun hn => h (fun hall => hn (hall d)))
  | .and A B, v, h =>
      ⟨gg_estable M A v (fun hn => h (fun hab => hn hab.1)), gg_estable M B v (fun hn => h (fun hab => hn hab.2))⟩
  | .or _ _, _, h => fun hab => h (fun hn => hn hab)
  | .ex _, _, h => fun hab => h (fun hn => hn hab)

/-! ## §3 · La solidez doble‑negada -/

section Solidez
open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.SolidezPrf

theorem gg_ind (A : Formula) :
    gg (ROBINSON_PlusPlus.Full.inductionFormula A) = ROBINSON_PlusPlus.Full.inductionFormula (gg A) := by
  simp only [ROBINSON_PlusPlus.Full.inductionFormula, gg, gg_subst, gg_lift]

theorem gg_qconf (P C : Formula) : gg (confinementFormula P C) = confinementFormula (gg P) (gg C) := by
  simp only [confinementFormula, gg, gg_lift]

theorem gg_listInd (A : Formula) : gg (listInductionFormula A) = listInductionFormula (gg A) := by
  simp only [listInductionFormula, gg, gg_subst, gg_lift]

/-- Un modelo estándar de la lectura doble‑negada: `0`, `σ` y `::` los de verdad, y los 120 verdaderos por `gg`. -/
structure EstandarDN (M : Model Nat) : Prop where
  hzero : M.func zero_sym [] = 0
  hsucc : ∀ a, M.func succ_sym [a] = a + 1
  hcons : ∀ a b, M.func cons_sym [a, b] = consN a b
  haxs  : ∀ (v : Nat → Nat) (a : Formula), List.Mem a axioms → evalFormula M v (gg a)

variable {M : Model Nat}

theorem prfI_sound_dn (hM : EstandarDN M) {φ : Formula} (h : Prfᵢ φ) : ∀ v, evalFormula M v (gg φ) := by
  induction h with
  | p1 A B => intro v hA _; exact hA
  | p2 A B C => intro v hABC hAB hA; exact hABC hA (hAB hA)
  | c1 A B => intro v hA hB; exact ⟨hA, hB⟩
  | c2 A B => intro v hAB; exact hAB.left
  | c3 A B => intro v hAB; exact hAB.right
  | j1 A B => intro v hA h; exact h.1 hA
  | j2 A B => intro v hB h; exact h.2 hB
  | j3 A B C =>
      intro v hAB hAC hBC
      exact gg_estable M C v (fun hnC => hAB ⟨fun hA => hnC (hAC hA), fun hB => hnC (hBC hB)⟩)
  | efq A => intro v hb; exact False.elim hb
  | q1 A t =>
      intro v hall
      show evalFormula M v (gg (substFormula 0 t A))
      rw [gg_subst]
      exact (eval_substFormula_zero M v t (gg A)).mpr (hall _)
  | q2 A t =>
      intro v hs hall
      have hs' : evalFormula M v (substFormula 0 t (gg A)) := by rw [← gg_subst]; exact hs
      exact hall _ ((eval_substFormula_zero M v t (gg A)).mp hs')
  | q3 A B =>
      intro v hall hex
      refine gg_estable M B v (fun hnB => hex (fun d hd => hnB ?_))
      have h1 : evalFormula M (shiftEnv v d) (gg (liftFormula 0 B)) := hall d hd
      rw [gg_lift] at h1
      exact (eval_liftFormula_zero M v d (gg B)).mp h1
  | eqrefl t => intro v hn; exact hn rfl
  | leibniz A t₁ t₂ =>
      intro v he hs
      refine gg_estable M (substFormula 0 t₂ A) v (fun hn => he (fun heq => hn ?_))
      have h1 : evalFormula M v (substFormula 0 t₁ (gg A)) := by rw [← gg_subst]; exact hs
      have h2 := (eval_substFormula_zero M v t₁ (gg A)).mp h1
      have heq' : evalTerm M v t₁ = evalTerm M v t₂ := heq
      rw [heq'] at h2
      rw [gg_subst]
      exact (eval_substFormula_zero M v t₂ (gg A)).mpr h2
  | thy a ha => intro v; exact hM.haxs v a ha
  | mp A B _ _ ih1 ih2 => intro v; exact ih1 v (ih2 v)
  | gen A _ ih => intro v d; exact ih (shiftEnv v d)

/-- 🏁 **`Prf` es sólido para la lectura doble‑negada, sin lógica clásica**: `p3` es `gg_estable`; `ind`, `qconf` y
    `listInd`, los casos de `prf_sound` con `gg A` en lugar de `A`. -/
theorem prf_sound_dn (hM : EstandarDN M) {φ : Formula} (h : Prf φ) : ∀ v, evalFormula M v (gg φ) := by
  induction h with
  | incl h0 => exact prfI_sound_dn hM h0
  | p3 A => intro v hnn; exact gg_estable M A v hnn
  | ind A =>
      intro v
      rw [gg_ind]
      simp only [ROBINSON_PlusPlus.Full.inductionFormula, evalFormula]
      intro h0 hst d
      have hz : evalTerm M v zero = 0 := by simp [zero, evalTerm, evalTerms, hM.hzero]
      have h0' : evalFormula M (shiftEnv v 0) (gg A) := by
        have := (eval_substFormula_zero M v zero (gg A)).mp h0; rwa [hz] at this
      induction d with
      | zero => exact h0'
      | succ n ih =>
          have hs := hst n ih
          have hsu : evalTerm M (shiftEnv v n) (succ (.var 0)) = n + 1 := by
            simp [succ, evalTerm, evalTerms, shiftEnv, hM.hsucc]
          rw [eval_substFormula_zero, hsu, env1, eval_liftFormula_ext] at hs
          exact hs
  | qconf P C =>
      intro v
      rw [gg_qconf]
      simp only [confinementFormula, evalFormula]
      intro hall hP d
      exact hall d ((eval_liftFormula_zero M v d (gg P)).mpr hP)
  | listInd A =>
      intro v
      rw [gg_listInd]
      simp only [listInductionFormula, evalFormula]
      intro h0 hst
      have hn : evalTerm M v nil = 0 := by simp [nil, zero, evalTerm, evalTerms, hM.hzero]
      have h0' : evalFormula M (shiftEnv v 0) (gg A) := by
        have := (eval_substFormula_zero M v nil (gg A)).mp h0; rwa [hn] at this
      refine fuerte (fun n => evalFormula M (shiftEnv v n) (gg A)) ?_
      intro n ih
      rcases n with _ | m
      · exact h0'
      · obtain ⟨x, y, hxy, _, hy⟩ := descompone m
        have hant : evalFormula M (shiftEnv (shiftEnv v x) y) (liftFormula 1 (gg A)) := by
          rw [env1, eval_liftFormula_ext]; exact ih y hy
        have hs := hst x y hant
        have hc : evalTerm M (shiftEnv (shiftEnv v x) y) (cons (.var 1) (.var 0)) = consN x y := by
          simp [cons, evalTerm, evalTerms, shiftEnv, hM.hcons]
        rw [eval_substFormula_zero, hc, hxy, env2, eval_liftFormula_ext, env1,
          eval_liftFormula_ext] at hs
        exact hs
  | mp A B _ _ ih1 ih2 => intro v; exact ih1 v (ih2 v)
  | gen A _ ih => intro v d; exact ih (shiftEnv v d)

/-- `ConsistentH` de un modelo estándar de la lectura doble‑negada: `gg ⊥ = ⊥`. -/
theorem consistentH_dn (hM : EstandarDN M) : ConsistentH :=
  fun h => prf_sound_dn hM h (fun _ => 0)

end Solidez

/-! ## §4 · De la lectura clásica a la doble‑negada, por la POLARIDAD

`clas D φ = (P, N, S)`: `P` si `φ ⇒ gg φ` vale sin más; `N` si `gg φ ⇒ ¬¬φ`; `S` si `gg φ ⇒ φ`. `D p n` dice qué
símbolos de relación, con aridad `n`, son decidibles en el modelo; la igualdad lo es siempre (el dominio es `Nat`).
Se calculan juntas, en una pasada (un `match` sobre el par), para que el núcleo no recalcule. -/

variable {M : Model Nat}

/-- Sin cuantificadores, y con todos sus átomos decidibles. -/
def qfD (D : List Char → Nat → Bool) : Formula → Bool
  | .bottom => true
  | .atom p ts => D p ts.length
  | .eq _ _ => true
  | .impl A B => qfD D A && qfD D B
  | .forall _ => false
  | .and A B => qfD D A && qfD D B
  | .or A B => qfD D A && qfD D B
  | .ex _ => false

/-- La polaridad `(P, N, S)`. `N (∀A)` pide `S A` (si no, sería el desplazamiento de la doble negación); `S (A ∨ B)`
    decide uno de los dos lados; `S (∃A)` no vale nunca. -/
def clas (D : List Char → Nat → Bool) : Formula → Bool × Bool × Bool
  | .bottom => (true, true, true)
  | .atom p ts => (true, true, D p ts.length)
  | .eq _ _ => (true, true, true)
  | .impl A B =>
      match clas D A, clas D B with
      | (pa, na, _), (pb, nb, sb) => (na && pb, pa && nb, pa && sb)
  | .forall A =>
      match clas D A with
      | (pa, _, sa) => (pa, sa, sa)
  | .and A B =>
      match clas D A, clas D B with
      | (pa, na, sa), (pb, nb, sb) => (pa && pb, na && nb, sa && sb)
  | .or A B =>
      match clas D A, clas D B with
      | (pa, na, sa), (pb, nb, sb) => (pa && pb, na && nb, (qfD D A && na && sb) || (qfD D B && nb && sa))
  | .ex A =>
      match clas D A with
      | (pa, na, _) => (pa, na, false)

theorem evalTerms_length {D : Type} (M' : Model D) (v : Nat → D) :
    ∀ ts : List Term, (evalTerms M' v ts).length = ts.length
  | [] => rfl
  | _ :: r => congrArg Nat.succ (evalTerms_length M' v r)

/-- Una fórmula sin cuantificadores y con átomos decidibles es DECIDIBLE en el modelo. -/
def decQF (D : List Char → Nat → Bool)
    (hD : ∀ (p : List Char) (args : List Nat), D p args.length = true → Decidable (M.rel p args)) :
    ∀ (φ : Formula), qfD D φ = true → ∀ v : Nat → Nat, Decidable (evalFormula M v φ)
  | .bottom, _, _ => isFalse id
  | .atom p ts, h, v => hD p (evalTerms M v ts) (by rw [evalTerms_length]; exact h)
  | .eq t u, _, v => Nat.decEq (evalTerm M v t) (evalTerm M v u)
  | .impl A B, h, v =>
      have h' : And (qfD D A = true) (qfD D B = true) := by simpa only [qfD, Bool.and_eq_true] using h
      match decQF D hD A h'.1 v, decQF D hD B h'.2 v with
      | _, isTrue hb => isTrue (fun _ => hb)
      | isFalse ha, _ => isTrue (fun a => absurd a ha)
      | isTrue ha, isFalse hb => isFalse (fun f => hb (f ha))
  | .forall _, h, _ => absurd h (by simp only [qfD]; decide)
  | .and A B, h, v =>
      have h' : And (qfD D A = true) (qfD D B = true) := by simpa only [qfD, Bool.and_eq_true] using h
      match decQF D hD A h'.1 v, decQF D hD B h'.2 v with
      | isTrue ha, isTrue hb => isTrue ⟨ha, hb⟩
      | isFalse ha, _ => isFalse (fun hab => ha hab.1)
      | _, isFalse hb => isFalse (fun hab => hb hab.2)
  | .or A B, h, v =>
      have h' : And (qfD D A = true) (qfD D B = true) := by simpa only [qfD, Bool.and_eq_true] using h
      match decQF D hD A h'.1 v, decQF D hD B h'.2 v with
      | isTrue ha, _ => isTrue (Or.inl ha)
      | _, isTrue hb => isTrue (Or.inr hb)
      | isFalse ha, isFalse hb => isFalse (fun hab => hab.elim ha hb)
  | .ex _, h, _ => absurd h (by simp only [qfD]; decide)

/-- 🏁 **El paso de la lectura clásica a la doble‑negada**, según la polaridad. Sin lógica clásica: lo único que se
    decide son los átomos `D` y las disyunciones sin cuantificadores que `S` necesita. -/
theorem transfer (D : List Char → Nat → Bool)
    (hD : ∀ (p : List Char) (args : List Nat), D p args.length = true → Decidable (M.rel p args)) :
    ∀ (φ : Formula) (v : Nat → Nat),
      And ((clas D φ).1 = true → evalFormula M v φ → evalFormula M v (gg φ))
        (And ((clas D φ).2.1 = true → evalFormula M v (gg φ) → ¬¬ evalFormula M v φ)
          ((clas D φ).2.2 = true → evalFormula M v (gg φ) → evalFormula M v φ))
  | .bottom, _ => ⟨fun _ h => h, fun _ h _ => h, fun _ h => h⟩
  | .atom p ts, v => by
      refine ⟨fun _ h hn => hn h, fun _ h => h, fun hS h => ?_⟩
      have hd : Decidable (M.rel p (evalTerms M v ts)) :=
        hD p (evalTerms M v ts) (by rw [evalTerms_length]; exact hS)
      exact match hd with
        | isTrue ha => ha
        | isFalse hna => (h hna).elim
  | .eq t u, v => by
      refine ⟨fun _ h hn => hn h, fun _ h => h, fun _ h => ?_⟩
      exact match Nat.decEq (evalTerm M v t) (evalTerm M v u) with
        | isTrue ha => ha
        | isFalse hna => (h hna).elim
  | .impl A B, v => by
      obtain ⟨PA, NA, SA⟩ := transfer D hD A v
      obtain ⟨PB, NB, SB⟩ := transfer D hD B v
      refine ⟨fun hc hAB hA' => ?_, fun hc h hn => ?_, fun hc h hA => ?_⟩
      · have hc' : And ((clas D A).2.1 = true) ((clas D B).1 = true) := by
          simpa only [clas, Bool.and_eq_true] using hc
        have hnnA := NA hc'.1 hA'
        exact gg_estable M B v (fun hnB' => hnnA (fun hA => hnB' (PB hc'.2 (hAB hA))))
      · have hc' : And ((clas D A).1 = true) ((clas D B).2.1 = true) := by
          simpa only [clas, Bool.and_eq_true] using hc
        have hnB : ¬ evalFormula M v B := fun hB => hn (fun _ => hB)
        have hnnA : ¬¬ evalFormula M v A := fun hnA => hn (fun hA => absurd hA hnA)
        have hA' : evalFormula M v (gg A) := gg_estable M A v (fun hnA' => hnnA (fun hA => hnA' (PA hc'.1 hA)))
        exact NB hc'.2 (h hA') hnB
      · have hc' : And ((clas D A).1 = true) ((clas D B).2.2 = true) := by
          simpa only [clas, Bool.and_eq_true] using hc
        exact SB hc'.2 (h (PA hc'.1 hA))
  | .forall A, v => by
      refine ⟨fun hc h d => ?_, fun hc h hn => hn (fun d => ?_), fun hc h d => ?_⟩
      · exact (transfer D hD A (shiftEnv v d)).1 (by simpa only [clas] using hc) (h d)
      · exact (transfer D hD A (shiftEnv v d)).2.2 (by simpa only [clas] using hc) (h d)
      · exact (transfer D hD A (shiftEnv v d)).2.2 (by simpa only [clas] using hc) (h d)
  | .and A B, v => by
      obtain ⟨PA, NA, SA⟩ := transfer D hD A v
      obtain ⟨PB, NB, SB⟩ := transfer D hD B v
      refine ⟨fun hc h => ?_, fun hc h hn => ?_, fun hc h => ?_⟩
      · have hc' : And ((clas D A).1 = true) ((clas D B).1 = true) := by
          simpa only [clas, Bool.and_eq_true] using hc
        exact ⟨PA hc'.1 h.1, PB hc'.2 h.2⟩
      · have hc' : And ((clas D A).2.1 = true) ((clas D B).2.1 = true) := by
          simpa only [clas, Bool.and_eq_true] using hc
        exact NA hc'.1 h.1 (fun hA => NB hc'.2 h.2 (fun hB => hn ⟨hA, hB⟩))
      · have hc' : And ((clas D A).2.2 = true) ((clas D B).2.2 = true) := by
          simpa only [clas, Bool.and_eq_true] using hc
        exact ⟨SA hc'.1 h.1, SB hc'.2 h.2⟩
  | .or A B, v => by
      obtain ⟨PA, NA, SA⟩ := transfer D hD A v
      obtain ⟨PB, NB, SB⟩ := transfer D hD B v
      refine ⟨fun hc h hn => ?_, fun hc h hn => ?_, fun hc h => ?_⟩
      · have hc' : And ((clas D A).1 = true) ((clas D B).1 = true) := by
          simpa only [clas, Bool.and_eq_true] using hc
        rcases h with hA | hB
        · exact hn.1 (PA hc'.1 hA)
        · exact hn.2 (PB hc'.2 hB)
      · have hc' : And ((clas D A).2.1 = true) ((clas D B).2.1 = true) := by
          simpa only [clas, Bool.and_eq_true] using hc
        exact h ⟨fun hA' => NA hc'.1 hA' (fun hA => hn (Or.inl hA)),
          fun hB' => NB hc'.2 hB' (fun hB => hn (Or.inr hB))⟩
      · have hc' : Or (And (And (qfD D A = true) ((clas D A).2.1 = true)) ((clas D B).2.2 = true))
            (And (And (qfD D B = true) ((clas D B).2.1 = true)) ((clas D A).2.2 = true)) := by
          simpa only [clas, Bool.or_eq_true, Bool.and_eq_true] using hc
        rcases hc' with ⟨⟨hqA, hNA⟩, hSB⟩ | ⟨⟨hqB, hNB⟩, hSA⟩
        · exact match decQF D hD A hqA v with
            | isTrue hA => Or.inl hA
            | isFalse hnA =>
                have hnA' : ¬ evalFormula M v (gg A) := fun hA' => NA hNA hA' hnA
                Or.inr (SB hSB (gg_estable M B v (fun hnB' => h ⟨hnA', hnB'⟩)))
        · exact match decQF D hD B hqB v with
            | isTrue hB => Or.inr hB
            | isFalse hnB =>
                have hnB' : ¬ evalFormula M v (gg B) := fun hB' => NB hNB hB' hnB
                Or.inl (SA hSA (gg_estable M A v (fun hnA' => h ⟨hnA', hnB'⟩)))
  | .ex A, v => by
      refine ⟨fun hc h hn => ?_, fun hc h hn => ?_, fun hc _ => ?_⟩
      · obtain ⟨d, hd⟩ := h
        exact hn d ((transfer D hD A (shiftEnv v d)).1 (by simpa only [clas] using hc) hd)
      · exact h (fun d hd' => (transfer D hD A (shiftEnv v d)).2.1 (by simpa only [clas] using hc) hd'
          (fun hd => hn ⟨d, hd⟩))
      · exact absurd hc (by simp only [clas]; decide)

/-! ## §5 · Los 120, y todo modelo estándar -/

/-- Lo único que hay que decidir para los 120: `∈`, con dos argumentos. -/
def Dmem (p : List Char) : Nat → Bool
  | 2 => p == ROBINSON_PlusPlus.Minimal.Axioms.in_sym
  | _ => false

/-- 🏁 **Los 120 pasan a la lectura doble‑negada con `P`**, con sólo `∈` decidible. Lo comprueba el núcleo: `clas` no
    mira ningún término, así que el numeral del ancla no se evalúa. -/
theorem axiomas_clas : ∀ a, List.Mem a ROBINSON_PlusPlus.Minimal.Axioms.axioms → (clas Dmem a).1 = true := by
  decide +kernel

end ROBINSON_PlusPlus.Meta.SolidezDobleNegacion

/-! ### Bajados de `Meta/RigidezEstandar.lean` (ADR‑191): la solidez doble‑negada en todo modelo estándar pide que
`∈` sea el de verdad, y aquí está antes de `Meta/Consistencia.lean`. Conservan su nombre. -/

section Bajados
open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.ModeloCodigo ROBINSON_PlusPlus.Meta.SolidezPrf

namespace ROBINSON_PlusPlus.Meta.RigidezEstandar

variable {M : Model Nat}

theorem ax_de (hM : Estandar M) {φ : Formula} (h : φ ∈ axioms) (v : Nat → Nat) : evalFormula M v φ :=
  hM.haxs v φ h

/-- Toda lista no vacía es un `consN`, y su cola es menor. -/
theorem consN_de {l : Nat} (h : ¬ l = 0) : ∃ a b, And (l = consN a b) (b < l) :=
  ⟨carN l, cdrN l, (consN_car_cdr h).symm, cdrN_lt h⟩

theorem M_mem (hM : Estandar M) : ∀ (l x : Nat), M.rel in_sym [x, l] ↔ memN x l := by
  intro l
  induction l using Nat.strongRecOn with
  | ind l ih =>
    intro x
    by_cases hl : l = 0
    · subst hl
      have h := ax_de hM (φ := ax_L1_in_nil) (by simp [axioms]) (fun _ => 0) x
      simp [ax_L1_in_nil, forall_, neg, In, nil, zero, evalFormula, evalTerm, evalTerms, shiftEnv, hM.hzero] at h
      simp [h, memN_zero]
    · obtain ⟨a, b, rfl, hb⟩ := consN_de hl
      have h := ax_de hM (φ := ax_L2_in_cons) (by simp [axioms]) (fun _ => 0) x a b
      simp [ax_L2_in_cons, forall_3, _root_.iff, In, cons, lor, evalFormula, evalTerm, evalTerms, shiftEnv,
        hM.hcons] at h
      rw [show M.rel in_sym [x, consN a b] ↔ Or (x = a) (M.rel in_sym [x, b]) from ⟨h.1, h.2⟩,
        memN_consN, ih b hb x]

end ROBINSON_PlusPlus.Meta.RigidezEstandar

end Bajados

namespace ROBINSON_PlusPlus.Meta.SolidezDobleNegacion

open ROBINSON_PlusPlus.Meta.ModeloCodigo ROBINSON_PlusPlus.Meta.SolidezPrf

variable {M : Model Nat}

/-- En un modelo estándar, `∈` (de aridad 2) es DECIDIBLE: es `memN` (`M_mem`). -/
def decMem (hM : Estandar M) :
    ∀ (p : List Char) (args : List Nat), Dmem p args.length = true → Decidable (M.rel p args)
  | p, [x, l], h => by
      have hp : p = ROBINSON_PlusPlus.Minimal.Axioms.in_sym := beq_iff_eq.mp h
      subst hp
      haveI : Decidable (memN x l) := by unfold memN; infer_instance
      exact decidable_of_iff (memN x l) (ROBINSON_PlusPlus.Meta.RigidezEstandar.M_mem hM l x).symm
  | _, [], h => absurd h Bool.false_ne_true
  | _, [_], h => absurd h Bool.false_ne_true
  | _, _ :: _ :: _ :: _, h => absurd h Bool.false_ne_true

/-- 🏁 **Todo modelo estándar lo es de la lectura doble‑negada**: los 120, de `φ` a `gg φ` por `P`. -/
theorem estandarDN_de (hM : Estandar M) : EstandarDN M where
  hzero := hM.hzero
  hsucc := hM.hsucc
  hcons := hM.hcons
  haxs := fun v a ha => (transfer Dmem (decMem hM) a v).1 (axiomas_clas a ha) (hM.haxs v a ha)

/-! ## §6 · Herramientas: leer en el modelo lo que `Prf` demuestra, y lo que no puede refutar

`clas` no mira los términos: la sustitución y el lift no la cambian (`clas_subst`, `clas_lift`), así que la polaridad
de `godelCN` o de `provCodeC' φ` se calcula en la fórmula de la que salen, sin tocar ningún numeral. -/

/-- Sin átomos decidibles: basta para todo lo que no pide `S` de un átomo de relación. -/
def Dnada : List Char → Nat → Bool := fun _ _ => false

def decNada : ∀ (p : List Char) (args : List Nat), Dnada p args.length = true → Decidable (M.rel p args) :=
  fun _ _ h => absurd h Bool.false_ne_true

theorem substTerms_length (k : Nat) (t : Term) : ∀ ts : List Term, (substTerms k t ts).length = ts.length
  | [] => rfl
  | _ :: r => congrArg Nat.succ (substTerms_length k t r)

theorem liftTerms_length (c : Nat) : ∀ ts : List Term, (liftTerms c ts).length = ts.length
  | [] => rfl
  | _ :: r => congrArg Nat.succ (liftTerms_length c r)

theorem qfD_subst (D : List Char → Nat → Bool) :
    ∀ (φ : Formula) (k : Nat) (t : Term), qfD D (substFormula k t φ) = qfD D φ
  | .bottom, _, _ => rfl
  | .atom p ts, k, t => by
      show D p (substTerms k t ts).length = D p ts.length
      rw [substTerms_length]
  | .eq _ _, _, _ => rfl
  | .impl A B, k, t => by
      show (qfD D (substFormula k t A) && qfD D (substFormula k t B)) = _
      rw [qfD_subst D A, qfD_subst D B]; rfl
  | .forall _, _, _ => rfl
  | .and A B, k, t => by
      show (qfD D (substFormula k t A) && qfD D (substFormula k t B)) = _
      rw [qfD_subst D A, qfD_subst D B]; rfl
  | .or A B, k, t => by
      show (qfD D (substFormula k t A) && qfD D (substFormula k t B)) = _
      rw [qfD_subst D A, qfD_subst D B]; rfl
  | .ex _, _, _ => rfl

theorem clas_subst (D : List Char → Nat → Bool) :
    ∀ (φ : Formula) (k : Nat) (t : Term), clas D (substFormula k t φ) = clas D φ
  | .bottom, _, _ => rfl
  | .atom p ts, k, t => by
      show (true, true, D p (substTerms k t ts).length) = (true, true, D p ts.length)
      rw [substTerms_length]
  | .eq _ _, _, _ => rfl
  | .impl A B, k, t => by
      show clas D (Formula.impl (substFormula k t A) (substFormula k t B)) = _
      simp only [clas, clas_subst D A k t, clas_subst D B k t]
  | .forall A, k, t => by
      show clas D (Formula.forall (substFormula (k + 1) (liftTerm 0 t) A)) = _
      simp only [clas, clas_subst D A (k + 1) (liftTerm 0 t)]
  | .and A B, k, t => by
      show clas D (Formula.and (substFormula k t A) (substFormula k t B)) = _
      simp only [clas, clas_subst D A k t, clas_subst D B k t]
  | .or A B, k, t => by
      show clas D (Formula.or (substFormula k t A) (substFormula k t B)) = _
      simp only [clas, clas_subst D A k t, clas_subst D B k t, qfD_subst D A k t, qfD_subst D B k t]
  | .ex A, k, t => by
      show clas D (Formula.ex (substFormula (k + 1) (liftTerm 0 t) A)) = _
      simp only [clas, clas_subst D A (k + 1) (liftTerm 0 t)]

section Herramientas
open ROBINSON_PlusPlus.Meta.Hilbert

/-- Lo que `Prf` demuestra, si tiene `S`, vale en el modelo en su lectura CLÁSICA. -/
theorem verdad_de_prf (hM : EstandarDN M) (D : List Char → Nat → Bool)
    (hD : ∀ (p : List Char) (args : List Nat), D p args.length = true → Decidable (M.rel p args))
    {φ : Formula} (hS : (clas D φ).2.2 = true) (h : Prf φ) (v : Nat → Nat) : evalFormula M v φ :=
  (transfer D hD φ v).2.2 hS (prf_sound_dn hM h v)

/-- Una igualdad que `Prf` demuestra vale en el modelo: el dominio es `Nat`, y la igualdad es decidible. -/
theorem eq_de_prf (hM : EstandarDN M) {t u : Term} (h : Prf (Formula.eq t u)) (v : Nat → Nat) :
    evalTerm M v t = evalTerm M v u :=
  verdad_de_prf hM Dnada decNada rfl h v

/-- Lo que es VERDADERO en el modelo, si tiene `P`, no lo refuta `Prf`. -/
theorem no_refuta (hM : EstandarDN M) (D : List Char → Nat → Bool)
    (hD : ∀ (p : List Char) (args : List Nat), D p args.length = true → Decidable (M.rel p args))
    {φ : Formula} (hP : (clas D φ).1 = true) (v : Nat → Nat) (hφ : evalFormula M v φ) : ¬ Prf (neg φ) :=
  fun h => prf_sound_dn hM h v ((transfer D hD φ v).1 hP hφ)

end Herramientas

end ROBINSON_PlusPlus.Meta.SolidezDobleNegacion

namespace ROBINSON_PlusPlus.Meta.SolidezPrf

open ROBINSON_PlusPlus.Meta.Hilbert

variable {M : Model Nat}

/-- `ConsistentH` a partir de CUALQUIER modelo estándar; `estandar_MN` lo instancia en `MNV V₀`. Desde ADR‑191, por la
    solidez doble‑negada (`estandarDN_de`, `consistentH_dn`): sin `p3` en `Prop`, sin lógica clásica. -/
theorem consistentH_de (hM : Estandar M) : ConsistentH :=
  ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.consistentH_dn
    (ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.estandarDN_de hM)

end ROBINSON_PlusPlus.Meta.SolidezPrf

#print axioms ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.prf_sound_dn
#print axioms ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.transfer
#print axioms ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.axiomas_clas
#print axioms ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.estandarDN_de
#print axioms ROBINSON_PlusPlus.Meta.SolidezPrf.consistentH_de
#print axioms ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.eq_de_prf
#print axioms ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.no_refuta
