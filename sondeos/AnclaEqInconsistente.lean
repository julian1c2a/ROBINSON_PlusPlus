/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta

/-!
# SONDEO · F1 — `[AnclaEq]` implica `Prf ⊥` (2026‑09‑28)

**Pregunta** (hallazgo F1 de la auditoría del 2026‑09‑28, que lo dejó como INFERENCIA): la clase
`AnclaEq` (`Prf (axiomsCodeT =eq listFormCodeM axioms)`, ADR‑026) es hipótesis de D1
(`repr_pos'_prf`), D3 (`d3_prf_real`), `pcc_lineWF_tracked`, `goedel_first_prf` y
`goedel_second_prf`, y no tiene instancia. ¿Es derivable? ¿Es siquiera compatible con `ConsistentH`?

## 🏁 Respuesta, COMPILADA: no es compatible

    theorem anclaEq_prf_bot [AnclaEq] : Prf ⊥
    theorem hipotesis_goedel_insatisfacibles : ¬ (AnclaEq ∧ ConsistentH)
    footprint: [propext, Classical.choice, Quot.sound]   ← ningún axioma de RPP, ningún `sorry`

⇒ **Gödel I y II sobre `Prf` son VACUOS**: sus dos hipótesis no pueden valer a la vez. §6 lo
demuestra con ejemplos: con las MISMAS hipótesis salen `Prf godelCN` y `Prf consistencyFormula'`.
D1, D3 y `pcc_lineWF_tracked` bajo `[AnclaEq]` no dicen nada que `efq` no diga ya.

**ADR‑113** (`cons a b = σ (pair a b)`, rama `claude/project-thread-bgzgkr`, `ae528f8`): este
mismo fichero, sin cambios, recompila allí con el mismo resultado y el mismo footprint (medido el
2026‑09‑28). ADR‑113 no toca ni los dos axiomas ni `ax_L2`, y `prf_cantor_mono_right` sigue en pie.

## Cómo (la prueba es sintáctica: no hace falta ningún modelo)

1. **Medido** (§2, `filtro_occ`, por el núcleo): de los 141 axiomas sólo DOS nombran `axiomsCodeT`
   —`ax_vpf_thy` y `ax_lineWF_thy`, posiciones 81 y 97— y en los dos aparece sólo como segundo
   argumento de `In`. La teoría no dice NADA de `axiomsCodeT` salvo su pertenencia.
2. **Transferencia** (§3, `prf_rep`): cambiar la constante `axiomsCodeT` por un término cerrado `r`
   conserva los teoremas de `Prf`, siempre que conserve los 141 axiomas. Inducción sobre `Prf`,
   legítima por M‑11 (ningún `axiom` habita `Prf`).
3. **El reemplazo** (§4): `r := cons a₀ axiomsCodeT`, con `a₀ = ⌜ax18⌝`. Con el ancla,
   `a₀ ∈ axiomsCodeT`, luego `In c r ⇔ In c axiomsCodeT` y los dos axiomas traducidos siguen
   siendo teoremas (`prf_rep_vpf`, `prf_rep_lwt`). Los otros 139 no cambian.
4. **La contradicción** (§5): el ancla traducida es `cons a₀ T = listFormCodeM axioms`; con el ancla,
   `cons a₀ T = T`; Cantor (`prf_cantor_mono_right`) da `T < cons a₀ T`, luego `T < T`, contra `ax18`.

🔑 *Una constante que la teoría sólo toca a través de `In` no tiene VALOR en la teoría, sólo
EXTENSIÓN. Un ancla que fija su valor no es derivable, y si se deriva, lo que se deriva es `⊥`.*

## Controles (vistos fallar)

* `filtro_occ` es cómputo real: mutado a `[ax_vpf_thy]`, el `rfl` FALLA (visto; el mutante se borró).
  Además, Control 1 lo refuta como teorema.
* Control 3: sin `[AnclaEq]`, el paso `in_rr_imp` NO compila (`#guard_msgs` fija el error; si
  compilara, el `#guard_msgs` rompería).
* `#print axioms` al final. ⚠️ Depende de los imports: este fichero importa `ROBINSON_PlusPlus.Meta`.

## ⚠️ Lo que este sondeo NO dice

* **No** dice que `Prf` sea inconsistente. Dice que `Prf ⊢ ancla ⟹ Prf ⊢ ⊥`, es decir, que si `Prf`
  es consistente el ancla NO es derivable (la inferencia de la auditoría, ahora compilada), y
  además que suponerla como hipótesis junto a `ConsistentH` es contradictorio.
* **No** dice nada de `ax_axiomsCodeT_eq` (el ancla sobre `⊢`): `Derives` está habitado por
  `axiom`s y no admite la inducción de §3. SIN MEDIR.
* **No** mide la salida. La propuesta de la auditoría (`EsAx(c) := ⋁ c = ⌜aᵢ⌝`) parece circular
  para los dos axiomas que la usarían, porque su lista tendría que contener su propio código.
  Es un argumento de tamaño, SIN COMPILAR.
-/

open FOL
open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.Representability2Prf
open ROBINSON_PlusPlus.Meta.CantorMonoPrf
open ROBINSON_PlusPlus.Meta.NatMulPrf
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf
open ROBINSON_PlusPlus.Meta.LineWFCases
open ROBINSON_PlusPlus.Meta.Sigma1Prf

namespace Sondeos.AnclaEqInconsistente

/-! ## §1 · Reemplazar el símbolo `axiomsCodeT` por un término `r` -/

/-- ¿Es `t` la constante `axiomsCodeT`? (símbolo `"axiomsCodeT"` sin argumentos). -/
def esAC : String → List Term → Bool
  | f, [] => f == "axiomsCodeT"
  | _, _ :: _ => false

mutual
/-- `repT r t`: cambia cada aparición de la constante `axiomsCodeT` en `t` por `r`. -/
def repT (r : Term) : Term → Term
  | .var n => .var n
  | .func f ts => if esAC f ts then r else .func f (repTs r ts)
def repTs (r : Term) : List Term → List Term
  | [] => []
  | t :: ts => repT r t :: repTs r ts
end

def repF (r : Term) : Formula → Formula
  | .bottom => .bottom
  | .atom p ts => .atom p (repTs r ts)
  | .eq a b => .eq (repT r a) (repT r b)
  | .impl a b => .impl (repF r a) (repF r b)
  | .forall a => .forall (repF r a)
  | .and a b => .and (repF r a) (repF r b)
  | .or a b => .or (repF r a) (repF r b)
  | .ex a => .ex (repF r a)

theorem esAC_liftTerms (f : String) (c : Nat) (ts : List Term) :
    esAC f (liftTerms c ts) = esAC f ts := by
  cases ts <;> rfl

theorem esAC_substTerms (f : String) (v : Nat) (s : Term) (ts : List Term) :
    esAC f (substTerms v s ts) = esAC f ts := by
  cases ts <;> rfl

theorem esAC_true {f : String} {ts : List Term} (h : esAC f ts = true) : ts = [] := by
  cases ts with
  | nil => rfl
  | cons _ _ => simp [esAC] at h

/-! ### Conmutación con `lift` y `subst`, si `r` es cerrado -/

section Conmuta
variable {r : Term}

mutual
theorem repT_lift (hl : ∀ c, liftTerm c r = r) (c : Nat) :
    ∀ t : Term, repT r (liftTerm c t) = liftTerm c (repT r t)
  | .var n => by
      unfold liftTerm; split <;> simp [repT, *]
  | .func f ts => by
      by_cases h : esAC f ts = true
      · have h0 := esAC_true h; subst h0
        simp only [liftTerm, liftTerms, repT, h, if_true, hl]
      · have h' : esAC f (liftTerms c ts) = false := by
          rw [esAC_liftTerms]; simpa using h
        simp only [liftTerm, repT, h', h, if_false, Bool.false_eq_true, repTs_lift hl c ts]
theorem repTs_lift (hl : ∀ c, liftTerm c r = r) (c : Nat) : ∀ ts : List Term, repTs r (liftTerms c ts) = liftTerms c (repTs r ts)
  | [] => rfl
  | t :: ts => by simp only [liftTerms, repTs, repT_lift hl c t, repTs_lift hl c ts]
end

mutual
theorem repT_subst (hs : ∀ v s, substTerm v s r = r) (v : Nat) (s : Term) :
    ∀ t : Term, repT r (substTerm v s t) = substTerm v (repT r s) (repT r t)
  | .var n => by
      by_cases h : n = v
      · subst h; simp [substTerm, repT]
      · by_cases h2 : n > v <;> simp [substTerm, repT, h, h2]
  | .func f ts => by
      by_cases h : esAC f ts = true
      · have h0 := esAC_true h; subst h0
        simp only [substTerm, substTerms, repT, h, if_true, hs]
      · have h' : esAC f (substTerms v s ts) = false := by
          rw [esAC_substTerms]; simpa using h
        simp only [substTerm, repT, h', h, if_false, Bool.false_eq_true, repTs_subst hs v s ts]
theorem repTs_subst (hs : ∀ v s, substTerm v s r = r) (v : Nat) (s : Term) :
    ∀ ts : List Term, repTs r (substTerms v s ts) = substTerms v (repT r s) (repTs r ts)
  | [] => rfl
  | t :: ts => by simp only [substTerms, repTs, repT_subst hs v s t, repTs_subst hs v s ts]
end

theorem repF_lift (hl : ∀ c, liftTerm c r = r) : ∀ (φ : Formula) (c : Nat), repF r (liftFormula c φ) = liftFormula c (repF r φ)
  | .bottom, _ => rfl
  | .atom p ts, c => by simp only [liftFormula, repF, repTs_lift hl c ts]
  | .eq a b, c => by simp only [liftFormula, repF, repT_lift hl c a, repT_lift hl c b]
  | .impl a b, c => by simp only [liftFormula, repF, repF_lift hl a c, repF_lift hl b c]
  | .and a b, c => by simp only [liftFormula, repF, repF_lift hl a c, repF_lift hl b c]
  | .or a b, c => by simp only [liftFormula, repF, repF_lift hl a c, repF_lift hl b c]
  | .forall a, c => by simp only [liftFormula, repF, repF_lift hl a (c + 1)]
  | .ex a, c => by simp only [liftFormula, repF, repF_lift hl a (c + 1)]

theorem repF_subst (hl : ∀ c, liftTerm c r = r) (hs : ∀ v s, substTerm v s r = r) : ∀ (φ : Formula) (v : Nat) (s : Term),
    repF r (substFormula v s φ) = substFormula v (repT r s) (repF r φ)
  | .bottom, _, _ => rfl
  | .atom p ts, v, s => by simp only [substFormula, repF, repTs_subst hs v s ts]
  | .eq a b, v, s => by simp only [substFormula, repF, repT_subst hs v s a, repT_subst hs v s b]
  | .impl a b, v, s => by simp only [substFormula, repF, repF_subst hl hs a v s, repF_subst hl hs b v s]
  | .and a b, v, s => by simp only [substFormula, repF, repF_subst hl hs a v s, repF_subst hl hs b v s]
  | .or a b, v, s => by simp only [substFormula, repF, repF_subst hl hs a v s, repF_subst hl hs b v s]
  | .forall a, v, s => by
      simp only [substFormula, repF, repF_subst hl hs a (v + 1) (liftTerm 0 s), repT_lift hl 0 s]
  | .ex a, v, s => by
      simp only [substFormula, repF, repF_subst hl hs a (v + 1) (liftTerm 0 s), repT_lift hl 0 s]

end Conmuta


/-! ## §2 · Dónde aparece `axiomsCodeT`, y los códigos que no lo contienen -/

mutual
def occT : Term → Bool
  | .var _ => false
  | .func f ts => esAC f ts || occTs ts
def occTs : List Term → Bool
  | [] => false
  | t :: ts => occT t || occTs ts
end

def occF : Formula → Bool
  | .bottom => false
  | .atom _ ts => occTs ts
  | .eq a b => occT a || occT b
  | .impl a b => occF a || occF b
  | .forall a => occF a
  | .and a b => occF a || occF b
  | .or a b => occF a || occF b
  | .ex a => occF a

mutual
theorem repT_of_occ (r : Term) : ∀ t : Term, occT t = false → repT r t = t
  | .var _, _ => rfl
  | .func f ts, h => by
      simp only [occT, Bool.or_eq_false_iff] at h
      simp only [repT, h.1, Bool.false_eq_true, if_false, repTs_of_occ r ts h.2]
theorem repTs_of_occ (r : Term) : ∀ ts : List Term, occTs ts = false → repTs r ts = ts
  | [], _ => rfl
  | t :: ts, h => by
      simp only [occTs, Bool.or_eq_false_iff] at h
      simp only [repTs, repT_of_occ r t h.1, repTs_of_occ r ts h.2]
end

theorem repF_of_occ (r : Term) : ∀ φ : Formula, occF φ = false → repF r φ = φ
  | .bottom, _ => rfl
  | .atom _ ts, h => by simp only [occF] at h; simp only [repF, repTs_of_occ r ts h]
  | .eq a b, h => by
      simp only [occF, Bool.or_eq_false_iff] at h
      simp only [repF, repT_of_occ r a h.1, repT_of_occ r b h.2]
  | .impl a b, h => by
      simp only [occF, Bool.or_eq_false_iff] at h
      simp only [repF, repF_of_occ r a h.1, repF_of_occ r b h.2]
  | .and a b, h => by
      simp only [occF, Bool.or_eq_false_iff] at h
      simp only [repF, repF_of_occ r a h.1, repF_of_occ r b h.2]
  | .or a b, h => by
      simp only [occF, Bool.or_eq_false_iff] at h
      simp only [repF, repF_of_occ r a h.1, repF_of_occ r b h.2]
  | .forall a, h => by simp only [occF] at h; simp only [repF, repF_of_occ r a h]
  | .ex a, h => by simp only [occF] at h; simp only [repF, repF_of_occ r a h]

/-- Los códigos son numerales y `cons`: no contienen la constante. Inducción estructural, sin
    materializar el término (como `liftTerm_formCodeM`). -/
theorem occT_numeralM : ∀ n : Nat, occT (numeralM n) = false
  | 0 => rfl
  | n + 1 => by simp only [numeralM, succ, occT, esAC, occTs, occT_numeralM n]; rfl

theorem occT_charsCodeM : ∀ cs : List Char, occT (charsCodeM cs) = false
  | [] => rfl
  | c :: cs => by
      simp only [charsCodeM, cons, occT, esAC, occTs, occT_numeralM, occT_charsCodeM cs]; rfl

mutual
theorem occT_termCodeM : ∀ t : Term, occT (termCodeM t) = false
  | .var n => by simp only [termCodeM, cons, occT, esAC, occTs, occT_numeralM]; rfl
  | .func s ts => by
      simp only [termCodeM, cons, occT, esAC, occTs, occT_numeralM, strCodeM, occT_charsCodeM,
        occT_termsCodeM ts]; rfl
theorem occT_termsCodeM : ∀ ts : List Term, occT (termsCodeM ts) = false
  | [] => rfl
  | t :: ts => by
      simp only [termsCodeM, cons, occT, esAC, occTs, occT_termCodeM t, occT_termsCodeM ts]; rfl
end

theorem occT_formCodeM : ∀ φ : Formula, occT (formCodeM φ) = false
  | .bottom => by simp only [formCodeM, cons, occT, esAC, occTs, occT_numeralM]; rfl
  | .atom p ts => by
      simp only [formCodeM, cons, occT, esAC, occTs, occT_numeralM, strCodeM, occT_charsCodeM,
        occT_termsCodeM]; rfl
  | .eq a b => by
      simp only [formCodeM, cons, occT, esAC, occTs, occT_numeralM, occT_termCodeM]; rfl
  | .impl a b => by
      simp only [formCodeM, cons, occT, esAC, occTs, occT_numeralM, occT_formCodeM a,
        occT_formCodeM b]; rfl
  | .forall a => by
      simp only [formCodeM, cons, occT, esAC, occTs, occT_numeralM, occT_formCodeM a]; rfl
  | .and a b => by
      simp only [formCodeM, cons, occT, esAC, occTs, occT_numeralM, occT_formCodeM a,
        occT_formCodeM b]; rfl
  | .or a b => by
      simp only [formCodeM, cons, occT, esAC, occTs, occT_numeralM, occT_formCodeM a,
        occT_formCodeM b]; rfl
  | .ex a => by
      simp only [formCodeM, cons, occT, esAC, occTs, occT_numeralM, occT_formCodeM a]; rfl

theorem occT_listFormCodeM : ∀ L : List Formula, occT (listFormCodeM L) = false
  | [] => rfl
  | f :: fs => by
      simp only [listFormCodeM, cons, occT, esAC, occTs, occT_formCodeM f,
        occT_listFormCodeM fs]; rfl

-- 📏 Medido: posiciones de `axioms` donde aparece `axiomsCodeT`.
#eval ((List.range axioms.length).filter (fun i => occF (axioms.getD i .bottom)))
#eval axioms.length


/-- ✅ Medido por el núcleo: exactamente DOS de los 141 axiomas mencionan `axiomsCodeT`. -/
theorem filtro_occ : List.filter occF axioms = ([ax_vpf_thy, ax_lineWF_thy] : List Formula) := by
  set_option maxRecDepth 20000 in rfl

theorem occ_casos {a : Formula} (ha : List.Mem a axioms) (ho : occF a = true) :
    Or (a = ax_vpf_thy) (a = ax_lineWF_thy) := by
  have hm : List.Mem a (List.filter occF axioms) := List.mem_filter.mpr ⟨ha, ho⟩
  rw [filtro_occ] at hm
  cases hm with
  | head => exact Or.inl rfl
  | tail _ h =>
      cases h with
      | head => exact Or.inr rfl
      | tail _ h => cases h

/-! ## §3 · `Prf` es cerrado bajo el reemplazo (dado que lo sean los axiomas) -/

theorem repT_axiomsCodeT (r : Term) : repT r axiomsCodeT = r := by
  simp [repT, axiomsCodeT, esAC]

section Transfer
variable {r : Term} (hl : ∀ c, liftTerm c r = r) (hs : ∀ v s, substTerm v s r = r)

include hl hs in
theorem rep_induction (A : Formula) :
    repF r (ROBINSON_PlusPlus.Full.inductionFormula A)
      = ROBINSON_PlusPlus.Full.inductionFormula (repF r A) := by
  simp only [ROBINSON_PlusPlus.Full.inductionFormula, repF, repF_subst hl hs, repF_lift hl]
  rfl

include hl hs in
theorem rep_listInduction (A : Formula) :
    repF r (listInductionFormula A) = listInductionFormula (repF r A) := by
  simp only [listInductionFormula, repF, repF_subst hl hs, repF_lift hl]
  rfl

include hl in
theorem rep_confinement (P C : Formula) :
    repF r (confinementFormula P C) = confinementFormula (repF r P) (repF r C) := by
  simp only [confinementFormula, repF, repF_lift hl]

include hl hs in
theorem prfI_rep (hax : ∀ a, List.Mem a axioms → Prf (repF r a)) {φ : Formula} (h : Prfᵢ φ) :
    Prf (repF r φ) := by
  induction h with
  | p1 A B => exact Prf.incl (Prfᵢ.p1 _ _)
  | p2 A B C => exact Prf.incl (Prfᵢ.p2 _ _ _)
  | c1 A B => exact Prf.incl (Prfᵢ.c1 _ _)
  | c2 A B => exact Prf.incl (Prfᵢ.c2 _ _)
  | c3 A B => exact Prf.incl (Prfᵢ.c3 _ _)
  | j1 A B => exact Prf.incl (Prfᵢ.j1 _ _)
  | j2 A B => exact Prf.incl (Prfᵢ.j2 _ _)
  | j3 A B C => exact Prf.incl (Prfᵢ.j3 _ _ _)
  | efq A => exact Prf.incl (Prfᵢ.efq _)
  | q1 A t =>
      show Prf (Formula.forall (repF r A) ⇒ repF r (substFormula 0 t A))
      rw [repF_subst hl hs]; exact Prf.incl (Prfᵢ.q1 _ _)
  | q2 A t =>
      show Prf (repF r (substFormula 0 t A) ⇒ Formula.ex (repF r A))
      rw [repF_subst hl hs]; exact Prf.incl (Prfᵢ.q2 _ _)
  | q3 A B =>
      show Prf (Formula.forall (repF r A ⇒ repF r (liftFormula 0 B)) ⇒ (Formula.ex (repF r A) ⇒ repF r B))
      rw [repF_lift hl]; exact Prf.incl (Prfᵢ.q3 _ _)
  | eqrefl t => exact Prf.incl (Prfᵢ.eqrefl _)
  | leibniz A t₁ t₂ =>
      show Prf ((repT r t₁ ≐ repT r t₂) ⇒
        (repF r (substFormula 0 t₁ A) ⇒ repF r (substFormula 0 t₂ A)))
      rw [repF_subst hl hs, repF_subst hl hs]; exact Prf.incl (Prfᵢ.leibniz _ _ _)
  | thy a ha => exact hax a ha
  | mp A B _ _ ih1 ih2 => exact Prf.mp _ _ ih1 ih2
  | gen A _ ih => exact Prf.gen _ ih

include hl hs in
/-- 🔑 **Transferencia**: si los 141 axiomas siguen siendo teoremas de `Prf` tras el reemplazo,
    TODO teorema de `Prf` lo sigue siendo. Inducción sobre `Prf`, legítima por M‑11 (ningún
    `axiom` habita `Prf` desde ADR‑026). -/
theorem prf_rep (hax : ∀ a, List.Mem a axioms → Prf (repF r a)) {φ : Formula} (h : Prf φ) :
    Prf (repF r φ) := by
  induction h with
  | incl h0 => exact prfI_rep hl hs hax h0
  | p3 A => exact Prf.p3 _
  | ind A => rw [rep_induction hl hs]; exact Prf.ind _
  | qconf P C => rw [rep_confinement hl]; exact Prf.qconf _ _
  | listInd A => rw [rep_listInduction hl hs]; exact Prf.listInd _
  | mp A B _ _ ih1 ih2 => exact Prf.mp _ _ ih1 ih2
  | gen A _ ih => exact Prf.gen _ ih

end Transfer


/-! ## §4 · El reemplazo concreto: `axiomsCodeT ↦ cons a₀ axiomsCodeT`

`a₀` es el código de un axioma cualquiera (aquí `ax18_lt_irrefl`). Con el ancla, `a₀ ∈ axiomsCodeT`,
así que `In c (cons a₀ axiomsCodeT) ⇔ In c axiomsCodeT` para todo `c`: la pertenencia —lo único que
los axiomas dicen de `axiomsCodeT`— no cambia. El valor sí: `t < cons a₀ t` (Cantor). -/

/-- El código usado como cabeza extra. -/
def a0 : Term := formCodeM ax18_lt_irrefl

/-- El término que sustituye a `axiomsCodeT`. -/
def rr : Term := cons a0 axiomsCodeT

theorem rr_lift (c : Nat) : liftTerm c rr = rr := by
  simp only [rr, a0, cons, axiomsCodeT, liftTerm, liftTerms, liftTerm_formCodeM]

theorem rr_subst (v : Nat) (s : Term) : substTerm v s rr = rr := by
  simp only [rr, a0, cons, axiomsCodeT, substTerm, substTerms, substTerm_formCodeM]

theorem ax18_mem : List.Mem ax18_lt_irrefl axioms := (show ax18_lt_irrefl ∈ axioms by simp [axioms])
theorem vpf_mem : List.Mem ax_vpf_thy axioms := (show ax_vpf_thy ∈ axioms by simp [axioms])
theorem lwt_mem : List.Mem ax_lineWF_thy axioms := (show ax_lineWF_thy ∈ axioms by simp [axioms])

/-- Con el ancla, la pertenencia a `rr` implica la pertenencia a `axiomsCodeT` (término `c` libre). -/
theorem in_rr_imp [AnclaEq] (c : Term) : Prf (In c rr ⇒ In c axiomsCodeT) := by
  have hA0 : Prf (In a0 axiomsCodeT) := prf_inAxC ax18_lt_irrefl ax18_mem
  have hmp : Prf (In c rr ⇒ lor (c =eq a0) (In c axiomsCodeT)) :=
    prf_and_elim_left (prf_in_cons_iff c a0 axiomsCodeT)
  have heq : Prf ((c =eq a0) ⇒ In c axiomsCodeT) :=
    prf_deduction (PrfH_congr_In_left (PrfH_eq_symm (prfH_hyp_self _)) (prf_to_prfH hA0 _))
  have hid : Prf (In c axiomsCodeT ⇒ In c axiomsCodeT) := Prf.incl (prfI_id _)
  exact prf_imp_trans hmp (prf_or_elim_imp heq hid)

/-- Y al revés, sin ancla. -/
theorem in_imp_rr (c : Term) : Prf (In c axiomsCodeT ⇒ In c rr) :=
  prf_in_cons_tail_imp a0 c axiomsCodeT

/-! ### Los dos axiomas que nombran `axiomsCodeT`, tras el reemplazo -/

def vpfE : Formula :=
  validProofFn (.var 2) (cons (cons (numeralM 15) (cons (.var 1) nil)) (.var 0)) =eq
    validProofFn (concat (.var 2) (cons (.var 1) nil)) (.var 0)

theorem vpf_eq : ax_vpf_thy = forall_3 (In (.var 1) axiomsCodeT ⇒ vpfE) := rfl
theorem vpfE_occ : occF vpfE = false := rfl

theorem rep_vpf : repF rr ax_vpf_thy = forall_3 (In (.var 1) rr ⇒ vpfE) := by
  rw [vpf_eq]
  simp only [forall_3, repF, In, repTs, repT_axiomsCodeT, repF_of_occ rr vpfE vpfE_occ]
  rfl

theorem prf_rep_vpf [AnclaEq] : Prf (repF rr ax_vpf_thy) := by
  rw [rep_vpf]
  have hax : Prf (forall_3 (In (.var 1) axiomsCodeT ⇒ vpfE)) := vpf_eq ▸ prf_ax vpf_mem
  -- abrir los tres `∀` instanciando con #2, #1, #0 devuelve el cuerpo tal cual
  have hbody : Prf (In (.var 1) axiomsCodeT ⇒ vpfE) :=
    prf_spec (prf_spec (prf_spec hax (.var 2)) (.var 1)) (.var 0)
  exact Prf.gen _ (Prf.gen _ (Prf.gen _ (prf_imp_trans (in_rr_imp (.var 1)) hbody)))

def lwN : Formula := nthc (.var 0) (succ zero) =eq numeralM 15
def lwL : Formula := lineWF (.var 0)
def lwP : Formula := lenc (.var 0) =eq numeralM 2

theorem lwt_eq : ax_lineWF_thy =
    forall_ (lwN ⇒ (lwL ⇔ Formula.and lwP (In (carc (.var 0)) axiomsCodeT))) := rfl

theorem rep_lwt : repF rr ax_lineWF_thy =
    forall_ (lwN ⇒ (lwL ⇔ Formula.and lwP (In (carc (.var 0)) rr))) := by
  rw [lwt_eq]
  simp only [forall_, iff, repF, In, repTs, repT_axiomsCodeT,
    repF_of_occ rr lwN rfl, repF_of_occ rr lwL rfl, repF_of_occ rr lwP rfl]
  rfl

/-- Composición de implicaciones dentro de un contexto `PrfH`. -/
theorem compH {Γ : List Formula} {A B C : Formula} (hAB : PrfH Γ (A ⇒ B)) (hBC : PrfH Γ (B ⇒ C)) :
    PrfH Γ (A ⇒ C) :=
  PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prfᵢ.p2 A B C))
    (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prfᵢ.p1 (B ⇒ C) A)) hBC)) hAB

/-- `P ∧ I ⇒ P ∧ I'` a partir de `I ⇒ I'`. -/
theorem and_mono {P I I' : Formula} (h : Prf (I ⇒ I')) : Prf (Formula.and P I ⇒ Formula.and P I') := by
  refine prf_deduction ?_
  have H := prfH_hyp_self (Formula.and P I)
  have hp : PrfH [Formula.and P I] P := PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prfᵢ.c2 P I)) H
  have hi : PrfH [Formula.and P I] I := PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prfᵢ.c3 P I)) H
  have hi' : PrfH [Formula.and P I] I' := PrfH.mp _ _ _ (prf_to_prfH h _) hi
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prfᵢ.c1 P I')) hp) hi'

/-- `(L ⇔ X) ⇒ (L ⇔ X')` a partir de `X ⇒ X'` y `X' ⇒ X`. -/
theorem iff_swap {L X X' : Formula} (h1 : Prf (X ⇒ X')) (h2 : Prf (X' ⇒ X)) :
    Prf ((L ⇔ X) ⇒ (L ⇔ X')) := by
  refine prf_deduction ?_
  have H := prfH_hyp_self (L ⇔ X)
  have a : PrfH [L ⇔ X] (L ⇒ X) := PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prfᵢ.c2 (L ⇒ X) (X ⇒ L))) H
  have b : PrfH [L ⇔ X] (X ⇒ L) := PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prfᵢ.c3 (L ⇒ X) (X ⇒ L))) H
  have a' := compH a (prf_to_prfH h1 _)
  have b' := compH (prf_to_prfH h2 _) b
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prfᵢ.c1 (L ⇒ X') (X' ⇒ L))) a') b'

theorem prf_rep_lwt [AnclaEq] : Prf (repF rr ax_lineWF_thy) := by
  rw [rep_lwt]
  have hax : Prf (forall_ (lwN ⇒ (lwL ⇔ Formula.and lwP (In (carc (.var 0)) axiomsCodeT)))) :=
    lwt_eq ▸ prf_ax lwt_mem
  have hbody : Prf (lwN ⇒ (lwL ⇔ Formula.and lwP (In (carc (.var 0)) axiomsCodeT))) :=
    prf_spec hax (.var 0)
  have hsw := iff_swap (L := lwL)
    (and_mono (P := lwP) (in_imp_rr (carc (.var 0))))
    (and_mono (P := lwP) (in_rr_imp (carc (.var 0))))
  exact Prf.gen _ (prf_imp_trans hbody hsw)

/-- Los 141 axiomas siguen siendo teoremas de `Prf` tras el reemplazo (con el ancla). -/
theorem hax_rr [AnclaEq] : ∀ a, List.Mem a axioms → Prf (repF rr a) := by
  intro a ha
  cases ho : occF a with
  | false => rw [repF_of_occ rr a ho]; exact prf_ax ha
  | true =>
      rcases occ_casos ha ho with rfl | rfl
      · exact prf_rep_vpf
      · exact prf_rep_lwt

/-! ## §5 · 🏁 El resultado -/

/-- 🏁 **`[AnclaEq]` implica `Prf ⊥`.** -/
theorem anclaEq_prf_bot [AnclaEq] : Prf Formula.bottom := by
  have hA : Prf (axiomsCodeT =eq listFormCodeM axioms) := AnclaEq.eq
  -- el ancla, tras el reemplazo: `cons a₀ axiomsCodeT = listFormCodeM axioms`
  have hB0 := prf_rep rr_lift rr_subst hax_rr hA
  have hB : Prf (rr =eq listFormCodeM axioms) := by
    have e : repF rr (axiomsCodeT =eq listFormCodeM axioms) = (rr =eq listFormCodeM axioms) := by
      simp only [repF, repT_axiomsCodeT, repT_of_occ rr _ (occT_listFormCodeM axioms)]
    rwa [e] at hB0
  -- `cons a₀ T = T`
  have hC : Prf (rr =eq axiomsCodeT) := prf_eq_trans hB (prf_eq_symm hA)
  -- `T < cons a₀ T`, luego `T < T`
  have hlt : Prf (lt axiomsCodeT rr) := prf_cantor_mono_right a0 axiomsCodeT
  let f : Formula := lt axiomsCodeT (.var 0)
  have hS : ∀ s : Term, substFormula 0 s f = lt axiomsCodeT s := by
    intro s; simp [f, lt, axiomsCodeT, substFormula, substTerms, substTerm]
  have hL := Prf.incl (Prfᵢ.leibniz f rr axiomsCodeT)
  rw [hS, hS] at hL
  have hTT : Prf (lt axiomsCodeT axiomsCodeT) := prf_mp (prf_mp hL hC) hlt
  exact prf_mp (prf_lt_irrefl axiomsCodeT) hTT

/-- 🏁 **Las hipótesis de Gödel I/II sobre `Prf` son insatisfacibles a la vez.** -/
theorem anclaEq_no_consistente (h : AnclaEq) : ¬ ConsistentH :=
  fun hcon => hcon (@anclaEq_prf_bot h)

theorem hipotesis_goedel_insatisfacibles : ¬ (AnclaEq ∧ ConsistentH) :=
  fun ⟨h, hcon⟩ => anclaEq_no_consistente h hcon


/-! ## §6 · Vacuidad, con ejemplos, y controles vistos fallar -/

open ROBINSON_PlusPlus.Meta.ProofChain ROBINSON_PlusPlus.Meta.GodelTwo
open ROBINSON_PlusPlus.Meta.DiagonalNumeral ROBINSON_PlusPlus.Meta.GodelTwoPrf

/-- Ejemplo de vacuidad (1): con las MISMAS hipótesis que `goedel_first_prf`, sale lo contrario de
    su conclusión. -/
example [AnclaEq] (hcon : ConsistentH) : Prf godelCN :=
  absurd anclaEq_prf_bot hcon

/-- Ejemplo de vacuidad (2): con las mismas hipótesis que `goedel_second_prf`, `Prf` demuestra su
    propia consistencia. -/
example [AnclaEq] (hcon : ConsistentH) : Prf consistencyFormula' :=
  absurd anclaEq_prf_bot hcon

/-- Ejemplo de vacuidad (3): bajo `[AnclaEq]` sola, D3 sale por `efq`, sin la maquinaria de
    `d3_prf_real` (y lo mismo D1, `pcc_lineWF_tracked` o cualquier fórmula). -/
example [AnclaEq] (φ : Formula) : Prf (provCodeC' φ ⇒ provCodeC' (provCodeC' φ)) :=
  Prf.mp _ _ (Prf.incl (Prfᵢ.efq _)) anclaEq_prf_bot

/-- Control 1 (el detector no es trivialmente verde): la lista de ocurrencias NO es otra. -/
example : List.filter occF axioms ≠ ([ax_vpf_thy] : List Formula) := by
  rw [filtro_occ]; intro h; cases h

/-- Control 2 (el detector ve la constante): `occF` es `true` en los dos y `false` en `ax18`. -/
example : And (occF ax_vpf_thy = true) (And (occF ax_lineWF_thy = true) (occF ax18_lt_irrefl = false)) :=
  ⟨rfl, rfl, rfl⟩

end Sondeos.AnclaEqInconsistente


/-! ### Control 3 (el ancla hace falta): sin `[AnclaEq]`, `in_rr_imp` NO compila. -/
open Sondeos.AnclaEqInconsistente in
/--
error: failed to synthesize instance of type class
  AnclaEq

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (c : Term) : Prf (In c rr ⇒ In c axiomsCodeT) :=
  prf_imp_trans (prf_and_elim_left (prf_in_cons_iff c a0 axiomsCodeT))
    (prf_or_elim_imp
      (prf_deduction (PrfH_congr_In_left (PrfH_eq_symm (prfH_hyp_self _))
        (prf_to_prfH (prf_inAxC ax18_lt_irrefl ax18_mem) _)))
      (Prf.incl (prfI_id _)))

/-! ### Medición del footprint (depende de los imports: este fichero importa `ROBINSON_PlusPlus.Meta`) -/
#print axioms Sondeos.AnclaEqInconsistente.anclaEq_prf_bot
#print axioms Sondeos.AnclaEqInconsistente.hipotesis_goedel_insatisfacibles
#print axioms Sondeos.AnclaEqInconsistente.prf_rep


/-! ## §7 · Control independiente (2026-10-01): las hipótesis EXACTAS de `goedel_first_prf` / `goedel_second_prf`

El mismo `hcon` alimenta a `goedel_first_prf` (luego es de su tipo) y a `absurd` contra `anclaEq_prf_bot`
(luego es `¬ Prf ⊥` del MISMO `Prf`): F1 no es un homónimo de `ConsistentH` ni de `Prf`. -/
#print ROBINSON_PlusPlus.Meta.Representability2Prf.AnclaEq
#check @ROBINSON_PlusPlus.Meta.GodelTwoPrf.goedel_first_prf
#check @ROBINSON_PlusPlus.Meta.GodelTwoPrf.goedel_second_prf

open ROBINSON_PlusPlus.Meta.GodelTwoPrf ROBINSON_PlusPlus.Meta.ProofChain ROBINSON_PlusPlus.Meta.GodelTwo in
/-- El MISMO `hcon` alimenta a `goedel_first_prf` (luego es de su tipo) y a `absurd` contra
    `anclaEq_prf_bot` (luego es `¬ Prf ⊥` del MISMO `Prf`). Si las constantes difirieran, no compilaría. -/
theorem verif_g1_vacuo [inst : ROBINSON_PlusPlus.Meta.Representability2Prf.AnclaEq] (hcon : ConsistentH) :
    And (¬ ROBINSON_PlusPlus.Meta.Hilbert.Prf godelCN) (ROBINSON_PlusPlus.Meta.Hilbert.Prf godelCN) :=
  ⟨@goedel_first_prf inst hcon, absurd Sondeos.AnclaEqInconsistente.anclaEq_prf_bot hcon⟩

open ROBINSON_PlusPlus.Meta.GodelTwoPrf ROBINSON_PlusPlus.Meta.ProofChain ROBINSON_PlusPlus.Meta.GodelTwo in
theorem verif_g2_vacuo [inst : ROBINSON_PlusPlus.Meta.Representability2Prf.AnclaEq] (hcon : ConsistentH) :
    And (¬ ROBINSON_PlusPlus.Meta.Hilbert.Prf consistencyFormula') (ROBINSON_PlusPlus.Meta.Hilbert.Prf consistencyFormula') :=
  ⟨@goedel_second_prf inst hcon, absurd Sondeos.AnclaEqInconsistente.anclaEq_prf_bot hcon⟩

#print axioms verif_g1_vacuo
#print axioms verif_g2_vacuo
