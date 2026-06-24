/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.Hilbert
import ROBINSON_PlusPlus.Meta.Godel
import ROBINSON_PlusPlus.Meta.Provability

import FOL.FOL

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.HilbertSeq

/-!
## META — NIVEL D (real): demostraciones como secuencias  (Fase 1)

`Prf`/`Prf₀` son inductivos en `Prop`: sus términos son finitos, pero `Prop`
borra el contenido computacional, así que no se pueden inspeccionar/codificar.
Para aritmetizar la demostrabilidad necesitamos una representación de las
demostraciones como **datos finitos**: una lista de líneas, cada una justificada
por una **regla** (`Rule`).

Truco clave (estándar): en vez de comprobar "¿esta fórmula es una instancia del
esquema Q1?" —que exigiría *invertir* la sustitución— cada línea lleva su regla
y sus parámetros explícitos; el verificador `checkProof` solo **recomputa** la
fórmula de cada línea y la compara. Eso es **decidible** y **codificable**.

Resultados de la fase:
* `checkProof : List Rule → Option (List Formula)` — verificador decidible.
* `Proves rs φ` — `rs` es una demostración cuya última línea es `φ`.
* **Solidez** `proves_to_prf : Proves rs φ → Prf φ`.
* **Completitud** `prf_to_proves : Prf φ → ∃ rs, Proves rs φ`.
  Juntas: `Prf φ ↔ ∃ rs, Proves rs φ` (la demostrabilidad de Hilbert = existe
  una secuencia-demostración finita). Base para el `Dem` concreto (codificación).
-/

/- Igualdad decidible para términos y fórmulas (necesaria para el verificador:
   el paso MP compara fórmulas). `Term` es inductivo **anidado** (`func` lleva
   `List Term`), así que el handler automático de `DecidableEq` no aplica: lo
   damos a mano por recursión estructural mutua. `Formula` ya se deriva una vez
   `Term` tiene la instancia. -/
mutual
def decEqTerm : (a b : Term) → Decidable (a = b)
  | .var n, .var m => if h : n = m then isTrue (by rw [h]) else isFalse (by simp_all)
  | .var _, .func _ _ => isFalse (by simp_all)
  | .func _ _, .var _ => isFalse (by simp_all)
  | .func f ts, .func g us =>
      if hf : f = g then
        match decEqTerms ts us with
        | isTrue h => isTrue (by rw [hf, h])
        | isFalse h => isFalse (by simp_all)
      else isFalse (by simp_all)
def decEqTerms : (as bs : List Term) → Decidable (as = bs)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by simp_all)
  | _ :: _, [] => isFalse (by simp_all)
  | a :: as, b :: bs =>
      match decEqTerm a b with
      | isTrue h =>
          match decEqTerms as bs with
          | isTrue h2 => isTrue (by rw [h, h2])
          | isFalse h2 => isFalse (by simp_all)
      | isFalse h => isFalse (by simp_all)
end

instance : DecidableEq Term := decEqTerm

deriving instance DecidableEq for Formula

/-- **Regla de demostración**: justificación de una línea. Los esquemas de
    axiomas llevan sus parámetros (fórmulas/términos); `thy k` es el `k`-ésimo
    axioma de la teoría; `mp i j`/`gen i` refieren líneas **anteriores** por
    índice. Tipo finito → codificable como `Term` (Fase 1, parte de coding). -/
inductive Rule where
  | p1 (A B : Formula)
  | p2 (A B C : Formula)
  | c1 (A B : Formula)
  | c2 (A B : Formula)
  | c3 (A B : Formula)
  | j1 (A B : Formula)
  | j2 (A B : Formula)
  | j3 (A B C : Formula)
  | efq (A : Formula)
  | q1 (A : Formula) (t : Term)
  | q2 (A : Formula) (t : Term)
  | q3 (A B : Formula)
  | eqrefl (t : Term)
  | leibniz (A : Formula) (t₁ t₂ : Term)
  | p3 (A : Formula)
  | ind (A : Formula)
  | qconf (P C : Formula)
  | listInd (A : Formula)
  | thy (k : Nat)
  | mp (i j : Nat)
  | gen (i : Nat)

/-- Conclusión de un modus ponens: si `fi = (fj ⇒ b)` devuelve `b`, si no `none`.
    (Factorizado para que la solidez sea limpia.) -/
def mpConcl (fi fj : Formula) : Option Formula :=
  match fi with
  | Formula.impl a b => if a = fj then some b else none
  | _ => none

/-- Fórmula concluida por una regla, dadas las líneas anteriores `earlier`.
    `none` si la regla no es aplicable (índice fuera de rango, MP mal formado…). -/
def stepConcl (earlier : List Formula) : Rule → Option Formula
  | .p1 A B => some (A ⇒ (B ⇒ A))
  | .p2 A B C => some ((A ⇒ (B ⇒ C)) ⇒ ((A ⇒ B) ⇒ (A ⇒ C)))
  | .c1 A B => some (A ⇒ (B ⇒ (A ∧ B)))
  | .c2 A B => some ((A ∧ B) ⇒ A)
  | .c3 A B => some ((A ∧ B) ⇒ B)
  | .j1 A B => some (A ⇒ (A ∨ B))
  | .j2 A B => some (B ⇒ (A ∨ B))
  | .j3 A B C => some ((A ∨ B) ⇒ ((A ⇒ C) ⇒ ((B ⇒ C) ⇒ C)))
  | .efq A => some (⊥ ⇒ A)
  | .q1 A t => some ((Formula.forall A) ⇒ substFormula 0 t A)
  | .q2 A t => some (substFormula 0 t A ⇒ Formula.ex A)
  | .q3 A B => some ((Formula.forall (A ⇒ liftFormula 0 B)) ⇒ ((Formula.ex A) ⇒ B))
  | .eqrefl t => some (t ≐ t)
  | .leibniz A t₁ t₂ => some ((t₁ ≐ t₂) ⇒ (substFormula 0 t₁ A ⇒ substFormula 0 t₂ A))
  | .p3 A => some (((A ⇒ ⊥) ⇒ ⊥) ⇒ A)
  | .ind A => some (Full.inductionFormula A)
  | .qconf P C => some (confinementFormula P C)
  | .listInd A => some (listInductionFormula A)
  | .thy k => axioms[k]?
  | .mp i j => (earlier[i]?).bind (fun fi => (earlier[j]?).bind (fun fj => mpConcl fi fj))
  | .gen i => (earlier[i]?).map Formula.forall

/-- Verificador acumulativo: procesa las reglas en orden, anexando la conclusión
    de cada una. `acc` son las líneas ya validadas (índices estables por anexar
    al final). -/
def checkAux : List Rule → List Formula → Option (List Formula)
  | [], acc => some acc
  | r :: rs, acc =>
      match stepConcl acc r with
      | some f => checkAux rs (acc ++ [f])
      | none => none

/-- **Verificador de demostraciones**: `some L` (líneas) si `rs` es una
    demostración válida; `none` si alguna línea falla. Decidible por cómputo. -/
def checkProof (rs : List Rule) : Option (List Formula) := checkAux rs []

/-- `rs` es una **derivación que contiene `φ`**: el verificador acepta `rs` y `φ`
    aparece entre sus líneas. (Como cada línea es demostrable, `∃ rs, Derivation
    rs φ ↔ Prf φ`; usar "aparece" en vez de "última línea" simplifica la
    combinación de subpruebas en la completitud.) -/
def Derivation (rs : List Rule) (φ : Formula) : Prop :=
  ∃ L, And (checkProof rs = some L) (φ ∈ L)

/-! ### Solidez del verificador: `Proves rs φ → Prf φ` -/

/-- Si `mpConcl fi fj = some f` entonces `fi` es la implicación `fj ⇒ f`. -/
theorem mpConcl_eq {fi fj f : Formula} (h : mpConcl fi fj = some f) : fi = (fj ⇒ f) := by
  cases fi with
  | impl a b =>
      simp only [mpConcl] at h
      by_cases hab : a = fj
      · rw [if_pos hab, Option.some.injEq] at h; subst h; rw [hab]
      · rw [if_neg hab] at h; exact absurd h (by simp)
  | bottom => simp [mpConcl] at h
  | atom p ts => simp [mpConcl] at h
  | eq t u => simp [mpConcl] at h
  | «forall» a => simp [mpConcl] at h
  | and a b => simp [mpConcl] at h
  | or a b => simp [mpConcl] at h
  | ex a => simp [mpConcl] at h

/-- **Cada línea es demostrable**: si las anteriores (`acc`) lo son y la regla
    valida produciendo `f`, entonces `Prf f`. Es el corazón de la solidez. -/
theorem stepConcl_prf {acc : List Formula} {r : Rule} {f : Formula}
    (hacc : ∀ g ∈ acc, Prf g) (h : stepConcl acc r = some f) : Prf f := by
  cases r with
  | p1 A B => simp only [stepConcl, Option.some.injEq] at h; subst h; exact Prf.incl (Prf₀.p1 A B)
  | p2 A B C => simp only [stepConcl, Option.some.injEq] at h; subst h; exact Prf.incl (Prf₀.p2 A B C)
  | c1 A B => simp only [stepConcl, Option.some.injEq] at h; subst h; exact Prf.incl (Prf₀.c1 A B)
  | c2 A B => simp only [stepConcl, Option.some.injEq] at h; subst h; exact Prf.incl (Prf₀.c2 A B)
  | c3 A B => simp only [stepConcl, Option.some.injEq] at h; subst h; exact Prf.incl (Prf₀.c3 A B)
  | j1 A B => simp only [stepConcl, Option.some.injEq] at h; subst h; exact Prf.incl (Prf₀.j1 A B)
  | j2 A B => simp only [stepConcl, Option.some.injEq] at h; subst h; exact Prf.incl (Prf₀.j2 A B)
  | j3 A B C => simp only [stepConcl, Option.some.injEq] at h; subst h; exact Prf.incl (Prf₀.j3 A B C)
  | efq A => simp only [stepConcl, Option.some.injEq] at h; subst h; exact Prf.incl (Prf₀.efq A)
  | q1 A t => simp only [stepConcl, Option.some.injEq] at h; subst h; exact Prf.incl (Prf₀.q1 A t)
  | q2 A t => simp only [stepConcl, Option.some.injEq] at h; subst h; exact Prf.incl (Prf₀.q2 A t)
  | q3 A B => simp only [stepConcl, Option.some.injEq] at h; subst h; exact Prf.incl (Prf₀.q3 A B)
  | eqrefl t => simp only [stepConcl, Option.some.injEq] at h; subst h; exact Prf.incl (Prf₀.eqrefl t)
  | leibniz A t₁ t₂ =>
      simp only [stepConcl, Option.some.injEq] at h; subst h; exact Prf.incl (Prf₀.leibniz A t₁ t₂)
  | p3 A => simp only [stepConcl, Option.some.injEq] at h; subst h; exact Prf.p3 A
  | ind A => simp only [stepConcl, Option.some.injEq] at h; subst h; exact Prf.ind A
  | qconf P C => simp only [stepConcl, Option.some.injEq] at h; subst h; exact Prf.qconf P C
  | listInd A => simp only [stepConcl, Option.some.injEq] at h; subst h; exact Prf.listInd A
  | thy k =>
      simp only [stepConcl] at h
      exact Prf.incl (Prf₀.thy f (List.mem_of_getElem? h))
  | mp i j =>
      simp only [stepConcl] at h
      cases hi : acc[i]? with
      | none => rw [hi] at h; simp at h
      | some fi =>
          cases hj : acc[j]? with
          | none => rw [hi, hj] at h; simp at h
          | some fj =>
              rw [hi, hj] at h
              change mpConcl fi fj = some f at h
              have hfi : Prf fi := hacc _ (List.mem_of_getElem? hi)
              have hfj : Prf fj := hacc _ (List.mem_of_getElem? hj)
              rw [mpConcl_eq h] at hfi
              exact Prf.mp fj f hfi hfj
  | gen i =>
      simp only [stepConcl] at h
      cases hi : acc[i]? with
      | none => rw [hi] at h; simp at h
      | some g =>
          rw [hi] at h
          change some (Formula.forall g) = some f at h
          simp only [Option.some.injEq] at h; subst h
          exact Prf.gen g (hacc _ (List.mem_of_getElem? hi))

/-- Invariante de `checkAux`: si todas las líneas de `acc` son demostrables y el
    verificador termina con `L`, todas las de `L` lo son. -/
theorem checkAux_mem_prf {rs : List Rule} {acc L : List Formula}
    (hacc : ∀ g ∈ acc, Prf g) (h : checkAux rs acc = some L) :
    ∀ g ∈ L, Prf g := by
  induction rs generalizing acc with
  | nil => simp only [checkAux, Option.some.injEq] at h; subst h; exact hacc
  | cons r rs ih =>
      simp only [checkAux] at h
      cases hstep : stepConcl acc r with
      | none => rw [hstep] at h; simp at h
      | some f =>
          rw [hstep] at h
          have hnew : ∀ g ∈ acc ++ [f], Prf g := by
            intro g hg
            rcases List.mem_append.mp hg with hg | hg
            · exact hacc g hg
            · rw [List.mem_singleton] at hg; subst hg; exact stepConcl_prf hacc hstep
          exact ih hnew h

/-- **Solidez del verificador**: toda derivación-secuencia válida da un teorema
    de Hilbert `Prf`. -/
theorem derivation_to_prf {rs : List Rule} {φ : Formula} (h : Derivation rs φ) : Prf φ := by
  obtain ⟨L, hchk, hmem⟩ := h
  unfold checkProof at hchk
  exact checkAux_mem_prf (by intro g hg; simp at hg) hchk φ hmem

/-! ### Completitud del verificador: `Prf φ → ∃ rs, Derivation rs φ` -/

/-- Desplaza los índices de línea (MP/GEN) en `n`; los esquemas de axioma y `thy`
    no dependen del contexto, quedan igual. -/
def shiftRule (n : Nat) : Rule → Rule
  | .mp i j => .mp (i + n) (j + n)
  | .gen i => .gen (i + n)
  | r => r

/-- Invarianza de `stepConcl` al anteponer contexto `pre` y desplazar índices. -/
theorem stepConcl_shift (pre acc : List Formula) (r : Rule) :
    stepConcl (pre ++ acc) (shiftRule pre.length r) = stepConcl acc r := by
  cases r <;>
    first
      | rfl
      | simp [shiftRule, stepConcl, List.getElem?_append_right, Nat.le_add_left,
          Nat.add_sub_cancel]

/-- `checkAux` es compositivo bajo concatenación de reglas. -/
theorem checkAux_append : ∀ (rs1 rs2 : List Rule) (acc : List Formula),
    checkAux (rs1 ++ rs2) acc = (checkAux rs1 acc).bind (fun L => checkAux rs2 L)
  | [], rs2, acc => by simp [checkAux]
  | r :: rs1, rs2, acc => by
      simp only [List.cons_append, checkAux]
      cases hstep : stepConcl acc r with
      | none => rfl
      | some f => exact checkAux_append rs1 rs2 (acc ++ [f])

/-- Correr reglas desplazadas sobre un contexto `pre` antepuesto. -/
theorem checkAux_shift : ∀ (rs : List Rule) (pre acc : List Formula),
    checkAux (rs.map (shiftRule pre.length)) (pre ++ acc)
      = (checkAux rs acc).map (fun L => pre ++ L)
  | [], pre, acc => by simp [checkAux]
  | r :: rs, pre, acc => by
      simp only [List.map_cons, checkAux]
      rw [stepConcl_shift]
      cases hstep : stepConcl acc r with
      | none => rfl
      | some f =>
          show checkAux (rs.map (shiftRule pre.length)) (pre ++ acc ++ [f])
            = Option.map (fun L => pre ++ L) (checkAux rs (acc ++ [f]))
          rw [List.append_assoc]
          exact checkAux_shift rs pre (acc ++ [f])

/-- Una sola regla que concluye `φ` (sin premisas anteriores) es una derivación. -/
theorem derivation_single {r : Rule} {φ : Formula} (h : stepConcl [] r = some φ) :
    Derivation [r] φ := by
  refine ⟨[φ], ?_, by simp⟩
  unfold checkProof
  simp only [checkAux]
  rw [h]
  rfl

/-- Combinador **GEN**: de una derivación de `A` sale una de `∀A`. -/
theorem combine_gen {rs1 : List Rule} {A : Formula} (h : Derivation rs1 A) :
    ∃ rs, Derivation rs (Formula.forall A) := by
  obtain ⟨L1, hchk1, hmem1⟩ := h
  obtain ⟨i, hi, hgeti⟩ := List.getElem_of_mem hmem1
  have hidx : L1[i]? = some A := by rw [List.getElem?_eq_getElem hi, hgeti]
  refine ⟨rs1 ++ [Rule.gen i], L1 ++ [Formula.forall A], ?_, by simp⟩
  unfold checkProof at hchk1 ⊢
  rw [checkAux_append, hchk1]
  show checkAux [Rule.gen i] L1 = some (L1 ++ [Formula.forall A])
  simp [checkAux, stepConcl, hidx]

/-- Combinador **MP**: de derivaciones de `A ⇒ B` y `A` sale una de `B`. -/
theorem combine_mp {rs1 rs2 : List Rule} {A B : Formula}
    (h1 : Derivation rs1 (A ⇒ B)) (h2 : Derivation rs2 A) :
    ∃ rs, Derivation rs B := by
  obtain ⟨L1, hchk1, hmem1⟩ := h1
  obtain ⟨L2, hchk2, hmem2⟩ := h2
  obtain ⟨i, hi, hgeti⟩ := List.getElem_of_mem hmem1
  obtain ⟨j, hj, hgetj⟩ := List.getElem_of_mem hmem2
  have hidxi : (L1 ++ L2)[i]? = some (A ⇒ B) := by
    rw [List.getElem?_append_left hi, List.getElem?_eq_getElem hi, hgeti]
  have hidxj : (L1 ++ L2)[L1.length + j]? = some A := by
    rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
        List.getElem?_eq_getElem hj, hgetj]
  unfold checkProof at hchk1 hchk2
  have hshift : checkAux (rs2.map (shiftRule L1.length)) L1 = some (L1 ++ L2) := by
    have hs := checkAux_shift rs2 L1 []
    rw [List.append_nil] at hs
    rw [hs, hchk2]; rfl
  refine ⟨rs1 ++ rs2.map (shiftRule L1.length) ++ [Rule.mp i (L1.length + j)],
          (L1 ++ L2) ++ [B], ?_, by simp⟩
  unfold checkProof
  rw [checkAux_append, checkAux_append, hchk1]
  show (checkAux (rs2.map (shiftRule L1.length)) L1).bind
      (fun L => checkAux [Rule.mp i (L1.length + j)] L) = some (L1 ++ L2 ++ [B])
  rw [hshift]
  show checkAux [Rule.mp i (L1.length + j)] (L1 ++ L2) = some (L1 ++ L2 ++ [B])
  simp [checkAux, stepConcl, hidxi, hidxj, mpConcl]

/-- Completitud para la capa intuicionista. -/
theorem prf0_to_derivation {φ : Formula} (h : Prf₀ φ) : ∃ rs, Derivation rs φ := by
  induction h with
  | p1 A B => exact ⟨_, derivation_single (r := Rule.p1 A B) rfl⟩
  | p2 A B C => exact ⟨_, derivation_single (r := Rule.p2 A B C) rfl⟩
  | c1 A B => exact ⟨_, derivation_single (r := Rule.c1 A B) rfl⟩
  | c2 A B => exact ⟨_, derivation_single (r := Rule.c2 A B) rfl⟩
  | c3 A B => exact ⟨_, derivation_single (r := Rule.c3 A B) rfl⟩
  | j1 A B => exact ⟨_, derivation_single (r := Rule.j1 A B) rfl⟩
  | j2 A B => exact ⟨_, derivation_single (r := Rule.j2 A B) rfl⟩
  | j3 A B C => exact ⟨_, derivation_single (r := Rule.j3 A B C) rfl⟩
  | efq A => exact ⟨_, derivation_single (r := Rule.efq A) rfl⟩
  | q1 A t => exact ⟨_, derivation_single (r := Rule.q1 A t) rfl⟩
  | q2 A t => exact ⟨_, derivation_single (r := Rule.q2 A t) rfl⟩
  | q3 A B => exact ⟨_, derivation_single (r := Rule.q3 A B) rfl⟩
  | eqrefl t => exact ⟨_, derivation_single (r := Rule.eqrefl t) rfl⟩
  | leibniz A t₁ t₂ => exact ⟨_, derivation_single (r := Rule.leibniz A t₁ t₂) rfl⟩
  | thy a ha =>
      obtain ⟨k, hk, hget⟩ := List.getElem_of_mem ha
      refine ⟨_, derivation_single (r := Rule.thy k) ?_⟩
      simp only [stepConcl]
      rw [List.getElem?_eq_getElem hk, hget]
  | mp A B _ _ ih1 ih2 =>
      obtain ⟨rs1, hd1⟩ := ih1
      obtain ⟨rs2, hd2⟩ := ih2
      exact combine_mp hd1 hd2
  | gen A _ ih =>
      obtain ⟨rs1, hd1⟩ := ih
      exact combine_gen hd1

/-- **Completitud del verificador**: todo teorema de Hilbert `Prf` admite una
    derivación-secuencia. Junto con `derivation_to_prf`:
    `Prf φ ↔ ∃ rs, Derivation rs φ`. -/
theorem prf_to_derivation {φ : Formula} (h : Prf φ) : ∃ rs, Derivation rs φ := by
  induction h with
  | incl h0 => exact prf0_to_derivation h0
  | p3 A => exact ⟨_, derivation_single (r := Rule.p3 A) rfl⟩
  | ind A => exact ⟨_, derivation_single (r := Rule.ind A) rfl⟩
  | qconf P C => exact ⟨_, derivation_single (r := Rule.qconf P C) rfl⟩
  | listInd A => exact ⟨_, derivation_single (r := Rule.listInd A) rfl⟩
  | mp A B _ _ ih1 ih2 =>
      obtain ⟨rs1, hd1⟩ := ih1
      obtain ⟨rs2, hd2⟩ := ih2
      exact combine_mp hd1 hd2
  | gen A _ ih =>
      obtain ⟨rs1, hd1⟩ := ih
      exact combine_gen hd1

/-- **Equivalencia** (núcleo de la Fase 1): la demostrabilidad de Hilbert
    coincide con la existencia de una derivación-secuencia finita y verificable.
    Esta es la versión "datos" de `Prf`, base para el `Dem` concreto (coding). -/
theorem prf_iff_derivation {φ : Formula} : Prf φ ↔ ∃ rs, Derivation rs φ :=
  ⟨prf_to_derivation, fun ⟨_, hd⟩ => derivation_to_prf hd⟩

/-! ### Codificación de Gödel de las demostraciones y `Dem` concreto  (Fase 1c)

Cada `Rule` se codifica como `⟨tag, payload…⟩` (con `cons`/`nil`/`numeral` y los
codificadores `formCode`/`termCode` de `Meta/Provability.lean`); una `List Rule`
como una lista codificada. Con eso definimos `Dem d x` **concreta** (reemplaza el
postulado opaco): "`d` es el código de una derivación-secuencia en la que aparece
la fórmula de código `x`". El tracking `(∃ d, Dem d ⌜φ⌝) ↔ Prf φ` sale de
`prf_iff_derivation` + `formCode_injective`; no requiere decodificador (la forma
Δ₀/decidible pertenece a la Fase 2, donde se construye el objeto `demFormula`). -/

/-- Código de Gödel de una regla: `⟨tag, args codificados…⟩`. -/
def ruleCode : Rule → Term
  | .p1 A B => cons (numeral 0) (cons (formCode A) (cons (formCode B) nil))
  | .p2 A B C => cons (numeral 1) (cons (formCode A) (cons (formCode B) (cons (formCode C) nil)))
  | .c1 A B => cons (numeral 2) (cons (formCode A) (cons (formCode B) nil))
  | .c2 A B => cons (numeral 3) (cons (formCode A) (cons (formCode B) nil))
  | .c3 A B => cons (numeral 4) (cons (formCode A) (cons (formCode B) nil))
  | .j1 A B => cons (numeral 5) (cons (formCode A) (cons (formCode B) nil))
  | .j2 A B => cons (numeral 6) (cons (formCode A) (cons (formCode B) nil))
  | .j3 A B C => cons (numeral 7) (cons (formCode A) (cons (formCode B) (cons (formCode C) nil)))
  | .efq A => cons (numeral 8) (cons (formCode A) nil)
  | .q1 A t => cons (numeral 9) (cons (formCode A) (cons (termCode t) nil))
  | .q2 A t => cons (numeral 10) (cons (formCode A) (cons (termCode t) nil))
  | .q3 A B => cons (numeral 11) (cons (formCode A) (cons (formCode B) nil))
  | .eqrefl t => cons (numeral 12) (cons (termCode t) nil)
  | .leibniz A t₁ t₂ =>
      cons (numeral 13) (cons (formCode A) (cons (termCode t₁) (cons (termCode t₂) nil)))
  | .p3 A => cons (numeral 14) (cons (formCode A) nil)
  | .ind A => cons (numeral 18) (cons (formCode A) nil)
  | .qconf P C => cons (numeral 19) (cons (formCode P) (cons (formCode C) nil))
  | .listInd A => cons (numeral 20) (cons (formCode A) nil)
  -- La línea `thy` TRANSPORTA el código del axioma (no el índice `k`). `thy`
  -- recorre `coreAxioms` (la teoría matemática), no las ecuaciones de coding (ver
  -- `ax_vpf_thy` y GODEL-D-ARITHMETIZATION §7). En una derivación válida `k` está
  -- en rango, luego `coreAxioms.getD k ⊥ = coreAxioms[k]` = la conclusión real.
  | .thy k => cons (numeral 15) (cons (formCode (axioms.getD k Formula.bottom)) nil)
  | .mp i j => cons (numeral 16) (cons (numeral i) (cons (numeral j) nil))
  | .gen i => cons (numeral 17) (cons (numeral i) nil)

/-- Código de Gödel de una demostración-secuencia (lista de reglas). -/
def rulesCode : List Rule → Term
  | [] => nil
  | r :: rs => cons (ruleCode r) (rulesCode rs)

/-- **Predicado de demostración concreto** `Dem d x`: `d` es el código de una
    derivación-secuencia válida en la que aparece la fórmula de código `x`.
    Reemplaza el `Dem` postulado de `Meta/Provability.lean`. -/
def Dem (d x : Term) : Prop :=
  ∃ rs : List Rule, ∃ φ : Formula,
    And (d = rulesCode rs) (And (x = formCode φ) (Derivation rs φ))

/-- **Demostrabilidad codificada**: existe un código de demostración de `x`. -/
def ProvableH (x : Term) : Prop := ∃ d : Term, Dem d x

/-- **Tracking (fidelidad del `Dem` concreto)**: la demostrabilidad codificada de
    `⌜φ⌝` coincide con la demostrabilidad de Hilbert `Prf φ`. Reemplaza el
    postulado `dem_iff_provable` (restringido a `⊢ᴴ`). -/
theorem dem_tracks (φ : Formula) : ProvableH (formCode φ) ↔ Prf φ := by
  unfold ProvableH Dem
  rw [prf_iff_derivation]
  constructor
  · rintro ⟨_, rs, ψ, _, hx, hder⟩
    rw [formCode_injective hx]
    exact ⟨rs, hder⟩
  · rintro ⟨rs, hder⟩
    exact ⟨rulesCode rs, rs, φ, rfl, rfl, hder⟩

end ROBINSON_PlusPlus.Meta.HilbertSeq
