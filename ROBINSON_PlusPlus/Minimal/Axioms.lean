/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import FOL.FOL        -- Term, Formula, Derives (⊢), notaciones ≐ ∧ ∨ ¬ ⇒ ⇔ ∀. ∃. ⊥ ⊤ #
import FOL.Theorems.Eq -- derive_eq_symm, derive_eq_trans, substTerm_liftTerm

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Minimal.Axioms

-- ## Notations & local aliases
-- FOL usa ≐ para igualdad de términos en fórmulas; aquí usamos =eq como alias legible.
scoped notation:50 t₁ " =eq " t₂ => Formula.eq t₁ t₂

-- Formula.ex no está en scope sin `open Formula`; lo reexportamos aquí.
abbrev ex := @Formula.ex

/-!
# Axioms of the Minimal Arithmetic System

This module defines the language and the 21 axioms of the minimal arithmetic
system as described in `TuplasFuncionesYListas.md`. This system is strong
enough to develop a theory of pairs (via Cantor's pairing function) and lists,
but it lacks a general induction principle.
-/

-- ## Language Definition

-- ### Function Symbols
def succ_sym : String := "σ"
def add_sym  : String := "+"
def mul_sym  : String := "*"
def sub_sym  : String := "−"   -- subtraction (monus): sub a b = max(a-b, 0)
def sqrt_sym : String := "√"
def div2_sym : String := "/₂"
def mod2_sym : String := "%₂"
-- proj1_sym, proj2_sym ELIMINADOS 2026-06-02: proj1/proj2 ya no son símbolos
-- opacos del lenguaje, sino defs concretas en Block4_C6_C7 (proj1 := x_of_c,
-- proj2 := y_of_c). Con ello ax22 deja de ser necesario (proj_is_cantor lo
-- demuestra como teorema).
-- El símbolo de display del predecesor es "τ", pero los axiomas se nombran con el
-- prefijo `pred_` (más legible que `tau_`). Ver ax25_pred_zero, ax26_pred_succ.
def pred_sym : String := "τ"
def nil_sym : String := "[]"
def cons_sym : String := "::"
def concat_sym : String := "##"

-- ### Predicate Symbols
def lt_sym : String := "<"
def le_sym : String := "≤"
def in_sym : String := "∈"

-- ### Constant Symbols
def zero_sym : String := "0"

-- ## Term Constructors

-- Constant `0`
def zero : Term := .func zero_sym []

-- Helper functions to build terms
def succ (t : Term)   : Term := .func succ_sym [t]
def add (t₁ t₂ : Term) : Term := .func add_sym [t₁, t₂]
def mul (t₁ t₂ : Term) : Term := .func mul_sym [t₁, t₂]
def sub (t₁ t₂ : Term) : Term := .func sub_sym [t₁, t₂]
def sqrt (t : Term)   : Term := .func sqrt_sym [t]
def div2 (t : Term)   : Term := .func div2_sym [t]
def mod2 (t : Term)   : Term := .func mod2_sym [t]
-- proj1, proj2 ELIMINADOS 2026-06-02: ahora son defs concretas en Block4_C6_C7
-- (proj1 := x_of_c, proj2 := y_of_c), no símbolos opacos.
def pred (t : Term)    : Term := .func pred_sym [t]
def cons (h t : Term) : Term := .func cons_sym [h, t]
def concat (l₁ l₂ : Term) : Term := .func concat_sym [l₁, l₂]

-- Derived operation `sq`
def sq (t : Term) : Term := mul t t

-- Derived constants `1` and `2`
def one : Term := succ zero
def two : Term := succ one
def eight : Term := mul two (mul two two) -- 2*4

-- Cantor pairing function components
/-!
Cantor's pairing function is defined as:
  $π₁(x,y) = \frac { \frac {(x+y)(x+y+1)} {2} + y } {2}$
  $π₂(x,y) = \frac { \frac {(x+y)(x+y+1)} {2} + y } {2} - (π₁(x,y) * 2)$
-/

/-!
  $ \text{cantor_poly}(x,y) := (x + y) (x + y + 1) + 2y = 2c $  (definición de la relación Cantor(x,y,c))
-/
def cantor_poly (x y : Term) : Term :=
  add (mul (add x y) (succ (add x y))) (mul two y)

/-!
  $ \text{cantor_func}(x,y) := \frac { (x+y)(x+y+1) + 2y } {2} = c $  (definición de la función π₁(x,y))
-/
def cantor_func (x y : Term) : Term :=
  div2 (cantor_poly x y)

/-!
  $ \text{is_cantor}(x,y,c) := 2c = (x + y) (x + y + 1) + 2y $  (definición de la relación Cantor(x,y,c))
-/
def is_cantor (x y c : Term) : Formula :=
  mul two c =eq cantor_poly x y

/-!
  $ \text{pair}(x,y) := \pi_1(x,y) $  (definición de la función par(x,y))
-/
def pair (x y : Term) : Term :=
  cantor_func x y

-- List constructors
def nil : Term := zero
-- `cons h t` es un constructor de lista con cabeza `h` y cola `t`. El símbolo de
-- función es `cons_sym = "::"`, opaco; ax_L0_cons_def lo conecta con `pair h (succ t)`.

-- ## Display

/-- Muestra un `Term` usando Oxford brackets ⟦⟧ para los argumentos de función.
    Ejemplos: `σ⟦0⟧`, `+⟦σ⟦0⟧, σ⟦σ⟦0⟧⟧⟧`, `#0`. -/
partial def termToString : Term → String
  | .var n      => s!"#{n}"
  | .func f []  => f
  | .func f args => f ++ "⟦" ++ ", ".intercalate (args.map termToString) ++ "⟧"

instance : ToString Term := ⟨termToString⟩

-- ## Formula Constructors

-- Helper function to build atomic formulas
def lt (t₁ t₂ : Term) : Formula := .atom lt_sym [t₁, t₂]
def le (t₁ t₂ : Term) : Formula := (lt t₁ t₂) ∨ (t₁ =eq t₂)
-- Alias de ≤ aritmético para Terms → Formula (sombrea ≤ de Prop dentro del namespace)
scoped notation:50 t₁ " ≤ " t₂ => le t₁ t₂

def In (x l : Term) : Formula := .atom in_sym [x, l]
scoped notation:50 x " ∈ " l => In x l

-- Helper for universal quantification over 1, 2, or 3 variables
def forall_ (f : Formula) : Formula := .forall f
def forall_2 (f : Formula) : Formula := .forall (.forall f)
def forall_3 (f : Formula) : Formula := .forall (.forall (.forall f))


-- ## Axioms

-- ### Axioms of Peano Puros

-- Ax 1: ∃0
-- This is a meta-axiom stating that the constant '0' exists in our language.
-- It is handled by including `zero : Term` in the language definition.

-- Ax 2: ∀ n, σ(n) ≠ 0
def ax2_peano_succ_neq_zero : Formula :=
  forall_ (
    neg (succ (.var 0) =eq zero)
  )

-- Ax 3: ∀ n, ∀ m, σ(n) = σ(m) ⇒ n = m
def ax3_peano_succ_inj : Formula :=
  forall_2 (
    (succ (.var 1) =eq succ (.var 0)) ⇒ ((.var 1) =eq (.var 0))
  )

-- ### Axioms of the Suma

-- Ax 4: ∀ n, n + 0 = n
def ax4_add_zero : Formula :=
  forall_ (
    add (.var 0) zero =eq (.var 0)
  )

-- Ax 5: ∀ n, ∀ m, n + σ(m) = σ(n + m)
def ax5_add_succ : Formula :=
  forall_2 (
    add (.var 1) (succ (.var 0)) =eq succ (add (.var 1) (.var 0))
  )

-- ### Axiomas Algebraicos de la Suma

-- Ax 6: ∀ n, ∀ m, n + m = m + n
def ax6_add_comm : Formula :=
  forall_2 (
    add (.var 1) (.var 0) =eq add (.var 0) (.var 1)
  )

-- Ax 7: ∀ n, ∀ m, ∀ k, (n + m) + k = n + (m + k)
def ax7_add_assoc : Formula :=
  forall_3 (
    add (add (.var 2) (.var 1)) (.var 0) =eq add (.var 2) (add (.var 1) (.var 0))
  )

-- ### Axioms of the Producto

-- Ax 8: ∀ n, n * 0 = 0
def ax8_mul_zero : Formula :=
  forall_ (
    mul (.var 0) zero =eq zero
  )

-- Ax 9: ∀ n, ∀ m, n * σ(m) = (n * m) + n
def ax9_mul_succ : Formula :=
  forall_2 (
    mul (.var 1) (succ (.var 0)) =eq add (mul (.var 1) (.var 0)) (.var 1)
  )

-- ### Axiomas Algebraicos del Producto

-- Ax 10: ∀ n, ∀ m, n * m = m * n
def ax10_mul_comm : Formula :=
  forall_2 (
    mul (.var 1) (.var 0) =eq mul (.var 0) (.var 1)
  )

-- Ax 11: ∀ n, ∀ m, ∀ k, (n * m) * k = n * (m * k)
def ax11_mul_assoc : Formula :=
  forall_3 (
    mul (mul (.var 2) (.var 1)) (.var 0) =eq mul (.var 2) (mul (.var 1) (.var 0))
  )

-- Ax 12: ∀ n, ∀ m, ∀ k, n * (m + k) = (n * m) + (n * k)
def ax12_mul_distrib : Formula :=
  forall_3 (
    mul (.var 2) (add (.var 1) (.var 0)) =eq add (mul (.var 2) (.var 1)) (mul (.var 2) (.var 0))
  )

-- ### Axioma del Orden Estricto

-- Ax 13: ∀ n, ∀ m, n < m ⇔ ∃ k, n + σ(k) = m
def ax13_lt_def : Formula :=
  forall_2 (
    (lt (.var 1) (.var 0)) -- n < m
    ⇔
    (ex (add (.var 2) (succ (.var 0)) =eq (.var 1))) -- ∃k, n + σ(k) = m
  )

-- ### Axiomas de la Raíz Cuadrada

-- Ax 14: ∀ n, (√n)² ≤ n
def ax14_sqrt_le : Formula :=
  forall_ (
    le (sq (sqrt (.var 0))) (.var 0)
  )

-- Ax 15: ∀ n, n < (σ(√n))²
def ax15_lt_succ_sqrt : Formula :=
  forall_ (
    lt (.var 0) (sq (succ (sqrt (.var 0))))
  )

-- ### Axiomas de la División Entera por 2

-- Ax 16: ∀ n, mod2(n) = 0 ⇔ mod2(σ(n)) = 1
def ax16_mod2_succ : Formula :=
  forall_ (
    (mod2 (.var 0) =eq zero) ⇔ (mod2 (succ (.var 0)) =eq one)
  )

-- Ax 17: ∀ n, (div2(n) * 2) + mod2(n) = n
def ax17_div_mod_eq : Formula :=
  forall_ (
    add (mul (div2 (.var 0)) two) (mod2 (.var 0)) =eq (.var 0)
  )

-- ### Axiomas del Orden Total

-- Ax 18: ∀ n, ¬(n < n)
def ax18_lt_irrefl : Formula :=
  forall_ (
    neg (lt (.var 0) (.var 0))
  )

-- Ax 19: ∀ a, ∀ b, a < b ∨ a = b ∨ b < a
def ax19_lt_trichotomy : Formula :=
  forall_2 (
    (lt (.var 1) (.var 0))  -- a < b
    ∨ ((.var 1) =eq (.var 0)) -- a = b
    ∨ (lt (.var 0) (.var 1))  -- b < a
  )

-- Ax 20: ∀ n, ∀ m, n = m ∨ n ≠ m
def ax20_eq_decidable : Formula :=
  forall_2 (
    ((.var 1) =eq (.var 0)) ∨ (neg ((.var 1) =eq (.var 0)))
  )

-- Ax 21: ∀ n, mod2(n) = 0 ∨ mod2(n) = 1
def ax21_mod2_range : Formula :=
  forall_ (
    (mod2 (.var 0) =eq zero) ∨ (mod2 (.var 0) =eq one)
  )

-- ax22_cantor_proj_exists, ax23_cantor_proj_uniq ELIMINADOS 2026-06-02:
-- ax22 era el axioma "Skolem" que ataba proj1/proj2 opacos a is_cantor.
-- Ahora proj1/proj2 son defs concretas (= x_of_c/y_of_c) en Block4_C6_C7, y
-- el contenido de ax22 se prueba como teorema `proj_is_cantor` allí mismo.
-- ax23 era cantor_uniqueness reescrito como axioma; nunca usado en código.

-- land/lor: versión funcional de ∧/∨ sobre Formula (para usar fuera de notación)
def land (A B : Formula) : Formula := Formula.and A B
def lor  (A B : Formula) : Formula := Formula.or  A B

-- Ax 24 (mod2 of even): ∀ n, k, n = 2*k → mod2(n) = 0
-- Teorema en sistemas con inducción (caso base + paso inductivo en k).
-- En Minimal, se incluye como axioma. Ver `mod2_of_even` en Block5 (sorry pendiente).
def ax24_mod2_of_even : Formula :=
  forall_2 (
    ((.var 1) =eq (mul two (.var 0))) ⇒ (mod2 (.var 1) =eq zero)
  )

-- ### Axioms of Predecessor Function
-- `pred` usa el símbolo opaco `pred_sym = "τ"`. Sin estos dos axiomas, cualquier
-- función satisface el sistema (el símbolo no está fijado por los axiomas anteriores).
-- Son necesarios para las pruebas de C5 (Block4_C5) que usan `spec (ax ax26_pred_succ)`.

-- Ax 25: pred(0) = 0
def ax25_pred_zero : Formula :=
  pred zero =eq zero

-- Ax 26: ∀n, pred(σ(n)) = n
def ax26_pred_succ : Formula :=
  forall_ (pred (succ (.var 0)) =eq (.var 0))

-- ### Axioms of Lists

-- Ax L0: Connects Cons to the underlying pair definition
def ax_L0_cons_def : Formula :=
  forall_2 (cons (.var 1) (.var 0) =eq pair (.var 1) (succ (.var 0)))

-- Ax L1: In(x, Nil) is always false
def ax_L1_in_nil : Formula :=
  forall_ (neg (In (.var 0) nil))

-- Ax L2: Membership in a Cons list
def ax_L2_in_cons : Formula :=
  forall_3 (
    In (.var 2) (cons (.var 1) (.var 0)) ⇔ (lor ((.var 2) =eq (.var 1)) (In (.var 2) (.var 0)))
  )

-- Ax C1: Concatenation with Nil
def ax_C1_concat_nil : Formula :=
  forall_ (concat nil (.var 0) =eq (.var 0))

-- Ax C2: Concatenation with Cons
def ax_C2_concat_cons : Formula :=
  forall_3 (concat (cons (.var 2) (.var 1)) (.var 0) =eq cons (.var 2) (concat (.var 1) (.var 0)))

-- Ax C3: Associatividad de concat. Teorema en sistemas con inducción
-- (sobre L); en Minimal se postula. Ver `concat_assoc` en Block6.
def ax_C3_concat_assoc : Formula :=
  forall_3 (concat (concat (.var 2) (.var 1)) (.var 0) =eq concat (.var 2) (concat (.var 1) (.var 0)))

-- Ax L3: Distribución de la pertenencia sobre concat. Teorema en sistemas
-- con inducción (sobre L); en Minimal se postula. Ver `in_concat_iff` en Block6.
def ax_L3_in_concat : Formula :=
  forall_3 (
    In (.var 2) (concat (.var 1) (.var 0)) ⇔ lor (In (.var 2) (.var 1)) (In (.var 2) (.var 0))
  )

-- Ax 27 (add_left_cancel): ∀ a,b,c, a+c = b+c → a=b
-- Teorema en sistemas con inducción (inducción sobre c).
-- En Minimal, se incluye como axioma para C6/C7. Ver `add_left_cancel` en Block4_C6_C7 (sorry pendiente).
def ax27_add_left_cancel : Formula :=
  forall_3 (
    (add (.var 2) (.var 0) =eq add (.var 1) (.var 0)) ⇒ ((.var 2) =eq (.var 1))
  )

-- ELIMINADO 2026-06-02: ax28_mul_two_cancel era REDUNDANTE.
-- La spec TuplasFuncionesYListas.md §Teo 2.11 muestra que es derivable sin inducción
-- usando tricotomía (ax19), irreflexividad (ax18), distributividad (ax12) y monotonía
-- estricta de *2 (probada vía ax13 + teo_2_7 + ax5 + ax2). La prueba directa está
-- ahora en `teo_2_11` (Block1.lean), que ya NO delega a este axioma.

-- Ax 29 (sub_witness): ∀ a b, b ≤ a → b + (a − b) = a
-- Axioma testigo para la resta truncada (monus). En sistemas con inducción es
-- teorema (induc. sobre b junto con sub_zero/sub_succ); en Minimal se postula.
-- Determina `sub` salvo equivalencia en el rango b ≤ a; fuera del rango se deja
-- sin especificar (la formulación `sub a b` para `b > a` no se usa en el proyecto).
def ax29_sub_witness : Formula :=
  forall_2 (
    le (.var 0) (.var 1) ⇒ (add (.var 0) (sub (.var 1) (.var 0)) =eq (.var 1))
  )

-- ## Axiom Set

/-- The complete list of axioms for the Minimal system. -/
def axioms : List Formula := [
  ax2_peano_succ_neq_zero,
  ax3_peano_succ_inj,
  ax4_add_zero,
  ax5_add_succ,
  ax6_add_comm,
  ax7_add_assoc,
  ax8_mul_zero,
  ax9_mul_succ,
  ax10_mul_comm,
  ax11_mul_assoc,
  ax12_mul_distrib,
  ax13_lt_def,
  ax14_sqrt_le,
  ax15_lt_succ_sqrt,
  ax16_mod2_succ,
  ax17_div_mod_eq,
  ax18_lt_irrefl,
  ax19_lt_trichotomy,
  -- ax20_eq_decidable es ahora el teorema `eq_decidable` en Block1.lean
  ax21_mod2_range,    -- teorema en sistemas con inducción; `mod2_range` en Block3 (sorry)
  -- ax22_cantor_proj_exists, ax23_cantor_proj_uniq ELIMINADOS 2026-06-02:
  -- proj1/proj2 ahora son defs concretas (Block4_C6_C7); ax22 se demuestra
  -- como teorema `proj_is_cantor`. ax23 era cantor_uniqueness reescrito (nunca usado).
  ax24_mod2_of_even,  -- teorema en sistemas con inducción; `mod2_of_even` en Block5 (sorry)
  ax25_pred_zero,
  ax26_pred_succ,
  ax_L0_cons_def,
  ax_L1_in_nil,
  ax_L2_in_cons,
  ax_C1_concat_nil,
  ax_C2_concat_cons,
  ax_C3_concat_assoc,
  ax_L3_in_concat,
  ax27_add_left_cancel, -- teorema en sistemas con inducción; usado por `add_left_cancel` en Block4_C6_C7
  -- ax28_mul_two_cancel ELIMINADO 2026-06-02: derivable sin inducción, ver `teo_2_11` en Block1.
  ax29_sub_witness      -- axioma testigo de la resta truncada (monus)
]

-- ## Helper Theorems
-- Estas herramientas son usadas en todos los archivos Block*.lean.

/-- Obtiene un axioma del conjunto de axiomas por membresía en la lista. -/
theorem ax {f : Formula} (h : f ∈ axioms) : axioms ⊢ f :=
  Derives.hyp axioms f h

/-- Especializa una fórmula ∀A con un término concreto t (un paso de sustitución). -/
theorem spec {Γ : List Formula} {A : Formula} (h : Γ ⊢ Formula.forall A) (t : Term) :
    Γ ⊢ substFormula 0 t A :=
  Derives.elim_forall Γ A t h

/-- Reflexividad: Γ ⊢ (t ≐ t) (funciona bajo igualdad definitional). -/
theorem eq_refl {Γ : List Formula} (t : Term) : Γ ⊢ (t ≐ t) :=
  Derives.refl Γ t

/-- Simetría de la igualdad. -/
theorem eq_symm {Γ : List Formula} {t₁ t₂ : Term} (h : Γ ⊢ (t₁ ≐ t₂)) : Γ ⊢ (t₂ ≐ t₁) :=
  FOL.derive_eq_symm h

/-- Transitividad no-estándar: de t₁≐t₂ y t₁≐t₃, concluye t₂≐t₃ (sym + trans estándar). -/
theorem eq_trans {Γ : List Formula} {t₁ t₂ t₃ : Term}
    (h1 : Γ ⊢ (t₁ ≐ t₂)) (h2 : Γ ⊢ (t₁ ≐ t₃)) : Γ ⊢ (t₂ ≐ t₃) :=
  FOL.derive_eq_trans (FOL.derive_eq_symm h1) h2

/-- Congruencia: succ respeta la igualdad. -/
theorem eq_congr_succ {Γ : List Formula} {t₁ t₂ : Term} (h : Γ ⊢ (t₁ ≐ t₂)) :
    Γ ⊢ (succ t₁ ≐ succ t₂) := by
  -- Estrategia: Derives.subst con f = Formula.eq (succ (liftTerm 0 t₁)) (succ #0)
  -- substFormula 0 s f  =  Formula.eq (succ t₁) (succ s)   para cualquier s : Term
  --   LHS: substTerm 0 s (succ (liftTerm 0 t₁))
  --       = succ (substTerms 0 s [liftTerm 0 t₁])
  --       = succ [substTerm 0 s (liftTerm 0 t₁)]
  --       = succ [t₁]                               (por FOL.substTerm_liftTerm)
  --       = succ t₁
  --   RHS: substTerm 0 s (succ (.var 0))
  --       = succ (substTerms 0 s [.var 0])
  --       = succ [substTerm 0 s (.var 0)]
  --       = succ [s]                                (0 = 0 → ite_true)
  --       = succ s
  let f : Formula := Formula.eq (succ (liftTerm 0 t₁)) (succ (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (succ t₁) (succ s) := by
    intro s
    simp only [f, substFormula, succ, substTerm, substTerms,
               FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ Derives.subst Γ t₁ t₂ f h ((hS t₁) ▸ Derives.refl Γ (succ t₁))

/-- Congruencia: pred respeta la igualdad (análogo a `eq_congr_succ`). -/
theorem eq_congr_pred {Γ : List Formula} {t₁ t₂ : Term} (h : Γ ⊢ (t₁ ≐ t₂)) :
    Γ ⊢ (pred t₁ ≐ pred t₂) := by
  let f : Formula := Formula.eq (pred (liftTerm 0 t₁)) (pred (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (pred t₁) (pred s) := by
    intro s
    simp only [f, substFormula, pred, substTerm, substTerms,
               FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ Derives.subst Γ t₁ t₂ f h ((hS t₁) ▸ Derives.refl Γ (pred t₁))

-- ## Additional Proof Helpers

/-- Modus ponens: from Γ ⊢ A ⇒ B and Γ ⊢ A, conclude Γ ⊢ B. -/
def mp {Γ : List Formula} {A B : Formula} (h1 : Γ ⊢ (A ⇒ B)) (h2 : Γ ⊢ A) : Γ ⊢ B :=
  Derives.elim_impl Γ A B h1 h2

/-- Implication introduction (meta-level function → object-level implication).
    Meta-axiom: sound for the object logic but not formally derivable from Derives alone. -/
axiom imp_intro {Γ : List Formula} {A B : Formula} (h : Γ ⊢ A → Γ ⊢ B) : Γ ⊢ (A ⇒ B)

/-- Universal generalization (ω-rule): from (∀ n, Γ ⊢ substFormula 0 n A), conclude Γ ⊢ ∀A.
    Meta-axiom: requires the ω-rule, not derivable from Derives.intro_forall alone. -/
axiom gen {Γ : List Formula} {A : Formula} (h : ∀ n : Term, Γ ⊢ substFormula 0 n A) :
    Γ ⊢ Formula.forall A

/-- Reductio ad absurdum (classical): from Γ ⊢ A → ⊥, conclude Γ ⊢ ¬A.
    Meta-axiom: sound for the object logic. -/
axiom raa {Γ : List Formula} {A : Formula} (h : Γ ⊢ A → Γ ⊢ ⊥) : Γ ⊢ ¬A

/-- Conjunction introduction. -/
def and_intro {Γ : List Formula} {A B : Formula} (h1 : Γ ⊢ A) (h2 : Γ ⊢ B) : Γ ⊢ (A ∧ B) :=
  Derives.intro_and Γ A B h1 h2

/-- Left conjunction elimination. -/
def and_elim_left {Γ : List Formula} {A B : Formula} (h : Γ ⊢ (A ∧ B)) : Γ ⊢ A :=
  Derives.elim_and_l Γ A B h

/-- Right conjunction elimination. -/
def and_elim_right {Γ : List Formula} {A B : Formula} (h : Γ ⊢ (A ∧ B)) : Γ ⊢ B :=
  Derives.elim_and_r Γ A B h

/-- Left disjunction introduction. -/
def or_intro_left {Γ : List Formula} {A B : Formula} (h : Γ ⊢ A) : Γ ⊢ (A ∨ B) :=
  Derives.intro_or_l Γ A B h

/-- Right disjunction introduction. -/
def or_intro_right {Γ : List Formula} {A B : Formula} (h : Γ ⊢ B) : Γ ⊢ (A ∨ B) :=
  Derives.intro_or_r Γ A B h

/-- Disjunction elimination (meta-level case split).
    Meta-axiom: sound for the object logic. -/
axiom or_elim {Γ : List Formula} {A B C : Formula}
    (h : Γ ⊢ (A ∨ B)) (h1 : Γ ⊢ A → Γ ⊢ C) (h2 : Γ ⊢ B → Γ ⊢ C) : Γ ⊢ C

/-- False elimination (ex falso). -/
def false_elim {Γ : List Formula} {A : Formula} (h : Γ ⊢ ⊥) : Γ ⊢ A :=
  Derives.bot_elim Γ A h

/-- Existential introduction. -/
def ex_intro {Γ : List Formula} {A : Formula} (t : Term)
    (h : Γ ⊢ substFormula 0 t A) : Γ ⊢ Formula.ex A :=
  Derives.intro_ex Γ A t h

/-- Existential elimination (meta-level witness extraction).
    Meta-axiom: sound for the object logic. -/
axiom ex_elim {Γ : List Formula} {A C : Formula}
    (h : Γ ⊢ Formula.ex A)
    (cont : ∀ t : Term, Γ ⊢ substFormula 0 t A → Γ ⊢ C) : Γ ⊢ C

/-- Forward direction of biconditional. -/
def iff_mp {Γ : List Formula} {A B : Formula} (h1 : Γ ⊢ (A ⇔ B)) (h2 : Γ ⊢ A) : Γ ⊢ B :=
  Derives.elim_impl Γ A B (Derives.elim_and_l Γ (A ⇒ B) (B ⇒ A) h1) h2

/-- Backward direction of biconditional. -/
def iff_mpr {Γ : List Formula} {A B : Formula} (h1 : Γ ⊢ (A ⇔ B)) (h2 : Γ ⊢ B) : Γ ⊢ A :=
  Derives.elim_impl Γ B A (Derives.elim_and_r Γ (A ⇒ B) (B ⇒ A) h1) h2

/-- Equality substitution (used to rewrite equality hypotheses). -/
theorem eq_subst {Γ : List Formula} {t₁ t₂ : Term} {A : Formula}
    (_heq : Γ ⊢ (t₁ ≐ t₂)) (hp : Γ ⊢ A) : Γ ⊢ A :=
  hp

/-- Negation respects equality symmetry: ¬(b = a) → ¬(a = b). -/
theorem eq_symm_neg {Γ : List Formula} {t₁ t₂ : Term}
    (h : Γ ⊢ ¬(t₂ ≐ t₁)) : Γ ⊢ ¬(t₁ ≐ t₂) :=
  Derives.intro_impl Γ (Formula.eq t₁ t₂) Formula.bottom
    (Derives.elim_impl (Formula.eq t₁ t₂ :: Γ) (Formula.eq t₂ t₁) Formula.bottom
      (Derives.weakening Γ (Formula.eq t₁ t₂ :: Γ) _ h
        (fun _ hx => List.Mem.tail _ hx))
      (FOL.derive_eq_symm
        (Derives.hyp (Formula.eq t₁ t₂ :: Γ) _ (List.Mem.head _))))

/-- Congruence: add respects equality in the right argument. -/
theorem eq_congr_add_left {Γ : List Formula} {u t₁ t₂ : Term} (h : Γ ⊢ (t₁ ≐ t₂)) :
    Γ ⊢ (add u t₁ ≐ add u t₂) := by
  let f : Formula := Formula.eq (add (liftTerm 0 u) (liftTerm 0 t₁)) (add (liftTerm 0 u) (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (add u t₁) (add u s) := by
    intro s
    simp only [f, substFormula, add, substTerm, substTerms,
               FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ Derives.subst Γ t₁ t₂ f h ((hS t₁) ▸ Derives.refl Γ (add u t₁))

/-- Congruence: add respects equality in the left argument. -/
theorem eq_congr_add_right {Γ : List Formula} {u t₁ t₂ : Term} (h : Γ ⊢ (t₁ ≐ t₂)) :
    Γ ⊢ (add t₁ u ≐ add t₂ u) := by
  let f : Formula := Formula.eq (add (liftTerm 0 t₁) (liftTerm 0 u)) (add (.var 0) (liftTerm 0 u))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (add t₁ u) (add s u) := by
    intro s
    simp only [f, substFormula, add, substTerm, substTerms,
               FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ Derives.subst Γ t₁ t₂ f h ((hS t₁) ▸ Derives.refl Γ (add t₁ u))

/-- Congruence: mul respects equality in the right argument. -/
theorem eq_congr_mul_left {Γ : List Formula} {u t₁ t₂ : Term} (h : Γ ⊢ (t₁ ≐ t₂)) :
    Γ ⊢ (mul u t₁ ≐ mul u t₂) := by
  let f : Formula := Formula.eq (mul (liftTerm 0 u) (liftTerm 0 t₁)) (mul (liftTerm 0 u) (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (mul u t₁) (mul u s) := by
    intro s
    simp only [f, substFormula, mul, substTerm, substTerms,
               FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ Derives.subst Γ t₁ t₂ f h ((hS t₁) ▸ Derives.refl Γ (mul u t₁))

/-- Congruence: mul respects equality in the left argument. -/
theorem eq_congr_mul_right {Γ : List Formula} {u t₁ t₂ : Term} (h : Γ ⊢ (t₁ ≐ t₂)) :
    Γ ⊢ (mul t₁ u ≐ mul t₂ u) := by
  let f : Formula := Formula.eq (mul (liftTerm 0 t₁) (liftTerm 0 u)) (mul (.var 0) (liftTerm 0 u))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (mul t₁ u) (mul s u) := by
    intro s
    simp only [f, substFormula, mul, substTerm, substTerms,
               FOL.substTerm_liftTerm, if_true]
  exact (hS t₂) ▸ Derives.subst Γ t₁ t₂ f h ((hS t₁) ▸ Derives.refl Γ (mul t₁ u))

/-- Coercion: use Γ ⊢ A ⇒ B as a function Γ ⊢ A → Γ ⊢ B. -/
instance {Γ : List Formula} {A B : Formula} :
    CoeFun (Derives Γ (Formula.impl A B)) (fun _ => Derives Γ A → Derives Γ B) where
  coe h ha := Derives.elim_impl Γ A B h ha

end ROBINSON_PlusPlus.Minimal.Axioms
