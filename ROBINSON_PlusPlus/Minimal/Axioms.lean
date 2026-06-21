/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import FOL.FOL        -- Term, Formula, Derives (⊢), notaciones ≐ ∧ ∨ ¬ ⇒ ⇔ ∀. ∃. ⊥ ⊤ #
import FOL.Theorems.Eq -- derive_eq_symm, derive_eq_trans, substTerm_liftTerm
import FOL.MetaRules    -- meta-reglas ω de deducción (imp_intro, gen, raa, or_elim, ex_elim, wrappers)

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
-- Bloque VIII extendido: potencia y producto sobre listas de pares.
def pow_sym  : String := "^"
def prodp_sym : String := "Π_p"

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
-- Bloque VIII extendido:
-- `pow b e := b^e`. Producto sobre lista de pares: `prod_pairs [(p₁,e₁),...,(pₖ,eₖ)] := Π pᵢ^eᵢ`.
def pow (b e : Term) : Term := .func pow_sym [b, e]
def prod_pairs (l : Term) : Term := .func prodp_sym [l]

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

-- ax27_add_left_cancel ELIMINADO 2026-06-03: derivable en PA⁻ (sin inducción).
-- Prueba (style PA⁻): si a+c=b+c, por tricotomía (ax19) a<b ∨ a=b ∨ b<a; los casos
-- estrictos llevan a a+c < a+c vía monotonía (lt_add_const_of_le_left + add_comm)
-- y contradicen ax18 (irreflexividad). Ver `add_left_cancel` en Block4_C6_C7.
-- Referencia: PA⁻ axiomatiza semirring discretamente ordenado, donde cancelación
-- aditiva es teorema. Ver https://diagonalargument.com/2020/10/21/topics-in-nonstandard-arithmetic-6-the-axioms/.

-- ELIMINADO 2026-06-02: ax28_mul_two_cancel era REDUNDANTE.
-- La spec TuplasFuncionesYListas.md §Teo 2.11 muestra que es derivable sin inducción
-- usando tricotomía (ax19), irreflexividad (ax18), distributividad (ax12) y monotonía
-- estricta de *2 (probada vía ax13 + teo_2_7 + ax5 + ax2). La prueba directa está
-- ahora en `teo_2_11` (Block1.lean), que ya NO delega a este axioma.

-- ### Axiomas de la Potencia (Bloque VIII extendido)
-- Definición recursiva de `pow` análoga a `*` (ax8/ax9).

-- Ax-Pow-0: ∀ b, b^0 = 1
def ax_pow_zero : Formula :=
  forall_ (pow (.var 0) zero =eq one)

-- Ax-Pow-σ: ∀ b, ∀ e, b^(σe) = b^e * b
def ax_pow_succ : Formula :=
  forall_2 (
    pow (.var 1) (succ (.var 0)) =eq mul (pow (.var 1) (.var 0)) (.var 1)
  )

-- ### Axiomas del Producto sobre Listas de Pares (Bloque VIII extendido)
-- `prod_pairs l` evalúa una lista de pares (p_i, e_i) como Π pᵢ^eᵢ.
-- Sólo se especifica sobre listas cuyos elementos tienen la forma `pair p e`.

-- Ax-ProdP-nil: prod_pairs [] = 1
def ax_prodp_nil : Formula :=
  prod_pairs nil =eq one

-- Ax-ProdP-cons: ∀ p, ∀ e, ∀ t, prod_pairs ((p,e) :: t) = p^e * prod_pairs t
def ax_prodp_cons : Formula :=
  forall_3 (
    prod_pairs (cons (pair (.var 2) (.var 1)) (.var 0)) =eq
      mul (pow (.var 2) (.var 1)) (prod_pairs (.var 0))
  )

-- Ax 29 (sub_witness): ∀ a b, b ≤ a → b + (a − b) = a
-- Axioma testigo para la resta truncada (monus). En sistemas con inducción es
-- teorema (induc. sobre b junto con sub_zero/sub_succ); en Minimal se postula.
-- Determina `sub` salvo equivalencia en el rango b ≤ a; fuera del rango se deja
-- sin especificar (la formulación `sub a b` para `b > a` no se usa en el proyecto).
def ax29_sub_witness : Formula :=
  forall_2 (
    le (.var 0) (.var 1) ⇒ (add (.var 0) (sub (.var 1) (.var 0)) =eq (.var 1))
  )

-- ### Funciones de codificación y sustitución aritmetizada (Meta Nivel D, Fase 2)
-- Extensión definicional para la aritmetización del predicado de demostración de
-- Gödel. `varc`/`funcc` son los códigos de `Term.var`/`Term.func` (tags 0 / 1 =
-- `zero` / `succ zero`); `substtc`/`substtsc` son la sustitución De Bruijn sobre
-- códigos de término / lista de términos. Sus **ecuaciones recursivas** se añaden
-- a `axioms` (abajo) — extensión definicional conservadora, estilo `pow`/`prod_pairs`.

/-- Código de `Term.var n`: `⟨0, n⟩`. -/
def varc (n : Term) : Term := cons zero (cons n nil)
/-- Código de `Term.func`: `⟨1, sym, ts⟩`. -/
def funcc (sc tsc : Term) : Term := cons (succ zero) (cons sc (cons tsc nil))
/-- Sustitución aritmetizada sobre códigos de término. -/
def substtc (v s c : Term) : Term := Term.func "substtc" [v, s, c]
/-- Sustitución aritmetizada sobre códigos de lista de términos. -/
def substtsc (v s c : Term) : Term := Term.func "substtsc" [v, s, c]

/-- Cuantificación universal cuádruple (De Bruijn). -/
def forall_4 (f : Formula) : Formula := .forall (.forall (.forall (.forall f)))

-- Ecuaciones recursivas de la sustitución. Convención `forall_n`: el primer
-- `spec` instancia el índice más alto (`var (n-1)`).
def ax_substtc_var_eq : Formula :=
  forall_3 (((.var 2) =eq (.var 0)) ⇒ (substtc (.var 2) (.var 1) (varc (.var 0)) =eq (.var 1)))
def ax_substtc_var_gt : Formula :=
  forall_3 ((lt (.var 2) (.var 0)) ⇒ (substtc (.var 2) (.var 1) (varc (.var 0)) =eq varc (pred (.var 0))))
def ax_substtc_var_lt : Formula :=
  forall_3 ((lt (.var 0) (.var 2)) ⇒ (substtc (.var 2) (.var 1) (varc (.var 0)) =eq varc (.var 0)))
def ax_substtc_func : Formula :=
  forall_4 (substtc (.var 3) (.var 2) (funcc (.var 1) (.var 0))
    =eq funcc (.var 1) (substtsc (.var 3) (.var 2) (.var 0)))
def ax_substtsc_nil : Formula :=
  forall_2 (substtsc (.var 1) (.var 0) nil =eq nil)
def ax_substtsc_cons : Formula :=
  forall_4 (substtsc (.var 3) (.var 2) (cons (.var 1) (.var 0))
    =eq cons (substtc (.var 3) (.var 2) (.var 1)) (substtsc (.var 3) (.var 2) (.var 0)))

-- Desplazamiento (lift) De Bruijn aritmetizado sobre códigos de término / lista.
/-- Lift aritmetizado sobre códigos de término. -/
def liftc (c t : Term) : Term := Term.func "liftc" [c, t]
/-- Lift aritmetizado sobre códigos de lista de términos. -/
def liftsc (c t : Term) : Term := Term.func "liftsc" [c, t]

-- Ecuaciones recursivas de `liftTerm`. Para el caso `n ≥ c` usamos la condición
-- equivalente `c < n+1` (`lt c (succ n)`), evitando `le`.
def ax_liftc_var_lt : Formula :=
  forall_2 ((lt (.var 0) (.var 1)) ⇒ (liftc (.var 1) (varc (.var 0)) =eq varc (.var 0)))
def ax_liftc_var_ge : Formula :=
  forall_2 ((lt (.var 1) (succ (.var 0))) ⇒ (liftc (.var 1) (varc (.var 0)) =eq varc (succ (.var 0))))
def ax_liftc_func : Formula :=
  forall_3 (liftc (.var 2) (funcc (.var 1) (.var 0)) =eq funcc (.var 1) (liftsc (.var 2) (.var 0)))
def ax_liftsc_nil : Formula :=
  forall_ (liftsc (.var 0) nil =eq nil)
def ax_liftsc_cons : Formula :=
  forall_3 (liftsc (.var 2) (cons (.var 1) (.var 0))
    =eq cons (liftc (.var 2) (.var 1)) (liftsc (.var 2) (.var 0)))

-- Constructores de código de fórmula (tags 2..9, espejo de `formCode`, numeral-free).
def botc : Term := cons (succ (succ zero)) nil
def atomc (pc tsc : Term) : Term := cons (succ (succ (succ zero))) (cons pc (cons tsc nil))
def eqc (a b : Term) : Term := cons (succ (succ (succ (succ zero)))) (cons a (cons b nil))
def implc (a b : Term) : Term := cons (succ (succ (succ (succ (succ zero))))) (cons a (cons b nil))
def forallc (a : Term) : Term := cons (succ (succ (succ (succ (succ (succ zero)))))) (cons a nil)
def andc (a b : Term) : Term :=
  cons (succ (succ (succ (succ (succ (succ (succ zero))))))) (cons a (cons b nil))
def orc (a b : Term) : Term :=
  cons (succ (succ (succ (succ (succ (succ (succ (succ zero)))))))) (cons a (cons b nil))
def exc (a : Term) : Term :=
  cons (succ (succ (succ (succ (succ (succ (succ (succ (succ zero))))))))) (cons a nil)

/-- Sustitución aritmetizada sobre códigos de **fórmula**. -/
def substfc (v t f : Term) : Term := Term.func "substfc" [v, t, f]

-- Ecuaciones recursivas de `substFormula` (8 constructores; los binders ∀/∃
-- incrementan el nivel con `succ` y desplazan el substituyendo con `liftc zero`).
def ax_substfc_bottom : Formula :=
  forall_2 (substfc (.var 1) (.var 0) botc =eq botc)
def ax_substfc_atom : Formula :=
  forall_4 (substfc (.var 3) (.var 2) (atomc (.var 1) (.var 0))
    =eq atomc (.var 1) (substtsc (.var 3) (.var 2) (.var 0)))
def ax_substfc_eq : Formula :=
  forall_4 (substfc (.var 3) (.var 2) (eqc (.var 1) (.var 0))
    =eq eqc (substtc (.var 3) (.var 2) (.var 1)) (substtc (.var 3) (.var 2) (.var 0)))
def ax_substfc_impl : Formula :=
  forall_4 (substfc (.var 3) (.var 2) (implc (.var 1) (.var 0))
    =eq implc (substfc (.var 3) (.var 2) (.var 1)) (substfc (.var 3) (.var 2) (.var 0)))
def ax_substfc_forall : Formula :=
  forall_3 (substfc (.var 2) (.var 1) (forallc (.var 0))
    =eq forallc (substfc (succ (.var 2)) (liftc zero (.var 1)) (.var 0)))
def ax_substfc_and : Formula :=
  forall_4 (substfc (.var 3) (.var 2) (andc (.var 1) (.var 0))
    =eq andc (substfc (.var 3) (.var 2) (.var 1)) (substfc (.var 3) (.var 2) (.var 0)))
def ax_substfc_or : Formula :=
  forall_4 (substfc (.var 3) (.var 2) (orc (.var 1) (.var 0))
    =eq orc (substfc (.var 3) (.var 2) (.var 1)) (substfc (.var 3) (.var 2) (.var 0)))
def ax_substfc_ex : Formula :=
  forall_3 (substfc (.var 2) (.var 1) (exc (.var 0))
    =eq exc (substfc (succ (.var 2)) (liftc zero (.var 1)) (.var 0)))

/-- Lift aritmetizado sobre códigos de **fórmula** (necesario para el esquema Q3,
    que usa `liftFormula 0 B`). -/
def liftfc (c f : Term) : Term := Term.func "liftfc" [c, f]

-- Ecuaciones recursivas de `liftFormula` (los binders ∀/∃ incrementan el nivel
-- con `succ`; átomos/igualdades usan `liftc`/`liftsc`).
def ax_liftfc_bottom : Formula :=
  forall_ (liftfc (.var 0) botc =eq botc)
def ax_liftfc_atom : Formula :=
  forall_3 (liftfc (.var 2) (atomc (.var 1) (.var 0)) =eq atomc (.var 1) (liftsc (.var 2) (.var 0)))
def ax_liftfc_eq : Formula :=
  forall_3 (liftfc (.var 2) (eqc (.var 1) (.var 0)) =eq eqc (liftc (.var 2) (.var 1)) (liftc (.var 2) (.var 0)))
def ax_liftfc_impl : Formula :=
  forall_3 (liftfc (.var 2) (implc (.var 1) (.var 0)) =eq implc (liftfc (.var 2) (.var 1)) (liftfc (.var 2) (.var 0)))
def ax_liftfc_forall : Formula :=
  forall_2 (liftfc (.var 1) (forallc (.var 0)) =eq forallc (liftfc (succ (.var 1)) (.var 0)))
def ax_liftfc_and : Formula :=
  forall_3 (liftfc (.var 2) (andc (.var 1) (.var 0)) =eq andc (liftfc (.var 2) (.var 1)) (liftfc (.var 2) (.var 0)))
def ax_liftfc_or : Formula :=
  forall_3 (liftfc (.var 2) (orc (.var 1) (.var 0)) =eq orc (liftfc (.var 2) (.var 1)) (liftfc (.var 2) (.var 0)))
def ax_liftfc_ex : Formula :=
  forall_2 (liftfc (.var 1) (exc (.var 0)) =eq exc (liftfc (succ (.var 1)) (.var 0)))

-- ### Verificador object de demostraciones (Fase 2.4)
-- Numeral local (= `Meta.Godel.numeral`; usado para las etiquetas de regla 0..17)
-- y extractores `carc`/`cdrc` (cabeza/cola de `cons`) para leer las líneas.

/-- Numeral De Bruijn `σⁿ(0)` (copia local en `Minimal`; coincide con `Godel.numeral`). -/
def numeralM : Nat → Term
  | 0     => zero
  | n + 1 => succ (numeralM n)

/-! ### Codificación de Gödel a nivel `Minimal` (`formCodeM`)

Copia local de la codificación `formCode` de `Meta/Provability.lean`, escrita con
`numeralM` (que `Minimal` sí tiene). Necesaria para expresar, **dentro de
`Minimal.axioms`**, el código object de los axiomas de la teoría (`axiomsCodeT`)
y así dar una regla `thy` **sólida** (que solo acepta códigos de axiomas reales).
El puente `formCodeM = formCode` se demuestra a nivel Meta. -/

/-- Código de una lista de caracteres (nivel `Minimal`). -/
def charsCodeM : List Char → Term
  | []      => nil
  | c :: cs => cons (numeralM c.toNat) (charsCodeM cs)

/-- Código de un símbolo `String` (nivel `Minimal`). -/
def strCodeM (s : String) : Term := charsCodeM s.toList

/- Código de Gödel de términos (nivel `Minimal`), mutuo con `termsCodeM`. -/
mutual
def termCodeM : Term → Term
  | .var n     => cons (numeralM 0) (cons (numeralM n) nil)
  | .func s ts => cons (numeralM 1) (cons (strCodeM s) (cons (termsCodeM ts) nil))
def termsCodeM : List Term → Term
  | []      => nil
  | t :: ts => cons (termCodeM t) (termsCodeM ts)
end

/-- Código de Gödel de fórmulas (nivel `Minimal`); espejo de `formCode`. -/
def formCodeM : Formula → Term
  | .bottom          => cons (numeralM 2) nil
  | .atom p ts       => cons (numeralM 3) (cons (strCodeM p) (cons (termsCodeM ts) nil))
  | .eq t u          => cons (numeralM 4) (cons (termCodeM t) (cons (termCodeM u) nil))
  | .impl a b        => cons (numeralM 5) (cons (formCodeM a) (cons (formCodeM b) nil))
  | Formula.forall a => cons (numeralM 6) (cons (formCodeM a) nil)
  | .and a b         => cons (numeralM 7) (cons (formCodeM a) (cons (formCodeM b) nil))
  | .or a b          => cons (numeralM 8) (cons (formCodeM a) (cons (formCodeM b) nil))
  | .ex a            => cons (numeralM 9) (cons (formCodeM a) nil)

/-- Código object de una lista de fórmulas (nivel `Minimal`). -/
def listFormCodeM : List Formula → Term
  | []      => nil
  | f :: fs => cons (formCodeM f) (listFormCodeM fs)

/-! ### Clausura De Bruijn de los códigos `formCodeM`

Los códigos no contienen variables libres ⟹ `liftTerm` es la identidad sobre
ellos. Se prueban por **inducción estructural** (no por `rfl`/cómputo del kernel),
lo cual es esencial: los códigos de símbolos (`σ`, `∈`, …) contienen numerales
gigantes (`numeralM` del codepoint Unicode) que harían explotar cualquier `rfl`.
Necesarias para `axioms_lift_eq` (con `ax_axiomsCodeT` en `axioms`). -/

theorem liftTerm_nil (c : Nat) : liftTerm c nil = nil := rfl

theorem liftTerm_numeralM (c n : Nat) : liftTerm c (numeralM n) = numeralM n := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [numeralM, succ, liftTerm, liftTerms, ih]

theorem liftTerm_charsCodeM (c : Nat) : ∀ cs : List Char, liftTerm c (charsCodeM cs) = charsCodeM cs
  | []      => rfl
  | _ :: cs => by
      simp only [charsCodeM, cons, liftTerm, liftTerms, liftTerm_numeralM, liftTerm_charsCodeM c cs]

theorem liftTerm_strCodeM (c : Nat) (s : String) : liftTerm c (strCodeM s) = strCodeM s :=
  liftTerm_charsCodeM c s.toList

mutual
theorem liftTerm_termCodeM (c : Nat) : ∀ t : Term, liftTerm c (termCodeM t) = termCodeM t
  | .var _    => by simp only [termCodeM, cons, liftTerm, liftTerms, liftTerm_numeralM, liftTerm_nil]
  | .func s ts => by
      simp only [termCodeM, cons, liftTerm, liftTerms, liftTerm_numeralM, liftTerm_strCodeM,
        liftTerm_nil, liftTerm_termsCodeM c ts]
theorem liftTerm_termsCodeM (c : Nat) : ∀ ts : List Term, liftTerm c (termsCodeM ts) = termsCodeM ts
  | []      => rfl
  | t :: ts => by
      simp only [termsCodeM, cons, liftTerm, liftTerms, liftTerm_termCodeM c t, liftTerm_termsCodeM c ts]
end

theorem liftTerm_formCodeM (c : Nat) : ∀ φ : Formula, liftTerm c (formCodeM φ) = formCodeM φ
  | .bottom    => by simp only [formCodeM, cons, liftTerm, liftTerms, liftTerm_numeralM, liftTerm_nil]
  | .atom _ _  => by
      simp only [formCodeM, cons, liftTerm, liftTerms, liftTerm_numeralM, liftTerm_strCodeM,
        liftTerm_nil, liftTerm_termsCodeM]
  | .eq _ _    => by
      simp only [formCodeM, cons, liftTerm, liftTerms, liftTerm_numeralM, liftTerm_nil, liftTerm_termCodeM]
  | .impl a b  => by
      simp only [formCodeM, cons, liftTerm, liftTerms, liftTerm_numeralM, liftTerm_nil,
        liftTerm_formCodeM c a, liftTerm_formCodeM c b]
  | .forall a  => by
      simp only [formCodeM, cons, liftTerm, liftTerms, liftTerm_numeralM, liftTerm_nil,
        liftTerm_formCodeM c a]
  | .and a b   => by
      simp only [formCodeM, cons, liftTerm, liftTerms, liftTerm_numeralM, liftTerm_nil,
        liftTerm_formCodeM c a, liftTerm_formCodeM c b]
  | .or a b    => by
      simp only [formCodeM, cons, liftTerm, liftTerms, liftTerm_numeralM, liftTerm_nil,
        liftTerm_formCodeM c a, liftTerm_formCodeM c b]
  | .ex a      => by
      simp only [formCodeM, cons, liftTerm, liftTerms, liftTerm_numeralM, liftTerm_nil,
        liftTerm_formCodeM c a]

theorem liftTerm_listFormCodeM (c : Nat) : ∀ L : List Formula,
    liftTerm c (listFormCodeM L) = listFormCodeM L
  | []      => rfl
  | f :: fs => by
      simp only [listFormCodeM, cons, liftTerm, liftTerms, liftTerm_formCodeM c f,
        liftTerm_listFormCodeM c fs]

/-! ### Clausura por `substTerm` (espejo de la de `liftTerm`)

`substTerm` también es identidad sobre los códigos `formCodeM` (cerrados). Igual
que arriba, por inducción estructural (no `rfl`, por los numerales gigantes).
Necesarias para re-derivar las ecuaciones de `tcFn` vía `spec` (que sustituye). -/

theorem substTerm_nil (v : Nat) (s : Term) : substTerm v s nil = nil := rfl

theorem substTerm_numeralM (v : Nat) (s : Term) (n : Nat) : substTerm v s (numeralM n) = numeralM n := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [numeralM, succ, substTerm, substTerms, ih]

theorem substTerm_charsCodeM (v : Nat) (s : Term) :
    ∀ cs : List Char, substTerm v s (charsCodeM cs) = charsCodeM cs
  | []      => rfl
  | _ :: cs => by
      simp only [charsCodeM, cons, substTerm, substTerms, substTerm_numeralM, substTerm_charsCodeM v s cs]

theorem substTerm_strCodeM (v : Nat) (s : Term) (str : String) :
    substTerm v s (strCodeM str) = strCodeM str :=
  substTerm_charsCodeM v s str.toList

mutual
theorem substTerm_termCodeM (v : Nat) (s : Term) : ∀ t : Term, substTerm v s (termCodeM t) = termCodeM t
  | .var _    => by simp only [termCodeM, cons, substTerm, substTerms, substTerm_numeralM, substTerm_nil]
  | .func sy ts => by
      simp only [termCodeM, cons, substTerm, substTerms, substTerm_numeralM, substTerm_strCodeM,
        substTerm_nil, substTerm_termsCodeM v s ts]
theorem substTerm_termsCodeM (v : Nat) (s : Term) : ∀ ts : List Term, substTerm v s (termsCodeM ts) = termsCodeM ts
  | []      => rfl
  | t :: ts => by
      simp only [termsCodeM, cons, substTerm, substTerms, substTerm_termCodeM v s t,
        substTerm_termsCodeM v s ts]
end

theorem substTerm_formCodeM (v : Nat) (s : Term) : ∀ φ : Formula, substTerm v s (formCodeM φ) = formCodeM φ
  | .bottom    => by simp only [formCodeM, cons, substTerm, substTerms, substTerm_numeralM, substTerm_nil]
  | .atom _ _  => by
      simp only [formCodeM, cons, substTerm, substTerms, substTerm_numeralM, substTerm_strCodeM,
        substTerm_nil, substTerm_termsCodeM]
  | .eq _ _    => by
      simp only [formCodeM, cons, substTerm, substTerms, substTerm_numeralM, substTerm_nil, substTerm_termCodeM]
  | .impl a b  => by
      simp only [formCodeM, cons, substTerm, substTerms, substTerm_numeralM, substTerm_nil,
        substTerm_formCodeM v s a, substTerm_formCodeM v s b]
  | .forall a  => by
      simp only [formCodeM, cons, substTerm, substTerms, substTerm_numeralM, substTerm_nil,
        substTerm_formCodeM v s a]
  | .and a b   => by
      simp only [formCodeM, cons, substTerm, substTerms, substTerm_numeralM, substTerm_nil,
        substTerm_formCodeM v s a, substTerm_formCodeM v s b]
  | .or a b    => by
      simp only [formCodeM, cons, substTerm, substTerms, substTerm_numeralM, substTerm_nil,
        substTerm_formCodeM v s a, substTerm_formCodeM v s b]
  | .ex a      => by
      simp only [formCodeM, cons, substTerm, substTerms, substTerm_numeralM, substTerm_nil,
        substTerm_formCodeM v s a]

/-- Cabeza de un `cons`. -/
def carc (l : Term) : Term := Term.func "carc" [l]
/-- Cola de un `cons`. -/
def cdrc (l : Term) : Term := Term.func "cdrc" [l]

def ax_carc : Formula := forall_2 (carc (cons (.var 1) (.var 0)) =eq (.var 1))
def ax_cdrc : Formula := forall_2 (cdrc (cons (.var 1) (.var 0)) =eq (.var 0))

/-! ### Verificador estructural `runFn` (Nivel D real — Fase R, D2/D3)

`runFn checked rest` acumula las **conclusiones** de una secuencia de líneas;
cada línea lleva su conclusión incorporada como cabeza (`line = cons ⌜concl⌝
justif`), de modo que `runFn` **reduce uniformemente** vía `carc` sobre la
estructura `cons`/`nil`, **sin depender de la regla de la línea**. Esto es lo que
permite la **inducción object-level** (compositividad/debilitamiento) que D2/D3
necesitan y que la `validProofFn` condicional bloqueaba. La validez de cada línea
se separa en el predicado `chainOk` (Fase R2). -/
def runFn (checked rest : Term) : Term := Term.func "runFn" [checked, rest]

/-- `runFn c nil = c`. -/
def ax_runFn_nil : Formula := forall_ (runFn (.var 0) nil =eq (.var 0))
/-- `runFn c (cons line rest) = runFn (concat c [carc line]) rest` (incondicional). -/
def ax_runFn_cons : Formula :=
  forall_3 (runFn (.var 2) (cons (.var 1) (.var 0)) =eq
    runFn (concat (.var 2) (cons (carc (.var 1)) nil)) (.var 0))

/-! ### Validez de líneas y cadenas: `allIn`, `lineWF`, `premsOf`, `lineOk`, `chainOk`

La validez de una línea se separa en (1) `lineWF line` — bien-formación
**independiente del contexto** (la conclusión casa con el esquema; para `thy`, el
código pertenece a `axiomsCodeT`); (2) `allIn c (premsOf line)` — las premisas que
la regla referencia (`premsOf`, p.ej. `[⌜A⇒B⌝, ⌜A⌝]` para `mp`) están en el
contexto `c`. `allIn` recurre **uniformemente** sobre su lista, de modo que la
**monotonía en el contexto** (`lineOk c line ⇒ lineOk (c'++c) line`) es demostrable
para líneas ARBITRARIAS — clave para `chainOk`-monotonía y D2. -/

/-- `allIn c L`: todo elemento de la lista `L` pertenece (`In`) a `c`. -/
def allIn (c L : Term) : Formula := Formula.atom "allIn" [c, L]
/-- `lineWF line`: bien-formación de la línea independiente del contexto. -/
def lineWF (line : Term) : Formula := Formula.atom "lineWF" [line]
/-- `premsOf line`: lista de premisas (códigos de fórmula) que la línea referencia. -/
def premsOf (line : Term) : Term := Term.func "premsOf" [line]
/-- `lineOk c line`: la línea es válida en el contexto `c`. -/
def lineOk (c line : Term) : Formula := land (lineWF line) (allIn c (premsOf line))
/-- `chainOk c p`: la secuencia `p` es una demostración válida desde el acumulador `c`. -/
def chainOk (c p : Term) : Formula := Formula.atom "chainOk" [c, p]

/-- `allIn c nil` (vacuamente cierto). -/
def ax_allIn_nil : Formula := forall_ (allIn (.var 0) nil)
/-- `allIn c (cons x t) ⇔ In x c ∧ allIn c t`. -/
def ax_allIn_cons : Formula :=
  forall_3 (allIn (.var 2) (cons (.var 1) (.var 0)) ⇔
    land (In (.var 1) (.var 2)) (allIn (.var 2) (.var 0)))
/-- `chainOk c nil` (la cadena vacía es válida). -/
def ax_chainOk_nil : Formula := forall_ (chainOk (.var 0) nil)
/-- `chainOk c (cons line rest) ⇔ lineOk c line ∧ chainOk (c ++ [carc line]) rest`. -/
def ax_chainOk_cons : Formula :=
  forall_3 (chainOk (.var 2) (cons (.var 1) (.var 0)) ⇔
    land (lineOk (.var 2) (.var 1)) (chainOk (concat (.var 2) (cons (carc (.var 1)) nil)) (.var 0)))

/-! ### Función «código del código» `tcFn` (para el lema diagonal, Fase 4)

`tcFn` computa `termCode` sobre **códigos** (términos cerrados construidos solo
con `cons`/`succ`/`zero`). Sus 3 ecuaciones espejan la cláusula `.func` de
`termCode` para los símbolos `::`/`σ`/`0`:

* `termCode (func s ts) = ⟨1, strCode s, termsCode ts⟩`.

Es la única pieza que falta para representar la **diagonalización** (substituir el
código de una fórmula en sí misma necesita el código de ese código). El puente
`tcFn (formCode ψ) = termCode (formCode ψ)` (`tc_arith`) se prueba por inducción
meta en `Meta/Diagonal.lean`. -/
def tcFn (t : Term) : Term := Term.func "tcFn" [t]

-- `termCode zero = ⟨1, strCode "0", []⟩`  (nil = zero, termsCode [] = nil)
def ax_tc_zero : Formula :=
  tcFn zero =eq cons (numeralM 1) (cons (strCodeM zero_sym) (cons nil nil))
-- `termCode (σ x) = ⟨1, strCode "σ", [termCode x]⟩`
def ax_tc_succ : Formula :=
  forall_ (tcFn (succ (.var 0)) =eq
    cons (numeralM 1) (cons (strCodeM succ_sym) (cons (cons (tcFn (.var 0)) nil) nil)))
-- `termCode (a :: b) = ⟨1, strCode "::", [termCode a, termCode b]⟩`
def ax_tc_cons : Formula :=
  forall_2 (tcFn (cons (.var 1) (.var 0)) =eq
    cons (numeralM 1) (cons (strCodeM cons_sym)
      (cons (cons (tcFn (.var 1)) (cons (tcFn (.var 0)) nil)) nil)))

/-- Cuantificación universal quíntuple. -/
def forall_5 (f : Formula) : Formula := .forall (forall_4 f)

/-- Verificador de demostraciones-secuencia: `validProofFn checked rest` recorre
    `rest` recomputando la conclusión de cada línea y acumulando en `checked`;
    devuelve la lista final de conclusiones para una demostración válida. -/
def validProofFn (checked rest : Term) : Term := Term.func "validProofFn" [checked, rest]

-- Ecuaciones de `validProofFn`. Una línea es `cons (numeralM K) (cons p₁ (… nil)))`;
-- la etiqueta K (embebida en el patrón) distingue la regla (axiomas incondicionales
-- para los esquemas lógicos; MP/Gen condicionados por pertenencia `In`). Parámetros
-- directos por binders. Orden de binders: `checked` el más externo, `rest` el más
-- interno (`.var 0`).
def ax_vpf_nil : Formula := forall_ (validProofFn (.var 0) nil =eq (.var 0))

-- 2 parámetros (a=.var 2, b=.var 1): checked=.var 3, rest=.var 0.
def ax_vpf_p1 : Formula :=
  forall_4 (validProofFn (.var 3) (cons (cons (numeralM 0) (cons (.var 2) (cons (.var 1) nil))) (.var 0)) =eq
    validProofFn (concat (.var 3) (cons (implc (.var 2) (implc (.var 1) (.var 2))) nil)) (.var 0))
def ax_vpf_c1 : Formula :=
  forall_4 (validProofFn (.var 3) (cons (cons (numeralM 2) (cons (.var 2) (cons (.var 1) nil))) (.var 0)) =eq
    validProofFn (concat (.var 3) (cons (implc (.var 2) (implc (.var 1) (andc (.var 2) (.var 1)))) nil)) (.var 0))
def ax_vpf_c2 : Formula :=
  forall_4 (validProofFn (.var 3) (cons (cons (numeralM 3) (cons (.var 2) (cons (.var 1) nil))) (.var 0)) =eq
    validProofFn (concat (.var 3) (cons (implc (andc (.var 2) (.var 1)) (.var 2)) nil)) (.var 0))
def ax_vpf_c3 : Formula :=
  forall_4 (validProofFn (.var 3) (cons (cons (numeralM 4) (cons (.var 2) (cons (.var 1) nil))) (.var 0)) =eq
    validProofFn (concat (.var 3) (cons (implc (andc (.var 2) (.var 1)) (.var 1)) nil)) (.var 0))
def ax_vpf_j1 : Formula :=
  forall_4 (validProofFn (.var 3) (cons (cons (numeralM 5) (cons (.var 2) (cons (.var 1) nil))) (.var 0)) =eq
    validProofFn (concat (.var 3) (cons (implc (.var 2) (orc (.var 2) (.var 1))) nil)) (.var 0))
def ax_vpf_j2 : Formula :=
  forall_4 (validProofFn (.var 3) (cons (cons (numeralM 6) (cons (.var 2) (cons (.var 1) nil))) (.var 0)) =eq
    validProofFn (concat (.var 3) (cons (implc (.var 1) (orc (.var 2) (.var 1))) nil)) (.var 0))
-- q1/q2/q3 (2 parámetros: A=.var 2, t/B=.var 1).
def ax_vpf_q1 : Formula :=
  forall_4 (validProofFn (.var 3) (cons (cons (numeralM 9) (cons (.var 2) (cons (.var 1) nil))) (.var 0)) =eq
    validProofFn (concat (.var 3) (cons (implc (forallc (.var 2)) (substfc zero (.var 1) (.var 2))) nil)) (.var 0))
def ax_vpf_q2 : Formula :=
  forall_4 (validProofFn (.var 3) (cons (cons (numeralM 10) (cons (.var 2) (cons (.var 1) nil))) (.var 0)) =eq
    validProofFn (concat (.var 3) (cons (implc (substfc zero (.var 1) (.var 2)) (exc (.var 2))) nil)) (.var 0))
def ax_vpf_q3 : Formula :=
  forall_4 (validProofFn (.var 3) (cons (cons (numeralM 11) (cons (.var 2) (cons (.var 1) nil))) (.var 0)) =eq
    validProofFn (concat (.var 3) (cons (implc (forallc (implc (.var 2) (liftfc zero (.var 1)))) (implc (exc (.var 2)) (.var 1))) nil)) (.var 0))
-- 3 parámetros (a=.var 3, b=.var 2, c=.var 1): checked=.var 4, rest=.var 0.
def ax_vpf_p2 : Formula :=
  forall_5 (validProofFn (.var 4) (cons (cons (numeralM 1) (cons (.var 3) (cons (.var 2) (cons (.var 1) nil)))) (.var 0)) =eq
    validProofFn (concat (.var 4) (cons (implc (implc (.var 3) (implc (.var 2) (.var 1))) (implc (implc (.var 3) (.var 2)) (implc (.var 3) (.var 1)))) nil)) (.var 0))
def ax_vpf_j3 : Formula :=
  forall_5 (validProofFn (.var 4) (cons (cons (numeralM 7) (cons (.var 3) (cons (.var 2) (cons (.var 1) nil)))) (.var 0)) =eq
    validProofFn (concat (.var 4) (cons (implc (orc (.var 3) (.var 2)) (implc (implc (.var 3) (.var 1)) (implc (implc (.var 2) (.var 1)) (.var 1)))) nil)) (.var 0))
-- leibniz (3 parámetros: A=.var 3, t₁=.var 2, t₂=.var 1).
def ax_vpf_leibniz : Formula :=
  forall_5 (validProofFn (.var 4) (cons (cons (numeralM 13) (cons (.var 3) (cons (.var 2) (cons (.var 1) nil)))) (.var 0)) =eq
    validProofFn (concat (.var 4) (cons (implc (eqc (.var 2) (.var 1)) (implc (substfc zero (.var 2) (.var 3)) (substfc zero (.var 1) (.var 3)))) nil)) (.var 0))
-- 1 parámetro (a=.var 1): checked=.var 2, rest=.var 0.
def ax_vpf_efq : Formula :=
  forall_3 (validProofFn (.var 2) (cons (cons (numeralM 8) (cons (.var 1) nil)) (.var 0)) =eq
    validProofFn (concat (.var 2) (cons (implc botc (.var 1)) nil)) (.var 0))
def ax_vpf_eqrefl : Formula :=
  forall_3 (validProofFn (.var 2) (cons (cons (numeralM 12) (cons (.var 1) nil)) (.var 0)) =eq
    validProofFn (concat (.var 2) (cons (eqc (.var 1) (.var 1)) nil)) (.var 0))
def ax_vpf_p3 : Formula :=
  forall_3 (validProofFn (.var 2) (cons (cons (numeralM 14) (cons (.var 1) nil)) (.var 0)) =eq
    validProofFn (concat (.var 2) (cons (implc (implc (implc (.var 1) botc) botc) (.var 1)) nil)) (.var 0))
-- MP (conclB=.var 2, premiseA=.var 1): condicional por pertenencia.
def ax_vpf_mp : Formula :=
  forall_4 ((In (implc (.var 1) (.var 2)) (.var 3)) ⇒
    ((In (.var 1) (.var 3)) ⇒
      (validProofFn (.var 3) (cons (cons (numeralM 16) (cons (.var 2) (cons (.var 1) nil))) (.var 0)) =eq
        validProofFn (concat (.var 3) (cons (.var 2) nil)) (.var 0))))
-- Gen (body=.var 1): condicional por pertenencia.
def ax_vpf_gen : Formula :=
  forall_3 ((In (.var 1) (.var 2)) ⇒
    (validProofFn (.var 2) (cons (cons (numeralM 17) (cons (.var 1) nil)) (.var 0)) =eq
      validProofFn (concat (.var 2) (cons (forallc (.var 1)) nil)) (.var 0)))
/-! ### Teoría-objeto `coreAxioms` y su código `axiomsCodeT`

`thy` recorre los **34 axiomas matemáticos** (`coreAxioms`), NO las ecuaciones de
coding (`codingAxioms`, maquinaria de verificación). `axiomsCodeT` es el código
object de esa lista; se declara **opaco** (símbolo `Term.func "axiomsCodeT" []`)
y se ancla por el axioma `ax_axiomsCodeT` a `listFormCodeM coreAxioms`, para que
la sustitución sobre él en las pruebas de los step-lemmas sea trivial (rápida).

Evita el **ciclo**: `axiomsCodeT`/`ax_axiomsCodeT` referencian `coreAxioms`, que
**no** contiene `ax_vpf_thy` ni `ax_axiomsCodeT`; por eso `axiomsCodeT` no se
contiene a sí mismo. -/

/-- Los 34 axiomas **matemáticos** de la teoría (sin las ecuaciones de coding). Es
    `axioms` truncada antes del bloque Nivel D (ver `axioms_eq`). -/
def coreAxioms : List Formula := [
  ax2_peano_succ_neq_zero, ax3_peano_succ_inj, ax4_add_zero, ax5_add_succ,
  ax6_add_comm, ax7_add_assoc, ax8_mul_zero, ax9_mul_succ, ax10_mul_comm,
  ax11_mul_assoc, ax12_mul_distrib, ax13_lt_def, ax14_sqrt_le, ax15_lt_succ_sqrt,
  ax16_mod2_succ, ax17_div_mod_eq, ax18_lt_irrefl, ax19_lt_trichotomy,
  ax21_mod2_range, ax24_mod2_of_even, ax25_pred_zero, ax26_pred_succ,
  ax_L0_cons_def, ax_L1_in_nil, ax_L2_in_cons, ax_C1_concat_nil, ax_C2_concat_cons,
  ax_C3_concat_assoc, ax_L3_in_concat, ax29_sub_witness, ax_pow_zero, ax_pow_succ,
  ax_prodp_nil, ax_prodp_cons
]

/-- Código object (opaco) de la teoría `coreAxioms`. Anclado por `ax_axiomsCodeT`. -/
def axiomsCodeT : Term := Term.func "axiomsCodeT" []

/-- Anclaje: `axiomsCodeT` es el código de la lista de axiomas de la teoría. -/
def ax_axiomsCodeT : Formula := axiomsCodeT =eq listFormCodeM coreAxioms

-- Thy (c=.var 1, el código del axioma de teoría): **condicional** a que `c`
-- pertenezca a `axiomsCodeT` (el código de `coreAxioms`). Así el verificador solo
-- acepta como axioma de teoría los códigos de axiomas REALES → `provCodeC` es fiel
-- (no demostrable para `φ` arbitraria). `axiomsCodeT` es opaco ⟹ la sustitución
-- sobre él es trivial. (La dirección negativa plena —probar `¬In c …` para no
-- axiomas— sigue en 2.6.)
def ax_vpf_thy : Formula :=
  forall_3 ((In (.var 1) axiomsCodeT) ⇒
    (validProofFn (.var 2) (cons (cons (numeralM 15) (cons (.var 1) nil)) (.var 0)) =eq
      validProofFn (concat (.var 2) (cons (.var 1) nil)) (.var 0)))

-- Inducción (a = .var 1, código del predicado φ): **incondicional** (todo esquema
-- de inducción es axioma legítimo de la aritmética, IΣ₁). El verificador
-- reconstruye el código de `inductionFormula φ` a partir de `⌜φ⌝` con
-- `substfc`/`liftfc` y los códigos cerrados de `O` (`termCodeM zero`) y de `σ#0`
-- (`termCodeM (succ #0)`). La **fidelidad** la da `ind_concl_code` (Meta/Induction):
-- la reconstrucción `=eq formCode (inductionFormula φ)`, y `Full.ax_induction` la
-- hace **sólida**. Tag 18. (`termCodeM (succ #0)` es un código CERRADO: `termCodeM`
-- consume el `Term.var 0` codificándolo, no es la variable ligada por `forall_3`.)
def ax_vpf_ind : Formula :=
  forall_3 (validProofFn (.var 2) (cons (cons (numeralM 18) (cons (.var 1) nil)) (.var 0)) =eq
    validProofFn (concat (.var 2)
      (cons (implc (substfc zero (termCodeM zero) (.var 1))
               (implc (forallc (implc (.var 1)
                         (substfc zero (termCodeM (succ (.var 0))) (liftfc (succ zero) (.var 1)))))
                      (forallc (.var 1)))) nil)) (.var 0))

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
  -- ax27_add_left_cancel ELIMINADO 2026-06-03: derivable en PA⁻ vía tricotomía +
  -- monotonía + irreflexividad. Ver `add_left_cancel` en Block4_C6_C7.
  -- ax28_mul_two_cancel ELIMINADO 2026-06-02: derivable sin inducción, ver `teo_2_11` en Block1.
  ax29_sub_witness,     -- axioma testigo de la resta truncada (monus)
  -- Bloque VIII extendido (factorización): pow y prod_pairs.
  ax_pow_zero,          -- b^0 = 1
  ax_pow_succ,          -- b^(σe) = b^e * b
  ax_prodp_nil,         -- prod_pairs [] = 1
  ax_prodp_cons,        -- prod_pairs ((p,e)::t) = p^e * prod_pairs t
  -- Nivel D (Fase 2): ecuaciones recursivas de la sustitución aritmetizada
  -- (extensión definicional conservadora; ver `Meta/SubstArith.lean`).
  ax_substtc_var_eq,
  ax_substtc_var_gt,
  ax_substtc_var_lt,
  ax_substtc_func,
  ax_substtsc_nil,
  ax_substtsc_cons,
  ax_liftc_var_lt,
  ax_liftc_var_ge,
  ax_liftc_func,
  ax_liftsc_nil,
  ax_liftsc_cons,
  ax_substfc_bottom,
  ax_substfc_atom,
  ax_substfc_eq,
  ax_substfc_impl,
  ax_substfc_forall,
  ax_substfc_and,
  ax_substfc_or,
  ax_substfc_ex,
  ax_liftfc_bottom,
  ax_liftfc_atom,
  ax_liftfc_eq,
  ax_liftfc_impl,
  ax_liftfc_forall,
  ax_liftfc_and,
  ax_liftfc_or,
  ax_liftfc_ex,
  ax_carc,
  ax_cdrc,
  ax_vpf_nil,
  ax_vpf_p1,
  ax_vpf_p2,
  ax_vpf_c1,
  ax_vpf_c2,
  ax_vpf_c3,
  ax_vpf_j1,
  ax_vpf_j2,
  ax_vpf_j3,
  ax_vpf_efq,
  ax_vpf_q1,
  ax_vpf_q2,
  ax_vpf_q3,
  ax_vpf_eqrefl,
  ax_vpf_leibniz,
  ax_vpf_p3,
  ax_vpf_mp,
  ax_vpf_gen,
  ax_vpf_thy,
  ax_vpf_ind,
  ax_axiomsCodeT,
  ax_tc_zero,
  ax_tc_succ,
  ax_tc_cons,
  ax_runFn_nil,
  ax_runFn_cons,
  ax_allIn_nil,
  ax_allIn_cons,
  ax_chainOk_nil,
  ax_chainOk_cons
]

/-- Las ecuaciones de coding / maquinaria de verificación (NO parte de la teoría
    matemática). `axioms = coreAxioms ++ codingAxioms` (por `rfl`, ver
    `axioms_eq`). -/
def codingAxioms : List Formula := [
  ax_substtc_var_eq, ax_substtc_var_gt, ax_substtc_var_lt, ax_substtc_func,
  ax_substtsc_nil, ax_substtsc_cons, ax_liftc_var_lt, ax_liftc_var_ge, ax_liftc_func,
  ax_liftsc_nil, ax_liftsc_cons, ax_substfc_bottom, ax_substfc_atom, ax_substfc_eq,
  ax_substfc_impl, ax_substfc_forall, ax_substfc_and, ax_substfc_or, ax_substfc_ex,
  ax_liftfc_bottom, ax_liftfc_atom, ax_liftfc_eq, ax_liftfc_impl, ax_liftfc_forall,
  ax_liftfc_and, ax_liftfc_or, ax_liftfc_ex, ax_carc, ax_cdrc, ax_vpf_nil, ax_vpf_p1,
  ax_vpf_p2, ax_vpf_c1, ax_vpf_c2, ax_vpf_c3, ax_vpf_j1, ax_vpf_j2, ax_vpf_j3,
  ax_vpf_efq, ax_vpf_q1, ax_vpf_q2, ax_vpf_q3, ax_vpf_eqrefl, ax_vpf_leibniz,
  ax_vpf_p3, ax_vpf_mp, ax_vpf_gen, ax_vpf_thy, ax_vpf_ind, ax_axiomsCodeT,
  ax_tc_zero, ax_tc_succ, ax_tc_cons, ax_runFn_nil, ax_runFn_cons,
  ax_allIn_nil, ax_allIn_cons, ax_chainOk_nil, ax_chainOk_cons
]

/-- `axioms` se parte en la teoría matemática y la maquinaria de coding. -/
theorem axioms_eq : axioms = coreAxioms ++ codingAxioms := rfl

/-- Todo axioma de la teoría está en `axioms`. -/
theorem coreAxioms_subset_axioms : coreAxioms ⊆ axioms :=
  axioms_eq ▸ List.subset_append_left _ _

/-- Pertenencia a la teoría implica pertenencia a `axioms`. -/
theorem mem_axioms_of_mem_core {f : Formula} (h : f ∈ coreAxioms) : f ∈ axioms :=
  coreAxioms_subset_axioms h

/-- `ax_axiomsCodeT` es invariante bajo desplazamiento (su único subtérmino no
    trivial, `listFormCodeM coreAxioms`, es cerrado). Aísla el término gigante en
    la prueba de `axioms_lift_eq`. -/
theorem ax_axiomsCodeT_lift : liftFormula 0 ax_axiomsCodeT = ax_axiomsCodeT := by
  simp only [ax_axiomsCodeT, liftFormula, axiomsCodeT, liftTerm, liftTerms, liftTerm_listFormCodeM]

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
--
-- Las meta-reglas de deducción (5 meta-axiomas ω — `imp_intro`, `gen`, `raa`,
-- `or_elim`, `ex_elim` — y los wrappers derivables `mp`, `and_intro`,
-- `and_elim_left/right`, `or_intro_left/right`, `false_elim`, `ex_intro`,
-- `iff_mp`, `iff_mpr`) son **lógica pura de FOL=** y viven ahora en
-- `FOL/MetaRules.lean` (refactor 2026-06-12, ver ADR-008 y
-- MINIMAL-AXIOMS.md §3.5.1). Se **re-exportan** aquí para que todo el código
-- existente (`Minimal.Axioms.or_elim`, `open Minimal.Axioms`, …) siga
-- resolviendo sin cambios.
export FOL.MetaRules (mp imp_intro gen raa dne and_intro and_elim_left and_elim_right
  or_intro_left or_intro_right or_elim false_elim ex_intro ex_elim iff_mp iff_mpr)

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
