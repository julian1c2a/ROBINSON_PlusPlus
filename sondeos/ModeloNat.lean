import ROBINSON_PlusPlus
import FOL.Semantics

/-!
# EL MODELO ESTÁNDAR de los 142 axiomas ⇒ `ConsistentH` es un TEOREMA

**Fecha**: 2026‑10‑05 (ADR‑119). Antes, del 2026‑09‑22 (ADR‑086) al 2026‑10‑05, este fichero era la capa
ARITMÉTICA sola: 25 de los 34 `coreAxioms`.

⬆️ **PROMOVIDO al build el mismo día (ADR‑120)**, partido en `Meta/ModeloCodigo.lean`, `Meta/ModeloEstandar.lean`,
`Meta/ModeloCodificacion.lean`, `Meta/SolidezPrf.lean` y `Meta/Consistencia.lean`: allí `consistencia`, `goedel_I` y
`goedel_II` son los nombres de producción. Este fichero se conserva como la versión en un solo fichero.

## 🏁 Qué demuestra

* `MN_axioms : ∀ v, contextSatisfies (MNV V₀) v axioms` — **un modelo de los 142**: los 34 de la teoría, los 107 de
  codificación y el ancla diagonal `ax_axiomsCodeT_def`.
* `consistentH : ConsistentH` — `¬ Prf ⊥`, por la solidez de `Prf` en todo modelo ESTÁNDAR (§6, `prf_sound`).
* `incompletitud_I : ¬ Prf godelCN` e `incompletitud_II : ¬ Prf consistencyFormula'` — `goedel_first_prf` y
  `goedel_second_prf` aplicados a `consistentH`: **Gödel I y II SIN HIPÓTESIS**.

Footprint de los cuatro, y de todo lo que imprime `#print axioms` al final: `[propext, Classical.choice,
Quot.sound]`. Ni `sorry`, ni `axiom`, ni `native_decide`.

## Cómo

* **§0–§1bis · aritmética y listas.** `nil = 0`, `cons a b = consN a b = pairN a b + 1` (ADR‑113): `pairN` es la
  biyección de Cantor, así que TODO `n` es una lista, y una sola. `unpairN` la invierte por recursión, y
  `decodeL`/`encodeL` son la biyección `ℕ ≅ List ℕ`.
* **§1ter · codificación.** Cada símbolo de los 107 es una función de `Nat` que mira la forma de su argumento
  (`nthN c 0` es la etiqueta) y recurre sobre los componentes, que son MENORES (`nthN_lt`): `substtcN`/`substtscN`,
  `liftcN`/`liftscN`, `substfcN`, `liftfcN`, `tcFnN`, `vpfN` (con `stepT`, la conclusión de cada etiqueta),
  `runFnN`, `premsOfN`, `allInN`, `chainOkN`, y `lineWFT`, las 21 RHS de `ax_lineWF_K` TRADUCIDAS (generadas del
  fuente, una por etiqueta). Las guardas `hasWit`/`hasWitF` son `Prop` sobre `Nat` (`hasWitN`, `hasWitFN`), y su
  evaluación es esa `Prop` para un término ARBITRARIO (`ev_hasWit`, `ev_hasWitF`).
* **§2 · el modelo `MNV V`**, PARAMÉTRICO en `V`, el valor de `axiomsCodeT`. Los 141 de la base valen para TODO `V`.
* **§4 · el ancla.** `V₀` es, por definición, el valor del lado derecho de `ax_axiomsCodeT_def`, que no nombra
  `axiomsCodeT`; en `MNV V₀` el ancla vale por construcción. No hace falta el lema diagonal semántico.

## ⛔ Las dos trampas, medidas

1. **El numeral astronómico del ancla** (`nD`, ADR‑117): vive dentro de `V₀`, PLEGADO. `v_ancla` va por `rw` con
   lemas ∀ (`ev_numeralM`, `ev_listFormCodeM`, …), y el único `rfl` (`V₀_def`) compara dos expresiones idénticas
   tras desplegar `V₀` un nivel.
2. **La altura de definición en el núcleo** (medido el 2026‑10‑05): con `MN` NO paramétrico, el lema
   `MN.func "axiomsCodeT" [] = V₀ := rfl` se comió 2,5 GB en 12 s y no acababa, aunque `V₀` fuera
   `@[irreducible]`: el núcleo ignora ese atributo y despliega primero el lado de MÁS altura, que es `V₀`, y sigue
   evaluándolo. Con `MNV V` y `V` VARIABLE, cada `rfl` es sobre una variable, y `V₀` sólo entra por INSTANCIACIÓN.
   🔑 *Un `rfl` contra un término gigante plegado no lo salva ningún atributo: se instancia un lema genérico.*

## Medido (2026‑10‑05, en local)

`lake env lean sondeos/ModeloNat.lean`: 0 errores, 0 avisos (con `linter.unusedSimpArgs` apagado), 56 s, pico de
memoria 5,48 GB.
⚠️ Un control negativo (que el modelo REFUTA `ax_tc_cons`, el axioma retirado que hacía inconsistente la teoría)
subió el pico por encima de 14 GB y se apartó: está pendiente, con otra forma.

## Lo que NO dice

* No dice que `G` ni `Con` sean VERDADERAS en `MNV V₀` (E10): `consistentH` no lo necesita.
* No dice que `V₀ = codeNatList axioms` (que en el modelo la regla `thy` acepte exactamente los 142): E10 lo pediría.
* No dice nada de `⊬¬G` (Rosser).
* Vive en `sondeos/`, FUERA del build (✏️ hasta ADR‑120, que lo promovió).

## Cómo re‑ejecutarlo

    lake env lean sondeos/ModeloNat.lean      # desde la raíz de RPP
-/

set_option linter.unusedSimpArgs false

namespace ModeloNat

/-! ## §1 · La raíz entera sobre `Nat`

Estilo `triN`: **recursión, sin división**, para que `omega` trate los productos como átomos. -/

def sqrtN : Nat → Nat
  | 0 => 0
  | n + 1 => if (sqrtN n + 1) * (sqrtN n + 1) ≤ n + 1 then sqrtN n + 1 else sqrtN n

/-- La única pieza no lineal.
    ⚠️ El sucesor va como `k+1+1` y **NO** como `k+2`: para `omega` el producto es un **ÁTOMO**,
    y `(k+2)*(k+2)` y `(k+1+1)*(k+1+1)` son átomos **distintos**. Con `k+2` no cierra. -/
theorem sq_lt_sq_succ (k : Nat) : (k + 1) * (k + 1) < (k + 1 + 1) * (k + 1 + 1) := by
  have h1 : (k + 1 + 1) * (k + 1 + 1) = (k + 1) * (k + 1) + 2 * (k + 1) + 1 := by
    rw [Nat.succ_mul, Nat.mul_succ]
    generalize (k + 1) * (k + 1) = A
    omega
  omega

/-- `ax14_sqrt_le` en el modelo: `sq (√x) ≤ x`. -/
theorem sqrtN_le : ∀ n : Nat, sqrtN n * sqrtN n ≤ n
  | 0 => by simp [sqrtN]
  | n + 1 => by
      have ih := sqrtN_le n
      simp only [sqrtN]
      by_cases h : (sqrtN n + 1) * (sqrtN n + 1) ≤ n + 1
      · rw [if_pos h]; exact h
      · rw [if_neg h]; omega

/-- `ax15_lt_succ_sqrt` en el modelo: `x < sq (σ (√x))`. -/
theorem lt_sq_succ_sqrtN : ∀ n : Nat, n < (sqrtN n + 1) * (sqrtN n + 1)
  | 0 => by simp [sqrtN]
  | n + 1 => by
      have ih := lt_sq_succ_sqrtN n
      have ih2 := sqrtN_le n
      simp only [sqrtN]
      by_cases h : (sqrtN n + 1) * (sqrtN n + 1) ≤ n + 1
      · rw [if_pos h]
        have hlt := sq_lt_sq_succ (sqrtN n)
        omega
      · rw [if_neg h]; exact Nat.lt_of_not_le h

/-! ## §1bis · Las LISTAS sobre `Nat` (2026‑10‑05)

`nil = 0` y `cons a b = consN a b = pairN a b + 1` (ADR‑113): **toda** `n` es una lista, y una sola —`pairN` es
la biyección de Cantor `ℕ² → ℕ`—. `unpairN` la invierte por recursión (recorre las diagonales en el orden de
`pairN`), `decodeL`/`encodeL` son la biyección `ℕ ≅ List ℕ`, y `concatN`, `memN` y `prodpN` son las operaciones
de `List` vistas a través de ella. Sin `Classical.choice`: `[propext, Quot.sound]`. -/

section Listas
open FOL
open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.CodeNumeralPrf ROBINSON_PlusPlus.Meta.CodeNatInjPrf

/-! ### Listas (copia de Listas.lean) -/

def unpairN : Nat → Nat × Nat
  | 0 => (0, 0)
  | n + 1 =>
    match unpairN n with
    | (0, b) => (b + 1, 0)
    | (a + 1, b) => (a, b + 1)

theorem pairN_unpairN : ∀ n : Nat, pairN (unpairN n).1 (unpairN n).2 = n
  | 0 => rfl
  | n + 1 => by
      have ih := pairN_unpairN n
      simp only [unpairN]
      split
      · rename_i b h
        rw [h] at ih
        simp only [pairN] at ih ⊢
        rw [Nat.zero_add] at ih
        show triN (b + 1 + 0) + 0 = n + 1
        rw [Nat.add_zero, Nat.add_zero, triN_succ]
        omega
      · rename_i a b h
        rw [h] at ih
        have ih' : triN (a + 1 + b) + b = n := ih
        show triN (a + (b + 1)) + (b + 1) = n + 1
        have e : a + (b + 1) = a + 1 + b := by omega
        rw [e]
        omega

theorem pairN_inj {a b a' b' : Nat} (h : pairN a b = pairN a' b') : And (a = a') (b = b') :=
  consN_inj (show consN a b = consN a' b' by simp only [consN, pairN] at h ⊢; omega)

theorem unpairN_pairN (a b : Nat) : unpairN (pairN a b) = (a, b) := by
  have h := pairN_unpairN (pairN a b)
  obtain ⟨h1, h2⟩ := pairN_inj h
  exact Prod.ext h1 h2

theorem le_triN : ∀ s : Nat, s < triN s + 1
  | 0 => by decide
  | s + 1 => by have := le_triN s; rw [triN_succ]; omega

theorem snd_le_pairN (a b : Nat) : b < pairN a b + 1 := by
  simp only [pairN]; omega

theorem fst_le_pairN (a b : Nat) : a < pairN a b + 1 := by
  have := le_triN (a + b)
  simp only [pairN]; omega

theorem unpairN_snd_lt (n : Nat) : (unpairN n).2 < n + 1 := by
  have h := pairN_unpairN n
  have := snd_le_pairN (unpairN n).1 (unpairN n).2
  omega

theorem unpairN_fst_lt (n : Nat) : (unpairN n).1 < n + 1 := by
  have h := pairN_unpairN n
  have := fst_le_pairN (unpairN n).1 (unpairN n).2
  omega

def decodeL : Nat → List Nat
  | 0 => []
  | n + 1 => (unpairN n).1 :: decodeL (unpairN n).2
termination_by n => n
decreasing_by exact unpairN_snd_lt n

def encodeL : List Nat → Nat
  | [] => 0
  | a :: l => consN a (encodeL l)

theorem consN_eq (a b : Nat) : consN a b = pairN a b + 1 := rfl

theorem decodeL_zero : decodeL 0 = [] := by rw [decodeL]

theorem decodeL_consN (a b : Nat) : decodeL (consN a b) = a :: decodeL b := by
  rw [consN_eq, decodeL, unpairN_pairN]

theorem decodeL_encodeL : ∀ l : List Nat, decodeL (encodeL l) = l
  | [] => decodeL_zero
  | a :: l => by rw [encodeL, decodeL_consN, decodeL_encodeL l]

theorem encodeL_decodeL (n : Nat) : encodeL (decodeL n) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => rw [decodeL_zero]; rfl
    | succ m =>
      rw [decodeL, encodeL, ih _ (unpairN_snd_lt m), consN_eq, pairN_unpairN]

def concatN (a b : Nat) : Nat := encodeL (decodeL a ++ decodeL b)
def memN (x l : Nat) : Prop := x ∈ decodeL l

theorem concatN_zero (b : Nat) : concatN 0 b = b := by
  rw [concatN, decodeL_zero, List.nil_append, encodeL_decodeL]

theorem concatN_consN (a b c : Nat) : concatN (consN a b) c = consN a (concatN b c) := by
  rw [concatN, decodeL_consN, List.cons_append, encodeL, concatN]

theorem memN_zero (x : Nat) : ¬ memN x 0 := by
  rw [memN, decodeL_zero]; exact List.not_mem_nil

theorem memN_consN (x a b : Nat) : memN x (consN a b) ↔ Or (x = a) (memN x b) := by
  rw [memN, decodeL_consN, List.mem_cons, memN]

/-! ### Accesores: `carc`, `cdrc`, `nthc`, `lenc` -/

def carN : Nat → Nat
  | 0 => 0
  | m + 1 => (unpairN m).1

def cdrN : Nat → Nat
  | 0 => 0
  | m + 1 => (unpairN m).2

/-- `nthc l i`: el `i`‑ésimo, por la cola (estructural en `i`). Fuera de rango, `0`. -/
def nthN (l : Nat) : Nat → Nat
  | 0 => carN l
  | i + 1 => nthN (cdrN l) i

def lenN (l : Nat) : Nat := (decodeL l).length

theorem carN_consN (a b : Nat) : carN (consN a b) = a := by
  rw [consN_eq, carN, unpairN_pairN]

theorem cdrN_consN (a b : Nat) : cdrN (consN a b) = b := by
  rw [consN_eq, cdrN, unpairN_pairN]

theorem nthN_cz (a b : Nat) : nthN (consN a b) 0 = a := carN_consN a b

theorem nthN_cs (a b i : Nat) : nthN (consN a b) (i + 1) = nthN b i := by
  rw [nthN, cdrN_consN]

theorem lenN_zero : lenN 0 = 0 := by rw [lenN, decodeL_zero]; rfl

theorem lenN_consN (a b : Nat) : lenN (consN a b) = lenN b + 1 := by
  rw [lenN, decodeL_consN, List.length_cons, lenN]

theorem carN_lt {l : Nat} (h : ¬ l = 0) : carN l < l := by
  cases l with
  | zero => exact absurd rfl h
  | succ m => exact unpairN_fst_lt m

theorem cdrN_lt {l : Nat} (h : ¬ l = 0) : cdrN l < l := by
  cases l with
  | zero => exact absurd rfl h
  | succ m => exact unpairN_snd_lt m

theorem nthN_zero_l : ∀ i : Nat, nthN 0 i = 0
  | 0 => rfl
  | i + 1 => nthN_zero_l i

theorem nthN_lt : ∀ (i : Nat) {l : Nat}, ¬ l = 0 → nthN l i < l
  | 0, _, h => carN_lt h
  | i + 1, l, h => by
      show nthN (cdrN l) i < l
      by_cases hc : cdrN l = 0
      · rw [hc, nthN_zero_l]; exact Nat.pos_of_ne_zero h
      · exact Nat.lt_trans (nthN_lt i hc) (cdrN_lt h)

theorem consN_car_cdr {l : Nat} (h : ¬ l = 0) : consN (carN l) (cdrN l) = l := by
  cases l with
  | zero => exact absurd rfl h
  | succ m => rw [consN_eq, carN, cdrN, pairN_unpairN]

/-! ### La sustitución y el lift sobre códigos de TÉRMINO -/

mutual
def substtcN (k s c : Nat) : Nat :=
  if h : c = 0 then 0
  else if nthN c 0 = 0 then
    (if k = nthN c 1 then s
     else if k < nthN c 1 then consN 0 (consN (nthN c 1 - 1) 0)
     else consN 0 (consN (nthN c 1) 0))
  else if nthN c 0 = 1 then consN 1 (consN (nthN c 1) (consN (substtscN k s (nthN c 2)) 0))
  else 0
termination_by c
decreasing_by exact nthN_lt 2 h

def substtscN (k s l : Nat) : Nat :=
  if _h : l = 0 then 0
  else consN (substtcN k s (carN l)) (substtscN k s (cdrN l))
termination_by l
decreasing_by
  · exact carN_lt _h
  · exact cdrN_lt _h
end

mutual
def liftcN (c t : Nat) : Nat :=
  if h : t = 0 then 0
  else if nthN t 0 = 0 then
    (if nthN t 1 < c then consN 0 (consN (nthN t 1) 0) else consN 0 (consN (nthN t 1 + 1) 0))
  else if nthN t 0 = 1 then consN 1 (consN (nthN t 1) (consN (liftscN c (nthN t 2)) 0))
  else 0
termination_by t
decreasing_by exact nthN_lt 2 h

def liftscN (c l : Nat) : Nat :=
  if _h : l = 0 then 0
  else consN (liftcN c (carN l)) (liftscN c (cdrN l))
termination_by l
decreasing_by
  · exact carN_lt _h
  · exact cdrN_lt _h
end

theorem substtcN_var (k s n : Nat) : substtcN k s (consN 0 (consN n 0)) =
    if k = n then s else if k < n then consN 0 (consN (n - 1) 0) else consN 0 (consN n 0) := by
  rw [substtcN, dif_neg (consN_ne_zero _ _), nthN_cz, if_pos rfl, nthN_cs, nthN_cz]

theorem substtcN_func (k s a b : Nat) : substtcN k s (consN 1 (consN a (consN b 0))) =
    consN 1 (consN a (consN (substtscN k s b) 0)) := by
  rw [substtcN, dif_neg (consN_ne_zero _ _), nthN_cz, if_neg (by decide), if_pos rfl,
    nthN_cs, nthN_cz, nthN_cs, nthN_cs, nthN_cz]

theorem substtscN_zero (k s : Nat) : substtscN k s 0 = 0 := by
  rw [substtscN, dif_pos rfl]

theorem substtscN_consN (k s a b : Nat) : substtscN k s (consN a b) =
    consN (substtcN k s a) (substtscN k s b) := by
  rw [substtscN, dif_neg (consN_ne_zero _ _), carN_consN, cdrN_consN]

theorem liftcN_var (c n : Nat) : liftcN c (consN 0 (consN n 0)) =
    if n < c then consN 0 (consN n 0) else consN 0 (consN (n + 1) 0) := by
  rw [liftcN, dif_neg (consN_ne_zero _ _), nthN_cz, if_pos rfl, nthN_cs, nthN_cz]

theorem liftcN_func (c a b : Nat) : liftcN c (consN 1 (consN a (consN b 0))) =
    consN 1 (consN a (consN (liftscN c b) 0)) := by
  rw [liftcN, dif_neg (consN_ne_zero _ _), nthN_cz, if_neg (by decide), if_pos rfl,
    nthN_cs, nthN_cz, nthN_cs, nthN_cs, nthN_cz]

theorem liftscN_zero (c : Nat) : liftscN c 0 = 0 := by
  rw [liftscN, dif_pos rfl]

theorem liftscN_consN (c a b : Nat) : liftscN c (consN a b) = consN (liftcN c a) (liftscN c b) := by
  rw [liftscN, dif_neg (consN_ne_zero _ _), carN_consN, cdrN_consN]

/-! ### La sustitución y el lift sobre códigos de FÓRMULA -/

def substfcN (v t f : Nat) : Nat :=
  if h : f = 0 then 0
  else if nthN f 0 = 2 then consN 2 0
  else if nthN f 0 = 3 then consN 3 (consN (nthN f 1) (consN (substtscN v t (nthN f 2)) 0))
  else if nthN f 0 = 4 then consN 4 (consN (substtcN v t (nthN f 1)) (consN (substtcN v t (nthN f 2)) 0))
  else if nthN f 0 = 5 then consN 5 (consN (substfcN v t (nthN f 1)) (consN (substfcN v t (nthN f 2)) 0))
  else if nthN f 0 = 6 then consN 6 (consN (substfcN (v + 1) (liftcN 0 t) (nthN f 1)) 0)
  else if nthN f 0 = 7 then consN 7 (consN (substfcN v t (nthN f 1)) (consN (substfcN v t (nthN f 2)) 0))
  else if nthN f 0 = 8 then consN 8 (consN (substfcN v t (nthN f 1)) (consN (substfcN v t (nthN f 2)) 0))
  else if nthN f 0 = 9 then consN 9 (consN (substfcN (v + 1) (liftcN 0 t) (nthN f 1)) 0)
  else 0
termination_by f
decreasing_by all_goals exact nthN_lt _ h

def liftfcN (c f : Nat) : Nat :=
  if h : f = 0 then 0
  else if nthN f 0 = 2 then consN 2 0
  else if nthN f 0 = 3 then consN 3 (consN (nthN f 1) (consN (liftscN c (nthN f 2)) 0))
  else if nthN f 0 = 4 then consN 4 (consN (liftcN c (nthN f 1)) (consN (liftcN c (nthN f 2)) 0))
  else if nthN f 0 = 5 then consN 5 (consN (liftfcN c (nthN f 1)) (consN (liftfcN c (nthN f 2)) 0))
  else if nthN f 0 = 6 then consN 6 (consN (liftfcN (c + 1) (nthN f 1)) 0)
  else if nthN f 0 = 7 then consN 7 (consN (liftfcN c (nthN f 1)) (consN (liftfcN c (nthN f 2)) 0))
  else if nthN f 0 = 8 then consN 8 (consN (liftfcN c (nthN f 1)) (consN (liftfcN c (nthN f 2)) 0))
  else if nthN f 0 = 9 then consN 9 (consN (liftfcN (c + 1) (nthN f 1)) 0)
  else 0
termination_by f
decreasing_by all_goals exact nthN_lt _ h

/-- Las ecuaciones, una por constructor: `simp only` con los accesores sobre `consN` y la
    aritmética de literales; nada recursivo se despliega más de un nivel. -/
theorem substfcN_bot (v t : Nat) : substfcN v t (consN 2 0) = consN 2 0 := by
  rw [substfcN]; simp only [consN_ne_zero, nthN_cz, dite_false, ite_true]

theorem substfcN_atom (v t a b : Nat) : substfcN v t (consN 3 (consN a (consN b 0))) =
    consN 3 (consN a (consN (substtscN v t b) 0)) := by
  rw [substfcN]; simp only [consN_ne_zero, nthN_cz, nthN_cs, dite_false]; rfl

theorem substfcN_eq (v t a b : Nat) : substfcN v t (consN 4 (consN a (consN b 0))) =
    consN 4 (consN (substtcN v t a) (consN (substtcN v t b) 0)) := by
  rw [substfcN]; simp only [consN_ne_zero, nthN_cz, nthN_cs, dite_false]; rfl

theorem substfcN_impl (v t a b : Nat) : substfcN v t (consN 5 (consN a (consN b 0))) =
    consN 5 (consN (substfcN v t a) (consN (substfcN v t b) 0)) := by
  rw [substfcN]; simp only [consN_ne_zero, nthN_cz, nthN_cs, dite_false]; rfl

theorem substfcN_forall (v t a : Nat) : substfcN v t (consN 6 (consN a 0)) =
    consN 6 (consN (substfcN (v + 1) (liftcN 0 t) a) 0) := by
  rw [substfcN]; simp only [consN_ne_zero, nthN_cz, nthN_cs, dite_false]; rfl

theorem substfcN_and (v t a b : Nat) : substfcN v t (consN 7 (consN a (consN b 0))) =
    consN 7 (consN (substfcN v t a) (consN (substfcN v t b) 0)) := by
  rw [substfcN]; simp only [consN_ne_zero, nthN_cz, nthN_cs, dite_false]; rfl

theorem substfcN_or (v t a b : Nat) : substfcN v t (consN 8 (consN a (consN b 0))) =
    consN 8 (consN (substfcN v t a) (consN (substfcN v t b) 0)) := by
  rw [substfcN]; simp only [consN_ne_zero, nthN_cz, nthN_cs, dite_false]; rfl

theorem substfcN_ex (v t a : Nat) : substfcN v t (consN 9 (consN a 0)) =
    consN 9 (consN (substfcN (v + 1) (liftcN 0 t) a) 0) := by
  rw [substfcN]; simp only [consN_ne_zero, nthN_cz, nthN_cs, dite_false]; rfl

theorem liftfcN_bot (c : Nat) : liftfcN c (consN 2 0) = consN 2 0 := by
  rw [liftfcN]; simp only [consN_ne_zero, nthN_cz, dite_false, ite_true]

theorem liftfcN_atom (c a b : Nat) : liftfcN c (consN 3 (consN a (consN b 0))) =
    consN 3 (consN a (consN (liftscN c b) 0)) := by
  rw [liftfcN]; simp only [consN_ne_zero, nthN_cz, nthN_cs, dite_false]; rfl

theorem liftfcN_eq (c a b : Nat) : liftfcN c (consN 4 (consN a (consN b 0))) =
    consN 4 (consN (liftcN c a) (consN (liftcN c b) 0)) := by
  rw [liftfcN]; simp only [consN_ne_zero, nthN_cz, nthN_cs, dite_false]; rfl

theorem liftfcN_impl (c a b : Nat) : liftfcN c (consN 5 (consN a (consN b 0))) =
    consN 5 (consN (liftfcN c a) (consN (liftfcN c b) 0)) := by
  rw [liftfcN]; simp only [consN_ne_zero, nthN_cz, nthN_cs, dite_false]; rfl

theorem liftfcN_forall (c a : Nat) : liftfcN c (consN 6 (consN a 0)) =
    consN 6 (consN (liftfcN (c + 1) a) 0) := by
  rw [liftfcN]; simp only [consN_ne_zero, nthN_cz, nthN_cs, dite_false]; rfl

theorem liftfcN_and (c a b : Nat) : liftfcN c (consN 7 (consN a (consN b 0))) =
    consN 7 (consN (liftfcN c a) (consN (liftfcN c b) 0)) := by
  rw [liftfcN]; simp only [consN_ne_zero, nthN_cz, nthN_cs, dite_false]; rfl

theorem liftfcN_or (c a b : Nat) : liftfcN c (consN 8 (consN a (consN b 0))) =
    consN 8 (consN (liftfcN c a) (consN (liftfcN c b) 0)) := by
  rw [liftfcN]; simp only [consN_ne_zero, nthN_cz, nthN_cs, dite_false]; rfl

theorem liftfcN_ex (c a : Nat) : liftfcN c (consN 9 (consN a 0)) =
    consN 9 (consN (liftfcN (c + 1) a) 0) := by
  rw [liftfcN]; simp only [consN_ne_zero, nthN_cz, nthN_cs, dite_false]; rfl


theorem concatN_assoc (a b c : Nat) : concatN (concatN a b) c = concatN a (concatN b c) := by
  simp only [concatN, decodeL_encodeL, List.append_assoc]

theorem memN_concatN (x a b : Nat) : memN x (concatN a b) ↔ Or (memN x a) (memN x b) := by
  rw [memN, concatN, decodeL_encodeL, List.mem_append, memN, memN]

def prodpN (l : Nat) : Nat :=
  ((decodeL l).map (fun h => (unpairN h).1 ^ (unpairN h).2)).foldr (· * ·) 1

theorem prodpN_zero : prodpN 0 = 1 := by
  rw [prodpN, decodeL_zero]; rfl

theorem prodpN_consN_pairN (p e t : Nat) : prodpN (consN (pairN p e) t) = p ^ e * prodpN t := by
  rw [prodpN, decodeL_consN, List.map_cons, List.foldr_cons, unpairN_pairN, prodpN]

/-! ### Los constructores de código, como valores -/

abbrev botcN : Nat := consN 2 0
abbrev eqcN (a b : Nat) : Nat := consN 4 (consN a (consN b 0))
abbrev implcN (a b : Nat) : Nat := consN 5 (consN a (consN b 0))
abbrev forallcN (a : Nat) : Nat := consN 6 (consN a 0)
abbrev andcN (a b : Nat) : Nat := consN 7 (consN a (consN b 0))
abbrev orcN (a b : Nat) : Nat := consN 8 (consN a (consN b 0))
abbrev excN (a : Nat) : Nat := consN 9 (consN a 0)

/-- Los códigos CERRADOS que incrustan `ax_vpf_ind`/`_listInd` y `ax_lineWF_ind`/`_listInd`: su valor se nombra,
    nunca se calcula (`codeNatTerm` de un símbolo `String`). -/
def TC0 : Nat := codeNatTerm zero
def TCS : Nat := codeNatTerm (succ (.var 0))
def TNIL : Nat := codeNatTerm nil
def TCONS : Nat := codeNatTerm (cons (.var 1) (.var 0))

/-! ### `tcFn`: el código del numeral, por recursión estructural -/

def tcFnN : Nat → Nat
  | 0 => consN 1 (consN (codeNatStr zero_sym) (consN 0 0))
  | n + 1 => consN 1 (consN (codeNatStr succ_sym) (consN (consN (tcFnN n) 0) 0))

/-! ### `validProofFn`: la conclusión de una línea `⟨K, a, b, d⟩` según su etiqueta -/

def stepT : Nat → Nat → Nat → Nat → Nat
  | 0, a, b, _ => implcN a (implcN b a)
  | 1, a, b, d => implcN (implcN a (implcN b d)) (implcN (implcN a b) (implcN a d))
  | 2, a, b, _ => implcN a (implcN b (andcN a b))
  | 3, a, b, _ => implcN (andcN a b) a
  | 4, a, b, _ => implcN (andcN a b) b
  | 5, a, b, _ => implcN a (orcN a b)
  | 6, a, b, _ => implcN b (orcN a b)
  | 7, a, b, d => implcN (orcN a b) (implcN (implcN a d) (implcN (implcN b d) d))
  | 8, a, _, _ => implcN botcN a
  | 9, a, b, _ => implcN (forallcN a) (substfcN 0 b a)
  | 10, a, b, _ => implcN (substfcN 0 b a) (excN a)
  | 11, a, b, _ => implcN (forallcN (implcN a (liftfcN 0 b))) (implcN (excN a) b)
  | 12, a, _, _ => eqcN a a
  | 13, a, b, d => implcN (eqcN b d) (implcN (substfcN 0 b a) (substfcN 0 d a))
  | 14, a, _, _ => implcN (implcN (implcN a botcN) botcN) a
  | 15, a, _, _ => a
  | 16, a, _, _ => a
  | 17, a, _, _ => forallcN a
  | 18, a, _, _ => implcN (substfcN 0 TC0 a)
      (implcN (forallcN (implcN a (substfcN 0 TCS (liftfcN 1 a)))) (forallcN a))
  | 19, a, b, _ => implcN (forallcN (implcN (liftfcN 0 a) b)) (implcN a (forallcN b))
  | 20, a, _, _ => implcN (substfcN 0 TNIL a)
      (implcN (forallcN (forallcN (implcN (liftfcN 1 a) (substfcN 0 TCONS (liftfcN 2 (liftfcN 1 a))))))
        (forallcN a))
  | _, _, _, _ => 0

def stepN (x : Nat) : Nat := stepT (nthN x 0) (nthN x 1) (nthN x 2) (nthN x 3)

def vpfL : Nat → List Nat → Nat
  | c, [] => c
  | c, x :: r => vpfL (concatN c (consN (stepN x) 0)) r

def vpfN (c r : Nat) : Nat := vpfL c (decodeL r)

theorem vpfN_zero (c : Nat) : vpfN c 0 = c := by rw [vpfN, decodeL_zero]; rfl

theorem vpfN_consN (c x r : Nat) : vpfN c (consN x r) = vpfN (concatN c (consN (stepN x) 0)) r := by
  rw [vpfN, decodeL_consN]; rfl

/-! ### `runFn`, `premsOf`, `allIn`, `chainOk` -/

def runFnL : Nat → List Nat → Nat
  | c, [] => c
  | c, x :: r => runFnL (concatN c (consN (carN x) 0)) r

def runFnN (c r : Nat) : Nat := runFnL c (decodeL r)

theorem runFnN_zero (c : Nat) : runFnN c 0 = c := by rw [runFnN, decodeL_zero]; rfl

theorem runFnN_consN (c x r : Nat) : runFnN c (consN x r) = runFnN (concatN c (consN (carN x) 0)) r := by
  rw [runFnN, decodeL_consN]; rfl

/-- Las premisas de una línea `⟨concl, K, args…⟩`: `mp` (16) y `gen` (17); las demás, ninguna. -/
def premsOfN (x : Nat) : Nat :=
  if nthN x 1 = 16 then consN (implcN (nthN x 2) (nthN x 0)) (consN (nthN x 2) 0)
  else if nthN x 1 = 17 then consN (nthN x 2) 0
  else 0

def allInN (c L : Nat) : Prop := ∀ y, memN y L → memN y c

theorem allInN_zero (c : Nat) : allInN c 0 := fun y h => absurd h (memN_zero y)

theorem allInN_consN (c a t : Nat) : allInN c (consN a t) ↔ And (memN a c) (allInN c t) := by
  constructor
  · intro h
    exact ⟨h a ((memN_consN a a t).mpr (Or.inl rfl)), fun y hy => h y ((memN_consN y a t).mpr (Or.inr hy))⟩
  · intro h y hy
    cases (memN_consN y a t).mp hy with
    | inl e => rw [e]; exact h.1
    | inr h' => exact h.2 y h'

/-! ### Las guardas `hasWit`/`hasWitF`, como `Prop` sobre `Nat` (espejo de `Minimal/Axioms.lean:1196-1277`) -/

def shapeUnN (X k : Nat) : Prop := X = consN k (consN (nthN X 1) 0)
def shapeBinN (X k : Nat) : Prop := X = consN k (consN (nthN X 1) (consN (nthN X 2) 0))
def argsInN (wT Y : Nat) : Prop := ∀ i, i < lenN Y → memN (nthN Y i) wT
def isTermCodeE1N (wT X : Nat) : Prop := Or (shapeUnN X 0) (And (shapeBinN X 1) (argsInN wT (nthN X 2)))
def wfAll1N (w : Nat) : Prop := ∀ i, i < lenN w → isTermCodeE1N w (nthN w i)
def hasWitN (c : Nat) : Prop := ∃ w, And (wfAll1N w) (memN c w)
def clBotN (X : Nat) : Prop := X = consN 2 0
def clAtomN (wT X : Nat) : Prop := And (shapeBinN X 3) (argsInN wT (nthN X 2))
def clEqN (wT X : Nat) : Prop := And (shapeBinN X 4) (And (memN (nthN X 1) wT) (memN (nthN X 2) wT))
def clBinN (wF X k : Nat) : Prop := And (shapeBinN X k) (And (memN (nthN X 1) wF) (memN (nthN X 2) wF))
def clUnN (wF X k : Nat) : Prop := And (shapeUnN X k) (memN (nthN X 1) wF)
def isFormCodeE2N (wF wT X : Nat) : Prop :=
  Or (clBotN X) (Or (clAtomN wT X) (Or (clEqN wT X) (Or (clBinN wF X 5) (Or (clUnN wF X 6)
    (Or (clBinN wF X 7) (Or (clBinN wF X 8) (clUnN wF X 9)))))))
def wfAllFN (wF wT : Nat) : Prop := ∀ i, i < lenN wF → isFormCodeE2N wF wT (nthN wF i)
def hasWitFN (c : Nat) : Prop := ∃ wF, ∃ wT, And (And (wfAll1N wT) (wfAllFN wF wT)) (memN c wF)

/-! ### El valor del ANCLA: el de su lado derecho, que no nombra `axiomsCodeT`

⛔ Ni se evalúa ni se despliega: es una expresión de `Nat` con el código de los 141 de la base y el de `δ`,
y las pruebas sólo la mueven por `rw` con lemas ∀ (el numeral astronómico del ancla vive aquí dentro, como
`codeNat (psiD axiomsBase)`, PLEGADO). -/

def codeNatList : List Formula → Nat
  | [] => 0
  | f :: fs => consN (codeNat f) (codeNatList fs)

def V₀ : Nat :=
  concatN (codeNatList axiomsBase)
    (consN (substfcN 0 (tcFnN (codeNat (psiD axiomsBase))) (codeNat (psiD axiomsBase))) 0)

/-! ### `lineWF`, por etiqueta -/

/-- Las 21 RHS de `ax_lineWF_K`, traducidas a `Prop` sobre `Nat`: generadas del fuente por un script (en el
    scratchpad de la sesión del 2026‑10‑05, no versionado) y después parametrizadas en `V` a mano (la firma y
    el caso `thy`). La correspondencia la comprueba el núcleo: `v_lineWF_*` cierra por `Iff.rfl`. -/
def lineWFT (V : Nat) : Nat → Nat → Prop
  | 0, x => And (lenN x = 4)
      ((carN x) = implcN (nthN x (2))
        (implcN (nthN x (3)) (nthN x (2))))   -- p1
  | 1, x => And (lenN x = 5) ((carN x) = implcN (implcN (nthN x (2)) (implcN (nthN x (3)) (nthN x (4)))) (implcN (implcN (nthN x (2)) (nthN x (3))) (implcN (nthN x (2)) (nthN x (4)))))   -- p2
  | 2, x => And (lenN x = 4) ((carN x) = implcN (nthN x (2)) (implcN (nthN x (3)) (andcN (nthN x (2)) (nthN x (3)))))   -- c1
  | 3, x => And (lenN x = 4) ((carN x) = implcN (andcN (nthN x (2)) (nthN x (3))) (nthN x (2)))   -- c2
  | 4, x => And (lenN x = 4) ((carN x) = implcN (andcN (nthN x (2)) (nthN x (3))) (nthN x (3)))   -- c3
  | 5, x => And (lenN x = 4) ((carN x) = implcN (nthN x (2)) (orcN (nthN x (2)) (nthN x (3))))   -- j1
  | 6, x => And (lenN x = 4) ((carN x) = implcN (nthN x (3)) (orcN (nthN x (2)) (nthN x (3))))   -- j2
  | 7, x => And (lenN x = 5) ((carN x) = implcN (orcN (nthN x (2)) (nthN x (3))) (implcN (implcN (nthN x (2)) (nthN x (4))) (implcN (implcN (nthN x (3)) (nthN x (4))) (nthN x (4)))))   -- j3
  | 8, x => And (lenN x = 3) ((carN x) = implcN (botcN) (nthN x (2)))   -- efq
  | 9, x => And (lenN x = 4) (And (hasWitFN (nthN x (2))) (And (hasWitN (nthN x (3))) ((carN x) = implcN (forallcN (nthN x (2))) (substfcN 0 (nthN x (3)) (nthN x (2))))))   -- q1
  | 10, x => And (lenN x = 4) (And (hasWitFN (nthN x (2))) (And (hasWitN (nthN x (3))) ((carN x) = implcN (substfcN 0 (nthN x (3)) (nthN x (2))) (excN (nthN x (2))))))   -- q2
  | 11, x => And (lenN x = 4) (And (hasWitFN (nthN x (3))) ((carN x) = implcN (forallcN (implcN (nthN x (2)) (liftfcN 0 (nthN x (3))))) (implcN (excN (nthN x (2))) (nthN x (3)))))   -- q3
  | 12, x => And (lenN x = 3)
      ((carN x) = eqcN (nthN x (2)) (nthN x (2)))   -- eqrefl
  | 13, x => And (lenN x = 5) (And (hasWitFN (nthN x (2))) (And (hasWitN (nthN x (3))) (And (hasWitN (nthN x (4))) ((carN x) = implcN (eqcN (nthN x (3)) (nthN x (4))) (implcN (substfcN 0 (nthN x (3)) (nthN x (2))) (substfcN 0 (nthN x (4)) (nthN x (2))))))))   -- leibniz
  | 14, x => And (lenN x = 3) ((carN x) = implcN (implcN (implcN (nthN x (2)) (botcN)) (botcN)) (nthN x (2)))   -- p3
  | 15, x => And (lenN x = 2)
      (memN (carN x) V)   -- thy
  | 16, x => (lenN x = 3)   -- mp
  | 17, x => And (lenN x = 3) ((carN x) = forallcN (nthN x (2)))   -- gen
  | 18, x => And (lenN x = 3) (And (hasWitFN (nthN x (2))) ((carN x) = implcN (substfcN 0 (TC0) (nthN x (2))) (implcN (forallcN (implcN (nthN x (2)) (substfcN 0 (TCS) (liftfcN 1 (nthN x (2)))))) (forallcN (nthN x (2))))))   -- ind
  | 19, x => And (lenN x = 4) (And (hasWitFN (nthN x (2))) ((carN x) = implcN (forallcN (implcN (liftfcN 0 (nthN x (2))) (nthN x (3)))) (implcN (nthN x (2)) (forallcN (nthN x (3))))))   -- qconf
  | 20, x => And (lenN x = 3) (And (hasWitFN (nthN x (2))) ((carN x) = implcN (substfcN 0 (TNIL) (nthN x (2))) (implcN (forallcN (forallcN (implcN (liftfcN 1 (nthN x (2))) (substfcN 0 (TCONS) (liftfcN 2 (liftfcN 1 (nthN x (2)))))))) (forallcN (nthN x (2))))))   -- listInd
  | _, _ => False

/-- `lineWF`: etiqueta ≤ 20 y la RHS de su etiqueta. Así `ax_lineWF_inv` vale por construcción. `V` es el valor
    de `axiomsCodeT` (la regla `thy` mira dentro): todo es PARAMÉTRICO en él, y sólo el ancla lo fija en `V₀`. -/
def lineWFN (V x : Nat) : Prop := And (nthN x 1 < 21) (lineWFT V (nthN x 1) x)

theorem lineWFN_of_tag {V x K : Nat} (h : nthN x 1 = K) (hK : K < 21) : lineWFN V x ↔ lineWFT V K x := by
  rw [lineWFN, h]
  exact ⟨fun h' => h'.2, fun h' => ⟨hK, h'⟩⟩

def chainOkL (V : Nat) : Nat → List Nat → Prop
  | _, [] => True
  | c, x :: r => And (And (lineWFN V x) (allInN c (premsOfN x))) (chainOkL V (concatN c (consN (carN x) 0)) r)

def chainOkN (V c p : Nat) : Prop := chainOkL V c (decodeL p)

theorem chainOkN_zero (V c : Nat) : chainOkN V c 0 := by rw [chainOkN, decodeL_zero]; trivial

theorem chainOkN_consN (V c x r : Nat) : chainOkN V c (consN x r) ↔
    And (And (lineWFN V x) (allInN c (premsOfN x))) (chainOkN V (concatN c (consN (carN x) 0)) r) := by
  rw [chainOkN, decodeL_consN]; exact Iff.rfl

end Listas

end ModeloNat

/-! ## §2 · LA INTERPRETACIÓN

⚠️ `open` acotado: fuera de esta sección `≤` resuelve al símbolo OBJETO `le` (ADR‑085 §3). -/

section Interpretacion
open FOL
open FOL.Metamath.Semantics
open ROBINSON_PlusPlus.Minimal.Axioms
open ModeloNat

variable {V : Nat}

/-- **El modelo estándar**: los 28 símbolos de función y los 5 de relación de los 142. Las listas, por la
    biyección de Cantor; los símbolos de codificación, por recursión (sobre la etiqueta de su argumento los de
    sustitución y lift, sobre `decodeL` `validProofFn`/`runFn`/`chainOk`, sobre el número `tcFn`); y
    `axiomsCodeT` por `V`, el PARÁMETRO: sólo la instancia `MNV V₀` lo fija en el valor del lado derecho del
    ancla. -/
def MNV (V : Nat) : Model Nat where
  func := fun s args =>
    match s, args with
    | "0",  []     => 0
    | "σ",  [a]    => a + 1
    | "+",  [a, b] => a + b
    | "*",  [a, b] => a * b
    | "−",  [a, b] => a - b            -- monus, como dice el comentario de `sub_sym`
    | "√",  [a]    => sqrtN a
    | "/₂", [a]    => a / 2
    | "%₂", [a]    => a % 2
    | "τ",  [a]    => a - 1            -- `pred`
    | "^",  [a, b] => a ^ b
    | "::", [a, b] => consN a b
    | "##", [a, b] => concatN a b
    | "Π_p", [l]   => prodpN l
    | "substtc", [k, s, c] => substtcN k s c
    | "substtsc", [k, s, c] => substtscN k s c
    | "liftc", [c, t] => liftcN c t
    | "liftsc", [c, t] => liftscN c t
    | "substfc", [v, t, f] => substfcN v t f
    | "liftfc", [c, f] => liftfcN c f
    | "carc", [l] => carN l
    | "cdrc", [l] => cdrN l
    | "lenc", [l] => lenN l
    | "nthc", [l, i] => nthN l i
    | "runFn", [c, r] => runFnN c r
    | "validProofFn", [c, r] => vpfN c r
    | "tcFn", [t] => tcFnN t
    | "premsOf", [l] => premsOfN l
    | "axiomsCodeT", [] => V
    | _, _         => 0
  rel := fun s args =>
    match s, args with
    | "<", [a, b] => a < b
    | "∈", [x, l] => memN x l
    | "allIn", [c, l] => allInN c l
    | "lineWF", [l] => lineWFN V l
    | "chainOk", [c, p] => chainOkN V c p
    | _, _        => False

/-! ### Un lema `rfl` por símbolo: así `simp` no tiene que abrir el `match` de 33 ramas -/

theorem MN_zero : (MNV V).func "0" [] = 0 := rfl
theorem MN_succ (a : Nat) : (MNV V).func "σ" [a] = a + 1 := rfl
theorem MN_pred (a : Nat) : (MNV V).func "τ" [a] = a - 1 := rfl
theorem MN_cons (a b : Nat) : (MNV V).func "::" [a, b] = consN a b := rfl
theorem MN_concat (a b : Nat) : (MNV V).func "##" [a, b] = concatN a b := rfl
theorem MN_substtc (k s c : Nat) : (MNV V).func "substtc" [k, s, c] = substtcN k s c := rfl
theorem MN_substtsc (k s c : Nat) : (MNV V).func "substtsc" [k, s, c] = substtscN k s c := rfl
theorem MN_liftc (c t : Nat) : (MNV V).func "liftc" [c, t] = liftcN c t := rfl
theorem MN_liftsc (c t : Nat) : (MNV V).func "liftsc" [c, t] = liftscN c t := rfl
theorem MN_substfc (v t f : Nat) : (MNV V).func "substfc" [v, t, f] = substfcN v t f := rfl
theorem MN_liftfc (c f : Nat) : (MNV V).func "liftfc" [c, f] = liftfcN c f := rfl
theorem MN_carc (l : Nat) : (MNV V).func "carc" [l] = carN l := rfl
theorem MN_cdrc (l : Nat) : (MNV V).func "cdrc" [l] = cdrN l := rfl
theorem MN_lenc (l : Nat) : (MNV V).func "lenc" [l] = lenN l := rfl
theorem MN_nthc (l i : Nat) : (MNV V).func "nthc" [l, i] = nthN l i := rfl
theorem MN_runFn (c r : Nat) : (MNV V).func "runFn" [c, r] = runFnN c r := rfl
theorem MN_vpf (c r : Nat) : (MNV V).func "validProofFn" [c, r] = vpfN c r := rfl
theorem MN_tcFn (t : Nat) : (MNV V).func "tcFn" [t] = tcFnN t := rfl
theorem MN_premsOf (l : Nat) : (MNV V).func "premsOf" [l] = premsOfN l := rfl
theorem MN_axiomsCodeT : (MNV V).func "axiomsCodeT" [] = V := rfl
theorem MN_lt (a b : Nat) : (MNV V).rel "<" [a, b] = (a < b) := rfl
theorem MN_mem (x l : Nat) : (MNV V).rel "∈" [x, l] = memN x l := rfl
theorem MN_allIn (c l : Nat) : (MNV V).rel "allIn" [c, l] = allInN c l := rfl
theorem MN_lineWF (l : Nat) : (MNV V).rel "lineWF" [l] = lineWFN V l := rfl
theorem MN_chainOk (c p : Nat) : (MNV V).rel "chainOk" [c, p] = chainOkN V c p := rfl

/-! ### La evaluación de los CÓDIGOS cerrados: por inducción, nunca por cómputo -/

theorem ev_numeralM (v : Nat → Nat) : ∀ n : Nat, evalTerm (MNV V) v (numeralM n) = n
  | 0 => rfl
  | n + 1 => by
      show (MNV V).func succ_sym [evalTerm (MNV V) v (numeralM n)] = n + 1
      rw [ev_numeralM v n]; rfl

theorem ev_charsCodeM (v : Nat → Nat) : ∀ cs : List Char, evalTerm (MNV V) v (charsCodeM cs) = codeNatChars cs
  | [] => rfl
  | c :: cs => by
      show (MNV V).func cons_sym [evalTerm (MNV V) v (numeralM c.toNat), evalTerm (MNV V) v (charsCodeM cs)] =
        consN c.toNat (codeNatChars cs)
      rw [ev_numeralM, ev_charsCodeM v cs]; rfl

theorem ev_strCodeM (v : Nat → Nat) (s : String) : evalTerm (MNV V) v (strCodeM s) = codeNatStr s :=
  ev_charsCodeM v s.toList

mutual
theorem ev_termCodeM (v : Nat → Nat) (t : Term) : evalTerm (MNV V) v (termCodeM t) = codeNatTerm t := by
  match t with
  | .var n =>
    show (MNV V).func cons_sym [evalTerm (MNV V) v (numeralM 0),
        (MNV V).func cons_sym [evalTerm (MNV V) v (numeralM n), (MNV V).func zero_sym []]] = consN 0 (consN n 0)
    rw [ev_numeralM, ev_numeralM]; rfl
  | .func s ts =>
    show (MNV V).func cons_sym [evalTerm (MNV V) v (numeralM 1),
        (MNV V).func cons_sym [evalTerm (MNV V) v (strCodeM s),
          (MNV V).func cons_sym [evalTerm (MNV V) v (termsCodeM ts), (MNV V).func zero_sym []]]] =
      consN 1 (consN (codeNatStr s) (consN (codeNatTerms ts) 0))
    rw [ev_numeralM, ev_strCodeM, ev_termsCodeM v ts]; rfl
theorem ev_termsCodeM (v : Nat → Nat) (ts : List Term) : evalTerm (MNV V) v (termsCodeM ts) = codeNatTerms ts := by
  match ts with
  | [] => rfl
  | t :: ts' =>
    show (MNV V).func cons_sym [evalTerm (MNV V) v (termCodeM t), evalTerm (MNV V) v (termsCodeM ts')] =
      consN (codeNatTerm t) (codeNatTerms ts')
    rw [ev_termCodeM v t, ev_termsCodeM v ts']; rfl
end

theorem ev_formCodeM (v : Nat → Nat) : ∀ φ : Formula, evalTerm (MNV V) v (formCodeM φ) = codeNat φ
  | .bottom => by
      show (MNV V).func cons_sym [evalTerm (MNV V) v (numeralM 2), (MNV V).func zero_sym []] = consN 2 0
      rw [ev_numeralM]; rfl
  | .atom p ts => by
      show (MNV V).func cons_sym [evalTerm (MNV V) v (numeralM 3),
          (MNV V).func cons_sym [evalTerm (MNV V) v (strCodeM p),
            (MNV V).func cons_sym [evalTerm (MNV V) v (termsCodeM ts), (MNV V).func zero_sym []]]] =
        consN 3 (consN (codeNatStr p) (consN (codeNatTerms ts) 0))
      rw [ev_numeralM, ev_strCodeM, ev_termsCodeM]; rfl
  | .eq t u => by
      show (MNV V).func cons_sym [evalTerm (MNV V) v (numeralM 4),
          (MNV V).func cons_sym [evalTerm (MNV V) v (termCodeM t),
            (MNV V).func cons_sym [evalTerm (MNV V) v (termCodeM u), (MNV V).func zero_sym []]]] =
        consN 4 (consN (codeNatTerm t) (consN (codeNatTerm u) 0))
      rw [ev_numeralM, ev_termCodeM, ev_termCodeM]; rfl
  | .impl a b => by
      show (MNV V).func cons_sym [evalTerm (MNV V) v (numeralM 5),
          (MNV V).func cons_sym [evalTerm (MNV V) v (formCodeM a),
            (MNV V).func cons_sym [evalTerm (MNV V) v (formCodeM b), (MNV V).func zero_sym []]]] =
        consN 5 (consN (codeNat a) (consN (codeNat b) 0))
      rw [ev_numeralM, ev_formCodeM v a, ev_formCodeM v b]; rfl
  | Formula.forall a => by
      show (MNV V).func cons_sym [evalTerm (MNV V) v (numeralM 6),
          (MNV V).func cons_sym [evalTerm (MNV V) v (formCodeM a), (MNV V).func zero_sym []]] =
        consN 6 (consN (codeNat a) 0)
      rw [ev_numeralM, ev_formCodeM v a]; rfl
  | .and a b => by
      show (MNV V).func cons_sym [evalTerm (MNV V) v (numeralM 7),
          (MNV V).func cons_sym [evalTerm (MNV V) v (formCodeM a),
            (MNV V).func cons_sym [evalTerm (MNV V) v (formCodeM b), (MNV V).func zero_sym []]]] =
        consN 7 (consN (codeNat a) (consN (codeNat b) 0))
      rw [ev_numeralM, ev_formCodeM v a, ev_formCodeM v b]; rfl
  | .or a b => by
      show (MNV V).func cons_sym [evalTerm (MNV V) v (numeralM 8),
          (MNV V).func cons_sym [evalTerm (MNV V) v (formCodeM a),
            (MNV V).func cons_sym [evalTerm (MNV V) v (formCodeM b), (MNV V).func zero_sym []]]] =
        consN 8 (consN (codeNat a) (consN (codeNat b) 0))
      rw [ev_numeralM, ev_formCodeM v a, ev_formCodeM v b]; rfl
  | .ex a => by
      show (MNV V).func cons_sym [evalTerm (MNV V) v (numeralM 9),
          (MNV V).func cons_sym [evalTerm (MNV V) v (formCodeM a), (MNV V).func zero_sym []]] =
        consN 9 (consN (codeNat a) 0)
      rw [ev_numeralM, ev_formCodeM v a]; rfl

theorem ev_listFormCodeM (v : Nat → Nat) : ∀ L : List Formula, evalTerm (MNV V) v (listFormCodeM L) = codeNatList L
  | [] => rfl
  | f :: fs => by
      show (MNV V).func cons_sym [evalTerm (MNV V) v (formCodeM f), evalTerm (MNV V) v (listFormCodeM fs)] =
        consN (codeNat f) (codeNatList fs)
      rw [ev_formCodeM, ev_listFormCodeM v fs]; rfl

/-! ### Las guardas: su evaluación es la `Prop` de §1ter, para un término ARBITRARIO -/

theorem ev_lift0 (v : Nat → Nat) (d : Nat) (t : Term) :
    evalTerm (MNV V) (shiftEnv v d) (liftTerm 0 t) = evalTerm (MNV V) v t := by
  have h := eval_liftTerm_ext (MNV V) v d 0 t
  have heq : updateEnv 0 v d = shiftEnv v d := by funext n; exact updateEnv_zero v d n
  rw [heq] at h; exact h

theorem ev_hasWit (v : Nat → Nat) (t : Term) : evalFormula (MNV V) v (hasWit t) ↔ hasWitN (evalTerm (MNV V) v t) := by
  simp only [hasWit, isTC1, wfAll1, wfAll1Body, isTermCodeE1, shapeUn, shapeBin, argsIn, argsInBody,
    land, lor, lt, In, lenc, nthc, cons, nil, zero, lt_sym, in_sym, cons_sym, zero_sym,
    evalFormula, evalTerm, evalTerms, shiftEnv, liftTerm, liftTerms, Nat.not_lt_zero, ↓reduceIte, Nat.zero_add,
    ROBINSON_PlusPlus.Minimal.Axioms.liftTerm_numeralM, ev_lift0, ev_numeralM,
    MN_lt, MN_mem, MN_lenc, MN_nthc, MN_cons, MN_zero,
    hasWitN, wfAll1N, isTermCodeE1N, shapeUnN, shapeBinN, argsInN]

theorem ev_hasWitF (v : Nat → Nat) (t : Term) : evalFormula (MNV V) v (hasWitF t) ↔ hasWitFN (evalTerm (MNV V) v t) := by
  simp only [hasWitF, isFC1, wfAll1, wfAll1Body, isTermCodeE1, shapeUn, shapeBin, shapeNul, argsIn, argsInBody,
    wfAllF, wfAllFBody, isFormCodeE2, lorAll, clBot, clAtom, clEq, clBin, clUn,
    land, lor, lt, In, lenc, nthc, cons, nil, zero, lt_sym, in_sym, cons_sym, zero_sym,
    evalFormula, evalTerm, evalTerms, shiftEnv, liftTerm, liftTerms, Nat.not_lt_zero, ↓reduceIte, Nat.zero_add,
    ROBINSON_PlusPlus.Minimal.Axioms.liftTerm_numeralM, ev_lift0, ev_numeralM,
    MN_lt, MN_mem, MN_lenc, MN_nthc, MN_cons, MN_zero,
    hasWitFN, wfAll1N, wfAllFN, isTermCodeE1N, isFormCodeE2N, shapeUnN, shapeBinN, argsInN,
    clBotN, clAtomN, clEqN, clBinN, clUnN]

/-- El `simp` que ABRE un axioma de codificación: los conectivos, los constructores de código, la evaluación
    y un lema `rfl` por símbolo. ⛔ Sin `numeralM`, `termCodeM`, `strCodeM` ni ningún `codeNat*`: los códigos
    cerrados se evalúan por sus lemas ∀ (`ev_*`), nunca desplegándolos. -/
local macro "abre" : tactic => `(tactic| simp only [forall_, forall_2, forall_3, forall_4, forall_5, _root_.iff,
    land, lor, cons, nil, zero, succ, pred, concat, lt, In, cons_sym, zero_sym, succ_sym, pred_sym,
    concat_sym, lt_sym, in_sym, substtc, substtsc, liftc, liftsc, substfc, liftfc, carc, cdrc, lenc, nthc,
    runFn, validProofFn, tcFn, premsOf, allIn, lineWF, chainOk, lineOk, varc, funcc, botc, atomc, eqc,
    implc, forallc, andc, orc, exc, axiomsCodeT, lineTag, tagDisj,
    evalFormula, evalTerm, evalTerms, shiftEnv, ev_numeralM, ev_strCodeM, ev_termCodeM, ev_hasWit, ev_hasWitF,
    MN_zero, MN_succ, MN_pred, MN_cons, MN_concat, MN_substtc, MN_substtsc, MN_liftc, MN_liftsc, MN_substfc,
    MN_liftfc, MN_carc, MN_cdrc, MN_lenc, MN_nthc, MN_runFn, MN_vpf, MN_tcFn, MN_premsOf, MN_axiomsCodeT,
    MN_lt, MN_mem, MN_allIn, MN_lineWF, MN_chainOk])

/-! ### Los axiomas core de ARITMÉTICA, validados -/

theorem v_ax2  : ∀ v : Nat → Nat, evalFormula (MNV V) v ax2_peano_succ_neq_zero := by
  intro v d; simp [succ, zero, succ_sym, zero_sym, neg,
    evalFormula, evalTerm, evalTerms, shiftEnv, MNV]

theorem v_ax3  : ∀ v : Nat → Nat, evalFormula (MNV V) v ax3_peano_succ_inj := by
  intro v d d'; simp [succ, succ_sym,
    evalFormula, evalTerm, evalTerms, shiftEnv, MNV]

theorem v_ax4  : ∀ v : Nat → Nat, evalFormula (MNV V) v ax4_add_zero := by
  intro v d; simp [add, zero, add_sym, zero_sym,
    evalFormula, evalTerm, evalTerms, shiftEnv, MNV]

theorem v_ax18 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax18_lt_irrefl := by
  intro v d; simp [lt, lt_sym, neg,
    evalFormula, evalTerm, evalTerms, shiftEnv, MNV]

theorem v_ax25 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax25_pred_zero := by
  -- ⚠️ `ax25_pred_zero` NO es un `forall_`: sin su nombre en el `simp` no hay nada que abrir.
  -- El linter lo marcó «no usado» en los OTROS siete (allí `forall_` lo abre) y aquí NO.
  -- 🔑 *Un aviso de «no usado» no es una medición de que sobre.* Segunda vez en esta sesión.
  intro v; simp [ax25_pred_zero, pred, zero, pred_sym, zero_sym,
    evalFormula, evalTerm, evalTerms, MNV]

theorem v_ax26 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax26_pred_succ := by
  intro v d; simp [pred, succ, pred_sym, succ_sym,
    evalFormula, evalTerm, evalTerms, shiftEnv, MNV]

/-- ⭐ Los dos que necesitaban la raíz. -/
theorem v_ax14 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax14_sqrt_le := by
  intro v d
  simp only [ax14_sqrt_le, forall_, le, lt, sq, mul, sqrt, lt_sym, mul_sym, sqrt_sym,
    evalFormula, evalTerm, evalTerms, shiftEnv, MNV]
  have := sqrtN_le d
  omega

theorem v_ax15 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax15_lt_succ_sqrt := by
  intro v d
  simp only [ax15_lt_succ_sqrt, forall_, lt, sq, mul, succ, sqrt, lt_sym, mul_sym, succ_sym,
    sqrt_sym, evalFormula, evalTerm, evalTerms, shiftEnv, MNV]
  exact lt_sq_succ_sqrtN d

/-! ### §2bis · El resto de la capa ARITMÉTICA

⭐ Todos siguen el mismo molde que los ocho de arriba: `intro` de los binders, `simp` que abre
la evaluación, y un `Nat.*` del core o un `omega` para rematar. **No hubo que inventar nada por
axioma** — que es lo que M2 (ADR‑085) predijo y aquí se confirma sobre quince más. -/

theorem v_ax5  : ∀ v : Nat → Nat, evalFormula (MNV V) v ax5_add_succ := by
  intro v d d'; simp [add, succ, add_sym, succ_sym,
    evalFormula, evalTerm, evalTerms, shiftEnv, MNV]
  omega

theorem v_ax6  : ∀ v : Nat → Nat, evalFormula (MNV V) v ax6_add_comm := by
  intro v d d'; simp [add, add_sym, evalFormula, evalTerm, evalTerms, shiftEnv, MNV]
  omega

theorem v_ax7  : ∀ v : Nat → Nat, evalFormula (MNV V) v ax7_add_assoc := by
  intro v d d' d''; simp [add, add_sym, evalFormula, evalTerm, evalTerms, shiftEnv, MNV]
  omega

theorem v_ax8  : ∀ v : Nat → Nat, evalFormula (MNV V) v ax8_mul_zero := by
  intro v d; simp [mul, zero, mul_sym, zero_sym,
    evalFormula, evalTerm, evalTerms, shiftEnv, MNV]

theorem v_ax9  : ∀ v : Nat → Nat, evalFormula (MNV V) v ax9_mul_succ := by
  intro v d d'; simp [mul, add, succ, mul_sym, add_sym, succ_sym,
    evalFormula, evalTerm, evalTerms, shiftEnv, MNV]
  exact Nat.mul_succ _ _

theorem v_ax10 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax10_mul_comm := by
  intro v d d'; simp [mul, mul_sym, evalFormula, evalTerm, evalTerms, shiftEnv, MNV]
  exact Nat.mul_comm _ _

theorem v_ax11 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax11_mul_assoc := by
  intro v d d' d''; simp [mul, mul_sym, evalFormula, evalTerm, evalTerms, shiftEnv, MNV]
  exact Nat.mul_assoc _ _ _

theorem v_ax12 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax12_mul_distrib := by
  intro v d d' d''; simp [mul, add, mul_sym, add_sym,
    evalFormula, evalTerm, evalTerms, shiftEnv, MNV]
  exact Nat.mul_add _ _ _

/-! #### La paridad: `omega` conoce `/2` y `%2` por literales -/

theorem v_ax16 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax16_mod2_succ := by
  intro v d; simp [_root_.iff, mod2, succ, zero, one, mod2_sym, succ_sym, zero_sym,
    evalFormula, evalTerm, evalTerms, shiftEnv, MNV]
  omega

theorem v_ax17 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax17_div_mod_eq := by
  intro v d; simp [add, mul, div2, mod2, two, one, succ, zero,
    add_sym, mul_sym, div2_sym, mod2_sym, succ_sym, zero_sym,
    evalFormula, evalTerm, evalTerms, shiftEnv, MNV]
  omega

theorem v_ax21 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax21_mod2_range := by
  intro v d; simp [mod2, zero, one, succ, mod2_sym, zero_sym, succ_sym,
    evalFormula, evalTerm, evalTerms, shiftEnv, MNV]
  omega

theorem v_ax24 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax24_mod2_of_even := by
  intro v d d'; simp [mod2, mul, two, one, succ, zero, mod2_sym, mul_sym, succ_sym, zero_sym,
    evalFormula, evalTerm, evalTerms, shiftEnv, MNV]
  omega

/-! #### Monus y potencia -/

theorem v_ax29 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax29_sub_witness := by
  intro v d d'; simp [le, lt, add, sub, lt_sym, add_sym, sub_sym,
    evalFormula, evalTerm, evalTerms, shiftEnv, MNV]
  omega

theorem v_pow_zero : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_pow_zero := by
  intro v d; simp [pow, zero, one, succ, pow_sym, zero_sym, succ_sym,
    evalFormula, evalTerm, evalTerms, shiftEnv, MNV]

theorem v_pow_succ : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_pow_succ := by
  intro v d d'; simp [pow, mul, succ, pow_sym, mul_sym, succ_sym,
    evalFormula, evalTerm, evalTerms, shiftEnv, MNV]
  exact Nat.pow_succ _ _

/-! #### El ORDEN. ⭐ `ax13` DEFINE `<` por un `∃`, así que aquí se comprueba que la relación
que el modelo eligió (`a < b` de `Nat`) es **la que el axioma exige**, no una cualquiera. -/

theorem v_ax13 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax13_lt_def := by
  intro v d d'; simp [_root_.iff, lt, add, succ, lt_sym, add_sym, succ_sym,
    evalFormula, evalTerm, evalTerms, shiftEnv, MNV]
  constructor
  · intro h; exact ⟨d' - d - 1, by omega⟩
  · -- ⚠️ `simp` convirtió el `∃k. …` del antecedente en un `∀k`, así que se introduce COMO TAL.
    intro k hk; omega

theorem v_ax19 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax19_lt_trichotomy := by
  intro v d d'; simp [lt, lt_sym, evalFormula, evalTerm, evalTerms, shiftEnv, MNV]
  omega

/-! ### Los axiomas core de LISTAS, validados (2026‑10‑05)

Cada uno se abre con el mismo `simp` que los de aritmética y se cierra con su lema de §1bis: `simp` NO despliega
`decodeL` (recursión bien fundada) ni `consN`, así que el paso que importa lo da el lema, a mano. -/

/-- `pair x y` evaluado en el modelo es `pairN x y`: el polinomio de Cantor es `2·pairN` (`two_mul_pairN`). -/
theorem eval_cantor (a b : Nat) : ((a + b) * (a + b + 1) + 2 * b) / 2 = pairN a b := by
  have h := ROBINSON_PlusPlus.Meta.CodeNumeralPrf.two_mul_pairN a b
  omega

theorem v_axL0 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_L0_cons_def := by
  intro v d d'
  simp only [ax_L0_cons_def, forall_2, cons, succ, pair, cantor_func, cantor_poly, div2, add, mul, two, one,
    zero, cons_sym, succ_sym, div2_sym, add_sym, mul_sym, zero_sym, evalFormula, evalTerm, evalTerms,
    shiftEnv, MNV]
  have h := eval_cantor d d'
  rw [consN_eq]
  omega

theorem v_axL1 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_L1_in_nil := by
  intro v d
  simp only [ax_L1_in_nil, forall_, neg, In, nil, zero, in_sym, zero_sym, evalFormula, evalTerm, evalTerms,
    shiftEnv, MNV]
  exact memN_zero d

theorem v_axL2 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_L2_in_cons := by
  intro v d d' d''
  simp only [ax_L2_in_cons, forall_3, _root_.iff, lor, In, cons, in_sym, cons_sym, evalFormula, evalTerm,
    evalTerms, shiftEnv, MNV]
  exact ⟨(memN_consN d d' d'').mp, (memN_consN d d' d'').mpr⟩

theorem v_axC1 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_C1_concat_nil := by
  intro v d
  simp only [ax_C1_concat_nil, forall_, concat, nil, zero, concat_sym, zero_sym, evalFormula, evalTerm,
    evalTerms, shiftEnv, MNV]
  exact concatN_zero d

theorem v_axC2 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_C2_concat_cons := by
  intro v d d' d''
  simp only [ax_C2_concat_cons, forall_3, concat, cons, concat_sym, cons_sym, evalFormula, evalTerm,
    evalTerms, shiftEnv, MNV]
  exact concatN_consN d d' d''

theorem v_axC3 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_C3_concat_assoc := by
  intro v d d' d''
  simp only [ax_C3_concat_assoc, forall_3, concat, concat_sym, evalFormula, evalTerm, evalTerms, shiftEnv, MNV]
  exact concatN_assoc d d' d''

theorem v_axL3 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_L3_in_concat := by
  intro v d d' d''
  simp only [ax_L3_in_concat, forall_3, _root_.iff, lor, In, concat, in_sym, concat_sym, evalFormula,
    evalTerm, evalTerms, shiftEnv, MNV]
  exact ⟨(memN_concatN d d' d'').mp, (memN_concatN d d' d'').mpr⟩

theorem v_prodp_nil : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_prodp_nil := by
  intro v
  simp only [ax_prodp_nil, prod_pairs, nil, one, succ, zero, prodp_sym, succ_sym, zero_sym, evalFormula,
    evalTerm, evalTerms, MNV]
  exact prodpN_zero

theorem v_prodp_cons : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_prodp_cons := by
  intro v d d' d''
  simp only [ax_prodp_cons, forall_3, prod_pairs, cons, pair, cantor_func, cantor_poly, div2, add, mul, two,
    one, succ, zero, pow, prodp_sym, cons_sym, div2_sym, add_sym, mul_sym, succ_sym, zero_sym, pow_sym,
    evalFormula, evalTerm, evalTerms, shiftEnv, MNV]
  have h : ((d + d') * (d + d' + 1) + (0 + 1 + 1) * d') / 2 = pairN d d' := by
    have := eval_cantor d d'
    omega
  rw [h, prodpN_consN_pairN]

/-- Para cerrar `∀ φ ∈ a :: l, p φ` de uno en uno (sin `List.Forall`, que el core no trae). -/
theorem mem_cons_elim {α : Type} {p : α → Prop} {a : α} {l : List α} (ha : p a)
    (hl : ∀ x, List.Mem x l → p x) : ∀ x, List.Mem x (a :: l) → p x := by
  intro x hx
  cases hx with
  | head => exact ha
  | tail _ h => exact hl x h

theorem mem_nil_elim {α : Type} {p : α → Prop} : ∀ x, List.Mem x ([] : List α) → p x :=
  fun _ h => nomatch h

/-- 🏁 **El modelo estándar satisface los 34 `coreAxioms`** (2026‑10‑05): la capa aritmética (25) y la de
    listas (9). Los 107 de `codingAxioms` y el ancla van aparte, y `MN_axioms` junta los 142. -/
theorem MN_coreAxioms (v : Nat → Nat) : ∀ φ, List.Mem φ coreAxioms → evalFormula (MNV V) v φ := by
  unfold coreAxioms
  exact mem_cons_elim (v_ax2 v) (mem_cons_elim (v_ax3 v) (mem_cons_elim (v_ax4 v) (mem_cons_elim (v_ax5 v) (mem_cons_elim (v_ax6 v) (mem_cons_elim (v_ax7 v) (mem_cons_elim (v_ax8 v) (mem_cons_elim (v_ax9 v) (mem_cons_elim (v_ax10 v) (mem_cons_elim (v_ax11 v) (mem_cons_elim (v_ax12 v) (mem_cons_elim (v_ax13 v) (mem_cons_elim (v_ax14 v) (mem_cons_elim (v_ax15 v) (mem_cons_elim (v_ax16 v) (mem_cons_elim (v_ax17 v) (mem_cons_elim (v_ax18 v) (mem_cons_elim (v_ax19 v) (mem_cons_elim (v_ax21 v) (mem_cons_elim (v_ax24 v) (mem_cons_elim (v_ax25 v) (mem_cons_elim (v_ax26 v) (mem_cons_elim (v_axL0 v) (mem_cons_elim (v_axL1 v) (mem_cons_elim (v_axL2 v) (mem_cons_elim (v_axC1 v) (mem_cons_elim (v_axC2 v) (mem_cons_elim (v_axC3 v) (mem_cons_elim (v_axL3 v) (mem_cons_elim (v_ax29 v) (mem_cons_elim (v_pow_zero v) (mem_cons_elim (v_pow_succ v) (mem_cons_elim (v_prodp_nil v) (mem_cons_elim (v_prodp_cons v) (mem_nil_elim))))))))))))))))))))))))))))))))))


/-! ## §3 · Los 107 de CODIFICACIÓN, validados

Todos con el mismo molde: `intro` de los binders, `abre`, y el lema de §1ter que dice lo que el axioma dice. -/

/-! ### Sustitución y lift sobre códigos de término (11) -/

theorem v_substtc_var_eq : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_substtc_var_eq := by
  intro v k s n; abre; intro h; rw [substtcN_var, if_pos h]
theorem v_substtc_var_gt : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_substtc_var_gt := by
  intro v k s n; abre; intro h; rw [substtcN_var, if_neg (Nat.ne_of_lt h), if_pos h]
theorem v_substtc_var_lt : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_substtc_var_lt := by
  intro v k s n; abre; intro h
  rw [substtcN_var, if_neg (by omega), if_neg (by omega)]
theorem v_substtc_func : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_substtc_func := by
  intro v k s a b; abre; exact substtcN_func k s a b
theorem v_substtsc_nil : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_substtsc_nil := by
  intro v k s; abre; exact substtscN_zero k s
theorem v_substtsc_cons : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_substtsc_cons := by
  intro v k s a b; abre; exact substtscN_consN k s a b
theorem v_liftc_var_lt : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_liftc_var_lt := by
  intro v c n; abre; intro h; rw [liftcN_var, if_pos h]
theorem v_liftc_var_ge : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_liftc_var_ge := by
  intro v c n; abre; intro h; rw [liftcN_var, if_neg (by omega)]
theorem v_liftc_func : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_liftc_func := by
  intro v c a b; abre; exact liftcN_func c a b
theorem v_liftsc_nil : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_liftsc_nil := by
  intro v c; abre; exact liftscN_zero c
theorem v_liftsc_cons : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_liftsc_cons := by
  intro v c a b; abre; exact liftscN_consN c a b

/-! ### Sustitución y lift sobre códigos de fórmula (16) -/

theorem v_substfc_bottom : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_substfc_bottom := by
  intro v x t; abre; exact substfcN_bot x t
theorem v_substfc_atom : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_substfc_atom := by
  intro v x t a b; abre; exact substfcN_atom x t a b
theorem v_substfc_eq : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_substfc_eq := by
  intro v x t a b; abre; exact substfcN_eq x t a b
theorem v_substfc_impl : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_substfc_impl := by
  intro v x t a b; abre; exact substfcN_impl x t a b
theorem v_substfc_forall : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_substfc_forall := by
  intro v x t a; abre; exact substfcN_forall x t a
theorem v_substfc_and : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_substfc_and := by
  intro v x t a b; abre; exact substfcN_and x t a b
theorem v_substfc_or : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_substfc_or := by
  intro v x t a b; abre; exact substfcN_or x t a b
theorem v_substfc_ex : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_substfc_ex := by
  intro v x t a; abre; exact substfcN_ex x t a
theorem v_liftfc_bottom : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_liftfc_bottom := by
  intro v c; abre; exact liftfcN_bot c
theorem v_liftfc_atom : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_liftfc_atom := by
  intro v c a b; abre; exact liftfcN_atom c a b
theorem v_liftfc_eq : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_liftfc_eq := by
  intro v c a b; abre; exact liftfcN_eq c a b
theorem v_liftfc_impl : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_liftfc_impl := by
  intro v c a b; abre; exact liftfcN_impl c a b
theorem v_liftfc_forall : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_liftfc_forall := by
  intro v c a; abre; exact liftfcN_forall c a
theorem v_liftfc_and : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_liftfc_and := by
  intro v c a b; abre; exact liftfcN_and c a b
theorem v_liftfc_or : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_liftfc_or := by
  intro v c a b; abre; exact liftfcN_or c a b
theorem v_liftfc_ex : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_liftfc_ex := by
  intro v c a; abre; exact liftfcN_ex c a

/-! ### Accesores (6) -/

theorem v_carc : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_carc := by
  intro v a b; abre; exact carN_consN a b
theorem v_cdrc : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_cdrc := by
  intro v a b; abre; exact cdrN_consN a b
theorem v_lenc_nil : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lenc_nil := by
  intro v; unfold ax_lenc_nil; abre; exact lenN_zero
theorem v_lenc_cons : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lenc_cons := by
  intro v a b; abre; exact lenN_consN a b
theorem v_nthc_zero : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_nthc_zero := by
  intro v a b; abre; exact nthN_cz a b
theorem v_nthc_succ : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_nthc_succ := by
  intro v a b i; abre; exact nthN_cs a b i

/-! ### `tcFn` y `runFn` (4) -/

theorem v_tc_zero : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_tc_zero := by
  intro v; unfold ax_tc_zero; abre; rfl
theorem v_tc_succ : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_tc_succ := by
  intro v n; abre; rfl
theorem v_runFn_nil : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_runFn_nil := by
  intro v c; abre; exact runFnN_zero c
theorem v_runFn_cons : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_runFn_cons := by
  intro v c l r; abre; exact runFnN_consN c l r

/-! ### `allIn` y `chainOk` (4) -/

theorem v_allIn_nil : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_allIn_nil := by
  intro v c; abre; exact allInN_zero c
theorem v_allIn_cons : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_allIn_cons := by
  intro v c a t; abre; exact ⟨(allInN_consN c a t).mp, (allInN_consN c a t).mpr⟩
theorem v_chainOk_nil : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_chainOk_nil := by
  intro v c; abre; exact chainOkN_zero _ c
theorem v_chainOk_cons : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_chainOk_cons := by
  intro v c l r; abre; exact ⟨(chainOkN_consN _ c l r).mp, (chainOkN_consN _ c l r).mpr⟩

/-! ### `validProofFn` (22): la conclusión la da `stepT`, sea cual sea la condición -/

/-- La línea `⟨K, …⟩` se consume por `vpfN_consN` y `stepT` la decide por su etiqueta. -/
local macro "vpf_paso" : tactic => `(tactic| (rw [vpfN_consN]; simp only [stepN, nthN_cz, nthN_cs, nthN_zero_l, stepT]))

theorem v_vpf_nil : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_vpf_nil := by
  intro v c; abre; exact vpfN_zero c
theorem v_vpf_p1 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_vpf_p1 := by
  intro v c a b r; abre; vpf_paso
theorem v_vpf_p2 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_vpf_p2 := by
  intro v c a b d r; abre; vpf_paso
theorem v_vpf_c1 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_vpf_c1 := by
  intro v c a b r; abre; vpf_paso
theorem v_vpf_c2 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_vpf_c2 := by
  intro v c a b r; abre; vpf_paso
theorem v_vpf_c3 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_vpf_c3 := by
  intro v c a b r; abre; vpf_paso
theorem v_vpf_j1 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_vpf_j1 := by
  intro v c a b r; abre; vpf_paso
theorem v_vpf_j2 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_vpf_j2 := by
  intro v c a b r; abre; vpf_paso
theorem v_vpf_j3 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_vpf_j3 := by
  intro v c a b d r; abre; vpf_paso
theorem v_vpf_efq : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_vpf_efq := by
  intro v c a r; abre; vpf_paso
theorem v_vpf_q1 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_vpf_q1 := by
  intro v c a b r; abre; vpf_paso
theorem v_vpf_q2 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_vpf_q2 := by
  intro v c a b r; abre; vpf_paso
theorem v_vpf_q3 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_vpf_q3 := by
  intro v c a b r; abre; vpf_paso
theorem v_vpf_eqrefl : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_vpf_eqrefl := by
  intro v c a r; abre; vpf_paso
theorem v_vpf_leibniz : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_vpf_leibniz := by
  intro v c a b d r; abre; vpf_paso
theorem v_vpf_p3 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_vpf_p3 := by
  intro v c a r; abre; vpf_paso
theorem v_vpf_mp : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_vpf_mp := by
  intro v c b a r; abre; intro _ _; vpf_paso
theorem v_vpf_gen : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_vpf_gen := by
  intro v c a r; abre; intro _; vpf_paso
theorem v_vpf_thy : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_vpf_thy := by
  intro v c a r; abre; intro _; vpf_paso
theorem v_vpf_ind : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_vpf_ind := by
  intro v c a r; abre; vpf_paso; rfl
theorem v_vpf_qconf : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_vpf_qconf := by
  intro v c a b r; abre; vpf_paso
theorem v_vpf_listInd : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_vpf_listInd := by
  intro v c a r; abre; vpf_paso; rfl

/-! ### `premsOf` (21) -/

local macro "prems" : tactic => `(tactic| ((simp only [premsOfN, nthN_cz, nthN_cs, nthN_zero_l]) <;> rfl))

theorem v_premsOf_mp : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_premsOf_mp := by
  intro v b a; abre; prems
theorem v_premsOf_gen : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_premsOf_gen := by
  intro v b a; abre; prems
theorem v_premsOf_thy : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_premsOf_thy := by
  intro v c; abre; prems
theorem v_premsOf_p1 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_premsOf_p1 := by
  intro v c a b; abre; prems
theorem v_premsOf_p2 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_premsOf_p2 := by
  intro v c a b d; abre; prems
theorem v_premsOf_c1 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_premsOf_c1 := by
  intro v c a b; abre; prems
theorem v_premsOf_c2 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_premsOf_c2 := by
  intro v c a b; abre; prems
theorem v_premsOf_c3 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_premsOf_c3 := by
  intro v c a b; abre; prems
theorem v_premsOf_j1 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_premsOf_j1 := by
  intro v c a b; abre; prems
theorem v_premsOf_j2 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_premsOf_j2 := by
  intro v c a b; abre; prems
theorem v_premsOf_j3 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_premsOf_j3 := by
  intro v c a b d; abre; prems
theorem v_premsOf_efq : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_premsOf_efq := by
  intro v c a; abre; prems
theorem v_premsOf_eqrefl : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_premsOf_eqrefl := by
  intro v c a; abre; prems
theorem v_premsOf_p3 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_premsOf_p3 := by
  intro v c a; abre; prems
theorem v_premsOf_q1 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_premsOf_q1 := by
  intro v c a b; abre; prems
theorem v_premsOf_q2 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_premsOf_q2 := by
  intro v c a b; abre; prems
theorem v_premsOf_q3 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_premsOf_q3 := by
  intro v c a b; abre; prems
theorem v_premsOf_leibniz : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_premsOf_leibniz := by
  intro v c a b d; abre; prems
theorem v_premsOf_ind : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_premsOf_ind := by
  intro v c a; abre; prems
theorem v_premsOf_qconf : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_premsOf_qconf := by
  intro v c a b; abre; prems
theorem v_premsOf_listInd : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_premsOf_listInd := by
  intro v c a; abre; prems

/-! ### `lineWF` (23): la RHS de cada etiqueta es, por construcción, la de `lineWFT` -/

local macro "lwf" : tactic => `(tactic| (intro h; exact ⟨(lineWFN_of_tag h (by decide)).mp, (lineWFN_of_tag h (by decide)).mpr⟩))

theorem v_lineWF_mp : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lineWF_mp := by
  intro v x; abre; lwf
theorem v_lineWF_gen : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lineWF_gen := by
  intro v x; abre; lwf
theorem v_lineWF_thy : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lineWF_thy := by
  intro v x; abre; lwf
theorem v_lineWF_p1 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lineWF_p1 := by
  intro v x; abre; lwf
theorem v_lineWF_p2 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lineWF_p2 := by
  intro v x; abre; lwf
theorem v_lineWF_c1 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lineWF_c1 := by
  intro v x; abre; lwf
theorem v_lineWF_c2 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lineWF_c2 := by
  intro v x; abre; lwf
theorem v_lineWF_c3 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lineWF_c3 := by
  intro v x; abre; lwf
theorem v_lineWF_j1 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lineWF_j1 := by
  intro v x; abre; lwf
theorem v_lineWF_j2 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lineWF_j2 := by
  intro v x; abre; lwf
theorem v_lineWF_j3 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lineWF_j3 := by
  intro v x; abre; lwf
theorem v_lineWF_efq : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lineWF_efq := by
  intro v x; abre; lwf
theorem v_lineWF_eqrefl : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lineWF_eqrefl := by
  intro v x; abre; lwf
theorem v_lineWF_p3 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lineWF_p3 := by
  intro v x; abre; lwf
theorem v_lineWF_q1 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lineWF_q1 := by
  intro v x; abre; lwf
theorem v_lineWF_q2 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lineWF_q2 := by
  intro v x; abre; lwf
theorem v_lineWF_q3 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lineWF_q3 := by
  intro v x; abre; lwf
theorem v_lineWF_leibniz : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lineWF_leibniz := by
  intro v x; abre; lwf
theorem v_lineWF_ind : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lineWF_ind := by
  intro v x; abre; lwf
theorem v_lineWF_qconf : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lineWF_qconf := by
  intro v x; abre; lwf
theorem v_lineWF_listInd : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lineWF_listInd := by
  intro v x; abre; lwf

theorem v_lineWF_inv : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lineWF_inv := by
  intro v x; abre; intro h
  have h1 : nthN x 1 < 21 := h.1
  rw [show (0 : Nat) + 1 = 1 from rfl]
  omega

theorem v_lineWF_cons : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_lineWF_cons := by
  intro v x; abre; intro h
  by_cases hx : x = 0
  · exfalso
    subst hx
    have h2 := h.2
    rw [nthN_zero_l] at h2
    have h3 : lenN 0 = 4 := h2.1
    rw [lenN_zero] at h3
    exact absurd h3 (by decide)
  · exact (consN_car_cdr hx).symm

/-! ## §4 · EL ANCLA, por `rw` con lemas ∀ (⛔ nada de `simp`, `decide` ni `rfl` que alcance `nD`)

Su lado derecho no nombra `axiomsCodeT`, y `(MNV V)` interpreta `axiomsCodeT` por `V₀`, que es por definición el valor
de ese lado derecho. Cada paso instancia un lema universal; el único `rfl` (`V₀_def`) compara dos expresiones
IDÉNTICAS tras desplegar `V₀` un nivel. -/

theorem ev_concat (v : Nat → Nat) (a b : Term) :
    evalTerm (MNV V) v (concat a b) = concatN (evalTerm (MNV V) v a) (evalTerm (MNV V) v b) := rfl
theorem ev_cons (v : Nat → Nat) (a b : Term) :
    evalTerm (MNV V) v (cons a b) = consN (evalTerm (MNV V) v a) (evalTerm (MNV V) v b) := rfl
theorem ev_nil (v : Nat → Nat) : evalTerm (MNV V) v nil = 0 := rfl
theorem ev_zero (v : Nat → Nat) : evalTerm (MNV V) v zero = 0 := rfl
theorem ev_substfc (v : Nat → Nat) (a b c : Term) :
    evalTerm (MNV V) v (substfc a b c) = substfcN (evalTerm (MNV V) v a) (evalTerm (MNV V) v b) (evalTerm (MNV V) v c) := rfl
theorem ev_tcFn (v : Nat → Nat) (a : Term) : evalTerm (MNV V) v (tcFn a) = tcFnN (evalTerm (MNV V) v a) := rfl
theorem ev_axiomsCodeT (v : Nat → Nat) : evalTerm (MNV V) v axiomsCodeT = V := rfl

theorem V₀_def : V₀ = concatN (codeNatList axiomsBase)
    (consN (substfcN 0 (tcFnN (codeNat (psiD axiomsBase))) (codeNat (psiD axiomsBase))) 0) := rfl

theorem v_ancla : ∀ v : Nat → Nat, evalFormula (MNV V₀) v ax_axiomsCodeT_def := by
  intro v
  rw [ax_axiomsCodeT_def, axD]
  show evalTerm (MNV V₀) v axiomsCodeT =
    evalTerm (MNV V₀) v (concat (listFormCodeM axiomsBase) (cons (deltaD axiomsBase) nil))
  rw [ev_axiomsCodeT, ev_concat, ev_cons, ev_nil, ev_listFormCodeM, deltaD, ev_substfc, ev_zero, ev_tcFn, nD,
    ev_numeralM]
  exact V₀_def

/-! ## §5 · LOS 142 -/

theorem MN_codingAxioms (v : Nat → Nat) : ∀ φ, List.Mem φ codingAxioms → evalFormula (MNV V) v φ := by
  unfold codingAxioms
  exact mem_cons_elim (v_substtc_var_eq v) (mem_cons_elim (v_substtc_var_gt v) (mem_cons_elim (v_substtc_var_lt v) (mem_cons_elim (v_substtc_func v) (mem_cons_elim (v_substtsc_nil v) (mem_cons_elim (v_substtsc_cons v) (mem_cons_elim (v_liftc_var_lt v) (mem_cons_elim (v_liftc_var_ge v) (mem_cons_elim (v_liftc_func v) (mem_cons_elim (v_liftsc_nil v) (mem_cons_elim (v_liftsc_cons v) (mem_cons_elim (v_substfc_bottom v) (mem_cons_elim (v_substfc_atom v) (mem_cons_elim (v_substfc_eq v) (mem_cons_elim (v_substfc_impl v) (mem_cons_elim (v_substfc_forall v) (mem_cons_elim (v_substfc_and v) (mem_cons_elim (v_substfc_or v) (mem_cons_elim (v_substfc_ex v) (mem_cons_elim (v_liftfc_bottom v) (mem_cons_elim (v_liftfc_atom v) (mem_cons_elim (v_liftfc_eq v) (mem_cons_elim (v_liftfc_impl v) (mem_cons_elim (v_liftfc_forall v) (mem_cons_elim (v_liftfc_and v) (mem_cons_elim (v_liftfc_or v) (mem_cons_elim (v_liftfc_ex v) (mem_cons_elim (v_carc v) (mem_cons_elim (v_cdrc v) (mem_cons_elim (v_vpf_nil v) (mem_cons_elim (v_vpf_p1 v) (mem_cons_elim (v_vpf_p2 v) (mem_cons_elim (v_vpf_c1 v) (mem_cons_elim (v_vpf_c2 v) (mem_cons_elim (v_vpf_c3 v) (mem_cons_elim (v_vpf_j1 v) (mem_cons_elim (v_vpf_j2 v) (mem_cons_elim (v_vpf_j3 v) (mem_cons_elim (v_vpf_efq v) (mem_cons_elim (v_vpf_q1 v) (mem_cons_elim (v_vpf_q2 v) (mem_cons_elim (v_vpf_q3 v) (mem_cons_elim (v_vpf_eqrefl v) (mem_cons_elim (v_vpf_leibniz v) (mem_cons_elim (v_vpf_p3 v) (mem_cons_elim (v_vpf_mp v) (mem_cons_elim (v_vpf_gen v) (mem_cons_elim (v_vpf_thy v) (mem_cons_elim (v_vpf_ind v) (mem_cons_elim (v_vpf_qconf v) (mem_cons_elim (v_vpf_listInd v) (mem_cons_elim (v_tc_zero v) (mem_cons_elim (v_tc_succ v) (mem_cons_elim (v_runFn_nil v) (mem_cons_elim (v_runFn_cons v) (mem_cons_elim (v_allIn_nil v) (mem_cons_elim (v_allIn_cons v) (mem_cons_elim (v_chainOk_nil v) (mem_cons_elim (v_chainOk_cons v) (mem_cons_elim (v_lineWF_mp v) (mem_cons_elim (v_premsOf_mp v) (mem_cons_elim (v_lineWF_gen v) (mem_cons_elim (v_premsOf_gen v) (mem_cons_elim (v_lineWF_thy v) (mem_cons_elim (v_premsOf_thy v) (mem_cons_elim (v_lineWF_p1 v) (mem_cons_elim (v_premsOf_p1 v) (mem_cons_elim (v_lineWF_p2 v) (mem_cons_elim (v_premsOf_p2 v) (mem_cons_elim (v_lineWF_c1 v) (mem_cons_elim (v_premsOf_c1 v) (mem_cons_elim (v_lineWF_c2 v) (mem_cons_elim (v_premsOf_c2 v) (mem_cons_elim (v_lineWF_c3 v) (mem_cons_elim (v_premsOf_c3 v) (mem_cons_elim (v_lineWF_j1 v) (mem_cons_elim (v_premsOf_j1 v) (mem_cons_elim (v_lineWF_j2 v) (mem_cons_elim (v_premsOf_j2 v) (mem_cons_elim (v_lineWF_j3 v) (mem_cons_elim (v_premsOf_j3 v) (mem_cons_elim (v_lineWF_efq v) (mem_cons_elim (v_premsOf_efq v) (mem_cons_elim (v_lineWF_eqrefl v) (mem_cons_elim (v_premsOf_eqrefl v) (mem_cons_elim (v_lineWF_p3 v) (mem_cons_elim (v_premsOf_p3 v) (mem_cons_elim (v_lineWF_q1 v) (mem_cons_elim (v_premsOf_q1 v) (mem_cons_elim (v_lineWF_q2 v) (mem_cons_elim (v_premsOf_q2 v) (mem_cons_elim (v_lineWF_q3 v) (mem_cons_elim (v_premsOf_q3 v) (mem_cons_elim (v_lineWF_leibniz v) (mem_cons_elim (v_premsOf_leibniz v) (mem_cons_elim (v_lineWF_ind v) (mem_cons_elim (v_premsOf_ind v) (mem_cons_elim (v_lineWF_qconf v) (mem_cons_elim (v_premsOf_qconf v) (mem_cons_elim (v_lineWF_listInd v) (mem_cons_elim (v_premsOf_listInd v) (mem_cons_elim (v_lenc_nil v) (mem_cons_elim (v_lenc_cons v) (mem_cons_elim (v_nthc_zero v) (mem_cons_elim (v_nthc_succ v) (mem_cons_elim (v_lineWF_inv v) (mem_cons_elim (v_lineWF_cons v) (mem_nil_elim)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem MN_axioms (v : Nat → Nat) : contextSatisfies (MNV V₀) v axioms := by
  intro φ hφ
  rw [axioms_split] at hφ
  cases List.mem_append.mp hφ with
  | inl h =>
    cases List.mem_append.mp h with
    | inl h1 => exact MN_coreAxioms v φ h1
    | inr h2 => exact MN_codingAxioms v φ h2
  | inr h =>
    have e : φ = ax_axiomsCodeT_def := List.mem_singleton.mp h
    rw [e]; exact v_ancla v

end Interpretacion

/-! ## §6 · LA SOLIDEZ de `Prf` en todo modelo ESTÁNDAR (de la sonda R2‑1‑2 de la ronda 2, corregida y compilada)

Única hipótesis: `Estandar M` (0, σ y `::` estándar, y los 142 verdaderos). `prf_sound` recorre los 7
constructores de `Prf` y los 17 de `Prfᵢ`; `ind`, `qconf` y `listInd` piden `descompone` (sin basura, ADR‑113) y
la inducción fuerte. -/

open ROBINSON_PlusPlus.Meta.CodeNumeralPrf

namespace Sondeos.SolidezPrfParam

/-! §0 · Aritmética pura (SIN `open` de Axioms: `≤` sería el símbolo objeto) -/

theorem triN_succ' (s : Nat) : triN (s + 1) = triN s + (s + 1) := rfl

theorem le_triN : ∀ s : Nat, s ≤ triN s
  | 0 => Nat.le_refl _
  | s + 1 => by have := le_triN s; rw [triN_succ']; omega

/-- Copia de sondeos/CantorSobreyectivo.lean:72-94. -/
def wN : Nat → Nat
  | 0 => 0
  | n + 1 => if triN (wN n + 1) ≤ n + 1 then wN n + 1 else wN n

theorem wN_le : ∀ n : Nat, triN (wN n) ≤ n
  | 0 => by simp [wN, triN]
  | n + 1 => by
      have ih := wN_le n
      simp only [wN]
      by_cases h : triN (wN n + 1) ≤ n + 1
      · rw [if_pos h]; exact h
      · rw [if_neg h]; omega

theorem lt_wN_succ : ∀ n : Nat, n < triN (wN n + 1)
  | 0 => by simp [wN, triN]
  | n + 1 => by
      have ih := lt_wN_succ n
      simp only [wN]
      by_cases h : triN (wN n + 1) ≤ n + 1
      · rw [if_pos h]; have := triN_succ' (wN n + 1); omega
      · rw [if_neg h]; exact Nat.lt_of_not_le h

/-- Sin basura (ADR-113): todo m+1 es un cons con cabeza y cola MENORES.
    Control: con el consN viejo es FALSO en m = 0. -/
theorem descompone (m : Nat) : ∃ x y, And (consN x y = m + 1) (And (x < m + 1) (y < m + 1)) := by
  have h1 := wN_le m
  have h2 := lt_wN_succ m
  have h3 := triN_succ' (wN m)
  have h4 := le_triN (wN m)
  refine ⟨wN m - (m - triN (wN m)), m - triN (wN m), ?_, by omega, by omega⟩
  have hs : (wN m - (m - triN (wN m))) + (m - triN (wN m)) = wN m := by omega
  simp only [consN, hs]; omega

theorem fuerte (P : Nat → Prop) (h : ∀ n, (∀ m, m < n → P m) → P n) : ∀ n, P n := by
  have key : ∀ k m, m < k → P m := by
    intro k
    induction k with
    | zero => intro m hm; exact absurd hm (Nat.not_lt_zero m)
    | succ k ih =>
        intro m hm
        rcases Nat.lt_or_ge m k with hlt | hge
        · exact ih m hlt
        · have hmk : m = k := by omega
          subst hmk; exact h m ih
  exact fun n => key (n + 1) n (Nat.lt_succ_self n)

end Sondeos.SolidezPrfParam

section Modelo
open FOL FOL.Metamath.Semantics
open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Hilbert

namespace Sondeos.SolidezPrfParam

/-- Lo que A2/A3 tienen que entregar. -/
structure Estandar (M : Model Nat) : Prop where
  hzero : M.func zero_sym [] = 0
  hsucc : ∀ a, M.func succ_sym [a] = a + 1
  hcons : ∀ a b, M.func cons_sym [a, b] = consN a b
  haxs  : ∀ v, contextSatisfies M v axioms

theorem env1 (v : Nat → Nat) (a b : Nat) :
    shiftEnv (shiftEnv v a) b = updateEnv 1 (shiftEnv v b) a := by
  have h0 : shiftEnv v a = updateEnv 0 v a := by
    funext n; exact (updateEnv_zero v a n).symm
  rw [h0, shift_updateEnv_comm]

theorem env2 (v : Nat → Nat) (a b c : Nat) :
    shiftEnv (shiftEnv (shiftEnv v a) b) c = updateEnv 2 (shiftEnv (shiftEnv v b) c) a := by
  rw [env1 v a b, shift_updateEnv_comm]

variable {M : Model Nat}

theorem prfI_sound (hM : Estandar M) {φ : Formula} (h : Prfᵢ φ) : ∀ v, evalFormula M v φ := by
  induction h with
  | p1 A B => intro v hA _; exact hA
  | p2 A B C => intro v hABC hAB hA; exact hABC hA (hAB hA)
  | c1 A B => intro v hA hB; exact ⟨hA, hB⟩
  | c2 A B => intro v hAB; exact hAB.left
  | c3 A B => intro v hAB; exact hAB.right
  | j1 A B => intro v hA; exact Or.inl hA
  | j2 A B => intro v hB; exact Or.inr hB
  | j3 A B C =>
      intro v hAB hAC hBC
      rcases hAB with hA | hB
      · exact hAC hA
      · exact hBC hB
  | efq A => intro v hb; exact False.elim hb
  | q1 A t => intro v hall; exact (eval_substFormula_zero M v t A).mpr (hall _)
  | q2 A t => intro v hs; exact ⟨_, (eval_substFormula_zero M v t A).mp hs⟩
  | q3 A B =>
      intro v hall hex
      obtain ⟨d, hd⟩ := hex
      exact (eval_liftFormula_zero M v d B).mp (hall d hd)
  | eqrefl t => intro v; rfl
  | leibniz A t₁ t₂ =>
      intro v he hs
      have h1 := (eval_substFormula_zero M v t₁ A).mp hs
      have he' : evalTerm M v t₁ = evalTerm M v t₂ := he
      rw [he'] at h1
      exact (eval_substFormula_zero M v t₂ A).mpr h1
  | thy a ha => intro v; exact hM.haxs v a ha
  | mp A B _ _ ih1 ih2 => intro v; exact ih1 v (ih2 v)
  | gen A _ ih => intro v d; exact ih (shiftEnv v d)

theorem prf_sound (hM : Estandar M) {φ : Formula} (h : Prf φ) : ∀ v, evalFormula M v φ := by
  induction h with
  | incl h0 => exact prfI_sound hM h0
  | p3 A => intro v hnn; exact Classical.byContradiction hnn
  | ind A =>
      intro v
      simp only [ROBINSON_PlusPlus.Full.inductionFormula, evalFormula]
      intro h0 hst d
      have hz : evalTerm M v zero = 0 := by simp [zero, evalTerm, evalTerms, hM.hzero]
      have h0' : evalFormula M (shiftEnv v 0) A := by
        have := (eval_substFormula_zero M v zero A).mp h0; rwa [hz] at this
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
      simp only [confinementFormula, evalFormula]
      intro hall hP d
      exact hall d ((eval_liftFormula_zero M v d P).mpr hP)
  | listInd A =>
      intro v
      simp only [listInductionFormula, evalFormula]
      intro h0 hst
      have hn : evalTerm M v nil = 0 := by simp [nil, zero, evalTerm, evalTerms, hM.hzero]
      have h0' : evalFormula M (shiftEnv v 0) A := by
        have := (eval_substFormula_zero M v nil A).mp h0; rwa [hn] at this
      refine fuerte (fun n => evalFormula M (shiftEnv v n) A) ?_
      intro n ih
      rcases n with _ | m
      · exact h0'
      · obtain ⟨x, y, hxy, _, hy⟩ := descompone m
        have hant : evalFormula M (shiftEnv (shiftEnv v x) y) (liftFormula 1 A) := by
          rw [env1, eval_liftFormula_ext]; exact ih y hy
        have hs := hst x y hant
        have hc : evalTerm M (shiftEnv (shiftEnv v x) y) (cons (.var 1) (.var 0)) = consN x y := by
          simp [cons, evalTerm, evalTerms, shiftEnv, hM.hcons]
        rw [eval_substFormula_zero, hc, hxy, env2, eval_liftFormula_ext, env1,
          eval_liftFormula_ext] at hs
        exact hs
  | mp A B _ _ ih1 ih2 => intro v; exact ih1 v (ih2 v)
  | gen A _ ih => intro v d; exact ih (shiftEnv v d)

/-- `ConsistentH` a partir de CUALQUIER modelo estándar; `estandar_MN` lo instancia en `MNV V₀`. -/
theorem consistentH_de (hM : Estandar M) : ConsistentH :=
  fun h => prf_sound hM h (fun _ => 0)

end Sondeos.SolidezPrfParam
end Modelo

#print axioms Sondeos.SolidezPrfParam.prf_sound
#print axioms Sondeos.SolidezPrfParam.consistentH_de

/-! ## §7 · `ConsistentH`, TEOREMA; y Gödel I/II sin hipótesis -/

section Final
open FOL FOL.Metamath.Semantics
open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Hilbert
open ModeloNat

/-- `MNV V₀` es estándar. `hzero`, `hsucc` y `hcons` INSTANCIAN lemas `rfl` demostrados para `V` arbitrario —⛔
    ningún `rfl` compara nada con `V₀`: el núcleo desplegaría `V₀` antes que `MNV`, por altura de definición, y no
    acabaría—; `haxs` es `MN_axioms`, propio de `V₀` porque el ancla fija `V`: junta `MN_coreAxioms` y
    `MN_codingAxioms` (genéricos en `V`) con `v_ancla`. -/
theorem estandar_MN : Sondeos.SolidezPrfParam.Estandar (MNV V₀) where
  hzero := MN_zero
  hsucc := MN_succ
  hcons := MN_cons
  haxs := MN_axioms

/-- 🏁 **Los 142 son CONSISTENTES**: `Prf ⊥` no tiene prueba, porque `MNV V₀` satisface los 142 (`MN_axioms`). -/
theorem consistentH : ConsistentH := Sondeos.SolidezPrfParam.consistentH_de estandar_MN

/-- 🏁 **GÖDEL I, sin hipótesis.** -/
theorem incompletitud_I : ¬ Prf ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN :=
  ROBINSON_PlusPlus.Meta.GodelTwoPrf.goedel_first_prf consistentH

/-- 🏁 **GÖDEL II, sin hipótesis.** -/
theorem incompletitud_II : ¬ Prf ROBINSON_PlusPlus.Meta.GodelTwo.consistencyFormula' :=
  ROBINSON_PlusPlus.Meta.GodelTwoPrf.goedel_second_prf consistentH

end Final

#print axioms MN_coreAxioms
#print axioms MN_codingAxioms
#print axioms v_ancla
#print axioms MN_axioms
#print axioms consistentH
#print axioms incompletitud_I
#print axioms incompletitud_II
