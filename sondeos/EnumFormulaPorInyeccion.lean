/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import FOL.FOL

/-!
# SONDEO · la OTRA ruta a `formula_enum`: codificar e invertir con elección

⚠️⚠️ **ESTE FICHERO SE RESCATA DE UN SCRATCHPAD, y ése es su primer hallazgo.**

Lo escribió la auditoría del **2026‑09‑12** (`doc/AUDITORIA-FOL-2026-09-12.md`, **M‑2**), que
anotó *«derivable — COMPILADO en 94 líneas»* y dejó el fichero en
`…/scratchpad/ProbeEnum.lean`, un directorio **de sesión**. El **2026‑09‑13**, al ir a construir
`FOL/Enumeration.lean`, busqué en los dos repos, no encontré nada, y **lo construí otra vez**.

🔑 **La regla «antes de construir, buscar» necesita un corolario**: *buscar incluye el scratchpad
de la propia sesión*. Y la recíproca, que es la que aquí se paga:
**una medición cuyo artefacto vive en un directorio efímero es una medición que se evapora.**
Por eso este fichero está ahora en el árbol.

## Qué mide

La ruta **contraria** a la de `FOL/Enumeration.lean`:

| | `FOL/Enumeration.lean` (lo que se adoptó) | este sondeo |
|---|---|---|
| dirección | `natToFormula : Nat → Formula`, **computable** | `codeNat : Formula → Nat`, **inyectiva** |
| la enumeración | construida, se puede `#eval` | `noncomputable`, por `Classical.choose` |
| la prueba | sobreyectividad por **cota de tamaño** | **inyectividad** de `codeNat` + elección |
| líneas | ~330 | **102** |
| footprint | `[propext, Classical.choice, Quot.sound]` | **idéntico** |

⚠️ **Las dos valen y las dos están compiladas.** Se adoptó la primera por una razón, y conviene
que quede escrita: una `noncomputable def formula_enum` obtenida por elección es una sobreyección
**semántica** y nada más — en un proyecto cuyo asunto es la **representabilidad** y los conjuntos
**r.e.**, tener la enumeración **efectiva** (y `#eval`‑uable) es la propiedad que se quiere.
El precio son 230 líneas.

⬜ **Y lo que de aquí sigue siendo útil por sí mismo**: `codeNat` es un **codificador inyectivo**
de fórmulas a `Nat` con su inyectividad probada. Si alguna vez hace falta uno, está aquí hecho.

⚠️ Este fichero **no entra en el build** (`sondeos/` está fuera del `lean_lib`). Para comprobarlo,
desde la raíz de ROBINSON_PlusPlus: `lake env lean sondeos/EnumFormulaPorInyeccion.lean`.
Verificado el 2026‑09‑13.
-/

/-! MEDICION: ¿son `formula_enum` / `formula_enum_surj` (FOL/Completeness.lean:119-120)
    DERIVABLES en vez de postulados? Este fichero importa SOLO `FOL.FOL`. -/
namespace ProbeEnum


def triN : Nat → Nat | 0 => 0 | n+1 => triN n + (n+1)
def consN (a b : Nat) : Nat := triN (a + (b + 1)) + (b + 1)

theorem triN_succ (n : Nat) : triN (n + 1) = triN n + (n + 1) := rfl
theorem triN_mono : ∀ {a b : Nat}, a ≤ b → triN a ≤ triN b := by
  intro a b h; induction h with
  | refl => exact Nat.le_refl _
  | @step n _ ih => refine Nat.le_trans ih ?_; rw [triN_succ]; omega
theorem tri_diag_unique {s y s' y' : Nat} (hy : y ≤ s) (hy' : y' ≤ s')
    (h : triN s + y = triN s' + y') : s = s' := by
  rcases Nat.lt_trichotomy s s' with hlt | heq | hgt
  · have h1 : triN (s + 1) ≤ triN s' := triN_mono hlt; rw [triN_succ] at h1; omega
  · exact heq
  · have h1 : triN (s' + 1) ≤ triN s := triN_mono hgt; rw [triN_succ] at h1; omega
theorem consN_inj {a b a' b' : Nat} (h : consN a b = consN a' b') : And (a = a') (b = b') := by
  have h' : triN (a + (b + 1)) + (b + 1) = triN (a' + (b' + 1)) + (b' + 1) := h
  have hs : a + (b + 1) = a' + (b' + 1) := tri_diag_unique (by omega) (by omega) h'
  rw [hs] at h'; exact And.intro (by omega) (by omega)
theorem consN_ne_zero (a b : Nat) : consN a b ≠ 0 := by unfold consN; omega

def codeNatChars : List Char → Nat | [] => 0 | c :: cs => consN c.toNat (codeNatChars cs)
def codeNatStr (s : String) : Nat := codeNatChars s.toList
mutual
def codeNatTerm : Term → Nat
  | .var n => consN 0 (consN n 0)
  | .func s ts => consN 1 (consN (codeNatStr s) (consN (codeNatTerms ts) 0))
def codeNatTerms : List Term → Nat
  | [] => 0
  | t :: ts => consN (codeNatTerm t) (codeNatTerms ts)
end
def codeNat : Formula → Nat
  | .bottom => consN 2 0
  | .atom p ts => consN 3 (consN (codeNatStr p) (consN (codeNatTerms ts) 0))
  | .eq t u => consN 4 (consN (codeNatTerm t) (consN (codeNatTerm u) 0))
  | .impl a b => consN 5 (consN (codeNat a) (consN (codeNat b) 0))
  | Formula.forall a => consN 6 (consN (codeNat a) 0)
  | .and a b => consN 7 (consN (codeNat a) (consN (codeNat b) 0))
  | .or a b => consN 8 (consN (codeNat a) (consN (codeNat b) 0))
  | .ex a => consN 9 (consN (codeNat a) 0)

theorem codeNatChars_inj : ∀ {cs ds : List Char}, codeNatChars cs = codeNatChars ds → cs = ds
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h.symm (consN_ne_zero _ _)
  | _ :: _, [], h => absurd h (consN_ne_zero _ _)
  | c :: cs, d :: ds, h => by
      have := consN_inj h
      have hc : c = d := Char.ext (UInt32.toNat_inj.mp this.1)
      rw [hc, codeNatChars_inj this.2]
theorem codeNatStr_inj {s t : String} (h : codeNatStr s = codeNatStr t) : s = t := by
  have := codeNatChars_inj (cs := s.toList) (ds := t.toList) h
  exact String.ext (by simpa [String.toList] using this)
mutual
theorem codeNatTerm_inj : ∀ {t u : Term}, codeNatTerm t = codeNatTerm u → t = u
  | .var _, .var _, h => by have h1 := consN_inj h; have h2 := consN_inj h1.2; rw [h2.1]
  | .var _, .func _ _, h => by have := consN_inj h; omega
  | .func _ _, .var _, h => by have := consN_inj h; omega
  | .func _ _, .func _ _, h => by
      have h1 := consN_inj h; have h2 := consN_inj h1.2; have h3 := consN_inj h2.2
      rw [codeNatStr_inj h2.1, codeNatTerms_inj h3.1]
theorem codeNatTerms_inj : ∀ {ts us : List Term}, codeNatTerms ts = codeNatTerms us → ts = us
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h.symm (consN_ne_zero _ _)
  | _ :: _, [], h => absurd h (consN_ne_zero _ _)
  | _ :: _, _ :: _, h => by
      have h1 := consN_inj h; rw [codeNatTerm_inj h1.1, codeNatTerms_inj h1.2]
end
theorem codeNat_inj : ∀ {φ ψ : Formula}, codeNat φ = codeNat ψ → φ = ψ := by
  intro φ ψ h
  cases φ <;> cases ψ <;>
    first
      | rfl
      | (exfalso; have := consN_inj h; omega)
      | (simp only [codeNat] at h
         have h1 := consN_inj h
         have h2 := consN_inj h1.2
         first
           | (have h3 := consN_inj h2.2; rw [codeNatStr_inj h2.1, codeNatTerms_inj h3.1])
           | (have h3 := consN_inj h2.2; rw [codeNatTerm_inj h2.1, codeNatTerm_inj h3.1])
           | (have h3 := consN_inj h2.2; rw [codeNat_inj h2.1, codeNat_inj h3.1])
           | rw [codeNat_inj h2.1])

/-! ### LOS DOS AXIOMAS, AHORA COMO DEFINICION Y TEOREMA -/
open Classical in
noncomputable def formula_enum (n : Nat) : Formula :=
  if h : ∃ f : Formula, codeNat f = n then h.choose else Formula.bottom

theorem formula_enum_surj : ∀ f : Formula, ∃ n, formula_enum n = f := by
  intro f
  refine ⟨codeNat f, ?_⟩
  have h : ∃ g : Formula, codeNat g = codeNat f := ⟨f, rfl⟩
  rw [formula_enum, dif_pos h]
  exact codeNat_inj h.choose_spec

#print axioms formula_enum
#print axioms formula_enum_surj
end ProbeEnum
