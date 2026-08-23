/-
✅ SONDEO POSITIVO (2026-08-23) — **`codeNat` ES INYECTIVA**, y el sustituto de `canon_ne` sale.

Contexto: `sondeos/CanonNeRefuta.lean` refutó el paso 1.1 de `PLAN-NEGVERIFIER.md` — `canon_ne`
(distinción de **términos con forma de código**) es FALSO y reintroduciría la inconsistencia. La
salida propuesta era la misma que ADR-012: **pasar a NUMERALES**, donde la distinción SÍ es
provable. Este sondeo mide si esa vía existe.

## RESULTADO: sí, y en dos mitades — una ya estaba hecha

| pieza | estado |
|---|---|
| **(b)** `numeral_ne : a ≠ b → axioms ⊢ neg (numeral a =eq numeral b)` | ✅ **YA EXISTÍA** (`Full/Numerals.lean:189`) |
| **(a)** inyectividad de `codeNat` | ✅ **construida aquí**, net‑0 |

## La cadena

    consN_inj        el núcleo: `consN` ES el emparejamiento de Cantor
                     (`consN a b = triN (a+b+1) + (b+1)`, offset acotado por la diagonal).
                     [propext, Quot.sound] -- ni siquiera necesita `choice`.
    codeNatChars_inj / codeNatStr_inj
    codeNatTerm_inj / codeNatTerms_inj   (mutua)
    codeNat_inj      los tags 2-9 separan los constructores vía `consN_inj`.
    codeNat_ne       EL SUSTITUTO DE canon_ne. Base sancionada (ω + ax_induction, vía numeral_ne).

⇒ **El rediseño de `NegVerifier` por numerales es viable, y NO cuesta axiomas nuevos.**

## Dos hallazgos laterales

1. ⚠️ **Hay DOS `numeral` duplicados**: `Full.numeral` (`Full/Numerals.lean:49`) y
   `Meta.Godel.numeral` (`Meta/Godel.lean:77`). Definiciones idénticas en namespaces distintos, así
   que Lean **no** las identifica y el puente (`num_bridge`) hay que probarlo por inducción.
   `numeral_ne` usa la de `Full`; los códigos usan la de `Godel`. **Deuda técnica menor, real.**
2. ⚠️ La trampa de notación de siempre: con `Minimal.Axioms` abierto, `∧` resuelve a `Formula.and`.
   Hay que escribir `And` explícito en enunciados sobre `Prop`.

## ▶ Lo que esto NO cubre todavía

`canon_ne` se usaba en el módulo C sobre **líneas** (`cons`-árboles de códigos), no sólo sobre
fórmulas. Pero **`consN_inj` es el motor general**: cualquier estructura construida con `consN` a
partir de hojas inyectivamente codificadas queda inyectivamente codificada. Falta **decidir la
representación numeral de las líneas** y aplicarlo. Ése es el siguiente paso del frente.

**Promoción a producción**: `consN_inj` y `codeNat_inj` encajan en `Meta/CodeNumeralPrf.lean` sin
más; `codeNat_ne` necesita además `Full.numeral_ne`.
-/
import ROBINSON_PlusPlus.Meta

open ROBINSON_PlusPlus.Meta.CodeNumeralPrf

namespace CodeNatInjDev

theorem triN_succ (n : Nat) : triN (n + 1) = triN n + (n + 1) := rfl

/-- `triN` es monótona. -/
theorem triN_mono : ∀ {a b : Nat}, a ≤ b → triN a ≤ triN b := by
  intro a b h
  induction h with
  | refl => exact Nat.le_refl _
  | @step n _ ih =>
      refine Nat.le_trans ih ?_
      rw [triN_succ]
      omega

/-- **El núcleo**: el emparejamiento de Cantor separa la «diagonal» del «offset».
    Si `triN s + y = triN s' + y'` con los offsets acotados por su diagonal, entonces `s = s'`. -/
theorem tri_diag_unique {s y s' y' : Nat} (hy : y ≤ s) (hy' : y' ≤ s')
    (h : triN s + y = triN s' + y') : s = s' := by
  rcases Nat.lt_trichotomy s s' with hlt | heq | hgt
  · -- s < s'  ⟹  triN s' ≥ triN (s+1) = triN s + s + 1 > triN s + y
    have h1 : triN (s + 1) ≤ triN s' := triN_mono hlt
    rw [triN_succ] at h1
    omega
  · exact heq
  · have h1 : triN (s' + 1) ≤ triN s := triN_mono hgt
    rw [triN_succ] at h1
    omega

/-- **`consN` es INYECTIVA.** Es el emparejamiento de Cantor: `consN a b = triN (a+b+1) + (b+1)`,
    con el offset `b+1` acotado por la diagonal `a+b+1`. -/
-- ⚠️ `∧` resuelve a `Formula.and` con `Minimal.Axioms` abierto (trampa de notación conocida):
--    aquí hace falta `And` de `Prop`, explícito.
theorem consN_inj {a b a' b' : Nat} (h : consN a b = consN a' b') :
    And (a = a') (b = b') := by
  have h' : triN (a + (b + 1)) + (b + 1) = triN (a' + (b' + 1)) + (b' + 1) := h
  have hs : a + (b + 1) = a' + (b' + 1) :=
    tri_diag_unique (by omega) (by omega) h'
  -- con la diagonal ya igualada, los dos `triN` son el MISMO término y se cancelan
  rw [hs] at h'
  exact And.intro (by omega) (by omega)

end CodeNatInjDev

#print axioms CodeNatInjDev.consN_inj

namespace CodeNatInjDev2
open CodeNatInjDev

/-- `consN` nunca vale 0 (su offset es `b+1 ≥ 1`) ⟹ separa lista vacía de no vacía. -/
theorem consN_ne_zero (a b : Nat) : consN a b ≠ 0 := by
  unfold consN; omega

theorem codeNatChars_inj : ∀ {cs ds : List Char},
    codeNatChars cs = codeNatChars ds → cs = ds
  | [], [], _ => rfl
  | [], d :: ds, h => absurd h.symm (consN_ne_zero _ _)
  | c :: cs, [], h => absurd h (consN_ne_zero _ _)
  | c :: cs, d :: ds, h => by
      have := consN_inj h
      have hc : c = d := Char.ext (UInt32.toNat_inj.mp this.1)
      rw [hc, codeNatChars_inj this.2]

theorem codeNatStr_inj {s t : String} (h : codeNatStr s = codeNatStr t) : s = t := by
  have := codeNatChars_inj (cs := s.toList) (ds := t.toList) h
  exact String.ext (by simpa [String.toList] using this)

end CodeNatInjDev2

namespace CodeNatInjDev3
open CodeNatInjDev CodeNatInjDev2

mutual
theorem codeNatTerm_inj : ∀ {t u : Term}, codeNatTerm t = codeNatTerm u → t = u
  | .var n, .var m, h => by
      have h1 := consN_inj h
      have h2 := consN_inj h1.2
      rw [h2.1]
  | .var _, .func _ _, h => by have := consN_inj h; omega
  | .func _ _, .var _, h => by have := consN_inj h; omega
  | .func s ts, .func s' ts', h => by
      have h1 := consN_inj h
      have h2 := consN_inj h1.2
      have h3 := consN_inj h2.2
      rw [codeNatStr_inj h2.1, codeNatTerms_inj h3.1]
theorem codeNatTerms_inj : ∀ {ts us : List Term}, codeNatTerms ts = codeNatTerms us → ts = us
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h.symm (consN_ne_zero _ _)
  | _ :: _, [], h => absurd h (consN_ne_zero _ _)
  | t :: ts, u :: us, h => by
      have h1 := consN_inj h
      rw [codeNatTerm_inj h1.1, codeNatTerms_inj h1.2]
end

/-- **`codeNat` es INYECTIVA.** Los tags 2‑9 separan los constructores vía `consN_inj`. -/
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
           | (have h3 := consN_inj h2.2
              rw [codeNatStr_inj h2.1, codeNatTerms_inj h3.1])
           | (have h3 := consN_inj h2.2
              rw [codeNatTerm_inj h2.1, codeNatTerm_inj h3.1])
           | (have h3 := consN_inj h2.2
              rw [codeNat_inj h2.1, codeNat_inj h3.1])
           | rw [codeNat_inj h2.1])

end CodeNatInjDev3

#print axioms CodeNatInjDev2.codeNatChars_inj
#print axioms CodeNatInjDev2.codeNatStr_inj
#print axioms CodeNatInjDev3.codeNatTerm_inj
#print axioms CodeNatInjDev3.codeNat_inj

namespace CodeNatInjDev4
open ROBINSON_PlusPlus.Minimal.Axioms
open CodeNatInjDev3

/-- ⚠️ **HALLAZGO LATERAL: hay DOS `numeral` duplicados** en el proyecto —
    `ROBINSON_PlusPlus.Full.numeral` (`Full/Numerals.lean:49`) y
    `ROBINSON_PlusPlus.Meta.Godel.numeral` (`Meta/Godel.lean:77`). Definiciones idénticas en
    namespaces distintos, así que Lean **no** las identifica: el puente hay que probarlo.
    `numeral_ne` usa la de `Full`; los códigos usan la de `Godel`. -/
theorem num_bridge : ∀ n : Nat,
    ROBINSON_PlusPlus.Full.numeral n = ROBINSON_PlusPlus.Meta.Godel.numeral n
  | 0 => rfl
  | n + 1 => by
      show succ (ROBINSON_PlusPlus.Full.numeral n) = succ (ROBINSON_PlusPlus.Meta.Godel.numeral n)
      rw [num_bridge n]

/-- **EL SUSTITUTO DE `canon_ne`.** Fórmulas distintas ⟹ sus códigos NUMERALES son
    provablemente distintos.

    ⚠️ Nótese la diferencia con el `canon_ne` refutado (`sondeos/CanonNeRefuta.lean`): allí se
    comparaban **términos con forma de código**, donde un árbol `cons` y un numeral pueden denotar
    el mismo número — y de ahí el `⊥`. Aquí se comparan **numerales**, donde la distinción SÍ es
    provable. Es la misma corrección que ADR‑012. -/
theorem codeNat_ne {φ ψ : Formula} (h : φ ≠ ψ) :
    axioms ⊢ neg (ROBINSON_PlusPlus.Meta.Godel.numeral (codeNat φ)
             =eq ROBINSON_PlusPlus.Meta.Godel.numeral (codeNat ψ)) := by
  rw [← num_bridge, ← num_bridge]
  exact ROBINSON_PlusPlus.Full.numeral_ne (fun heq => h (codeNat_inj heq))

/-- Y su versión para TÉRMINOS. -/
theorem codeNatTerm_ne {t u : Term} (h : t ≠ u) :
    axioms ⊢ neg (ROBINSON_PlusPlus.Meta.Godel.numeral (codeNatTerm t)
             =eq ROBINSON_PlusPlus.Meta.Godel.numeral (codeNatTerm u)) := by
  rw [← num_bridge, ← num_bridge]
  exact ROBINSON_PlusPlus.Full.numeral_ne (fun heq => h (codeNatTerm_inj heq))

end CodeNatInjDev4

#print axioms CodeNatInjDev4.num_bridge
#print axioms CodeNatInjDev4.codeNat_ne
#print axioms CodeNatInjDev4.codeNatTerm_ne
