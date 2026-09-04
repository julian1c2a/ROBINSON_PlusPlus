import ROBINSON_PlusPlus.Meta.CodeNumeralPrf
import ROBINSON_PlusPlus.Full.Numerals
/-!
# `Meta/CodeNatInjPrf.lean` — INYECTIVIDAD de la codificación numeral, y `codeNat_ne`

`Meta/CodeNumeralPrf.lean` define `triN`, `consN`, `codeNatChars`, `codeNatTerm` y `codeNat`.
Aquí se prueba que **son inyectivas**, y de ahí sale el resultado que consume el frente:

```lean
codeNat_ne     {φ ψ : Formula} (h : φ ≠ ψ) : axioms ⊢ neg (numeral (codeNat φ) =eq numeral (codeNat ψ))
codeNatTerm_ne {t u : Term}    (h : t ≠ u) : axioms ⊢ neg (numeral (codeNatTerm t) =eq numeral (codeNatTerm u))
```

## ⚠️ Por qué esto NO es `canon_ne`, que era FALSO

`canon_ne` comparaba **términos con forma de código**, y en esta teoría un árbol `cons` **ES** un
número (`cons nil nil = 2 = numeralM 2`), así que términos sintácticamente distintos pueden ser
**provablemente iguales** — de ahí el `⊥` (`sondeos/CanonNeRefuta.lean`).

Aquí se comparan **NUMERALES**, donde la distinción **sí** es provable. Es la misma corrección de
categoría que ADR‑012: lo que hay que distinguir es el **VALOR**, no la sintaxis.

## El motor

**`consN_inj`** es el emparejamiento de Cantor: `consN a b = triN (a+b+1) + (b+1)`, con el offset
acotado por la diagonal. De él salen en cascada `codeNatChars_inj` → `codeNatStr_inj` →
`codeNatTerm_inj`/`codeNatTerms_inj` → `codeNat_inj`. ⇒ **cualquier estructura construida con
`consN` desde hojas inyectivas queda inyectiva.**

⚠️ **Deuda que este módulo hace visible**: hay **DOS `numeral`** —`Full.numeral`
(`Full/Numerals.lean:49`) y `Meta.Godel.numeral` (`Meta/Godel.lean:77`)—, definiciones idénticas en
namespaces distintos que Lean **no** identifica. `numeral_ne` usa la de `Full` y los códigos la de
`Godel`, así que hace falta el puente **`num_bridge`**, que se prueba aquí por inducción.

Promovido de `sondeos/CodeNatInj.lean` (2026‑09‑01). Cero `sorry`.

⚠️ **NO «cero axiomas de Lean»**, como decía antes esta línea. Medido con `#print axioms`,
los dos resultados de cabecera —`codeNat_ne` y `codeNatTerm_ne`— salen con **OCHO**:

    [propext, Classical.choice, Quot.sound,
     FOL.MetaRules.ex_elim, FOL.MetaRules.gen, FOL.MetaRules.imp_intro, FOL.MetaRules.raa,
     ROBINSON_PlusPlus.Full.ax_induction]

Las cinco meta-reglas ω y `ax_induction` entran enteras por `Full.numeral_ne`, que tiene ese
mismo footprint. **No hay axioma NUEVO** —que es lo que la frase quería decir— pero «cero
axiomas» era falso, y es justo la clase de frase que un libro cita como garantía.
Desbloquea los casos 3 y 4 del módulo C de `NegVerifier` (ver `PLAN-NEGVERIFIER.md`).
-/

open ROBINSON_PlusPlus.Meta.CodeNumeralPrf

namespace ROBINSON_PlusPlus.Meta.CodeNatInjPrf


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




/-! ### El puente, y el sustituto de `canon_ne`

⚠️ Estas dos necesitan `Minimal.Axioms` abierto, pero **NO se puede abrir arriba del fichero**:
con él, `≤` y `<` resuelven al orden **OBJETO** (sobre `Term`) y `triN_mono` deja de tipar con un
error **opaco** que no menciona `≤`. Es la trampa de notación registrada del proyecto
(`feedback-lean-notation-traps` §1), y mordió exactamente así al promover. Por eso el `open` va
**confinado a esta sección**. -/

section CanonNeSustituto
open ROBINSON_PlusPlus.Minimal.Axioms

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


end CanonNeSustituto

end ROBINSON_PlusPlus.Meta.CodeNatInjPrf

export ROBINSON_PlusPlus.Meta.CodeNatInjPrf (
  triN_succ triN_mono tri_diag_unique consN_inj consN_ne_zero
  codeNatChars_inj codeNatStr_inj codeNatTerm_inj codeNatTerms_inj codeNat_inj
  num_bridge codeNat_ne codeNatTerm_ne
)
