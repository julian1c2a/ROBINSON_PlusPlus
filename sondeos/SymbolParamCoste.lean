import FOL

-- ══════════════════════════════════════════════════════════════════════════
-- SONDEO del coste que QUEDA del paso 4 (`String → S`), **después** de ADR-068.
--
-- ADR-068 metió el parámetro: el árbol dice `TermG S` / `FormulaG S` con
-- `abbrev Term := TermG String`. Coste medido: TRES ficheros, ~40 líneas, y los
-- 147 footprints idénticos. `sondeos/SymbolParam.lean` midió la viabilidad del
-- inductivo; ESTE mide lo que falta para **instanciar `S` en otro tipo**.
--
-- Son dos obstrucciones, y sólo la segunda es cara:
--   (1) `FOL/Fresh0.lean` fabrica símbolos frescos (`shift`, `cst`) ⇒ clase `FreshSym`
--   (2) ⛔ `FOL/Enumeration.lean` necesita `natToString_surj` ⇒ clase `EnumSym`, y de
--       ésta cuelgan `Lindenbaum0` → `HenkinLimit0` → `Canonical0` → `completeness₀`.
--
-- ⚠️ Cero `sorry`, cero `axiom`. Lo que aquí se mide es que **las dos clases existen,
-- son mínimas y son instanciables por `List Char` SIN pasar por `String`**.
-- ══════════════════════════════════════════════════════════════════════════

namespace ProbeCoste

-- ══════════════════════════════════════════════════════════════════════════
-- §1 · obstrucción (1): `Fresh0` fabrica símbolos frescos.
-- En el árbol (`FOL/Fresh0.lean`): `shift s := "f" ++ s`, `cst 0 := "g"`, `cst (n+1) := "a" ++ cst n`, con TRES propiedades
-- (`shift_inj`, `cst_inj`, `cst_ne_shift`). La clase es exactamente esas tres:
-- ni una más, y ninguna de ellas pide decidibilidad ni orden.
-- ══════════════════════════════════════════════════════════════════════════

class FreshSym (S : Type) where
  shift        : S → S
  cst          : Nat → S
  shift_inj    : ∀ s t, shift s = shift t → s = t
  cst_inj      : ∀ m n, cst m = cst n → m = n
  cst_ne_shift : ∀ n s, cst n ≠ shift s

/-- ⭐ `List Char` la satisface **sin pasar por `String`** ⇒ el paso 4 no depende de que
el tipo de símbolos siga siendo `String` ni un día más. -/
instance : FreshSym (List Char) where
  shift s := 'f' :: s
  cst n := 'c' :: List.replicate n 'i'
  shift_inj := by
    intro s t h
    injection h
  cst_inj := by
    intro m n h
    injection h with _ h2
    have hl := congrArg List.length h2
    simpa using hl
  cst_ne_shift := by
    intro n s h
    injection h with h1 _
    exact absurd h1 (by decide)

/-- ⚠️ Y `String` también, con lo que `FOL/Fresh0.lean` **ya tiene probado**: la clase no
pide nada que el árbol no pague hoy. Este testigo es el control de que la clase no se
quedó corta ni se pasó de larga. -/
instance : FreshSym String where
  shift := FOL.Fresh0.shift
  cst := FOL.Fresh0.cst
  shift_inj := FOL.Fresh0.shift_inj
  cst_inj := FOL.Fresh0.cst_inj
  cst_ne_shift := FOL.Fresh0.cst_ne_shift

-- ══════════════════════════════════════════════════════════════════════════
-- §2 · ⛔⛔ obstrucción (2), LA CARA: `Enumeration.natToString_surj`.
-- `Lindenbaum0` enumera las FÓRMULAS (`φₙ`), y para eso enumera los SÍMBOLOS.
-- Con `S` genérico eso **no es demostrable**: hay `S` no numerables.
-- ⇒ hace falta una hipótesis, y la pregunta medible es **de qué fuerza**.
-- ══════════════════════════════════════════════════════════════════════════

/-- La hipótesis mínima que `Enumeration` usa: una **sobreyección** `Nat → S`.
⭐ No hace falta biyección, ni decidibilidad, ni orden, ni inyectividad. -/
class EnumSym (S : Type) where
  enum      : Nat → S
  enum_surj : ∀ s, ∃ n, enum n = s

/-- ✅ `String` la satisface con lo que `FOL/Enumeration.lean` **ya tiene probado**. -/
instance : EnumSym String where
  enum := FOL.Metamath.Enumeration.natToString
  enum_surj := FOL.Metamath.Enumeration.natToString_surj

/-- ⭐⭐ Y `List Char` la satisface **más barato todavía**: sale de la capa 1 de
`Enumeration.lean` (`natToList_surj`, sobre `List Nat`) más `map_ofNat_toNat`, y **no toca
`String` en absoluto** ⇒ si el paso 4 se cierra con `List Char`, el `Classical.choice` que
entra hoy por DESCOMPONER un `String` no entra por aquí
(véase [[feedback-footprint-no-es-constructividad]]). -/
instance : EnumSym (List Char) where
  enum n := (FOL.Metamath.Enumeration.natToList n).map Char.ofNat
  enum_surj := by
    intro s
    obtain ⟨n, hn⟩ := FOL.Metamath.Enumeration.natToList_surj (s.map Char.toNat)
    refine ⟨n, ?_⟩
    rw [hn]
    exact FOL.Metamath.Enumeration.map_ofNat_toNat s

-- ══════════════════════════════════════════════════════════════════════════
-- §3 · el CONSUMIDOR antes que el molde (regla del proyecto).
-- Lo único que `Lindenbaum0` le pide a `Enumeration` es una `Nat → Formula`
-- SOBREYECTIVA. El resto de `Enumeration.lean` (pares de Cantor, capas 3 y 4) es
-- genérico en el símbolo y no cambia; el único eslabón nuevo es éste.
-- ══════════════════════════════════════════════════════════════════════════

/-- ⭐ El eslabón: de símbolos enumerables a átomos enumerables, **genérico en `S`**.
Si esto sale, el resto de la capa 4 es el mismo emparejamiento de Cantor de hoy. -/
theorem atom_surj {S : Type} [EnumSym S]
    (enumTs : Nat → List (TermG S)) (hTs : ∀ ts, ∃ n, enumTs n = ts) :
    ∀ p ts, ∃ n m, FormulaG.atom (EnumSym.enum n) (enumTs m) = FormulaG.atom p ts := by
  intro p ts
  obtain ⟨n, hn⟩ := EnumSym.enum_surj (S := S) p
  obtain ⟨m, hm⟩ := hTs ts
  exact ⟨n, m, by rw [hn, hm]⟩

/-- ⚠️ Y el control de que la clase **no sobra**: sin `EnumSym` el eslabón es falso, porque
hay `S` sin ninguna sobreyección desde `Nat`. Aquí se deja sólo enunciado lo que la
hipótesis compra, no una demostración de que haga falta (eso es cardinalidad y el
proyecto no la tiene). -/
theorem enum_gives_witness {S : Type} [EnumSym S] (p : S) : ∃ n, EnumSym.enum n = p :=
  EnumSym.enum_surj p

end ProbeCoste

-- ⚠️ CONTROL: el sondeo no debe traer nada que el árbol no traiga ya.
#print axioms ProbeCoste.atom_surj
#print axioms ProbeCoste.instFreshSymListChar
#print axioms ProbeCoste.instEnumSymListChar
#print axioms ProbeCoste.instEnumSymString
