import ROBINSON_PlusPlus

/-!
# SONDEO · ¿es caro el **despachador** de `DEUDA_chainNeg`?

**Fecha**: 2026‑09‑21. **Pregunta**: repartir entre las seis causas exige un split de 21 tags,
y `Meta/ChainDecode.lean:44` avisa de que *«un `match` sobre `Term` con las 21 formas anidadas
revienta el `whnf` (`String.decEq` en el discriminante)»*. Ése era el riesgo declarado de la vía.

## Resultado: el aviso **no aplica**, y el riesgo se cae

⛔⛔ El aviso era **cierto** y estaba en el sitio equivocado: describe la vía que **`peelArgs` ya
había abandonado**. El despachador no matchea sobre `Term`; matchea sobre `(tag : Nat, args :
List Term)`, que es exactamente lo que `peelArgs` deja a mano. **Medido: 4,5 s y net‑0 puro.**

🔑 *Una nota de riesgo sobrevive al rediseño que la deja sin objeto, y se sigue cotizando.*
Es el mismo patrón que ADR‑075 §2 («una afirmación de estado viaja a una cabecera sin que nadie
la compile») y que ADR‑076 (la ✅ falsa de (d)), pero al revés: aquí lo que viajaba era un **coste
sobrestimado**, no un logro inexistente.

⚠️ **Lo único que Lean no cierra solo** es la rama `k ≥ 21`: `omega` **no** ve `Nat.le` escrito
como aplicación explícita («No usable constraints found»), aunque sea defeq a `≤`. Se descarga con
`Nat.le_trans (Nat.le_add_left 21 n) hk` y un `decide` sobre `21 ≤ 20`.
🔑 *Escribir `Nat.le` para esquivar la trampa del símbolo OBJETO `le` tiene su propio precio:
las tácticas aritméticas dejan de reconocerlo.*

## Cómo re‑ejecutarlo

    lake env lean sondeos/DespachadorCoste.lean      # desde la raíz de RPP, NUNCA desde FOL/
-/

open FOL
open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.CodeDecode
open ROBINSON_PlusPlus.Meta.ChainDecode
open ROBINSON_PlusPlus.Meta.HilbertSeq

namespace DespachadorCoste

set_option maxHeartbeats 2000000

/-- ⭐⭐⭐ **EL SPLIT DE 21 TAGS CON LA HIPÓTESIS ABIERTA** — la forma exacta que tendrá el
despachador al repartir. La rama 15 se cierra de verdad (es la de (d)); las demás sólo hacen ver
que el split **elabora**. Coste medido del fichero entero: **4,5 s**. -/
theorem split21_none (acc : List Formula) (f : Formula) (k : Nat) (args : List Term)
    (h : decodeRuleTag acc f k args = none) (hk : Nat.le k 20) :
    Or (findIdx f axioms = none) (k ≠ 15) := by
  match k, hk with
  | 0, _ => exact Or.inr (by decide)
  | 1, _ => exact Or.inr (by decide)
  | 2, _ => exact Or.inr (by decide)
  | 3, _ => exact Or.inr (by decide)
  | 4, _ => exact Or.inr (by decide)
  | 5, _ => exact Or.inr (by decide)
  | 6, _ => exact Or.inr (by decide)
  | 7, _ => exact Or.inr (by decide)
  | 8, _ => exact Or.inr (by decide)
  | 9, _ => exact Or.inr (by decide)
  | 10, _ => exact Or.inr (by decide)
  | 11, _ => exact Or.inr (by decide)
  | 12, _ => exact Or.inr (by decide)
  | 13, _ => exact Or.inr (by decide)
  | 14, _ => exact Or.inr (by decide)
  | 15, _ =>
      refine Or.inl ?_
      rcases hj : findIdx f axioms with _ | j
      · rfl
      · rw [show decodeRuleTag acc f 15 args = (findIdx f axioms).map Rule.thy from rfl, hj] at h
        simp at h
  | 16, _ => exact Or.inr (by decide)
  | 17, _ => exact Or.inr (by decide)
  | 18, _ => exact Or.inr (by decide)
  | 19, _ => exact Or.inr (by decide)
  | 20, _ => exact Or.inr (by decide)
  -- ⚠️ `omega` NO cierra esto: no reconoce `Nat.le` como aplicación explícita.
  | (n + 21), hk2 => exact absurd (Nat.le_trans (Nat.le_add_left 21 n) hk2) (by decide)

/-! ## Las ecuaciones por tag, todas por `rfl`

Cada rama del split abre su propia ecuación de `decodeRuleTag` **sin táctica**: el `match` del
`def` es superficial sobre `(Nat, List Term)`. Muestra de las tres aridades y de los tres raros. -/

example (acc : List Formula) (f : Formula) (a b c : Term) :
    decodeRuleTag acc f 1 [a, b, c]
      = (decodeForm a).bind fun A => (decodeForm b).bind fun B => (decodeForm c).map fun C =>
          Rule.p2 A B C := rfl

example (acc : List Formula) (f : Formula) (a t : Term) :
    decodeRuleTag acc f 9 [a, t]
      = (decodeForm a).bind fun A => (decodeTerm t).map fun u => Rule.q1 A u := rfl

example (acc : List Formula) (f : Formula) (args : List Term) :
    decodeRuleTag acc f 15 args = (findIdx f axioms).map Rule.thy := rfl

example (acc : List Formula) (f : Formula) (cfj : Term) :
    decodeRuleTag acc f 16 [cfj]
      = (decodeForm cfj).bind fun fj => (findIdx fj acc).bind fun j =>
          (findIdx (Formula.impl fj f) acc).map fun i => Rule.mp i j := rfl

example (acc : List Formula) (f : Formula) (cg : Term) :
    decodeRuleTag acc f 17 [cg]
      = (decodeForm cg).bind fun g => (findIdx g acc).map fun i => Rule.gen i := rfl

/-- ⛔ Y la **aridad equivocada**, que es la causa (b): tres argumentos en un tag de aridad dos.
    También por `rfl` ⇒ (b) no necesita nada estructural, sólo las 21 ramas de `prf_lenc_*`. -/
example (acc : List Formula) (f : Formula) (a b c : Term) :
    decodeRuleTag acc f 0 [a, b, c] = none := rfl

end DespachadorCoste

#print axioms DespachadorCoste.split21_none
