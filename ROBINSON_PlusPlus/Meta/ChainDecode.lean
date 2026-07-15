/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.CodeDecode
import ROBINSON_PlusPlus.Meta.Representability2

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.CodeDecode
open ROBINSON_PlusPlus.Meta.HilbertSeq
open ROBINSON_PlusPlus.Meta.Representability2

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.ChainDecode

/-!
## META — NIVEL D real (§43·A.2): DECODIFICADOR de CADENAS (módulo A de `PLAN-NEGVERIFIER.md`)

Inversos de los codificadores de prueba `lineJustif` / `lineCode'` / `proofCode'`
(`Meta/Representability2.lean`). Construido sobre `CodeDecode` (fórmulas/términos).

### ⚠️ El codificador es LOSSY para `thy`/`mp`/`gen` ⟹ **sección**, no *retract*

`lineJustif` **descarta los índices** de tres reglas (ver `Representability2.lean:46`):
* `thy k    ↦ cons 15̇ nil`                       — la `k` NO se guarda;
* `mp i j   ↦ cons 16̇ (cons ⌜acc[j]⌝ nil)`        — guarda la **premisa resuelta**, no `i`/`j`;
* `gen i    ↦ cons 17̇ (cons ⌜acc[i]⌝ nil)`        — guarda `acc[i]`, no `i`.

Por tanto `decodeChain (proofCode' rs []) = some rs` (**retract**, como decía el plan) es **FALSO**
(dos `thy 3`/`thy 5` con la misma conclusión, o dos `mp i j`/`mp i' j`, producen el mismo código).
Lo correcto —y lo que `VerifierSound` (módulo E) necesita— es la **SECCIÓN**:
`decodeChain t = some rs → proofCode' rs [] = t ∧ checkProof rs ≠ none`. Los índices se recuperan
**por búsqueda** en el acumulador (`List.idxOf?`). Para los **18 tags limpios** el retract SÍ vale
(`decodeRule_lineJustif_clean`).

### Nota de rendimiento

Un `match` sobre `Term` con las 21 formas anidadas revienta el `whnf` (`String.decEq` en el
discriminante). Se **pela** el justif a `List Term` (`peelArgs`) y se matchea `(tag : Nat, args)` —
superficial y barato.
-/

/-- `decodeForm`/`decodeTerm` invierten también `formCode`/`termCode` (capa Meta), vía los puentes
    `formCodeM_eq`/`termCodeM_eq`. -/
theorem decodeForm_formCode (A : Formula) : decodeForm (formCode A) = some A := by
  rw [← ROBINSON_PlusPlus.Meta.Representability.formCodeM_eq]; exact decodeForm_formCodeM A
theorem decodeTerm_termCode (t : Term) : decodeTerm (termCode t) = some t := by
  rw [← ROBINSON_PlusPlus.Meta.Representability.termCodeM_eq]; exact decodeTerm_termCodeM t

/-- Pela un término‑lista `cons a₀ (cons a₁ … nil)` a `[a₀, a₁, …]`. -/
def peelArgs : Term → List Term
  | .func s [a, b] => if s == cons_sym then a :: peelArgs b else []
  | _ => []

@[simp] theorem peelArgs_nil : peelArgs nil = [] := rfl
@[simp] theorem peelArgs_cons (a b : Term) : peelArgs (cons a b) = a :: peelArgs b := by
  simp only [peelArgs, cons, beq_self_eq_true, if_true]

/-- Reglas por tag (0..20) + lista de argumentos (match superficial sobre `List Term`).
    `thy`/`mp`/`gen` recuperan sus índices por búsqueda en `axioms`/`acc`. -/
def decodeRuleTag (acc : List Formula) (f : Formula) : Nat → List Term → Option Rule
  | 0, [cA, cB] => (decodeForm cA).bind fun A => (decodeForm cB).map fun B => Rule.p1 A B
  | 1, [cA, cB, cC] => (decodeForm cA).bind fun A => (decodeForm cB).bind fun B => (decodeForm cC).map fun C => Rule.p2 A B C
  | 2, [cA, cB] => (decodeForm cA).bind fun A => (decodeForm cB).map fun B => Rule.c1 A B
  | 3, [cA, cB] => (decodeForm cA).bind fun A => (decodeForm cB).map fun B => Rule.c2 A B
  | 4, [cA, cB] => (decodeForm cA).bind fun A => (decodeForm cB).map fun B => Rule.c3 A B
  | 5, [cA, cB] => (decodeForm cA).bind fun A => (decodeForm cB).map fun B => Rule.j1 A B
  | 6, [cA, cB] => (decodeForm cA).bind fun A => (decodeForm cB).map fun B => Rule.j2 A B
  | 7, [cA, cB, cC] => (decodeForm cA).bind fun A => (decodeForm cB).bind fun B => (decodeForm cC).map fun C => Rule.j3 A B C
  | 8, [cA] => (decodeForm cA).map fun A => Rule.efq A
  | 9, [cA, cT] => (decodeForm cA).bind fun A => (decodeTerm cT).map fun t => Rule.q1 A t
  | 10, [cA, cT] => (decodeForm cA).bind fun A => (decodeTerm cT).map fun t => Rule.q2 A t
  | 11, [cA, cB] => (decodeForm cA).bind fun A => (decodeForm cB).map fun B => Rule.q3 A B
  | 12, [cT] => (decodeTerm cT).map fun t => Rule.eqrefl t
  | 13, [cA, cT1, cT2] => (decodeForm cA).bind fun A => (decodeTerm cT1).bind fun t1 => (decodeTerm cT2).map fun t2 => Rule.leibniz A t1 t2
  | 14, [cA] => (decodeForm cA).map fun A => Rule.p3 A
  | 18, [cA] => (decodeForm cA).map fun A => Rule.ind A
  | 19, [cP, cC] => (decodeForm cP).bind fun P => (decodeForm cC).map fun C => Rule.qconf P C
  | 20, [cA] => (decodeForm cA).map fun A => Rule.listInd A
  | 15, _ => (List.idxOf? f axioms).map Rule.thy
  | 16, [cfj] => (decodeForm cfj).bind fun fj =>
      (List.idxOf? fj acc).bind fun j => (List.idxOf? (Formula.impl fj f) acc).map fun i => Rule.mp i j
  | 17, [cg] => (decodeForm cg).bind fun g => (List.idxOf? g acc).map fun i => Rule.gen i
  | _, _ => none

/-- Inverso de `lineJustif acc` dada la conclusión `f` (necesaria para `thy`/`mp`/`gen`). -/
def decodeRule (acc : List Formula) (f : Formula) (jT : Term) : Option Rule :=
  match peelArgs jT with
  | tagT :: args => (decodeNat tagT).bind fun tag => decodeRuleTag acc f tag args
  | [] => none

/-- Inverso de `lineCode' acc f r = cons ⌜f⌝ (lineJustif acc r)`: decodifica la
    conclusión (cabeza) y la regla. -/
def decodeLine (acc : List Formula) : Term → Option (Formula × Rule)
  | .func cs [conclT, justifT] =>
      if cs == cons_sym then
        (decodeForm conclT).bind fun f => (decodeRule acc f justifT).map fun r => (f, r)
      else none
  | _ => none

/-- Inverso de `proofCode'`, hilando el acumulador de conclusiones. -/
def decodeChainAux (acc : List Formula) : Term → Option (List Rule)
  | .func s [] => if s == zero_sym then some [] else none
  | .func s [lineT, rest] =>
      if s == cons_sym then
        (decodeLine acc lineT).bind fun fr =>
          (decodeChainAux (acc ++ [fr.1]) rest).map fun rs => fr.2 :: rs
      else none
  | _ => none

def decodeChain (t : Term) : Option (List Rule) := decodeChainAux [] t

/-- Reglas cuya codificación NO descarta información (todas menos `thy`/`mp`/`gen`). -/
def cleanRule : Rule → Bool
  | .thy _ | .mp _ _ | .gen _ => false
  | _ => true

set_option maxHeartbeats 400000 in
/-- **RETRACT sobre los 18 tags limpios**: `decodeRule acc f (lineJustif acc r) = some r`.
    (Para `thy`/`mp`/`gen` sólo vale la sección, ver la cabecera.) -/
theorem decodeRule_lineJustif_clean (acc : List Formula) (f : Formula) (r : Rule)
    (hcl : cleanRule r = true) : decodeRule acc f (lineJustif acc r) = some r := by
  cases r <;>
    simp_all only [cleanRule, lineJustif, decodeRule, peelArgs_cons, peelArgs_nil,
      decodeNat_numeralM, decodeRuleTag, decodeForm_formCode, decodeTerm_termCode,
      Option.bind, Option.map, reduceCtorEq]

end ROBINSON_PlusPlus.Meta.ChainDecode

export ROBINSON_PlusPlus.Meta.ChainDecode (
  decodeForm_formCode decodeTerm_termCode
  peelArgs peelArgs_nil peelArgs_cons
  decodeRuleTag decodeRule decodeLine decodeChainAux decodeChain
  cleanRule decodeRule_lineJustif_clean
)
