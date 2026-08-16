/-
SONDEO DE MAGNITUD — ¿de qué tamaño es `codeNat φ` de verdad?

Calcula log₂(valor+1) del término `formCode φ` siguiendo las ecuaciones EXACTAS del proyecto:
  nil = zero = 0
  cons h t = pair h (σ t) = ((h+σt)(h+σt+1) + 2(σt)) / 2        [ax_L0_cons_def + cantor_func]
Todo en espacio logarítmico para no desbordar.
-/
import ROBINSON_PlusPlus.Meta.Provability

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Provability

/-- `log₂(2^a + 2^b)` sin desbordar. -/
def lse2 (a b : Float) : Float :=
  let m := max a b
  let d := -(Float.abs (a - b))
  m + Float.log2 (1.0 + Float.exp2 d)

/-- `L t = log₂(valor(t) + 1)`, siguiendo `cons h t = ((h+σt)(h+σt+1) + 2σt)/2`. -/
partial def L : Term → Float
  | .func s args =>
      if s = zero_sym then 0.0
      else if s = succ_sym then
        match args with
        | [x] => lse2 (L x) 0.0          -- v+1
        | _   => 0.0
      else if s = cons_sym then
        match args with
        | [h, t] =>
            let a := L h                  -- vh = 2^a - 1
            let b := lse2 (L t) 0.0       -- σt : vt+1 = 2^b - 1
            let ls := lse2 a b            -- ≈ log₂(vh + vt+1 + 1)
            2.0 * ls - 1.0                -- ≈ log₂((s² /2) + 1)
        | _ => 0.0
      else 0.0
  | _ => 0.0

/-- Profundidad de anidamiento de `cons` (el exponente de la torre). -/
partial def consDepth : Term → Nat
  | .func s args =>
      if s = cons_sym then
        match args with
        | [h, t] => 1 + max (consDepth h) (consDepth t)
        | _ => 0
      else 0
  | _ => 0

/-- Nº de nodos `cons` (tamaño del árbol de código). -/
partial def consSize : Term → Nat
  | .func s args =>
      if s = cons_sym then
        match args with
        | [h, t] => 1 + consSize h + consSize t
        | _ => 0
      else 0
  | _ => 0

def report (nombre : String) (φ : Formula) : String :=
  let c := formCode φ
  let l := L c
  s!"{nombre}: prof_cons={consDepth c}  nodos={consSize c}  log2(N)≈{l}  ⟹ N ≈ 2^{l}"

-- Fórmulas de referencia, de la más simple a un axioma real.
#eval report "bottom            " Formula.bottom
#eval report "0 = 0             " (Formula.eq zero zero)
#eval report "0 = 0 ⇒ 0 = 0     " (Formula.impl (Formula.eq zero zero) (Formula.eq zero zero))
#eval report "ax_L0_cons_def    " ax_L0_cons_def
#eval report "ax_tc_succ        " ax_tc_succ
#eval report "ax_tc_cons        " ax_tc_cons

-- ¿Cuántas líneas tiene una lista de axiomas? (la cota REAL de boundedCarcIn es `lenc p`)
#eval s!"nº de axiomas del sistema = {axioms.length}"
