/-
SONDEO S3 — ¿se mantiene SIMBÓLICO `codeNat φ`?
SONDEO S5 — ¿cuánto recorta codificar los símbolos por ÍNDICE en vez de por Unicode?

`codeNat` se escribe TOTAL y ESTRUCTURAL a propósito: si fuera `partial` sería opaca y Lean no
podría reducirla nunca, con lo que el sondeo S3 no probaría nada.

NO ES MÓDULO DE PRODUCCIÓN.
-/
import ROBINSON_PlusPlus.Meta.TcArithPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.TcArithPrf

/-! ## `codeNat` — el valor numérico del código, TOTAL y ESTRUCTURAL -/

/-- `cons h t` a nivel de valores: `cons h t = pair h (σt)` con `pair` = Cantor. -/
def consN (h t : Nat) : Nat :=
  let b := t + 1
  ((h + b) * (h + b + 1) + 2 * b) / 2

def charsCodeN : List Char → Nat
  | []      => 0
  | c :: cs => consN c.toNat (charsCodeN cs)

def strCodeN (s : String) : Nat := charsCodeN s.toList

mutual
/-- Valor de `termCode t`. -/
def tCodeN : Term → Nat
  | .var n     => consN 0 (consN n 0)
  | .func s ts => consN 1 (consN (strCodeN s) (consN (tsCodeN ts) 0))
/-- Valor de `termsCode ts`. -/
def tsCodeN : List Term → Nat
  | []      => 0
  | t :: ts => consN (tCodeN t) (tsCodeN ts)
end

/-- **`codeNat φ` = valor de `formCode φ`.** Espeja `formCode` (Provability.lean:55‑63). -/
def codeNat : Formula → Nat
  | .bottom          => consN 2 0
  | .atom p ts       => consN 3 (consN (strCodeN p) (consN (tsCodeN ts) 0))
  | .eq t u          => consN 4 (consN (tCodeN t) (consN (tCodeN u) 0))
  | .impl a b        => consN 5 (consN (codeNat a) (consN (codeNat b) 0))
  | Formula.forall a => consN 6 (consN (codeNat a) 0)
  | .and a b         => consN 7 (consN (codeNat a) (consN (codeNat b) 0))
  | .or a b          => consN 8 (consN (codeNat a) (consN (codeNat b) 0))
  | .ex a            => consN 9 (consN (codeNat a) 0)

/-! ## S3.a — ¿elabora con `φ` ABSTRACTA? (si no, la vía numeral no existe) -/

theorem s3a_simbolico (φ : Formula) :
    Prf (tcFn (numeral (codeNat φ)) =eq termCode (numeral (codeNat φ))) :=
  prf_tc_numeral (codeNat φ)

/-! ## S3.b — ¿elabora con `φ` CONCRETA sin intentar reducir?
`codeNat ax_tc_zero` es un `Nat` CERRADO de magnitud astronómica. Si la elaboración lo fuerza a
forma normal, esto cuelga o desborda. Es la prueba de fuego. -/

theorem s3b_concreto_pequeno :
    Prf (tcFn (numeral (codeNat Formula.bottom)) =eq termCode (numeral (codeNat Formula.bottom))) :=
  prf_tc_numeral (codeNat Formula.bottom)

theorem s3b_concreto_axioma :
    Prf (tcFn (numeral (codeNat ax_tc_zero)) =eq termCode (numeral (codeNat ax_tc_zero))) :=
  prf_tc_numeral (codeNat ax_tc_zero)

/-- El peor caso medido: `log₂ N` desborda un `double`. -/
theorem s3b_peor_caso :
    Prf (tcFn (numeral (codeNat ax_tc_succ)) =eq termCode (numeral (codeNat ax_tc_succ))) :=
  prf_tc_numeral (codeNat ax_tc_succ)

/-! ## S3.c — el paso que SÍ podría forzar reducción: encadenar por congruencia -/

theorem s3c_encadenado (φ : Formula) (W : Term)
    (h : Prf (termCode (numeral (codeNat φ)) =eq W)) :
    Prf (tcFn (numeral (codeNat φ)) =eq W) :=
  prf_eq_trans (prf_tc_numeral (codeNat φ)) h

/-- Y con argumento CONCRETO, que es donde la unificación tiene más tentación de reducir. -/
theorem s3c_encadenado_concreto (W : Term)
    (h : Prf (termCode (numeral (codeNat ax_tc_succ)) =eq W)) :
    Prf (tcFn (numeral (codeNat ax_tc_succ)) =eq W) :=
  prf_eq_trans (prf_tc_numeral (codeNat ax_tc_succ)) h

#print axioms s3a_simbolico
#print axioms s3b_concreto_pequeno
#print axioms s3b_concreto_axioma
#print axioms s3b_peor_caso
#print axioms s3c_encadenado
#print axioms s3c_encadenado_concreto

/-! ## S5 — de dónde sale la profundidad: los puntos Unicode -/

def simbolos : List (String × String) :=
  [("zero", zero_sym), ("succ", succ_sym), ("add", add_sym), ("mul", mul_sym),
   ("pred", pred_sym), ("div2", div2_sym), ("mod2", mod2_sym), ("cons", cons_sym),
   ("concat", concat_sym), ("pow", pow_sym)]

partial def consDepth : Term → Nat
  | .func s args =>
      if s = cons_sym then
        match args with
        | [h, t] => 1 + max (consDepth h) (consDepth t)
        | _ => 0
      else 0
  | _ => 0

#eval simbolos.map (fun (n, s) =>
  s!"{n}=\"{s}\" puntos={s.toList.map Char.toNat} suma={s.toList.foldl (fun a c => a + c.toNat) 0}")

#eval s!"S5 — profundidad REAL de formCode: ax_tc_succ={consDepth (formCode ax_tc_succ)}, \
ax_tc_cons={consDepth (formCode ax_tc_cons)}, ax_L0_cons_def={consDepth (formCode ax_L0_cons_def)}, \
ax_tc_zero={consDepth (formCode ax_tc_zero)}"

#eval s!"S5 — suma de puntos Unicode de los 10 simbolos = \
{simbolos.foldl (fun a (_, s) => a + s.toList.foldl (fun b c => b + c.toNat) 0) 0}; \
con indices 0..9 seria {(List.range 10).foldl (·+·) 0}"
