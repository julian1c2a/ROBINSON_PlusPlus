-- ══════════════════════════════════════════════════════════════════════════
-- SONDEO DE VIABILIDAD de la migración `String → S` (paso 4).
-- ⚠️ SIN `import FOL`: se reconstruye el núcleo mínimo para medir qué sobrevive.
-- ══════════════════════════════════════════════════════════════════════════

namespace ProbeSymA

-- ── VARIANTE A: parámetro GENUINO en el inductivo ──────────────────────────
inductive Term (S : Type) where
  | var  : Nat → Term S
  | func : S → List (Term S) → Term S
  deriving Repr, BEq

inductive Formula (S : Type) where
  | bottom : Formula S
  | atom   : S → List (Term S) → Formula S
  | eq     : Term S → Term S → Formula S
  | impl   : Formula S → Formula S → Formula S
  | forall : Formula S → Formula S
  | and    : Formula S → Formula S → Formula S
  | or     : Formula S → Formula S → Formula S
  | ex     : Formula S → Formula S
  deriving Repr, BEq

-- ¿sobrevive una función mutua anidada como `liftTerm`/`liftTerms`?
mutual
def liftTerm {S : Type} (c : Nat) : Term S → Term S
  | .var n => if n < c then .var n else .var (n + 1)
  | .func f ts => .func f (liftTerms c ts)
def liftTerms {S : Type} (c : Nat) : List (Term S) → List (Term S)
  | [] => []
  | t :: ts => liftTerm c t :: liftTerms c ts
end

def liftFormula {S : Type} (c : Nat) : Formula S → Formula S
  | .bottom => .bottom
  | .atom p ts => .atom p (liftTerms c ts)
  | .eq t u => .eq (liftTerm c t) (liftTerm c u)
  | .impl a b => .impl (liftFormula c a) (liftFormula c b)
  | .forall a => .forall (liftFormula (c + 1) a)
  | .and a b => .and (liftFormula c a) (liftFormula c b)
  | .or a b => .or (liftFormula c a) (liftFormula c b)
  | .ex a => .ex (liftFormula (c + 1) a)

-- ¿y un predicado que COMPARA símbolos, como `occursTerm`?
mutual
def occursTerm {S : Type} (c : S) : Term S → Prop
  | .var _ => False
  | .func s ts => Or (s = c) (occursTerms c ts)
def occursTerms {S : Type} (c : S) : List (Term S) → Prop
  | [] => False
  | t :: ts => Or (occursTerm c t) (occursTerms c ts)
end

-- ¿y uno que DECIDE la igualdad de símbolos (el `if f = c` de `updateFunc`)?
noncomputable def updateFuncLike {S D : Type} [DecidableEq S]
    (g : S → List D → D) (c : S) (F : List D → D) : S → List D → D :=
  fun f ds => if f = c then F ds else g f ds

-- las instancias de HOY, por `abbrev`
abbrev TermC := Term (List Char)
abbrev FormulaC := Formula (List Char)

example : TermC := Term.func ['f'] [Term.var 0]

end ProbeSymA

-- ══════════════════════════════════════════════════════════════════════════
namespace ProbeSymB
-- ── VARIANTE B: un `abbrev` en la raíz, el inductivo SIN parámetro ─────────
-- ⭐ Todos los módulos siguen diciendo `Term`/`Formula` sin tocar nada; sólo cambian las
--   líneas que hoy dicen `String`. Y cambiar de tipo de símbolos es UNA línea.
abbrev Sym : Type := List Char

inductive Term where
  | var  : Nat → Term
  | func : Sym → List Term → Term
  deriving Repr, BEq

inductive Formula where
  | bottom : Formula
  | atom   : Sym → List Term → Formula
  | eq     : Term → Term → Formula
  | impl   : Formula → Formula → Formula
  | forall : Formula → Formula
  | and    : Formula → Formula → Formula
  | or     : Formula → Formula → Formula
  | ex     : Formula → Formula
  deriving Repr, BEq

mutual
def liftTerm (c : Nat) : Term → Term
  | .var n => if n < c then .var n else .var (n + 1)
  | .func f ts => .func f (liftTerms c ts)
def liftTerms (c : Nat) : List Term → List Term
  | [] => []
  | t :: ts => liftTerm c t :: liftTerms c ts
end

/-- ⭐ LA PRUEBA QUE DECIDE: ¿desaparece el `Classical.choice`?
Hoy `strCode s := charsCode s.toList` lo trae porque DESCOMPONE un `String`.
Con `Sym = List Char` no hay nada que descomponer. -/
def symCode : Sym → Nat
  | [] => 0
  | c :: cs => c.toNat + symCode cs

example : Term := Term.func ['f'] [Term.var 0]

end ProbeSymB

#print axioms ProbeSymA.liftFormula
#print axioms ProbeSymA.occursTerm
#print axioms ProbeSymA.updateFuncLike
#print axioms ProbeSymB.liftTerm
#print axioms ProbeSymB.symCode
