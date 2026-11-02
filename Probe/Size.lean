import ROBINSON_PlusPlus.Meta
open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel

partial def tsize : Term → Nat
  | .var _ => 1
  | .func _ args => 1 + args.foldl (fun a t => a + tsize t) 0

/-- Todos los símbolos que aparecen en un término / fórmula, CON multiplicidad. -/
partial def symsT : Term → List String
  | .var _ => []
  | .func s args => s :: args.foldl (fun a t => a ++ symsT t) []
partial def symsF : Formula → List String
  | .bottom => []
  | .atom p ts => p :: ts.foldl (fun a t => a ++ symsT t) []
  | .eq t u => symsT t ++ symsT u
  | .impl a b => symsF a ++ symsF b
  | .and a b => symsF a ++ symsF b
  | .or a b => symsF a ++ symsF b
  | Formula.forall a => symsF a
  | .ex a => symsF a

/-- Índice de tabla: posición en la lista de símbolos distintos. -/
def tabla : List String :=
  [zero_sym, succ_sym, add_sym, mul_sym, pred_sym, div2_sym, mod2_sym, cons_sym,
   concat_sym, pow_sym, sqrt_sym, sub_sym, lt_sym,
   "::", "carc", "cdrc", "lenc", "nthc", "liftc", "liftfc", "liftsc",
   "substfc", "substtc", "substtsc", "tcFn", "runFn", "premsOf", "validProofFn", "axiomsCodeT"]
def idxOf (s : String) : Nat := (tabla.findIdx? (· == s)).getD 99

partial def report (nombre : String) (f : Formula) : String :=
  let ss := symsF f
  let costeUnicode := ss.foldl (fun a s => a + tsize (strCodeM s)) 0
  let costeIdx     := ss.foldl (fun a s => a + (idxOf s + 2)) 0
  let total := tsize (formCode f)
  s!"{nombre}: total={total} nodos | simbolos={ss.length} ocurrencias | \
coste simbolos: Unicode={costeUnicode} ({100*costeUnicode/total}%) -> indices={costeIdx} | \
formCode quedaria en ~{total - costeUnicode + costeIdx} nodos"

#eval report "ax_tc_zero     " ax_tc_zero
#eval report "ax_L0_cons_def " ax_L0_cons_def
#eval report "ax4_add_zero   " ax4_add_zero
