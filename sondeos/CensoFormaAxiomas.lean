/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus

/-!
# SONDEO · la FORMA LÓGICA de los 120 axiomas de `axioms`, sin reducir ningún numeral

**Fecha:** 2026‑11‑02 · **Por qué:** T69 de `doc/AUDITORIA-SUELO-2026-10-12.md` (Gentzen: primeros pasos medibles).
Un análisis ordinal de `T_Prf` tiene que tratar TODOS sus axiomas, y nadie había medido su forma: se sabía de oídas
que `ax13_lt_def` lleva un `∃` y los `ax_lineWF_*` guardas Σ₁, nada más. Gentzen ya no vive en RPP (ADR‑140): esto es
la medida para cuando empiece.

**Qué mide:** para cada axioma de `axiomsBase` (`coreAxioms ++ codingAxioms`, en su orden) y para el ancla
(`ax_axiomsCodeT_def`, el último de `axioms`), su clase SINTÁCTICA en la jerarquía aritmética —el Σₙ y el Πₙ mínimos,
contando los átomos (`lt`, `In`, `allIn`, `lineWF`, `chainOk`…) y las ecuaciones como Δ₀— y cuántos `∀` y `∃` tiene.
La clase se calcula sobre la fórmula tal cual (sin prenexar): `A ⇒ B` como `¬A ∨ B`, `∀` sube a Πₙ y `∃` a Σₙ.
⚠️ Es la forma del ENUNCIADO, no la de su interpretación: `lineWF` es un átomo con sus axiomas de definición
(`ax_lineWF_*`, bicondicionales), y su complejidad semántica no cuenta aquí.

**Cómo:** recorre el término de cada axioma en `MetaM`, con `whnfD` sólo en la CABEZA de cada subfórmula (despliega
`forall_2`, `iff`, `hasWitF`, `land`… hasta un constructor de `FormulaG`) y sin entrar nunca en un argumento de tipo
`Term`: ningún numeral se reduce, tampoco el `nD` del ancla. No evalúa nada (ni `#eval` ni `#reduce`): una orden
propia, `#censo_forma`. Tarda ≈ 5 s (`lake lean sondeos/CensoFormaAxiomas.lean`).

**Resultado de la ejecución del 2026‑11‑02** (build de ese día; la salida entera, en
`doc/registro/2026-11-02-t69/censo.txt`; lo que significa para Gentzen, en `doc/GENTZEN-ALCANCE.md` §1):
* `axiomsBase` = 34 de la teoría + 85 de codificación = 119; con el ancla, 120.
* **112 de los 120 son Π₁ o Δ₀** (31 + 2 de la teoría, 76 + 2 de codificación, y el ancla, una ecuación: Δ₀).
* **8 son Π₂**: `ax13_lt_def` (`∀n m (n < m ⇔ ∃k n + σk = m)`, un `∃` SIN acotar) y los siete `ax_lineWF_*` que llevan
  la guarda de testigo (`q1`, `q2`, `q3`, `leibniz`, `ind`, `qconf`, `listInd`): su `hasWitF` es `∃∃` de un cuerpo con
  `∀` acotados (`∀i (i < lenc w ⇒ …)`), Σ₁, dentro de un bicondicional y bajo un `∀`. Contando también los acotados
  como cuantificadores, esos siete serían Π₃.
* Ningún otro axioma lleva un `∃`. Los esquemas (`ind`, `listInd`, `qconf`, `p3`) no son axiomas de `axioms`: son
  constructores de `Prf`, para TODA fórmula.
-/

open Lean Meta Elab Command

namespace CensoFormaAxiomas

/-- Los elementos de un literal de lista, sin reducir nada más que la cabeza de cada cola. -/
partial def elementos (e : Expr) : MetaM (Array Expr) := do
  let e ← whnfR e
  match e.getAppFnArgs with
  | (``List.cons, #[_, a, t]) => return #[a] ++ (← elementos t)
  | (``List.nil, _) => return #[]
  | _ => throwError "no es un literal de lista: {e}"

/-- La clase de una fórmula: los niveles mínimos Σ y Π, cuántos `∀` y `∃` tiene, y cuántos de ellos son ACOTADOS. -/
structure Clase where
  s : Nat
  p : Nat
  nA : Nat
  nE : Nat
  nAcot : Nat
  deriving Inhabited

/-- Σₙ ⊆ Πₙ₊₁ y Πₙ ⊆ Σₙ₊₁. -/
def ajusta (s p : Nat) : Nat × Nat := (min s (p + 1), min p (s + 1))

/-- ¿Es `t` un término sin la variable 0 libre, a la vista y SIN reducirlo? Sí si es `liftTerm 0 _` (el lift deja libre
    el índice 0) o si no lleva ningún `TermG.var`. Si no se puede ver, no (el lado seguro: la cota no cuenta). -/
def sinVar0 (t : Expr) : MetaM Bool := do
  match t.getAppFnArgs with
  | (n, #[_, k, _]) =>   -- `liftTerm {Sym} c t`
      if n.componentsRev.head!.toString == "liftTerm" then
        return (← Meta.evalNat k) == some 0
      else return (t.find? fun x => x.isAppOf ``TermG.var).isNone
  | _ => return (t.find? fun x => x.isAppOf ``TermG.var).isNone

/-- ¿Es `g` la guarda `x₀ < t` de un cuantificador acotado (el átomo `lt` con la variable 0 y un `t` sin ella)? -/
def esGuarda (g : Expr) : MetaM Bool := do
  match (← whnfD g).getAppFnArgs with
  | (``FormulaG.atom, #[_, sym, args]) =>
      unless sym.isConst && sym.constName!.componentsRev.head!.toString == "lt_sym" do return false
      let xs ← elementos args
      unless xs.size == 2 do return false
      match xs[0]!.getAppFnArgs with
      | (``TermG.var, #[_, k]) => return (← Meta.evalNat k) == some 0 && (← sinVar0 xs[1]!)
      | _ => return false
  | _ => return false

/-- La clase. Con `acotado`, `∀x (x < t ⇒ φ)` y `∃x (x < t ∧ φ)` (con `t` sin `x`) no suben el nivel: cuentan como
    Δ₀, como en la jerarquía de Lévy. Sin él, todo cuantificador cuenta. -/
partial def clasifica (acotado : Bool) (e : Expr) : MetaM Clase := do
  let e ← whnfD e
  match e.getAppFnArgs with
  | (``FormulaG.bottom, _) | (``FormulaG.atom, _) | (``FormulaG.eq, _) => return ⟨0, 0, 0, 0, 0⟩
  | (``FormulaG.impl, #[_, a, b]) => do
      let ca ← clasifica acotado a; let cb ← clasifica acotado b
      let (s, p) := ajusta (max ca.p cb.s) (max ca.s cb.p)
      return ⟨s, p, ca.nA + cb.nA, ca.nE + cb.nE, ca.nAcot + cb.nAcot⟩
  | (``FormulaG.and, #[_, a, b]) | (``FormulaG.or, #[_, a, b]) => do
      let ca ← clasifica acotado a; let cb ← clasifica acotado b
      let (s, p) := ajusta (max ca.s cb.s) (max ca.p cb.p)
      return ⟨s, p, ca.nA + cb.nA, ca.nE + cb.nE, ca.nAcot + cb.nAcot⟩
  | (``FormulaG.forall, #[_, a]) => do
      let ca ← clasifica acotado a
      let acot ← if acotado then
          match (← whnfD a).getAppFnArgs with
          | (``FormulaG.impl, #[_, g, _]) => esGuarda g
          | _ => pure false
        else pure false
      if acot then return { ca with nA := ca.nA + 1, nAcot := ca.nAcot + 1 }
      let p := max 1 ca.p
      let (s', p') := ajusta (p + 1) p
      return ⟨s', p', ca.nA + 1, ca.nE, ca.nAcot⟩
  | (``FormulaG.ex, #[_, a]) => do
      let ca ← clasifica acotado a
      let acot ← if acotado then
          match (← whnfD a).getAppFnArgs with
          | (``FormulaG.and, #[_, g, _]) => esGuarda g
          | _ => pure false
        else pure false
      if acot then return { ca with nE := ca.nE + 1, nAcot := ca.nAcot + 1 }
      let s := max 1 ca.s
      let (s', p') := ajusta s (s + 1)
      return ⟨s', p', ca.nA, ca.nE + 1, ca.nAcot⟩
  | _ => throwError "cabeza inesperada (no es un constructor de FormulaG): {e.getAppFn}"

def sub (n : Nat) : String :=
  String.ofList ((toString n).toList.map fun c => Char.ofNat (c.toNat - '0'.toNat + 0x2080))

def etiqueta (c : Clase) : String :=
  if c.s == 0 && c.p == 0 then "Δ₀"
  else if c.p < c.s then s!"Π{sub c.p}"
  else if c.s < c.p then s!"Σ{sub c.s}"
  else s!"Σ{sub c.s}∩Π{sub c.p}"

/-- `#censo_forma`: la tabla de los 120 axiomas y el recuento por clase. -/
elab "#censo_forma" : command => liftTermElabM do
  let env ← getEnv
  let valor (n : Name) : MetaM Expr := do
    match env.find? n with
    | some ci => match ci.value? with
      | some v => return v
      | none => throwError "{n} no tiene valor"
    | none => throwError "{n} no existe"
  -- `axiomsBase` es `coreAxioms ++ codingAxioms`: se comprueba la forma, no se supone
  let base ← valor ``ROBINSON_PlusPlus.Minimal.Axioms.axiomsBase
  match base.getAppFnArgs with
  | (``HAppend.hAppend, #[_, _, _, _, .const a _, .const b _]) =>
      unless a == ``ROBINSON_PlusPlus.Minimal.Axioms.coreAxioms && b == ``ROBINSON_PlusPlus.Minimal.Axioms.codingAxioms do
        throwError "axiomsBase ya no es coreAxioms ++ codingAxioms: {base}"
  | _ => throwError "axiomsBase ya no es coreAxioms ++ codingAxioms: {base}"
  let core ← elementos (← valor ``ROBINSON_PlusPlus.Minimal.Axioms.coreAxioms)
  let coding ← elementos (← valor ``ROBINSON_PlusPlus.Minimal.Axioms.codingAxioms)
  let filas : Array (String × Expr) :=
    (core.map fun e => ("teoría", e)) ++ (coding.map fun e => ("codificación", e)) ++
      #[("ancla", .const ``ROBINSON_PlusPlus.Minimal.Axioms.ax_axiomsCodeT_def [])]
  let mut out := s!"axiomsBase: {core.size} de la teoría + {coding.size} de codificación = {core.size + coding.size}; con el ancla, {filas.size}\n"
  out := out ++ "n\tgrupo\taxioma\tclase (todo cuantificador cuenta)\tclase (los acotados, Δ₀)\t∀\t∃\tacotados\n"
  let mut cuenta : Std.HashMap String Nat := {}
  let mut cuentaAc : Std.HashMap String Nat := {}
  let mut conE : Array String := #[]
  let mut i := 0
  for (g, e) in filas do
    i := i + 1
    let nombre := match e with
      | .const n _ => n.componentsRev.head!.toString
      | _ => toString e
    let v ← match e with
      | .const n _ => valor n
      | _ => pure e
    let c ← clasifica false v
    let ca ← clasifica true v
    let et := etiqueta c
    let eta := etiqueta ca
    cuenta := cuenta.insert s!"{g} · {et}" (cuenta.getD s!"{g} · {et}" 0 + 1)
    cuentaAc := cuentaAc.insert s!"{g} · {eta}" (cuentaAc.getD s!"{g} · {eta}" 0 + 1)
    if c.nE > 0 then conE := conE.push nombre
    out := out ++ s!"{i}\t{g}\t{nombre}\t{et}\t{eta}\t{c.nA}\t{c.nE}\t{ca.nAcot}\n"
  out := out ++ "\nrecuento por grupo y clase (todo cuantificador cuenta):\n"
  for (k, v) in cuenta.toArray.qsort (fun a b => a.1 < b.1) do
    out := out ++ s!"  {k}: {v}\n"
  out := out ++ "\nrecuento por grupo y clase (los acotados, Δ₀):\n"
  for (k, v) in cuentaAc.toArray.qsort (fun a b => a.1 < b.1) do
    out := out ++ s!"  {k}: {v}\n"
  out := out ++ s!"\ncon algún ∃ ({conE.size}): {", ".intercalate conE.toList}\n"
  logInfo out

end CensoFormaAxiomas

#censo_forma
