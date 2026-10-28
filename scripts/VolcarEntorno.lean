/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus
import FOL
import TheoryFramework.Instances.FOL
-- ✏️ 2026-10-28 (T58, ADR-217): y la de los modelos, con `Semantics` y `Conservativity` (sin ella, `[B]` daba por
-- muertas las citas de sus declaraciones).
import TheoryFramework.Instances.FOLModels

/-! `scripts/VolcarEntorno.lean` — el entorno de Lean de RPP, para `[B]` de `check-doc-sync.bash` (T04, ADR‑166).

Escribe en el fichero de la variable `VOLCADO` (sin ella, en la salida estándar), una por línea, cada constante no
interna del entorno de RPP y de FOL entero —RPP importa sólo una parte de FOL, y los documentos citan también lo
demás— (con «P» si su módulo es del proyecto, RPP, FOL o TheoryFramework, y «L» si no), cada opción registrada (con
«O»), cada módulo importado (con «M») y cada orden, un token del analizador que empieza por «#» (con «T»). Con eso
`[B]` sabe qué cita de un documento nombra algo que existe: una constante de Lean (`Nat.succ`), un constructor o un
campo del proyecto (`listInd`), un espacio de nombres (`FOL.Metamath.Semantics`), una opción (`autoImplicit`), un
módulo de Lean (`Init.Classical`) o una orden (`#pureza_titulares`). No está en el build: necesita el build hecho, y
lo llama `check-doc-sync.bash` con `lake env lean`. -/

open Lean Elab Command

elab "#volcar_entorno" : command => do
  let env ← getEnv
  -- a un FICHERO, el de la variable VOLCADO: en Windows, la salida estándar de Lean tarda más de dos minutos con
  -- 130 000 líneas, y el fichero, siete segundos (medido el 2026-10-18)
  let mut out : Array String := #[]
  let proyecto (n : Name) : Bool :=
    let m := match env.getModuleIdxFor? n with
      | some i => (env.header.moduleNames[i.toNat]?).getD Name.anonymous
      | none => Name.anonymous
    (`ROBINSON_PlusPlus).isPrefixOf m || (`FOL).isPrefixOf m || (`TheoryFramework).isPrefixOf m
  -- los ALIAS del proyecto: con `abbrev Formula := FormulaG (List Char)`, Lean resuelve `Formula.atom` como
  -- `FormulaG.atom`, y los documentos lo citan así. Van con un tercer campo, «A»: valen enteros, pero sus componentes
  -- no absuelven nombres sueltos (un `abbrev N := Nat` no revive `add_comm`; ADR‑167)
  let mut alias : NameMap (Array Name) := {}
  for (n, ci) in env.constants.toList do
    if let .defnInfo d := ci then
      if proyecto n then
        if let .reducible ← getReducibilityStatus n then
          let mut v := d.value
          while v.isLambda do v := v.bindingBody!
          if let .const h _ := v.getAppFn then
            if let some (.inductInfo _) := env.find? h then
              alias := alias.insert h (((alias.find? h).getD #[]).push n)
  for (n, _) in env.constants.toList do
    unless n.isInternal do
      out := out.push s!"{n}\t{if proyecto n then "P" else "L"}"
      let mut p := n.getPrefix
      while !p.isAnonymous do
        for a in (alias.find? p).getD #[] do
          out := out.push s!"{n.replacePrefix p a}\tP\tA"
        p := p.getPrefix
  for (n, _) in (← getOptionDecls).toList do
    out := out.push s!"{n}\tO"
  -- y los módulos importados (`Init.Classical`): se citan y no son constantes
  for m in env.header.moduleNames do
    out := out.push s!"{m}\tM"
  -- y las ÓRDENES (`#print`, `#pureza_titulares`, `#contrato_generar`): los tokens del analizador que empiezan por «#»
  for t in Lean.Data.Trie.values (Lean.Parser.getTokenTable env) do
    if t.startsWith "#" then
      out := out.push s!"{t}\tT"
  let texto := "\n".intercalate out.toList ++ "\n"
  match (← IO.getEnv "VOLCADO") with
  | some ruta => IO.FS.writeFile ruta texto
  | none => IO.print texto

#volcar_entorno
