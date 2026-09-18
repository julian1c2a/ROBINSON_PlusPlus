import Lean

/-!
# SONDEO ⬜4 de `Sugerencias.md` — ¿hay API de LINTER en Lean v4.31 SIN Mathlib?

**Respuesta: SÍ, y salta en el punto de declaración.** Medido, no supuesto.

Es lo único que sobrevive de (5b): ADR-070 mató la idea de meter M-10 en la firma, pero ⬜4 no
iba de M-10 — va de **adelantar el censo de `axiom`**, de un barrido posterior a un aviso **en el
punto de declaración**.

## ⚠️ La trampa que costó tres intentos

El linter recibe **el comando ENTERO**, que para una declaración es
`Lean.Parser.Command.declaration`; el `axiom` es un nodo **HIJO**. Comparar el kind del nodo raíz
(`stx.isOfKind ``Lean.Parser.Command.axiom`) **no casa nunca**, y el linter se queda mudo sin dar
ningún error. Hay que buscarlo con `stx.find?`.

🔑 *Un linter que no casa no falla: calla. Y un control que calla se lee como que no hay nada.*

## ⛔ El PUNTO CIEGO, medido y no supuesto

1. Un linter registrado con `initialize addLinter` **no se aplica al fichero que lo registra**:
   sus propios `axiom` posteriores pasan sin aviso. Medido.
2. Sí se aplica a los ficheros que **importan** ese módulo — `lintersRef` llega con 19 entradas
   (18 de core + ésta) y los dos `axiom` de `Uso.lean` sacan su warning. Medido.
3. ⇒ **un `axiom` en un módulo que no importe esto no lo mira nadie.**

⇒ **tienen que ser LOS DOS**: el linter como aviso TEMPRANO y `check-axioms.bash` como CENSO,
con la misma tabla y siempre **igualdad exacta**, nunca cota. Es la misma doctrina que
`check-warnings.bash` y que `[E]`/`[COBERTURA]`.

## ⬜ Lo que falta para desplegarlo (NO medido)

Dónde colgarlo para que lo importe todo el árbol: el candidato es el barril, pero eso lo hace
dependencia de todo y habría que medir qué le hace al tiempo de construcción.
-/

open Lean Elab Command

register_option linter.axiomCensus : Bool := {
  defValue := true
  descr := "avisa al declarar un `axiom`: cada uno necesita su ADR y su fila en AXIOMS.md"
}

def axiomLinter : Linter where
  name := `linter.axiomCensus
  run := fun stx => do
    -- ⚠️ `stx` es el comando ENTERO (`…Command.declaration`); el `axiom` es un HIJO.
    match stx.find? (·.isOfKind ``Lean.Parser.Command.axiom) with
    | some ax => logWarningAt ax "axiom declarado -- necesita ADR y fila en AXIOMS.md"
    | none => pure ()

initialize addLinter axiomLinter
