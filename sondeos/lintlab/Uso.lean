import AxLinter

/-!
# El consumidor del sondeo ⬜4 — la EVIDENCIA de que el linter salta

Se compila fuera del `lakefile` (`sondeos/` no entra en el build), con
`lake env lean -o sondeos/lintlab/AxLinter.olean sondeos/lintlab/AxLinter.lean` y luego
`LEAN_PATH=…/lintlab lake env lean sondeos/lintlab/Uso.lean`.

**Salida medida el 2026-09-18:**

    linters: 19 — … linter.axiomCensus
    Uso.lean:29:0: warning: axiom declarado -- necesita ADR y fila en AXIOMS.md
    Uso.lean:31:0: warning: axiom declarado -- necesita ADR y fila en AXIOMS.md

⭐ **Dos warnings, en las dos líneas `axiom`, y NINGUNO** en el `def` ni en el `theorem`: el
linter no grita lobo.
-/

open Lean Elab Command

-- control: ¿llegó el linter al fichero que importa?
#eval show CommandElabM Unit from do
  let ls ← lintersRef.get
  logInfo s!"linters: {ls.size} — incluye axiomCensus: {ls.any (·.name == `linter.axiomCensus)}"

-- ── los cuatro casos ──────────────────────────────────────────────────────
def zz : Nat := 1                    -- no debe avisar
axiom probe_ax_importado : True      -- ⬅ DEBE avisar
theorem tt : True := trivial         -- no debe avisar
axiom probe_ax_dos : Nat             -- ⬅ DEBE avisar
