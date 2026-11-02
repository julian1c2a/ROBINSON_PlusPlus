import ROBINSON_PlusPlus.Meta.CodeWitnessPrf

/-!
# `Probe/T2_e1.lean` — ¿puede BAJAR `prf_isTermCodeE1_of_boundedIn` a `CodeWitnessPrf.SinWTs`?

## ⚠️ LINEAS RE-MEDIDAS HOY (2026-09-03 20:55/20:59)

Los ficheros de produccion cambiaron mientras se medía. Las lineas del encargo estaban
DESPLAZADAS. Las de verdad, ahora:

| simbolo                                     | linea del encargo | linea REAL |
|---------------------------------------------|-------------------|------------|
| `SinWTs.prf_crit_In_rejects_open1`           | 1112              | **1163**   |
| su consumidor `SinWTs.crit_isTC1_junk_refuted_open` | 1136/1141  | **1187/1192** |
| `ENS.prf_isFormCodeE2_of_boundedIn`          | 1578              | **1629**   |
| `ENS.prf_isFormCodeE2_of_In`                 | 1602              | **1655**   |
| `SinWTs.impT` / `ENS.impT`                   | 105 / 1332        | **105 / 1383** |
| `EvalLiftcPrf.prf_isTermCodeE1_of_boundedIn` | 329               | **304**    |
| `EvalLiftcPrf.prf_isTermCodeE1_of_In`        | 359               | **334**    |

## ⚠️ Y HAY UN PRECEDENTE EJECUTADO HOY, EN ESTE MISMO PAR DE FICHEROS

`prf_argsIn_head` / `prf_argsIn_tail` **ya se bajaron** de `EvalLiftcPrf` a
`CodeWitnessPrf.SinWTs` (:680 y :692), con la justificacion escrita en `:673-679` y la nota
correspondiente en `EvalLiftcPrf.lean:291-298`. Es exactamente la misma operacion que se
pregunta aqui, sobre el mismo modulo y con la misma razon (lema generico, seis sondeos lo
copian a mano). No es una analogia: es el mismo movimiento, ya hecho y ya verde.

## Regla del experimento

* Se importa **SOLO** `Meta.CodeWitnessPrf` (y con el sus 36 `import`).
  **NO** `Meta.EvalLiftcPrf`, **NO** `Meta.LiftcCodePrf`, **NO** el barrel `ROBINSON_PlusPlus.Meta`.
* Las declaraciones van LITERALMENTE dentro de
  `namespace ROBINSON_PlusPlus.Meta.CodeWitnessPrf` + `namespace SinWTs`, con los MISMOS
  `open` de la seccion `S_Clausura` (`CodeWitnessPrf.lean:84-95`). La resolucion de nombres
  es por tanto la que habria en el sitio real.
* §4 MIDE (no supone) la linea de declaracion de cada constante de `CodeWitnessPrf` que usan
  las pruebas: si alguna fuese `> 1163`, el lema NO podria bajar a ese punto.

## Los enunciados son los de produccion, byte a byte

`Meta/EvalLiftcPrf.lean:304-305` y `:334-335`. `EvalLiftcPrf` abre `SinWTs` (`:156`), asi que
`isTermCodeE1`, `wfAll1`, `In` de aquellos enunciados SON estas constantes de `SinWTs`, y
`boundedIn` es el de `BoundedInPrf` en los dos casos. No hay nada que traducir.
-/

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.BoundedInPrf ROBINSON_PlusPlus.Meta.BdAllIntroPrf
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.TrackedCorePrf
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf ROBINSON_PlusPlus.Meta.Sigma1CorePrf
open ROBINSON_PlusPlus.Meta.EvalListPrf ROBINSON_PlusPlus.Meta.EvalNthcPrf
open ROBINSON_PlusPlus.Meta.EvalLtPrf ROBINSON_PlusPlus.Meta.EvalBoundedPrf
open ROBINSON_PlusPlus.Meta.EvalArithPrf ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
open ROBINSON_PlusPlus.Meta.InAxiomsCodePrf ROBINSON_PlusPlus.Meta.Delta0ReflectPrf
open ROBINSON_PlusPlus.Meta.DerivCondPrf ROBINSON_PlusPlus.Meta.D3InDotPrf
open ROBINSON_PlusPlus.Meta.ChainPrf ROBINSON_PlusPlus.Meta.MpCodePrf

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace ROBINSON_PlusPlus.Meta.CodeWitnessPrf

namespace SinWTs

/-! ## §1 · LOS DOS LEMAS GENERALES, RE-DEMOSTRADOS *DENTRO* DE `SinWTs`

    Copia literal de `Meta/EvalLiftcPrf.lean:304-327` y `:334-337`, con **UN SOLO cambio**:
    el `impT` deja de estar cualificado (aqui no hace falta; ver §3). -/

theorem prf_isTermCodeE1_of_boundedIn' (w c : Term) :
    Prf (Formula.impl (boundedIn c w) (Formula.impl (wfAll1 w) (isTermCodeE1 w c))) := by
  refine prf_ex_elim_imp ?_
  rw [liftFormula, liftF_wfAll1, liftF_isTermCodeE1]
  refine deduction_aux ?_ (wfAll1 (liftTerm 0 w)) _ rfl
  have hwf : PrfH [wfAll1 (liftTerm 0 w),
      land (lt (.var 0) (liftTerm 0 (lenc w)))
        (Formula.eq (nthc (liftTerm 0 w) (.var 0)) (liftTerm 0 c))]
      (wfAll1 (liftTerm 0 w)) := PrfH.hyp _ _ (List.Mem.head _)
  have hbody : PrfH [wfAll1 (liftTerm 0 w),
      land (lt (.var 0) (liftTerm 0 (lenc w)))
        (Formula.eq (nthc (liftTerm 0 w) (.var 0)) (liftTerm 0 c))]
      (land (lt (.var 0) (liftTerm 0 (lenc w)))
        (Formula.eq (nthc (liftTerm 0 w) (.var 0)) (liftTerm 0 c))) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hlt : PrfH [wfAll1 (liftTerm 0 w),
      land (lt (.var 0) (liftTerm 0 (lenc w)))
        (Formula.eq (nthc (liftTerm 0 w) (.var 0)) (liftTerm 0 c))]
      (lt (.var 0) (lenc (liftTerm 0 w))) := by
    have h := PrfH_and_elim_left hbody
    simpa only [lenc, liftTerm, liftTerms] using h
  have heq := PrfH_and_elim_right hbody
  have hitc := PrfH.mp _ _ _ (PrfH_inst_wfAll1 (liftTerm 0 w) (.var 0) hwf) hlt
  exact PrfH_congr_isTermCodeE1 heq hitc

/-- ⚠️ `impT` **SIN CUALIFICAR**, a proposito: aqui dentro *tiene* que resolver a
    `SinWTs.impT`. Medido en §3. -/
theorem prf_isTermCodeE1_of_In' (w c : Term) :
    Prf (Formula.impl (In c w) (Formula.impl (wfAll1 w) (isTermCodeE1 w c))) :=
  impT (prf_boundedIn_of_In c w) (prf_isTermCodeE1_of_boundedIn' w c)

/-! ## §2 · EL COROLARIO QUE RECUPERA `prf_crit_In_rejects_open1` (`CodeWitnessPrf.lean:1163`)

    ⚠️ La FIRMA se conserva **exacta**, `hcl` incluida, aunque por esta via `hcl` **sobra**:
    el lema general no la necesita (su conclusion es `isTermCodeE1 w c`, cuyo `liftFormula`
    se atraviesa con `liftF_isTermCodeE1`) y `crit_isTermCodeE1_rejects` (`:369`) tampoco.
    En la prueba ORIGINAL `hcl` si hacia falta, porque alli la conclusion es `⊥` y habia que
    volver de `liftTerm 0 c` a `c` a mano (`:1179`, `rwa [hcl 0]`).

    Conservar `hcl` en la firma es lo que hace que el consumidor de `:1192` siga tipando
    **sin tocarlo** (§3). El `linter.unusedVariables` ya esta apagado en esa seccion
    (`CodeWitnessPrf.lean:97`), asi que el parametro muerto no da aviso. -/

theorem prf_crit_In_rejects_open1' (w c : Term) (k : Nat) (hk0 : k ≠ 0) (hk1 : k ≠ 1)
    (hcl : ∀ n : Nat, liftTerm n c = c) (hck : Prf (carc c =eq numeralM k)) :
    Prf (Formula.impl (boundedIn c w) (Formula.impl (wfAll1 w) Formula.bottom)) := by
  refine prf_deduction (deduction_aux ?_ (wfAll1 w) [boundedIn c w] rfl)
  show PrfH [wfAll1 w, boundedIn c w] Formula.bottom
  have hwf : PrfH [wfAll1 w, boundedIn c w] (wfAll1 w) := PrfH.hyp _ _ (List.Mem.head _)
  have hbd : PrfH [wfAll1 w, boundedIn c w] (boundedIn c w) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hitc : PrfH [wfAll1 w, boundedIn c w] (isTermCodeE1 w c) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _
      (prf_to_prfH (prf_isTermCodeE1_of_boundedIn' w c) _) hbd) hwf
  exact PrfH.mp _ _ _
    (prf_to_prfH (crit_isTermCodeE1_rejects w c k hk0 hk1 hck) _) hitc

/-! ## §3 · EL CONSUMIDOR DE `:1192` SIGUE TIPANDO CON EL COROLARIO

    Copia literal de `crit_isTC1_junk_refuted_open` (`:1187-1193`) cambiando SOLO
    `prf_crit_In_rejects_open1` por el corolario. `impT` sigue sin cualificar. -/

theorem crit_isTC1_junk_refuted_open' (w c : Term)
    (hcl : ∀ n : Nat, liftTerm n c = c)
    (k : Nat) (hk0 : k ≠ 0) (hk1 : k ≠ 1) (hck : Prf (carc c =eq numeralM k))
    (hjunk : Prf (isTC1 w c)) : Prf Formula.bottom :=
  prf_mp (prf_mp (impT (prf_boundedIn_of_In c w)
      (prf_crit_In_rejects_open1' w c k hk0 hk1 hcl hck))
    (prf_and_elim_right hjunk)) (prf_and_elim_left hjunk)

/-- Control de que el consumidor nuevo NO se ha debilitado: reproduce
    `crit_junk_SubCodesCritica_open1` (`:1202-1207`) con la misma llamada. -/
example (w : Term)
    (hjunk : Prf (isTC1 w (implc (termCodeM (.var 0)) (termCodeM (.var 0))))) :
    Prf Formula.bottom :=
  crit_isTC1_junk_refuted_open' w _
    (crit_closed_implc (closed_termCodeM _) (closed_termCodeM _)).1
    5 (by decide) (by decide) (prf_carc_cons _ _) hjunk

/-- Y el corolario es INTERCAMBIABLE con el de produccion en los dos sentidos: mismos
    enunciados, misma firma. -/
example : (∀ (w c : Term) (k : Nat), k ≠ 0 → k ≠ 1 → (∀ n : Nat, liftTerm n c = c) →
      Prf (carc c =eq numeralM k) →
      Prf (Formula.impl (boundedIn c w) (Formula.impl (wfAll1 w) Formula.bottom)))
    = (∀ (w c : Term) (k : Nat), k ≠ 0 → k ≠ 1 → (∀ n : Nat, liftTerm n c = c) →
      Prf (carc c =eq numeralM k) →
      Prf (Formula.impl (boundedIn c w) (Formula.impl (wfAll1 w) Formula.bottom))) := rfl

example : @prf_crit_In_rejects_open1' = @prf_crit_In_rejects_open1' := rfl
example (w c : Term) (k : Nat) (h0 : k ≠ 0) (h1 : k ≠ 1)
    (hcl : ∀ n : Nat, liftTerm n c = c) (hck : Prf (carc c =eq numeralM k)) :
    Prf (Formula.impl (boundedIn c w) (Formula.impl (wfAll1 w) Formula.bottom)) :=
  prf_crit_In_rejects_open1 w c k h0 h1 hcl hck

/-- ⚠️ CONTROL DEL `impT` AMBIGUO — la mitad `SinWTs`. Dentro de `namespace SinWTs` el
    `impT` bare de §1/§3 resuelve a `SinWTs.impT` (`:105`), NO a `ENS.impT` (`:1383`). -/
example {A B C : Formula} (h1 : Prf (A ⇒ B)) (h2 : Prf (B ⇒ C)) :
    impT h1 h2 = SinWTs.impT h1 h2 := rfl

end SinWTs

/-! ## §3b · CONTROL DEL `impT` AMBIGUO — la otra mitad

    En `namespace ENS` el mismo `impT` bare cambia de constante. Por eso el veredicto dice
    `SinWTs` y no `ENS`. (En el fichero real `ENS` ademas hace `open SinWTs` en `:1412`, con
    lo que ahi el bare seria directamente AMBIGUO; aqui se reproduce sin ese `open` para
    aislar la resolucion por namespace.) -/

namespace ENS

example {A B C : Formula} (h1 : Prf (A ⇒ B)) (h2 : Prf (B ⇒ C)) :
    impT h1 h2 = ENS.impT h1 h2 := rfl

end ENS

end ROBINSON_PlusPlus.Meta.CodeWitnessPrf

/-! ## §4 · LA MEDIDA: linea de declaracion de cada dependencia en `CodeWitnessPrf`

    ⚠️ **ANDAMIO, no entregable.** Lean 4.31 elabora los cuerpos de `theorem` de forma
    ASINCRONA y no los expone en el entorno del propio fichero (`hasValue = false`), asi que
    un `#deps` sobre los `theorem` de §1 mediria 0 y haria `PANIC`. Los `def` SI exponen su
    cuerpo. Estas cuatro copias `MED_*` llevan el **mismo texto de prueba** que §1-§3 y solo
    existen para poder medir. El control de abajo comprueba que habitan el enunciado exacto.

    Si alguna linea saliera `> 1163`, el lema NO podria bajar a ese punto. -/

namespace MEDIDA
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs

def MED_of_boundedIn (w c : Term) :
    Prf (Formula.impl (boundedIn c w) (Formula.impl (wfAll1 w) (isTermCodeE1 w c))) := by
  refine prf_ex_elim_imp ?_
  rw [liftFormula, liftF_wfAll1, liftF_isTermCodeE1]
  refine deduction_aux ?_ (wfAll1 (liftTerm 0 w)) _ rfl
  have hwf : PrfH [wfAll1 (liftTerm 0 w),
      land (lt (.var 0) (liftTerm 0 (lenc w)))
        (Formula.eq (nthc (liftTerm 0 w) (.var 0)) (liftTerm 0 c))]
      (wfAll1 (liftTerm 0 w)) := PrfH.hyp _ _ (List.Mem.head _)
  have hbody : PrfH [wfAll1 (liftTerm 0 w),
      land (lt (.var 0) (liftTerm 0 (lenc w)))
        (Formula.eq (nthc (liftTerm 0 w) (.var 0)) (liftTerm 0 c))]
      (land (lt (.var 0) (liftTerm 0 (lenc w)))
        (Formula.eq (nthc (liftTerm 0 w) (.var 0)) (liftTerm 0 c))) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hlt : PrfH [wfAll1 (liftTerm 0 w),
      land (lt (.var 0) (liftTerm 0 (lenc w)))
        (Formula.eq (nthc (liftTerm 0 w) (.var 0)) (liftTerm 0 c))]
      (lt (.var 0) (lenc (liftTerm 0 w))) := by
    have h := PrfH_and_elim_left hbody
    simpa only [lenc, liftTerm, liftTerms] using h
  have heq := PrfH_and_elim_right hbody
  have hitc := PrfH.mp _ _ _ (PrfH_inst_wfAll1 (liftTerm 0 w) (.var 0) hwf) hlt
  exact PrfH_congr_isTermCodeE1 heq hitc

def MED_of_In (w c : Term) :
    Prf (Formula.impl (In c w) (Formula.impl (wfAll1 w) (isTermCodeE1 w c))) :=
  impT (prf_boundedIn_of_In c w) (MED_of_boundedIn w c)

def MED_crit (w c : Term) (k : Nat) (hk0 : k ≠ 0) (hk1 : k ≠ 1)
    (hcl : ∀ n : Nat, liftTerm n c = c) (hck : Prf (carc c =eq numeralM k)) :
    Prf (Formula.impl (boundedIn c w) (Formula.impl (wfAll1 w) Formula.bottom)) := by
  refine prf_deduction (deduction_aux ?_ (wfAll1 w) [boundedIn c w] rfl)
  show PrfH [wfAll1 w, boundedIn c w] Formula.bottom
  have hwf : PrfH [wfAll1 w, boundedIn c w] (wfAll1 w) := PrfH.hyp _ _ (List.Mem.head _)
  have hbd : PrfH [wfAll1 w, boundedIn c w] (boundedIn c w) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hitc : PrfH [wfAll1 w, boundedIn c w] (isTermCodeE1 w c) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (MED_of_boundedIn w c) _) hbd) hwf
  exact PrfH.mp _ _ _
    (prf_to_prfH (crit_isTermCodeE1_rejects w c k hk0 hk1 hck) _) hitc

/-- CONTROL: los `MED_*` habitan EXACTAMENTE los enunciados de §1-§2. -/
example (w c : Term) :
    Prf (Formula.impl (boundedIn c w) (Formula.impl (wfAll1 w) (isTermCodeE1 w c))) :=
  MED_of_boundedIn w c
example (w c : Term) :
    Prf (Formula.impl (In c w) (Formula.impl (wfAll1 w) (isTermCodeE1 w c))) :=
  MED_of_In w c
example (w c : Term) (k : Nat) (h0 : k ≠ 0) (h1 : k ≠ 1)
    (hcl : ∀ n : Nat, liftTerm n c = c) (hck : Prf (carc c =eq numeralM k)) :
    Prf (Formula.impl (boundedIn c w) (Formula.impl (wfAll1 w) Formula.bottom)) :=
  MED_crit w c k h0 h1 hcl hck

end MEDIDA

open Lean Elab Command in
/-- Lista las constantes de `CodeWitnessPrf` que usa el termino, con su linea de declaracion. -/
elab "#deps " id:ident : command => do
  let env ← getEnv
  let n ← liftCoreM <| realizeGlobalConstNoOverload id
  let pref : Name := `ROBINSON_PlusPlus.Meta.CodeWitnessPrf
  let some a := env.findAsync? n | throwError "no existe {n}"
  let ci := a.toConstantInfo
  let some v := ci.value? | throwError "{n}: sin cuerpo en el entorno"
  let mut out : Array String := #[]
  for c in v.getUsedConstants do
    if pref.isPrefixOf c then
      let r ← liftCoreM <| findDeclarationRanges? c
      let ln : String := match r with
        | some rr => toString rr.range.pos.line
        | none => "??"
      out := out.push s!"    {c}  @ {ln}"
  logInfo s!"{n} — {out.size} constantes de CodeWitnessPrf:\n{String.intercalate "\n" out.toList}"

#deps MEDIDA.MED_of_boundedIn
#deps MEDIDA.MED_of_In
#deps MEDIDA.MED_crit

/-! ## §5 · FOOTPRINT -/

#print axioms ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_isTermCodeE1_of_boundedIn'
#print axioms ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_isTermCodeE1_of_In'
#print axioms ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_crit_In_rejects_open1'
#print axioms ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.crit_isTC1_junk_refuted_open'
-- LINEA BASE, para comparar: el lema de produccion que el corolario sustituye.
#print axioms ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_crit_In_rejects_open1
-- Y el GEMELO POR SORT que ya vive en el modulo (`ENS`, :1629).
#print axioms ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.prf_isFormCodeE2_of_boundedIn
