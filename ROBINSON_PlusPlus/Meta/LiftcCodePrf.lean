import ROBINSON_PlusPlus.Meta.ArithPrf
import ROBINSON_PlusPlus.Meta.ChainPrf
import ROBINSON_PlusPlus.Meta.CodeCtorKit
import ROBINSON_PlusPlus.Meta.CodeWitnessPrf
import ROBINSON_PlusPlus.Meta.Delta0ReflectPrf
import ROBINSON_PlusPlus.Meta.DerivCondPrf
import ROBINSON_PlusPlus.Meta.DotConsPrf
import ROBINSON_PlusPlus.Meta.EvalArithPrf
import ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf
import ROBINSON_PlusPlus.Meta.EvalLtPrf
import ROBINSON_PlusPlus.Meta.Godel
import ROBINSON_PlusPlus.Meta.Hilbert
import ROBINSON_PlusPlus.Meta.HilbertDeduction
import ROBINSON_PlusPlus.Meta.LineWFTrackedPrf
import ROBINSON_PlusPlus.Meta.MpCodePrf
import ROBINSON_PlusPlus.Meta.NatArithPrf
import ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
import ROBINSON_PlusPlus.Meta.Provability
import ROBINSON_PlusPlus.Meta.ReprPrf
import ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
import ROBINSON_PlusPlus.Meta.Sigma1Prf
import ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
import ROBINSON_PlusPlus.Meta.TcArithPrf
import ROBINSON_PlusPlus.Meta.TrackedCorePrf
import ROBINSON_PlusPlus.Meta.EvalRunFnPrf
/-!
# `Meta/LiftcCodePrf.lean` — CONTENIDO EXACTO PROPUESTO (validado desde `Probe/`)

Promocion de `sondeos/ReflectorDesdeConsumidor.lean` (rama B1).

**ESTE FICHERO ES EL MODULO, BYTE A BYTE** — promovido a `ROBINSON_PlusPlus/Meta/` y anadido al
barrel el 2026‑09‑02. La lista de `import` de arriba es la concreta: **25** modulos de `Meta/`,
ninguno es el barrel. El bloque final de `#print axioms` / `example` se conserva a proposito: es
el control de footprint del modulo, no andamio.

## Nombre propuesto: `LiftcCodePrf`, NO `CodeCtorDotPrf`

`CodeCtorKit` ya es «el kit de constructores de codigo dotados» genericos (`nulT`/`unT`/`binT`
y sus congruencias internas), y este modulo lo CONSUME. Lo que aporta no son constructores
genericos sino la teoria a nivel de CODIGO de `liftc`/`liftsc`: su vocabulario, sus cuatro
axiomas en imagen dotada, y las cuatro clausulas del reflector. `LiftcCodePrf` lo dice; y el
sufijo `…Prf` es la convencion del arbol.

## Lo que NO se promueve (ya esta en produccion, byte a byte)

| simbolo del sondeo   | ya vive en                                          |
|----------------------|-----------------------------------------------------|
| `shapeUn`            | `Minimal/Axioms.lean` — alias `CodeWitnessPrf.SinWTs` (ADR-020) |
| `shapeBin`           | `Minimal/Axioms.lean` (idem)                        |
| `argsInBody`         | `Minimal/Axioms.lean` (idem)                        |
| `argsIn`             | `Minimal/Axioms.lean` (idem)                        |
| `isTermCodeE1`       | `Minimal/Axioms.lean` (idem)                        |
| `impT`               | `Meta/CodeWitnessPrf.lean:105` (idem)               |
| `prf_or_elim_imp`    | `Meta/CodeWitnessPrf.lean:109` (idem)               |
| `PrfH_eq_trans_code` | `Meta/EvalCarcNthcPrf.lean:66` (exportado a raiz)   |
| `eqc_eq_eqCodeFn`    | `Meta/Sigma1AtomPrf.lean:122` como `eqCodeFn_eq_eqc` |

Los siete primeros se CONSUMEN con un `open` SELECTIVO (abrir `SinWTs` entero colisionaria con
`NumCodeClosedPrf.prf_congr_liftc`, que tiene otra aridad). El octavo llega solo, por el `export`
de `EvalCarcNthcPrf`. El noveno es la orientacion contraria del mismo `rfl`: se usa `.symm`.

## Lo que SI se promueve: **69** declaraciones (65 de las 75 del sondeo, + 2 puentes nuevos,
+ **2 bajadas desde `sondeos/DescensoLiftc.lean`** en B2: `substF_targetLift`/`substF_targetLiftsc`)

Vocabulario de codigo dotado de `liftc`/`liftsc` (§1–§2), los cuatro axiomas de `liftc`/`liftsc`
en su imagen DOTADA (§4–§5), las congruencias internas que faltaban (§6) y las cuatro clausulas
del reflector, en las DOS monedas: meta (`refl_caso_*`, §7) y objeto (`refl_*_imp`, §9–§10).

⚠️ `varcT`/`funccT` son, por definicion, `unT 0` / `binT 1` del KIT (`Meta/CodeCtorKit.lean`):
NO son constructores nuevos, son alias que hacen legible el tag. Todo lema del KIT sobre
`unT`/`binT` se les aplica por defeq (asi se prueban `prf_congr_varcT` y `prf_substtc_varcT_at`).
-/

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.TcArithPrf ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf ROBINSON_PlusPlus.Meta.MpCodePrf
open ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
open ROBINSON_PlusPlus.Meta.EvalArithPrf ROBINSON_PlusPlus.Meta.EvalLtPrf
open ROBINSON_PlusPlus.Meta.NatArithPrf ROBINSON_PlusPlus.Meta.DotConsPrf
open ROBINSON_PlusPlus.Meta.DerivCondPrf ROBINSON_PlusPlus.Meta.CodeCtorKit
open ROBINSON_PlusPlus.Meta.HilbertDeduction ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf ROBINSON_PlusPlus.Meta.TrackedCorePrf
open ROBINSON_PlusPlus.Meta.LineWFTrackedPrf ROBINSON_PlusPlus.Meta.EvalRunFnPrf

/-! ⚠️ `open` **SELECTIVO**: se toma de `CodeWitnessPrf.SinWTs` **solo** lo que este modulo
    consume. (Hasta B8b el motivo era otro: abrirlo entero traia `SinWTs.prf_congr_liftc
    (v : Term) …`, AMBIGUO con `NumCodeClosedPrf.prf_congr_liftc {c : Term} …`. Ese duplicado
    ya no existe — se borro por no tener consumidores —, pero el `open` sigue siendo selectivo
    porque un `open` entero de un modulo de 2 200 lineas no es una dependencia declarada.) -/
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs
  (shapeUn shapeBin argsIn argsInBody isTermCodeE1 impT prf_or_elim_imp)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace ROBINSON_PlusPlus.Meta.LiftcCodePrf

/-! ## §1 · Los constructores de codigo DOTADOS

    Ninguna ecuacion de recursion se postula para `liftcT`/`liftscT`: **la imagen DOTADA es una
    DEFINICION**, y sus puentes con `termCode` salen por `rfl`.

    ⚠️ **Distincion que la version anterior de esta frase borraba, y que aqui es critica**: las
    ecuaciones de `liftc`/`liftsc` (el nivel OBJETO) **si estan postuladas**, como axiomas objeto
    de `Minimal/Axioms.lean`. Lo que NO se postula —y no se puede, porque hace la teoria
    INCONSISTENTE— es la ecuacion de recursion de su imagen dotada. -/

/-- `⌜liftc c t⌝` como constructor de codigo. -/
def liftcT (c t : Term) : Term := funcc (strCode "liftc") (cons c (cons t nil))
/-- `⌜liftsc c ts⌝` como constructor de codigo. -/
def liftscT (c ts : Term) : Term := funcc (strCode "liftsc") (cons c (cons ts nil))

/-! ### La GUARDA de los dos constructores (ADR-020): `funcc` binarios ⇒ escalera §28 -/
theorem prf_hasWit_liftcT {c t : Term} (hc : Prf (hasWit c)) (ht : Prf (hasWit t)) :
    Prf (hasWit (liftcT c t)) := prf_hasWit_funcc2 (strCode "liftc") c t hc ht
theorem prf_hasWit_liftscT {c t : Term} (hc : Prf (hasWit c)) (ht : Prf (hasWit t)) :
    Prf (hasWit (liftscT c t)) := prf_hasWit_funcc2 (strCode "liftsc") c t hc ht

/-- `varc x = cons 0 (cons x nil)` ⇒ su imagen punteada es el `unT 0` del KIT
    (`Meta/CodeCtorKit.lean:60`). CERO simbolos nuevos: es un alias defeq. -/
def varcT (X : Term) : Term := unT 0 X
/-- `funcc a b = cons 1 (cons a (cons b nil))` ⇒ su imagen punteada es el `binT 1` del KIT
    (`Meta/CodeCtorKit.lean:64`). Alias defeq. -/
def funccT (X Y : Term) : Term := binT 1 X Y

theorem prf_hasWit_varcT {X : Term} (hX : Prf (hasWit X)) : Prf (hasWit (varcT X)) :=
  prf_hasWit_unT 0 hX
theorem prf_hasWit_funccT {X Y : Term} (hX : Prf (hasWit X)) (hY : Prf (hasWit Y)) :
    Prf (hasWit (funccT X Y)) := prf_hasWit_binT 1 hX hY

/-- Control explicito de que `varcT` NO es un constructor nuevo. -/
theorem varcT_eq_unT (X : Term) : varcT X = unT 0 X := rfl
/-- Control explicito de que `funccT` NO es un constructor nuevo. -/
theorem funccT_eq_binT (X Y : Term) : funccT X Y = binT 1 X Y := rfl

theorem liftcT_termCode (c t : Term) :
    liftcT (termCode c) (termCode t) = termCode (liftc c t) := rfl
theorem liftscT_termCode (c t : Term) :
    liftscT (termCode c) (termCode t) = termCode (liftsc c t) := rfl
theorem varcT_termCode (x : Term) : varcT (termCode x) = termCode (varc x) := rfl
theorem funccT_termCode (x y : Term) : funccT (termCode x) (termCode y) = termCode (funcc x y) :=
  rfl

/-! ## §2 · Fontaneria: congruencias e invariancias de los constructores nuevos -/

theorem prf_congr_liftcT {c c' t t' : Term} (hc : Prf (c =eq c')) (ht : Prf (t =eq t')) :
    Prf (liftcT c t =eq liftcT c' t') :=
  prf_congr_funcc2 (prf_eq_trans (prf_congr_cons_head hc)
    (prf_congr_cons_tail (prf_congr_cons_head ht)))

theorem prf_congr_liftscT {c c' t t' : Term} (hc : Prf (c =eq c')) (ht : Prf (t =eq t')) :
    Prf (liftscT c t =eq liftscT c' t') :=
  prf_congr_funcc2 (prf_eq_trans (prf_congr_cons_head hc)
    (prf_congr_cons_tail (prf_congr_cons_head ht)))

theorem prf_congr_varcT {X X' : Term} (h : Prf (X =eq X')) : Prf (varcT X =eq varcT X') :=
  prf_congr_unT h
theorem prf_congr_funccT {X X' Y Y' : Term} (hx : Prf (X =eq X')) (hy : Prf (Y =eq Y')) :
    Prf (funccT X Y =eq funccT X' Y') := prf_congr_binT hx hy

theorem prf_substtc_liftcT (v W x y : Term) :
    Prf (substtc v W (liftcT x y) =eq liftcT (substtc v W x) (substtc v W y)) :=
  prf_substtc_funcc2 v W (strCode "liftc") x y
theorem prf_substtc_liftscT (v W x y : Term) :
    Prf (substtc v W (liftscT x y) =eq liftscT (substtc v W x) (substtc v W y)) :=
  prf_substtc_funcc2 v W (strCode "liftsc") x y

theorem substtc_inv_liftcT {X Y : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y)) :
    ∀ W, Prf (substtc zero W (liftcT X Y) =eq liftcT X Y) := fun W =>
  prf_eq_trans (prf_substtc_liftcT zero W X Y) (prf_congr_liftcT (hX W) (hY W))
theorem substtc_inv_liftscT {X Y : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y)) :
    ∀ W, Prf (substtc zero W (liftscT X Y) =eq liftscT X Y) := fun W =>
  prf_eq_trans (prf_substtc_liftscT zero W X Y) (prf_congr_liftscT (hX W) (hY W))

/-! ### `substtc` a NIVEL ARBITRARIO sobre los codigos cerrados

    Produccion ya tiene el caso `zero` (`CodeCtorKit.prf_substtc_unT`/`prf_substtc_binT`,
    `LineWFSchemaPrf.substtc_inv_termCode_numeralM`). Estos son la GENERALIZACION a
    `numeral v` arbitrario, que es la que consume `pcc_liftc_func_code` (nivel 1 y 2). -/

-- ⚠️ `prf_substtc_termCode_closed` / `_numeralM` / `_zero` **SUBIERON a
--    `Meta/CodeCtorKit.lean`** en B3 (2026‑09‑04). Fue la TARIFA de colocar alli el general
--    `prf_substtc_binK_at`, que los consume: si el general se quedaba aqui, no podia
--    reescribir `prf_congr_binT` ni `prf_substtc_binT`, que son de `CodeCtorKit` y este
--    modulo lo IMPORTA (el ciclo de ADR‑019). Se siguen usando aqui sin cambiar nada:
--    llegan por el `import` y por el `export` de aquel modulo.

theorem prf_substtc_unT_at (m v : Nat) (W a : Term) :
    Prf (substtc (numeral v) W (unT m a) =eq unT m (substtc (numeral v) W a)) := by
  unfold unT consT
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  refine prf_congr_funcc2 ?_
  refine prf_eq_trans (prf_congr_cons_head (prf_substtc_termCode_numeralM v m W)) ?_
  refine prf_congr_cons_tail (prf_congr_cons_head ?_)
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  exact prf_congr_funcc2
    (prf_congr_cons_tail (prf_congr_cons_head (prf_substtc_termCode_zero v W)))

/-- **Corolario de `CodeCtorKit.prf_substtc_binK_at`** desde B3: eran DOCE lineas de
    `refine`, y son una. El general esta aguas arriba, en `CodeCtorKit`, por el ciclo de
    imports (ADR‑019). -/
theorem prf_substtc_binT_at (m v : Nat) (W a b : Term) :
    Prf (substtc (numeral v) W (binT m a b)
      =eq binT m (substtc (numeral v) W a) (substtc (numeral v) W b)) :=
  prf_substtc_binK_at (numeralM m) (fun c => liftTerm_numeralM c m) v W a b

theorem prf_substtc_varcT_at (v : Nat) (W a : Term) :
    Prf (substtc (numeral v) W (varcT a) =eq varcT (substtc (numeral v) W a)) :=
  prf_substtc_unT_at 0 v W a
theorem prf_substtc_funccT_at (v : Nat) (W a b : Term) :
    Prf (substtc (numeral v) W (funccT a b)
      =eq funccT (substtc (numeral v) W a) (substtc (numeral v) W b)) :=
  prf_substtc_binT_at 1 v W a b

/-! ## §3 · LOS DOS OBJETIVOS

    `targetLift s` es LITERALMENTE la hipotesis sin descargar de
    `sondeos/Paso2CasoForall.lean:507`; `targetLiftsc b` es su companera sobre listas de
    argumentos.

    ⚠️ **`sondeos/DescensoLiftc.lean` (rama B2) los redefine byte a byte**: al promover B2 hay
    que BORRAR alli §1–§4 y consumir estas. -/

/-- El objetivo sobre TERMINOS. -/
def targetLift (s : Term) : Formula :=
  provFromCode (eqc (liftcT (termCode zero) (tcFn s)) (tcFn (liftc zero s)))

/-- El objetivo sobre LISTAS de terminos. -/
def targetLiftsc (b : Term) : Formula :=
  provFromCode (eqc (liftscT (termCode zero) (tcFn b)) (tcFn (liftsc zero b)))

/-- CONTROL NEGATIVO: `targetLift` no es una reflexividad disfrazada. -/
example (s : Term) : True := by
  fail_if_success
    exact (rfl : liftcT (termCode zero) (tcFn s) = tcFn (liftc zero s))
  trivial

/-! ## §4 · LAS ECUACIONES DE `liftc`/`liftsc`, DOTADAS

    Las cinco ecuaciones recursivas de `liftc`/`liftsc` (`ax_liftc_var_lt`, `ax_liftc_var_ge`,
    `ax_liftc_func`, `ax_liftsc_nil`, `ax_liftsc_cons`) son `forall_2`/`forall_3`/`forall_`.
    Su imagen DOTADA sale por `pcc_axiom_inst*` + computo del `substfc` sobre el codigo
    explicito (patron `pcc_nthc_zero_code`, `pcc_substfc_forall_dot`).

    ⚠️ MEDIDA CENTRAL: **todas son LIBRES DE CUANTIFICADOR**. Ni un solo `bdAllCode`. -/

def LIFTC_FUNC_BODY : Formula :=
  liftc (.var 2) (funcc (.var 1) (.var 0)) =eq funcc (.var 1) (liftsc (.var 2) (.var 0))

theorem LIFTC_FUNC_BODY_ok : ax_liftc_func = forall_3 LIFTC_FUNC_BODY := rfl

/-- **`ax_liftc_func` DOTADA**: `⊢ Prov(⌜ liftc(ċ, funcc(ȧ,ḃ)) = funcc(ȧ, liftsc(ċ,ḃ)) ⌝)`,
    con `c`, `a`, `b` **ABSTRACTOS**. -/
theorem pcc_liftc_func_code [AnclaEq] (c a b : Term) :
    Prf (provFromCode (eqCodeFn
      (liftcT (tcFn c) (funccT (tcFn a) (tcFn b)))
      (funccT (tcFn a) (liftscT (tcFn c) (tcFn b))))) := by
  let W2 : Term := liftc zero (liftc zero (tcFn c))
  let W1 : Term := liftc zero (tcFn a)
  let W0 : Term := tcFn b
  have hin : Prf (substfc (succ (succ zero)) W2 (formCode LIFTC_FUNC_BODY)
      =eq eqCodeFn (liftcT W2 (funccT (varc (numeral 1)) (varc (numeral 0))))
                   (funccT (varc (numeral 1)) (liftscT W2 (varc (numeral 0))))) :=
    prf_substfc_arith_open 2 W2 LIFTC_FUNC_BODY
  have hA2 : Prf (W2 =eq tcFn c) :=
    prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn c)) (prf_liftc_tcFn c)
  have hnorm : Prf (eqCodeFn (liftcT W2 (funccT (varc (numeral 1)) (varc (numeral 0))))
                   (funccT (varc (numeral 1)) (liftscT W2 (varc (numeral 0))))
      =eq eqCodeFn (liftcT (tcFn c) (funccT (varc (numeral 1)) (varc (numeral 0))))
                   (funccT (varc (numeral 1)) (liftscT (tcFn c) (varc (numeral 0))))) :=
    prf_congr_eqCodeFn (prf_congr_liftcT hA2 (prf_refl _))
      (prf_congr_funccT (prf_refl _) (prf_congr_liftscT hA2 (prf_refl _)))
  have hv1 : Prf (substtc (succ zero) W1 (varc (numeral 1)) =eq tcFn a) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (succ zero) W1 (numeral 1)) (prf_refl _))
      (prf_liftc_tcFn a)
  have hv0 : Prf (substtc (succ zero) W1 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (succ zero) W1 (numeral 0)) (prf_zero_lt_succ zero)
  have hc1 : Prf (substtc (succ zero) W1 (tcFn c) =eq tcFn c) := prf_substtc_tcFn_at 1 W1 c
  have hmid : Prf (substfc (succ zero) W1 (eqCodeFn
        (liftcT (tcFn c) (funccT (varc (numeral 1)) (varc (numeral 0))))
        (funccT (varc (numeral 1)) (liftscT (tcFn c) (varc (numeral 0)))))
      =eq eqCodeFn (liftcT (tcFn c) (funccT (tcFn a) (varc (numeral 0))))
                   (funccT (tcFn a) (liftscT (tcFn c) (varc (numeral 0))))) := by
    refine prf_eq_trans (prf_substfc_eq (succ zero) W1 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_liftcT (succ zero) W1 _ _) ?_
      refine prf_congr_liftcT hc1 ?_
      exact prf_eq_trans (prf_substtc_funccT_at 1 W1 _ _) (prf_congr_funccT hv1 hv0)
    · refine prf_eq_trans (prf_substtc_funccT_at 1 W1 _ _) ?_
      refine prf_congr_funccT hv1 ?_
      exact prf_eq_trans (prf_substtc_liftscT (succ zero) W1 _ _) (prf_congr_liftscT hc1 hv0)
  have hout : Prf (substfc zero W0 (eqCodeFn
        (liftcT (tcFn c) (funccT (tcFn a) (varc (numeral 0))))
        (funccT (tcFn a) (liftscT (tcFn c) (varc (numeral 0)))))
      =eq eqCodeFn (liftcT (tcFn c) (funccT (tcFn a) (tcFn b)))
                   (funccT (tcFn a) (liftscT (tcFn c) (tcFn b)))) := by
    refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_liftcT zero W0 _ _) ?_
      refine prf_congr_liftcT (prf_substtc_tcFn W0 c) ?_
      exact prf_eq_trans (prf_substtc_funccT_at 0 W0 _ _)
        (prf_congr_funccT (prf_substtc_tcFn W0 a) (prf_substtc_varc0 W0))
    · refine prf_eq_trans (prf_substtc_funccT_at 0 W0 _ _) ?_
      refine prf_congr_funccT (prf_substtc_tcFn W0 a) ?_
      exact prf_eq_trans (prf_substtc_liftscT zero W0 _ _)
        (prf_congr_liftscT (prf_substtc_tcFn W0 c) (prf_substtc_varc0 W0))
  have hchain : Prf (substfc zero W0 (substfc (succ zero) W1
      (substfc (succ (succ zero)) W2 (formCode LIFTC_FUNC_BODY)))
      =eq eqCodeFn (liftcT (tcFn c) (funccT (tcFn a) (tcFn b)))
                   (funccT (tcFn a) (liftscT (tcFn c) (tcFn b)))) :=
    prf_eq_trans (prf_congr_substfc_arg3
      (prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hmid)) hout
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst3 LIFTC_FUNC_BODY (show ax_liftc_func ∈ axioms by simp [axioms])
      (tcFn c) (tcFn a) (tcFn b)
      (prf_hasWit_tcFn (liftTerm 0 c)) (prf_hasWit_tcFn (liftTerm 0 a))
      (prf_hasWit_tcFn (liftTerm 0 b)))

/-- `substfc` atraviesa un atomo binario de codigo. Generaliza los dos casos particulares de
    produccion (`D3InDotPrf.prf_substfc_ltCodeFn_snd`, `EvalBoundedPrf.prf_substfc_ltCodeFn_varc0`),
    que fijan uno de los dos argumentos. -/
theorem prf_substfc_atom2CodeFn (v t : Term) (s : String) (a b : Term) :
    Prf (substfc v t (atom2CodeFn s a b)
      =eq atom2CodeFn s (substtc v t a) (substtc v t b)) := by
  unfold atom2CodeFn
  refine prf_eq_trans (prf_substfc_atom v t (strCode s) (cons a (cons b nil))) ?_
  refine prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head ?_))
  refine prf_eq_trans (prf_substtsc_cons v t a (cons b nil)) ?_
  exact prf_congr_cons_tail
    (prf_eq_trans (prf_substtsc_cons v t b nil) (prf_congr_cons_tail (prf_substtsc_nil v t)))

/-- Caso `<` de `prf_substfc_atom2CodeFn`, con AMBOS argumentos abiertos. -/
theorem prf_substfc_ltCodeFn' (v t a b : Term) :
    Prf (substfc v t (ltCodeFn a b) =eq ltCodeFn (substtc v t a) (substtc v t b)) :=
  prf_substfc_atom2CodeFn v t lt_sym a b

def LIFTC_VARGE_BODY : Formula :=
  Formula.impl (lt (.var 1) (succ (.var 0)))
    (liftc (.var 1) (varc (.var 0)) =eq varc (succ (.var 0)))

theorem LIFTC_VARGE_BODY_ok : ax_liftc_var_ge = forall_2 LIFTC_VARGE_BODY := rfl

/-- **`ax_liftc_var_ge` DOTADA** (con la guarda interna `ċ < σṅ` SIN descargar). -/
theorem pcc_liftc_var_ge_code [AnclaEq] (c n : Term) :
    Prf (provFromCode (implc (ltCodeFn (tcFn c) (succcT (tcFn n)))
      (eqCodeFn (liftcT (tcFn c) (varcT (tcFn n))) (varcT (succcT (tcFn n)))))) := by
  let W1 : Term := liftc zero (tcFn c)
  let W0 : Term := tcFn n
  have hin : Prf (substfc (succ zero) W1 (formCode LIFTC_VARGE_BODY)
      =eq implc (ltCodeFn W1 (succcT (varc (numeral 0))))
            (eqCodeFn (liftcT W1 (varcT (varc (numeral 0))))
              (varcT (succcT (varc (numeral 0)))))) :=
    prf_substfc_arith_open 1 W1 LIFTC_VARGE_BODY
  have hA1 : Prf (W1 =eq tcFn c) := prf_liftc_tcFn c
  have hnorm : Prf (implc (ltCodeFn W1 (succcT (varc (numeral 0))))
        (eqCodeFn (liftcT W1 (varcT (varc (numeral 0))))
          (varcT (succcT (varc (numeral 0)))))
      =eq implc (ltCodeFn (tcFn c) (succcT (varc (numeral 0))))
            (eqCodeFn (liftcT (tcFn c) (varcT (varc (numeral 0))))
              (varcT (succcT (varc (numeral 0)))))) :=
    prf_congr_implc (prf_congr_atom2CodeFn hA1 (prf_refl _))
      (prf_congr_eqCodeFn (prf_congr_liftcT hA1 (prf_refl _)) (prf_refl _))
  have hout : Prf (substfc zero W0 (implc (ltCodeFn (tcFn c) (succcT (varc (numeral 0))))
        (eqCodeFn (liftcT (tcFn c) (varcT (varc (numeral 0))))
          (varcT (succcT (varc (numeral 0))))))
      =eq implc (ltCodeFn (tcFn c) (succcT (tcFn n)))
            (eqCodeFn (liftcT (tcFn c) (varcT (tcFn n))) (varcT (succcT (tcFn n))))) := by
    refine prf_eq_trans (prf_substfc_impl zero W0 _ _) ?_
    refine prf_congr_implc ?_ ?_
    · refine prf_eq_trans (prf_substfc_ltCodeFn' zero W0 _ _) ?_
      refine prf_congr_atom2CodeFn (prf_substtc_tcFn W0 c) ?_
      exact prf_eq_trans (prf_substtc_funcc1 zero W0 _ _)
        (prf_congr_succcT (prf_substtc_varc0 W0))
    · refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
      refine prf_congr_eqCodeFn ?_ ?_
      · refine prf_eq_trans (prf_substtc_liftcT zero W0 _ _) ?_
        exact prf_congr_liftcT (prf_substtc_tcFn W0 c)
          (prf_eq_trans (prf_substtc_varcT_at 0 W0 _) (prf_congr_varcT (prf_substtc_varc0 W0)))
      · refine prf_eq_trans (prf_substtc_varcT_at 0 W0 _) ?_
        refine prf_congr_varcT ?_
        exact prf_eq_trans (prf_substtc_funcc1 zero W0 _ _)
          (prf_congr_succcT (prf_substtc_varc0 W0))
  have hchain : Prf (substfc zero W0 (substfc (succ zero) W1 (formCode LIFTC_VARGE_BODY))
      =eq implc (ltCodeFn (tcFn c) (succcT (tcFn n)))
            (eqCodeFn (liftcT (tcFn c) (varcT (tcFn n))) (varcT (succcT (tcFn n))))) :=
    prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hout
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst2 LIFTC_VARGE_BODY (show ax_liftc_var_ge ∈ axioms by simp [axioms])
      (tcFn c) (tcFn n)
      (prf_hasWit_tcFn (liftTerm 0 c)) (prf_hasWit_tcFn (liftTerm 0 n)))

/-! ### A5 · EL OBJETIVO A NIVEL ABIERTO, Y LA TRICOTOMÍA DEL `varc`

⚠️ `targetLift`/`targetLiftsc` (arriba) tienen el nivel **clavado a `zero`**, y eso basta
mientras el consumidor sea el sorte término: `liftc c (funcc s ts) = funcc s (liftsc c ts)` y
`liftsc c (cons h t) = cons (liftc c h) (liftsc c t)` **no cambian el nivel**. Lo cambia el
sorte FÓRMULA (`liftfc c (forallc a) = forallc (liftfc (σc) a)`), y por eso `pcc_eval_liftfc`
obliga a abrirlo — es **A5** (§3.49.1).

⭐ **Y por eso A5 es más barata de lo que parece**: en toda la recursión de término el nivel es
un **parámetro inerte**. El único sitio donde de verdad interviene es el `varc`, y ahí lo que
aparece es la **tricotomía**: a nivel `zero` sólo valía la rama `≥` (porque `n < 0` es falso),
y al abrirlo hacen falta las dos. -/

/-- El objetivo del sorte TÉRMINO, con el nivel `c` **abierto**. -/
def targetLiftAt (c s : Term) : Formula :=
  provFromCode (eqc (liftcT (tcFn c) (tcFn s)) (tcFn (liftc c s)))

/-- El objetivo del sorte LISTA, con el nivel `c` **abierto**. -/
def targetLiftscAt (c b : Term) : Formula :=
  provFromCode (eqc (liftscT (tcFn c) (tcFn b)) (tcFn (liftsc c b)))

theorem liftF_targetLiftAt (k : Nat) (c s : Term) :
    liftFormula k (targetLiftAt c s) = targetLiftAt (liftTerm k c) (liftTerm k s) := by
  simp only [targetLiftAt, liftFormula_provFromCode_open, eqc, liftcT, funcc, tcFn, liftc,
    cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_strCode]

theorem substF_targetLiftAt (k : Nat) (u c s : Term) :
    substFormula k u (targetLiftAt c s)
      = targetLiftAt (substTerm k u c) (substTerm k u s) := by
  simp only [targetLiftAt, substFormula_provFromCode_open, eqc, liftcT, funcc, tcFn, liftc,
    cons, nil, zero, succ, substTerm, substTerms, substTerm_strCode]

theorem liftF_targetLiftscAt (k : Nat) (c b : Term) :
    liftFormula k (targetLiftscAt c b) = targetLiftscAt (liftTerm k c) (liftTerm k b) := by
  simp only [targetLiftscAt, liftFormula_provFromCode_open, eqc, liftscT, funcc, tcFn, liftsc,
    cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_strCode]

theorem substF_targetLiftscAt (k : Nat) (u c b : Term) :
    substFormula k u (targetLiftscAt c b)
      = targetLiftscAt (substTerm k u c) (substTerm k u b) := by
  simp only [targetLiftscAt, substFormula_provFromCode_open, eqc, liftscT, funcc, tcFn, liftsc,
    cons, nil, zero, succ, substTerm, substTerms, substTerm_strCode]

/-- ⭐ **LA TRICOTOMÍA DEL `varc`, EMPAQUETADA**: los dos axiomas `ax_liftc_var_lt` /
    `ax_liftc_var_ge` cubren todos los casos, porque `a < c` o `c < σa` siempre.

    A nivel `zero` esto es trivial (`prf_zero_lt_succ`); al abrir el nivel es lo único
    genuinamente nuevo del sorte término. -/
theorem prf_liftc_varc_cases (c a : Term) : Prf (lor (lt a c) (lt c (succ a))) := by
  refine ROBINSON_PlusPlus.Meta.CantorMonoPrf.prf_or_elim (prf_lt_trichotomy a c) ?_ ?_
  · exact prf_deduction (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.j1 _ _)) (prfH_hyp_self _))
  · refine prf_deduction ?_
    refine PrfH_or_elim (prfH_hyp_self _) ?_ ?_
    · -- `a = c` ⟹ `c < σa`  (por `c < σc` y Leibniz)
      refine PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.j2 _ _)) ?_
      exact PrfH_lt_subst2
        (ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.PrfH_congr_succ
          (PrfH_eq_symm (PrfH.hyp _ _ (List.Mem.head _))))
        (prf_to_prfH (prf_lt_succ_self c) _)
    · -- `c < a` ⟹ `c < σa`
      refine PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.j2 _ _)) ?_
      exact PrfH.mp _ _ _ (prf_to_prfH (prf_lt_succ_of_lt c a) _)
        (PrfH.hyp _ _ (List.Mem.head _))

/-! ### La rama `<` del `varc`, que faltaba

⚠️ **A nivel `zero` esta rama no existe**: `lt n zero` es falso, así que `refl_caso_varc` sólo
necesitaba `pcc_liftc_var_ge_code`. Al abrir el nivel aparece la **tricotomía**, y con ella la
otra mitad del axioma — que hasta hoy no estaba dotada. Es literalmente el molde de
`pcc_liftc_var_ge_code`, con la guarda al revés y sin el `succcT` del lado derecho. -/

def LIFTC_VARLT_BODY : Formula :=
  Formula.impl (lt (.var 0) (.var 1))
    (liftc (.var 1) (varc (.var 0)) =eq varc (.var 0))

theorem LIFTC_VARLT_BODY_ok : ax_liftc_var_lt = forall_2 LIFTC_VARLT_BODY := rfl

/-- **`ax_liftc_var_lt` DOTADA** (con la guarda interna `ṅ < ċ` SIN descargar). -/
theorem pcc_liftc_var_lt_code [AnclaEq] (c n : Term) :
    Prf (provFromCode (implc (ltCodeFn (tcFn n) (tcFn c))
      (eqCodeFn (liftcT (tcFn c) (varcT (tcFn n))) (varcT (tcFn n))))) := by
  let W1 : Term := liftc zero (tcFn c)
  let W0 : Term := tcFn n
  have hin : Prf (substfc (succ zero) W1 (formCode LIFTC_VARLT_BODY)
      =eq implc (ltCodeFn (varc (numeral 0)) W1)
            (eqCodeFn (liftcT W1 (varcT (varc (numeral 0))))
              (varcT (varc (numeral 0))))) :=
    prf_substfc_arith_open 1 W1 LIFTC_VARLT_BODY
  have hA1 : Prf (W1 =eq tcFn c) := prf_liftc_tcFn c
  have hnorm : Prf (implc (ltCodeFn (varc (numeral 0)) W1)
        (eqCodeFn (liftcT W1 (varcT (varc (numeral 0))))
          (varcT (varc (numeral 0))))
      =eq implc (ltCodeFn (varc (numeral 0)) (tcFn c))
            (eqCodeFn (liftcT (tcFn c) (varcT (varc (numeral 0))))
              (varcT (varc (numeral 0))))) :=
    prf_congr_implc (prf_congr_atom2CodeFn (prf_refl _) hA1)
      (prf_congr_eqCodeFn (prf_congr_liftcT hA1 (prf_refl _)) (prf_refl _))
  have hout : Prf (substfc zero W0 (implc (ltCodeFn (varc (numeral 0)) (tcFn c))
        (eqCodeFn (liftcT (tcFn c) (varcT (varc (numeral 0))))
          (varcT (varc (numeral 0)))))
      =eq implc (ltCodeFn (tcFn n) (tcFn c))
            (eqCodeFn (liftcT (tcFn c) (varcT (tcFn n))) (varcT (tcFn n)))) := by
    refine prf_eq_trans (prf_substfc_impl zero W0 _ _) ?_
    refine prf_congr_implc ?_ ?_
    · refine prf_eq_trans (prf_substfc_ltCodeFn' zero W0 _ _) ?_
      exact prf_congr_atom2CodeFn (prf_substtc_varc0 W0) (prf_substtc_tcFn W0 c)
    · refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
      refine prf_congr_eqCodeFn ?_ ?_
      · refine prf_eq_trans (prf_substtc_liftcT zero W0 _ _) ?_
        exact prf_congr_liftcT (prf_substtc_tcFn W0 c)
          (prf_eq_trans (prf_substtc_varcT_at 0 W0 _) (prf_congr_varcT (prf_substtc_varc0 W0)))
      · exact prf_eq_trans (prf_substtc_varcT_at 0 W0 _)
          (prf_congr_varcT (prf_substtc_varc0 W0))
  have hchain : Prf (substfc zero W0 (substfc (succ zero) W1 (formCode LIFTC_VARLT_BODY))
      =eq implc (ltCodeFn (tcFn n) (tcFn c))
            (eqCodeFn (liftcT (tcFn c) (varcT (tcFn n))) (varcT (tcFn n)))) :=
    prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hout
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst2 LIFTC_VARLT_BODY (show ax_liftc_var_lt ∈ axioms by simp [axioms])
      (tcFn c) (tcFn n)
      (prf_hasWit_tcFn (liftTerm 0 c)) (prf_hasWit_tcFn (liftTerm 0 n)))

def LIFTSC_NIL_BODY : Formula := liftsc (.var 0) nil =eq nil

theorem LIFTSC_NIL_BODY_ok : ax_liftsc_nil = Formula.forall LIFTSC_NIL_BODY := rfl

/-- **`ax_liftsc_nil` DOTADA**. -/
theorem pcc_liftsc_nil_code [AnclaEq] (c : Term) :
    Prf (provFromCode (eqCodeFn (liftscT (tcFn c) (termCode nil)) (termCode nil))) := by
  have hin : Prf (substfc zero (tcFn c) (formCode LIFTSC_NIL_BODY)
      =eq eqCodeFn (liftscT (tcFn c) (termCode nil)) (termCode nil)) :=
    prf_substfc_arith_open 0 (tcFn c) LIFTSC_NIL_BODY
  exact prf_mp (prf_provCode_congr hin)
    (pcc_axiom_inst LIFTSC_NIL_BODY (show ax_liftsc_nil ∈ axioms by simp [axioms]) (tcFn c)
      (prf_hasWit_tcFn (liftTerm 0 c)))

def LIFTSC_CONS_BODY : Formula :=
  liftsc (.var 2) (cons (.var 1) (.var 0))
    =eq cons (liftc (.var 2) (.var 1)) (liftsc (.var 2) (.var 0))

theorem LIFTSC_CONS_BODY_ok : ax_liftsc_cons = forall_3 LIFTSC_CONS_BODY := rfl

/-- **`ax_liftsc_cons` DOTADA**, con `c`, `h`, `t` **ABSTRACTOS**. -/
theorem pcc_liftsc_cons_code [AnclaEq] (c h t : Term) :
    Prf (provFromCode (eqCodeFn
      (liftscT (tcFn c) (consT (tcFn h) (tcFn t)))
      (consT (liftcT (tcFn c) (tcFn h)) (liftscT (tcFn c) (tcFn t))))) := by
  let W2 : Term := liftc zero (liftc zero (tcFn c))
  let W1 : Term := liftc zero (tcFn h)
  let W0 : Term := tcFn t
  have hin : Prf (substfc (succ (succ zero)) W2 (formCode LIFTSC_CONS_BODY)
      =eq eqCodeFn (liftscT W2 (consT (varc (numeral 1)) (varc (numeral 0))))
            (consT (liftcT W2 (varc (numeral 1))) (liftscT W2 (varc (numeral 0))))) :=
    prf_substfc_arith_open 2 W2 LIFTSC_CONS_BODY
  have hA2 : Prf (W2 =eq tcFn c) :=
    prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn c)) (prf_liftc_tcFn c)
  have hnorm : Prf (eqCodeFn (liftscT W2 (consT (varc (numeral 1)) (varc (numeral 0))))
            (consT (liftcT W2 (varc (numeral 1))) (liftscT W2 (varc (numeral 0))))
      =eq eqCodeFn (liftscT (tcFn c) (consT (varc (numeral 1)) (varc (numeral 0))))
            (consT (liftcT (tcFn c) (varc (numeral 1)))
              (liftscT (tcFn c) (varc (numeral 0))))) :=
    prf_congr_eqCodeFn (prf_congr_liftscT hA2 (prf_refl _))
      (prf_congr_consT (prf_congr_liftcT hA2 (prf_refl _))
        (prf_congr_liftscT hA2 (prf_refl _)))
  have hv1 : Prf (substtc (succ zero) W1 (varc (numeral 1)) =eq tcFn h) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (succ zero) W1 (numeral 1)) (prf_refl _))
      (prf_liftc_tcFn h)
  have hv0 : Prf (substtc (succ zero) W1 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (succ zero) W1 (numeral 0)) (prf_zero_lt_succ zero)
  have hc1 : Prf (substtc (succ zero) W1 (tcFn c) =eq tcFn c) := prf_substtc_tcFn_at 1 W1 c
  have hmid : Prf (substfc (succ zero) W1 (eqCodeFn
        (liftscT (tcFn c) (consT (varc (numeral 1)) (varc (numeral 0))))
        (consT (liftcT (tcFn c) (varc (numeral 1))) (liftscT (tcFn c) (varc (numeral 0)))))
      =eq eqCodeFn (liftscT (tcFn c) (consT (tcFn h) (varc (numeral 0))))
            (consT (liftcT (tcFn c) (tcFn h)) (liftscT (tcFn c) (varc (numeral 0))))) := by
    refine prf_eq_trans (prf_substfc_eq (succ zero) W1 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_liftscT (succ zero) W1 _ _) ?_
      refine prf_congr_liftscT hc1 ?_
      exact prf_eq_trans (prf_substtc_consT (succ zero) W1 _ _) (prf_congr_consT hv1 hv0)
    · refine prf_eq_trans (prf_substtc_consT (succ zero) W1 _ _) ?_
      refine prf_congr_consT ?_ ?_
      · exact prf_eq_trans (prf_substtc_liftcT (succ zero) W1 _ _) (prf_congr_liftcT hc1 hv1)
      · exact prf_eq_trans (prf_substtc_liftscT (succ zero) W1 _ _) (prf_congr_liftscT hc1 hv0)
  have hout : Prf (substfc zero W0 (eqCodeFn
        (liftscT (tcFn c) (consT (tcFn h) (varc (numeral 0))))
        (consT (liftcT (tcFn c) (tcFn h)) (liftscT (tcFn c) (varc (numeral 0)))))
      =eq eqCodeFn (liftscT (tcFn c) (consT (tcFn h) (tcFn t)))
            (consT (liftcT (tcFn c) (tcFn h)) (liftscT (tcFn c) (tcFn t)))) := by
    refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_liftscT zero W0 _ _) ?_
      refine prf_congr_liftscT (prf_substtc_tcFn W0 c) ?_
      exact prf_eq_trans (prf_substtc_consT zero W0 _ _)
        (prf_congr_consT (prf_substtc_tcFn W0 h) (prf_substtc_varc0 W0))
    · refine prf_eq_trans (prf_substtc_consT zero W0 _ _) ?_
      refine prf_congr_consT ?_ ?_
      · exact prf_eq_trans (prf_substtc_liftcT zero W0 _ _)
          (prf_congr_liftcT (prf_substtc_tcFn W0 c) (prf_substtc_tcFn W0 h))
      · exact prf_eq_trans (prf_substtc_liftscT zero W0 _ _)
          (prf_congr_liftscT (prf_substtc_tcFn W0 c) (prf_substtc_varc0 W0))
  have hchain : Prf (substfc zero W0 (substfc (succ zero) W1
      (substfc (succ (succ zero)) W2 (formCode LIFTSC_CONS_BODY)))
      =eq eqCodeFn (liftscT (tcFn c) (consT (tcFn h) (tcFn t)))
            (consT (liftcT (tcFn c) (tcFn h)) (liftscT (tcFn c) (tcFn t)))) :=
    prf_eq_trans (prf_congr_substfc_arg3
      (prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hmid)) hout
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst3 LIFTSC_CONS_BODY (show ax_liftsc_cons ∈ axioms by simp [axioms])
      (tcFn c) (tcFn h) (tcFn t)
      (prf_hasWit_tcFn (liftTerm 0 c)) (prf_hasWit_tcFn (liftTerm 0 h))
      (prf_hasWit_tcFn (liftTerm 0 t)))

/-! ## §5 · LA GUARDA INTERNA SE DESCARGA — y las cuatro ecuaciones quedan a NIVEL `zero`

    `pcc_lt_tracked` (`Meta/Delta0ReflectPrf.lean:233`, completitud‑Δ₀ provable del atomo `<`,
    con argumentos **ABIERTOS**) refleja `0 < σn` sin pedir clausura. La guarda de
    `ax_liftc_var_ge` **no es un obstaculo**. -/

theorem pcc_zero_lt_succ_code [AnclaEq] (n : Term) :
    Prf (provFromCode (ltCodeFn (tcFn zero) (succcT (tcFn n)))) := by
  have h : Prf (provFromCode (ltCodeFn (tcFn zero) (tcFn (succ n)))) :=
    prf_mp (pcc_lt_tracked zero (succ n)) (prf_zero_lt_succ n)
  exact prf_mp (prf_provCode_congr (prf_congr_atom2CodeFn (prf_refl _) (prf_tc_succ' n))) h

theorem pcc_liftc0_var_code [AnclaEq] (n : Term) :
    Prf (provFromCode (eqCodeFn (liftcT (termCode zero) (varcT (tcFn n)))
      (varcT (succcT (tcFn n))))) := by
  have h := pcc_mp_code_apply (pcc_liftc_var_ge_code zero n) (pcc_zero_lt_succ_code n)
  exact prf_mp (prf_provCode_congr (prf_congr_eqCodeFn
    (prf_congr_liftcT prf_tc_zero (prf_refl _)) (prf_refl _))) h

theorem pcc_liftc0_func_code [AnclaEq] (a b : Term) :
    Prf (provFromCode (eqCodeFn (liftcT (termCode zero) (funccT (tcFn a) (tcFn b)))
      (funccT (tcFn a) (liftscT (termCode zero) (tcFn b))))) :=
  prf_mp (prf_provCode_congr (prf_congr_eqCodeFn
      (prf_congr_liftcT prf_tc_zero (prf_refl _))
      (prf_congr_funccT (prf_refl _) (prf_congr_liftscT prf_tc_zero (prf_refl _)))))
    (pcc_liftc_func_code zero a b)

theorem pcc_liftsc0_nil_code [AnclaEq] :
    Prf (provFromCode (eqCodeFn (liftscT (termCode zero) (tcFn nil)) (tcFn nil))) :=
  prf_mp (prf_provCode_congr (prf_congr_eqCodeFn
      (prf_congr_liftscT prf_tc_zero (prf_eq_symm prf_tc_zero)) (prf_eq_symm prf_tc_zero)))
    (pcc_liftsc_nil_code zero)

theorem pcc_liftsc0_cons_code [AnclaEq] (h t : Term) :
    Prf (provFromCode (eqCodeFn (liftscT (termCode zero) (consT (tcFn h) (tcFn t)))
      (consT (liftcT (termCode zero) (tcFn h)) (liftscT (termCode zero) (tcFn t))))) :=
  prf_mp (prf_provCode_congr (prf_congr_eqCodeFn
      (prf_congr_liftscT prf_tc_zero (prf_refl _))
      (prf_congr_consT (prf_congr_liftcT prf_tc_zero (prf_refl _))
        (prf_congr_liftscT prf_tc_zero (prf_refl _)))))
    (pcc_liftsc_cons_code zero h t)

/-! ## §6 · Congruencias INTERNAS (dentro de `Prov`) para los constructores nuevos.

     Patron `pcc_congr_binT_2_code` (`Meta/CodeCtorKit.lean:248`). Las dos de `consT` faltaban:
     el KIT solo tiene las de `unT`/`binT`, y el paso `cons` de la lista las pide sobre `consT`
     con tag `cons_sym`, que NO es un `binT`. -/

theorem pcc_congr_liftcT_arg2_code (A X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hX : ∀ W, Prf (substtc zero W X =eq X))
    (hwA : Prf (hasWit A) := by hw_auto) (hwX : Prf (hasWit X) := by hw_auto)
    (hwY : Prf (hasWit Y) := by hw_auto) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (liftcT A X) (liftcT A Y))) := by
  let Ac : Term := eqc (liftcT A X) (liftcT A (varc (numeral 0)))
  have hcomp : ∀ w : Term, Prf (substfc zero w Ac =eq eqc (liftcT A X) (liftcT A w)) := by
    intro w
    refine prf_eq_trans (prf_substfc_eq zero w (liftcT A X) (liftcT A (varc (numeral 0)))) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_liftcT zero w A X) (prf_congr_liftcT (hA w) (hX w))
    · exact prf_eq_trans (prf_substtc_liftcT zero w A (varc (numeral 0)))
        (prf_congr_liftcT (hA w) (prf_substtc_varc0 w))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (liftcT A X))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _)
      (prf_hasWitF_eq2 (liftcT A X) (liftcT A (varc (numeral 0)))
        (prf_hasWit_liftcT hwA hwX) (prf_hasWit_liftcT hwA (prf_hasWit_varc (numeral 0)))) hwX hwY)

theorem pcc_congr_liftscT_arg2_code (A X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hX : ∀ W, Prf (substtc zero W X =eq X))
    (hwA : Prf (hasWit A) := by hw_auto) (hwX : Prf (hasWit X) := by hw_auto)
    (hwY : Prf (hasWit Y) := by hw_auto) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (liftscT A X) (liftscT A Y))) := by
  let Ac : Term := eqc (liftscT A X) (liftscT A (varc (numeral 0)))
  have hcomp : ∀ w : Term, Prf (substfc zero w Ac =eq eqc (liftscT A X) (liftscT A w)) := by
    intro w
    refine prf_eq_trans (prf_substfc_eq zero w (liftscT A X) (liftscT A (varc (numeral 0)))) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_liftscT zero w A X) (prf_congr_liftscT (hA w) (hX w))
    · exact prf_eq_trans (prf_substtc_liftscT zero w A (varc (numeral 0)))
        (prf_congr_liftscT (hA w) (prf_substtc_varc0 w))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (liftscT A X))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _)
      (prf_hasWitF_eq2 (liftscT A X) (liftscT A (varc (numeral 0)))
        (prf_hasWit_liftscT hwA hwX) (prf_hasWit_liftscT hwA (prf_hasWit_varc (numeral 0)))) hwX hwY)

/-- Congruencia interna en la COLA de `consT` (para el paso `cons` de la lista). -/
theorem pcc_congr_consT_arg2_code (A X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hX : ∀ W, Prf (substtc zero W X =eq X))
    (hwA : Prf (hasWit A) := by hw_auto) (hwX : Prf (hasWit X) := by hw_auto)
    (hwY : Prf (hasWit Y) := by hw_auto) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (consT A X) (consT A Y))) := by
  let Ac : Term := eqc (consT A X) (consT A (varc (numeral 0)))
  have hcomp : ∀ w : Term, Prf (substfc zero w Ac =eq eqc (consT A X) (consT A w)) := by
    intro w
    refine prf_eq_trans (prf_substfc_eq zero w (consT A X) (consT A (varc (numeral 0)))) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_consT zero w A X) (prf_congr_consT (hA w) (hX w))
    · exact prf_eq_trans (prf_substtc_consT zero w A (varc (numeral 0)))
        (prf_congr_consT (hA w) (prf_substtc_varc0 w))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (consT A X))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _)
      (prf_hasWitF_eq2 (consT A X) (consT A (varc (numeral 0)))
        (prf_hasWit_consT hwA hwX) (prf_hasWit_consT hwA (prf_hasWit_varc (numeral 0)))) hwX hwY)

/-- Congruencia interna en la CABEZA de `consT`. -/
theorem pcc_congr_consT_arg1_code (B X Y : Term)
    (hB : ∀ W, Prf (substtc zero W B =eq B)) (hX : ∀ W, Prf (substtc zero W X =eq X))
    (hwB : Prf (hasWit B) := by hw_auto) (hwX : Prf (hasWit X) := by hw_auto)
    (hwY : Prf (hasWit Y) := by hw_auto) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (consT X B) (consT Y B))) := by
  let Ac : Term := eqc (consT X B) (consT (varc (numeral 0)) B)
  have hcomp : ∀ w : Term, Prf (substfc zero w Ac =eq eqc (consT X B) (consT w B)) := by
    intro w
    refine prf_eq_trans (prf_substfc_eq zero w (consT X B) (consT (varc (numeral 0)) B)) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_consT zero w X B) (prf_congr_consT (hX w) (hB w))
    · exact prf_eq_trans (prf_substtc_consT zero w (varc (numeral 0)) B)
        (prf_congr_consT (prf_substtc_varc0 w) (hB w))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (consT X B))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _)
      (prf_hasWitF_eq2 (consT X B) (consT (varc (numeral 0)) B)
        (prf_hasWit_consT hwX hwB)
        (prf_hasWit_consT (prf_hasWit_varc (numeral 0)) hwB)) hwX hwY)

/-! ## §7 · LAS CUATRO CLAUSULAS DE LA RECURSION — el esqueleto entero de `hLift`

    ⚠️ Observese el ENUNCIADO de las cuatro: la guarda entra **SOLO como una ecuacion PLANA**
    (`s ≐ varc a`, `s ≐ funcc p b`). Ni `wfAll1`, ni `argsIn`, ni `In`, ni ningun `bdAllCode`
    aparecen en ninguna de ellas. -/

/- ⛔ **`iz_inv` RETIRADO al promover (decimo duplicado).** Era
   `∀ W, Prf (substtc zero W (termCode zero) =eq termCode zero)`, que es EXACTAMENTE
   `ROBINSON_PlusPlus.Meta.EvalRunFnPrf.prf_substtc_termCode_nil` — porque `nil := zero`
   (`Minimal/Axioms.lean:126`), asi que `termCode nil` y `termCode zero` son EL MISMO termino.
   Ya esta `export`ado a la raiz (`EvalRunFnPrf.lean:157`), luego visible sin cualificar.
   La comparacion por NOMBRE no lo detectaba: lo caza el verificador con un `rfl` compilado. -/

/-- **(1) BASE `varc` — CERRADA, sin hipotesis mas alla de la forma ecuacional.** -/
theorem refl_caso_varc [AnclaEq] (s a : Term) (hs : Prf (s =eq varc a)) : Prf (targetLift s) := by
  unfold targetLift
  have hplain : Prf (liftc zero s =eq varc (succ a)) :=
    prf_eq_trans (prf_congr_liftc hs) (prf_mp (prf_liftc_var_ge zero a) (prf_zero_lt_succ a))
  have hX : ∀ W, Prf (substtc zero W (liftcT (termCode zero) (tcFn (varc a)))
      =eq liftcT (termCode zero) (tcFn (varc a))) :=
    substtc_inv_liftcT prf_substtc_termCode_nil (substtc_inv_tcFn (varc a))
  have hY : ∀ W, Prf (substtc zero W (liftcT (termCode zero) (varcT (tcFn a)))
      =eq liftcT (termCode zero) (varcT (tcFn a))) :=
    substtc_inv_liftcT prf_substtc_termCode_nil (substtc_inv_unT (substtc_inv_tcFn a))
  have s1 : Prf (provFromCode (eqc (liftcT (termCode zero) (tcFn (varc a)))
      (liftcT (termCode zero) (varcT (tcFn a))))) :=
    prf_mp (pcc_congr_liftcT_arg2_code (termCode zero) (tcFn (varc a)) (varcT (tcFn a))
      prf_substtc_termCode_nil (substtc_inv_tcFn (varc a))
      (prf_hasWit_tc zero) (prf_hasWit_tcFn (varc a))
      (prf_hasWit_varcT (prf_hasWit_tcFn a))) (pcc_dot_un_symm 0 a)
  have s2 : Prf (provFromCode (eqc (liftcT (termCode zero) (varcT (tcFn a)))
      (varcT (succcT (tcFn a))))) := pcc_liftc0_var_code a
  have s3 : Prf (provFromCode (eqc (varcT (succcT (tcFn a))) (tcFn (varc (succ a))))) :=
    prf_mp (prf_provCode_congr (prf_congr_eqCodeFn
      (prf_congr_varcT (prf_tc_succ' a)) (prf_refl _)))
      (pcc_dot_un 0 (succ a))
  have hchain : Prf (provFromCode (eqc (liftcT (termCode zero) (tcFn (varc a)))
      (tcFn (varc (succ a))))) :=
    pcc_eq_trans_code _ _ _ hX
      (prf_hasWit_liftcT (prf_hasWit_tc zero) (prf_hasWit_tcFn (varc a)))
      (prf_hasWit_liftcT (prf_hasWit_tc zero) (prf_hasWit_varcT (prf_hasWit_tcFn a)))
      (prf_hasWit_tcFn (varc (succ a))) s1
      (pcc_eq_trans_code _ _ _ hY
        (prf_hasWit_liftcT (prf_hasWit_tc zero) (prf_hasWit_varcT (prf_hasWit_tcFn a)))
        (prf_hasWit_varcT (prf_hasWit_succcT (prf_hasWit_tcFn a)))
        (prf_hasWit_tcFn (varc (succ a))) s2 s3)
  exact prf_mp (prf_provCode_congr (prf_congr_eqCodeFn
    (prf_congr_liftcT (prf_refl _) (prf_congr_tcFn (prf_eq_symm hs)))
    (prf_congr_tcFn (prf_eq_symm hplain)))) hchain

/-- **(2) PASO `funcc`** — el unico salto: pide la companera sobre la LISTA de argumentos. -/
theorem refl_caso_funcc [AnclaEq] (s p b : Term) (hs : Prf (s =eq funcc p b))
    (hb : Prf (targetLiftsc b)) : Prf (targetLift s) := by
  unfold targetLift
  unfold targetLiftsc at hb
  have hplain : Prf (liftc zero s =eq funcc p (liftsc zero b)) :=
    prf_eq_trans (prf_congr_liftc hs) (prf_liftc_func zero p b)
  have hX : ∀ W, Prf (substtc zero W (liftcT (termCode zero) (tcFn (funcc p b)))
      =eq liftcT (termCode zero) (tcFn (funcc p b))) :=
    substtc_inv_liftcT prf_substtc_termCode_nil (substtc_inv_tcFn (funcc p b))
  have hY : ∀ W, Prf (substtc zero W (liftcT (termCode zero) (funccT (tcFn p) (tcFn b)))
      =eq liftcT (termCode zero) (funccT (tcFn p) (tcFn b))) :=
    substtc_inv_liftcT prf_substtc_termCode_nil
      (substtc_inv_binT (substtc_inv_tcFn p) (substtc_inv_tcFn b))
  have hZ : ∀ W, Prf (substtc zero W
      (funccT (tcFn p) (liftscT (termCode zero) (tcFn b)))
      =eq funccT (tcFn p) (liftscT (termCode zero) (tcFn b))) :=
    substtc_inv_binT (substtc_inv_tcFn p)
      (substtc_inv_liftscT prf_substtc_termCode_nil (substtc_inv_tcFn b))
  have s1 : Prf (provFromCode (eqc (liftcT (termCode zero) (tcFn (funcc p b)))
      (liftcT (termCode zero) (funccT (tcFn p) (tcFn b))))) :=
    prf_mp (pcc_congr_liftcT_arg2_code (termCode zero) (tcFn (funcc p b))
      (funccT (tcFn p) (tcFn b)) prf_substtc_termCode_nil (substtc_inv_tcFn (funcc p b))
      (prf_hasWit_tc zero) (prf_hasWit_tcFn (funcc p b))
      (prf_hasWit_funccT (prf_hasWit_tcFn p) (prf_hasWit_tcFn b)))
      (pcc_dot_bin_symm 1 p b)
  have s2 : Prf (provFromCode (eqc (liftcT (termCode zero) (funccT (tcFn p) (tcFn b)))
      (funccT (tcFn p) (liftscT (termCode zero) (tcFn b))))) := pcc_liftc0_func_code p b
  have s3 : Prf (provFromCode (eqc (funccT (tcFn p) (liftscT (termCode zero) (tcFn b)))
      (funccT (tcFn p) (tcFn (liftsc zero b))))) :=
    prf_mp (pcc_congr_binT_2_code 1 (tcFn p) (liftscT (termCode zero) (tcFn b))
      (tcFn (liftsc zero b)) (substtc_inv_tcFn p)
      (substtc_inv_liftscT prf_substtc_termCode_nil (substtc_inv_tcFn b))
      (prf_hasWit_tcFn p)
      (prf_hasWit_liftscT (prf_hasWit_tc zero) (prf_hasWit_tcFn b))
      (prf_hasWit_tcFn (liftsc zero b))) hb
  have s4 : Prf (provFromCode (eqc (funccT (tcFn p) (tcFn (liftsc zero b)))
      (tcFn (funcc p (liftsc zero b))))) := pcc_dot_bin 1 p (liftsc zero b)
  have hchain : Prf (provFromCode (eqc (liftcT (termCode zero) (tcFn (funcc p b)))
      (tcFn (funcc p (liftsc zero b))))) :=
    pcc_eq_trans_code _ _ _ hX
      (prf_hasWit_liftcT (prf_hasWit_tc zero) (prf_hasWit_tcFn (funcc p b)))
      (prf_hasWit_liftcT (prf_hasWit_tc zero)
        (prf_hasWit_funccT (prf_hasWit_tcFn p) (prf_hasWit_tcFn b)))
      (prf_hasWit_tcFn (funcc p (liftsc zero b))) s1
      (pcc_eq_trans_code _ _ _ hY
        (prf_hasWit_liftcT (prf_hasWit_tc zero)
          (prf_hasWit_funccT (prf_hasWit_tcFn p) (prf_hasWit_tcFn b)))
        (prf_hasWit_funccT (prf_hasWit_tcFn p)
          (prf_hasWit_liftscT (prf_hasWit_tc zero) (prf_hasWit_tcFn b)))
        (prf_hasWit_tcFn (funcc p (liftsc zero b))) s2
        (pcc_eq_trans_code _ _ _ hZ
          (prf_hasWit_funccT (prf_hasWit_tcFn p)
            (prf_hasWit_liftscT (prf_hasWit_tc zero) (prf_hasWit_tcFn b)))
          (prf_hasWit_funccT (prf_hasWit_tcFn p) (prf_hasWit_tcFn (liftsc zero b)))
          (prf_hasWit_tcFn (funcc p (liftsc zero b))) s3 s4))
  exact prf_mp (prf_provCode_congr (prf_congr_eqCodeFn
    (prf_congr_liftcT (prf_refl _) (prf_congr_tcFn (prf_eq_symm hs)))
    (prf_congr_tcFn (prf_eq_symm hplain)))) hchain

/-- **(3) BASE de la LISTA (`nil`) — CERRADA, sin hipotesis ninguna.** -/
theorem refl_lista_nil [AnclaEq] : Prf (targetLiftsc nil) := by
  unfold targetLiftsc
  exact prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
    (prf_congr_tcFn (prf_eq_symm (prf_liftsc_nil zero))))) pcc_liftsc0_nil_code

/-- **(4) PASO de la LISTA (`cons`)** — pide la companera sobre la cabeza y sobre la cola. -/
theorem refl_lista_cons [AnclaEq] (h t : Term) (hh : Prf (targetLift h)) (ht : Prf (targetLiftsc t)) :
    Prf (targetLiftsc (cons h t)) := by
  unfold targetLift at hh
  unfold targetLiftsc at ht ⊢
  have hplain : Prf (liftsc zero (cons h t) =eq cons (liftc zero h) (liftsc zero t)) :=
    prf_liftsc_cons zero h t
  have hX : ∀ W, Prf (substtc zero W (liftscT (termCode zero) (tcFn (cons h t)))
      =eq liftscT (termCode zero) (tcFn (cons h t))) :=
    substtc_inv_liftscT prf_substtc_termCode_nil (substtc_inv_tcFn (cons h t))
  have hY : ∀ W, Prf (substtc zero W (liftscT (termCode zero) (consT (tcFn h) (tcFn t)))
      =eq liftscT (termCode zero) (consT (tcFn h) (tcFn t))) :=
    substtc_inv_liftscT prf_substtc_termCode_nil (substtc_inv_consT (substtc_inv_tcFn h) (substtc_inv_tcFn t))
  have hZ : ∀ W, Prf (substtc zero W
      (consT (liftcT (termCode zero) (tcFn h)) (liftscT (termCode zero) (tcFn t)))
      =eq consT (liftcT (termCode zero) (tcFn h)) (liftscT (termCode zero) (tcFn t))) :=
    substtc_inv_consT (substtc_inv_liftcT prf_substtc_termCode_nil (substtc_inv_tcFn h))
      (substtc_inv_liftscT prf_substtc_termCode_nil (substtc_inv_tcFn t))
  have hU : ∀ W, Prf (substtc zero W
      (consT (tcFn (liftc zero h)) (liftscT (termCode zero) (tcFn t)))
      =eq consT (tcFn (liftc zero h)) (liftscT (termCode zero) (tcFn t))) :=
    substtc_inv_consT (substtc_inv_tcFn (liftc zero h))
      (substtc_inv_liftscT prf_substtc_termCode_nil (substtc_inv_tcFn t))
  have s1 : Prf (provFromCode (eqc (liftscT (termCode zero) (tcFn (cons h t)))
      (liftscT (termCode zero) (consT (tcFn h) (tcFn t))))) :=
    prf_mp (pcc_congr_liftscT_arg2_code (termCode zero) (tcFn (cons h t))
      (consT (tcFn h) (tcFn t)) prf_substtc_termCode_nil (substtc_inv_tcFn (cons h t)))
      (pcc_dot_cons_symm h t)
  have s2 : Prf (provFromCode (eqc (liftscT (termCode zero) (consT (tcFn h) (tcFn t)))
      (consT (liftcT (termCode zero) (tcFn h)) (liftscT (termCode zero) (tcFn t))))) :=
    pcc_liftsc0_cons_code h t
  have s3 : Prf (provFromCode (eqc
      (consT (liftcT (termCode zero) (tcFn h)) (liftscT (termCode zero) (tcFn t)))
      (consT (tcFn (liftc zero h)) (liftscT (termCode zero) (tcFn t))))) :=
    prf_mp (pcc_congr_consT_arg1_code (liftscT (termCode zero) (tcFn t))
      (liftcT (termCode zero) (tcFn h)) (tcFn (liftc zero h))
      (substtc_inv_liftscT prf_substtc_termCode_nil (substtc_inv_tcFn t))
      (substtc_inv_liftcT prf_substtc_termCode_nil (substtc_inv_tcFn h))) hh
  have s4 : Prf (provFromCode (eqc
      (consT (tcFn (liftc zero h)) (liftscT (termCode zero) (tcFn t)))
      (consT (tcFn (liftc zero h)) (tcFn (liftsc zero t))))) :=
    prf_mp (pcc_congr_consT_arg2_code (tcFn (liftc zero h))
      (liftscT (termCode zero) (tcFn t)) (tcFn (liftsc zero t))
      (substtc_inv_tcFn (liftc zero h))
      (substtc_inv_liftscT prf_substtc_termCode_nil (substtc_inv_tcFn t))) ht
  have s5 : Prf (provFromCode (eqc
      (consT (tcFn (liftc zero h)) (tcFn (liftsc zero t)))
      (tcFn (cons (liftc zero h) (liftsc zero t))))) :=
    pcc_dot_cons (liftc zero h) (liftsc zero t)
  have hchain : Prf (provFromCode (eqc (liftscT (termCode zero) (tcFn (cons h t)))
      (tcFn (cons (liftc zero h) (liftsc zero t))))) :=
    pcc_eq_trans_code _ _ _ hX (by hw_auto) (by hw_auto) (by hw_auto) s1
      (pcc_eq_trans_code _ _ _ hY (by hw_auto) (by hw_auto) (by hw_auto) s2
        (pcc_eq_trans_code _ _ _ hZ (by hw_auto) (by hw_auto) (by hw_auto) s3
          (pcc_eq_trans_code _ _ _ hU (by hw_auto) (by hw_auto) (by hw_auto) s4 s5)))
  exact prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
    (prf_congr_tcFn (prf_eq_symm hplain)))) hchain

/-! ## §7bis · A5 · LAS CUATRO CLAUSULAS A **NIVEL ARBITRARIO**

⭐ Espejo casi literal de §7, con `termCode zero` ↦ `tcFn c` y `prf_substtc_termCode_nil` ↦
`substtc_inv_tcFn c`. Sale tan barato porque **en el sorte TÉRMINO el nivel es un parámetro
INERTE**: `liftc c (funcc s ts) = funcc s (liftsc c ts)` y `liftsc c (cons h t) =
cons (liftc c h) (liftsc c t)` no lo tocan, y sus reflexiones internas
(`pcc_liftc_func_code`, `pcc_liftsc_nil_code`, `pcc_liftsc_cons_code`) ya eran genéricas en
`c` desde §4 — las `pcc_liftc0_*` de §5 son sus instancias `c := zero`.

⚠️ **Lo único que cambia de verdad es el `varc`.** A nivel `zero` la guarda `0 < σa` se
descargaba de una vez (`pcc_zero_lt_succ_code`) y quedaba UNA sola ecuación; al abrir el nivel
la guarda **no se puede descargar**, y hay que abrir la **tricotomía**: dos ramas, cada una con
su ecuación meta distinta (`liftc c (varc a) ≐ varc a` frente a `≐ varc (σa)`) y con su guarda
reflejada dentro de `Prov` por `pcc_lt_tracked`.

⚠️ Y por eso las dos ramas se escriben en **`PrfH`**, no en `Prf`: la disyunción se elimina con
`prf_or_elim`, así que la guarda entra en el CONTEXTO y toda la cadena interna la tiene que
llevar el kit `PrfH_*` (`PrfH_eq_trans_code`, `PrfH_mp_code_apply`, `PrfH_provCode_congr`),
que ya está en producción. -/

/-- El HUECO a nivel abierto — el `v := 0`, `s := #0` de `substF_targetLiftAt`.
    ⚠️ El nivel viaja `liftTerm`‑eado: es un parámetro del hueco, no el agujero. -/
theorem substF_targetLiftAt_hole (c t : Term) :
    substFormula 0 t (targetLiftAt (liftTerm 0 c) (.var 0)) = targetLiftAt c t := by
  simp only [substF_targetLiftAt, FOL.substTerm_liftTerm, substTerm, if_true]

/-- El HUECO de la LISTA, misma forma. -/
theorem substF_targetLiftscAt_hole (c t : Term) :
    substFormula 0 t (targetLiftscAt (liftTerm 0 c) (.var 0)) = targetLiftscAt c t := by
  simp only [substF_targetLiftscAt, FOL.substTerm_liftTerm, substTerm, if_true]

/-- Transporte de Leibniz del objetivo a nivel abierto (espeja `PrfH_congr_targetLift`). -/
theorem PrfH_congr_targetLiftAt {Γ : List Formula} (c : Term) {s s' : Term}
    (h : PrfH Γ (s =eq s')) (ha : PrfH Γ (targetLiftAt c s)) : PrfH Γ (targetLiftAt c s') :=
  (substF_targetLiftAt_hole c s') ▸
    PrfH_leibniz_subst (A := targetLiftAt (liftTerm 0 c) (.var 0)) h
      ((substF_targetLiftAt_hole c s) ▸ ha)

/-! ### Las dos guardas de la tricotomía, reflejadas DENTRO de `Prov`

`pcc_lt_tracked` (completitud‑Δ₀ provable del átomo `<`, con argumentos ABIERTOS) es lo que
convierte la hipótesis META en la premisa que el axioma dotado pide. -/

theorem PrfH_guard_lt_code [AnclaEq] {Γ : List Formula} (a c : Term) (h : PrfH Γ (lt a c)) :
    PrfH Γ (provFromCode (ltCodeFn (tcFn a) (tcFn c))) :=
  PrfH.mp _ _ _ (prf_to_prfH (pcc_lt_tracked a c) Γ) h

theorem PrfH_guard_ge_code [AnclaEq] {Γ : List Formula} (c a : Term) (h : PrfH Γ (lt c (succ a))) :
    PrfH Γ (provFromCode (ltCodeFn (tcFn c) (succcT (tcFn a)))) :=
  PrfH_provCode_congr
    (prf_to_prfH (prf_congr_atom2CodeFn (prf_refl _) (prf_tc_succ' a)) Γ)
    (PrfH.mp _ _ _ (prf_to_prfH (pcc_lt_tracked c (succ a)) Γ) h)

/-- **(1‑at) BASE `varc` A NIVEL ABIERTO** — la única clausula con contenido nuevo.

    ⚠️ **Rompe el patrón `_at` de la familia a propósito**: `refl_caso_varc_at` a secas ya
    existe en `Meta/EvalSubsttcPrf.lean` —otro enunciado, sobre `substtc`— **y está
    exportado a la raíz**, mientras que éste es interno. `Meta/EvalSubstfcPrf.lean` abre
    los dos módulos, así que el nombre corto sería AMBIGUO allí. No revienta hoy porque la
    ambigüedad de `open` en Lean es perezosa — y eso es justo lo que convierte a estos
    homónimos en trampas (B8b). Se desambigua en el origen. -/
theorem refl_caso_varc_lift_at [AnclaEq] (c s a : Term) (hs : Prf (s =eq varc a)) : Prf (targetLiftAt c s) := by
  have hs1 : Prf (provFromCode (eqc (liftcT (tcFn c) (tcFn (varc a)))
      (liftcT (tcFn c) (varcT (tcFn a))))) :=
    prf_mp (pcc_congr_liftcT_arg2_code (tcFn c) (tcFn (varc a)) (varcT (tcFn a))
      (substtc_inv_tcFn c) (substtc_inv_tcFn (varc a))) (pcc_dot_un_symm 0 a)
  have hinvX : ∀ W, Prf (substtc zero W (liftcT (tcFn c) (tcFn (varc a)))
      =eq liftcT (tcFn c) (tcFn (varc a))) :=
    substtc_inv_liftcT (substtc_inv_tcFn c) (substtc_inv_tcFn (varc a))
  have hinvY : ∀ W, Prf (substtc zero W (liftcT (tcFn c) (varcT (tcFn a)))
      =eq liftcT (tcFn c) (varcT (tcFn a))) :=
    substtc_inv_liftcT (substtc_inv_tcFn c) (substtc_inv_unT (substtc_inv_tcFn a))
  refine ROBINSON_PlusPlus.Meta.CantorMonoPrf.prf_or_elim (prf_liftc_varc_cases c a) ?_ ?_
  · -- ▸ RAMA `a < c`: `liftc c (varc a) ≐ varc a`, el nivel NO sube
    refine prf_deduction ?_
    have hplain : PrfH [lt a c] (liftc c (varc a) =eq varc a) :=
      PrfH.mp _ _ _ (prf_to_prfH (prf_liftc_var_lt c a) _) (prfH_hyp_self _)
    have s2 : PrfH [lt a c] (provFromCode (eqc (liftcT (tcFn c) (varcT (tcFn a)))
        (varcT (tcFn a)))) :=
      PrfH_mp_code_apply (prf_to_prfH (pcc_liftc_var_lt_code c a) _)
        (PrfH_guard_lt_code a c (prfH_hyp_self _))
    have s3 : PrfH [lt a c] (provFromCode (eqc (varcT (tcFn a)) (tcFn (varc a)))) :=
      prf_to_prfH (pcc_dot_un 0 a) _
    have hchain : PrfH [lt a c] (provFromCode (eqc (liftcT (tcFn c) (tcFn (varc a)))
        (tcFn (varc a)))) :=
      PrfH_eq_trans_code _ _ _ hinvX (prf_to_prfH hs1 _)
        (PrfH_eq_trans_code _ _ _ hinvY s2 s3 (by hw_auto) (by hw_auto) (by hw_auto))
        (by hw_auto) (by hw_auto) (by hw_auto)
    refine PrfH_congr_targetLiftAt c (prf_to_prfH (prf_eq_symm hs) _) ?_
    exact PrfH_provCode_congr
      (PrfH_congr_eqCodeFn (prf_to_prfH (prf_refl _) _)
        (PrfH_congr_tcFn (PrfH_eq_symm hplain))) hchain
  · -- ▸ RAMA `c < σa`: `liftc c (varc a) ≐ varc (σa)`, el nivel SÍ sube
    refine prf_deduction ?_
    have hplain : PrfH [lt c (succ a)] (liftc c (varc a) =eq varc (succ a)) :=
      PrfH.mp _ _ _ (prf_to_prfH (prf_liftc_var_ge c a) _) (prfH_hyp_self _)
    have s2 : PrfH [lt c (succ a)] (provFromCode (eqc (liftcT (tcFn c) (varcT (tcFn a)))
        (varcT (succcT (tcFn a))))) :=
      PrfH_mp_code_apply (prf_to_prfH (pcc_liftc_var_ge_code c a) _)
        (PrfH_guard_ge_code c a (prfH_hyp_self _))
    have s3 : PrfH [lt c (succ a)] (provFromCode (eqc (varcT (succcT (tcFn a)))
        (tcFn (varc (succ a))))) :=
      prf_to_prfH (prf_mp (prf_provCode_congr (prf_congr_eqCodeFn
        (prf_congr_varcT (prf_tc_succ' a)) (prf_refl _))) (pcc_dot_un 0 (succ a))) _
    have hchain : PrfH [lt c (succ a)] (provFromCode (eqc (liftcT (tcFn c) (tcFn (varc a)))
        (tcFn (varc (succ a))))) :=
      PrfH_eq_trans_code _ _ _ hinvX (prf_to_prfH hs1 _)
        (PrfH_eq_trans_code _ _ _ hinvY s2 s3 (by hw_auto) (by hw_auto) (by hw_auto))
        (by hw_auto) (by hw_auto) (by hw_auto)
    refine PrfH_congr_targetLiftAt c (prf_to_prfH (prf_eq_symm hs) _) ?_
    exact PrfH_provCode_congr
      (PrfH_congr_eqCodeFn (prf_to_prfH (prf_refl _) _)
        (PrfH_congr_tcFn (PrfH_eq_symm hplain))) hchain

/-- **(2‑at) PASO `funcc`** — espejo puro: el nivel viaja intacto al `liftsc`. -/
theorem refl_caso_funcc_at [AnclaEq] (c s p b : Term) (hs : Prf (s =eq funcc p b))
    (hb : Prf (targetLiftscAt c b)) : Prf (targetLiftAt c s) := by
  unfold targetLiftAt
  unfold targetLiftscAt at hb
  have hplain : Prf (liftc c s =eq funcc p (liftsc c b)) :=
    prf_eq_trans (prf_congr_liftc hs) (prf_liftc_func c p b)
  have hX : ∀ W, Prf (substtc zero W (liftcT (tcFn c) (tcFn (funcc p b)))
      =eq liftcT (tcFn c) (tcFn (funcc p b))) :=
    substtc_inv_liftcT (substtc_inv_tcFn c) (substtc_inv_tcFn (funcc p b))
  have hY : ∀ W, Prf (substtc zero W (liftcT (tcFn c) (funccT (tcFn p) (tcFn b)))
      =eq liftcT (tcFn c) (funccT (tcFn p) (tcFn b))) :=
    substtc_inv_liftcT (substtc_inv_tcFn c)
      (substtc_inv_binT (substtc_inv_tcFn p) (substtc_inv_tcFn b))
  have hZ : ∀ W, Prf (substtc zero W (funccT (tcFn p) (liftscT (tcFn c) (tcFn b)))
      =eq funccT (tcFn p) (liftscT (tcFn c) (tcFn b))) :=
    substtc_inv_binT (substtc_inv_tcFn p)
      (substtc_inv_liftscT (substtc_inv_tcFn c) (substtc_inv_tcFn b))
  have s1 : Prf (provFromCode (eqc (liftcT (tcFn c) (tcFn (funcc p b)))
      (liftcT (tcFn c) (funccT (tcFn p) (tcFn b))))) :=
    prf_mp (pcc_congr_liftcT_arg2_code (tcFn c) (tcFn (funcc p b))
      (funccT (tcFn p) (tcFn b)) (substtc_inv_tcFn c) (substtc_inv_tcFn (funcc p b)))
      (pcc_dot_bin_symm 1 p b)
  have s2 : Prf (provFromCode (eqc (liftcT (tcFn c) (funccT (tcFn p) (tcFn b)))
      (funccT (tcFn p) (liftscT (tcFn c) (tcFn b))))) := pcc_liftc_func_code c p b
  have s3 : Prf (provFromCode (eqc (funccT (tcFn p) (liftscT (tcFn c) (tcFn b)))
      (funccT (tcFn p) (tcFn (liftsc c b))))) :=
    prf_mp (pcc_congr_binT_2_code 1 (tcFn p) (liftscT (tcFn c) (tcFn b))
      (tcFn (liftsc c b)) (substtc_inv_tcFn p)
      (substtc_inv_liftscT (substtc_inv_tcFn c) (substtc_inv_tcFn b))) hb
  have s4 : Prf (provFromCode (eqc (funccT (tcFn p) (tcFn (liftsc c b)))
      (tcFn (funcc p (liftsc c b))))) := pcc_dot_bin 1 p (liftsc c b)
  have hchain : Prf (provFromCode (eqc (liftcT (tcFn c) (tcFn (funcc p b)))
      (tcFn (funcc p (liftsc c b))))) :=
    pcc_eq_trans_code _ _ _ hX (by hw_auto) (by hw_auto) (by hw_auto) s1
      (pcc_eq_trans_code _ _ _ hY (by hw_auto) (by hw_auto) (by hw_auto) s2
        (pcc_eq_trans_code _ _ _ hZ (by hw_auto) (by hw_auto) (by hw_auto) s3 s4))
  exact prf_mp (prf_provCode_congr (prf_congr_eqCodeFn
    (prf_congr_liftcT (prf_refl _) (prf_congr_tcFn (prf_eq_symm hs)))
    (prf_congr_tcFn (prf_eq_symm hplain)))) hchain

/-- El puente `termCode nil` ↦ `tcFn nil` de `pcc_liftsc_nil_code`, a nivel abierto. -/
theorem pcc_liftsc_nil_code_at [AnclaEq] (c : Term) :
    Prf (provFromCode (eqCodeFn (liftscT (tcFn c) (tcFn nil)) (tcFn nil))) :=
  prf_mp (prf_provCode_congr (prf_congr_eqCodeFn
      (prf_congr_liftscT (prf_refl _) (prf_eq_symm prf_tc_zero)) (prf_eq_symm prf_tc_zero)))
    (pcc_liftsc_nil_code c)

/-- **(3‑at) BASE de la LISTA (`nil`)** — sin hipótesis, a cualquier nivel. -/
theorem refl_lista_nil_at [AnclaEq] (c : Term) : Prf (targetLiftscAt c nil) := by
  unfold targetLiftscAt
  exact prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
    (prf_congr_tcFn (prf_eq_symm (prf_liftsc_nil c))))) (pcc_liftsc_nil_code_at c)

/-- **(4‑at) PASO de la LISTA (`cons`)** — espejo puro. -/
theorem refl_lista_cons_at [AnclaEq] (c h t : Term) (hh : Prf (targetLiftAt c h))
    (ht : Prf (targetLiftscAt c t)) : Prf (targetLiftscAt c (cons h t)) := by
  unfold targetLiftAt at hh
  unfold targetLiftscAt at ht ⊢
  have hplain : Prf (liftsc c (cons h t) =eq cons (liftc c h) (liftsc c t)) :=
    prf_liftsc_cons c h t
  have hX : ∀ W, Prf (substtc zero W (liftscT (tcFn c) (tcFn (cons h t)))
      =eq liftscT (tcFn c) (tcFn (cons h t))) :=
    substtc_inv_liftscT (substtc_inv_tcFn c) (substtc_inv_tcFn (cons h t))
  have hY : ∀ W, Prf (substtc zero W (liftscT (tcFn c) (consT (tcFn h) (tcFn t)))
      =eq liftscT (tcFn c) (consT (tcFn h) (tcFn t))) :=
    substtc_inv_liftscT (substtc_inv_tcFn c)
      (substtc_inv_consT (substtc_inv_tcFn h) (substtc_inv_tcFn t))
  have hZ : ∀ W, Prf (substtc zero W
      (consT (liftcT (tcFn c) (tcFn h)) (liftscT (tcFn c) (tcFn t)))
      =eq consT (liftcT (tcFn c) (tcFn h)) (liftscT (tcFn c) (tcFn t))) :=
    substtc_inv_consT (substtc_inv_liftcT (substtc_inv_tcFn c) (substtc_inv_tcFn h))
      (substtc_inv_liftscT (substtc_inv_tcFn c) (substtc_inv_tcFn t))
  have hU : ∀ W, Prf (substtc zero W
      (consT (tcFn (liftc c h)) (liftscT (tcFn c) (tcFn t)))
      =eq consT (tcFn (liftc c h)) (liftscT (tcFn c) (tcFn t))) :=
    substtc_inv_consT (substtc_inv_tcFn (liftc c h))
      (substtc_inv_liftscT (substtc_inv_tcFn c) (substtc_inv_tcFn t))
  have s1 : Prf (provFromCode (eqc (liftscT (tcFn c) (tcFn (cons h t)))
      (liftscT (tcFn c) (consT (tcFn h) (tcFn t))))) :=
    prf_mp (pcc_congr_liftscT_arg2_code (tcFn c) (tcFn (cons h t))
      (consT (tcFn h) (tcFn t)) (substtc_inv_tcFn c) (substtc_inv_tcFn (cons h t)))
      (pcc_dot_cons_symm h t)
  have s2 : Prf (provFromCode (eqc (liftscT (tcFn c) (consT (tcFn h) (tcFn t)))
      (consT (liftcT (tcFn c) (tcFn h)) (liftscT (tcFn c) (tcFn t))))) :=
    pcc_liftsc_cons_code c h t
  have s3 : Prf (provFromCode (eqc
      (consT (liftcT (tcFn c) (tcFn h)) (liftscT (tcFn c) (tcFn t)))
      (consT (tcFn (liftc c h)) (liftscT (tcFn c) (tcFn t))))) :=
    prf_mp (pcc_congr_consT_arg1_code (liftscT (tcFn c) (tcFn t))
      (liftcT (tcFn c) (tcFn h)) (tcFn (liftc c h))
      (substtc_inv_liftscT (substtc_inv_tcFn c) (substtc_inv_tcFn t))
      (substtc_inv_liftcT (substtc_inv_tcFn c) (substtc_inv_tcFn h))) hh
  have s4 : Prf (provFromCode (eqc
      (consT (tcFn (liftc c h)) (liftscT (tcFn c) (tcFn t)))
      (consT (tcFn (liftc c h)) (tcFn (liftsc c t))))) :=
    prf_mp (pcc_congr_consT_arg2_code (tcFn (liftc c h))
      (liftscT (tcFn c) (tcFn t)) (tcFn (liftsc c t))
      (substtc_inv_tcFn (liftc c h))
      (substtc_inv_liftscT (substtc_inv_tcFn c) (substtc_inv_tcFn t))) ht
  have s5 : Prf (provFromCode (eqc
      (consT (tcFn (liftc c h)) (tcFn (liftsc c t)))
      (tcFn (cons (liftc c h) (liftsc c t))))) :=
    pcc_dot_cons (liftc c h) (liftsc c t)
  have hchain : Prf (provFromCode (eqc (liftscT (tcFn c) (tcFn (cons h t)))
      (tcFn (cons (liftc c h) (liftsc c t))))) :=
    pcc_eq_trans_code _ _ _ hX (by hw_auto) (by hw_auto) (by hw_auto) s1
      (pcc_eq_trans_code _ _ _ hY (by hw_auto) (by hw_auto) (by hw_auto) s2
        (pcc_eq_trans_code _ _ _ hZ (by hw_auto) (by hw_auto) (by hw_auto) s3
          (pcc_eq_trans_code _ _ _ hU (by hw_auto) (by hw_auto) (by hw_auto) s4 s5)))
  exact prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
    (prf_congr_tcFn (prf_eq_symm hplain)))) hchain

/-! ### NO VACUIDAD a nivel abierto: las cuatro clausulas `_at` cubren todo código GENUINO -/

mutual
theorem refl_termCode_at [AnclaEq] (c : Term) : ∀ t : Term, Prf (targetLiftAt c (termCode t))
  | .var n     => refl_caso_varc_lift_at c (termCode (.var n)) (numeral n) (prf_refl _)
  | .func f ts =>
      refl_caso_funcc_at c (termCode (.func f ts)) (strCode f) (termsCode ts)
        (prf_refl _) (refl_termsCode_at c ts)
theorem refl_termsCode_at [AnclaEq] (c : Term) : ∀ ts : List Term, Prf (targetLiftscAt c (termsCode ts))
  | []      => refl_lista_nil_at c
  | t :: ts =>
      refl_lista_cons_at c (termCode t) (termsCode ts)
        (refl_termCode_at c t) (refl_termsCode_at c ts)
end

/-! ## §8 · NO VACUIDAD / COMPLETITUD DEL ESQUEMA — las cuatro clausulas CIERRAN el objetivo
       para todo codigo de termino GENUINO (`termCode t`), por recursion META.

    No es el teorema que hace falta (ahi `s` es abstracto), pero comprueba que las cuatro
    clausulas son un CUBRIMIENTO COMPLETO: no falta ninguna forma. -/

mutual
theorem refl_termCode [AnclaEq] : ∀ t : Term, Prf (targetLift (termCode t))
  | .var n     => refl_caso_varc (termCode (.var n)) (numeral n) (prf_refl _)
  | .func f ts =>
      refl_caso_funcc (termCode (.func f ts)) (strCode f) (termsCode ts)
        (prf_refl _) (refl_termsCode ts)
theorem refl_termsCode [AnclaEq] : ∀ ts : List Term, Prf (targetLiftsc (termsCode ts))
  | []      => refl_lista_nil
  | t :: ts => refl_lista_cons (termCode t) (termsCode ts) (refl_termCode t) (refl_termsCode ts)
end

/-! ## §9 · LA FORMA ECUACIONAL DE LA GUARDA ES *EXACTAMENTE* LO QUE PIDEN LAS CLAUSULAS

    `shapeUn`/`shapeBin` son los de PRODUCCION: se DECLARAN en `Minimal/Axioms.lean`
    (ADR-020, bajaron con las guardas) y `CodeWitnessPrf.SinWTs` los re-exporta, asi que el
    nombre cualificado de siempre sigue valiendo. Aqui NO se redefinen, se abren selectivamente. `shapeUn X 0` y `shapeBin X 1`
    son, **por `rfl`**, las dos ecuaciones que consumen `refl_caso_varc`/`refl_caso_funcc`. -/

theorem shapeUn0_es_varc (X : Term) :
    shapeUn X 0 = Formula.eq X (varc (nthc X (numeralM 1))) := rfl
theorem shapeBin1_es_funcc (X : Term) :
    shapeBin X 1 = Formula.eq X (funcc (nthc X (numeralM 1)) (nthc X (numeralM 2))) := rfl

/-! ### La guarda llega como HIPOTESIS OBJETO, no como `Prf`: el transporte de Leibniz -/

mutual
theorem substTerm_termCode (v : Nat) (u : Term) :
    ∀ t : Term, substTerm v u (termCode t) = termCode t
  | .var _ => by simp only [termCode, cons, nil, zero, substTerm, substTerms, substTerm_numeral]
  | .func s ts => by
      simp only [termCode, cons, nil, zero, substTerm, substTerms, substTerm_numeral,
        substTerm_strCode, substTerm_termsCode v u ts]
theorem substTerm_termsCode (v : Nat) (u : Term) :
    ∀ ts : List Term, substTerm v u (termsCode ts) = termsCode ts
  | []      => rfl
  | t :: ts => by
      simp only [termsCode, cons, substTerm, substTerms, substTerm_termCode v u t,
        substTerm_termsCode v u ts]
end

/-- **`formCode φ` es CERRADO también bajo `substTerm`** — el gemelo del `liftTerm_formCode` de
    `DerivCondPrf`, que sí existía.

    ⚠️ Vive **aquí y no allí** por dependencia, no por tema: necesita `substTerm_termCode` /
    `substTerm_termsCode`, que están en este módulo, y `DerivCondPrf` está **aguas arriba**
    (ADR‑019: no se sube el corolario, y bajar la pareja obligaría a mover tres lemas y
    reescribir sus referencias en un módulo de la ruta crítica). Se deja medido en vez de
    duplicarlo.

    Lo pide `D3ChainDotPrf` §10 para la naturalidad del `PsiF` dotado. -/
theorem substTerm_formCode (v : Nat) (u : Term) :
    ∀ φ : Formula, substTerm v u (formCode φ) = formCode φ
  | .bottom => by simp only [formCode, cons, nil, zero, substTerm, substTerms, substTerm_numeral]
  | .atom _ _ => by
      simp only [formCode, cons, nil, zero, substTerm, substTerms, substTerm_numeral,
        substTerm_strCode, substTerm_termsCode]
  | .eq _ _ => by
      simp only [formCode, cons, nil, zero, substTerm, substTerms, substTerm_numeral,
        substTerm_termCode]
  | .impl a b => by
      simp only [formCode, cons, nil, zero, substTerm, substTerms, substTerm_numeral,
        substTerm_formCode v u a, substTerm_formCode v u b]
  | Formula.forall a => by
      simp only [formCode, cons, nil, zero, substTerm, substTerms, substTerm_numeral,
        substTerm_formCode v u a]
  | .and a b => by
      simp only [formCode, cons, nil, zero, substTerm, substTerms, substTerm_numeral,
        substTerm_formCode v u a, substTerm_formCode v u b]
  | .or a b => by
      simp only [formCode, cons, nil, zero, substTerm, substTerms, substTerm_numeral,
        substTerm_formCode v u a, substTerm_formCode v u b]
  | .ex a => by
      simp only [formCode, cons, nil, zero, substTerm, substTerms, substTerm_numeral,
        substTerm_formCode v u a]

/-- **`substFormula` atraviesa `targetLift`**, en su forma GENERAL: cae sobre el argumento.

    ⚠️ Bajado desde `sondeos/DescensoLiftc.lean` al promover `Meta/EvalLiftcPrf.lean`
    (2026‑09‑04). **Tuvo que bajar AQUI, no quedarse arriba**: `EvalLiftcPrf` importa a este
    modulo, asi que reescribir `substF_targetLift_hole` como corolario de un lema de alli
    seria un CICLO. Y el `_hole` se consume dentro de este mismo fichero —dos veces en
    `PrfH_congr_targetLift`, mas el bloque `export`—, asi que no podia simplemente irse.

    ⚠️ Se cita por NOMBRE y no por numero de linea a proposito: la version anterior de este
    docstring daba tres numeros y los TRES eran falsos — se copiaron de un parche escrito
    antes de que el fichero creciera, y dos de ellos caian en lineas que no son consumidores
    (un `simp only` de otra prueba y una linea de docstring). Los nombres no derivan. -/
theorem substF_targetLift (v : Nat) (u s : Term) :
    substFormula v u (targetLift s) = targetLift (substTerm v u s) := by
  simp only [targetLift, substFormula_provFromCode_open, eqc, liftcT, funcc, tcFn, liftc,
    cons, nil, zero, succ, substTerm, substTerms, substTerm_termCode, substTerm_strCode]

/-- La companera sobre LISTAS, mismo footprint. -/
theorem substF_targetLiftsc (v : Nat) (u s : Term) :
    substFormula v u (targetLiftsc s) = targetLiftsc (substTerm v u s) := by
  simp only [targetLiftsc, substFormula_provFromCode_open, eqc, liftscT, funcc, tcFn, liftsc,
    cons, nil, zero, succ, substTerm, substTerms, substTerm_termCode, substTerm_strCode]

/-- El HUECO: el caso `v := 0`, `s := #0` del general. Instancia DEFEQ, sin conversion.
    Se conserva el nombre porque lo consumen `:799`, `:802` y el `export`. -/
theorem substF_targetLift_hole (t : Term) :
    substFormula 0 t (provFromCode (eqc (liftcT (termCode zero) (tcFn (.var 0)))
        (tcFn (liftc zero (.var 0)))))
      = targetLift t :=
  substF_targetLift 0 t (.var 0)

theorem PrfH_congr_targetLift {Γ : List Formula} {s s' : Term} (h : PrfH Γ (s =eq s'))
    (ha : PrfH Γ (targetLift s)) : PrfH Γ (targetLift s') :=
  (substF_targetLift_hole s') ▸
    PrfH_leibniz_subst
      (A := provFromCode (eqc (liftcT (termCode zero) (tcFn (.var 0)))
        (tcFn (liftc zero (.var 0))))) h ((substF_targetLift_hole s) ▸ ha)

/-- **EL DISYUNTO `varc`, EN LA MONEDA QUE PIDE LA INDUCCION OBJETO** (implicacion interna,
    guarda como HIPOTESIS): `⊢ shapeUn X 0 ⇒ targetLift X`. CERRADO, sin hipotesis. -/
theorem refl_shapeUn_imp [AnclaEq] (X : Term) : Prf (Formula.impl (shapeUn X 0) (targetLift X)) := by
  refine prf_deduction ?_
  let a : Term := nthc X (numeralM 1)
  have hh : PrfH [shapeUn X 0] (Formula.eq X (varc a)) := prfH_hyp_self _
  exact PrfH_congr_targetLift (PrfH_eq_symm hh)
    (prf_to_prfH (refl_caso_varc (varc a) a (prf_refl _)) _)

/-! ### El disyunto `funcc`: la HI llega tambien como hipotesis OBJETO.

    La transitividad interna en contexto `PrfH` es `PrfH_eq_trans_code`, que YA esta en
    produccion (`Meta/EvalCarcNthcPrf.lean:66`, exportado a la raiz). No se redefine. -/

/-- **(2') PASO `funcc`, en forma IMPLICACION**: la companera de la lista entra como
    hipotesis OBJETO. Es la moneda que consume una induccion objeto. -/
theorem refl_caso_funcc_imp [AnclaEq] (p b : Term) :
    Prf (Formula.impl (targetLiftsc b) (targetLift (funcc p b))) := by
  refine prf_deduction ?_
  have hb : PrfH [targetLiftsc b] (targetLiftsc b) := prfH_hyp_self _
  have hX : ∀ W, Prf (substtc zero W (liftcT (termCode zero) (tcFn (funcc p b)))
      =eq liftcT (termCode zero) (tcFn (funcc p b))) :=
    substtc_inv_liftcT prf_substtc_termCode_nil (substtc_inv_tcFn (funcc p b))
  have hY : ∀ W, Prf (substtc zero W (liftcT (termCode zero) (funccT (tcFn p) (tcFn b)))
      =eq liftcT (termCode zero) (funccT (tcFn p) (tcFn b))) :=
    substtc_inv_liftcT prf_substtc_termCode_nil (substtc_inv_binT (substtc_inv_tcFn p) (substtc_inv_tcFn b))
  have hZ : ∀ W, Prf (substtc zero W (funccT (tcFn p) (liftscT (termCode zero) (tcFn b)))
      =eq funccT (tcFn p) (liftscT (termCode zero) (tcFn b))) :=
    substtc_inv_binT (substtc_inv_tcFn p) (substtc_inv_liftscT prf_substtc_termCode_nil (substtc_inv_tcFn b))
  have s1 : PrfH [targetLiftsc b] (provFromCode (eqc
      (liftcT (termCode zero) (tcFn (funcc p b)))
      (liftcT (termCode zero) (funccT (tcFn p) (tcFn b))))) :=
    prf_to_prfH (prf_mp (pcc_congr_liftcT_arg2_code (termCode zero) (tcFn (funcc p b))
      (funccT (tcFn p) (tcFn b)) prf_substtc_termCode_nil (substtc_inv_tcFn (funcc p b)))
      (pcc_dot_bin_symm 1 p b)) _
  have s2 : PrfH [targetLiftsc b] (provFromCode (eqc
      (liftcT (termCode zero) (funccT (tcFn p) (tcFn b)))
      (funccT (tcFn p) (liftscT (termCode zero) (tcFn b))))) :=
    prf_to_prfH (pcc_liftc0_func_code p b) _
  have s3 : PrfH [targetLiftsc b] (provFromCode (eqc
      (funccT (tcFn p) (liftscT (termCode zero) (tcFn b)))
      (funccT (tcFn p) (tcFn (liftsc zero b))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_binT_2_code 1 (tcFn p)
      (liftscT (termCode zero) (tcFn b)) (tcFn (liftsc zero b)) (substtc_inv_tcFn p)
      (substtc_inv_liftscT prf_substtc_termCode_nil (substtc_inv_tcFn b))) _) hb
  have s4 : PrfH [targetLiftsc b] (provFromCode (eqc
      (funccT (tcFn p) (tcFn (liftsc zero b))) (tcFn (funcc p (liftsc zero b))))) :=
    prf_to_prfH (pcc_dot_bin 1 p (liftsc zero b)) _
  have hchain : PrfH [targetLiftsc b] (provFromCode (eqc
      (liftcT (termCode zero) (tcFn (funcc p b))) (tcFn (funcc p (liftsc zero b))))) :=
    PrfH_eq_trans_code _ _ _ hX s1
      (PrfH_eq_trans_code _ _ _ hY s2
        (PrfH_eq_trans_code _ _ _ hZ s3 s4
          (by hw_auto) (by hw_auto) (by hw_auto))
        (by hw_auto) (by hw_auto) (by hw_auto))
      (by hw_auto) (by hw_auto) (by hw_auto)
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
    (prf_congr_tcFn (prf_eq_symm (prf_liftc_func zero p b))))) _) hchain

/-- **EL DISYUNTO `funcc`, EN LA MONEDA DE LA INDUCCION OBJETO**:
    `⊢ (shapeBin X 1 ∧ targetLiftsc (nthc X 2̄)) ⇒ targetLift X`. -/
theorem refl_shapeBin_imp [AnclaEq] (X : Term) :
    Prf (Formula.impl (land (shapeBin X 1) (targetLiftsc (nthc X (numeralM 2))))
      (targetLift X)) := by
  refine prf_deduction ?_
  let p : Term := nthc X (numeralM 1)
  let b : Term := nthc X (numeralM 2)
  let H : Formula := land (shapeBin X 1) (targetLiftsc b)
  have hh : PrfH [H] H := prfH_hyp_self _
  have hs : PrfH [H] (Formula.eq X (funcc p b)) := PrfH_and_elim_left hh
  have hb : PrfH [H] (targetLiftsc b) := PrfH_and_elim_right hh
  have hfb : PrfH [H] (targetLift (funcc p b)) :=
    PrfH.mp _ _ _ (prf_to_prfH (refl_caso_funcc_imp p b) _) hb
  exact PrfH_congr_targetLift (PrfH_eq_symm hs) hfb

/-- **(4') PASO de la LISTA, en forma IMPLICACION.** -/
theorem refl_lista_cons_imp [AnclaEq] (h t : Term) :
    Prf (Formula.impl (land (targetLift h) (targetLiftsc t)) (targetLiftsc (cons h t))) := by
  refine prf_deduction ?_
  let H : Formula := land (targetLift h) (targetLiftsc t)
  have hh0 : PrfH [H] H := prfH_hyp_self _
  have hh : PrfH [H] (targetLift h) := PrfH_and_elim_left hh0
  have ht : PrfH [H] (targetLiftsc t) := PrfH_and_elim_right hh0
  have hX : ∀ W, Prf (substtc zero W (liftscT (termCode zero) (tcFn (cons h t)))
      =eq liftscT (termCode zero) (tcFn (cons h t))) :=
    substtc_inv_liftscT prf_substtc_termCode_nil (substtc_inv_tcFn (cons h t))
  have hY : ∀ W, Prf (substtc zero W (liftscT (termCode zero) (consT (tcFn h) (tcFn t)))
      =eq liftscT (termCode zero) (consT (tcFn h) (tcFn t))) :=
    substtc_inv_liftscT prf_substtc_termCode_nil (substtc_inv_consT (substtc_inv_tcFn h) (substtc_inv_tcFn t))
  have hZ : ∀ W, Prf (substtc zero W
      (consT (liftcT (termCode zero) (tcFn h)) (liftscT (termCode zero) (tcFn t)))
      =eq consT (liftcT (termCode zero) (tcFn h)) (liftscT (termCode zero) (tcFn t))) :=
    substtc_inv_consT (substtc_inv_liftcT prf_substtc_termCode_nil (substtc_inv_tcFn h))
      (substtc_inv_liftscT prf_substtc_termCode_nil (substtc_inv_tcFn t))
  have hU : ∀ W, Prf (substtc zero W
      (consT (tcFn (liftc zero h)) (liftscT (termCode zero) (tcFn t)))
      =eq consT (tcFn (liftc zero h)) (liftscT (termCode zero) (tcFn t))) :=
    substtc_inv_consT (substtc_inv_tcFn (liftc zero h))
      (substtc_inv_liftscT prf_substtc_termCode_nil (substtc_inv_tcFn t))
  have s1 : PrfH [H] (provFromCode (eqc (liftscT (termCode zero) (tcFn (cons h t)))
      (liftscT (termCode zero) (consT (tcFn h) (tcFn t))))) :=
    prf_to_prfH (prf_mp (pcc_congr_liftscT_arg2_code (termCode zero) (tcFn (cons h t))
      (consT (tcFn h) (tcFn t)) prf_substtc_termCode_nil (substtc_inv_tcFn (cons h t)))
      (pcc_dot_cons_symm h t)) _
  have s2 : PrfH [H] (provFromCode (eqc (liftscT (termCode zero) (consT (tcFn h) (tcFn t)))
      (consT (liftcT (termCode zero) (tcFn h)) (liftscT (termCode zero) (tcFn t))))) :=
    prf_to_prfH (pcc_liftsc0_cons_code h t) _
  have s3 : PrfH [H] (provFromCode (eqc
      (consT (liftcT (termCode zero) (tcFn h)) (liftscT (termCode zero) (tcFn t)))
      (consT (tcFn (liftc zero h)) (liftscT (termCode zero) (tcFn t))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_consT_arg1_code (liftscT (termCode zero) (tcFn t))
      (liftcT (termCode zero) (tcFn h)) (tcFn (liftc zero h))
      (substtc_inv_liftscT prf_substtc_termCode_nil (substtc_inv_tcFn t))
      (substtc_inv_liftcT prf_substtc_termCode_nil (substtc_inv_tcFn h))) _) hh
  have s4 : PrfH [H] (provFromCode (eqc
      (consT (tcFn (liftc zero h)) (liftscT (termCode zero) (tcFn t)))
      (consT (tcFn (liftc zero h)) (tcFn (liftsc zero t))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_consT_arg2_code (tcFn (liftc zero h))
      (liftscT (termCode zero) (tcFn t)) (tcFn (liftsc zero t))
      (substtc_inv_tcFn (liftc zero h))
      (substtc_inv_liftscT prf_substtc_termCode_nil (substtc_inv_tcFn t))) _) ht
  have s5 : PrfH [H] (provFromCode (eqc
      (consT (tcFn (liftc zero h)) (tcFn (liftsc zero t)))
      (tcFn (cons (liftc zero h) (liftsc zero t))))) :=
    prf_to_prfH (pcc_dot_cons (liftc zero h) (liftsc zero t)) _
  have hchain : PrfH [H] (provFromCode (eqc (liftscT (termCode zero) (tcFn (cons h t)))
      (tcFn (cons (liftc zero h) (liftsc zero t))))) :=
    PrfH_eq_trans_code _ _ _ hX s1
      (PrfH_eq_trans_code _ _ _ hY s2
        (PrfH_eq_trans_code _ _ _ hZ s3
          (PrfH_eq_trans_code _ _ _ hU s4 s5
            (by hw_auto) (by hw_auto) (by hw_auto))
          (by hw_auto) (by hw_auto) (by hw_auto))
        (by hw_auto) (by hw_auto) (by hw_auto))
      (by hw_auto) (by hw_auto) (by hw_auto)
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
    (prf_congr_tcFn (prf_eq_symm (prf_liftsc_cons zero h t))))) _) hchain

/-! ## §9bis · A5 · LAS CUATRO CLAUSULAS EN LA **MONEDA DE LA INDUCCION OBJETO**

Espejo de §9 con el nivel abierto. ⚠️ Hay que reescribir las cadenas (no basta invocar §7bis):
la HI llega como hipótesis **OBJETO**, y sin `PrfH_mono` (deuda B6b) una premisa `Prf` no vale.
Por eso `refl_caso_funcc_imp_at` y `refl_lista_cons_imp_at` repiten la cadena en `PrfH`, igual
que hacen sus originales a nivel `zero`.

⭐ En cambio `refl_shapeUn_imp_at` y `refl_shapeBin_imp_at` sí son de una línea: la guarda
`shapeUn X 0` / `shapeBin X 1` es una ECUACION, y el transporte es Leibniz. -/

/-- La compañera sobre LISTAS del transporte de §7bis. -/
theorem PrfH_congr_targetLiftscAt {Γ : List Formula} (c : Term) {s s' : Term}
    (h : PrfH Γ (s =eq s')) (ha : PrfH Γ (targetLiftscAt c s)) : PrfH Γ (targetLiftscAt c s') :=
  (substF_targetLiftscAt_hole c s') ▸
    PrfH_leibniz_subst (A := targetLiftscAt (liftTerm 0 c) (.var 0)) h
      ((substF_targetLiftscAt_hole c s) ▸ ha)

/-- **EL DISYUNTO `varc` A NIVEL ABIERTO**: `⊢ shapeUn X 0 ⇒ targetLiftAt c X`. -/
theorem refl_shapeUn_imp_at [AnclaEq] (c X : Term) :
    Prf (Formula.impl (shapeUn X 0) (targetLiftAt c X)) := by
  refine prf_deduction ?_
  let a : Term := nthc X (numeralM 1)
  have hh : PrfH [shapeUn X 0] (Formula.eq X (varc a)) := prfH_hyp_self _
  exact PrfH_congr_targetLiftAt c (PrfH_eq_symm hh)
    (prf_to_prfH (refl_caso_varc_lift_at c (varc a) a (prf_refl _)) _)

/-- **(2'‑at) PASO `funcc`, en forma IMPLICACION**, con el nivel abierto. -/
theorem refl_caso_funcc_imp_at [AnclaEq] (c p b : Term) :
    Prf (Formula.impl (targetLiftscAt c b) (targetLiftAt c (funcc p b))) := by
  refine prf_deduction ?_
  have hb : PrfH [targetLiftscAt c b] (targetLiftscAt c b) := prfH_hyp_self _
  have hX : ∀ W, Prf (substtc zero W (liftcT (tcFn c) (tcFn (funcc p b)))
      =eq liftcT (tcFn c) (tcFn (funcc p b))) :=
    substtc_inv_liftcT (substtc_inv_tcFn c) (substtc_inv_tcFn (funcc p b))
  have hY : ∀ W, Prf (substtc zero W (liftcT (tcFn c) (funccT (tcFn p) (tcFn b)))
      =eq liftcT (tcFn c) (funccT (tcFn p) (tcFn b))) :=
    substtc_inv_liftcT (substtc_inv_tcFn c)
      (substtc_inv_binT (substtc_inv_tcFn p) (substtc_inv_tcFn b))
  have hZ : ∀ W, Prf (substtc zero W (funccT (tcFn p) (liftscT (tcFn c) (tcFn b)))
      =eq funccT (tcFn p) (liftscT (tcFn c) (tcFn b))) :=
    substtc_inv_binT (substtc_inv_tcFn p)
      (substtc_inv_liftscT (substtc_inv_tcFn c) (substtc_inv_tcFn b))
  have s1 : PrfH [targetLiftscAt c b] (provFromCode (eqc
      (liftcT (tcFn c) (tcFn (funcc p b)))
      (liftcT (tcFn c) (funccT (tcFn p) (tcFn b))))) :=
    prf_to_prfH (prf_mp (pcc_congr_liftcT_arg2_code (tcFn c) (tcFn (funcc p b))
      (funccT (tcFn p) (tcFn b)) (substtc_inv_tcFn c) (substtc_inv_tcFn (funcc p b)))
      (pcc_dot_bin_symm 1 p b)) _
  have s2 : PrfH [targetLiftscAt c b] (provFromCode (eqc
      (liftcT (tcFn c) (funccT (tcFn p) (tcFn b)))
      (funccT (tcFn p) (liftscT (tcFn c) (tcFn b))))) :=
    prf_to_prfH (pcc_liftc_func_code c p b) _
  have s3 : PrfH [targetLiftscAt c b] (provFromCode (eqc
      (funccT (tcFn p) (liftscT (tcFn c) (tcFn b)))
      (funccT (tcFn p) (tcFn (liftsc c b))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_binT_2_code 1 (tcFn p)
      (liftscT (tcFn c) (tcFn b)) (tcFn (liftsc c b)) (substtc_inv_tcFn p)
      (substtc_inv_liftscT (substtc_inv_tcFn c) (substtc_inv_tcFn b))) _) hb
  have s4 : PrfH [targetLiftscAt c b] (provFromCode (eqc
      (funccT (tcFn p) (tcFn (liftsc c b))) (tcFn (funcc p (liftsc c b))))) :=
    prf_to_prfH (pcc_dot_bin 1 p (liftsc c b)) _
  have hchain : PrfH [targetLiftscAt c b] (provFromCode (eqc
      (liftcT (tcFn c) (tcFn (funcc p b))) (tcFn (funcc p (liftsc c b))))) :=
    PrfH_eq_trans_code _ _ _ hX s1
      (PrfH_eq_trans_code _ _ _ hY s2
        (PrfH_eq_trans_code _ _ _ hZ s3 s4
          (by hw_auto) (by hw_auto) (by hw_auto))
        (by hw_auto) (by hw_auto) (by hw_auto))
      (by hw_auto) (by hw_auto) (by hw_auto)
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
    (prf_congr_tcFn (prf_eq_symm (prf_liftc_func c p b))))) _) hchain

/-- **EL DISYUNTO `funcc` A NIVEL ABIERTO**, en la moneda de la inducción objeto. -/
theorem refl_shapeBin_imp_at [AnclaEq] (c X : Term) :
    Prf (Formula.impl (land (shapeBin X 1) (targetLiftscAt c (nthc X (numeralM 2))))
      (targetLiftAt c X)) := by
  refine prf_deduction ?_
  let p : Term := nthc X (numeralM 1)
  let b : Term := nthc X (numeralM 2)
  let H : Formula := land (shapeBin X 1) (targetLiftscAt c b)
  have hh : PrfH [H] H := prfH_hyp_self _
  have hs : PrfH [H] (Formula.eq X (funcc p b)) := PrfH_and_elim_left hh
  have hb : PrfH [H] (targetLiftscAt c b) := PrfH_and_elim_right hh
  have hfb : PrfH [H] (targetLiftAt c (funcc p b)) :=
    PrfH.mp _ _ _ (prf_to_prfH (refl_caso_funcc_imp_at c p b) _) hb
  exact PrfH_congr_targetLiftAt c (PrfH_eq_symm hs) hfb

/-- **(4'‑at) PASO de la LISTA, en forma IMPLICACION**, con el nivel abierto. -/
theorem refl_lista_cons_imp_at [AnclaEq] (c h t : Term) :
    Prf (Formula.impl (land (targetLiftAt c h) (targetLiftscAt c t))
      (targetLiftscAt c (cons h t))) := by
  refine prf_deduction ?_
  let H : Formula := land (targetLiftAt c h) (targetLiftscAt c t)
  have hh0 : PrfH [H] H := prfH_hyp_self _
  have hh : PrfH [H] (targetLiftAt c h) := PrfH_and_elim_left hh0
  have ht : PrfH [H] (targetLiftscAt c t) := PrfH_and_elim_right hh0
  have hX : ∀ W, Prf (substtc zero W (liftscT (tcFn c) (tcFn (cons h t)))
      =eq liftscT (tcFn c) (tcFn (cons h t))) :=
    substtc_inv_liftscT (substtc_inv_tcFn c) (substtc_inv_tcFn (cons h t))
  have hY : ∀ W, Prf (substtc zero W (liftscT (tcFn c) (consT (tcFn h) (tcFn t)))
      =eq liftscT (tcFn c) (consT (tcFn h) (tcFn t))) :=
    substtc_inv_liftscT (substtc_inv_tcFn c)
      (substtc_inv_consT (substtc_inv_tcFn h) (substtc_inv_tcFn t))
  have hZ : ∀ W, Prf (substtc zero W
      (consT (liftcT (tcFn c) (tcFn h)) (liftscT (tcFn c) (tcFn t)))
      =eq consT (liftcT (tcFn c) (tcFn h)) (liftscT (tcFn c) (tcFn t))) :=
    substtc_inv_consT (substtc_inv_liftcT (substtc_inv_tcFn c) (substtc_inv_tcFn h))
      (substtc_inv_liftscT (substtc_inv_tcFn c) (substtc_inv_tcFn t))
  have hU : ∀ W, Prf (substtc zero W
      (consT (tcFn (liftc c h)) (liftscT (tcFn c) (tcFn t)))
      =eq consT (tcFn (liftc c h)) (liftscT (tcFn c) (tcFn t))) :=
    substtc_inv_consT (substtc_inv_tcFn (liftc c h))
      (substtc_inv_liftscT (substtc_inv_tcFn c) (substtc_inv_tcFn t))
  have s1 : PrfH [H] (provFromCode (eqc (liftscT (tcFn c) (tcFn (cons h t)))
      (liftscT (tcFn c) (consT (tcFn h) (tcFn t))))) :=
    prf_to_prfH (prf_mp (pcc_congr_liftscT_arg2_code (tcFn c) (tcFn (cons h t))
      (consT (tcFn h) (tcFn t)) (substtc_inv_tcFn c) (substtc_inv_tcFn (cons h t)))
      (pcc_dot_cons_symm h t)) _
  have s2 : PrfH [H] (provFromCode (eqc (liftscT (tcFn c) (consT (tcFn h) (tcFn t)))
      (consT (liftcT (tcFn c) (tcFn h)) (liftscT (tcFn c) (tcFn t))))) :=
    prf_to_prfH (pcc_liftsc_cons_code c h t) _
  have s3 : PrfH [H] (provFromCode (eqc
      (consT (liftcT (tcFn c) (tcFn h)) (liftscT (tcFn c) (tcFn t)))
      (consT (tcFn (liftc c h)) (liftscT (tcFn c) (tcFn t))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_consT_arg1_code (liftscT (tcFn c) (tcFn t))
      (liftcT (tcFn c) (tcFn h)) (tcFn (liftc c h))
      (substtc_inv_liftscT (substtc_inv_tcFn c) (substtc_inv_tcFn t))
      (substtc_inv_liftcT (substtc_inv_tcFn c) (substtc_inv_tcFn h))) _) hh
  have s4 : PrfH [H] (provFromCode (eqc
      (consT (tcFn (liftc c h)) (liftscT (tcFn c) (tcFn t)))
      (consT (tcFn (liftc c h)) (tcFn (liftsc c t))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_consT_arg2_code (tcFn (liftc c h))
      (liftscT (tcFn c) (tcFn t)) (tcFn (liftsc c t))
      (substtc_inv_tcFn (liftc c h))
      (substtc_inv_liftscT (substtc_inv_tcFn c) (substtc_inv_tcFn t))) _) ht
  have s5 : PrfH [H] (provFromCode (eqc
      (consT (tcFn (liftc c h)) (tcFn (liftsc c t)))
      (tcFn (cons (liftc c h) (liftsc c t))))) :=
    prf_to_prfH (pcc_dot_cons (liftc c h) (liftsc c t)) _
  have hchain : PrfH [H] (provFromCode (eqc (liftscT (tcFn c) (tcFn (cons h t)))
      (tcFn (cons (liftc c h) (liftsc c t))))) :=
    PrfH_eq_trans_code _ _ _ hX s1
      (PrfH_eq_trans_code _ _ _ hY s2
        (PrfH_eq_trans_code _ _ _ hZ s3
          (PrfH_eq_trans_code _ _ _ hU s4 s5
            (by hw_auto) (by hw_auto) (by hw_auto))
          (by hw_auto) (by hw_auto) (by hw_auto))
        (by hw_auto) (by hw_auto) (by hw_auto))
      (by hw_auto) (by hw_auto) (by hw_auto)
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
    (prf_congr_tcFn (prf_eq_symm (prf_liftsc_cons c h t))))) _) hchain

/-! ## §10 · EL PREDICADO SIN‑`wTs` ENTERO, CONTRA EL OBJETIVO — la MEDIDA

    `isTermCodeE1`/`argsIn` son los de PRODUCCION: declarados en `Minimal/Axioms.lean`
    (ADR-020), re-exportados por `CodeWitnessPrf.SinWTs`. -/

/-- **LA MEDIDA DEL MODULO, no su resultado consumible.**

    ⚠️ Censo 2026‑09‑04: **cero usos**, aqui y aguas abajo. Toma como PREMISA justo lo que el
    descenso FABRICA, asi que nadie rio abajo puede aportarsela: es inconsumible por
    construccion. Se conserva porque mide que el predicado entero cuadra contra el objetivo,
    pero **no es lo que el frente consume** — eso es `pcc_eval_liftc`, en `Meta/EvalLiftcPrf.lean`.

    El predicado `isTermCodeE1 w X` de la via sin‑`wTs`, contra el objetivo `targetLift X`:

        ⊢ isTermCodeE1 w X ⇒ (targetLiftsc (nthc X 2̄) ⇒ targetLift X)

    * La `∨` de los dos disyuntos, su forma ECUACIONAL y el `land`: **usados**.
    * `argsIn w (nthc X 2̄)` — el `∀` ACOTADO ANIDADO: **NO se usa**. Se descarta en la
      eliminacion del `∧`. Su unico papel es alimentar el DESCENSO (garantizar que los hijos
      vuelven a ser codigos), es decir producir la premisa `targetLiftsc (nthc X 2̄)`.
    * Ni un solo `bdAllCode` en la cara punteada: el consecuente es una ecuacion de codigo. -/
theorem refl_isTermCodeE1_imp [AnclaEq] (w X : Term) :
    Prf (Formula.impl (isTermCodeE1 w X)
      (Formula.impl (targetLiftsc (nthc X (numeralM 2))) (targetLift X))) := by
  unfold ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.isTermCodeE1
  refine prf_or_elim_imp ?_ ?_
  · exact impT (refl_shapeUn_imp X)
      (Prf.incl (Prf₀.p1 (targetLift X) (targetLiftsc (nthc X (numeralM 2)))))
  · refine prf_deduction (deduction_aux ?_ (targetLiftsc (nthc X (numeralM 2)))
      [land (shapeBin X 1) (argsIn w (nthc X (numeralM 2)))] rfl)
    have hT : PrfH [targetLiftsc (nthc X (numeralM 2)),
        land (shapeBin X 1) (argsIn w (nthc X (numeralM 2)))]
        (targetLiftsc (nthc X (numeralM 2))) := PrfH.hyp _ _ (List.Mem.head _)
    have hB : PrfH [targetLiftsc (nthc X (numeralM 2)),
        land (shapeBin X 1) (argsIn w (nthc X (numeralM 2)))]
        (land (shapeBin X 1) (argsIn w (nthc X (numeralM 2)))) :=
      PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
    exact PrfH.mp _ _ _ (prf_to_prfH (refl_shapeBin_imp X) _)
      (PrfH_and_intro (PrfH_and_elim_left hB) hT)

/-! ## §11 · EL RESIDUO — no se cierra aqui, y desde el 2026‑09‑04 esta CERRADO aguas abajo
    en `Meta/EvalLiftcPrf.lean` (`DESCENSO` / `pcc_eval_liftc`, rama B2).


    Lo unico que NO se descarga aqui es el **DESCENSO**: pasar de «cada hijo es de nuevo un
    codigo con testigo» a la premisa `targetLiftsc (nthc X 2̄)`. En enunciado:

    ```lean
    DESCENSO :
      ∀ w X, Prf (isTC1 w X)                       -- wfAll1 w ∧ In X w
           → Prf (targetLiftsc (nthc X (numeralM 2)))
    ```

    y es una recursion BIEN FUNDADA sobre el valor del codigo (`prf_strong_induction` +
    `prf_cantor_mono_left/right`, ambos en produccion), combinada con `prf_list_induction`
    para recorrer la lista de argumentos —— con `refl_lista_nil` / `refl_lista_cons_imp` como
    base y paso, que YA estan cerrados aqui. Es el contenido de la rama B2
    (`sondeos/DescensoLiftc.lean`).

    ⚠️ Ese residuo es **enteramente PLANO** (`Prf` de formulas objeto). Ninguna de sus piezas
    pide la imagen PUNTEADA de `wfAll1`, de `argsIn` ni de `isTC1`. -/

end ROBINSON_PlusPlus.Meta.LiftcCodePrf

export ROBINSON_PlusPlus.Meta.LiftcCodePrf (
  liftcT liftscT varcT funccT
  varcT_eq_unT funccT_eq_binT
  liftcT_termCode liftscT_termCode varcT_termCode funccT_termCode
  prf_congr_liftcT prf_congr_liftscT prf_congr_varcT prf_congr_funccT
  prf_substtc_liftcT prf_substtc_liftscT substtc_inv_liftcT substtc_inv_liftscT
  -- ⚠️ `prf_substtc_termCode_closed`/`_numeralM`/`_zero` ya NO se exportan desde aqui:
  --    subieron a `Meta/CodeCtorKit.lean` (B3) y salen a la raiz desde su `export`.
  prf_substtc_unT_at prf_substtc_binT_at prf_substtc_varcT_at prf_substtc_funccT_at
  targetLift targetLiftsc
  LIFTC_FUNC_BODY LIFTC_FUNC_BODY_ok pcc_liftc_func_code
  prf_substfc_atom2CodeFn prf_substfc_ltCodeFn'
  LIFTC_VARGE_BODY LIFTC_VARGE_BODY_ok pcc_liftc_var_ge_code
  LIFTC_VARLT_BODY LIFTC_VARLT_BODY_ok pcc_liftc_var_lt_code
  targetLiftAt targetLiftscAt liftF_targetLiftAt substF_targetLiftAt
  liftF_targetLiftscAt substF_targetLiftscAt prf_liftc_varc_cases
  LIFTSC_NIL_BODY LIFTSC_NIL_BODY_ok pcc_liftsc_nil_code
  LIFTSC_CONS_BODY LIFTSC_CONS_BODY_ok pcc_liftsc_cons_code
  pcc_zero_lt_succ_code pcc_liftc0_var_code pcc_liftc0_func_code
  pcc_liftsc0_nil_code pcc_liftsc0_cons_code
  pcc_congr_liftcT_arg2_code pcc_congr_liftscT_arg2_code
  pcc_congr_consT_arg1_code pcc_congr_consT_arg2_code
  refl_caso_varc refl_caso_funcc refl_lista_nil refl_lista_cons
  refl_termCode refl_termsCode
  shapeUn0_es_varc shapeBin1_es_funcc
  substTerm_termCode substTerm_termsCode substTerm_formCode
  substF_targetLift substF_targetLiftsc substF_targetLift_hole PrfH_congr_targetLift
  refl_shapeUn_imp refl_caso_funcc_imp refl_shapeBin_imp refl_lista_cons_imp
  refl_isTermCodeE1_imp
  -- A5 (§7bis/§9bis) — las CINCO que consume `Meta/EvalLiftcPrf.lean` en su descenso a nivel
  -- abierto (`PHIat_step`). El resto de la familia `_at` (`refl_caso_varc_lift_at`,
  -- `refl_caso_funcc_at`, `refl_lista_cons_at`, `refl_caso_funcc_imp_at`, `refl_termCode_at`,
  -- `refl_termsCode_at`, `PrfH_congr_targetLiftAt`, los dos `_hole`, las dos guardas y
  -- `pcc_liftsc_nil_code_at`) se consume SOLO dentro de este modulo: no se exporta.
  refl_shapeUn_imp_at refl_shapeBin_imp_at refl_lista_nil_at refl_lista_cons_imp_at
  PrfH_congr_targetLiftscAt
)

/-! ## CONTROL DE FOOTPRINT — todo debe salir NET-0 (solo los `axiom` de Lean sancionados). -/

#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_isTermCodeE1_imp
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_caso_funcc_imp
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_shapeBin_imp
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_lista_cons_imp
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_shapeUn_imp
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_termCode
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_termsCode
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_caso_varc
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_caso_funcc
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_lista_nil
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_lista_cons
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_liftc_func_code
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_liftc_var_ge_code
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_liftsc_nil_code
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_liftsc_cons_code
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_liftc0_var_code
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_liftc0_func_code
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_liftsc0_nil_code
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_liftsc0_cons_code
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_zero_lt_succ_code
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substfc_atom2CodeFn
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.substF_targetLift_hole
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.PrfH_congr_targetLift
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_liftc_varc_cases
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_liftc_var_lt_code
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_caso_varc_lift_at
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_caso_funcc_at
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_lista_nil_at
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_lista_cons_at
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_termCode_at
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_shapeUn_imp_at
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_shapeBin_imp_at
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_lista_cons_imp_at
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.substTerm_termCode

-- CONTROL: la base sancionada es EXACTAMENTE la que ya carga produccion.
#print axioms ROBINSON_PlusPlus.Meta.EvalNthcPrf.pcc_nthc_zero_code
#print axioms ROBINSON_PlusPlus.Meta.DotConsPrf.pcc_dot_cons
#print axioms ROBINSON_PlusPlus.Meta.Delta0ReflectPrf.pcc_lt_tracked

-- CONTROL DE NO-DUPLICACION: los simbolos consumidos son los de PRODUCCION, no copias.
example (X : Term) (k : Nat) :
    ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.shapeUn X k = shapeUn X k := rfl
example (wT X : Term) :
    ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.isTermCodeE1 wT X = isTermCodeE1 wT X := rfl
example {Γ : List Formula} (X Y Z : Term)
    (hX : ∀ W, Prf (substtc zero W X =eq X))
    (h1 : PrfH Γ (provFromCode (eqc X Y))) (h2 : PrfH Γ (provFromCode (eqc Y Z)))
    (hwX : Prf (hasWit X)) (hwY : Prf (hasWit Y)) (hwZ : Prf (hasWit Z)) :
    PrfH Γ (provFromCode (eqc X Z)) :=
  ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf.PrfH_eq_trans_code X Y Z hX h1 h2 hwX hwY hwZ
example (a b : Term) : eqc a b = eqCodeFn a b :=
  (ROBINSON_PlusPlus.Meta.Sigma1AtomPrf.eqCodeFn_eq_eqc a b).symm
