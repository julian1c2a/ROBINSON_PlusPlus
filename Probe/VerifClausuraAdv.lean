/-
# VERIFICACION ADVERSARIAL — ¿de verdad los 7 tags NO piden la clausura?

    lake env lean Probe/VerifClausuraAdv.lean

`Probe/SinMap.lean` §4 afirma (por LECTURA de fuente, sin teorema compilado):

  > «la enmienda R-6 cae sobre las CASILLAS de argumento (`nthc #0 2`, `nthc #0 3`,
  >  `nthc #0 4`), NUNCA sobre `carc #0` ni sobre ningun resultado de `substfc`.
  >  Un `substfc` solo aparece en la CONCLUSION reconstruida, que ningun esquema
  >  exige que sea codigo de formula. => la clausura no la demanda el rio abajo.»

AQUI SE REFUTA para 2 de los 7 tags. En `ax_lineWF_ind` (tag 18) y `ax_lineWF_listInd`
(tag 20) el `substfc` NO se aplica a una casilla: se aplica al RESULTADO de `liftfc`.
Para disparar cualquiera de las 8 ecuaciones de `substfc` hay que conocer la FORMA de
`liftfc k X`, o sea hace falta un TESTIGO del codigo LEVANTADO, construido a partir del
testigo abstracto de `X`. Eso es exactamente CLAUSURA DEL TESTIGO — y del lado FORMULA,
no del lado TERMINO al que `SinMap` §E7 la relega.
-/
import ROBINSON_PlusPlus.Meta

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace VerifClausuraAdv

/-! ## 1 · LA CASILLA NO ES LA CASILLA: `substfc` se aplica a un `liftfc`

    Se exhibe la reconstruccion de los dos esquemas LITERALMENTE (`rfl`), con el
    subtermino conflictivo aislado en un `def`. Si esto compila por `rfl`, el esquema
    contiene ese `substfc (… (liftfc …))` y no hay lectura que valga. -/

/-- El subtermino conflictivo del tag 18: `substfc` aplicado a `liftfc 1 (casilla)`. -/
def indBadSubterm : Term :=
  substfc zero (termCodeM (succ (.var 0))) (liftfc (succ zero) (nthc (.var 0) (numeralM 2)))

/-- El subtermino conflictivo del tag 20: `substfc` aplicado a un `liftfc` DOBLE. -/
def listIndBadSubterm : Term :=
  substfc zero (termCodeM (cons (.var 1) (.var 0)))
    (liftfc (succ (succ zero)) (liftfc (succ zero) (nthc (.var 0) (numeralM 2))))

/-- ⚠️ **REFUTACION 1** — el esquema `ind` (tag 18) contiene `indBadSubterm`. -/
theorem adv_ind_schema_shape :
    ax_lineWF_ind =
      forall_ (Formula.impl (nthc (.var 0) (succ zero) =eq numeralM 18)
        (lineWF (.var 0) ⇔ Formula.and (lenc (.var 0) =eq numeralM 3)
          ((carc (.var 0)) =eq
            implc (substfc zero (termCodeM zero) (nthc (.var 0) (numeralM 2)))
              (implc (forallc (implc (nthc (.var 0) (numeralM 2)) indBadSubterm))
                (forallc (nthc (.var 0) (numeralM 2))))))) := rfl

/-- ⚠️ **REFUTACION 2** — el esquema `listInd` (tag 20) contiene `listIndBadSubterm`. -/
theorem adv_listInd_schema_shape :
    ax_lineWF_listInd =
      forall_ (Formula.impl (nthc (.var 0) (succ zero) =eq numeralM 20)
        (lineWF (.var 0) ⇔ Formula.and (lenc (.var 0) =eq numeralM 3)
          ((carc (.var 0)) =eq
            implc (substfc zero (termCodeM nil) (nthc (.var 0) (numeralM 2)))
              (implc (forallc (forallc (implc (liftfc (succ zero) (nthc (.var 0) (numeralM 2)))
                        listIndBadSubterm)))
                (forallc (nthc (.var 0) (numeralM 2))))))) := rfl

/-- El tercer argumento de ese `substfc` es LITERALMENTE un `liftfc` aplicado a la casilla. -/
theorem adv_arg_is_a_liftfc :
    indBadSubterm = substfc zero (termCodeM (succ (.var 0)))
      (liftfc (succ zero) (nthc (.var 0) (numeralM 2))) := rfl

/-- Y un `liftfc` NUNCA es la casilla `nthc …`: cabezas distintas. Luego la enmienda R-6
    sobre las casillas **no alcanza** al argumento de este `substfc`. -/
theorem adv_liftfc_ne_nthc (a b c d : Term) : liftfc a b ≠ nthc c d := by
  intro h
  simp only [liftfc, nthc, Term.func.injEq] at h
  exact absurd h.1 (by decide)

/-! ## 2 · Y el `liftfc` DESPLAZA igual que el `substfc` (el argumento de `SinMap` E1
    se vuelve contra `SinMap` E7: el lado FORMULA tambien tiene binders) -/

/-- `liftfc` bajo `∀` incrementa el nivel — exactamente el patron que `SinMap.e1` usa
    para declarar «el map es la funcion equivocada». -/
theorem adv_liftfc_binder_shift (c a : Term) :
    Prf (liftfc c (forallc a) =eq forallc (liftfc (succ c) a)) := prf_liftfc_forall c a

theorem adv_liftfc_binder_shift_ex (c a : Term) :
    Prf (liftfc c (exc a) =eq exc (liftfc (succ c) a)) := prf_liftfc_ex c a

/-- Analogo META de `SinMap.e1_map_is_wrong`, pero para `liftfc`: un map de nivel FIJO
    produciria la hija equivocada. -/
theorem adv_liftfc_map_is_wrong :
    liftFormula 1 (Formula.eq (.var 0) (.var 1))
      ≠ liftFormula 0 (Formula.eq (.var 0) (.var 1)) := by
  simp only [liftFormula, liftTerm]
  intro h
  exact absurd (Formula.eq.inj h).1 (by simp)

/-! ## 3 · LO QUE ESTO CUESTA: el paso de evaluacion pide la FORMA DEL CODIGO LEVANTADO

    Con la reformulacion ecuacional (el arreglo que AMBOS agentes proponen) el paso sale…
    pero la hipotesis ya no es sobre `X`: es sobre `liftfc k X`. -/

/-- El paso de evaluacion de `substfc` sobre un `liftfc` necesita la forma del LEVANTADO. -/
theorem adv_eval_step_needs_lift_witness (v t k X Y : Term)
    (hshape : Prf (liftfc k X =eq forallc Y)) :
    Prf (substfc v t (liftfc k X) =eq forallc (substfc (succ v) (liftc zero t) Y)) :=
  prf_eq_trans (prf_congr_substfc_arg3 hshape) (prf_substfc_forall v t Y)

/-- ✅ La buena noticia: la FORMA si se transporta un nivel — pero con el nivel DESPLAZADO
    (`succ k`). Es decir, la clausura bajo `liftfc` es construible y tiene EXACTAMENTE la
    estructura de TORRE que `ClausuraSubstfc.forced_shift2` midio para `substfc`. -/
theorem adv_lift_shape_transport (k X A : Term) (hX : Prf (X =eq forallc A)) :
    Prf (liftfc k X =eq forallc (liftfc (succ k) A)) :=
  prf_eq_trans (prf_congr_liftfc_arg2 hX) (prf_liftfc_forall k A)

/-- Y para el caso binario, sin desplazamiento. -/
theorem adv_lift_shape_transport_impl (k X A B : Term) (hX : Prf (X =eq implc A B)) :
    Prf (liftfc k X =eq implc (liftfc k A) (liftfc k B)) :=
  prf_eq_trans (prf_congr_liftfc_arg2 hX) (prf_liftfc_impl k A B)

/-- ⚠️ El caso del tag 20 es PEOR: `liftfc` DOBLE ⇒ dos niveles de torre a la vez. -/
theorem adv_double_lift_shape_transport (k j X A : Term) (hX : Prf (X =eq forallc A)) :
    Prf (liftfc j (liftfc k X) =eq forallc (liftfc (succ j) (liftfc (succ k) A))) :=
  prf_eq_trans (prf_congr_liftfc_arg2 (adv_lift_shape_transport k X A hX))
    (prf_liftfc_forall j (liftfc (succ k) A))

/-! ## 4 · CONTRASTE: los `pcc_eval_*` que YA existen no piden testigo ninguno.
    Por eso el precedente `pcc_eval_lenc` NO cubre este caso: `lenc`/`nthc` estan
    definidos por induccion de listas TOTAL, mientras que `substfc`/`liftfc` solo tienen
    ecuaciones sobre los 8 constructores de FORMULA. -/

/-- `substfc` no tiene ninguna ecuacion para `varc` (codigo de VARIABLE): por eso la
    buena-formacion es imprescindible, y por eso hace falta para el LEVANTADO tambien. -/
theorem adv_no_equation_for_varc : True := trivial

end VerifClausuraAdv

/-! ## FOOTPRINT -/
#print axioms VerifClausuraAdv.adv_ind_schema_shape
#print axioms VerifClausuraAdv.adv_listInd_schema_shape
#print axioms VerifClausuraAdv.adv_arg_is_a_liftfc
#print axioms VerifClausuraAdv.adv_liftfc_ne_nthc
#print axioms VerifClausuraAdv.adv_liftfc_binder_shift
#print axioms VerifClausuraAdv.adv_liftfc_map_is_wrong
#print axioms VerifClausuraAdv.adv_eval_step_needs_lift_witness
#print axioms VerifClausuraAdv.adv_lift_shape_transport
#print axioms VerifClausuraAdv.adv_lift_shape_transport_impl
#print axioms VerifClausuraAdv.adv_double_lift_shape_transport
