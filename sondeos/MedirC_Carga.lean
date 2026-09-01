/-
# `Probe/MC_carga.lean` — MEDICION del ANGULO (B): **CARGAR LA GUARDA COMO HIPOTESIS**

Pregunta del encargo: la via (A) esta muerta (`ENS.CRIT_isFC1_rejects_varc` refuta la guarda para
argumento abstracto). Queda (B): arrastrar la guarda de `pcc_eval_substfc` como hipotesis a lo
largo de la cadena y descargarla al final. **¿Lo aguantan el CHASIS y el ENSAMBLADOR sin
rehacerse?**

Todo lo que sigue COMPILA (exit 0) contra PRODUCCION: `pcc_lineWF_tracked_of_schema`,
`pcc_lineWF_tracked_modulo_7`, `d3_prf_of_chainOkDot`, `ax_lineWF_q1` y `Meta/CodeWitnessPrf.lean`.
Cero axiomas de Lean nuevos, cero `sorry`, cero modificaciones fuera de `Probe/`.

    lake env lean Probe\MC_carga.lean
-/
import ROBINSON_PlusPlus.Meta

set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.ArithPrf ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.LineWFSchemaPrf ROBINSON_PlusPlus.Meta.LineWFAssemblePrf
open ROBINSON_PlusPlus.Meta.D3InDotPrf
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf

namespace MC_carga

/-! ############################################################################
    ## §0 · EL TAG `q1` EN LAS PIEZAS DEL CHASIS, Y LA GUARDA INSTANCIADA
    ############################################################################ -/

/-- La condicion `C` del esquema `q1`, literalmente la de `Minimal/Axioms.lean:1119`. -/
def condQ1 : Formula :=
  carc (.var 0) =eq implc (forallc (nthc (.var 0) (numeralM 2)))
    (substfc zero (nthc (.var 0) (numeralM 3)) (nthc (.var 0) (numeralM 2)))

/-- El esquema real de `q1`, reexpresado con las piezas del chasis. **Definicional.** -/
theorem ax_lineWF_q1_eq :
    ax_lineWF_q1
      = Formula.forall (Formula.impl (tagF 9) (lwfVar ⇔ Formula.and (lencF 4) condQ1)) := rfl

/-- Obligacion administrativa del chasis para `q1`: `rfl`, como en los tags ya cerrados. -/
theorem substFormula_condQ1 : substFormula 0 (.var 0) condQ1 = condQ1 := rfl

/-- El esquema `q1` es AXIOMA de la teoria objeto (sin enmendar). -/
theorem hax_q1 :
    Prf (Formula.forall (Formula.impl (tagF 9) (lwfVar ⇔ Formula.and (lencF 4) condQ1))) :=
  ax_lineWF_q1_eq ▸ prf_ax (show ax_lineWF_q1 ∈ axioms by simp [axioms])

/-- **LA GUARDA DE `pcc_eval_substfc_wit`, INSTANCIADA EN EL TAG `q1`.**

    `pcc_eval_substfc_wit (v s f) : Prf ((hasWit s ∧ hasWitF f) ⇒ targetSubstfc v s f)`.
    En `q1` el `substfc` es `substfc zero (nthc X 3) (nthc X 2)`, luego `s := nthc X 3`
    (sustituyendo, TERMINO) y `f := nthc X 2` (cuerpo, FORMULA). -/
def GQ1 (t : Term) : Formula :=
  Formula.and (ENS.hasWit (nthc t (numeralM 3))) (ENS.hasWitF (nthc t (numeralM 2)))

/-- Control: la guarda es LITERALMENTE el antecedente de `pcc_eval_substfc_wit`
    (`land = Formula.and`, comprobado por `rfl`). -/
example (t : Term) :
    GQ1 t = land (ENS.hasWit (nthc t (numeralM 3))) (ENS.hasWitF (nthc t (numeralM 2))) := rfl

/-! ############################################################################
    ## §1 · MEDICION 1 — **EL CHASIS**. ¿Admite la guarda sin tocar su firma?
    ############################################################################ -/

/-- ### ✅ RESPUESTA 1a — **SI, el chasis NO se toca.**

    Con la guarda disponible al nivel de LEAN (`hg`), el `hcond` guardado se convierte por MP en
    el `hcond` EXACTO que pide `pcc_lineWF_tracked_of_schema`, y el chasis cierra `q1` **en una
    llamada**, igual que `pcc_lineWF_tracked_efq_imp`. La firma del chasis queda intacta.

    ⚠️ Pero fijate DONDE queda `hg`: en la firma de ESTE teorema. La guarda no ha desaparecido,
    ha SUBIDO un nivel. -/
theorem M1a_chasis_admite_guarda (t : Term)
    (hg : Prf (GQ1 t))
    (hcondG : Prf (GQ1 t ⇒ (lineWF t ⇒ ((lenc t =eq numeralM 4) ⇒
      (substFormula 0 t condQ1 ⇒ provFromCode (condD condQ1 t)))))) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 9) ⇒
      provFromCode (lineWFCodeFn (tcFn t)))) :=
  pcc_lineWF_tracked_of_schema t substFormula_condQ1 hax_q1 (prf_mp hcondG hg) (by omega)

/-- ### ✅ RESPUESTA 1b — la guarda se puede meter DENTRO de la cadena objeto, pero SOLO si es
    DERIVABLE de los tres antecedentes que el chasis ya concede.

    Este es el enunciado EXACTO de lo que habria que probar para que la guarda **no** suba:
    `hder`. Es la unica via que deja el chasis intacto Y no deja hipotesis colgando.
    (Con `G := GQ1 t`, `C := condQ1`, `n := 4`, `P := provFromCode (condD condQ1 t)`.) -/
theorem M1b_descarga_desde_los_tres_antecedentes {G C P : Formula} {t : Term} {n : Nat}
    (hcondG : Prf (G ⇒ (lineWF t ⇒ ((lenc t =eq numeralM n) ⇒ (substFormula 0 t C ⇒ P)))))
    (hder : Prf (lineWF t ⇒ ((lenc t =eq numeralM n) ⇒ (substFormula 0 t C ⇒ G)))) :
    Prf (lineWF t ⇒ ((lenc t =eq numeralM n) ⇒ (substFormula 0 t C ⇒ P))) := by
  refine prf_deduction (deduction_aux (deduction_aux ?_
    (substFormula 0 t C) [lenc t =eq numeralM n, lineWF t] rfl)
    (lenc t =eq numeralM n) [lineWF t] rfl)
  let Γ : List Formula := [substFormula 0 t C, lenc t =eq numeralM n, lineWF t]
  have hlw : PrfH Γ (lineWF t) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have hln : PrfH Γ (lenc t =eq numeralM n) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hct : PrfH Γ (substFormula 0 t C) := PrfH.hyp _ _ (List.Mem.head _)
  have hG : PrfH Γ G :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH hder _) hlw) hln) hct
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.mp _ _ _
    (PrfH.mp _ _ _ (prf_to_prfH hcondG _) hG) hlw) hln) hct

/-- La misma, ya instanciada a `q1` y enchufada al chasis REAL: si alguien prueba `hder`,
    `q1` cierra **sin ninguna hipotesis colgando**. Es el objetivo a batir. -/
theorem M1b_q1_cierra_limpio_si_hay_hder (t : Term)
    (hcondG : Prf (GQ1 t ⇒ (lineWF t ⇒ ((lenc t =eq numeralM 4) ⇒
      (substFormula 0 t condQ1 ⇒ provFromCode (condD condQ1 t))))))
    (hder : Prf (lineWF t ⇒ ((lenc t =eq numeralM 4) ⇒ (substFormula 0 t condQ1 ⇒ GQ1 t)))) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 9) ⇒
      provFromCode (lineWFCodeFn (tcFn t)))) :=
  pcc_lineWF_tracked_of_schema t substFormula_condQ1 hax_q1
    (M1b_descarga_desde_los_tres_antecedentes hcondG hder) (by omega)

/-- ### 📏 LO UNICO CON LO QUE PUEDE CONTAR `hder` — medido, no supuesto.

    De los tres antecedentes, `lineWF t` y `lenc t ≐ 4̄` son opacos, y la condicion instanciada
    `substFormula 0 t condQ1` es EXACTAMENTE esta ECUACION sobre `carc t`. No dice **nada** sobre
    la buena formacion de `nthc t 2̄` ni de `nthc t 3̄`: `implc`/`forallc` son meros `cons`, y
    `substfc` es opaco (no tiene ecuaciones de recursion, y postularlas es INCONSISTENTE).
    Esa es la distancia real que `hder` tiene que cubrir. -/
theorem M1c_lo_unico_que_da_la_condicion (t : Term) :
    substFormula 0 t condQ1
      = (carc t =eq implc (forallc (nthc t (numeralM 2)))
          (substfc zero (nthc t (numeralM 3)) (nthc t (numeralM 2)))) := by
  simp only [condQ1, carc, nthc, implc, forallc, substfc, numeralM, succ, zero, cons, nil,
    substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, substTerm_numeralM, if_true]

/-- ### ❌ CONTROL NEGATIVO — la cadena CON guarda **no es** la `hcond` del chasis.
    O sea: no hay hueco libre; la guarda o se descarga (1b) o sube (1a). -/
example (t : Term) : True := by
  fail_if_success
    exact (rfl : (GQ1 t ⇒ (lineWF t ⇒ ((lenc t =eq numeralM 4) ⇒
        (substFormula 0 t condQ1 ⇒ provFromCode (condD condQ1 t)))))
      = (lineWF t ⇒ ((lenc t =eq numeralM 4) ⇒
        (substFormula 0 t condQ1 ⇒ provFromCode (condD condQ1 t)))))
  trivial

/-! ############################################################################
    ## §2 · MEDICION 2 — **EL ENSAMBLADOR**. Encaja, pero la guarda pasa de largo.
    ############################################################################ -/

/-- ### ✅/⚠️ RESPUESTA 2 — el ensamblador **tampoco se toca**, pero **no descarga nada**.

    `pcc_lineWF_tracked_modulo_7` pide sus 7 hipotesis en forma FIJA. Un `q1` con guarda encaja
    sin tocar el ensamblador **con tal de aplicarle la guarda ANTES** (`hq1 hgq1`). El precio es
    exacto y esta a la vista en la firma: `hgq1` sale por arriba, y sale colgando de
    `pcc_lineWF_tracked`.

    Se mide solo con `q1` guardado; los otros 6 se dejan como hipotesis limpias para aislar el
    efecto. En la realidad **los 7 llevan guarda** (`q2 q3 leibniz ind qconf listInd` tambien
    contienen `substfc`/`liftfc`), luego lo que cuelga es la CONJUNCION de las 7. -/
theorem M2_ensamblador_intacto_pero_la_guarda_SUBE (t : Term)
    (hgq1 : Prf (GQ1 t))                                    -- ← ⚠️ LA GUARDA, COLGANDO
    (hq1 : Prf (GQ1 t) → Prf (lineWF t ⇒ ((lineTag t =eq numeralM 9) ⇒
      provFromCode (lineWFCodeFn (tcFn t)))))
    (hq2 : Prf (lineWF t ⇒ ((lineTag t =eq numeralM 10) ⇒
      provFromCode (lineWFCodeFn (tcFn t)))))
    (hq3 : Prf (lineWF t ⇒ ((lineTag t =eq numeralM 11) ⇒
      provFromCode (lineWFCodeFn (tcFn t)))))
    (hleibniz : Prf (lineWF t ⇒ ((lineTag t =eq numeralM 13) ⇒
      provFromCode (lineWFCodeFn (tcFn t)))))
    (hind : Prf (lineWF t ⇒ ((lineTag t =eq numeralM 18) ⇒
      provFromCode (lineWFCodeFn (tcFn t)))))
    (hqconf : Prf (lineWF t ⇒ ((lineTag t =eq numeralM 19) ⇒
      provFromCode (lineWFCodeFn (tcFn t)))))
    (hlistInd : Prf (lineWF t ⇒ ((lineTag t =eq numeralM 20) ⇒
      provFromCode (lineWFCodeFn (tcFn t)))))
    (hOther : ∀ k : Nat, Prf (lineWF t ⇒ ((lineTag t =eq numeralM k) ⇒
      provFromCode (lineWFCodeFn (tcFn t))))) :
    Prf (lineWF t ⇒ provFromCode (lineWFCodeFn (tcFn t))) :=
  pcc_lineWF_tracked_modulo_7 t (hq1 hgq1) hq2 hq3 hleibniz hind hqconf hlistInd hOther

/-- La cadena COMPLETA, chasis + ensamblador, con la guarda entrando por §1a: `pcc_lineWF_tracked`
    sale **CONDICIONADO** por `GQ1 t`. Este es el resultado de la medicion 2, compilado. -/
theorem M2_tracked_CONDICIONADO (t : Term)
    (hgq1 : Prf (GQ1 t))                                    -- ← ⚠️ LA GUARDA, COLGANDO
    (hcondG : Prf (GQ1 t ⇒ (lineWF t ⇒ ((lenc t =eq numeralM 4) ⇒
      (substFormula 0 t condQ1 ⇒ provFromCode (condD condQ1 t))))))
    (hq2 hq3 hleibniz hind hqconf hlistInd :
      ∀ k : Nat, Prf (lineWF t ⇒ ((lineTag t =eq numeralM k) ⇒
        provFromCode (lineWFCodeFn (tcFn t)))))
    (hOther : ∀ k : Nat, Prf (lineWF t ⇒ ((lineTag t =eq numeralM k) ⇒
      provFromCode (lineWFCodeFn (tcFn t))))) :
    Prf (lineWF t ⇒ provFromCode (lineWFCodeFn (tcFn t))) :=
  pcc_lineWF_tracked_modulo_7 t (M1a_chasis_admite_guarda t hgq1 hcondG)
    (hq2 10) (hq3 11) (hleibniz 13) (hind 18) (hqconf 19) (hlistInd 20) hOther

/-! ############################################################################
    ## §3 · MEDICION 3 — `hcond_absorbe_extra`. **APLICA, pero cobra en `axioms`.**
    ############################################################################ -/

/-- Replica net-0 de `sondeos/SegundoMuro.lean:112` (`sondeos/` esta fuera del build y no es
    importable). Prueba **literal**; se reproduce aqui para poder MEDIRLA contra `q1`. -/
theorem hcond_absorbe_extra (P C : Formula) (t : Term) (n : Nat)
    (hP : Prf (lineWF t ⇒ ((lenc t =eq numeralM n) ⇒
      (substFormula 0 t P ⇒ provFromCode (condD P t)))))
    (hC : Prf (lineWF t ⇒ ((lenc t =eq numeralM n) ⇒
      (substFormula 0 t C ⇒ provFromCode (condD C t))))) :
    Prf (lineWF t ⇒ ((lenc t =eq numeralM n) ⇒
      (substFormula 0 t (Formula.and P C) ⇒ provFromCode (condD (Formula.and P C) t)))) := by
  refine prf_deduction (deduction_aux (deduction_aux ?_
    (substFormula 0 t (Formula.and P C))
    [lenc t =eq numeralM n, lineWF t] rfl)
    (lenc t =eq numeralM n) [lineWF t] rfl)
  let Γ : List Formula :=
    [substFormula 0 t (Formula.and P C), lenc t =eq numeralM n, lineWF t]
  have hlw : PrfH Γ (lineWF t) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have hln : PrfH Γ (lenc t =eq numeralM n) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hand : PrfH Γ (Formula.and (substFormula 0 t P) (substFormula 0 t C)) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hPt : PrfH Γ (substFormula 0 t P) :=
    PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c2 _ _)) hand
  have hCt : PrfH Γ (substFormula 0 t C) :=
    PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c3 _ _)) hand
  have hPd : PrfH Γ (provFromCode (condD P t)) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH hP _) hlw) hln) hPt
  have hCd : PrfH Γ (provFromCode (condD C t)) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH hC _) hlw) hln) hCt
  have hcomp : Prf (andc (condD P t) (condD C t) =eq condD (Formula.and P C) t) :=
    prf_eq_symm (prf_substfc_and zero (tcFn t) (formCode P) (formCode C))
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr hcomp) _)
    (PrfH_and_intro_code _ _ hPd hCd)

/-- ### ⚠️ RESPUESTA 3 — `hcond_absorbe_extra` **si aplica a `q1`**: absorbe la guarda como
    conjunto extra `P` y el chasis la traga. **Pero mira el `haxEnmendado`.**

    El chasis pide `hax` del esquema **cuya condicion es `P ∧ condQ1`**. Ese NO es `ax_lineWF_q1`
    (§3, control de abajo). Para tenerlo hay que meterlo en `axioms` ⇒ cambia `axiomsCodeT`
    ⇒ cambia `provCodeC'` ⇒ **CAMBIA LA SENTENCIA G**. -/
theorem M3_absorbe_pero_pide_hax_ENMENDADO (P : Formula) (t : Term)
    (hPsub : substFormula 0 (.var 0) (Formula.and P condQ1) = Formula.and P condQ1)
    (haxEnmendado : Prf (Formula.forall (Formula.impl (tagF 9)
      (lwfVar ⇔ Formula.and (lencF 4) (Formula.and P condQ1)))))
    (hP : Prf (lineWF t ⇒ ((lenc t =eq numeralM 4) ⇒
      (substFormula 0 t P ⇒ provFromCode (condD P t)))))
    (hC : Prf (lineWF t ⇒ ((lenc t =eq numeralM 4) ⇒
      (substFormula 0 t condQ1 ⇒ provFromCode (condD condQ1 t))))) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 9) ⇒
      provFromCode (lineWFCodeFn (tcFn t)))) :=
  pcc_lineWF_tracked_of_schema t hPsub haxEnmendado
    (hcond_absorbe_extra P condQ1 t 4 hP hC) (by omega)

/-- ### ❌ EL PRECIO, COMPILADO: la condicion enmendada **no es** la condicion de `q1`. -/
theorem M3_enmienda_cambia_la_condicion (P : Formula) : Formula.and P condQ1 ≠ condQ1 := by
  intro h; simp only [condQ1] at h; exact Formula.noConfusion h

/-- ### ❌ Y por tanto el AXIOMA enmendado **no es** `ax_lineWF_q1`: `axioms` cambia. -/
theorem M3_enmienda_cambia_el_axioma (P : Formula) :
    Formula.forall (Formula.impl (tagF 9)
        (lwfVar ⇔ Formula.and (lencF 4) (Formula.and P condQ1)))
      ≠ ax_lineWF_q1 := by
  rw [ax_lineWF_q1_eq]
  intro h
  injection h with h1
  injection h1 with _ h3
  simp only [iff] at h3
  injection h3 with h4 _
  injection h4 with _ h7
  injection h7 with _ h9
  exact M3_enmienda_cambia_la_condicion P h9

/-- El esquema `q1` SIN enmendar si esta en `axioms` (referencia de la comparacion). -/
theorem M3_q1_esta_en_axioms : ax_lineWF_q1 ∈ axioms := by simp [axioms]

/-! ############################################################################
    ## §4 · MEDICION 4 — **QUE CUELGA EXACTAMENTE**, y hasta donde llega.
    ############################################################################ -/

/-- **LA HIPOTESIS QUE QUEDARIA COLGANDO EN `pcc_lineWF_tracked`**, enunciada en Lean.
    `pcc_lineWF_tracked` se usa con la linea `t := #0` (variable De Bruijn), porque `hC_dot`
    tiene que GENERALIZARLA para el `∀` acotado sobre las lineas de la derivacion. -/
def GUARDA_COLGANTE : Formula := GQ1 (.var 0)

example : GUARDA_COLGANTE
    = Formula.and (ENS.hasWit (nthc (.var 0) (numeralM 3)))
                  (ENS.hasWitF (nthc (.var 0) (numeralM 2))) := rfl

/-- ### 🚨 RESPUESTA 4 — **LA GUARDA SUBE HASTA D3.**

    `d3_prf_of_chainOkDot` es PRODUCCION (`Meta/D3InDotPrf.lean:465`) y es literalmente el
    enunciado «D3 queda reducida a `hC_dot` SOLO». Si `hC_dot` cuelga de la guarda, D3 cuelga de
    la guarda. Compilado: -/
theorem M4_D3_SALE_CONDICIONADA (φ : Formula)
    (hg : Prf GUARDA_COLGANTE)                              -- ← ⚠️ LA GUARDA, EN D3
    (hC : Prf GUARDA_COLGANTE →
      Prf (chainOk nil (.var 0) ⇒ provFromCode chainOkDot)) :
    Prf (provCodeC' φ ⇒ provCodeC' (provCodeC' φ)) :=
  d3_prf_of_chainOkDot φ (hC hg)

/-! ### ¿Es satisfacible la guarda colgante? Las dos caras, medidas. -/

/-- **CARA BUENA — la guarda NO es contradictoria**: sobre codigos REALES se descarga.
    `HW.prf_hasWitF_real` es produccion y es net-0. -/
theorem M4_guarda_satisfacible_en_codigos_reales (φ : Formula) :
    Prf (ENS.hasWitF (formCodeM φ)) := HW.prf_hasWitF_real φ

/-- El gemelo de TERMINO, que produccion no tenia: la mitad `hasWit` de la guarda tambien es
    satisfacible sobre codigos reales. Net-0, misma receta que `prf_hasWitF_real`. -/
theorem M4_prf_hasWit_real (u : Term) : Prf (ENS.hasWit (termCodeM u)) := by
  have hsub : substFormula 0 (objList (SinWTs.tcodes1 u))
      (SinWTs.isTC1 (.var 0) (liftTerm 0 (termCodeM u)))
      = SinWTs.isTC1 (objList (SinWTs.tcodes1 u)) (termCodeM u) := by
    rw [ENS.substF_isTC1]
    simp only [substTerm, reduceIte, FOL.substTerm_liftTerm]
  show Prf (Formula.ex (SinWTs.isTC1 (.var 0) (liftTerm 0 (termCodeM u))))
  exact prf_ex_intro _ (hsub ▸ SinWTs.prf_isTC1_tcodes u)

/-- La guarda ENTERA, descargada sobre casillas que son codigos reales. Es el unico caso en que
    se descarga: `s` codigo de TERMINO real, `f` codigo de FORMULA real. -/
theorem M4_guarda_descargable_solo_sobre_codigos_reales (u : Term) (φ : Formula) :
    Prf (Formula.and (ENS.hasWit (termCodeM u)) (ENS.hasWitF (formCodeM φ))) :=
  prf_and_intro (M4_prf_hasWit_real u) (HW.prf_hasWitF_real φ)

/-- Fontaneria que produccion no tenia (`ENS` solo publica `liftF_hasWitF`): la sustitucion
    atraviesa los DOS `∃` de la guarda de FORMULA. Gemela literal de `ENS.substF_hasWit`. -/
theorem substF_hasWitF (v : Nat) (s c : Term) :
    substFormula v s (ENS.hasWitF c) = ENS.hasWitF (substTerm v s c) := by
  have h1 : (1 = v + 1 + 1) = False := eq_false (by omega)
  have h2 : (1 > v + 1 + 1) = False := eq_false (by omega)
  have hz : (0 = v + 1 + 1) = False := eq_false (by omega)
  have hz2 : (0 > v + 1 + 1) = False := eq_false (by omega)
  simp only [ENS.hasWitF, substFormula, ENS.substF_isFC1, substTerm, h1, h2, hz, hz2, if_false,
    FOL.substTerm_lift_comm_zero]

/-- **CARA MALA — la guarda colgante es una afirmacion UNIVERSAL sobre TODO objeto.**
    `Prf` de una formula abierta en `#0` se generaliza; especializando, la hipotesis colgante
    dice que la casilla 2 de CUALQUIER objeto `t` es codigo de formula y la 3 codigo de termino.
    No es una hipotesis tecnica inocua: es un axioma de buena-formacion global. -/
theorem M4_colgante_es_universal (h : Prf GUARDA_COLGANTE) (t : Term) : Prf (GQ1 t) := by
  have hspec := prf_spec (Prf.gen _ h) t
  simpa only [GUARDA_COLGANTE, GQ1, substFormula, ENS.substF_hasWit, substF_hasWitF,
    nthc, substTerm, substTerms, substTerm_numeralM, if_true] using hspec

/-! ############################################################################
    ## §5 · LA PREGUNTA QUE DECIDE: ¿es SATISFACIBLE la guarda colgante?
       **NO. ES REFUTABLE.** Reconstruccion en PRODUCCION de la discriminacion que
       en `sondeos/EvalSubstfcPrf.lean:8306` mato la via (A), aplicada ahora a la via (B).
    ############################################################################ -/

/-- El disyunto NUL de la forma ECUACIONAL fortalece el POSICIONAL. (Produccion tiene
    `prf_shapeUn_str`/`prf_shapeBin_str` pero no el de `shapeNul`, que es de `ENS`.) -/
theorem prf_shapeNul_str (X : Term) (k : Nat) :
    Prf (Formula.impl (ENS.shapeNul X k)
      (land (SinWTs.consOk X) (land (Formula.eq (carc X) (numeralM k))
                                    (Formula.eq (lenc X) (numeralM 1))))) :=
  SinWTs.prf_shape_strengthens X _ k 1 (prf_carc_cons _ _)
    (SinWTs.prf_lenc_c1 _) (SinWTs.prf_consOk_cons _ _)

theorem lor_map {A A' B B' : Formula} (hA : Prf (A ⇒ A')) (hB : Prf (B ⇒ B')) :
    Prf (lor A B ⇒ lor A' B') :=
  SinWTs.prf_or_elim_imp (SinWTs.impT hA (SinWTs.prf_lorL _ _))
    (SinWTs.impT hB (SinWTs.prf_lorR _ _))

/-- **La forma ECUACIONAL fortalece la POSICIONAL** — 8 disyuntos a 8 disyuntos. -/
theorem prf_isFormCodeE2_str (wF wT X : Term) :
    Prf (Formula.impl (ENS.isFormCodeE2 wF wT X) (SinWTs.isFormCodeB2 wF wT X)) := by
  simp only [ENS.isFormCodeE2, SinWTs.lorAll, ENS.clBot, ENS.clAtom, ENS.clEq, ENS.clBin,
    ENS.clUn, SinWTs.isFormCodeB2]
  exact lor_map (prf_shapeNul_str X 2)
   (lor_map (SinWTs.prf_str_and X 3 3 _ _ (SinWTs.prf_shapeBin_str X 3))
    (lor_map (SinWTs.prf_str_and X 4 3 _ _ (SinWTs.prf_shapeBin_str X 4))
     (lor_map (SinWTs.prf_str_and X 5 3 _ _ (SinWTs.prf_shapeBin_str X 5))
      (lor_map (SinWTs.prf_str_and X 6 2 _ _ (SinWTs.prf_shapeUn_str X 6))
       (lor_map (SinWTs.prf_str_and X 7 3 _ _ (SinWTs.prf_shapeBin_str X 7))
        (lor_map (SinWTs.prf_str_and X 8 3 _ _ (SinWTs.prf_shapeBin_str X 8))
                 (SinWTs.prf_str_and X 9 2 _ _ (SinWTs.prf_shapeUn_str X 9))))))))

/-- **CONTROL**: la GUARDA COMPLETA de FORMULA rechaza un codigo de VARIABLE, con
    CUALQUIER par de testigos. (Replica en produccion de `ENS.CRIT_isFC1_rejects_varc`.) -/
theorem CRIT_isFC1_rejects_varc (wF wT n : Term) :
    Prf (Formula.impl (ENS.isFC1 wF wT (varc n)) Formula.bottom) := by
  refine prf_deduction ?_
  have hh := prfH_hyp_self (ENS.isFC1 wF wT (varc n))
  have hwF := PrfH_and_elim_right (PrfH_and_elim_left hh)
  have hin := PrfH_and_elim_right hh
  have hcode := PrfH.mp _ _ _ (PrfH.mp _ _ _
    (prf_to_prfH (ENS.prf_isFormCodeE2_of_In wF wT (varc n)) _) hin) hwF
  exact PrfH.mp _ _ _ (prf_to_prfH
    (SinWTs.impT (prf_isFormCodeE2_str wF wT (varc n))
      (SinWTs.crit_isFormCodeB2_rejects_varc wF wT n)) _) hcode

theorem liftTerm_varc (k : Nat) (n : Term) : liftTerm k (varc n) = varc (liftTerm k n) := by
  simp only [varc, cons, nil, zero, liftTerm, liftTerms]

/-- **La guarda CUANTIFICADA tampoco acepta un codigo de VARIABLE**: los dos `∃` no salvan
    nada, porque la discriminacion vale para CUALQUIER testigo. -/
theorem CRIT_hasWitF_rejects_varc (n : Term) :
    Prf (Formula.impl (ENS.hasWitF (varc n)) Formula.bottom) := by
  have hlift : liftTerm 0 (liftTerm 0 (varc n)) = varc (liftTerm 0 (liftTerm 0 n)) := by
    simp only [liftTerm_varc]
  refine prf_deduction ?_
  refine PrfH_ex_elim (prfH_hyp_self (ENS.hasWitF (varc n))) ?_
  refine PrfH_ex_elim (PrfH.hyp _ _ (List.Mem.head _)) ?_
  refine PrfH.mp _ _ _ (prf_to_prfH (CRIT_isFC1_rejects_varc (.var 1) (.var 0)
    (liftTerm 0 (liftTerm 0 n))) _) ?_
  rw [← hlift]
  exact PrfH.hyp _ _ (List.Mem.head _)

/-- Una linea CONCRETA de longitud 4 con etiqueta 9 cuya **casilla 2** es un codigo de
    VARIABLE. Nada impide construirla: `substfc` es opaco y no tiene ecuaciones de recursion. -/
def lineaMala : Term :=
  cons zero (cons (numeralM 9) (cons (varc (numeralM 0)) (cons zero nil)))

/-- ### 🚨🚨 RESPUESTA 5 — **LA GUARDA COLGANTE IMPLICA `⊥`.**

    De `Prf GUARDA_COLGANTE` (la hipotesis que la via (B) deja colgando de
    `pcc_lineWF_tracked` y por tanto de `hC_dot` y de D3) se deriva la INCONSISTENCIA de la
    teoria objeto. Luego la guarda **no se descarga nunca** y **D3 condicionada por ella es
    VACUA**: no dice nada. -/
theorem M5_LA_GUARDA_COLGANTE_IMPLICA_BOT (h : Prf GUARDA_COLGANTE) : Prf Formula.bottom := by
  have hall : Prf (GQ1 lineaMala) := M4_colgante_es_universal h lineaMala
  have hwit : Prf (ENS.hasWitF (nthc lineaMala (numeralM 2))) := prf_and_elim_right hall
  have heq : Prf (nthc lineaMala (numeralM 2) =eq varc (numeralM 0)) :=
    SinWTs.prf_nthc_c2 zero (numeralM 9) (varc (numeralM 0)) (cons zero nil)
  have hS : ∀ s : Term, substFormula 0 s (ENS.hasWitF (.var 0)) = ENS.hasWitF s := by
    intro s; simp only [substF_hasWitF, substTerm, reduceIte]
  have h1 : Prf (substFormula 0 (nthc lineaMala (numeralM 2)) (ENS.hasWitF (.var 0))) := by
    rw [hS]; exact hwit
  have h2 : Prf (substFormula 0 (varc (numeralM 0)) (ENS.hasWitF (.var 0))) :=
    prf_mp (prf_mp (Prf.incl (Prf₀.leibniz (ENS.hasWitF (.var 0)) _ _)) heq) h1
  rw [hS] at h2
  exact prf_mp (CRIT_hasWitF_rejects_varc (numeralM 0)) h2

/-- La misma conclusion **sin pasar por `#0`**, para quitar toda objecion sobre en que termino se
    instancia `pcc_lineWF_tracked`: el reflector del chasis es generico en `t`, luego la
    obligacion que cuelga del teorema GENERICO es `∀ t, Prf (GQ1 t)` — y eso da `⊥` directo. -/
theorem M5_la_forma_GENERICA_tambien_implica_BOT (h : ∀ t : Term, Prf (GQ1 t)) :
    Prf Formula.bottom := by
  have hwit : Prf (ENS.hasWitF (nthc lineaMala (numeralM 2))) := prf_and_elim_right (h lineaMala)
  have heq : Prf (nthc lineaMala (numeralM 2) =eq varc (numeralM 0)) :=
    SinWTs.prf_nthc_c2 zero (numeralM 9) (varc (numeralM 0)) (cons zero nil)
  have hS : ∀ s : Term, substFormula 0 s (ENS.hasWitF (.var 0)) = ENS.hasWitF s := by
    intro s; simp only [substF_hasWitF, substTerm, reduceIte]
  have h1 : Prf (substFormula 0 (nthc lineaMala (numeralM 2)) (ENS.hasWitF (.var 0))) := by
    rw [hS]; exact hwit
  have h2 : Prf (substFormula 0 (varc (numeralM 0)) (ENS.hasWitF (.var 0))) :=
    prf_mp (prf_mp (Prf.incl (Prf₀.leibniz (ENS.hasWitF (.var 0)) _ _)) heq) h1
  rw [hS] at h2
  exact prf_mp (CRIT_hasWitF_rejects_varc (numeralM 0)) h2

/-- Y por tanto, bajo la guarda colgante **TODO** es demostrable: la «D3 condicionada» de §4
    no aporta informacion ninguna. -/
theorem M5_bajo_la_guarda_todo_es_demostrable (h : Prf GUARDA_COLGANTE) (A : Formula) : Prf A :=
  prf_mp (Prf.incl (Prf₀.efq A)) (M5_LA_GUARDA_COLGANTE_IMPLICA_BOT h)

end MC_carga

/-! ############################################################################
    ## §6 · FOOTPRINT
    ############################################################################ -/

#print axioms MC_carga.hax_q1
#print axioms MC_carga.M1a_chasis_admite_guarda
#print axioms MC_carga.M1b_descarga_desde_los_tres_antecedentes
#print axioms MC_carga.M1b_q1_cierra_limpio_si_hay_hder
#print axioms MC_carga.M2_ensamblador_intacto_pero_la_guarda_SUBE
#print axioms MC_carga.M2_tracked_CONDICIONADO
#print axioms MC_carga.hcond_absorbe_extra
#print axioms MC_carga.M3_absorbe_pero_pide_hax_ENMENDADO
#print axioms MC_carga.M3_enmienda_cambia_la_condicion
#print axioms MC_carga.M3_enmienda_cambia_el_axioma
#print axioms MC_carga.M3_q1_esta_en_axioms
#print axioms MC_carga.M4_D3_SALE_CONDICIONADA
#print axioms MC_carga.M4_prf_hasWit_real
#print axioms MC_carga.M4_guarda_descargable_solo_sobre_codigos_reales
#print axioms MC_carga.M4_colgante_es_universal
#print axioms MC_carga.prf_isFormCodeE2_str
#print axioms MC_carga.CRIT_isFC1_rejects_varc
#print axioms MC_carga.CRIT_hasWitF_rejects_varc
#print axioms MC_carga.M5_LA_GUARDA_COLGANTE_IMPLICA_BOT
#print axioms MC_carga.M5_la_forma_GENERICA_tambien_implica_BOT
#print axioms MC_carga.M5_bajo_la_guarda_todo_es_demostrable
#print axioms MC_carga.M1c_lo_unico_que_da_la_condicion

#check @MC_carga.M1a_chasis_admite_guarda
#check @MC_carga.M2_tracked_CONDICIONADO
#check @MC_carga.M4_D3_SALE_CONDICIONADA
