/- # `Probe/MC_deriva.lean` — MEDICION del angulo (A):
   **¿sale la guarda `hasWitF (nthc t 2̄)` del propio antecedente `lineWF t`?**

   Encargo: NO cerrar `q1`. MEDIR, con Lean compilado, si la hipotesis (A) es cierta.
   RESPUESTA: **NO — y aqui esta REFUTADA**, no opinada.

   CERO `axiom` de Lean, CERO `sorry`.

       lake env lean Probe\MC_deriva.lean
-/
import ROBINSON_PlusPlus.Meta

set_option maxHeartbeats 1000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace MCderiva

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.BoundedInPrf ROBINSON_PlusPlus.Meta.BdAllIntroPrf
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.TrackedCorePrf
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf ROBINSON_PlusPlus.Meta.Sigma1CorePrf
open ROBINSON_PlusPlus.Meta.EvalListPrf ROBINSON_PlusPlus.Meta.EvalNthcPrf
open ROBINSON_PlusPlus.Meta.EvalLtPrf ROBINSON_PlusPlus.Meta.EvalBoundedPrf
open ROBINSON_PlusPlus.Meta.EvalArithPrf ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
open ROBINSON_PlusPlus.Meta.NumListPrf
open ROBINSON_PlusPlus.Meta.LineWFTrackedPrf ROBINSON_PlusPlus.Meta.LineWFSchemaPrf
open ROBINSON_PlusPlus.Meta.LineWFAssemblePrf ROBINSON_PlusPlus.Meta.CodeTreeReflect
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf

/-! ############################################################################
    # §1 · QUE DICE EXACTAMENTE `ax_lineWF_q1` SOBRE LAS CASILLAS 2 Y 3
    ############################################################################ -/

/-- La condicion `C` del esquema q1, escrita como `def`, tal cual la pone
    `Minimal/Axioms.lean:1119`. -/
def condQ1 : Formula :=
  Formula.eq (carc (.var 0))
    (implc (forallc (nthc (.var 0) (numeralM 2)))
           (substfc zero (nthc (.var 0) (numeralM 3)) (nthc (.var 0) (numeralM 2))))

/-- **MEDIDA 1.** El esquema q1 ES, LITERALMENTE (`rfl`), la forma que pide el chasis:
    `∀ (tag 9 ⇒ (lineWF #0 ⇔ lenc #0 = 4̄ ∧ condQ1))`. No hay nada mas en el. -/
theorem ax_lineWF_q1_eq :
    ax_lineWF_q1
      = Formula.forall (Formula.impl (tagF 9) (lwfVar ⇔ Formula.and (lencF 4) condQ1)) := rfl

/-- **MEDIDA 1a — LA RESPUESTA A «¿menciona bien-formacion?».**
    La condicion ENTERA del esquema q1 es UNA ECUACION ATOMICA `a ≐ b`.
    Una ecuacion atomica no puede afirmar bien-formacion de nada: no hay `∃`, no hay `∧`,
    no hay ningun predicado salvo `≐`. Solo la ecuacion de `carc`. -/
theorem condQ1_es_UNA_ecuacion_atomica : ∃ a b : Term, condQ1 = Formula.eq a b :=
  ⟨_, _, rfl⟩

/-- Obligacion administrativa del chasis para q1: `C` solo menciona `#0`. Sale por `rfl`. -/
theorem substFormula_condQ1 : substFormula 0 (.var 0) condQ1 = condQ1 := rfl

/-- La condicion instanciada en una linea `t`: lo UNICO que el chasis pone en la mano de
    `hcond` ademas de `lineWF t` y `lenc t = 4̄`. Sigue siendo una sola ecuacion. -/
theorem substFormula_condQ1_at (t : Term) :
    substFormula 0 t condQ1
      = Formula.eq (carc t)
          (implc (forallc (nthc t (numeralM 2)))
                 (substfc zero (nthc t (numeralM 3)) (nthc t (numeralM 2)))) := by
  simp only [condQ1, carc, nthc, implc, forallc, substfc, numeralM, succ, zero, cons, nil,
    substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]

/-! ############################################################################
    # §2 · LOS OTROS AXIOMAS DE `lineWF`: TAMPOCO IMPONEN BIEN-FORMACION
    ############################################################################ -/

/-- `ax_lineWF_inv` dice SOLO que la etiqueta esta entre 0 y 20. Nada de las casillas. -/
theorem ax_lineWF_inv_eq :
    ax_lineWF_inv = Formula.forall (Formula.impl lwfVar (tagDisj (.var 0) 20)) := rfl

/-- Y `tagDisj` esta construida SOLO con ecuaciones sobre `lineTag` (= `nthc · 1̄`). -/
theorem tagDisj_base (L : Term) : tagDisj L 0 = Formula.eq (lineTag L) (numeralM 0) := rfl
theorem tagDisj_step (L : Term) (n : Nat) :
    tagDisj L (n + 1) = lor (Formula.eq (lineTag L) (numeralM (n + 1))) (tagDisj L n) := rfl

/-- `ax_lineWF_cons` dice SOLO que la linea es un `cons`. Nada de las casillas. -/
theorem ax_lineWF_cons_eq :
    ax_lineWF_cons
      = Formula.forall (Formula.impl lwfVar
          (Formula.eq (.var 0) (cons (carc (.var 0)) (cdrc (.var 0))))) := rfl

/-! ############################################################################
    # §3 · EL CHASIS SI ACEPTA q1 — el UNICO hueco es `hcond`
    ############################################################################ -/

/-- El esquema q1, disponible como `Prf` en la forma exacta que pide el chasis. -/
theorem prf_ax_q1 :
    Prf (Formula.forall (Formula.impl (tagF 9) (lwfVar ⇔ Formula.and (lencF 4) condQ1))) :=
  ax_lineWF_q1_eq ▸ prf_ax (show ax_lineWF_q1 ∈ axioms by simp [axioms])

/-- **MEDIDA 2.** El chasis generico cierra q1 EN UNA LLAMADA a partir de `hcond`.
    O sea: el tag 9 esta reducido EXACTAMENTE a `hcond`, y `hcond` recibe como tercer
    antecedente `substFormula 0 t condQ1` — la ecuacion de §1, NADA MAS. -/
theorem q1_reducido_a_hcond (t : Term)
    (hcond : Prf (lineWF t ⇒ ((lenc t =eq numeralM 4) ⇒
      (substFormula 0 t condQ1 ⇒ provFromCode (condD condQ1 t))))) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 9) ⇒
      provFromCode (lineWFCodeFn (tcFn t)))) :=
  pcc_lineWF_tracked_of_schema t substFormula_condQ1 prf_ax_q1 hcond (by omega)

/-! ############################################################################
    # §4 · LA LINEA BASURA: bien formada de tipo q1, con la casilla 2 = CODIGO DE
      VARIABLE (que NO es codigo de formula)
    ############################################################################ -/

/-- Casilla 2: codigo de la VARIABLE `#0`. **No es codigo de formula.** -/
def Ajunk : Term := varc zero
/-- Casilla 3: el codigo `0`. -/
def Sjunk : Term := zero
/-- La conclusion RECONSTRUIDA por el esquema q1 a partir de esa basura. -/
def CONCLjunk : Term := implc (forallc Ajunk) (substfc zero Sjunk Ajunk)
/-- La linea `⟨CONCLjunk, 9̄, varc 0, 0⟩`. -/
def Ljunk : Term := cons CONCLjunk (cons (numeralM 9) (cons Ajunk (cons Sjunk nil)))

/-- **MEDIDA 3 — LA CLAVE.** La linea basura es `lineWF`. Sale del propio esquema q1
    (`prf_lineWF_q1`, produccion), por reflexividad de la conclusion. -/
theorem prf_lineWF_Ljunk : Prf (lineWF Ljunk) :=
  prf_iff_mpr (prf_lineWF_q1 CONCLjunk Ajunk Sjunk) (prf_refl _)

/-- Y su etiqueta ES la 9: no se esta esquivando la rama. -/
theorem prf_tag_Ljunk : Prf (nthc Ljunk (succ zero) =eq numeralM 9) :=
  SinWTs.prf_nthc_c1 CONCLjunk (numeralM 9) (cons Ajunk (cons Sjunk nil))

/-- Y su longitud canonica ES 4. -/
theorem prf_lenc_Ljunk : Prf (lenc Ljunk =eq numeralM 4) :=
  prf_eq_trans (prf_lenc_cons _ _)
    (prf_eq_congr_succ (SinWTs.prf_lenc_c3 (numeralM 9) Ajunk Sjunk))

/-- Su casilla 2 es el codigo de VARIABLE. -/
theorem prf_nth2_Ljunk : Prf (nthc Ljunk (numeralM 2) =eq varc zero) :=
  SinWTs.prf_nthc_c2 CONCLjunk (numeralM 9) Ajunk (cons Sjunk nil)

/-! ############################################################################
    # §5 · EL RECONOCEDOR DE FORMULA RECHAZA ESA CASILLA
      (reconstruccion, sobre PRODUCCION, de `prf_isFormCodeE2_str` +
       `CRIT_E2_rejects_varc`, que viven en `sondeos/` pero no en `Meta/`)
    ############################################################################ -/

/-- Funtorialidad de `lor` en las dos ramas. -/
theorem lor_map {A A' B B' : Formula} (hA : Prf (A ⇒ A')) (hB : Prf (B ⇒ B')) :
    Prf (lor A B ⇒ lor A' B') :=
  ENS.prf_or_elim_imp (ENS.impT hA (SinWTs.prf_lorL _ _)) (ENS.impT hB (SinWTs.prf_lorR _ _))

theorem prf_shapeNul_str (X : Term) (k : Nat) :
    Prf (Formula.impl (ENS.shapeNul X k)
      (land (SinWTs.consOk X) (land (Formula.eq (carc X) (numeralM k))
                                    (Formula.eq (lenc X) (numeralM 1))))) :=
  SinWTs.prf_shape_strengthens X _ k 1 (prf_carc_cons _ _)
    (SinWTs.prf_lenc_c1 _) (SinWTs.prf_consOk_cons _ _)

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

/-- Un codigo de VARIABLE no pasa por el reconocedor de FORMULA. -/
theorem CRIT_E2_rejects_varc (wF wT n : Term) :
    Prf (Formula.impl (ENS.isFormCodeE2 wF wT (varc n)) Formula.bottom) :=
  ENS.impT (prf_isFormCodeE2_str wF wT (varc n))
    (SinWTs.crit_isFormCodeB2_rejects_varc wF wT n)

/-- **Version CONGRUENTE** (la que hace falta aqui: la casilla es `nthc Ljunk 2̄`, no
    literalmente `varc n`). La guarda `isFC1` rechaza todo `X` OBJETO-IGUAL a un `varc n`. -/
theorem CRIT_isFC1_rejects_eqvarc (wF wT X n : Term) (heq : Prf (X =eq varc n)) :
    Prf (Formula.impl (ENS.isFC1 wF wT X) Formula.bottom) := by
  refine prf_deduction ?_
  have hh := prfH_hyp_self (ENS.isFC1 wF wT X)
  have hwF := PrfH_and_elim_right (PrfH_and_elim_left hh)
  have hin := PrfH_and_elim_right hh
  have hcode := PrfH.mp _ _ _ (PrfH.mp _ _ _
    (prf_to_prfH (ENS.prf_isFormCodeE2_of_In wF wT X) _) hin) hwF
  have hcode2 := ENS.PrfH_congr_isFormCodeE2 (prf_to_prfH heq _) hcode
  exact PrfH.mp _ _ _ (prf_to_prfH (CRIT_E2_rejects_varc wF wT n) _) hcode2

/-- Y lo mismo con los DOS testigos CUANTIFICADOS: la guarda real `hasWitF`. -/
theorem CRIT_hasWitF_rejects_eqvarc (X n : Term) (heq : Prf (X =eq varc n))
    (hlift : liftTerm 0 (liftTerm 0 X) = X) :
    Prf (Formula.impl (ENS.hasWitF X) Formula.bottom) := by
  refine prf_deduction ?_
  have hh : PrfH [ENS.hasWitF X]
      (Formula.ex (Formula.ex (ENS.isFC1 (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 X))))) :=
    prfH_hyp_self _
  rw [hlift] at hh
  refine PrfH_ex_elim hh ?_
  refine PrfH_ex_elim (PrfH.hyp _ _ (List.Mem.head _)) ?_
  exact PrfH.mp _ _ _
    (prf_to_prfH (CRIT_isFC1_rejects_eqvarc (.var 1) (.var 0) X n heq) _)
    (PrfH.hyp _ _ (List.Mem.head _))

/-- La casilla 2 de la linea basura es un termino CERRADO: el lift es la identidad. -/
theorem lift_nth2_Ljunk :
    liftTerm 0 (liftTerm 0 (nthc Ljunk (numeralM 2))) = nthc Ljunk (numeralM 2) := rfl

/-- La guarda de q1, evaluada en la linea basura, es REFUTABLE. -/
theorem CRIT_hasWitF_nth2_Ljunk :
    Prf (Formula.impl (ENS.hasWitF (nthc Ljunk (numeralM 2))) Formula.bottom) :=
  CRIT_hasWitF_rejects_eqvarc (nthc Ljunk (numeralM 2)) zero prf_nth2_Ljunk lift_nth2_Ljunk

/-! ############################################################################
    # §6 · LA MEDICION: LA HIPOTESIS (A) ESTA REFUTADA
    ############################################################################ -/

/-- **RESULTADO.** Si `lineWF t` implicase la guarda (aunque sea SOLO para esta linea),
    la teoria objeto probaria `⊥`. La linea basura es bien formada de tipo q1 y su
    casilla 2 no es codigo de formula: `lineWF` no dice nada de las casillas. -/
theorem MEDIDA_A_REFUTADA
    (hA : Prf (lineWF Ljunk ⇒ ENS.hasWitF (nthc Ljunk (numeralM 2)))) :
    Prf Formula.bottom :=
  prf_mp CRIT_hasWitF_nth2_Ljunk (prf_mp hA prf_lineWF_Ljunk)

/-- La misma, en la forma ESQUEMATICA (`t` universal) que consumiria la rama C. -/
theorem MEDIDA_A_REFUTADA_esquematica
    (hA : ∀ t : Term, Prf (lineWF t ⇒ ENS.hasWitF (nthc t (numeralM 2)))) :
    Prf Formula.bottom :=
  MEDIDA_A_REFUTADA (hA Ljunk)

/-- Y tampoco vale ANADIR la hipotesis del tag: la linea basura la cumple. -/
theorem MEDIDA_A_REFUTADA_con_tag
    (hA : ∀ t : Term, Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 9) ⇒
      ENS.hasWitF (nthc t (numeralM 2))))) :
    Prf Formula.bottom :=
  prf_mp CRIT_hasWitF_nth2_Ljunk
    (prf_mp (prf_mp (hA Ljunk) prf_lineWF_Ljunk) prf_tag_Ljunk)

/-- Y tampoco anadiendo ADEMAS la longitud canonica: la linea basura tambien la cumple. -/
theorem MEDIDA_A_REFUTADA_con_tag_y_lenc
    (hA : ∀ t : Term, Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 9) ⇒
      ((lenc t =eq numeralM 4) ⇒ ENS.hasWitF (nthc t (numeralM 2)))))) :
    Prf Formula.bottom :=
  prf_mp CRIT_hasWitF_nth2_Ljunk
    (prf_mp (prf_mp (prf_mp (hA Ljunk) prf_lineWF_Ljunk) prf_tag_Ljunk) prf_lenc_Ljunk)

/-! ### Y tampoco anadiendo la CONDICION ESTRUCTURAL ENTERA del esquema

Ni siquiera `hcond` — que recibe `lineWF t`, `lenc t = 4̄` **y** `substFormula 0 t condQ1` —
tiene con que sacar la guarda: la linea basura satisface los TRES antecedentes. -/

/-- Casilla 2 de la linea basura, en la forma `nthc ... ≐ Ajunk`. -/
theorem prf_nth2_Ljunk' : Prf (nthc Ljunk (numeralM 2) =eq Ajunk) :=
  SinWTs.prf_nthc_c2 CONCLjunk (numeralM 9) Ajunk (cons Sjunk nil)

/-- Casilla 3 de la linea basura. -/
theorem prf_nth3_Ljunk' : Prf (nthc Ljunk (numeralM 3) =eq Sjunk) :=
  prf_eq_trans
    (prf_nthc_succ CONCLjunk (cons (numeralM 9) (cons Ajunk (cons Sjunk nil))) (numeralM 2))
    (SinWTs.prf_nthc_c2 (numeralM 9) Ajunk Sjunk nil)

theorem prf_condQ1_at_Ljunk : Prf (substFormula 0 Ljunk condQ1) := by
  rw [substFormula_condQ1_at]
  exact prf_eq_trans (prf_carc_cons _ _)
    (prf_congr_bin (prf_congr_un (prf_eq_symm prf_nth2_Ljunk'))
      (prf_eq_trans (prf_congr_substfc_arg2 (prf_eq_symm prf_nth3_Ljunk'))
                    (prf_congr_substfc_arg3 (prf_eq_symm prf_nth2_Ljunk'))))

theorem MEDIDA_A_REFUTADA_con_TODO_el_antecedente_de_hcond
    (hA : ∀ t : Term, Prf (lineWF t ⇒ ((lenc t =eq numeralM 4) ⇒
      (substFormula 0 t condQ1 ⇒ ENS.hasWitF (nthc t (numeralM 2)))))) :
    Prf Formula.bottom :=
  prf_mp CRIT_hasWitF_nth2_Ljunk
    (prf_mp (prf_mp (prf_mp (hA Ljunk) prf_lineWF_Ljunk) prf_lenc_Ljunk) prf_condQ1_at_Ljunk)

/-! ############################################################################
    # §6bis · LA OTRA MITAD DE LA GUARDA (`hasWit (nthc t 3̄)`, el testigo de TERMINO)
      TAMPOCO SALE DE `lineWF`
    ############################################################################ -/

/-- Congruencia de `carc` en `Prf` (espejo literal de `SinWTs.prf_congr_lenc`). -/
theorem prf_congr_carc {t₁ t₂ : Term} (h : Prf (t₁ =eq t₂)) : Prf (carc t₁ =eq carc t₂) := by
  let f : Formula := Formula.eq (carc (liftTerm 0 t₁)) (carc (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (carc t₁) (carc s) := by
    intro s
    simp only [f, carc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact prfH_nil_to_prf
    ((hS t₂) ▸ ROBINSON_PlusPlus.Meta.ChainPrf.PrfH_leibniz_subst (A := f) (prf_to_prfH h [])
      ((hS t₁) ▸ prf_to_prfH (prf_refl (carc t₁)) [])) rfl

/-- El testigo de TERMINO tambien DISCRIMINA: `hasWit c` es refutable para todo `c` cerrado
    cuyo tag no sea 0 (`varc`) ni 1 (`funcc`). -/
theorem CRIT_hasWit_rejects (c : Term) (k : Nat) (hk0 : k ≠ 0) (hk1 : k ≠ 1)
    (hcl : ∀ n : Nat, liftTerm n c = c) (hck : Prf (carc c =eq numeralM k)) :
    Prf (Formula.impl (ENS.hasWit c) Formula.bottom) := by
  refine prf_deduction ?_
  have hh : PrfH [ENS.hasWit c] (Formula.ex (SinWTs.isTC1 (.var 0) (liftTerm 0 c))) :=
    prfH_hyp_self _
  rw [hcl 0] at hh
  have hkill : Prf (Formula.impl (In c (.var 0)) (Formula.impl (SinWTs.wfAll1 (.var 0))
      Formula.bottom)) :=
    SinWTs.impT (prf_boundedIn_of_In c (.var 0))
      (SinWTs.prf_crit_In_rejects_open1 (.var 0) c k hk0 hk1 hcl hck)
  refine PrfH_ex_elim hh ?_
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH hkill _)
    (PrfH_and_elim_right (PrfH.hyp _ _ (List.Mem.head _))))
    (PrfH_and_elim_left (PrfH.hyp _ _ (List.Mem.head _)))

/-- Segunda linea basura: casilla 2 = codigo de formula REAL (⊥), casilla 3 = `botc`,
    que es un codigo de FORMULA metido en la ranura de TERMINO. -/
def A2 : Term := formCodeM Formula.bottom
def S2 : Term := botc
def CONCL2 : Term := implc (forallc A2) (substfc zero S2 A2)
def L2 : Term := cons CONCL2 (cons (numeralM 9) (cons A2 (cons S2 nil)))

theorem prf_lineWF_L2 : Prf (lineWF L2) :=
  prf_iff_mpr (prf_lineWF_q1 CONCL2 A2 S2) (prf_refl _)

theorem prf_tag_L2 : Prf (nthc L2 (succ zero) =eq numeralM 9) :=
  SinWTs.prf_nthc_c1 CONCL2 (numeralM 9) (cons A2 (cons S2 nil))

theorem prf_nth3_L2 : Prf (nthc L2 (numeralM 3) =eq S2) :=
  prf_eq_trans
    (prf_nthc_succ CONCL2 (cons (numeralM 9) (cons A2 (cons S2 nil))) (numeralM 2))
    (SinWTs.prf_nthc_c2 (numeralM 9) A2 S2 nil)

theorem carc_nth3_L2 : Prf (carc (nthc L2 (numeralM 3)) =eq numeralM 2) :=
  prf_eq_trans (prf_congr_carc prf_nth3_L2) (prf_carc_cons (numeralM 2) nil)

theorem lift_nth3_L2 : ∀ n : Nat, liftTerm n (nthc L2 (numeralM 3)) = nthc L2 (numeralM 3) :=
  fun _ => rfl

theorem CRIT_hasWit_nth3_L2 :
    Prf (Formula.impl (ENS.hasWit (nthc L2 (numeralM 3))) Formula.bottom) :=
  CRIT_hasWit_rejects (nthc L2 (numeralM 3)) 2 (by decide) (by decide)
    lift_nth3_L2 carc_nth3_L2

/-- **RESULTADO 2.** La OTRA mitad de la guarda tampoco sale de `lineWF`. -/
theorem MEDIDA_A_REFUTADA_mitad_TERMINO
    (hA : ∀ t : Term, Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 9) ⇒
      ENS.hasWit (nthc t (numeralM 3))))) :
    Prf Formula.bottom :=
  prf_mp CRIT_hasWit_nth3_L2 (prf_mp (prf_mp (hA L2) prf_lineWF_L2) prf_tag_L2)

/-! ############################################################################
    # §7 · ¿SUBE LA GUARDA? — SI: atraviesa el ensamblador y acaba EN EL ENUNCIADO
      de `pcc_lineWF_tracked` (y por tanto en el de D3)
    ############################################################################ -/

/-- **Ensamblador GUARDADO.** Si las 21 ramas solo se prueban bajo una guarda OBJETO `G`,
    el ensamblador sigue funcionando — pero lo que sale NO es `pcc_lineWF_tracked`, es
    `G ⇒ pcc_lineWF_tracked`. La guarda no se absorbe en ningun sitio: SUBE ENTERA. -/
theorem pcc_lineWF_tracked_of_branches_GUARDADO (t : Term) (G : Formula)
    (hbranch : ∀ k : Nat, Prf (G ⇒ (lineWF t ⇒ ((lineTag t =eq numeralM k) ⇒
      provFromCode (lineWFCodeFn (tcFn t)))))) :
    Prf (G ⇒ (lineWF t ⇒ provFromCode (lineWFCodeFn (tcFn t)))) := by
  -- se lleva el TAG al frente (es sobre el que recorre el ensamblador)
  have hbranch' : ∀ k : Nat, Prf ((lineTag t =eq numeralM k) ⇒
      (G ⇒ (lineWF t ⇒ provFromCode (lineWFCodeFn (tcFn t))))) := by
    intro k
    refine prf_deduction (deduction_aux (deduction_aux ?_ (lineWF t)
      [G, lineTag t =eq numeralM k] rfl) G [lineTag t =eq numeralM k] rfl)
    let Γ : List Formula := [lineWF t, G, lineTag t =eq numeralM k]
    have hLW : PrfH Γ (lineWF t) := PrfH.hyp _ _ (List.Mem.head _)
    have hG : PrfH Γ G := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
    have hTag : PrfH Γ (lineTag t =eq numeralM k) :=
      PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    exact PrfH.mp _ _ _ (PrfH.mp _ _ _
      (PrfH.mp _ _ _ (prf_to_prfH (hbranch k) Γ) hG) hLW) hTag
  have hall : Prf (tagDisj t 20 ⇒ (G ⇒ (lineWF t ⇒ provFromCode (lineWFCodeFn (tcFn t))))) :=
    prf_of_tagDisj t _ hbranch' 20
  refine prf_deduction (deduction_aux ?_ (lineWF t) [G] rfl)
  have hlw : PrfH [lineWF t, G] (lineWF t) := PrfH.hyp _ _ (List.Mem.head _)
  have hG2 : PrfH [lineWF t, G] G := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hdisj : PrfH [lineWF t, G] (tagDisj t 20) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_lineWF_inv t) _) hlw
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH hall _) hdisj) hG2) hlw

/-- Y con la guarda de q1 puesta con su nombre: lo que la rama C podria entregar, en el mejor
    de los casos, es esto — un `pcc_lineWF_tracked` **con la guarda en el antecedente**. -/
theorem tracked_GUARDADO_por_hasWitF (t : Term)
    (hbranch : ∀ k : Nat, Prf (ENS.hasWitF (nthc t (numeralM 2)) ⇒
      (lineWF t ⇒ ((lineTag t =eq numeralM k) ⇒ provFromCode (lineWFCodeFn (tcFn t)))))) :
    Prf (ENS.hasWitF (nthc t (numeralM 2)) ⇒
      (lineWF t ⇒ provFromCode (lineWFCodeFn (tcFn t)))) :=
  pcc_lineWF_tracked_of_branches_GUARDADO t _ hbranch

/-! ############################################################################
    # §8 · CONTROLES — que esto no sea vacuo
    ############################################################################ -/

/-- CONTROL POSITIVO: la guarda NO es refutable en general — es DEMOSTRABLE para todo
    codigo de formula REAL (`HW.prf_hasWitF_real`, produccion). O sea: `hasWitF` discrimina,
    y lo que falla es que `lineWF` no la implica. -/
example (phi : Formula) : Prf (ENS.hasWitF (formCodeM phi)) := HW.prf_hasWitF_real phi

/-- CONTROL POSITIVO 2: una linea q1 con casilla 2 = codigo de formula REAL tambien es
    `lineWF`; la construccion de §4 no explota nada raro del esquema. -/
example (phi : Formula) (s : Term) :
    Prf (lineWF (cons (implc (forallc (formCodeM phi)) (substfc zero s (formCodeM phi)))
      (cons (numeralM 9) (cons (formCodeM phi) (cons s nil))))) :=
  prf_iff_mpr (prf_lineWF_q1 _ (formCodeM phi) s) (prf_refl _)

/-- CONTROL NEGATIVO: `condQ1` no es trivial ni es `⊤` disfrazado. -/
example : True := by
  fail_if_success exact (rfl : condQ1 = Formula.bottom)
  trivial

/-- CONTROL NEGATIVO: la linea basura NO es la linea buena — son terminos distintos. -/
example (phi : Formula) : True := by
  fail_if_success exact (rfl : Ajunk = formCodeM phi)
  trivial

end MCderiva

#print axioms MCderiva.ax_lineWF_q1_eq
#print axioms MCderiva.condQ1_es_UNA_ecuacion_atomica
#print axioms MCderiva.ax_lineWF_inv_eq
#print axioms MCderiva.ax_lineWF_cons_eq
#print axioms MCderiva.q1_reducido_a_hcond
#print axioms MCderiva.prf_lineWF_Ljunk
#print axioms MCderiva.prf_tag_Ljunk
#print axioms MCderiva.prf_lenc_Ljunk
#print axioms MCderiva.prf_nth2_Ljunk
#print axioms MCderiva.prf_condQ1_at_Ljunk
#print axioms MCderiva.CRIT_hasWitF_nth2_Ljunk
#print axioms MCderiva.MEDIDA_A_REFUTADA
#print axioms MCderiva.MEDIDA_A_REFUTADA_esquematica
#print axioms MCderiva.MEDIDA_A_REFUTADA_con_tag
#print axioms MCderiva.MEDIDA_A_REFUTADA_con_tag_y_lenc
#print axioms MCderiva.MEDIDA_A_REFUTADA_con_TODO_el_antecedente_de_hcond
#print axioms MCderiva.prf_lineWF_L2
#print axioms MCderiva.CRIT_hasWit_nth3_L2
#print axioms MCderiva.MEDIDA_A_REFUTADA_mitad_TERMINO
#print axioms MCderiva.pcc_lineWF_tracked_of_branches_GUARDADO
#print axioms MCderiva.tracked_GUARDADO_por_hasWitF

#check @MCderiva.MEDIDA_A_REFUTADA_esquematica
#check @MCderiva.MEDIDA_A_REFUTADA_con_TODO_el_antecedente_de_hcond
#check @MCderiva.q1_reducido_a_hcond
#check @ROBINSON_PlusPlus.Meta.LineWFAssemblePrf.pcc_lineWF_tracked_modulo_7
