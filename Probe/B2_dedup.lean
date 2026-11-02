import ROBINSON_PlusPlus.Meta

/-
# B2 · AUDITORIA DE DUPLICACION de `sondeos/DescensoLiftc.lean` (2011 lineas, 198 decls)

Este fichero NO promueve nada y NO toca `Meta/`. Solo PRUEBA, con Lean compilado, en cual de
los tres cajones cae cada una de las **39** declaraciones del sondeo que NO estan en produccion
por nombre:

  1. DUPLICADO EXACTO   — ya existe en produccion (otro nombre / orientacion invertida)
  2. CASI-DUPLICADO     — produccion tiene el caso particular, o el sondeo lo particulariza
  3. GENUINAMENTE NUEVO

Metodo: las definiciones del sondeo se COPIAN VERBATIM al namespace `Sonda`, **bajo los MISMOS
`open` que el sondeo** (mismo texto con `open`s distintos elabora DISTINTO), y se enfrentan a
produccion con puentes `:= rfl` que tienen que salir NET-0.

    lake env lean Probe\B2_dedup.lean
-/

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.TcArithPrf ROBINSON_PlusPlus.Meta.CheckArith
open ROBINSON_PlusPlus.Meta.Sigma1Prf ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.MpCodePrf ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
open ROBINSON_PlusPlus.Meta.NumCodeClosedPrf ROBINSON_PlusPlus.Meta.EvalArithPrf
open ROBINSON_PlusPlus.Meta.EvalListPrf ROBINSON_PlusPlus.Meta.EvalLtPrf
open ROBINSON_PlusPlus.Meta.EvalNthcPrf ROBINSON_PlusPlus.Meta.NatArithPrf
open ROBINSON_PlusPlus.Meta.DotConsPrf ROBINSON_PlusPlus.Meta.DerivCondPrf
open ROBINSON_PlusPlus.Meta.CodeCtorKit ROBINSON_PlusPlus.Meta.BdAllIntroPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction ROBINSON_PlusPlus.Meta.BoundedInPrf
open ROBINSON_PlusPlus.Meta.ChainPrf ROBINSON_PlusPlus.Meta.ChainOkBoundedPrf
open ROBINSON_PlusPlus.Meta.TrackedCorePrf ROBINSON_PlusPlus.Meta.Sigma1CorePrf
open ROBINSON_PlusPlus.Meta.EvalBoundedPrf ROBINSON_PlusPlus.Meta.InAxiomsCodePrf
open ROBINSON_PlusPlus.Meta.Delta0ReflectPrf ROBINSON_PlusPlus.Meta.D3InDotPrf
open ROBINSON_PlusPlus.Meta.NumListPrf ROBINSON_PlusPlus.Meta.CantorMonoPrf
open ROBINSON_PlusPlus.Meta.StrongInductionPrf
-- añadidos SOLO para poder nombrar produccion (el sondeo no los abre porque se lo redefine todo)
open ROBINSON_PlusPlus.Meta.EvalRunFnPrf ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace B2Dedup

/-! ############################################################################
    ## §0 · COPIAS VERBATIM del sondeo (namespace `Sonda`)

    Todas estas definiciones estan YA en produccion por nombre (son de las 159), pero el
    sondeo las REDEFINE. Los puentes de §1 prueban que son las MISMAS constantes modulo
    delta, es decir: al promover hay que BORRARLAS y consumir produccion.
    ############################################################################ -/

namespace Sonda

-- `sondeos/DescensoLiftc.lean:56-63`
def liftcT (c t : Term) : Term := funcc (strCode "liftc") (cons c (cons t nil))
def liftscT (c ts : Term) : Term := funcc (strCode "liftsc") (cons c (cons ts nil))
def varcT (X : Term) : Term := unT 0 X
def funccT (X Y : Term) : Term := binT 1 X Y

-- `:79-83`
def targetLift (s : Term) : Formula :=
  provFromCode (eqc (liftcT (termCode zero) (tcFn s)) (tcFn (liftc zero s)))
-- `:535`
def targetLiftsc (b : Term) : Formula :=
  provFromCode (eqc (liftscT (termCode zero) (tcFn b)) (tcFn (liftsc zero b)))

-- `:676-680`
def shapeUn (X : Term) (k : Nat) : Formula :=
  Formula.eq X (cons (numeralM k) (cons (nthc X (numeralM 1)) nil))
def shapeBin (X : Term) (k : Nat) : Formula :=
  Formula.eq X (cons (numeralM k)
    (cons (nthc X (numeralM 1)) (cons (nthc X (numeralM 2)) nil)))

-- `:862-868`
def argsInBody (wT Y : Term) : Formula :=
  Formula.impl (lt (.var 0) (liftTerm 0 (lenc Y)))
    (In (nthc (liftTerm 0 Y) (.var 0)) (liftTerm 0 wT))
def argsIn (wT Y : Term) : Formula := Formula.forall (argsInBody wT Y)

def isTermCodeE1 (wT X : Term) : Formula :=
  lor (shapeUn X 0) (land (shapeBin X 1) (argsIn wT (nthc X (numeralM 2))))

-- `:889-899`
def consOk (X : Term) : Formula := Formula.eq X (cons (carc X) (cdrc X))
def cOk (X : Term) (F : Formula) : Formula := land (consOk X) F

def wfAll1Body (w : Term) : Formula :=
  Formula.impl (lt (.var 0) (liftTerm 0 (lenc w)))
    (isTermCodeE1 (liftTerm 0 w) (nthc (liftTerm 0 w) (.var 0)))
def wfAll1 (w : Term) : Formula := Formula.forall (wfAll1Body w)
def isTC1 (w c : Term) : Formula := land (wfAll1 w) (In c w)

-- `:1386`
def hasWit (c : Term) : Formula := Formula.ex (isTC1 (.var 0) (liftTerm 0 c))

/-! ### Las que SI estan en la lista de 39 (definiciones) -/

-- `:1085`
def nilOrCons : Formula := lor (Formula.eq (.var 0) nil) (consOk (.var 0))

-- `:1192-1197`
def PHIbody : Formula :=
  land (Formula.impl (isTC1 (.var 0) (.var 1)) (targetLift (.var 1)))
       (Formula.impl (land (wfAll1 (.var 0)) (argsIn (.var 0) (.var 1)))
         (targetLiftsc (.var 1)))
def PHI : Formula := Formula.forall PHIbody

-- `:1909-1910`
def tEjA : Term := succ (Term.var 0)
def tEjB : Term := add (succ (Term.var 0)) (Term.var 1)

end Sonda

/-! ############################################################################
    ## §1 · PUENTES `rfl`: las copias del sondeo SON las constantes de produccion
    ############################################################################ -/

theorem br_liftcT : @Sonda.liftcT = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.liftcT := rfl
theorem br_liftscT : @Sonda.liftscT = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.liftscT := rfl
theorem br_varcT : @Sonda.varcT = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.varcT := rfl
theorem br_funccT : @Sonda.funccT = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.funccT := rfl

/-- ⚠️⚠️ **`targetLift` YA ESTA EN PRODUCCION** (`Meta/LiftcCodePrf.lean:225`). -/
theorem br_targetLift : @Sonda.targetLift = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLift := rfl
theorem br_targetLiftsc :
    @Sonda.targetLiftsc = @ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLiftsc := rfl

theorem br_shapeUn : @Sonda.shapeUn = @SinWTs.shapeUn := rfl
theorem br_shapeBin : @Sonda.shapeBin = @SinWTs.shapeBin := rfl
theorem br_argsInBody : @Sonda.argsInBody = @SinWTs.argsInBody := rfl
theorem br_argsIn : @Sonda.argsIn = @SinWTs.argsIn := rfl
theorem br_isTermCodeE1 : @Sonda.isTermCodeE1 = @SinWTs.isTermCodeE1 := rfl
theorem br_consOk : @Sonda.consOk = @SinWTs.consOk := rfl
theorem br_cOk : @Sonda.cOk = @SinWTs.cOk := rfl
theorem br_wfAll1Body : @Sonda.wfAll1Body = @SinWTs.wfAll1Body := rfl
theorem br_wfAll1 : @Sonda.wfAll1 = @SinWTs.wfAll1 := rfl
theorem br_isTC1 : @Sonda.isTC1 = @SinWTs.isTC1 := rfl
theorem br_hasWit : @Sonda.hasWit = @ENS.hasWit := rfl

/-! ############################################################################
    ## §2 · CALIBRACION — los DOS duplicados que el orquestador ya conocia.
       Si el metodo no los caza, el metodo no vale.
    ############################################################################ -/

/-- **`iz_inv` (`:538`) = `EvalRunFnPrf.prf_substtc_termCode_nil`**, porque `nil := zero`
    (`Minimal/Axioms.lean:126`). El enunciado del sondeo se HABITA con la constante de
    produccion **sin ninguna tactica**: son el mismo tipo modulo delta. -/
theorem dup_iz_inv : ∀ W, Prf (substtc zero W (termCode zero) =eq termCode zero) :=
  prf_substtc_termCode_nil

/-- Y en la otra direccion, como igualdad de TIPOS. -/
theorem br_iz_inv :
    (∀ W, Prf (substtc zero W (termCode zero) =eq termCode zero))
      = (∀ W, Prf (substtc zero W (termCode nil) =eq termCode nil)) := rfl

/-- **`eqc_eq_eqCodeFn` (`:74`) = `Sigma1AtomPrf.eqCodeFn_eq_eqc` INVERTIDO.** -/
theorem dup_eqc_eq_eqCodeFn (a b : Term) : eqc a b = eqCodeFn a b :=
  (eqCodeFn_eq_eqc a b).symm

/-! ############################################################################
    ## §3 · LOS DUPLICADOS **NUEVOS** QUE ENCUENTRA ESTA AUDITORIA
    ############################################################################ -/

/-! ### 3.1 · `CRIT_antecedente_discrimina` (`:1941`) **ES** `SinWTs.crit_junk_var0_witness1`
       (`Meta/CodeWitnessPrf.lean:1160`), renombrado. Mismo tipo, misma prueba (el sondeo lo
       define literalmente como `crit_junk_var0_witness1 hjunk`). -/

theorem dup_CRIT_antecedente_discrimina :
    Prf (Sonda.isTC1 (.var 0) (implc (termCodeM (Term.var 0)) (termCodeM (Term.var 0))))
      → Prf Formula.bottom :=
  SinWTs.crit_junk_var0_witness1

/-- Igualdad de TIPOS, no solo habitacion. -/
theorem br_CRIT_antecedente_discrimina :
    (Prf (Sonda.isTC1 (.var 0) (implc (termCodeM (Term.var 0)) (termCodeM (Term.var 0))))
      → Prf Formula.bottom)
    = (Prf (SinWTs.isTC1 (.var 0) (implc (termCodeM (.var 0)) (termCodeM (.var 0))))
      → Prf Formula.bottom) := rfl

/-! ### 3.2 · `pcc_eval_liftc` (`:1379`) **ES** `DESCENSO` (`:1371`): el mismo tipo, con
       `targetLift` desplegado a mano. Es un duplicado INTERNO del propio sondeo. -/

theorem br_pcc_eval_liftc_es_DESCENSO (w s : Term) :
    (Prf (Sonda.isTC1 w s) →
       Prf (provFromCode (eqc (Sonda.liftcT (termCode zero) (tcFn s)) (tcFn (liftc zero s)))))
    = (Prf (Sonda.isTC1 w s) → Prf (Sonda.targetLift s)) := rfl

/-- Y con el vocabulario de PRODUCCION en los dos lados. -/
theorem br_pcc_eval_liftc_produccion (w s : Term) :
    (Prf (SinWTs.isTC1 w s) →
       Prf (provFromCode (eqc (liftcT (termCode zero) (tcFn s)) (tcFn (liftc zero s)))))
    = (Prf (SinWTs.isTC1 w s) → Prf (targetLift s)) := rfl

/-! ### 3.3 · `CRIT_hasWit_descenso` (`:1972`) tiene EL MISMO ENUNCIADO que
       `CRIT_targetLift_real` (`:1904`). Duplicado INTERNO de enunciado (dos rutas de prueba). -/

theorem br_CRIT_hasWit_descenso_es_CRIT_targetLift_real (t : Term) :
    (Prf (Sonda.targetLift (termCodeM t))) = (Prf (targetLift (termCodeM t))) := rfl

/-! ### 3.4 · ⚠️ **EL HALLAZGO GORDO**: los SEIS controles `CRIT_*_real` tienen enunciados que
       PRODUCCION YA PRUEBA sola, sin ningun descenso: `LiftcCodePrf.refl_termCode` /
       `refl_termsCode` (recursion META sobre `termCode`) mas el puente
       `Representability.termCodeM_eq : termCodeM t = termCode t`.

       No son duplicados EXACTOS (`termCodeM ≠ termCode` por defeq: uno usa `numeralM`/`strCodeM`
       y el otro `numeral`/`strCode`), pero como ENUNCIADO no aportan nada nuevo: su valor es la
       RUTA (que el DESCENSO dispara), no el teorema. -/

theorem prod_targetLift_termCodeM (t : Term) : Prf (targetLift (termCodeM t)) := by
  rw [ROBINSON_PlusPlus.Meta.Representability.termCodeM_eq]
  exact refl_termCode t

theorem prod_targetLiftsc_termsCodeM (ts : List Term) :
    Prf (targetLiftsc (termsCodeM ts)) := by
  rw [ROBINSON_PlusPlus.Meta.Representability.termsCodeM_eq]
  exact refl_termsCode ts

/-- `CRIT_targetLift_real` (`:1904`), probado SIN el descenso. -/
theorem dup_CRIT_targetLift_real (t : Term) : Prf (Sonda.targetLift (termCodeM t)) :=
  prod_targetLift_termCodeM t

/-- `CRIT_real_A` (`:1912`) y `CRIT_real_B` (`:1913`), idem. -/
theorem dup_CRIT_real_A : Prf (Sonda.targetLift (termCodeM Sonda.tEjA)) :=
  prod_targetLift_termCodeM _
theorem dup_CRIT_real_B : Prf (Sonda.targetLift (termCodeM Sonda.tEjB)) :=
  prod_targetLift_termCodeM _

/-- `CRIT_targetLiftsc_real` (`:1917`) — y ademas el parametro `f : String` del sondeo es
    **inerte** (no aparece en la conclusion): la version de produccion no lo necesita. -/
theorem dup_CRIT_targetLiftsc_real (f : String) (ts : List Term) :
    Prf (Sonda.targetLiftsc (termsCodeM ts)) :=
  prod_targetLiftsc_termsCodeM ts

/-- `CRIT_real_lista` (`:1934`). -/
theorem dup_CRIT_real_lista :
    Prf (Sonda.targetLiftsc (termsCodeM [succ (Term.var 0), Term.var 1])) :=
  prod_targetLiftsc_termsCodeM _

/-- `CRIT_hasWit_descenso` (`:1972`). -/
theorem dup_CRIT_hasWit_descenso (t : Term) : Prf (Sonda.targetLift (termCodeM t)) :=
  prod_targetLift_termCodeM t

/-- CONTROL NEGATIVO: `termCodeM` NO es defeq a `termCode` — luego lo anterior no es
    trivialidad sintactica, hace falta el puente `termCodeM_eq`. -/
example : True := by
  fail_if_success exact (rfl : @termCodeM = @termCode)
  trivial

/-! ############################################################################
    ## §4 · CASI-DUPLICADOS — los peligrosos
    ############################################################################ -/

/-! ### 4.1 · `substF_targetLift` (`:1060`) **SUBSUME** a
       `LiftcCodePrf.substF_targetLift_hole` (`Meta/LiftcCodePrf.lean:790`), que es su caso
       `v := 0`, `s := #0`. Promover el general obliga a REESCRIBIR el de produccion como
       corolario, o quedan dos lemas para lo mismo. -/

theorem substF_targetLift_gen (v : Nat) (u s : Term) :
    substFormula v u (targetLift s) = targetLift (substTerm v u s) := by
  simp only [targetLift, substFormula_provFromCode_open, eqc, liftcT, funcc, tcFn, liftc,
    cons, nil, zero, succ, substTerm, substTerms, substTerm_termCode, substTerm_strCode]

/-- El lema de produccion, DERIVADO del general en dos lineas. -/
theorem prod_substF_targetLift_hole_desde_el_general (t : Term) :
    substFormula 0 t (provFromCode (eqc (liftcT (termCode zero) (tcFn (.var 0)))
        (tcFn (liftc zero (.var 0)))))
      = targetLift t := by
  have h := substF_targetLift_gen 0 t (.var 0)
  rwa [show substTerm 0 t (Term.var 0) = t from by simp only [substTerm, if_true]] at h

/-! ### 4.2 · `psi_lift_form` (`:1222`) y `PSI_inst` (`:1227`) son INSTANCIAS `Φ := PHI` de
       maquinaria GENERICA que pertenece a `Meta/StrongInductionPrf.lean`. `psi_lift_form` sale
       en DOS lineas de `psi_lift_eq_subst` + `psi_at`, ambos YA en produccion. -/

theorem psi_lift_form_gen (Φ : Formula) (hΦ : liftFormula 1 Φ = Φ) :
    liftFormula 0 (PSI Φ) = Formula.forall (Formula.impl (lt (.var 0) (.var 2)) Φ) := by
  rw [psi_lift_eq_subst Φ hΦ, psi_at]
  simp only [liftTerm, Nat.reduceLT, reduceIte, Nat.reduceAdd]

theorem PSI_inst_gen {Γ : List Formula} (Φ : Formula) (hΦ : liftFormula 1 Φ = Φ)
    (hpsi : PrfH Γ (liftFormula 0 (PSI Φ))) (z : Term) :
    PrfH Γ (Formula.impl (lt z (.var 1)) (substFormula 0 z Φ)) := by
  rw [psi_lift_form_gen Φ hΦ] at hpsi
  have h := PrfH_spec hpsi z
  have e : substFormula 0 z (Formula.impl (lt (.var 0) (.var 2)) Φ)
      = Formula.impl (lt z (.var 1)) (substFormula 0 z Φ) := by
    simp only [substFormula, lt, substTerm, substTerms, Nat.reduceEqDiff, Nat.reduceGT,
      Nat.reduceSub, reduceIte, if_true]
  rwa [e] at h

/-! ### 4.3 · `prf_isTermCodeE1_of_boundedIn` (`:1158`) / `prf_isTermCodeE1_of_In` (`:1183`)
       NO estan en produccion, pero:
       (a) su GEMELO POR SORT si esta: `ENS.prf_isFormCodeE2_of_boundedIn` /
           `ENS.prf_isFormCodeE2_of_In` (`Meta/CodeWitnessPrf.lean:1578,1602`), con el MISMO
           esqueleto de prueba linea a linea;
       (b) **SUBSUMEN** a `SinWTs.prf_crit_In_rejects_open1` (`:1112`), que pasa a ser un
           corolario de tres lineas. Es la deduplicacion real que hay que hacer al promover. -/

section
open SinWTs

theorem new_prf_isTermCodeE1_of_boundedIn (w c : Term) :
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

theorem new_prf_isTermCodeE1_of_In (w c : Term) :
    Prf (Formula.impl (In c w) (Formula.impl (wfAll1 w) (isTermCodeE1 w c))) :=
  impT (prf_boundedIn_of_In c w) (new_prf_isTermCodeE1_of_boundedIn w c)

/-- Post-composicion en la segunda premisa: de `⊢P⇒Q⇒R` y `⊢R⇒S` sale `⊢P⇒Q⇒S`. -/
theorem imp2_post {P Q R S : Formula} (h1 : Prf (Formula.impl P (Formula.impl Q R)))
    (h2 : Prf (Formula.impl R S)) : Prf (Formula.impl P (Formula.impl Q S)) := by
  refine prf_deduction (deduction_aux ?_ Q [P] rfl)
  have hq : PrfH [Q, P] Q := PrfH.hyp _ _ (List.Mem.head _)
  have hp : PrfH [Q, P] P := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  exact PrfH.mp _ _ _ (prf_to_prfH h2 _)
    (PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH h1 _) hp) hq)

/-- **SUBSUNCION COMPILADA**: `prf_crit_In_rejects_open1` de produccion sale del lema nuevo. -/
theorem prod_crit_In_rejects_open1_desde_el_nuevo (w c : Term) (k : Nat)
    (hk0 : k ≠ 0) (hk1 : k ≠ 1) (hcl : ∀ n : Nat, liftTerm n c = c)
    (hck : Prf (carc c =eq numeralM k)) :
    Prf (Formula.impl (boundedIn c w) (Formula.impl (wfAll1 w) Formula.bottom)) :=
  imp2_post (new_prf_isTermCodeE1_of_boundedIn w c)
    (crit_isTermCodeE1_rejects w c k hk0 hk1 hck)

end

/-! ### 4.4 · `nilOrCons` / `prf_nil_or_cons` (`:1085,:1106`) NO estan en produccion, pero son
       el ANALOGO EXACTO, sobre `cons`, de `BoundedInPrf.prf_zero_or_eq_succ_pred` sobre `succ`
       — y **comparten el disyunto izquierdo**, porque `nil := zero`. Al promover, ponerlos
       juntos y decir cual es cual, o el consumidor se equivoca de lema. -/

theorem br_nilOrCons_izq_es_el_de_produccion (Y : Term) :
    (Formula.eq Y nil) = (Formula.eq Y zero) := rfl

theorem prod_analogo_nat (n : Term) :
    Prf (lor (Formula.eq n nil) (Formula.eq n (succ (pred n)))) :=
  prf_zero_or_eq_succ_pred n

/-- CONTROL NEGATIVO: y sin embargo NO es el mismo lema — el disyunto derecho difiere. -/
example : True := by
  fail_if_success
    exact (rfl : (fun Y => Formula.eq Y (succ (pred Y)))
                 = (fun Y => Sonda.consOk Y))
  trivial

/-! ### 4.5 · `tEjA` / `tEjB` (`:1909-1910`) son datos de un control, no vocabulario.
       Su unico uso es `CRIT_real_A/B`, cuyos enunciados ya prueba produccion (§3.4). -/

theorem br_tEjA : Sonda.tEjA = succ (Term.var 0) := rfl
theorem br_tEjB : Sonda.tEjB = add (succ (Term.var 0)) (Term.var 1) := rfl

/-! ############################################################################
    ## §5 · GENUINAMENTE NUEVO — lo que si hay que promover
       (aqui solo se COMPRUEBA que el enunciado elabora sobre el vocabulario de PRODUCCION,
        que es la condicion de que el descenso CONECTE; las pruebas viven en el sondeo)
    ############################################################################ -/

section
open SinWTs

/-- `liftF_targetLift` (`:1050`) — compañera de `substF_targetLift_hole`, no existe. -/
theorem new_liftF_targetLift (k : Nat) (s : Term) :
    liftFormula k (targetLift s) = targetLift (liftTerm k s) := by
  simp only [targetLift, liftFormula_provFromCode_open, eqc, liftcT, funcc, tcFn, liftc,
    cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_termCode, liftTerm_strCode]

/-- `liftF_targetLiftsc` (`:1055`). -/
theorem new_liftF_targetLiftsc (k : Nat) (s : Term) :
    liftFormula k (targetLiftsc s) = targetLiftsc (liftTerm k s) := by
  simp only [targetLiftsc, liftFormula_provFromCode_open, eqc, liftscT, funcc, tcFn, liftsc,
    cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_termCode, liftTerm_strCode]

/-- `substF_targetLiftsc` (`:1065`). -/
theorem new_substF_targetLiftsc (v : Nat) (u s : Term) :
    substFormula v u (targetLiftsc s) = targetLiftsc (substTerm v u s) := by
  simp only [targetLiftsc, substFormula_provFromCode_open, eqc, liftscT, funcc, tcFn, liftsc,
    cons, nil, zero, succ, substTerm, substTerms, substTerm_termCode, substTerm_strCode]

/-- `PrfH_congr_targetLiftsc` (`:1071`) — la compañera `sc` de `PrfH_congr_targetLift`,
    que si esta en produccion. -/
theorem new_PrfH_congr_targetLiftsc {Γ : List Formula} {s s' : Term} (h : PrfH Γ (s =eq s'))
    (ha : PrfH Γ (targetLiftsc s)) : PrfH Γ (targetLiftsc s') := by
  have hS : ∀ u : Term, substFormula 0 u (targetLiftsc (.var 0)) = targetLiftsc u := by
    intro u
    rw [new_substF_targetLiftsc]
    simp only [substTerm, if_true]
  exact (hS s') ▸ PrfH_leibniz_subst (A := targetLiftsc (.var 0)) h ((hS s) ▸ ha)

/-- `nilOrCons_at` (`:1087`) — sobre el vocabulario de PRODUCCION (`SinWTs.consOk`). -/
theorem new_nilOrCons_at (Y : Term) :
    substFormula 0 Y (lor (Formula.eq (.var 0) nil) (consOk (.var 0)))
      = lor (Formula.eq Y nil) (consOk Y) := by
  simp only [consOk, lor, carc, cdrc, cons, nil, zero, substFormula, substTerm,
    substTerms, if_true]

/-- `hPHI` (`:1199`) — el gate de `prf_strong_induction`, sobre PRODUCCION. Es la razon de
    que `w` vaya cuantificado DENTRO de `PHI`. Se apoya en `liftF_targetLift`, que es nuevo. -/
theorem new_hPHI :
    liftFormula 1 (Formula.forall
      (land (Formula.impl (isTC1 (.var 0) (.var 1)) (targetLift (.var 1)))
            (Formula.impl (land (wfAll1 (.var 0)) (argsIn (.var 0) (.var 1)))
              (targetLiftsc (.var 1)))))
    = Formula.forall
      (land (Formula.impl (isTC1 (.var 0) (.var 1)) (targetLift (.var 1)))
            (Formula.impl (land (wfAll1 (.var 0)) (argsIn (.var 0) (.var 1)))
              (targetLiftsc (.var 1)))) := by
  -- ⚠️ `liftF_isTC1` NO esta en `SinWTs` (donde vive `isTC1`) sino en `ENS`: colocacion
  --    asimetrica de produccion que hay que respetar al promover.
  simp only [land, liftFormula, ENS.liftF_isTC1, liftF_wfAll1, liftF_argsIn,
    new_liftF_targetLift, new_liftF_targetLiftsc, liftTerm, Nat.reduceAdd, Nat.reduceLT,
    reduceIte]

/-- `PHI` de produccion es `Sonda.PHI`: el descenso CONECTA. -/
theorem br_PHI :
    Sonda.PHI = Formula.forall
      (land (Formula.impl (isTC1 (.var 0) (.var 1)) (targetLift (.var 1)))
            (Formula.impl (land (wfAll1 (.var 0)) (argsIn (.var 0) (.var 1)))
              (targetLiftsc (.var 1)))) := rfl

/-- Y el enunciado FINAL, `DESCENSO_hasWit`, elabora sobre el `hasWit` de PRODUCCION. -/
theorem br_DESCENSO_hasWit_tipo (s : Term) :
    (Prf (Formula.impl (Sonda.hasWit s) (Sonda.targetLift s)))
      = (Prf (Formula.impl (ENS.hasWit s) (targetLift s))) := rfl

/-- Y `DESCENSO` / `pcc_eval_liftc` sobre el `isTC1` de PRODUCCION. -/
theorem br_DESCENSO_tipo (w s : Term) :
    (Prf (Sonda.isTC1 w s) → Prf (Sonda.targetLift s))
      = (Prf (isTC1 w s) → Prf (targetLift s)) := rfl

end

/-! ############################################################################
    ## §5bis · AVISO SOBRE EL DESTINO: `Meta/CodeWitnessPrf.lean` YA duplica seis lemas
       entre sus namespaces `SinWTs` y `ENS` (`ENS` hace `open SinWTs`, luego son teoremas
       sobre LAS MISMAS constantes). No es cosa de B2, pero es el sitio donde va a caer la
       promocion: no añadir una tercera copia.
    ############################################################################ -/

theorem br_prod_ya_duplica_liftF_argsIn :
    @SinWTs.liftF_argsIn = @ENS.liftF_argsIn := rfl
theorem br_prod_ya_duplica_substF_argsIn :
    @SinWTs.substF_argsIn = @ENS.substF_argsIn := rfl
theorem br_prod_ya_duplica_liftF_isTermCodeE1 :
    @SinWTs.liftF_isTermCodeE1 = @ENS.liftF_isTermCodeE1 := rfl
theorem br_prod_ya_duplica_substF_isTermCodeE1 :
    @SinWTs.substF_isTermCodeE1 = @ENS.substF_isTermCodeE1 := rfl
theorem br_prod_ya_duplica_liftF_wfAll1 :
    @SinWTs.liftF_wfAll1 = @ENS.liftF_wfAll1 := rfl
-- (`substF_wfAll1` solo existe en `ENS`: son CINCO duplicados, no seis.)

/-! ############################################################################
    ## §6 · FOOTPRINT — todo puente NET-0
    ############################################################################ -/

#print axioms B2Dedup.br_liftcT
#print axioms B2Dedup.br_liftscT
#print axioms B2Dedup.br_varcT
#print axioms B2Dedup.br_funccT
#print axioms B2Dedup.br_targetLift
#print axioms B2Dedup.br_targetLiftsc
#print axioms B2Dedup.br_shapeUn
#print axioms B2Dedup.br_shapeBin
#print axioms B2Dedup.br_argsInBody
#print axioms B2Dedup.br_argsIn
#print axioms B2Dedup.br_isTermCodeE1
#print axioms B2Dedup.br_consOk
#print axioms B2Dedup.br_cOk
#print axioms B2Dedup.br_wfAll1Body
#print axioms B2Dedup.br_wfAll1
#print axioms B2Dedup.br_isTC1
#print axioms B2Dedup.br_hasWit
#print axioms B2Dedup.dup_iz_inv
#print axioms B2Dedup.br_iz_inv
#print axioms B2Dedup.dup_eqc_eq_eqCodeFn
#print axioms B2Dedup.dup_CRIT_antecedente_discrimina
#print axioms B2Dedup.br_CRIT_antecedente_discrimina
#print axioms B2Dedup.br_pcc_eval_liftc_es_DESCENSO
#print axioms B2Dedup.br_pcc_eval_liftc_produccion
#print axioms B2Dedup.br_CRIT_hasWit_descenso_es_CRIT_targetLift_real
#print axioms B2Dedup.prod_targetLift_termCodeM
#print axioms B2Dedup.prod_targetLiftsc_termsCodeM
#print axioms B2Dedup.dup_CRIT_targetLift_real
#print axioms B2Dedup.dup_CRIT_real_A
#print axioms B2Dedup.dup_CRIT_real_B
#print axioms B2Dedup.dup_CRIT_targetLiftsc_real
#print axioms B2Dedup.dup_CRIT_real_lista
#print axioms B2Dedup.dup_CRIT_hasWit_descenso
#print axioms B2Dedup.substF_targetLift_gen
#print axioms B2Dedup.prod_substF_targetLift_hole_desde_el_general
#print axioms B2Dedup.psi_lift_form_gen
#print axioms B2Dedup.PSI_inst_gen
#print axioms B2Dedup.new_prf_isTermCodeE1_of_boundedIn
#print axioms B2Dedup.new_prf_isTermCodeE1_of_In
#print axioms B2Dedup.imp2_post
#print axioms B2Dedup.prod_crit_In_rejects_open1_desde_el_nuevo
#print axioms B2Dedup.br_nilOrCons_izq_es_el_de_produccion
#print axioms B2Dedup.prod_analogo_nat
#print axioms B2Dedup.br_tEjA
#print axioms B2Dedup.br_tEjB
#print axioms B2Dedup.new_liftF_targetLift
#print axioms B2Dedup.new_liftF_targetLiftsc
#print axioms B2Dedup.new_substF_targetLiftsc
#print axioms B2Dedup.new_PrfH_congr_targetLiftsc
#print axioms B2Dedup.new_nilOrCons_at
#print axioms B2Dedup.new_hPHI
#print axioms B2Dedup.br_PHI
#print axioms B2Dedup.br_DESCENSO_hasWit_tipo
#print axioms B2Dedup.br_DESCENSO_tipo
#print axioms B2Dedup.br_prod_ya_duplica_liftF_argsIn
#print axioms B2Dedup.br_prod_ya_duplica_substF_argsIn
#print axioms B2Dedup.br_prod_ya_duplica_liftF_isTermCodeE1
#print axioms B2Dedup.br_prod_ya_duplica_substF_isTermCodeE1
#print axioms B2Dedup.br_prod_ya_duplica_liftF_wfAll1

-- CONTROL: la base sancionada de produccion
#print axioms ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_termCode
#print axioms ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.crit_junk_var0_witness1
#print axioms ROBINSON_PlusPlus.Meta.StrongInductionPrf.prf_strong_induction

end B2Dedup
