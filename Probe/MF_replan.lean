/-
MEDICION (2026-09-01) — RE-MEDIDA COMPLETA de `PLAN-NEGVERIFIER.md` (2026-07-14)
contra el arbol de HOY.  Angulo (C): que afirmaciones del plan siguen siendo
ciertas y cuales estan obsoletas.  Producto = DIAGNOSTICO respaldado por Lean.

NO se toca nada fuera de Probe/.
-/
import ROBINSON_PlusPlus.Meta

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Representability
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.OmegaReflect
open ROBINSON_PlusPlus.Meta.Sigma1CorePrf
open ROBINSON_PlusPlus.Meta.AxiomListCode
open ROBINSON_PlusPlus.Meta.LineWFCases
open ROBINSON_PlusPlus.Meta.CodeArith
open ROBINSON_PlusPlus.Meta.CodeDistinct
open ROBINSON_PlusPlus.Meta.CheckArith
open ROBINSON_PlusPlus.Meta.CodeNumeralPrf

set_option maxHeartbeats 1000000
set_option maxRecDepth 8000
set_option linter.unusedSimpArgs false

namespace MFReplan

/-! ############################################################################
    § 1 — BLOQUEO 2 DEL PLAN (§B, «`axiomsCodeT` es OPACO ⟹ `NegVerifier` NO es
    demostrable»): ESTA MUERTO, y no «a un paso»: la cadena ENTERA esta montada
    y COMPILADA dentro del build (`Meta/`), no en `sondeos/`.
    ############################################################################ -/

/-- El ancla: `axiomsCodeT` NO es opaco. Es un `axiom` de Lean (`Minimal/Axioms.lean:1376`)
    que lo iguala a una lista CONCRETA. -/
example : axioms ⊢ (axiomsCodeT =eq listFormCodeM axioms) := ax_axiomsCodeT_eq

/-- La DIRECCION NEGATIVA sobre lista concreta — ya existe (`Meta/AxiomListCode.lean:43`). -/
example (φ : Formula) (L : List Formula) (h : ¬ List.Mem φ L) :
    axioms ⊢ neg (In (formCode φ) (listFormCodeM L)) :=
  prf_not_In_listFormCodeM φ L h

/-- ⚠️ **LA REFUTACION QUE EL PLAN DECLARA IMPOSIBLE**, literalmente:
    «No existe ninguna forma de refutar `In v0 axiomsCodeT`» (plan §B, lin. 103).
    EXISTE, esta compilada, y es exactamente la que el plan pedia. -/
example (φ : Formula) (hnp : ¬ Prf φ) : axioms ⊢ neg (In (formCode φ) axiomsCodeT) :=
  neg_In_axiomsCodeT φ hnp

/-- Y el CONSUMIDOR ya esta alimentado: una linea `thy` cuya conclusion es un `⌜φ⌝`
    indemostrable queda REFUTADA. Esto es exactamente el caso que el plan §B daba
    por irrecuperable («si `formCode φ` aparece solo como conclusion de una linea
    `thy`, refutar la cadena requiere ⊢ ¬ In ⌜φ⌝ axiomsCodeT, que tampoco se puede»). -/
example (φ : Formula) (hnp : ¬ Prf φ) :
    axioms ⊢ neg (lineWF (cons (formCode φ) (cons (numeralM 15) nil))) :=
  derives_lineWF_neg_thy_of_not_prf φ hnp

/-! ############################################################################
    § 2 — BLOQUEO 1 (`canon_ne` FALSO): SIGUE EN PIE. Re-verificado aqui.
    ############################################################################ -/

theorem cons_nil_nil_ne_numeralM2 : cons nil nil ≠ numeralM 2 := by decide

/-- ... pero son PROVABLEMENTE IGUALES (`consN 0 0 = 2`). -/
theorem cons_nil_nil_eq_2 : Prf (cons nil nil =eq numeralM 2) := by
  have h := prf_cons_eval 0 0
  simpa only [ROBINSON_PlusPlus.Meta.Godel.numeral, numeralM, nil, consN, triN] using h

/-- ⇒ `canon_ne` sobre `IsCodeShaped` sigue dando ⊥. El paso 1.1 del plan sigue MUERTO. -/
theorem canon_ne_sigue_inconsistente
    (canon_ne : ∀ {a b : Term}, IsCodeShaped a → IsCodeShaped b → a ≠ b → Prf (neg (a =eq b))) :
    Prf Formula.bottom :=
  prf_mp (canon_ne (IsCodeShaped.cons IsCodeShaped.nil IsCodeShaped.nil)
    (IsCodeShaped.numeral 2) cons_nil_nil_ne_numeralM2) cons_nil_nil_eq_2

/-! ############################################################################
    § 3 — LA «DEUDA TECNICA» DE LOS `numeral` DUPLICADOS: YA ESTABA PAGADA,
    y en el BUILD, desde `Meta/CodeArith.lean` (13-jun) y `Meta/CheckArith.lean`.
    Ademas NO son DOS copias: son TRES.
    ############################################################################ -/

/-- El puente que el plan dice que «hay que probar» — existe desde junio. -/
example (n : Nat) :
    ROBINSON_PlusPlus.Meta.Godel.numeral n = ROBINSON_PlusPlus.Full.numeral n :=
  numeral_bridge n

/-- Y la TERCERA copia (`Minimal.numeralM`) tambien tiene su puente. -/
example (n : Nat) : numeralM n = ROBINSON_PlusPlus.Meta.Godel.numeral n := numeralM_eq n

/-- Corolario: `numeral_ne` YA esta re-expuesto sobre la copia de los codigos.
    O sea, el «sustituto de `canon_ne`» no necesita `num_bridge` de `sondeos/`. -/
example {a b : Nat} (h : a ≠ b) :
    axioms ⊢ neg (ROBINSON_PlusPlus.Meta.Godel.numeral a
             =eq ROBINSON_PlusPlus.Meta.Godel.numeral b) :=
  gnum_ne h

/-! ############################################################################
    § 4 — MODULO A (decodificador): HECHO, y MAS de lo que el plan pedia.
    ############################################################################ -/

example : ∀ {c : Term} {φ : Formula},
    ROBINSON_PlusPlus.Meta.CodeDecode.decodeForm c = some φ → c = formCodeM φ :=
  ROBINSON_PlusPlus.Meta.CodeDecode.decodeForm_inj

/-- El plan pedia (§8, modulo E) `chainOkDec_decodes` + `verifier_sound`. La mitad
    META de esa solidez YA esta: lo que `decodeChain` acepta ES una derivacion real. -/
example {t : Term} {rs : List ROBINSON_PlusPlus.Meta.HilbertSeq.Rule} {φ : Formula}
    (h : ROBINSON_PlusPlus.Meta.ChainDecode.decodeChain t = some rs)
    (hmem : ∀ L, ROBINSON_PlusPlus.Meta.HilbertSeq.checkProof rs = some L → φ ∈ L) : Prf φ :=
  ROBINSON_PlusPlus.Meta.ChainDecode.decodeChain_prf h hmem

/-! ############################################################################
    § 5 — MODULO D, pieza 1 (`prf_runFn_eval`): **YA EXISTE**, y sin hipotesis
    de canonicidad, desde `Meta/Sigma1CorePrf.lean:188`.
    ############################################################################ -/

example (lines : List Term) :
    Prf (runFn nil (objList lines) =eq objList (lines.map carc)) :=
  prf_runFn_nil_objList lines

/-! ############################################################################
    § 6 — MODULO D, pieza 2 (`prf_not_In_of_notMem`): NO existia. LA CONSTRUYO
    AQUI para medir su coste real. Son ~10 lineas, no «300-400».
    ############################################################################ -/

/-- **`In` NEGATIVO sobre una lista object explicita.** Misma recursion que
    `prf_not_In_listFormCodeM`, pero con las desigualdades como HIPOTESIS (asi
    evita el `canon_ne` refutado: quien llama aporta la distincion PARALELA POR
    TIPO, que es la unica que la teoria decide). -/
theorem derives_not_In_objList (x : Term) :
    ∀ (L : List Term), (∀ y, List.Mem y L → axioms ⊢ neg (x =eq y)) →
      axioms ⊢ neg (In x (objList L))
  | [], _ => by simpa only [objList] using prf_not_in_nil_D x
  | y :: ys, hne => by
      show axioms ⊢ neg (In x (cons y (objList ys)))
      apply FOL.MetaRules.raa; intro h_in
      have h_disj := FOL.MetaRules.iff_mp (prf_in_cons_iff_D x y (objList ys)) h_in
      apply FOL.MetaRules.or_elim h_disj
      · intro h_eq; exact FOL.MetaRules.mp (hne y (List.Mem.head _)) h_eq
      · intro h_tail
        exact FOL.MetaRules.mp
          (derives_not_In_objList x ys (fun z hz => hne z (List.Mem.tail _ hz))) h_tail

/-! ############################################################################
    § 7 — ENSAMBLAJE §5+§6: la MITAD «In» de `NegVerifier` sobre un testigo
    CONCRETO, cerrada aqui de punta a punta. Es la rama «⌜φ⌝ no esta entre las
    conclusiones» del modulo F del plan.
    ############################################################################ -/

/-- **`⊢ ¬ In ⌜φ⌝ (runFn nil ⟦lines⟧)`** cuando `⌜φ⌝` difiere (provablemente) de
    cada conclusion `carc lineᵢ`. Transporte por Leibniz object con el tracking de
    `runFn`. NUEVO — no existia en el arbol. -/
theorem derives_not_In_runFn_formCode (φ : Formula) (lines : List Term)
    (h : ∀ y, List.Mem y (lines.map carc) → axioms ⊢ neg (formCode φ =eq y)) :
    axioms ⊢ neg (In (formCode φ) (runFn nil (objList lines))) := by
  have key : ∀ t : Term,
      substFormula 0 t (neg (In (formCode φ) (.var 0))) = neg (In (formCode φ) t) := by
    intro t
    rw [← formCodeM_eq φ]
    simp [neg, In, substFormula, substTerm, substTerms, substTerm_formCodeM,
      FOL.substTerm_liftTerm]
  have hbase : axioms ⊢
      substFormula 0 (objList (lines.map carc)) (neg (In (formCode φ) (.var 0))) := by
    rw [key]; exact derives_not_In_objList (formCode φ) (lines.map carc) h
  have hsub := Derives.subst axioms (objList (lines.map carc)) (runFn nil (objList lines))
    (neg (In (formCode φ) (.var 0)))
    (FOL.derive_eq_symm (prf_to_derives (prf_runFn_nil_objList lines))) hbase
  rwa [key] at hsub

/-- Y su especializacion inmediata: si todas las conclusiones de la cadena son
    codigos de formulas `ψ ≠ φ`, la teoria REFUTA que `⌜φ⌝` este entre ellas.
    Aqui la distincion la da `formCode_ne` — comparacion PARALELA POR TIPO. -/
theorem derives_not_In_runFn_of_formCodes (φ : Formula) (ψs : List Formula)
    (lines : List Term) (hcarc : lines.map carc = ψs.map formCode)
    (hne : ∀ ψ, List.Mem ψ ψs → ψ ≠ φ) :
    axioms ⊢ neg (In (formCode φ) (runFn nil (objList lines))) := by
  refine derives_not_In_runFn_formCode φ lines ?_
  rw [hcarc]
  intro y hy
  have : ∃ ψ, List.Mem ψ ψs ∧ y = formCode ψ := by
    clear hcarc
    induction ψs with
    | nil => cases hy
    | cons a as ih =>
        cases hy with
        | head => exact ⟨a, List.Mem.head _, rfl⟩
        | tail _ ht =>
            obtain ⟨ψ, hm, he⟩ := ih (fun ψ hψ => hne ψ (List.Mem.tail _ hψ)) ht
            exact ⟨ψ, List.Mem.tail _ hm, he⟩
  obtain ⟨ψ, hm, rfl⟩ := this
  exact formCode_ne (fun e => hne ψ hm e.symm)

/-! ############################################################################
    § 7bis — **UNA DE LAS DOS RAMAS DE `NegVerifier` (modulo F), CERRADA AQUI.**
    `Verifies φ t = land (chainOk nil t) (In ⌜φ⌝ (runFn nil t))`, asi que refutar
    el segundo conjunto BASTA. Con §7 eso da `NegVerifier` completo para todo
    testigo cuya lista de conclusiones no contenga `⌜φ⌝`.
    ############################################################################ -/

/-- De `⊢ ¬ In ⌜φ⌝ (runFn nil t)` sale `⊢ ¬ Verifies φ t` (and-elim derecho + raa). -/
theorem derives_neg_Verifies_of_not_In (φ : Formula) (t : Term)
    (h : axioms ⊢ neg (In (formCode φ) (runFn nil t))) :
    axioms ⊢ neg (Verifies φ t) := by
  apply FOL.MetaRules.raa; intro hv
  exact FOL.MetaRules.mp h (FOL.MetaRules.and_elim_right hv)

/-- **RAMA 1 DE `NegVerifier`, COMPLETA.** Si las conclusiones del testigo son
    codigos de formulas todas distintas de `φ`, la teoria REFUTA que el testigo
    verifique `φ` — sin usar `¬ Prf φ`, sin `chainOk`, sin solidez del verificador.
    Lo unico que queda de `NegVerifier` es la OTRA rama (⌜φ⌝ SI aparece ⟹ refutar
    `chainOk`), que es donde vive el modulo E. -/
theorem negVerifier_rama_notIn (φ : Formula) (ψs : List Formula) (lines : List Term)
    (hcarc : lines.map carc = ψs.map formCode) (hne : ∀ ψ, List.Mem ψ ψs → ψ ≠ φ) :
    axioms ⊢ neg (Verifies φ (objList lines)) :=
  derives_neg_Verifies_of_not_In φ (objList lines)
    (derives_not_In_runFn_of_formCodes φ ψs lines hcarc hne)

/-! ############################################################################
    § 8 — LO QUE SIGUE SIN EXISTIR (verificado por grep sobre
    ROBINSON_PlusPlus/ + sondeos/ + Probe/, los TRES):

      * `Meta/LineWFNeg.lean`   (modulo C)  — el FICHERO no existe;
        pero SUS ENVOLTORIOS negativos SI: `derives_lineWF_neg_of_tag` (19 tags
        estructurales) y `derives_lineWF_neg_thy` (tag 15) en `Meta/LineWFCases.lean`.
      * `lineWFDec`, `chainOkDec`, `runFnDec` — 0 ocurrencias en todo el arbol.
      * `Meta/ChainNeg.lean`, `Meta/VerifierSound.lean`, `Meta/NegVerifierPrf.lean`
        — no existen; `verifier_sound`, `chainOkDec_decodes`, `negVerifier`:
        0 ocurrencias.
      * `codeNat_inj` / `codeNat_ne` / `consN_inj` — SOLO en `sondeos/CodeNatInj.lean`
        y `Probe/CodeNatInj.lean`: FUERA DEL BUILD. La rama B (promocion a `Meta/`)
        les afecta igual que al frente de `substfc`.
    ############################################################################ -/

/-- Los envoltorios negativos de los 19 tags estructurales, en `⊢`. SI existen. -/
example (k : Nat) (concl : Term) (args : List Term) (e : Term)
    (h : tagConcl k args = some e) (hne : axioms ⊢ neg (concl =eq e)) :
    axioms ⊢ neg (lineWF (cons concl (cons (numeralM k) (objList args)))) :=
  derives_lineWF_neg_of_tag k concl args e h hne

/-- La inversion (`lineWF ⇒ tagDisj`) y el «es un cons» — en pie, nivel `Prf`. -/
example (line : Term) : Prf (lineWF line ⇒ tagDisj line 20) := prf_lineWF_inv line

/-! ############################################################################
    § 9 — EL ENUNCIADO DE CIERRE CAMBIO DE SENTENCIA: hoy es `godelCN`
    (NUMERAL), no `godelC'`. El §9 del plan y su criterio de aceptacion citan
    `goedel_first_undecidable_final ... godelC'`.
    ############################################################################ -/

example (hcon : ConsistentOmega) (hω : OmegaConsistent) (hneg : NegVerifier) :
    (¬ Prf godelCN) ∧ (¬ Prf (neg godelCN)) :=
  goedel_first_undecidable_omega hcon hω hneg

end MFReplan

/-! ### MEDIDAS NUMERICAS

El plan (§B, lin. 120) dice que «`axioms` es una lista finita concreta
(~35 entradas)». Eso es `coreAxioms`. El ancla `ax_axiomsCodeT_eq` iguala
`axiomsCodeT` a `listFormCodeM axioms` — la lista ENTERA, no `coreAxioms`. -/

#eval ROBINSON_PlusPlus.Minimal.Axioms.coreAxioms.length
#eval ROBINSON_PlusPlus.Minimal.Axioms.codingAxioms.length
#eval ROBINSON_PlusPlus.Minimal.Axioms.axioms.length

/-! ### FOOTPRINTS (auditoria por `#print axioms`, unica fuente valida) -/

#print axioms ROBINSON_PlusPlus.Meta.AxiomListCode.neg_In_axiomsCodeT
#print axioms ROBINSON_PlusPlus.Meta.LineWFCases.derives_lineWF_neg_thy_of_not_prf
#print axioms ROBINSON_PlusPlus.Meta.ChainDecode.decodeChain_prf
#print axioms ROBINSON_PlusPlus.Meta.CodeDecode.decodeForm_inj
#print axioms ROBINSON_PlusPlus.Meta.Sigma1CorePrf.prf_runFn_nil_objList
#print axioms ROBINSON_PlusPlus.Meta.CodeArith.numeral_bridge
#print axioms MFReplan.derives_not_In_objList
#print axioms MFReplan.derives_not_In_runFn_formCode
#print axioms MFReplan.derives_not_In_runFn_of_formCodes
#print axioms MFReplan.derives_neg_Verifies_of_not_In
#print axioms MFReplan.negVerifier_rama_notIn
#print axioms MFReplan.canon_ne_sigue_inconsistente

/-! ############################################################################
    RESUMEN DE CORRECCIONES AL PLAN (evidencia = lo compilado arriba + greps)

    1. §B (lin. 100-110) «`axiomsCodeT` es OPACO ⟹ NegVerifier NO es demostrable»
       — FALSO HOY. `Minimal/Axioms.lean:1376` (`ax_axiomsCodeT_eq`),
       `Meta/AxiomListCode.lean:43,62,70`, `Meta/LineWFCases.lean:216,223`.
       No falta «un paso de Leibniz»: el paso YA ESTA DADO (AxiomListCode:70-81).
    2. §B (lin. 118) «`axiomsCodeT` fue concreto y se retiro en 7ae7b7b» — cierto
       como historia, pero la retirada YA SE REVIRTIO (paso 0.5, opcion 1).
    3. §B (lin. 120) «`axioms` es una lista de ~35 entradas» — son 141
       (34 core + 107 coding). El ancla es a `listFormCodeM axioms`, la ENTERA.
       ⚠️ La docstring de `Minimal/Axioms.lean:908-917` sigue diciendo
       `listFormCodeM coreAxioms` y `ax_axiomsCodeT`: NO cuadra con el codigo.
    4. §A (lin. 85) «El unico incondicional es `mp`» — obsoleto: `ax_lineWF_mp`
       (Axioms:998) es hoy ESTRICTO y guardado por tag (`lenc = 3`).
    5. §A (lin. 90) «la unica via para probar `In · axiomsCodeT` es `ax_inAxC`»
       — obsoleto: `ax_inAxC` (Axioms:1417) es hoy un TEOREMA derivado del ancla.
    6. §10 criterio de aceptacion: pide ver `ax_inAxC` en `#print axioms`. Hoy lo
       que aparece es `ax_axiomsCodeT_eq` (ver footprints arriba).
    7. §9 y §10 hablan de `godelC'`. La sentencia de cierre es hoy `godelCN`
       (`Meta/DiagonalNumeral.lean`), via `goedel_first_undecidable_numeral`.
    8. Nota lateral (lin. 59-61) «hay DOS `numeral` duplicados y el puente
       (`num_bridge`) hay que probarlo» — TRIPLE error: son TRES copias, y los
       DOS puentes existen en el BUILD desde junio (`Meta/CodeArith.lean:39`
       `numeral_bridge`, `Meta/CheckArith.lean:36` `numeralM_eq`), ademas de
       `gnum_ne` ya re-expuesto. `sondeos/CodeNatInj.lean:179` reprueba
       `numeral_bridge` sin saberlo.
    9. §7 modulo D, pieza `prf_runFn_eval` — YA EXISTE y mas fuerte (sin
       hipotesis de canonicidad): `Meta/Sigma1CorePrf.lean:188`.
   10. §7 modulo D, pieza `prf_not_In_of_notMem` — no existia; cuesta 12 lineas
       (§6 de este fichero), no las «300-400» del bloque.
   11. §8 modulo E — su mitad META (`cadena aceptada ⟹ derivacion real ⟹ Prf`)
       YA EXISTE: `Meta/ChainDecode.lean:380` `decodeChain_prf`. Lo que queda de
       E es SOLO el puente objeto→meta (`chainOk nil t ⟹ decodeChain t = some rs`).
   12. §9 modulo F — una de sus dos ramas queda CERRADA aqui (§7bis), y sin
       necesitar `StdChain` ni `¬ Prf φ`.
   13. §10 estimaciones de LINEAS: los modulos A+B ya entregados suman ~1160
       lineas reales (438+396+234+88) frente a las 650-900 estimadas. El plan
       subestima ~30-80% en lo que ya se puede medir.
   14. §6 modulo C: el FICHERO `Meta/LineWFNeg.lean` no existe, pero sus casos
       1 y 2 tienen ya su munición (`prf_lineWF_inv`, `ax_lineWF_cons`) y los
       envoltorios negativos uniformes estan hechos
       (`derives_lineWF_neg_of_tag`, `derives_lineWF_neg_thy`).
    ############################################################################ -/
