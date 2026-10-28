#!/usr/bin/env bash
# check-footprints.bash — comprueba que los teoremas TITULARES tienen EXACTAMENTE el footprint
# que la documentación publica. ROMPE si alguno no cuadra.
#
# ⚠️ LO QUE NO COMPRUEBA (✏️ 2026-10-18, T07 y ADR-165): el ENUNCIADO de un titular, ni el valor de las
# definiciones de las que depende. Un enunciado debilitado con el mismo footprint pasa: el mutante M4 de
# ADR-165 debilita `con_indecidible` y su fila de aquí sigue cuadrando. Eso lo fija el contrato de los
# enunciados, `#contrato_titulares` (`Meta/PurezaTitulares.lean`), sobre los 24 titulares de `T_UNIVERSO`.
# Los «titulares» de este script son otra cosa, más amplia: toda declaración cuyo `#print axioms` imprime el
# árbol (abajo).
#
# ⭐⭐ QUÉ ES UN «TITULAR» — LA DEFINICIÓN OPERATIVA (2026-09-18, ADR-073, encargo A2)
#
# *Un TITULAR es toda declaración cuyo `#print axioms` **EL ÁRBOL IMPRIME**.*
#
# ⛔ Hasta hoy no había definición, y por eso el reparto «41 titulares / 182 andamio» que
# propuso la auditoría era **JUICIO y no medición** — lo dijo su propio refutador. Sin
# definición, adjudicar es opinar.
#
# 🔑 Por qué ÉSTA: (a) es **objetiva** — la decide un grep sobre la salida de construcción,
# sin leer a nadie; (b) está **alineada con el propósito** — si el proyecto se molesta en
# imprimir un footprint es que lo **PUBLICA**, y *una cifra publicada hay que vigilarla*; y
# (c) es **auto-mantenida** — poner un `#print axioms` OBLIGA a poner la fila, y quitarlo
# obliga a quitarla. La cifra no se puede quedar vieja sin que el control lo diga.
#
# ⚠️ Filas que están en la tabla y el árbol NO imprime: son **legítimas**. Este script genera
# su propio fichero Lean y las mide ahí; sirven para vigilar algo sin ensuciar el módulo con un
# `#print axioms`. Lo que NO es legítimo es lo contrario, y es lo que [COBERTURA] caza.
# ⛔ POR QUÉ EXISTE (2026-09-14, criterio §9 de doc/PLAN-COMPLETITUD-FINITISTA.md):
# los footprints se imprimen en el build como `info:` — y un `info:` en medio de 145 jobs
# NO ES UN CONTROL: nadie lo lee, y si cambia no rompe nada. `check-axioms.bash` cuenta
# `axiom` declarados; esto mide lo que de verdad importa, que es de qué DEPENDE cada
# teorema.
#
# ⚠️ Un footprint es la única evidencia que este proyecto acepta (feedback_auditoria_footprint).
# Publicar una cifra y no volver a medirla es exactamente lo que ADR-032 §4 llama una
# medición falsa.
#
# 🔧 EJECUTAR DESDE POWERSHELL: desde Bash, `lake` no está en el PATH (y el propio script
#    lo dice en vez de callarse, que es la lección de feedback_controles_que_no_comprueban).
# ⛔ Y desde la raíz de ROBINSON_PlusPlus, NUNCA `cd FOL && lake ...`.
export PATH="/usr/bin:$PATH"
cd "$(dirname "$0")" || exit 2

# ── La tabla: declaración ⇒ footprint esperado (nombres ORDENADOS alfabéticamente) ─────────
# «-» significa: no depende de ningún axioma.
read -r -d '' TABLA <<'EOF'
Derives₀.rec|propext
Derives₁.rec|-
Derives₂.rec|-
FOL.BlockExtraction0.herbrand_block₀|Quot.sound,propext
FOL.BlockExtraction0.herbrand_extraction_block₀|Quot.sound,propext
FOL.BlockExtraction0.instB_nil|-
FOL.BlockExtraction0.lk0_herbrand_block|Quot.sound,propext
FOL.Complexity.complexity_substFormula|propext
FOL.Inconsistencia.derives0_no_disjunction_property|Quot.sound,propext
FOL.Inconsistencia.derives_soundness|propext,Classical.choice,Quot.sound
FOL.Inconsistencia.derives_to_derives0|propext,Quot.sound
FOL.Inconsistencia.ex_elim_refutable|propext,Classical.choice,Quot.sound
FOL.Inconsistencia.imp_intro_refutable|propext,Quot.sound
FOL.Inconsistencia.or_elim_refutable|propext,Quot.sound
FOL.Inconsistencia.raa_refutable|propext,Quot.sound
FOL.Canonical0.max_cons_neg|propext,Classical.choice,Quot.sound
FOL.Canonical0.max_cons_complete|propext,Classical.choice,Quot.sound
FOL.Compacity0.model_existence_iff₀|propext,Classical.choice,Quot.sound
FOL.Herbrand0.pcheck_complete|propext
FOL.Herbrand0.ptautCheck_iff|propext
FOL.Inversion0.inv_implR|propext,Quot.sound
FOL.Inversion0.inv_implL_l|propext,Quot.sound
FOL.Inversion0.inv_implL_r|propext,Quot.sound
FOL.Inversion0.inv_andR_l|propext,Quot.sound
FOL.Inversion0.inv_andR_r|propext,Quot.sound
FOL.Inversion0.inv_andL|propext,Quot.sound
FOL.Inversion0.inv_orR|propext,Quot.sound
FOL.Inversion0.inv_orL_l|propext,Quot.sound
FOL.Inversion0.inv_orL_r|propext,Quot.sound
FOL.Inversion0.inv_allR|propext,Quot.sound
FOL.Inversion0.inv_exL|propext,Quot.sound
FOL.Hauptsatz0.derives0_of_eqPropCert|propext,Quot.sound
FOL.Hauptsatz0.eqPropCert_of_derives0|propext,Quot.sound
FOL.Hauptsatz0.derives0_qf_iff|propext,Quot.sound
FOL.Hauptsatz0.peval_true_eqInstance|-
FOL.Compacity0.evalFormula_updateCsts|-
FOL.Compacity0.evalTerm_updateCsts|-
FOL.Compacity0.infTheory_finSat|Quot.sound,propext
FOL.Compacity0.infinite_model_of_large_fresh|propext,Classical.choice,Quot.sound
FOL.Compacity0.infinite_model_of_large|propext,Classical.choice,Quot.sound
FOL.Compacity0.countable_infinite_of_infinite|propext,Classical.choice,Quot.sound
FOL.Compacity0.hasLargeModels_empty|-
FOL.Compacity0.not_hasLargeModels_one|-
FOL.Canonical0.completeness₀|Classical.choice,Quot.sound,propext
FOL.Canonical0.derives0_complete_iff|Classical.choice,Quot.sound,propext
FOL.Canonical0.derives0_em|Classical.choice,Quot.sound,propext
FOL.Canonical0.eval_pullback_formula|-
FOL.Canonical0.model_existence_lemma₀|Classical.choice,Quot.sound,propext
FOL.Canonical0.truth_lemma₀|Classical.choice,Quot.sound,propext
FOL.Compacity0.compactness|Classical.choice,Quot.sound,propext
FOL.Compacity0.loewenheim_skolem_down|Classical.choice,Quot.sound,propext
FOL.Craig0.craigₚ|Quot.sound,propext
FOL.Craig0.craig_implₚ|Quot.sound,propext
FOL.Craig0.lkp_example|-
FOL.Craig0.lkp_to_lk0|-
FOL.Craig0.maeharaₚ|Quot.sound,propext
FOL.Craig0.predF_subst|-
FOL.DecEq.instDecidableEqTerm|-
FOL.Derives1.derives0_iff_derives1|Quot.sound,propext
FOL.Derives1.derives0_to_derives1|Quot.sound,propext
FOL.Derives1.rewrite_at_admissible|Quot.sound,propext
FOL.Derives1.rewrite_equiv|Quot.sound,propext
FOL.Derives2.derives0_iff_derives2|Quot.sound,propext
FOL.Derives2.derives1_to_derives2|Quot.sound,propext
FOL.Derives2.derives2_lift|Quot.sound,propext
FOL.Derives2.eq_substFormula|Quot.sound,propext
FOL.Derives2.eq_substTerm|propext
FOL.Eigenvariable.absDerives|Quot.sound,propext
FOL.Eigenvariable.absFormula|-
FOL.Eigenvariable.derives0_gen_fresh|Quot.sound,propext
FOL.Eigenvariable.derives0_inst_fresh|Quot.sound,propext
FOL.Eigenvariable.occursFormula|-
FOL.Eq0.derives0_atom_congr|Quot.sound,propext
FOL.Eq0.derives0_eq_func_congr|Quot.sound,propext
FOL.Estratos0.derives1_complete|Classical.choice,Quot.sound,propext
FOL.Estratos0.derives1_soundness|Classical.choice,Quot.sound,propext
FOL.Estratos0.derives2_complete|Classical.choice,Quot.sound,propext
FOL.Estratos0.derives2_soundness|Classical.choice,Quot.sound,propext
FOL.Estratos0.derives_semantic_complete|Classical.choice,Quot.sound,propext
FOL.Estratos0.lk0_complete|Classical.choice,Quot.sound,propext
FOL.Estratos0.lkc_complete|Classical.choice,Quot.sound,propext
FOL.Estratos0.lkh_complete|Classical.choice,Quot.sound,propext
FOL.Estratos0.lkh_sound|Classical.choice,Quot.sound,propext
FOL.Estratos0.lkp_complete|Classical.choice,Quot.sound,propext
FOL.Estratos0.lkp_sound|Classical.choice,Quot.sound,propext
FOL.Esencialidad0.E1.soundness_stmt_implies_dne|-
FOL.Esencialidad0.E1.lkc_stmt_implies_em|-
FOL.Esencialidad0.E2.sound_stable|Quot.sound,propext
FOL.Esencialidad0.E2.stable_of_dec|-
FOL.Esencialidad0.E2b.lkc_sound_dec|Quot.sound,propext
FOL.Esencialidad0.E3.T_consistent|Quot.sound,propext
FOL.Esencialidad0.E3.SP_max|Quot.sound,propext
FOL.Esencialidad0.E3.contains_stmt_implies_dne|Quot.sound,propext
FOL.Esencialidad0.E3.complete_stmt_implies_dne|Quot.sound,propext
FOL.Esencialidad0.E3.impl_iff_stmt_implies_dne|Quot.sound,propext
FOL.Esencialidad0.E3.or_stmt_implies_dne|Quot.sound,propext
FOL.Esencialidad0.E3.intro_impl'|propext
FOL.Esencialidad0.E3.contains'|propext
FOL.Esencialidad0.E3.impl_iff'|propext
FOL.Esencialidad0.E3.complete'|propext
FOL.Esencialidad0.E3.or'|propext
FOL.Esencialidad0.E3.forall'|propext
FOL.Esencialidad0.E6.skolem_expansion_implies_ac|Quot.sound,propext
FOL.Esencialidad0.E6.ac_implies_em|Quot.sound,propext
FOL.Esencialidad0.E7.SP_consistent|Quot.sound,propext
FOL.Esencialidad0.E7.model_existence_stmt_implies_wlem|Quot.sound,propext
FOL.Esencialidad0.ExElimFin.stable_MB|-
FOL.Esencialidad0.ExElimFin.sound_MB|Quot.sound,propext
FOL.Esencialidad0.ExElimFin.ex_elim_refutable_fin|Quot.sound,propext
FOL.Finitary0.derives0_consistent_fin|Quot.sound,propext
FOL.Finitary0.lk0_empty|Quot.sound,propext
FOL.Finitary0.lk0_empty_of_no_bot|-
FOL.Finitary0.lk0_not_empty_fin|Quot.sound,propext
FOL.Finitary0.lk0_tval|Quot.sound,propext
FOL.Finitary0.lkc_empty|Quot.sound,propext
FOL.Finitary0.lkc_tval|Quot.sound,propext
FOL.Finitary0.tval_eqInstance|-
FOL.Fresh0.cst_bound_formula|Quot.sound,propext
FOL.Fresh0.cst_bound_sym|Quot.sound,propext
FOL.Fresh0.derivesSet0_shift_inv|Quot.sound,propext
FOL.Fresh0.exists_fresh|Quot.sound,propext
FOL.Fresh0.instFreshSymListChar|-
FOL.Fresh0.shiftTheory_consistent₀|Quot.sound,propext
FOL.Hauptsatz0.cutElim_of|-
FOL.Hauptsatz0.cutLeftAux|Quot.sound,propext
FOL.Hauptsatz0.cutPrinAux|Quot.sound,propext
FOL.Hauptsatz0.cut_elimination₀|Quot.sound,propext
FOL.Hauptsatz0.eqInstance_lift|-
FOL.Hauptsatz0.eqInstance_subst|-
FOL.Hauptsatz0.hauptsatz₀|Quot.sound,propext
FOL.Hauptsatz0.herbrand₀|Quot.sound,propext
FOL.Hauptsatz0.herbrand_extraction₀|Quot.sound,propext
FOL.Hauptsatz0.liftFormula_subst_le|Quot.sound,propext
FOL.Hauptsatz0.lk0_to_lkh|propext
FOL.Hauptsatz0.lkh_lift|Quot.sound,propext
FOL.Hauptsatz0.lkh_mono|-
FOL.Hauptsatz0.lkh_subst|Quot.sound,propext
FOL.Hauptsatz0.lkh_to_lk0|-
FOL.Hauptsatz0.substFormula_subst_le|Quot.sound,propext
FOL.Henkin0.henkin_step_consistent₀|Quot.sound,propext
FOL.HenkinLimit0.henLimit_consistent₀|Quot.sound,propext
FOL.HenkinLimit0.henLimit_witness|Quot.sound,propext
FOL.HenkinLimit0.not_occurs_henkinAx|-
FOL.Herbrand0.derives0_discharge|-
FOL.Herbrand0.derives0_ex_of_cert|Quot.sound,propext
FOL.Herbrand0.derives0_of_eqInstance|Quot.sound,propext
FOL.Herbrand0.ex_igualdad|Quot.sound,propext
FOL.Herbrand0.herbrand_iff|Quot.sound,propext
FOL.Herbrand0.ptaut_of_check|propext
FOL.HerbrandBlock0.derives0_exBlock_of_cert|Quot.sound,propext
FOL.HerbrandBlock0.ex_bloque_igualdad|Quot.sound,propext
FOL.HerbrandBlock0.subst_exBlock|Quot.sound,propext
FOL.Lift0.derives0_ex_forall_neg_absurd|Quot.sound,propext
FOL.Lift0.derives0_lift|Quot.sound,propext
FOL.Lindenbaum0.henkin_completion₀|Quot.sound,propext
FOL.Lindenbaum0.lindenbaum_lemma₀|Quot.sound,propext
FOL.Metamath.Enumeration.instEnumSymListChar|Quot.sound,propext
FOL.Metamath.Enumeration.natToFormula_surj|Quot.sound,propext
FOL.Metamath.Enumeration.natToSym_surj|Quot.sound,propext
FOL.Metamath.Semantics.contextSatisfies_lift_zero|Quot.sound,propext
FOL.Metamath.Semantics.eval_liftFormula_ext|Quot.sound,propext
FOL.Metamath.Semantics.eval_substFormula_ext|Quot.sound,propext
FOL.Metamath.Semantics.shift_updateEnv_comm|Quot.sound,propext
FOL.Metamath.Soundness0.derives0_consistent|Classical.choice,Quot.sound,propext
FOL.Metamath.Soundness0.derives0_not_complete|Classical.choice,Quot.sound,propext
FOL.Metamath.Soundness0.derives0_soundness|Classical.choice,Quot.sound,propext
FOL.NDtoLK0.herbrandExtraction_of_cutElim|Quot.sound,propext
FOL.NDtoLK0.mpLK|-
FOL.NDtoLK0.ndToLK|Quot.sound,propext
FOL.Prenex0.and_forall|Quot.sound,propext
FOL.Prenex0.impl_ex_right|Quot.sound,propext
FOL.Prenex0.impl_forall_left|Quot.sound,propext
FOL.Prenex0.or_forall|Quot.sound,propext
FOL.PrenexNF0.derives0_prenex_iff|Quot.sound,propext
FOL.PrenexNF0.iffAll_trans|-
FOL.PrenexNF0.prenex_iff|Quot.sound,propext
FOL.PrenexNF0.prenex_isPrenex|propext
FOL.PrenexNF0.quantFree_lift|-
FOL.Propositional0.derives0_em_ctx|-
FOL.Propositional0.derives0_em_prop|Quot.sound,propext
FOL.Propositional0.derives0_of_ptaut|Quot.sound,propext
FOL.Propositional0.derives0_of_ptaut_ctx|Quot.sound,propext
FOL.Propositional0.derives0_peirce_prop|Quot.sound,propext
FOL.Propositional0.kalmar|propext
FOL.Rename.derives0_rename|Quot.sound,propext
FOL.Rename.derives0_rename_conservative|Quot.sound,propext
FOL.Rename.derives0_rename_iff|Quot.sound,propext
FOL.Rename.derives0_rename_inv|Quot.sound,propext
FOL.Rename.renameFormula|-
FOL.Sequent0.herbrandExtraction_of|Quot.sound,propext
FOL.Sequent0.lk0_herbrand|propext
FOL.Sequent0.lk0_to_lkc|-
FOL.Sequent0.quantFree_subst|-
FOL.SequentSound0.eqInstance_valid|-
FOL.SequentSound0.lk0_not_empty|Classical.choice,Quot.sound,propext
FOL.SequentSound0.lk0_to_derives0|Classical.choice,Quot.sound,propext
FOL.SequentSound0.lkc_sound|Classical.choice,Quot.sound,propext
FOL.Skolem0.evalFormula_updateFunc|-
FOL.Skolem0.henkin_conservative₀|Quot.sound,propext
FOL.Skolem0.skolem_conservative₀|Classical.choice,Quot.sound,propext
FOL.SkolemHerbrand0.derives0_neg_allBlock_iff|Quot.sound,propext
FOL.SkolemHerbrand0.herbrand_of_skolemNF₀|Quot.sound,propext
FOL.SkolemHerbrand0.derives0_neg_iff_neg_skolemNF|propext,Classical.choice,Quot.sound
FOL.SkolemHerbrand0.herbrand_refutation₀|propext,Classical.choice,Quot.sound
FOL.SkolemHerbrand0.derives0_iff_neg_neg|-
FOL.SkolemHerbrand0.herbrand_validity₀|propext,Classical.choice,Quot.sound
FOL.SkolemHerbrand0.implChain_of_derives0|propext
FOL.SkolemHerbrand0.derives0_iff_implChain|propext
FOL.SkolemHerbrand0.herbrand_validity_ctx₀|propext,Classical.choice,Quot.sound
FOL.Interpolation0.lk0_refute|propext,Quot.sound
FOL.Interpolation0.lk0_to_derives0_fin|propext,Quot.sound
FOL.Interpolation0.lk0_to_lkp|propext,Quot.sound
FOL.Interpolation0.predF_em|-
FOL.Interpolation0.eqGen_side|-
FOL.Interpolation0.craig_ctx₀|propext,Quot.sound
FOL.Interpolation0.craig₀|propext,Quot.sound
FOL.Interpolation0.craig_impl₀|propext,Quot.sound
FOL.Interpolation0.craig₀_example|propext,Quot.sound
FOL.QFDecide0.instsOf_eqInstance|propext,Quot.sound
FOL.QFDecide0.ext_eqInstance|propext
FOL.QFDecide0.evI_S|propext,Quot.sound
FOL.QFDecide0.ext_agree|propext,Quot.sound
FOL.QFDecide0.eqPropCert_prune|propext,Quot.sound
FOL.QFDecide0.qfCheck_iff|propext
FOL.QFDecide0.derives0_qf_iff_bounded|propext,Quot.sound
FOL.QFDecide0.derives0_qf_iff_sub|propext,Quot.sound
FOL.QFDecide0.decideDerives0QF|propext,Quot.sound
FOL.SkolemN0.evalTerms_vars|Quot.sound,propext
FOL.SkolemN0.eval_allBlock_envPush|Quot.sound,propext
FOL.SkolemN0.eval_skolemAxN|Classical.choice,Quot.sound,propext
FOL.SkolemN0.not_occurs_vars|-
FOL.SkolemN0.skolem_conservative_n₀|Classical.choice,Quot.sound,propext
FOL.SkolemNF0.allBlock_forall|-
FOL.SkolemNF0.derives0_allBlock_mp|Quot.sound,propext
FOL.SkolemNF0.derives0_of_skolemNF|Classical.choice,Quot.sound,propext
FOL.SkolemNF0.derives0_skolemize_iff|Quot.sound,propext
FOL.SkolemNF0.occursFormula_lift|-
FOL.SkolemNF0.qdepth_subst|propext
FOL.SkolemNF0.skolemNF_shape|Quot.sound,propext
FOL.SkolemNF0.skolem_conservative_nf₀|Classical.choice,Quot.sound,propext
FOL.SkolemNF0.skolemizeF_impAll|Quot.sound,propext
FOL.derive_atom_congr|Quot.sound,propext
FOL.derive_eq_func_congr|Quot.sound,propext
FOL.substTerm_liftTerm|Quot.sound,propext
LK₀.rec|-
TheoryFramework.Instances.fol0System|-
TheoryFramework.Instances.fol0Sound|Classical.choice,Quot.sound,propext
TheoryFramework.Instances.fol0Complete|Classical.choice,Quot.sound,propext
TheoryFramework.Instances.fol0_proves_iff_models|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.GodelTwoPrf.goedel_first_prf|Quot.sound,propext
ROBINSON_PlusPlus.Meta.GodelTwoPrf.goedel_second_prf|Quot.sound,propext
ROBINSON_PlusPlus.Meta.GodelTwoPrf.prf_con_imp_godel|Quot.sound,propext
ROBINSON_PlusPlus.Meta.Representability2Prf.repr_pos'_prf|Quot.sound,propext
ROBINSON_PlusPlus.Meta.DerivCondPrf.d2_prf|Quot.sound,propext
ROBINSON_PlusPlus.Meta.SolidezPrf.prf_sound|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.SolidezPrf.prfI_sound|Quot.sound,propext
ROBINSON_PlusPlus.Meta.SolidezPrf.prfH_sound|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.SolidezPrf.consistentH_de|Quot.sound,propext
ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.prf_sound_dn|Quot.sound,propext
ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.transfer|propext
ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.axiomas_clas|-
ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.estandarDN_de|Quot.sound,propext
ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.eq_de_prf|Quot.sound,propext
ROBINSON_PlusPlus.Meta.SolidezDobleNegacion.no_refuta|Quot.sound,propext
ROBINSON_PlusPlus.Meta.ProvFiel.proofN_of_prf|Quot.sound,propext
ROBINSON_PlusPlus.Meta.ProvFiel.M_cadena_de|Quot.sound,propext
ROBINSON_PlusPlus.Meta.PuenteFOL.derives1_to_prfH|Quot.sound,propext
ROBINSON_PlusPlus.Meta.PuenteFOL.prf_of_derivesSet|Quot.sound,propext
ROBINSON_PlusPlus.Meta.PuenteFOL.prf_completo|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.PuenteFOL.goedel_I_fol|Quot.sound,propext
ROBINSON_PlusPlus.Meta.PuenteFOL.goedel_I_neg_fol|Quot.sound,propext
ROBINSON_PlusPlus.Meta.PuenteFOL.goedel_II_fol|Quot.sound,propext
ROBINSON_PlusPlus.Meta.PuenteFOL.modelo_sin_G|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.PuenteFOL.goedel_I_semantico|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.Consistencia.consistencia|Quot.sound,propext
ROBINSON_PlusPlus.Meta.Consistencia.goedel_I|Quot.sound,propext
ROBINSON_PlusPlus.Meta.Consistencia.goedel_II|Quot.sound,propext
ROBINSON_PlusPlus.Meta.Consistencia.V₀_eq_codigo|Quot.sound,propext
ROBINSON_PlusPlus.Meta.ModeloEstandar.MN_coreAxioms|Quot.sound,propext
ROBINSON_PlusPlus.Meta.ModeloCodificacion.MN_codingAxioms|Quot.sound,propext
ROBINSON_PlusPlus.Meta.ModeloCodificacion.v_ancla|Quot.sound,propext
ROBINSON_PlusPlus.Meta.ModeloCodificacion.MN_axioms|Quot.sound,propext
ROBINSON_PlusPlus.Meta.TarskiPrf.prf_diagonal|Quot.sound,propext
ROBINSON_PlusPlus.Meta.TarskiPrf.prf_tarski|Quot.sound,propext
ROBINSON_PlusPlus.Meta.TarskiPrf.tarski|Quot.sound,propext
ROBINSON_PlusPlus.Meta.TarskiPrf.tarski_semantico|Quot.sound,propext
ROBINSON_PlusPlus.Meta.TarskiPrf.godelCN_isSentence|Quot.sound,propext
ROBINSON_PlusPlus.Meta.SolidezVerificador.verificador_solido|Quot.sound,propext
ROBINSON_PlusPlus.Meta.SolidezVerificador.goedel_I_neg|Quot.sound,propext
ROBINSON_PlusPlus.Meta.SolidezVerificador.godelCN_indecidible|Quot.sound,propext
ROBINSON_PlusPlus.Meta.SolidezVerificador.modelo_prov_iff|Quot.sound,propext
ROBINSON_PlusPlus.Meta.SolidezVerificador.godelCN_verdadera|Quot.sound,propext
ROBINSON_PlusPlus.Meta.SolidezVerificador.con_verdadera|Quot.sound,propext
ROBINSON_PlusPlus.Meta.RosserW1.w1Ax|Quot.sound,propext
ROBINSON_PlusPlus.Meta.RosserW1.proofN_axioma|Quot.sound,propext
ROBINSON_PlusPlus.Meta.RosserW1.not_proofN_zero|Quot.sound,propext
ROBINSON_PlusPlus.Meta.RosserPosNum.posNum|Quot.sound,propext
ROBINSON_PlusPlus.Meta.RosserPosNum.repr_pos_num|Quot.sound,propext
ROBINSON_PlusPlus.Meta.RosserNumerales.prf_numeral_cons|Quot.sound,propext
ROBINSON_PlusPlus.Meta.RosserNumerales.prf_lenc_numeral|Quot.sound,propext
ROBINSON_PlusPlus.Meta.RosserNumerales.prf_nthc_numeral|Quot.sound,propext
ROBINSON_PlusPlus.Meta.RosserNumerales.prf_not_In_numeral|Quot.sound,propext
ROBINSON_PlusPlus.Meta.RosserNumerales.prf_runFn_numeral|Quot.sound,propext
ROBINSON_PlusPlus.Meta.RosserNumerales.prf_not_In_runFn|Quot.sound,propext
ROBINSON_PlusPlus.Meta.RosserNumerales.prf_In_decide|Quot.sound,propext
ROBINSON_PlusPlus.Meta.RosserNumEval.prf_substtc_numeral|Quot.sound,propext
ROBINSON_PlusPlus.Meta.RosserNumEval.prf_liftc_numeral|Quot.sound,propext
ROBINSON_PlusPlus.Meta.RosserNumEval.prf_substfc_numeral|Quot.sound,propext
ROBINSON_PlusPlus.Meta.RosserNumEval.prf_liftfc_numeral|Quot.sound,propext
ROBINSON_PlusPlus.Meta.RosserNumEval.codF_of_hasWitFN|Quot.sound,propext
ROBINSON_PlusPlus.Meta.RosserNumEval.prf_substfc_guarda|Quot.sound,propext
ROBINSON_PlusPlus.Meta.RosserGuardNeg.hasWitN_of_codT|Quot.sound,propext
ROBINSON_PlusPlus.Meta.RosserGuardNeg.hasWitFN_of_codF|Quot.sound,propext
ROBINSON_PlusPlus.Meta.RosserGuardNeg.codT_or_rejT|Quot.sound,propext
ROBINSON_PlusPlus.Meta.RosserGuardNeg.codF_or_rejF|Quot.sound,propext
ROBINSON_PlusPlus.Meta.RosserGuardNeg.prf_neg_hasWit|Quot.sound,propext
ROBINSON_PlusPlus.Meta.RosserGuardNeg.prf_neg_hasWitF|Quot.sound,propext
ROBINSON_PlusPlus.Meta.RosserNegLinea.lineWF_decide|Quot.sound,propext
ROBINSON_PlusPlus.Meta.RosserNegLinea.prf_neg_lineWF|Quot.sound,propext
ROBINSON_PlusPlus.Meta.RosserNegLinea.prf_not_In_axiomsCodeT|Quot.sound,propext
ROBINSON_PlusPlus.Meta.RosserNegLinea.refT_q1|Quot.sound,propext
ROBINSON_PlusPlus.Meta.RosserNegLinea.refT_thy|Quot.sound,propext
ROBINSON_PlusPlus.Meta.RosserNegLinea.refT_ind|Quot.sound,propext
ROBINSON_PlusPlus.Meta.RosserNegNum.chainOkN_decide|Quot.sound,propext
ROBINSON_PlusPlus.Meta.RosserNegNum.proofN_decide|Quot.sound,propext
ROBINSON_PlusPlus.Meta.RosserNegNum.negNum|Quot.sound,propext
ROBINSON_PlusPlus.Meta.RosserNegNum.negNum_formCode|Quot.sound,propext
ROBINSON_PlusPlus.Meta.RosserNegNum.prf_neg_lineOk_prem|Quot.sound,propext
ROBINSON_PlusPlus.Meta.Rosser.prfH_iff_prf_impChain|propext
ROBINSON_PlusPlus.Meta.Rosser.formCode_impChain|-
ROBINSON_PlusPlus.Meta.Rosser.posNumE|Quot.sound,propext
ROBINSON_PlusPlus.Meta.Rosser.negNumE|Quot.sound,propext
ROBINSON_PlusPlus.Meta.Rosser.R_isSentence|Quot.sound,propext
ROBINSON_PlusPlus.Meta.Rosser.rosser_red|Quot.sound,propext
ROBINSON_PlusPlus.Meta.Rosser.rosser_ext|Quot.sound,propext
ROBINSON_PlusPlus.Meta.Rosser.rosser|Quot.sound,propext
ROBINSON_PlusPlus.Meta.Lob.prf_lob_fix|Quot.sound,propext
ROBINSON_PlusPlus.Meta.Lob.lob|Quot.sound,propext
ROBINSON_PlusPlus.Meta.Lob.lob_iff|Quot.sound,propext
ROBINSON_PlusPlus.Meta.Lob.goedel_second_de_lob|Quot.sound,propext
ROBINSON_PlusPlus.Meta.GodelCorolarios.prf_godel_imp_con|Quot.sound,propext
ROBINSON_PlusPlus.Meta.GodelCorolarios.prf_godel_iff_con|Quot.sound,propext
ROBINSON_PlusPlus.Meta.GodelCorolarios.goedel_second_formalizado|Quot.sound,propext
ROBINSON_PlusPlus.Meta.GodelCorolarios.con_indecidible|Quot.sound,propext
ROBINSON_PlusPlus.Meta.RigidezEstandar.M_hasWitF|Quot.sound,propext
ROBINSON_PlusPlus.Meta.RigidezEstandar.M_substfc|Quot.sound,propext
ROBINSON_PlusPlus.Meta.RigidezEstandar.M_lineWF|Quot.sound,propext
ROBINSON_PlusPlus.Meta.RigidezEstandar.M_cadena|Quot.sound,propext
ROBINSON_PlusPlus.Meta.RigidezEstandar.prf_of_prov_de|Quot.sound,propext
ROBINSON_PlusPlus.Meta.RigidezEstandar.modelo_prov_iff_de|Quot.sound,propext
ROBINSON_PlusPlus.Meta.RigidezEstandar.godelCN_verdadera_de|Quot.sound,propext
ROBINSON_PlusPlus.Meta.RigidezEstandar.con_verdadera_de|Quot.sound,propext
ROBINSON_PlusPlus.Meta.RigidezEstandar.control_ancla|Quot.sound,propext
ROBINSON_PlusPlus.Meta.TarskiPrf.tarski_semantico_de|Quot.sound,propext
ROBINSON_PlusPlus.Meta.SegundoModelo.substfcB_codF|Quot.sound,propext
ROBINSON_PlusPlus.Meta.SegundoModelo.agreeF|Quot.sound,propext
ROBINSON_PlusPlus.Meta.SegundoModelo.vB_ancla|Quot.sound,propext
ROBINSON_PlusPlus.Meta.SegundoModelo.estandar_MB|Quot.sound,propext
ROBINSON_PlusPlus.Meta.SegundoModelo.segundo_modelo|Quot.sound,propext
ROBINSON_PlusPlus.Meta.SegundoModelo.modelo_prov_iff_MB|Quot.sound,propext
ROBINSON_PlusPlus.Meta.Provability.charsCode|-
ROBINSON_PlusPlus.Meta.Provability.strCode|-
ROBINSON_PlusPlus.Minimal.Axioms.strCodeM|-
ROBINSON_PlusPlus.Minimal.Axioms.codeNatStr|-
ROBINSON_PlusPlus.Minimal.SymLit.symProbe|-
ROBINSON_PlusPlus.Minimal.Axioms.axiomsCodeT|-
derives0_to_derives|propext
instDecidableEqFormula|-
liftFormula|-
neg|-
substFormula|-
top|-
FOL.BlockExtraction0.herbrandExtractionBlock_of|Quot.sound,propext
FOL.BlockExtraction0.instB_snoc|Quot.sound,propext
FOL.BlockExtraction0.quantFree_of_blockInv|Quot.sound,propext
FOL.Canonical0.derives0_peirce|Classical.choice,Quot.sound,propext
FOL.Compacity0.consistency_of_satisfiable₀|Classical.choice,Quot.sound,propext
FOL.Compacity0.model_existence_countable₀|Classical.choice,Quot.sound,propext
FOL.Craig0.predF_lift|-
FOL.Eq0.derives0_eq_symm|Quot.sound,propext
FOL.Eq0.derives0_eq_trans|Quot.sound,propext
FOL.Finitary0.derives0_not_P_fin|Quot.sound,propext
FOL.Finitary0.lk0_no_bot|Quot.sound,propext
FOL.Finitary0.lkc_empty_of_no_bot|-
FOL.Finitary0.lkc_no_bot|Quot.sound,propext
FOL.Finitary0.lkc_not_empty_fin|Quot.sound,propext
FOL.HenkinLimit0.hen_consistent|Quot.sound,propext
FOL.Herbrand0.ex_tercio|Quot.sound,propext
FOL.HerbrandBlock0.derives0_exBlock_of_disj|Quot.sound,propext
FOL.HerbrandBlock0.derives0_exBlock_of_inst|Quot.sound,propext
FOL.Lindenbaum0.derivesSet0_intro_impl|-
FOL.Lindenbaum0.max_cons_contains|Classical.choice,Quot.sound,propext
FOL.NDtoLK0.viaEqImpl|-
FOL.Prenex0.and_ex|Quot.sound,propext
FOL.Prenex0.impl_ex_left|Quot.sound,propext
FOL.Prenex0.impl_forall_right|Quot.sound,propext
FOL.Prenex0.or_ex|Quot.sound,propext
FOL.PrenexNF0.mergeAnd_iff|Quot.sound,propext
FOL.PrenexNF0.mergeImpl_iff|Quot.sound,propext
FOL.Propositional0.elim_atoms|Quot.sound,propext
FOL.SequentSound0.lk0_sound|Classical.choice,Quot.sound,propext
FOL.SequentSound0.lk0_to_derives2|Classical.choice,Quot.sound,propext
FOL.Skolem0.evalTerm_new|-
FOL.Skolem0.evalTerm_updateFunc|-
FOL.SkolemHerbrand0.impAll_ex_neg_not_forall|Quot.sound,propext
FOL.SkolemHerbrand0.impAll_neg_allBlock|Quot.sound,propext
FOL.SkolemNF0.derives0_skolemize|Quot.sound,propext
FOL.SkolemNF0.occurs_prenex|propext
FOL.SkolemNF0.skolemizeF_shape|Quot.sound,propext
LKh.rec|-
ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_isTermCodeE1_of_In|Quot.sound,propext
ROBINSON_PlusPlus.Meta.D3BodyPrf.hA_lineWFDotAt|Quot.sound,propext
ROBINSON_PlusPlus.Meta.D3BodyPrf.pcc_bnd_bridge_at|Quot.sound,propext
ROBINSON_PlusPlus.Meta.D3ChainDotPrf.DEUDA_chainOkBDot_of|Quot.sound,propext
ROBINSON_PlusPlus.Meta.D3ChainDotPrf.PrfH_chainOkB_bnd_bridge|Quot.sound,propext
ROBINSON_PlusPlus.Meta.D3ChainDotPrf.chainOkBPsiDot_eq|Quot.sound,propext
ROBINSON_PlusPlus.Meta.D3ChainDotPrf.d3_prf_of|Quot.sound,propext
ROBINSON_PlusPlus.Meta.D3ChainDotPrf.d3_prf_of_body|Quot.sound,propext
ROBINSON_PlusPlus.Meta.D3ChainDotPrf.d3_prf_of_body_only|Quot.sound,propext
ROBINSON_PlusPlus.Meta.D3ChainDotPrf.d3_prf_of_chainOkBDot|Quot.sound,propext
ROBINSON_PlusPlus.Meta.D3ChainDotPrf.d3_prf_of_halves|Quot.sound,propext
ROBINSON_PlusPlus.Meta.D3ChainDotPrf.d3_prf_of_hbody|Quot.sound,propext
ROBINSON_PlusPlus.Meta.D3ChainDotPrf.d3_prf_of_two|Quot.sound,propext
ROBINSON_PlusPlus.Meta.D3ChainDotPrf.hC_dot_of_chainOkBDot|Quot.sound,propext
ROBINSON_PlusPlus.Meta.D3ChainDotPrf.hPinv_chainOkBPsi|Quot.sound,propext
ROBINSON_PlusPlus.Meta.D3ChainDotPrf.hPsiId_chainOkBPsiDot|Quot.sound,propext
ROBINSON_PlusPlus.Meta.D3ChainDotPrf.hwP_chainOkBPsi|Quot.sound,propext
ROBINSON_PlusPlus.Meta.D3ChainDotPrf.hwPsi_chainOkBPsiDot|Quot.sound,propext
ROBINSON_PlusPlus.Meta.D3ChainDotPrf.pcc_bdCarcLt_reflect|Quot.sound,propext
ROBINSON_PlusPlus.Meta.D3ChainDotPrf.pcc_chainOkBDot_imp_chainOkDot|Quot.sound,propext
ROBINSON_PlusPlus.Meta.D3ChainDotPrf.pcc_premsBody_reflect|Quot.sound,propext
ROBINSON_PlusPlus.Meta.D3ChainDotPrf.substfc_chainOkBPsiDot|Quot.sound,propext
ROBINSON_PlusPlus.Meta.Delta0ReflectPrf.pcc_lt_tracked|Quot.sound,propext
ROBINSON_PlusPlus.Meta.DotConsPrf.pcc_dot_cons|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftcPrf.CRIT_hasWit_descenso|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftcPrf.CRIT_targetLift_real|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftcPrf.CRIT_targetLiftsc_real|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO_at_hasWit|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO_at_imp|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO_at_lista_imp|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO_hasWit|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO_imp|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO_lista|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO_lista_imp|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftcPrf.PHI_all|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftcPrf.PHI_step|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftcPrf.PHIat_all|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftcPrf.PHIat_step|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftcPrf.iz_inv_es_prf_substtc_termCode_nil|-
ROBINSON_PlusPlus.Meta.EvalLiftcPrf.pcc_eval_liftc|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftcPrf.pcc_eval_liftc_at|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftcPrf.pcc_eval_liftsc_at|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftcPrf.targetLift_es_el_del_sondeo|-
ROBINSON_PlusPlus.Meta.EvalLiftcPrf.targetLiftsc_es_el_del_sondeo|-
ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.PHIliftfc_step|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.casoAtomL_thm|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.casoBinL5|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.casoBotL|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.casoEqL_thm|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.casoUnL6|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.casoUnL9|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.deuda_of_isFC1|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.hasWitF_liftfc_of_deuda|-
ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.liftfcT_termCode|-
ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.pcc_eval_liftfc|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.pcc_eval_liftfc_modulo_2|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.pcc_eval_liftfc_modulo_8|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.pcc_eval_liftfc_wit|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.pcc_liftfc_atom_code|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.pcc_liftfc_bottom_code|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.pcc_liftfc_eq_code|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.pcc_liftfc_ex_code|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.pcc_liftfc_forall_code|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.pcc_liftfc_impl_code|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalNthcPrf.pcc_nthc_zero_code|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalSubstfcPrf.DESCENSO_substfc|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalSubstfcPrf.pcc_congr_substfcT_arg2_code|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalSubstfcPrf.pcc_eval_substfc|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalSubstfcPrf.pcc_eval_substfc_wit|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalSubstfcPrf.pcc_substfc_un_dot|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalSubsttcPrf.PHIsubsttc_step|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalSubsttcPrf.pcc_eval_substtc|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalSubsttcPrf.pcc_eval_substtc_hasWit|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalSubsttcPrf.pcc_eval_substtsc|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalSubsttcPrf.pcc_substtc_func_code|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalSubsttcPrf.pcc_substtc_var_lt_code|Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalSubsttcPrf.prf_pred_dot_guarded|Quot.sound,propext
ROBINSON_PlusPlus.Meta.GodelTwoPrf.prf_godelCN_fixedpoint|Quot.sound,propext
ROBINSON_PlusPlus.Meta.HasWitFTrackedPrf.hGuard_of_slots|Quot.sound,propext
ROBINSON_PlusPlus.Meta.HasWitFTrackedPrf.pcc_hGuardF|Quot.sound,propext
ROBINSON_PlusPlus.Meta.HasWitFTrackedPrf.pcc_hasWitF_exc|Quot.sound,propext
ROBINSON_PlusPlus.Meta.HasWitFTrackedPrf.pcc_isFC1_trackedC|Quot.sound,propext
ROBINSON_PlusPlus.Meta.HasWitFTrackedPrf.pcc_isFormCodeE2_trackedC|Quot.sound,propext
ROBINSON_PlusPlus.Meta.HasWitFTrackedPrf.pcc_shapeNul_fc|Quot.sound,propext
ROBINSON_PlusPlus.Meta.HasWitFTrackedPrf.pcc_wfAllF_trackedC|Quot.sound,propext
ROBINSON_PlusPlus.Meta.HasWitTcFnPrf.prf_argsIn_mono|Quot.sound,propext
ROBINSON_PlusPlus.Meta.HasWitTcFnPrf.prf_hasWit_tcFn|Quot.sound,propext
ROBINSON_PlusPlus.Meta.HasWitTcFnPrf.prf_wfAll1_cons|Quot.sound,propext
ROBINSON_PlusPlus.Meta.HasWitTrackedPrf.hGuard_of_deudaF|Quot.sound,propext
ROBINSON_PlusPlus.Meta.HasWitTrackedPrf.pcc_argsIn_pair_tracked|Quot.sound,propext
ROBINSON_PlusPlus.Meta.HasWitTrackedPrf.pcc_hGuardT|Quot.sound,propext
ROBINSON_PlusPlus.Meta.HasWitTrackedPrf.pcc_hasWit_exc|Quot.sound,propext
ROBINSON_PlusPlus.Meta.HasWitTrackedPrf.pcc_isTC1_tracked_of|Quot.sound,propext
ROBINSON_PlusPlus.Meta.HasWitTrackedPrf.pcc_isTermCodeE1_tracked|Quot.sound,propext
ROBINSON_PlusPlus.Meta.HasWitTrackedPrf.pcc_wfAll1_trackedC|Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.PrfH_congr_targetLift|Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_liftc0_func_code|Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_liftc0_var_code|Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_liftc_func_code|Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_liftc_var_ge_code|Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_liftc_var_lt_code|Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_liftsc0_cons_code|Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_liftsc0_nil_code|Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_liftsc_cons_code|Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_liftsc_nil_code|Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_zero_lt_succ_code|Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_liftc_varc_cases|Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substfc_atom2CodeFn|Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_caso_funcc|Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_caso_funcc_at|Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_caso_funcc_imp|Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_caso_varc|Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_caso_varc_lift_at|Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_isTermCodeE1_imp|Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_lista_cons|Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_lista_cons_at|Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_lista_cons_imp|Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_lista_cons_imp_at|Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_lista_nil|Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_lista_nil_at|Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_shapeBin_imp|Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_shapeBin_imp_at|Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_shapeUn_imp|Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_shapeUn_imp_at|Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_termCode|Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_termCode_at|Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_termsCode|Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.substF_targetLift_hole|Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.substTerm_termCode|propext
ROBINSON_PlusPlus.Meta.LiftfcWitnessPrf.deuda_hasWitF_liftfc|Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftfcWitnessPrf.prf_hasWitArgs_liftsc_of|Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftfcWitnessPrf.prf_hasWitF_liftfc|Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftfcWitnessPrf.prf_hasWit_liftc_at|Quot.sound,propext
ROBINSON_PlusPlus.Meta.LineWFGuardPrf.hGuard_of_deudas|Quot.sound,propext
ROBINSON_PlusPlus.Meta.LineWFGuardPrf.hcond_absorbe_cascade|Quot.sound,propext
ROBINSON_PlusPlus.Meta.LineWFGuardPrf.hcond_absorbe_extra|Quot.sound,propext
ROBINSON_PlusPlus.Meta.ListEtaPrf.prf_eta_lenc|Quot.sound,propext
ROBINSON_PlusPlus.Meta.ListEtaPrf.prf_nthc1_carc_cdrc|Quot.sound,propext
ROBINSON_PlusPlus.Meta.PremsBdAllPrf.d3_prf_real|Quot.sound,propext
ROBINSON_PlusPlus.Meta.PremsBdAllPrf.hB_premsDotAt|Quot.sound,propext
ROBINSON_PlusPlus.Meta.PremsBdAllPrf.hPsiId_premsPsi|Quot.sound,propext
ROBINSON_PlusPlus.Meta.PremsBdAllPrf.hbdAllPrems_of_body|Quot.sound,propext
ROBINSON_PlusPlus.Meta.PremsBdAllPrf.hbdAllPrems_unpacked|Quot.sound,propext
ROBINSON_PlusPlus.Meta.PremsBdAllPrf.hwPsi_premsPsi|Quot.sound,propext
ROBINSON_PlusPlus.Meta.PremsBdAllPrf.premsBody_deuda|Quot.sound,propext
ROBINSON_PlusPlus.Meta.PremsBdAllPrf.substfc_id_substCodeF2|Quot.sound,propext
ROBINSON_PlusPlus.Meta.PremsOfDotPrf.pcc_eval_premsOf|Quot.sound,propext
ROBINSON_PlusPlus.Meta.PremsOfDotPrf.pcc_premsOf_dot_mp|Quot.sound,propext
ROBINSON_PlusPlus.Meta.PremsOfDotPrf.pcc_rw_dot_consN|Quot.sound,propext
ROBINSON_PlusPlus.Meta.PremsOfTagPrf.prf_of_premsOf_branches|propext
ROBINSON_PlusPlus.Meta.PremsOfTagPrf.prf_premsOf_mp|Quot.sound,propext
ROBINSON_PlusPlus.Meta.PremsOfTagPrf.prf_premsOf_of_tag|Quot.sound,propext
ROBINSON_PlusPlus.Meta.PremsOfTagPrf.prf_premsOf_thy|Quot.sound,propext
ROBINSON_PlusPlus.Meta.Representability2Prf.f1_traduccion_refutada|Quot.sound,propext
ROBINSON_PlusPlus.Meta.Representability2Prf.prf_ancla|Quot.sound,propext
ROBINSON_PlusPlus.Meta.SubstTreeReflect.PrfH_tc_objAt|Quot.sound,propext
ROBINSON_PlusPlus.Meta.SubstTreeReflect.pcc_lineWF_tracked|Quot.sound,propext
ROBINSON_PlusPlus.Meta.SubstTreeReflect.pcc_lineWF_tracked_ind_imp|Quot.sound,propext
ROBINSON_PlusPlus.Meta.SubstTreeReflect.pcc_lineWF_tracked_leibniz_imp|Quot.sound,propext
ROBINSON_PlusPlus.Meta.SubstTreeReflect.pcc_lineWF_tracked_listInd_imp|Quot.sound,propext
ROBINSON_PlusPlus.Meta.SubstTreeReflect.pcc_lineWF_tracked_modulo_2|Quot.sound,propext
ROBINSON_PlusPlus.Meta.SubstTreeReflect.pcc_lineWF_tracked_modulo_other|Quot.sound,propext
ROBINSON_PlusPlus.Meta.SubstTreeReflect.pcc_lineWF_tracked_q1_imp|Quot.sound,propext
ROBINSON_PlusPlus.Meta.SubstTreeReflect.pcc_lineWF_tracked_q2_imp|Quot.sound,propext
ROBINSON_PlusPlus.Meta.SubstTreeReflect.pcc_lineWF_tracked_q3_imp|Quot.sound,propext
ROBINSON_PlusPlus.Meta.SubstTreeReflect.pcc_lineWF_tracked_qconf_imp|Quot.sound,propext
ROBINSON_PlusPlus.Meta.SubstTreeReflect.prf_condD_of_stree_eq|Quot.sound,propext
ROBINSON_PlusPlus.Meta.SubstTreeReflect.prf_substtc_code|Quot.sound,propext
ROBINSON_PlusPlus.Meta.SubstfcWitnessPrf.prf_hasWitF_bin|Quot.sound,propext
ROBINSON_PlusPlus.Meta.SubstfcWitnessPrf.prf_hasWitF_implc|Quot.sound,propext
ROBINSON_PlusPlus.Meta.SubstfcWitnessPrf.prf_hasWitF_substfc|Quot.sound,propext
ROBINSON_PlusPlus.Meta.SubstfcWitnessPrf.prf_hasWit_funcc2|Quot.sound,propext
ROBINSON_PlusPlus.Meta.SubstfcWitnessPrf.prf_hasWit_substtc|Quot.sound,propext
ROBINSON_PlusPlus.Meta.SubstfcWitnessPrf.prf_nil_or_cons|Quot.sound,propext
ROBINSON_PlusPlus.Meta.TrackedAtomsPrf.pcc_In_atom_tracked|Quot.sound,propext
ROBINSON_PlusPlus.Meta.TrackedAtomsPrf.pcc_boundedIn_tracked|Quot.sound,propext
ROBINSON_PlusPlus.Meta.TrackedAtomsPrf.pcc_child_tracked|Quot.sound,propext
ROBINSON_PlusPlus.Meta.TrackedAtomsPrf.pcc_shape_tracked|Quot.sound,propext
derives0_raa|-
EOF

TMP=$(mktemp -d)
LEANFILE="$TMP/Footprints.lean"
{
  echo "import ROBINSON_PlusPlus"
  echo "import FOL"
  # TheoryFramework no la importa el barril FOL: su instancia sobre Derives₀ (2026-09-27) se mide aparte
  echo "import TheoryFramework.Instances.FOL"
  while IFS='|' read -r NOMBRE _; do
    [ -n "$NOMBRE" ] || continue
    echo "#print axioms $NOMBRE"
  done <<< "$TABLA"
} > "$LEANFILE"

echo "════ FOOTPRINTS DE LOS TITULARES ════"

if ! command -v lake >/dev/null 2>&1; then
  echo "  ⚠️  SIN MEDIR — 'lake' no está en el PATH de este shell."
  echo "      Lánzalo desde PowerShell. Un control que no se ejecuta NO es un control."
  rm -rf "$TMP"
  exit 2
fi

SALIDA=$(lake env lean "$LEANFILE" 2>&1)
RC=$?
# ⚠️ `#print axioms` PARTE LA LÍNEA cuando la lista es larga. Se aplasta todo a una sola
# línea antes de buscar: si no, los footprints de tres axiomas no casan nunca.
PLANA=$(printf '%s' "$SALIDA" | tr '\n' ' ' | tr -s ' ')

FAIL=0
N=0
while IFS='|' read -r NOMBRE ESPERADO; do
  [ -n "$NOMBRE" ] || continue
  N=$((N + 1))
  SEG=$(printf '%s' "$PLANA" \
        | grep -oF -e "'$NOMBRE' does not depend on any axioms" -e "'$NOMBRE' depends on axioms: [" \
        | head -1)
  if [ -z "$SEG" ]; then
    # ⛔ La causa raíz de «un verde que no comprueba»: el patrón no aparece. Rompe.
    printf "  ✗ %-55s NO MEDIDO — la declaración no aparece en la salida\n" "$NOMBRE"
    FAIL=1
    continue
  fi
  if printf '%s' "$SEG" | grep -qF 'does not depend'; then
    REAL="-"
  else
    REAL=$(printf '%s' "$PLANA" \
           | sed -E "s/.*'$(printf '%s' "$NOMBRE" | sed 's/[.[\*^$]/\\&/g')' depends on axioms: \[([^]]*)\].*/\1/" \
           | tr -d ' ' )
    REAL=$(printf '%s' "$REAL" | tr ',' '\n' | sort | paste -sd, -)
  fi
  ESP=$(printf '%s' "$ESPERADO" | tr ',' '\n' | sort | paste -sd, -)
  if [ "$REAL" = "$ESP" ]; then
    printf "  ✓ %-55s %s\n" "$NOMBRE" "$REAL"
  else
    printf "  ✗ %-55s dice [%s], esperado [%s]\n" "$NOMBRE" "$REAL" "$ESP"
    FAIL=1
  fi
done <<< "$TABLA"

rm -rf "$TMP"

# ─── [COBERTURA] ¿falta algún titular POR DECLARAR? ─────────────────────────
# ⛔⛔ POR QUÉ EXISTE (2026-09-18, ADR-073, encargo A2): el verde de este control decía que las
# filas DECLARADAS cuadran, y **no decía cuántas FALTAN**. Medido: 356 nombres impresos por el
# árbol contra 161 filas ⇒ **222 titulares entregados que no vigilaba nadie**. Ya había fallado
# igual el 09-17 (la tabla tenía 85 y había 88 entregados).
# 🔑 *Un control que sólo mira lo declarado mide su propia tabla, no el árbol.*
echo ""
echo "════ [COBERTURA] titulares impresos por el árbol y NO declarados ════"
COBTMP=$(mktemp)
# ✏️ 2026-10-21 (T11b, ADR-188): el nombre se extraía con «'[^']+'», y un nombre con PRIMA (`repr_pos'_prf`) salía
# partido —«_prf», un titular inexistente—. El nombre no lleva espacios: «'[^ ]+'» lo toma entero, primas incluidas. Y
# sin retro‑referencias (PLAN-PRUEBAS §4): se quitan la cola y la comilla de cabeza por separado.
# ✏️ 2026-10-28 (T11, ADR-199): la extracción, en una función, con su PRUEBA DE ROTURA: una prima interior y una FINAL
# (con la extracción de antes de T11b, un nombre acabado en prima desaparecía: un verde falso si se imprimía sin fila).
cob_extrae() {
  tr '\n' ' ' | tr -s ' ' \
    | grep -oE "'[^ ]+' (depends on axioms|does not depend)" \
    | sed -E "s/' (depends on axioms|does not depend)$//" | sed -E "s/^'//"
}
COB_AUTO=$(printf '%s\n' "info: a.lean:1:0: 'X.uno'' depends on axioms: [propext]" \
  "info: b.lean:2:0: 'X.dos'_tres' does not depend on any axioms" | cob_extrae | tr '\n' ' ')
if [ "$COB_AUTO" != "X.uno' X.dos'_tres " ]; then
  echo "  ❌ la extracción de nombres no pasa su prueba de rotura (primas): «$COB_AUTO»"
  FAIL=1
fi
( lake build FOL TheoryFramework 2>&1; lake build 2>&1 ) | cob_extrae | sort -u > "$COBTMP"
COB_IMPRESOS=$(wc -l < "$COBTMP" | tr -d ' ')
COBDECL=$(mktemp)
printf '%s' "$TABLA" | sed -E 's/\|.*//' | sed '/^$/d' | sort -u > "$COBDECL"
# ✏️ 2026-10-28 (T11, ADR-199): el universo, también desde la FUENTE: cada `#print axioms X` del árbol del build (sin
# comentarios ni cadenas, `strip-lean.awk`). La construcción tiene que imprimirlos todos: si no, o no se construyó o la
# extracción no los ve, y el control no puede aprobar. Y los que faltan en la tabla salen de los dos universos.
COBSRC=$(mktemp)
find ROBINSON_PlusPlus ../FOL/FOL ../FOL/TheoryFramework -name '*.lean' ! -path '*/.lake/*' -print0 2>/dev/null \
  | xargs -0 env LC_ALL=C awk -f strip-lean.awk | grep -oE "^#print axioms [^ ]+" | sed 's/^#print axioms //' \
  | sort -u > "$COBSRC"
COB_NOIMP=$(comm -23 "$COBSRC" "$COBTMP")
if [ ! -s "$COBSRC" ]; then
  echo "  ❌ NO PUDE MEDIR la fuente: ningún «#print axioms» en el árbol (¿strip-lean.awk? ¿../FOL?)."
  FAIL=1
elif [ -n "$COB_NOIMP" ]; then
  echo "  ❌ «#print axioms» en la fuente que la construcción NO imprime (o la extracción no ve):"
  printf '%s\n' "$COB_NOIMP" | head -10 | sed 's/^/      /'
  FAIL=1
fi
COB_FALTAN=$(sort -u "$COBTMP" "$COBSRC" | comm -23 - "$COBDECL")
# ⚠️ `printf '%s'` NO añade salto final: con EXACTAMENTE un titular sin declarar, `wc -l`
# contaba 0 y este control APROBABA. Lo cazó su propia prueba de rotura, a la primera.
# 🔑 Un control que no se ha visto romper no es un control — y el que lo escribe tampoco
#    está exento: éste nació con el bug que el repo lleva doce veces documentando.
COB_N=$(printf '%s\n' "$COB_FALTAN" | sed '/^$/d' | wc -l | tr -d ' ')
if [ "$COB_IMPRESOS" = "0" ]; then
  echo "  ❌ NO PUDE MEDIR: la construcción no imprimió ningún footprint."
  echo "      Un control que no mide no aprueba. ¿Se construyó de verdad?"
  FAIL=1
elif [ "$COB_N" = "0" ]; then
  echo "  ✓ los $COB_IMPRESOS titulares que el árbol imprime (con los $(wc -l < "$COBSRC" | tr -d " ") «#print axioms» de la fuente) están TODOS declarados"
else
  echo "  ❌ $COB_N titular(es) impreso(s) por el árbol y SIN declarar en la tabla:"
  printf '%s\n' "$COB_FALTAN" | sed '/^$/d' | head -20 | sed 's/^/      /'
  [ "$COB_N" -gt 20 ] && echo "      … y $((COB_N - 20)) más"
  echo "      🔑 Un titular que no se declara no lo vigila nadie. Añádelos a TABLA."
  FAIL=1
fi
rm -f "$COBTMP" "$COBDECL" "$COBSRC"

echo
if [ "$N" = "0" ]; then
  echo "❌ LA TABLA ESTÁ VACÍA — el control no comprueba nada."
  exit 1
fi
if [ "$FAIL" = "0" ]; then
  echo "✅ LOS $N FOOTPRINTS CUADRAN."
else
  echo "❌ ALGÚN FOOTPRINT NO CUADRA."
  echo "   O el código cambió de dependencias (⇒ mirar QUÉ entró, puede ser grave),"
  echo "   o la tabla de este script está obsoleta (⇒ actualizarla Y la documentación)."
  [ "$RC" != "0" ] && echo "   ⚠️  Además, 'lake env lean' salió con código $RC."
fi
exit "$FAIL"
