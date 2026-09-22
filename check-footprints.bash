#!/usr/bin/env bash
# check-footprints.bash — comprueba que los teoremas TITULARES tienen EXACTAMENTE el footprint
# que la documentación publica. ROMPE si alguno no cuadra.
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
FOL.BlockExtraction0.herbrand_block|Quot.sound,propext
FOL.BlockExtraction0.herbrand_extraction_block|Quot.sound,propext
FOL.BlockExtraction0.instB_nil|-
FOL.BlockExtraction0.lk0_herbrand_block|Quot.sound,propext
FOL.Canonical0.completeness₀|Classical.choice,Quot.sound,propext
FOL.Canonical0.derives0_complete_iff|Classical.choice,Quot.sound,propext
FOL.Canonical0.derives0_em|Classical.choice,Quot.sound,propext
FOL.Canonical0.eval_pullback_formula|-
FOL.Canonical0.model_existence_lemma₀|Classical.choice,Quot.sound,propext
FOL.Canonical0.truth_lemma|Classical.choice,Quot.sound,propext
FOL.Compacity0.compactness₀|Classical.choice,Quot.sound,propext
FOL.Compacity0.loewenheim_skolem_down|Classical.choice,Quot.sound,propext
FOL.Craig0.craig|Quot.sound,propext
FOL.Craig0.craig_impl|Quot.sound,propext
FOL.Craig0.lkp_example|-
FOL.Craig0.lkp_to_lk0|-
FOL.Craig0.maehara|Quot.sound,propext
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
FOL.Finitary0.derives0_consistent_fin|Quot.sound,propext
FOL.Finitary0.lk0_empty|Quot.sound,propext
FOL.Finitary0.lk0_empty_of_no_bot|-
FOL.Finitary0.lk0_not_empty_fin|Quot.sound,propext
FOL.Finitary0.lk0_tval|Quot.sound,propext
FOL.Finitary0.lkc_empty|Quot.sound,propext
FOL.Finitary0.lkc_tval|Quot.sound,propext
FOL.Finitary0.tval_eqInstance|-
FOL.Fresh0.cst_bound_formula|Classical.choice,Quot.sound,propext
FOL.Fresh0.cst_bound_sym|Classical.choice,Quot.sound,propext
FOL.Fresh0.derivesSet0_shift_inv|Classical.choice,Quot.sound,propext
FOL.Fresh0.exists_fresh|Classical.choice,Quot.sound,propext
FOL.Fresh0.instFreshSymString|Classical.choice,Quot.sound,propext
FOL.Fresh0.shiftTheory_consistent|Classical.choice,Quot.sound,propext
FOL.Hauptsatz0.cutElim_of|-
FOL.Hauptsatz0.cutLeftAux|Quot.sound,propext
FOL.Hauptsatz0.cutPrinAux|Quot.sound,propext
FOL.Hauptsatz0.cut_elimination|Quot.sound,propext
FOL.Hauptsatz0.eqInstance_lift|-
FOL.Hauptsatz0.eqInstance_subst|-
FOL.Hauptsatz0.hauptsatz|Quot.sound,propext
FOL.Hauptsatz0.herbrand|Quot.sound,propext
FOL.Hauptsatz0.herbrand_extraction|Quot.sound,propext
FOL.Hauptsatz0.liftFormula_subst_le|Quot.sound,propext
FOL.Hauptsatz0.lk0_to_lkh|propext
FOL.Hauptsatz0.lkh_lift|Quot.sound,propext
FOL.Hauptsatz0.lkh_mono|-
FOL.Hauptsatz0.lkh_subst|Quot.sound,propext
FOL.Hauptsatz0.lkh_to_lk0|-
FOL.Hauptsatz0.substFormula_subst_le|Quot.sound,propext
FOL.Henkin0.henkin_step_consistent|Classical.choice,Quot.sound,propext
FOL.HenkinLimit0.henLimit_consistent|Classical.choice,Quot.sound,propext
FOL.HenkinLimit0.henLimit_witness|Classical.choice,Quot.sound,propext
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
FOL.Lindenbaum0.henkin_completion|Classical.choice,Quot.sound,propext
FOL.Lindenbaum0.lindenbaum_lemma|Classical.choice,Quot.sound,propext
FOL.Metamath.Enumeration.instEnumSymListChar|Quot.sound,propext
FOL.Metamath.Enumeration.instEnumSymString|Classical.choice,Quot.sound,propext
FOL.Metamath.Enumeration.natToFormula_surj|Classical.choice,Quot.sound,propext
FOL.Metamath.Enumeration.natToString_surj|Classical.choice,Quot.sound,propext
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
FOL.Rename.derives0_rename_conservative|Classical.choice,Quot.sound,propext
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
FOL.Skolem0.henkin_conservative|Classical.choice,Quot.sound,propext
FOL.Skolem0.skolem_conservative|Classical.choice,Quot.sound,propext
FOL.SkolemHerbrand0.derives0_neg_allBlock_iff|Quot.sound,propext
FOL.SkolemHerbrand0.herbrand_of_skolemNF|Quot.sound,propext
FOL.SkolemN0.evalTerms_vars|Quot.sound,propext
FOL.SkolemN0.eval_allBlock_envPush|Quot.sound,propext
FOL.SkolemN0.eval_skolemAxN|Classical.choice,Quot.sound,propext
FOL.SkolemN0.not_occurs_vars|-
FOL.SkolemN0.skolem_conservative_n|Classical.choice,Quot.sound,propext
FOL.SkolemNF0.allBlock_forall|-
FOL.SkolemNF0.derives0_allBlock_mp|Quot.sound,propext
FOL.SkolemNF0.derives0_of_skolemNF|Classical.choice,Quot.sound,propext
FOL.SkolemNF0.derives0_skolemize_iff|Quot.sound,propext
FOL.SkolemNF0.occursFormula_lift|-
FOL.SkolemNF0.qdepth_subst|propext
FOL.SkolemNF0.skolemNF_shape|Quot.sound,propext
FOL.SkolemNF0.skolem_conservative_nf|Classical.choice,Quot.sound,propext
FOL.SkolemNF0.skolemizeF_impAll|Quot.sound,propext
FOL.derive_atom_congr|Quot.sound,propext
FOL.derive_eq_func_congr|Quot.sound,propext
FOL.instFreshSymListChar|propext
FOL.substTerm_liftTerm|Quot.sound,propext
LK₀.rec|-
ROBINSON_PlusPlus.Meta.GodelTwoPrf.goedel_first_prf|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.GodelTwoPrf.goedel_second_prf|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.Provability.charsCode|-
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
FOL.HenkinLimit0.hen_consistent|Classical.choice,Quot.sound,propext
FOL.Herbrand0.ex_tercio|Quot.sound,propext
FOL.HerbrandBlock0.derives0_exBlock_of_disj|Quot.sound,propext
FOL.HerbrandBlock0.derives0_exBlock_of_inst|Quot.sound,propext
FOL.Lindenbaum0.derivesSet0_intro_impl|Classical.choice,Quot.sound,propext
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
ROBINSON_PlusPlus.Meta.ChainNegPrf.derives_chainOk_neg_of_line|Classical.choice,FOL.MetaRules.imp_intro,FOL.MetaRules.raa,Quot.sound,ROBINSON_PlusPlus.Full.ax_induction_prim,ROBINSON_PlusPlus.Full.ax_list_induction,propext
ROBINSON_PlusPlus.Meta.ChainNegPrf.prf_boundedPremsIn_of_chainOk|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.ChainNegPrf.derives_chainOk_neg_of_prems|Classical.choice,FOL.MetaRules.imp_intro,FOL.MetaRules.raa,Quot.sound,propext,ROBINSON_PlusPlus.Full.ax_induction_prim,ROBINSON_PlusPlus.Full.ax_list_induction
ROBINSON_PlusPlus.Meta.ChainNegPrf.derives_not_boundedCarcLt|Classical.choice,FOL.MetaRules.imp_intro,FOL.MetaRules.or_elim,FOL.MetaRules.raa,Quot.sound,propext,ROBINSON_PlusPlus.Full.ax_induction_prim,ROBINSON_PlusPlus.Full.ax_list_induction
ROBINSON_PlusPlus.Meta.ChainNegPrf.decodeChainAux_none_first|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.ChainNegPrf.decodeChainAux_carc_mem|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.ChainNegPrf.stdArgs_objList|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.ChainNegPrf.derives_lineWF_neg_of_tag_big|Classical.choice,FOL.MetaRules.imp_intro,Quot.sound,propext,ROBINSON_PlusPlus.Full.ax_induction_prim,ROBINSON_PlusPlus.Full.ax_list_induction
ROBINSON_PlusPlus.Meta.ChainNegPrf.derives_lineWF_neg_of_lenc_imp|Classical.choice,FOL.MetaRules.ex_elim,FOL.MetaRules.imp_intro,FOL.MetaRules.raa,Quot.sound,propext,ROBINSON_PlusPlus.Full.ax_induction_prim,ROBINSON_PlusPlus.Full.ax_list_induction
ROBINSON_PlusPlus.Meta.ChainNegPrf.prf_lenc_p1|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.ChainNegPrf.prf_lenc_mp|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.ChainDecode.not_mem_of_findIdx_none|propext
ROBINSON_PlusPlus.Meta.AxiomListCode.neg_In_axiomsCodeT_of_not_mem|propext,Classical.choice,Quot.sound,FOL.MetaRules.ex_elim,FOL.MetaRules.imp_intro,FOL.MetaRules.or_elim,FOL.MetaRules.raa,ROBINSON_PlusPlus.Full.ax_induction_prim,ROBINSON_PlusPlus.Minimal.Axioms.ax_axiomsCodeT_eq
ROBINSON_PlusPlus.Meta.LineWFCases.derives_lineWF_neg_thy_of_not_mem|propext,Classical.choice,Quot.sound,FOL.MetaRules.ex_elim,FOL.MetaRules.imp_intro,FOL.MetaRules.or_elim,FOL.MetaRules.raa,ROBINSON_PlusPlus.Full.ax_induction_prim,ROBINSON_PlusPlus.Full.ax_list_induction,ROBINSON_PlusPlus.Minimal.Axioms.ax_axiomsCodeT_eq
ROBINSON_PlusPlus.Meta.ChainNegPrf.decodeLine_none_cases|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.ChainNegPrf.derives_lineWF_neg_thy_of_decode|propext,Classical.choice,Quot.sound,FOL.MetaRules.ex_elim,FOL.MetaRules.imp_intro,FOL.MetaRules.or_elim,FOL.MetaRules.raa,ROBINSON_PlusPlus.Full.ax_induction_prim,ROBINSON_PlusPlus.Full.ax_list_induction,ROBINSON_PlusPlus.Minimal.Axioms.ax_axiomsCodeT_eq
ROBINSON_PlusPlus.Meta.ChainNegPrf.derives_neg_lor|propext,Classical.choice,Quot.sound,FOL.MetaRules.or_elim,FOL.MetaRules.raa
ROBINSON_PlusPlus.Meta.ChainNegPrf.derives_not_boundedCarcLt_congr|propext,Classical.choice,Quot.sound
ROBINSON_PlusPlus.Meta.ChainNegPrf.derives_not_boundedCarcLt_of_not_mem|propext,Classical.choice,Quot.sound,FOL.MetaRules.ex_elim,FOL.MetaRules.imp_intro,FOL.MetaRules.or_elim,FOL.MetaRules.raa,ROBINSON_PlusPlus.Full.ax_induction_prim,ROBINSON_PlusPlus.Full.ax_list_induction
ROBINSON_PlusPlus.Meta.ChainNegPrf.derives_not_boundedPremsIn_of_index|propext,Classical.choice,Quot.sound,FOL.MetaRules.raa
ROBINSON_PlusPlus.Meta.ChainNegPrf.derives_chainOk_neg_of_prem|propext,Classical.choice,Quot.sound,FOL.MetaRules.imp_intro,FOL.MetaRules.or_elim,FOL.MetaRules.raa,ROBINSON_PlusPlus.Full.ax_induction_prim,ROBINSON_PlusPlus.Full.ax_list_induction
ROBINSON_PlusPlus.Meta.ChainNegPrf.derives_not_boundedPremsIn_congr|propext,Classical.choice,Quot.sound
ROBINSON_PlusPlus.Meta.ChainNegPrf.derives_chainOk_neg_of_prem_line|propext,Classical.choice,Quot.sound,FOL.MetaRules.imp_intro,FOL.MetaRules.or_elim,FOL.MetaRules.raa,ROBINSON_PlusPlus.Full.ax_induction_prim,ROBINSON_PlusPlus.Full.ax_list_induction
ROBINSON_PlusPlus.Meta.ChainNegPrf.dispatcher|propext,Classical.choice,Quot.sound
ROBINSON_PlusPlus.Meta.ChainNegPrf.prf_lenc_thy|propext,Classical.choice,Quot.sound
ROBINSON_PlusPlus.Meta.ChainNegPrf.prf_lenc_listInd|propext,Classical.choice,Quot.sound
ROBINSON_PlusPlus.Meta.ChainNegPrf.derives_lineWF_neg_of_arity|propext,Classical.choice,Quot.sound,FOL.MetaRules.ex_elim,FOL.MetaRules.imp_intro,FOL.MetaRules.raa,ROBINSON_PlusPlus.Full.ax_induction_prim,ROBINSON_PlusPlus.Full.ax_list_induction
ROBINSON_PlusPlus.Meta.ChainNegPrf.derives_lineWF_neg_of_concl|propext,Classical.choice,Quot.sound,FOL.MetaRules.ex_elim,FOL.MetaRules.imp_intro,FOL.MetaRules.or_elim,FOL.MetaRules.raa,ROBINSON_PlusPlus.Full.ax_induction_prim,ROBINSON_PlusPlus.Full.ax_list_induction
ROBINSON_PlusPlus.Meta.ChainNegPrf.tc_p1|propext,Classical.choice,Quot.sound
ROBINSON_PlusPlus.Meta.ChainNegPrf.tc_ind|propext,Classical.choice,Quot.sound
ROBINSON_PlusPlus.Meta.ChainNegPrf.tc_listInd|propext,Classical.choice,Quot.sound
ROBINSON_PlusPlus.Meta.ChainNegPrf.tc_qconf|propext,Classical.choice,Quot.sound
ROBINSON_PlusPlus.Meta.ChainNegPrf.prf_premsOf_mp_line|propext,Classical.choice,Quot.sound
ROBINSON_PlusPlus.Meta.ChainNegPrf.derives_chainOk_neg_of_prem_code|propext,Classical.choice,Quot.sound,FOL.MetaRules.ex_elim,FOL.MetaRules.imp_intro,FOL.MetaRules.or_elim,FOL.MetaRules.raa,ROBINSON_PlusPlus.Full.ax_induction_prim,ROBINSON_PlusPlus.Full.ax_list_induction
ROBINSON_PlusPlus.Meta.ChainNegPrf.derives_chainOk_neg_mp_major|propext,Classical.choice,Quot.sound,FOL.MetaRules.ex_elim,FOL.MetaRules.imp_intro,FOL.MetaRules.or_elim,FOL.MetaRules.raa,ROBINSON_PlusPlus.Full.ax_induction_prim,ROBINSON_PlusPlus.Full.ax_list_induction
ROBINSON_PlusPlus.Meta.ChainNegPrf.derives_chainOk_neg_gen|propext,Classical.choice,Quot.sound,FOL.MetaRules.ex_elim,FOL.MetaRules.imp_intro,FOL.MetaRules.or_elim,FOL.MetaRules.raa,ROBINSON_PlusPlus.Full.ax_induction_prim,ROBINSON_PlusPlus.Full.ax_list_induction
ROBINSON_PlusPlus.Meta.CodeDistinct.formCode_ne_termCode|propext,Classical.choice,Quot.sound,FOL.MetaRules.ex_elim,FOL.MetaRules.imp_intro,FOL.MetaRules.or_elim,FOL.MetaRules.raa,ROBINSON_PlusPlus.Full.ax_induction_prim
ROBINSON_PlusPlus.Meta.CodeDistinct.formCode_ne_cons_of_tag|propext,Classical.choice,Quot.sound,FOL.MetaRules.ex_elim,FOL.MetaRules.imp_intro,FOL.MetaRules.or_elim,FOL.MetaRules.raa,ROBINSON_PlusPlus.Full.ax_induction_prim
ROBINSON_PlusPlus.Meta.CodeDistinct.formCode_ne_implc_tc_1|propext,Classical.choice,Quot.sound,FOL.MetaRules.ex_elim,FOL.MetaRules.imp_intro,FOL.MetaRules.or_elim,FOL.MetaRules.raa,ROBINSON_PlusPlus.Full.ax_induction_prim
ROBINSON_PlusPlus.Meta.CodeDistinct.formCode_ne_eqc_fc_1|propext,Classical.choice,Quot.sound,FOL.MetaRules.ex_elim,FOL.MetaRules.imp_intro,FOL.MetaRules.or_elim,FOL.MetaRules.raa,ROBINSON_PlusPlus.Full.ax_induction_prim
ROBINSON_PlusPlus.Meta.ChainNegPrf.derives_lineWF_neg_p1_badtype|propext,Classical.choice,Quot.sound,FOL.MetaRules.ex_elim,FOL.MetaRules.imp_intro,FOL.MetaRules.or_elim,FOL.MetaRules.raa,ROBINSON_PlusPlus.Full.ax_induction_prim,ROBINSON_PlusPlus.Full.ax_list_induction
ROBINSON_PlusPlus.Meta.ChainNegPrf.derives_lineWF_neg_eqrefl_badtype|propext,Classical.choice,Quot.sound,FOL.MetaRules.ex_elim,FOL.MetaRules.imp_intro,FOL.MetaRules.or_elim,FOL.MetaRules.raa,ROBINSON_PlusPlus.Full.ax_induction_prim,ROBINSON_PlusPlus.Full.ax_list_induction
ROBINSON_PlusPlus.Meta.ChainNegPrf.stdArgs_peel|propext,Classical.choice,Quot.sound
ROBINSON_PlusPlus.Meta.ChainNegPrf.stdArgList_cons|propext,Classical.choice,Quot.sound
ROBINSON_PlusPlus.Meta.ChainNegPrf.tag0_none_dichotomy|propext,Classical.choice,Quot.sound
ROBINSON_PlusPlus.Meta.ChainNegPrf.rama_tag_grande|propext,Classical.choice,Quot.sound,FOL.MetaRules.imp_intro,FOL.MetaRules.raa,ROBINSON_PlusPlus.Full.ax_induction_prim,ROBINSON_PlusPlus.Full.ax_list_induction
ROBINSON_PlusPlus.Meta.ChainNegPrf.rama_concl|propext,Classical.choice,Quot.sound,FOL.MetaRules.imp_intro,FOL.MetaRules.raa,ROBINSON_PlusPlus.Full.ax_induction_prim,ROBINSON_PlusPlus.Full.ax_list_induction,FOL.MetaRules.ex_elim,FOL.MetaRules.or_elim
ROBINSON_PlusPlus.Meta.ChainNegPrf.rama_aridad|propext,Classical.choice,Quot.sound,FOL.MetaRules.imp_intro,FOL.MetaRules.raa,ROBINSON_PlusPlus.Full.ax_induction_prim,ROBINSON_PlusPlus.Full.ax_list_induction,FOL.MetaRules.ex_elim
ROBINSON_PlusPlus.Meta.ChainNegPrf.rama_tipo_p1|propext,Classical.choice,Quot.sound,FOL.MetaRules.imp_intro,FOL.MetaRules.raa,ROBINSON_PlusPlus.Full.ax_induction_prim,ROBINSON_PlusPlus.Full.ax_list_induction,FOL.MetaRules.ex_elim,FOL.MetaRules.or_elim
ROBINSON_PlusPlus.Meta.ChainNegPrf.dico_FF|propext,Classical.choice,Quot.sound
ROBINSON_PlusPlus.Meta.ChainNegPrf.dico_FT|propext,Classical.choice,Quot.sound
ROBINSON_PlusPlus.Meta.ChainNegPrf.dico_FFF|propext,Classical.choice,Quot.sound
ROBINSON_PlusPlus.Meta.ChainNegPrf.dico_FTT|propext,Classical.choice,Quot.sound
ROBINSON_PlusPlus.Meta.ChainNegPrf.decodes_leibniz|propext,Classical.choice,Quot.sound
ROBINSON_PlusPlus.Meta.ChainNegPrf.deuda_inNeg|Classical.choice,FOL.MetaRules.ex_elim,FOL.MetaRules.imp_intro,FOL.MetaRules.or_elim,FOL.MetaRules.raa,Quot.sound,ROBINSON_PlusPlus.Full.ax_induction_prim,ROBINSON_PlusPlus.Full.ax_list_induction,propext
ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_isTermCodeE1_of_In|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.D3BodyPrf.hA_lineWFDotAt|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.D3BodyPrf.pcc_bnd_bridge_at|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.D3ChainDotPrf.DEUDA_chainOkBDot_of|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.D3ChainDotPrf.PrfH_chainOkB_bnd_bridge|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.D3ChainDotPrf.chainOkBPsiDot_eq|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.D3ChainDotPrf.d3_prf_of|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.D3ChainDotPrf.d3_prf_of_body|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.D3ChainDotPrf.d3_prf_of_body_only|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.D3ChainDotPrf.d3_prf_of_chainOkBDot|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.D3ChainDotPrf.d3_prf_of_halves|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.D3ChainDotPrf.d3_prf_of_hbody|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.D3ChainDotPrf.d3_prf_of_two|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.D3ChainDotPrf.hC_dot_of_chainOkBDot|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.D3ChainDotPrf.hPinv_chainOkBPsi|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.D3ChainDotPrf.hPsiId_chainOkBPsiDot|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.D3ChainDotPrf.hwP_chainOkBPsi|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.D3ChainDotPrf.hwPsi_chainOkBPsiDot|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.D3ChainDotPrf.pcc_bdCarcLt_reflect|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.D3ChainDotPrf.pcc_chainOkBDot_imp_chainOkDot|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.D3ChainDotPrf.pcc_premsBody_reflect|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.D3ChainDotPrf.substfc_chainOkBPsiDot|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.Delta0ReflectPrf.pcc_lt_tracked|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.DotConsPrf.pcc_dot_cons|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftcPrf.CRIT_hasWit_descenso|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftcPrf.CRIT_targetLift_real|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftcPrf.CRIT_targetLiftsc_real|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO_at_hasWit|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO_at_imp|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO_at_lista_imp|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO_hasWit|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO_imp|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO_lista|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO_lista_imp|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftcPrf.PHI_all|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftcPrf.PHI_step|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftcPrf.PHIat_all|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftcPrf.PHIat_step|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftcPrf.iz_inv_es_prf_substtc_termCode_nil|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftcPrf.pcc_eval_liftc|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftcPrf.pcc_eval_liftc_at|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftcPrf.pcc_eval_liftsc_at|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftcPrf.targetLift_es_el_del_sondeo|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftcPrf.targetLiftsc_es_el_del_sondeo|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.PHIliftfc_step|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.casoAtomL_thm|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.casoBinL5|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.casoBotL|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.casoEqL_thm|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.casoUnL6|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.casoUnL9|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.deuda_of_isFC1|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.hasWitF_liftfc_of_deuda|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.liftfcT_termCode|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.pcc_eval_liftfc|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.pcc_eval_liftfc_modulo_2|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.pcc_eval_liftfc_modulo_8|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.pcc_eval_liftfc_wit|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.pcc_liftfc_atom_code|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.pcc_liftfc_bottom_code|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.pcc_liftfc_eq_code|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.pcc_liftfc_ex_code|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.pcc_liftfc_forall_code|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.pcc_liftfc_impl_code|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalNthcPrf.pcc_nthc_zero_code|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalSubstfcPrf.DESCENSO_substfc|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalSubstfcPrf.pcc_congr_substfcT_arg2_code|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalSubstfcPrf.pcc_eval_substfc|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalSubstfcPrf.pcc_eval_substfc_wit|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalSubstfcPrf.pcc_substfc_un_dot|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalSubsttcPrf.PHIsubsttc_step|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalSubsttcPrf.pcc_eval_substtc|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalSubsttcPrf.pcc_eval_substtc_hasWit|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalSubsttcPrf.pcc_eval_substtsc|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalSubsttcPrf.pcc_substtc_func_code|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalSubsttcPrf.pcc_substtc_var_lt_code|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.EvalSubsttcPrf.prf_pred_dot_guarded|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.GodelTwo.d3|Classical.choice,FOL.MetaRules.imp_intro,Quot.sound,ROBINSON_PlusPlus.Full.ax_induction_prim,ROBINSON_PlusPlus.Full.ax_list_induction,propext
ROBINSON_PlusPlus.Meta.GodelTwoPrf.prf_godelCN_fixedpoint|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.HasWitFTrackedPrf.hGuard_of_slots|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.HasWitFTrackedPrf.pcc_hGuardF|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.HasWitFTrackedPrf.pcc_hasWitF_exc|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.HasWitFTrackedPrf.pcc_isFC1_trackedC|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.HasWitFTrackedPrf.pcc_isFormCodeE2_trackedC|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.HasWitFTrackedPrf.pcc_shapeNul_fc|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.HasWitFTrackedPrf.pcc_wfAllF_trackedC|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.HasWitTcFnPrf.prf_argsIn_mono|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.HasWitTcFnPrf.prf_hasWit_tcFn|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.HasWitTcFnPrf.prf_wfAll1_cons|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.HasWitTrackedPrf.hGuard_of_deudaF|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.HasWitTrackedPrf.pcc_argsIn_pair_tracked|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.HasWitTrackedPrf.pcc_hGuardT|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.HasWitTrackedPrf.pcc_hasWit_exc|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.HasWitTrackedPrf.pcc_isTC1_tracked_of|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.HasWitTrackedPrf.pcc_isTermCodeE1_tracked|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.HasWitTrackedPrf.pcc_wfAll1_trackedC|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.PrfH_congr_targetLift|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_liftc0_func_code|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_liftc0_var_code|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_liftc_func_code|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_liftc_var_ge_code|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_liftc_var_lt_code|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_liftsc0_cons_code|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_liftsc0_nil_code|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_liftsc_cons_code|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_liftsc_nil_code|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.pcc_zero_lt_succ_code|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_liftc_varc_cases|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.prf_substfc_atom2CodeFn|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_caso_funcc|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_caso_funcc_at|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_caso_funcc_imp|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_caso_varc|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_caso_varc_lift_at|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_isTermCodeE1_imp|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_lista_cons|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_lista_cons_at|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_lista_cons_imp|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_lista_cons_imp_at|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_lista_nil|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_lista_nil_at|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_shapeBin_imp|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_shapeBin_imp_at|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_shapeUn_imp|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_shapeUn_imp_at|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_termCode|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_termCode_at|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_termsCode|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.substF_targetLift_hole|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftcCodePrf.substTerm_termCode|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftfcWitnessPrf.deuda_hasWitF_liftfc|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftfcWitnessPrf.prf_hasWitArgs_liftsc_of|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftfcWitnessPrf.prf_hasWitF_liftfc|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.LiftfcWitnessPrf.prf_hasWit_liftc_at|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.LineWFGuardPrf.hGuard_of_deudas|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.LineWFGuardPrf.hcond_absorbe_cascade|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.LineWFGuardPrf.hcond_absorbe_extra|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.ListEtaPrf.prf_eta_lenc|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.ListEtaPrf.prf_nthc1_carc_cdrc|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.OmegaStrength.derives_completo|Classical.choice,FOL.MetaRules.raa,Quot.sound,propext
ROBINSON_PlusPlus.Meta.PremsBdAllPrf.d3_prf_real|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.PremsBdAllPrf.hB_premsDotAt|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.PremsBdAllPrf.hPsiId_premsPsi|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.PremsBdAllPrf.hbdAllPrems_of_body|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.PremsBdAllPrf.hbdAllPrems_unpacked|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.PremsBdAllPrf.hwPsi_premsPsi|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.PremsBdAllPrf.premsBody_deuda|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.PremsBdAllPrf.substfc_id_substCodeF2|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.PremsOfDotPrf.pcc_eval_premsOf|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.PremsOfDotPrf.pcc_premsOf_dot_mp|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.PremsOfDotPrf.pcc_rw_dot_consN|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.PremsOfTagPrf.prf_of_premsOf_branches|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.PremsOfTagPrf.prf_premsOf_mp|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.PremsOfTagPrf.prf_premsOf_of_tag|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.PremsOfTagPrf.prf_premsOf_thy|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.SubstTreeReflect.PrfH_tc_objAt|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.SubstTreeReflect.pcc_lineWF_tracked|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.SubstTreeReflect.pcc_lineWF_tracked_ind_imp|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.SubstTreeReflect.pcc_lineWF_tracked_leibniz_imp|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.SubstTreeReflect.pcc_lineWF_tracked_listInd_imp|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.SubstTreeReflect.pcc_lineWF_tracked_modulo_2|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.SubstTreeReflect.pcc_lineWF_tracked_modulo_other|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.SubstTreeReflect.pcc_lineWF_tracked_q1_imp|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.SubstTreeReflect.pcc_lineWF_tracked_q2_imp|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.SubstTreeReflect.pcc_lineWF_tracked_q3_imp|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.SubstTreeReflect.pcc_lineWF_tracked_qconf_imp|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.SubstTreeReflect.prf_condD_of_stree_eq|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.SubstTreeReflect.prf_substtc_code|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.SubstfcWitnessPrf.prf_hasWitF_bin|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.SubstfcWitnessPrf.prf_hasWitF_implc|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.SubstfcWitnessPrf.prf_hasWitF_substfc|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.SubstfcWitnessPrf.prf_hasWit_funcc2|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.SubstfcWitnessPrf.prf_hasWit_substtc|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.SubstfcWitnessPrf.prf_nil_or_cons|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.TrackedAtomsPrf.pcc_In_atom_tracked|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.TrackedAtomsPrf.pcc_boundedIn_tracked|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.TrackedAtomsPrf.pcc_child_tracked|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.TrackedAtomsPrf.pcc_shape_tracked|Classical.choice,Quot.sound,propext
ROBINSON_PlusPlus.Meta.VerifierSound.negVerifier_of_deudas|Classical.choice,FOL.MetaRules.imp_intro,Quot.sound,propext
ROBINSON_PlusPlus.Meta.VerifierSound.verifier_sound|Classical.choice,Quot.sound,propext
derives0_raa|-
EOF

TMP=$(mktemp -d)
LEANFILE="$TMP/Footprints.lean"
{
  echo "import ROBINSON_PlusPlus"
  echo "import FOL"
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
( lake build FOL TheoryFramework 2>&1; lake build 2>&1 ) \
  | tr '\n' ' ' | tr -s ' ' \
  | grep -oE "'[^']+' (depends on axioms|does not depend)" \
  | sed -E "s/^'([^']*)'.*/\1/" | sort -u > "$COBTMP"
COB_IMPRESOS=$(wc -l < "$COBTMP" | tr -d ' ')
COBDECL=$(mktemp)
printf '%s' "$TABLA" | sed -E 's/\|.*//' | sed '/^$/d' | sort -u > "$COBDECL"
COB_FALTAN=$(comm -23 "$COBTMP" "$COBDECL")
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
  echo "  ✓ los $COB_IMPRESOS titulares que el árbol imprime están TODOS declarados"
else
  echo "  ❌ $COB_N titular(es) impreso(s) por el árbol y SIN declarar en la tabla:"
  printf '%s\n' "$COB_FALTAN" | sed '/^$/d' | head -20 | sed 's/^/      /'
  [ "$COB_N" -gt 20 ] && echo "      … y $((COB_N - 20)) más"
  echo "      🔑 Un titular que no se declara no lo vigila nadie. Añádelos a TABLA."
  FAIL=1
fi
rm -f "$COBTMP" "$COBDECL"

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
