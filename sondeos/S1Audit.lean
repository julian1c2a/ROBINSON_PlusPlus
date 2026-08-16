/-
SONDEO S1 — auditoría mecánica. `ax_tc_cons` está FUERA de `axioms`, y `prf_tc_cons`/`tc_cons`
son AXIOMAS DE LEAN. Por tanto `#print axioms` delata EXACTAMENTE quién depende de la lectura
sintáctica de `tcFn`: aparece `prf_tc_cons` (o `tc_cons`) en su footprint.

Footprint sano esperado: [propext, Classical.choice, Quot.sound] (+ meta-reglas ω donde toque).
NO ES MÓDULO DE PRODUCCIÓN. NO MERGEAR.
-/
import ROBINSON_PlusPlus.Meta

/-! ## Los RESULTADOS CABECERA -/

#print axioms ROBINSON_PlusPlus.Meta.DiagonalTwo.goedel_first_real'
#print axioms ROBINSON_PlusPlus.Meta.DiagonalTwo.goedel_first_unprovable_real'
#print axioms ROBINSON_PlusPlus.Meta.DiagonalTwo.goedel_first_unrefutable_real'
#print axioms ROBINSON_PlusPlus.Meta.DiagonalTwo.goedel_first_undecidable_real'
#print axioms ROBINSON_PlusPlus.Meta.GodelTwo.goedel_second'
#print axioms ROBINSON_PlusPlus.Meta.Diagonal.goedel_first_real

/-! ## D1 / D2 / representabilidad -/

#print axioms ROBINSON_PlusPlus.Meta.Representability2Prf.repr_pos'_prf

/-! ## La capa RASTREADA (donde se supone que está el daño) -/

#print axioms ROBINSON_PlusPlus.Meta.LineWFAssemblePrf.pcc_lineWF_tracked_modulo_7
#print axioms ROBINSON_PlusPlus.Meta.D3InDotPrf.hI_dot
#print axioms ROBINSON_PlusPlus.Meta.D3InDotPrf.d3_prf_of_chainOkDot
#print axioms ROBINSON_PlusPlus.Meta.D3DottedPrf.d3_prf_of_dotted_atoms

/-! ## Los 14 tags cerrados (muestra) -/

#print axioms ROBINSON_PlusPlus.Meta.LineWFMpPrf.pcc_lineWF_tracked_mp_imp
#print axioms ROBINSON_PlusPlus.Meta.LineWFEfqPrf.pcc_lineWF_tracked_efq_imp
#print axioms ROBINSON_PlusPlus.Meta.LineWFPropPrf.pcc_lineWF_tracked_p1_imp
#print axioms ROBINSON_PlusPlus.Meta.LineWFThyPrf.pcc_lineWF_tracked_thy_imp

/-! ## Los sitios PUENTE identificados en la fase 2 -/

#print axioms ROBINSON_PlusPlus.Meta.TcArithPrf.prf_tc_form
#print axioms ROBINSON_PlusPlus.Meta.InAxiomsCodePrf.prf_tc_listFormCodeM
#print axioms ROBINSON_PlusPlus.Meta.Sigma1CorePrf.prf_tc_objList
