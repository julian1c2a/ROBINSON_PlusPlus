# Inventario de NegNum

**Last updated:** 2026-10-16 — registro (ADR‑146): el informe final de un agente de sólo lectura, CONDENSADO (las
citas, los enunciados y las referencias fichero:línea, tal cual). Lo que dice del árbol es de esa fecha (HEAD
`24e3b55`); no se actualiza.

Read-only; nothing compiled; `#pureza` was not run by the agent (the purity column of `pureza.txt` is the measured
one). [R] = read in the source; [I] = inference. `AX` = `ROBINSON_PlusPlus/Minimal/Axioms.lean`; `M/` =
`ROBINSON_PlusPlus/Meta/`; `S/` = `sondeos/`.

## 0. Corrections to the premises [R]

* `M/ChainNegPrf.lean`: 1 617 lines, 899 non-blank after `strip-lean.awk`, 109 declarations, 30 `theorem prf_*`; in
  the build, outside the cone.
* The audit's CodeWitnessPrf line numbers predate `4498df3`: `prf_bdAll_numeral` :870, `prf_crit_In_rejects_open1`
  :1150, `crit_isTC1_junk_refuted_open` :1174, `CRIT_isFC1_rejects_varc` :1605.
* `M/ArithPrf.lean:181-475` holds no numeral-decision lemmas: it is substitution and lift on CANONICAL codes. The
  numeral lemmas of that file are at :84-132.
* `M/ModeloCodigo.lean:530` cites «Axioms.lean:1197-1278» for the guards; the real lines are AX:1225-1306.

## 1. The guards [R]

| Name | Loc | Definition |
|---|---|---|
| `hasWit c` | AX:1259 | `∃w. isTC1 w c`, `isTC1 w c := wfAll1 w ∧ In c w` (AX:1256) |
| `wfAll1 w` | AX:1254 | `∀i. i < lenc w ⇒ isTermCodeE1 w (nthc w i)` |
| `isTermCodeE1 wT X` | AX:1246 | `shapeUn X 0 ∨ (shapeBin X 1 ∧ argsIn wT (nthc X 2̄))` |
| `argsIn wT Y` | AX:1243 | `∀i. i < lenc Y ⇒ In (nthc Y i) wT` |
| `hasWitF c` | AX:1305 | `∃wF ∃wT. isFC1 wF wT c`, `isFC1 := (wfAll1 wT ∧ wfAllF wF wT) ∧ In c wF` (AX:1301) |
| `wfAllF` / `isFormCodeE2` | AX:1297 / 1283 | `∀i < lenc wF`: one of 8 clauses `clBot/clAtom/clEq/clBin 5,7,8/clUn 6,9` (AX:1267-1281) |

* They are DEFINITIONS (not atoms nor axioms, AX:1222-1223); they appear only inside 7 `ax_lineWF_*` biconditionals.
* Logical form: Σ₁ (one unbounded ∃, two for `hasWitF`, before a Δ₀ body with bounded ∀). So `¬hasWit`, `¬hasWitF`
  are Π₁.
* Positive instances only: `CRIT_hasWit_real` (M/CodeWitnessPrf.lean:1426), `prf_hasWitF_real` (:2150),
  `prf_hasWit_termCodeM` (M/SubstTreeReflect.lean:946).
* Nat mirrors (M/ModeloCodigo.lean:532-547): `shapeUnN`, `shapeBinN`, `argsInN`, `isTermCodeE1N`, `wfAll1N`,
  `hasWitN c := ∃w, wfAll1N w ∧ memN c w`, `cl*N`, `isFormCodeE2N`, `wfAllFN`, `hasWitFN`. No Nat-level recursive
  characterization of `hasWitN`/`hasWitFN` exists; the only links are the semantic `ev_hasWit`/`ev_hasWitF`.

## 2. `M/ChainNegPrf.lean` [R]

It was the machinery behind `NegVerifier` («negative Δ₀-completeness of the verifier» on STANDARD witnesses). The
closing pieces lived on `⊢` and were retired with ADR-115. Reusable for NegNum [I]: `prf_boundedPremsIn_of_chainOk`
(:223), `prf_lineTag_cons` (:354), `prf_lenc_tag_and` / `_plain` (:365/:379), the 21 `prf_lenc_<tag>` (:387-541,
`lineWF t ⇒ (nthc t 1 = k̄ ⇒ lenc t = n̄ₖ)`), `prf_premsOf_mp_line`/`_gen_line` (:906/:916, duplicates of ReprPrf),
`prf_lenc_two`/`_one`/`prf_nthc_two_1` (:925-934). Not reusable: `TagCode` and the 19 `tc_*` (canonical arguments),
the Term-decoder facts (`StdArgList`, `decodeRuleTag_*`…), the decoder-driven front-end (template only), the `dico_*`,
`decodes_*`, `badlen_*` dichotomies.

## 3. CodeWitnessPrf refuters [R] (outside the cone, model-free by reading, not exported)

`crit_num_ne` :176 — `∀ m n, m ≠ n → Prf (numeralM m = numeralM n ⇒ ⊥)`; `prf_crit_In_rejects_open1` :1150 —
`Prf (boundedIn c w ⇒ (wfAll1 w ⇒ ⊥))` for a closed c with `carc c = k̄`, k ∉ {0,1}, w possibly `#0`;
`crit_isTC1_junk_refuted_open` :1174; `CRIT_isFC1_rejects_varc` :1605; `CRIT_E2_rejects_varc` :1592,
`CRIT_E2_rejects_funcc` :1598; `crit_isFormCodeB2_rejects` :1286; `prf_isFormCodeE2_str` :1578;
`crit_isTermCodeE1_rejects` :323, `prf_isTermCodeE1_str` :316; `crit_tag_absurd`/`crit_cOk2_absurd`/`crit_cOk3_absurd`
:186/192/198; in the cone `prf_shapeUn/Bin/Nul_str` :288/294/1565. `prf_bdAll_numeral` :870 (cone),
`prf_bdAll_of_bound` :900. Hereditary-step tools (cone): `prf_isTermCodeE1_of_In` :706, `prf_isFormCodeE2_of_In`
:1529, `PrfH_inst_argsIn` :600, `PrfH_inst_wfAll1` :606, `prf_argsIn_head/tail` :621/633.

## 4. Numeral-decision lemmas [R]

M/ArithPrf.lean: `prf_pred_numeral` :84, `prf_numeral_add` :99, `prf_numeral_lt` :111, `prf_gnum_lt` :130. Elsewhere:
`prf_succ_ne_zero` (M/NatArithPrf.lean:162), `prf_succ_inj` :169, `prf_not_lt_zero` :176, `prf_zero_lt_succ` :128,
`prf_succ_lt_succ_of_lt` :145, `prf_lt_irrefl` (M/NatMulPrf.lean:288), `prf_lt_trichotomy` :295, `prf_lt_numeralM`
(M/LineWFTrackedPrf.lean:554), `prf_gnum_add` (M/CodeNumeralPrf.lean:75), `prf_gnum_mul`/`prf_numeral_mul`
(M/Div2ParityPrf.lean:104/82), `prf_div2_numeral` :262, `prf_cons_def` (M/CantorMonoPrf.lean:54),
`prf_cantor_mono_left/right` :325/330, `crit_num_ne`. Absent: `Prf ¬(ā < b̄)` for a ≥ b, `le` lemmas on numerals, a
general evaluator for closed terms.

## 5. The sondeos (both CI controls) [R]

`S/RosserBasura.lean` (217 lines, 14 theorems): `prf_zero_ne_cons` :73, `prf_isTermCodeE1_zero_absurd` :79,
`prf_neg_hasWit_zero` :84, `prf_neg_hasWit_tag` :95, `prf_congr_carc` :107, `prf_carc_numeral` :114,
`prf_neg_hasWit_num` :121, `prf_cons_evalM` :136, `prf_parte`/`prf_args`/`prf_lt_args`/`prf_nth0_args` :143-161,
`prf_neg_hasWit_prof2` :167 — all model-free; `control_codigo_no_refutable` :202 uses `prf_sound`.
`S/RosserReflexion.lean` (189 lines, 18 theorems): §1 `ev_*` and `ev_provFromCode` semantic; `prf_dec_of_prov` :119
uses `verificador_solido`; `prf_eval_substfc_num` :128 and `prf_eval_liftfc_num` :143 use `prf_sound`; pure Nat:
`decT_tcFnN` :104, `dec_valor_substfc` :174, `dec_valor_liftfc` :182. Archived non-compiling precedents in tag
`archivo/sondeos-2026-10`: `CRIT_hasWit_rejects` (`MedirC_Deriva.lean:296`), `CRIT_hasWitF_rejects_eqvarc` (:193),
`CRIT_hasWit_rejects_tag`/`CRIT_hasWitF_rejects_tag` (`HasWitFCritica.lean:2101/2111`), `CRIT_hasWitF_rejects_varc`
(`MedirC_Carga.lean:394`).

## 6. Refuters for In / lineWF / chainOk / thy, and the guard projections [R]

* In: `prf_not_in_nil` (M/ChainPrf.lean:367), `prf_in_cons_iff` :359, `prf_in_cons_nil_iff`
  (M/ChainOkBoundedPrf.lean:52), `prf_in_concat_iff` :43, `prf_in_concat_singleton_iff` :68, `prf_boundedIn_nil`
  (M/BoundedInPrf.lean:236), `prf_In_iff_boundedIn` :379. None composes into «numeral ∉ numeral list»; the ⊢-era
  template `prf_not_In_listFormCodeM` / `neg_In_axiomsCodeT_of_not_mem` survives only in tag `pre-adr115`
  (`Meta/AxiomListCode.lean:45-95`).
* lineWF: `prf_lineWF_inv` (M/Sigma1AtomPrf.lean:369), `prf_of_tagDisj` (M/LineWFAssemblePrf.lean:55),
  `pcc_tag_vacuous` (M/SubstTreeReflect.lean:1159), `prf_tag_absurd` :1119, `prf_tagDisj_absurd` :1142,
  `prf_lineWF_cons` (M/LineWFConsPrf.lean:34), `prf_lenc_of_tag` (M/PremsOfTagPrf.lean:66), `prf_lineWF_tag_imp`
  (M/LineWFCases.lean:115, out), `prf_lineWF_neg_of_tag` :224 (out) — `Prf ¬lineWF (cons concl (cons k̄ (objList
  args)))` for the 19 structural tags; the per-tag biconditionals: M/ReprPrf.lean:469-1099.
* thy: `prf_lineWF_thy` (M/ReprPrf.lean:515) — `lineWF ⟨c,15⟩ ⇔ In c axiomsCodeT`; `prf_ancla`
  (M/Representability2Prf.lean:157); membership positive only: `prf_inAxC` :233, `prf_In_listFormCodeM_prf` :222.
* chainOk / runFn: `prf_chainOk_cons` (M/ReprPrf.lean:415), `prf_allIn_cons` :429, `prf_chainOk_iff_chainOkB`
  (M/ChainOkBoundedPrf.lean:832), `prf_lineWF_of_chainOk` (M/D3BodyPrf.lean:80), `prf_In_runFn_iff`
  (M/RunFnBoundedPrf.lean:279, out), `prf_runFn_nil_objList` (M/Sigma1CorePrf.lean:202, out), `prf_chainOk_subst2`
  (M/ChainPrf.lean:470).
* Guard projections: 11 slots (verified by `rfl`, M/LineWFGuardPrf.lean:142-179); 3 exist, for explicit lines,
  outside the cone: `prf_lineWF_q1_hasWit` (M/ReprPrf.lean:1016), `prf_lineWF_q2_hasWit` :1029,
  `prf_lineWF_leibniz_hasWitF` :1042. Missing 8: q1/2 `hasWitF`, q2/2 `hasWitF`, q3/3 `hasWitF`, leibniz/3 `hasWit`,
  leibniz/4 `hasWit`, ind/2 `hasWitF`, qconf/2 `hasWitF`, listInd/2 `hasWitF`.

## 7. Astronomical numerals, ∀-n families, decomposition [R]

Rules: `nD` folded, nothing may evaluate `axioms` (AX:1105-1109); structural `rw`, `simp only` makes the kernel unfold
the numeral (AX:1137-1140); codes closed under `liftTerm` by induction, never by `rfl` (AX:682-688); `V₀` moved only by
`rw` with ∀-lemmas; no `rfl` against `V₀`; `#eval`/`#reduce`/`#guard` banned on `axioms`, `codeNatList`, `V₀`,
`godelCN` (check-sorry.bash:317-333); [I] `decodeL`/`unpairN` recurse in unary, so `decodeL` of a concrete code can
never be evaluated. ∀-n lemmas: `liftTerm_numeralM` AX:692, `substTerm_numeralM` AX:755; bridges `numeralM_eq`,
`numeral_bridge`, `num_bridge`; Prf equalities `prf_cons_eval`, `prf_cons_eval_of`, `prf_formCode_numeral`,
`prf_termCode_numeral`, `prf_termCodeM_numeral`, `prf_tc_numeral` (M/TcArithPrf.lean:57), `prf_objList_numeral`
(M/Sigma1CorePrf.lean:232, out); list accessors `prf_lenc_objList`/`prf_nthc_objList` (M/CodeWitnessPrf.lean:1046/
1052). Nat side: `consN_car_cdr`, `encodeL_decodeL`, `decodeL_consN`, `carN/cdrN/nthN/lenN` lemmas, `chainOkN_consN`,
`memN_consN`, `memN_concatN`, `consN_inj`/`consN_ne_zero`/`codeNat_inj`. Decomposition: no lemma `numeralM m = cons
(numeralM (carN m)) (numeralM (cdrN m))` in the build; only sondeo special cases.

## MISSING for NegNum

**A. Numeral decomposition / evaluation.** (1) `m≠0 → Prf (numeralM m = cons (carN m)‾ (cdrN m)‾)`, and `numeralM m =
objList ((decodeL m).map numeralM)` (also the missing `objListN = encodeL`). (2) `carc`/`cdrc`/`lenc`/`nthc` of
`numeralM m` equal to numerals (`carc`/`nthc` are unconstrained on `nil`, AX:829-830). (3) Constructor codes on
numerals: `implc ā b̄ = (implcN a b)‾`, and `botc/eqc/forallc/andc/orc/exc/varc/funcc/atomc`. (4) `¬memN y l → Prf ¬In
ȳ l̄`, also for the symbolic accumulator `concat c [carc x]`. (5) Nat lemmas: `memN y (runFnN 0 m) ↔ ∃ x ∈ decodeL m,
carN x = y`; accumulator membership as an ∃ over earlier lines. (6) Syntactic external evaluation of
`substtc/substtsc/liftc/liftsc/substfc/liftfc` on numerals under true Nat guards (an analog of ArithPrf:181-473 over
Nat codes), with the Nat closure of goodness and a pure `hasWitN (codeNatTerm t)` for TC0/TCS/TNIL/TCONS.

**B. Per-tag lineWF refutation (`¬lineWFN V x ⇒ Prf ¬lineWF x̄`).** x = 0; length ≤ 1; tag ≥ 21; wrong length; wrong
conclusion for the 12 propositional tags + gen (`prf_lineWF_neg_of_tag` + A1 + A3, and a Nat lemma matching `lineWFT
K` with `tagConcl K`); wrong conclusion for the 7 substitution tags with true guards (needs A6); guard false (the 8
missing projections).

**C. Guard refutation (GuardNeg; unavoidable — resultado.json:212-215 argues it, not compiled).** (1) Nat: witness
construction (var-shape ⇒ `hasWitN`; func with all arguments `hasWitN` ⇒ `hasWitN`), and the analog for `hasWitFN`,
so that `¬hasWitN` yields a bad descendant. (2) `∀c, ¬hasWitN c → Prf ¬hasWit c̄` (missing: tag 0/1 with the wrong
length, the hereditary case at any depth). (3) `∀c, ¬hasWitFN c → Prf ¬hasWitF c̄` (all missing: ∃∃-elimination on
numerals, the 8 clauses with wrong lengths, recursion through `wF`, term slots through C2 with an arbitrary `wT`, atom
argument lists).

**D. Premises / allIn (tags 16/17).** `premsOf` of numeral lines, then `¬allInN c (premsOfN x) ⇒ Prf ¬allIn` (via
`prf_allIn_cons` + A4) or the Δ₀ route (`prf_boundedPremsIn_of_chainOk` + `prf_bdAll_numeral`).

**E. thy refutation.** `¬memN c (codeNatList axioms) ⇒ ∀a∈axioms, c ≠ codeNat a` (the converse of
`memN_codeNatList`), then a structural recursion `Prf ¬In c̄ (listFormCodeM L)` (via `prf_formCode_numeral` +
`formCodeM_eq` + `crit_num_ne`), transported with `prf_ancla`. Never unfold `axioms` or `nD`.

**F. Chain level.** A Nat «first bad line» lemma for `chainOkL`, and the Prf assembly: stepping with
`prf_chainOk_cons`, or Δ₀ with `prf_chainOk_iff_chainOkB`/`prf_lineWF_of_chainOk`.

**G. The In part.** `prf_In_runFn_iff` (or stepping with `prf_runFn_cons`) + `prf_formCode_numeral` + A2 + A4; split on
`chainOkN` first: only valid chains (lines ≠ 0) have evaluable `carc`.

**H. Final assembly.** State NegNum with `V := codeNatList axioms` to avoid `V₀_eq_codigo` (`NegNumStmt`,
informe.md:183-185); `Pf` is `Verifies φ t` (M/OmegaReflect.lean:96, out); `neg (land A B)` from `neg A` or `neg B`
has no named helper; register the instance in `PUROS`. Naming trap: `prf_lenc_c1` exists both as a ChainNegPrf export
(tag 2) and as `SinWTs.prf_lenc_c1` (list of length 1).
