import LaviSection2

/-! Run `lake env lean AxiomAudit.lean`.  Each theorem below should report only
`[propext, Classical.choice, Quot.sound]`; `scripts/check_axioms.py` checks the output
(`lake env lean AxiomAudit.lean > axioms.txt; python3 scripts/check_axioms.py AxiomAudit.lean
axioms.txt`).  `#print axioms` reads the axiom lists recorded in the compiled files;
`scripts/kernel_check.sh` re-checks the final theorems with an independent kernel. -/

open LaviSection2

-- Lemma 2.1
#print axioms lavi_lemma_2_1
#print axioms faceMinimizer_cofactor_eq
#print axioms faceMinimizer_support_eq_of_nearlyDecomposable
-- Lemma 2.2
#print axioms permanent_contractMatrix
#print axioms faceMinimizer_contraction
#print axioms faceMinimizer_row_contraction_nd
-- Lemma 2.3
#print axioms nearlyDecomposable_no_fourCycle
#print axioms nearlyDecomposable_common_neighbor_unique
-- Lemma 2.4
#print axioms lavi_lemma_2_4_column
#print axioms lavi_lemma_2_4_row
-- Lemma 2.5
#print axioms lavi_lemma_2_5
#print axioms nearlyDecomposableOn_canonicalAdj
#print axioms privateContraction_canonical
#print axioms privateRowContraction_canonical
-- Cycle branch
#print axioms cycleSupported_foregger_sharp
-- Lemma 3.1
#print axioms lavi_lemma_3_1
#print axioms faceFunctional_le_log_permanent
-- Lemma 3.2 and the matrix bridge
#print axioms lavi_lemma_3_2
#print axioms coreFunctional_eq_faceFunctional
-- Equations (3.5)-(3.7)
#print axioms lavi_eq_3_5
#print axioms subdivCharge_nonneg
#print axioms lavi_eq_3_7
-- Section 4: tight cuts
#print axioms ShoreCut.sum_lmatch_eq_sum_pairs
#print axioms ShoreCut.lavi_eq_4_1
#print axioms ShoreCut.lavi_lemma_4_1
#print axioms ShoreCut.removable_internal₁
#print axioms ShoreCut.removable_internal₂
#print axioms ShoreCut.coreFI_cut_iff
#print axioms ShoreCut.lavi_eq_4_3
#print axioms ShoreCut.lavi_eq_4_4
#print axioms ShoreCut.lavi_eq_4_4'
#print axioms ShoreCut.lavi_eq_4_5
#print axioms ShoreCut.lavi_eq_4_5'
#print axioms tightCut_orientation
#print axioms exists_shoreCut_of_tight
-- Section 5: one-star bound (Gurvits's inequality is the hypothesis `hG`, not an axiom)
#print axioms permanent_expandedMatrix_eq_elim
#print axioms eq_expandedMatrix_liftFlow
#print axioms capacity_elim_ge
#print axioms sum_colCount_le
#print axioms rowFactor_secant
#print axioms colFactor_secant
#print axioms lavi_lemma_5_1
#print axioms lavi_corollary_5_2
#print axioms lavi_corollary_5_2_col
-- Section 6: leaves
#print axioms lavi_lemma_6_1
#print axioms ShoreCut.cutFree₁
#print axioms ShoreCut.cutFree₂
#print axioms ShoreCut.card_rowSet₁
#print axioms ShoreCut.card_colSet₁
#print axioms ShoreCut.card_rowSet₂
#print axioms ShoreCut.card_colSet₂
#print axioms lavi_lemma_6_2
#print axioms ShoreCut.lavi_eq_6_1
#print axioms ShoreCut.lavi_eq_6_1'
#print axioms ShoreCut.lavi_lemma_6_3
#print axioms ShoreCut.lavi_lemma_6_3'
#print axioms ShoreCut.lavi_eq_6_5
#print axioms ShoreCut.lavi_eq_6_5'
-- Section 7: the induction, and Theorem 1.1 with the hypothesis `hG`
#print axioms contraction_branch_column
#print axioms contraction_branch_row
#print axioms lavi_eq_7_2
#print axioms lavi_lemma_2_5_univ
#print axioms terminal_branch_strict
#print axioms isHalfCycle_of_half_entries
#print axioms half_entries_of_contractMatrix
#print axioms isHalfCycle_of_not_terminal
#print axioms foreggerSharpAt_of_terminal_strict
#print axioms foreggerSharpAt_of_gurvits
#print axioms lavi_theorem_1_1
#print axioms lavi_theorem_1_1_moreover
#print axioms lavi_theorem_1_1_attained
-- Gurvits's inequality, proved from the RealRooted library
#print axioms LaviGurvits.gurvitsFactor_mul_capacity_le_capacity_step_of_degreeOf
#print axioms LaviGurvits.prod_gurvitsFactor_min_mul_capacity_le_coeffIter
#print axioms gurvitsCapacityInequality
-- Theorem 1.1 without the hypothesis
#print axioms foreggerSharpAt_all
#print axioms lavi_theorem_1_1_unconditional
#print axioms lavi_theorem_1_1_moreover_unconditional
#print axioms foregger_conjecture
#print axioms foregger_bound
