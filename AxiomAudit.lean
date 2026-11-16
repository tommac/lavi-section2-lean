import LaviSection2

/-! Run `lake env lean AxiomAudit.lean`.  Each theorem below should report only
`[propext, Classical.choice, Quot.sound]`. -/

open LaviSection2

-- Lemma 2.1
#print axioms lavi_lemma_2_1
#print axioms faceMinimizer_cofactor_eq
#print axioms faceMinimizer_support_eq_of_nearlyDecomposable
-- Lemma 2.2
#print axioms permanent_contractMatrix
#print axioms faceMinimizer_contraction
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
#print axioms ShoreCut.lavi_eq_4_1
#print axioms ShoreCut.lavi_lemma_4_1
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
#print axioms rowFactor_secant
#print axioms colFactor_secant
#print axioms lavi_lemma_5_1
#print axioms lavi_corollary_5_2
#print axioms lavi_corollary_5_2_col
-- Section 6: leaves
#print axioms lavi_lemma_6_1
#print axioms lavi_lemma_6_2
#print axioms ShoreCut.lavi_eq_6_1
#print axioms ShoreCut.lavi_eq_6_1'
#print axioms ShoreCut.lavi_lemma_6_3
#print axioms ShoreCut.lavi_lemma_6_3'
#print axioms ShoreCut.lavi_eq_6_5
#print axioms ShoreCut.lavi_eq_6_5'
-- Section 7: the induction and Theorem 1.1 (conditional on `GurvitsCapacityInequality`)
#print axioms lavi_eq_7_2
#print axioms lavi_lemma_2_5_univ
#print axioms terminal_branch_strict
#print axioms foreggerSharpAt_of_terminal_strict
#print axioms foreggerSharpAt_of_gurvits
#print axioms lavi_theorem_1_1
#print axioms lavi_theorem_1_1_moreover
#print axioms lavi_theorem_1_1_attained
