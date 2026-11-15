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
