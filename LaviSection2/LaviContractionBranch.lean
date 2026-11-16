import LaviSection2.Arithmetic
import LaviSection2.LaviFaceBasics
import LaviSection2.LaviTerminalStructure

/-!
# Lavi Section 7: the contraction branch and equation (7.1)

Branch 1 of the induction in Section 7 of Lavi's preprint (lines 764-769):
fix an ND support `D` of order `n ≥ 3` and a permanent minimizer `A` of the
face `Ω(D)`; its support is `D` by Lemma 2.1.  If some degree-two line of `D`
has an ND contraction, Lemma 2.2 and the induction hypothesis give

  `2 per A = per C(A) ≥ 2^(2-n)`,  so  `per A ≥ 2^(1-n)`.            (7.1)

The earlier modules provide the two halves separately, in different
coordinates:

* `contractMatrix A r s c : Square m` (`LaviContractionIdentity`), the matrix
  contraction, indexed through `Fin.succAbove`, with
  `faceMinimizer_contraction` giving double stochasticity and
  `per C(A) = 2 per A` at a face minimizer (Lemmas 2.1 and 2.2);
* `contractColumn D r s c : Drop s → Drop c → Prop` (`LaviContraction`), the
  support contraction on subtypes, which is what `Terminal` and Lemma 2.4
  speak about, with the generic predicate `NearlyDecomposableOn`.

This module supplies the bridge and assembles the branch:

* `support_contractMatrix_iff`: for a nonnegative matrix, the support of the
  contracted matrix is the contracted support, in the coordinates
  `finSuccAboveEquiv`; hence `nearlyDecomposable_support_contractMatrix`, so
  the induction hypothesis (a statement about matrices of order `m` with ND
  support) applies to `C(A)`.  `fullyIndecomposable_support_contractMatrix`
  is the remark of Section 2.2 that the support of `C(A)` is FI.
* The row case is reduced to the column case by transposing the matrix
  (`nearlyDecomposableOn_contractRow_iff`, `faceMinimizer_transpose`), as in
  the paper ("A degree-two row has the transposed contraction").
* `exists_nd_contraction_iff_not_terminal`: a support fails to be `Terminal`
  exactly when a degree-two column or a degree-two row has an ND contraction.
* `faceMinimizer_contraction_nd`, `faceMinimizer_row_contraction_nd`: the
  packaged data of an ND contraction at a face minimizer.
* `contraction_branch_column`, `contraction_branch_row`,
  `bound_of_not_terminal`: the bound (7.1).

Unlike the paper, no appeal to Minc's edge bound (line 766) is needed: the
case split is on `Terminal D` itself, and a support without any degree-two
line is `Terminal` by definition.

The branch is only meaningful in order at least three: `K_{2,2}` is
`Terminal` for the Lean predicates (`nearlyDecomposable_two_terminal`),
because its contractions are the order-one singleton, which the Lean
predicate `NearlyDecomposableOn` rejects.
-/

namespace LaviSection2

/-! ### Entries and support of the contracted matrix -/

/-- The merged row of the contracted matrix `C(A)`: the entries of rows `r` and `s` are
added in every surviving column (Section 2.2, lines 113-114). -/
theorem contractMatrix_merged {m : ℕ} (A : Square (m + 1)) {r s : Fin (m + 1)}
    (c : Fin (m + 1)) {i : Fin m} (hi : s.succAbove i = r) (j : Fin m) :
    contractMatrix A r s c i j = A r (c.succAbove j) + A s (c.succAbove j) := by
  simp [contractMatrix, hi]

/-- The other rows of the contracted matrix `C(A)` keep their entries (Section 2.2, lines
113-114). -/
theorem contractMatrix_unmerged {m : ℕ} (A : Square (m + 1)) {r s : Fin (m + 1)}
    (c : Fin (m + 1)) {i : Fin m} (hi : s.succAbove i ≠ r) (j : Fin m) :
    contractMatrix A r s c i j = A (s.succAbove i) (c.succAbove j) := by
  simp [contractMatrix, hi]

/-- The bridge between the two contractions, which the paper identifies tacitly (Section
2.2, lines 113-117): for a nonnegative matrix `A`, the support of the contracted matrix
`contractMatrix A r s c` is the contracted support `contractColumn (support A) r s c`, read
in the coordinates `finSuccAboveEquiv`.  Nonnegativity is what makes a sum of two entries
vanish only if both do. -/
theorem support_contractMatrix_iff {m : ℕ} {A : Square (m + 1)} (hA : Nonnegative A)
    (r s c : Fin (m + 1)) (i j : Fin m) :
    support (contractMatrix A r s c) i j ↔
      contractColumn (support A) r s c (finSuccAboveEquiv s i) (finSuccAboveEquiv c j) := by
  have h1 := hA r (c.succAbove j)
  have h2 := hA s (c.succAbove j)
  by_cases h : s.succAbove i = r
  · simp only [support, contractMatrix, contractColumn, finSuccAboveEquiv_apply, h, ite_true]
    constructor
    · intro hne
      by_contra hcon
      push Not at hcon
      exact hne (by rw [hcon.1, hcon.2, add_zero])
    · rintro (h' | h') hsum
      · exact h' (by linarith)
      · exact h' (by linarith)
  · simp only [support, contractMatrix, contractColumn, finSuccAboveEquiv_apply, h, ite_false]

/-- If the contraction of the support of a nonnegative matrix `A` at column `c` is nearly
decomposable (in the generic sense used by `Terminal` and Lemma 2.4), then the support of
the contracted matrix is `NearlyDecomposable`.  This is what lets the induction hypothesis
of Section 7 be applied to `C(A)` (lines 767-769). -/
theorem nearlyDecomposable_support_contractMatrix {m : ℕ} {A : Square (m + 1)}
    (hA : Nonnegative A) {r s c : Fin (m + 1)}
    (hND : NearlyDecomposableOn (contractColumn (support A) r s c)) :
    NearlyDecomposable (support (contractMatrix A r s c)) := by
  rw [← nearlyDecomposableOn_fin_iff]
  exact (nearlyDecomposableOn_relabel_iff (finSuccAboveEquiv s) (finSuccAboveEquiv c)
    (fun i j => support_contractMatrix_iff hA r s c i j)).2 hND

/-- Section 2.2, lines 115-117: if the support of a nonnegative matrix `A` is fully
indecomposable and column `c` meets exactly the rows `r ≠ s`, then the support of the
contracted matrix `C(A)` is fully indecomposable.  (The paper argues through total support
and connectedness; here it follows from the preservation of the strict Hall inequalities,
`fullyIndecomposable_contractColumn`.) -/
theorem fullyIndecomposable_support_contractMatrix {m : ℕ} {A : Square (m + 1)}
    (hA : Nonnegative A) (hFI : FullyIndecomposable (support A)) {r s c : Fin (m + 1)}
    (hrs : r ≠ s) (hc : ∀ i, support A i c ↔ i = r ∨ i = s) :
    FullyIndecomposable (support (contractMatrix A r s c)) := by
  rw [fullyIndecomposable_iff_strictHall, ← strictHallOn_fin_iff]
  exact (strictHallOn_relabel_iff (finSuccAboveEquiv s) (finSuccAboveEquiv c)
    (fun i j => support_contractMatrix_iff hA r s c i j)).2
    (fullyIndecomposable_contractColumn _ hrs hc hFI)

/-! ### The row case through the transpose -/

/-- A row contraction of `D` is the transpose of a column contraction of the transposed
support, so one is nearly decomposable exactly when the other is (line 115: "A degree-two
row has the transposed contraction"). -/
theorem nearlyDecomposableOn_contractRow_iff {n : ℕ} (D : Fin n → Fin n → Prop)
    (r c d : Fin n) :
    NearlyDecomposableOn (contractRow D r c d) ↔
      NearlyDecomposableOn (contractColumn (transposeSupport D) c d r) := by
  have hcard : Fintype.card (Drop r) = Fintype.card (Drop d) :=
    (Set.card_ne_eq r).trans (Set.card_ne_eq d).symm
  exact (nearlyDecomposableOn_transpose_iff hcard (contractRow D r c d)).symm

/-- Row form of `nearlyDecomposable_support_contractMatrix` (line 115): if the contraction
of the support of a nonnegative matrix `A` at row `r` is nearly decomposable, then the
column contraction of the transposed matrix `Aᵀ` at its column `r` has nearly decomposable
support. -/
theorem nearlyDecomposable_support_contractMatrix_transpose {m : ℕ} {A : Square (m + 1)}
    (hA : Nonnegative A) {r c d : Fin (m + 1)}
    (hND : NearlyDecomposableOn (contractRow (support A) r c d)) :
    NearlyDecomposable (support (contractMatrix A.transpose c d r)) :=
  nearlyDecomposable_support_contractMatrix (nonnegative_transpose hA)
    ((nearlyDecomposableOn_contractRow_iff (support A) r c d).1 hND)

/-! ### The case split of the induction step -/

/-- The case split at the start of the induction step (lines 766-767 and 772; the
definition of a terminal support is at lines 152-153): a support is not `Terminal` exactly
when some degree-two column or some degree-two row has a nearly decomposable contraction. -/
theorem exists_nd_contraction_iff_not_terminal {n : ℕ} (D : Fin n → Fin n → Prop) :
    ((∃ r s c, r ≠ s ∧ D r c ∧ D s c ∧ columnDegreeOn D c = 2 ∧
        NearlyDecomposableOn (contractColumn D r s c)) ∨
      (∃ r c d, c ≠ d ∧ D r c ∧ D r d ∧ rowDegreeOn D r = 2 ∧
        NearlyDecomposableOn (contractRow D r c d))) ↔ ¬Terminal D := by
  unfold Terminal
  rw [not_and_or]
  push Not
  rfl

/-! ### The contraction data at a face minimizer -/

/-- At a face minimizer `A` of a nearly decomposable face `Ω(D)`, a degree-two column `c`
of `D` meeting the rows `r ≠ s` carries exactly two nonzero entries of `A`, in rows `r` and
`s`, because the support of `A` is `D` by Lemma 2.1 (line 106).  These are the hypotheses
under which the contraction `C(A)` is defined (lines 113-114). -/
theorem faceMinimizer_column_entries {n : ℕ} {D : Fin n → Fin n → Prop}
    (hD : NearlyDecomposable D) {A : Square n} (hA : FaceMinimizer D A) {r s c : Fin n}
    (hrs : r ≠ s) (hrc : D r c) (hsc : D s c) (hdeg : columnDegreeOn D c = 2) :
    A r c ≠ 0 ∧ A s c ≠ 0 ∧ ∀ i, i ≠ r → i ≠ s → A i c = 0 := by
  have hsupp : support A = D := faceMinimizer_support_eq hD hA
  have hpair := column_neighbors_eq_pair_of_degree_two D hrs hrc hsc hdeg
  refine ⟨?_, ?_, fun i hir his => ?_⟩
  · exact (congrFun (congrFun hsupp r) c).mpr hrc
  · exact (congrFun (congrFun hsupp s) c).mpr hsc
  · by_contra h
    rcases (hpair i).1 (hA.1.2 i c h) with h' | h'
    · exact hir h'
    · exact his h'

/-- The data produced by an ND-preserving column contraction at a face minimizer (Lemmas
2.1 and 2.2, lines 101-122, together with the bridge `support_contractMatrix_iff`): let `A`
minimize the permanent on the nearly decomposable face `Ω(D)`, and let `c` be a degree-two
column of `D`, meeting the rows `r ≠ s`, whose contraction is nearly decomposable.  Then the
contracted matrix `C(A)` is doubly stochastic, its support is nearly decomposable, and
`per C(A) = 2 per A` (equation (2.2)). -/
theorem faceMinimizer_contraction_nd {m : ℕ} {D : Fin (m + 1) → Fin (m + 1) → Prop}
    (hD : NearlyDecomposable D) {A : Square (m + 1)} (hA : FaceMinimizer D A)
    {r s c : Fin (m + 1)} (hrs : r ≠ s) (hrc : D r c) (hsc : D s c)
    (hdeg : columnDegreeOn D c = 2)
    (hND : NearlyDecomposableOn (contractColumn D r s c)) :
    DoublyStochastic (contractMatrix A r s c) ∧
      NearlyDecomposable (support (contractMatrix A r s c)) ∧
      permanent (contractMatrix A r s c) = 2 * permanent A := by
  have hsupp : support A = D := faceMinimizer_support_eq hD hA
  obtain ⟨hr, hs, hc⟩ := faceMinimizer_column_entries hD hA hrs hrc hsc hdeg
  obtain ⟨hDS, hper, -⟩ := faceMinimizer_contraction hA hrs hr hs hc
  exact ⟨hDS, nearlyDecomposable_support_contractMatrix hA.1.1.1 (by rw [hsupp]; exact hND),
    hper⟩

/-- Row form of `faceMinimizer_contraction_nd`, by transposition (line 115; Lemma 2.2 is
stated for rows and columns, lines 119-122): at a degree-two row `r` of `D`, meeting the
columns `c ≠ d`, whose contraction is nearly decomposable, the column contraction `C(Aᵀ)` of
the transposed minimizer is doubly stochastic with nearly decomposable support, and
`per C(Aᵀ) = 2 per A`. -/
theorem faceMinimizer_row_contraction_nd {m : ℕ} {D : Fin (m + 1) → Fin (m + 1) → Prop}
    (hD : NearlyDecomposable D) {A : Square (m + 1)} (hA : FaceMinimizer D A)
    {r c d : Fin (m + 1)} (hcd : c ≠ d) (hrc : D r c) (hrd : D r d)
    (hdeg : rowDegreeOn D r = 2)
    (hND : NearlyDecomposableOn (contractRow D r c d)) :
    DoublyStochastic (contractMatrix A.transpose c d r) ∧
      NearlyDecomposable (support (contractMatrix A.transpose c d r)) ∧
      permanent (contractMatrix A.transpose c d r) = 2 * permanent A := by
  have h := faceMinimizer_contraction_nd (nearlyDecomposable_transposeSupport hD)
    (faceMinimizer_transpose hA) hcd (show transposeSupport D c r from hrc)
    (show transposeSupport D d r from hrd) hdeg
    ((nearlyDecomposableOn_contractRow_iff D r c d).1 hND)
  rwa [permanent_transpose] at h

/-! ### Equation (7.1) -/

/-- **Equation (7.1), column form** (lines 766-769).  Let `A` minimize the permanent on the
nearly decomposable face `Ω(D)` of order `m + 1`, and let a degree-two column of `D` have a
nearly decomposable contraction.  If the Foregger bound holds at order `m`, then
`per A ≥ 2^(1-(m+1))`: indeed `2 per A = per C(A) ≥ 2^(1-m)`. -/
theorem contraction_branch_column {m : ℕ} (hIH : ForeggerBoundAt m)
    {D : Fin (m + 1) → Fin (m + 1) → Prop} (hD : NearlyDecomposable D)
    {A : Square (m + 1)} (hA : FaceMinimizer D A) {r s c : Fin (m + 1)} (hrs : r ≠ s)
    (hrc : D r c) (hsc : D s c) (hdeg : columnDegreeOn D c = 2)
    (hND : NearlyDecomposableOn (contractColumn D r s c)) :
    foreggerTarget (m + 1) ≤ permanent A := by
  have hm : 1 ≤ m := by
    by_contra h
    have hr := r.isLt
    have hs := s.isLt
    exact hrs (Fin.ext (by omega))
  obtain ⟨hDS, hNDc, hper⟩ := faceMinimizer_contraction_nd hD hA hrs hrc hsc hdeg hND
  exact bicontraction_transports_bound (n := m + 1) (by omega) hper (hIH _ hDS hNDc)

/-- **Equation (7.1), row form** (lines 766-769), by transposition: the same bound when a
degree-two row of `D` has a nearly decomposable contraction. -/
theorem contraction_branch_row {m : ℕ} (hIH : ForeggerBoundAt m)
    {D : Fin (m + 1) → Fin (m + 1) → Prop} (hD : NearlyDecomposable D)
    {A : Square (m + 1)} (hA : FaceMinimizer D A) {r c d : Fin (m + 1)} (hcd : c ≠ d)
    (hrc : D r c) (hrd : D r d) (hdeg : rowDegreeOn D r = 2)
    (hND : NearlyDecomposableOn (contractRow D r c d)) :
    foreggerTarget (m + 1) ≤ permanent A := by
  have h := contraction_branch_column hIH (nearlyDecomposable_transposeSupport hD)
    (faceMinimizer_transpose hA) hcd (show transposeSupport D c r from hrc)
    (show transposeSupport D d r from hrd) hdeg
    ((nearlyDecomposableOn_contractRow_iff D r c d).1 hND)
  rwa [permanent_transpose] at h

/-- **Branch 1 of Section 7** (lines 748 and 766-769): if the nearly decomposable support
`D` of order `m + 1` is not `Terminal`, i.e. some degree-two line has a nearly decomposable
contraction, and the Foregger bound holds at order `m`, then every permanent minimizer of
the face `Ω(D)` satisfies `per A ≥ 2^(1-(m+1))`. -/
theorem bound_of_not_terminal {m : ℕ} (hIH : ForeggerBoundAt m)
    {D : Fin (m + 1) → Fin (m + 1) → Prop} (hD : NearlyDecomposable D)
    {A : Square (m + 1)} (hA : FaceMinimizer D A) (hnt : ¬Terminal D) :
    foreggerTarget (m + 1) ≤ permanent A := by
  rcases (exists_nd_contraction_iff_not_terminal D).2 hnt with
    ⟨r, s, c, hrs, hrc, hsc, hdeg, hND⟩ | ⟨r, c, d, hcd, hrc, hrd, hdeg, hND⟩
  · exact contraction_branch_column hIH hD hA hrs hrc hsc hdeg hND
  · exact contraction_branch_row hIH hD hA hcd hrc hrd hdeg hND

/-! ### Order two is outside the contraction branch -/

/-- On a row type with at most one element the strict Hall condition is vacuous, so a
support with an edge is never `NearlyDecomposableOn` there (auxiliary; this is the generic
form of the order-one convention discussed in `LaviFaceBasics`). -/
theorem not_nearlyDecomposableOn_of_card_le_one {α β : Type*} [Fintype α] [Fintype β]
    {S : α → β → Prop} (hα : Fintype.card α ≤ 1) {a : α} {b : β} (hab : S a b) :
    ¬NearlyDecomposableOn S := by
  intro hND
  refine hND.2 a b hab fun R hR hlt => ?_
  have hpos := Finset.card_pos.mpr hR
  omega

/-- The nearly decomposable support of order two, `K_{2,2}`, is `Terminal` in the Lean
sense: each of its contractions is the order-one singleton, which is not nearly decomposable
for the Lean predicates.  (In the paper the singleton *is* ND, lines 33-34, and terminal
supports have order at least three, line 152.)  This is why order two is a base case of the
induction and why every statement about `Terminal` supports assumes order at least three. -/
theorem nearlyDecomposable_two_terminal {D : Fin 2 → Fin 2 → Prop}
    (hD : NearlyDecomposable D) : Terminal D := by
  have hall := (nearlyDecomposable_two_iff D).1 hD
  have hcard : ∀ x : Fin 2, Fintype.card (Drop x) ≤ 1 := by
    intro x
    have h : Fintype.card (Drop x) = Fintype.card (Fin 2) - 1 := Set.card_ne_eq x
    rw [Fintype.card_fin] at h
    omega
  constructor
  · intro r s c hrs _ _ _
    obtain ⟨j, hj⟩ := exists_ne c
    exact not_nearlyDecomposableOn_of_card_le_one (hcard s)
      ((contractColumn_merged D hrs c ⟨j, hj⟩).2 (Or.inl (hall r j)))
  · intro r c d hcd _ _ _
    obtain ⟨i, hi⟩ := exists_ne r
    have hedge : contractRow D r c d ⟨i, hi⟩ ⟨c, hcd⟩ := by
      simp [contractRow, hall]
    exact not_nearlyDecomposableOn_of_card_le_one (hcard r) hedge

end LaviSection2
