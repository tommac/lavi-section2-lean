import LaviSection2.LaviCutFree

/-!
# Transposition, the column one-star bound, and the leaf gap (6.1)

* `transposeEquiv`: labelled matchings of `(row, col)` and of the transposed
  core `(col, row)` correspond, with the same occurrences.  Hence the core
  functional and the normalized gap are transposition invariant
  (`coreFunctional_transpose`, `normalizedGap_transpose`).
* `lavi_corollary_5_2_col`: Corollary 5.2 with a distinguished column
  ("transposition proves the column version").
* `lavi_eq_6_1`, `lavi_eq_6_1'`: if a closed factor of order at least three is
  cut-free, the correction set `N` of (4.5) is empty, every non-marker
  occurrence is long in `B`, and `G_B ≥ log (8192/6561) > 0` (Lavi (6.1)),
  assuming Gurvits's inequality.  The marker may be a column (`H₁`) or a row
  (`H₂`).
-/

set_option linter.unusedSectionVars false

namespace LaviSection2

open Finset Real Function

section Transpose

variable {U V E : Type*} [Fintype U] [Fintype V] [Fintype E]
  [DecidableEq U] [DecidableEq V] [DecidableEq E] {row : E → U} {col : E → V}

/-- The transposed matching: the occurrence chosen at each column. -/
noncomputable def transposeMatch (M : LMatch row col) : LMatch col row :=
  ⟨fun w => M.1 ((Equiv.ofBijective _ M.2.2).symm w),
    fun w => Equiv.ofBijective_apply_symm_apply _ M.2.2 w, by
      have : (fun w => row (M.1 ((Equiv.ofBijective _ M.2.2).symm w))) =
          (Equiv.ofBijective _ M.2.2).symm := funext fun w => M.2.1 _
      rw [this]; exact Equiv.bijective _⟩

theorem transposeMatch_mem (M : LMatch row col) (e : E) :
    (transposeMatch M).1 (col e) = e ↔ M.1 (row e) = e := by
  set σ := Equiv.ofBijective _ M.2.2
  show M.1 (σ.symm (col e)) = e ↔ M.1 (row e) = e
  constructor
  · intro h
    have hr : row e = σ.symm (col e) := by
      have := M.2.1 (σ.symm (col e)); rw [h] at this; exact this
    rw [hr, h]
  · intro h
    have : σ (row e) = col e := by
      show col (M.1 (row e)) = col e
      rw [h]
    rw [← this, Equiv.symm_apply_apply, h]

theorem transposeMatch_transposeMatch (M : LMatch row col) :
    transposeMatch (transposeMatch M) = M := by
  refine Subtype.ext (funext fun u => ?_)
  have h1 : (transposeMatch M).1 (col (M.1 u)) = M.1 u :=
    (transposeMatch_mem M (M.1 u)).2 (by rw [M.2.1])
  have h2 := (transposeMatch_mem (transposeMatch M) (M.1 u)).2 h1
  rwa [M.2.1] at h2

/-- Matchings of a core and of its transpose correspond. -/
noncomputable def transposeEquiv : LMatch row col ≃ LMatch col row where
  toFun := transposeMatch
  invFun := transposeMatch
  left_inv := transposeMatch_transposeMatch
  right_inv := transposeMatch_transposeMatch

theorem coreMarginal_transpose (μ : LMatch row col → ℝ) (e : E) :
    coreMarginal col row (μ ∘ transposeEquiv.symm) e = coreMarginal row col μ e := by
  classical
  unfold coreMarginal
  rw [Finset.sum_filter, Finset.sum_filter,
    ← Equiv.sum_comp (transposeEquiv (row := row) (col := col))]
  refine Finset.sum_congr rfl fun M _ => ?_
  simp only [comp_apply, Equiv.symm_apply_apply]
  show (if (transposeMatch M).1 (col e) = e then μ M else 0) = _
  rw [if_congr (transposeMatch_mem M e) rfl rfl]

theorem isCoreLaw_transpose {x : E → ℝ} {μ : LMatch row col → ℝ} :
    IsCoreLaw row col x μ ↔ IsCoreLaw col row x (μ ∘ transposeEquiv.symm) := by
  have hsum : ∑ N, (μ ∘ transposeEquiv.symm) N = ∑ M, μ M :=
    Equiv.sum_comp transposeEquiv.symm μ
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact ⟨fun _ => h0 _, by rw [hsum, h1], funext fun e => by rw [coreMarginal_transpose, h2]⟩
  · rintro ⟨h0, h1, h2⟩
    refine ⟨fun M => by simpa using h0 (transposeEquiv M), by rw [← hsum, h1], funext fun e => ?_⟩
    rw [← coreMarginal_transpose, h2]

/-- The core functional is transposition invariant. -/
theorem coreFunctional_transpose (x : E → ℝ) :
    coreFunctional col row x = coreFunctional row col x := by
  unfold coreFunctional coreMaxEntropy
  congr 2
  ext t
  constructor
  · rintro ⟨ν, hν, rfl⟩
    refine ⟨ν ∘ transposeEquiv, isCoreLaw_transpose.2 (by
      have : (ν ∘ ⇑transposeEquiv) ∘ ⇑transposeEquiv.symm = ν :=
        funext fun N => by simp
      rw [this]; exact hν), ?_⟩
    unfold coreLawEntropy
    exact Equiv.sum_comp transposeEquiv (fun N => -(ν N * log (ν N)))
  · rintro ⟨μ, hμ, rfl⟩
    refine ⟨μ ∘ transposeEquiv.symm, isCoreLaw_transpose.1 hμ, ?_⟩
    unfold coreLawEntropy
    exact Equiv.sum_comp transposeEquiv.symm (fun M => -(μ M * log (μ M)))

/-- The normalized gap is transposition invariant on balanced cores. -/
theorem normalizedGap_transpose (hbal : Fintype.card U = Fintype.card V) (L : Finset E)
    (x : E → ℝ) : normalizedGap col row L x = normalizedGap row col L x := by
  unfold normalizedGap
  rw [coreFunctional_transpose, hbal]

variable (row col)

/-- **Lavi Corollary 5.2, column version (assuming Gurvits).**  With a
distinguished column `w` and `L` the occurrences off `w`. -/
theorem lavi_corollary_5_2_col (hG : GurvitsCapacityInequality)
    (hbal : Fintype.card U = Fintype.card V) (hk : 3 ≤ Fintype.card U)
    (hR : ∀ u, 3 ≤ ((rowSet row u).image col).card)
    (hC : ∀ w, 3 ≤ (((univ : Finset E).filter fun e => col e = w).image row).card)
    (w : V) {x : E → ℝ} (hlaw : ∃ μ, IsCoreLaw row col x μ) :
    log (8192 / 6561) ≤ normalizedGap row col (offRoot col w) x := by
  obtain ⟨μ, hμ⟩ := hlaw
  rw [← normalizedGap_transpose hbal]
  exact (lavi_corollary_5_2 col row w hG hbal.symm (hbal ▸ hk) hC hR
    ⟨_, isCoreLaw_transpose.1 hμ⟩).1

end Transpose

section LeafGap

variable {U V E : Type*} [Fintype U] [Fintype V] [Fintype E]
  [DecidableEq U] [DecidableEq V] [DecidableEq E] {row : E → U} {col : E → V}
  (K : ShoreCut row col)

namespace ShoreCut

theorem leafLong₂_eq_of_all (h : removableSet K.row₂ K.col₂ univ = univ) :
    K.leafLong₂ = offRoot K.row₂ (Sum.inl ()) := by
  ext e
  simp only [leafLong₂, h, offRoot, mem_filter, mem_univ, true_and]
  constructor
  · intro hs h'; by_contra hc
    rw [K.row₂_of_not_sR hs] at h'; exact Sum.inr_ne_inl h'
  · intro h' hs; exact h' (K.row₂_of_sR hs)

theorem leafLong₁_eq_of_all (h : removableSet K.row₁ K.col₁ univ = univ) :
    K.leafLong₁ = offRoot K.col₁ (Sum.inr ()) := by
  ext e
  simp only [leafLong₁, h, offRoot, mem_filter, mem_univ, true_and]
  rw [Ne, K.col₁_eq_inr_iff, not_not]

theorem essential₂_eq_empty (h : removableSet K.row₂ K.col₂ univ = univ) : K.essential₂ = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro e he
  obtain ⟨hsd, hc⟩ := mem_filter.1 he
  have : e ∈ K.remLabels₂ := (K.mem_remLabels₂).2 ⟨hc.2, by
    have := (mem_removableSet K.row₂ K.col₂).1 (h ▸ mem_univ (⟨e, hc.2⟩ : K.E₂))
    exact this.2⟩
  exact (mem_sdiff.1 hsd).2 this

theorem essential₁_eq_empty (h : removableSet K.row₁ K.col₁ univ = univ) : K.essential₁ = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro e he
  obtain ⟨hsd, hc⟩ := mem_filter.1 he
  have : e ∈ K.remLabels₁ := (K.mem_remLabels₁).2 ⟨hc.1, by
    have := (mem_removableSet K.row₁ K.col₁).1 (h ▸ mem_univ (⟨e, hc.1⟩ : K.E₁))
    exact this.2⟩
  exact (mem_sdiff.1 hsd).2 this

variable (hG : GurvitsCapacityInequality) (hbal : Fintype.card U = Fintype.card V)
  (hFI : CoreFI row col univ)

include hG hbal hFI in
/-- **Lavi (6.1), leaf `H₂` (marker row).**  If `H₂` has order at least three
and no nontrivial tight cut, then `N = ∅` and `G_B ≥ log (8192/6561)`, so
`G_{H,L(H)} = G_B + G_R` with `G_B > 0`. -/
theorem lavi_eq_6_1' (hk : 3 ≤ Fintype.card (Unit ⊕ K.U₂)) (hcut : CutFree K.row₂ K.col₂)
    {x : E → ℝ} (hlaw : ∃ μ, IsCoreLaw row col x μ) :
    log (8192 / 6561) ≤ normalizedGap K.row₂ K.col₂ K.leafLong₂ (K.flow₂ x) ∧
      K.essential₂ = ∅ ∧
      normalizedGap row col (removableSet row col univ) x =
        normalizedGap K.row₂ K.col₂ K.leafLong₂ (K.flow₂ x) +
          normalizedGap K.row₁ K.col₁ (removableSet K.row₁ K.col₁ univ) (K.flow₁ x) := by
  have hbal₂ : Fintype.card (Unit ⊕ K.U₂) = Fintype.card K.V₂ := by
    rw [Fintype.card_sum, Fintype.card_unit, K.card_V₂ hbal]; ring
  have hFI₂ := (K.coreFI_factors hbal hFI).2
  obtain ⟨hR, hC, hall⟩ := lavi_lemma_6_1 hbal₂ hFI₂ hcut hk
  obtain ⟨μ, hμ⟩ := hlaw
  have hgap := (lavi_corollary_5_2 K.row₂ K.col₂ (Sum.inl ()) hG hbal₂ hk hR hC
    ⟨_, K.isCoreLaw_push₂ hμ⟩).1
  rw [← K.leafLong₂_eq_of_all hall] at hgap
  refine ⟨hgap, K.essential₂_eq_empty hall, ?_⟩
  rw [K.lavi_eq_4_5' hbal hFI ⟨μ, hμ⟩, K.essential₂_eq_empty hall, Finset.sum_empty, sub_zero]

include hG hbal hFI in
/-- **Lavi (6.1), leaf `H₁` (marker column).** -/
theorem lavi_eq_6_1 (hk : 3 ≤ Fintype.card K.U₁) (hcut : CutFree K.row₁ K.col₁)
    {x : E → ℝ} (hlaw : ∃ μ, IsCoreLaw row col x μ) :
    log (8192 / 6561) ≤ normalizedGap K.row₁ K.col₁ K.leafLong₁ (K.flow₁ x) ∧
      K.essential₁ = ∅ ∧
      normalizedGap row col (removableSet row col univ) x =
        normalizedGap K.row₁ K.col₁ K.leafLong₁ (K.flow₁ x) +
          normalizedGap K.row₂ K.col₂ (removableSet K.row₂ K.col₂ univ) (K.flow₂ x) := by
  have hbal₁ : Fintype.card K.U₁ = Fintype.card (K.V₁ ⊕ Unit) := by
    rw [Fintype.card_sum, Fintype.card_unit]; exact K.card
  have hFI₁ := (K.coreFI_factors hbal hFI).1
  obtain ⟨hR, hC, hall⟩ := lavi_lemma_6_1 hbal₁ hFI₁ hcut hk
  obtain ⟨μ, hμ⟩ := hlaw
  have hgap := lavi_corollary_5_2_col K.row₁ K.col₁ hG hbal₁ hk hR hC (Sum.inr ())
    ⟨_, K.isCoreLaw_push₁ hμ⟩
  rw [← K.leafLong₁_eq_of_all hall] at hgap
  refine ⟨hgap, K.essential₁_eq_empty hall, ?_⟩
  rw [K.lavi_eq_4_5 hbal hFI ⟨μ, hμ⟩, K.essential₁_eq_empty hall, Finset.sum_empty, sub_zero]

end ShoreCut

end LeafGap

end LaviSection2
