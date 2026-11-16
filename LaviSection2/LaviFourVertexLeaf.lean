import LaviSection2.LaviMinShore
import Mathlib.Combinatorics.Pigeonhole

/-!
# Lavi Lemma 6.3 (four-vertex leaf) and the order count (6.5)

* `faceFunctional_two`: a `2 × 2` doubly stochastic matrix has a unique law,
  so `F = h₂(t) - 2 h₂(t) = -h₂(t)` with `t = X₀₀`.
* `normalizedGap_order_two`: for an order-two core, at any position `(u, w)`,
  `G_{K,L} = δ(t) + ∑_{e ∈ L} δ(x_e)` with `t` the aggregated flow at
  `(u, w)` (Lavi (6.4); `δ(t) = δ(1 - t)` makes the position irrelevant).
* `mem_removableSet_order_two`: in an FI core of order two, an occurrence is
  removable exactly when it has a parallel occurrence.
* `lavi_lemma_6_3`, `lavi_lemma_6_3'`: for an order-two leaf (marker column,
  resp. marker row) of a nontrivial tight cut of a core of minimum occurrence
  degree three, at every positive feasible flow,
  `G_B - ∑_{e ∈ N} δ(x_e) > 0`, with `ℓ_B ≥ 2` and `|N| ≤ 1`.
* `lavi_eq_6_5`: the order count `n = (k - 1) + ℓ_B + n_R - |N|`, hence
  `n_R < n` whenever `k ≥ 3` and `N = ∅`, or `k = 2`, `ℓ_B ≥ 2`, `|N| ≤ 1`.
-/

set_option linter.unusedSectionVars false

namespace LaviSection2

open Finset Real Equiv

/-! ### The `2 × 2` face functional -/

theorem perm_fin_two (σ : Perm (Fin 2)) : σ = 1 ∨ σ = swap 0 1 := by
  revert σ; decide

theorem sum_perm_fin_two (f : Perm (Fin 2) → ℝ) : ∑ σ, f σ = f 1 + f (swap 0 1) := by
  refine Fintype.sum_eq_add 1 (swap 0 1) (by decide) fun σ ⟨h1, h2⟩ => ?_
  rcases perm_fin_two σ with h | h
  · exact absurd h h1
  · exact absurd h h2

theorem doublyStochastic_two {X : Square 2} (hX : DoublyStochastic X) :
    X 0 1 = 1 - X 0 0 ∧ X 1 0 = 1 - X 0 0 ∧ X 1 1 = X 0 0 := by
  have r0 := hX.2.1 0
  have r1 := hX.2.1 1
  have c0 := hX.2.2 0
  simp only [Fin.sum_univ_two] at r0 r1 c0
  refine ⟨by linarith, by linarith, by linarith⟩

/-- **Lavi (6.4), matrix form.**  `F(X) = -h₂(X₀₀)` for `2 × 2` doubly
stochastic `X`. -/
theorem faceFunctional_two {X : Square 2} (hX : DoublyStochastic X) :
    faceFunctional X = -binEntropy (X 0 0) := by
  obtain ⟨h01, h10, h11⟩ := doublyStochastic_two hX
  have hlaw : ∀ μ, IsLaw X μ → lawEntropy μ = binEntropy (X 0 0) := by
    intro μ hμ
    have hm : marginal μ 0 0 = X 0 0 := by rw [hμ.2.2]
    unfold marginal at hm
    rw [Finset.sum_filter, sum_perm_fin_two] at hm
    simp only [Perm.one_apply, if_true, swap_apply_left, show ¬ (1 : Fin 2) = 0 by decide,
      if_false, add_zero] at hm
    have hs := hμ.2.1
    rw [sum_perm_fin_two] at hs
    unfold lawEntropy
    rw [sum_perm_fin_two, hm, show μ (swap 0 1) = 1 - X 0 0 by linarith,
      binEntropy_eq_negMulLog_add_negMulLog_one_sub, Real.negMulLog, Real.negMulLog]
    ring
  obtain ⟨μ₀, hμ₀⟩ := exists_isLaw (m := 1) hX
  have hset : lawEntropy '' {μ | IsLaw X μ} = {binEntropy (X 0 0)} := by
    ext t
    constructor
    · rintro ⟨μ, hμ, rfl⟩; exact hlaw μ hμ
    · rintro rfl; exact ⟨μ₀, hμ₀, hlaw μ₀ hμ₀⟩
  have hrow : rowEntropy X = 2 * binEntropy (X 0 0) := by
    unfold rowEntropy
    simp only [Fin.sum_univ_two]
    rw [h01, h10, h11, binEntropy_eq_negMulLog_add_negMulLog_one_sub, Real.negMulLog,
      Real.negMulLog]
    ring
  unfold faceFunctional maxMatchingEntropy
  rw [hset, csSup_singleton, hrow]
  ring

section OrderTwo

variable {U V E : Type*} [Fintype U] [Fintype V] [Fintype E]
  [DecidableEq U] [DecidableEq V] [DecidableEq E] {row : E → U} {col : E → V}

/-- Unit row sums of a law's marginals. -/
theorem IsCoreLaw.rowSet_sum {x : E → ℝ} {μ : LMatch row col → ℝ}
    (hμ : IsCoreLaw row col x μ) (u : U) : ∑ e ∈ rowSet row u, x e = 1 := by
  classical
  calc ∑ e ∈ rowSet row u, x e
      = ∑ e ∈ rowSet row u,
          ∑ M ∈ (univ : Finset (LMatch row col)).filter (fun M => M.1 (row e) = e), μ M :=
        Finset.sum_congr rfl fun e _ => (congrFun hμ.2.2 e).symm
    _ = ∑ M, ∑ e ∈ (univ : Finset E).filter (fun e => row e = u ∧ M.1 (row e) = e), μ M :=
        Finset.sum_comm' (by intro e M; simp only [rowSet, mem_filter, mem_univ, true_and]; tauto)
    _ = ∑ M, μ M := by
        refine Finset.sum_congr rfl fun M _ => ?_
        rw [Finset.sum_eq_single_of_mem (M.1 u)
          (Finset.mem_filter.2 ⟨mem_univ _, M.2.1 _, by rw [M.2.1]⟩)]
        intro e he hne
        obtain ⟨-, hr, hm⟩ := Finset.mem_filter.1 he
        exact absurd (by rw [← hm, hr]) hne
    _ = 1 := hμ.2.1

/-- Unit column sums of a law's marginals. -/
theorem IsCoreLaw.colSet_sum {x : E → ℝ} {μ : LMatch row col → ℝ}
    (hμ : IsCoreLaw row col x μ) (w : V) :
    ∑ e ∈ (univ : Finset E).filter (fun e => col e = w), x e = 1 := by
  have h := (isCoreLaw_transpose.1 hμ).rowSet_sum w
  exact h

/-- **Lavi (6.4).**  For an order-two core, at any position `(u, w)`,
`G_{K,L}(x) = δ(t) + ∑_{e ∈ L} δ(x_e)`, `t` the aggregated flow at `(u, w)`. -/
theorem normalizedGap_order_two (hU : Fintype.card U = 2) (hV : Fintype.card V = 2)
    {x : E → ℝ} {μ : LMatch row col → ℝ} (hμ : IsCoreLaw row col x μ) (L : Finset E)
    (u : U) (w : V) :
    normalizedGap row col L x =
      subdivCharge (∑ e ∈ (univ : Finset E).filter (fun e => row e = u ∧ col e = w), x e) +
        ∑ ℓ ∈ L, subdivCharge (x ℓ) := by
  classical
  obtain ⟨f⟩ : Nonempty (Fin 2 ≃ U) := ⟨(Fintype.equivFinOfCardEq hU).symm⟩
  obtain ⟨g⟩ : Nonempty (Fin 2 ≃ V) := ⟨(Fintype.equivFinOfCardEq hV).symm⟩
  set eR : Fin 2 ≃ U := f.trans (swap (f 0) u)
  set eC : Fin 2 ≃ V := g.trans (swap (g 0) w)
  have hR0 : eR 0 = u := by simp [eR]
  have hC0 : eC 0 = w := by simp [eC]
  have hF := coreFunctional_eq_faceFunctional (n := 2) eR eC ⟨μ, hμ⟩
  rw [faceFunctional_two (doublyStochastic_aggregate_of_law eR eC hμ)] at hF
  have h00 : aggregateMatrix row col eR eC x 0 0 =
      ∑ e ∈ (univ : Finset E).filter (fun e => row e = u ∧ col e = w), x e := by
    unfold aggregateMatrix mergeFlow
    rw [hR0, hC0]
    congr 1; ext e; simp [Prod.ext_iff]
  unfold normalizedGap subdivCharge
  rw [hF, h00, hU]
  push_cast
  ring

/-- In an FI core of order two, an occurrence is removable exactly when some
other occurrence is parallel to it. -/
theorem mem_removableSet_order_two (hU : Fintype.card U = 2) (hV : Fintype.card V = 2)
    (hFI : CoreFI row col univ) (e : E) :
    e ∈ removableSet row col univ ↔ ∃ f, f ≠ e ∧ row f = row e ∧ col f = col e := by
  rw [mem_removableSet]
  constructor
  · rintro ⟨-, hFI'⟩
    by_contra hno
    push Not at hno
    obtain ⟨w', hw'⟩ : ∃ w', ∀ j, j ≠ col e → j = w' := by
      have h1 : ((univ : Finset V).erase (col e)).card = 1 := by
        rw [card_erase_of_mem (mem_univ _), card_univ, hV]
      obtain ⟨w', hw'⟩ := Finset.card_eq_one.1 h1
      exact ⟨w', fun j hj => Finset.mem_singleton.1 (hw' ▸ Finset.mem_erase.2 ⟨hj, mem_univ _⟩)⟩
    refine not_strictHallOn_of_row_single (coreAdj row col (univ.erase e)) (by omega) (row e) w'
      (fun j ⟨f, hf, hfr, hfc⟩ => hw' j ?_) hFI'.1
    rintro rfl
    exact hno f (Finset.ne_of_mem_erase hf) hfr hfc
  · rintro ⟨f, hfe, hfr, hfc⟩
    exact ⟨mem_univ _, coreFI_erase_of_parallel hFI (mem_univ _) (mem_univ _) hfe ⟨hfr, hfc⟩⟩

end OrderTwo

section FourVertexLeaf

variable {U V E : Type*} [Fintype U] [Fintype V] [Fintype E]
  [DecidableEq U] [DecidableEq V] [DecidableEq E] {row : E → U} {col : E → V}
  (K : ShoreCut row col)

theorem subdivCharge_pos {t : ℝ} (ht : t ≠ 1 / 2) : 0 < subdivCharge t := by
  unfold subdivCharge
  have := (binEntropy_lt_log_two (p := t)).2 (by rw [one_div] at ht; exact ht)
  linarith

namespace ShoreCut

variable (hbal : Fintype.card U = Fintype.card V) (hFI : CoreFI row col univ)
  (hrow3 : ∀ u, 3 ≤ (rowSet row u).card)
  (hcol3 : ∀ w, 3 ≤ ((univ : Finset E).filter fun e => col e = w).card)

include hbal hFI hrow3 hcol3 in
/-- **Lavi Lemma 6.3, leaf `H₁` (marker column).**  If `H₁` has order two,
then at every positive feasible flow `G_B - ∑_{e ∈ N} δ(x_e) > 0`, with
`ℓ_B ≥ 2` and `|N| ≤ 1`. -/
theorem lavi_lemma_6_3 (hnt : 3 ≤ Fintype.card K.U₂ + Fintype.card K.V₂)
    (hk : Fintype.card K.U₁ = 2) {x : E → ℝ} {μ : LMatch row col → ℝ}
    (hμ : IsCoreLaw row col x μ) (hpos : ∀ e, 0 < x e) :
    2 ≤ K.leafLong₁.card ∧ K.essential₁.card ≤ 1 ∧
      0 < normalizedGap K.row₁ K.col₁ K.leafLong₁ (K.flow₁ x) -
        ∑ e ∈ K.essential₁, subdivCharge (x e) := by
  classical
  have hV1 : Fintype.card K.V₁ = 1 := by have : Fintype.card K.U₁ = Fintype.card K.V₁ + 1 := K.card; omega
  have hV : Fintype.card (K.V₁ ⊕ Unit) = 2 := by rw [Fintype.card_sum, Fintype.card_unit, hV1]
  have hFI₁ := (K.coreFI_factors hbal hFI).1
  have hμ₁ := K.isCoreLaw_push₁ hμ
  have hrem := mem_removableSet_order_two hk hV hFI₁
  obtain ⟨w₀, hw₀⟩ := Fintype.card_eq_one_iff.1 hV1
  have hU2 : 1 ≤ Fintype.card K.U₂ := by have := K.card_V₂ hbal; omega
  -- an internal bundle with two parallel occurrences
  set S := (univ : Finset K.E₁).filter fun e => K.col₁ e = Sum.inl w₀
  have hS : 3 ≤ S.card := by rw [K.card_colSet₁ w₀]; exact hcol3 _
  obtain ⟨u₀, -, hu₀⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := S) (t := (univ : Finset K.U₁)) (f := K.row₁) (n := 1) (fun _ _ => mem_univ _)
    (by rw [card_univ, hk]; omega)
  obtain ⟨f₁, f₂, hf₁, hf₂, hf12⟩ := Finset.one_lt_card_iff.1 hu₀
  obtain ⟨hf₁S, hf₁r⟩ := mem_filter.1 hf₁
  obtain ⟨hf₂S, hf₂r⟩ := mem_filter.1 hf₂
  have hf₁c : K.col₁ f₁ = Sum.inl w₀ := (mem_filter.1 hf₁S).2
  have hf₂c : K.col₁ f₂ = Sum.inl w₀ := (mem_filter.1 hf₂S).2
  have hint : ∀ f : K.E₁, K.col₁ f = Sum.inl w₀ → K.sC (col f.1) := fun f hf => by
    by_contra h; rw [(K.col₁_eq_inr_iff f).2 h] at hf; exact Sum.inr_ne_inl hf
  have hf₁L : f₁ ∈ K.leafLong₁ := mem_filter.2 ⟨(hrem f₁).2 ⟨f₂, hf12.symm, by rw [hf₁r, hf₂r],
    by rw [hf₁c, hf₂c]⟩, hint f₁ hf₁c⟩
  have hf₂L : f₂ ∈ K.leafLong₁ := mem_filter.2 ⟨(hrem f₂).2 ⟨f₁, hf12, by rw [hf₁r, hf₂r],
    by rw [hf₁c, hf₂c]⟩, hint f₂ hf₂c⟩
  have hℓB : 2 ≤ K.leafLong₁.card := by
    have : ({f₁, f₂} : Finset K.E₁) ⊆ K.leafLong₁ := by
      intro f hf; rcases mem_insert.1 hf with rfl | hf
      · exact hf₁L
      · rw [mem_singleton.1 hf]; exact hf₂L
    have := card_le_card this; rw [card_pair hf12] at this; exact this
  -- the marker occurrence at `u₀`
  obtain ⟨g, hgr, hgc⟩ : ∃ g : K.E₁, K.row₁ g = u₀ ∧ K.col₁ g = Sum.inr () := by
    by_contra hno
    push Not at hno
    refine not_strictHallOn_of_row_single (coreAdj K.row₁ K.col₁ univ) (by omega) u₀
      (Sum.inl w₀) (fun j ⟨f, _, hfr, hfc⟩ => ?_) hFI₁.1
    rcases j with w | t
    · rw [hw₀ w, ← hw₀ w₀]
    · cases t; exact absurd hfc (hno f hfr)
  have hsum1 := hμ₁.rowSet_sum u₀
  have hlt : K.flow₁ x f₁ + K.flow₁ x f₂ < 1 := by
    have hsub : ({f₁, f₂, g} : Finset K.E₁) ⊆ rowSet K.row₁ u₀ := by
      intro f hf
      simp only [mem_insert, mem_singleton] at hf
      rcases hf with rfl | rfl | rfl
      · exact mem_rowSet.2 hf₁r
      · exact mem_rowSet.2 hf₂r
      · exact mem_rowSet.2 hgr
    have hg1 : g ≠ f₁ := fun h => by rw [h, hf₁c] at hgc; exact Sum.inl_ne_inr hgc
    have hg2 : g ≠ f₂ := fun h => by rw [h, hf₂c] at hgc; exact Sum.inl_ne_inr hgc
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun f _ _ => (hpos f.1).le : ∀ f ∈ rowSet K.row₁ u₀, f ∉ ({f₁, f₂, g} : Finset K.E₁) →
        0 ≤ K.flow₁ x f)
    rw [Finset.sum_insert (by simp [hf12, hg1.symm]), Finset.sum_insert (by simp [hg2.symm]),
      Finset.sum_singleton] at hle
    have := hpos g.1
    unfold flow₁ at *
    linarith
  have hLpos : 0 < ∑ ℓ ∈ K.leafLong₁, subdivCharge (K.flow₁ x ℓ) := by
    have hne : K.flow₁ x f₁ ≠ 1 / 2 ∨ K.flow₁ x f₂ ≠ 1 / 2 := by
      by_contra h; push Not at h; linarith [h.1, h.2]
    rcases hne with h | h
    · exact lt_of_lt_of_le (subdivCharge_pos h) (Finset.single_le_sum
        (fun ℓ _ => subdivCharge_nonneg _) hf₁L)
    · exact lt_of_lt_of_le (subdivCharge_pos h) (Finset.single_le_sum
        (fun ℓ _ => subdivCharge_nonneg _) hf₂L)
  -- the correction set has at most one element
  rcases K.essential₁.eq_empty_or_nonempty with hN | ⟨e, he⟩
  · refine ⟨hℓB, by rw [hN]; simp, ?_⟩
    rw [hN, Finset.sum_empty, sub_zero, normalizedGap_order_two hk hV hμ₁ _ u₀ (Sum.inr ())]
    linarith [subdivCharge_nonneg (∑ e ∈ (univ : Finset K.E₁).filter
      (fun e => K.row₁ e = u₀ ∧ K.col₁ e = Sum.inr ()), K.flow₁ x e)]
  · -- every element of `N` is a singleton marker bundle of `H₁`
    have hsingle : ∀ e ∈ K.essential₁, ∃ hc : K.Crossing e,
        ∀ f : K.E₁, K.row₁ f = K.row₁ ⟨e, hc.1⟩ → K.col₁ f = Sum.inr () → f = ⟨e, hc.1⟩ := by
      intro e he
      obtain ⟨hsd, hc⟩ := mem_filter.1 he
      refine ⟨hc, fun f hfr hfc => ?_⟩
      by_contra hfe
      have : ⟨e, hc.1⟩ ∈ removableSet K.row₁ K.col₁ univ := (hrem _).2 ⟨f, hfe, hfr, by
        rw [hfc]; exact ((K.col₁_eq_inr_iff _).2 hc.2).symm⟩
      exact (mem_sdiff.1 hsd).2 (K.mem_remLabels₁.2 ⟨hc.1,
        ((mem_removableSet K.row₁ K.col₁).1 this).2⟩)
    obtain ⟨hc, hsing⟩ := hsingle e he
    have hNe : K.essential₁ = {e} := by
      refine Finset.eq_singleton_iff_unique_mem.2 ⟨he, fun e' he' => ?_⟩
      by_contra hne'
      obtain ⟨hc', hsing'⟩ := hsingle e' he'
      have hrows : K.row₁ ⟨e', hc'.1⟩ ≠ K.row₁ ⟨e, hc.1⟩ := fun h => hne'
        (congrArg Subtype.val (hsing ⟨e', hc'.1⟩ h ((K.col₁_eq_inr_iff _).2 hc'.2)))
      -- every crossing occurrence is `e` or `e'`
      have hcross : ∀ f : E, K.Crossing f → f = e ∨ f = e' := by
        intro f hf
        have hfc : K.col₁ ⟨f, hf.1⟩ = Sum.inr () := (K.col₁_eq_inr_iff _).2 hf.2
        have hU1 : ∀ a b c : K.U₁, a ≠ b → c = a ∨ c = b := by
          intro a b c hab
          by_contra h; push Not at h
          have : ({a, b, c} : Finset K.U₁).card ≤ 2 := hk ▸ card_le_univ _
          rw [card_insert_of_notMem (by simp [hab, h.1.symm]), card_pair (Ne.symm h.2)] at this
          omega
        rcases hU1 _ _ (K.row₁ ⟨f, hf.1⟩) hrows.symm with h | h
        · exact Or.inl (congrArg Subtype.val (hsing ⟨f, hf.1⟩ h hfc))
        · exact Or.inr (congrArg Subtype.val (hsing' ⟨f, hf.1⟩ h hfc))
      -- then the marker row of `H₂` has degree two, so `e` is essential in `H₂`
      obtain ⟨hsd, -⟩ := mem_filter.1 he
      obtain ⟨h2, hFI2⟩ := K.mem_remLabels₂.1 (mem_sdiff.1 hsd).1
      refine not_strictHallOn_of_row_single (coreAdj K.row₂ K.col₂ (univ.erase ⟨e, h2⟩))
        (by rw [Fintype.card_sum, Fintype.card_unit]; omega) (Sum.inl ()) (K.col₂ ⟨e', hc'.2⟩)
        (fun j ⟨f, hf, hfr, hfc⟩ => ?_) hFI2.1
      have hfR : K.sR (row f.1) := by
        by_contra h; rw [K.row₂_of_not_sR h] at hfr; exact Sum.inr_ne_inl hfr
      rcases hcross f.1 ⟨hfR, f.2⟩ with h | h
      · exact absurd (Subtype.ext h) (Finset.ne_of_mem_erase hf)
      · rw [← hfc]; exact Subtype.ext (congrArg Subtype.val (Subtype.ext h :
          (⟨f.1, f.2⟩ : K.E₂) = ⟨e', hc'.2⟩)) ▸ rfl
    refine ⟨hℓB, by rw [hNe, card_singleton], ?_⟩
    have hagg : ∑ f ∈ (univ : Finset K.E₁).filter
        (fun f => K.row₁ f = K.row₁ ⟨e, hc.1⟩ ∧ K.col₁ f = Sum.inr ()), K.flow₁ x f = x e := by
      rw [Finset.sum_eq_single_of_mem ⟨e, hc.1⟩ (mem_filter.2 ⟨mem_univ _, rfl,
        (K.col₁_eq_inr_iff _).2 hc.2⟩) fun f hf hfe => absurd (hsing f (mem_filter.1 hf).2.1
          (mem_filter.1 hf).2.2) hfe]
      rfl
    rw [hNe, Finset.sum_singleton,
      normalizedGap_order_two hk hV hμ₁ _ (K.row₁ ⟨e, hc.1⟩) (Sum.inr ()), hagg]
    linarith

include hbal hFI hrow3 hcol3 in
/-- **Lavi Lemma 6.3, leaf `H₂` (marker row).** -/
theorem lavi_lemma_6_3' (hnt : 3 ≤ Fintype.card K.U₁ + Fintype.card K.V₁)
    (hk : Fintype.card (Unit ⊕ K.U₂) = 2) {x : E → ℝ} {μ : LMatch row col → ℝ}
    (hμ : IsCoreLaw row col x μ) (hpos : ∀ e, 0 < x e) :
    2 ≤ K.leafLong₂.card ∧ K.essential₂.card ≤ 1 ∧
      0 < normalizedGap K.row₂ K.col₂ K.leafLong₂ (K.flow₂ x) -
        ∑ e ∈ K.essential₂, subdivCharge (x e) := by
  classical
  have hU21 : Fintype.card K.U₂ = 1 := by
    rw [Fintype.card_sum, Fintype.card_unit] at hk; omega
  have hV : Fintype.card K.V₂ = 2 := by rw [K.card_V₂ hbal, hU21]
  have hbal₂ : Fintype.card (Unit ⊕ K.U₂) = Fintype.card K.V₂ := by rw [hk, hV]
  have hFI₂ := (K.coreFI_factors hbal hFI).2
  have hμ₂ := K.isCoreLaw_push₂ hμ
  have hrem := mem_removableSet_order_two hk hV hFI₂
  obtain ⟨u₀, hu₀U⟩ := Fintype.card_eq_one_iff.1 hU21
  have hU1 : 2 ≤ Fintype.card K.U₁ := by have : Fintype.card K.U₁ = Fintype.card K.V₁ + 1 := K.card; omega
  have hbal₁ : Fintype.card K.U₁ = Fintype.card (K.V₁ ⊕ Unit) := by
    rw [Fintype.card_sum, Fintype.card_unit]; exact K.card
  -- an internal bundle with two parallel occurrences
  set S := rowSet K.row₂ (Sum.inr u₀)
  have hS : 3 ≤ S.card := by rw [K.card_rowSet₂ u₀]; exact hrow3 _
  obtain ⟨w₁, -, hw₁⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := S) (t := (univ : Finset K.V₂)) (f := K.col₂) (n := 1) (fun _ _ => mem_univ _)
    (by rw [card_univ, hV]; omega)
  obtain ⟨f₁, f₂, hf₁, hf₂, hf12⟩ := Finset.one_lt_card_iff.1 hw₁
  obtain ⟨hf₁S, hf₁c⟩ := mem_filter.1 hf₁
  obtain ⟨hf₂S, hf₂c⟩ := mem_filter.1 hf₂
  have hf₁r : K.row₂ f₁ = Sum.inr u₀ := mem_rowSet.1 hf₁S
  have hf₂r : K.row₂ f₂ = Sum.inr u₀ := mem_rowSet.1 hf₂S
  have hint : ∀ f : K.E₂, K.row₂ f = Sum.inr u₀ → ¬ K.sR (row f.1) := fun f hf h => by
    rw [K.row₂_of_sR h] at hf; exact Sum.inl_ne_inr hf
  have hf₁L : f₁ ∈ K.leafLong₂ := mem_filter.2 ⟨(hrem f₁).2 ⟨f₂, hf12.symm, by rw [hf₁r, hf₂r],
    by rw [hf₁c, hf₂c]⟩, hint f₁ hf₁r⟩
  have hf₂L : f₂ ∈ K.leafLong₂ := mem_filter.2 ⟨(hrem f₂).2 ⟨f₁, hf12, by rw [hf₁r, hf₂r],
    by rw [hf₁c, hf₂c]⟩, hint f₂ hf₂r⟩
  have hℓB : 2 ≤ K.leafLong₂.card := by
    have : ({f₁, f₂} : Finset K.E₂) ⊆ K.leafLong₂ := by
      intro f hf; rcases mem_insert.1 hf with rfl | hf
      · exact hf₁L
      · rw [mem_singleton.1 hf]; exact hf₂L
    have := card_le_card this; rw [card_pair hf12] at this; exact this
  -- the marker occurrence in column `w₁`
  obtain ⟨g, hgr, hgc⟩ : ∃ g : K.E₂, K.row₂ g = Sum.inl () ∧ K.col₂ g = w₁ := by
    by_contra hno
    push Not at hno
    refine not_strictHallOn_of_column_single (coreAdj K.row₂ K.col₂ univ) hbal₂ (by omega) w₁
      (Sum.inr u₀) (fun i ⟨f, _, hfr, hfc⟩ => ?_) hFI₂.1
    rcases i with t | u
    · cases t; exact absurd hfc (hno f hfr)
    · rw [hu₀U u, ← hu₀U u₀]
  have hsum1 := hμ₂.colSet_sum w₁
  have hlt : K.flow₂ x f₁ + K.flow₂ x f₂ < 1 := by
    have hsub : ({f₁, f₂, g} : Finset K.E₂) ⊆
        (univ : Finset K.E₂).filter fun f => K.col₂ f = w₁ := by
      intro f hf
      simp only [mem_insert, mem_singleton] at hf
      rcases hf with rfl | rfl | rfl
      · exact mem_filter.2 ⟨mem_univ _, hf₁c⟩
      · exact mem_filter.2 ⟨mem_univ _, hf₂c⟩
      · exact mem_filter.2 ⟨mem_univ _, hgc⟩
    have hg1 : g ≠ f₁ := fun h => by rw [h, hf₁r] at hgr; exact Sum.inr_ne_inl hgr
    have hg2 : g ≠ f₂ := fun h => by rw [h, hf₂r] at hgr; exact Sum.inr_ne_inl hgr
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun f _ _ => (hpos f.1).le : ∀ f ∈ (univ : Finset K.E₂).filter
        (fun f => K.col₂ f = w₁), f ∉ ({f₁, f₂, g} : Finset K.E₂) → 0 ≤ K.flow₂ x f)
    rw [Finset.sum_insert (by simp [hf12, hg1.symm]), Finset.sum_insert (by simp [hg2.symm]),
      Finset.sum_singleton] at hle
    have := hpos g.1
    unfold flow₂ at *
    linarith
  have hLpos : 0 < ∑ ℓ ∈ K.leafLong₂, subdivCharge (K.flow₂ x ℓ) := by
    have hne : K.flow₂ x f₁ ≠ 1 / 2 ∨ K.flow₂ x f₂ ≠ 1 / 2 := by
      by_contra h; push Not at h; linarith [h.1, h.2]
    rcases hne with h | h
    · exact lt_of_lt_of_le (subdivCharge_pos h) (Finset.single_le_sum
        (fun ℓ _ => subdivCharge_nonneg _) hf₁L)
    · exact lt_of_lt_of_le (subdivCharge_pos h) (Finset.single_le_sum
        (fun ℓ _ => subdivCharge_nonneg _) hf₂L)
  rcases K.essential₂.eq_empty_or_nonempty with hN | ⟨e, he⟩
  · refine ⟨hℓB, by rw [hN]; simp, ?_⟩
    rw [hN, Finset.sum_empty, sub_zero, normalizedGap_order_two hk hV hμ₂ _ (Sum.inl ()) w₁]
    linarith [subdivCharge_nonneg (∑ e ∈ (univ : Finset K.E₂).filter
      (fun e => K.row₂ e = Sum.inl () ∧ K.col₂ e = w₁), K.flow₂ x e)]
  · have hsingle : ∀ e ∈ K.essential₂, ∃ hc : K.Crossing e,
        ∀ f : K.E₂, K.row₂ f = Sum.inl () → K.col₂ f = K.col₂ ⟨e, hc.2⟩ → f = ⟨e, hc.2⟩ := by
      intro e he
      obtain ⟨hsd, hc⟩ := mem_filter.1 he
      refine ⟨hc, fun f hfr hfc => ?_⟩
      by_contra hfe
      have : ⟨e, hc.2⟩ ∈ removableSet K.row₂ K.col₂ univ := (hrem _).2 ⟨f, hfe, by
        rw [hfr]; exact (K.row₂_of_sR hc.1).symm, hfc⟩
      exact (mem_sdiff.1 hsd).2 (K.mem_remLabels₂.2 ⟨hc.2,
        ((mem_removableSet K.row₂ K.col₂).1 this).2⟩)
    obtain ⟨hc, hsing⟩ := hsingle e he
    have hNe : K.essential₂ = {e} := by
      refine Finset.eq_singleton_iff_unique_mem.2 ⟨he, fun e' he' => ?_⟩
      by_contra hne'
      obtain ⟨hc', hsing'⟩ := hsingle e' he'
      have hcols : K.col₂ ⟨e', hc'.2⟩ ≠ K.col₂ ⟨e, hc.2⟩ := fun h => hne'
        (congrArg Subtype.val (hsing ⟨e', hc'.2⟩ (K.row₂_of_sR hc'.1) h))
      have hcross : ∀ f : E, K.Crossing f → f = e ∨ f = e' := by
        intro f hf
        have hfr : K.row₂ ⟨f, hf.2⟩ = Sum.inl () := K.row₂_of_sR hf.1
        have hV2 : ∀ a b c : K.V₂, a ≠ b → c = a ∨ c = b := by
          intro a b c hab
          by_contra h; push Not at h
          have : ({a, b, c} : Finset K.V₂).card ≤ 2 := hV ▸ card_le_univ _
          rw [card_insert_of_notMem (by simp [hab, h.1.symm]), card_pair (Ne.symm h.2)] at this
          omega
        rcases hV2 _ _ (K.col₂ ⟨f, hf.2⟩) hcols.symm with h | h
        · exact Or.inl (congrArg Subtype.val (hsing ⟨f, hf.2⟩ hfr h))
        · exact Or.inr (congrArg Subtype.val (hsing' ⟨f, hf.2⟩ hfr h))
      obtain ⟨hsd, -⟩ := mem_filter.1 he
      obtain ⟨h1, hFI1⟩ := K.mem_remLabels₁.1 (mem_sdiff.1 hsd).1
      refine not_strictHallOn_of_column_single (coreAdj K.row₁ K.col₁ (univ.erase ⟨e, h1⟩))
        hbal₁ hU1 (Sum.inr ()) (K.row₁ ⟨e', hc'.1⟩) (fun i ⟨f, hf, hfr, hfc⟩ => ?_) hFI1.1
      have hfC : ¬ K.sC (col f.1) := (K.col₁_eq_inr_iff f).1 hfc
      rcases hcross f.1 ⟨f.2, hfC⟩ with h | h
      · exact absurd (Subtype.ext h) (Finset.ne_of_mem_erase hf)
      · rw [← hfr]; exact congrArg K.row₁ (Subtype.ext h)
    refine ⟨hℓB, by rw [hNe, card_singleton], ?_⟩
    have hagg : ∑ f ∈ (univ : Finset K.E₂).filter
        (fun f => K.row₂ f = Sum.inl () ∧ K.col₂ f = K.col₂ ⟨e, hc.2⟩), K.flow₂ x f = x e := by
      rw [Finset.sum_eq_single_of_mem ⟨e, hc.2⟩ (mem_filter.2 ⟨mem_univ _, K.row₂_of_sR hc.1,
        rfl⟩) fun f hf hfe => absurd (hsing f (mem_filter.1 hf).2.1 (mem_filter.1 hf).2.2) hfe]
      rfl
    rw [hNe, Finset.sum_singleton,
      normalizedGap_order_two hk hV hμ₂ _ (Sum.inl ()) (K.col₂ ⟨e, hc.2⟩), hagg]
    linarith

include hbal hFI in
/-- **Lavi (6.5), leaf `H₁`:** with `n = |U| + |L(H)|` the parent expansion
order and `n_R = |rows of H₂| + |L(H₂)|` the remainder order,
`n + |N| = (k - 1) + ℓ_B + n_R`. -/
theorem lavi_eq_6_5 :
    Fintype.card U + (removableSet row col univ).card + K.essential₁.card =
      (Fintype.card K.U₁ - 1) + K.leafLong₁.card +
        (Fintype.card (Unit ⊕ K.U₂) + (removableSet K.row₂ K.col₂ univ).card) := by
  obtain ⟨h44, hdisj⟩ := K.lavi_eq_4_4 hbal hFI
  have hsub : K.essential₁ ⊆ K.remLabels₂ := fun e he => (mem_sdiff.1 (mem_filter.1 he).1).1
  have h41 := K.lavi_eq_4_1
  have hk : 1 ≤ Fintype.card K.U₁ := by have : Fintype.card K.U₁ = Fintype.card K.V₁ + 1 := K.card; omega
  rw [h44, card_union_of_disjoint hdisj, Finset.card_map, card_sdiff_of_subset hsub]
  have hc2 : K.remLabels₂.card = (removableSet K.row₂ K.col₂ univ).card := Finset.card_map _
  have := card_le_card hsub
  omega

include hbal hFI in
/-- **Lavi (6.5), leaf `H₂`.** -/
theorem lavi_eq_6_5' :
    Fintype.card U + (removableSet row col univ).card + K.essential₂.card =
      (Fintype.card (Unit ⊕ K.U₂) - 1) + K.leafLong₂.card +
        (Fintype.card K.U₁ + (removableSet K.row₁ K.col₁ univ).card) := by
  obtain ⟨h44, hdisj⟩ := K.lavi_eq_4_4' hbal hFI
  have hsub : K.essential₂ ⊆ K.remLabels₁ := fun e he => (mem_sdiff.1 (mem_filter.1 he).1).1
  have h41 := K.lavi_eq_4_1
  have hk : 1 ≤ Fintype.card (Unit ⊕ K.U₂) := by rw [Fintype.card_sum, Fintype.card_unit]; omega
  rw [h44, card_union_of_disjoint hdisj, Finset.card_map, card_sdiff_of_subset hsub]
  have hc1 : K.remLabels₁.card = (removableSet K.row₁ K.col₁ univ).card := Finset.card_map _
  have := card_le_card hsub
  omega

end ShoreCut

end FourVertexLeaf

end LaviSection2
