import LaviSection2.LaviLeafGap

/-!
# Lavi Lemma 6.2: a minimum shore closes to a leaf

Choose a nontrivial tight shore `X` of minimum cardinality and close it with
one marker.  Then the closed factor is a leaf (it has no nontrivial tight
cut), and every non-marker vertex keeps its occurrence degree.

`lavi_lemma_6_2` returns the cut in oriented form (`ShoreCut`) and records
that both of its shores have at least three vertices: `X` is a shore of a
nontrivial tight cut, so neither the leaf nor the opposite factor is trivial.

Proof (as in the manuscript, with the orientation form of tightness): a
nontrivial tight shore `Z` of the factor may be taken to avoid the marker.  By
`tightCut_orientation` it is oriented in the factor; the same orientation holds
in the parent for the same vertex set, so `Z` is a tight shore of `H` by
`isTightCut_of_forward` / `_backward`.  Its complement contains the opposite
shore of `X`, so it is nontrivial, and `|Z| ≤ |X| - 2`, contradicting
minimality.

The hypotheses `hcov` (every occurrence lies in a perfect matching) and a
perfect matching `M₀` hold for every FI core; here they are stated
explicitly (they follow, e.g., from a positive feasible flow,
`covered_of_positive_flow`).
-/

set_option linter.unusedSectionVars false

namespace LaviSection2

open Finset

section MinShore

variable {U V E : Type*} [Fintype U] [Fintype V] [Fintype E]
  [DecidableEq U] [DecidableEq V] [DecidableEq E] {row : E → U} {col : E → V}
  (K : ShoreCut row col)

namespace ShoreCut

variable (hcov : ∀ e, ∃ M : LMatch row col, M.1 (row e) = e) (M₀ : LMatch row col)

include hcov in
theorem cov₁ : ∀ e : K.E₁, ∃ M₁ : LMatch K.row₁ K.col₁, M₁.1 (K.row₁ e) = e := by
  intro e
  obtain ⟨M, hM⟩ := hcov e.1
  exact ⟨K.proj₁ M, (K.proj₁_apply_iff M e).2 hM⟩

include hcov in
theorem cov₂ : ∀ e : K.E₂, ∃ M₂ : LMatch K.row₂ K.col₂, M₂.1 (K.row₂ e) = e := by
  intro e
  obtain ⟨M, hM⟩ := hcov e.1
  exact ⟨K.proj₂ M, (K.proj₂_apply_iff M e).2 hM⟩

include hcov M₀ in
/-- A marker-free nontrivial tight shore of `H₁` gives a smaller nontrivial
tight shore of `H`. -/
theorem shore_of_factor₁ (hnt : 3 ≤ Fintype.card K.U₂ + Fintype.card K.V₂)
    {R : Finset K.U₁} {C : Finset (K.V₁ ⊕ Unit)} (hK : IsNontrivialShore K.row₁ K.col₁ R C)
    (hm : Sum.inr () ∉ C) :
    ∃ R' : Finset U, ∃ C' : Finset V, IsNontrivialShore row col R' C' ∧
      R'.card + C'.card + 2 ≤ Fintype.card K.U₁ + Fintype.card K.V₁ := by
  classical
  set R' : Finset U := R.map (Function.Embedding.subtype _)
  set C' : Finset V := C.toLeft.map (Function.Embedding.subtype _)
  have hR' : ∀ u, u ∈ R' ↔ ∃ h : K.sR u, (⟨u, h⟩ : K.U₁) ∈ R := by
    intro u; rw [mem_map_subtype_iff]
  have hC' : ∀ w, w ∈ C' ↔ ∃ h : K.sC w, (Sum.inl ⟨w, h⟩ : K.V₁ ⊕ Unit) ∈ C := by
    intro w; rw [mem_map_subtype_iff]; simp only [mem_toLeft]
  have hRc : R'.card = R.card := Finset.card_map _
  have hCr : C.toRight = ∅ := by
    rw [eq_empty_iff_forall_notMem]; intro t ht; cases t; exact hm (mem_toRight.1 ht)
  have hCc : C'.card = C.card := by
    rw [Finset.card_map, ← card_toLeft_add_card_toRight (u := C), hCr, card_empty, add_zero]
  have M₁ : LMatch K.row₁ K.col₁ := K.proj₁ M₀
  have htight : IsTightShore row col R' C' := by
    rcases tightCut_orientation (· ∈ R) (· ∈ C) hK.1 (K.cov₁ hcov) M₁ with ⟨hbw, hc⟩ | ⟨hfw, hc⟩
    · refine isTightCut_of_backward _ _ (fun e he => ?_) ?_
      · obtain ⟨hs, hmem⟩ := (hC' (col e)).1 he
        have hr : K.sR (row e) := K.back e hs
        have hcol : K.col₁ ⟨e, hr⟩ = Sum.inl ⟨col e, hs⟩ := by
          unfold col₁; rw [dite_eq_left hs]
        have := hbw ⟨e, hr⟩ (by rw [hcol]; exact hmem)
        exact (hR' (row e)).2 ⟨hr, this⟩
      · rw [card_filter_mem, card_filter_mem, hRc, hCc]
        rwa [card_filter_mem, card_filter_mem] at hc
    · refine isTightCut_of_forward _ _ (fun e he => ?_) ?_
      · obtain ⟨hr, hmem⟩ := (hR' (row e)).1 he
        have := hfw ⟨e, hr⟩ hmem
        have hs : K.sC (col e) := by
          by_contra hs
          have h1 : K.col₁ ⟨e, hr⟩ = Sum.inr () := (K.col₁_eq_inr_iff _).2 hs
          rw [h1] at this; exact hm this
        have hcol : K.col₁ ⟨e, hr⟩ = Sum.inl ⟨col e, hs⟩ := by
          unfold col₁; rw [dite_eq_left hs]
        rw [hcol] at this
        exact (hC' (col e)).2 ⟨hs, this⟩
      · rw [card_filter_mem, card_filter_mem, hRc, hCc]
        rwa [card_filter_mem, card_filter_mem] at hc
  have hU : Fintype.card K.U₂ = Fintype.card U - Fintype.card K.U₁ :=
    Fintype.card_subtype_compl K.sR
  have hV : Fintype.card K.V₂ = Fintype.card V - Fintype.card K.V₁ :=
    Fintype.card_subtype_compl K.sC
  have hU1 : Fintype.card K.U₁ ≤ Fintype.card U := Fintype.card_subtype_le _
  have hV1 : Fintype.card K.V₁ ≤ Fintype.card V := Fintype.card_subtype_le _
  have hRle : R.card ≤ Fintype.card K.U₁ := card_le_univ _
  have hCle : C.toLeft.card ≤ Fintype.card K.V₁ := card_le_univ _
  have hCl : C.toLeft.card = C.card := by
    rw [← card_toLeft_add_card_toRight (u := C), hCr, card_empty, add_zero]
  obtain ⟨-, h3, h3c⟩ := hK
  rw [card_compl, card_compl, Fintype.card_sum, Fintype.card_unit] at h3c
  refine ⟨R', C', ⟨htight, by omega, ?_⟩, by omega⟩
  rw [card_compl, card_compl]
  omega

include hcov M₀ in
/-- A marker-free nontrivial tight shore of `H₂` gives a smaller nontrivial
tight shore of `H`. -/
theorem shore_of_factor₂ (hnt : 3 ≤ Fintype.card K.U₁ + Fintype.card K.V₁)
    {R : Finset (Unit ⊕ K.U₂)} {C : Finset K.V₂} (hK : IsNontrivialShore K.row₂ K.col₂ R C)
    (hm : Sum.inl () ∉ R) :
    ∃ R' : Finset U, ∃ C' : Finset V, IsNontrivialShore row col R' C' ∧
      R'.card + C'.card + 2 ≤ Fintype.card K.U₂ + Fintype.card K.V₂ := by
  classical
  set R' : Finset U := R.toRight.map (Function.Embedding.subtype _)
  set C' : Finset V := C.map (Function.Embedding.subtype _)
  have hR' : ∀ u, u ∈ R' ↔ ∃ h : ¬ K.sR u, (Sum.inr ⟨u, h⟩ : Unit ⊕ K.U₂) ∈ R := by
    intro u; rw [mem_map_subtype_iff]; simp only [mem_toRight]
  have hC' : ∀ w, w ∈ C' ↔ ∃ h : ¬ K.sC w, (⟨w, h⟩ : K.V₂) ∈ C := by
    intro w; rw [mem_map_subtype_iff]
  have hRl : R.toLeft = ∅ := by
    rw [eq_empty_iff_forall_notMem]; intro t ht; cases t; exact hm (mem_toLeft.1 ht)
  have hRc : R'.card = R.card := by
    rw [Finset.card_map, ← card_toLeft_add_card_toRight (u := R), hRl, card_empty, zero_add]
  have hCc : C'.card = C.card := Finset.card_map _
  have M₂ : LMatch K.row₂ K.col₂ := K.proj₂ M₀
  have htight : IsTightShore row col R' C' := by
    rcases tightCut_orientation (· ∈ R) (· ∈ C) hK.1 (K.cov₂ hcov) M₂ with ⟨hbw, hc⟩ | ⟨hfw, hc⟩
    · refine isTightCut_of_backward _ _ (fun e he => ?_) ?_
      · obtain ⟨hs, hmem⟩ := (hC' (col e)).1 he
        have := hbw ⟨e, hs⟩ hmem
        have hr : ¬ K.sR (row e) := by
          intro hr
          rw [K.row₂_of_sR (e := ⟨e, hs⟩) hr] at this; exact hm this
        rw [K.row₂_of_not_sR (e := ⟨e, hs⟩) hr] at this
        exact (hR' (row e)).2 ⟨hr, this⟩
      · rw [card_filter_mem, card_filter_mem, hRc, hCc]
        rwa [card_filter_mem, card_filter_mem] at hc
    · refine isTightCut_of_forward _ _ (fun e he => ?_) ?_
      · obtain ⟨hr, hmem⟩ := (hR' (row e)).1 he
        have hs : ¬ K.sC (col e) := fun h => hr (K.back e h)
        have := hfw ⟨e, hs⟩ (by rw [K.row₂_of_not_sR (e := ⟨e, hs⟩) hr]; exact hmem)
        exact (hC' (col e)).2 ⟨hs, this⟩
      · rw [card_filter_mem, card_filter_mem, hRc, hCc]
        rwa [card_filter_mem, card_filter_mem] at hc
  have hU : Fintype.card K.U₂ = Fintype.card U - Fintype.card K.U₁ :=
    Fintype.card_subtype_compl K.sR
  have hV : Fintype.card K.V₂ = Fintype.card V - Fintype.card K.V₁ :=
    Fintype.card_subtype_compl K.sC
  have hU1 : Fintype.card K.U₁ ≤ Fintype.card U := Fintype.card_subtype_le _
  have hV1 : Fintype.card K.V₁ ≤ Fintype.card V := Fintype.card_subtype_le _
  have hRle : R.toRight.card ≤ Fintype.card K.U₂ := card_le_univ _
  have hCle : C.card ≤ Fintype.card K.V₂ := card_le_univ _
  have hRr : R.toRight.card = R.card := by
    rw [← card_toLeft_add_card_toRight (u := R), hRl, card_empty, zero_add]
  obtain ⟨-, h3, h3c⟩ := hK
  rw [card_compl, card_compl, Fintype.card_sum, Fintype.card_unit] at h3c
  refine ⟨R', C', ⟨htight, by omega, ?_⟩, by omega⟩
  rw [card_compl, card_compl]
  omega

include hcov in
/-- **Lemma 6.2 for `H₁`.**  If `S₁` has minimum size among nontrivial tight
shores of `H`, the closed factor `H₁` is a leaf. -/
theorem cutFree₁ (M₀ : LMatch row col) (hnt : 3 ≤ Fintype.card K.U₂ + Fintype.card K.V₂)
    (hmin : ∀ R C, IsNontrivialShore row col R C →
      Fintype.card K.U₁ + Fintype.card K.V₁ ≤ R.card + C.card) :
    CutFree K.row₁ K.col₁ := by
  intro R C hK
  by_cases hm : Sum.inr () ∈ C
  · obtain ⟨R', C', h, hlt⟩ := K.shore_of_factor₁ hcov M₀ hnt (isNontrivialShore_compl.2 hK)
      (fun h => (mem_compl.1 h) hm)
    have := hmin R' C' h; omega
  · obtain ⟨R', C', h, hlt⟩ := K.shore_of_factor₁ hcov M₀ hnt hK hm
    have := hmin R' C' h; omega

include hcov in
/-- **Lemma 6.2 for `H₂`.** -/
theorem cutFree₂ (M₀ : LMatch row col) (hnt : 3 ≤ Fintype.card K.U₁ + Fintype.card K.V₁)
    (hmin : ∀ R C, IsNontrivialShore row col R C →
      Fintype.card K.U₂ + Fintype.card K.V₂ ≤ R.card + C.card) :
    CutFree K.row₂ K.col₂ := by
  intro R C hK
  by_cases hm : Sum.inl () ∈ R
  · obtain ⟨R', C', h, hlt⟩ := K.shore_of_factor₂ hcov M₀ hnt (isNontrivialShore_compl.2 hK)
      (fun h => (mem_compl.1 h) hm)
    have := hmin R' C' h; omega
  · obtain ⟨R', C', h, hlt⟩ := K.shore_of_factor₂ hcov M₀ hnt hK hm
    have := hmin R' C' h; omega

/-! ### Occurrence degrees are preserved at non-marker vertices -/

theorem card_rowSet₁ (u : K.U₁) : (rowSet K.row₁ u).card = (rowSet row u.1).card := by
  refine Finset.card_bij (fun e _ => e.1) (fun e he => ?_) (fun _ _ _ _ h => Subtype.ext h)
    (fun e he => ?_)
  · exact mem_rowSet.2 (congrArg Subtype.val (mem_rowSet.1 he))
  · have hr : row e = u.1 := mem_rowSet.1 he
    exact ⟨⟨e, hr ▸ u.2⟩, mem_rowSet.2 (Subtype.ext hr), rfl⟩

theorem card_colSet₁ (w : K.V₁) :
    ((univ : Finset K.E₁).filter fun e => K.col₁ e = Sum.inl w).card =
      ((univ : Finset E).filter fun e => col e = w.1).card := by
  refine Finset.card_bij (fun e _ => e.1) (fun e he => ?_) (fun _ _ _ _ h => Subtype.ext h)
    (fun e he => ?_)
  · exact mem_filter.2 ⟨mem_univ _, K.col_of_col₁_eq_inl (mem_filter.1 he).2⟩
  · have hc : col e = w.1 := (mem_filter.1 he).2
    have hs : K.sC (col e) := hc ▸ w.2
    refine ⟨⟨e, K.back e hs⟩, mem_filter.2 ⟨mem_univ _, ?_⟩, rfl⟩
    unfold col₁; rw [dite_eq_left hs]; exact congrArg Sum.inl (Subtype.ext hc)

theorem card_rowSet₂ (u : K.U₂) :
    (rowSet K.row₂ (Sum.inr u)).card = (rowSet row u.1).card := by
  refine Finset.card_bij (fun e _ => e.1) (fun e he => ?_) (fun _ _ _ _ h => Subtype.ext h)
    (fun e he => ?_)
  · exact mem_rowSet.2 (K.row_of_row₂_eq_inr (mem_rowSet.1 he))
  · have hr : row e = u.1 := mem_rowSet.1 he
    have hns : ¬ K.sR (row e) := hr ▸ u.2
    have hnc : ¬ K.sC (col e) := fun h => hns (K.back e h)
    refine ⟨⟨e, hnc⟩, mem_rowSet.2 ?_, rfl⟩
    rw [K.row₂_of_not_sR (e := ⟨e, hnc⟩) hns]
    exact congrArg Sum.inr (Subtype.ext hr)

theorem card_colSet₂ (w : K.V₂) :
    ((univ : Finset K.E₂).filter fun e => K.col₂ e = w).card =
      ((univ : Finset E).filter fun e => col e = w.1).card := by
  refine Finset.card_bij (fun e _ => e.1) (fun e he => ?_) (fun _ _ _ _ h => Subtype.ext h)
    (fun e he => ?_)
  · exact mem_filter.2 ⟨mem_univ _, congrArg Subtype.val (mem_filter.1 he).2⟩
  · have hc : col e = w.1 := (mem_filter.1 he).2
    exact ⟨⟨e, hc ▸ w.2⟩, mem_filter.2 ⟨mem_univ _, Subtype.ext hc⟩, rfl⟩

end ShoreCut

variable (hbal : Fintype.card U = Fintype.card V)
  (hcov : ∀ e, ∃ M : LMatch row col, M.1 (row e) = e)

include hbal hcov in
/-- **Lavi Lemma 6.2 (minimum-shore leaf).**  Let `H` be a balanced core with
at least one occurrence (`[Nonempty E]`) in which every occurrence lies in a
perfect matching.  That holds for every FI core, but the implication is not
formalized: here it is the hypothesis `hcov`, which Section 7 obtains from a
positive law (`covered_of_positive_flow`).  If `H` has a nontrivial tight cut,
then
some oriented cut `K` of `H` has at least three vertices on each shore and
closes one of its shores to a leaf: `H₁` is cut-free or `H₂` is cut-free.

The cut is built from a nontrivial tight shore `X` of minimum cardinality, as
in the manuscript, and the cut-free factor is the closure of `X`; minimality
is used in the proof but is not part of the statement.  The two size bounds
say that the cut is nontrivial (the manuscript takes `X` to be a shore of a
nontrivial tight cut); with `ShoreCut.card` and `ShoreCut.card_V₂` they give
both closed factors, in particular the leaf, order at least two.  Non-marker
vertices keep their occurrence degrees (`ShoreCut.card_rowSet₁`,
`card_colSet₁`, `card_rowSet₂`, `card_colSet₂`, valid for every oriented
cut). -/
theorem lavi_lemma_6_2 [Nonempty E] (hex : ∃ R C, IsNontrivialShore row col R C) :
    ∃ K : ShoreCut row col,
      3 ≤ Fintype.card K.U₁ + Fintype.card K.V₁ ∧ 3 ≤ Fintype.card K.U₂ + Fintype.card K.V₂ ∧
        (CutFree K.row₁ K.col₁ ∨ CutFree K.row₂ K.col₂) := by
  classical
  have hP : ∃ n, ∃ R : Finset U, ∃ C : Finset V, IsNontrivialShore row col R C ∧
      R.card + C.card = n := by
    obtain ⟨R, C, h⟩ := hex; exact ⟨_, R, C, h, rfl⟩
  obtain ⟨R, C, hRC, hn⟩ := Nat.find_spec hP
  have hmin : ∀ R' C', IsNontrivialShore row col R' C' → R.card + C.card ≤ R'.card + C'.card :=
    fun R' C' h => hn ▸ Nat.find_min' hP ⟨R', C', h, rfl⟩
  obtain ⟨M₀, -⟩ := hcov (Classical.arbitrary E)
  obtain ⟨K, hK⟩ := exists_shoreCut_of_tight (· ∈ R) (· ∈ C) hbal hRC.1 hcov M₀
  refine ⟨K, ?_⟩
  have hfR : ∀ (p : U → Prop) [DecidablePred p], (∀ u, p u ↔ u ∈ R) →
      Fintype.card {u // p u} = R.card := fun p _ hp => by
    rw [Fintype.card_subtype, ← card_filter_mem R]; congr 1; ext u; simp [hp]
  have hfC : ∀ (p : V → Prop) [DecidablePred p], (∀ w, p w ↔ w ∈ C) →
      Fintype.card {w // p w} = C.card := fun p _ hp => by
    rw [Fintype.card_subtype, ← card_filter_mem C]; congr 1; ext w; simp [hp]
  have hfR' : ∀ (p : U → Prop) [DecidablePred p], (∀ u, p u ↔ u ∈ Rᶜ) →
      Fintype.card {u // p u} = Rᶜ.card := fun p _ hp => by
    rw [Fintype.card_subtype, ← card_filter_mem Rᶜ]; congr 1; ext u; simp [hp]
  have hfC' : ∀ (p : V → Prop) [DecidablePred p], (∀ w, p w ↔ w ∈ Cᶜ) →
      Fintype.card {w // p w} = Cᶜ.card := fun p _ hp => by
    rw [Fintype.card_subtype, ← card_filter_mem Cᶜ]; congr 1; ext w; simp [hp]
  rcases hK with ⟨hsR, hsC⟩ | ⟨hsR, hsC⟩
  · have h1 : Fintype.card K.U₁ = R.card := hfR _ fun u => by rw [hsR]
    have h2 : Fintype.card K.V₁ = C.card := hfC _ fun w => by rw [hsC]
    have h3 : Fintype.card K.U₂ = Rᶜ.card := hfR' _ fun u => by rw [hsR, mem_compl]
    have h4 : Fintype.card K.V₂ = Cᶜ.card := hfC' _ fun w => by rw [hsC, mem_compl]
    refine ⟨by rw [h1, h2]; exact hRC.2.1, by rw [h3, h4]; exact hRC.2.2, Or.inl ?_⟩
    refine K.cutFree₁ hcov M₀ (by rw [h3, h4]; exact hRC.2.2) fun R' C' h => ?_
    rw [h1, h2]; exact hmin R' C' h
  · have h1 : Fintype.card K.U₁ = Rᶜ.card := hfR' _ fun u => by rw [hsR, mem_compl]
    have h2 : Fintype.card K.V₁ = Cᶜ.card := hfC' _ fun w => by rw [hsC, mem_compl]
    have h3 : Fintype.card K.U₂ = R.card := hfR _ fun u => by rw [hsR, not_not]
    have h4 : Fintype.card K.V₂ = C.card := hfC _ fun w => by rw [hsC, not_not]
    refine ⟨by rw [h1, h2]; exact hRC.2.2, by rw [h3, h4]; exact hRC.2.1, Or.inr ?_⟩
    refine K.cutFree₂ hcov M₀ (by rw [h1, h2]; exact hRC.2.2) fun R' C' h => ?_
    rw [h3, h4]; exact hmin R' C' h

end MinShore

end LaviSection2
