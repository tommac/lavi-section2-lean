import LaviSection2.LaviOccurrenceCore

/-!
# Lavi Lemma 2.5: canonical expansions

This module proves the "converse" parts of Lavi's Lemma 2.5.

* `nearlyDecomposableOn_expAdj`: an expansion `D(H, L)` of an FI core is
  nearly decomposable whenever every direct occurrence is essential and has
  no parallel occurrence.
* `nearlyDecomposableOn_canonicalAdj`: the canonical expansion `D_can(H)` of
  every FI core (excluding the order-one, one-occurrence core) is nearly
  decomposable.
* `contractColumn_private_iff`: contracting `D(H, L)` at the private column
  `c_e` of a long occurrence `e` gives `D(H, L \ {e})`, up to relabelling.
* `privateContraction_canonical`: if `H` has minimum occurrence degree at
  least three, every private-column contraction of `D_can(H)` is fully
  indecomposable but not nearly decomposable.
-/

namespace LaviSection2

open Finset

section Generic

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- A row with at most one neighbor violates strict Hall (order at least two). -/
theorem not_strictHallOn_of_row_single (S : α → β → Prop) (h2 : 2 ≤ Fintype.card α)
    (x : α) (y : β) (hx : ∀ j, S x j → j = y) : ¬StrictHallOn S := by
  classical
  intro hH
  have h := hH {x} (Finset.singleton_nonempty x) (by rw [Finset.card_singleton]; omega)
  have hsub : rowNeighborsOn S {x} ⊆ {y} := by
    intro j hj
    obtain ⟨i, hi, hij⟩ := mem_rowNeighborsOn.1 hj
    rw [Finset.mem_singleton.1 hi] at hij
    exact Finset.mem_singleton.2 (hx j hij)
  have := Finset.card_le_card hsub
  rw [Finset.card_singleton] at h this
  omega

/-- A column with at most one neighbor violates strict Hall (balanced, order ≥ 2). -/
theorem not_strictHallOn_of_column_single (S : α → β → Prop)
    (hcard : Fintype.card α = Fintype.card β) (h2 : 2 ≤ Fintype.card α)
    (y : β) (x : α) (hy : ∀ i, S i y → i = x) : ¬StrictHallOn S := by
  classical
  intro hH
  have hR : (Finset.univ.erase x).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ]
    omega
  have hRc : (Finset.univ.erase x).card = Fintype.card α - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ]
  have h := hH _ hR (by rw [hRc]; omega)
  have hsub : rowNeighborsOn S (Finset.univ.erase x) ⊆ Finset.univ.erase y := by
    intro j hj
    obtain ⟨i, hi, hij⟩ := mem_rowNeighborsOn.1 hj
    refine Finset.mem_erase.2 ⟨?_, Finset.mem_univ j⟩
    rintro rfl
    exact (Finset.mem_erase.1 hi).1 (hy i hij)
  have := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_univ y), Finset.card_univ] at this
  omega

/-- Strict Hall of a support pointwise equivalent to another. -/
theorem strictHallOn_congr {S T : α → β → Prop} (h : ∀ a b, S a b ↔ T a b) :
    StrictHallOn S ↔ StrictHallOn T :=
  strictHallOn_relabel_iff (Equiv.refl α) (Equiv.refl β) h

end Generic

section Expansion

variable {U V E : Type*} [Fintype U] [Fintype V] [Fintype E]
  [DecidableEq U] [DecidableEq V] [DecidableEq E]
variable {row : E → U} {col : E → V}

/-- Two parallel occurrences: deleting one of them keeps an FI core FI. -/
theorem coreFI_erase_of_parallel {O : Finset E} (hO : CoreFI row col O) {d e : E}
    (hd : d ∈ O) (he : e ∈ O) (hed : e ≠ d) (hpar : row e = row d ∧ col e = col d) :
    CoreFI row col (O.erase d) := by
  have hadj : ∀ u v, coreAdj row col (O.erase d) u v ↔ coreAdj row col O u v := by
    intro u v
    constructor
    · rintro ⟨f, hf, h⟩
      exact ⟨f, Finset.mem_of_mem_erase hf, h⟩
    · rintro ⟨f, hf, h⟩
      by_cases hfd : f = d
      · subst hfd
        exact ⟨e, Finset.mem_erase.2 ⟨hed, he⟩, hpar.1.trans h.1, hpar.2.trans h.2⟩
      · exact ⟨f, Finset.mem_erase.2 ⟨hfd, hf⟩, h⟩
  refine ⟨(strictHallOn_congr hadj).2 hO.1, fun u => ?_⟩
  obtain ⟨f, hf, hfu⟩ := hO.2 u
  by_cases hfd : f = d
  · subst hfd
    exact ⟨e, Finset.mem_erase.2 ⟨hed, he⟩, hpar.1.trans hfu⟩
  · exact ⟨f, Finset.mem_erase.2 ⟨hfd, hf⟩, hfu⟩

/-- Minimum occurrence degree three leaves at least two occurrences per
column after deleting one occurrence. -/
theorem colOcc_erase_two {O : Finset E} (hmin : MinOccDegreeThree row col O) (d : E)
    (v : V) : 2 ≤ (colOcc col (O.erase d) v).card := by
  have h := hmin.2 v
  have hsub : (colOcc col O v).erase d ⊆ colOcc col (O.erase d) v := by
    intro e he
    obtain ⟨hed, he'⟩ := Finset.mem_erase.1 he
    rw [colOcc, Finset.mem_filter] at he' ⊢
    exact ⟨Finset.mem_erase.2 ⟨hed, he'.1⟩, he'.2⟩
  have := Finset.card_le_card hsub
  have := Finset.pred_card_le_card_erase (s := colOcc col O v) (a := d)
  omega

/-- In a balanced FI core of order at least two, every column carries at least
two occurrences. -/
theorem colOcc_two_of_coreFI {O : Finset E} (hbal : Fintype.card U = Fintype.card V)
    (hO : CoreFI row col O) (h2 : 2 ≤ Fintype.card U) (v : V) :
    2 ≤ (colOcc col O v).card := by
  classical
  have hT := (strictHallOn_transpose_iff hbal (coreAdj row col O)).2 hO.1
  have h := hT {v} (Finset.singleton_nonempty v) (by rw [Finset.card_singleton]; omega)
  rw [Finset.card_singleton] at h
  have hsub : rowNeighborsOn (fun j i => coreAdj row col O i j) {v} ⊆
      (colOcc col O v).image row := by
    intro u hu
    obtain ⟨w, hw, e, he, hrow, hcol⟩ := mem_rowNeighborsOn.1 hu
    rw [Finset.mem_singleton.1 hw] at hcol
    exact Finset.mem_image.2 ⟨e, by rw [colOcc, Finset.mem_filter]; exact ⟨he, hcol⟩, hrow⟩
  have := (Finset.card_le_card hsub).trans Finset.card_image_le
  omega

variable (O L : Finset E)

/-- Deleting the support edge of a direct occurrence `d` with no other direct
occurrence in parallel gives the expansion of `H - d`. -/
theorem deleteEdgeOn_expAdj_direct {d : E} (hd : d ∈ O) (hdL : d ∉ L)
    (hpar : ∀ e ∈ O, e ∉ L → e ≠ d → ¬(row e = row d ∧ col e = col d))
    (x : U ⊕ L) (y : V ⊕ L) :
    deleteEdgeOn (expAdj row col O L) (Sum.inl (row d)) (Sum.inl (col d)) x y ↔
      expAdj row col (O.erase d) L x y := by
  rcases x with u | e <;> rcases y with v | e'
  · simp only [deleteEdgeOn, expAdj, Sum.inl.injEq]
    constructor
    · rintro ⟨⟨e, he, heL, hrow, hcol⟩, hnot⟩
      refine ⟨e, Finset.mem_erase.2 ⟨?_, he⟩, heL, hrow, hcol⟩
      rintro rfl
      exact hnot ⟨hrow.symm, hcol.symm⟩
    · rintro ⟨e, he, heL, hrow, hcol⟩
      obtain ⟨hed, he'⟩ := Finset.mem_erase.1 he
      refine ⟨⟨e, he', heL, hrow, hcol⟩, ?_⟩
      rintro ⟨rfl, rfl⟩
      exact hpar e he' heL hed ⟨hrow, hcol⟩
  · simp [deleteEdgeOn, expAdj]
  · simp [deleteEdgeOn, expAdj]
  · simp [deleteEdgeOn, expAdj]

/--
An expansion of a balanced FI core is nearly decomposable when every direct
occurrence is essential and has no parallel occurrence.
-/
theorem nearlyDecomposableOn_expAdj (hbal : Fintype.card U = Fintype.card V)
    (hL : L ⊆ O) (hO : CoreFI row col O) (hcol2 : ∀ v, 2 ≤ (colOcc col O v).card)
    (h2 : 2 ≤ Fintype.card (U ⊕ L))
    (hess : ∀ d ∈ O, d ∉ L → ¬CoreFI row col (O.erase d))
    (hpar : ∀ d ∈ O, d ∉ L → ∀ e ∈ O, e ≠ d → ¬(row e = row d ∧ col e = col d)) :
    NearlyDecomposableOn (expAdj row col O L) := by
  classical
  have hcardUL : Fintype.card (U ⊕ L) = Fintype.card (V ⊕ L) := by
    rw [Fintype.card_sum, Fintype.card_sum, hbal]
  refine ⟨strictHallOn_expAdj O L hbal hL hO.1 hcol2, ?_⟩
  intro x y hxy
  rcases x with u | e <;> rcases y with v | e'
  · -- A direct edge.
    obtain ⟨d, hd, hdL, hrow, hcol⟩ := hxy
    subst hrow hcol
    intro hdel
    have hdel' := (strictHallOn_congr
      (deleteEdgeOn_expAdj_direct O L hd hdL
        (fun e he heL hed => hpar d hd hdL e he hed))).1 hdel
    have hL' : L ⊆ O.erase d := fun f hf =>
      Finset.mem_erase.2 ⟨fun h => hdL (h ▸ hf), hL hf⟩
    exact hess d hd hdL (coreFI_of_expAdj (O.erase d) L hL' h2 hdel')
  · -- The edge `u - c_e'`: afterwards `c_e'` meets only `r_e'`.
    refine not_strictHallOn_of_column_single _ hcardUL h2 (Sum.inr e') (Sum.inr e') ?_
    intro i hi
    rcases i with u' | f
    · exact (hi.2 ⟨congrArg Sum.inl ((hi.1 : row e'.1 = u').symm.trans hxy), rfl⟩).elim
    · exact congrArg Sum.inr (hi.1 : f = e')
  · -- The edge `r_e - col e`: afterwards `r_e` meets only `c_e`.
    refine not_strictHallOn_of_row_single _ h2 (Sum.inr e) (Sum.inr e) ?_
    intro j hj
    rcases j with v' | f
    · exact (hj.2 ⟨rfl, congrArg Sum.inl ((hj.1 : col e.1 = v').symm.trans hxy)⟩).elim
    · exact congrArg Sum.inr (hj.1 : e = f).symm
  · -- The edge `r_e - c_e'` (so `e = e'`): afterwards `r_e` meets only `col e`.
    refine not_strictHallOn_of_row_single _ h2 (Sum.inr e) (Sum.inl (col e.1)) ?_
    intro j hj
    rcases j with v' | f
    · exact congrArg Sum.inl (hj.1 : col e.1 = v').symm
    · exact (hj.2 ⟨rfl, congrArg Sum.inr ((hj.1 : e = f).symm.trans hxy)⟩).elim

/--
Lavi Lemma 2.5, converse part: the canonical expansion of a balanced FI core
is nearly decomposable.  The hypothesis `hcol2` excludes only the order-one
core with a single occurrence (see `colOcc_two_of_coreFI`), and `h2` asks for
order at least two.
-/
theorem nearlyDecomposableOn_canonicalAdj (hbal : Fintype.card U = Fintype.card V)
    (hO : CoreFI row col O) (hcol2 : ∀ v, 2 ≤ (colOcc col O v).card)
    (h2 : 2 ≤ Fintype.card (U ⊕ removableSet row col O)) :
    NearlyDecomposableOn (canonicalAdj row col O) := by
  classical
  have hL : removableSet row col O ⊆ O := fun e he => ((mem_removableSet row col).1 he).1
  refine nearlyDecomposableOn_expAdj O _ hbal hL hO hcol2 h2 ?_ ?_
  · intro d hd hdL hFI
    exact hdL ((mem_removableSet row col).2 ⟨hd, hFI⟩)
  · intro d hd hdL e he hed hp
    exact hdL ((mem_removableSet row col).2 ⟨hd, coreFI_erase_of_parallel hO hd he hed hp⟩)

end Expansion

section PrivateContraction

variable {U V E : Type*} [Fintype U] [Fintype V] [Fintype E]
  [DecidableEq U] [DecidableEq V] [DecidableEq E]
variable {row : E → U} {col : E → V}

/-- Removing the private vertex of `e₀` from `W ⊕ L`. -/
def dropInrEquiv (W : Type*) {L : Finset E} {e₀ : E} (he₀ : e₀ ∈ L) :
    {x : W ⊕ L // x ≠ Sum.inr ⟨e₀, he₀⟩} ≃ W ⊕ (L.erase e₀) where
  toFun x := match x with
    | ⟨Sum.inl w, _⟩ => Sum.inl w
    | ⟨Sum.inr e, h⟩ => Sum.inr ⟨e.1, Finset.mem_erase.2
        ⟨fun h' => h (congrArg Sum.inr (Subtype.ext h')), e.2⟩⟩
  invFun y := match y with
    | Sum.inl w => ⟨Sum.inl w, Sum.inl_ne_inr⟩
    | Sum.inr e => ⟨Sum.inr ⟨e.1, Finset.mem_of_mem_erase e.2⟩, fun h =>
        (Finset.mem_erase.1 e.2).1 (congrArg Subtype.val (Sum.inr_injective h))⟩
  left_inv := by rintro ⟨w | e, h⟩ <;> rfl
  right_inv := by rintro (w | e) <;> rfl

variable (O L : Finset E)

/--
Contracting `D(H, L)` at the private column of a long occurrence `e₀` (merging
the private row into `row e₀`) gives `D(H, L \ {e₀})`, up to relabelling.
-/
theorem contractColumn_private_iff (hL : L ⊆ O) {e₀ : E} (he₀ : e₀ ∈ L)
    (x : {x : U ⊕ L // x ≠ Sum.inr ⟨e₀, he₀⟩})
    (y : {y : V ⊕ L // y ≠ Sum.inr ⟨e₀, he₀⟩}) :
    contractColumn (expAdj row col O L) (Sum.inl (row e₀)) (Sum.inr ⟨e₀, he₀⟩)
        (Sum.inr ⟨e₀, he₀⟩) x y ↔
      expAdj row col O (L.erase e₀) (dropInrEquiv U he₀ x) (dropInrEquiv V he₀ y) := by
  classical
  have hnotL : ∀ e, e ∉ L.erase e₀ ↔ e = e₀ ∨ e ∉ L := by
    intro e
    rw [Finset.mem_erase]
    tauto
  rcases x with ⟨u | e, hx⟩ <;> rcases y with ⟨v | e', hy⟩
  · by_cases hu : u = row e₀
    · subst hu
      simp only [contractColumn, ite_true, dropInrEquiv, Equiv.coe_fn_mk, expAdj]
      constructor
      · rintro (⟨e, he, heL, h1, h2⟩ | h)
        · exact ⟨e, he, (hnotL e).2 (Or.inr heL), h1, h2⟩
        · exact ⟨e₀, hL he₀, (hnotL e₀).2 (Or.inl rfl), rfl, h⟩
      · rintro ⟨e, he, heL, h1, h2⟩
        rcases (hnotL e).1 heL with rfl | heL'
        · exact Or.inr h2
        · exact Or.inl ⟨e, he, heL', h1, h2⟩
    · have hne : (Sum.inl u : U ⊕ L) ≠ Sum.inl (row e₀) := fun h => hu (Sum.inl_injective h)
      simp only [contractColumn, hne, ite_false, dropInrEquiv, Equiv.coe_fn_mk, expAdj]
      constructor
      · rintro ⟨e, he, heL, h1, h2⟩
        exact ⟨e, he, (hnotL e).2 (Or.inr heL), h1, h2⟩
      · rintro ⟨e, he, heL, h1, h2⟩
        rcases (hnotL e).1 heL with rfl | heL'
        · exact absurd h1.symm hu
        · exact ⟨e, he, heL', h1, h2⟩
  · have hne' : e' ≠ ⟨e₀, he₀⟩ := fun h => hy (congrArg Sum.inr h)
    by_cases hu : u = row e₀
    · subst hu
      simp only [contractColumn, ite_true, dropInrEquiv, Equiv.coe_fn_mk, expAdj]
      constructor
      · rintro (h | h)
        · exact h
        · exact absurd h.symm hne'
      · exact Or.inl
    · have hne : (Sum.inl u : U ⊕ L) ≠ Sum.inl (row e₀) := fun h => hu (Sum.inl_injective h)
      simp only [contractColumn, hne, ite_false, dropInrEquiv, Equiv.coe_fn_mk, expAdj]
  · simp only [contractColumn, reduceCtorEq, ite_false, dropInrEquiv, Equiv.coe_fn_mk, expAdj]
  · simp only [contractColumn, reduceCtorEq, ite_false, dropInrEquiv, Equiv.coe_fn_mk, expAdj]
    constructor
    · rintro rfl
      rfl
    · intro h
      apply Subtype.ext
      have := congrArg (fun z : ↥(L.erase e₀) => (z : E)) h
      simpa using this

/-- The private column of a long occurrence meets exactly its hub row and its
private row. -/
theorem expAdj_private_column {e₀ : E} (he₀ : e₀ ∈ L) (i : U ⊕ L) :
    expAdj row col O L i (Sum.inr ⟨e₀, he₀⟩) ↔
      i = Sum.inl (row e₀) ∨ i = Sum.inr ⟨e₀, he₀⟩ := by
  rcases i with u | f
  · simp only [expAdj, Sum.inl.injEq, reduceCtorEq, or_false]
    exact eq_comm
  · simp only [expAdj, reduceCtorEq, Sum.inr.injEq, false_or]

/--
Private-column contraction of a general expansion: if `e₀ ∈ L` is removable
and no direct occurrence is parallel to it, the contraction at its private
column is fully indecomposable but not nearly decomposable.
-/
theorem privateContraction_expAdj (hbal : Fintype.card U = Fintype.card V)
    (hL : L ⊆ O) (hO : CoreFI row col O) (hmin : MinOccDegreeThree row col O) {e₀ : E}
    (he₀ : e₀ ∈ L) (hrem₀ : CoreFI row col (O.erase e₀))
    (hparL : ∀ e ∈ O, e ∉ L → e ≠ e₀ → ¬(row e = row e₀ ∧ col e = col e₀)) :
    StrictHallOn (contractColumn (expAdj row col O L) (Sum.inl (row e₀))
        (Sum.inr ⟨e₀, he₀⟩) (Sum.inr ⟨e₀, he₀⟩)) ∧
      ¬NearlyDecomposableOn (contractColumn (expAdj row col O L) (Sum.inl (row e₀))
        (Sum.inr ⟨e₀, he₀⟩) (Sum.inr ⟨e₀, he₀⟩)) := by
  classical
  have hcol2 : ∀ v, 2 ≤ (colOcc col O v).card := fun v => (hmin.2 v).trans' (by norm_num)
  have hD : StrictHallOn (expAdj row col O L) := strictHallOn_expAdj O L hbal hL hO.1 hcol2
  refine ⟨strictHallOn_contractColumn _ Sum.inl_ne_inr (expAdj_private_column O L he₀) hD, ?_⟩
  intro hND
  have hND' := (nearlyDecomposableOn_relabel_iff (dropInrEquiv U he₀) (dropInrEquiv V he₀)
    (contractColumn_private_iff O L hL he₀)).1 hND
  have he₀O : e₀ ∈ O := hL he₀
  have hnot : e₀ ∉ L.erase e₀ := Finset.notMem_erase e₀ L
  have hpar : ∀ e ∈ O, e ∉ L.erase e₀ → e ≠ e₀ → ¬(row e = row e₀ ∧ col e = col e₀) := by
    intro e he heL hee
    exact hparL e he (fun h => heL (Finset.mem_erase.2 ⟨hee, h⟩)) hee
  apply hND'.2 (Sum.inl (row e₀)) (Sum.inl (col e₀)) ⟨e₀, he₀O, hnot, rfl, rfl⟩
  refine (strictHallOn_congr (deleteEdgeOn_expAdj_direct O (L.erase e₀) he₀O hnot hpar)).2 ?_
  exact strictHallOn_expAdj (O.erase e₀) (L.erase e₀) hbal (Finset.erase_subset_erase e₀ hL)
    hrem₀.1 (colOcc_erase_two hmin e₀)

/-- In the canonical expansion, no direct occurrence is parallel to a long one. -/
theorem canonical_no_direct_parallel (hO : CoreFI row col O) {e₀ : E}
    (he₀ : e₀ ∈ removableSet row col O) :
    ∀ e ∈ O, e ∉ removableSet row col O → e ≠ e₀ →
      ¬(row e = row e₀ ∧ col e = col e₀) := by
  intro e he heL hee hp
  exact heL ((mem_removableSet row col).2 ⟨he, coreFI_erase_of_parallel hO he
    ((mem_removableSet row col).1 he₀).1 (Ne.symm hee) ⟨hp.1.symm, hp.2.symm⟩⟩)

/--
Lavi Lemma 2.5, last assertion (private columns): if `H` has minimum
occurrence degree at least three, contracting `D_can(H)` at the private
column of any long occurrence gives a fully indecomposable support that is
not nearly decomposable.
-/
theorem privateContraction_canonical (hbal : Fintype.card U = Fintype.card V)
    (hO : CoreFI row col O) (hmin : MinOccDegreeThree row col O) {e₀ : E}
    (he₀ : e₀ ∈ removableSet row col O) :
    StrictHallOn (contractColumn (canonicalAdj row col O) (Sum.inl (row e₀))
        (Sum.inr ⟨e₀, he₀⟩) (Sum.inr ⟨e₀, he₀⟩)) ∧
      ¬NearlyDecomposableOn (contractColumn (canonicalAdj row col O) (Sum.inl (row e₀))
        (Sum.inr ⟨e₀, he₀⟩) (Sum.inr ⟨e₀, he₀⟩)) :=
  privateContraction_expAdj O _ hbal (fun e he => ((mem_removableSet row col).1 he).1) hO hmin
    he₀ ((mem_removableSet row col).1 he₀).2 (canonical_no_direct_parallel O hO he₀)

/--
For the classification: if `D(H, L)` is nearly decomposable and every
direct occurrence has no parallel occurrence, then every direct occurrence is
essential.
-/
theorem direct_essential_of_nearlyDecomposableOn (hbal : Fintype.card U = Fintype.card V)
    (hL : L ⊆ O) (hmin : MinOccDegreeThree row col O)
    (hND : NearlyDecomposableOn (expAdj row col O L))
    (hpar : ∀ d ∈ O, d ∉ L → ∀ e ∈ O, e ≠ d → ¬(row e = row d ∧ col e = col d)) :
    ∀ d ∈ O, d ∉ L → ¬CoreFI row col (O.erase d) := by
  intro d hd hdL hFI
  have hL' : L ⊆ O.erase d := fun f hf => Finset.mem_erase.2 ⟨fun h => hdL (h ▸ hf), hL hf⟩
  apply hND.2 (Sum.inl (row d)) (Sum.inl (col d)) ⟨d, hd, hdL, rfl, rfl⟩
  refine (strictHallOn_congr (deleteEdgeOn_expAdj_direct O L hd hdL
    (fun e he _ hed => hpar d hd hdL e he hed))).2 ?_
  exact strictHallOn_expAdj (O.erase d) L hbal hL' hFI.1 (colOcc_erase_two hmin d)

/--
For the classification: if every direct occurrence is essential and
unparallelled, and a long occurrence `e₀` is essential, then contracting at
its private column gives a nearly decomposable support.
-/
theorem nearlyDecomposableOn_privateContraction_of_essential
    (hbal : Fintype.card U = Fintype.card V) (hL : L ⊆ O) (hO : CoreFI row col O)
    (hmin : MinOccDegreeThree row col O)
    (hess : ∀ d ∈ O, d ∉ L → ¬CoreFI row col (O.erase d))
    (hpar : ∀ d ∈ O, d ∉ L → ∀ e ∈ O, e ≠ d → ¬(row e = row d ∧ col e = col d))
    {e₀ : E} (he₀ : e₀ ∈ L) (hess₀ : ¬CoreFI row col (O.erase e₀))
    (h2 : 2 ≤ Fintype.card (U ⊕ (L.erase e₀))) :
    NearlyDecomposableOn (contractColumn (expAdj row col O L) (Sum.inl (row e₀))
      (Sum.inr ⟨e₀, he₀⟩) (Sum.inr ⟨e₀, he₀⟩)) := by
  classical
  rw [nearlyDecomposableOn_relabel_iff (dropInrEquiv U he₀) (dropInrEquiv V he₀)
    (contractColumn_private_iff O L hL he₀)]
  have hcol2 : ∀ v, 2 ≤ (colOcc col O v).card := fun v => (hmin.2 v).trans' (by norm_num)
  have he₀O : e₀ ∈ O := hL he₀
  refine nearlyDecomposableOn_expAdj O (L.erase e₀) hbal ((Finset.erase_subset e₀ L).trans hL)
    hO hcol2 h2 ?_ ?_
  · intro d hd hdL
    by_cases hde : d = e₀
    · subst hde
      exact hess₀
    · exact hess d hd (fun h => hdL (Finset.mem_erase.2 ⟨hde, h⟩))
  · intro d hd hdL e he hed hp
    by_cases hde : d = e₀
    · subst hde
      exact hess₀ (coreFI_erase_of_parallel hO hd he hed hp)
    · exact hpar d hd (fun h => hdL (Finset.mem_erase.2 ⟨hde, h⟩)) e he hed hp

end PrivateContraction

section RelabelContraction

variable {α β α' β' : Type*} [Fintype α] [Fintype β] [Fintype α'] [Fintype β']
  [DecidableEq α] [DecidableEq β] [DecidableEq α'] [DecidableEq β']

/-- An equivalence restricted to the complements of a point and its image. -/
def dropEquiv (e : α ≃ α') (s : α) : Drop s ≃ Drop (e s) :=
  e.subtypeEquiv fun a => e.injective.ne_iff.symm

/-- Contraction commutes with relabelling. -/
theorem contractColumn_relabel (eα : α ≃ α') (eβ : β ≃ β')
    {S : α → β → Prop} {T : α' → β' → Prop} (h : ∀ a b, S a b ↔ T (eα a) (eβ b))
    (r s : α) (c : β) (x : Drop s) (y : Drop c) :
    contractColumn S r s c x y ↔
      contractColumn T (eα r) (eα s) (eβ c) (dropEquiv eα s x) (dropEquiv eβ c y) := by
  simp only [contractColumn, dropEquiv, Equiv.subtypeEquiv_apply, eα.injective.eq_iff]
  split_ifs <;> simp [h]

/-- Column degree is invariant under relabelling. -/
theorem columnDegreeOn_relabel (eα : α ≃ α') (eβ : β ≃ β')
    {S : α → β → Prop} {T : α' → β' → Prop} (h : ∀ a b, S a b ↔ T (eα a) (eβ b)) (c : β) :
    columnDegreeOn S c = columnDegreeOn T (eβ c) := by
  classical
  unfold columnDegreeOn
  have := rowNeighborsOn_relabel eβ eα (S := fun j i => S i j) (T := fun j i => T i j)
    (fun b a => h a b) {c}
  rw [Finset.map_singleton, Equiv.coe_toEmbedding] at this
  rw [this, Finset.card_map]

end RelabelContraction

section Transpose

variable {U V E : Type*} [Fintype U] [Fintype V] [Fintype E]
  [DecidableEq U] [DecidableEq V] [DecidableEq E]
variable {row : E → U} {col : E → V}

/-- Full indecomposability of a balanced core does not depend on orientation. -/
theorem coreFI_transpose (hbal : Fintype.card U = Fintype.card V) {O : Finset E}
    (hO : CoreFI row col O) : CoreFI col row O := by
  classical
  have hadj : ∀ v u, coreAdj col row O v u ↔ coreAdj row col O u v := by
    intro v u
    constructor <;> rintro ⟨e, he, h1, h2⟩ <;> exact ⟨e, he, h2, h1⟩
  have hT : StrictHallOn (coreAdj col row O) :=
    (strictHallOn_congr hadj).2 ((strictHallOn_transpose_iff hbal _).2 hO.1)
  refine ⟨hT, fun v => ?_⟩
  rcases Nat.lt_or_ge (Fintype.card U) 2 with hsmall | hbig
  · have hU : Nonempty U := by
      rw [← Fintype.card_pos_iff, hbal]
      exact Fintype.card_pos_iff.2 ⟨v⟩
    obtain ⟨u⟩ := hU
    obtain ⟨e, he, _⟩ := hO.2 u
    have hsub : Subsingleton V := Fintype.card_le_one_iff_subsingleton.1 (by omega)
    exact ⟨e, he, Subsingleton.elim _ _⟩
  · have h := colOcc_two_of_coreFI hbal hO hbig v
    obtain ⟨e, he⟩ := Finset.card_pos.1 (by omega : 0 < (colOcc col O v).card)
    rw [colOcc, Finset.mem_filter] at he
    exact ⟨e, he.1, he.2⟩

theorem coreFI_transpose_iff (hbal : Fintype.card U = Fintype.card V) {O : Finset E} :
    CoreFI col row O ↔ CoreFI row col O :=
  ⟨coreFI_transpose hbal.symm, coreFI_transpose hbal⟩

theorem removableSet_transpose (hbal : Fintype.card U = Fintype.card V) (O : Finset E) :
    removableSet col row O = removableSet row col O := by
  ext e
  rw [mem_removableSet, mem_removableSet, coreFI_transpose_iff hbal]

/-- Contraction is unchanged by replacing the support with a pointwise
equivalent one. -/
theorem nearlyDecomposableOn_contractColumn_congr {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] {S T : α → β → Prop} (h : ∀ a b, S a b ↔ T a b)
    (r s : α) (c : β) :
    NearlyDecomposableOn (contractColumn S r s c) ↔
      NearlyDecomposableOn (contractColumn T r s c) := by
  refine nearlyDecomposableOn_relabel_iff (Equiv.refl _) (Equiv.refl _) fun x y => ?_
  simp only [contractColumn, Equiv.refl_apply, h]
  exact Iff.rfl

theorem strictHallOn_contractColumn_congr {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] {S T : α → β → Prop} (h : ∀ a b, S a b ↔ T a b)
    (r s : α) (c : β) :
    StrictHallOn (contractColumn S r s c) ↔ StrictHallOn (contractColumn T r s c) := by
  refine strictHallOn_congr fun x y => ?_
  simp only [contractColumn, h]

/--
Lavi Lemma 2.5, last assertion (private rows): if `H` has minimum occurrence
degree at least three, contracting `D_can(H)` at the private row of any long
occurrence gives a fully indecomposable support that is not nearly
decomposable.
-/
theorem privateRowContraction_canonical (hbal : Fintype.card U = Fintype.card V)
    {O : Finset E} (hO : CoreFI row col O) (hmin : MinOccDegreeThree row col O) {e₀ : E}
    (he₀ : e₀ ∈ removableSet row col O) :
    StrictHallOn (contractRow (canonicalAdj row col O) (Sum.inr ⟨e₀, he₀⟩)
        (Sum.inl (col e₀)) (Sum.inr ⟨e₀, he₀⟩)) ∧
      ¬NearlyDecomposableOn (contractRow (canonicalAdj row col O) (Sum.inr ⟨e₀, he₀⟩)
        (Sum.inl (col e₀)) (Sum.inr ⟨e₀, he₀⟩)) := by
  classical
  set L := removableSet row col O
  have hL : L ⊆ O := fun e he => ((mem_removableSet row col).1 he).1
  have hrem₀ := ((mem_removableSet row col).1 he₀).2
  have hpar := canonical_no_direct_parallel O hO he₀
  -- The column result for the transposed core, with the same long set `L`.
  have hB := privateContraction_expAdj (row := col) (col := row) O L hbal.symm hL
    (coreFI_transpose hbal hO) ⟨hmin.2, hmin.1⟩ he₀ (coreFI_transpose hbal hrem₀)
    (fun e he heL hee hp => hpar e he heL hee ⟨hp.2, hp.1⟩)
  let ST : V ⊕ L → U ⊕ L → Prop := fun j i => expAdj row col O L i j
  have hST : ∀ j i, expAdj col row O L j i ↔ ST j i := fun j i => expAdj_transpose O L i j
  have hdrop : Fintype.card {y : V ⊕ L // y ≠ Sum.inr ⟨e₀, he₀⟩} =
      Fintype.card {x : U ⊕ L // x ≠ Sum.inr ⟨e₀, he₀⟩} := by
    have h1 : Fintype.card {y : V ⊕ L // y ≠ Sum.inr ⟨e₀, he₀⟩} = Fintype.card (V ⊕ L) - 1 :=
      Set.card_ne_eq _
    have h2 : Fintype.card {x : U ⊕ L // x ≠ Sum.inr ⟨e₀, he₀⟩} = Fintype.card (U ⊕ L) - 1 :=
      Set.card_ne_eq _
    rw [h1, h2, Fintype.card_sum, Fintype.card_sum, hbal]
  have hH := (strictHallOn_contractColumn_congr hST _ _ _).1 hB.1
  have hN : ¬NearlyDecomposableOn (contractColumn ST (Sum.inl (col e₀))
      (Sum.inr ⟨e₀, he₀⟩) (Sum.inr ⟨e₀, he₀⟩)) := fun h =>
    hB.2 ((nearlyDecomposableOn_contractColumn_congr hST _ _ _).2 h)
  refine ⟨?_, ?_⟩
  · exact (strictHallOn_transpose_iff hdrop _).2 hH
  · intro h
    exact hN ((nearlyDecomposableOn_transpose_iff hdrop _).1 h)

end Transpose

end LaviSection2
