import LaviSection2.LaviStrictHall

/-!
# Lavi Lemma 2.3: no four-cycles

This module formalizes the strict-Hall/submodularity proof that a nearly
decomposable support of order at least three contains no bipartite four-cycle.
-/

namespace LaviSection2

/-- Four distinct corners forming a `K₂,₂` in a support. -/
def HasFourCycle {n : ℕ} (S : Fin n → Fin n → Prop) : Prop :=
  ∃ r s c d, r ≠ s ∧ c ≠ d ∧ S r c ∧ S r d ∧ S s c ∧ S s d

/--
The core submodularity argument in Lemma 2.3: if deleting both edges from one
row into a four-cycle pair violates strict Hall, that row has exactly those two
neighbors.
-/
theorem rowNeighbors_singleton_eq_pair_of_delete_failures {n : ℕ}
    {S : Fin n → Fin n → Prop} (hHall : StrictHall S)
    {r s c d : Fin n} (hrs : r ≠ s) (hcd : c ≠ d)
    (hrc : S r c) (hrd : S r d) (hsc : S s c) (hsd : S s d)
    (hdelc : ¬StrictHall (deleteEdge S r c))
    (hdeld : ¬StrictHall (deleteEdge S r d)) :
    rowNeighbors S {r} = {c, d} := by
  classical
  obtain ⟨Sc, hSc, hScproper, hrSc, hScTight, _, hcOnly⟩ :=
    exists_tight_witness_of_delete_not_strictHall hHall hdelc
  obtain ⟨Sd, hSd, hSdproper, hrSd, hSdTight, _, hdOnly⟩ :=
    exists_tight_witness_of_delete_not_strictHall hHall hdeld
  have hsNotSc : s ∉ Sc := by
    intro hsSc
    exact hrs (hcOnly s hsSc hsc).symm
  have hsNotSd : s ∉ Sd := by
    intro hsSd
    exact hrs (hdOnly s hsSd hsd).symm
  let T := Sc ∩ Sd
  let U := Sc ∪ Sd
  have hrT : r ∈ T := Finset.mem_inter.mpr ⟨hrSc, hrSd⟩
  have hT : T.Nonempty := ⟨r, hrT⟩
  have hrU : r ∈ U := Finset.mem_union.mpr (Or.inl hrSc)
  have hU : U.Nonempty := ⟨r, hrU⟩
  have hsNotU : s ∉ U := by
    simp only [U, Finset.mem_union, not_or]
    exact ⟨hsNotSc, hsNotSd⟩
  have hUproper : U.card < n := by
    have hssub : U ⊂ (Finset.univ : Finset (Fin n)) := by
      apply Finset.ssubset_iff.mpr
      exact ⟨s, hsNotU, Finset.insert_subset_iff.mpr
        ⟨Finset.mem_univ s, Finset.subset_univ U⟩⟩
    simpa using Finset.card_lt_card hssub
  have hTproper : T.card < n := by
    have hTU : T ⊆ U := by
      intro i hi
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mp hi).1)
    exact (Finset.card_le_card hTU).trans_lt hUproper
  have hHallT := hHall T hT hTproper
  have hHallU := hHall U hU hUproper
  have hsub := rowNeighbors_card_inter_union_le S Sc Sd
  have hsets : T.card + U.card = Sc.card + Sd.card := by
    exact Finset.card_inter_add_card_union Sc Sd
  have hTtight : (rowNeighbors S T).card = T.card + 1 := by
    dsimp only [T, U] at hHallT hHallU hsub hsets ⊢
    omega
  let T₀ := T.erase r
  have hT₀sub : T₀ ⊆ T := Finset.erase_subset r T
  have hneighborSub :
      rowNeighbors S T₀ ⊆ rowNeighbors S T \ {c, d} := by
    intro j hj
    obtain ⟨i, hiT₀, hij⟩ := mem_rowNeighbors.mp hj
    have hiT := hT₀sub hiT₀
    apply Finset.mem_sdiff.mpr
    refine ⟨mem_rowNeighbors.mpr ⟨i, hiT, hij⟩, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton]
    intro hjpair
    rcases hjpair with rfl | rfl
    · have hir := hcOnly i (Finset.mem_inter.mp hiT).1 hij
      exact (Finset.mem_erase.mp hiT₀).1 hir
    · have hir := hdOnly i (Finset.mem_inter.mp hiT).2 hij
      exact (Finset.mem_erase.mp hiT₀).1 hir
  have hcT : c ∈ rowNeighbors S T :=
    mem_rowNeighbors.mpr ⟨r, hrT, hrc⟩
  have hdT : d ∈ rowNeighbors S T :=
    mem_rowNeighbors.mpr ⟨r, hrT, hrd⟩
  have hpairSub : {c, d} ⊆ rowNeighbors S T := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    exact hj.elim (· ▸ hcT) (· ▸ hdT)
  have hpairCard : ({c, d} : Finset (Fin n)).card = 2 := Finset.card_pair hcd
  have hdiffCard :
      (rowNeighbors S T \ {c, d}).card = (rowNeighbors S T).card - 2 := by
    rw [Finset.card_sdiff_of_subset hpairSub, hpairCard]
  have hneighborCard := Finset.card_le_card hneighborSub
  rw [hdiffCard, hTtight] at hneighborCard
  have hrTcard : T₀.card = T.card - 1 := by
    exact Finset.card_erase_of_mem hrT
  have hT₀empty : T₀ = ∅ := by
    by_contra hne
    have hT₀ : T₀.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
    have hT₀proper : T₀.card < n :=
      (Finset.card_le_card hT₀sub).trans_lt hTproper
    have hstrict₀ := hHall T₀ hT₀ hT₀proper
    omega
  have hTeq : T = {r} := by
    rcases (Finset.erase_eq_empty_iff T r).mp hT₀empty with h | h
    · exact (hT.ne_empty h).elim
    · exact h
  have hNcard : (rowNeighbors S {r}).card = 2 := by
    rw [← hTeq, hTtight]
    simp [hTeq]
  have hpairN : {c, d} ⊆ rowNeighbors S {r} := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    · exact mem_rowNeighbors.mpr ⟨r, Finset.mem_singleton_self r, hrc⟩
    · exact mem_rowNeighbors.mpr ⟨r, Finset.mem_singleton_self r, hrd⟩
  exact (Finset.eq_of_subset_of_card_le hpairN (by omega)).symm

/-- Lavi Lemma 2.3: an ND support of order at least three has no four-cycle. -/
theorem nearlyDecomposable_no_fourCycle {n : ℕ} (hn : 3 ≤ n)
    {S : Fin n → Fin n → Prop} (hND : NearlyDecomposable S) :
    ¬HasFourCycle S := by
  classical
  intro hfour
  obtain ⟨r, s, c, d, hrs, hcd, hrc, hrd, hsc, hsd⟩ := hfour
  have hHall : StrictHall S :=
    (fullyIndecomposable_iff_strictHall S).mp hND.1
  have hdelrc : ¬StrictHall (deleteEdge S r c) := by
    intro h
    exact hND.2 r c hrc ((fullyIndecomposable_iff_strictHall _).mpr h)
  have hdelrd : ¬StrictHall (deleteEdge S r d) := by
    intro h
    exact hND.2 r d hrd ((fullyIndecomposable_iff_strictHall _).mpr h)
  have hdelsc : ¬StrictHall (deleteEdge S s c) := by
    intro h
    exact hND.2 s c hsc ((fullyIndecomposable_iff_strictHall _).mpr h)
  have hdelsd : ¬StrictHall (deleteEdge S s d) := by
    intro h
    exact hND.2 s d hsd ((fullyIndecomposable_iff_strictHall _).mpr h)
  have hNr := rowNeighbors_singleton_eq_pair_of_delete_failures hHall
    hrs hcd hrc hrd hsc hsd hdelrc hdelrd
  have hNs := rowNeighbors_singleton_eq_pair_of_delete_failures hHall
    hrs.symm hcd hsc hsd hrc hrd hdelsc hdelsd
  let R : Finset (Fin n) := {r, s}
  have hRcard : R.card = 2 := Finset.card_pair hrs
  have hR : R.Nonempty := ⟨r, by simp [R]⟩
  have hRproper : R.card < n := by omega
  have hNR : rowNeighbors S R = {c, d} := by
    rw [show R = ({r} : Finset (Fin n)) ∪ {s} by ext i; simp [R],
      rowNeighbors_union, hNr, hNs, Finset.union_self]
  have hstrict := hHall R hR hRproper
  rw [hRcard, hNR, Finset.card_pair hcd] at hstrict
  omega

/-- Two distinct rows in an ND support of order at least three share at most one column. -/
theorem nearlyDecomposable_common_neighbor_unique {n : ℕ} (hn : 3 ≤ n)
    {S : Fin n → Fin n → Prop} (hND : NearlyDecomposable S)
    {r s c d : Fin n} (hrs : r ≠ s)
    (hrc : S r c) (hsc : S s c) (hrd : S r d) (hsd : S s d) :
    d = c := by
  by_contra hdc
  exact nearlyDecomposable_no_fourCycle hn hND
    ⟨r, s, c, d, hrs, Ne.symm hdc, hrc, hrd, hsc, hsd⟩

end LaviSection2
