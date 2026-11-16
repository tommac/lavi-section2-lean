import LaviSection2.LaviNoFourCycles
import Mathlib.Data.Fintype.Card

/-!
# Column contraction for finite bipartite supports

This module begins the formalization of Lavi's Lemma 2.4.  A degree-two
column is removed and its two neighboring rows are merged.  The contracted
row and column types are literal complements of one vertex, so no cardinality
or relabelling information is hidden in an informal graph operation.

The main theorem in this first layer proves that contraction preserves the
strict Hall inequalities, and hence full indecomposability.  The edge-minimal
part of Lemma 2.4 is treated separately: it needs the deletion witnesses and,
for edges away from the merged row, the perfect-matching/positive-scaling
argument from the manuscript.
-/

namespace LaviSection2

open Function

section GenericSupport

variable {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

/-- Columns adjacent to a finite set of rows, for arbitrary finite vertex types. -/
noncomputable def rowNeighborsOn (S : α → β → Prop) (R : Finset α) : Finset β := by
  classical
  exact Finset.univ.filter fun j ↦ ∃ i ∈ R, S i j

@[simp]
theorem mem_rowNeighborsOn {S : α → β → Prop} {R : Finset α} {j : β} :
    j ∈ rowNeighborsOn S R ↔ ∃ i ∈ R, S i j := by
  classical
  simp [rowNeighborsOn]

/-- Generic row neighborhoods turn row-set unions into unions. -/
theorem rowNeighborsOn_union (S : α → β → Prop) (R T : Finset α) :
    rowNeighborsOn S (R ∪ T) =
      rowNeighborsOn S R ∪ rowNeighborsOn S T := by
  classical
  ext j
  simp [mem_rowNeighborsOn, or_and_right, exists_or]

/-- Strict Hall for a balanced bipartite support presented on arbitrary types. -/
def StrictHallOn (S : α → β → Prop) : Prop :=
  ∀ R : Finset α, R.Nonempty → R.card < Fintype.card α →
    R.card < (rowNeighborsOn S R).card

/-- The zero-rectangle definition on arbitrary balanced finite vertex types. -/
def FullyIndecomposableOn (S : α → β → Prop) : Prop :=
  ∀ R : Finset α, ∀ C : Finset β,
    R.Nonempty → C.Nonempty → R.card + C.card = Fintype.card α →
      ∃ i ∈ R, ∃ j ∈ C, S i j

/-- The zero-rectangle and strict-Hall formulations agree on balanced types. -/
theorem fullyIndecomposableOn_iff_strictHallOn
    (hcard : Fintype.card α = Fintype.card β) (S : α → β → Prop) :
    FullyIndecomposableOn S ↔ StrictHallOn S := by
  classical
  constructor
  · intro hFI R hR hRproper
    by_contra hnot
    have hNle : (rowNeighborsOn S R).card ≤ R.card := Nat.le_of_not_gt hnot
    let C₀ : Finset β := Finset.univ \ rowNeighborsOn S R
    have hC₀card : C₀.card = Fintype.card β - (rowNeighborsOn S R).card := by
      rw [show C₀ = Finset.univ \ rowNeighborsOn S R by rfl,
        Finset.card_sdiff_of_subset (Finset.subset_univ _)]
      simp
    have hsize : Fintype.card α - R.card ≤ C₀.card := by
      omega
    obtain ⟨C, hCC₀, hCcard⟩ := Finset.exists_subset_card_eq hsize
    have hC : C.Nonempty := Finset.card_pos.mp (by omega)
    have hsum : R.card + C.card = Fintype.card α := by omega
    obtain ⟨i, hiR, j, hjC, hij⟩ := hFI R C hR hC hsum
    have hjC₀ := hCC₀ hjC
    have hjN : j ∈ rowNeighborsOn S R :=
      mem_rowNeighborsOn.mpr ⟨i, hiR, hij⟩
    exact (Finset.mem_sdiff.mp hjC₀).2 hjN
  · intro hHall R C hR hC hsum
    have hRproper : R.card < Fintype.card α := by
      have hCpos := Finset.card_pos.mpr hC
      omega
    have hstrict := hHall R hR hRproper
    by_contra hedge
    push Not at hedge
    have hCsub : C ⊆ Finset.univ \ rowNeighborsOn S R := by
      intro j hjC
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ j, ?_⟩
      intro hjN
      obtain ⟨i, hiR, hij⟩ := mem_rowNeighborsOn.mp hjN
      exact hedge i hiR j hjC hij
    have hcardle := Finset.card_le_card hCsub
    have hcompcard :
        (Finset.univ \ rowNeighborsOn S R).card =
          Fintype.card β - (rowNeighborsOn S R).card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
      simp
    rw [hcompcard] at hcardle
    omega

/-- Full indecomposability is invariant under swapping the bipartition. -/
theorem fullyIndecomposableOn_transpose_iff
    (hcard : Fintype.card α = Fintype.card β) (S : α → β → Prop) :
    FullyIndecomposableOn (fun j i ↦ S i j) ↔ FullyIndecomposableOn S := by
  constructor
  · intro h R C hR hC hsum
    obtain ⟨j, hjC, i, hiR, hij⟩ := h C R hC hR (by omega)
    exact ⟨i, hiR, j, hjC, hij⟩
  · intro h C R hC hR hsum
    obtain ⟨i, hiR, j, hjC, hij⟩ := h R C hR hC (by omega)
    exact ⟨j, hjC, i, hiR, hij⟩

/-- Strict Hall is invariant under swapping equal finite bipartitions. -/
theorem strictHallOn_transpose_iff
    (hcard : Fintype.card α = Fintype.card β) (S : α → β → Prop) :
    StrictHallOn (fun j i ↦ S i j) ↔ StrictHallOn S := by
  rw [← fullyIndecomposableOn_iff_strictHallOn hcard.symm,
    ← fullyIndecomposableOn_iff_strictHallOn hcard,
    fullyIndecomposableOn_transpose_iff hcard]

/-- Remove one edge from a support on arbitrary finite vertex types. -/
def deleteEdgeOn (S : α → β → Prop) (a : α) (b : β) : α → β → Prop :=
  fun i j ↦ S i j ∧ ¬(i = a ∧ j = b)

/-- Deleting an edge can only shrink a generic row neighborhood. -/
theorem rowNeighborsOn_deleteEdgeOn_subset
    (S : α → β → Prop) (r : α) (c : β) (R : Finset α) :
    rowNeighborsOn (deleteEdgeOn S r c) R ⊆ rowNeighborsOn S R := by
  intro j hj
  obtain ⟨i, hiR, hij⟩ := mem_rowNeighborsOn.mp hj
  exact mem_rowNeighborsOn.mpr ⟨i, hiR, hij.1⟩

/-- Deleting `(r,c)` can remove no generic row neighbor other than `c`. -/
theorem rowNeighborsOn_subset_insert_deleteEdgeOn
    (S : α → β → Prop) (r : α) (c : β) (R : Finset α) :
    rowNeighborsOn S R ⊆
      insert c (rowNeighborsOn (deleteEdgeOn S r c) R) := by
  classical
  intro j hj
  obtain ⟨i, hiR, hij⟩ := mem_rowNeighborsOn.mp hj
  by_cases h : i = r ∧ j = c
  · exact Finset.mem_insert.mpr (Or.inl h.2)
  · exact Finset.mem_insert.mpr (Or.inr <|
      mem_rowNeighborsOn.mpr ⟨i, hiR, hij, h⟩)

/--
A failed edge deletion exposes the exact tight row set used in Lavi's
contraction analysis, now for arbitrary finite bipartite vertex types.
-/
theorem exists_tight_witnessOn_of_delete_not_strictHallOn
    {S : α → β → Prop} (hHall : StrictHallOn S)
    {r : α} {c : β} (hdelete : ¬StrictHallOn (deleteEdgeOn S r c)) :
    ∃ R : Finset α,
      R.Nonempty ∧ R.card < Fintype.card α ∧ r ∈ R ∧
      (rowNeighborsOn S R).card = R.card + 1 ∧
      c ∉ rowNeighborsOn (deleteEdgeOn S r c) R ∧
      (∀ i ∈ R, S i c → i = r) := by
  classical
  unfold StrictHallOn at hdelete
  push Not at hdelete
  obtain ⟨R, hR, hRproper, hfail⟩ := hdelete
  have hdelLe : (rowNeighborsOn (deleteEdgeOn S r c) R).card ≤ R.card :=
    hfail
  have hstrict := hHall R hR hRproper
  have hsubset := rowNeighborsOn_subset_insert_deleteEdgeOn S r c R
  have hNleInsert := Finset.card_le_card hsubset
  have hInsertLe := Finset.card_insert_le c
    (rowNeighborsOn (deleteEdgeOn S r c) R)
  have hNtight : (rowNeighborsOn S R).card = R.card + 1 := by omega
  have hcNot : c ∉ rowNeighborsOn (deleteEdgeOn S r c) R := by
    intro hc
    have hinsert :
        insert c (rowNeighborsOn (deleteEdgeOn S r c) R) =
          rowNeighborsOn (deleteEdgeOn S r c) R := Finset.insert_eq_of_mem hc
    rw [hinsert] at hNleInsert
    omega
  have hrR : r ∈ R := by
    by_contra hr
    have hreverse : rowNeighborsOn S R ⊆
        rowNeighborsOn (deleteEdgeOn S r c) R := by
      intro j hj
      obtain ⟨i, hiR, hij⟩ := mem_rowNeighborsOn.mp hj
      apply mem_rowNeighborsOn.mpr
      refine ⟨i, hiR, hij, ?_⟩
      intro h
      exact hr (h.1 ▸ hiR)
    have hcard := Finset.card_le_card hreverse
    omega
  refine ⟨R, hR, hRproper, hrR, hNtight, hcNot, ?_⟩
  intro i hiR hic
  by_contra hir
  apply hcNot
  exact mem_rowNeighborsOn.mpr ⟨i, hiR, hic, fun h ↦ hir h.1⟩

/-- If `r` is the unique row of `R` meeting `c`, deletion erases exactly `c`. -/
theorem rowNeighborsOn_deleteEdgeOn_eq_erase
    (S : α → β → Prop) {r : α} {c : β} {R : Finset α}
    (hrR : r ∈ R) (hrc : S r c)
    (hcOnly : ∀ i ∈ R, S i c → i = r) :
    rowNeighborsOn (deleteEdgeOn S r c) R =
      (rowNeighborsOn S R).erase c := by
  classical
  ext j
  simp only [mem_rowNeighborsOn, Finset.mem_erase]
  constructor
  · rintro ⟨i, hiR, hij, hne⟩
    refine ⟨?_, ⟨i, hiR, hij⟩⟩
    intro hjc
    subst j
    exact hne ⟨hcOnly i hiR hij, rfl⟩
  · rintro ⟨hjc, i, hiR, hij⟩
    exact ⟨i, hiR, hij, fun h ↦ hjc h.2⟩

/--
The deletion witness can be normalized so that the deleted neighborhood has
exactly `|R|` columns, not merely at most `|R|`.
-/
theorem exists_exact_tight_witnessOn_of_delete_not_strictHallOn
    {S : α → β → Prop} (hHall : StrictHallOn S)
    {r : α} {c : β} (hrc : S r c)
    (hdelete : ¬StrictHallOn (deleteEdgeOn S r c)) :
    ∃ R : Finset α,
      R.Nonempty ∧ R.card < Fintype.card α ∧ r ∈ R ∧
      (rowNeighborsOn S R).card = R.card + 1 ∧
      rowNeighborsOn (deleteEdgeOn S r c) R =
        (rowNeighborsOn S R).erase c ∧
      (rowNeighborsOn (deleteEdgeOn S r c) R).card = R.card ∧
      (∀ i ∈ R, S i c → i = r) := by
  classical
  obtain ⟨R, hR, hRproper, hrR, hNtight, _, hcOnly⟩ :=
    exists_tight_witnessOn_of_delete_not_strictHallOn hHall hdelete
  have hcN : c ∈ rowNeighborsOn S R :=
    mem_rowNeighborsOn.mpr ⟨r, hrR, hrc⟩
  have hEq := rowNeighborsOn_deleteEdgeOn_eq_erase S hrR hrc hcOnly
  have hcard : (rowNeighborsOn (deleteEdgeOn S r c) R).card = R.card := by
    rw [hEq, Finset.card_erase_of_mem hcN, hNtight]
    omega
  exact ⟨R, hR, hRproper, hrR, hNtight, hEq, hcard, hcOnly⟩

/-- Number of distinct columns incident to a row. -/
noncomputable def rowDegreeOn (S : α → β → Prop) (r : α) : ℕ :=
  (rowNeighborsOn S {r}).card

/-- Number of distinct rows incident to a column. -/
noncomputable def columnDegreeOn (S : α → β → Prop) (c : β) : ℕ :=
  (rowNeighborsOn (fun j i ↦ S i j) {c}).card

/-- Two distinct incident rows exhaust a column of degree two. -/
theorem column_neighbors_eq_pair_of_degree_two
    (S : α → β → Prop) {r s : α} {c : β} (hrs : r ≠ s)
    (hrc : S r c) (hsc : S s c) (hdeg : columnDegreeOn S c = 2) :
    ∀ i, S i c ↔ i = r ∨ i = s := by
  classical
  let N := rowNeighborsOn (fun j i ↦ S i j) {c}
  have hrN : r ∈ N := mem_rowNeighborsOn.mpr ⟨c, by simp, hrc⟩
  have hsN : s ∈ N := mem_rowNeighborsOn.mpr ⟨c, by simp, hsc⟩
  have hpair : ({r, s} : Finset α) ⊆ N := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    exact hi.elim (fun h ↦ h ▸ hrN) (fun h ↦ h ▸ hsN)
  have hNcard : N.card = 2 := by simpa [N, columnDegreeOn] using hdeg
  have hpairCard : ({r, s} : Finset α).card = 2 := Finset.card_pair hrs
  have hN : N = {r, s} :=
    (Finset.eq_of_subset_of_card_le hpair (by omega)).symm
  intro i
  rw [← show i ∈ N ↔ S i c by
    simp only [N, mem_rowNeighborsOn, Finset.mem_singleton, exists_eq_left], hN]
  simp

/-- Two distinct incident columns exhaust a row of degree two. -/
theorem row_neighbors_eq_pair_of_degree_two
    (S : α → β → Prop) {r : α} {c d : β} (hcd : c ≠ d)
    (hrc : S r c) (hrd : S r d) (hdeg : rowDegreeOn S r = 2) :
    ∀ j, S r j ↔ j = c ∨ j = d := by
  classical
  let N := rowNeighborsOn S {r}
  have hcN : c ∈ N := mem_rowNeighborsOn.mpr ⟨r, by simp, hrc⟩
  have hdN : d ∈ N := mem_rowNeighborsOn.mpr ⟨r, by simp, hrd⟩
  have hpair : ({c, d} : Finset β) ⊆ N := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    exact hj.elim (fun h ↦ h ▸ hcN) (fun h ↦ h ▸ hdN)
  have hNcard : N.card = 2 := by simpa [N, rowDegreeOn] using hdeg
  have hpairCard : ({c, d} : Finset β).card = 2 := Finset.card_pair hcd
  have hN : N = {c, d} :=
    (Finset.eq_of_subset_of_card_le hpair (by omega)).symm
  intro j
  rw [← show j ∈ N ↔ S r j by
    simp only [N, mem_rowNeighborsOn, Finset.mem_singleton, exists_eq_left], hN]
  simp

/-- Deleting an incident edge from a degree-two row destroys strict Hall. -/
theorem deleteEdgeOn_not_strictHallOn_of_rowDegree_two
    (S : α → β → Prop) (hsize : 2 ≤ Fintype.card α)
    {r : α} {c : β} (hrc : S r c) (hdeg : rowDegreeOn S r = 2) :
    ¬StrictHallOn (deleteEdgeOn S r c) := by
  intro hHall
  have hEq : rowNeighborsOn (deleteEdgeOn S r c) {r} =
      (rowNeighborsOn S {r}).erase c :=
    rowNeighborsOn_deleteEdgeOn_eq_erase S (by simp) hrc (by
      intro i hi _
      simpa using hi)
  have hcN : c ∈ rowNeighborsOn S {r} :=
    mem_rowNeighborsOn.mpr ⟨r, by simp, hrc⟩
  have hproper : ({r} : Finset α).card < Fintype.card α := by
    simp only [Finset.card_singleton]
    omega
  have hstrict := hHall {r} (by simp) hproper
  rw [hEq, Finset.card_erase_of_mem hcN] at hstrict
  simp only [Finset.card_singleton] at hstrict
  unfold rowDegreeOn at hdeg
  omega

/-- Inclusion-minimal strict Hall on arbitrary finite vertex types. -/
def NearlyDecomposableOn (S : α → β → Prop) : Prop :=
  StrictHallOn S ∧
    ∀ i j, S i j → ¬StrictHallOn (deleteEdgeOn S i j)

/-- The generic strict-Hall predicate agrees with the original square one. -/
theorem strictHallOn_fin_iff {n : ℕ} (S : Fin n → Fin n → Prop) :
    StrictHallOn S ↔ StrictHall S := by
  classical
  have hneighbors (R : Finset (Fin n)) :
      rowNeighborsOn S R = rowNeighbors S R := by
    ext j
    simp
  simp only [StrictHallOn, StrictHall, hneighbors, Fintype.card_fin]

/-- The generic deletion operation agrees with the original square one. -/
theorem deleteEdgeOn_fin_eq {n : ℕ} (S : Fin n → Fin n → Prop)
    (i j : Fin n) :
    deleteEdgeOn S i j = deleteEdge S i j := by
  rfl

/-- The generic minimality predicate agrees with near decomposability on `Fin n`. -/
theorem nearlyDecomposableOn_fin_iff {n : ℕ} (S : Fin n → Fin n → Prop) :
    NearlyDecomposableOn S ↔ NearlyDecomposable S := by
  rw [NearlyDecomposableOn, NearlyDecomposable,
    fullyIndecomposable_iff_strictHall, ← strictHallOn_fin_iff]
  constructor
  · rintro ⟨hHall, hmin⟩
    refine ⟨hHall, fun i j hij hFI ↦ ?_⟩
    exact hmin i j hij ((strictHallOn_fin_iff _).2 <|
      (fullyIndecomposable_iff_strictHall _).1 hFI)
  · rintro ⟨hHall, hmin⟩
    refine ⟨hHall, fun i j hij hStrict ↦ ?_⟩
    exact hmin i j hij ((fullyIndecomposable_iff_strictHall _).2 <|
      (strictHallOn_fin_iff _).1 hStrict)

end GenericSupport

section Contraction

variable {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

/-- The finite vertex type obtained by deleting `x`. -/
abbrev Drop (x : α) := {y : α // y ≠ x}

/--
Delete column `c` and merge row `s` into row `r`.  The surviving
representative of the merged row is `r`; row `s` is absent from the new type.
-/
def contractColumn (S : α → β → Prop) (r s : α) (c : β) :
    Drop s → Drop c → Prop :=
  fun i j ↦ if i.1 = r then S r j.1 ∨ S s j.1 else S i.1 j.1

/--
Delete row `r` and merge column `d` into column `c`.  This is the transpose
of `contractColumn` with the surviving representative chosen to be `c`.
-/
def contractRow (S : α → β → Prop) (r : α) (c d : β) :
    Drop r → Drop d → Prop :=
  fun i j ↦ if j.1 = c then S i.1 c ∨ S i.1 d else S i.1 j.1

@[simp]
theorem contractColumn_merged (S : α → β → Prop) {r s : α} (hrs : r ≠ s)
    (c : β) (j : Drop c) :
    contractColumn S r s c ⟨r, hrs⟩ j ↔ S r j.1 ∨ S s j.1 := by
  simp [contractColumn]

@[simp]
theorem contractColumn_unmerged (S : α → β → Prop) {r s i : α}
    (hi : i ≠ s) (hir : i ≠ r) (c : β) (j : Drop c) :
    contractColumn S r s c ⟨i, hi⟩ j ↔ S i j.1 := by
  simp [contractColumn, hir]

/-- The row set in the old support represented by contracted rows not using the merge. -/
noncomputable def liftContractedRows {s : α} (R : Finset (Drop s)) : Finset α := by
  classical
  exact R.image Subtype.val

@[simp]
theorem mem_liftContractedRows {s : α} {R : Finset (Drop s)} {i : α} :
    i ∈ liftContractedRows R ↔ ∃ hi : i ≠ s, (⟨i, hi⟩ : Drop s) ∈ R := by
  classical
  simp [liftContractedRows]

theorem card_liftContractedRows {s : α} (R : Finset (Drop s)) :
    (liftContractedRows R).card = R.card := by
  classical
  exact Finset.card_image_of_injective R Subtype.val_injective

theorem deleted_row_not_mem_liftContractedRows {s : α} (R : Finset (Drop s)) :
    s ∉ liftContractedRows R := by
  classical
  simp [liftContractedRows]

/-- Regard a finset as a finset in the complement of one vertex. -/
noncomputable def restrictAway (c : β) (T : Finset β) : Finset (Drop c) := by
  classical
  exact Finset.univ.filter fun j ↦ j.1 ∈ T

@[simp]
theorem mem_restrictAway {c : β} {T : Finset β} {j : Drop c} :
    j ∈ restrictAway c T ↔ j.1 ∈ T := by
  classical
  simp [restrictAway]

/-- Restriction to the complement of `c` has the cardinality of erasing `c`. -/
theorem card_restrictAway (c : β) (T : Finset β) :
    (restrictAway c T).card = (T.erase c).card := by
  classical
  have hEq : (restrictAway c T).image Subtype.val = T.erase c := by
    ext j
    simp [and_comm]
  have hcard := Finset.card_image_of_injective (restrictAway c T)
    Subtype.val_injective
  rw [hEq] at hcard
  exact hcard.symm

/--
The exact neighborhood formula when a contracted row set avoids the merged
row.  The removed column cannot occur because it was adjacent only to the two
rows involved in the contraction.
-/
theorem rowNeighborsOn_contractColumn_of_merged_not_mem
    (S : α → β → Prop) {r s : α} (hrs : r ≠ s) {c : β}
    (hc : ∀ i, S i c ↔ i = r ∨ i = s)
    (R : Finset (Drop s)) (hr : (⟨r, hrs⟩ : Drop s) ∉ R) :
    rowNeighborsOn (contractColumn S r s c) R =
      restrictAway c (rowNeighborsOn S (liftContractedRows R)) := by
  classical
  ext j
  simp only [mem_rowNeighborsOn, mem_restrictAway]
  constructor
  · rintro ⟨i, hiR, hiSj⟩
    have hir : i.1 ≠ r := by
      intro h
      apply hr
      have him : i = (⟨r, hrs⟩ : Drop s) := Subtype.ext h
      exact him ▸ hiR
    have hS : S i.1 j.1 := (contractColumn_unmerged S i.2 hir c j).mp hiSj
    exact ⟨i.1, mem_liftContractedRows.mpr ⟨i.2, hiR⟩, hS⟩
  · rintro ⟨i, hiLift, hS⟩
    obtain ⟨his, hiR⟩ := mem_liftContractedRows.mp hiLift
    have hir : i ≠ r := by
      intro h
      apply hr
      exact h ▸ hiR
    refine ⟨⟨i, his⟩, hiR, ?_⟩
    exact (contractColumn_unmerged S his hir c j).mpr hS

/--
The exact neighborhood formula when a contracted row set contains the merged
row.  Before deleting `c`, it represents the old row set obtained by adjoining
the removed row `s`.
-/
theorem rowNeighborsOn_contractColumn_of_merged_mem
    (S : α → β → Prop) {r s : α} (hrs : r ≠ s) {c : β}
    (R : Finset (Drop s)) (hr : (⟨r, hrs⟩ : Drop s) ∈ R) :
    rowNeighborsOn (contractColumn S r s c) R =
      restrictAway c (rowNeighborsOn S (insert s (liftContractedRows R))) := by
  classical
  ext j
  simp only [mem_rowNeighborsOn, mem_restrictAway]
  constructor
  · rintro ⟨i, hiR, hiSj⟩
    by_cases hir : i.1 = r
    · have hcases : S r j.1 ∨ S s j.1 := by
        simpa [contractColumn, hir] using hiSj
      rcases hcases with hrj | hsj
      · exact ⟨r, Finset.mem_insert_of_mem <|
          mem_liftContractedRows.mpr ⟨hrs, hir ▸ hiR⟩, hrj⟩
      · exact ⟨s, Finset.mem_insert_self _ _, hsj⟩
    · refine ⟨i.1, Finset.mem_insert_of_mem <|
          mem_liftContractedRows.mpr ⟨i.2, hiR⟩, ?_⟩
      exact (contractColumn_unmerged S i.2 hir c j).mp hiSj
  · rintro ⟨i, hiOld, hS⟩
    rcases Finset.mem_insert.mp hiOld with rfl | hiLift
    · exact ⟨⟨r, hrs⟩, hr, (contractColumn_merged S hrs c j).mpr (Or.inr hS)⟩
    · obtain ⟨his, hiR⟩ := mem_liftContractedRows.mp hiLift
      by_cases hir : i = r
      · subst i
        exact ⟨⟨r, hrs⟩, hr, (contractColumn_merged S hrs c j).mpr (Or.inl hS)⟩
      · exact ⟨⟨i, his⟩, hiR,
          (contractColumn_unmerged S his hir c j).mpr hS⟩

/-- Restricting a finset away from `c` removes exactly one point when present. -/
theorem card_restrictAway_eq (T : Finset β) (c : β) :
    (restrictAway c T).card = T.card - (if c ∈ T then 1 else 0) := by
  classical
  rw [card_restrictAway]
  by_cases hc : c ∈ T
  · rw [ite_eq_left hc]
    exact Finset.card_erase_of_mem hc
  · rw [ite_eq_right hc]
    simp [Finset.erase_eq_of_notMem hc]

/--
Contracting a column whose only neighbors are two distinct rows preserves the
strict Hall inequalities.  This is the full-indecomposability half of Lavi
Lemma 2.4, proved without importing the later matrix-scaling argument.
-/
theorem strictHallOn_contractColumn
    (S : α → β → Prop) {r s : α} (hrs : r ≠ s) {c : β}
    (hc : ∀ i, S i c ↔ i = r ∨ i = s)
    (hHall : StrictHallOn S) :
    StrictHallOn (contractColumn S r s c) := by
  classical
  intro R hR hRproper
  let m : Drop s := ⟨r, hrs⟩
  by_cases hm : m ∈ R
  · let Rold : Finset α := insert s (liftContractedRows R)
    have hsNot : s ∉ liftContractedRows R :=
      deleted_row_not_mem_liftContractedRows R
    have hRoldCard : Rold.card = R.card + 1 := by
      simp [Rold, hsNot, card_liftContractedRows]
    have hRold : Rold.Nonempty := ⟨s, Finset.mem_insert_self _ _⟩
    have hDropCard : Fintype.card (Drop s) = Fintype.card α - 1 :=
      Set.card_ne_eq s
    have hRoldProper : Rold.card < Fintype.card α := by
      dsimp [m] at hRproper hm
      omega
    have hOldStrict := hHall Rold hRold hRoldProper
    have hcOld : c ∈ rowNeighborsOn S Rold := by
      apply mem_rowNeighborsOn.mpr
      exact ⟨r, Finset.mem_insert_of_mem <|
        mem_liftContractedRows.mpr ⟨hrs, hm⟩, (hc r).2 (Or.inl rfl)⟩
    dsimp [Rold] at hRoldCard hOldStrict hcOld
    rw [rowNeighborsOn_contractColumn_of_merged_mem S hrs R hm,
      card_restrictAway_eq, ite_eq_left hcOld]
    omega
  · have hLiftCard : (liftContractedRows R).card = R.card :=
      card_liftContractedRows R
    have hLift : (liftContractedRows R).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hEmpty
      have : R.card = 0 := by simpa [hEmpty] using hLiftCard.symm
      exact hR.ne_empty (Finset.card_eq_zero.mp this)
    have hLiftProper : (liftContractedRows R).card < Fintype.card α := by
      have hDropCard : Fintype.card (Drop s) = Fintype.card α - 1 :=
        Set.card_ne_eq s
      omega
    have hOldStrict := hHall (liftContractedRows R) hLift hLiftProper
    have hcNot : c ∉ rowNeighborsOn S (liftContractedRows R) := by
      intro hcN
      obtain ⟨i, hiLift, hic⟩ := mem_rowNeighborsOn.mp hcN
      obtain ⟨his, hiR⟩ := mem_liftContractedRows.mp hiLift
      rcases (hc i).mp hic with rfl | rfl
      · exact hm hiR
      · exact his rfl
    rw [rowNeighborsOn_contractColumn_of_merged_not_mem S hrs hc R hm,
      card_restrictAway_eq, ite_eq_right hcNot]
    omega

/--
If both rows merged across `c` have degree two and share no other neighbor,
then the merged row has degree two in the contracted support.
-/
theorem rowDegreeOn_contractColumn_merged_eq_two
    (S : α → β → Prop) {r s : α} (hrs : r ≠ s) {c : β}
    (hc : ∀ i, S i c ↔ i = r ∨ i = s)
    (hcommon : ∀ j, S r j → S s j → j = c)
    (hdegR : rowDegreeOn S r = 2) (hdegS : rowDegreeOn S s = 2) :
    rowDegreeOn (contractColumn S r s c) (⟨r, hrs⟩ : Drop s) = 2 := by
  classical
  let A := rowNeighborsOn S {r}
  let B := rowNeighborsOn S {s}
  have hrc : S r c := (hc r).2 (Or.inl rfl)
  have hsc : S s c := (hc s).2 (Or.inr rfl)
  have hcA : c ∈ A := mem_rowNeighborsOn.mpr ⟨r, by simp, hrc⟩
  have hcB : c ∈ B := mem_rowNeighborsOn.mpr ⟨s, by simp, hsc⟩
  have hAcard : A.card = 2 := by simpa [A, rowDegreeOn] using hdegR
  have hBcard : B.card = 2 := by simpa [B, rowDegreeOn] using hdegS
  have hinter : A ∩ B = {c} := by
    ext j
    constructor
    · intro hj
      have hjA := (Finset.mem_inter.mp hj).1
      have hjB := (Finset.mem_inter.mp hj).2
      have hrj : S r j := by
        simpa [A, mem_rowNeighborsOn] using hjA
      have hsj : S s j := by
        simpa [B, mem_rowNeighborsOn] using hjB
      simpa using hcommon j hrj hsj
    · intro hj
      have hjc : j = c := by simpa using hj
      subst j
      exact Finset.mem_inter.mpr ⟨hcA, hcB⟩
  have hUnionCard : (A ∪ B).card = 3 := by
    have hcardIdentity := Finset.card_inter_add_card_union A B
    rw [hinter, Finset.card_singleton, hAcard, hBcard] at hcardIdentity
    omega
  let m : Drop s := ⟨r, hrs⟩
  have hm : m ∈ ({m} : Finset (Drop s)) := by simp
  have hLift : liftContractedRows ({m} : Finset (Drop s)) = {r} := by
    ext i
    simp [m, liftContractedRows]
  have hOldRows : insert s (liftContractedRows ({m} : Finset (Drop s))) =
      ({r, s} : Finset α) := by
    rw [hLift]
    exact Finset.pair_comm s r
  have hOldNeighbors :
      rowNeighborsOn S (insert s (liftContractedRows ({m} : Finset (Drop s)))) =
        A ∪ B := by
    rw [hOldRows, show ({r, s} : Finset α) = ({r} : Finset α) ∪ {s} by
      ext i; simp]
    exact rowNeighborsOn_union S {r} {s}
  have hcOld : c ∈
      rowNeighborsOn S (insert s (liftContractedRows ({m} : Finset (Drop s)))) := by
    rw [hOldNeighbors]
    exact Finset.mem_union_left B hcA
  have hNeighborhood := rowNeighborsOn_contractColumn_of_merged_mem
    (c := c) S hrs ({m} : Finset (Drop s)) hm
  change (rowNeighborsOn (contractColumn S r s c) {m}).card = 2
  rw [hNeighborhood, card_restrictAway_eq, ite_eq_left hcOld,
    hOldNeighbors, hUnionCard]

/--
Low-low specialization of the merged-row edge case in Lavi Lemma 2.4: after
contracting a degree-two column of an ND support, deleting any edge incident
to the merged row violates strict Hall.
-/
theorem nearlyDecomposable_contractColumn_low_low_merged_edge
    {n : ℕ} (hn : 3 ≤ n) (S : Fin n → Fin n → Prop)
    {r s c : Fin n} (hrs : r ≠ s) (hrc : S r c) (hsc : S s c)
    (hdegC : columnDegreeOn S c = 2)
    (hdegR : rowDegreeOn S r = 2) (hdegS : rowDegreeOn S s = 2)
    (hND : NearlyDecomposable S) {j : Drop c}
    (hmj : contractColumn S r s c (⟨r, hrs⟩ : Drop s) j) :
    ¬StrictHallOn
      (deleteEdgeOn (contractColumn S r s c) (⟨r, hrs⟩ : Drop s) j) := by
  have hc := column_neighbors_eq_pair_of_degree_two S hrs hrc hsc hdegC
  have hcommon : ∀ k, S r k → S s k → k = c := by
    intro k hrk hsk
    exact nearlyDecomposable_common_neighbor_unique hn hND hrs hrc hsc hrk hsk
  have hMergedDegree :
      rowDegreeOn (contractColumn S r s c) (⟨r, hrs⟩ : Drop s) = 2 :=
    rowDegreeOn_contractColumn_merged_eq_two S hrs hc hcommon hdegR hdegS
  have hsize : 2 ≤ Fintype.card (Drop s) := by
    change 2 ≤ Fintype.card {x : Fin n // x ≠ s}
    have hcard : Fintype.card {x : Fin n // x ≠ s} = n - 1 := by
      simpa using Set.card_ne_eq s
    rw [hcard]
    omega
  exact deleteEdgeOn_not_strictHallOn_of_rowDegree_two
    (contractColumn S r s c) hsize hmj hMergedDegree

/-- The transposed contraction also preserves strict Hall. -/
theorem strictHallOn_contractRow
    (hcard : Fintype.card α = Fintype.card β)
    (S : α → β → Prop) {r : α} {c d : β} (hcd : c ≠ d)
    (hr : ∀ j, S r j ↔ j = c ∨ j = d)
    (hHall : StrictHallOn S) :
    StrictHallOn (contractRow S r c d) := by
  let ST : β → α → Prop := fun j i ↦ S i j
  have hHallT : StrictHallOn ST :=
    (strictHallOn_transpose_iff hcard S).2 hHall
  have hContractT : StrictHallOn (contractColumn ST c d r) :=
    strictHallOn_contractColumn ST hcd hr hHallT
  have hdrop : Fintype.card (Drop d) = Fintype.card (Drop r) := by
    change Fintype.card {x : β // x ≠ d} =
      Fintype.card {x : α // x ≠ r}
    calc
      Fintype.card {x : β // x ≠ d} = Fintype.card β - 1 :=
        Set.card_ne_eq d
      _ = Fintype.card α - 1 := by rw [hcard]
      _ = Fintype.card {x : α // x ≠ r} := (Set.card_ne_eq r).symm
  have hTranspose :
      StrictHallOn (fun i j ↦ contractColumn ST c d r j i) :=
    (strictHallOn_transpose_iff hdrop (contractColumn ST c d r)).2 hContractT
  change StrictHallOn
    (fun (i : Drop r) (j : Drop d) ↦
      if j.1 = c then S i.1 c ∨ S i.1 d else S i.1 j.1)
  simpa only [contractColumn, ST] using hTranspose

/--
Concrete square specialization: contracting a degree-two column in a fully
indecomposable support leaves a fully indecomposable support on `n-1` rows and
columns (represented by complement subtypes).
-/
theorem fullyIndecomposable_contractColumn {n : ℕ}
    (S : Fin n → Fin n → Prop) {r s c : Fin n} (hrs : r ≠ s)
    (hc : ∀ i, S i c ↔ i = r ∨ i = s)
    (hFI : FullyIndecomposable S) :
    StrictHallOn (contractColumn S r s c) := by
  exact strictHallOn_contractColumn S hrs hc
    ((strictHallOn_fin_iff S).2 <|
      (fullyIndecomposable_iff_strictHall S).1 hFI)

/-- Degree-form version of `fullyIndecomposable_contractColumn`. -/
theorem fullyIndecomposable_contractColumn_of_degree_two {n : ℕ}
    (S : Fin n → Fin n → Prop) {r s c : Fin n} (hrs : r ≠ s)
    (hrc : S r c) (hsc : S s c) (hdeg : columnDegreeOn S c = 2)
    (hFI : FullyIndecomposable S) :
    StrictHallOn (contractColumn S r s c) := by
  exact fullyIndecomposable_contractColumn S hrs
    (column_neighbors_eq_pair_of_degree_two S hrs hrc hsc hdeg) hFI

/-- The corresponding square specialization for a degree-two row. -/
theorem fullyIndecomposable_contractRow {n : ℕ}
    (S : Fin n → Fin n → Prop) {r c d : Fin n} (hcd : c ≠ d)
    (hr : ∀ j, S r j ↔ j = c ∨ j = d)
    (hFI : FullyIndecomposable S) :
    StrictHallOn (contractRow S r c d) := by
  exact strictHallOn_contractRow rfl S hcd hr
    ((strictHallOn_fin_iff S).2 <|
      (fullyIndecomposable_iff_strictHall S).1 hFI)

/-- Degree-form version of `fullyIndecomposable_contractRow`. -/
theorem fullyIndecomposable_contractRow_of_degree_two {n : ℕ}
    (S : Fin n → Fin n → Prop) {r c d : Fin n} (hcd : c ≠ d)
    (hrc : S r c) (hrd : S r d) (hdeg : rowDegreeOn S r = 2)
    (hFI : FullyIndecomposable S) :
    StrictHallOn (contractRow S r c d) := by
  exact fullyIndecomposable_contractRow S hcd
    (row_neighbors_eq_pair_of_degree_two S hcd hrc hrd hdeg) hFI

end Contraction

end LaviSection2
