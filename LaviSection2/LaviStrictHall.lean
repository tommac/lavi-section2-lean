import LaviSection2.Definitions
import Mathlib.Data.Finset.Card

/-!
# Strict Hall form of full indecomposability

Lavi's support reductions use the strict Hall characterization of a fully
indecomposable balanced bipartite support.  This module derives that
characterization from the zero-submatrix definition in `Definitions` rather than
assuming it as a separate primitive.
-/

namespace LaviSection2

/-- Columns adjacent to at least one row in `R`. -/
noncomputable def rowNeighbors {n : ℕ} (S : Fin n → Fin n → Prop)
    (R : Finset (Fin n)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun j ↦ ∃ i ∈ R, S i j

@[simp]
theorem mem_rowNeighbors {n : ℕ} {S : Fin n → Fin n → Prop}
    {R : Finset (Fin n)} {j : Fin n} :
    j ∈ rowNeighbors S R ↔ ∃ i ∈ R, S i j := by
  classical
  simp [rowNeighbors]

/-- The row-set strict Hall inequalities. -/
def StrictHall {n : ℕ} (S : Fin n → Fin n → Prop) : Prop :=
  ∀ R : Finset (Fin n), R.Nonempty → R.card < n →
    R.card < (rowNeighbors S R).card

/-- Row neighborhoods are monotone in the row set. -/
theorem rowNeighbors_mono {n : ℕ} {S : Fin n → Fin n → Prop}
    {R T : Finset (Fin n)} (hRT : R ⊆ T) :
    rowNeighbors S R ⊆ rowNeighbors S T := by
  intro j hj
  obtain ⟨i, hiR, hij⟩ := mem_rowNeighbors.mp hj
  exact mem_rowNeighbors.mpr ⟨i, hRT hiR, hij⟩

/-- Neighborhoods turn row-set unions into unions. -/
theorem rowNeighbors_union {n : ℕ} (S : Fin n → Fin n → Prop)
    (R T : Finset (Fin n)) :
    rowNeighbors S (R ∪ T) = rowNeighbors S R ∪ rowNeighbors S T := by
  classical
  ext j
  simp [mem_rowNeighbors, or_and_right, exists_or]

/-- Neighborhoods of intersections lie in the intersection of neighborhoods. -/
theorem rowNeighbors_inter_subset {n : ℕ}
    (S : Fin n → Fin n → Prop) (R T : Finset (Fin n)) :
    rowNeighbors S (R ∩ T) ⊆ rowNeighbors S R ∩ rowNeighbors S T := by
  intro j hj
  obtain ⟨i, hi, hij⟩ := mem_rowNeighbors.mp hj
  exact Finset.mem_inter.mpr
    ⟨mem_rowNeighbors.mpr ⟨i, (Finset.mem_inter.mp hi).1, hij⟩,
      mem_rowNeighbors.mpr ⟨i, (Finset.mem_inter.mp hi).2, hij⟩⟩

/-- Cardinal submodularity of the row-neighborhood operation. -/
theorem rowNeighbors_card_inter_union_le {n : ℕ}
    (S : Fin n → Fin n → Prop) (R T : Finset (Fin n)) :
    (rowNeighbors S (R ∩ T)).card + (rowNeighbors S (R ∪ T)).card ≤
      (rowNeighbors S R).card + (rowNeighbors S T).card := by
  have hinter := Finset.card_le_card (rowNeighbors_inter_subset S R T)
  rw [rowNeighbors_union]
  calc
    (rowNeighbors S (R ∩ T)).card +
        (rowNeighbors S R ∪ rowNeighbors S T).card ≤
      (rowNeighbors S R ∩ rowNeighbors S T).card +
        (rowNeighbors S R ∪ rowNeighbors S T).card :=
      Nat.add_le_add_right hinter _
    _ = (rowNeighbors S R).card + (rowNeighbors S T).card :=
      Finset.card_inter_add_card_union _ _

/-- Deleting an edge can only shrink a row neighborhood. -/
theorem rowNeighbors_deleteEdge_subset {n : ℕ}
    (S : Fin n → Fin n → Prop) (r c : Fin n) (R : Finset (Fin n)) :
    rowNeighbors (deleteEdge S r c) R ⊆ rowNeighbors S R := by
  intro j hj
  obtain ⟨i, hiR, hij⟩ := mem_rowNeighbors.mp hj
  exact mem_rowNeighbors.mpr ⟨i, hiR, hij.1⟩

/-- Deleting `(r,c)` can remove no neighbor other than `c`. -/
theorem rowNeighbors_subset_insert_deleteEdge {n : ℕ}
    (S : Fin n → Fin n → Prop) (r c : Fin n) (R : Finset (Fin n)) :
    rowNeighbors S R ⊆
      insert c (rowNeighbors (deleteEdge S r c) R) := by
  classical
  intro j hj
  obtain ⟨i, hiR, hij⟩ := mem_rowNeighbors.mp hj
  by_cases h : i = r ∧ j = c
  · exact Finset.mem_insert.mpr (Or.inl h.2)
  · exact Finset.mem_insert.mpr (Or.inr <|
      mem_rowNeighbors.mpr ⟨i, hiR, hij, h⟩)

/--
The zero-submatrix definition of full indecomposability is equivalent to the
strict Hall inequalities.
-/
theorem fullyIndecomposable_iff_strictHall {n : ℕ}
    (S : Fin n → Fin n → Prop) :
    FullyIndecomposable S ↔ StrictHall S := by
  classical
  constructor
  · intro hfi R hR hRproper
    by_contra hnot
    have hNle : (rowNeighbors S R).card ≤ R.card := Nat.le_of_not_gt hnot
    let C₀ : Finset (Fin n) := Finset.univ \ rowNeighbors S R
    have hC₀card : C₀.card = n - (rowNeighbors S R).card := by
      rw [show C₀ = Finset.univ \ rowNeighbors S R by rfl,
        Finset.card_sdiff_of_subset (Finset.subset_univ _)]
      simp
    have hsize : n - R.card ≤ C₀.card := by
      omega
    obtain ⟨C, hCC₀, hCcard⟩ := Finset.exists_subset_card_eq hsize
    have hC : C.Nonempty := Finset.card_pos.mp (by omega)
    have hsum : R.card + C.card = n := by omega
    obtain ⟨i, hiR, j, hjC, hij⟩ := hfi R C hR hC hsum
    have hjC₀ := hCC₀ hjC
    have hjN : j ∈ rowNeighbors S R := mem_rowNeighbors.mpr ⟨i, hiR, hij⟩
    exact (Finset.mem_sdiff.mp hjC₀).2 hjN
  · intro hhall R C hR hC hsum
    have hRproper : R.card < n := by
      have hCpos := Finset.card_pos.mpr hC
      omega
    have hstrict := hhall R hR hRproper
    by_contra hedge
    push Not at hedge
    have hCsub : C ⊆ Finset.univ \ rowNeighbors S R := by
      intro j hjC
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ j, ?_⟩
      intro hjN
      obtain ⟨i, hiR, hij⟩ := mem_rowNeighbors.mp hjN
      exact hedge i hiR j hjC hij
    have hcardle := Finset.card_le_card hCsub
    have hcompcard :
        (Finset.univ \ rowNeighbors S R).card =
          n - (rowNeighbors S R).card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
      simp
    rw [hcompcard] at hcardle
    omega

/--
If deleting one support edge violates strict Hall, the deleted edge exposes a
tight row set.  The deleted column loses exactly that one incident row within
the witness.  This is the witness used in Lavi's proof of Lemma 2.3.
-/
theorem exists_tight_witness_of_delete_not_strictHall {n : ℕ}
    {S : Fin n → Fin n → Prop} (hHall : StrictHall S)
    {r c : Fin n} (hdelete : ¬StrictHall (deleteEdge S r c)) :
    ∃ R : Finset (Fin n),
      R.Nonempty ∧ R.card < n ∧ r ∈ R ∧
      (rowNeighbors S R).card = R.card + 1 ∧
      c ∉ rowNeighbors (deleteEdge S r c) R ∧
      (∀ i ∈ R, S i c → i = r) := by
  classical
  unfold StrictHall at hdelete
  push Not at hdelete
  obtain ⟨R, hR, hRproper, hfail⟩ := hdelete
  have hdelLe : (rowNeighbors (deleteEdge S r c) R).card ≤ R.card :=
    hfail
  have hstrict := hHall R hR hRproper
  have hsubset := rowNeighbors_subset_insert_deleteEdge S r c R
  have hNleInsert := Finset.card_le_card hsubset
  have hInsertLe := Finset.card_insert_le c (rowNeighbors (deleteEdge S r c) R)
  have hNtight : (rowNeighbors S R).card = R.card + 1 := by omega
  have hcNot : c ∉ rowNeighbors (deleteEdge S r c) R := by
    intro hc
    have hinsert :
        insert c (rowNeighbors (deleteEdge S r c) R) =
          rowNeighbors (deleteEdge S r c) R := Finset.insert_eq_of_mem hc
    rw [hinsert] at hNleInsert
    omega
  have hrR : r ∈ R := by
    by_contra hr
    have hreverse : rowNeighbors S R ⊆
        rowNeighbors (deleteEdge S r c) R := by
      intro j hj
      obtain ⟨i, hiR, hij⟩ := mem_rowNeighbors.mp hj
      apply mem_rowNeighbors.mpr
      refine ⟨i, hiR, hij, ?_⟩
      intro h
      exact hr (h.1 ▸ hiR)
    have hcard := Finset.card_le_card hreverse
    omega
  refine ⟨R, hR, hRproper, hrR, hNtight, hcNot, ?_⟩
  intro i hiR hic
  by_contra hir
  apply hcNot
  exact mem_rowNeighbors.mpr ⟨i, hiR, hic, fun h ↦ hir h.1⟩

end LaviSection2
