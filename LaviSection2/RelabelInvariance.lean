import LaviSection2.Definitions

/-!
# Independent row and column relabelling

Foregger's equality class and Lavi's proof are stated only up to independent
permutations of the two colour classes.  This module proves that all of the
theorem-facing matrix and support predicates are invariant under that action.
-/

namespace LaviSection2

open scoped BigOperators

/-- Independently relabel a bipartite support relation. -/
def relabelSupport {n : ℕ} (r c : Equiv.Perm (Fin n))
    (S : Fin n → Fin n → Prop) : Fin n → Fin n → Prop :=
  fun i j ↦ S (r i) (c j)

/-- The permanent is unchanged by independent row and column permutations. -/
theorem permanent_relabel {n : ℕ} (r c : Equiv.Perm (Fin n)) (A : Square n) :
    permanent (relabel r c A) = permanent A := by
  change Matrix.permanent (relabel r c A).transpose =
    Matrix.permanent A.transpose
  rw [show (relabel r c A).transpose = A.transpose.submatrix c r by rfl]
  rw [show A.transpose.submatrix c r =
    (A.transpose.submatrix c id).submatrix id r by rfl]
  rw [Matrix.permanent_permute_rows, Matrix.permanent_permute_cols]

/-- Entrywise nonnegativity is invariant under independent relabelling. -/
theorem nonnegative_relabel {n : ℕ} (r c : Equiv.Perm (Fin n))
    {A : Square n} (hA : Nonnegative A) : Nonnegative (relabel r c A) := by
  intro i j
  exact hA (r i) (c j)

/-- Row stochasticity is invariant under independent relabelling. -/
theorem rowStochastic_relabel {n : ℕ} (r c : Equiv.Perm (Fin n))
    {A : Square n} (hA : RowStochastic A) : RowStochastic (relabel r c A) := by
  intro i
  calc
    ∑ j, relabel r c A i j = ∑ j, A (r i) j := by
      simpa [relabel] using (Equiv.sum_comp c (fun j ↦ A (r i) j))
    _ = 1 := hA (r i)

/-- Column stochasticity is invariant under independent relabelling. -/
theorem columnStochastic_relabel {n : ℕ} (r c : Equiv.Perm (Fin n))
    {A : Square n} (hA : ColumnStochastic A) : ColumnStochastic (relabel r c A) := by
  intro j
  calc
    ∑ i, relabel r c A i j = ∑ i, A i (c j) := by
      simpa [relabel] using (Equiv.sum_comp r (fun i ↦ A i (c j)))
    _ = 1 := hA (c j)

/-- Doubly stochasticity is invariant under independent relabelling. -/
theorem doublyStochastic_relabel {n : ℕ} (r c : Equiv.Perm (Fin n))
    {A : Square n} (hA : DoublyStochastic A) :
    DoublyStochastic (relabel r c A) := by
  exact ⟨nonnegative_relabel r c hA.1,
    rowStochastic_relabel r c hA.2.1,
    columnStochastic_relabel r c hA.2.2⟩

/-- The matrix support operation commutes with independent relabelling. -/
theorem support_relabel {n : ℕ} (r c : Equiv.Perm (Fin n)) (A : Square n) :
    support (relabel r c A) = relabelSupport r c (support A) := by
  rfl

/-- Full indecomposability is preserved by independent relabelling. -/
theorem fullyIndecomposable_relabelSupport {n : ℕ}
    (r c : Equiv.Perm (Fin n)) {S : Fin n → Fin n → Prop}
    (hS : FullyIndecomposable S) :
    FullyIndecomposable (relabelSupport r c S) := by
  intro R C hR hC hcard
  let R' := R.map r.toEmbedding
  let C' := C.map c.toEmbedding
  have hR' : R'.Nonempty := by
    simpa [R'] using hR.map (f := r.toEmbedding)
  have hC' : C'.Nonempty := by
    simpa [C'] using hC.map (f := c.toEmbedding)
  have hcard' : R'.card + C'.card = n := by
    simpa [R', C'] using hcard
  obtain ⟨ri, hri, cj, hcj, hSc⟩ := hS R' C' hR' hC' hcard'
  rcases Finset.mem_map.mp hri with ⟨i, hi, rfl⟩
  rcases Finset.mem_map.mp hcj with ⟨j, hj, rfl⟩
  exact ⟨i, hi, j, hj, hSc⟩

/-- Edge deletion commutes with independent support relabelling. -/
theorem relabelSupport_deleteEdge {n : ℕ}
    (r c : Equiv.Perm (Fin n)) (S : Fin n → Fin n → Prop) (i j : Fin n) :
    relabelSupport r c (deleteEdge S (r i) (c j)) =
      deleteEdge (relabelSupport r c S) i j := by
  funext a b
  simp [relabelSupport, deleteEdge]

/-- Near decomposability is preserved by independent relabelling. -/
theorem nearlyDecomposable_relabelSupport {n : ℕ}
    (r c : Equiv.Perm (Fin n)) {S : Fin n → Fin n → Prop}
    (hS : NearlyDecomposable S) :
    NearlyDecomposable (relabelSupport r c S) := by
  refine ⟨fullyIndecomposable_relabelSupport r c hS.1, ?_⟩
  intro i j hij hdeleted
  have hback :=
    fullyIndecomposable_relabelSupport r.symm c.symm hdeleted
  have heq :
      relabelSupport r.symm c.symm
          (deleteEdge (relabelSupport r c S) i j) =
        deleteEdge S (r i) (c j) := by
    funext a b
    simp only [relabelSupport, deleteEdge, Equiv.apply_symm_apply,
      Equiv.symm_apply_eq]
  rw [heq] at hback
  exact hS.2 (r i) (c j) hij hback

/--
The complete theorem-facing data are invariant under independent row and
column relabelling.
-/
theorem relabel_preserves_foregger_data {n : ℕ}
    (r c : Equiv.Perm (Fin n)) {A : Square n}
    (hds : DoublyStochastic A)
    (hnd : NearlyDecomposable (support A)) :
    DoublyStochastic (relabel r c A) ∧
      NearlyDecomposable (support (relabel r c A)) ∧
      permanent (relabel r c A) = permanent A := by
  refine ⟨doublyStochastic_relabel r c hds, ?_, permanent_relabel r c A⟩
  rw [support_relabel]
  exact nearlyDecomposable_relabelSupport r c hnd

end LaviSection2
