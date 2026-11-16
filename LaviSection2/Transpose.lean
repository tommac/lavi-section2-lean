import LaviSection2.Definitions

/-!
# Transposition of supports and matrices

Transposing a support swaps its two colour classes.  Double stochasticity,
full indecomposability, near decomposability and the permanent are invariant
under transposition.
-/

namespace LaviSection2

/-- Transpose a bipartite support relation by swapping its color classes. -/
def transposeSupport {n : ℕ} (S : Fin n → Fin n → Prop) :
    Fin n → Fin n → Prop :=
  fun i j ↦ S j i

/-- Entrywise nonnegativity is invariant under matrix transposition. -/
theorem nonnegative_transpose {n : ℕ} {A : Square n}
    (hA : Nonnegative A) : Nonnegative A.transpose := by
  intro i j
  exact hA j i

/-- Column stochasticity becomes row stochasticity after transposition. -/
theorem rowStochastic_transpose {n : ℕ} {A : Square n}
    (hA : ColumnStochastic A) : RowStochastic A.transpose := by
  intro i
  exact hA i

/-- Row stochasticity becomes column stochasticity after transposition. -/
theorem columnStochastic_transpose {n : ℕ} {A : Square n}
    (hA : RowStochastic A) : ColumnStochastic A.transpose := by
  intro j
  exact hA j

/-- Doubly stochasticity is invariant under matrix transposition. -/
theorem doublyStochastic_transpose {n : ℕ} {A : Square n}
    (hA : DoublyStochastic A) : DoublyStochastic A.transpose := by
  exact ⟨nonnegative_transpose hA.1,
    rowStochastic_transpose hA.2.2,
    columnStochastic_transpose hA.2.1⟩

/-- Full indecomposability is invariant under swapping the color classes. -/
theorem fullyIndecomposable_transposeSupport {n : ℕ}
    {S : Fin n → Fin n → Prop}
    (hS : FullyIndecomposable S) :
    FullyIndecomposable (transposeSupport S) := by
  intro R C hR hC hcard
  obtain ⟨j, hj, i, hi, hji⟩ :=
    hS C R hC hR (by omega)
  exact ⟨i, hi, j, hj, hji⟩

/-- Deleting an edge commutes with support transposition. -/
theorem transposeSupport_deleteEdge {n : ℕ}
    (S : Fin n → Fin n → Prop) (i j : Fin n) :
    transposeSupport (deleteEdge S i j) =
      deleteEdge (transposeSupport S) j i := by
  funext a b
  apply propext
  constructor
  · rintro ⟨hab, hne⟩
    exact ⟨hab, fun hbad ↦ hne ⟨hbad.2, hbad.1⟩⟩
  · rintro ⟨hab, hne⟩
    exact ⟨hab, fun hbad ↦ hne ⟨hbad.2, hbad.1⟩⟩

/-- Swapping the two color classes twice returns the original support. -/
theorem transposeSupport_transposeSupport {n : ℕ}
    (S : Fin n → Fin n → Prop) :
    transposeSupport (transposeSupport S) = S := by
  rfl

/-- Near decomposability is invariant under swapping the color classes. -/
theorem nearlyDecomposable_transposeSupport {n : ℕ}
    {S : Fin n → Fin n → Prop}
    (hS : NearlyDecomposable S) :
    NearlyDecomposable (transposeSupport S) := by
  refine ⟨fullyIndecomposable_transposeSupport hS.1, ?_⟩
  intro i j hij hdeleted
  have hback := fullyIndecomposable_transposeSupport hdeleted
  rw [transposeSupport_deleteEdge, transposeSupport_transposeSupport] at hback
  have horiginal : FullyIndecomposable (deleteEdge S j i) := hback
  exact hS.2 j i hij horiginal

/-- The permanent `permanent` is invariant under transposition. -/
theorem permanent_transpose {n : ℕ} (A : Square n) :
    permanent A.transpose = permanent A := by
  change Matrix.permanent A = Matrix.permanent A.transpose
  exact (Matrix.permanent_transpose A).symm

/-- The support of a transposed matrix is the transposed support relation. -/
theorem support_transpose {n : ℕ} (A : Square n) :
    support A.transpose = transposeSupport (support A) := by
  rfl

end LaviSection2
