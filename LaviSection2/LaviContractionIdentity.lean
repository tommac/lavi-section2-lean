import LaviSection2.Definitions
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Lavi Lemma 2.2: the contraction identity

This module formalizes the algebra behind Lemma 2.2 of Lavi's preprint
(Foregger's contraction identity).

Let column `c` of an `(m+1) × (m+1)` matrix `A` be supported on two distinct
rows `r` and `s`.  Contracting at `c` deletes column `c` and row `s`, and adds
row `s` into row `r`.  The result `contractMatrix A r s c` is an honest
`m × m` matrix: rows are indexed through `s.succAbove` and columns through
`c.succAbove`.

The main results are:

* `permanent_succ_column`: cofactor (Laplace) expansion of the permanent
  along any column, which Mathlib does not provide;
* `permanent_contractMatrix`: for every such matrix,
  `per C(A) = per A(r|c) + per A(s|c)`, with no minimizer hypothesis;
* `permanent_contractMatrix_eq_two_mul`: under the cofactor equalities (2.1)
  at the two positive entries of column `c`, `per C(A) = 2 per A`, which is
  equation (2.2);
* `doublyStochastic_contractMatrix`: contraction of a doubly stochastic
  matrix is doubly stochastic of order `m`;
* `rho_contractMatrix`: under (2.1), contraction preserves
  `ρ = 2^(n-1) per A`, which is how Lemma 2.2 feeds the induction;
* `permanent_two_entry_column`: the two-term expansion at a column with two
  positive entries.

The cofactor equalities themselves (Lavi Lemma 2.1, due to Foregger) are a
hypothesis here, not a proved fact.
-/

namespace LaviSection2

open Matrix Equiv Finset
open scoped BigOperators

section Expansion

/-- Cofactor expansion of Mathlib's permanent along column `0`. -/
theorem matrix_permanent_succ_column_zero {m : ℕ}
    (M : Matrix (Fin m.succ) (Fin m.succ) ℝ) :
    M.permanent =
      ∑ i : Fin m.succ, M i 0 * (M.submatrix i.succAbove Fin.succ).permanent := by
  rw [Matrix.permanent, Finset.univ_perm_fin_succ, ← Finset.univ_product_univ]
  simp only [Finset.sum_map, Equiv.toEmbedding_apply, Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [Fin.prod_univ_succ, Matrix.permanent, Finset.mul_sum,
      Perm.decomposeFin_symm_apply_zero, Perm.decomposeFin_symm_apply_succ,
      Equiv.swap_self, Equiv.coe_refl, id, Fin.succAbove_zero,
      Matrix.submatrix_apply]
  · rw [← permanent_permute_cols (Fin.cycleRange i), Matrix.permanent,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Fin.prod_univ_succ]
    simp only [Perm.decomposeFin_symm_apply_zero,
      Perm.decomposeFin_symm_apply_succ, Matrix.submatrix_apply, id,
      Fin.succAbove_cycleRange]

/-- The permanent `permanent` agrees with Mathlib's permanent. -/
theorem permanent_eq_matrix_permanent {n : ℕ} (A : Square n) :
    permanent A = A.permanent := by
  rw [← Matrix.permanent_transpose]
  rfl

/-- The cofactor `per A(i|j)`: delete row `i` and column `j`. -/
noncomputable def cofactor {m : ℕ} (A : Square (m + 1)) (i j : Fin (m + 1)) : ℝ :=
  permanent (A.submatrix i.succAbove j.succAbove)

/-- Cofactor expansion of the permanent along an arbitrary column `c`. -/
theorem permanent_succ_column {m : ℕ} (A : Square (m + 1)) (c : Fin (m + 1)) :
    permanent A = ∑ i, A i c * cofactor A i c := by
  have h := matrix_permanent_succ_column_zero (A.submatrix id c.cycleRange.symm)
  rw [permanent_permute_rows] at h
  rw [permanent_eq_matrix_permanent, h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cofactor, permanent_eq_matrix_permanent, Matrix.submatrix_submatrix]
  simp only [Matrix.submatrix_apply, id, Fin.cycleRange_symm_zero]
  congr 2
  funext k j
  simp [Matrix.submatrix_apply, Fin.cycleRange_symm_succ]

/-- The permanent is additive in a single row. -/
theorem permanent_add_row {m : ℕ} (M : Square m) (i0 : Fin m) (u v : Fin m → ℝ)
    (h : ∀ j, M i0 j = u j + v j) :
    permanent M = permanent (M.updateRow i0 u) + permanent (M.updateRow i0 v) := by
  simp only [permanent, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i0),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i0),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i0)]
  have hrest : ∀ w : Fin m → ℝ,
      ∏ k ∈ Finset.univ.erase i0, M.updateRow i0 w k (σ k) =
        ∏ k ∈ Finset.univ.erase i0, M k (σ k) := by
    intro w
    refine Finset.prod_congr rfl fun k hk => ?_
    rw [Matrix.updateRow_ne (Finset.ne_of_mem_erase hk)]
  rw [hrest, hrest, Matrix.updateRow_self, Matrix.updateRow_self, h]
  ring

/--
Reindexing the rows of a minor: if `f` is an injective row map avoiding `r`,
the minor through `f` has the same permanent as the minor deleting `r`.
-/
theorem permanent_submatrix_rows_avoiding {m : ℕ} (A : Square (m + 1))
    (r : Fin (m + 1)) (f : Fin m → Fin (m + 1)) (hf : Function.Injective f)
    (hfr : ∀ k, f k ≠ r) (cols : Fin m → Fin (m + 1)) :
    permanent (A.submatrix f cols) = permanent (A.submatrix r.succAbove cols) := by
  let g : Fin m → Fin m := fun k => (finSuccAboveEquiv r).symm ⟨f k, hfr k⟩
  have hg : Function.Injective g := by
    intro a b hab
    apply hf
    have := congrArg (fun x => ((finSuccAboveEquiv r) x : Fin (m + 1))) hab
    simpa [g] using this
  let π : Perm (Fin m) := Equiv.ofBijective g hg.bijective_of_finite
  have hπ : ∀ k, r.succAbove (π k) = f k := by
    intro k
    have h1 := congrArg Subtype.val ((finSuccAboveEquiv r).apply_symm_apply ⟨f k, hfr k⟩)
    rw [finSuccAboveEquiv_apply] at h1
    exact h1
  have hEq : A.submatrix f cols = (A.submatrix r.succAbove cols).submatrix π id := by
    ext i j
    simp [hπ]
  rw [hEq, permanent_eq_matrix_permanent, permanent_permute_cols,
    ← permanent_eq_matrix_permanent]

end Expansion

section Contraction

/--
Lavi's contraction at column `c`, whose positive entries lie in rows `r ≠ s`:
delete column `c` and row `s`, and add row `s` into row `r`.  The result is an
`m × m` matrix.
-/
def contractMatrix {m : ℕ} (A : Square (m + 1)) (r s c : Fin (m + 1)) : Square m :=
  fun i j ↦
    if s.succAbove i = r then A r (c.succAbove j) + A s (c.succAbove j)
    else A (s.succAbove i) (c.succAbove j)

/--
The contraction identity, valid for every matrix:
`per C(A) = per A(r|c) + per A(s|c)`.
-/
theorem permanent_contractMatrix {m : ℕ} (A : Square (m + 1))
    {r s : Fin (m + 1)} (hrs : r ≠ s) (c : Fin (m + 1)) :
    permanent (contractMatrix A r s c) = cofactor A r c + cofactor A s c := by
  obtain ⟨i0, hi0⟩ := Fin.exists_succAbove_eq hrs
  rw [permanent_add_row (contractMatrix A r s c) i0
      (fun j => A r (c.succAbove j)) (fun j => A s (c.succAbove j))
      (by intro j; simp [contractMatrix, hi0])]
  have h1 : (contractMatrix A r s c).updateRow i0 (fun j => A r (c.succAbove j)) =
      A.submatrix s.succAbove c.succAbove := by
    ext i j
    by_cases hi : i = i0
    · subst hi
      simp [hi0]
    · have hne : s.succAbove i ≠ r := by
        rw [← hi0]
        exact fun h => hi (Fin.succAbove_right_injective h)
      simp [Matrix.updateRow_ne hi, contractMatrix, hne]
  let f : Fin m → Fin (m + 1) := Function.update s.succAbove i0 s
  have h2 : (contractMatrix A r s c).updateRow i0 (fun j => A s (c.succAbove j)) =
      A.submatrix f c.succAbove := by
    ext i j
    by_cases hi : i = i0
    · subst hi
      simp [f]
    · have hne : s.succAbove i ≠ r := by
        rw [← hi0]
        exact fun h => hi (Fin.succAbove_right_injective h)
      simp [Matrix.updateRow_ne hi, contractMatrix, hne, f, Function.update_of_ne hi]
  have hf : Function.Injective f := by
    intro a b hab
    by_cases ha : a = i0 <;> by_cases hb : b = i0
    · rw [ha, hb]
    · exfalso
      simp only [f, ha, Function.update_self, Function.update_of_ne hb] at hab
      exact Fin.succAbove_ne s b hab.symm
    · exfalso
      simp only [f, hb, Function.update_self, Function.update_of_ne ha] at hab
      exact Fin.succAbove_ne s a hab
    · simp only [f, Function.update_of_ne ha, Function.update_of_ne hb] at hab
      exact Fin.succAbove_right_injective hab
  have hfr : ∀ k, f k ≠ r := by
    intro k
    by_cases hk : k = i0
    · simp only [f, hk, Function.update_self]
      exact hrs.symm
    · simp only [f, Function.update_of_ne hk]
      rw [← hi0]
      exact fun h => hk (Fin.succAbove_right_injective h)
  rw [h1, h2, permanent_submatrix_rows_avoiding A r f hf hfr, add_comm]
  rfl

/--
Lavi Lemma 2.2 (Foregger's contraction identity, equation (2.2)).  If the two
cofactors at the positive entries of column `c` equal `per A`, as Lemma 2.1
provides at a face minimizer, then `per C(A) = 2 per A`.
-/
theorem permanent_contractMatrix_eq_two_mul {m : ℕ} (A : Square (m + 1))
    {r s : Fin (m + 1)} (hrs : r ≠ s) (c : Fin (m + 1))
    (hr : cofactor A r c = permanent A) (hs : cofactor A s c = permanent A) :
    permanent (contractMatrix A r s c) = 2 * permanent A := by
  rw [permanent_contractMatrix A hrs c, hr, hs]
  ring

/-- Under the same hypotheses, contraction preserves `ρ = 2^(n-1) per A`. -/
theorem rho_contractMatrix {m : ℕ} (hm : 1 ≤ m) (A : Square (m + 1))
    {r s : Fin (m + 1)} (hrs : r ≠ s) (c : Fin (m + 1))
    (hr : cofactor A r c = permanent A) (hs : cofactor A s c = permanent A) :
    rho (contractMatrix A r s c) = rho A := by
  rw [rho, rho, permanent_contractMatrix_eq_two_mul A hrs c hr hs]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  simp only [Nat.add_sub_cancel_left, Nat.add_sub_cancel]
  ring

/--
Contracting a column supported on two distinct rows of a doubly stochastic
matrix gives a doubly stochastic matrix of order `m`.
-/
theorem doublyStochastic_contractMatrix {m : ℕ} (A : Square (m + 1))
    {r s c : Fin (m + 1)} (hrs : r ≠ s) (hA : DoublyStochastic A)
    (hc : ∀ i, i ≠ r → i ≠ s → A i c = 0) :
    DoublyStochastic (contractMatrix A r s c) := by
  obtain ⟨hnn, hrow, hcol⟩ := hA
  obtain ⟨i0, hi0⟩ := Fin.exists_succAbove_eq hrs
  have hcolc : A r c + A s c = 1 := by
    have h := hcol c
    rw [Fin.sum_univ_succAbove _ s] at h
    have hsum : ∑ i : Fin m, A (s.succAbove i) c = A r c := by
      rw [Finset.sum_eq_single i0
        (fun b _ hb => hc _
          (fun h => hb (Fin.succAbove_right_injective (h.trans hi0.symm)))
          (Fin.succAbove_ne s b))
        (fun h => absurd (Finset.mem_univ _) h), hi0]
    linarith
  have hrowc : ∀ k, ∑ j, A k (c.succAbove j) = 1 - A k c := by
    intro k
    have h := hrow k
    rw [Fin.sum_univ_succAbove _ c] at h
    linarith
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    unfold contractMatrix
    split_ifs
    · exact add_nonneg (hnn _ _) (hnn _ _)
    · exact hnn _ _
  · intro i
    unfold contractMatrix
    split_ifs with h
    · rw [Finset.sum_add_distrib, hrowc, hrowc]
      linarith
    · rw [hrowc, hc _ h (Fin.succAbove_ne s i)]
      ring
  · intro j
    have hsplit : ∀ i, contractMatrix A r s c i j =
        A (s.succAbove i) (c.succAbove j) +
          if i = i0 then A s (c.succAbove j) else 0 := by
      intro i
      by_cases hi : i = i0
      · subst hi
        simp [contractMatrix, hi0]
      · have hne : s.succAbove i ≠ r := by
          rw [← hi0]
          exact fun h => hi (Fin.succAbove_right_injective h)
        simp [contractMatrix, hne, hi]
    simp only [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
    have h := hcol (c.succAbove j)
    rw [Fin.sum_univ_succAbove _ s] at h
    linarith

/--
At a column supported on two rows, the expansion has two terms:
`per A = a_{rc} per A(r|c) + a_{sc} per A(s|c)`.
-/
theorem permanent_two_entry_column {m : ℕ} (A : Square (m + 1))
    {r s c : Fin (m + 1)} (hrs : r ≠ s) (hc : ∀ i, i ≠ r → i ≠ s → A i c = 0) :
    permanent A = A r c * cofactor A r c + A s c * cofactor A s c := by
  rw [permanent_succ_column A c]
  have hpair := Finset.sum_pair (f := fun i => A i c * cofactor A i c) hrs
  rw [← hpair]
  refine (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_).symm
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
  rw [hc i hi.1 hi.2, zero_mul]

/--
Consistency check: under the cofactor equalities, the two-term expansion
reduces to the column sum, so `per A = (a_{rc} + a_{sc}) per A`.
-/
theorem permanent_eq_column_mass_mul {m : ℕ} (A : Square (m + 1))
    {r s c : Fin (m + 1)} (hrs : r ≠ s) (hc : ∀ i, i ≠ r → i ≠ s → A i c = 0)
    (hr : cofactor A r c = permanent A) (hs : cofactor A s c = permanent A) :
    permanent A = (A r c + A s c) * permanent A := by
  conv_lhs => rw [permanent_two_entry_column A hrs hc, hr, hs]
  ring

end Contraction

end LaviSection2
