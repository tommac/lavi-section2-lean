import LaviSection2.LaviContractionIdentity
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Lavi Lemma 2.1: cofactor equalization at a face minimizer

Let `Ω(D)` be the face of doubly stochastic matrices supported in `D`.  This
module proves the cofactor half of Lavi's Lemma 2.1 (Foregger's Lemma 1):
if `A` minimizes the permanent on `Ω(D)`, then

  `per A(i|j) = per A`   at every position with `a_ij ≠ 0`,

which is equation (2.1).

The proof is self-contained and needs no connectivity hypothesis on `D`.
Write `C_ij = per A(i|j)`, `P = per A` and `X_ij = a_ij (C_ij - P)`.  The row
and column cofactor expansions show that `X` has zero line sums, and `X` is
supported where `A` is positive, so `A + tX` stays in `Ω(D)` for small `|t|`.
The derivative of `t ↦ per (A + tX)` at `0` is `Σ C_ij X_ij`, which vanishes
at a minimizer.  Subtracting `P Σ X_ij = 0` gives `Σ a_ij (C_ij - P)^2 = 0`,
so `C_ij = P` wherever `a_ij > 0`.

The other half of Lemma 2.1, that the support of a face minimizer is fully
indecomposable when `D` is, is not proved here.

`faceMinimizer_contraction` combines this with Lemma 2.2: at a face minimizer,
contracting a column with exactly two positive entries doubles the permanent,
preserves `ρ`, and preserves double stochasticity, with no remaining
hypothesis.
-/

namespace LaviSection2

open Matrix Equiv Finset Filter Topology
open scoped BigOperators

/-- `A` lies in the face `Ω(D)`: doubly stochastic with support inside `D`. -/
def InFace {n : ℕ} (D : Fin n → Fin n → Prop) (A : Square n) : Prop :=
  DoublyStochastic A ∧ ∀ i j, A i j ≠ 0 → D i j

/-- `A` minimizes the permanent on the face `Ω(D)`. -/
def FaceMinimizer {n : ℕ} (D : Fin n → Fin n → Prop) (A : Square n) : Prop :=
  InFace D A ∧ ∀ B, InFace D B → permanent A ≤ permanent B

section Cofactor

variable {m : ℕ}

/-- Transposition preserves the permanent `permanent`. -/
theorem permanent_transpose' {n : ℕ} (A : Square n) : permanent Aᵀ = permanent A := by
  rw [permanent_eq_matrix_permanent, permanent_eq_matrix_permanent,
    Matrix.permanent_transpose]

/-- The cofactor as a sum over the permutations sending `i` to `j`. -/
theorem cofactor_eq_sum_filter (A : Square (m + 1)) (i j : Fin (m + 1)) :
    cofactor A i j =
      ∑ σ ∈ (univ : Finset (Perm (Fin (m + 1)))).filter (fun σ => σ i = j),
        ∏ k ∈ univ.erase i, A k (σ k) := by
  classical
  set M : Square (m + 1) := A.updateRow i (Pi.single j 1) with hM
  -- Step 1: the cofactor is the permanent of `M`.
  have h1 : cofactor A i j = permanent M := by
    rw [← permanent_transpose' M, permanent_succ_column Mᵀ i]
    rw [Finset.sum_eq_single j]
    · have hsub : Mᵀ.submatrix j.succAbove i.succAbove =
          (A.submatrix i.succAbove j.succAbove)ᵀ := by
        ext a b
        simp [hM]
      have hMji : Mᵀ j i = 1 := by simp [hM]
      rw [hMji, one_mul]
      unfold cofactor
      rw [hsub, permanent_transpose']
    · intro k _ hk
      simp [hM, Pi.single_eq_of_ne hk]
    · intro h
      exact absurd (Finset.mem_univ j) h
  -- Step 2: expand the permanent of `M` along its unit row.
  rw [h1, permanent, Finset.sum_filter]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have hrest : ∏ k ∈ univ.erase i, M k (σ k) = ∏ k ∈ univ.erase i, A k (σ k) := by
    refine Finset.prod_congr rfl fun k hk => ?_
    rw [hM, Matrix.updateRow_ne (Finset.ne_of_mem_erase hk)]
  rw [hrest, hM, Matrix.updateRow_self]
  by_cases hσ : σ i = j
  · simp [hσ]
  · simp [hσ]

/-- Cofactor expansion of the permanent along an arbitrary row `i`. -/
theorem permanent_row_expansion (A : Square (m + 1)) (i : Fin (m + 1)) :
    permanent A = ∑ j, A i j * cofactor A i j := by
  classical
  rw [permanent]
  calc ∑ σ : Perm (Fin (m + 1)), ∏ k, A k (σ k)
      = ∑ σ : Perm (Fin (m + 1)), A i (σ i) * ∏ k ∈ univ.erase i, A k (σ k) :=
        Finset.sum_congr rfl fun σ _ =>
          (Finset.mul_prod_erase univ (fun k => A k (σ k)) (Finset.mem_univ i)).symm
    _ = ∑ j, ∑ σ ∈ (univ : Finset (Perm (Fin (m + 1)))).filter (fun σ => σ i = j),
          A i (σ i) * ∏ k ∈ univ.erase i, A k (σ k) :=
        (Finset.sum_fiberwise _ _ _).symm
    _ = ∑ j, A i j * cofactor A i j := by
        simp_rw [cofactor_eq_sum_filter, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun σ hσ => ?_
        rw [(Finset.mem_filter.1 hσ).2]

/--
The directional derivative of the permanent:
`d/dt per (A + tX) |_{t=0} = Σ_ij X_ij per A(i|j)`.
-/
theorem hasDerivAt_permanent_add_smul (A X : Square (m + 1)) :
    HasDerivAt (fun t : ℝ => permanent (A + t • X))
      (∑ i, ∑ j, X i j * cofactor A i j) 0 := by
  classical
  have hfun : (fun t : ℝ => permanent (A + t • X)) =
      fun t => ∑ σ : Perm (Fin (m + 1)), ∏ k, (A k (σ k) + t * X k (σ k)) := by
    funext t
    simp [permanent]
  rw [hfun]
  have hσ : ∀ σ : Perm (Fin (m + 1)),
      HasDerivAt (fun t : ℝ => ∏ k, (A k (σ k) + t * X k (σ k)))
        (∑ k, (∏ l ∈ univ.erase k, A l (σ l)) * X k (σ k)) 0 := by
    intro σ
    have hk : ∀ k ∈ (univ : Finset (Fin (m + 1))),
        HasDerivAt (fun t : ℝ => A k (σ k) + t * X k (σ k)) (X k (σ k)) 0 := by
      intro k _
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (X k (σ k))).const_add (A k (σ k))
    have := HasDerivAt.fun_finsetProd hk
    simpa [smul_eq_mul] using this
  have hsum := HasDerivAt.fun_sum (u := (univ : Finset (Perm (Fin (m + 1)))))
    (fun σ _ => hσ σ)
  refine hsum.congr_deriv ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [cofactor_eq_sum_filter, Finset.mul_sum]
  rw [← Finset.sum_fiberwise (univ : Finset (Perm (Fin (m + 1)))) (fun σ => σ i)]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun σ hσ => ?_
  rw [(Finset.mem_filter.1 hσ).2, mul_comm]

end Cofactor

section Equalization

variable {m : ℕ}

/--
Lavi Lemma 2.1, cofactor half (equation (2.1)).  At a permanent minimizer on
any face `Ω(D)`, every cofactor at a positive position equals the permanent.
-/
theorem faceMinimizer_cofactor_eq {D : Fin (m + 1) → Fin (m + 1) → Prop}
    {A : Square (m + 1)} (hA : FaceMinimizer D A) {i j : Fin (m + 1)}
    (hij : A i j ≠ 0) :
    cofactor A i j = permanent A := by
  classical
  obtain ⟨⟨⟨hnn, hrow, hcol⟩, hsupp⟩, hmin⟩ := hA
  set P := permanent A with hP
  let Y : Square (m + 1) := fun a b => cofactor A a b - P
  let X : Square (m + 1) := fun a b => A a b * Y a b
  have hrowE : ∀ a, ∑ b, A a b * cofactor A a b = P := fun a =>
    (permanent_row_expansion A a).symm
  have hcolE : ∀ b, ∑ a, A a b * cofactor A a b = P := fun b =>
    (permanent_succ_column A b).symm
  have hXrow : ∀ a, ∑ b, X a b = 0 := by
    intro a
    simp only [X, Y, mul_sub, Finset.sum_sub_distrib, hrowE, ← Finset.sum_mul, hrow a]
    ring
  have hXcol : ∀ b, ∑ a, X a b = 0 := by
    intro b
    simp only [X, Y, mul_sub, Finset.sum_sub_distrib, hcolE, ← Finset.sum_mul, hcol b]
    ring
  -- The perturbation stays in the face for small `|t|`.
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ a b, 0 < 1 + t * Y a b := by
    rw [Filter.eventually_all]
    intro a
    rw [Filter.eventually_all]
    intro b
    have ht : Tendsto (fun t : ℝ => 1 + t * Y a b) (𝓝 0) (𝓝 (1 + 0 * Y a b)) :=
      (by fun_prop : Continuous (fun t : ℝ => 1 + t * Y a b)).tendsto 0
    rw [zero_mul, add_zero] at ht
    exact ht.eventually (lt_mem_nhds one_pos)
  have hloc : IsLocalMin (fun t : ℝ => permanent (A + t • X)) 0 := by
    filter_upwards [hev] with t ht
    simp only [zero_smul, add_zero]
    apply hmin
    have hentry : ∀ a b, (A + t • X) a b = A a b * (1 + t * Y a b) := by
      intro a b
      simp [X]
      ring
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro a b
      rw [hentry]
      exact mul_nonneg (hnn a b) (ht a b).le
    · intro a
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        Finset.sum_add_distrib, ← Finset.mul_sum, hXrow a, hrow a]
      ring
    · intro b
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        Finset.sum_add_distrib, ← Finset.mul_sum, hXcol b, hcol b]
      ring
    · intro a b hab
      apply hsupp
      intro h0
      apply hab
      rw [hentry, h0, zero_mul]
  have hderiv := hloc.hasDerivAt_eq_zero (hasDerivAt_permanent_add_smul A X)
  -- `Σ a_ij (C_ij - P)^2 = Σ X_ij C_ij - P Σ X_ij = 0`.
  have hsq : ∑ a, ∑ b, A a b * Y a b ^ 2 = 0 := by
    have hXP : ∑ a, ∑ b, X a b * P = 0 := by
      simp only [← Finset.sum_mul, hXrow, Finset.sum_const_zero, zero_mul]
    have : ∑ a, ∑ b, A a b * Y a b ^ 2 =
        ∑ a, ∑ b, X a b * cofactor A a b - ∑ a, ∑ b, X a b * P := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [X, Y]
      ring
    rw [this, hderiv, hXP, sub_zero]
  have hterm_nonneg : ∀ a b, 0 ≤ A a b * Y a b ^ 2 := fun a b =>
    mul_nonneg (hnn a b) (sq_nonneg _)
  have hrow0 := (Fintype.sum_eq_zero_iff_of_nonneg fun a =>
    Finset.sum_nonneg fun b _ => hterm_nonneg a b).1 hsq
  have hij0 := (Fintype.sum_eq_zero_iff_of_nonneg (hterm_nonneg i)).1
    (congrFun hrow0 i)
  have h2 : A i j * Y i j ^ 2 = 0 := congrFun hij0 j
  rcases mul_eq_zero.1 h2 with h | h
  · exact absurd h hij
  · have : Y i j = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
    simp only [Y] at this
    linarith

/--
Lemmas 2.1 and 2.2 together.  At a permanent minimizer on any face, contract
a column whose positive entries are exactly in rows `r ≠ s`.  The contraction
is doubly stochastic, doubles the permanent, and preserves `ρ` (for order at
least three).
-/
theorem faceMinimizer_contraction {D : Fin (m + 1) → Fin (m + 1) → Prop}
    {A : Square (m + 1)} (hA : FaceMinimizer D A) {r s c : Fin (m + 1)}
    (hrs : r ≠ s) (hr : A r c ≠ 0) (hs : A s c ≠ 0)
    (hc : ∀ i, i ≠ r → i ≠ s → A i c = 0) :
    DoublyStochastic (contractMatrix A r s c) ∧
      permanent (contractMatrix A r s c) = 2 * permanent A ∧
      (1 ≤ m → rho (contractMatrix A r s c) = rho A) := by
  have hcr := faceMinimizer_cofactor_eq hA hr
  have hcs := faceMinimizer_cofactor_eq hA hs
  refine ⟨doublyStochastic_contractMatrix A hrs hA.1.1 hc,
    permanent_contractMatrix_eq_two_mul A hrs c hcr hcs, fun hm => ?_⟩
  exact rho_contractMatrix hm A hrs c hcr hcs

end Equalization

end LaviSection2
