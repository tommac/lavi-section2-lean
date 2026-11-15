import LaviSection2.LaviMinimizerSupport
import Mathlib.Algebra.BigOperators.Field

/-!
# Lavi Section 3: matching entropy and the Gibbs inequality

Laws on perfect matchings are probability vectors on permutations.  For a
matrix `X`, a law `μ` *has marginal* `X` when `∑_{σ i = j} μ σ = X i j` for
every position.  Lavi's functional is

`F(X) = Ent*(X) - ∑_rows Ent(X_i)`,

where `Ent*(X)` is the supremum of the Shannon entropy of laws with marginal
`X`.  Because such a law is automatically supported on matchings inside the
support of `X`, the functional does not depend on the ambient face `D`.

This file proves the first inequality of Lavi's Lemma 3.1, the finite Gibbs
inequality `Ent(μ) - ∑_rows Ent(X_i) ≤ log per X`, together with the Gibbs-law
toolkit used for the converse inequality.
-/

namespace LaviSection2

open Finset Equiv Real

open scoped BigOperators

section Laws

variable {n : ℕ}

/-- The edge marginals of a law on permutations. -/
def marginal (μ : Perm (Fin n) → ℝ) : Square n :=
  fun i j => ∑ σ ∈ (univ : Finset (Perm (Fin n))).filter (fun σ => σ i = j), μ σ

/-- `μ` is a probability law on permutations with edge marginals `X`. -/
def IsLaw (X : Square n) (μ : Perm (Fin n) → ℝ) : Prop :=
  (∀ σ, 0 ≤ μ σ) ∧ ∑ σ, μ σ = 1 ∧ marginal μ = X

/-- Shannon entropy (natural logarithm) of a law on permutations. -/
noncomputable def lawEntropy (μ : Perm (Fin n) → ℝ) : ℝ :=
  ∑ σ, -(μ σ * log (μ σ))

/-- The sum of the row entropies of a matrix. -/
noncomputable def rowEntropy (X : Square n) : ℝ :=
  -∑ i, ∑ j, X i j * log (X i j)

/-- Lavi's maximum matching entropy `Ent*(X)`. -/
noncomputable def maxMatchingEntropy (X : Square n) : ℝ :=
  sSup (lawEntropy '' {μ | IsLaw X μ})

/-- Lavi's functional `F(X) = Ent*(X) - ∑_rows Ent(X_i)`, equation (3.2). -/
noncomputable def faceFunctional (X : Square n) : ℝ :=
  maxMatchingEntropy X - rowEntropy X

/-- Row sums of a marginal equal the total mass. -/
theorem marginal_row_sum (μ : Perm (Fin n) → ℝ) (i : Fin n) :
    ∑ j, marginal μ i j = ∑ σ, μ σ := by
  classical
  unfold marginal
  exact Finset.sum_fiberwise univ (fun σ : Perm (Fin n) => σ i) μ

/-- Column sums of a marginal equal the total mass. -/
theorem marginal_col_sum (μ : Perm (Fin n) → ℝ) (j : Fin n) :
    ∑ i, marginal μ i j = ∑ σ, μ σ := by
  classical
  unfold marginal
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have : ∀ i, (σ i = j) ↔ (i = σ.symm j) := fun i => by
    constructor
    · rintro rfl; simp
    · rintro rfl; simp
  simp_rw [this]
  simp

/-- The marginals of a probability law form a doubly stochastic matrix. -/
theorem doublyStochastic_marginal {μ : Perm (Fin n) → ℝ} (hnn : ∀ σ, 0 ≤ μ σ)
    (hsum : ∑ σ, μ σ = 1) : DoublyStochastic (marginal μ) := by
  refine ⟨fun i j => Finset.sum_nonneg fun σ _ => hnn σ, fun i => ?_, fun j => ?_⟩
  · rw [marginal_row_sum, hsum]
  · rw [marginal_col_sum, hsum]

theorem IsLaw.nonneg_entry {X : Square n} {μ : Perm (Fin n) → ℝ} (h : IsLaw X μ)
    (i j : Fin n) : 0 ≤ X i j := by
  rw [← h.2.2]
  exact Finset.sum_nonneg fun σ _ => h.1 σ

/-- A law charges a matching by at most the matrix entries it uses. -/
theorem IsLaw.le_entry {X : Square n} {μ : Perm (Fin n) → ℝ} (h : IsLaw X μ)
    (σ : Perm (Fin n)) (i : Fin n) : μ σ ≤ X i (σ i) := by
  classical
  rw [← h.2.2]
  unfold marginal
  exact Finset.single_le_sum (f := μ) (fun τ _ => h.1 τ)
    (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩)

/-- The expected log-weight of a law: `∑_σ μ σ log ∏_i A i (σ i)`
equals `∑_{ij} m_ij log A_ij` for the marginals `m` of `μ`, provided `μ` only
charges matchings with nonzero weight. -/
theorem sum_mul_log_prod (A : Square n) (μ : Perm (Fin n) → ℝ)
    (hμ : ∀ σ, μ σ ≠ 0 → ∀ i, A i (σ i) ≠ 0) :
    ∑ σ, μ σ * log (∏ i, A i (σ i)) = ∑ i, ∑ j, marginal μ i j * log (A i j) := by
  classical
  calc ∑ σ, μ σ * log (∏ i, A i (σ i))
      = ∑ σ, ∑ i, μ σ * log (A i (σ i)) := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        by_cases h0 : μ σ = 0
        · simp [h0]
        · rw [Real.log_prod (fun i _ => hμ σ h0 i), Finset.mul_sum]
    _ = ∑ i, ∑ σ, μ σ * log (A i (σ i)) := Finset.sum_comm
    _ = ∑ i, ∑ j, marginal μ i j * log (A i j) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_fiberwise univ (fun σ : Perm (Fin n) => σ i)
          (fun σ => μ σ * log (A i (σ i)))]
        refine Finset.sum_congr rfl fun j _ => ?_
        unfold marginal
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun σ hσ => ?_
        rw [(Finset.mem_filter.1 hσ).2]

/-- **Lavi Lemma 3.1, first inequality (finite Gibbs inequality).**  For every
law `μ` with marginal `X`, `Ent(μ) - ∑_rows Ent(X_i) ≤ log per X`. -/
theorem lawEntropy_sub_rowEntropy_le {X : Square n} {μ : Perm (Fin n) → ℝ}
    (h : IsLaw X μ) : lawEntropy μ - rowEntropy X ≤ log (permanent X) := by
  classical
  set w : Perm (Fin n) → ℝ := fun σ => ∏ i, X i (σ i) with hw
  have hZ : permanent X = ∑ σ, w σ := rfl
  have hwnn : ∀ σ, 0 ≤ w σ := fun σ => Finset.prod_nonneg fun i _ => h.nonneg_entry _ _
  have hwpos : ∀ σ, 0 < μ σ → 0 < w σ := fun σ hσ =>
    Finset.prod_pos fun i _ => lt_of_lt_of_le hσ (h.le_entry σ i)
  -- the permanent is positive
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ, 0 < μ σ := by
    by_contra hne
    push Not at hne
    have : ∑ σ, μ σ = 0 :=
      Finset.sum_eq_zero fun σ _ => le_antisymm (hne σ) (h.1 σ)
    rw [h.2.1] at this
    exact one_ne_zero this
  set Z := permanent X with hZdef
  have hZpos : 0 < Z := by
    rw [hZ]
    exact lt_of_lt_of_le (hwpos σ₀ hσ₀)
      (Finset.single_le_sum (fun σ _ => hwnn σ) (Finset.mem_univ σ₀))
  -- expected log-weight identity
  have hid : ∑ σ, μ σ * log (w σ) = ∑ i, ∑ j, X i j * log (X i j) := by
    rw [hw, sum_mul_log_prod X μ ?_, h.2.2]
    intro σ hσ i
    exact ne_of_gt (lt_of_lt_of_le (lt_of_le_of_ne (h.1 σ) (Ne.symm hσ)) (h.le_entry σ i))
  -- termwise bound
  have hterm : ∀ σ, -(μ σ * log (μ σ)) + μ σ * log (w σ) ≤
      w σ / Z - μ σ + μ σ * log Z := by
    intro σ
    rcases (h.1 σ).lt_or_eq with hpos | hzero
    · have hwσ := hwpos σ hpos
      have hq : 0 < w σ / (Z * μ σ) := div_pos hwσ (mul_pos hZpos hpos)
      have hlog := Real.log_le_sub_one_of_pos hq
      rw [Real.log_div (ne_of_gt hwσ) (ne_of_gt (mul_pos hZpos hpos)),
        Real.log_mul (ne_of_gt hZpos) (ne_of_gt hpos)] at hlog
      have := mul_le_mul_of_nonneg_left hlog hpos.le
      have hsimp : μ σ * (w σ / (Z * μ σ) - 1) = w σ / Z - μ σ := by
        field_simp
      nlinarith [this, hsimp]
    · rw [← hzero]
      simp only [zero_mul, neg_zero, sub_zero, add_zero]
      exact div_nonneg (hwnn σ) hZpos.le
  have hsum := Finset.sum_le_sum fun σ (_ : σ ∈ univ) => hterm σ
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_div, ← hZ, div_self (ne_of_gt hZpos), ← Finset.sum_mul, h.2.1] at hsum
  unfold lawEntropy rowEntropy
  rw [hid] at hsum
  linarith

end Laws

section Gibbs

variable {n : ℕ}

/-- The Gibbs law of a nonnegative matrix: weight proportional to the product
of the entries along the matching. -/
noncomputable def gibbsLaw (W : Square n) : Perm (Fin n) → ℝ :=
  fun σ => (∏ i, W i (σ i)) / permanent W

theorem gibbsLaw_nonneg {W : Square n} (hW : Nonnegative W) (hP : 0 < permanent W)
    (σ : Perm (Fin n)) : 0 ≤ gibbsLaw W σ :=
  div_nonneg (Finset.prod_nonneg fun _ _ => hW _ _) hP.le

theorem gibbsLaw_sum {W : Square n} (hP : 0 < permanent W) :
    ∑ σ, gibbsLaw W σ = 1 := by
  unfold gibbsLaw
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt hP)

theorem isLaw_gibbsLaw {W : Square n} (hW : Nonnegative W) (hP : 0 < permanent W) :
    IsLaw (marginal (gibbsLaw W)) (gibbsLaw W) :=
  ⟨gibbsLaw_nonneg hW hP, gibbsLaw_sum hP, rfl⟩

/-- Entropy of a Gibbs law: `Ent(q_W) = log per W - ∑ m_ij log W_ij`. -/
theorem lawEntropy_gibbsLaw {W : Square n} (hP : 0 < permanent W) :
    lawEntropy (gibbsLaw W) =
      log (permanent W) - ∑ i, ∑ j, marginal (gibbsLaw W) i j * log (W i j) := by
  classical
  have hsupp : ∀ σ, gibbsLaw W σ ≠ 0 → ∀ i, W i (σ i) ≠ 0 := by
    intro σ hσ i hi
    apply hσ
    unfold gibbsLaw
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hi, zero_div]
  rw [← sum_mul_log_prod W _ hsupp]
  unfold lawEntropy
  have hterm : ∀ σ, -(gibbsLaw W σ * log (gibbsLaw W σ)) =
      gibbsLaw W σ * log (permanent W) - gibbsLaw W σ * log (∏ i, W i (σ i)) := by
    intro σ
    by_cases h0 : ∏ i, W i (σ i) = 0
    · simp [gibbsLaw, h0]
    · unfold gibbsLaw
      rw [Real.log_div h0 (ne_of_gt hP)]
      ring
  rw [Finset.sum_congr rfl fun σ _ => hterm σ, Finset.sum_sub_distrib, ← Finset.sum_mul,
    gibbsLaw_sum hP, one_mul]

/-- Gibbs marginals in terms of cofactors: `W_ij · cof_ij = per W · m_ij`. -/
theorem mul_cofactor_eq_marginal_gibbsLaw {m : ℕ} {W : Square (m + 1)}
    (hP : permanent W ≠ 0) (i j : Fin (m + 1)) :
    W i j * cofactor W i j = permanent W * marginal (gibbsLaw W) i j := by
  classical
  unfold marginal gibbsLaw
  rw [cofactor_eq_sum_filter, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  rw [← (Finset.mem_filter.1 hσ).2,
    Finset.mul_prod_erase univ (fun k => W k (σ k)) (Finset.mem_univ i)]
  field_simp

/-- Row-wise relative entropy is nonnegative: if `X` and `W` have unit row sums,
`X` is nonnegative and `W` is positive wherever `X` is, then
`∑ X log W ≤ ∑ X log X`. -/
theorem sum_mul_log_le_sum_mul_log {X W : Square n} (hX : Nonnegative X) (hW : Nonnegative W)
    (hXr : RowStochastic X) (hWr : RowStochastic W) (hsupp : ∀ i j, X i j ≠ 0 → W i j ≠ 0) :
    ∑ i, ∑ j, X i j * log (W i j) ≤ ∑ i, ∑ j, X i j * log (X i j) := by
  have hterm : ∀ i j, X i j * log (W i j) - X i j * log (X i j) ≤ W i j - X i j := by
    intro i j
    rcases (hX i j).lt_or_eq with hpos | hzero
    · have hw : 0 < W i j := lt_of_le_of_ne (hW i j) (Ne.symm (hsupp i j (ne_of_gt hpos)))
      have hlog := Real.log_le_sub_one_of_pos (div_pos hw hpos)
      rw [Real.log_div (ne_of_gt hw) (ne_of_gt hpos)] at hlog
      have := mul_le_mul_of_nonneg_left hlog hpos.le
      have hs : X i j * (W i j / X i j - 1) = W i j - X i j := by field_simp
      nlinarith [this, hs]
    · rw [← hzero]; simp [hW i j]
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ univ) =>
    Finset.sum_le_sum fun j (_ : j ∈ univ) => hterm i j
  simp only [Finset.sum_sub_distrib] at hsum
  have h1 : ∑ i, ∑ j, W i j = ∑ i, ∑ j, X i j :=
    Finset.sum_congr rfl fun i _ => (hWr i).trans (hXr i).symm
  linarith

end Gibbs

end LaviSection2
