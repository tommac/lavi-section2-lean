/-
Portions of this file are adapted from the RealRooted library
(https://github.com/PerAlexandersson/RealRooted), file `RealRooted/Gurvits.lean` at commit
d667074269bb822fa18ca9142a14fdd90734dd57, by Per Alexandersson and contributors, licensed
under the Apache License, Version 2.0 (see `LICENSE`).

Changes made here (T. Maciejewski, 2026):
* `LaviGurvits.gurvitsFactor_mul_capacity_le_capacity_step_of_degreeOf` is adapted from
  `RealRooted.Gurvits.gurvitsFactor_mul_capacity_le_capacity_step`: the degree of the
  restriction is bounded by `degreeOf 0 p ≤ d` instead of the total degree.
* `LaviGurvits.prod_gurvitsFactor_min_mul_capacity_le_coeffIter` is adapted from
  `RealRooted.Gurvits.prod_gurvitsFactor_mul_capacity_le_coeffIter`, with a separate degree
  cap for each variable.
* `LaviSection2.coeff_prodLin_nonneg`, `LaviSection2.mvRealStableOrZero_prodLin` and
  `LaviSection2.totalDegree_prodLin_le` are adapted from steps of the proof of
  `RealRooted.Gurvits.factorial_div_pow_le_permanent`, generalized to every nonnegative
  matrix (zero rows allowed).
-/
import LaviSection2.LaviOneStarCapacity
import LaviSection2.LaviContractionIdentity
import RealRooted.Gurvits

/-!
# Gurvits's capacity inequality, proved from the RealRooted library

This file proves `GurvitsCapacityInequality` (`LaviOneStarCapacity.lean`), the hypothesis `hG`
of the theorems in `LaviTheorem11.lean`.  It builds on the Lean formalization of Gurvits's
argument in the RealRooted library (P. Alexandersson et al.,
<https://github.com/PerAlexandersson/RealRooted>, Apache-2.0, used here at commit
`d667074269bb822fa18ca9142a14fdd90734dd57`).

**What RealRooted provides.**  For a real stable (or zero) polynomial `p` in `k + 1` variables
with nonnegative coefficients and total degree at most `k + 1`, it proves
`gurvitsFactor (k + 1) * Cap p ≤ Cap (∂p/∂x₀ |_{x₀ = 0})`
(`RealRooted.Gurvits.gurvitsFactor_mul_capacity_le_capacity_step`), and from it van der
Waerden's bound `n!/nⁿ`.  The one-variable inequality behind the step,
`RealRooted.Gurvits.mul_le_coeff_one_of_splits`, takes an arbitrary degree bound `d ≥ 1`.

**What is added here.**
* `LaviGurvits.gurvitsFactor_mul_capacity_le_capacity_step_of_degreeOf`: the step with the
  degree of `p` in `x₀` in place of the total degree.  The proof is RealRooted's, with the
  degree of the restriction bounded by `degreeOf 0 p` (`natDegree_finSuccEquiv`).
* `LaviGurvits.prod_gurvitsFactor_min_mul_capacity_le_coeffIter`: the iteration with a
  separate degree cap `c i` for each variable.  Variable `i` is eliminated when `k - i`
  variables remain, giving the factor `gurvitsFactor (min (c i) (k - i))`
  (Gurvits's Theorem 2.4).
* `gurvitsCapacityInequality`: the matrix form.  It is applied to
  `∏ᵢ ∑ᵥ M i (rev v) xᵥ`, so that column `j` is variable `rev j` and is eliminated when
  `j + 1` variables remain: the cap `min (colDegree M j) (j + 1)`.
-/

open MvPolynomial Finset

namespace LaviGurvits

open RealRooted RealRooted.Gurvits

/-- **Degree-sensitive Gurvits step.**  For a weakly real-stable `p` in `k + 1` variables
with nonnegative coefficients whose degree in `x₀` is at most `d` (`1 ≤ d`),
`gurvitsFactor d * Cap p ≤ Cap (step p)`.  This is
`RealRooted.Gurvits.gurvitsFactor_mul_capacity_le_capacity_step` with `degreeOf 0 p` in
place of the total degree; the proof is the same. -/
theorem gurvitsFactor_mul_capacity_le_capacity_step_of_degreeOf {k d : ℕ}
    {p : MvPolynomial (Fin (k + 1)) ℝ} (hp : MvRealStableOrZero p)
    (hnn : ∀ m, 0 ≤ p.coeff m) (hdeg : p.degreeOf 0 ≤ d) (hd : 1 ≤ d) :
    gurvitsFactor d * capacity p ≤ capacity (step p) := by
  apply le_capacity
  intro y hy
  have hprod : 0 < ∏ i, y i := Finset.prod_pos fun i _ => hy i
  set u := Polynomial.map (eval y) (finSuccEquiv ℝ k p)
  have hbound : ∀ t > 0, (capacity p * ∏ i, y i) * t ≤ u.eval t := by
    intro t ht
    have hx : ∀ i, 0 < (Fin.cons t y : Fin (k + 1) → ℝ) i :=
      fun i => Fin.cases ht (fun j => hy j) i
    calc (capacity p * ∏ i, y i) * t
        = capacity p * ∏ i, (Fin.cons t y : Fin (k + 1) → ℝ) i := by
          rw [prod_fin_cons]; ring
      _ ≤ eval (Fin.cons t y) p := capacity_mul_prod_le hnn hx
      _ = u.eval t := (eval_map_finSuccEquiv p y t).symm
  have hudeg : u.natDegree ≤ d :=
    Polynomial.natDegree_map_le.trans ((natDegree_finSuccEquiv p).trans_le hdeg)
  have hL1 := mul_le_coeff_one_of_splits (splits_map_finSuccEquiv hp y)
    (coeff_map_finSuccEquiv_nonneg hnn fun i => (hy i).le) hudeg hd hbound
  rw [coeff_one_map_finSuccEquiv] at hL1
  rw [le_div_iff₀ hprod]
  calc gurvitsFactor d * capacity p * ∏ i, y i
      = (capacity p * ∏ i, y i) * gurvitsFactor d := by ring
    _ ≤ eval y (step p) := hL1

/-- `step` does not raise the degree in any remaining variable. -/
theorem degreeOf_step_le {k : ℕ} (p : MvPolynomial (Fin (k + 1)) ℝ) (i : Fin k) :
    (step p).degreeOf i ≤ p.degreeOf i.succ := by
  rw [step_eq_coeff_one]
  exact degreeOf_coeff_finSuccEquiv p i 1

theorem gurvitsFactor_max_one (d : ℕ) : gurvitsFactor (max 1 d) = gurvitsFactor d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [gurvitsFactor_zero, gurvitsFactor_one]
  · rw [max_eq_right (by omega)]

/-- **Gurvits's Theorem 2.4 (capacity form).**  If `p` in `k` variables is weakly real stable
with nonnegative coefficients and total degree at most `k`, and `degreeOf i p ≤ c i` for each
variable, then `∏ᵢ gurvitsFactor (min (c i) (k - i)) * Cap p` is at most the coefficient of
`x₀ ⋯ x_{k-1}` (here `coeffIter k p`). -/
theorem prod_gurvitsFactor_min_mul_capacity_le_coeffIter :
    ∀ (k : ℕ) (p : MvPolynomial (Fin k) ℝ) (c : Fin k → ℕ), MvRealStableOrZero p →
      (∀ m, 0 ≤ p.coeff m) → p.totalDegree ≤ k → (∀ i, p.degreeOf i ≤ c i) →
      (∏ i : Fin k, gurvitsFactor (min (c i) (k - (i : ℕ)))) * capacity p ≤ coeffIter k p
  | 0, p, _, _, hnn, _, _ => by
    have h := capacity_le hnn (x := fun i => Fin.elim0 i) fun i => Fin.elim0 i
    simpa [coeffIter, eval_eq_coeff_zero_of_fin_zero] using h
  | k + 1, p, c, hs, hnn, hdeg, hc => by
    have ih := prod_gurvitsFactor_min_mul_capacity_le_coeffIter k (step p) (fun i => c i.succ)
      hs.step (coeff_step_nonneg hnn) (totalDegree_step_le hdeg)
      fun i => (degreeOf_step_le p i).trans (hc i.succ)
    have hnn' : 0 ≤ ∏ i : Fin k, gurvitsFactor (min (c i.succ) (k - (i : ℕ))) :=
      Finset.prod_nonneg fun i _ => gurvitsFactor_nonneg _
    have h0 : p.degreeOf 0 ≤ max 1 (min (c 0) (k + 1)) :=
      (le_min (hc 0) ((degreeOf_le_totalDegree p 0).trans hdeg)).trans (le_max_right _ _)
    have hstep := gurvitsFactor_mul_capacity_le_capacity_step_of_degreeOf hs hnn h0
      (le_max_left _ _)
    rw [gurvitsFactor_max_one] at hstep
    rw [Fin.prod_univ_succ]
    simp only [Fin.val_zero, Nat.sub_zero, Fin.val_succ, Nat.add_sub_add_right]
    calc gurvitsFactor (min (c 0) (k + 1)) *
          (∏ i : Fin k, gurvitsFactor (min (c i.succ) (k - (i : ℕ)))) * capacity p
        = (∏ i : Fin k, gurvitsFactor (min (c i.succ) (k - (i : ℕ)))) *
            (gurvitsFactor (min (c 0) (k + 1)) * capacity p) := by ring
      _ ≤ (∏ i : Fin k, gurvitsFactor (min (c i.succ) (k - (i : ℕ)))) * capacity (step p) :=
          mul_le_mul_of_nonneg_left hstep hnn'
      _ ≤ coeffIter k (step p) := ih
      _ = coeffIter (k + 1) p := rfl

end LaviGurvits

namespace LaviSection2

/-- Gurvits's constant `gurvitsG d` (`LaviOneStarConstants.lean`) is RealRooted's
`gurvitsFactor d`. -/
theorem gurvitsG_eq_gurvitsFactor (d : ℕ) : gurvitsG d = RealRooted.Gurvits.gurvitsFactor d := by
  unfold gurvitsG
  split_ifs with h
  · interval_cases d
    · exact RealRooted.Gurvits.gurvitsFactor_zero.symm
    · exact RealRooted.Gurvits.gurvitsFactor_one.symm
  · rfl

/-- The matrix with its columns in reverse order, `(i, v) ↦ M i (rev v)`. -/
abbrev revCols {n : ℕ} (M : Square n) : Matrix (Fin n) (Fin n) ℝ :=
  M.submatrix id Fin.revPerm

theorem coeff_prodLin_nonneg {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ} (hnn : ∀ i j, 0 ≤ B i j)
    (m : Fin n →₀ ℕ) : 0 ≤ (RealRooted.Gurvits.prodLin B).coeff m := by
  unfold RealRooted.Gurvits.prodLin
  refine Finset.prod_induction _ (fun q : MvPolynomial (Fin n) ℝ => ∀ m, 0 ≤ q.coeff m)
    (fun a b ha hb m => ?_) (fun m => ?_) (fun i _ m => ?_) m
  · rw [coeff_mul]
    exact Finset.sum_nonneg fun x _ => mul_nonneg (ha _) (hb _)
  · rw [coeff_one]
    split_ifs <;> norm_num
  · rw [coeff_sum]
    refine Finset.sum_nonneg fun j _ => ?_
    rw [coeff_C_mul]
    exact mul_nonneg (hnn i j) (by rw [coeff_X]; split_ifs <;> norm_num)

/-- `∏ᵢ ∑ⱼ B i j xⱼ` is weakly real stable for a nonnegative matrix: each row with a
positive entry gives a real-stable linear form, and a zero row makes the product zero. -/
theorem mvRealStableOrZero_prodLin {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ}
    (hnn : ∀ i j, 0 ≤ B i j) : RealRooted.MvRealStableOrZero (RealRooted.Gurvits.prodLin B) := by
  by_cases hrow : ∀ i, ∃ j, 0 < B i j
  · refine Or.inr (RealRooted.MvRealStable.finset_prod _ _ fun i _ => ?_)
    obtain ⟨j, hj⟩ := hrow i
    exact RealRooted.MvRealStable.finset_sum_C_mul_X Finset.univ (B i) id (fun j _ => hnn i j)
      ⟨j, Finset.mem_univ j, hj⟩
  · push Not at hrow
    obtain ⟨i, hi⟩ := hrow
    refine Or.inl (Finset.prod_eq_zero (Finset.mem_univ i) ?_)
    have h0 : ∀ j, B i j = 0 := fun j => le_antisymm (hi j) (hnn i j)
    simp [h0]

theorem totalDegree_prodLin_le {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) :
    (RealRooted.Gurvits.prodLin B).totalDegree ≤ n := by
  unfold RealRooted.Gurvits.prodLin
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ i, (∑ j, C (B i j) * X j : MvPolynomial (Fin n) ℝ).totalDegree
      ≤ ∑ _i : Fin n, 1 := Finset.sum_le_sum fun i _ => (totalDegree_finsetSum _ _).trans
        (Finset.sup_le fun j _ => (totalDegree_mul _ _).trans (by simp))
    _ = n := by simp

/-- A linear form has degree at most one in `x_v`, and degree zero if its `v`-th
coefficient vanishes. -/
theorem degreeOf_linearForm_le {n : ℕ} (a : Fin n → ℝ) (v : Fin n) :
    (∑ j, C (a j) * X j : MvPolynomial (Fin n) ℝ).degreeOf v ≤ if a v = 0 then 0 else 1 := by
  refine (degreeOf_sum_le v _ _).trans (Finset.sup_le fun j _ => ?_)
  by_cases hj : j = v
  · subst hj
    by_cases ha : a j = 0
    · simp [ha]
    · rw [ite_eq_right ha]
      exact (degreeOf_C_mul_le _ _ _).trans (by rw [degreeOf_X]; simp)
  · refine (degreeOf_C_mul_le _ _ _).trans ?_
    rw [degreeOf_X, ite_eq_right (Ne.symm hj)]
    exact Nat.zero_le _

/-- In `∏ᵢ ∑ᵥ M i (rev v) xᵥ`, the degree in `x_v` is at most the number of nonzero
entries of column `rev v`. -/
theorem degreeOf_prodLin_le_colDegree {n : ℕ} (M : Square n) (v : Fin n) :
    (RealRooted.Gurvits.prodLin (revCols M)).degreeOf v ≤ colDegree M (Fin.rev v) := by
  classical
  unfold RealRooted.Gurvits.prodLin
  refine (degreeOf_prod_le v _ _).trans ?_
  calc ∑ i, (∑ j, C (revCols M i j) * X j : MvPolynomial (Fin n) ℝ).degreeOf v
      ≤ ∑ i, (if revCols M i v = 0 then 0 else 1) :=
        Finset.sum_le_sum fun i _ => degreeOf_linearForm_le (revCols M i) v
    _ = colDegree M (Fin.rev v) := by
        unfold colDegree
        rw [Finset.card_filter]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases h : M i (Fin.rev v) = 0 <;> simp [h]

/-- Our matrix capacity is at most RealRooted's capacity of `∏ᵢ ∑ᵥ M i (rev v) xᵥ`
(they are equal; only this direction is needed).  The value of RealRooted's quotient at
`x > 0` is the value of ours at `z = x ∘ rev`. -/
theorem capacity_le_capacity_prodLin {n : ℕ} {M : Square n} (hM : Nonnegative M) :
    capacity M ≤ RealRooted.Gurvits.capacity (RealRooted.Gurvits.prodLin (revCols M)) := by
  have : Nonempty {x : Fin n → ℝ // ∀ i, 0 < x i} := ⟨⟨fun _ => 1, fun _ => one_pos⟩⟩
  refine le_ciInf fun x => csInf_le ⟨0, ?_⟩ ⟨fun j => x.1 (Fin.rev j), fun j => x.2 _, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact div_nonneg (Finset.prod_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (hM i j) (hz j).le) (Finset.prod_nonneg fun j _ => (hz j).le)
  · simp only [RealRooted.Gurvits.eval_prodLin]
    congr 1
    · refine Finset.prod_congr rfl fun i _ => ?_
      exact Fintype.sum_equiv Fin.revPerm _ _ fun j => by simp
    · exact Fintype.prod_equiv Fin.revPerm _ _ fun j => by simp

/-- **Gurvits's degree-sensitive capacity inequality** (Gurvits 2008, Theorem 2.4 and
Corollary 2.7(a); Laurent–Schrijver 2010, Corollary 1a): for every nonnegative `n × n`
matrix `M`, `Cap(M) · ∏ⱼ g(min(Δⱼ, j + 1)) ≤ per M`.  Proved from RealRooted's
formalization of Gurvits's stable-polynomial argument. -/
theorem gurvitsCapacityInequality : GurvitsCapacityInequality := by
  intro n M hM
  have hBnn : ∀ i j, 0 ≤ revCols M i j := fun i j => hM _ _
  have key := LaviGurvits.prod_gurvitsFactor_min_mul_capacity_le_coeffIter n
    (RealRooted.Gurvits.prodLin (revCols M)) (fun v => colDegree M (Fin.rev v))
    (mvRealStableOrZero_prodLin hBnn) (coeff_prodLin_nonneg hBnn) (totalDegree_prodLin_le _)
    (degreeOf_prodLin_le_colDegree M)
  rw [RealRooted.Gurvits.coeffIter_eq_coeff_allOnes, RealRooted.Gurvits.coeff_allOnes_prodLin,
    Matrix.permanent_permute_rows] at key
  have hprod : ∏ j, gurvitsG (min (colDegree M j) (j.val + 1)) =
      ∏ v : Fin n,
        RealRooted.Gurvits.gurvitsFactor (min (colDegree M (Fin.rev v)) (n - (v : ℕ))) := by
    refine Fintype.prod_equiv Fin.revPerm _ _ fun j => ?_
    have hj := j.isLt
    rw [gurvitsG_eq_gurvitsFactor, Fin.revPerm_apply, Fin.rev_rev, Fin.val_rev,
      show n - (n - (j.val + 1)) = j.val + 1 by omega]
  rw [hprod, permanent_eq_matrix_permanent, mul_comm (capacity M)]
  exact (mul_le_mul_of_nonneg_left (capacity_le_capacity_prodLin hM)
    (Finset.prod_nonneg fun _ _ => RealRooted.Gurvits.gurvitsFactor_nonneg _)).trans key

end LaviSection2
