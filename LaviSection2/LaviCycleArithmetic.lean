import LaviSection2.Definitions
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic.NormNum

/-!
# Exact scalar bound on a cycle face

Section 7 of Lavi's preprint reduces a doubly stochastic point on a cycle
support to the one-parameter permanent `t^n + (1-t)^n`.  This module proves
the sharp lower-bound part of that scalar reduction for every order.  The
combinatorial statement identifying the two supported perfect matchings is a
separate obligation.
-/

namespace LaviSection2

/-- The cycle-face scalar permanent is bounded below by Foregger's target. -/
theorem lavi_cycle_scalar_lower {n : ℕ} (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    foreggerTarget n ≤ t ^ n + (1 - t) ^ n := by
  have hpow := add_pow_le ht0 (sub_nonneg.mpr ht1) n
  have hscaled :
      (1 : ℝ) ≤ (2 : ℝ) ^ (n - 1) * (t ^ n + (1 - t) ^ n) := by
    simpa using hpow
  rw [foreggerTarget, inv_eq_one_div]
  apply (div_le_iff₀ (pow_pos (by norm_num) (n - 1))).2
  simpa [mul_comm] using hscaled

/-- At the balanced point the scalar cycle permanent is exactly the target. -/
theorem lavi_cycle_scalar_balanced (n : ℕ) (hn : 1 ≤ n) :
    ((1 / 2 : ℝ) ^ n + (1 - (1 / 2 : ℝ)) ^ n) =
      foreggerTarget n := by
  rw [show (1 - (1 / 2 : ℝ)) = 1 / 2 by norm_num]
  simp only [foreggerTarget]
  rw [← two_mul]
  rw [show n = (n - 1) + 1 by
    exact (Nat.sub_add_cancel hn).symm, pow_succ]
  simp only [div_pow, one_pow]
  calc
    2 * ((1 / (2 ^ (n - 1) : ℝ)) * (1 / 2 : ℝ)) =
        (1 / (2 ^ (n - 1) : ℝ)) * (2 * (1 / 2 : ℝ)) := by ac_rfl
    _ = 1 / (2 ^ (n - 1) : ℝ) := by norm_num
    _ = (2 ^ (n - 1) : ℝ)⁻¹ := by rw [one_div]

/--
For orders at least two, equality in the cycle-face bound occurs only at the
balanced point.  This is the strict-convexity step used in Section 7 of Lavi's
proof.
-/
theorem lavi_cycle_scalar_eq_iff {n : ℕ} (hn : 2 ≤ n) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t ^ n + (1 - t) ^ n = foreggerTarget n ↔ t = 1 / 2 := by
  constructor
  · intro heq
    by_contra hne
    have hne' : t ≠ 1 - t := by
      intro h
      apply hne
      linarith
    have hnReal : (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast hn
    have hstrict :=
      (strictConvexOn_rpow hnReal).2 ht0 (sub_nonneg.mpr ht1) hne'
        (show (0 : ℝ) < 1 / 2 by norm_num)
        (show (0 : ℝ) < 1 / 2 by norm_num)
        (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
    simp only [smul_eq_mul, Real.rpow_natCast] at hstrict
    have hmidpoint :
        (1 / 2 : ℝ) * t + (1 / 2) * (1 - t) = 1 / 2 := by
      ring
    rw [hmidpoint] at hstrict
    have hbalanced := lavi_cycle_scalar_balanced n (le_trans (by norm_num) hn)
    rw [show (1 - (1 / 2 : ℝ)) = 1 / 2 by norm_num] at hbalanced
    nlinarith
  · rintro rfl
    exact lavi_cycle_scalar_balanced n (le_trans (by norm_num) hn)

end LaviSection2
