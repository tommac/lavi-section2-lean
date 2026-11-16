import LaviSection2.Definitions
import Mathlib.Algebra.BigOperators.Field

/-!
# Exact algebra used by the reduction
-/

namespace LaviSection2

open scoped BigOperators

/-- Normalization by `2^(n-1)` is exactly equivalent to Foregger's bound. -/
theorem normalized_iff_bound {n : ℕ} {p : ℝ} :
    1 ≤ (2 : ℝ) ^ (n - 1) * p ↔ foreggerTarget n ≤ p := by
  have hpow : 0 < (2 : ℝ) ^ (n - 1) := pow_pos (by norm_num) _
  rw [foreggerTarget, inv_eq_one_div, div_le_iff₀ hpow]
  constructor <;> intro h
  · simpa [mul_comm] using h
  · simpa [mul_comm] using h

/--
The exact arithmetic in a critical bicontraction step:
`per(B)=2 per(A)` transports the order-`n-1` target to the order-`n` target.
-/
theorem bicontraction_transports_bound {n : ℕ} (hn : 2 ≤ n) {perA perB : ℝ}
    (hscale : perB = 2 * perA)
    (hchild : foreggerTarget (n - 1) ≤ perB) :
    foreggerTarget n ≤ perA := by
  have hsub : n - 1 - 1 = n - 2 := by omega
  have hnexp : n - 1 = (n - 2) + 1 := by omega
  have hq : 0 < (2 : ℝ) ^ (n - 2) := pow_pos (by norm_num) _
  rw [foreggerTarget, hsub] at hchild
  rw [foreggerTarget, hnexp, pow_succ]
  rw [hscale] at hchild
  have hchild' : 1 ≤ (2 * perA) * (2 : ℝ) ^ (n - 2) := by
    rw [inv_eq_one_div, div_le_iff₀ hq] at hchild
    exact hchild
  have hden : 0 < (2 : ℝ) ^ (n - 2) * 2 := mul_pos hq (by norm_num)
  rw [inv_eq_one_div, div_le_iff₀ hden]
  nlinarith

end LaviSection2
