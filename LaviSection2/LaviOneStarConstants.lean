import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Algebra.Order.Ring.Pow
import LaviSection2.LaviOneStarArithmetic

/-!
# Lavi Section 5: the row and column factors and their secant bounds

Lavi's one-star bound uses the row factor `A_d = 2^d (d-1)^(d-1) / d^d`, the
column factor `C_d = 2 ((d-1)/d)^(d-1)`, and Gurvits's `g(d) = ((d-1)/d)^(d-1)`
(with `g(0) = g(1) = 1`), see (5.7).  We prove

* the secant bounds (5.10) `A_d ≥ (32/27)(729/512)^(d-3)` and
  `C_d ≥ (8/9)(243/256)^(d-3)` for every integer `d ≥ 3`;
* `C_d` decreases, `C_d ≤ 8/9` for `d ≥ 3`, and `g` is antitone;
* `A_d = 2^d exp(-d h₂(1/d))`.

The manuscript derives (5.10) from convexity of `log A_t` and `log C_t`.  For
integers it suffices that `a_m = (1 + 1/m)^m` increases and
`b_m = (1 + 1/m)^(m+1)` decreases, which follow from Bernoulli's inequality.
-/

namespace LaviSection2

open Real

/-- `a_m = (1 + 1/m)^m`. -/
noncomputable def aSeq (m : ℕ) : ℝ := (1 + 1 / (m : ℝ)) ^ m

/-- `b_m = (1 + 1/m)^(m+1)`. -/
noncomputable def bSeq (m : ℕ) : ℝ := (1 + 1 / (m : ℝ)) ^ (m + 1)

/-- Lavi's row factor `A_d = 2^d (d-1)^(d-1) / d^d`. -/
noncomputable def rowFactor (d : ℕ) : ℝ := 2 ^ d * ((d : ℝ) - 1) ^ (d - 1) / (d : ℝ) ^ d

/-- Lavi's column factor `C_d = 2 ((d-1)/d)^(d-1)`. -/
noncomputable def colFactor (d : ℕ) : ℝ := 2 * (((d : ℝ) - 1) / d) ^ (d - 1)

/-- Gurvits's `g(d) = ((d-1)/d)^(d-1)` for `d ≥ 2`, and `g(0) = g(1) = 1`. -/
noncomputable def gurvitsG (d : ℕ) : ℝ := if d ≤ 1 then 1 else (((d : ℝ) - 1) / d) ^ (d - 1)

theorem aSeq_pos (m : ℕ) : 0 < aSeq m := by
  unfold aSeq; positivity

theorem bSeq_eq (m : ℕ) : bSeq m = aSeq m * (1 + 1 / (m : ℝ)) := by
  unfold bSeq aSeq; rw [pow_succ]

/-- `a_m ≤ a_{m+1}` (Bernoulli). -/
theorem aSeq_le_succ {m : ℕ} (hm : 1 ≤ m) : aSeq m ≤ aSeq (m + 1) := by
  have hM : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set p : ℝ := 1 + 1 / (m : ℝ) with hp
  set t : ℝ := -1 / ((m : ℝ) + 1) ^ 2 with ht
  have hq : (1 + 1 / ((m + 1 : ℕ) : ℝ)) = p * (1 + t) := by
    rw [hp, ht]; push_cast; field_simp; ring
  have hpos : 0 < p := by rw [hp]; positivity
  have ht1 : -1 ≤ t := by
    rw [ht, neg_div, neg_le_neg_iff, div_le_one (by positivity)]
    nlinarith
  have hbern := one_add_mul_le_pow (a := t) (by linarith) (m + 1)
  have key : p ^ (m + 1) * (1 + ((m + 1 : ℕ) : ℝ) * t) = p ^ m := by
    rw [pow_succ, ht, hp]; push_cast; field_simp; ring
  unfold aSeq
  rw [hq, mul_pow, ← hp]
  calc p ^ m = p ^ (m + 1) * (1 + ((m + 1 : ℕ) : ℝ) * t) := key.symm
    _ ≤ p ^ (m + 1) * (1 + t) ^ (m + 1) :=
        mul_le_mul_of_nonneg_left hbern (by positivity)

/-- `b_{m+1} ≤ b_m` (Bernoulli). -/
theorem bSeq_succ_le {m : ℕ} (hm : 1 ≤ m) : bSeq (m + 1) ≤ bSeq m := by
  have hM : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set q : ℝ := 1 + 1 / ((m : ℝ) + 1) with hq
  set s : ℝ := 1 / ((m : ℝ) * ((m : ℝ) + 2)) with hs
  have hp : (1 + 1 / (m : ℝ)) = q * (1 + s) := by
    rw [hq, hs]; field_simp; ring
  have hqpos : 0 < q := by rw [hq]; positivity
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  have hbern := one_add_mul_le_pow (a := s) (by linarith) (m + 2)
  have hms : (1 : ℝ) + ((m + 2 : ℕ) : ℝ) * s = 1 + 1 / (m : ℝ) := by
    rw [hs]; push_cast; field_simp
  -- `b_m = p^(m+1)` and `p^(m+2) ≥ q^(m+2) · p`
  have hpm : q ^ (m + 2) * (1 + 1 / (m : ℝ)) ≤ (1 + 1 / (m : ℝ)) ^ (m + 2) := by
    calc q ^ (m + 2) * (1 + 1 / (m : ℝ)) = q ^ (m + 2) * (1 + ((m + 2 : ℕ) : ℝ) * s) := by
          rw [hms]
      _ ≤ q ^ (m + 2) * (1 + s) ^ (m + 2) := mul_le_mul_of_nonneg_left hbern (by positivity)
      _ = (1 + 1 / (m : ℝ)) ^ (m + 2) := by rw [hp, mul_pow]
  have hp0 : 0 < 1 + 1 / (m : ℝ) := by positivity
  unfold bSeq
  have hcast : (1 + 1 / ((m + 1 : ℕ) : ℝ)) = q := by rw [hq]; push_cast; ring
  rw [hcast]
  rw [show m + 2 = (m + 1) + 1 from rfl, pow_succ (1 + 1 / (m : ℝ)) (m + 1)] at hpm
  exact le_of_mul_le_mul_right hpm hp0

theorem aSeq_mono {m n : ℕ} (hm : 1 ≤ m) (h : m ≤ n) : aSeq m ≤ aSeq n := by
  induction n, h using Nat.le_induction with
  | base => exact le_rfl
  | succ n hmn ih => exact ih.trans (aSeq_le_succ (hm.trans hmn))

theorem bSeq_anti {m n : ℕ} (hm : 1 ≤ m) (h : m ≤ n) : bSeq n ≤ bSeq m := by
  induction n, h using Nat.le_induction with
  | base => exact le_rfl
  | succ n hmn ih => exact (bSeq_succ_le (hm.trans hmn)).trans ih

theorem aSeq_two : aSeq 2 = 9 / 4 := by unfold aSeq; norm_num

theorem aSeq_three : aSeq 3 = 64 / 27 := by unfold aSeq; norm_num

theorem bSeq_three : bSeq 3 = 256 / 81 := by unfold bSeq; norm_num

/-- A sharper ratio: `a_m ≥ (m+1)(m+3)/(m+2)² · a_{m+1}`. -/
theorem aSeq_ratio {m : ℕ} (hm : 1 ≤ m) :
    ((m : ℝ) + 1) * ((m : ℝ) + 3) / ((m : ℝ) + 2) ^ 2 * aSeq (m + 1) ≤ aSeq m := by
  have hM : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set q : ℝ := 1 + 1 / ((m : ℝ) + 1) with hq
  set s : ℝ := 1 / ((m : ℝ) * ((m : ℝ) + 2)) with hs
  have hp : (1 + 1 / (m : ℝ)) = q * (1 + s) := by
    rw [hq, hs]; field_simp; ring
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  have hbern := one_add_mul_le_pow (a := s) (by linarith) m
  have hcast : (1 + 1 / ((m + 1 : ℕ) : ℝ)) = q := by rw [hq]; push_cast; ring
  have hqpos : 0 < q := by rw [hq]; positivity
  unfold aSeq
  rw [hcast, hp, mul_pow]
  have hqv : ((m : ℝ) + 1) * ((m : ℝ) + 3) / ((m : ℝ) + 2) ^ 2 * q = 1 + (m : ℝ) * s := by
    rw [hq, hs]; field_simp; ring
  have h1 : ((m : ℝ) + 1) * ((m : ℝ) + 3) / ((m : ℝ) + 2) ^ 2 * q ^ (m + 1) =
      q ^ m * (1 + (m : ℝ) * s) := by
    rw [pow_succ, ← hqv]; ring
  rw [h1]
  exact mul_le_mul_of_nonneg_left hbern (by positivity)

theorem colFactor_succ (m : ℕ) : colFactor (m + 1) = 2 / aSeq m := by
  unfold colFactor aSeq
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hM : (0 : ℝ) < m := by exact_mod_cast hm
  push_cast
  rw [show ((m : ℝ) + 1 - 1) = m by ring]
  rw [eq_div_iff (by positivity), mul_assoc, ← mul_pow]
  rw [show (m : ℝ) / (m + 1) * (1 + 1 / m) = 1 by field_simp]
  simp

theorem rowFactor_succ (m : ℕ) :
    rowFactor (m + 1) = 2 ^ (m + 1) / (((m : ℝ) + 1) * aSeq m) := by
  unfold rowFactor aSeq
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hM : (0 : ℝ) < m := by exact_mod_cast hm
  push_cast
  rw [show ((m : ℝ) + 1 - 1) = m by ring]
  rw [div_eq_div_iff (by positivity) (by positivity)]
  have : (1 + 1 / (m : ℝ)) = ((m : ℝ) + 1) / m := by field_simp
  rw [this, div_pow]
  field_simp
  ring

/-- Ratio of consecutive column factors. -/
theorem colFactor_succ_succ (m : ℕ) :
    colFactor (m + 2) = colFactor (m + 1) * (aSeq m / aSeq (m + 1)) := by
  rw [show colFactor (m + 2) = 2 / aSeq (m + 1) from colFactor_succ (m + 1), colFactor_succ m]
  have := aSeq_pos m; have := aSeq_pos (m + 1)
  field_simp

theorem colFactor_three : colFactor 3 = 8 / 9 := by
  rw [show 3 = 2 + 1 by rfl, colFactor_succ, aSeq_two]; norm_num

theorem rowFactor_three : rowFactor 3 = 32 / 27 := by
  unfold rowFactor; norm_num

/-- `C_{d+1} ≥ (243/256) C_d` for `d ≥ 3`. -/
theorem colFactor_step {m : ℕ} (hm : 2 ≤ m) :
    243 / 256 * colFactor (m + 1) ≤ colFactor (m + 2) := by
  rw [colFactor_succ_succ]
  have hc : 0 < colFactor (m + 1) := by rw [colFactor_succ]; exact div_pos two_pos (aSeq_pos m)
  have hr : 243 / 256 ≤ aSeq m / aSeq (m + 1) := by
    rw [le_div_iff₀ (aSeq_pos _)]
    rcases Nat.lt_or_ge m 3 with h3 | h3
    · obtain rfl : m = 2 := by omega
      rw [aSeq_two, aSeq_three]; norm_num
    · have hM : (3 : ℝ) ≤ m := by exact_mod_cast h3
      have key := aSeq_ratio (m := m) (by omega)
      have hb : (243 / 256 : ℝ) ≤ ((m : ℝ) + 1) * ((m : ℝ) + 3) / ((m : ℝ) + 2) ^ 2 := by
        rw [le_div_iff₀ (by positivity)]; nlinarith
      have := aSeq_pos (m + 1)
      nlinarith
  rw [mul_comm (colFactor (m + 1))]
  exact mul_le_mul_of_nonneg_right hr hc.le

/-- `A_{d+1} ≥ (729/512) A_d` for `d ≥ 3`. -/
theorem rowFactor_step {m : ℕ} (hm : 2 ≤ m) :
    729 / 512 * rowFactor (m + 1) ≤ rowFactor (m + 2) := by
  rw [show rowFactor (m + 2) = 2 ^ (m + 1 + 1) / (((m + 1 : ℕ) : ℝ) + 1) / aSeq (m + 1) by
      rw [rowFactor_succ (m + 1), div_div], rowFactor_succ m]
  have ha : 9 / 4 ≤ aSeq m := aSeq_two ▸ aSeq_mono (by norm_num) hm
  have hb : bSeq (m + 1) ≤ 256 / 81 := bSeq_three ▸ bSeq_anti (by norm_num) (by omega)
  rw [bSeq_eq] at hb
  have hM : (0 : ℝ) ≤ m := by positivity
  have ha1 := aSeq_pos (m + 1)
  have ha0 := aSeq_pos m
  push_cast at hb ⊢
  have hb' : aSeq (m + 1) * ((m : ℝ) + 2) ≤ 256 / 81 * ((m : ℝ) + 1) := by
    have h1 : aSeq (m + 1) * (1 + 1 / ((m : ℝ) + 1)) * ((m : ℝ) + 1) =
        aSeq (m + 1) * ((m : ℝ) + 2) := by field_simp; ring
    nlinarith
  have hpow : (0 : ℝ) < 2 ^ (m + 1) := by positivity
  have hkey : 729 / 512 * (((m : ℝ) + 1 + 1) * aSeq (m + 1)) ≤ 2 * (((m : ℝ) + 1) * aSeq m) := by
    nlinarith
  rw [div_div, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity), pow_succ 2 (m + 1)]
  have := mul_le_mul_of_nonneg_left hkey hpow.le
  nlinarith

/-- **Lavi (5.10), row secant:** `A_d ≥ (32/27)(729/512)^(d-3)` for `d ≥ 3`. -/
theorem rowFactor_secant {d : ℕ} (hd : 3 ≤ d) :
    32 / 27 * (729 / 512) ^ (d - 3) ≤ rowFactor d := by
  induction d, hd using Nat.le_induction with
  | base => rw [rowFactor_three]; norm_num
  | succ d hd ih =>
    have := rowFactor_step (m := d - 1) (by omega)
    rw [show d - 1 + 1 = d by omega, show d - 1 + 2 = d + 1 by omega] at this
    rw [show d + 1 - 3 = (d - 3) + 1 by omega, pow_succ]
    nlinarith

/-- **Lavi (5.10), column secant:** `C_d ≥ (8/9)(243/256)^(d-3)` for `d ≥ 3`. -/
theorem colFactor_secant {d : ℕ} (hd : 3 ≤ d) :
    8 / 9 * (243 / 256) ^ (d - 3) ≤ colFactor d := by
  induction d, hd using Nat.le_induction with
  | base => rw [colFactor_three]; norm_num
  | succ d hd ih =>
    have := colFactor_step (m := d - 1) (by omega)
    rw [show d - 1 + 1 = d by omega, show d - 1 + 2 = d + 1 by omega] at this
    rw [show d + 1 - 3 = (d - 3) + 1 by omega, pow_succ]
    nlinarith

theorem colFactor_pos (d : ℕ) (hd : 1 ≤ d) : 0 < colFactor d := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  rw [colFactor_succ]; exact div_pos two_pos (aSeq_pos m)

/-- `C_d` decreases for `d ≥ 2`. -/
theorem colFactor_anti {d e : ℕ} (hd : 2 ≤ d) (h : d ≤ e) : colFactor e ≤ colFactor d := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n, e = n + 1 := ⟨e - 1, by omega⟩
  rw [colFactor_succ, colFactor_succ]
  exact div_le_div_of_nonneg_left two_pos.le (aSeq_pos m) (aSeq_mono (by omega) (by omega))

theorem colFactor_le {d : ℕ} (hd : 3 ≤ d) : colFactor d ≤ 8 / 9 :=
  colFactor_three ▸ colFactor_anti (by norm_num) hd

theorem gurvitsG_eq (d : ℕ) (hd : 1 ≤ d) : gurvitsG d = colFactor d / 2 := by
  unfold gurvitsG colFactor
  split_ifs with h
  · obtain rfl : d = 1 := by omega
    norm_num
  · ring

theorem gurvitsG_pos (d : ℕ) : 0 < gurvitsG d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [gurvitsG]
  · rw [gurvitsG_eq d hd]; exact div_pos (colFactor_pos d hd) two_pos

/-- Gurvits's `g` is antitone (Gurvits, Definition 2.1(6)). -/
theorem gurvitsG_anti {d e : ℕ} (h : d ≤ e) : gurvitsG e ≤ gurvitsG d := by
  rcases Nat.lt_or_ge d 2 with hd | hd
  · have hgd : gurvitsG d = 1 := by unfold gurvitsG; rw [ite_eq_left (by omega)]
    rw [hgd]
    rcases Nat.lt_or_ge e 2 with he | he
    · unfold gurvitsG; rw [ite_eq_left (by omega)]
    · rw [gurvitsG_eq e (by omega)]
      have := colFactor_anti (by norm_num) he
      rw [show colFactor 2 = 1 by unfold colFactor; norm_num] at this
      linarith
  · rw [gurvitsG_eq e (by omega), gurvitsG_eq d (by omega)]
    exact div_le_div_of_nonneg_right (colFactor_anti hd h) two_pos.le

/-- `A_d = 2^d exp(-d h₂(1/d))` for `d ≥ 2`. -/
theorem rowFactor_eq_exp {d : ℕ} (hd : 2 ≤ d) :
    rowFactor d = 2 ^ d * exp (-((d : ℝ) * binEntropy (1 / d))) := by
  have hD : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hD0 : (0 : ℝ) < d := by linarith
  have hD1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  have hent : (d : ℝ) * binEntropy (1 / d) =
      log d - ((d : ℝ) - 1) * log (((d : ℝ) - 1) / d) := by
    rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub, Real.negMulLog, Real.negMulLog]
    rw [show (1 : ℝ) - 1 / d = ((d : ℝ) - 1) / d by field_simp]
    rw [Real.log_div (by positivity) (by positivity), Real.log_div hD1.ne' hD0.ne', Real.log_one]
    field_simp
    ring
  rw [hent, show -(log (d : ℝ) - ((d : ℝ) - 1) * log (((d : ℝ) - 1) / d)) =
      ((d : ℝ) - 1) * log (((d : ℝ) - 1) / d) - log d by ring,
    Real.exp_sub, ← Real.log_rpow (by positivity), Real.exp_log (by positivity),
    Real.exp_log hD0]
  unfold rowFactor
  rw [show ((d : ℝ) - 1) = ((d - 1 : ℕ) : ℝ) by push_cast [Nat.cast_sub (by omega : 1 ≤ d)]; ring,
    Real.rpow_natCast, div_pow]
  have hd' : d = (d - 1) + 1 := by omega
  conv_lhs => rw [hd']
  conv_rhs => rw [hd']
  push_cast [Nat.cast_sub (by omega : 1 ≤ d)]
  rw [pow_succ, pow_succ]
  field_simp

end LaviSection2
