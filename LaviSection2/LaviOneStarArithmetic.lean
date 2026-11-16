import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Exact arithmetic in Lavi's one-star estimate

This module kernel-checks the rational constant identities at the end of
Lemma 5.1 of Yair Lavi's 2026 preprint: the scalar tail of that lemma.  The
reduction from the core to the eliminated matrix is in `LaviOneStar.lean`, and
the Gurvits capacity inequality is proved in `GurvitsRealRooted.lean`.
-/

namespace LaviSection2

/-- The sharp `K₃,₃` one-star constant is strictly larger than one. -/
theorem lavi_oneStar_base_gt_one :
    (1 : ℝ) < 8192 / 6561 := by
  norm_num

/-- Every extra nonroot occurrence contributes a factor larger than one. -/
theorem lavi_oneStar_growth_gt_one :
    (1 : ℝ) < 177147 / 131072 := by
  norm_num

/-- The cancellation identity used to remove the extra `k - 3` factors. -/
theorem lavi_oneStar_cancellation :
    (32 / 27 : ℝ) * (8 / 9) * (243 / 256) = 1 := by
  norm_num

/-- The two secant-line growth factors combine as claimed in the paper. -/
theorem lavi_oneStar_growth_identity :
    (729 / 512 : ℝ) * (243 / 256) = 177147 / 131072 := by
  norm_num

/-- The normalized one-star lower bound is strict for every excess exponent. -/
theorem lavi_oneStar_bound_strict (m : ℕ) :
    (1 : ℝ) < (8192 / 6561) * (177147 / 131072) ^ m := by
  have hbase : (1 : ℝ) < 8192 / 6561 := lavi_oneStar_base_gt_one
  have hgrowth : (1 : ℝ) ≤ 177147 / 131072 :=
    le_of_lt lavi_oneStar_growth_gt_one
  have hpow : (1 : ℝ) ≤ (177147 / 131072) ^ m := one_le_pow₀ hgrowth
  have hbase_nonneg : (0 : ℝ) ≤ 8192 / 6561 := by norm_num
  have hmul := mul_le_mul_of_nonneg_left hpow hbase_nonneg
  nlinarith

end LaviSection2
