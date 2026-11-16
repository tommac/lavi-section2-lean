import LaviSection2.LaviTerminalBranch
import LaviSection2.LaviInduction
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Lavi Theorem 1.1 (Foregger's conjecture), conditional on Gurvits's inequality

**The paper's statement (Theorem 1.1).**  Let `n ≥ 2` and let `A` be a nearly
decomposable (ND) doubly stochastic `n × n` matrix.  Then `per A ≥ 2^(1-n)`,
with equality if and only if `A` is obtained from `½(I_n + P_n)` by independent
row and column permutations, where `P_n` is the permutation matrix of the
`n`-cycle.  Moreover, if an ND support `D` is not a cycle support, then
`min_{A ∈ Ω(D)} per A > 2^(1-n)`.

**What is proved here.**  All three assertions, in the forms below, from the
single explicit hypothesis `hG : GurvitsCapacityInequality`:

* `foreggerSharpAt_of_gurvits`: the induction of Section 7;
* `lavi_theorem_1_1`: the bound and the equality characterization;
* `lavi_theorem_1_1_moreover`: strictness on every noncycle ND face;
* `lavi_theorem_1_1_attained`: the bound is attained in every order `n ≥ 2`
  (unconditional), so the hypotheses are satisfiable and the bound is sharp.

**Status.**  `GurvitsCapacityInequality` (file `LaviOneStarCapacity.lean`) is
Gurvits's degree-sensitive capacity inequality for permanents, a published
theorem that is *assumed, not proved*, in this development.  It is a
hypothesis of the theorems below, not a Lean axiom.  These theorems are
therefore a machine-checked reduction of Theorem 1.1 to that inequality; they
are not, by themselves, a complete machine-checked proof of Foregger's
conjecture.
-/

namespace LaviSection2

open Finset

/-- **The induction of Section 7, assuming Gurvits's inequality.**  In every
order `n`, every doubly stochastic matrix with nearly decomposable support has
permanent at least `foreggerTarget n = 2^(1-n)`, and equality forces a half
cycle.  The contraction branch, the base cases and the equality argument are
`foreggerSharpAt_of_terminal_strict`; the terminal branch is
`terminal_branch_strict`, which is where `hG` enters. -/
theorem foreggerSharpAt_of_gurvits (hG : GurvitsCapacityInequality) : ∀ n, ForeggerSharpAt n :=
  foreggerSharpAt_of_terminal_strict fun n hn hIH D hND hterm A hA => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact terminal_branch_strict hG hn D hND hterm hA
      fun k hk _ hD' _ hB => face_bound_of_foreggerBoundAt (hIH k hk) hD' hB

/-- The paper's matrix `½(I_n + P_n)`, with `P_n` the permutation matrix of the
`n`-cycle `finRotate n` (`i ↦ i + 1`). -/
noncomputable def halfCycleMatrix (n : ℕ) : Square n :=
  (1 / 2 : ℝ) • (1 + (finRotate n).permMatrix ℝ)

theorem finRotate_ne_self {n : ℕ} (hn : 2 ≤ n) (i : Fin n) : finRotate n i ≠ i := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [finRotate_apply]
  intro h
  simp at h

/-- Entries of `½(I_n + P_n)` for `n ≥ 2`: `1/2` on the diagonal and at
`(i, i + 1)`, zero elsewhere. -/
theorem halfCycleMatrix_apply {n : ℕ} (hn : 2 ≤ n) (i j : Fin n) :
    halfCycleMatrix n i j = if j = i ∨ j = finRotate n i then 1 / 2 else 0 := by
  have hne : finRotate n i ≠ i := finRotate_ne_self hn i
  have hentry : halfCycleMatrix n i j =
      1 / 2 * ((if i = j then 1 else 0) + if finRotate n i = j then 1 else 0) := by
    simp only [halfCycleMatrix, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply,
      Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
      Option.some.injEq, smul_eq_mul]
  rw [hentry]
  by_cases h1 : j = i <;> by_cases h2 : j = finRotate n i
  · exact absurd (h2.symm.trans h1) hne
  · rw [if_pos h1.symm, if_neg (fun h => h2 h.symm), if_pos (Or.inl h1)]; norm_num
  · rw [if_neg (fun h => h1 h.symm), if_pos h2.symm, if_pos (Or.inr h2)]; norm_num
  · rw [if_neg (fun h => h1 h.symm), if_neg (fun h => h2 h.symm), if_neg (not_or.2 ⟨h1, h2⟩)]
    norm_num

/-- `A` is obtained from `½(I_n + P_n)` by independent row and column
permutations exactly when it is a half cycle in the sense of `IsHalfCycle`. -/
theorem isHalfCycle_iff_permuted_halfCycleMatrix {n : ℕ} (hn : 2 ≤ n) {A : Square n} :
    IsHalfCycle A ↔
      ∃ σ τ : Equiv.Perm (Fin n), ∀ i j, A i j = halfCycleMatrix n (σ i) (τ j) := by
  rw [isHalfCycle_iff_finRotate hn]
  constructor
  · rintro ⟨r, c, h⟩
    refine ⟨r⁻¹, c⁻¹, fun i j => ?_⟩
    rw [halfCycleMatrix_apply hn, ← h]
    simp
  · rintro ⟨σ, τ, h⟩
    refine ⟨σ⁻¹, τ⁻¹, fun i j => ?_⟩
    rw [h, ← halfCycleMatrix_apply hn]
    simp

/-- **Lavi Theorem 1.1 (Foregger's conjecture), assuming Gurvits's capacity
inequality.**  Let `n ≥ 2` and let `A` be a doubly stochastic `n × n` matrix
whose support is nearly decomposable.  Then `per A ≥ 2^(1-n)`, with equality
if and only if `A` is obtained from `½(I_n + P_n)` by independent row and
column permutations. -/
theorem lavi_theorem_1_1 (hG : GurvitsCapacityInequality) {n : ℕ} (hn : 2 ≤ n) {A : Square n}
    (hA : DoublyStochastic A) (hND : NearlyDecomposable (support A)) :
    (2 : ℝ) ^ ((1 : ℤ) - (n : ℤ)) ≤ permanent A ∧
      (permanent A = (2 : ℝ) ^ ((1 : ℤ) - (n : ℤ)) ↔
        ∃ σ τ : Equiv.Perm (Fin n), ∀ i j, A i j = halfCycleMatrix n (σ i) (τ j)) := by
  have h := foreggerSharpAt_of_gurvits hG n A hA hND
  rw [← foreggerTarget_eq_zpow (by omega), ← isHalfCycle_iff_permuted_halfCycleMatrix hn]
  exact ⟨h.1, h.2, permanent_eq_foreggerTarget_of_isHalfCycle hn⟩

/-- **Theorem 1.1, the "Moreover" clause, assuming Gurvits's inequality.**  If
a nearly decomposable support `D` of order `n ≥ 2` is not a cycle support, in
the paper's sense of a connected 2-regular bipartite support, then the minimum
of the permanent on the face `Ω(D)` is attained and is strictly larger than
`2^(1-n)`; equivalently every matrix of the face has permanent `> 2^(1-n)`.
(By `isCycleSupport_iff_connected_two_regular` the hypothesis says exactly
`¬ IsCycleSupport D`: `D` is not, up to relabelling rows and columns, the
support of `½(I + P)` for a single `n`-cycle `P`.) -/
theorem lavi_theorem_1_1_moreover (hG : GurvitsCapacityInequality) {n : ℕ} (hn : 2 ≤ n)
    {D : Fin n → Fin n → Prop} (hD : NearlyDecomposable D)
    (hnc : ¬((supportGraph D).Connected ∧
      (∀ i, rowDegreeOn D i = 2) ∧ (∀ j, columnDegreeOn D j = 2))) :
    (∃ A₀, FaceMinimizer D A₀ ∧ (2 : ℝ) ^ ((1 : ℤ) - (n : ℤ)) < permanent A₀) ∧
      ∀ A, InFace D A → (2 : ℝ) ^ ((1 : ℤ) - (n : ℤ)) < permanent A := by
  rw [← foreggerTarget_eq_zpow (by omega)]
  have hnc' : ¬IsCycleSupport D := fun h =>
    hnc ((isCycleSupport_iff_connected_two_regular hn).1 h)
  have hstrict : ∀ A, InFace D A → foreggerTarget n < permanent A := fun A hA =>
    strict_of_not_cycleSupport (foreggerSharpAt_of_gurvits hG n) hD hnc' hA
  obtain ⟨A₀, hA₀, -⟩ := exists_faceMinimizer_support_eq hn hD
  exact ⟨⟨A₀, hA₀, hstrict A₀ hA₀.1⟩, hstrict⟩

/-- **The bound is attained (unconditional).**  For every `n ≥ 2` the matrix
`½(I_n + P_n)` is doubly stochastic with nearly decomposable support and has
permanent exactly `2^(1-n)`.  In particular the hypotheses of
`lavi_theorem_1_1` are satisfiable in every order. -/
theorem lavi_theorem_1_1_attained {n : ℕ} (hn : 2 ≤ n) :
    DoublyStochastic (halfCycleMatrix n) ∧ NearlyDecomposable (support (halfCycleMatrix n)) ∧
      permanent (halfCycleMatrix n) = (2 : ℝ) ^ ((1 : ℤ) - (n : ℤ)) := by
  have h : IsHalfCycle (halfCycleMatrix n) :=
    (isHalfCycle_iff_permuted_halfCycleMatrix hn).2 ⟨1, 1, fun _ _ => rfl⟩
  rw [← foreggerTarget_eq_zpow (by omega)]
  exact ⟨doublyStochastic_of_isHalfCycle hn h, nearlyDecomposable_support_of_isHalfCycle hn h,
    permanent_eq_foreggerTarget_of_isHalfCycle hn h⟩

end LaviSection2
