import LaviSection2.LaviTheorem11
import LaviSection2.GurvitsRealRooted

/-!
# Lavi's Theorem 1.1 with the Gurvits hypothesis discharged

`LaviTheorem11.lean` proves Lavi's Theorem 1.1 from the hypothesis
`hG : GurvitsCapacityInequality`.  `GurvitsRealRooted.lean` proves that hypothesis
(`gurvitsCapacityInequality`) from the RealRooted library's formalization of Gurvits's
stable-polynomial argument.  The theorems below combine the two, so their only hypotheses
are the stated matrix hypotheses.

The statements are for `n ≥ 2`, as in the paper.  With the definitions used here order
one is vacuous (the only nearly decomposable support of order one is empty), so
`foreggerSharpAt_all` should not be quoted for `n < 2`.
-/

namespace LaviSection2

/-- The induction of Section 7 with the Gurvits hypothesis discharged: in every order `n`,
every doubly stochastic matrix with nearly decomposable support has permanent at least
`foreggerTarget n`, and equality forces a half cycle. -/
theorem foreggerSharpAt_all : ∀ n, ForeggerSharpAt n :=
  foreggerSharpAt_of_gurvits gurvitsCapacityInequality

/-- **Lavi Theorem 1.1, without hypotheses beyond the matrix ones.**  Let `n ≥ 2` and let `A`
be a doubly stochastic `n × n` matrix whose support is nearly decomposable.  Then
`per A ≥ 2^(1-n)`, with equality if and only if `A` is obtained from `½(I_n + P_n)` by
independent row and column permutations. -/
theorem lavi_theorem_1_1_unconditional {n : ℕ} (hn : 2 ≤ n) {A : Square n}
    (hA : DoublyStochastic A) (hND : NearlyDecomposable (support A)) :
    (2 : ℝ) ^ ((1 : ℤ) - (n : ℤ)) ≤ permanent A ∧
      (permanent A = (2 : ℝ) ^ ((1 : ℤ) - (n : ℤ)) ↔
        ∃ σ τ : Equiv.Perm (Fin n), ∀ i j, A i j = halfCycleMatrix n (σ i) (τ j)) :=
  lavi_theorem_1_1 gurvitsCapacityInequality hn hA hND

/-- **Theorem 1.1, the "Moreover" clause, without the Gurvits hypothesis.**  If a nearly
decomposable support `D` of order `n ≥ 2` is not both connected and 2-regular, the minimum of
the permanent on the face `Ω(D)` is attained and is strictly larger than `2^(1-n)`. -/
theorem lavi_theorem_1_1_moreover_unconditional {n : ℕ} (hn : 2 ≤ n)
    {D : Fin n → Fin n → Prop} (hD : NearlyDecomposable D)
    (hnc : ¬((supportGraph D).Connected ∧
      (∀ i, rowDegreeOn D i = 2) ∧ (∀ j, columnDegreeOn D j = 2))) :
    (∃ A₀, FaceMinimizer D A₀ ∧ (2 : ℝ) ^ ((1 : ℤ) - (n : ℤ)) < permanent A₀) ∧
      ∀ A, InFace D A → (2 : ℝ) ^ ((1 : ℤ) - (n : ℤ)) < permanent A :=
  lavi_theorem_1_1_moreover gurvitsCapacityInequality hn hD hnc

/-- **Foregger's conjecture, in the form formalized here.**  For `n ≥ 2`, every doubly
stochastic `n × n` matrix `A` whose support is nearly decomposable has `per A ≥ 2^(1-n)`,
and equality holds exactly when `A` is obtained from `½(I_n + P_n)` by independent row and
column permutations.  This is the first assertion of Lavi's Theorem 1.1
(`lavi_theorem_1_1_unconditional`); the inequality alone is `foregger_bound`. -/
theorem foregger_conjecture {n : ℕ} (hn : 2 ≤ n) {A : Square n}
    (hA : DoublyStochastic A) (hND : NearlyDecomposable (support A)) :
    (2 : ℝ) ^ ((1 : ℤ) - (n : ℤ)) ≤ permanent A ∧
      (permanent A = (2 : ℝ) ^ ((1 : ℤ) - (n : ℤ)) ↔
        ∃ σ τ : Equiv.Perm (Fin n), ∀ i j, A i j = halfCycleMatrix n (σ i) (τ j)) :=
  lavi_theorem_1_1_unconditional hn hA hND

/-- **The permanent bound of Foregger's conjecture**: for `n ≥ 2`, every doubly stochastic
`n × n` matrix whose support is nearly decomposable has permanent at least `2^(1-n)`.
This is the inequality part of `foregger_conjecture`. -/
theorem foregger_bound {n : ℕ} (hn : 2 ≤ n) {A : Square n}
    (hA : DoublyStochastic A) (hND : NearlyDecomposable (support A)) :
    (2 : ℝ) ^ ((1 : ℤ) - (n : ℤ)) ≤ permanent A :=
  (foregger_conjecture hn hA hND).1

end LaviSection2
