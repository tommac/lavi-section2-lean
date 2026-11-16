import LaviSection2.LaviEqualityCase

/-!
# Lavi Section 7: the induction skeleton of Theorem 1.1

Section 7 of Lavi's preprint proves Theorem 1.1 (Foregger's conjecture) by
strong induction on the order `n`, simultaneously for all nearly decomposable
(ND) supports.  This module formalizes the skeleton of that induction and
reduces the theorem to **one hypothesis about terminal supports**:

  `hterm`: for every `n ≥ 3`, assuming the Foregger bound in all orders
  `k < n`, every permanent minimizer `A` of the face `Ω(D)` of a `Terminal`
  ND support `D` of order `n` satisfies `per A > 2^(1-n)`.

The paper establishes this strictness in branches 2-5 of its induction (lines
772-800), using the terminal classification (Lemma 2.5), the entropy and
tight-cut machinery of Sections 3-6 and the induction hypothesis on smaller
canonical remainders.  None of that is proved or used here: `hterm` is an
assumption of `foreggerSharpAt_of_terminal_strict`.

What is proved here, from `hterm`:

* the base cases, orders `0`, `1`, `2` (`LaviFaceBasics`); order one is
  vacuous for the Lean predicate `NearlyDecomposable`, and `K_{2,2}`, which is
  `Terminal` in the Lean sense, is handled as the cycle face of order two;
* for `n ≥ 3`: a face minimizer `Y` of `Ω(support A)` exists; if the support
  is `Terminal`, `hterm` gives the strict bound; otherwise a degree-two line
  has an ND contraction and (7.1) gives the bound (`bound_of_not_terminal`);
* equality: `per A = 2^(1-n)` makes `A` itself a face minimizer; the terminal
  branch is strict, so the contraction branch applies and `A` is a half cycle
  (`isHalfCycle_of_not_terminal`).

One difference from the paper's organization: the paper first settles all
cycle faces by the explicit formula `t^n + (1-t)^n` (lines 743-745) and then
runs its five branches on noncycle supports.  Here the induction uses the
cycle-face formula only at order two; a cycle support of order at least three
is not `Terminal` (`IsCycleSupport.not_terminal`), so it goes through the
contraction branch, and `hterm` only concerns noncycle supports.  (The
paper's statement on all cycle faces is available separately and
unconditionally as `cycleFace_foregger_sharp`.)

`foreggerSharpAt_of_face_strict_terminal` is the same reduction with the
induction hypothesis handed to `hterm` in whole-face form.

The second half of the module derives the face-level statements: the sharp
statement on the whole closed face of every ND support, the equivalence
"equality iff half cycle", and the "Moreover" part of Theorem 1.1 (strictness
on every noncycle ND face, lines 809-811).  Finally
`lavi_theorem_1_1_of_foreggerSharpAt` restates `ForeggerSharpAt n`, `n ≥ 2`,
as Theorem 1.1 in the paper's own vocabulary (`2^(1-n)` as an integer power,
the cycle `(1 2 ... n)`, connected 2-regular supports).

In the docstrings `2^(1-n)` stands for `foreggerTarget n`; the two agree for
`n ≥ 1` (`foreggerTarget_eq_zpow`), and `foreggerTarget 0 = 1`.
-/

namespace LaviSection2

/-! ### The induction -/

/-- **The induction step of Section 7** (lines 764-808) at order `m + 1 ≥ 3`.  Assume the
sharp statement at order `m` and strictness at the face minimizers of the `Terminal` nearly
decomposable supports of order `m + 1` (an assumption here; the paper's branches 2-5).  Then
the sharp statement holds at order `m + 1`: every doubly stochastic matrix `A` of order
`m + 1` with nearly decomposable support has `per A ≥ 2^(1-(m+1))`, and equality forces `A`
to be a half cycle. -/
theorem foreggerSharpAt_succ_of_strict_terminal {m : ℕ} (hm : 2 ≤ m)
    (hIH : ForeggerSharpAt m)
    (hterm : ∀ D : Fin (m + 1) → Fin (m + 1) → Prop, NearlyDecomposable D → Terminal D →
      ∀ A, FaceMinimizer D A → foreggerTarget (m + 1) < permanent A) :
    ForeggerSharpAt (m + 1) := by
  intro A hA hND
  have hAface : InFace (support A) A := inFace_support hA
  obtain ⟨Y, hY⟩ := exists_faceMinimizer ⟨A, hAface⟩
  by_cases hT : Terminal (support A)
  · -- terminal branch: strict, so equality is impossible
    have hlt : foreggerTarget (m + 1) < permanent A :=
      lt_of_lt_of_le (hterm _ hND hT Y hY) (hY.2 A hAface)
    exact ⟨hlt.le, fun heq => absurd heq (ne_of_gt hlt)⟩
  · -- contraction branch: (7.1) at the minimizer, then the equality case
    have hbound := bound_of_not_terminal hIH.foreggerBoundAt hND hY hT
    refine ⟨hbound.trans (hY.2 A hAface), fun heq => ?_⟩
    have hAmin : FaceMinimizer (support A) A :=
      ⟨hAface, fun B hB => heq ▸ hbound.trans (hY.2 B hB)⟩
    exact isHalfCycle_of_not_terminal hm hIH hND hAmin hT heq

/-- **Section 7 modulo the terminal branch.**  Suppose that for every `n ≥ 3`, given the
Foregger bound in all orders `k < n`, every permanent minimizer of the face of every
`Terminal` nearly decomposable support of order `n` is strictly above `2^(1-n)`.  Then
`ForeggerSharpAt n` holds for every `n`.  For `n ≥ 2` this is the bound and the "only if"
half of the equality statement of Theorem 1.1 (lines 39-43): every doubly stochastic matrix
`A` of order `n` with nearly decomposable support satisfies `per A ≥ 2^(1-n)`, and
`per A = 2^(1-n)` implies that `A` is `(1/2)(I + P)` up to independent row and column
permutations.

The hypothesis `hterm` is **assumed**, not proved: it is the content of branches 2-5 of the
paper's induction (lines 772-800, resting on Lemma 2.5 and Sections 3-6).  Everything else
in Section 7 (the base cases, the contraction branch (7.1), and the equality case in the
contraction branch) is proved.  Orders `0` and `1` are included for the induction only:
`ForeggerSharpAt 0` is the trivial statement `1 ≤ 1` about the empty matrix, and
`ForeggerSharpAt 1` is vacuous because no doubly stochastic matrix of order one has
`NearlyDecomposable` support.  The "if" half of the equality statement is
`permanent_eq_foreggerTarget_of_isHalfCycle`. -/
theorem foreggerSharpAt_of_terminal_strict
    (hterm : ∀ n, 3 ≤ n → (∀ k, k < n → ForeggerBoundAt k) →
      ∀ D : Fin n → Fin n → Prop, NearlyDecomposable D → Terminal D →
        ∀ A, FaceMinimizer D A → foreggerTarget n < permanent A) :
    ∀ n, ForeggerSharpAt n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.lt_or_ge n 3 with hlt | hge
    · interval_cases n
      · exact foreggerSharpAt_zero
      · exact foreggerSharpAt_one
      · exact foreggerSharpAt_two
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      exact foreggerSharpAt_succ_of_strict_terminal (by omega) (ih m (Nat.lt_succ_self m))
        (hterm (m + 1) hge fun k hk => (ih k hk).foreggerBoundAt)

/-- Variant of `foreggerSharpAt_of_terminal_strict` in which the terminal hypothesis
receives the induction hypothesis in whole-face form, as the paper's terminal branch uses it
(lines 760-762 and 794-796: "the inductive bound holds on the whole face" of a smaller
nearly decomposable remainder).  The conversion is `face_bound_of_foreggerBoundAt`.  As in
`foreggerSharpAt_of_terminal_strict`, the hypothesis `hterm` is assumed, not proved. -/
theorem foreggerSharpAt_of_face_strict_terminal
    (hterm : ∀ n, 3 ≤ n →
      (∀ k, k < n → ∀ D' : Fin k → Fin k → Prop, NearlyDecomposable D' →
        ∀ B : Square k, InFace D' B → foreggerTarget k ≤ permanent B) →
      ∀ D : Fin n → Fin n → Prop, NearlyDecomposable D → Terminal D →
        ∀ A, FaceMinimizer D A → foreggerTarget n < permanent A) :
    ∀ n, ForeggerSharpAt n :=
  foreggerSharpAt_of_terminal_strict fun n hn ihB =>
    hterm n hn fun k hk _ hD' _ hB => face_bound_of_foreggerBoundAt (ihB k hk) hD' hB

/-! ### Consequences on the whole face -/

/-- The sharp statement on the whole closed face: if `ForeggerSharpAt n` holds, then every
point `A` of the face `Ω(D)` of every nearly decomposable support `D` of order `n`,
including the boundary points whose support is smaller than `D`, satisfies
`foreggerTarget n ≤ per A`, and equality forces `A` to be a half cycle.  (An equality point
is a face minimizer, so its support is `D` by Lemma 2.1; lines 801-802 and 108-110.) -/
theorem face_sharp_of_foreggerSharpAt {n : ℕ} (h : ForeggerSharpAt n)
    {D : Fin n → Fin n → Prop} (hD : NearlyDecomposable D) {A : Square n} (hA : InFace D A) :
    foreggerTarget n ≤ permanent A ∧ (permanent A = foreggerTarget n → IsHalfCycle A) := by
  refine ⟨face_bound_of_foreggerBoundAt h.foreggerBoundAt hD hA, fun heq => ?_⟩
  obtain ⟨-, hs⟩ := faceMinimizer_of_eq_foreggerTarget h.foreggerBoundAt hD hA heq
  exact (h A hA.1 (hs ▸ hD)).2 heq

/-- The equality statement of Theorem 1.1 as an equivalence (lines 42-43): given
`ForeggerSharpAt n` with `n ≥ 2`, a doubly stochastic matrix with nearly decomposable
support has permanent `2^(1-n)` if and only if it is a half cycle. -/
theorem permanent_eq_foreggerTarget_iff_isHalfCycle {n : ℕ} (hn : 2 ≤ n)
    (h : ForeggerSharpAt n) {A : Square n} (hA : DoublyStochastic A)
    (hND : NearlyDecomposable (support A)) :
    permanent A = foreggerTarget n ↔ IsHalfCycle A :=
  ⟨(h A hA hND).2, permanent_eq_foreggerTarget_of_isHalfCycle hn⟩

/-- **The "Moreover" part of Theorem 1.1** (lines 43-45 and 809-811), pointwise form: given
`ForeggerSharpAt n`, on the face `Ω(D)` of a nearly decomposable support `D` that is not a
cycle support the permanent is strictly above `foreggerTarget n` (that is, `2^(1-n)` for
`n ≥ 1`) at every point.  Indeed an equality point would be a face minimizer with support
`D` and a half cycle, whose support is a cycle support. -/
theorem strict_of_not_cycleSupport {n : ℕ} (h : ForeggerSharpAt n) {D : Fin n → Fin n → Prop}
    (hD : NearlyDecomposable D) (hnc : ¬ IsCycleSupport D) {A : Square n} (hA : InFace D A) :
    foreggerTarget n < permanent A := by
  obtain ⟨hle, heq⟩ := face_sharp_of_foreggerSharpAt h hD hA
  refine lt_of_le_of_ne hle fun hEq => hnc ?_
  obtain ⟨-, hs⟩ := faceMinimizer_of_eq_foreggerTarget h.foreggerBoundAt hD hA hEq.symm
  exact hs ▸ isCycleSupport_of_isHalfCycle (heq hEq.symm)

/-- **The "Moreover" part of Theorem 1.1** in the paper's form
`min_{A ∈ Ω(D)} per A > 2^(1-n)` (lines 43-45 and 809-811): given `ForeggerSharpAt n` with
`n ≥ 2`, the face of a nearly decomposable support that is not a cycle support has a
permanent minimizer, and the minimum is strictly above `2^(1-n)`. -/
theorem exists_faceMinimizer_gt_of_not_cycleSupport {n : ℕ} (hn : 2 ≤ n)
    (h : ForeggerSharpAt n) {D : Fin n → Fin n → Prop} (hD : NearlyDecomposable D)
    (hnc : ¬ IsCycleSupport D) :
    ∃ Y, FaceMinimizer D Y ∧ foreggerTarget n < permanent Y := by
  obtain ⟨Y, hY, -⟩ := exists_faceMinimizer_support_eq hn hD
  exact ⟨Y, hY, strict_of_not_cycleSupport h hD hnc hY.1⟩

/-- The dichotomy behind Theorem 1.1 (lines 743-745 and 809-811): given `ForeggerSharpAt n`
with `n ≥ 2`, the value `2^(1-n)` is attained on the face of a nearly decomposable support
`D` if and only if `D` is a cycle support.  (On a cycle face it is attained at the half
cycle with support `D`.) -/
theorem isCycleSupport_iff_exists_eq_foreggerTarget {n : ℕ} (hn : 2 ≤ n)
    (h : ForeggerSharpAt n) {D : Fin n → Fin n → Prop} (hD : NearlyDecomposable D) :
    IsCycleSupport D ↔ ∃ A, InFace D A ∧ permanent A = foreggerTarget n := by
  constructor
  · intro hc
    obtain ⟨A, hA, hs⟩ := exists_isHalfCycle_support_eq hc
    refine ⟨A, ⟨doublyStochastic_of_isHalfCycle hn hA, fun i j hij => ?_⟩,
      permanent_eq_foreggerTarget_of_isHalfCycle hn hA⟩
    rw [← hs]
    exact hij
  · rintro ⟨A, hA, heq⟩
    by_contra hnc
    exact absurd heq (ne_of_gt (strict_of_not_cycleSupport h hD hnc hA))

/-! ### Theorem 1.1 in the vocabulary of the paper -/

/-- **Theorem 1.1 of the paper (lines 39-45), given `ForeggerSharpAt n`.**  Let `n ≥ 2` and
assume the repository's sharp statement at order `n`.  Then, in the paper's own terms:

* every doubly stochastic `n × n` matrix `A` with nearly decomposable support satisfies
  `per A ≥ 2^(1-n)`, with equality if and only if independent row and column permutations
  turn `A` into `(1/2)(I_n + P_n)`, where `P_n` is the permutation matrix of the `n`-cycle
  `finRotate n`;
* if a nearly decomposable support `D` is not a cycle support, i.e. not a connected
  2-regular bipartite support (lines 37-38), then the minimum of the permanent on the face
  `Ω(D)` is attained and is strictly greater than `2^(1-n)`.

This is a translation of `ForeggerSharpAt n` only: it does not prove `ForeggerSharpAt n`,
which `foreggerSharpAt_of_terminal_strict` reduces to the terminal branch of the paper. -/
theorem lavi_theorem_1_1_of_foreggerSharpAt {n : ℕ} (hn : 2 ≤ n) (h : ForeggerSharpAt n) :
    (∀ A : Square n, DoublyStochastic A → NearlyDecomposable (support A) →
      (2 : ℝ) ^ ((1 : ℤ) - (n : ℤ)) ≤ permanent A ∧
        (permanent A = (2 : ℝ) ^ ((1 : ℤ) - (n : ℤ)) ↔
          ∃ r c : Equiv.Perm (Fin n),
            ∀ i j, A (r i) (c j) = if j = i ∨ j = finRotate n i then 1 / 2 else 0)) ∧
    (∀ D : Fin n → Fin n → Prop, NearlyDecomposable D →
      ¬((supportGraph D).Connected ∧
          (∀ i, rowDegreeOn D i = 2) ∧ (∀ j, columnDegreeOn D j = 2)) →
      ∃ Y, FaceMinimizer D Y ∧ (2 : ℝ) ^ ((1 : ℤ) - (n : ℤ)) < permanent Y) := by
  have htar := foreggerTarget_eq_zpow (n := n) (by omega)
  refine ⟨fun A hA hND => ?_, fun D hD hnc => ?_⟩
  · rw [← htar, ← isHalfCycle_iff_finRotate hn]
    exact ⟨(h A hA hND).1, permanent_eq_foreggerTarget_iff_isHalfCycle hn h hA hND⟩
  · rw [← htar]
    exact exists_faceMinimizer_gt_of_not_cycleSupport hn h hD
      (fun hc => hnc ((isCycleSupport_iff_connected_two_regular hn).1 hc))

end LaviSection2
