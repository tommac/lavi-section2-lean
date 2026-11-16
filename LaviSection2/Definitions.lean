import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Common

/-!
# Foregger conjecture: theorem vocabulary

This file gives a proposition-level formal vocabulary for Foregger's
conjecture: permanents, doubly stochastic matrices, supports, full
indecomposability and near decomposability.  It deliberately does not turn external
certificates or prose proofs into axioms.
-/

namespace LaviSection2

open scoped BigOperators

/-- A real square matrix of order `n`. -/
abbrev Square (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- The permanent, defined directly as the sum over permutations. -/
noncomputable def permanent {n : ℕ} (A : Square n) : ℝ :=
  ∑ σ : Equiv.Perm (Fin n), ∏ i, A i (σ i)

/-- Entrywise nonnegativity. -/
def Nonnegative {n : ℕ} (A : Square n) : Prop :=
  ∀ i j, 0 ≤ A i j

/-- Every row sums to one. -/
def RowStochastic {n : ℕ} (A : Square n) : Prop :=
  ∀ i, ∑ j, A i j = 1

/-- Every column sums to one. -/
def ColumnStochastic {n : ℕ} (A : Square n) : Prop :=
  ∀ j, ∑ i, A i j = 1

/-- The usual doubly stochastic predicate. -/
def DoublyStochastic {n : ℕ} (A : Square n) : Prop :=
  Nonnegative A ∧ RowStochastic A ∧ ColumnStochastic A

/-- The support relation of a matrix. -/
def support {n : ℕ} (A : Square n) : Fin n → Fin n → Prop :=
  fun i j ↦ A i j ≠ 0

/--
The zero-submatrix characterization of full indecomposability.

For every nonempty row set `R` and nonempty column set `C` whose cardinalities
sum to `n`, the rectangle `R × C` contains a support edge.
-/
def FullyIndecomposable {n : ℕ} (S : Fin n → Fin n → Prop) : Prop :=
  ∀ R C : Finset (Fin n),
    R.Nonempty →
    C.Nonempty →
    R.card + C.card = n →
    ∃ i ∈ R, ∃ j ∈ C, S i j

/-- Remove one support edge. -/
def deleteEdge {n : ℕ} (S : Fin n → Fin n → Prop) (a b : Fin n) :
    Fin n → Fin n → Prop :=
  fun i j ↦ S i j ∧ ¬(i = a ∧ j = b)

/-- Inclusion-minimal full indecomposability. -/
def NearlyDecomposable {n : ℕ} (S : Fin n → Fin n → Prop) : Prop :=
  FullyIndecomposable S ∧
    ∀ i j, S i j → ¬FullyIndecomposable (deleteEdge S i j)

/-- Foregger's unnormalized target value, written without integer exponents. -/
noncomputable def foreggerTarget (n : ℕ) : ℝ :=
  ((2 : ℝ) ^ (n - 1))⁻¹

/-- The normalized permanent `ρ = 2^(n-1) per(A)`. -/
noncomputable def rho {n : ℕ} (A : Square n) : ℝ :=
  (2 : ℝ) ^ (n - 1) * permanent A

/-- The lower-bound part of Foregger's conjecture at order `n`. -/
def ForeggerBoundAt (n : ℕ) : Prop :=
  ∀ A : Square n,
    DoublyStochastic A →
    NearlyDecomposable (support A) →
    foreggerTarget n ≤ permanent A

/-- A permutation consists of one orbit. -/
def IsSingleCycle {n : ℕ} (p : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j, ∃ k : ℕ, (p ^ k) i = j

/-- Independently relabel the row and column indices of a square matrix. -/
def relabel {n : ℕ} (r c : Equiv.Perm (Fin n)) (A : Square n) : Square n :=
  fun i j ↦ A (r i) (c j)

/-- The canonical equality candidate `(I + P)/2` for a full-cycle permutation `P`. -/
def IsCanonicalHalfCycle {n : ℕ} (A : Square n) : Prop :=
  ∃ p : Equiv.Perm (Fin n),
    IsSingleCycle p ∧
      ∀ i j, A i j = if j = i ∨ j = p i then (1 / 2 : ℝ) else 0

/--
The equality class from Foregger's conjecture: a canonical half-cycle up to
independent permutations of the rows and columns.
-/
def IsHalfCycle {n : ℕ} (A : Square n) : Prop :=
  ∃ r c : Equiv.Perm (Fin n), IsCanonicalHalfCycle (relabel r c A)

/-- Bound plus the claimed equality classification. -/
def ForeggerSharpAt (n : ℕ) : Prop :=
  ∀ A : Square n,
    DoublyStochastic A →
    NearlyDecomposable (support A) →
    foreggerTarget n ≤ permanent A ∧
      (permanent A = foreggerTarget n → IsHalfCycle A)

/--
The abstract weak-terminal inequality at shadow order `m`.

`P` is intentionally a parameter: instantiating it requires formal definitions
of the localized weak-cleanup shadows and their interior fixed-point locus.
-/
def WeakTerminalAt (P : ℕ → Type*) (rhoW : ∀ m, P m → ℝ) (m : ℕ) : Prop :=
  ∀ C : P m, 1 < rhoW m C

end LaviSection2
