import LaviSection2.LaviCycleArithmetic
import Mathlib.GroupTheory.Perm.Support

/-!
# The cycle face in matrix form

This module formalizes the combinatorial part of the cycle-face calculation in
Section 7 of Lavi's preprint.  A single-cycle permutation has exactly two
perfect matchings in the union of its graph with the diagonal.  Consequently,
the permanent of the corresponding one-parameter matrix is
`t ^ n + (1 - t) ^ n`.
-/

namespace LaviSection2

open scoped BigOperators

/-- The standard one-parameter doubly stochastic matrix on a cycle support. -/
def cycleFaceMatrix {n : ℕ} (p : Equiv.Perm (Fin n)) (t : ℝ) : Square n :=
  fun i j ↦ if j = i then t else if j = p i then 1 - t else 0

/-- A matrix has no nonzero entries outside the diagonal-plus-cycle graph. -/
def SupportedOnCycle {n : ℕ} (p : Equiv.Perm (Fin n)) (A : Square n) : Prop :=
  ∀ i j, A i j ≠ 0 → j = i ∨ j = p i

/-- A single cycle of order at least two has no fixed point. -/
theorem singleCycle_ne_apply_self {n : ℕ} (hn : 2 ≤ n)
    {p : Equiv.Perm (Fin n)} (hp : IsSingleCycle p) (i : Fin n) :
    p i ≠ i := by
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨j, hji⟩ := exists_ne i
  obtain ⟨k, hk⟩ := hp i j
  intro hpi
  have hpow : (p ^ k) i = i :=
    Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hpi k
  exact hji (hk.symm.trans hpow)

/--
Every perfect matching supported in the diagonal-plus-cycle graph is one of
the two displayed matchings.
-/
theorem cycle_matching_eq_id_or_cycle {n : ℕ} (hn : 2 ≤ n)
    {p σ : Equiv.Perm (Fin n)} (hp : IsSingleCycle p)
    (hσ : ∀ i, σ i = i ∨ σ i = p i) :
    σ = 1 ∨ σ = p := by
  by_cases hid : ∀ i, σ i = i
  · left
    apply Equiv.ext
    exact hid
  · right
    push Not at hid
    obtain ⟨i, hi⟩ := hid
    have hip : σ i = p i := (hσ i).resolve_left hi
    have hstep : ∀ x, σ x = p x → σ (p x) = p (p x) := by
      intro x hx
      have hpne := singleCycle_ne_apply_self hn hp x
      have hnotfix : σ (p x) ≠ p x := by
        intro hfix
        have := σ.injective (hx.trans hfix.symm)
        exact hpne this.symm
      exact (hσ (p x)).resolve_left hnotfix
    have horbit : ∀ k : ℕ, σ ((p ^ k) i) = p ((p ^ k) i) := by
      intro k
      induction k with
      | zero => simpa using hip
      | succ k ih =>
          rw [pow_succ']
          simpa only [Equiv.Perm.mul_apply, Function.comp_apply] using hstep _ ih
    apply Equiv.ext
    intro j
    obtain ⟨k, rfl⟩ := hp i j
    exact horbit k

/-- The two matchings in a cycle support are distinct in order at least two. -/
theorem singleCycle_ne_one {n : ℕ} (hn : 2 ≤ n)
    {p : Equiv.Perm (Fin n)} (hp : IsSingleCycle p) :
    p ≠ 1 := by
  intro h
  let i : Fin n := ⟨0, lt_of_lt_of_le (by norm_num) hn⟩
  have hne := singleCycle_ne_apply_self hn hp i
  apply hne
  simp [h]

/-- The one-parameter matrices on a single-cycle support are doubly stochastic. -/
theorem doublyStochastic_cycleFaceMatrix {n : ℕ} (hn : 2 ≤ n)
    {p : Equiv.Perm (Fin n)} (hp : IsSingleCycle p) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    DoublyStochastic (cycleFaceMatrix p t) := by
  have hpfix : ∀ i, p i ≠ i := singleCycle_ne_apply_self hn hp
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    simp only [cycleFaceMatrix]
    split_ifs <;> linarith
  · intro i
    have hip : i ≠ p i := (hpfix i).symm
    calc
      (∑ x, cycleFaceMatrix p t i x) =
          ∑ x, ((if x = i then t else 0) +
            if x = p i then 1 - t else 0) := by
        apply Fintype.sum_congr
        intro x
        by_cases hxi : x = i
        · subst x
          simp [cycleFaceMatrix, hip]
        · simp [cycleFaceMatrix, hxi]
      _ = (∑ x, if x = i then t else 0) +
            ∑ x, if x = p i then 1 - t else 0 := by
        rw [Finset.sum_add_distrib]
      _ = t + (1 - t) := by
        rw [Fintype.sum_ite_eq' i (fun _ ↦ t),
          Fintype.sum_ite_eq' (p i) (fun _ ↦ 1 - t)]
      _ = 1 := by ring
  · intro j
    have hpfix' : p.symm j ≠ j := by
      intro h
      have := congr_arg p h
      exact hpfix j (by simpa using this.symm)
    have hjp : j ≠ p.symm j := Ne.symm hpfix'
    calc
      (∑ x, cycleFaceMatrix p t x j) =
          ∑ x, ((if x = j then t else 0) +
            if x = p.symm j then 1 - t else 0) := by
        apply Fintype.sum_congr
        intro x
        have hcond : (j = p x) ↔ x = p.symm j := by
          rw [p.eq_symm_apply, eq_comm]
        by_cases hxj : x = j
        · subst x
          simp [cycleFaceMatrix, hjp]
        · have hjx : ¬j = x := fun h ↦ hxj h.symm
          simp [cycleFaceMatrix, hxj, hjx, hcond]
      _ = (∑ x, if x = j then t else 0) +
            ∑ x, if x = p.symm j then 1 - t else 0 := by
        rw [Finset.sum_add_distrib]
      _ = t + (1 - t) := by
        rw [Fintype.sum_ite_eq' j (fun _ ↦ t),
          Fintype.sum_ite_eq' (p.symm j) (fun _ ↦ 1 - t)]
      _ = 1 := by ring

/--
Every doubly stochastic matrix supported on a single cycle has the standard
one-parameter form.  This internalizes the matrix-to-scalar reduction at the
start of Section 7 of Lavi's proof.
-/
theorem eq_cycleFaceMatrix_of_supported {n : ℕ} (hn : 2 ≤ n)
    {p : Equiv.Perm (Fin n)} (hp : IsSingleCycle p) {A : Square n}
    (hds : DoublyStochastic A) (hs : SupportedOnCycle p A) (a : Fin n) :
    A = cycleFaceMatrix p (A a a) := by
  have hpfix : ∀ i, p i ≠ i := singleCycle_ne_apply_self hn hp
  have hrow : ∀ i, A i i + A i (p i) = 1 := by
    intro i
    have hip : i ≠ p i := (hpfix i).symm
    calc
      A i i + A i (p i) =
          (∑ j, if j = i then A i i else 0) +
            ∑ j, if j = p i then A i (p i) else 0 := by
        rw [Fintype.sum_ite_eq' i (fun _ ↦ A i i),
          Fintype.sum_ite_eq' (p i) (fun _ ↦ A i (p i))]
      _ = ∑ j, ((if j = i then A i i else 0) +
            if j = p i then A i (p i) else 0) := by
        rw [Finset.sum_add_distrib]
      _ = ∑ j, A i j := by
        apply Fintype.sum_congr
        intro j
        by_cases hji : j = i
        · subst j
          simp [hip]
        by_cases hjp : j = p i
        · subst j
          simp [hpfix i]
        · have hz : A i j = 0 := by
            by_contra hne
            exact (hs i j hne).elim hji hjp
          simp [hji, hjp, hz]
      _ = 1 := hds.2.1 i
  have hcol : ∀ i, A (p i) (p i) + A i (p i) = 1 := by
    intro i
    have hpi : p i ≠ i := hpfix i
    calc
      A (p i) (p i) + A i (p i) =
          (∑ x, if x = p i then A (p i) (p i) else 0) +
            ∑ x, if x = i then A i (p i) else 0 := by
        rw [Fintype.sum_ite_eq' (p i) (fun _ ↦ A (p i) (p i)),
          Fintype.sum_ite_eq' i (fun _ ↦ A i (p i))]
      _ = ∑ x, ((if x = p i then A (p i) (p i) else 0) +
            if x = i then A i (p i) else 0) := by
        rw [Finset.sum_add_distrib]
      _ = ∑ x, A x (p i) := by
        apply Fintype.sum_congr
        intro x
        by_cases hxpi : x = p i
        · subst x
          simp [hpi]
        by_cases hxi : x = i
        · subst x
          simp [hxpi]
        · have hz : A x (p i) = 0 := by
            by_contra hne
            rcases hs x (p i) hne with h | h
            · exact hxpi h.symm
            · exact hxi (p.injective h.symm)
          simp [hxpi, hxi, hz]
      _ = 1 := hds.2.2 (p i)
  have hdiag : ∀ i, A i i = A (p i) (p i) := by
    intro i
    linarith [hrow i, hcol i]
  have hdiagOrbit : ∀ k : ℕ, A a a = A ((p ^ k) a) ((p ^ k) a) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ']
        exact ih.trans (hdiag ((p ^ k) a))
  have hdiagAll : ∀ i, A i i = A a a := by
    intro i
    obtain ⟨k, hk⟩ := hp a i
    exact ((hdiagOrbit k).trans (congrArg (fun x ↦ A x x) hk)).symm
  funext i j
  by_cases hji : j = i
  · subst j
    simp [cycleFaceMatrix, hdiagAll i]
  by_cases hjp : j = p i
  · subst j
    have hentry : A i (p i) = 1 - A a a := by
      linarith [hrow i, hdiagAll i]
    simp [cycleFaceMatrix, hpfix i, hentry]
  · have hz : A i j = 0 := by
      by_contra hne
      exact (hs i j hne).elim hji hjp
    simp [cycleFaceMatrix, hji, hjp, hz]

/-- Cycle support plus double stochasticity yields a parameter in `[0,1]`. -/
theorem exists_cycleFaceMatrix_of_supported {n : ℕ} (hn : 2 ≤ n)
    {p : Equiv.Perm (Fin n)} (hp : IsSingleCycle p) {A : Square n}
    (hds : DoublyStochastic A) (hs : SupportedOnCycle p A) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ A = cycleFaceMatrix p t := by
  let a : Fin n := ⟨0, lt_of_lt_of_le (by norm_num) hn⟩
  refine ⟨A a a, hds.1 a a, ?_, eq_cycleFaceMatrix_of_supported hn hp hds hs a⟩
  have hshape := eq_cycleFaceMatrix_of_supported hn hp hds hs a
  have hnonneg := hds.1 a (p a)
  rw [hshape] at hnonneg
  simp [cycleFaceMatrix, singleCycle_ne_apply_self hn hp a] at hnonneg
  linarith

/-- Exact permanent formula for the one-parameter cycle-face matrix. -/
theorem permanent_cycleFaceMatrix {n : ℕ} (hn : 2 ≤ n)
    {p : Equiv.Perm (Fin n)} (hp : IsSingleCycle p) (t : ℝ) :
    permanent (cycleFaceMatrix p t) = t ^ n + (1 - t) ^ n := by
  classical
  have hpfix : ∀ i, p i ≠ i := singleCycle_ne_apply_self hn hp
  have hpone : p ≠ 1 := singleCycle_ne_one hn hp
  have honep : (1 : Equiv.Perm (Fin n)) ≠ p := Ne.symm hpone
  have hterm : ∀ σ : Equiv.Perm (Fin n),
      (∏ i, cycleFaceMatrix p t i (σ i)) =
        if σ = 1 then t ^ n else if σ = p then (1 - t) ^ n else 0 := by
    intro σ
    by_cases hσone : σ = 1
    · subst σ
      simp [cycleFaceMatrix]
    by_cases hσp : σ = p
    · subst σ
      simp [cycleFaceMatrix, hpfix, hpone]
    · have hbad : ∃ i, σ i ≠ i ∧ σ i ≠ p i := by
        by_contra hnone
        push Not at hnone
        exact (cycle_matching_eq_id_or_cycle hn hp fun i ↦
          (eq_or_ne (σ i) i).imp_right (hnone i)).elim hσone hσp
      obtain ⟨i, hi, hip⟩ := hbad
      rw [ite_eq_right hσone, ite_eq_right hσp]
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [cycleFaceMatrix, hi, hip]
  simp only [permanent, hterm]
  calc
    (∑ σ : Equiv.Perm (Fin n),
        if σ = 1 then t ^ n else if σ = p then (1 - t) ^ n else 0) =
        ∑ σ : Equiv.Perm (Fin n),
          ((if σ = 1 then t ^ n else 0) +
            if σ = p then (1 - t) ^ n else 0) := by
      apply Fintype.sum_congr
      intro σ
      by_cases hσone : σ = 1
      · subst σ
        simp [honep]
      · simp only [ite_eq_right hσone, zero_add]
    _ = (∑ σ : Equiv.Perm (Fin n), if σ = 1 then t ^ n else 0) +
          ∑ σ : Equiv.Perm (Fin n), if σ = p then (1 - t) ^ n else 0 := by
      rw [Finset.sum_add_distrib]
    _ = t ^ n + (1 - t) ^ n := by
      rw [
        Fintype.sum_ite_eq' (1 : Equiv.Perm (Fin n)) (fun _ ↦ t ^ n),
        Fintype.sum_ite_eq' p (fun _ ↦ (1 - t) ^ n)]

/-- The cycle-face matrices satisfy Foregger's lower bound. -/
theorem cycleFaceMatrix_foregger_lower {n : ℕ} (hn : 2 ≤ n)
    {p : Equiv.Perm (Fin n)} (hp : IsSingleCycle p) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    foreggerTarget n ≤ permanent (cycleFaceMatrix p t) := by
  rw [permanent_cycleFaceMatrix hn hp]
  exact lavi_cycle_scalar_lower t ht0 ht1

/-- Equality on a cycle face occurs exactly at the balanced matrix. -/
theorem cycleFaceMatrix_permanent_eq_iff {n : ℕ} (hn : 2 ≤ n)
    {p : Equiv.Perm (Fin n)} (hp : IsSingleCycle p) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    permanent (cycleFaceMatrix p t) = foreggerTarget n ↔ t = 1 / 2 := by
  rw [permanent_cycleFaceMatrix hn hp]
  exact lavi_cycle_scalar_eq_iff hn ht0 ht1

/-- The balanced cycle-face matrix is the canonical equality candidate. -/
theorem isCanonicalHalfCycle_cycleFaceMatrix_half {n : ℕ} (hn : 2 ≤ n)
    {p : Equiv.Perm (Fin n)} (hp : IsSingleCycle p) :
    IsCanonicalHalfCycle (cycleFaceMatrix p (1 / 2)) := by
  refine ⟨p, hp, ?_⟩
  intro i j
  have hpfix := singleCycle_ne_apply_self hn hp i
  by_cases hji : j = i
  · subst j
    simp [cycleFaceMatrix]
  by_cases hjp : j = p i
  · subst j
    norm_num [cycleFaceMatrix, hpfix]
  · simp [cycleFaceMatrix, hji, hjp]

/-- The complete lower bound on every doubly stochastic cycle-supported matrix. -/
theorem cycleSupported_foregger_lower {n : ℕ} (hn : 2 ≤ n)
    {p : Equiv.Perm (Fin n)} (hp : IsSingleCycle p) {A : Square n}
    (hds : DoublyStochastic A) (hs : SupportedOnCycle p A) :
    foreggerTarget n ≤ permanent A := by
  obtain ⟨t, ht0, ht1, rfl⟩ := exists_cycleFaceMatrix_of_supported hn hp hds hs
  exact cycleFaceMatrix_foregger_lower hn hp ht0 ht1

/-- Equality on a doubly stochastic cycle face is exactly the balanced point. -/
theorem cycleSupported_permanent_eq_iff {n : ℕ} (hn : 2 ≤ n)
    {p : Equiv.Perm (Fin n)} (hp : IsSingleCycle p) {A : Square n}
    (hds : DoublyStochastic A) (hs : SupportedOnCycle p A) :
    permanent A = foreggerTarget n ↔ A = cycleFaceMatrix p (1 / 2) := by
  obtain ⟨t, ht0, ht1, hshape⟩ := exists_cycleFaceMatrix_of_supported hn hp hds hs
  constructor
  · intro heq
    have hperm : permanent (cycleFaceMatrix p t) = foreggerTarget n := by
      rwa [← hshape]
    have ht := (cycleFaceMatrix_permanent_eq_iff hn hp ht0 ht1).mp hperm
    rw [hshape, ht]
  · intro hbalanced
    rw [hbalanced]
    exact (cycleFaceMatrix_permanent_eq_iff hn hp (by norm_num) (by norm_num)).mpr rfl

/--
The cycle branch of Foregger's sharp theorem, including the
row/column-relabelled equality predicate.
-/
theorem cycleSupported_foregger_sharp {n : ℕ} (hn : 2 ≤ n)
    {p : Equiv.Perm (Fin n)} (hp : IsSingleCycle p) {A : Square n}
    (hds : DoublyStochastic A) (hs : SupportedOnCycle p A) :
    foreggerTarget n ≤ permanent A ∧
      (permanent A = foreggerTarget n → IsHalfCycle A) := by
  refine ⟨cycleSupported_foregger_lower hn hp hds hs, ?_⟩
  intro heq
  have hbalanced := (cycleSupported_permanent_eq_iff hn hp hds hs).mp heq
  rw [hbalanced]
  refine ⟨1, 1, ?_⟩
  change IsCanonicalHalfCycle (cycleFaceMatrix p (1 / 2))
  exact isCanonicalHalfCycle_cycleFaceMatrix_half hn hp

end LaviSection2
