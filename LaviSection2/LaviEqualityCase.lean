import LaviSection2.LaviContractionBranch
import LaviSection2.RelabelInvariance
import Mathlib.GroupTheory.Perm.Fin

/-!
# Lavi Section 7: cycle supports and the equality case

This module formalizes the equality part of Theorem 1.1 of Lavi's preprint in
the contraction branch (lines 801-808), together with the vocabulary needed
to state the theorem faithfully.

## Cycle supports and half cycles

The paper's equality class is "`A` is obtained from `(1/2)(I_n + P_n)` by
independent row and column permutations", `P_n` the permutation matrix of the
`n`-cycle `(1 2 ... n)` (lines 37-43).  The repository's `IsHalfCycle A` says
that some relabelling `A (r i) (c j)` equals `1/2` on the diagonal and on the
graph of a single-cycle permutation `p`, and `0` elsewhere.

* `cycleAdj p` is the labelled cycle graph "row `i` meets columns `i` and
  `p i`"; it is fully indecomposable exactly when `p` is a single cycle, and
  then nearly decomposable for `n ≥ 2`.
* `IsCycleSupport D`: up to independent relabelling of rows and columns, `D`
  is `cycleAdj p` for a single cycle `p`.  The paper defines a cycle support
  as "a connected 2-regular bipartite support" (lines 37-38);
  `isCycleSupport_iff_connected_two_regular` shows that the two definitions
  agree in every order `n ≥ 2`.  For fully indecomposable supports, the only
  ones Theorem 1.1 speaks about, connectedness is automatic and
  `IsCycleSupport` is equivalent to 2-regularity
  (`isCycleSupport_iff_two_regular`).  A cycle support of order at least two
  is nearly decomposable, and never `Terminal` in order at least three.
* `isHalfCycle_iff_finRotate`: for `n ≥ 2`, `IsHalfCycle` is exactly the
  paper's class with the specific cycle `P_n = (1 2 ... n)` (Mathlib's
  `finRotate n`); `isHalfCycle_iff_submatrix_finRotate` is the same statement
  with the literal matrix `(1/2)(I_n + P_n)`.
* The converse of the equality statement:
  `permanent_eq_foreggerTarget_of_isHalfCycle`,
  `doublyStochastic_of_isHalfCycle`,
  `nearlyDecomposable_support_of_isHalfCycle`: every half cycle of order
  `n ≥ 2` is an ND doubly stochastic matrix with permanent `2^(1-n)`.
* `cycleFace_foregger_sharp`: the theorem on all cycle faces (lines 743-745),
  unconditionally, from the explicit formula `t^n + (1-t)^n` of
  `LaviCycleFace`.

## The equality case in the contraction branch

Let `A` be a face minimizer of the ND face `Ω(D)` of order `n ≥ 3` with
`per A = 2^(1-n)`, and let a degree-two line have an ND contraction.  Then
`per C(A) = 2^(2-n)`, so by the induction hypothesis `C(A)` is a half cycle.

The paper concludes by counting edges: the support of `C(A)` has `2(n-1)`
edges, Lemma 2.3 shows that the contraction removed exactly two, every line
of `D` has degree at least two, hence exactly two, and `D` is a cycle support
whose unique minimizing weights are `1/2`.  We use the same ingredients with
different bookkeeping, transporting *entries* instead of edge counts:

1. every entry of a half cycle is `0` or `1/2` (`half_entries_of_isHalfCycle`);
2. by Lemma 2.3 the two merged rows share no column other than the contracted
   one, so every entry of `A` outside the contracted column is zero or an
   entry of `C(A)`, and the two entries in the contracted column are forced
   to be `1/2` by the row sums (`half_entries_of_contractMatrix`);
3. a doubly stochastic matrix with entries in `{0, 1/2}` has a 2-regular
   support (`two_regular_of_half_entries`);
4. a fully indecomposable 2-regular support is a cycle support
   (`isCycleSupport_of_two_regular`: a perfect matching and the second
   neighbours give a permutation `p`, and full indecomposability forces a
   single orbit), so `A` is a half cycle (`isHalfCycle_of_half_entries`).

The result is `isHalfCycle_of_not_terminal`.
-/

namespace LaviSection2

open scoped BigOperators

/-! ### Single-cycle permutations -/

/-- The repository's `IsSingleCycle` (one orbit under natural-number powers) is Mathlib's
"any two points lie in the same cycle" (auxiliary). -/
theorem isSingleCycle_iff_sameCycle {n : ℕ} (p : Equiv.Perm (Fin n)) :
    IsSingleCycle p ↔ ∀ i j, p.SameCycle i j := by
  constructor
  · intro h i j
    obtain ⟨k, hk⟩ := h i j
    exact ⟨(k : ℤ), by simpa using hk⟩
  · intro h i j
    exact (h i j).exists_nat_pow_eq

/-- For order at least two, `IsSingleCycle p` says that `p` is a cycle in Mathlib's sense
(`Equiv.Perm.IsCycle`) moving every point, i.e. an `n`-cycle as in the paper (line 37). -/
theorem isSingleCycle_iff_isCycle {n : ℕ} (hn : 2 ≤ n) (p : Equiv.Perm (Fin n)) :
    IsSingleCycle p ↔ p.IsCycle ∧ ∀ i, p i ≠ i := by
  constructor
  · intro h
    have hfix := singleCycle_ne_apply_self hn h
    refine ⟨?_, hfix⟩
    let a : Fin n := ⟨0, by omega⟩
    exact ⟨a, hfix a, fun y _ => (isSingleCycle_iff_sameCycle p).1 h a y⟩
  · rintro ⟨hc, hfix⟩
    rw [isSingleCycle_iff_sameCycle]
    intro i j
    exact hc.sameCycle (hfix i) (hfix j)

/-- The inverse of a single cycle is a single cycle (auxiliary). -/
theorem isSingleCycle_inv {n : ℕ} {p : Equiv.Perm (Fin n)} (hp : IsSingleCycle p) :
    IsSingleCycle p⁻¹ := by
  rw [isSingleCycle_iff_sameCycle] at hp ⊢
  intro i j
  exact Equiv.Perm.sameCycle_inv.2 (hp i j)

/-- The rotation `i ↦ i + 1` of `Fin n`, i.e. the `n`-cycle `(1 2 ... n)` of the paper
(line 37), is a single cycle for `n ≥ 2`. -/
theorem isSingleCycle_finRotate {n : ℕ} (hn : 2 ≤ n) : IsSingleCycle (finRotate n) :=
  (isSingleCycle_iff_isCycle hn _).2 ⟨isCycle_finRotate_of_le hn, fun i => by
    have hi : i ∈ (finRotate n).support := by
      rw [support_finRotate_of_le hn]
      exact Finset.mem_univ i
    exact Equiv.Perm.mem_support.1 hi⟩

/-! ### Relabelling back -/

/-- Relabelling by `r, c` and then by the inverse permutations gives the matrix back
(auxiliary). -/
theorem relabel_inv_relabel {n : ℕ} (r c : Equiv.Perm (Fin n)) (A : Square n) :
    relabel r⁻¹ c⁻¹ (relabel r c A) = A := by
  funext i j
  simp [relabel]

/-- Relabelling a support by `r, c` and then by the inverse permutations gives it back
(auxiliary). -/
theorem relabelSupport_inv_relabelSupport {n : ℕ} (r c : Equiv.Perm (Fin n))
    (S : Fin n → Fin n → Prop) : relabelSupport r⁻¹ c⁻¹ (relabelSupport r c S) = S := by
  funext i j
  simp [relabelSupport]

/-! ### Counting neighbours -/

/-- A row with exactly the two distinct neighbours `c ≠ d` has degree two (auxiliary; the
converse of `row_neighbors_eq_pair_of_degree_two`). -/
theorem rowDegreeOn_eq_two_of_pair {n : ℕ} {D : Fin n → Fin n → Prop} {r c d : Fin n}
    (hcd : c ≠ d) (h : ∀ y, D r y ↔ y = c ∨ y = d) : rowDegreeOn D r = 2 := by
  unfold rowDegreeOn
  have hN : rowNeighborsOn D {r} = {c, d} := by
    ext y
    simp only [mem_rowNeighborsOn, Finset.mem_singleton, exists_eq_left, Finset.mem_insert]
    exact h y
  rw [hN, Finset.card_pair hcd]

/-- A column with exactly the two distinct neighbours `r ≠ s` has degree two (auxiliary;
the converse of `column_neighbors_eq_pair_of_degree_two`). -/
theorem columnDegreeOn_eq_two_of_pair {n : ℕ} {D : Fin n → Fin n → Prop} {r s c : Fin n}
    (hrs : r ≠ s) (h : ∀ x, D x c ↔ x = r ∨ x = s) : columnDegreeOn D c = 2 :=
  rowDegreeOn_eq_two_of_pair (D := fun j i => D i j) hrs h

/-- A finite sum of numbers in `{0, 1/2}` is half the number of nonzero terms; `t` is any
description of the set of indices in `s` with a nonzero term (auxiliary). -/
theorem sum_eq_card_mul_half_of_half_entries {ι : Type*} {s t : Finset ι} {f : ι → ℝ}
    (hf : ∀ j ∈ s, f j = 0 ∨ f j = 1 / 2) (hts : t ⊆ s) (ht : ∀ j ∈ s, j ∈ t ↔ f j ≠ 0) :
    ∑ j ∈ s, f j = (t.card : ℝ) * (1 / 2) := by
  rw [← Finset.sum_subset hts (fun j hj hjt => by_contra fun h => hjt ((ht j hj).2 h)),
    Finset.sum_congr rfl
      (fun j hj => (hf j (hts hj)).resolve_left ((ht j (hts hj)).1 hj)),
    Finset.sum_const, nsmul_eq_mul]

/-! ### The labelled cycle graph -/

/-- The labelled cycle graph of a permutation `p`: row `i` is joined to the columns `i` and
`p i`.  For a single cycle `p` of order at least two this is the support of the matrix
`(1/2)(I + P)` of Theorem 1.1 (line 42), a bipartite cycle through all `2n` vertices. -/
def cycleAdj {n : ℕ} (p : Equiv.Perm (Fin n)) : Fin n → Fin n → Prop :=
  fun i j => j = i ∨ j = p i

/-- The labelled cycle graph of a single-cycle permutation is fully indecomposable: a zero
block `R × C` with `|R| + |C| = n` would make `R` a proper nonempty set of rows closed under
`p`.  (Implicit in Theorem 1.1, whose equality class consists of ND matrices.) -/
theorem fullyIndecomposable_cycleAdj {n : ℕ} {p : Equiv.Perm (Fin n)}
    (hp : IsSingleCycle p) : FullyIndecomposable (cycleAdj p) := by
  intro R C hR hC hcard
  by_contra hno
  have hno' : ∀ i ∈ R, ∀ j ∈ C, ¬cycleAdj p i j :=
    fun i hi j hj hij => hno ⟨i, hi, j, hj, hij⟩
  have hsub : R ⊆ Finset.univ \ C := by
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, fun hiC => hno' i hi i hiC (Or.inl rfl)⟩
  have hcardC : (Finset.univ \ C).card = R.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ C), Finset.card_univ, Fintype.card_fin]
    omega
  have hReq : R = Finset.univ \ C := Finset.eq_of_subset_of_card_le hsub (by omega)
  have hclosed : ∀ i ∈ R, p i ∈ R := by
    intro i hi
    rw [hReq]
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, fun hpC => hno' i hi (p i) hpC (Or.inr rfl)⟩
  obtain ⟨i, hi⟩ := hR
  obtain ⟨j, hj⟩ := hC
  obtain ⟨k, hk⟩ := hp i j
  have hpow : ∀ k : ℕ, (p ^ k) i ∈ R := by
    intro k
    induction k with
    | zero => simpa using hi
    | succ k ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        exact hclosed _ ih
  have hjR : j ∈ R := hk ▸ hpow k
  rw [hReq] at hjR
  exact (Finset.mem_sdiff.mp hjR).2 hj

/-- Conversely, if the labelled cycle graph of `p` is fully indecomposable then `p` is a
single cycle: the orbit `O` of a point is closed under `p`, so `O × Oᶜ` is a zero block.
This is the step "`D` is connected; hence ... `D` is a cycle support" of lines 807-808, with
full indecomposability in place of connectedness. -/
theorem isSingleCycle_of_fullyIndecomposable_cycleAdj {n : ℕ} {p : Equiv.Perm (Fin n)}
    (h : FullyIndecomposable (cycleAdj p)) : IsSingleCycle p := by
  classical
  intro i j
  by_contra hno
  let O : Finset (Fin n) := Finset.univ.filter fun x => ∃ k : ℕ, (p ^ k) i = x
  have hiO : i ∈ O := Finset.mem_filter.2 ⟨Finset.mem_univ _, 0, by simp⟩
  have hjO : j ∉ O := fun hj => hno (Finset.mem_filter.1 hj).2
  have hclosed : ∀ x ∈ O, p x ∈ O := by
    intro x hx
    obtain ⟨k, hk⟩ := (Finset.mem_filter.1 hx).2
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, k + 1, by
      rw [pow_succ', Equiv.Perm.mul_apply, hk]⟩
  have hcard : O.card + (Finset.univ \ O).card = n := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ O), Finset.card_univ, Fintype.card_fin]
    have hle := Finset.card_le_univ O
    rw [Fintype.card_fin] at hle
    omega
  obtain ⟨x, hx, y, hy, hxy⟩ := h O (Finset.univ \ O) ⟨i, hiO⟩
    ⟨j, Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hjO⟩⟩ hcard
  have hyO : y ∉ O := (Finset.mem_sdiff.mp hy).2
  rcases hxy with e | e
  · exact hyO (e ▸ hx)
  · exact hyO (e ▸ hclosed x hx)

/-- The labelled cycle graph of `p` is fully indecomposable exactly when `p` is a single
cycle (auxiliary summary of the two previous statements). -/
theorem fullyIndecomposable_cycleAdj_iff {n : ℕ} {p : Equiv.Perm (Fin n)} :
    FullyIndecomposable (cycleAdj p) ↔ IsSingleCycle p :=
  ⟨isSingleCycle_of_fullyIndecomposable_cycleAdj, fullyIndecomposable_cycleAdj⟩

/-- The labelled cycle graph of a single cycle of order at least two is nearly
decomposable: after deleting an edge at row `i`, that row has a single neighbour `y`, and
`{i} × {y}ᶜ` is a zero block.  (Implicit in Theorem 1.1: the matrices `(1/2)(I + P)` of the
equality class are ND.) -/
theorem nearlyDecomposable_cycleAdj {n : ℕ} (hn : 2 ≤ n) {p : Equiv.Perm (Fin n)}
    (hp : IsSingleCycle p) : NearlyDecomposable (cycleAdj p) := by
  refine ⟨fullyIndecomposable_cycleAdj hp, ?_⟩
  intro i j hij hfi
  let y : Fin n := if j = i then p i else i
  have hC : (Finset.univ \ {y} : Finset (Fin n)).Nonempty :=
    ⟨p y, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by
      simpa using singleCycle_ne_apply_self hn hp y⟩⟩
  obtain ⟨a, ha, b, hb, hcyc, hdel⟩ := hfi {i} (Finset.univ \ {y})
    (Finset.singleton_nonempty i) hC (by
      rw [Finset.card_singleton, Finset.card_sdiff_of_subset (Finset.subset_univ _),
        Finset.card_univ, Fintype.card_fin, Finset.card_singleton]
      omega)
  rw [Finset.mem_singleton] at ha
  have hby : b ≠ y := by
    have := (Finset.mem_sdiff.mp hb).2
    simpa using this
  rw [ha] at hcyc
  by_cases hji : j = i
  · have hy : y = p i := by simp [y, hji]
    rcases hcyc with e | e
    · exact hdel ⟨ha, e.trans hji.symm⟩
    · exact hby (e.trans hy.symm)
  · have hjp : j = p i := hij.resolve_left hji
    have hy : y = i := by simp [y, hji]
    rcases hcyc with e | e
    · exact hby (e.trans hy.symm)
    · exact hdel ⟨ha, e.trans hjp.symm⟩

/-! ### Cycle supports -/

/-- A **cycle support**: up to independent relabellings `r` of the rows and `c` of the
columns, the support is the labelled cycle graph of a single-cycle permutation `p`.

The paper (lines 37-38) defines a cycle support as "a connected 2-regular bipartite
support".  The two definitions agree in every order `n ≥ 2`
(`isCycleSupport_iff_connected_two_regular`); for a fully indecomposable support, such as
every support in Theorem 1.1, connectedness is automatic and `IsCycleSupport` is equivalent
to 2-regularity (`isCycleSupport_iff_two_regular`).  At order one the definition holds
exactly for the singleton support, which is connected but 1-regular; order one is outside
the theorem. -/
def IsCycleSupport {n : ℕ} (D : Fin n → Fin n → Prop) : Prop :=
  ∃ r c p : Equiv.Perm (Fin n), IsSingleCycle p ∧ ∀ i j, D (r i) (c j) ↔ (j = i ∨ j = p i)

/-- A cycle support is fully indecomposable (auxiliary; see
`IsCycleSupport.nearlyDecomposable`). -/
theorem IsCycleSupport.fullyIndecomposable {n : ℕ} {D : Fin n → Fin n → Prop}
    (h : IsCycleSupport D) : FullyIndecomposable D := by
  obtain ⟨r, c, p, hp, hD⟩ := h
  have heq : relabelSupport r c D = cycleAdj p :=
    funext fun i => funext fun j => propext (hD i j)
  have hfi : FullyIndecomposable (relabelSupport r c D) := by
    rw [heq]
    exact fullyIndecomposable_cycleAdj hp
  have hback := fullyIndecomposable_relabelSupport r⁻¹ c⁻¹ hfi
  rwa [relabelSupport_inv_relabelSupport] at hback

/-- A cycle support of order at least two is nearly decomposable (implicit in Theorem 1.1
and in "`K_{2,2}`, a cycle support", line 743).  At order one the cycle support is the
singleton, which is ND in the paper's convention but not for the Lean predicate
`NearlyDecomposable`. -/
theorem IsCycleSupport.nearlyDecomposable {n : ℕ} (hn : 2 ≤ n) {D : Fin n → Fin n → Prop}
    (h : IsCycleSupport D) : NearlyDecomposable D := by
  obtain ⟨r, c, p, hp, hD⟩ := h
  have heq : relabelSupport r c D = cycleAdj p :=
    funext fun i => funext fun j => propext (hD i j)
  have hnd : NearlyDecomposable (relabelSupport r c D) := by
    rw [heq]
    exact nearlyDecomposable_cycleAdj hn hp
  have hback := nearlyDecomposable_relabelSupport r⁻¹ c⁻¹ hnd
  rwa [relabelSupport_inv_relabelSupport] at hback

/-- Every row of a cycle support of order at least two has degree two ("2-regular", line
38). -/
theorem IsCycleSupport.rowDegreeOn_eq_two {n : ℕ} (hn : 2 ≤ n) {D : Fin n → Fin n → Prop}
    (h : IsCycleSupport D) (x : Fin n) : rowDegreeOn D x = 2 := by
  obtain ⟨r, c, p, hp, hD⟩ := h
  have hpfix := singleCycle_ne_apply_self hn hp (r.symm x)
  refine rowDegreeOn_eq_two_of_pair (c := c (r.symm x)) (d := c (p (r.symm x)))
    (fun e => hpfix (c.injective e).symm) (fun y => ?_)
  have h := hD (r.symm x) (c.symm y)
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
  rw [h, Equiv.symm_apply_eq, Equiv.symm_apply_eq]

/-- Every column of a cycle support of order at least two has degree two ("2-regular", line
38). -/
theorem IsCycleSupport.columnDegreeOn_eq_two {n : ℕ} (hn : 2 ≤ n)
    {D : Fin n → Fin n → Prop} (h : IsCycleSupport D) (y : Fin n) :
    columnDegreeOn D y = 2 := by
  obtain ⟨r, c, p, hp, hD⟩ := h
  have hpfix := singleCycle_ne_apply_self hn hp (p.symm (c.symm y))
  rw [Equiv.apply_symm_apply] at hpfix
  refine columnDegreeOn_eq_two_of_pair (r := r (c.symm y)) (s := r (p.symm (c.symm y)))
    (fun e => hpfix (r.injective e)) (fun x => ?_)
  have h := hD (r.symm x) (c.symm y)
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
  rw [h]
  constructor
  · rintro (e | e)
    · exact Or.inl (by rw [e, Equiv.apply_symm_apply])
    · exact Or.inr (by rw [e, Equiv.symm_apply_apply, Equiv.apply_symm_apply])
  · rintro (e | e)
    · exact Or.inl (by rw [e, Equiv.symm_apply_apply])
    · exact Or.inr (by rw [e, Equiv.symm_apply_apply, Equiv.apply_symm_apply])

/-- The bipartite graph of a cycle support of order at least two is connected ("connected",
line 37). -/
theorem IsCycleSupport.connected {n : ℕ} (hn : 2 ≤ n) {D : Fin n → Fin n → Prop}
    (h : IsCycleSupport D) : (supportGraph D).Connected :=
  supportGraph_connected_of_fullyIndecomposable hn h.fullyIndecomposable

/-- Paper, lines 742-743: "In order two, the only ND support is `K_{2,2}`, a cycle
support." -/
theorem isCycleSupport_of_nearlyDecomposable_two {D : Fin 2 → Fin 2 → Prop}
    (hD : NearlyDecomposable D) : IsCycleSupport D := by
  have hall := (nearlyDecomposable_two_iff D).1 hD
  refine ⟨1, 1, Equiv.swap 0 1, isSingleCycle_swap_fin_two, fun i j => ?_⟩
  have hij : j = i ∨ j = Equiv.swap (0 : Fin 2) 1 i := by
    fin_cases i <;> fin_cases j <;> simp
  exact ⟨fun _ => hij, fun _ => hall _ _⟩

/-! ### Recognizing cycle supports -/

/-- A support all of whose lines have degree two contains a perfect matching: half of its
indicator matrix is doubly stochastic, so Hall's theorem for doubly stochastic matrices
applies (auxiliary). -/
theorem exists_perm_of_two_regular {n : ℕ} {D : Fin n → Fin n → Prop}
    (hrow : ∀ i, rowDegreeOn D i = 2) (hcol : ∀ j, columnDegreeOn D j = 2) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, D i (σ i) := by
  classical
  let A : Square n := fun i j => if D i j then 1 / 2 else 0
  have hsupp : ∀ i j, A i j ≠ 0 ↔ D i j := by
    intro i j
    by_cases h : D i j <;> simp [A, h]
  have hhalf : ∀ i j, A i j = 0 ∨ A i j = 1 / 2 := by
    intro i j
    by_cases h : D i j <;> simp [A, h]
  have hA : DoublyStochastic A := by
    refine ⟨fun i j => ?_, fun i => ?_, fun j => ?_⟩
    · rcases hhalf i j with h | h <;> linarith
    · have hsum := sum_eq_card_mul_half_of_half_entries (s := Finset.univ)
        (t := rowNeighborsOn D {i}) (f := fun j => A i j) (fun j _ => hhalf i j)
        (Finset.subset_univ _) (fun j _ => by simp [hsupp])
      have hdeg : (rowNeighborsOn D {i}).card = 2 := hrow i
      rw [hsum, hdeg]
      norm_num
    · have hsum := sum_eq_card_mul_half_of_half_entries (s := Finset.univ)
        (t := rowNeighborsOn (fun j i => D i j) {j}) (f := fun i => A i j)
        (fun i _ => hhalf i j) (Finset.subset_univ _) (fun i _ => by simp [hsupp])
      have hdeg : (rowNeighborsOn (fun j i => D i j) {j}).card = 2 := hcol j
      rw [hsum, hdeg]
      norm_num
  obtain ⟨σ, hσ⟩ := exists_perm_support_of_doublyStochastic hA
  exact ⟨σ, fun i => (hsupp i (σ i)).1 (hσ i)⟩

/-- In a support all of whose lines have degree two, a perfect matching `σ` determines the
second neighbour of every row, and these second neighbours form another perfect matching:
relabelling the columns by `σ` turns the support into the labelled cycle graph of a
permutation `p`, not yet known to be a single cycle.  (Auxiliary: the 2-regular half of
lines 807-808.) -/
theorem exists_cycleAdj_of_two_regular {n : ℕ} {D : Fin n → Fin n → Prop}
    (hrow : ∀ i, rowDegreeOn D i = 2) (hcol : ∀ j, columnDegreeOn D j = 2)
    {σ : Equiv.Perm (Fin n)} (hσ : ∀ i, D i (σ i)) :
    ∃ p : Equiv.Perm (Fin n), ∀ i j, D i (σ j) ↔ cycleAdj p i j := by
  -- the second neighbour `q i ≠ σ i` of each row
  have hother : ∀ i, ∃ y, y ≠ σ i ∧ ∀ z, D i z ↔ z = σ i ∨ z = y := by
    intro i
    obtain ⟨a, b, hab, hN⟩ := exists_pair_of_rowDegreeOn_eq_two (hrow i)
    rcases (hN (σ i)).1 (hσ i) with h | h
    · exact ⟨b, by rw [h]; exact hab.symm, fun z => by rw [hN z, h]⟩
    · exact ⟨a, by rw [h]; exact hab, fun z => by rw [hN z, h]; exact or_comm⟩
  choose q hq hD using hother
  let p₀ : Fin n → Fin n := fun i => σ.symm (q i)
  have hσp : ∀ i, σ (p₀ i) = q i := fun i => by simp [p₀]
  have hp₀ne : ∀ i, p₀ i ≠ i := by
    intro i h
    apply hq i
    rw [← hσp i, h]
  -- `p₀` is injective: the rows `i`, `i'` and `p₀ i` would be three neighbours of one column
  have hinj : Function.Injective p₀ := by
    intro i i' h
    by_contra hne
    have hqq : q i = q i' := by rw [← hσp i, ← hσp i', h]
    obtain ⟨a, b, -, hN⟩ := exists_pair_of_columnDegreeOn_eq_two (hcol (q i))
    have h1 : D i (q i) := (hD i (q i)).2 (Or.inr rfl)
    have h2 : D i' (q i) := by rw [hqq]; exact (hD i' (q i')).2 (Or.inr rfl)
    have h3 : D (p₀ i) (q i) := by
      have := hσ (p₀ i)
      rwa [hσp i] at this
    have e1 := (hN i).1 h1
    have e2 := (hN i').1 h2
    have e3 := (hN (p₀ i)).1 h3
    have n1 : p₀ i ≠ i := hp₀ne i
    have n2 : p₀ i ≠ i' := by rw [h]; exact hp₀ne i'
    rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2 <;> rcases e3 with e3 | e3
    · exact hne (e1.trans e2.symm)
    · exact hne (e1.trans e2.symm)
    · exact n1 (e3.trans e1.symm)
    · exact n2 (e3.trans e2.symm)
    · exact n2 (e3.trans e2.symm)
    · exact n1 (e3.trans e1.symm)
    · exact hne (e1.trans e2.symm)
    · exact hne (e1.trans e2.symm)
  refine ⟨Equiv.ofBijective p₀ (Finite.injective_iff_bijective.1 hinj), fun i j => ?_⟩
  show D i (σ j) ↔ (j = i ∨ j = p₀ i)
  rw [hD i (σ j)]
  constructor
  · rintro (h | h)
    · exact Or.inl (σ.injective h)
    · exact Or.inr (σ.injective (h.trans (hσp i).symm))
  · rintro (h | h)
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h, hσp])

/-- **Cycle recognition** (lines 806-808: "every line has degree exactly two and `D` is
connected; hence ... `D` is a cycle support").  Let `D` be fully indecomposable with every
row and column of degree two, and let `σ` be a perfect matching inside `D`.  After
relabelling the columns by `σ`, the support is exactly the diagonal together with the graph
of a single-cycle permutation `p`.  Full indecomposability plays the role of the paper's
connectedness. -/
theorem exists_singleCycle_of_two_regular {n : ℕ} {D : Fin n → Fin n → Prop}
    (hFI : FullyIndecomposable D)
    (hrow : ∀ i, rowDegreeOn D i = 2) (hcol : ∀ j, columnDegreeOn D j = 2)
    {σ : Equiv.Perm (Fin n)} (hσ : ∀ i, D i (σ i)) :
    ∃ p : Equiv.Perm (Fin n), IsSingleCycle p ∧ ∀ i j, D i (σ j) ↔ (j = i ∨ j = p i) := by
  obtain ⟨p, hp⟩ := exists_cycleAdj_of_two_regular hrow hcol hσ
  refine ⟨p, isSingleCycle_of_fullyIndecomposable_cycleAdj ?_, hp⟩
  have heq : relabelSupport 1 σ D = cycleAdj p :=
    funext fun i => funext fun j => propext (hp i j)
  rw [← heq]
  exact fullyIndecomposable_relabelSupport 1 σ hFI

/-- A fully indecomposable support all of whose lines have degree two is a cycle support
(lines 806-808). -/
theorem isCycleSupport_of_two_regular {n : ℕ} {D : Fin n → Fin n → Prop}
    (hFI : FullyIndecomposable D)
    (hrow : ∀ i, rowDegreeOn D i = 2) (hcol : ∀ j, columnDegreeOn D j = 2) :
    IsCycleSupport D := by
  obtain ⟨σ, hσ⟩ := exists_perm_of_two_regular hrow hcol
  obtain ⟨p, hp, hiff⟩ := exists_singleCycle_of_two_regular hFI hrow hcol hσ
  exact ⟨1, σ, p, hp, hiff⟩

/-- For a fully indecomposable support of order at least two, being a cycle support in the
sense of `IsCycleSupport` is the same as being 2-regular.  Every support in Theorem 1.1 is
nearly decomposable, hence fully indecomposable, and its graph is then connected
(`supportGraph_connected_of_fullyIndecomposable`); so on those supports this is the paper's
definition "a connected 2-regular bipartite support" (lines 37-38). -/
theorem isCycleSupport_iff_two_regular {n : ℕ} (hn : 2 ≤ n) {D : Fin n → Fin n → Prop}
    (hFI : FullyIndecomposable D) :
    IsCycleSupport D ↔ (∀ i, rowDegreeOn D i = 2) ∧ (∀ j, columnDegreeOn D j = 2) :=
  ⟨fun h => ⟨h.rowDegreeOn_eq_two hn, h.columnDegreeOn_eq_two hn⟩,
    fun h => isCycleSupport_of_two_regular hFI h.1 h.2⟩

/-- A fully indecomposable support of order at least two all of whose lines have degree at
most two is a cycle support: every line of such a support has degree at least two (lines
143-144: "Every FI line has degree at least two"). -/
theorem isCycleSupport_of_degree_le_two {n : ℕ} (hn : 2 ≤ n) {D : Fin n → Fin n → Prop}
    (hFI : FullyIndecomposable D)
    (hrow : ∀ i, rowDegreeOn D i ≤ 2) (hcol : ∀ j, columnDegreeOn D j ≤ 2) :
    IsCycleSupport D :=
  isCycleSupport_of_two_regular hFI
    (fun i => le_antisymm (hrow i) (two_le_rowDegreeOn hn hFI i))
    (fun j => le_antisymm (hcol j) (two_le_columnDegreeOn hn hFI j))

/-- If, after relabelling the columns by `σ`, a support is the labelled cycle graph of `p`
and its bipartite graph is connected, then `p` is a single cycle: lying in the `p`-cycle of
a fixed row is a property of vertices preserved along every edge.  (Auxiliary to
`isCycleSupport_iff_connected_two_regular`.) -/
theorem isSingleCycle_of_connected {n : ℕ} {D : Fin n → Fin n → Prop}
    {σ p : Equiv.Perm (Fin n)} (hD : ∀ i j, D i (σ j) ↔ cycleAdj p i j)
    (hconn : (supportGraph D).Connected) : IsSingleCycle p := by
  rw [isSingleCycle_iff_sameCycle]
  intro i j
  let P : Fin n ⊕ Fin n → Prop :=
    Sum.elim (fun x => p.SameCycle i x) (fun y => p.SameCycle i (σ.symm y))
  have key : ∀ x y, D x y → (p.SameCycle i x ↔ p.SameCycle i (σ.symm y)) := by
    intro x y hxy
    rcases (hD x (σ.symm y)).1 (by rwa [Equiv.apply_symm_apply]) with e | e
    · rw [e]
    · rw [e, Equiv.Perm.sameCycle_apply_right]
  have hadj : ∀ u v, (supportGraph D).Adj u v → (P u ↔ P v) := by
    intro u v huv
    rcases supportGraph_adj_cases huv with ⟨x, y, rfl, rfl, hxy⟩ | ⟨x, y, rfl, rfl, hxy⟩
    · exact key x y hxy
    · exact (key x y hxy).symm
  have hwalk : ∀ u v, (supportGraph D).Reachable u v → P u → P v := by
    rintro u v ⟨w⟩
    induction w with
    | nil => exact id
    | cons h _ ih => exact fun hu => ih ((hadj _ _ h).1 hu)
  exact hwalk (Sum.inl i) (Sum.inl j) (hconn.preconnected _ _) (Equiv.Perm.SameCycle.refl p i)

/-- A connected support all of whose lines have degree two is a cycle support in the sense
of `IsCycleSupport` (the paper's definition, lines 37-38, implies the Lean one). -/
theorem isCycleSupport_of_connected_two_regular {n : ℕ} {D : Fin n → Fin n → Prop}
    (hconn : (supportGraph D).Connected)
    (hrow : ∀ i, rowDegreeOn D i = 2) (hcol : ∀ j, columnDegreeOn D j = 2) :
    IsCycleSupport D := by
  obtain ⟨σ, hσ⟩ := exists_perm_of_two_regular hrow hcol
  obtain ⟨p, hp⟩ := exists_cycleAdj_of_two_regular hrow hcol hσ
  exact ⟨1, σ, p, isSingleCycle_of_connected hp hconn, hp⟩

/-- **Faithfulness of `IsCycleSupport`** (paper, lines 37-38: "A cycle support is a
connected 2-regular bipartite support").  In every order `n ≥ 2`, a support is a cycle
support in the sense of `IsCycleSupport` exactly when its bipartite graph is connected and
every row and every column has degree two. -/
theorem isCycleSupport_iff_connected_two_regular {n : ℕ} (hn : 2 ≤ n)
    {D : Fin n → Fin n → Prop} :
    IsCycleSupport D ↔ (supportGraph D).Connected ∧
      (∀ i, rowDegreeOn D i = 2) ∧ (∀ j, columnDegreeOn D j = 2) :=
  ⟨fun h => ⟨h.connected hn, h.rowDegreeOn_eq_two hn, h.columnDegreeOn_eq_two hn⟩,
    fun h => isCycleSupport_of_connected_two_regular h.1 h.2.1 h.2.2⟩

/-- A nearly decomposable support of order at least three all of whose lines have degree
two is not `Terminal`: by Lemma 2.4 (lines 158-160) the contraction at any column is nearly
decomposable, because both neighbouring rows have degree two. -/
theorem two_regular_not_terminal {n : ℕ} (hn : 3 ≤ n) {D : Fin n → Fin n → Prop}
    (hND : NearlyDecomposable D) (hrow : ∀ i, rowDegreeOn D i = 2)
    (hcol : ∀ j, columnDegreeOn D j = 2) : ¬Terminal D := by
  intro hterm
  let c : Fin n := ⟨0, by omega⟩
  obtain ⟨r, s, hrs, hN⟩ := exists_pair_of_columnDegreeOn_eq_two (hcol c)
  have hrc : D r c := (hN r).2 (Or.inl rfl)
  have hsc : D s c := (hN s).2 (Or.inr rfl)
  exact hterm.1 r s c hrs hrc hsc (hcol c)
    (lavi_lemma_2_4_column hn D hND hrs hrc hsc (hcol c) (Or.inl ⟨hrow r, hrow s⟩))

/-- A cycle support of order at least three is never `Terminal`.  So in the induction of
Section 7 the cycle supports of order at least three fall into the contraction branch, and
a hypothesis about all `Terminal` supports is a hypothesis about noncycle supports only, as
in the paper (lines 745-746: "For a noncycle support, the induction has five branches"). -/
theorem IsCycleSupport.not_terminal {n : ℕ} (hn : 3 ≤ n) {D : Fin n → Fin n → Prop}
    (h : IsCycleSupport D) : ¬Terminal D :=
  two_regular_not_terminal hn (h.nearlyDecomposable (by omega))
    (h.rowDegreeOn_eq_two (by omega)) (h.columnDegreeOn_eq_two (by omega))

/-! ### Half cycles -/

/-- The equality class is invariant under relabelling ("independent row and column
permutations", lines 42-43): if a relabelling of `A` is a half cycle then so is `A`. -/
theorem isHalfCycle_of_relabel {n : ℕ} (r c : Equiv.Perm (Fin n)) {A : Square n}
    (h : IsHalfCycle (relabel r c A)) : IsHalfCycle A := by
  obtain ⟨r', c', h'⟩ := h
  exact ⟨r * r', c * c', h'⟩

/-- The equality class is invariant under relabelling (lines 42-43): every relabelling of a
half cycle is a half cycle. -/
theorem isHalfCycle_relabel {n : ℕ} (r c : Equiv.Perm (Fin n)) {A : Square n}
    (h : IsHalfCycle A) : IsHalfCycle (relabel r c A) := by
  apply isHalfCycle_of_relabel r⁻¹ c⁻¹
  rwa [relabel_inv_relabel]

/-- `IsHalfCycle` is invariant under independent row and column permutations (lines
42-43). -/
theorem isHalfCycle_relabel_iff {n : ℕ} (r c : Equiv.Perm (Fin n)) {A : Square n} :
    IsHalfCycle (relabel r c A) ↔ IsHalfCycle A :=
  ⟨isHalfCycle_of_relabel r c, isHalfCycle_relabel r c⟩

/-- The equality class is closed under transposition: the transpose of `(1/2)(I + P)` is
`(1/2)(I + P⁻¹)` (auxiliary). -/
theorem isHalfCycle_transpose {n : ℕ} {A : Square n} (h : IsHalfCycle A) :
    IsHalfCycle A.transpose := by
  obtain ⟨r, c, p, hp, hA⟩ := h
  refine ⟨c, r, p⁻¹, isSingleCycle_inv hp, fun i j => ?_⟩
  have h1 := hA j i
  simp only [relabel] at h1
  simp only [relabel, Matrix.transpose_apply]
  rw [h1]
  have hiff : (i = j ∨ i = p j) ↔ (j = i ∨ j = p⁻¹ i) :=
    or_congr eq_comm (eq_comm.trans Equiv.Perm.eq_inv_iff_eq.symm)
  simp only [hiff]

/-- Every entry of a half cycle is `0` or `1/2` (the form of `(1/2)(I_n + P_n)`, line 42,
for `n ≥ 2`; the statement itself holds in every order). -/
theorem half_entries_of_isHalfCycle {n : ℕ} {B : Square n} (hB : IsHalfCycle B) :
    ∀ i j, B i j = 0 ∨ B i j = 1 / 2 := by
  obtain ⟨r, c, p, -, hent⟩ := hB
  intro i j
  have h := hent (r.symm i) (c.symm j)
  simp only [relabel, Equiv.apply_symm_apply] at h
  rw [h]
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- The support of a half cycle is a cycle support (used for the "Moreover" part of
Theorem 1.1, lines 809-811). -/
theorem isCycleSupport_of_isHalfCycle {n : ℕ} {A : Square n} (h : IsHalfCycle A) :
    IsCycleSupport (support A) := by
  obtain ⟨r, c, p, hp, hent⟩ := h
  refine ⟨r, c, p, hp, fun i j => ?_⟩
  have h1 : support A (r i) (c j) ↔ relabel r c A i j ≠ 0 := Iff.rfl
  rw [h1, hent i j]
  by_cases hc : j = i ∨ j = p i
  · simp [hc]
  · simp [hc]

/-- A matrix is a half cycle exactly when its support is a cycle support and all its
nonzero entries equal `1/2` (lines 807-808: "`D` is a cycle support.  Its unique minimizing
weights are `1/2`"). -/
theorem isHalfCycle_iff_isCycleSupport {n : ℕ} {A : Square n} :
    IsHalfCycle A ↔ IsCycleSupport (support A) ∧ ∀ i j, A i j = 0 ∨ A i j = 1 / 2 := by
  constructor
  · intro h
    exact ⟨isCycleSupport_of_isHalfCycle h, half_entries_of_isHalfCycle h⟩
  · rintro ⟨⟨r, c, p, hp, hD⟩, hhalf⟩
    refine ⟨r, c, p, hp, fun i j => ?_⟩
    show A (r i) (c j) = _
    by_cases h : j = i ∨ j = p i
    · rw [if_pos h]
      exact (hhalf (r i) (c j)).resolve_left ((hD i j).2 h)
    · rw [if_neg h]
      by_contra hne
      exact h ((hD i j).1 hne)

/-- Every cycle support is the support of a half cycle: the matrix with entries `1/2` on
the support.  So on a cycle face of order at least two the value `2^(1-n)` is attained
(`permanent_eq_foreggerTarget_of_isHalfCycle`; lines 743-745). -/
theorem exists_isHalfCycle_support_eq {n : ℕ} {D : Fin n → Fin n → Prop}
    (h : IsCycleSupport D) : ∃ A : Square n, IsHalfCycle A ∧ support A = D := by
  obtain ⟨r, c, p, hp, hD⟩ := h
  refine ⟨fun x y => if c.symm y = r.symm x ∨ c.symm y = p (r.symm x) then 1 / 2 else 0,
    ⟨r, c, p, hp, fun i j => ?_⟩, ?_⟩
  · simp [relabel]
  · funext x y
    apply propext
    have h := hD (r.symm x) (c.symm y)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
    rw [h]
    show (if c.symm y = r.symm x ∨ c.symm y = p (r.symm x) then (1 / 2 : ℝ) else 0) ≠ 0 ↔ _
    by_cases hc : c.symm y = r.symm x ∨ c.symm y = p (r.symm x)
    · simp [hc]
    · simp [hc]

/-- For order at least two, a canonical half cycle is the matrix `cycleFaceMatrix p (1/2)`,
i.e. `t I_n + (1 - t) P` at `t = 1/2` (lines 743-745), for a single-cycle permutation `p`. -/
theorem isCanonicalHalfCycle_iff_cycleFaceMatrix {n : ℕ} (hn : 2 ≤ n) {A : Square n} :
    IsCanonicalHalfCycle A ↔
      ∃ p : Equiv.Perm (Fin n), IsSingleCycle p ∧ A = cycleFaceMatrix p (1 / 2) := by
  constructor
  · rintro ⟨p, hp, hA⟩
    refine ⟨p, hp, ?_⟩
    funext i j
    rw [hA i j]
    have hpfix := singleCycle_ne_apply_self hn hp i
    by_cases hji : j = i
    · subst hji
      simp [cycleFaceMatrix]
    · by_cases hjp : j = p i
      · subst hjp
        norm_num [cycleFaceMatrix, hpfix]
      · simp [cycleFaceMatrix, hji, hjp]
  · rintro ⟨p, hp, rfl⟩
    exact isCanonicalHalfCycle_cycleFaceMatrix_half hn hp

/-- **Converse of the equality statement, part 1** (Theorem 1.1, lines 39-43, "equality
if"): a half cycle of order at least two is doubly stochastic.  (False at order one, where
`IsHalfCycle A` means `A = [1/2]`.) -/
theorem doublyStochastic_of_isHalfCycle {n : ℕ} (hn : 2 ≤ n) {A : Square n}
    (h : IsHalfCycle A) : DoublyStochastic A := by
  obtain ⟨r, c, hcan⟩ := h
  obtain ⟨p, hp, hshape⟩ := (isCanonicalHalfCycle_iff_cycleFaceMatrix hn).1 hcan
  have hds : DoublyStochastic (relabel r c A) := by
    rw [hshape]
    exact doublyStochastic_cycleFaceMatrix hn hp (by norm_num) (by norm_num)
  have hback := doublyStochastic_relabel r⁻¹ c⁻¹ hds
  rwa [relabel_inv_relabel] at hback

/-- **Converse of the equality statement, part 2** (Theorem 1.1, "equality if ..."; lines
743-745): a half cycle of order `n ≥ 2` has permanent `(1/2)^n + (1/2)^n = 2^(1-n)`. -/
theorem permanent_eq_foreggerTarget_of_isHalfCycle {n : ℕ} (hn : 2 ≤ n) {A : Square n}
    (h : IsHalfCycle A) : permanent A = foreggerTarget n := by
  obtain ⟨r, c, hcan⟩ := h
  obtain ⟨p, hp, hshape⟩ := (isCanonicalHalfCycle_iff_cycleFaceMatrix hn).1 hcan
  rw [← permanent_relabel r c A, hshape]
  exact (cycleFaceMatrix_permanent_eq_iff hn hp (by norm_num) (by norm_num)).mpr rfl

/-- **Converse of the equality statement, part 3** (Theorem 1.1, lines 39-43): the support
of a half cycle of order at least two is nearly decomposable.  Together with parts 1 and 2
this shows that the equality class of Theorem 1.1 consists of ND doubly stochastic matrices
attaining `2^(1-n)`. -/
theorem nearlyDecomposable_support_of_isHalfCycle {n : ℕ} (hn : 2 ≤ n) {A : Square n}
    (h : IsHalfCycle A) : NearlyDecomposable (support A) :=
  (isCycleSupport_of_isHalfCycle h).nearlyDecomposable hn

/-- Every row of the support of a half cycle of order at least two has degree two
(auxiliary). -/
theorem rowDegreeOn_support_of_isHalfCycle {n : ℕ} (hn : 2 ≤ n) {A : Square n}
    (h : IsHalfCycle A) (i : Fin n) : rowDegreeOn (support A) i = 2 :=
  (isCycleSupport_of_isHalfCycle h).rowDegreeOn_eq_two hn i

/-- Every column of the support of a half cycle of order at least two has degree two
(auxiliary). -/
theorem columnDegreeOn_support_of_isHalfCycle {n : ℕ} (hn : 2 ≤ n) {A : Square n}
    (h : IsHalfCycle A) (j : Fin n) : columnDegreeOn (support A) j = 2 :=
  (isCycleSupport_of_isHalfCycle h).columnDegreeOn_eq_two hn j

/-- **Faithfulness of the equality class** (Theorem 1.1, lines 42-43, with `P_n` the
permutation matrix of the `n`-cycle `(1 2 ... n)`, line 37).  For `n ≥ 2`, `IsHalfCycle A`
holds exactly when independent permutations `r` of the rows and `c` of the columns turn `A`
into `(1/2)(I_n + P_n)`: the matrix with entries `1/2` at the positions `(i, i)` and
`(i, i + 1 mod n)` and `0` elsewhere.  The arbitrary single cycle in the definition of
`IsHalfCycle` can be replaced by the rotation `finRotate n` because all `n`-cycles are
conjugate. -/
theorem isHalfCycle_iff_finRotate {n : ℕ} (hn : 2 ≤ n) {A : Square n} :
    IsHalfCycle A ↔ ∃ r c : Equiv.Perm (Fin n),
      ∀ i j, A (r i) (c j) = if j = i ∨ j = finRotate n i then 1 / 2 else 0 := by
  constructor
  · rintro ⟨r, c, p, hp, hA⟩
    have hpc := (isSingleCycle_iff_isCycle hn p).1 hp
    have hsupp : p.support = Finset.univ := by
      ext i
      simp [hpc.2 i]
    have hconj : IsConj (finRotate n) p :=
      (isCycle_finRotate_of_le hn).isConj hpc.1 (by rw [support_finRotate_of_le hn, hsupp])
    obtain ⟨g, hg⟩ := isConj_iff.1 hconj
    refine ⟨r * g, c * g, fun i j => ?_⟩
    have h1 := hA (g i) (g j)
    simp only [relabel] at h1
    simp only [Equiv.Perm.mul_apply]
    rw [h1]
    have hiff : (g j = g i ∨ g j = p (g i)) ↔ (j = i ∨ j = finRotate n i) := by
      rw [← hg]
      simp [Equiv.Perm.mul_apply]
    simp only [hiff]
  · rintro ⟨r, c, hA⟩
    exact ⟨r, c, finRotate n, isSingleCycle_finRotate hn, hA⟩

/-- The entries of the matrix `(1/2)(I + P)`, where `P` is the permutation matrix of a
permutation `σ` without fixed points: `1/2` at the positions `(i, i)` and `(i, σ i)`, and
`0` elsewhere (auxiliary to `isHalfCycle_iff_submatrix_finRotate`). -/
theorem half_one_add_permutationMatrix_apply {n : ℕ} {σ : Equiv.Perm (Fin n)}
    (hσ : ∀ i, σ i ≠ i) (i j : Fin n) :
    ((1 / 2 : ℝ) • ((1 : Square n) + permutationMatrix σ)) i j =
      if j = i ∨ j = σ i then 1 / 2 else 0 := by
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, permutationMatrix,
    smul_eq_mul]
  by_cases hji : j = i
  · subst hji
    simp [(hσ j).symm]
  · by_cases hjs : j = σ i
    · subst hjs
      simp [(hσ i).symm]
    · have hij : ¬i = j := fun h => hji h.symm
      simp [hji, hjs, hij]

/-- **Faithfulness of the equality class, matrix form** (Theorem 1.1, lines 42-43).  For
`n ≥ 2`, `IsHalfCycle A` holds exactly when some submatrix `A.submatrix r c`, obtained by
independent permutations `r` of the rows and `c` of the columns, is literally the matrix
`(1/2)(I_n + P_n)`, with `P_n` the permutation matrix of the `n`-cycle `finRotate n`. -/
theorem isHalfCycle_iff_submatrix_finRotate {n : ℕ} (hn : 2 ≤ n) {A : Square n} :
    IsHalfCycle A ↔ ∃ r c : Equiv.Perm (Fin n),
      A.submatrix r c = (1 / 2 : ℝ) • ((1 : Square n) + permutationMatrix (finRotate n)) := by
  have hfix : ∀ i, finRotate n i ≠ i :=
    singleCycle_ne_apply_self hn (isSingleCycle_finRotate hn)
  rw [isHalfCycle_iff_finRotate hn]
  constructor
  · rintro ⟨r, c, h⟩
    refine ⟨r, c, ?_⟩
    ext i j
    rw [half_one_add_permutationMatrix_apply hfix]
    exact h i j
  · rintro ⟨r, c, h⟩
    refine ⟨r, c, fun i j => ?_⟩
    have hij := congrFun (congrFun h i) j
    rw [half_one_add_permutationMatrix_apply hfix] at hij
    exact hij

/-! ### Cycle faces -/

/-- Paper, lines 743-744: "on a cycle support every doubly stochastic matrix is, after
independent row and column permutations, `t I_n + (1 - t) P_n`".  Here `D` is a cycle
support of order at least two, `A` any point of its face, and `cycleFaceMatrix p t` is the
matrix `t I + (1 - t) P` of a single-cycle permutation `p`. -/
theorem exists_cycleFaceMatrix_of_inFace {n : ℕ} (hn : 2 ≤ n) {D : Fin n → Fin n → Prop}
    (hD : IsCycleSupport D) {A : Square n} (hA : InFace D A) :
    ∃ (r c p : Equiv.Perm (Fin n)) (t : ℝ),
      IsSingleCycle p ∧ 0 ≤ t ∧ t ≤ 1 ∧ relabel r c A = cycleFaceMatrix p t := by
  obtain ⟨r, c, p, hp, hiff⟩ := hD
  have hs : SupportedOnCycle p (relabel r c A) := fun i j h => (hiff i j).1 (hA.2 _ _ h)
  obtain ⟨t, ht0, ht1, ht⟩ :=
    exists_cycleFaceMatrix_of_supported hn hp (doublyStochastic_relabel r c hA.1) hs
  exact ⟨r, c, p, t, hp, ht0, ht1, ht⟩

/-- Paper, lines 744-745 ("Its permanent is `t^n + (1 - t)^n`, uniquely minimized at
`t = 1/2` for `n ≥ 2`.  This proves the theorem on all cycle faces"): on the face of a cycle
support of order `n ≥ 2` every matrix has permanent at least `2^(1-n)`, and equality forces a
half cycle.  This statement is unconditional. -/
theorem cycleFace_foregger_sharp {n : ℕ} (hn : 2 ≤ n) {D : Fin n → Fin n → Prop}
    (hD : IsCycleSupport D) {A : Square n} (hA : InFace D A) :
    foreggerTarget n ≤ permanent A ∧ (permanent A = foreggerTarget n → IsHalfCycle A) := by
  obtain ⟨r, c, p, hp, hiff⟩ := hD
  have hs : SupportedOnCycle p (relabel r c A) := fun i j h => (hiff i j).1 (hA.2 _ _ h)
  have h := cycleSupported_foregger_sharp hn hp (doublyStochastic_relabel r c hA.1) hs
  rw [permanent_relabel] at h
  exact ⟨h.1, fun heq => isHalfCycle_of_relabel r c (h.2 heq)⟩

/-! ### Matrices with entries in `{0, 1/2}` -/

/-- In a row-stochastic matrix with entries in `{0, 1/2}`, every row has exactly two nonzero
entries (auxiliary). -/
theorem rowDegreeOn_support_eq_two_of_half_entries {n : ℕ} {A : Square n}
    (hrow : RowStochastic A) (hhalf : ∀ i j, A i j = 0 ∨ A i j = 1 / 2) (i : Fin n) :
    rowDegreeOn (support A) i = 2 := by
  have hsum := sum_eq_card_mul_half_of_half_entries (s := Finset.univ)
    (t := rowNeighborsOn (support A) {i}) (f := fun j => A i j) (fun j _ => hhalf i j)
    (Finset.subset_univ _) (fun j _ => by simp [support])
  rw [hrow i] at hsum
  have hcard : ((rowNeighborsOn (support A) {i}).card : ℝ) = 2 := by linarith
  unfold rowDegreeOn
  exact_mod_cast hcard

/-- A doubly stochastic matrix with entries in `{0, 1/2}` has a 2-regular support.  This
replaces the paper's edge count ("`D` has `2n` edges ... hence every line has degree exactly
two", lines 806-807). -/
theorem two_regular_of_half_entries {n : ℕ} {A : Square n} (hA : DoublyStochastic A)
    (hhalf : ∀ i j, A i j = 0 ∨ A i j = 1 / 2) :
    (∀ i, rowDegreeOn (support A) i = 2) ∧ (∀ j, columnDegreeOn (support A) j = 2) :=
  ⟨rowDegreeOn_support_eq_two_of_half_entries hA.2.1 hhalf,
    fun j => rowDegreeOn_support_eq_two_of_half_entries (A := A.transpose) hA.2.2
      (fun i j => hhalf j i) j⟩

/-- A doubly stochastic matrix with fully indecomposable support and all entries in
`{0, 1/2}` is a half cycle (lines 806-808: "every line has degree exactly two and `D` is
connected; hence ... `D` is a cycle support.  Its unique minimizing weights are `1/2`"). -/
theorem isHalfCycle_of_half_entries {n : ℕ} {A : Square n}
    (hA : DoublyStochastic A) (hFI : FullyIndecomposable (support A))
    (hhalf : ∀ i j, A i j = 0 ∨ A i j = 1 / 2) : IsHalfCycle A := by
  obtain ⟨hrow, hcol⟩ := two_regular_of_half_entries hA hhalf
  exact isHalfCycle_iff_isCycleSupport.2 ⟨isCycleSupport_of_two_regular hFI hrow hcol, hhalf⟩

/-! ### Un-contraction -/

/-- **Un-contraction** (lines 805-806, with Lemma 2.3).  Let `A` lie in the face of a
nearly decomposable support `D` of order `m + 1 ≥ 3`, with column `c` carrying exactly the
two nonzero entries `A r c` and `A s c`.  If every entry of the contracted matrix `C(A)` is
`0` or `1/2`, then every entry of `A` is `0` or `1/2`.

By Lemma 2.3 the rows `r` and `s` have no common neighbour other than `c`, so each entry of
`A` outside column `c` is zero or an entry of `C(A)`; the entries `A r c` and `A s c` are
positive and sum to one, and each is `1` minus a multiple of `1/2`, so both are `1/2`. -/
theorem half_entries_of_contractMatrix {m : ℕ} (hm : 2 ≤ m)
    {D : Fin (m + 1) → Fin (m + 1) → Prop} (hD : NearlyDecomposable D)
    {A : Square (m + 1)} (hA : InFace D A) {r s c : Fin (m + 1)} (hrs : r ≠ s)
    (hr : A r c ≠ 0) (hs : A s c ≠ 0) (hc : ∀ i, i ≠ r → i ≠ s → A i c = 0)
    (hB : ∀ i j, contractMatrix A r s c i j = 0 ∨ contractMatrix A r s c i j = 1 / 2) :
    ∀ i j, A i j = 0 ∨ A i j = 1 / 2 := by
  obtain ⟨⟨hnn, hrow, hcol⟩, hsupp⟩ := hA
  have hrc : D r c := hsupp r c hr
  have hsc : D s c := hsupp s c hs
  -- Lemma 2.3: rows `r` and `s` have no common nonzero column other than `c`.
  have hdisj : ∀ j, j ≠ c → A r j ≠ 0 → A s j ≠ 0 → False := fun j hj h1 h2 =>
    hj (nearlyDecomposable_common_neighbor_unique (by omega) hD hrs hrc hsc
      (hsupp r j h1) (hsupp s j h2))
  obtain ⟨ir, hir⟩ := Fin.exists_succAbove_eq hrs
  -- Entries outside column `c` are entries of the contracted matrix.
  have hoff : ∀ i j, j ≠ c → A i j = 0 ∨ A i j = 1 / 2 := by
    intro i j hj
    obtain ⟨j₀, rfl⟩ := Fin.exists_succAbove_eq hj
    by_cases his : i = s
    · rw [his]
      by_cases h0 : A s (c.succAbove j₀) = 0
      · exact Or.inl h0
      · have hr0 : A r (c.succAbove j₀) = 0 := by
          by_contra h1
          exact hdisj _ hj h1 h0
        have h := hB ir j₀
        rwa [contractMatrix_merged A c hir, hr0, zero_add] at h
    · obtain ⟨i₀, rfl⟩ := Fin.exists_succAbove_eq his
      by_cases hi : s.succAbove i₀ = r
      · rw [hi]
        by_cases h0 : A r (c.succAbove j₀) = 0
        · exact Or.inl h0
        · have hs0 : A s (c.succAbove j₀) = 0 := by
            by_contra h1
            exact hdisj _ hj h0 h1
          have h := hB i₀ j₀
          rwa [contractMatrix_merged A c hi, hs0, add_zero] at h
      · have h := hB i₀ j₀
        rwa [contractMatrix_unmerged A c hi] at h
  -- A row whose entry in column `c` lies strictly between `0` and `1` has `1/2` there.
  have hkey : ∀ i, 0 < A i c → A i c < 1 → A i c = 1 / 2 := by
    intro i hpos hlt
    have hsplit : A i c + ∑ j ∈ Finset.univ.erase c, A i j = 1 := by
      rw [Finset.add_sum_erase _ _ (Finset.mem_univ c)]
      exact hrow i
    have hk := sum_eq_card_mul_half_of_half_entries (s := Finset.univ.erase c)
      (t := (Finset.univ.erase c).filter fun j => A i j ≠ 0) (f := fun j => A i j)
      (fun j hj => hoff i j (Finset.ne_of_mem_erase hj)) (Finset.filter_subset _ _)
      (fun j hj => by simp [hj])
    set k := ((Finset.univ.erase c).filter fun j => A i j ≠ 0).card
    rw [hk] at hsplit
    have h1 : (0 : ℝ) < k := by linarith
    have h2 : (k : ℝ) < 2 := by linarith
    have h1' : 0 < k := by exact_mod_cast h1
    have h2' : k < 2 := by exact_mod_cast h2
    have hk1 : (k : ℝ) = 1 := by
      have : k = 1 := by omega
      exact_mod_cast this
    rw [hk1] at hsplit
    linarith
  have hcs : A r c + A s c = 1 := by
    rw [← Fintype.sum_eq_add r s hrs (fun x hx => hc x hx.1 hx.2)]
    exact hcol c
  have hrpos : 0 < A r c := lt_of_le_of_ne (hnn r c) (Ne.symm hr)
  have hspos : 0 < A s c := lt_of_le_of_ne (hnn s c) (Ne.symm hs)
  intro i j
  by_cases hj : j = c
  · rw [hj]
    by_cases hir' : i = r
    · rw [hir']
      exact Or.inr (hkey r hrpos (by linarith))
    · by_cases his' : i = s
      · rw [his']
        exact Or.inr (hkey s hspos (by linarith))
      · exact Or.inl (hc i hir' his')
  · exact hoff i j hj

/-! ### Equality in the contraction branch -/

/-- Equality in (7.1), column form (lines 803-804): let `A` minimize the permanent on the
nearly decomposable face `Ω(D)` of order `m + 1 ≥ 3` with `per A = 2^(1-(m+1))`, and let a
degree-two column have a nearly decomposable contraction.  Given the sharp statement at
order `m`, the contracted matrix `C(A)` has permanent `2^(1-m)` and is a half cycle; hence
every entry of `A` is `0` or `1/2`. -/
theorem half_entries_of_equality_column {m : ℕ} (hm : 2 ≤ m) (hIH : ForeggerSharpAt m)
    {D : Fin (m + 1) → Fin (m + 1) → Prop} (hD : NearlyDecomposable D)
    {A : Square (m + 1)} (hA : FaceMinimizer D A) {r s c : Fin (m + 1)} (hrs : r ≠ s)
    (hrc : D r c) (hsc : D s c) (hdeg : columnDegreeOn D c = 2)
    (hND : NearlyDecomposableOn (contractColumn D r s c))
    (heq : permanent A = foreggerTarget (m + 1)) :
    ∀ i j, A i j = 0 ∨ A i j = 1 / 2 := by
  obtain ⟨hr, hs, hc⟩ := faceMinimizer_column_entries hD hA hrs hrc hsc hdeg
  obtain ⟨hDS, hNDc, hper⟩ := faceMinimizer_contraction_nd hD hA hrs hrc hsc hdeg hND
  have hBeq : permanent (contractMatrix A r s c) = foreggerTarget m := by
    rw [hper, heq, two_mul_foreggerTarget_succ (by omega)]
  exact half_entries_of_contractMatrix hm hD hA.1 hrs hr hs hc
    (half_entries_of_isHalfCycle ((hIH _ hDS hNDc).2 hBeq))

/-- Equality in (7.1), row form (lines 803-804), by transposition: the same conclusion when
a degree-two row has a nearly decomposable contraction. -/
theorem half_entries_of_equality_row {m : ℕ} (hm : 2 ≤ m) (hIH : ForeggerSharpAt m)
    {D : Fin (m + 1) → Fin (m + 1) → Prop} (hD : NearlyDecomposable D)
    {A : Square (m + 1)} (hA : FaceMinimizer D A) {r c d : Fin (m + 1)} (hcd : c ≠ d)
    (hrc : D r c) (hrd : D r d) (hdeg : rowDegreeOn D r = 2)
    (hND : NearlyDecomposableOn (contractRow D r c d))
    (heq : permanent A = foreggerTarget (m + 1)) :
    ∀ i j, A i j = 0 ∨ A i j = 1 / 2 := by
  have h := half_entries_of_equality_column hm hIH (nearlyDecomposable_transposeSupport hD)
    (faceMinimizer_transpose hA) hcd (show transposeSupport D c r from hrc)
    (show transposeSupport D d r from hrd) hdeg
    ((nearlyDecomposableOn_contractRow_iff D r c d).1 hND)
    (by rw [permanent_transpose]; exact heq)
  exact fun i j => h j i

/-- **The equality case in the contraction branch** (lines 801-808).  Let `D` be a nearly
decomposable support of order `m + 1 ≥ 3` that is not `Terminal`, and let `A` be a
permanent minimizer of `Ω(D)` with `per A = 2^(1-(m+1))`.  Given the sharp statement at
order `m`, the matrix `A` is a half cycle: `(1/2)(I + P)` up to independent row and column
permutations. -/
theorem isHalfCycle_of_not_terminal {m : ℕ} (hm : 2 ≤ m) (hIH : ForeggerSharpAt m)
    {D : Fin (m + 1) → Fin (m + 1) → Prop} (hD : NearlyDecomposable D)
    {A : Square (m + 1)} (hA : FaceMinimizer D A) (hnt : ¬Terminal D)
    (heq : permanent A = foreggerTarget (m + 1)) : IsHalfCycle A := by
  have hFI : FullyIndecomposable (support A) := by
    rw [faceMinimizer_support_eq hD hA]
    exact hD.1
  refine isHalfCycle_of_half_entries hA.1.1 hFI ?_
  rcases (exists_nd_contraction_iff_not_terminal D).2 hnt with
    ⟨r, s, c, hrs, hrc, hsc, hdeg, hND⟩ | ⟨r, c, d, hcd, hrc, hrd, hdeg, hND⟩
  · exact half_entries_of_equality_column hm hIH hD hA hrs hrc hsc hdeg hND heq
  · exact half_entries_of_equality_row hm hIH hD hA hcd hrc hrd hdeg hND heq

end LaviSection2
