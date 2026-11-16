import LaviSection2.Transpose
import LaviSection2.LaviStrictHall
import LaviSection2.LaviCycleFace
import LaviSection2.LaviFaceVariational
import Mathlib.Combinatorics.Hall.Basic

/-!
# Lavi Section 7: faces, small orders and the Foregger target

Section 7 of Lavi's preprint proves Theorem 1.1 by strong induction on the
order, simultaneously for all nearly decomposable (ND) supports.  This module
collects the elementary facts on which the induction rests.  None of them is
a numbered statement of the paper.  Where a declaration formalizes a specific
sentence, its docstring cites the lines of the preprint; the declarations
marked "auxiliary" have no counterpart sentence and are used tacitly there.

* **Small orders.**  The zero-submatrix definition `FullyIndecomposable` is
  vacuous in orders zero and one, so `NearlyDecomposable` at order one means
  that the support is *empty* (`nearlyDecomposable_one_iff`).  This differs
  from the paper's convention (lines 33-34: "in order one ... a support is FI
  exactly when it is nonempty; the singleton support is ND").  Consequently no
  doubly stochastic matrix of order one has ND support, and order one is a
  vacuous case of the induction here, whereas the paper treats it as the
  singleton with permanent `1 = 2^(1-1)` (lines 740-742).  In order two both
  FI and ND mean that the support is all of `K_{2,2}`, as in the paper.
* **Faces.**  An FI support of order at least two contains a permutation
  (Hall's theorem from the strict Hall inequalities), so its face `Ω(D)` is
  nonempty and, being compact, has a permanent minimizer.  For an ND support
  the minimizer has support exactly `D` by Lemma 2.1.  This is the sentence
  "The compact face `Ω(D)` has a permanent minimizer `A`, whose support is
  `D` by Lemma 2.1" (lines 764-765).  The bipartite graph of an FI support
  of order at least two is moreover connected (lines 86-88).
* **The whole-face bound.**  `face_bound_of_foreggerBoundAt` upgrades the
  matrix-level statement `ForeggerBoundAt n` (matrices whose support *is* ND)
  to every matrix of the closed face of every ND support of order `n`.  This
  is the second of the paper's "two ways" of using the induction hypothesis
  (lines 760-762).
* **The target.**  `foreggerTarget n = ((2:ℝ)^(n-1))⁻¹` is the paper's
  `2^(1-n)` for `n ≥ 1` (`foreggerTarget_eq_zpow`), while
  `foreggerTarget 0 = 1`; positivity, the logarithm and the doubling identity
  `2 * foreggerTarget (m+1) = foreggerTarget m` behind (7.1).
* **Base cases.**  `ForeggerSharpAt 0` (trivial), `ForeggerSharpAt 1`
  (vacuous, see above) and `ForeggerSharpAt 2` (the cycle face `K_{2,2}`,
  lines 742-745); moreover the bound holds for every doubly stochastic matrix
  of order at most two (`foreggerTarget_le_permanent_of_le_two`), which is
  the usable form of the paper's order-one case.
-/

namespace LaviSection2

/-! ### Full indecomposability and near decomposability in orders at most two -/

/-- In orders zero and one the zero-submatrix definition of full indecomposability is
vacuous: every support is `FullyIndecomposable`, the empty one included.  (The paper's
order-one convention, lines 33-34, instead calls a support FI exactly when it is nonempty.) -/
theorem fullyIndecomposable_of_le_one {n : ℕ} (hn : n ≤ 1) (S : Fin n → Fin n → Prop) :
    FullyIndecomposable S := by
  intro R C hR hC hcard
  have hRpos := Finset.card_pos.mpr hR
  have hCpos := Finset.card_pos.mpr hC
  omega

/-- The unique support of order zero is nearly decomposable (it has no edge to delete).
Auxiliary: order zero does not occur in the paper. -/
theorem nearlyDecomposable_zero (S : Fin 0 → Fin 0 → Prop) : NearlyDecomposable S :=
  ⟨fullyIndecomposable_of_le_one (Nat.zero_le 1) S, fun i => i.elim0⟩

/-- At order one, `NearlyDecomposable` means that the support is **empty**: every support is
FI there, so an edge can always be deleted without destroying full indecomposability.  This
is the opposite of the paper's convention (line 34: "the singleton support is ND"). -/
theorem nearlyDecomposable_one_iff (S : Fin 1 → Fin 1 → Prop) :
    NearlyDecomposable S ↔ ¬S 0 0 := by
  constructor
  · intro h h00
    exact h.2 0 0 h00 (fullyIndecomposable_of_le_one le_rfl _)
  · intro h
    refine ⟨fullyIndecomposable_of_le_one le_rfl S, fun i j hij => ?_⟩
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst hi
    subst hj
    exact absurd hij h

/-- In order two a support is fully indecomposable exactly when it is all of `K_{2,2}`
(auxiliary to `nearlyDecomposable_two_iff`). -/
theorem fullyIndecomposable_two_iff (S : Fin 2 → Fin 2 → Prop) :
    FullyIndecomposable S ↔ ∀ i j, S i j := by
  constructor
  · intro h i j
    obtain ⟨a, ha, b, hb, hab⟩ := h {i} {j} (Finset.singleton_nonempty i)
      (Finset.singleton_nonempty j) (by simp)
    rw [Finset.mem_singleton] at ha hb
    subst ha
    subst hb
    exact hab
  · intro h R C hR hC _
    obtain ⟨i, hi⟩ := hR
    obtain ⟨j, hj⟩ := hC
    exact ⟨i, hi, j, hj, h i j⟩

/-- In order two the only nearly decomposable support is `K_{2,2}` (paper, lines 742-743:
"In order two, the only ND support is `K_{2,2}`"). -/
theorem nearlyDecomposable_two_iff (S : Fin 2 → Fin 2 → Prop) :
    NearlyDecomposable S ↔ ∀ i j, S i j := by
  constructor
  · intro h
    exact (fullyIndecomposable_two_iff S).1 h.1
  · intro h
    refine ⟨(fullyIndecomposable_two_iff S).2 h, fun i j _ hdel => ?_⟩
    exact ((fullyIndecomposable_two_iff _).1 hdel i j).2 ⟨rfl, rfl⟩

/-- No doubly stochastic matrix of order one has nearly decomposable support: its only entry
is `1`, while the ND support of order one is empty (`nearlyDecomposable_one_iff`).  Hence
every statement about ND doubly stochastic matrices is vacuous at order one, in contrast
with the paper's order-one case (lines 740-742). -/
theorem not_nearlyDecomposable_support_one {A : Square 1} (hA : DoublyStochastic A) :
    ¬NearlyDecomposable (support A) := by
  intro h
  apply (nearlyDecomposable_one_iff _).1 h
  show A 0 0 ≠ 0
  have h1 : A 0 0 = 1 := by simpa using hA.2.1 0
  rw [h1]
  exact one_ne_zero

/-- The face `Ω(D)` of the nearly decomposable support of order one is empty: the support is
empty, while a doubly stochastic `1 × 1` matrix has the entry `1`.  (Again in contrast with
the paper's order-one convention, lines 740-742.) -/
theorem not_inFace_of_nearlyDecomposable_one {D : Fin 1 → Fin 1 → Prop}
    (hD : NearlyDecomposable D) (A : Square 1) : ¬InFace D A := by
  rintro ⟨hA, hsupp⟩
  apply (nearlyDecomposable_one_iff D).1 hD
  apply hsupp
  have h1 : A 0 0 = 1 := by simpa using hA.2.1 0
  rw [h1]
  exact one_ne_zero

/-! ### Fully indecomposable supports of order at least two: matchings and connectedness

The paper recalls (lines 86-88) that, for order at least two, a support is FI precisely when
its bipartite graph is connected and matching-covered.  Section 7 uses two consequences of
full indecomposability: the support contains a perfect matching (so that its face is
nonempty), and its graph is connected. -/

/-- Hall's theorem for supports: a fully indecomposable support of order at least two
contains a permutation (a perfect matching of the bipartite graph), by the strict Hall
inequalities (lines 88-90).  The hypothesis `2 ≤ n` cannot be dropped: at order one the
empty support is `FullyIndecomposable`. -/
theorem exists_perm_of_fullyIndecomposable {n : ℕ} (hn : 2 ≤ n) {S : Fin n → Fin n → Prop}
    (hS : FullyIndecomposable S) : ∃ σ : Equiv.Perm (Fin n), ∀ i, S i (σ i) := by
  classical
  have hH := (fullyIndecomposable_iff_strictHall S).1 hS
  let f : Fin n → Finset (Fin n) := fun i => Finset.univ.filter fun j => S i j
  have hfeq : ∀ s : Finset (Fin n), s.biUnion f = rowNeighbors S s := by
    intro s
    ext j
    simp [f]
  have hf : ∀ s : Finset (Fin n), s.card ≤ (s.biUnion f).card := by
    intro s
    rw [hfeq]
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simp
    · by_cases hlt : s.card < n
      · exact (hH s hs hlt).le
      · obtain ⟨i, hi⟩ := hs
        have hcard : (s.erase i).card = s.card - 1 := Finset.card_erase_of_mem hi
        have hsle : s.card ≤ n := by simpa using Finset.card_le_univ s
        have hne : (s.erase i).Nonempty := Finset.card_pos.1 (by omega)
        have h1 := hH (s.erase i) hne (by omega)
        have h2 := Finset.card_le_card (rowNeighbors_mono (S := S) (Finset.erase_subset i s))
        omega
  obtain ⟨g, hg, hg'⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective f).1 hf
  rw [Finite.injective_iff_bijective] at hg
  refine ⟨Equiv.ofBijective g hg, fun i => ?_⟩
  have := hg' i
  simpa [f] using this

/-- Every column of a fully indecomposable support of order at least two meets the support
(auxiliary). -/
theorem exists_row_neighbor_of_fullyIndecomposable {n : ℕ} (hn : 2 ≤ n)
    {S : Fin n → Fin n → Prop} (hS : FullyIndecomposable S) (j : Fin n) : ∃ i, S i j := by
  have hcard : (Finset.univ.erase j).card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
  obtain ⟨i, -, j', hj', hij⟩ := hS (Finset.univ.erase j) {j}
    (Finset.card_pos.1 (by omega)) (Finset.singleton_nonempty j)
    (by rw [hcard, Finset.card_singleton]; omega)
  rw [Finset.mem_singleton] at hj'
  exact ⟨i, hj' ▸ hij⟩

/-- The bipartite graph of a fully indecomposable support of order at least two is connected
(paper, lines 86-88).  If the connected component of a row missed some row, its rows `R` and
columns `C` would form a closed pair with `|C| > |R|` by strict Hall, and the rows outside
`R` together with `|R|` columns of `C` would be a zero block.  (False at order one for the
empty support, which is `FullyIndecomposable` in Lean.) -/
theorem supportGraph_connected_of_fullyIndecomposable {n : ℕ} (hn : 2 ≤ n)
    {S : Fin n → Fin n → Prop} (hS : FullyIndecomposable S) : (supportGraph S).Connected := by
  have hH := (fullyIndecomposable_iff_strictHall S).1 hS
  let i0 : Fin n := ⟨0, by omega⟩
  set κ := (supportGraph S).connectedComponentMk (Sum.inl i0)
  have hclosed := closedPair_comp S κ
  have hRne : (compRows S κ).Nonempty := ⟨i0, mem_compRows.2 rfl⟩
  -- All rows lie in the component of `i0`.
  have hRuniv : compRows S κ = Finset.univ := by
    by_contra hne
    have hlt : (compRows S κ).card < n := by
      have hle : (compRows S κ).card ≤ n := by simpa using Finset.card_le_univ (compRows S κ)
      rcases Nat.lt_or_eq_of_le hle with h | h
      · exact h
      · exact absurd (Finset.eq_univ_of_card _ (by simpa using h)) hne
    have hstrict := hH _ hRne hlt
    have hNsub : rowNeighbors S (compRows S κ) ⊆ compCols S κ := by
      intro j hj
      obtain ⟨i, hi, hij⟩ := mem_rowNeighbors.1 hj
      exact hclosed.1 i hi j hij
    have hCcard : (compRows S κ).card ≤ (compCols S κ).card :=
      hstrict.le.trans (Finset.card_le_card hNsub)
    obtain ⟨C', hC'sub, hC'card⟩ := Finset.exists_subset_card_eq hCcard
    have hC'ne : C'.Nonempty :=
      Finset.card_pos.1 (by rw [hC'card]; exact Finset.card_pos.2 hRne)
    have hRc : (compRows S κ)ᶜ.Nonempty := by
      rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin]
      omega
    obtain ⟨i, hi, j, hj, hij⟩ := hS (compRows S κ)ᶜ C' hRc hC'ne (by
      rw [Finset.card_compl, Fintype.card_fin, hC'card]
      omega)
    exact (Finset.mem_compl.1 hi) (hclosed.2 j (hC'sub hj) i hij)
  -- Every column has a row neighbour, so it lies in the same component.
  have hall : ∀ v, (supportGraph S).connectedComponentMk v = κ := by
    intro v
    cases v with
    | inl i => exact mem_compRows.1 (hRuniv ▸ Finset.mem_univ i)
    | inr j =>
      obtain ⟨i, hij⟩ := exists_row_neighbor_of_fullyIndecomposable hn hS j
      rw [← SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        (supportGraph_adj_inl_inr hij)]
      exact mem_compRows.1 (hRuniv ▸ Finset.mem_univ i)
  haveI : Nonempty (Fin n ⊕ Fin n) := ⟨Sum.inl i0⟩
  exact ⟨fun u v => SimpleGraph.ConnectedComponent.exact ((hall u).trans (hall v).symm)⟩

/-- The `0/1` permutation matrix with a one at each position `(i, σ i)`.  It is a point of
the face of every support containing the graph of `σ`; the paper's `P_n` (line 37) is the
permutation matrix of the `n`-cycle `finRotate n`. -/
def permutationMatrix {n : ℕ} (σ : Equiv.Perm (Fin n)) : Square n :=
  fun i j => if j = σ i then 1 else 0

/-- A permutation matrix is doubly stochastic (auxiliary). -/
theorem doublyStochastic_permutationMatrix {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    DoublyStochastic (permutationMatrix σ) := by
  refine ⟨fun i j => ?_, fun i => ?_, fun j => ?_⟩
  · unfold permutationMatrix
    split_ifs <;> norm_num
  · simp [permutationMatrix]
  · have h : ∀ i, (if j = σ i then (1 : ℝ) else 0) = if i = σ.symm j then 1 else 0 := by
      intro i
      have hiff : j = σ i ↔ i = σ.symm j :=
        ⟨fun h => by rw [h, Equiv.symm_apply_apply], fun h => by rw [h, Equiv.apply_symm_apply]⟩
      simp only [hiff]
    simp [permutationMatrix, h]

/-- The permutation matrix of `σ` lies in the face of every support containing the graph of
`σ` (auxiliary). -/
theorem inFace_permutationMatrix {n : ℕ} {S : Fin n → Fin n → Prop} {σ : Equiv.Perm (Fin n)}
    (hσ : ∀ i, S i (σ i)) : InFace S (permutationMatrix σ) := by
  refine ⟨doublyStochastic_permutationMatrix σ, fun i j h => ?_⟩
  unfold permutationMatrix at h
  split_ifs at h with hj
  · rw [hj]
    exact hσ i
  · exact absurd rfl h

/-! ### Faces and face minimizers -/

/-- The face `Ω(S)` of a fully indecomposable support of order at least two is nonempty: it
contains a permutation matrix.  The paper uses this tacitly when it takes a minimizer of the
compact face (lines 764-765).  (False at order one for the empty support.) -/
theorem exists_inFace_of_fullyIndecomposable {n : ℕ} (hn : 2 ≤ n) {S : Fin n → Fin n → Prop}
    (hS : FullyIndecomposable S) : ∃ X, InFace S X := by
  obtain ⟨σ, hσ⟩ := exists_perm_of_fullyIndecomposable hn hS
  exact ⟨permutationMatrix σ, inFace_permutationMatrix hσ⟩

/-- The face of a fully indecomposable support of order at least two has a permanent
minimizer, by compactness of the nonempty face (lines 764-765). -/
theorem exists_faceMinimizer_of_fullyIndecomposable {n : ℕ} (hn : 2 ≤ n)
    {S : Fin n → Fin n → Prop} (hS : FullyIndecomposable S) : ∃ A, FaceMinimizer S A :=
  exists_faceMinimizer (exists_inFace_of_fullyIndecomposable hn hS)

/-- A doubly stochastic matrix lies in the face of its own support (auxiliary). -/
theorem inFace_support {n : ℕ} {A : Square n} (hA : DoublyStochastic A) :
    InFace (support A) A :=
  ⟨hA, fun _ _ h => h⟩

/-- Faces are monotone in the support: `Ω(D) ⊆ Ω(D')` when `D ⊆ D'` (auxiliary). -/
theorem InFace.mono {n : ℕ} {D D' : Fin n → Fin n → Prop} {A : Square n} (hA : InFace D A)
    (h : ∀ i j, D i j → D' i j) : InFace D' A :=
  ⟨hA.1, fun i j hij => h i j (hA.2 i j hij)⟩

/-- Transposition maps the face `Ω(D)` into the face of the transposed support
(auxiliary). -/
theorem inFace_transpose {n : ℕ} {D : Fin n → Fin n → Prop} {A : Square n}
    (hA : InFace D A) : InFace (transposeSupport D) A.transpose :=
  ⟨doublyStochastic_transpose hA.1, fun i j h => hA.2 j i h⟩

/-- The transpose of a face minimizer of `Ω(D)` is a face minimizer of the face of the
transposed support.  This is how the row case of every column statement is obtained (the
paper, line 115: "A degree-two row has the transposed contraction"). -/
theorem faceMinimizer_transpose {n : ℕ} {D : Fin n → Fin n → Prop} {A : Square n}
    (hA : FaceMinimizer D A) : FaceMinimizer (transposeSupport D) A.transpose := by
  refine ⟨inFace_transpose hA.1, fun B hB => ?_⟩
  have hB' : InFace D B.transpose := inFace_transpose hB
  have h := hA.2 B.transpose hB'
  rwa [permanent_transpose, ← permanent_transpose A] at h

/-- Lemma 2.1, final sentence (line 106), as an equality of relations and in every order: a
face minimizer of a nearly decomposable face has support exactly `D`. -/
theorem faceMinimizer_support_eq {n : ℕ} {D : Fin n → Fin n → Prop}
    (hD : NearlyDecomposable D) {A : Square n} (hA : FaceMinimizer D A) : support A = D := by
  rcases n with _ | m
  · exact funext fun i => i.elim0
  · exact funext fun i => funext fun j =>
      propext (faceMinimizer_support_eq_of_nearlyDecomposable hD hA i j)

/-- Paper, lines 764-765: "The compact face `Ω(D)` has a permanent minimizer `A`, whose
support is `D` by Lemma 2.1."  Stated for an ND support of order at least two; at order one
the Lean ND support is empty and its face is empty
(`not_inFace_of_nearlyDecomposable_one`). -/
theorem exists_faceMinimizer_support_eq {n : ℕ} (hn : 2 ≤ n) {D : Fin n → Fin n → Prop}
    (hD : NearlyDecomposable D) : ∃ A, FaceMinimizer D A ∧ support A = D := by
  obtain ⟨A, hA⟩ := exists_faceMinimizer_of_fullyIndecomposable hn hD.1
  exact ⟨A, hA, faceMinimizer_support_eq hD hA⟩

/-! ### Arithmetic of the Foregger target -/

/-- The Foregger target is positive (auxiliary). -/
theorem foreggerTarget_pos (n : ℕ) : 0 < foreggerTarget n := by
  unfold foreggerTarget
  positivity

/-- `foreggerTarget 0 = 1` (auxiliary; natural subtraction: the exponent `0 - 1` is `0`). -/
theorem foreggerTarget_zero : foreggerTarget 0 = 1 := by
  simp [foreggerTarget]

/-- `foreggerTarget 1 = 1 = 2^(1-1)` (the value of line 742). -/
theorem foreggerTarget_one : foreggerTarget 1 = 1 := by
  simp [foreggerTarget]

/-- `foreggerTarget 2 = 1/2 = 2^(1-2)` (auxiliary). -/
theorem foreggerTarget_two : foreggerTarget 2 = 1 / 2 := by
  norm_num [foreggerTarget]

/-- The repository's target, written with a natural-number exponent, is the paper's
`2^(1-n)` (Theorem 1.1, line 41) for every order `n ≥ 1`.  At `n = 0` the two differ
(`foreggerTarget 0 = 1`, while `2^(1-0) = 2`); order zero is outside the theorem. -/
theorem foreggerTarget_eq_zpow {n : ℕ} (hn : 1 ≤ n) :
    foreggerTarget n = (2 : ℝ) ^ ((1 : ℤ) - (n : ℤ)) := by
  have hexp : (1 : ℤ) - (n : ℤ) = -((n - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub hn]
    push_cast
    ring
  rw [foreggerTarget, hexp, zpow_neg, zpow_natCast]

/-- The doubling identity behind (7.1) (line 769): `2 * 2^(1-(m+1)) = 2^(1-m)` for `m ≥ 1`.
It turns `per C(A) = 2 per A` into an exact transport of the target between consecutive
orders. -/
theorem two_mul_foreggerTarget_succ {m : ℕ} (hm : 1 ≤ m) :
    2 * foreggerTarget (m + 1) = foreggerTarget m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp only [foreggerTarget, Nat.add_sub_cancel]
  rw [pow_succ]
  have hk : (2 : ℝ) ^ k ≠ 0 := by positivity
  field_simp

/-- The logarithm of the target: `log 2^(1-n) = -(n - 1) log 2` for `n ≥ 1` (auxiliary). -/
theorem log_foreggerTarget {n : ℕ} (hn : 1 ≤ n) :
    Real.log (foreggerTarget n) = -(((n : ℝ) - 1) * Real.log 2) := by
  unfold foreggerTarget
  rw [Real.log_inv, Real.log_pow, Nat.cast_sub hn, Nat.cast_one]

/-- The strict Foregger inequality in logarithmic form: `2^(1-n) < p` exactly when
`log p + (n - 1) log 2 > 0`.  This is the last step of the paper's terminal branch (lines
799-800): by (3.3) and (3.7) a positive normalized gap `G = F + (n - 1) log 2` gives
`log per + (n - 1) log 2 > 0`. -/
theorem foreggerTarget_lt_iff_log {n : ℕ} (hn : 1 ≤ n) {p : ℝ} (hp : 0 < p) :
    foreggerTarget n < p ↔ 0 < Real.log p + ((n : ℝ) - 1) * Real.log 2 := by
  rw [← Real.log_lt_log_iff (foreggerTarget_pos n) hp, log_foreggerTarget hn]
  constructor <;> intro h <;> linarith

/-- The Foregger inequality in logarithmic form: `2^(1-n) ≤ p` exactly when
`log p + (n - 1) log 2 ≥ 0` (the non-strict companion of `foreggerTarget_lt_iff_log`). -/
theorem foreggerTarget_le_iff_log {n : ℕ} (hn : 1 ≤ n) {p : ℝ} (hp : 0 < p) :
    foreggerTarget n ≤ p ↔ 0 ≤ Real.log p + ((n : ℝ) - 1) * Real.log 2 := by
  rw [← Real.log_le_log_iff (foreggerTarget_pos n) hp, log_foreggerTarget hn]
  constructor <;> intro h <;> linarith

/-! ### From the matrix-level statement to the whole face -/

/-- The sharp statement at order `n` contains the bound at order `n` (auxiliary). -/
theorem ForeggerSharpAt.foreggerBoundAt {n : ℕ} (h : ForeggerSharpAt n) : ForeggerBoundAt n :=
  fun A hA hND => (h A hA hND).1

/-- Paper, lines 761-762 ("Lemma 2.1 places the minimum of `Ω(R)` at full support, so the
inductive bound holds on the whole face"): the matrix-level bound `ForeggerBoundAt n`, which
only speaks about matrices whose support *is* nearly decomposable, gives the bound at every
point of the closed face `Ω(D)` of every nearly decomposable support `D` of order `n`,
including boundary points whose support is a proper subset of `D`.

At order one the statement is vacuous, because the face of the Lean ND support of order one
is empty; for an arbitrary doubly stochastic matrix of order at most two use
`foreggerTarget_le_permanent_of_le_two`. -/
theorem face_bound_of_foreggerBoundAt {n : ℕ} (h : ForeggerBoundAt n)
    {D : Fin n → Fin n → Prop} (hD : NearlyDecomposable D) {A : Square n} (hA : InFace D A) :
    foreggerTarget n ≤ permanent A := by
  obtain ⟨Y, hY⟩ := exists_faceMinimizer ⟨A, hA⟩
  have hs : support Y = D := faceMinimizer_support_eq hD hY
  exact (h Y hY.1.1 (hs ▸ hD)).trans (hY.2 A hA)

/-- Paper, lines 801-802 ("The lower bound just proved on `Ω(D)` makes `A` a face
minimizer"): given the bound at order `n`, a point of a nearly decomposable face whose
permanent equals the Foregger target minimizes the permanent on that face; by Lemma 2.1 its
support is then exactly `D`. -/
theorem faceMinimizer_of_eq_foreggerTarget {n : ℕ} (h : ForeggerBoundAt n)
    {D : Fin n → Fin n → Prop} (hD : NearlyDecomposable D) {A : Square n} (hA : InFace D A)
    (heq : permanent A = foreggerTarget n) : FaceMinimizer D A ∧ support A = D := by
  have hmin : FaceMinimizer D A :=
    ⟨hA, fun B hB => heq ▸ face_bound_of_foreggerBoundAt h hD hB⟩
  exact ⟨hmin, faceMinimizer_support_eq hD hmin⟩

/-! ### Base cases of the induction -/

/-- The transposition of `Fin 2` is a single cycle (auxiliary to the order-two case). -/
theorem isSingleCycle_swap_fin_two : IsSingleCycle (Equiv.swap (0 : Fin 2) 1) := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact ⟨0, rfl⟩
  · exact ⟨1, by simp⟩
  · exact ⟨1, by simp⟩
  · exact ⟨0, rfl⟩

/-- Every `2 × 2` matrix is supported on the diagonal-plus-cycle graph of the transposition:
that graph is all of `K_{2,2}`, "a cycle support" (lines 742-743). -/
theorem supportedOnCycle_swap_fin_two (A : Square 2) :
    SupportedOnCycle (Equiv.swap (0 : Fin 2) 1) A := by
  intro i j _
  fin_cases i <;> fin_cases j <;> simp

/-- Order two, paper lines 742-745: every doubly stochastic `2 × 2` matrix is
`t I + (1 - t) P` with permanent `t^2 + (1 - t)^2 ≥ 1/2`, and equality forces the all-`1/2`
matrix.  No hypothesis on the support is needed. -/
theorem foregger_sharp_order_two {A : Square 2} (hA : DoublyStochastic A) :
    foreggerTarget 2 ≤ permanent A ∧ (permanent A = foreggerTarget 2 → IsHalfCycle A) :=
  cycleSupported_foregger_sharp (le_refl 2) isSingleCycle_swap_fin_two hA
    (supportedOnCycle_swap_fin_two A)

/-- Order zero: the empty matrix has permanent `1 = foreggerTarget 0`, and `IsHalfCycle`
holds vacuously for it.  (Order zero is outside Theorem 1.1 and the paper; it only serves
as a harmless start of the strong induction.) -/
theorem foreggerSharpAt_zero : ForeggerSharpAt 0 := by
  intro A _ _
  refine ⟨?_, fun _ => ⟨1, 1, 1, fun i => i.elim0, fun i => i.elim0⟩⟩
  simp [foreggerTarget, permanent]

/-- Order one is **vacuous** in this formalization: no doubly stochastic `1 × 1` matrix has
`NearlyDecomposable` support (`not_nearlyDecomposable_support_one`).  The paper (lines
740-742) instead includes order one in its induction, with the singleton support and
permanent `1 = 2^(1-1)`.  Theorem 1.1 itself starts at `n = 2`; where the bound for a matrix
of order one is needed, `foreggerTarget_le_permanent_of_le_two` gives it without any
hypothesis on the support. -/
theorem foreggerSharpAt_one : ForeggerSharpAt 1 :=
  fun _ hA hND => absurd hND (not_nearlyDecomposable_support_one hA)

/-- Order two (paper, lines 742-745): the bound and the equality classification on the cycle
face `K_{2,2}`. -/
theorem foreggerSharpAt_two : ForeggerSharpAt 2 :=
  fun _ hA _ => foregger_sharp_order_two hA

/-- In orders at most two the Foregger bound holds for **every** doubly stochastic matrix,
with no hypothesis on its support: the permanent is `1` in orders zero and one (the paper's
order-one case, lines 740-742), and `t^2 + (1 - t)^2 ≥ 1/2` in order two (lines 742-745). -/
theorem foreggerTarget_le_permanent_of_le_two {n : ℕ} (hn : n ≤ 2) {A : Square n}
    (hA : DoublyStochastic A) : foreggerTarget n ≤ permanent A := by
  interval_cases n
  · simp [foreggerTarget, permanent]
  · have h1 : A 0 0 = 1 := by simpa using hA.2.1 0
    simp [foreggerTarget, permanent, h1]
  · exact (foregger_sharp_order_two hA).1

end LaviSection2
