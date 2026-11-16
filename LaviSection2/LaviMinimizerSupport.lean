import LaviSection2.LaviCofactorEqualization
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Lavi Lemma 2.1: the support of a face minimizer

This module proves the support half of Lavi's Lemma 2.1 (Foregger's Lemma 1):
if `D` is fully indecomposable and `A` minimizes the permanent on the face
`Ω(D)`, then the support of `A` is fully indecomposable.  Consequently, when
`D` is nearly decomposable, every face minimizer has support exactly `D`.

Proof outline.  Suppose the support `S` of `A` is not fully indecomposable.
A zero block of `A` and double stochasticity split `S` into two closed
pieces.  Every connected component `K` of the bipartite graph of `S` is a
closed pair of rows and columns of equal size.  Because `D` is fully
indecomposable, each component has a `D`-edge leaving it; following these
edges defines a self-map of the finite set of components with no fixed
points, so it has a nonempty set of periodic components on which it is a
bijection.  Around that cycle we build a direction `X`: the leaving edges
with coefficient `+1`, and inside each component a flow along support edges
carrying one unit back from the next leaving row to the arriving column.
Cofactors vanish on the leaving edges (a pigeonhole count on the closed
pair) and equal `per A` on support edges (`faceMinimizer_cofactor_eq`), so
the derivative of `t ↦ per (A + tX)` at `0` is `-(cycle length) · per A < 0`.
Since `X ≥ 0` off the support, `A + tX` stays in `Ω(D)` for small `t > 0`,
contradicting minimality.  Positivity of `per A` comes from Hall's theorem.
-/

namespace LaviSection2

open Matrix Equiv Finset Filter Topology
open scoped BigOperators

variable {n : ℕ}

section Positivity

/-- Hall's theorem: a doubly stochastic matrix has a permutation in its support. -/
theorem exists_perm_support_of_doublyStochastic {A : Square n}
    (hA : DoublyStochastic A) : ∃ σ : Perm (Fin n), ∀ i, A i (σ i) ≠ 0 := by
  classical
  obtain ⟨hnn, hrow, hcol⟩ := hA
  let f : Fin n → Finset (Fin n) := fun i => univ.filter fun j => A i j ≠ 0
  have hf : ∀ s : Finset (Fin n), s.card ≤ (s.biUnion f).card := by
    intro s
    set T := s.biUnion f
    have hrowf : ∀ i, ∑ j ∈ f i, A i j = 1 := by
      intro i
      rw [← hrow i]
      refine Finset.sum_subset (Finset.filter_subset _ _) fun j _ hj => ?_
      simpa [f] using hj
    have h1 : ∑ i ∈ s, ∑ j ∈ f i, A i j = s.card := by
      rw [Finset.sum_congr rfl fun i _ => hrowf i]
      simp
    have h2 : ∑ i, ∑ j ∈ T, A i j = T.card := by
      rw [Finset.sum_comm (f := fun i j => A i j), Finset.sum_congr rfl fun j _ => hcol j]
      simp
    have hle : (s.card : ℝ) ≤ T.card := by
      rw [← h1, ← h2]
      calc ∑ i ∈ s, ∑ j ∈ f i, A i j
          ≤ ∑ i ∈ s, ∑ j ∈ T, A i j :=
            Finset.sum_le_sum fun i hi =>
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_biUnion_of_mem f hi)
                fun j _ _ => hnn i j
        _ ≤ ∑ i, ∑ j ∈ T, A i j :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              fun i _ _ => Finset.sum_nonneg fun j _ => hnn i j
    exact_mod_cast hle
  obtain ⟨g, hg, hg'⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective f).1 hf
  rw [Finite.injective_iff_bijective] at hg
  refine ⟨Equiv.ofBijective g hg, fun i => ?_⟩
  have := hg' i
  simpa [f] using this

/-- The permanent of a doubly stochastic matrix is positive. -/
theorem permanent_pos_of_doublyStochastic {A : Square n} (hA : DoublyStochastic A) :
    0 < permanent A := by
  obtain ⟨σ, hσ⟩ := exists_perm_support_of_doublyStochastic hA
  have hterm : 0 < ∏ i, A i (σ i) :=
    Finset.prod_pos fun i _ => lt_of_le_of_ne (hA.1 i (σ i)) (Ne.symm (hσ i))
  refine lt_of_lt_of_le hterm ?_
  exact Finset.single_le_sum (f := fun τ : Perm (Fin n) => ∏ i, A i (τ i))
    (fun τ _ => Finset.prod_nonneg fun i _ => hA.1 i (τ i)) (Finset.mem_univ σ)

end Positivity

section ClosedPairs

/-- A row set and column set closed under the support relation. -/
def ClosedPair (S : Fin n → Fin n → Prop) (R C : Finset (Fin n)) : Prop :=
  (∀ i ∈ R, ∀ j, S i j → j ∈ C) ∧ (∀ j ∈ C, ∀ i, S i j → i ∈ R)

/-- A matrix whose nonzero entries lie in `S`. -/
def SupportedIn (S : Fin n → Fin n → Prop) (Z : Square n) : Prop :=
  ∀ i j, Z i j ≠ 0 → S i j

/-- Flow conservation across a closed pair. -/
theorem closedPair_conservation {S : Fin n → Fin n → Prop} {R C : Finset (Fin n)}
    (hRC : ClosedPair S R C) {Z : Square n} (hZ : SupportedIn S Z) :
    ∑ i ∈ R, ∑ j, Z i j = ∑ j ∈ C, ∑ i, Z i j := by
  classical
  have hL : ∑ i ∈ R, ∑ j, Z i j = ∑ i ∈ R, ∑ j ∈ C, Z i j := by
    refine Finset.sum_congr rfl fun i hi => ?_
    refine (Finset.sum_subset (Finset.subset_univ C) fun j _ hj => ?_).symm
    by_contra h
    exact hj (hRC.1 i hi j (hZ i j h))
  have hR : ∑ j ∈ C, ∑ i, Z i j = ∑ j ∈ C, ∑ i ∈ R, Z i j := by
    refine Finset.sum_congr rfl fun j hj => ?_
    refine (Finset.sum_subset (Finset.subset_univ R) fun i _ hi => ?_).symm
    by_contra h
    exact hi (hRC.2 j hj i (hZ i j h))
  rw [hL, hR, Finset.sum_comm]

/-- A closed pair in the support of a doubly stochastic matrix is balanced. -/
theorem card_eq_of_closedPair {A : Square n} (hA : DoublyStochastic A)
    {R C : Finset (Fin n)} (hRC : ClosedPair (support A) R C) : R.card = C.card := by
  have h := closedPair_conservation hRC (Z := A) (fun i j h => h)
  rw [Finset.sum_congr rfl fun i _ => hA.2.1 i,
    Finset.sum_congr rfl fun j _ => hA.2.2 j] at h
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  exact_mod_cast h

/--
Cofactors vanish across a closed pair: if the rows `R` reach only columns in
`C`, `|C| ≤ |R|`, `i ∉ R` and `j ∈ C`, then `per A(i|j) = 0`.
-/
theorem cofactor_eq_zero_of_closedPair {m : ℕ} {A : Square (m + 1)}
    {R C : Finset (Fin (m + 1))} (hRC : ClosedPair (support A) R C)
    (hcard : C.card ≤ R.card) {i j : Fin (m + 1)} (hi : i ∉ R) (hj : j ∈ C) :
    cofactor A i j = 0 := by
  classical
  rw [cofactor_eq_sum_filter]
  refine Finset.sum_eq_zero fun σ hσ => ?_
  have hσi : σ i = j := (Finset.mem_filter.1 hσ).2
  by_contra hne0
  have hne := Finset.prod_ne_zero_iff.1 hne0
  have hmaps : ∀ k ∈ R, σ k ∈ C.erase j := by
    intro k hk
    have hki : k ≠ i := fun h => hi (h ▸ hk)
    refine Finset.mem_erase.2 ⟨fun h => hki (σ.injective (h.trans hσi.symm)), ?_⟩
    exact hRC.1 k hk (σ k) (hne k (Finset.mem_erase.2 ⟨hki, Finset.mem_univ k⟩))
  have hle := Finset.card_le_card_of_injOn σ hmaps (σ.injective.injOn)
  rw [Finset.card_erase_of_mem hj] at hle
  have hCpos : 0 < C.card := Finset.card_pos.2 ⟨j, hj⟩
  omega

end ClosedPairs

section Graph

/-- The bipartite graph of a support relation: rows `inl i`, columns `inr j`. -/
def supportGraph (S : Fin n → Fin n → Prop) : SimpleGraph (Fin n ⊕ Fin n) :=
  SimpleGraph.fromRel fun u v => ∃ i j, u = Sum.inl i ∧ v = Sum.inr j ∧ S i j

theorem supportGraph_adj_inl_inr {S : Fin n → Fin n → Prop} {i j : Fin n}
    (h : S i j) : (supportGraph S).Adj (Sum.inl i) (Sum.inr j) := by
  rw [supportGraph, SimpleGraph.fromRel_adj]
  exact ⟨Sum.inl_ne_inr, Or.inl ⟨i, j, rfl, rfl, h⟩⟩

theorem supportGraph_adj_cases {S : Fin n → Fin n → Prop} {u v : Fin n ⊕ Fin n}
    (h : (supportGraph S).Adj u v) :
    (∃ i j, u = Sum.inl i ∧ v = Sum.inr j ∧ S i j) ∨
      (∃ i j, u = Sum.inr j ∧ v = Sum.inl i ∧ S i j) := by
  rw [supportGraph, SimpleGraph.fromRel_adj] at h
  rcases h.2 with ⟨i, j, hu, hv, hs⟩ | ⟨i, j, hv, hu, hs⟩
  · exact Or.inl ⟨i, j, hu, hv, hs⟩
  · exact Or.inr ⟨i, j, hu, hv, hs⟩

/-- Signed boundary: row sums at rows, minus column sums at columns. -/
def boundary (Z : Square n) : Fin n ⊕ Fin n → ℝ
  | Sum.inl i => ∑ j, Z i j
  | Sum.inr j => -∑ i, Z i j

/-- The matrix unit at `(i, j)`. -/
def unitAt (i j : Fin n) : Square n := fun a b => if a = i ∧ b = j then 1 else 0

/-- The indicator of one vertex. -/
def vertexIndicator (u : Fin n ⊕ Fin n) : Fin n ⊕ Fin n → ℝ :=
  fun x => if x = u then 1 else 0

theorem unitAt_row_sum (i j a : Fin n) : ∑ b, unitAt i j a b = if a = i then 1 else 0 := by
  by_cases ha : a = i
  · subst ha
    simp [unitAt]
  · simp [unitAt, ha]

theorem unitAt_col_sum (i j b : Fin n) : ∑ a, unitAt i j a b = if b = j then 1 else 0 := by
  by_cases hb : b = j
  · subst hb
    simp [unitAt]
  · simp [unitAt, hb]

theorem unitAt_pair_sum (i j : Fin n) (F : Fin n → Fin n → ℝ) :
    ∑ a, ∑ b, unitAt i j a b * F a b = F i j := by
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp [unitAt]
    · intro b _ hb
      simp [unitAt, hb]
    · intro h
      exact absurd (Finset.mem_univ j) h
  · intro a _ ha
    refine Finset.sum_eq_zero fun b _ => ?_
    simp [unitAt, ha]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem boundary_add (Z W : Square n) : boundary (Z + W) = boundary Z + boundary W := by
  funext x
  cases x with
  | inl i => simp [boundary, Finset.sum_add_distrib]
  | inr j => simp [boundary, Finset.sum_add_distrib]; ring

theorem boundary_neg (Z : Square n) : boundary (-Z) = -boundary Z := by
  funext x
  cases x with
  | inl i => simp [boundary]
  | inr j => simp [boundary]

theorem boundary_zero : boundary (0 : Square n) = 0 := by
  funext x
  cases x with
  | inl i => simp [boundary]
  | inr j => simp [boundary]

theorem boundary_unitAt (i j : Fin n) :
    boundary (unitAt i j) = vertexIndicator (Sum.inl i) - vertexIndicator (Sum.inr j) := by
  funext x
  cases x with
  | inl a => simp [boundary, unitAt_row_sum, vertexIndicator]
  | inr b => simp [boundary, unitAt_col_sum, vertexIndicator]

/-- A walk in the support graph carries a unit flow from its start to its end. -/
theorem exists_flow_of_reachable {S : Fin n → Fin n → Prop} {u v : Fin n ⊕ Fin n}
    (h : (supportGraph S).Reachable u v) :
    ∃ Z : Square n, SupportedIn S Z ∧
      boundary Z = vertexIndicator u - vertexIndicator v := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact ⟨0, fun i j h => absurd rfl h, by rw [boundary_zero, sub_self]⟩
  | cons hadj p ih =>
    obtain ⟨Z, hZ, hb⟩ := ih
    rcases supportGraph_adj_cases hadj with ⟨i, j, rfl, rfl, hs⟩ | ⟨i, j, rfl, rfl, hs⟩
    · refine ⟨unitAt i j + Z, ?_, ?_⟩
      · intro a b hab
        by_cases hE : a = i ∧ b = j
        · obtain ⟨rfl, rfl⟩ := hE
          exact hs
        · apply hZ a b
          simpa [unitAt, hE] using hab
      · rw [boundary_add, boundary_unitAt, hb]
        abel
    · refine ⟨-unitAt i j + Z, ?_, ?_⟩
      · intro a b hab
        by_cases hE : a = i ∧ b = j
        · obtain ⟨rfl, rfl⟩ := hE
          exact hs
        · apply hZ a b
          simpa [unitAt, hE] using hab
      · rw [boundary_add, boundary_neg, boundary_unitAt, hb]
        abel

/-- A row and a column in one component are joined by a unit transfer matrix. -/
theorem exists_transfer {S : Fin n → Fin n → Prop} {p q : Fin n}
    (h : (supportGraph S).Reachable (Sum.inl p) (Sum.inr q)) :
    ∃ Z : Square n, SupportedIn S Z ∧
      (∀ a, ∑ b, Z a b = if a = p then 1 else 0) ∧
      (∀ b, ∑ a, Z a b = if b = q then 1 else 0) := by
  obtain ⟨Z, hZ, hb⟩ := exists_flow_of_reachable h
  refine ⟨Z, hZ, fun a => ?_, fun b => ?_⟩
  · have := congrFun hb (Sum.inl a)
    simpa [boundary, vertexIndicator] using this
  · have := congrFun hb (Sum.inr b)
    simp only [boundary, vertexIndicator, Pi.sub_apply, reduceCtorEq, ite_false,
      Sum.inr.injEq, zero_sub, neg_inj] at this
    exact this

/-- Rows of a connected component. -/
noncomputable def compRows (S : Fin n → Fin n → Prop)
    (κ : (supportGraph S).ConnectedComponent) : Finset (Fin n) := by
  classical
  exact univ.filter fun i => (supportGraph S).connectedComponentMk (Sum.inl i) = κ

/-- Columns of a connected component. -/
noncomputable def compCols (S : Fin n → Fin n → Prop)
    (κ : (supportGraph S).ConnectedComponent) : Finset (Fin n) := by
  classical
  exact univ.filter fun j => (supportGraph S).connectedComponentMk (Sum.inr j) = κ

theorem mem_compRows {S : Fin n → Fin n → Prop} {κ} {i : Fin n} :
    i ∈ compRows S κ ↔ (supportGraph S).connectedComponentMk (Sum.inl i) = κ := by
  classical
  simp [compRows]

theorem mem_compCols {S : Fin n → Fin n → Prop} {κ} {j : Fin n} :
    j ∈ compCols S κ ↔ (supportGraph S).connectedComponentMk (Sum.inr j) = κ := by
  classical
  simp [compCols]

/-- Every connected component is a closed pair. -/
theorem closedPair_comp (S : Fin n → Fin n → Prop)
    (κ : (supportGraph S).ConnectedComponent) :
    ClosedPair S (compRows S κ) (compCols S κ) := by
  constructor
  · intro i hi j hs
    rw [mem_compCols, ← SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      (supportGraph_adj_inl_inr hs)]
    exact mem_compRows.1 hi
  · intro j hj i hs
    rw [mem_compRows, SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      (supportGraph_adj_inl_inr hs)]
    exact mem_compCols.1 hj

end Graph

section Support

/-- Full indecomposability is monotone in the support. -/
theorem FullyIndecomposable.mono {S T : Fin n → Fin n → Prop}
    (hS : FullyIndecomposable S) (h : ∀ i j, S i j → T i j) : FullyIndecomposable T := by
  intro R C hR hC hc
  obtain ⟨i, hi, j, hj, hs⟩ := hS R C hR hC hc
  exact ⟨i, hi, j, hj, h i j hs⟩

/--
Lavi Lemma 2.1, support half.  If `D` is fully indecomposable and `A`
minimizes the permanent on `Ω(D)`, then the support of `A` is fully
indecomposable.
-/
theorem faceMinimizer_support_fullyIndecomposable {m : ℕ}
    {D : Fin (m + 1) → Fin (m + 1) → Prop} (hD : FullyIndecomposable D)
    {A : Square (m + 1)} (hA : FaceMinimizer D A) :
    FullyIndecomposable (support A) := by
  classical
  have hDS := hA.1.1
  have hsupp := hA.1.2
  have hmin := hA.2
  obtain ⟨hnn, hrow, hcol⟩ := hDS
  by_contra hnot
  unfold FullyIndecomposable at hnot
  push Not at hnot
  obtain ⟨R, C, hRne, hCne, hcard, hRC⟩ := hnot
  have hzero : ∀ i ∈ R, ∀ j ∈ C, A i j = 0 := fun i hi j hj => by
    have := hRC i hi j hj
    simpa [support] using this
  set S := support A with hSdef
  set G := supportGraph S with hGdef
  -- Double stochasticity forces the complementary block to vanish too.
  have hcardC : Cᶜ.card = R.card := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  have hzero2 : ∀ i ∉ R, ∀ j ∉ C, A i j = 0 := by
    have hmR : ∑ i ∈ R, ∑ j ∈ Cᶜ, A i j = R.card := by
      have : ∀ i ∈ R, ∑ j ∈ Cᶜ, A i j = 1 := by
        intro i hi
        rw [← hrow i]
        refine Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_
        exact hzero i hi j (by simpa using hj)
      rw [Finset.sum_congr rfl this]
      simp
    have hmC : ∑ j ∈ Cᶜ, ∑ i, A i j = R.card := by
      rw [Finset.sum_congr rfl fun j _ => hcol j]
      simp [hcardC]
    have hsplit : ∑ j ∈ Cᶜ, ∑ i, A i j =
        ∑ i ∈ R, ∑ j ∈ Cᶜ, A i j + ∑ j ∈ Cᶜ, ∑ i ∈ Rᶜ, A i j := by
      rw [Finset.sum_comm (s := R) (f := fun i j => A i j)]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact (Finset.sum_add_sum_compl R fun i => A i j).symm
    have hrest : ∑ j ∈ Cᶜ, ∑ i ∈ Rᶜ, A i j = 0 := by
      rw [hmC, hmR] at hsplit
      linarith
    intro i hi j hj
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
      Finset.sum_nonneg fun i _ => hnn i j).1 hrest j (Finset.mem_compl.2 hj)
    exact (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hnn i j).1 h1 i
      (Finset.mem_compl.2 hi)
  have hRCc : ClosedPair S R Cᶜ := by
    constructor
    · intro i hi j hs
      rw [Finset.mem_compl]
      intro hj
      exact hs (hzero i hi j hj)
    · intro j hj i hs
      by_contra hi
      exact hs (hzero2 i hi j (Finset.mem_compl.1 hj))
  -- Every line meets the support.
  have hrowEdge : ∀ i, ∃ j, A i j ≠ 0 := by
    intro i
    by_contra h
    push Not at h
    have := hrow i
    simp [h] at this
  have hcolEdge : ∀ j, ∃ i, A i j ≠ 0 := by
    intro j
    by_contra h
    push Not at h
    have := hcol j
    simp [h] at this
  have hclosed := closedPair_comp S
  have hbal : ∀ κ, (compRows S κ).card = (compCols S κ).card := fun κ =>
    card_eq_of_closedPair ⟨hnn, hrow, hcol⟩ (hclosed κ)
  have hrowsne : ∀ κ, (compRows S κ).Nonempty := by
    intro κ
    induction κ using SimpleGraph.ConnectedComponent.ind with
    | h v =>
      cases v with
      | inl i => exact ⟨i, mem_compRows.2 rfl⟩
      | inr j =>
        obtain ⟨i, hi⟩ := hcolEdge j
        exact ⟨i, mem_compRows.2
          (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
            (supportGraph_adj_inl_inr hi))⟩
  have hcolsne : ∀ κ, (compCols S κ)ᶜ.Nonempty := by
    intro κ
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty, Finset.compl_eq_empty_iff] at hempty
    obtain ⟨r, hr⟩ := hRne
    obtain ⟨c, hc⟩ := hCne
    obtain ⟨j, hj⟩ := hrowEdge r
    have hjκ : j ∈ compCols S κ := hempty ▸ Finset.mem_univ j
    have hcκ : c ∈ compCols S κ := hempty ▸ Finset.mem_univ c
    have hrκ : G.connectedComponentMk (Sum.inl r) = κ :=
      (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        (supportGraph_adj_inl_inr hj)).trans (mem_compCols.1 hjκ)
    have hreach : G.Reachable (Sum.inl r) (Sum.inr c) :=
      SimpleGraph.ConnectedComponent.exact (hrκ.trans (mem_compCols.1 hcκ).symm)
    obtain ⟨Z, hZ, hZrow, hZcol⟩ := exists_transfer hreach
    have hcons := closedPair_conservation hRCc hZ
    simp only [hZrow, hZcol, Finset.sum_ite_eq', hr, ite_true, Finset.mem_compl, hc,
      not_true_eq_false, ite_false] at hcons
    norm_num at hcons
  -- Each component has a `D`-edge leaving it.
  have hout : ∀ κ : G.ConnectedComponent, ∃ a b, a ∈ compRows S κ ∧
      b ∉ compCols S κ ∧ D a b := by
    intro κ
    have hcard' : (compRows S κ).card + (compCols S κ)ᶜ.card = m + 1 := by
      rw [Finset.card_compl, Fintype.card_fin, hbal κ]
      have := Finset.card_le_univ (compCols S κ)
      rw [Fintype.card_fin] at this
      omega
    obtain ⟨a, ha, b, hb, hab⟩ := hD _ _ (hrowsne κ) (hcolsne κ) hcard'
    exact ⟨a, b, ha, Finset.mem_compl.1 hb, hab⟩
  choose ea eb hea heb hDe using hout
  let next : G.ConnectedComponent → G.ConnectedComponent := fun κ =>
    G.connectedComponentMk (Sum.inr (eb κ))
  have hnext_ne : ∀ κ, next κ ≠ κ := fun κ h => heb κ (mem_compCols.2 h)
  have hea_not : ∀ κ, ea κ ∉ compRows S (next κ) := by
    intro κ h
    exact hnext_ne κ ((mem_compRows.1 h).symm.trans (mem_compRows.1 (hea κ)))
  have heb_mem : ∀ κ, eb κ ∈ compCols S (next κ) := fun κ => mem_compCols.2 rfl
  -- A nonempty set of components on which `next` is a bijection.
  have hfinP : (Function.periodicPts next).Finite := Set.toFinite _
  set Cyc := hfinP.toFinset with hCyc
  have hCycne : Cyc.Nonempty := by
    obtain ⟨a, b, hab, heq⟩ := Finite.exists_ne_map_eq_of_infinite
      (fun k : ℕ => next^[k] (G.connectedComponentMk (Sum.inl (0 : Fin (m + 1)))))
    rcases Nat.lt_or_gt_of_ne hab with h | h
    · refine ⟨next^[a] (G.connectedComponentMk (Sum.inl 0)), ?_⟩
      rw [Set.Finite.mem_toFinset]
      refine Function.mk_mem_periodicPts (n := b - a) (by omega) ?_
      show next^[b - a] (next^[a] _) = next^[a] _
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel h.le]
      exact heq.symm
    · refine ⟨next^[b] (G.connectedComponentMk (Sum.inl 0)), ?_⟩
      rw [Set.Finite.mem_toFinset]
      refine Function.mk_mem_periodicPts (n := a - b) (by omega) ?_
      show next^[a - b] (next^[b] _) = next^[b] _
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel h.le]
      exact heq
  have hbij := Function.bijOn_periodicPts next
  have hreindex : ∀ g : G.ConnectedComponent → ℝ,
      ∑ κ ∈ Cyc, g (next κ) = ∑ κ ∈ Cyc, g κ := by
    intro g
    refine Finset.sum_nbij next ?_ ?_ ?_ fun κ _ => rfl
    · intro κ hκ
      rw [Set.Finite.mem_toFinset] at hκ ⊢
      exact hbij.mapsTo hκ
    · rw [Set.Finite.coe_toFinset]
      exact hbij.injOn
    · rw [Set.Finite.coe_toFinset]
      exact hbij.surjOn
  -- Transfers inside the arriving component.
  have htr : ∀ κ, ∃ Z : Square (m + 1), SupportedIn S Z ∧
      (∀ a, ∑ b, Z a b = if a = ea (next κ) then 1 else 0) ∧
      (∀ b, ∑ a, Z a b = if b = eb κ then 1 else 0) := by
    intro κ
    apply exists_transfer
    apply SimpleGraph.ConnectedComponent.exact
    exact (mem_compRows.1 (hea (next κ))).trans (mem_compCols.1 (heb_mem κ)).symm
  choose Zt hZt hZrow hZcol using htr
  let X : Square (m + 1) := fun a b =>
    ∑ κ ∈ Cyc, (unitAt (ea κ) (eb κ) a b - Zt κ a b)
  have hXrow : ∀ a, ∑ b, X a b = 0 := by
    intro a
    simp only [X]
    rw [Finset.sum_comm]
    simp only [Finset.sum_sub_distrib, unitAt_row_sum, hZrow]
    rw [hreindex (fun κ => if a = ea κ then (1 : ℝ) else 0), sub_self]
  have hXcol : ∀ b, ∑ a, X a b = 0 := by
    intro b
    simp only [X]
    rw [Finset.sum_comm]
    simp only [Finset.sum_sub_distrib, unitAt_col_sum, hZcol, sub_self,
      Finset.sum_const_zero]
  have hZoff : ∀ κ a b, A a b = 0 → Zt κ a b = 0 := by
    intro κ a b h
    by_contra hz
    exact hZt κ a b hz h
  have hXnn : ∀ a b, A a b = 0 → 0 ≤ X a b := by
    intro a b h
    refine Finset.sum_nonneg fun κ _ => ?_
    rw [hZoff κ a b h, sub_zero]
    simp only [unitAt]
    split_ifs <;> norm_num
  have hXD : ∀ a b, X a b ≠ 0 → D a b := by
    intro a b hX
    by_contra hDab
    apply hX
    refine Finset.sum_eq_zero fun κ _ => ?_
    have hu : unitAt (ea κ) (eb κ) a b = 0 := by
      simp only [unitAt]
      split_ifs with h
      · obtain ⟨rfl, rfl⟩ := h
        exact absurd (hDe κ) hDab
      · rfl
    have hz : Zt κ a b = 0 := by
      by_contra hz
      exact hDab (hsupp a b (hZt κ a b hz))
    rw [hu, hz, sub_zero]
  -- The derivative along `X` is `-(#Cyc) · per A`.
  set P := permanent A with hP
  have hPpos : 0 < P := permanent_pos_of_doublyStochastic ⟨hnn, hrow, hcol⟩
  have hedge : ∀ κ, cofactor A (ea κ) (eb κ) = 0 := fun κ =>
    cofactor_eq_zero_of_closedPair (hclosed (next κ)) (hbal (next κ)).symm.le
      (hea_not κ) (heb_mem κ)
  have hZC : ∀ κ, ∑ a, ∑ b, Zt κ a b * cofactor A a b = P := by
    intro κ
    have : ∀ a b, Zt κ a b * cofactor A a b = Zt κ a b * P := by
      intro a b
      by_cases hz : Zt κ a b = 0
      · rw [hz, zero_mul, zero_mul]
      · rw [faceMinimizer_cofactor_eq hA (hZt κ a b hz)]
    simp only [this, ← Finset.sum_mul, hZrow, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true, one_mul]
  have hval : ∑ a, ∑ b, X a b * cofactor A a b = -(Cyc.card : ℝ) * P := by
    have hexp : ∀ a b, X a b * cofactor A a b =
        ∑ κ ∈ Cyc, (unitAt (ea κ) (eb κ) a b * cofactor A a b -
          Zt κ a b * cofactor A a b) := by
      intro a b
      simp only [X, Finset.sum_mul, sub_mul]
    have hexp2 : ∑ a, ∑ b, X a b * cofactor A a b =
        ∑ κ ∈ Cyc, ∑ a, ∑ b, (unitAt (ea κ) (eb κ) a b * cofactor A a b -
          Zt κ a b * cofactor A a b) := by
      calc ∑ a, ∑ b, X a b * cofactor A a b
          = ∑ a, ∑ b, ∑ κ ∈ Cyc, (unitAt (ea κ) (eb κ) a b * cofactor A a b -
              Zt κ a b * cofactor A a b) := by simp only [hexp]
        _ = ∑ a, ∑ κ ∈ Cyc, ∑ b, (unitAt (ea κ) (eb κ) a b * cofactor A a b -
              Zt κ a b * cofactor A a b) :=
            Finset.sum_congr rfl fun a _ => Finset.sum_comm
        _ = _ := Finset.sum_comm
    rw [hexp2]
    simp only [Finset.sum_sub_distrib, unitAt_pair_sum, hedge, hZC, zero_sub,
      Finset.sum_neg_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  have hneg : -(Cyc.card : ℝ) * P < 0 := by
    have : (0 : ℝ) < Cyc.card := by exact_mod_cast hCycne.card_pos
    nlinarith
  -- A small step along `X` stays in the face and lowers the permanent.
  have hderiv := hasDerivAt_permanent_add_smul A X
  rw [hval] at hderiv
  have hslope := hderiv.tendsto_slope_zero_right
  have hev1 : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      t⁻¹ • (permanent (A + (0 + t) • X) - permanent (A + (0 : ℝ) • X)) < 0 :=
    hslope.eventually (eventually_lt_nhds hneg)
  have hev2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have hev3' : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ a b, 0 < A a b → 0 < A a b + t * X a b := by
    rw [Filter.eventually_all]
    intro a
    rw [Filter.eventually_all]
    intro b
    by_cases hab : 0 < A a b
    · have ht : Tendsto (fun t : ℝ => A a b + t * X a b) (𝓝 0) (𝓝 (A a b + 0 * X a b)) :=
        (by fun_prop : Continuous (fun t : ℝ => A a b + t * X a b)).tendsto 0
      rw [zero_mul, add_zero] at ht
      exact (ht.eventually (lt_mem_nhds hab)).mono fun t h _ => h
    · exact Filter.Eventually.of_forall fun t h => absurd h hab
  have hev3 : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ a b, 0 < A a b → 0 < A a b + t * X a b :=
    nhdsWithin_le_nhds hev3'
  obtain ⟨t, h1, h2, h3⟩ := (hev1.and (hev2.and hev3)).exists
  simp only [zero_add, zero_smul, add_zero, smul_eq_mul] at h1
  have hlt : permanent (A + t • X) < permanent A := by
    have := (mul_neg_iff.1 h1)
    rcases this with ⟨_, h⟩ | ⟨h, _⟩
    · linarith
    · exact absurd (inv_pos.2 h2) (not_lt.2 h.le)
  have hentry : ∀ a b, (A + t • X) a b = A a b + t * X a b := by
    intro a b
    simp
  have hface : InFace D (A + t • X) := by
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro a b
      rw [hentry]
      by_cases hab : A a b = 0
      · rw [hab, zero_add]
        exact mul_nonneg h2.le (hXnn a b hab)
      · exact (h3 a b (lt_of_le_of_ne (hnn a b) (Ne.symm hab))).le
    · intro a
      simp only [hentry, Finset.sum_add_distrib, ← Finset.mul_sum, hXrow, hrow a]
      ring
    · intro b
      simp only [hentry, Finset.sum_add_distrib, ← Finset.mul_sum, hXcol, hcol b]
      ring
    · intro a b hab
      rw [hentry] at hab
      by_cases hA0 : A a b = 0
      · rw [hA0, zero_add] at hab
        exact hXD a b (right_ne_zero_of_mul hab)
      · exact hsupp a b hA0
  exact absurd (hmin _ hface) (not_le.2 hlt)

/--
Lavi Lemma 2.1 in full: at a permanent minimizer on the face of a fully
indecomposable support, the support is fully indecomposable and every
cofactor at a positive entry equals the permanent.
-/
theorem lavi_lemma_2_1 {m : ℕ} {D : Fin (m + 1) → Fin (m + 1) → Prop}
    (hD : FullyIndecomposable D) {A : Square (m + 1)} (hA : FaceMinimizer D A) :
    FullyIndecomposable (support A) ∧
      ∀ i j, A i j ≠ 0 → cofactor A i j = permanent A :=
  ⟨faceMinimizer_support_fullyIndecomposable hD hA,
    fun _ _ hij => faceMinimizer_cofactor_eq hA hij⟩

/--
The consequence stated with Lemma 2.1: on a nearly decomposable face, every
face minimizer has support exactly `D`.
-/
theorem faceMinimizer_support_eq_of_nearlyDecomposable {m : ℕ}
    {D : Fin (m + 1) → Fin (m + 1) → Prop} (hD : NearlyDecomposable D)
    {A : Square (m + 1)} (hA : FaceMinimizer D A) (i j : Fin (m + 1)) :
    A i j ≠ 0 ↔ D i j := by
  refine ⟨hA.1.2 i j, fun hDij => ?_⟩
  intro h0
  have hFI := faceMinimizer_support_fullyIndecomposable hD.1 hA
  refine hD.2 i j hDij (hFI.mono fun a b hab => ⟨hA.1.2 a b hab, ?_⟩)
  rintro ⟨rfl, rfl⟩
  exact hab h0

end Support

end LaviSection2
