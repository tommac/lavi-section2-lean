import LaviSection2.LaviFaceVariational

/-!
# Lavi Section 3: matching entropy on occurrence cores, and Lemma 3.2

An occurrence core is a bipartite multigraph: edges `E` with endpoints
`row : E → U` and `col : E → V`.  A *labelled perfect matching* chooses, for
every row `u`, an edge `M u` at `u` so that the columns `col (M u)` are all
distinct.  A law on labelled matchings has edge marginal `x e` = probability
that `e` is chosen.  Lavi's core functional (3.2) is

`F_H(x) = Ent*_H(x) - ∑_rows Ent((x_e)_{e ∋ u})`,

and, since every edge has exactly one row, the row-entropy sum is the total
edge entropy `-∑_e x_e log x_e`.

**Lemma 3.2 (aggregation).**  Merging parallel occurrences does not change
`F`.  We prove it for any edge map `φ : E → E'` that respects endpoints, with
the merged flows `x'_{e'} = ∑_{φ e = e'} x_e`.  Both `Ent*` and the edge
entropy drop by the same amount `C = -∑_e x_e log (x_e / x'_{φ e})`:

* any law `μ` on `H` pushes forward to a law on `H'`, and the finite Gibbs
  inequality against the *independent relabelling* law gives
  `Ent(μ) ≤ Ent(φ_* μ) + C`;
* any law `ν` on `H'` lifts, choosing labels independently with
  probabilities `x_e / x'_{φ e}`, to a law on `H` of entropy exactly
  `Ent(ν) + C`.

This avoids the entropy chain rule and concavity used in the manuscript.
-/

set_option linter.unusedSectionVars false

namespace LaviSection2

open Finset Equiv Real

open scoped BigOperators

/-- Regrouping a sum over a filtered set of fibres. -/
theorem sum_filter_fibers {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (g : α → β) (p : β → Prop) [DecidablePred p] (f : α → ℝ) :
    ∑ b ∈ (univ : Finset β).filter p, ∑ a ∈ (univ : Finset α).filter (fun a => g a = b), f a =
      ∑ a ∈ (univ : Finset α).filter (fun a => p (g a)), f a := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := (univ : Finset α).filter (fun a => p (g a)))
    (t := (univ : Finset β).filter p) (g := g)
    (fun a ha => Finset.mem_filter.2 ⟨mem_univ _, (Finset.mem_filter.1 ha).2⟩) f]
  refine Finset.sum_congr rfl fun b hb => Finset.sum_congr ?_ fun _ _ => rfl
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h; exact ⟨by rw [h]; exact (Finset.mem_filter.1 hb).2, h⟩
  · exact fun h => h.2

section CoreLaws

variable {U V E : Type*} [Fintype U] [Fintype V] [Fintype E]
  [DecidableEq U] [DecidableEq V] [DecidableEq E]

/-- Labelled perfect matchings of the bipartite multigraph `(row, col)`. -/
abbrev LMatch (row : E → U) (col : E → V) : Type _ :=
  {M : U → E // (∀ u, row (M u) = u) ∧ Function.Bijective fun u => col (M u)}

variable (row : E → U) (col : E → V)

/-- Edge marginals of a law on labelled matchings. -/
def coreMarginal (μ : LMatch row col → ℝ) (e : E) : ℝ :=
  ∑ M ∈ (univ : Finset (LMatch row col)).filter (fun M => M.1 (row e) = e), μ M

/-- `μ` is a probability law on labelled matchings with edge marginals `x`. -/
def IsCoreLaw (x : E → ℝ) (μ : LMatch row col → ℝ) : Prop :=
  (∀ M, 0 ≤ μ M) ∧ ∑ M, μ M = 1 ∧ coreMarginal row col μ = x

/-- Shannon entropy of a law on labelled matchings. -/
noncomputable def coreLawEntropy (μ : LMatch row col → ℝ) : ℝ :=
  ∑ M, -(μ M * log (μ M))

/-- Total edge entropy, equal to the sum of the row entropies. -/
noncomputable def edgeEntropy (x : E → ℝ) : ℝ :=
  -∑ e, x e * log (x e)

/-- `Ent*_H(x)`, the maximal entropy of a law with marginals `x`. -/
noncomputable def coreMaxEntropy (x : E → ℝ) : ℝ :=
  sSup (coreLawEntropy row col '' {μ | IsCoreLaw row col x μ})

/-- Lavi's core functional `F_H(x)`, equation (3.2). -/
noncomputable def coreFunctional (x : E → ℝ) : ℝ :=
  coreMaxEntropy row col x - edgeEntropy x

variable {row col}

theorem IsCoreLaw.nonneg_edge {x : E → ℝ} {μ : LMatch row col → ℝ}
    (h : IsCoreLaw row col x μ) (e : E) : 0 ≤ x e := by
  rw [← h.2.2]
  exact Finset.sum_nonneg fun M _ => h.1 M

theorem IsCoreLaw.le_edge {x : E → ℝ} {μ : LMatch row col → ℝ}
    (h : IsCoreLaw row col x μ) (M : LMatch row col) (u : U) : μ M ≤ x (M.1 u) := by
  classical
  rw [← h.2.2]
  unfold coreMarginal
  refine Finset.single_le_sum (f := μ) (fun N _ => h.1 N) (Finset.mem_filter.2 ⟨mem_univ _, ?_⟩)
  rw [M.2.1 u]

/-- Expected edge sums: `∑_M μ M ∑_u g (M u) = ∑_e m_e g e`. -/
theorem sum_mul_sum_edge (μ : LMatch row col → ℝ) (g : E → ℝ) :
    ∑ M, μ M * ∑ u, g (M.1 u) = ∑ e, coreMarginal row col μ e * g e := by
  classical
  calc ∑ M, μ M * ∑ u, g (M.1 u)
      = ∑ u, ∑ M, μ M * g (M.1 u) := by
        simp_rw [Finset.mul_sum]; exact Finset.sum_comm
    _ = ∑ u, ∑ e, if row e = u then
          ∑ M ∈ (univ : Finset (LMatch row col)).filter (fun M => M.1 (row e) = e), μ M * g e
          else 0 := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [← Finset.sum_fiberwise univ (fun M : LMatch row col => M.1 u)
          (fun M => μ M * g (M.1 u))]
        refine Finset.sum_congr rfl fun e _ => ?_
        split_ifs with he
        · subst he
          refine Finset.sum_congr rfl fun M hM => ?_
          rw [(Finset.mem_filter.1 hM).2]
        · refine Finset.sum_eq_zero fun M hM => ?_
          exact absurd (by rw [← (Finset.mem_filter.1 hM).2, M.2.1 u]) he
    _ = ∑ e, coreMarginal row col μ e * g e := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _), coreMarginal, Finset.sum_mul]

/-- Entropy is at most the number of matchings (a crude but sufficient bound). -/
theorem coreLawEntropy_le_card {μ : LMatch row col → ℝ} (hμ : ∀ M, 0 ≤ μ M) :
    coreLawEntropy row col μ ≤ Fintype.card (LMatch row col) := by
  unfold coreLawEntropy
  rw [Fintype.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  refine Finset.sum_le_sum fun M _ => ?_
  rcases (hμ M).lt_or_eq with hpos | hzero
  · have := Real.one_sub_inv_le_log_of_pos hpos
    have h1 : μ M * (1 - (μ M)⁻¹) = μ M - 1 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left this hpos.le]
  · rw [← hzero]; simp

theorem bddAbove_coreLawEntropy (x : E → ℝ) :
    BddAbove (coreLawEntropy row col '' {μ | IsCoreLaw row col x μ}) :=
  ⟨_, by rintro _ ⟨μ, hμ, rfl⟩; exact coreLawEntropy_le_card hμ.1⟩

end CoreLaws

section Aggregation

variable {U V E E' : Type*} [Fintype U] [Fintype V] [Fintype E] [Fintype E']
  [DecidableEq U] [DecidableEq V] [DecidableEq E] [DecidableEq E']
  {row : E → U} {col : E → V} {row' : E' → U} {col' : E' → V}
  (φ : E → E') (hrow : ∀ e, row' (φ e) = row e) (hcol : ∀ e, col' (φ e) = col e)

include hrow hcol in
/-- Pushing a labelled matching forward along `φ`. -/
def pushMatch (M : LMatch row col) : LMatch row' col' :=
  ⟨fun u => φ (M.1 u), fun u => by rw [hrow, M.2.1 u], by simpa only [hcol] using M.2.2⟩

/-- Merged flows `x'_{e'} = ∑_{φ e = e'} x_e`. -/
def mergeFlow (x : E → ℝ) (e' : E') : ℝ :=
  ∑ e ∈ (univ : Finset E).filter (fun e => φ e = e'), x e

/-- The push-forward of a law. -/
def pushLaw (μ : LMatch row col → ℝ) (M' : LMatch row' col') : ℝ :=
  ∑ M ∈ (univ : Finset (LMatch row col)).filter (fun M => pushMatch φ hrow hcol M = M'), μ M

/-- Relabelling probabilities `r_e = x_e / x'_{φ e}`. -/
noncomputable def relabelProb (x : E → ℝ) (e : E) : ℝ :=
  x e / mergeFlow φ x (φ e)

/-- The independent-relabelling lift of a law on `H'`. -/
noncomputable def liftLaw (x : E → ℝ) (ν : LMatch row' col' → ℝ) (M : LMatch row col) : ℝ :=
  ν (pushMatch φ hrow hcol M) * ∏ u, relabelProb φ x (M.1 u)

theorem pushMatch_val (M : LMatch row col) (u : U) :
    (pushMatch φ hrow hcol M).1 u = φ (M.1 u) := rfl

/-- Sums of products over a fibre of `pushMatch` factor over rows. -/
theorem sum_fiber_prod (M' : LMatch row' col') (f : U → E → ℝ) :
    ∑ M ∈ (univ : Finset (LMatch row col)).filter (fun M => pushMatch φ hrow hcol M = M'),
      ∏ u, f u (M.1 u) =
    ∏ u, ∑ e ∈ (univ : Finset E).filter (fun e => φ e = M'.1 u), f u e := by
  classical
  rw [Finset.prod_univ_sum (fun u => (univ : Finset E).filter (fun e => φ e = M'.1 u)) f]
  refine Finset.sum_bij (fun M _ => M.1) ?_ ?_ ?_ ?_
  · intro M hM
    rw [Fintype.mem_piFinset]
    intro u
    rw [Finset.mem_filter]
    refine ⟨mem_univ _, ?_⟩
    rw [← (Finset.mem_filter.1 hM).2]
    rfl
  · intro M₁ _ M₂ _ h
    exact Subtype.ext h
  · intro g hg
    rw [Fintype.mem_piFinset] at hg
    have hφ : ∀ u, φ (g u) = M'.1 u := fun u => (Finset.mem_filter.1 (hg u)).2
    have hr : ∀ u, row (g u) = u := fun u => by rw [← hrow, hφ, M'.2.1 u]
    have hb : Function.Bijective fun u => col (g u) := by
      have : (fun u => col (g u)) = fun u => col' (M'.1 u) := funext fun u => by
        rw [← hcol, hφ]
      rw [this]; exact M'.2.2
    refine ⟨⟨g, hr, hb⟩, Finset.mem_filter.2 ⟨mem_univ _, ?_⟩, rfl⟩
    exact Subtype.ext (funext fun u => hφ u)
  · intro M _
    rfl

theorem mergeFlow_ge {x : E → ℝ} (hx : ∀ e, 0 ≤ x e) (e : E) : x e ≤ mergeFlow φ x (φ e) :=
  Finset.single_le_sum (f := x) (fun e _ => hx e) (Finset.mem_filter.2 ⟨mem_univ _, rfl⟩)

/-- Relabelling probabilities sum to one on every fibre of positive flow. -/
theorem sum_relabelProb {x : E → ℝ} (e' : E') (he' : mergeFlow φ x e' ≠ 0) :
    ∑ e ∈ (univ : Finset E).filter (fun e => φ e = e'), relabelProb φ x e = 1 := by
  unfold relabelProb
  rw [Finset.sum_congr rfl fun e he => by rw [(Finset.mem_filter.1 he).2], ← Finset.sum_div]
  exact div_self he'

theorem sum_relabelProb_le {x : E → ℝ} (hx : ∀ e, 0 ≤ x e) (e' : E') :
    ∑ e ∈ (univ : Finset E).filter (fun e => φ e = e'), relabelProb φ x e ≤ 1 := by
  by_cases he' : mergeFlow φ x e' = 0
  · unfold relabelProb
    rw [Finset.sum_congr rfl fun e he => by rw [(Finset.mem_filter.1 he).2, he', div_zero]]
    simp
  · exact (sum_relabelProb φ e' he').le

theorem relabelProb_nonneg {x : E → ℝ} (hx : ∀ e, 0 ≤ x e) (e : E) : 0 ≤ relabelProb φ x e :=
  div_nonneg (hx e) (Finset.sum_nonneg fun e _ => hx e)

/-- Total mass of a lifted law. -/
theorem sum_liftLaw {x : E → ℝ} (ν : LMatch row' col' → ℝ) :
    ∑ M, liftLaw φ hrow hcol x ν M =
      ∑ M', ν M' * ∏ u, ∑ e ∈ (univ : Finset E).filter (fun e => φ e = M'.1 u),
        relabelProb φ x e := by
  classical
  unfold liftLaw
  rw [← Finset.sum_fiberwise univ (pushMatch φ hrow hcol)]
  refine Finset.sum_congr rfl fun M' _ => ?_
  rw [← sum_fiber_prod φ hrow hcol M' (fun _ e => relabelProb φ x e), Finset.mul_sum]
  refine Finset.sum_congr rfl fun M hM => ?_
  rw [(Finset.mem_filter.1 hM).2]

/-- Push-forward of a law is a law with the merged marginals. -/
theorem isCoreLaw_pushLaw {x : E → ℝ} {μ : LMatch row col → ℝ} (h : IsCoreLaw row col x μ) :
    IsCoreLaw row' col' (mergeFlow φ x) (pushLaw φ hrow hcol μ) := by
  classical
  refine ⟨fun M' => Finset.sum_nonneg fun M _ => h.1 M, ?_, ?_⟩
  · unfold pushLaw
    rw [Finset.sum_fiberwise univ (pushMatch φ hrow hcol) μ, h.2.1]
  · funext e'
    have hL : coreMarginal row' col' (pushLaw φ hrow hcol μ) e' =
        ∑ M ∈ (univ : Finset (LMatch row col)).filter (fun M => φ (M.1 (row' e')) = e'), μ M := by
      unfold coreMarginal pushLaw
      exact sum_filter_fibers (pushMatch φ hrow hcol) (fun M' => M'.1 (row' e') = e') μ
    have hR : mergeFlow φ x e' =
        ∑ M ∈ (univ : Finset (LMatch row col)).filter (fun M => φ (M.1 (row' e')) = e'), μ M := by
      unfold mergeFlow
      rw [← h.2.2]
      unfold coreMarginal
      rw [← sum_filter_fibers (fun M : LMatch row col => M.1 (row' e')) (fun e => φ e = e') μ]
      refine Finset.sum_congr rfl fun e he => ?_
      have hre : row e = row' e' := by rw [← hrow, (Finset.mem_filter.1 he).2]
      rw [hre]
    rw [hL, hR]


/-- The relabelling entropy `C = -∑_e x_e log (x_e / x'_{φ e})`. -/
noncomputable def relabelEntropy (x : E → ℝ) : ℝ :=
  -∑ e, x e * log (relabelProb φ x e)

/-- Fibre sums of a lifted law. -/
theorem sum_fiber_liftLaw (x : E → ℝ) (ν : LMatch row' col' → ℝ) (M' : LMatch row' col') :
    ∑ M ∈ (univ : Finset (LMatch row col)).filter (fun M => pushMatch φ hrow hcol M = M'),
      liftLaw φ hrow hcol x ν M =
    ν M' * ∏ u, ∑ e ∈ (univ : Finset E).filter (fun e => φ e = M'.1 u), relabelProb φ x e := by
  unfold liftLaw
  rw [← sum_fiber_prod φ hrow hcol M' (fun _ e => relabelProb φ x e), Finset.mul_sum]
  refine Finset.sum_congr rfl fun M hM => ?_
  rw [(Finset.mem_filter.1 hM).2]

/-- On a fibre charged by a law with merged marginals, the relabelling
product is one. -/
theorem prod_sum_relabelProb_eq_one {x : E → ℝ} {ν : LMatch row' col' → ℝ}
    (hν : IsCoreLaw row' col' (mergeFlow φ x) ν) {M' : LMatch row' col'} (h0 : ν M' ≠ 0) :
    ∏ u, ∑ e ∈ (univ : Finset E).filter (fun e => φ e = M'.1 u), relabelProb φ x e = 1 := by
  refine Finset.prod_eq_one fun u _ => sum_relabelProb φ _ ?_
  exact ne_of_gt (lt_of_lt_of_le (lt_of_le_of_ne (hν.1 M') (Ne.symm h0)) (hν.le_edge M' u))

/-- The lift of a law on `H'` is a law on `H` with marginals `x`. -/
theorem isCoreLaw_liftLaw {x : E → ℝ} (hx : ∀ e, 0 ≤ x e) {ν : LMatch row' col' → ℝ}
    (hν : IsCoreLaw row' col' (mergeFlow φ x) ν) :
    IsCoreLaw row col x (liftLaw φ hrow hcol x ν) := by
  classical
  refine ⟨fun M => mul_nonneg (hν.1 _) (Finset.prod_nonneg fun u _ => relabelProb_nonneg φ hx _),
    ?_, ?_⟩
  · rw [sum_liftLaw, ← hν.2.1]
    refine Finset.sum_congr rfl fun M' _ => ?_
    by_cases h0 : ν M' = 0
    · simp [h0]
    · rw [prod_sum_relabelProb_eq_one φ hν h0, mul_one]
  · funext e
    set u₀ := row e with hu₀
    let f : U → E → ℝ := fun u e₂ =>
      if u = u₀ then (if e₂ = e then relabelProb φ x e₂ else 0) else relabelProb φ x e₂
    -- insert the constraint `M u₀ = e` into the product
    have hM : ∀ M : LMatch row col, (if M.1 u₀ = e then liftLaw φ hrow hcol x ν M else 0) =
        ν (pushMatch φ hrow hcol M) * ∏ u, f u (M.1 u) := by
      intro M
      unfold liftLaw
      rw [← Finset.mul_prod_erase univ (fun u => f u (M.1 u)) (mem_univ u₀),
        ← Finset.mul_prod_erase univ (fun u => relabelProb φ x (M.1 u)) (mem_univ u₀)]
      have hrest : ∏ u ∈ univ.erase u₀, f u (M.1 u) =
          ∏ u ∈ univ.erase u₀, relabelProb φ x (M.1 u) :=
        Finset.prod_congr rfl fun u hu => by
          simp only [f, if_neg (Finset.ne_of_mem_erase hu)]
      rw [hrest]
      simp only [f, if_true]
      split_ifs <;> ring
    have hfib : ∀ M' : LMatch row' col', ν M' *
        ∏ u, ∑ e₂ ∈ (univ : Finset E).filter (fun e₂ => φ e₂ = M'.1 u), f u e₂ =
        if M'.1 u₀ = φ e then ν M' * relabelProb φ x e else 0 := by
      intro M'
      by_cases h0 : ν M' = 0
      · simp [h0]
      rw [← Finset.mul_prod_erase univ _ (mem_univ u₀)]
      have hrest : ∏ u ∈ univ.erase u₀,
          ∑ e₂ ∈ (univ : Finset E).filter (fun e₂ => φ e₂ = M'.1 u), f u e₂ = 1 := by
        refine Finset.prod_eq_one fun u hu => ?_
        simp only [f, if_neg (Finset.ne_of_mem_erase hu)]
        refine sum_relabelProb φ _ ?_
        exact ne_of_gt (lt_of_lt_of_le (lt_of_le_of_ne (hν.1 M') (Ne.symm h0))
          (hν.le_edge M' u))
      rw [hrest, mul_one]
      simp only [f, if_true]
      rw [Finset.sum_ite_eq']
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs with h1 h2 h2
      · rfl
      · exact absurd h1.symm h2
      · exact absurd h2.symm h1
      · simp
    calc coreMarginal row col (liftLaw φ hrow hcol x ν) e
        = ∑ M, ν (pushMatch φ hrow hcol M) * ∏ u, f u (M.1 u) := by
          unfold coreMarginal
          rw [Finset.sum_filter]
          exact Finset.sum_congr rfl fun M _ => hM M
      _ = ∑ M', ν M' *
            ∏ u, ∑ e₂ ∈ (univ : Finset E).filter (fun e₂ => φ e₂ = M'.1 u), f u e₂ := by
          rw [← Finset.sum_fiberwise univ (pushMatch φ hrow hcol)]
          refine Finset.sum_congr rfl fun M' _ => ?_
          rw [← sum_fiber_prod φ hrow hcol M' f, Finset.mul_sum]
          refine Finset.sum_congr rfl fun M hM => ?_
          rw [(Finset.mem_filter.1 hM).2]
      _ = ∑ M', if M'.1 u₀ = φ e then ν M' * relabelProb φ x e else 0 :=
          Finset.sum_congr rfl fun M' _ => hfib M'
      _ = relabelProb φ x e * mergeFlow φ x (φ e) := by
          rw [← Finset.sum_filter, ← Finset.sum_mul, mul_comm, ← hν.2.2]
          unfold coreMarginal
          congr 2
          ext M'
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, hu₀, hrow]
      _ = x e := by
          unfold relabelProb
          by_cases hz : mergeFlow φ x (φ e) = 0
          · have := mergeFlow_ge φ hx e
            rw [hz] at this ⊢
            simp only [div_zero, zero_mul]
            linarith [hx e]
          · exact div_mul_cancel₀ _ hz

/-- The entropy of a lifted law is `Ent(ν) + C`. -/
theorem coreLawEntropy_liftLaw {x : E → ℝ} (hx : ∀ e, 0 ≤ x e) {ν : LMatch row' col' → ℝ}
    (hν : IsCoreLaw row' col' (mergeFlow φ x) ν) :
    coreLawEntropy row col (liftLaw φ hrow hcol x ν) =
      coreLawEntropy row' col' ν + relabelEntropy φ x := by
  classical
  have hlaw := isCoreLaw_liftLaw φ hrow hcol hx hν
  set κ := liftLaw φ hrow hcol x ν with hκ
  have hterm : ∀ M, κ M * log (κ M) =
      κ M * log (ν (pushMatch φ hrow hcol M)) + κ M * ∑ u, log (relabelProb φ x (M.1 u)) := by
    intro M
    by_cases h0 : κ M = 0
    · simp [h0]
    · have hν0 : ν (pushMatch φ hrow hcol M) ≠ 0 := fun h => h0 (by simp [hκ, liftLaw, h])
      have hr0 : ∏ u, relabelProb φ x (M.1 u) ≠ 0 := fun h => h0 (by simp [hκ, liftLaw, h])
      rw [show κ M = ν (pushMatch φ hrow hcol M) * ∏ u, relabelProb φ x (M.1 u) from rfl,
        Real.log_mul hν0 hr0, Real.log_prod (fun u _ => Finset.prod_ne_zero_iff.1 hr0 u
          (mem_univ u))]
      ring
  have h1 : ∑ M, κ M * log (ν (pushMatch φ hrow hcol M)) = ∑ M', ν M' * log (ν M') := by
    rw [← Finset.sum_fiberwise univ (pushMatch φ hrow hcol)]
    refine Finset.sum_congr rfl fun M' _ => ?_
    rw [Finset.sum_congr rfl fun M hM => by rw [(Finset.mem_filter.1 hM).2], ← Finset.sum_mul,
      hκ, sum_fiber_liftLaw]
    by_cases h0 : ν M' = 0
    · simp [h0]
    · rw [prod_sum_relabelProb_eq_one φ hν h0, mul_one]
  have h2 : ∑ M, κ M * ∑ u, log (relabelProb φ x (M.1 u)) =
      ∑ e, x e * log (relabelProb φ x e) := by
    rw [sum_mul_sum_edge (row := row) (col := col) κ (fun e => log (relabelProb φ x e)),
      hlaw.2.2]
  unfold coreLawEntropy relabelEntropy
  simp only [Finset.sum_neg_distrib]
  rw [Finset.sum_congr rfl fun M _ => hterm M, Finset.sum_add_distrib, h1, h2]
  ring

/-- Gibbs comparison: `Ent(μ) ≤ Ent(φ_* μ) + C`. -/
theorem coreLawEntropy_le_pushLaw {x : E → ℝ} {μ : LMatch row col → ℝ}
    (hμ : IsCoreLaw row col x μ) :
    coreLawEntropy row col μ ≤
      coreLawEntropy row' col' (pushLaw φ hrow hcol μ) + relabelEntropy φ x := by
  classical
  have hx : ∀ e, 0 ≤ x e := hμ.nonneg_edge
  set ν := pushLaw φ hrow hcol μ with hνdef
  have hν := isCoreLaw_pushLaw φ hrow hcol hμ
  set κ := liftLaw φ hrow hcol x ν with hκ
  have hκlaw := isCoreLaw_liftLaw φ hrow hcol hx hν
  have hνge : ∀ M, μ M ≤ ν (pushMatch φ hrow hcol M) := fun M =>
    Finset.single_le_sum (f := μ) (fun N _ => hμ.1 N) (Finset.mem_filter.2 ⟨mem_univ _, rfl⟩)
  have hrpos : ∀ M, 0 < μ M → ∀ u, 0 < relabelProb φ x (M.1 u) := by
    intro M hM u
    have h1 := lt_of_lt_of_le hM (hμ.le_edge M u)
    exact div_pos h1 (lt_of_lt_of_le h1 (mergeFlow_ge φ hx _))
  have hκpos : ∀ M, 0 < μ M → 0 < κ M := fun M hM =>
    mul_pos (lt_of_lt_of_le hM (hνge M)) (Finset.prod_pos fun u _ => hrpos M hM u)
  have hlogκ : ∀ M, μ M * log (κ M) =
      μ M * log (ν (pushMatch φ hrow hcol M)) + μ M * ∑ u, log (relabelProb φ x (M.1 u)) := by
    intro M
    rcases (hμ.1 M).lt_or_eq with hM | hM
    · rw [show κ M = ν (pushMatch φ hrow hcol M) * ∏ u, relabelProb φ x (M.1 u) from rfl,
        Real.log_mul (ne_of_gt (lt_of_lt_of_le hM (hνge M)))
          (ne_of_gt (Finset.prod_pos fun u _ => hrpos M hM u)),
        Real.log_prod (fun u _ => ne_of_gt (hrpos M hM u))]
      ring
    · rw [← hM]; simp
  -- termwise Gibbs inequality
  have hgibbs : ∀ M, -(μ M * log (μ M)) ≤ -(μ M * log (κ M)) + κ M - μ M := by
    intro M
    rcases (hμ.1 M).lt_or_eq with hM | hM
    · have hk := hκpos M hM
      have hl := Real.log_le_sub_one_of_pos (div_pos hk hM)
      rw [Real.log_div (ne_of_gt hk) (ne_of_gt hM)] at hl
      have h3 := mul_le_mul_of_nonneg_left hl hM.le
      have h4 : μ M * (κ M / μ M - 1) = κ M - μ M := by field_simp
      nlinarith [h3, h4]
    · rw [← hM]; simpa using hκlaw.1 M
  have hsum := Finset.sum_le_sum fun M (_ : M ∈ univ) => hgibbs M
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hκlaw.2.1, hμ.2.1] at hsum
  have h1 : ∑ M, μ M * log (ν (pushMatch φ hrow hcol M)) = ∑ M', ν M' * log (ν M') := by
    rw [← Finset.sum_fiberwise univ (pushMatch φ hrow hcol)]
    refine Finset.sum_congr rfl fun M' _ => ?_
    rw [Finset.sum_congr rfl fun M hM => by rw [(Finset.mem_filter.1 hM).2], ← Finset.sum_mul]
    rfl
  have h2 : ∑ M, μ M * ∑ u, log (relabelProb φ x (M.1 u)) =
      ∑ e, x e * log (relabelProb φ x e) := by
    rw [sum_mul_sum_edge (row := row) (col := col) μ (fun e => log (relabelProb φ x e)),
      hμ.2.2]
  have hcross : ∑ M, -(μ M * log (κ M)) =
      -∑ M', ν M' * log (ν M') - ∑ e, x e * log (relabelProb φ x e) := by
    rw [Finset.sum_neg_distrib, Finset.sum_congr rfl fun M _ => hlogκ M, Finset.sum_add_distrib,
      h1, h2]
    ring
  unfold coreLawEntropy relabelEntropy
  simp only [Finset.sum_neg_distrib] at hsum hcross ⊢
  linarith

/-- Edge entropy drops by `C` under merging. -/
theorem edgeEntropy_mergeFlow {x : E → ℝ} (hx : ∀ e, 0 ≤ x e) :
    edgeEntropy x = edgeEntropy (mergeFlow φ x) + relabelEntropy φ x := by
  classical
  have hterm : ∀ e, x e * log (x e) =
      x e * log (relabelProb φ x e) + x e * log (mergeFlow φ x (φ e)) := by
    intro e
    rcases (hx e).lt_or_eq with he | he
    · have h' := lt_of_lt_of_le he (mergeFlow_ge φ hx e)
      unfold relabelProb
      rw [Real.log_div (ne_of_gt he) (ne_of_gt h')]
      ring
    · rw [← he]; simp
  have hgroup : ∑ e, x e * log (mergeFlow φ x (φ e)) =
      ∑ e', mergeFlow φ x e' * log (mergeFlow φ x e') := by
    rw [← Finset.sum_fiberwise univ φ]
    refine Finset.sum_congr rfl fun e' _ => ?_
    rw [Finset.sum_congr rfl fun e he => by rw [(Finset.mem_filter.1 he).2], ← Finset.sum_mul]
    rfl
  unfold edgeEntropy relabelEntropy
  rw [Finset.sum_congr rfl fun e _ => hterm e, Finset.sum_add_distrib, hgroup]
  ring

include hrow hcol in
/-- `Ent*` drops by `C` under merging. -/
theorem coreMaxEntropy_mergeFlow {x : E → ℝ} {μ₀ : LMatch row col → ℝ}
    (hμ₀ : IsCoreLaw row col x μ₀) :
    coreMaxEntropy row col x = coreMaxEntropy row' col' (mergeFlow φ x) + relabelEntropy φ x := by
  have hx : ∀ e, 0 ≤ x e := hμ₀.nonneg_edge
  have hne : (coreLawEntropy row col '' {μ | IsCoreLaw row col x μ}).Nonempty :=
    ⟨_, μ₀, hμ₀, rfl⟩
  have hne' : (coreLawEntropy row' col' '' {ν | IsCoreLaw row' col' (mergeFlow φ x) ν}).Nonempty :=
    ⟨_, _, isCoreLaw_pushLaw φ hrow hcol hμ₀, rfl⟩
  apply le_antisymm
  · refine csSup_le hne ?_
    rintro _ ⟨μ, hμ, rfl⟩
    have := coreLawEntropy_le_pushLaw φ hrow hcol hμ
    have h' : coreLawEntropy row' col' (pushLaw φ hrow hcol μ) ≤
        coreMaxEntropy row' col' (mergeFlow φ x) :=
      le_csSup (bddAbove_coreLawEntropy _) ⟨_, isCoreLaw_pushLaw φ hrow hcol hμ, rfl⟩
    linarith
  · have : coreMaxEntropy row' col' (mergeFlow φ x) ≤
        coreMaxEntropy row col x - relabelEntropy φ x := by
      refine csSup_le hne' ?_
      rintro _ ⟨ν, hν, rfl⟩
      have h1 := coreLawEntropy_liftLaw φ hrow hcol hx hν
      have h2 : coreLawEntropy row col (liftLaw φ hrow hcol x ν) ≤ coreMaxEntropy row col x :=
        le_csSup (bddAbove_coreLawEntropy _) ⟨_, isCoreLaw_liftLaw φ hrow hcol hx hν, rfl⟩
      linarith
    linarith

include hrow hcol in
/-- **Lavi Lemma 3.2 (aggregation of parallel occurrences).**  Merging edges
along any endpoint-preserving map `φ` leaves the core functional unchanged:
`F_H(x) = F_{H'}(x')` with `x'_{e'} = ∑_{φ e = e'} x_e`.  (Lavi states it
for one bundle at a time; a general `φ` merges any collection at once.) -/
theorem lavi_lemma_3_2 {x : E → ℝ} (hlaw : ∃ μ, IsCoreLaw row col x μ) :
    coreFunctional row col x = coreFunctional row' col' (mergeFlow φ x) := by
  obtain ⟨μ₀, hμ₀⟩ := hlaw
  unfold coreFunctional
  rw [coreMaxEntropy_mergeFlow φ hrow hcol hμ₀, edgeEntropy_mergeFlow φ hμ₀.nonneg_edge]
  ring

end Aggregation

section Bridge

variable {n : ℕ} {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
  (eR : Fin n ≃ U) (eC : Fin n ≃ V)

/-- Labelled matchings of the complete simple core on `U × V` are permutations. -/
noncomputable def completeMatchEquiv : LMatch (Prod.fst : U × V → U) Prod.snd ≃ Perm (Fin n) where
  toFun M := eR.trans ((Equiv.ofBijective _ M.2.2).trans eC.symm)
  invFun σ := ⟨fun u => (u, eC (σ (eR.symm u))), fun _ => rfl,
    (eR.symm.trans (σ.trans eC)).bijective⟩
  left_inv M := by
    apply Subtype.ext
    funext u
    simp only [Equiv.trans_apply, Equiv.ofBijective_apply, Equiv.apply_symm_apply]
    exact Prod.ext (M.2.1 u).symm rfl
  right_inv σ := by
    ext i
    simp

theorem completeMatchEquiv_apply (M : LMatch (Prod.fst : U × V → U) Prod.snd) (i : Fin n) :
    completeMatchEquiv eR eC M i = eC.symm (M.1 (eR i)).2 := rfl

/-- The law sets of the complete core and of the matrix agree. -/
theorem isCoreLaw_complete_iff (y : U × V → ℝ) (μ : LMatch (Prod.fst : U × V → U) Prod.snd → ℝ) :
    IsCoreLaw Prod.fst Prod.snd y μ ↔
      IsLaw (fun i j => y (eR i, eC j)) (μ ∘ (completeMatchEquiv eR eC).symm) := by
  classical
  set Ψ := completeMatchEquiv eR eC
  have hmarg : ∀ i j, marginal (μ ∘ Ψ.symm) i j =
      coreMarginal Prod.fst Prod.snd μ (eR i, eC j) := by
    intro i j
    unfold marginal coreMarginal
    rw [Finset.sum_filter, Finset.sum_filter,
      ← Equiv.sum_comp Ψ (fun σ => if σ i = j then (μ ∘ Ψ.symm) σ else 0)]
    refine Finset.sum_congr rfl fun M _ => ?_
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
    congr 1
    apply propext
    rw [completeMatchEquiv_apply]
    constructor
    · intro h
      exact Prod.ext (M.2.1 _) (by rw [← h]; simp)
    · intro h
      rw [h]; simp
  have hsum : ∑ σ, (μ ∘ Ψ.symm) σ = ∑ M, μ M := Equiv.sum_comp Ψ.symm μ
  constructor
  · rintro ⟨hnn, h1, hm⟩
    refine ⟨fun σ => hnn _, by rw [hsum, h1], ?_⟩
    funext i j
    rw [hmarg, hm]
  · rintro ⟨hnn, h1, hm⟩
    refine ⟨fun M => by simpa using hnn (Ψ M), by rw [← hsum, h1], ?_⟩
    funext p
    obtain ⟨u, v⟩ := p
    have := congrFun (congrFun hm (eR.symm u)) (eC.symm v)
    rw [hmarg] at this
    simpa using this

/-- **Bridge.**  The core functional of the complete simple core is Lavi's
matrix functional `F`. -/
theorem coreFunctional_complete (y : U × V → ℝ) :
    coreFunctional Prod.fst Prod.snd y = faceFunctional (fun i j => y (eR i, eC j)) := by
  classical
  set Ψ := completeMatchEquiv eR eC
  have hset : coreLawEntropy Prod.fst Prod.snd '' {μ | IsCoreLaw Prod.fst Prod.snd y μ} =
      lawEntropy '' {ν | IsLaw (fun i j => y (eR i, eC j)) ν} := by
    ext t
    constructor
    · rintro ⟨μ, hμ, rfl⟩
      refine ⟨μ ∘ Ψ.symm, (isCoreLaw_complete_iff eR eC y μ).1 hμ, ?_⟩
      unfold lawEntropy coreLawEntropy
      exact Equiv.sum_comp Ψ.symm (fun M => -(μ M * log (μ M)))
    · rintro ⟨ν, hν, rfl⟩
      have hcomp : (ν ∘ Ψ) ∘ Ψ.symm = ν :=
        funext fun σ => by simp only [Function.comp_apply, Equiv.apply_symm_apply]
      refine ⟨ν ∘ Ψ, (isCoreLaw_complete_iff eR eC y (ν ∘ Ψ)).2 (by rw [hcomp]; exact hν), ?_⟩
      unfold lawEntropy coreLawEntropy
      exact Equiv.sum_comp Ψ (fun σ => -(ν σ * log (ν σ)))
  have hent : edgeEntropy y = rowEntropy (fun i j => y (eR i, eC j)) := by
    unfold edgeEntropy rowEntropy
    rw [Fintype.sum_prod_type, ← Equiv.sum_comp eR]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (Equiv.sum_comp eC (fun v => y (eR i, v) * log (y (eR i, v)))).symm
  unfold coreFunctional faceFunctional coreMaxEntropy maxMatchingEntropy
  rw [hset, hent]

end Bridge

section Aggregate

variable {n : ℕ} {U V E : Type*} [Fintype U] [Fintype V] [Fintype E]
  [DecidableEq U] [DecidableEq V] [DecidableEq E] {row : E → U} {col : E → V}

/-- The aggregated matrix of a core flow, in coordinates `eR`, `eC`:
`X̄_ij = ∑_{row e = eR i, col e = eC j} x_e`. -/
def aggregateMatrix (row : E → U) (col : E → V) (eR : Fin n ≃ U) (eC : Fin n ≃ V)
    (x : E → ℝ) : Square n :=
  fun i j => mergeFlow (fun e => (row e, col e)) x (eR i, eC j)

/-- **Lemma 3.2, matrix form.**  The core functional of `H` equals Lavi's
matrix functional of the aggregated flow matrix. -/
theorem coreFunctional_eq_faceFunctional (eR : Fin n ≃ U) (eC : Fin n ≃ V) {x : E → ℝ}
    (hlaw : ∃ μ, IsCoreLaw row col x μ) :
    coreFunctional row col x = faceFunctional (aggregateMatrix row col eR eC x) := by
  rw [lavi_lemma_3_2 (row' := Prod.fst) (col' := Prod.snd) (fun e => (row e, col e))
    (fun _ => rfl) (fun _ => rfl) hlaw]
  exact coreFunctional_complete eR eC _

end Aggregate

end LaviSection2
