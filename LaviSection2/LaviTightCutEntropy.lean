import LaviSection2.LaviTightCut

/-!
# Lavi Lemma 4.1, entropy part: `F_H = F_{H₁} + F_{H₂}` across a tight cut

Let `x` be a feasible parent flow.  The inherited factor flows keep `x_e` on
every occurrence of the factor (a crossing label `e` keeps `x_e` at either
marker).  Write `Ent(q) = -∑_{e crossing} x_e log x_e` for the entropy of the
crossing-label distribution.

* Projection: any parent law `μ` projects to factor laws `ν₁, ν₂` with the
  inherited marginals, and the finite Gibbs inequality against the glued law
  `ν₁(M₁) ν₂(M₂) / x_{label}` gives `Ent(μ) ≤ Ent(ν₁) + Ent(ν₂) - Ent(q)`.
* Gluing: for any factor laws with the inherited marginals, the glued law is a
  parent law with marginals `x` and entropy exactly
  `Ent(ν₁) + Ent(ν₂) - Ent(q)`.

Hence `Ent*_H + Ent(q) = Ent*_{H₁} + Ent*_{H₂}`.  The factor edge entropies
count every crossing occurrence twice, so they exceed the parent edge entropy
by exactly `Ent(q)`, and (4.2) follows.  As in Section 3, no conditional
entropy or chain rule is needed.
-/

set_option linter.unusedSectionVars false

namespace LaviSection2

open Finset Equiv Real

open scoped BigOperators

/-- Marginals as sums of indicator products. -/
theorem coreMarginal_eq_sum_mul_ite {U V E : Type*} [Fintype U] [Fintype V] [Fintype E]
    [DecidableEq U] [DecidableEq V] [DecidableEq E] (row : E → U) (col : E → V)
    (μ : LMatch row col → ℝ) (e : E) :
    coreMarginal row col μ e = ∑ M, μ M * if M.1 (row e) = e then 1 else 0 := by
  unfold coreMarginal
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun M _ => ?_
  split_ifs <;> simp

section TightCutEntropy

variable {U V E : Type*} [Fintype U] [Fintype V] [Fintype E]
  [DecidableEq U] [DecidableEq V] [DecidableEq E]
  {row : E → U} {col : E → V} (K : ShoreCut row col)

namespace ShoreCut

/-- The flow inherited by `H₁`. -/
def flow₁ (x : E → ℝ) (e : K.E₁) : ℝ := x e.1

/-- The flow inherited by `H₂`. -/
def flow₂ (x : E → ℝ) (e : K.E₂) : ℝ := x e.1

/-- Projection of a parent law to `H₁`. -/
def push₁ (μ : LMatch row col → ℝ) (M₁ : LMatch K.row₁ K.col₁) : ℝ :=
  ∑ M ∈ (univ : Finset (LMatch row col)).filter (fun M => K.proj₁ M = M₁), μ M

/-- Projection of a parent law to `H₂`. -/
noncomputable def push₂ (μ : LMatch row col → ℝ) (M₂ : LMatch K.row₂ K.col₂) : ℝ :=
  ∑ M ∈ (univ : Finset (LMatch row col)).filter (fun M => K.proj₂ M = M₂), μ M

/-- The entropy of the crossing-label distribution, `Ent(q)`. -/
noncomputable def crossEntropy (x : E → ℝ) : ℝ :=
  -∑ c ∈ (univ : Finset E).filter K.Crossing, x c * log (x c)

theorem proj₁_apply_iff (M : LMatch row col) (e : K.E₁) :
    (K.proj₁ M).1 (K.row₁ e) = e ↔ M.1 (row e.1) = e.1 :=
  ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem proj₂_apply_iff (M : LMatch row col) (e : K.E₂) :
    (K.proj₂ M).1 (K.row₂ e) = e ↔ M.1 (row e.1) = e.1 := by
  by_cases h : K.sR (row e.1)
  · have hc : K.Crossing e.1 := ⟨h, e.2⟩
    rw [K.row₂_of_sR h]
    have key := K.label₁_eq_iff (K.proj₁ M) hc
    constructor
    · intro h'
      have hl : K.label₁ (K.proj₁ M) = e.1 := congrArg Subtype.val h'
      exact (K.proj₁_apply_iff M ⟨e.1, h⟩).1 (key.1 hl)
    · intro h'
      exact Subtype.ext (key.2 ((K.proj₁_apply_iff M ⟨e.1, h⟩).2 h'))
  · rw [K.row₂_of_not_sR h]
    exact ⟨fun h' => congrArg Subtype.val h', fun h' => Subtype.ext h'⟩

/-! ### Projected laws -/

theorem coreMarginal_push₁ (μ : LMatch row col → ℝ) (e : K.E₁) :
    coreMarginal K.row₁ K.col₁ (K.push₁ μ) e = coreMarginal row col μ e.1 := by
  unfold coreMarginal push₁
  rw [sum_filter_fibers K.proj₁ (fun M₁ => M₁.1 (K.row₁ e) = e) μ]
  exact Finset.sum_congr (Finset.filter_congr fun M _ => K.proj₁_apply_iff M e) fun _ _ => rfl

theorem coreMarginal_push₂ (μ : LMatch row col → ℝ) (e : K.E₂) :
    coreMarginal K.row₂ K.col₂ (K.push₂ μ) e = coreMarginal row col μ e.1 := by
  unfold coreMarginal push₂
  rw [sum_filter_fibers K.proj₂ (fun M₂ => M₂.1 (K.row₂ e) = e) μ]
  exact Finset.sum_congr (Finset.filter_congr fun M _ => K.proj₂_apply_iff M e) fun _ _ => rfl

/-- A parent law projects to a law on `H₁` with the inherited marginals. -/
theorem isCoreLaw_push₁ {x : E → ℝ} {μ : LMatch row col → ℝ} (h : IsCoreLaw row col x μ) :
    IsCoreLaw K.row₁ K.col₁ (K.flow₁ x) (K.push₁ μ) :=
  ⟨fun _ => Finset.sum_nonneg fun M _ => h.1 M,
    by unfold push₁; rw [Finset.sum_fiberwise univ K.proj₁ μ, h.2.1],
    funext fun e => by rw [coreMarginal_push₁, h.2.2]; rfl⟩

/-- A parent law projects to a law on `H₂` with the inherited marginals. -/
theorem isCoreLaw_push₂ {x : E → ℝ} {μ : LMatch row col → ℝ} (h : IsCoreLaw row col x μ) :
    IsCoreLaw K.row₂ K.col₂ (K.flow₂ x) (K.push₂ μ) :=
  ⟨fun _ => Finset.sum_nonneg fun M _ => h.1 M,
    by unfold push₂; rw [Finset.sum_fiberwise univ K.proj₂ μ, h.2.1],
    funext fun e => by rw [coreMarginal_push₂, h.2.2]; rfl⟩

theorem sum_mul_proj₁ (μ : LMatch row col → ℝ) (f : LMatch K.row₁ K.col₁ → ℝ) :
    ∑ M, μ M * f (K.proj₁ M) = ∑ M₁, K.push₁ μ M₁ * f M₁ := by
  rw [← Finset.sum_fiberwise univ K.proj₁ (fun M => μ M * f (K.proj₁ M))]
  refine Finset.sum_congr rfl fun M₁ _ => ?_
  unfold push₁
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun M hM => by rw [(Finset.mem_filter.1 hM).2]

theorem sum_mul_proj₂ (μ : LMatch row col → ℝ) (f : LMatch K.row₂ K.col₂ → ℝ) :
    ∑ M, μ M * f (K.proj₂ M) = ∑ M₂, K.push₂ μ M₂ * f M₂ := by
  rw [← Finset.sum_fiberwise univ K.proj₂ (fun M => μ M * f (K.proj₂ M))]
  refine Finset.sum_congr rfl fun M₂ _ => ?_
  unfold push₂
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun M hM => by rw [(Finset.mem_filter.1 hM).2]

/-! ### Label distributions of factor laws -/

theorem sum_label₁ {x : E → ℝ} {ν₁ : LMatch K.row₁ K.col₁ → ℝ}
    (hν : IsCoreLaw K.row₁ K.col₁ (K.flow₁ x) ν₁) {c : E} (hc : K.Crossing c) :
    ∑ M₁ ∈ (univ : Finset _).filter (fun M₁ => K.label₁ M₁ = c), ν₁ M₁ = x c :=
  calc _ = coreMarginal K.row₁ K.col₁ ν₁ ⟨c, hc.1⟩ := by
        unfold coreMarginal
        exact Finset.sum_congr (Finset.filter_congr fun M₁ _ => K.label₁_eq_iff M₁ hc)
          fun _ _ => rfl
    _ = x c := congrFun hν.2.2 _

theorem sum_label₂ {x : E → ℝ} {ν₂ : LMatch K.row₂ K.col₂ → ℝ}
    (hν : IsCoreLaw K.row₂ K.col₂ (K.flow₂ x) ν₂) {c : E} (hc : K.Crossing c) :
    ∑ M₂ ∈ (univ : Finset _).filter (fun M₂ => K.label₂ M₂ = c), ν₂ M₂ = x c :=
  calc _ = coreMarginal K.row₂ K.col₂ ν₂ ⟨c, hc.2⟩ := by
        unfold coreMarginal
        exact Finset.sum_congr (Finset.filter_congr fun M₂ _ => K.label₂_eq_iff M₂ hc)
          fun _ _ => rfl
    _ = x c := congrFun hν.2.2 _

/-- Expectations of functions of the label. -/
theorem sum_mul_label₁ {x : E → ℝ} {ν₁ : LMatch K.row₁ K.col₁ → ℝ}
    (hν : IsCoreLaw K.row₁ K.col₁ (K.flow₁ x) ν₁) (g : E → ℝ) :
    ∑ M₁, ν₁ M₁ * g (K.label₁ M₁) = ∑ c ∈ (univ : Finset E).filter K.Crossing, x c * g c := by
  rw [← Finset.sum_fiberwise univ K.label₁ (fun M₁ => ν₁ M₁ * g (K.label₁ M₁)),
    ← Finset.sum_filter_add_sum_filter_not univ K.Crossing]
  have hzero : ∑ c ∈ (univ : Finset E).filter (fun c => ¬ K.Crossing c),
      ∑ M₁ ∈ (univ : Finset _).filter (fun M₁ => K.label₁ M₁ = c), ν₁ M₁ * g (K.label₁ M₁) =
      0 := by
    refine Finset.sum_eq_zero fun c hc => Finset.sum_eq_zero fun M₁ hM => ?_
    have h1 := K.label₁_crossing M₁
    rw [(Finset.mem_filter.1 hM).2] at h1
    exact absurd h1 (Finset.mem_filter.1 hc).2
  rw [hzero, add_zero]
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [Finset.sum_congr rfl fun M₁ hM => by rw [(Finset.mem_filter.1 hM).2], ← Finset.sum_mul,
    K.sum_label₁ hν (Finset.mem_filter.1 hc).2]

/-! ### The glued law -/

/-- Glue two factor laws independently, conditional on the common label. -/
noncomputable def glueLaw (x : E → ℝ) (ν₁ : LMatch K.row₁ K.col₁ → ℝ)
    (ν₂ : LMatch K.row₂ K.col₂ → ℝ) (M : LMatch row col) : ℝ :=
  ν₁ (K.proj₁ M) * ν₂ (K.proj₂ M) / x (K.label M)

variable {K}

theorem sum_glueLaw_mul₁ {x : E → ℝ} {ν₁ : LMatch K.row₁ K.col₁ → ℝ}
    {ν₂ : LMatch K.row₂ K.col₂ → ℝ} (h₁ : IsCoreLaw K.row₁ K.col₁ (K.flow₁ x) ν₁)
    (h₂ : IsCoreLaw K.row₂ K.col₂ (K.flow₂ x) ν₂) (f : LMatch K.row₁ K.col₁ → ℝ) :
    ∑ M, K.glueLaw x ν₁ ν₂ M * f (K.proj₁ M) = ∑ M₁, ν₁ M₁ * f M₁ := by
  unfold glueLaw label
  rw [K.sum_lmatch_eq_sum_pairs (fun M₁ M₂ => ν₁ M₁ * ν₂ M₂ / x (K.label₁ M₁) * f M₁)]
  refine Finset.sum_congr rfl fun M₁ _ => ?_
  rw [← Finset.sum_mul, ← Finset.sum_div, ← Finset.mul_sum,
    K.sum_label₂ h₂ (K.label₁_crossing M₁)]
  by_cases hx : x (K.label₁ M₁) = 0
  · have hle : ν₁ M₁ ≤ x (K.label₁ M₁) := h₁.le_edge M₁ (K.markRow₁ M₁)
    have : ν₁ M₁ = 0 := le_antisymm (by rw [hx] at hle; exact hle) (h₁.1 M₁)
    simp [this]
  · rw [mul_div_assoc, div_self hx, mul_one]

theorem sum_glueLaw_mul₂ {x : E → ℝ} {ν₁ : LMatch K.row₁ K.col₁ → ℝ}
    {ν₂ : LMatch K.row₂ K.col₂ → ℝ} (h₁ : IsCoreLaw K.row₁ K.col₁ (K.flow₁ x) ν₁)
    (h₂ : IsCoreLaw K.row₂ K.col₂ (K.flow₂ x) ν₂) (f : LMatch K.row₂ K.col₂ → ℝ) :
    ∑ M, K.glueLaw x ν₁ ν₂ M * f (K.proj₂ M) = ∑ M₂, ν₂ M₂ * f M₂ := by
  unfold glueLaw label
  rw [K.sum_lmatch_eq_sum_pairs' (fun M₁ M₂ => ν₁ M₁ * ν₂ M₂ / x (K.label₁ M₁) * f M₂)]
  refine Finset.sum_congr rfl fun M₂ _ => ?_
  rw [Finset.sum_congr rfl fun M₁ hM => by rw [(Finset.mem_filter.1 hM).2]]
  rw [← Finset.sum_mul, ← Finset.sum_div,
    show ∑ M₁ ∈ (univ : Finset _).filter (fun M₁ => K.label₁ M₁ = K.label₂ M₂), ν₁ M₁ * ν₂ M₂ =
      (∑ M₁ ∈ (univ : Finset _).filter (fun M₁ => K.label₁ M₁ = K.label₂ M₂), ν₁ M₁) * ν₂ M₂
      from (Finset.sum_mul _ _ _).symm,
    K.sum_label₁ h₁ (K.label₂_crossing M₂)]
  by_cases hx : x (K.label₂ M₂) = 0
  · have hle : ν₂ M₂ ≤ x (K.label₂ M₂) := h₂.le_edge M₂ (Sum.inl ())
    have : ν₂ M₂ = 0 := le_antisymm (by rw [hx] at hle; exact hle) (h₂.1 M₂)
    simp [this]
  · rw [mul_comm (x _), mul_div_assoc, div_self hx, mul_one]

/-- The glued law is a parent law with marginals `x`. -/
theorem isCoreLaw_glueLaw {x : E → ℝ} {ν₁ : LMatch K.row₁ K.col₁ → ℝ}
    {ν₂ : LMatch K.row₂ K.col₂ → ℝ} (h₁ : IsCoreLaw K.row₁ K.col₁ (K.flow₁ x) ν₁)
    (h₂ : IsCoreLaw K.row₂ K.col₂ (K.flow₂ x) ν₂) :
    IsCoreLaw row col x (K.glueLaw x ν₁ ν₂) := by
  refine ⟨fun M => ?_, ?_, ?_⟩
  · have hx : 0 ≤ x (K.label M) :=
      h₁.nonneg_edge ⟨K.label M, (K.label₁_crossing _).1⟩
    exact div_nonneg (mul_nonneg (h₁.1 _) (h₂.1 _)) hx
  · have := sum_glueLaw_mul₁ h₁ h₂ (fun _ => 1)
    simp only [mul_one] at this
    rw [this, h₁.2.1]
  · funext e
    rw [coreMarginal_eq_sum_mul_ite]
    by_cases hs : K.sR (row e)
    · calc _ = ∑ M, K.glueLaw x ν₁ ν₂ M *
              (fun M₁ : LMatch K.row₁ K.col₁ =>
                if M₁.1 (K.row₁ ⟨e, hs⟩) = ⟨e, hs⟩ then (1 : ℝ) else 0) (K.proj₁ M) := by
            refine Finset.sum_congr rfl fun M _ => ?_
            simp only [K.proj₁_apply_iff M ⟨e, hs⟩]
        _ = coreMarginal K.row₁ K.col₁ ν₁ ⟨e, hs⟩ := by
            exact (sum_glueLaw_mul₁ h₁ h₂ (fun M₁ => if M₁.1 (K.row₁ ⟨e, hs⟩) = ⟨e, hs⟩
              then (1 : ℝ) else 0)).trans (coreMarginal_eq_sum_mul_ite _ _ _ _).symm
        _ = x e := congrFun h₁.2.2 _
    · have hc : ¬ K.sC (col e) := fun h => hs (K.back e h)
      calc _ = ∑ M, K.glueLaw x ν₁ ν₂ M *
              (fun M₂ : LMatch K.row₂ K.col₂ =>
                if M₂.1 (K.row₂ ⟨e, hc⟩) = ⟨e, hc⟩ then (1 : ℝ) else 0) (K.proj₂ M) := by
            refine Finset.sum_congr rfl fun M _ => ?_
            simp only [K.proj₂_apply_iff M ⟨e, hc⟩]
        _ = coreMarginal K.row₂ K.col₂ ν₂ ⟨e, hc⟩ := by
            exact (sum_glueLaw_mul₂ h₁ h₂ (fun M₂ => if M₂.1 (K.row₂ ⟨e, hc⟩) = ⟨e, hc⟩
              then (1 : ℝ) else 0)).trans (coreMarginal_eq_sum_mul_ite _ _ _ _).symm
        _ = x e := congrFun h₂.2.2 _

/-- The glued law has entropy `Ent(ν₁) + Ent(ν₂) - Ent(q)`. -/
theorem coreLawEntropy_glueLaw {x : E → ℝ} {ν₁ : LMatch K.row₁ K.col₁ → ℝ}
    {ν₂ : LMatch K.row₂ K.col₂ → ℝ} (h₁ : IsCoreLaw K.row₁ K.col₁ (K.flow₁ x) ν₁)
    (h₂ : IsCoreLaw K.row₂ K.col₂ (K.flow₂ x) ν₂) :
    coreLawEntropy row col (K.glueLaw x ν₁ ν₂) =
      coreLawEntropy K.row₁ K.col₁ ν₁ + coreLawEntropy K.row₂ K.col₂ ν₂ - K.crossEntropy x := by
  set κ := K.glueLaw x ν₁ ν₂ with hκ
  have hterm : ∀ M, κ M * log (κ M) = κ M * log (ν₁ (K.proj₁ M)) +
      κ M * log (ν₂ (K.proj₂ M)) - κ M * log (x (K.label₁ (K.proj₁ M))) := by
    intro M
    by_cases h0 : κ M = 0
    · simp [h0]
    · have ha : ν₁ (K.proj₁ M) ≠ 0 := fun h => h0 (by simp [hκ, glueLaw, h])
      have hb : ν₂ (K.proj₂ M) ≠ 0 := fun h => h0 (by simp [hκ, glueLaw, h])
      have hc : x (K.label M) ≠ 0 := fun h => h0 (by simp [hκ, glueLaw, h])
      show κ M * log (ν₁ (K.proj₁ M) * ν₂ (K.proj₂ M) / x (K.label M)) = _
      rw [Real.log_div (mul_ne_zero ha hb) hc, Real.log_mul ha hb]
      simp only [label]
      ring
  have hA := sum_glueLaw_mul₁ h₁ h₂ (fun M₁ => log (ν₁ M₁))
  have hB := sum_glueLaw_mul₂ h₁ h₂ (fun M₂ => log (ν₂ M₂))
  have hC := sum_glueLaw_mul₁ h₁ h₂ (fun M₁ => log (x (K.label₁ M₁)))
  rw [K.sum_mul_label₁ h₁ (fun c => log (x c))] at hC
  unfold coreLawEntropy crossEntropy
  simp only [Finset.sum_neg_distrib]
  rw [Finset.sum_congr rfl fun M _ => hterm M, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [← hκ] at hA hB hC
  rw [hA, hB, hC]
  ring

/-- Gibbs comparison: `Ent(μ) ≤ Ent(ν₁) + Ent(ν₂) - Ent(q)` for the projections. -/
theorem coreLawEntropy_le_push {x : E → ℝ} {μ : LMatch row col → ℝ}
    (hμ : IsCoreLaw row col x μ) :
    coreLawEntropy row col μ ≤ coreLawEntropy K.row₁ K.col₁ (K.push₁ μ) +
      coreLawEntropy K.row₂ K.col₂ (K.push₂ μ) - K.crossEntropy x := by
  have h₁ := K.isCoreLaw_push₁ hμ
  have h₂ := K.isCoreLaw_push₂ hμ
  set ν₁ := K.push₁ μ with hν₁
  set ν₂ := K.push₂ μ with hν₂
  set κ := K.glueLaw x ν₁ ν₂ with hκ
  have hκlaw := isCoreLaw_glueLaw h₁ h₂
  have hge₁ : ∀ M, μ M ≤ ν₁ (K.proj₁ M) := fun M =>
    Finset.single_le_sum (f := μ) (fun N _ => hμ.1 N) (Finset.mem_filter.2 ⟨mem_univ _, rfl⟩)
  have hge₂ : ∀ M, μ M ≤ ν₂ (K.proj₂ M) := fun M =>
    Finset.single_le_sum (f := μ) (fun N _ => hμ.1 N) (Finset.mem_filter.2 ⟨mem_univ _, rfl⟩)
  have hge₃ : ∀ M, μ M ≤ x (K.label M) := fun M => by
    rw [K.label_eq]; exact hμ.le_edge M _
  have hlogκ : ∀ M, μ M * log (κ M) = μ M * log (ν₁ (K.proj₁ M)) +
      μ M * log (ν₂ (K.proj₂ M)) - μ M * log (x (K.label₁ (K.proj₁ M))) := by
    intro M
    rcases (hμ.1 M).lt_or_eq with hM | hM
    · have ha := ne_of_gt (lt_of_lt_of_le hM (hge₁ M))
      have hb := ne_of_gt (lt_of_lt_of_le hM (hge₂ M))
      have hc := ne_of_gt (lt_of_lt_of_le hM (hge₃ M))
      show μ M * log (ν₁ (K.proj₁ M) * ν₂ (K.proj₂ M) / x (K.label M)) = _
      rw [Real.log_div (mul_ne_zero ha hb) hc, Real.log_mul ha hb]
      simp only [label]
      ring
    · rw [← hM]; simp
  have hgibbs : ∀ M, -(μ M * log (μ M)) ≤ -(μ M * log (κ M)) + κ M - μ M := by
    intro M
    rcases (hμ.1 M).lt_or_eq with hM | hM
    · have hk : 0 < κ M := div_pos (mul_pos (lt_of_lt_of_le hM (hge₁ M))
        (lt_of_lt_of_le hM (hge₂ M))) (lt_of_lt_of_le hM (hge₃ M))
      have hl := Real.log_le_sub_one_of_pos (div_pos hk hM)
      rw [Real.log_div (ne_of_gt hk) (ne_of_gt hM)] at hl
      have h3 := mul_le_mul_of_nonneg_left hl hM.le
      have h4 : μ M * (κ M / μ M - 1) = κ M - μ M := by field_simp
      nlinarith [h3, h4]
    · rw [← hM]; simpa using hκlaw.1 M
  have hsum := Finset.sum_le_sum fun M (_ : M ∈ univ) => hgibbs M
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hκlaw.2.1, hμ.2.1] at hsum
  have hA := K.sum_mul_proj₁ μ (fun M₁ => log (ν₁ M₁))
  have hB := K.sum_mul_proj₂ μ (fun M₂ => log (ν₂ M₂))
  have hC := K.sum_mul_proj₁ μ (fun M₁ => log (x (K.label₁ M₁)))
  rw [K.sum_mul_label₁ h₁ (fun c => log (x c))] at hC
  rw [← hν₁] at hA
  rw [← hν₂] at hB
  have hcross : ∑ M, -(μ M * log (κ M)) =
      -(∑ M₁, ν₁ M₁ * log (ν₁ M₁)) - (∑ M₂, ν₂ M₂ * log (ν₂ M₂)) +
        ∑ c ∈ (univ : Finset E).filter K.Crossing, x c * log (x c) := by
    rw [Finset.sum_neg_distrib, Finset.sum_congr rfl fun M _ => hlogκ M, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, hA, hB, hC]
    ring
  unfold coreLawEntropy crossEntropy
  simp only [Finset.sum_neg_distrib] at hsum hcross ⊢
  linarith

/-! ### Edge entropy and Lemma 4.1 -/

/-- The factor edge entropies count crossing occurrences twice. -/
theorem edgeEntropy_cut (x : E → ℝ) :
    edgeEntropy (K.flow₁ x) + edgeEntropy (K.flow₂ x) = edgeEntropy x + K.crossEntropy x := by
  set g : E → ℝ := fun e => x e * log (x e)
  have h₁ : ∑ e : K.E₁, K.flow₁ x e * log (K.flow₁ x e) =
      ∑ e ∈ (univ : Finset E).filter (fun e => K.sR (row e)), g e :=
    (Finset.sum_subtype _ (fun e => by simp) g).symm
  have h₂ : ∑ e : K.E₂, K.flow₂ x e * log (K.flow₂ x e) =
      ∑ e ∈ (univ : Finset E).filter (fun e => ¬ K.sC (col e)), g e :=
    (Finset.sum_subtype _ (fun e => by simp) g).symm
  have key : ∀ e, ((if K.sR (row e) then g e else 0) + if ¬ K.sC (col e) then g e else 0) =
      g e + if K.Crossing e then g e else 0 := by
    intro e
    by_cases h1 : K.sR (row e)
    · by_cases h2 : K.sC (col e) <;> simp [Crossing, h1, h2]
    · have h2 : ¬ K.sC (col e) := fun h => h1 (K.back e h)
      simp [Crossing, h1, h2]
  unfold edgeEntropy crossEntropy
  rw [h₁, h₂]
  simp only [Finset.sum_filter]
  rw [← neg_add, ← Finset.sum_add_distrib, Finset.sum_congr rfl fun e _ => key e,
    Finset.sum_add_distrib]
  ring

/-- `Ent*_H + Ent(q) = Ent*_{H₁} + Ent*_{H₂}` at inherited marginals. -/
theorem coreMaxEntropy_cut {x : E → ℝ} {μ₀ : LMatch row col → ℝ}
    (hμ₀ : IsCoreLaw row col x μ₀) :
    coreMaxEntropy row col x + K.crossEntropy x =
      coreMaxEntropy K.row₁ K.col₁ (K.flow₁ x) + coreMaxEntropy K.row₂ K.col₂ (K.flow₂ x) := by
  have hne : (coreLawEntropy row col '' {μ | IsCoreLaw row col x μ}).Nonempty :=
    ⟨_, μ₀, hμ₀, rfl⟩
  have hne₁ : (coreLawEntropy K.row₁ K.col₁ ''
      {ν | IsCoreLaw K.row₁ K.col₁ (K.flow₁ x) ν}).Nonempty :=
    ⟨_, _, K.isCoreLaw_push₁ hμ₀, rfl⟩
  have hne₂ : (coreLawEntropy K.row₂ K.col₂ ''
      {ν | IsCoreLaw K.row₂ K.col₂ (K.flow₂ x) ν}).Nonempty :=
    ⟨_, _, K.isCoreLaw_push₂ hμ₀, rfl⟩
  have le₁ : ∀ ν, IsCoreLaw K.row₁ K.col₁ (K.flow₁ x) ν →
      coreLawEntropy K.row₁ K.col₁ ν ≤ coreMaxEntropy K.row₁ K.col₁ (K.flow₁ x) :=
    fun ν h => le_csSup (bddAbove_coreLawEntropy _) ⟨ν, h, rfl⟩
  have le₂ : ∀ ν, IsCoreLaw K.row₂ K.col₂ (K.flow₂ x) ν →
      coreLawEntropy K.row₂ K.col₂ ν ≤ coreMaxEntropy K.row₂ K.col₂ (K.flow₂ x) :=
    fun ν h => le_csSup (bddAbove_coreLawEntropy _) ⟨ν, h, rfl⟩
  have le₀ : ∀ μ, IsCoreLaw row col x μ → coreLawEntropy row col μ ≤ coreMaxEntropy row col x :=
    fun μ h => le_csSup (bddAbove_coreLawEntropy _) ⟨μ, h, rfl⟩
  apply le_antisymm
  · have : coreMaxEntropy row col x ≤ coreMaxEntropy K.row₁ K.col₁ (K.flow₁ x) +
        coreMaxEntropy K.row₂ K.col₂ (K.flow₂ x) - K.crossEntropy x := by
      refine csSup_le hne ?_
      rintro _ ⟨μ, hμ, rfl⟩
      have := coreLawEntropy_le_push (K := K) hμ
      linarith [le₁ _ (K.isCoreLaw_push₁ hμ), le₂ _ (K.isCoreLaw_push₂ hμ)]
    linarith
  · -- for every pair of factor laws, the glued law bounds their entropies
    have hpair : ∀ ν₂, IsCoreLaw K.row₂ K.col₂ (K.flow₂ x) ν₂ →
        coreMaxEntropy K.row₁ K.col₁ (K.flow₁ x) ≤
          coreMaxEntropy row col x + K.crossEntropy x - coreLawEntropy K.row₂ K.col₂ ν₂ := by
      intro ν₂ h₂
      refine csSup_le hne₁ ?_
      rintro _ ⟨ν₁, h₁, rfl⟩
      have := coreLawEntropy_glueLaw h₁ h₂
      linarith [le₀ _ (isCoreLaw_glueLaw h₁ h₂)]
    have : coreMaxEntropy K.row₂ K.col₂ (K.flow₂ x) ≤
        coreMaxEntropy row col x + K.crossEntropy x -
          coreMaxEntropy K.row₁ K.col₁ (K.flow₁ x) := by
      refine csSup_le hne₂ ?_
      rintro _ ⟨ν₂, h₂, rfl⟩
      linarith [hpair ν₂ h₂]
    linarith

variable (K)

/-- **Lavi Lemma 4.1, (4.2).**  Across a tight cut, at the factor marginals
inherited from a feasible parent flow, `F_H = F_{H₁} + F_{H₂}`. -/
theorem lavi_lemma_4_1 {x : E → ℝ} (hlaw : ∃ μ, IsCoreLaw row col x μ) :
    coreFunctional row col x =
      coreFunctional K.row₁ K.col₁ (K.flow₁ x) + coreFunctional K.row₂ K.col₂ (K.flow₂ x) := by
  obtain ⟨μ₀, hμ₀⟩ := hlaw
  have h1 := K.coreMaxEntropy_cut hμ₀
  have h2 := K.edgeEntropy_cut x
  unfold coreFunctional
  linarith

end ShoreCut

end TightCutEntropy

end LaviSection2
