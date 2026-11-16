import LaviSection2.LaviMatchingEntropy
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Lavi Lemma 3.1: the face variational identity

For a doubly stochastic `X` in the face `Ω(D)`,

`log per X ≥ F(X) ≥ log min_{Y ∈ Ω(D)} per Y`,

so `min_{Ω(D)} F = log min_{Ω(D)} per`, attained at every face minimizer.

The first inequality is the finite Gibbs inequality
(`lawEntropy_sub_rowEntropy_le`).  For the second, Lavi takes the entropy
maximizer, shows it is positive, applies Lagrange stationarity, and scales the
resulting product weights to a doubly stochastic matrix by the
Sinkhorn–Knopp theorem.  We use a shorter route that needs none of these:

* minimize `Φ(W) = log per W - ∑ x_ij log w_ij` over the doubly stochastic
  matrices supported on `supp X` (it blows up at the boundary, so a minimizer
  `W` is positive on `supp X`);
* perturb `W` in the direction `m - X`, where `m` are the marginals of the
  Gibbs law of `W`.  The derivative is `∑ (m_ij - x_ij)² / w_ij`, so `m = X`;
* hence the Gibbs law of `W` has marginal `X`, and
  `F(X) ≥ Ent(q_W) - ∑ Ent(X_i) = log per W + ∑ x log (x/w) ≥ log per W`.

This is the same squared-sum device as in the cofactor half of Lemma 2.1.
-/

namespace LaviSection2

open Finset Equiv Real Filter Topology

open scoped BigOperators

section Compactness

variable {n : ℕ}

theorem continuous_entry (i j : Fin n) : Continuous fun W : Square n => W i j :=
  continuous_id.matrix_elem i j

theorem continuous_permanent : Continuous (permanent : Square n → ℝ) := by
  unfold permanent
  exact continuous_finsetSum _ fun σ _ =>
    continuous_finsetProd _ fun i _ => continuous_entry i (σ i)

/-- Faces `Ω(D)` are closed. -/
theorem isClosed_inFace (D : Fin n → Fin n → Prop) :
    IsClosed {W : Square n | InFace D W} := by
  classical
  have hset : {W : Square n | InFace D W} =
      (⋂ i, ⋂ j, {W : Square n | 0 ≤ W i j}) ∩ (⋂ i, {W : Square n | ∑ j, W i j = 1}) ∩
        (⋂ j, {W : Square n | ∑ i, W i j = 1}) ∩
          ⋂ i, ⋂ j, {W : Square n | ¬ D i j → W i j = 0} := by
    ext W
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨⟨hnn, hr, hc⟩, hs⟩
      exact ⟨⟨⟨hnn, hr⟩, hc⟩, fun i j hD => by_contra fun h => hD (hs i j h)⟩
    · rintro ⟨⟨⟨hnn, hr⟩, hc⟩, hs⟩
      exact ⟨⟨hnn, hr, hc⟩, fun i j h => by_contra fun hD => h (hs i j hD)⟩
  rw [hset]
  refine ((IsClosed.inter (IsClosed.inter ?_ ?_) ?_)).inter ?_
  · exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_le continuous_const (continuous_entry i j)
  · exact isClosed_iInter fun i => isClosed_eq
      (continuous_finsetSum _ fun j _ => continuous_entry i j) continuous_const
  · exact isClosed_iInter fun j => isClosed_eq
      (continuous_finsetSum _ fun i _ => continuous_entry i j) continuous_const
  · refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
    by_cases hD : D i j
    · simp [hD]
    · simpa [hD] using isClosed_eq (continuous_entry i j) continuous_const

theorem entry_le_one_of_doublyStochastic {W : Square n} (hW : DoublyStochastic W)
    (i j : Fin n) : W i j ≤ 1 := by
  rw [← hW.2.1 i]
  exact Finset.single_le_sum (f := fun k => W i k) (fun k _ => hW.1 i k) (Finset.mem_univ j)

/-- Faces `Ω(D)` are compact. -/
theorem isCompact_inFace (D : Fin n → Fin n → Prop) :
    IsCompact {W : Square n | InFace D W} := by
  have hbox : IsCompact (Set.univ.pi fun _ : Fin n =>
      Set.univ.pi fun _ : Fin n => Set.Icc (0 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  refine hbox.of_isClosed_subset (isClosed_inFace D) ?_
  intro W hW
  simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, forall_const]
  exact fun i j => ⟨hW.1.1 i j, entry_le_one_of_doublyStochastic hW.1 i j⟩

/-- Every nonempty face has a permanent minimizer. -/
theorem exists_faceMinimizer {D : Fin n → Fin n → Prop} (hne : ∃ X, InFace D X) :
    ∃ Y, FaceMinimizer D Y := by
  obtain ⟨X, hX⟩ := hne
  obtain ⟨Y, hY, hmin⟩ := (isCompact_inFace D).exists_isMinOn ⟨X, hX⟩
    continuous_permanent.continuousOn
  exact ⟨Y, hY, fun B hB => hmin hB⟩

end Compactness

section Variational

variable {m : ℕ}

/-- The objective `Φ(W) = log per W - ∑ x_ij log w_ij`. -/
noncomputable def gibbsObjective (X W : Square (m + 1)) : ℝ :=
  log (permanent W) - ∑ i, ∑ j, X i j * log (W i j)

/-- A positive lower bound for the nonzero entries of a matrix. -/
theorem exists_pos_le_nonzero_entries (X : Square (m + 1)) (hX : Nonnegative X) :
    ∃ c, 0 < c ∧ ∀ i j, X i j ≠ 0 → c ≤ X i j := by
  classical
  let f : Fin (m + 1) × Fin (m + 1) → ℝ := fun p => if X p.1 p.2 ≠ 0 then X p.1 p.2 else 1
  obtain ⟨p, hp⟩ := Finite.exists_min f
  have hfpos : ∀ q, 0 < f q := by
    intro q
    by_cases h : X q.1 q.2 ≠ 0
    · simp only [f, ite_eq_left h]; exact lt_of_le_of_ne (hX _ _) (Ne.symm h)
    · simp only [f, ite_eq_right h]; exact one_pos
  refine ⟨f p, hfpos p, fun i j h => ?_⟩
  have := hp (i, j)
  simp only [f, ite_eq_left h] at this
  exact this

/-- **Key step.**  Every doubly stochastic `X` is the marginal of the Gibbs
law of some doubly stochastic `W` with the same support as `X`. -/
theorem exists_gibbs_marginal {X : Square (m + 1)} (hX : DoublyStochastic X) :
    ∃ W : Square (m + 1), DoublyStochastic W ∧ (∀ i j, W i j ≠ 0 → X i j ≠ 0) ∧
      (∀ i j, X i j ≠ 0 → 0 < W i j) ∧ marginal (gibbsLaw W) = X := by
  classical
  set S : Fin (m + 1) → Fin (m + 1) → Prop := fun i j => X i j ≠ 0 with hSdef
  have hXface : InFace S X := ⟨hX, fun i j h => h⟩
  obtain ⟨Y₀, hY₀⟩ := exists_faceMinimizer ⟨X, hXface⟩
  have hY₀pos : 0 < permanent Y₀ := permanent_pos_of_doublyStochastic hY₀.1.1
  obtain ⟨c, hcpos, hc⟩ := exists_pos_le_nonzero_entries X hX.1
  set Φ : Square (m + 1) → ℝ := gibbsObjective X with hΦ
  set ε₀ : ℝ := exp ((log (permanent Y₀) - Φ X) / c) with hε₀
  set ε : ℝ := min c ε₀ with hε
  have hεpos : 0 < ε := lt_min hcpos (exp_pos _)
  set K : Set (Square (m + 1)) :=
    {W | InFace S W} ∩ ⋂ i, ⋂ j, {W | X i j ≠ 0 → ε ≤ W i j} with hK
  have hKclosed : IsClosed K := by
    refine (isClosed_inFace S).inter (isClosed_iInter fun i => isClosed_iInter fun j => ?_)
    by_cases hx : X i j ≠ 0
    · simpa [hx] using isClosed_le continuous_const (continuous_entry i j)
    · simp [hx]
  have hKc : IsCompact K :=
    (isCompact_inFace S).of_isClosed_subset hKclosed Set.inter_subset_left
  have hXK : X ∈ K := by
    refine ⟨hXface, ?_⟩
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    exact fun i j h => (min_le_left _ _).trans (hc i j h)
  have hKmem : ∀ W ∈ K, InFace S W ∧ ∀ i j, X i j ≠ 0 → ε ≤ W i j := by
    intro W hW
    refine ⟨hW.1, fun i j h => ?_⟩
    have := hW.2
    simp only [Set.mem_iInter, Set.mem_setOf_eq] at this
    exact this i j h
  -- continuity of the objective on `K`
  have hΦcont : ContinuousOn Φ K := by
    refine ContinuousOn.sub ?_ ?_
    · exact continuous_permanent.continuousOn.log fun W hW =>
        ne_of_gt (permanent_pos_of_doublyStochastic (hKmem W hW).1.1)
    · refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
      by_cases hx : X i j = 0
      · simp only [hx, zero_mul]; exact continuousOn_const
      · exact continuousOn_const.mul ((continuous_entry i j).continuousOn.log fun W hW =>
          ne_of_gt (lt_of_lt_of_le hεpos ((hKmem W hW).2 i j hx)))
  obtain ⟨W, hWK, hWmin⟩ := hKc.exists_isMinOn ⟨X, hXK⟩ hΦcont
  obtain ⟨hWface, hWε⟩ := hKmem W hWK
  have hWds : DoublyStochastic W := hWface.1
  have hWsupp : ∀ i j, W i j ≠ 0 → X i j ≠ 0 := hWface.2
  have hWpos : ∀ i j, X i j ≠ 0 → 0 < W i j := fun i j h => lt_of_lt_of_le hεpos (hWε i j h)
  have hPW : 0 < permanent W := permanent_pos_of_doublyStochastic hWds
  -- `W` minimizes `Φ` over all matrices of the face that are positive on `supp X`
  have hWP : ∀ V : Square (m + 1), InFace S V → (∀ i j, X i j ≠ 0 → 0 < V i j) →
      Φ W ≤ Φ V := by
    intro V hV hVpos
    by_cases hVK : ∀ i j, X i j ≠ 0 → ε ≤ V i j
    · refine hWmin ⟨hV, ?_⟩
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      exact hVK
    · push Not at hVK
      obtain ⟨i, j, hx, hlt⟩ := hVK
      refine le_of_lt (lt_of_le_of_lt (hWmin hXK) ?_)
      have hVij := hVpos i j hx
      have hle1 : ∀ a b, V a b ≤ 1 := entry_le_one_of_doublyStochastic hV.1
      -- every term `-x log v` is nonnegative
      have hneg : ∀ a b, 0 ≤ -(X a b * log (V a b)) := by
        intro a b
        have := Real.log_nonpos (hV.1.1 a b) (hle1 a b)
        nlinarith [hX.1 a b]
      have hsingle : -(X i j * log (V i j)) ≤ -∑ a, ∑ b, X a b * log (V a b) := by
        have hrow : -(X i j * log (V i j)) ≤ ∑ b, -(X i b * log (V i b)) :=
          Finset.single_le_sum (f := fun b => -(X i b * log (V i b))) (fun b _ => hneg i b)
            (Finset.mem_univ j)
        have hall : ∑ b, -(X i b * log (V i b)) ≤ ∑ a, ∑ b, -(X a b * log (V a b)) :=
          Finset.single_le_sum (f := fun a => ∑ b, -(X a b * log (V a b)))
            (fun a _ => Finset.sum_nonneg fun b _ => hneg a b) (Finset.mem_univ i)
        simp only [Finset.sum_neg_distrib] at hrow hall
        linarith
      have hlogV : log (V i j) < log ε₀ :=
        Real.log_lt_log hVij (lt_of_lt_of_le hlt (min_le_right _ _))
      have hlogε₀ : log ε₀ = (log (permanent Y₀) - Φ X) / c := Real.log_exp _
      have hneglog : 0 ≤ -log (V i j) := by
        have := Real.log_nonpos (hV.1.1 i j) (hle1 i j); linarith
      have hcx : c * (-log (V i j)) ≤ X i j * (-log (V i j)) :=
        mul_le_mul_of_nonneg_right (hc i j hx) hneglog
      have hkey : Φ X - log (permanent Y₀) < c * (-log (V i j)) := by
        have h1 : c * (-log ε₀) < c * (-log (V i j)) :=
          mul_lt_mul_of_pos_left (by linarith) hcpos
        rw [hlogε₀] at h1
        have h2 : c * (-((log (permanent Y₀) - Φ X) / c)) = Φ X - log (permanent Y₀) := by
          field_simp; ring
        linarith
      have hper : log (permanent Y₀) ≤ log (permanent V) :=
        Real.log_le_log hY₀pos (hY₀.2 V hV)
      show Φ X < gibbsObjective X V
      unfold gibbsObjective
      linarith
  -- the Gibbs marginals of `W`
  set mW : Square (m + 1) := marginal (gibbsLaw W) with hmW
  have hmds : DoublyStochastic mW :=
    doublyStochastic_marginal (gibbsLaw_nonneg hWds.1 hPW) (gibbsLaw_sum hPW)
  have hm0 : ∀ i j, X i j = 0 → mW i j = 0 := by
    intro i j hx
    have hWij : W i j = 0 := by_contra fun h => hWsupp i j h hx
    simp only [hmW, marginal, gibbsLaw]
    refine Finset.sum_eq_zero fun σ hσ => ?_
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [(Finset.mem_filter.1 hσ).2]; exact hWij),
      zero_div]
  set Δ : Square (m + 1) := mW - X with hΔ
  have hΔ0 : ∀ i j, X i j = 0 → Δ i j = 0 := by
    intro i j hx; simp [hΔ, hx, hm0 i j hx]
  have hWzero : ∀ i j, X i j = 0 → W i j = 0 := fun i j hx => by_contra fun h => hWsupp i j h hx
  -- local minimality along `W + t Δ`
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i j, X i j ≠ 0 → 0 < W i j + t * Δ i j := by
    refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
    by_cases hx : X i j ≠ 0
    · have hcont : Continuous fun t : ℝ => W i j + t * Δ i j :=
        continuous_const.add (continuous_id.mul continuous_const)
      have := (hcont.tendsto 0).eventually_const_lt (by simpa using hWpos i j hx)
      exact this.mono fun t ht _ => ht
    · exact Filter.Eventually.of_forall fun t h => absurd h hx
  have hlocal : IsLocalMin (fun t : ℝ => Φ (W + t • Δ)) 0 := by
    refine hev.mono fun t ht => ?_
    simp only [zero_smul, add_zero]
    apply hWP
    · refine ⟨⟨fun i j => ?_, fun i => ?_, fun j => ?_⟩, fun i j h => ?_⟩
      · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        by_cases hx : X i j = 0
        · rw [hWzero i j hx, hΔ0 i j hx]; simp
        · exact (ht i j hx).le
      · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
          ← Finset.mul_sum, hΔ, Matrix.sub_apply, Finset.sum_sub_distrib]
        rw [hWds.2.1 i, hmds.2.1 i, hX.2.1 i]; ring
      · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
          ← Finset.mul_sum, hΔ, Matrix.sub_apply, Finset.sum_sub_distrib]
        rw [hWds.2.2 j, hmds.2.2 j, hX.2.2 j]; ring
      · by_contra hx
        apply h
        simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        rw [hWzero i j hx, hΔ0 i j hx]; ring
    · intro i j hx
      simpa only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using ht i j hx
  -- the derivative along `Δ`
  have hW0 : W + (0 : ℝ) • Δ = W := by simp
  have hderP : HasDerivAt (fun t : ℝ => log (permanent (W + t • Δ)))
      ((∑ i, ∑ j, Δ i j * cofactor W i j) / permanent W) 0 := by
    have := (hasDerivAt_permanent_add_smul W Δ).log (by rw [hW0]; exact ne_of_gt hPW)
    rwa [hW0] at this
  have hderT : ∀ i j, HasDerivAt (fun t : ℝ => X i j * log ((W + t • Δ) i j))
      (X i j * (Δ i j / W i j)) 0 := by
    intro i j
    by_cases hx : X i j = 0
    · simpa [hx] using hasDerivAt_const (0 : ℝ) (0 : ℝ)
    · have hd : HasDerivAt (fun t : ℝ => W i j + t * Δ i j) (Δ i j) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (Δ i j)).const_add (W i j)
      have hd' := (hd.log (by simpa using ne_of_gt (hWpos i j hx))).const_mul (X i j)
      simp only [zero_mul, add_zero] at hd'
      refine hd'.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have hder : HasDerivAt (fun t : ℝ => Φ (W + t • Δ))
      ((∑ i, ∑ j, Δ i j * cofactor W i j) / permanent W -
        ∑ i, ∑ j, X i j * (Δ i j / W i j)) 0 := by
    have hsum := HasDerivAt.sum (u := univ) fun i _ =>
      HasDerivAt.sum (u := univ) fun j _ => hderT i j
    exact (hderP.sub hsum).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => by simp [hΦ, gibbsObjective])
  have hzero := hlocal.hasDerivAt_eq_zero hder
  -- rewrite the derivative as `∑ Δ² / W`
  have hterm : ∀ i j, Δ i j * cofactor W i j / permanent W - X i j * (Δ i j / W i j) =
      Δ i j ^ 2 / W i j := by
    intro i j
    by_cases hx : X i j = 0
    · simp [hΔ0 i j hx]
    · have hWij := hWpos i j hx
      have hcof : cofactor W i j = permanent W * mW i j / W i j := by
        rw [eq_div_iff (ne_of_gt hWij), mul_comm,
          mul_cofactor_eq_marginal_gibbsLaw (ne_of_gt hPW) i j]
      rw [hcof]
      have hΔij : Δ i j = mW i j - X i j := rfl
      rw [hΔij]
      field_simp
  have hsq : ∑ i, ∑ j, Δ i j ^ 2 / W i j = 0 := by
    rw [← hzero, Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => (hterm i j).symm
  have hnn : ∀ i j, 0 ≤ Δ i j ^ 2 / W i j := fun i j => div_nonneg (sq_nonneg _) (hWds.1 i j)
  have hall : ∀ i j, Δ i j ^ 2 / W i j = 0 := by
    intro i j
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun a _ =>
      Finset.sum_nonneg fun b _ => hnn a b).1 hsq i (Finset.mem_univ i)
    exact (Finset.sum_eq_zero_iff_of_nonneg fun b _ => hnn i b).1 h1 j (Finset.mem_univ j)
  refine ⟨W, hWds, hWsupp, hWpos, ?_⟩
  ext i j
  by_cases hx : X i j = 0
  · rw [hx]; exact hm0 i j hx
  · have := hall i j
    rw [div_eq_zero_iff] at this
    rcases this with h | h
    · have : Δ i j = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
      have hΔij : Δ i j = mW i j - X i j := rfl
      linarith
    · exact absurd h (ne_of_gt (hWpos i j hx))

/-- The law constraint set of a doubly stochastic matrix is nonempty. -/
theorem exists_isLaw {X : Square (m + 1)} (hX : DoublyStochastic X) : ∃ μ, IsLaw X μ := by
  obtain ⟨W, hW, -, -, hm⟩ := exists_gibbs_marginal hX
  have hP := permanent_pos_of_doublyStochastic hW
  exact ⟨gibbsLaw W, gibbsLaw_nonneg hW.1 hP, gibbsLaw_sum hP, hm⟩

theorem bddAbove_lawEntropy (X : Square (m + 1)) :
    BddAbove (lawEntropy '' {μ | IsLaw X μ}) := by
  refine ⟨log (permanent X) + rowEntropy X, ?_⟩
  rintro _ ⟨μ, hμ, rfl⟩
  have := lawEntropy_sub_rowEntropy_le hμ
  linarith

/-- **Lavi Lemma 3.1, first inequality:** `F(X) ≤ log per X`. -/
theorem faceFunctional_le_log_permanent {X : Square (m + 1)} (hX : DoublyStochastic X) :
    faceFunctional X ≤ log (permanent X) := by
  obtain ⟨μ, hμ⟩ := exists_isLaw hX
  have : maxMatchingEntropy X ≤ log (permanent X) + rowEntropy X := by
    refine csSup_le ⟨_, μ, hμ, rfl⟩ ?_
    rintro _ ⟨ν, hν, rfl⟩
    have := lawEntropy_sub_rowEntropy_le hν
    linarith
  unfold faceFunctional
  linarith

/-- **Lavi Lemma 3.1, second inequality:** for `X ∈ Ω(D)` there is `Y ∈ Ω(D)`,
supported inside the support of `X`, with `log per Y ≤ F(X)`. -/
theorem exists_inFace_log_permanent_le_faceFunctional {D : Fin (m + 1) → Fin (m + 1) → Prop}
    {X : Square (m + 1)} (hX : InFace D X) :
    ∃ Y, InFace D Y ∧ (∀ i j, Y i j ≠ 0 → X i j ≠ 0) ∧
      log (permanent Y) ≤ faceFunctional X := by
  obtain ⟨W, hW, hWsupp, -, hm⟩ := exists_gibbs_marginal hX.1
  have hP := permanent_pos_of_doublyStochastic hW
  refine ⟨W, ⟨hW, fun i j h => hX.2 i j (hWsupp i j h)⟩, hWsupp, ?_⟩
  have hlaw : IsLaw X (gibbsLaw W) := ⟨gibbsLaw_nonneg hW.1 hP, gibbsLaw_sum hP, hm⟩
  have hle : lawEntropy (gibbsLaw W) ≤ maxMatchingEntropy X :=
    le_csSup (bddAbove_lawEntropy X) ⟨_, hlaw, rfl⟩
  have hent := lawEntropy_gibbsLaw hP
  rw [hm] at hent
  have hKL := sum_mul_log_le_sum_mul_log hX.1.1 hW.1 hX.1.2.1 hW.2.1
    (fun i j h => by
      by_contra h'
      exact h (by
        have hWi : W i j = 0 := h'
        rw [← hm]
        simp only [marginal, gibbsLaw]
        refine Finset.sum_eq_zero fun σ hσ => ?_
        rw [Finset.prod_eq_zero (Finset.mem_univ i)
          (by rw [(Finset.mem_filter.1 hσ).2]; exact hWi), zero_div]))
  unfold faceFunctional rowEntropy
  linarith

/-- **Lavi Lemma 3.1, consequence:** every face minimizer bounds `F` from below
on the whole face, `F(X) ≥ log min_{Ω(D)} per`. -/
theorem log_faceMinimizer_le_faceFunctional {D : Fin (m + 1) → Fin (m + 1) → Prop}
    {Y X : Square (m + 1)} (hY : FaceMinimizer D Y) (hX : InFace D X) :
    log (permanent Y) ≤ faceFunctional X := by
  obtain ⟨Z, hZ, -, hZle⟩ := exists_inFace_log_permanent_le_faceFunctional hX
  exact le_trans (Real.log_le_log (permanent_pos_of_doublyStochastic hY.1.1) (hY.2 Z hZ)) hZle

/-- **Lavi Lemma 3.1 (face variational identity).**  On a nonempty face,
`min_{Ω(D)} F = log min_{Ω(D)} per`: some face minimizer `Y` satisfies
`F(Y) = log per Y`, and `log per Y ≤ F(X)` for every `X ∈ Ω(D)`. -/
theorem lavi_lemma_3_1 {D : Fin (m + 1) → Fin (m + 1) → Prop} (hne : ∃ X, InFace D X) :
    ∃ Y, FaceMinimizer D Y ∧ faceFunctional Y = log (permanent Y) ∧
      ∀ X, InFace D X → log (permanent Y) ≤ faceFunctional X ∧
        faceFunctional X ≤ log (permanent X) := by
  obtain ⟨Y, hY⟩ := exists_faceMinimizer hne
  refine ⟨Y, hY, le_antisymm (faceFunctional_le_log_permanent hY.1.1)
    (log_faceMinimizer_le_faceFunctional hY hY.1), fun X hX =>
      ⟨log_faceMinimizer_le_faceFunctional hY hX, faceFunctional_le_log_permanent hX.1⟩⟩

end Variational

end LaviSection2
