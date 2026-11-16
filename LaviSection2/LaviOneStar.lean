import LaviSection2.LaviOneStarCapacity

/-!
# Lavi Lemma 5.1 (one-star bound) and Corollary 5.2, assuming Gurvits

Let `K` be a balanced occurrence core of order `k ≥ 3` with at least three
distinct neighbors at every vertex, `v` a root row, `L` the `ℓ` occurrences off
`v`, and `B = D(K, L)` the shortened star.  Assuming Gurvits's capacity
inequality (`GurvitsCapacityInequality`, an explicit hypothesis), every doubly
stochastic matrix `A` supported on `B` satisfies (5.1):

`per A / 2^(1-k-ℓ) ≥ (8192/6561) (177147/131072)^(ℓ - 3(k-1)) > 1`

(`lavi_lemma_5_1`), and every feasible flow `x` on `K` has
`G_{K,L}(x) ≥ log (8192/6561)` (`lavi_corollary_5_2`).

Full indecomposability of `K` is not needed for the bound.  The proof follows
the manuscript: the flow lift and the elimination (5.2) give `per A = per M`,
Gurvits gives (5.5), AM–GM with concavity gives (5.4), and the secant bounds
(5.10) with the degree count (5.6) give (5.12).
-/

set_option linter.unusedSectionVars false

namespace LaviSection2

open Finset Real

open scoped BigOperators

/-- The exact constant arithmetic of (5.12). -/
theorem oneStar_arith (m p : ℕ) :
    (1 / 2 : ℝ) * (81 / 32) * (32 / 27) ^ (m + 2) * (8 / 9) ^ (m + 3) * (243 / 256) ^ (p + m) *
      (729 / 512) ^ p = 8192 / 6561 * (177147 / 131072) ^ p := by
  have h1 : (32 / 27 : ℝ) ^ (m + 2) * (8 / 9) ^ (m + 3) * (243 / 256) ^ (p + m) =
      (32 / 27) ^ 2 * (8 / 9) ^ 3 * (243 / 256) ^ p * ((32 / 27) * (8 / 9) * (243 / 256)) ^ m := by
    rw [mul_pow, mul_pow, pow_add, pow_add, pow_add]; ring
  have h2 : (177147 / 131072 : ℝ) ^ p = (729 / 512) ^ p * (243 / 256) ^ p := by
    rw [← mul_pow]; norm_num
  rw [h2, show (32 / 27 : ℝ) * (8 / 9) * (243 / 256) = 1 by norm_num, one_pow, mul_one] at *
  calc (1 / 2 : ℝ) * (81 / 32) * (32 / 27) ^ (m + 2) * (8 / 9) ^ (m + 3) * (243 / 256) ^ (p + m) *
        (729 / 512) ^ p
      = (1 / 2 : ℝ) * (81 / 32) * ((32 / 27) ^ (m + 2) * (8 / 9) ^ (m + 3) *
          (243 / 256) ^ (p + m)) * (729 / 512) ^ p := by ring
    _ = 8192 / 6561 * ((729 / 512) ^ p * (243 / 256) ^ p) := by rw [h1]; ring

section OneStar

variable {U V E : Type*} [Fintype U] [Fintype V] [Fintype E]
  [DecidableEq U] [DecidableEq V] [DecidableEq E] {row : E → U} {col : E → V} {v : U}

/-- The column-product bound: `∏_j g(min(c_j, j)) ≥ (81/32) ∏_j C_{c_j}/2`. -/
theorem prod_gurvitsG_ge {k : ℕ} (hk : 3 ≤ k) (c : Fin k → ℕ) (hc : ∀ j, 3 ≤ c j) :
    81 / 32 * ∏ j, colFactor (c j) / 2 ≤ ∏ j : Fin k, gurvitsG (min (c j) (j.val + 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  conv_rhs => rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  have hC : ∀ j, colFactor (c j) ≤ 8 / 9 := fun j => colFactor_le (hc j)
  have hC0 : ∀ j, 0 < colFactor (c j) := fun j => colFactor_pos _ (by linarith [hc j])
  have h0 : gurvitsG (min (c 0) ((0 : Fin (m + 2)).val + 1)) = 1 := by
    simp only [Fin.val_zero, zero_add]
    rw [min_eq_right (by linarith [hc 0])]; simp [gurvitsG]
  have h1 : gurvitsG (min (c (Fin.succ 0)) ((Fin.succ (0 : Fin (m + 1))).val + 1)) = 1 / 2 := by
    simp only [Fin.val_succ, Fin.val_zero]
    rw [min_eq_right (by linarith [hc (Fin.succ 0)])]
    unfold gurvitsG; norm_num
  have hrest : ∏ j : Fin m, colFactor (c j.succ.succ) / 2 ≤
      ∏ j : Fin m, gurvitsG (min (c j.succ.succ) (j.succ.succ.val + 1)) := by
    refine Finset.prod_le_prod (fun j _ => (div_pos (hC0 _) two_pos).le) fun j _ => ?_
    have hmin3 : 3 ≤ min (c j.succ.succ) (j.succ.succ.val + 1) := by
      simp only [Fin.val_succ]; exact le_min (hc _) (by omega)
    rw [gurvitsG_eq _ (by omega)]
    exact div_le_div_of_nonneg_right (colFactor_anti (by omega) (min_le_left _ _)) two_pos.le
  rw [h0, h1]
  have hprod_nonneg : 0 ≤ ∏ j : Fin m, colFactor (c j.succ.succ) / 2 :=
    Finset.prod_nonneg fun j _ => (div_pos (hC0 _) two_pos).le
  have e0 := hC 0
  have e1 := hC (Fin.succ 0)
  have p0 := hC0 0
  have p1 := hC0 (Fin.succ 0)
  calc 81 / 32 * (colFactor (c 0) / 2 * (colFactor (c (Fin.succ 0)) / 2 *
        ∏ j : Fin m, colFactor (c j.succ.succ) / 2))
      ≤ 1 * (1 / 2 * ∏ j : Fin m, colFactor (c j.succ.succ) / 2) := by
        have : 81 / 32 * (colFactor (c 0) / 2 * (colFactor (c (Fin.succ 0)) / 2)) ≤ 1 * (1 / 2) := by
          nlinarith [mul_le_mul e0 e1 p1.le (by norm_num)]
        nlinarith [mul_le_mul_of_nonneg_right this hprod_nonneg]
    _ ≤ 1 * (1 / 2 * ∏ j : Fin m, gurvitsG (min (c j.succ.succ) (j.succ.succ.val + 1))) := by
        gcongr

/-- **Lavi (5.1) at the eliminated matrix**, for a flow on the shortened star. -/
theorem oneStar_bound_elim (hG : GurvitsCapacityInequality) {x : E → ℝ}
    (hx : StarFlow row col v x) {k : ℕ} (hkU : Fintype.card U = k) (hk : 3 ≤ k)
    (eR' : Fin k ≃ U) (eC' : Fin k ≃ V)
    (hR : ∀ u, 3 ≤ ((rowSet row u).image col).card)
    (hC : ∀ w, 3 ≤ (((univ : Finset E).filter fun e => col e = w).image row).card) :
    8192 / 6561 * (177147 / 131072) ^ ((offRoot row v).card - 3 * (k - 1)) ≤
      2 ^ (k + (offRoot row v).card - 1) *
        permanent (aggregateMatrix row col eR' eC' (elimWeight row v x)) := by
  set ℓ := (offRoot row v).card with hℓ
  set M := aggregateMatrix row col eR' eC' (elimWeight row v x) with hM
  have hr3 : ∀ u, 3 ≤ (rowSet row u).card := fun u => (hR u).trans Finset.card_image_le
  have hr2 : ∀ u, 2 ≤ (rowSet row u).card := fun u => by linarith [hr3 u]
  have hc3 : ∀ w, 3 ≤ colCount row col v w := three_le_colCount hC
  -- `ℓ ≥ 3(k - 1)` and `∑ c ≤ ℓ + k`
  have hsumr := sum_rowSet_card (row := row) (v := v)
  have hcard_erase : ((univ : Finset U).erase v).card = k - 1 := by
    rw [Finset.card_erase_of_mem (mem_univ v), Finset.card_univ, hkU]
  have hℓ3 : 3 * (k - 1) ≤ ℓ := by
    rw [hℓ, ← hsumr, ← hcard_erase, mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun u _ => hr3 u
  have hsumc := sum_colCount_le (row := row) (col := col) (v := v)
  have hcardV : Fintype.card V = k := (Fintype.card_congr (eR'.symm.trans eC')).symm.trans hkU
  rw [hcardV] at hsumc
  -- Gurvits, with the degree bound
  have hMnn : Nonnegative M := fun i j =>
    Finset.sum_nonneg fun e _ => elimWeight_nonneg hx e
  have hGM := hG k M hMnn
  have hcap := capacity_elim_ge eR' eC' hx hr2
  set B := ∏ u ∈ (univ : Finset U).erase v, rowFactor (rowSet row u).card / 2 ^ (rowSet row u).card
  have hB0 : 0 ≤ B := Finset.prod_nonneg fun u _ =>
    div_nonneg (by rw [rowFactor_eq_exp (hr2 u)]; positivity) (by positivity)
  have hgdeg : ∏ j : Fin k, gurvitsG (min (colCount row col v (eC' j)) (j.val + 1)) ≤
      ∏ j : Fin k, gurvitsG (min (colDegree M j) (j.val + 1)) :=
    Finset.prod_le_prod (fun j _ => (gurvitsG_pos _).le) fun j _ =>
      gurvitsG_anti (min_le_min_right _ (colDegree_elim_le eR' eC' j))
  have hgc := prod_gurvitsG_ge hk (fun j => colCount row col v (eC' j)) (fun j => hc3 _)
  set PC := ∏ w, colFactor (colCount row col v w)
  have hPC : ∏ j : Fin k, colFactor (colCount row col v (eC' j)) / 2 = PC / 2 ^ k := by
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Equiv.prod_comp eC' (fun w => colFactor (colCount row col v w))]
  rw [hPC] at hgc
  have hPC0 : 0 ≤ PC := Finset.prod_nonneg fun w _ => (colFactor_pos _ (by linarith [hc3 w])).le
  -- `per M ≥ B · (81/32) · PC / 2^k`
  have hper : B * (81 / 32 * (PC / 2 ^ k)) ≤ permanent M := by
    have hG0 : 0 ≤ ∏ j : Fin k, gurvitsG (min (colDegree M j) (j.val + 1)) :=
      Finset.prod_nonneg fun j _ => (gurvitsG_pos _).le
    calc B * (81 / 32 * (PC / 2 ^ k))
        ≤ B * ∏ j : Fin k, gurvitsG (min (colDegree M j) (j.val + 1)) :=
          mul_le_mul_of_nonneg_left (hgc.trans hgdeg) hB0
      _ ≤ capacity M * ∏ j : Fin k, gurvitsG (min (colDegree M j) (j.val + 1)) :=
          mul_le_mul_of_nonneg_right hcap hG0
      _ ≤ permanent M := hGM
  -- the row product
  set PA := ∏ u ∈ (univ : Finset U).erase v, rowFactor (rowSet row u).card
  have hBeq : B = PA / 2 ^ ℓ := by
    simp only [B, PA]
    rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, hsumr]
  obtain ⟨m, hm⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  obtain ⟨p, hp⟩ : ∃ p, ℓ = p + 3 * m + 6 := ⟨ℓ - 3 * (k - 1), by omega⟩
  have hPA : (32 / 27 : ℝ) ^ (m + 2) * (729 / 512) ^ p ≤ PA := by
    have hsec : ∏ u ∈ (univ : Finset U).erase v,
        (32 / 27 * (729 / 512 : ℝ) ^ ((rowSet row u).card - 3)) ≤ PA :=
      Finset.prod_le_prod (fun u _ => by positivity) fun u _ => rowFactor_secant (hr3 u)
    have hexp : ∑ u ∈ (univ : Finset U).erase v, ((rowSet row u).card - 3) = p := by
      have h := Finset.sum_tsub_distrib ((univ : Finset U).erase v) (fun u _ => hr3 u)
      rw [h, hsumr, Finset.sum_const, hcard_erase, smul_eq_mul]
      omega
    rw [Finset.prod_mul_distrib, Finset.prod_const, hcard_erase, Finset.prod_pow_eq_pow_sum,
      hexp, show k - 1 = m + 2 by omega] at hsec
    exact hsec
  have hPCb : (8 / 9 : ℝ) ^ (m + 3) * (243 / 256) ^ (p + m) ≤ PC := by
    have hsec : ∏ w, (8 / 9 * (243 / 256 : ℝ) ^ (colCount row col v w - 3)) ≤ PC :=
      Finset.prod_le_prod (fun w _ => by positivity) fun w _ => colFactor_secant (hc3 w)
    have hexp : ∑ w, (colCount row col v w - 3) ≤ p + m := by
      have h := Finset.sum_tsub_distrib (univ : Finset V) (fun w _ => hc3 w)
      rw [h, Finset.sum_const, Finset.card_univ, hcardV, smul_eq_mul]
      omega
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcardV,
      Finset.prod_pow_eq_pow_sum, show k = m + 3 from hm] at hsec
    refine le_trans ?_ hsec
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) hexp)
      (by positivity)
  -- combine
  have h2k : (2 : ℝ) ^ (k + ℓ - 1) = 2 ^ ℓ * 2 ^ k / 2 := by
    rw [show k + ℓ - 1 = (k + ℓ - 1) from rfl, eq_div_iff two_ne_zero, ← pow_succ, ← pow_add]
    congr 1; omega
  have hfinal : 8192 / 6561 * (177147 / 131072 : ℝ) ^ p ≤
      2 ^ (k + ℓ - 1) * (B * (81 / 32 * (PC / 2 ^ k))) := by
    rw [hBeq, h2k, ← oneStar_arith m p]
    have h2l : (0 : ℝ) < 2 ^ ℓ := by positivity
    have h2kk : (0 : ℝ) < 2 ^ k := by positivity
    have hrhs : 2 ^ ℓ * 2 ^ k / 2 * (PA / 2 ^ ℓ * (81 / 32 * (PC / 2 ^ k))) =
        1 / 2 * (81 / 32) * (PA * PC) := by field_simp
    rw [hrhs]
    have hmul := mul_le_mul hPA hPCb (by positivity) (by
      exact le_trans (by positivity) hPA)
    nlinarith [hmul]
  rw [show ℓ - 3 * (k - 1) = p by omega]
  exact hfinal.trans (mul_le_mul_of_nonneg_left hper (by positivity))

variable (row col v)

/-- **Lavi Lemma 5.1 (one-star bound), assuming Gurvits's inequality.**  Let
`k = |U| ≥ 3`, every vertex have at least three distinct neighbors, `v` a root
row and `ℓ` the number of occurrences off `v`.  Every doubly stochastic matrix
`A` supported on the shortened star `D(K, L)` satisfies
`2^(k+ℓ-1) per A ≥ (8192/6561)(177147/131072)^(ℓ-3(k-1))`, and the right side
exceeds one. -/
theorem lavi_lemma_5_1 (hG : GurvitsCapacityInequality)
    (hbal : Fintype.card U = Fintype.card V) (hk : 3 ≤ Fintype.card U)
    (hR : ∀ u, 3 ≤ ((rowSet row u).image col).card)
    (hC : ∀ w, 3 ≤ (((univ : Finset E).filter fun e => col e = w).image row).card)
    {n : ℕ} (eR : Fin n ≃ U ⊕ ↥(offRoot row v)) (eC : Fin n ≃ V ⊕ ↥(offRoot row v))
    {A : Square n} (hA : InFace (expSupport row col (offRoot row v) eR eC) A) :
    8192 / 6561 * (177147 / 131072) ^ ((offRoot row v).card - 3 * (Fintype.card U - 1)) ≤
        2 ^ (n - 1) * permanent A ∧
      1 < 8192 / 6561 * (177147 / 131072 : ℝ) ^
        ((offRoot row v).card - 3 * (Fintype.card U - 1)) := by
  refine ⟨?_, lavi_oneStar_bound_strict _⟩
  set x := liftFlow row col (offRoot row v) eR eC A
  have hAeq := eq_expandedMatrix_liftFlow hA
  have hDS : DoublyStochastic (expandedMatrix row col (offRoot row v) eR eC x) := hAeq ▸ hA.1
  have hx : StarFlow row col v x :=
    ⟨liftFlow_nonneg hA, fun e he => liftFlow_le_one hA he, rowSet_sum_of_DS hDS,
      colSet_sum_of_DS hDS⟩
  set eR' : Fin (Fintype.card U) ≃ U := (Fintype.equivFin U).symm
  set eC' : Fin (Fintype.card U) ≃ V := (Fintype.equivFinOfCardEq hbal.symm).symm
  have hn : n = Fintype.card U + (offRoot row v).card := by
    rw [← Fintype.card_fin n, Fintype.card_congr eR, Fintype.card_sum, Fintype.card_coe]
  have hper : permanent A = permanent (aggregateMatrix row col eR' eC' (elimWeight row v x)) := by
    conv_lhs => rw [hAeq]
    exact permanent_expandedMatrix_eq_elim row col v eR eC eR' eC' x
  rw [hper, hn]
  exact oneStar_bound_elim hG hx rfl hk eR' eC' hR hC

/-- A law's marginals aggregate to a doubly stochastic matrix. -/
theorem doublyStochastic_aggregate_of_law {n : ℕ} {U' V' E' : Type*} [Fintype U'] [Fintype V']
    [Fintype E'] [DecidableEq U'] [DecidableEq V'] [DecidableEq E'] {row' : E' → U'}
    {col' : E' → V'} (eR : Fin n ≃ U') (eC : Fin n ≃ V') {z : E' → ℝ}
    {μ : LMatch row' col' → ℝ} (hμ : IsCoreLaw row' col' z μ) :
    DoublyStochastic (aggregateMatrix row' col' eR eC z) := by
  classical
  refine ⟨fun i j => Finset.sum_nonneg fun e _ => hμ.nonneg_edge e, fun i => ?_, fun j => ?_⟩
  · rw [aggregateMatrix_row_sum]
    calc ∑ e ∈ (univ : Finset E').filter (fun e => row' e = eR i), z e
        = ∑ e ∈ (univ : Finset E').filter (fun e => row' e = eR i),
            ∑ M ∈ (univ : Finset (LMatch row' col')).filter (fun M => M.1 (row' e) = e), μ M :=
          Finset.sum_congr rfl fun e _ => (congrFun hμ.2.2 e).symm
      _ = ∑ M, ∑ e ∈ (univ : Finset E').filter (fun e => row' e = eR i ∧ M.1 (row' e) = e),
            μ M :=
          Finset.sum_comm' (by intro e M; simp only [mem_filter, mem_univ, true_and]; tauto)
      _ = ∑ M, μ M := by
          refine Finset.sum_congr rfl fun M _ => ?_
          rw [Finset.sum_eq_single_of_mem (M.1 (eR i))
            (Finset.mem_filter.2 ⟨mem_univ _, M.2.1 _, by rw [M.2.1]⟩)]
          intro e he hne
          obtain ⟨-, hr, hm⟩ := Finset.mem_filter.1 he
          exact absurd (by rw [← hm, hr]) hne
      _ = 1 := hμ.2.1
  · rw [aggregateMatrix_col_sum]
    calc ∑ e ∈ (univ : Finset E').filter (fun e => col' e = eC j), z e
        = ∑ e ∈ (univ : Finset E').filter (fun e => col' e = eC j),
            ∑ M ∈ (univ : Finset (LMatch row' col')).filter (fun M => M.1 (row' e) = e), μ M :=
          Finset.sum_congr rfl fun e _ => (congrFun hμ.2.2 e).symm
      _ = ∑ M, ∑ e ∈ (univ : Finset E').filter (fun e => col' e = eC j ∧ M.1 (row' e) = e),
            μ M :=
          Finset.sum_comm' (by intro e M; simp only [mem_filter, mem_univ, true_and]; tauto)
      _ = ∑ M, μ M := by
          refine Finset.sum_congr rfl fun M _ => ?_
          set u₀ := (Equiv.ofBijective _ M.2.2).symm (eC j)
          have hu₀ : col' (M.1 u₀) = eC j := Equiv.ofBijective_apply_symm_apply _ M.2.2 _
          rw [Finset.sum_eq_single_of_mem (M.1 u₀) (Finset.mem_filter.2 ⟨mem_univ _, hu₀,
            by rw [M.2.1]⟩)]
          intro e he hne
          exfalso
          obtain ⟨-, hc, hm⟩ := Finset.mem_filter.1 he
          have : row' e = u₀ := M.2.2.1 (show col' (M.1 (row' e)) = col' (M.1 u₀) by
            rw [hm, hc, hu₀])
          exact hne (by rw [← hm, this])
      _ = 1 := hμ.2.1

/-- The expanded matrix of a law's marginal lies in the expanded face. -/
theorem inFace_expandedMatrix {L : Finset E} {n : ℕ} (eR : Fin n ≃ U ⊕ ↥L) (eC : Fin n ≃ V ⊕ ↥L)
    {x : E → ℝ} {μ : LMatch row col → ℝ} (hμ : IsCoreLaw row col x μ) :
    InFace (expSupport row col L eR eC) (expandedMatrix row col L eR eC x) := by
  obtain ⟨κ, hκ⟩ : ∃ κ, IsCoreLaw (expRow row L) (expCol col L) (expFlow L x) κ :=
    ⟨_, (isCoreLaw_exp_iff x μ).1 hμ⟩
  refine ⟨doublyStochastic_aggregate_of_law eR eC hκ, fun i j h => ?_⟩
  unfold expandedMatrix aggregateMatrix mergeFlow at h
  obtain ⟨f, hf, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have := (Finset.mem_filter.1 hf).2
  exact ⟨f, (Prod.ext_iff.1 this).1, (Prod.ext_iff.1 this).2⟩

/-- `G ≥ log(8192/6561)` for one choice of coordinates. -/
theorem corollary_5_2_aux (hG : GurvitsCapacityInequality)
    (hbal : Fintype.card U = Fintype.card V) (hk : 3 ≤ Fintype.card U)
    (hR : ∀ u, 3 ≤ ((rowSet row u).image col).card)
    (hC : ∀ w, 3 ≤ (((univ : Finset E).filter fun e => col e = w).image row).card)
    {n : ℕ} (eR : Fin n ≃ U ⊕ ↥(offRoot row v)) (eC : Fin n ≃ V ⊕ ↥(offRoot row v))
    {x : E → ℝ} (hlaw : ∃ μ, IsCoreLaw row col x μ) :
    log (8192 / 6561) ≤ normalizedGap row col (offRoot row v) x := by
  obtain ⟨μ, hμ⟩ := hlaw
  have h37 := lavi_eq_3_7 eR eC ⟨μ, hμ⟩
  have hX := inFace_expandedMatrix row col eR eC hμ
  rcases n with _ | m
  · exact absurd (Fintype.card_congr eR.symm) (by
      rw [Fintype.card_fin, Fintype.card_sum]; omega)
  obtain ⟨Z, hZ, -, hlog⟩ := exists_inFace_log_permanent_le_faceFunctional hX
  obtain ⟨h51, -⟩ := lavi_lemma_5_1 row col v hG hbal hk hR hC eR eC hZ
  have hc1 : (8192 / 6561 : ℝ) ≤
      8192 / 6561 * (177147 / 131072) ^ ((offRoot row v).card - 3 * (Fintype.card U - 1)) := by
    have : (1 : ℝ) ≤ (177147 / 131072) ^ ((offRoot row v).card - 3 * (Fintype.card U - 1)) :=
      one_le_pow₀ (by norm_num)
    nlinarith
  have hZpos := permanent_pos_of_doublyStochastic hZ.1
  have hle : (8192 / 6561 : ℝ) ≤ 2 ^ m * permanent Z := by
    simpa using hc1.trans h51
  have hlog2 : log (8192 / 6561) ≤ (m : ℝ) * log 2 + log (permanent Z) := by
    rw [← Real.log_pow, ← Real.log_mul (by positivity) hZpos.ne']
    exact Real.log_le_log (by norm_num) hle
  rw [h37.1]
  push_cast
  linarith

/-- **Lavi Corollary 5.2, assuming Gurvits's inequality.**  Under the
hypotheses of Lemma 5.1, with `L` the occurrences off the root row `v`, every
feasible flow `x` on `K` has `G_{K,L}(x) ≥ log (8192/6561) > 0`. -/
theorem lavi_corollary_5_2 (hG : GurvitsCapacityInequality)
    (hbal : Fintype.card U = Fintype.card V) (hk : 3 ≤ Fintype.card U)
    (hR : ∀ u, 3 ≤ ((rowSet row u).image col).card)
    (hC : ∀ w, 3 ≤ (((univ : Finset E).filter fun e => col e = w).image row).card)
    {x : E → ℝ} (hlaw : ∃ μ, IsCoreLaw row col x μ) :
    log (8192 / 6561) ≤ normalizedGap row col (offRoot row v) x ∧ 0 < log (8192 / 6561 : ℝ) := by
  refine ⟨?_, Real.log_pos (by norm_num)⟩
  have hcard : Fintype.card (V ⊕ ↥(offRoot row v)) = Fintype.card (U ⊕ ↥(offRoot row v)) := by
    rw [Fintype.card_sum, Fintype.card_sum, hbal]
  exact corollary_5_2_aux row col v hG hbal hk hR hC (Fintype.equivFin _).symm
    (Fintype.equivFinOfCardEq hcard).symm hlaw

end OneStar

end LaviSection2
