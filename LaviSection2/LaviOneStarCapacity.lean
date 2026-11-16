import LaviSection2.LaviOneStarPermanent
import LaviSection2.LaviOneStarConstants
import Mathlib.Analysis.MeanInequalities

/-!
# Lavi Section 5: capacity of the eliminated matrix, (5.3)–(5.6)

* `capacity` is Gurvits's `Cap(M) = inf_{y > 0} ∏_i (M y)_i / ∏_j y_j`.
* `GurvitsCapacityInequality` is Gurvits's degree-sensitive capacity bound
  [Gurvits 2008, Theorem 2.4 and Corollary 2.7(a)] for permanents,
  `per M ≥ Cap(M) ∏_j g(min(Δ_j, j))`, with columns in their given order.  It
  is **not** proved here; Section 5 uses it only as an explicit hypothesis.
* `rowSum_nonroot_ge`, `rowSum_root_ge`: Lavi's weighted AM–GM step (5.3),
  sharpened by concavity of `h₂` to `(M y)_i ≥ (A_{r_i}/2^{r_i}) ∏ y^{x_e}`.
* `capacity_elim_ge`: (5.4) in the form
  `Cap(M) ≥ ∏_{i ≠ v} A_{r_i} / 2^{r_i}`.
* `colDegree_elim_le`, `three_le_colCount`, `sum_colCount_le`: the degree
  bookkeeping `Δ_j ≤ c_j`, `c_j ≥ 3`, and (5.6) `∑ c_j ≤ ℓ + k`.
-/

set_option linter.unusedSectionVars false

namespace LaviSection2

open Finset Real

open scoped BigOperators

/-- Gurvits's capacity of a square matrix. -/
noncomputable def capacity {n : ℕ} (M : Square n) : ℝ :=
  sInf ((fun z : Fin n → ℝ => (∏ i, ∑ j, M i j * z j) / ∏ j, z j) '' {z | ∀ j, 0 < z j})

/-- The number of nonzero entries in a column, `Δ_j`. -/
noncomputable def colDegree {n : ℕ} (M : Square n) (j : Fin n) : ℕ := by
  classical exact ((univ : Finset (Fin n)).filter fun i => M i j ≠ 0).card

/-- **Gurvits's degree-sensitive capacity inequality** for permanents
[L. Gurvits, *Van der Waerden/Schrijver–Valiant like conjectures and stable
(aka hyperbolic) homogeneous polynomials: one theorem for all*, Electron. J.
Combin. 15 (2008), Theorem 2.4 and Corollary 2.7(a)]: for a nonnegative
`n × n` matrix with `Δ_j` nonzero entries in column `j`,
`per M ≥ Cap(M) ∏_{j=1}^{n} g(min(Δ_j, j))`.  This is an external theorem,
assumed (not proved) in this development.

Relation to the published statements.  Gurvits writes the product over
`j = 2, …, n` and defines `G` only for arguments `≥ 1`; the form used here,
with the product from `j = 1` and `g(0) = g(1) = 1` for every nonnegative
matrix, is the one stated by M. Laurent and A. Schrijver, *On Leonid Gurvits's
proof for permanents*, Amer. Math. Monthly 117 (2010), 903–911, Corollary 1a.
The two agree: the `j = 1` factor is `g(min(Δ₁, 1)) = 1`, and if `M` has a
zero row or a zero column then `Cap(M) = 0`, so the inequality is `0 ≤ per M`.
The bound depends on the order of the columns (column `j` is capped at `j`)
and holds for every order; it is used with the columns in their given order. -/
def GurvitsCapacityInequality : Prop :=
  ∀ (n : ℕ) (M : Square n), Nonnegative M →
    capacity M * ∏ j : Fin n, gurvitsG (min (colDegree M j) (j.val + 1)) ≤ permanent M

/-- The entropy factor `t^t (1-t)^(1-t) = exp(-h₂(t))` on `[0, 1]`. -/
theorem entropyFactor_eq {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    t ^ t * (1 - t) ^ (1 - t) = exp (-binEntropy t) := by
  rcases h0.lt_or_eq with ht | ht
  · rcases h1.lt_or_eq with ht1 | ht1
    · have h1t : 0 < 1 - t := by linarith
      rw [Real.rpow_def_of_pos ht, Real.rpow_def_of_pos h1t, ← Real.exp_add,
        binEntropy_eq_negMulLog_add_negMulLog_one_sub, Real.negMulLog, Real.negMulLog]
      congr 1; ring
    · subst ht1; simp
  · subst ht; simp

section Capacity

variable {U V E : Type*} [Fintype U] [Fintype V] [Fintype E]
  [DecidableEq U] [DecidableEq V] [DecidableEq E] (row : E → U) (col : E → V) (v : U)

/-- A flow on the core with unit row and column sums, at most one off the
root row (as for the lift of a matrix on the shortened-star face). -/
structure StarFlow (x : E → ℝ) : Prop where
  nonneg : ∀ e, 0 ≤ x e
  le_one : ∀ e ∈ offRoot row v, x e ≤ 1
  row_sum : ∀ u, ∑ e ∈ rowSet row u, x e = 1
  col_sum : ∀ w, ∑ e ∈ (univ : Finset E).filter (fun e => col e = w), x e = 1

/-- `(M y)_u` at the core level. -/
noncomputable def rowSum (x : E → ℝ) (z : V → ℝ) (u : U) : ℝ :=
  ∑ e ∈ rowSet row u, elimWeight row v x e * z (col e)

variable {row col v} {x : E → ℝ}

theorem mem_rowSet {u : U} {e : E} : e ∈ rowSet row u ↔ row e = u := by
  simp [rowSet]

theorem mem_offRoot_of_rowSet {u : U} (hu : u ≠ v) {e : E} (he : e ∈ rowSet row u) :
    e ∈ offRoot row v := by
  simp only [offRoot, mem_filter, mem_univ, true_and]
  rw [mem_rowSet.1 he]; exact hu

theorem elimWeight_nonneg (hx : StarFlow row col v x) (e : E) : 0 ≤ elimWeight row v x e := by
  unfold elimWeight
  refine mul_nonneg (hx.nonneg e) ?_
  split_ifs with h
  · exact zero_le_one
  · refine mul_nonneg (hx.nonneg e) (Finset.prod_nonneg fun f hf => ?_)
    have hf' := mem_rowSet.1 (Finset.mem_erase.1 hf).2
    have := hx.le_one f (by
      simp only [offRoot, mem_filter, mem_univ, true_and]; rw [hf']; exact h)
    linarith

/-- Concavity of binary entropy on one row. -/
theorem sum_binEntropy_le {s : Finset E} (hs : s.Nonempty) (hx0 : ∀ e ∈ s, 0 ≤ x e)
    (hx1 : ∀ e ∈ s, x e ≤ 1) (hsum : ∑ e ∈ s, x e = 1) :
    ∑ e ∈ s, binEntropy (x e) ≤ s.card * binEntropy (1 / s.card) := by
  have hc : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hJ := strictConcave_binEntropy.concaveOn.le_map_sum (t := s) (w := fun _ => 1 / (s.card : ℝ))
    (p := fun e => x e) (fun _ _ => by positivity)
    (by rw [Finset.sum_const, nsmul_eq_mul]; field_simp)
    (fun e he => ⟨hx0 e he, hx1 e he⟩)
  simp only [smul_eq_mul] at hJ
  rw [← Finset.mul_sum, ← Finset.mul_sum, hsum, mul_one] at hJ
  have := mul_le_mul_of_nonneg_left hJ hc.le
  rwa [← mul_assoc, mul_one_div_cancel hc.ne', one_mul] at this

/-- **Lavi (5.3)** at a nonroot row, with concavity:
`(M y)_u ≥ (A_r / 2^r) ∏_{e ∈ S_u} y_{col e}^{x_e}`, `r = |S_u| ≥ 2`. -/
theorem rowSum_nonroot_ge (hx : StarFlow row col v x) {z : V → ℝ} (hz : ∀ w, 0 < z w) {u : U}
    (hu : u ≠ v) (hr : 2 ≤ (rowSet row u).card) :
    rowFactor (rowSet row u).card / 2 ^ (rowSet row u).card *
        ∏ e ∈ rowSet row u, z (col e) ^ x e ≤ rowSum row col v x z u := by
  set S := rowSet row u with hS
  have hne : S.Nonempty := Finset.card_pos.1 (by omega)
  have hx1 : ∀ e ∈ S, x e ≤ 1 := fun e he => hx.le_one e (mem_offRoot_of_rowSet hu he)
  have hx0 : ∀ e ∈ S, 0 ≤ x e := fun e _ => hx.nonneg e
  have hsum : ∑ e ∈ S, x e = 1 := hx.row_sum u
  -- entropy factors and the concavity bound
  have hEF : rowFactor S.card / 2 ^ S.card ≤ ∏ e ∈ S, (x e ^ x e * (1 - x e) ^ (1 - x e)) := by
    rw [Finset.prod_congr rfl fun e he => entropyFactor_eq (hx0 e he) (hx1 e he),
      ← Real.exp_sum, rowFactor_eq_exp hr, mul_div_cancel_left₀ _ (by positivity)]
    apply Real.exp_le_exp.2
    rw [Finset.sum_neg_distrib, neg_le_neg_iff]
    exact sum_binEntropy_le hne hx0 hx1 hsum
  have hzpow : 0 ≤ ∏ e ∈ S, z (col e) ^ x e :=
    Finset.prod_nonneg fun e _ => Real.rpow_nonneg (hz _).le _
  have hrow : ∀ e ∈ S, row e = u := fun e he => mem_rowSet.1 he
  have hw : ∀ e ∈ S, elimWeight row v x e = x e * (x e * ∏ f ∈ S.erase e, (1 - x f)) := by
    intro e he
    unfold elimWeight
    rw [if_neg (by rw [hrow e he]; exact hu), hrow e he]
  -- the AM–GM bound for the row sum
  have key : (∏ e ∈ S, (x e ^ x e * (1 - x e) ^ (1 - x e))) * ∏ e ∈ S, z (col e) ^ x e ≤
      rowSum row col v x z u := by
    unfold rowSum
    rw [← hS, Finset.sum_congr rfl fun e he => by rw [hw e he]]
    by_cases hone : ∃ e₀ ∈ S, x e₀ = 1
    · obtain ⟨e₀, he₀, hx₀⟩ := hone
      have hzero : ∀ f ∈ S, f ≠ e₀ → x f = 0 := by
        have hs' : ∑ f ∈ S.erase e₀, x f = 0 := by
          have := Finset.add_sum_erase S x he₀; rw [hx₀] at this; linarith
        intro f hf hfe
        exact (Finset.sum_eq_zero_iff_of_nonneg fun g hg => hx0 g (Finset.mem_of_mem_erase hg)).1
          hs' f (Finset.mem_erase.2 ⟨hfe, hf⟩)
      have h1 : ∏ e ∈ S, (x e ^ x e * (1 - x e) ^ (1 - x e)) = 1 := by
        refine Finset.prod_eq_one fun e he => ?_
        by_cases h : e = e₀
        · subst h; rw [hx₀]; simp
        · rw [hzero e he h]; simp
      have h2 : ∏ e ∈ S, z (col e) ^ x e = z (col e₀) := by
        rw [Finset.prod_eq_single_of_mem e₀ he₀ fun b hb hbe => by rw [hzero b hb hbe]; simp,
          hx₀, Real.rpow_one]
      rw [h1, h2, one_mul]
      have hterm : x e₀ * (x e₀ * ∏ f ∈ S.erase e₀, (1 - x f)) * z (col e₀) = z (col e₀) := by
        rw [hx₀, Finset.prod_eq_one fun f hf => by
          rw [hzero f (Finset.mem_of_mem_erase hf) (Finset.ne_of_mem_erase hf)]; ring]
        ring
      rw [← hterm]
      refine Finset.single_le_sum (f := fun e => x e * (x e * ∏ f ∈ S.erase e, (1 - x f)) *
        z (col e)) (fun e he => ?_) he₀
      refine mul_nonneg (mul_nonneg (hx0 e he) (mul_nonneg (hx0 e he)
        (Finset.prod_nonneg fun f hf => ?_))) (hz _).le
      linarith [hx1 f (Finset.mem_of_mem_erase hf)]
    · push Not at hone
      have hlt : ∀ e ∈ S, x e < 1 := fun e he => lt_of_le_of_ne (hx1 e he) (hone e he)
      set P := ∏ f ∈ S, (1 - x f) with hP
      have hPpos : 0 < P := Finset.prod_pos fun f hf => by linarith [hlt f hf]
      have herase : ∀ e ∈ S, ∏ f ∈ S.erase e, (1 - x f) = P / (1 - x e) := by
        intro e he
        have h1e : (1 - x e) ≠ 0 := by linarith [hlt e he]
        rw [eq_div_iff h1e, mul_comm]
        exact Finset.mul_prod_erase S (fun f => 1 - x f) he
      set ζ : E → ℝ := fun e => x e * z (col e) / (1 - x e) with hζ
      have hsumP : ∑ e ∈ S, x e * (x e * ∏ f ∈ S.erase e, (1 - x f)) * z (col e) =
          P * ∑ e ∈ S, x e * ζ e := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun e he => ?_
        rw [herase e he, hζ]
        have h1e : (1 - x e) ≠ 0 := by linarith [hlt e he]
        field_simp
      rw [hsumP]
      have hamgm := Real.geom_mean_le_arith_mean_weighted S x ζ hx0 hsum (fun e he =>
        div_nonneg (mul_nonneg (hx0 e he) (hz _).le) (by linarith [hlt e he]))
      have hident : (∏ e ∈ S, (x e ^ x e * (1 - x e) ^ (1 - x e))) * ∏ e ∈ S, z (col e) ^ x e =
          P * ∏ e ∈ S, ζ e ^ x e := by
        rw [← Finset.prod_mul_distrib, hP, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun e he => ?_
        have h1e : 0 < 1 - x e := by linarith [hlt e he]
        rw [hζ]
        simp only
        rw [Real.div_rpow (mul_nonneg (hx0 e he) (hz _).le) h1e.le,
          Real.mul_rpow (hx0 e he) (hz _).le, Real.rpow_sub h1e, Real.rpow_one]
        field_simp
      rw [hident]
      exact mul_le_mul_of_nonneg_left hamgm hPpos.le
  calc rowFactor S.card / 2 ^ S.card * ∏ e ∈ S, z (col e) ^ x e
      ≤ (∏ e ∈ S, (x e ^ x e * (1 - x e) ^ (1 - x e))) * ∏ e ∈ S, z (col e) ^ x e :=
        mul_le_mul_of_nonneg_right hEF hzpow
    _ ≤ rowSum row col v x z u := key

/-- **Lavi (5.3)** at the root row: `(M y)_v ≥ ∏_{e ∈ S_v} y_{col e}^{x_e}`. -/
theorem rowSum_root_ge (hx : StarFlow row col v x) {z : V → ℝ} (hz : ∀ w, 0 < z w) :
    ∏ e ∈ rowSet row v, z (col e) ^ x e ≤ rowSum row col v x z v := by
  unfold rowSum
  have hw : ∀ e ∈ rowSet row v, elimWeight row v x e * z (col e) = x e * z (col e) := by
    intro e he
    unfold elimWeight
    rw [if_pos (mem_rowSet.1 he), mul_one]
  rw [Finset.sum_congr rfl hw]
  exact Real.geom_mean_le_arith_mean_weighted _ x _ (fun e _ => hx.nonneg e) (hx.row_sum v)
    (fun e _ => (hz _).le)

/-- The `y`-powers cancel against the column sums. -/
theorem prod_rpow_col (hx : StarFlow row col v x) {z : V → ℝ} (hz : ∀ w, 0 < z w) :
    ∏ e, z (col e) ^ x e = ∏ w, z w := by
  rw [← Finset.prod_fiberwise univ col (fun e => z (col e) ^ x e)]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [Finset.prod_congr rfl fun e he => by rw [(Finset.mem_filter.1 he).2],
    ← Real.rpow_sum_of_pos (hz w), hx.col_sum w, Real.rpow_one]

/-- The row lower bounds multiply to the capacity bound. -/
theorem prod_rowSum_ge (hx : StarFlow row col v x) {z : V → ℝ} (hz : ∀ w, 0 < z w)
    (hr : ∀ u, 2 ≤ (rowSet row u).card) :
    (∏ u ∈ (univ : Finset U).erase v,
        rowFactor (rowSet row u).card / 2 ^ (rowSet row u).card) * ∏ w, z w ≤
      ∏ u, rowSum row col v x z u := by
  set lower : U → ℝ := fun u =>
    (if u = v then 1 else rowFactor (rowSet row u).card / 2 ^ (rowSet row u).card) *
      ∏ e ∈ rowSet row u, z (col e) ^ x e with hlower
  have hle : ∏ u, lower u ≤ ∏ u, rowSum row col v x z u := by
    refine Finset.prod_le_prod (fun u _ => ?_) fun u _ => ?_
    · refine mul_nonneg ?_ (Finset.prod_nonneg fun e _ => Real.rpow_nonneg (hz _).le _)
      split_ifs
      · exact zero_le_one
      · refine div_nonneg ?_ (by positivity)
        rw [rowFactor_eq_exp (hr u)]; positivity
    · by_cases h : u = v
      · simp only [hlower, if_pos h, one_mul]; subst h; exact rowSum_root_ge hx hz
      · simp only [hlower, if_neg h]; exact rowSum_nonroot_ge hx hz h (hr u)
  refine le_trans (le_of_eq ?_) hle
  rw [Finset.prod_mul_distrib]
  congr 1
  · rw [← Finset.prod_erase_mul _ _ (mem_univ v), if_pos rfl, mul_one]
    exact Finset.prod_congr rfl fun u hu => by rw [if_neg (Finset.ne_of_mem_erase hu)]
  · rw [← prod_rpow_col hx hz, ← Finset.prod_fiberwise univ row (fun e => z (col e) ^ x e)]
    rfl

/-- `(M z)_i` for the aggregated matrix is the core row sum. -/
theorem aggregateMatrix_mulVec {k : ℕ} (eR : Fin k ≃ U) (eC : Fin k ≃ V) (w : E → ℝ)
    (z : Fin k → ℝ) (i : Fin k) :
    ∑ j, aggregateMatrix row col eR eC w i j * z j =
      ∑ e ∈ rowSet row (eR i), w e * z (eC.symm (col e)) := by
  classical
  unfold aggregateMatrix mergeFlow
  simp_rw [Finset.sum_mul]
  rw [← Finset.sum_fiberwise (rowSet row (eR i)) (fun e => eC.symm (col e))
    (fun e => w e * z (eC.symm (col e)))]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr ?_ fun e he => ?_
  · ext e
    simp only [mem_filter, mem_univ, true_and, rowSet, Prod.ext_iff, Equiv.symm_apply_eq]
  · have : eC.symm (col e) = j := (Finset.mem_filter.1 he).2
    rw [this]

/-- **Lavi (5.4)** with concavity: `Cap(M) ≥ ∏_{i ≠ v} A_{r_i} / 2^{r_i}`. -/
theorem capacity_elim_ge {k : ℕ} (eR : Fin k ≃ U) (eC : Fin k ≃ V) (hx : StarFlow row col v x)
    (hr : ∀ u, 2 ≤ (rowSet row u).card) :
    ∏ u ∈ (univ : Finset U).erase v, rowFactor (rowSet row u).card / 2 ^ (rowSet row u).card ≤
      capacity (aggregateMatrix row col eR eC (elimWeight row v x)) := by
  refine le_csInf ⟨_, fun _ => 1, fun _ => one_pos, rfl⟩ ?_
  rintro _ ⟨z, hz, rfl⟩
  have hz' : ∀ w, 0 < z (eC.symm w) := fun w => hz _
  have h := prod_rowSum_ge hx hz' hr
  have hprodz : ∏ w, z (eC.symm w) = ∏ j, z j := Equiv.prod_comp eC.symm z
  have hrows : ∏ u, rowSum row col v x (fun w => z (eC.symm w)) u =
      ∏ i, ∑ j, aggregateMatrix row col eR eC (elimWeight row v x) i j * z j := by
    rw [← Equiv.prod_comp eR]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [aggregateMatrix_mulVec]
    rfl
  rw [hprodz, hrows] at h
  rw [le_div_iff₀ (Finset.prod_pos fun j _ => hz j)]
  exact h

/-! ### Degree bookkeeping -/

variable (row col v)

/-- Lavi's `c_w`: nonroot occurrences ending at `w`, plus one if `v` meets `w`. -/
noncomputable def colCount (w : V) : ℕ := by
  classical exact ((offRoot row v).filter fun e => col e = w).card +
    if ∃ e ∈ rowSet row v, col e = w then 1 else 0

variable {row col v}

/-- `Δ_j ≤ c_j`, even with parallel occurrences. -/
theorem colDegree_elim_le {k : ℕ} (eR : Fin k ≃ U) (eC : Fin k ≃ V) (j : Fin k) :
    colDegree (aggregateMatrix row col eR eC (elimWeight row v x)) j ≤ colCount row col v (eC j) := by
  classical
  unfold colDegree colCount
  set F := (univ : Finset (Fin k)).filter
    (fun i => aggregateMatrix row col eR eC (elimWeight row v x) i j ≠ 0)
  have hedge : ∀ i ∈ F, ∃ e, row e = eR i ∧ col e = eC j := by
    intro i hi
    have h := (Finset.mem_filter.1 hi).2
    unfold aggregateMatrix mergeFlow at h
    obtain ⟨e, he, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    exact ⟨e, (Prod.ext_iff.1 (Finset.mem_filter.1 he).2).1,
      (Prod.ext_iff.1 (Finset.mem_filter.1 he).2).2⟩
  rw [← Finset.card_filter_add_card_filter_not (s := F) (fun i => eR i = v), add_comm]
  apply add_le_add
  · -- nonroot rows inject into the nonroot occurrences ending at the column
    have hsub : (F.filter fun i => ¬ eR i = v).map eR.toEmbedding ⊆
        ((offRoot row v).filter fun e => col e = eC j).image row := by
      intro u hu
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.1 hu
      obtain ⟨hiF, hiv⟩ := Finset.mem_filter.1 hi
      obtain ⟨e, hr, hc⟩ := hedge i hiF
      refine Finset.mem_image.2 ⟨e, Finset.mem_filter.2 ⟨?_, hc⟩, hr⟩
      simp only [offRoot, mem_filter, mem_univ, true_and]; rw [hr]; exact hiv
    calc (F.filter fun i => ¬ eR i = v).card
        = ((F.filter fun i => ¬ eR i = v).map eR.toEmbedding).card := (Finset.card_map _).symm
      _ ≤ (((offRoot row v).filter fun e => col e = eC j).image row).card := card_le_card hsub
      _ ≤ _ := Finset.card_image_le
  · -- the root row contributes at most one
    split_ifs with hroot
    · have hsub : (F.filter fun i => eR i = v).map eR.toEmbedding ⊆ {v} := by
        intro u hu
        obtain ⟨i, hi, rfl⟩ := Finset.mem_map.1 hu
        exact Finset.mem_singleton.2 (Finset.mem_filter.1 hi).2
      calc (F.filter fun i => eR i = v).card
          = ((F.filter fun i => eR i = v).map eR.toEmbedding).card := (Finset.card_map _).symm
        _ ≤ ({v} : Finset U).card := card_le_card hsub
        _ = 1 := Finset.card_singleton v
    · rw [Nat.le_zero, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro i hi
      obtain ⟨hiF, hiv⟩ := Finset.mem_filter.1 hi
      obtain ⟨e, hr, hc⟩ := hedge i hiF
      exact hroot ⟨e, mem_rowSet.2 (hr.trans hiv), hc⟩

/-- Every `c_w ≥ 3` when every column has at least three distinct neighbors. -/
theorem three_le_colCount (hC : ∀ w, 3 ≤ (((univ : Finset E).filter fun e => col e = w).image row).card)
    (w : V) : 3 ≤ colCount row col v w := by
  classical
  unfold colCount
  have hsub : ((univ : Finset E).filter fun e => col e = w).image row ⊆
      (((offRoot row v).filter fun e => col e = w).image row) ∪
        (if ∃ e ∈ rowSet row v, col e = w then {v} else ∅) := by
    intro u hu
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hu
    have hc := (Finset.mem_filter.1 he).2
    by_cases hv : row e = v
    · refine Finset.mem_union_right _ ?_
      rw [if_pos ⟨e, mem_rowSet.2 hv, hc⟩]; exact Finset.mem_singleton.2 hv
    · refine Finset.mem_union_left _ (Finset.mem_image.2 ⟨e, Finset.mem_filter.2 ⟨?_, hc⟩, rfl⟩)
      simp only [offRoot, mem_filter, mem_univ, true_and]; exact hv
  have h1 := (hC w).trans ((card_le_card hsub).trans (Finset.card_union_le _ _))
  have h2 : (((offRoot row v).filter fun e => col e = w).image row).card ≤
      ((offRoot row v).filter fun e => col e = w).card := Finset.card_image_le
  have h3 : (if ∃ e ∈ rowSet row v, col e = w then ({v} : Finset U) else ∅).card ≤
      if ∃ e ∈ rowSet row v, col e = w then 1 else 0 := by
    split_ifs <;> simp
  omega

/-- **Lavi (5.6):** `∑_w c_w ≤ ℓ + k`. -/
theorem sum_colCount_le :
    ∑ w, colCount row col v w ≤ (offRoot row v).card + Fintype.card V := by
  classical
  unfold colCount
  rw [Finset.sum_add_distrib, ← Finset.card_eq_sum_card_fiberwise (fun e _ => mem_univ (col e))]
  apply Nat.add_le_add_left
  calc ∑ w, (if ∃ e ∈ rowSet row v, col e = w then 1 else 0) ≤ ∑ _w : V, 1 :=
        Finset.sum_le_sum fun w _ => by split_ifs <;> simp
    _ = Fintype.card V := by simp

/-- `∑_{u ≠ v} r_u = ℓ`. -/
theorem sum_rowSet_card :
    ∑ u ∈ (univ : Finset U).erase v, (rowSet row u).card = (offRoot row v).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := row) (t := univ) (fun e _ => mem_univ _),
    ← Finset.sum_erase_add _ _ (mem_univ v)]
  rw [offRoot_filter_row, if_pos rfl, Finset.card_empty, add_zero]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [offRoot_filter_row, if_neg (Finset.ne_of_mem_erase hu)]

end Capacity

end LaviSection2
