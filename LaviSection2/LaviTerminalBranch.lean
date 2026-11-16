import LaviSection2.LaviTerminalBridge
import LaviSection2.LaviFourVertexLeaf

/-!
# Lavi Section 7: the terminal branch

Let `D` be a terminal nearly decomposable support of order `n ≥ 3`.  By
Lemma 2.5, `D = D_can(H)` for a balanced FI occurrence core `H`, of order `h`
and minimum occurrence degree at least three.  A permanent minimizer `A` on
`Ω(D)` has support exactly `D` (Lemma 2.1), so it is the expanded matrix `X_x`
of a positive feasible core flow `x`.  Section 7 of the manuscript shows

`G_{H,L(H)}(x) > 0` at every positive core flow `x`,

and then (3.7) with the first inequality of (3.3) gives `per A > 2^(1-n)`.
The gap is positive in four cases, proved here in this order:

* `h = 1`: the core is a bundle of `q ≥ 3` occurrences, `F_H = 0`, and
  (7.2) reads `G = ∑ δ(x_e) ≥ q δ(1/q) = log (2^q (q-1)^(q-1) / q^q) > 0`
  (`lavi_eq_7_2`, `gap_pos_order_one`).  The remark after (7.2) is proved as
  well: `(q-1)^(q-1) / q^q` is the minimum of the permanent on this face,
  attained at the uniform flow (`permanent_ge_order_one`,
  `lavi_eq_7_2_sharp`);
* `h = 2`: `G = δ(t) + ∑_{long} δ(x_e)` by (6.4) without a marker, and a
  parallel pair forced by the degrees makes it positive (`gap_pos_order_two`);
* `h ≥ 3` and no nontrivial tight cut: Lemma 6.1 makes every occurrence
  removable, Corollary 5.2 bounds the gap of one shortened star, and making
  the star paths long again only adds charges (`gap_ge_cutFree`,
  `gap_pos_cutFree`);
* `h ≥ 3` with a nontrivial tight cut: Lemma 6.2 gives a leaf, (6.5) shows
  that the remainder `R` has smaller order (`ShoreCut.remainder_lt₁`,
  `remainder_lt₂`), the induction hypothesis gives `G_R ≥ 0`
  (`canonical_gap_nonneg`), and (6.1) or Lemma 6.3 with (4.5) make the gap
  positive (`ShoreCut.gap_pos_of_leaf₁`, `gap_pos_of_leaf₂`,
  `gap_pos_tightCut`).

`terminal_gap_pos` assembles the four cases at the core level, and
`terminal_interior_strict`, `terminal_branch_strict`, `terminal_face_strict`
are the conclusions for matrices: an interior point, in particular a
permanent minimizer, hence every point of a terminal face has permanent
strictly above `2^(1-n)`.

As in `LaviTerminalBridge`, a flow is *feasible* when it is the vector of
marginals of a law on labelled perfect matchings (`IsCoreLaw row col x μ`).

Two hypotheses are explicit throughout.

* `hG : GurvitsCapacityInequality` is Gurvits's capacity inequality, an
  external theorem that is not proved in this development.  It enters only
  through Corollary 5.2, that is, in the cases `h ≥ 3`.
* The induction hypothesis `hIH` is the Foregger bound on the whole face
  `Ω(D')` of every nearly decomposable support `D'` of smaller order.  The
  manuscript's induction hypothesis is Theorem 1.1 in smaller order, a bound
  for matrices whose support is exactly `D'`; it passes to the whole face
  through Lemma 2.1.  That passage is not made here.

The other parts of Section 7 (cycle faces, the contraction branch (7.1) and
the equality classification) are not treated in this file.
-/

namespace LaviSection2

open Finset

/-! ### Order one: the quantitative statement (7.2) -/

private theorem permanent_eq_one_of_order_one {X : Square 1} (hX : DoublyStochastic X) :
    permanent X = 1 := by
  have h00 : X 0 0 = 1 := by
    have h := hX.2.1 0
    rwa [Fin.sum_univ_one] at h
  unfold permanent
  rw [Fintype.sum_eq_single 1 fun σ h => absurd (Subsingleton.elim σ 1) h, Fin.prod_univ_one,
    Equiv.Perm.one_apply, h00]

/-- `F(X) = 0` for the `1 × 1` doubly stochastic matrix, by both inequalities
of Lemma 3.1. -/
private theorem faceFunctional_eq_zero_of_order_one {X : Square 1} (hX : DoublyStochastic X) :
    faceFunctional X = 0 := by
  have hup := faceFunctional_le_log_permanent (m := 0) hX
  obtain ⟨Y, hY, -, hlow⟩ := exists_inFace_log_permanent_le_faceFunctional (m := 0)
    (D := fun _ _ => True) (X := X) ⟨hX, fun _ _ _ => trivial⟩
  rw [permanent_eq_one_of_order_one hX, Real.log_one] at hup
  rw [permanent_eq_one_of_order_one hY.1, Real.log_one] at hlow
  exact le_antisymm hup hlow

/-- The row factor of (5.7) exceeds one from `q = 3` on:
`A_q = 2^q (q-1)^(q-1) / q^q > 1`.  It gives the final inequality
`log A_q > 0` of (7.2). -/
theorem one_lt_rowFactor {q : ℕ} (hq : 3 ≤ q) : 1 < rowFactor q :=
  calc (1 : ℝ) < 32 / 27 * 1 := by norm_num
    _ ≤ 32 / 27 * (729 / 512) ^ (q - 3) :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ (by norm_num)) (by norm_num)
    _ ≤ rowFactor q := rowFactor_secant hq

/-- The equality `q δ(1/q) = log (2^q (q-1)^(q-1) / q^q)` of (7.2), for
`q ≥ 2`; the constant on the right is `rowFactor q`, the row factor `A_q` of
(5.7). -/
theorem log_rowFactor_eq {q : ℕ} (hq : 2 ≤ q) :
    Real.log (rowFactor q) = (q : ℝ) * subdivCharge (1 / q) := by
  rw [rowFactor_eq_exp hq, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_pow,
    Real.log_exp]
  unfold subdivCharge
  ring

/-- The total weight of `q` matchings, each of weight `q⁻² (1 - 1/q)^(q-1)`. -/
private theorem uniform_weight_arith {q : ℕ} (hq : 1 ≤ q) :
    (q : ℝ) * (1 / q * (1 / q * (1 - 1 / q) ^ (q - 1))) =
      ((q : ℝ) - 1) ^ (q - 1) / (q : ℝ) ^ q := by
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
  have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [Nat.add_sub_cancel, pow_succ,
    show (1 : ℝ) - 1 / ((k + 1 : ℕ) : ℝ) = (((k + 1 : ℕ) : ℝ) - 1) / ((k + 1 : ℕ) : ℝ) by
      field_simp,
    div_pow]
  field_simp

section Cores

variable {U V E : Type*} [Fintype U] [Fintype V] [Fintype E]
  [DecidableEq U] [DecidableEq V] [DecidableEq E] {row : E → U} {col : E → V}

/-- The concavity step of (7.2): if the numbers `x_e ∈ [0, 1]`, `e ∈ s`, sum to
one, then `∑_{e ∈ s} δ(x_e) ≥ q δ(1/q)` with `q = |s|` (concavity of binary
entropy, `sum_binEntropy_le`). -/
theorem card_mul_subdivCharge_le_sum {x : E → ℝ} {s : Finset E} (hs : s.Nonempty)
    (hx0 : ∀ e ∈ s, 0 ≤ x e) (hx1 : ∀ e ∈ s, x e ≤ 1) (hsum : ∑ e ∈ s, x e = 1) :
    (s.card : ℝ) * subdivCharge (1 / s.card) ≤ ∑ e ∈ s, subdivCharge (x e) := by
  have h := sum_binEntropy_le hs hx0 hx1 hsum
  unfold subdivCharge
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  linarith

/-- The inequality of (7.2) in one step: if the numbers `x_e ∈ [0, 1]`,
`e ∈ s`, sum to one and `q = |s| ≥ 2`, then
`∑_{e ∈ s} δ(x_e) ≥ log (2^q (q-1)^(q-1) / q^q)`. -/
theorem log_rowFactor_le_sum_subdivCharge {x : E → ℝ} {s : Finset E} (hs : 2 ≤ s.card)
    (hx0 : ∀ e ∈ s, 0 ≤ x e) (hx1 : ∀ e ∈ s, x e ≤ 1) (hsum : ∑ e ∈ s, x e = 1) :
    Real.log (rowFactor s.card) ≤ ∑ e ∈ s, subdivCharge (x e) := by
  rw [log_rowFactor_eq hs]
  exact card_mul_subdivCharge_le_sum (Finset.card_pos.1 (by omega)) hx0 hx1 hsum

/-- The core functional vanishes in order one ("here `F_H = 0`", Section 7,
case `h = 1`), at every feasible flow. -/
theorem coreFunctional_order_one (hbal : Fintype.card U = Fintype.card V)
    (hU : Fintype.card U = 1) {x : E → ℝ} {μ : LMatch row col → ℝ}
    (hμ : IsCoreLaw row col x μ) : coreFunctional row col x = 0 := by
  have eR : Fin 1 ≃ U := (Fintype.equivFinOfCardEq hU).symm
  have eC : Fin 1 ≃ V := (Fintype.equivFinOfCardEq (hbal ▸ hU)).symm
  rw [coreFunctional_eq_faceFunctional eR eC ⟨μ, hμ⟩]
  exact faceFunctional_eq_zero_of_order_one (doublyStochastic_aggregate_of_law eR eC hμ)

/-- In order one the normalized gap is the sum of the subdivision charges of
the long occurrences: `G_{H,L}(x) = ∑_{ℓ ∈ L} δ(x_ℓ)` (the equality of (7.2),
for any set `L` of long occurrences), at every feasible flow. -/
theorem normalizedGap_order_one (hbal : Fintype.card U = Fintype.card V)
    (hU : Fintype.card U = 1) {x : E → ℝ} {μ : LMatch row col → ℝ}
    (hμ : IsCoreLaw row col x μ) (L : Finset E) :
    normalizedGap row col L x = ∑ ℓ ∈ L, subdivCharge (x ℓ) := by
  unfold normalizedGap
  rw [coreFunctional_order_one hbal hU hμ, hU, Nat.cast_one, sub_self, zero_mul, zero_add,
    zero_add]

/-- In a core of order one with at least two occurrences every occurrence is
removable ("a bundle of `q ≥ 3` occurrences, all removable and hence long in
`D_can(H)`", Section 7, case `h = 1`). -/
theorem removableSet_eq_univ_order_one (hU : Fintype.card U = 1) (hE : 2 ≤ Fintype.card E) :
    removableSet row col univ = univ := by
  haveI : Subsingleton U := Fintype.card_le_one_iff_subsingleton.1 hU.le
  rw [eq_univ_iff_forall]
  intro e
  refine (mem_removableSet row col).2 ⟨mem_univ _, fun R hR hRc => ?_, fun u => ?_⟩
  · have := hR.card_pos
    omega
  · obtain ⟨f, hf⟩ : ((univ : Finset E).erase e).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem (mem_univ e), Finset.card_univ]
      omega
    exact ⟨f, hf, Subsingleton.elim _ _⟩

/-- **Lavi (7.2).**  Let `H` be a balanced core of order one with
`q = |E| ≥ 3` occurrences, and `x` a feasible flow.  Then

`G_{H,L(H)}(x) = ∑_e δ(x_e) ≥ q δ(1/q) = log (2^q (q-1)^(q-1) / q^q) > 0`,

where `rowFactor q = 2^q (q-1)^(q-1) / q^q`.  The four conjuncts are the four
relations of the display, in this order.  The first uses `F_H = 0` and the
fact that all occurrences are removable, the second is concavity of binary
entropy.  Positivity of the flow is not needed. -/
theorem lavi_eq_7_2 (hbal : Fintype.card U = Fintype.card V) (hU : Fintype.card U = 1)
    (hq : 3 ≤ Fintype.card E) {x : E → ℝ} {μ : LMatch row col → ℝ}
    (hμ : IsCoreLaw row col x μ) :
    normalizedGap row col (removableSet row col univ) x = ∑ e, subdivCharge (x e) ∧
      (Fintype.card E : ℝ) * subdivCharge (1 / Fintype.card E) ≤ ∑ e, subdivCharge (x e) ∧
      (Fintype.card E : ℝ) * subdivCharge (1 / Fintype.card E) =
        Real.log (rowFactor (Fintype.card E)) ∧
      0 < Real.log (rowFactor (Fintype.card E)) := by
  haveI : Subsingleton U := Fintype.card_le_one_iff_subsingleton.1 hU.le
  obtain ⟨u⟩ : Nonempty U := Fintype.card_pos_iff.1 (by omega)
  have huniv : rowSet row u = univ :=
    eq_univ_iff_forall.2 fun e => mem_rowSet.2 (Subsingleton.elim _ _)
  have hsum : ∑ e, x e = 1 := huniv ▸ hμ.rowSet_sum u
  have hx0 : ∀ e ∈ (univ : Finset E), 0 ≤ x e := fun e _ => hμ.nonneg_edge e
  have hx1 : ∀ e ∈ (univ : Finset E), x e ≤ 1 := fun e he => by
    rw [← hsum]
    exact Finset.single_le_sum hx0 he
  have hne : (univ : Finset E).Nonempty := Finset.card_pos.1 (by rw [Finset.card_univ]; omega)
  refine ⟨?_, ?_, (log_rowFactor_eq (by omega)).symm, Real.log_pos (one_lt_rowFactor hq)⟩
  · rw [normalizedGap_order_one hbal hU hμ, removableSet_eq_univ_order_one hU (by omega)]
  · have h := card_mul_subdivCharge_le_sum hne hx0 hx1 hsum
    rwa [Finset.card_univ] at h

/-- **Section 7, terminal core of order one.**  For a balanced core of order
one and minimum occurrence degree at least three, `G_{H,L(H)}(x) > 0` at every
feasible flow, by (7.2). -/
theorem gap_pos_order_one (hbal : Fintype.card U = Fintype.card V) (hU : Fintype.card U = 1)
    (hmin : MinOccDegreeThree row col univ) {x : E → ℝ} {μ : LMatch row col → ℝ}
    (hμ : IsCoreLaw row col x μ) :
    0 < normalizedGap row col (removableSet row col univ) x := by
  obtain ⟨u⟩ : Nonempty U := Fintype.card_pos_iff.1 (by omega)
  have hq : 3 ≤ Fintype.card E := (hmin.1 u).trans (Finset.card_le_univ _)
  obtain ⟨h1, h2, h3, h4⟩ := lavi_eq_7_2 hbal hU hq hμ
  rw [h1]
  linarith

/-! ### Order one: the face minimum (the remark after (7.2)) -/

/-- **The face bound after (7.2)** ("by (3.3) and (3.7), (7.2) gives
`per X ≥ (q-1)^(q-1) / q^q` throughout this face").  Let `H` be a balanced core
of order one with `q = |E| ≥ 3` occurrences.  Every doubly stochastic matrix
on the canonical expansion `D_can(H)` has permanent at least
`(q-1)^(q-1) / q^q`. -/
theorem permanent_ge_order_one (hbal : Fintype.card U = Fintype.card V)
    (hU : Fintype.card U = 1) (hq : 3 ≤ Fintype.card E) {m : ℕ}
    (eR : Fin (m + 1) ≃ U ⊕ ↥(removableSet row col univ))
    (eC : Fin (m + 1) ≃ V ⊕ ↥(removableSet row col univ)) {A : Square (m + 1)}
    (hA : InFace (expSupport row col (removableSet row col univ) eR eC) A) :
    ((Fintype.card E : ℝ) - 1) ^ (Fintype.card E - 1) / (Fintype.card E : ℝ) ^ Fintype.card E ≤
      permanent A := by
  obtain ⟨μ, hμ⟩ := exists_isCoreLaw_liftFlow _ eR eC hA
  obtain ⟨h1, h2, h3, -⟩ := lavi_eq_7_2 hbal hU hq hμ
  have hm : m + 1 = Fintype.card U + (removableSet row col univ).card :=
    (lavi_eq_3_7 eR eC ⟨μ, hμ⟩).2
  rw [removableSet_eq_univ_order_one hU (by omega), Finset.card_univ, hU] at hm
  have hmq : m = Fintype.card E := by omega
  have hA0 : 0 < rowFactor (Fintype.card E) := lt_trans one_pos (one_lt_rowFactor hq)
  have hexp : rowFactor (Fintype.card E) ≤
      Real.exp (normalizedGap row col (removableSet row col univ)
        (liftFlow row col (removableSet row col univ) eR eC A)) := by
    rw [← Real.exp_log hA0, Real.exp_le_exp, h1, ← h3]
    exact h2
  have hT : (0 : ℝ) ≤ foreggerTarget (m + 1) := by
    unfold foreggerTarget
    positivity
  calc ((Fintype.card E : ℝ) - 1) ^ (Fintype.card E - 1) / (Fintype.card E : ℝ) ^ Fintype.card E
      = foreggerTarget (m + 1) * rowFactor (Fintype.card E) := by
        unfold foreggerTarget rowFactor
        rw [Nat.add_sub_cancel, hmq, mul_div_assoc, ← mul_assoc,
          inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero), one_mul]
    _ ≤ foreggerTarget (m + 1) * Real.exp (normalizedGap row col (removableSet row col univ)
          (liftFlow row col (removableSet row col univ) eR eC A)) :=
        mul_le_mul_of_nonneg_left hexp hT
    _ ≤ permanent A := permanent_ge_exp_gap _ eR eC hA

/-- In a balanced core of order one, the labelled perfect matchings are the
occurrences: each occurrence is the matching that selects it. -/
private noncomputable def orderOneMatchEquiv (row : E → U) (col : E → V)
    (hbal : Fintype.card U = Fintype.card V) (hU : Fintype.card U = 1) : E ≃ LMatch row col :=
  haveI : Subsingleton U := Fintype.card_le_one_iff_subsingleton.1 hU.le
  haveI : Subsingleton V := Fintype.card_le_one_iff_subsingleton.1 (hbal ▸ hU).le
  haveI : Nonempty U := Fintype.card_pos_iff.1 (by omega)
  { toFun := fun e => ⟨fun _ => e, fun _ => Subsingleton.elim _ _,
      fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨Classical.arbitrary U, Subsingleton.elim _ _⟩⟩
    invFun := fun M => M.1 (Classical.arbitrary U)
    left_inv := fun _ => rfl
    right_inv := fun M => Subtype.ext (funext fun _ => congrArg M.1 (Subsingleton.elim _ _)) }

/-- The uniform flow `x_e = 1/q` on a balanced core of order one with `q ≥ 1`
occurrences is feasible. -/
theorem exists_isCoreLaw_uniform_order_one (hbal : Fintype.card U = Fintype.card V)
    (hU : Fintype.card U = 1) (hq : 1 ≤ Fintype.card E) :
    ∃ μ, IsCoreLaw row col (fun _ : E => 1 / (Fintype.card E : ℝ)) μ := by
  haveI : Subsingleton U := Fintype.card_le_one_iff_subsingleton.1 hU.le
  haveI : Subsingleton V := Fintype.card_le_one_iff_subsingleton.1 (hbal ▸ hU).le
  have hq0 : (Fintype.card E : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hsum : ∀ s : Finset E, s = univ → ∑ _e ∈ s, 1 / (Fintype.card E : ℝ) = 1 := by
    rintro s rfl
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div_cancel hq0]
  exact exists_isCoreLaw_of_feasible hbal (fun _ => by positivity)
    (fun u => hsum _ (Finset.filter_true_of_mem fun _ _ => Subsingleton.elim _ _))
    (fun w => hsum _ (Finset.filter_true_of_mem fun _ _ => Subsingleton.elim _ _))

/-- **The permanent at the uniform flow** ("at the uniform flow `x_e = 1/q`,
its `q` matchings each have weight `q⁻² (1 - 1/q)^(q-1)`").  For a balanced
core of order one with `q = |E| ≥ 2` occurrences, the expanded matrix of the
uniform flow on `D_can(H)` has permanent `(q-1)^(q-1) / q^q`. -/
theorem permanent_expandedMatrix_uniform_order_one (hbal : Fintype.card U = Fintype.card V)
    (hU : Fintype.card U = 1) (hq : 2 ≤ Fintype.card E) {n : ℕ}
    (eR : Fin n ≃ U ⊕ ↥(removableSet row col univ))
    (eC : Fin n ≃ V ⊕ ↥(removableSet row col univ)) :
    permanent (expandedMatrix row col (removableSet row col univ) eR eC
        fun _ => 1 / (Fintype.card E : ℝ)) =
      ((Fintype.card E : ℝ) - 1) ^ (Fintype.card E - 1) /
        (Fintype.card E : ℝ) ^ Fintype.card E := by
  rw [permanent_expandedMatrix, removableSet_eq_univ_order_one hU hq,
    ← Equiv.sum_comp (orderOneMatchEquiv row col hbal hU)]
  have hterm : ∀ e : E,
      (∏ _u : U, (1 / (Fintype.card E : ℝ))) * ∏ ℓ ∈ (univ : Finset E),
        (if (orderOneMatchEquiv row col hbal hU e).1 (row ℓ) = ℓ then 1 / (Fintype.card E : ℝ)
          else 1 - 1 / (Fintype.card E : ℝ)) =
      1 / (Fintype.card E : ℝ) *
        (1 / (Fintype.card E : ℝ) * (1 - 1 / (Fintype.card E : ℝ)) ^ (Fintype.card E - 1)) := by
    intro e
    rw [Finset.prod_const, Finset.card_univ, hU, pow_one]
    congr 1
    change (∏ ℓ ∈ (univ : Finset E),
      if e = ℓ then 1 / (Fintype.card E : ℝ) else 1 - 1 / (Fintype.card E : ℝ)) = _
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, Finset.filter_eq,
      ite_eq_left (mem_univ e), Finset.card_singleton, pow_one, Finset.filter_ne,
      Finset.card_erase_of_mem (mem_univ e), Finset.card_univ]
  rw [Finset.sum_congr rfl fun e _ => hterm e, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact uniform_weight_arith (by omega)

/-- **The bound (7.2) is sharp** ("so equality holds and the face minimum is
`(q-1)^(q-1) / q^q = 2^(-q) A_q`").  Let `H` be a balanced core of order one
with `q = |E| ≥ 3` occurrences.  The expanded matrix of the uniform flow
`x_e = 1/q` minimizes the permanent on the face of `D_can(H)`, and its
permanent is `(q-1)^(q-1) / q^q`. -/
theorem lavi_eq_7_2_sharp (hbal : Fintype.card U = Fintype.card V) (hU : Fintype.card U = 1)
    (hq : 3 ≤ Fintype.card E) {m : ℕ}
    (eR : Fin (m + 1) ≃ U ⊕ ↥(removableSet row col univ))
    (eC : Fin (m + 1) ≃ V ⊕ ↥(removableSet row col univ)) :
    FaceMinimizer (expSupport row col (removableSet row col univ) eR eC)
        (expandedMatrix row col (removableSet row col univ) eR eC
          fun _ => 1 / (Fintype.card E : ℝ)) ∧
      permanent (expandedMatrix row col (removableSet row col univ) eR eC
          fun _ => 1 / (Fintype.card E : ℝ)) =
        ((Fintype.card E : ℝ) - 1) ^ (Fintype.card E - 1) /
          (Fintype.card E : ℝ) ^ Fintype.card E := by
  obtain ⟨μ, hμ⟩ :=
    exists_isCoreLaw_uniform_order_one (row := row) (col := col) hbal hU (by omega)
  have hval := permanent_expandedMatrix_uniform_order_one hbal hU (by omega) eR eC
  exact ⟨⟨inFace_expandedMatrix row col eR eC hμ,
    fun B hB => hval ▸ permanent_ge_order_one hbal hU hq eR eC hB⟩, hval⟩

/-! ### Order two: the `K_{2,2}` calculation -/

/-- In a core of order two, two parallel long occurrences force
`G_{H,L}(x) > 0` at every feasible flow.  By (6.4) without a marker,
`G = δ(t) + ∑_{ℓ ∈ L} δ(x_ℓ)` with `t` the flow of the bundle of the pair.  If
one of the two flows is not `1/2`, its charge is positive; if both are `1/2`,
then `t = 1` and `δ(1) = log 2 > 0`. -/
theorem normalizedGap_pos_order_two (hU : Fintype.card U = 2) (hV : Fintype.card V = 2)
    {x : E → ℝ} {μ : LMatch row col → ℝ} (hμ : IsCoreLaw row col x μ) {L : Finset E}
    {e f : E} (he : e ∈ L) (hf : f ∈ L) (hef : e ≠ f) (hrow : row f = row e)
    (hcol : col f = col e) : 0 < normalizedGap row col L x := by
  rw [normalizedGap_order_two hU hV hμ L (row e) (col e)]
  set B : Finset E := (univ : Finset E).filter fun e' => row e' = row e ∧ col e' = col e
  have hsumL : 0 ≤ ∑ ℓ ∈ L, subdivCharge (x ℓ) :=
    Finset.sum_nonneg fun ℓ _ => subdivCharge_nonneg (x ℓ)
  by_cases h : x e = 1 / 2 ∧ x f = 1 / 2
  · have hsub : ({e, f} : Finset E) ⊆ B :=
      Finset.insert_subset_iff.2 ⟨Finset.mem_filter.2 ⟨mem_univ _, rfl, rfl⟩,
        Finset.singleton_subset_iff.2 (Finset.mem_filter.2 ⟨mem_univ _, hrow, hcol⟩)⟩
    have hge : x e + x f ≤ ∑ e' ∈ B, x e' := by
      rw [← Finset.sum_pair hef]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun g _ _ => hμ.nonneg_edge g
    have hle : ∑ e' ∈ B, x e' ≤ 1 := by
      rw [← hμ.rowSet_sum (row e)]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun g hg => mem_rowSet.2 (Finset.mem_filter.1 hg).2.1) fun g _ _ => hμ.nonneg_edge g
    have ht : ∑ e' ∈ B, x e' = 1 := by linarith [h.1, h.2]
    rw [ht]
    have : 0 < subdivCharge 1 := subdivCharge_pos (by norm_num)
    linarith
  · have hpos : 0 < ∑ ℓ ∈ L, subdivCharge (x ℓ) := by
      rcases not_and_or.1 h with h | h
      · exact lt_of_lt_of_le (subdivCharge_pos h) (Finset.single_le_sum
          (f := fun ℓ => subdivCharge (x ℓ)) (fun ℓ _ => subdivCharge_nonneg _) he)
      · exact lt_of_lt_of_le (subdivCharge_pos h) (Finset.single_le_sum
          (f := fun ℓ => subdivCharge (x ℓ)) (fun ℓ _ => subdivCharge_nonneg _) hf)
    linarith [subdivCharge_nonneg (∑ e' ∈ B, x e')]

/-- **Section 7, terminal core of order two.**  For a balanced FI core of
order two and minimum occurrence degree at least three, `G_{H,L(H)}(x) > 0` at
every feasible flow: a row with three occurrences and two columns carries two
parallel occurrences, which are removable, hence long in `D_can(H)`.  The
manuscript argues at a positive flow; positivity is not needed here. -/
theorem gap_pos_order_two (hbal : Fintype.card U = Fintype.card V) (hU : Fintype.card U = 2)
    (hFI : CoreFI row col univ) (hmin : MinOccDegreeThree row col univ) {x : E → ℝ}
    {μ : LMatch row col → ℝ} (hμ : IsCoreLaw row col x μ) :
    0 < normalizedGap row col (removableSet row col univ) x := by
  have hV : Fintype.card V = 2 := hbal ▸ hU
  obtain ⟨u⟩ : Nonempty U := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨e, he, f, hf, hef, hcol⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (s := rowSet row u) (t := (univ : Finset V))
      (f := col) (by rw [Finset.card_univ, hV]; exact hmin.1 u) (fun a _ => mem_univ _)
  have hrow : row f = row e := (mem_rowSet.1 hf).trans (mem_rowSet.1 he).symm
  have heL : e ∈ removableSet row col univ :=
    (mem_removableSet_order_two hU hV hFI e).2 ⟨f, hef.symm, hrow, hcol.symm⟩
  have hfL : f ∈ removableSet row col univ :=
    (mem_removableSet_order_two hU hV hFI f).2 ⟨e, hef, hrow.symm, hcol⟩
  exact normalizedGap_pos_order_two hU hV hμ heL hfL hef hrow hcol.symm

/-! ### Order at least three without a nontrivial tight cut -/

/-- **Section 7, cut-free core of order at least three, assuming Gurvits's
inequality.**  For a balanced FI core `H` of order `h ≥ 3` with no nontrivial
tight cut, `G_{H,L(H)}(x) ≥ log (8192/6561)` at every feasible flow: by
Lemma 6.1 every occurrence is removable, Corollary 5.2 bounds the gap of the
expansion with one row star shortened, and making the star paths long again
adds only nonnegative `δ`-terms.  `hG` is Gurvits's capacity inequality, an
external theorem that is assumed, not proved (it is used by Corollary 5.2). -/
theorem gap_ge_cutFree (hG : GurvitsCapacityInequality)
    (hbal : Fintype.card U = Fintype.card V) (hFI : CoreFI row col univ)
    (hcut : CutFree row col) (hk : 3 ≤ Fintype.card U) {x : E → ℝ}
    (hlaw : ∃ μ, IsCoreLaw row col x μ) :
    Real.log (8192 / 6561) ≤ normalizedGap row col (removableSet row col univ) x := by
  obtain ⟨hR, hC, hall⟩ := lavi_lemma_6_1 hbal hFI hcut hk
  obtain ⟨v⟩ : Nonempty U := Fintype.card_pos_iff.1 (by omega)
  rw [hall]
  exact (lavi_corollary_5_2 row col v hG hbal hk hR hC hlaw).1.trans
    (normalizedGap_mono (Finset.subset_univ _) x)

/-- **Section 7, cut-free core of order at least three, assuming Gurvits's
inequality:** `G_{H,L(H)}(x) > 0` at every feasible flow.  `hG` is Gurvits's
capacity inequality, an external theorem that is assumed, not proved. -/
theorem gap_pos_cutFree (hG : GurvitsCapacityInequality)
    (hbal : Fintype.card U = Fintype.card V) (hFI : CoreFI row col univ)
    (hcut : CutFree row col) (hk : 3 ≤ Fintype.card U) {x : E → ℝ}
    (hlaw : ∃ μ, IsCoreLaw row col x μ) :
    0 < normalizedGap row col (removableSet row col univ) x :=
  lt_of_lt_of_le (Real.log_pos (by norm_num)) (gap_ge_cutFree hG hbal hFI hcut hk hlaw)

/-! ### Order at least three with a nontrivial tight cut -/

omit [Fintype E] [DecidableEq E] in
/-- A balanced core with a nontrivial tight cut has order at least three: each
shore has at least three vertices. -/
theorem three_le_card_of_nontrivialShore (hbal : Fintype.card U = Fintype.card V)
    {R : Finset U} {C : Finset V} (h : IsNontrivialShore row col R C) :
    3 ≤ Fintype.card U := by
  obtain ⟨-, h1, h2⟩ := h
  rw [card_compl, card_compl] at h2
  have hR := R.card_le_univ
  have hC := C.card_le_univ
  omega

/-- **`G_R ≥ 0` for a canonical remainder, from the induction hypothesis**
(Section 7: "Lemma 3.1 and (3.7) then give `G_R ≥ 0` at every inherited
marginal").  Let `H` be a balanced FI core of order at least two whose
canonical expansion `D_can(H)` has order `h + |L(H)| < N`, and assume the
Foregger bound on the whole face of every nearly decomposable support of order
below `N`.  Then `G_{H,L(H)}(x) ≥ 0` at every feasible flow `x`.  The canonical
expansion is nearly decomposable by the converse part of Lemma 2.5.

The hypothesis `hIH` is a bound on whole faces.  The manuscript's induction
hypothesis bounds full-support matrices and reaches the whole face through
Lemma 2.1; that step is not part of this lemma. -/
theorem canonical_gap_nonneg {N : ℕ}
    (hIH : ∀ m, m < N → ∀ D : Fin m → Fin m → Prop, NearlyDecomposable D →
      ∀ A : Square m, InFace D A → foreggerTarget m ≤ permanent A)
    (hbal : Fintype.card U = Fintype.card V) (hFI : CoreFI row col univ)
    (h2 : 2 ≤ Fintype.card U) (hlt : Fintype.card U + (removableSet row col univ).card < N)
    {x : E → ℝ} {μ : LMatch row col → ℝ} (hμ : IsCoreLaw row col x μ) :
    0 ≤ normalizedGap row col (removableSet row col univ) x := by
  have hcR : Fintype.card (U ⊕ ↥(removableSet row col univ)) =
      Fintype.card U + (removableSet row col univ).card := by
    rw [Fintype.card_sum, Fintype.card_coe]
  have hcC : Fintype.card (V ⊕ ↥(removableSet row col univ)) =
      Fintype.card U + (removableSet row col univ).card := by
    rw [Fintype.card_sum, Fintype.card_coe, hbal]
  exact gap_nonneg_of_face_bound _ (Fintype.equivFinOfCardEq hcR).symm
    (Fintype.equivFinOfCardEq hcC).symm hμ (by omega)
    (hIH _ hlt _ (nearlyDecomposable_expSupport_canonical hbal hFI h2 _ _))

namespace ShoreCut

variable (K : ShoreCut row col)

omit [Fintype E] [DecidableEq U] [DecidableEq V] [DecidableEq E] in
/-- The closed factor `H₁` (marker column) is balanced. -/
theorem card_factor₁ : Fintype.card K.U₁ = Fintype.card (K.V₁ ⊕ Unit) := by
  rw [Fintype.card_sum, Fintype.card_unit]
  exact K.card

/-- The closed factor `H₂` (marker row) of a balanced core is balanced. -/
theorem card_factor₂ (hbal : Fintype.card U = Fintype.card V) :
    Fintype.card (Unit ⊕ K.U₂) = Fintype.card K.V₂ := by
  rw [Fintype.card_sum, Fintype.card_unit, K.card_V₂ hbal, add_comm]

omit [Fintype E] [DecidableEq U] [DecidableEq V] [DecidableEq E] in
/-- A shore `S₁` with at least three vertices closes to a factor `H₁` of order
at least two. -/
theorem two_le_card_factor₁ (hnt₁ : 3 ≤ Fintype.card K.U₁ + Fintype.card K.V₁) :
    2 ≤ Fintype.card K.U₁ := by
  have hc : Fintype.card K.U₁ = Fintype.card K.V₁ + 1 := K.card
  omega

/-- In a balanced core, a shore `S₂` with at least three vertices closes to a
factor `H₂` of order at least two. -/
theorem two_le_card_factor₂ (hbal : Fintype.card U = Fintype.card V)
    (hnt₂ : 3 ≤ Fintype.card K.U₂ + Fintype.card K.V₂) :
    2 ≤ Fintype.card (Unit ⊕ K.U₂) := by
  have hc : Fintype.card K.V₂ = Fintype.card K.U₂ + 1 := K.card_V₂ hbal
  rw [Fintype.card_sum, Fintype.card_unit]
  omega

/-- **The remainder has smaller order, leaf `H₁`** (the consequence
`n_R < n` of (6.5)).  Let the closed factor `H₁` of a nontrivial cut of a
balanced FI core of minimum occurrence degree at least three be a leaf.  Then
the canonical expansion of the remainder `H₂` has smaller order than
`D_can(H)`: `|rows of H₂| + |L(H₂)| < h + |L(H)|`.  For a leaf of order at
least three, `N = ∅` by Lemma 6.1; for a leaf of order two, `ℓ_B ≥ 2` and
`|N| ≤ 1` by Lemma 6.3.

The positive feasible flow `x` is used only to quote `lavi_lemma_6_3`, which
states these two combinatorial facts together with (6.2); the manuscript's
count does not involve a flow. -/
theorem remainder_lt₁ (hbal : Fintype.card U = Fintype.card V) (hFI : CoreFI row col univ)
    (hmin : MinOccDegreeThree row col univ)
    (hnt₁ : 3 ≤ Fintype.card K.U₁ + Fintype.card K.V₁)
    (hnt₂ : 3 ≤ Fintype.card K.U₂ + Fintype.card K.V₂) (hcut : CutFree K.row₁ K.col₁)
    {x : E → ℝ} {μ : LMatch row col → ℝ} (hμ : IsCoreLaw row col x μ) (hpos : ∀ e, 0 < x e) :
    Fintype.card (Unit ⊕ K.U₂) + (removableSet K.row₂ K.col₂ univ).card <
      Fintype.card U + (removableSet row col univ).card := by
  have hc : Fintype.card K.U₁ = Fintype.card K.V₁ + 1 := K.card
  have h65 := K.lavi_eq_6_5 hbal hFI
  rcases Nat.lt_or_ge (Fintype.card K.U₁) 3 with hlt | hge
  · obtain ⟨hℓ, hN, -⟩ :=
      K.lavi_lemma_6_3 hbal hFI hmin.1 hmin.2 hnt₂ (by omega) hμ hpos
    omega
  · have hall := (lavi_lemma_6_1 K.card_factor₁ (K.coreFI_factors hbal hFI).1 hcut hge).2.2
    rw [K.essential₁_eq_empty hall, card_empty] at h65
    omega

/-- **The remainder has smaller order, leaf `H₂`** (the consequence
`n_R < n` of (6.5)).  As `remainder_lt₁`, with the leaf `H₂` (marker row) and
the remainder `H₁`: `|rows of H₁| + |L(H₁)| < h + |L(H)|`.  The positive
feasible flow is used only to quote `lavi_lemma_6_3'`. -/
theorem remainder_lt₂ (hbal : Fintype.card U = Fintype.card V) (hFI : CoreFI row col univ)
    (hmin : MinOccDegreeThree row col univ)
    (hnt₁ : 3 ≤ Fintype.card K.U₁ + Fintype.card K.V₁)
    (hnt₂ : 3 ≤ Fintype.card K.U₂ + Fintype.card K.V₂) (hcut : CutFree K.row₂ K.col₂)
    {x : E → ℝ} {μ : LMatch row col → ℝ} (hμ : IsCoreLaw row col x μ) (hpos : ∀ e, 0 < x e) :
    Fintype.card K.U₁ + (removableSet K.row₁ K.col₁ univ).card <
      Fintype.card U + (removableSet row col univ).card := by
  have hc : Fintype.card K.V₂ = Fintype.card K.U₂ + 1 := K.card_V₂ hbal
  have hord : Fintype.card (Unit ⊕ K.U₂) = Fintype.card K.U₂ + 1 := by
    rw [Fintype.card_sum, Fintype.card_unit, add_comm]
  have h65 := K.lavi_eq_6_5' hbal hFI
  rcases Nat.lt_or_ge (Fintype.card (Unit ⊕ K.U₂)) 3 with hlt | hge
  · obtain ⟨hℓ, hN, -⟩ :=
      K.lavi_lemma_6_3' hbal hFI hmin.1 hmin.2 hnt₁ (by omega) hμ hpos
    omega
  · have hall :=
      (lavi_lemma_6_1 (K.card_factor₂ hbal) (K.coreFI_factors hbal hFI).2 hcut hge).2.2
    rw [K.essential₂_eq_empty hall, card_empty] at h65
    omega

/-- **Section 7, leaf `H₁`, assuming Gurvits's inequality.**  Let the closed
factor `H₁` (marker column) of a nontrivial cut of a balanced FI core `H` of
minimum occurrence degree at least three be a leaf, and let `x` be a positive
feasible flow of `H`.  If the gap `G_R` of the remainder `R = D_can(H₂)` is
nonnegative at the inherited flow, then `G_{H,L(H)}(x) > 0`: for a leaf of
order at least three by (6.1), where `N = ∅` and (4.5) reads `G = G_B + G_R`;
for a leaf of order two by Lemma 6.3 and (4.5).

`hG` is Gurvits's capacity inequality, an external theorem that is assumed,
not proved (it is used by (6.1)).  The hypothesis `hGR` is what the manuscript
obtains from the induction hypothesis; see `canonical_gap_nonneg`. -/
theorem gap_pos_of_leaf₁ (hG : GurvitsCapacityInequality)
    (hbal : Fintype.card U = Fintype.card V) (hFI : CoreFI row col univ)
    (hmin : MinOccDegreeThree row col univ)
    (hnt₁ : 3 ≤ Fintype.card K.U₁ + Fintype.card K.V₁)
    (hnt₂ : 3 ≤ Fintype.card K.U₂ + Fintype.card K.V₂) (hcut : CutFree K.row₁ K.col₁)
    {x : E → ℝ} {μ : LMatch row col → ℝ} (hμ : IsCoreLaw row col x μ) (hpos : ∀ e, 0 < x e)
    (hGR : 0 ≤ normalizedGap K.row₂ K.col₂ (removableSet K.row₂ K.col₂ univ) (K.flow₂ x)) :
    0 < normalizedGap row col (removableSet row col univ) x := by
  have hc : Fintype.card K.U₁ = Fintype.card K.V₁ + 1 := K.card
  rcases Nat.lt_or_ge (Fintype.card K.U₁) 3 with hlt | hge
  · obtain ⟨-, -, h63⟩ :=
      K.lavi_lemma_6_3 hbal hFI hmin.1 hmin.2 hnt₂ (by omega) hμ hpos
    rw [K.lavi_eq_4_5 hbal hFI ⟨μ, hμ⟩]
    linarith
  · obtain ⟨h61, -, h45⟩ := K.lavi_eq_6_1 hG hbal hFI hge hcut ⟨μ, hμ⟩
    have hlog : 0 < Real.log (8192 / 6561 : ℝ) := Real.log_pos (by norm_num)
    rw [h45]
    linarith

/-- **Section 7, leaf `H₂`, assuming Gurvits's inequality.**  As
`gap_pos_of_leaf₁`, with the leaf `H₂` (marker row) and the remainder
`R = D_can(H₁)`: if `G_R ≥ 0` at the inherited flow, then
`G_{H,L(H)}(x) > 0` at a positive feasible flow `x`.  `hG` is Gurvits's
capacity inequality, an external theorem that is assumed, not proved. -/
theorem gap_pos_of_leaf₂ (hG : GurvitsCapacityInequality)
    (hbal : Fintype.card U = Fintype.card V) (hFI : CoreFI row col univ)
    (hmin : MinOccDegreeThree row col univ)
    (hnt₁ : 3 ≤ Fintype.card K.U₁ + Fintype.card K.V₁)
    (hnt₂ : 3 ≤ Fintype.card K.U₂ + Fintype.card K.V₂) (hcut : CutFree K.row₂ K.col₂)
    {x : E → ℝ} {μ : LMatch row col → ℝ} (hμ : IsCoreLaw row col x μ) (hpos : ∀ e, 0 < x e)
    (hGR : 0 ≤ normalizedGap K.row₁ K.col₁ (removableSet K.row₁ K.col₁ univ) (K.flow₁ x)) :
    0 < normalizedGap row col (removableSet row col univ) x := by
  have hc : Fintype.card K.V₂ = Fintype.card K.U₂ + 1 := K.card_V₂ hbal
  have hord : Fintype.card (Unit ⊕ K.U₂) = Fintype.card K.U₂ + 1 := by
    rw [Fintype.card_sum, Fintype.card_unit, add_comm]
  rcases Nat.lt_or_ge (Fintype.card (Unit ⊕ K.U₂)) 3 with hlt | hge
  · obtain ⟨-, -, h63⟩ :=
      K.lavi_lemma_6_3' hbal hFI hmin.1 hmin.2 hnt₁ (by omega) hμ hpos
    rw [K.lavi_eq_4_5' hbal hFI ⟨μ, hμ⟩]
    linarith
  · obtain ⟨h61, -, h45⟩ := K.lavi_eq_6_1' hG hbal hFI hge hcut ⟨μ, hμ⟩
    have hlog : 0 < Real.log (8192 / 6561 : ℝ) := Real.log_pos (by norm_num)
    rw [h45]
    linarith

end ShoreCut

/-- **Section 7, core with a nontrivial tight cut, assuming Gurvits's
inequality.**  Let `H` be a balanced FI core of minimum occurrence degree at
least three with a nontrivial tight cut (so `H` has order at least three),
and let `x` be a positive feasible flow of `H`.  Assume the Foregger bound on
the whole face of every nearly decomposable support of order below
`n = h + |L(H)|`.  Then `G_{H,L(H)}(x) > 0`.

A minimum nontrivial tight shore closes to a leaf (Lemma 6.2); the canonical
expansion of the other factor is a nearly decomposable remainder of smaller
order ((6.5), `ShoreCut.remainder_lt₁`, `remainder_lt₂`), so its gap is
nonnegative at the inherited flow (`canonical_gap_nonneg`), and the leaf makes
(4.5) positive (`ShoreCut.gap_pos_of_leaf₁`, `gap_pos_of_leaf₂`).

`hG` is Gurvits's capacity inequality, an external theorem that is assumed,
not proved.  The induction hypothesis `hIH` is stated on whole faces; the
manuscript reaches the whole face of the remainder through Lemma 2.1, a step
that is not part of this theorem. -/
theorem gap_pos_tightCut (hG : GurvitsCapacityInequality)
    (hbal : Fintype.card U = Fintype.card V) (hFI : CoreFI row col univ)
    (hmin : MinOccDegreeThree row col univ) (hex : ∃ R C, IsNontrivialShore row col R C)
    {x : E → ℝ} {μ : LMatch row col → ℝ} (hμ : IsCoreLaw row col x μ) (hpos : ∀ e, 0 < x e)
    (hIH : ∀ m, m < Fintype.card U + (removableSet row col univ).card →
      ∀ D : Fin m → Fin m → Prop, NearlyDecomposable D →
        ∀ A : Square m, InFace D A → foreggerTarget m ≤ permanent A) :
    0 < normalizedGap row col (removableSet row col univ) x := by
  obtain ⟨u⟩ : Nonempty U := by
    obtain ⟨R, C, hRC⟩ := hex
    have hk := three_le_card_of_nontrivialShore hbal hRC
    exact Fintype.card_pos_iff.1 (by omega)
  obtain ⟨e, -, -⟩ := hFI.2 u
  haveI : Nonempty E := ⟨e⟩
  obtain ⟨K, hnt₁, hnt₂, hcut₁ | hcut₂⟩ :=
    lavi_lemma_6_2 hbal (covered_of_positive_flow hμ hpos) hex
  · -- the leaf is `H₁`, the remainder is `D_can(H₂)`
    exact K.gap_pos_of_leaf₁ hG hbal hFI hmin hnt₁ hnt₂ hcut₁ hμ hpos
      (canonical_gap_nonneg hIH (K.card_factor₂ hbal) (K.coreFI_factors hbal hFI).2
        (K.two_le_card_factor₂ hbal hnt₂)
        (K.remainder_lt₁ hbal hFI hmin hnt₁ hnt₂ hcut₁ hμ hpos) (K.isCoreLaw_push₂ hμ))
  · -- the leaf is `H₂`, the remainder is `D_can(H₁)`
    exact K.gap_pos_of_leaf₂ hG hbal hFI hmin hnt₁ hnt₂ hcut₂ hμ hpos
      (canonical_gap_nonneg hIH K.card_factor₁ (K.coreFI_factors hbal hFI).1
        (K.two_le_card_factor₁ hnt₁)
        (K.remainder_lt₂ hbal hFI hmin hnt₁ hnt₂ hcut₂ hμ hpos) (K.isCoreLaw_push₁ hμ))

/-! ### Assembly -/

/-- **Section 7, terminal branch at the core level, assuming Gurvits's
inequality:** `G_{H,L(H)}(x) > 0` at every positive core flow.

Let `H` be a balanced FI occurrence core of order `h ≥ 1` and minimum
occurrence degree at least three (as Lemma 2.5 provides for a terminal
support), and let `x` be a positive feasible flow of `H`.  Assume the Foregger
bound on the whole face of every nearly decomposable support of order below
`n = h + |L(H)|`, the order of `D_can(H)`.  Then the normalized gap of the
canonical expansion is positive at `x`.

The proof follows the four terminal cases of Section 7: `h = 1` by (7.2)
(`gap_pos_order_one`); `h = 2` by the `K_{2,2}` calculation
(`gap_pos_order_two`); `h ≥ 3` without a nontrivial tight cut by Lemma 6.1 and
Corollary 5.2 (`gap_pos_cutFree`); `h ≥ 3` with a nontrivial tight cut by
Lemmas 6.2-6.3, (4.5), (6.5) and the induction hypothesis for the remainder
(`gap_pos_tightCut`).

`hG` is Gurvits's capacity inequality, an external theorem that is assumed,
not proved; it is used in the two cases `h ≥ 3`.  The induction hypothesis
`hIH` is stated on whole faces; the manuscript's induction hypothesis bounds
full-support matrices of smaller order and reaches the whole face of the
remainder through Lemma 2.1, a step that is not part of this theorem. -/
theorem terminal_gap_pos (hG : GurvitsCapacityInequality)
    (hbal : Fintype.card U = Fintype.card V) (hU : 1 ≤ Fintype.card U)
    (hFI : CoreFI row col univ) (hmin : MinOccDegreeThree row col univ)
    {x : E → ℝ} {μ : LMatch row col → ℝ} (hμ : IsCoreLaw row col x μ) (hpos : ∀ e, 0 < x e)
    (hIH : ∀ m, m < Fintype.card U + (removableSet row col univ).card →
      ∀ D : Fin m → Fin m → Prop, NearlyDecomposable D →
        ∀ A : Square m, InFace D A → foreggerTarget m ≤ permanent A) :
    0 < normalizedGap row col (removableSet row col univ) x := by
  rcases Nat.lt_or_ge (Fintype.card U) 3 with hlt | hk
  · rcases Nat.lt_or_ge (Fintype.card U) 2 with h1 | h2
    · exact gap_pos_order_one hbal (by omega) hmin hμ
    · exact gap_pos_order_two hbal (by omega) hFI hmin hμ
  by_cases hcut : CutFree row col
  · exact gap_pos_cutFree hG hbal hFI hcut hk ⟨μ, hμ⟩
  · refine gap_pos_tightCut hG hbal hFI hmin ?_ hμ hpos hIH
    by_contra h
    exact hcut fun R C hRC => h ⟨R, C, hRC⟩

end Cores

/-- **Section 7, terminal branch at interior points, assuming Gurvits's
inequality** ("the permanent at an interior terminal point is strictly above
`2^(1-n)`").  Let `D` be a terminal nearly decomposable support of order
`m + 1 ≥ 3`, and let `A ∈ Ω(D)` have support exactly `D`.  Assume the Foregger
bound on the whole face of every nearly decomposable support of smaller order.
Then `per A > 2^(-m)`.

By Lemma 2.5, `D = D_can(H)`; the flow lift of `A` is a positive feasible core
flow; `terminal_gap_pos` makes the gap positive there; (3.7) and the first
inequality of (3.3) conclude.  `hG` is Gurvits's capacity inequality, an
external theorem that is assumed, not proved.  The hypothesis `hIH` is stated
on whole faces, see `terminal_gap_pos`. -/
theorem terminal_interior_strict (hG : GurvitsCapacityInequality) {m : ℕ} (hn : 3 ≤ m + 1)
    (D : Fin (m + 1) → Fin (m + 1) → Prop) (hND : NearlyDecomposable D) (hterm : Terminal D)
    {A : Square (m + 1)} (hA : InFace D A) (hfull : ∀ i j, D i j → A i j ≠ 0)
    (hIH : ∀ k, k < m + 1 → ∀ D' : Fin k → Fin k → Prop, NearlyDecomposable D' →
        ∀ B : Square k, InFace D' B → foreggerTarget k ≤ permanent B) :
    foreggerTarget (m + 1) < permanent A := by
  obtain ⟨U, V, E, iU, iV, iE, dU, dV, dE, row, col, hbal, hFI, hmin, eR, eC, hiso⟩ :=
    lavi_lemma_2_5_univ hn D hND hterm
  have hAexp : InFace (expSupport row col (removableSet row col univ) eR eC) A :=
    ⟨hA.1, fun i j h => (hiso i j).1 (hA.2 i j h)⟩
  have hpos := liftFlow_pos _ eR eC hAexp fun i j h => hfull i j ((hiso i j).2 h)
  obtain ⟨μ, hμ⟩ := exists_isCoreLaw_liftFlow _ eR eC hAexp
  have hcard : m + 1 = Fintype.card U + (removableSet row col univ).card :=
    (lavi_eq_3_7 eR eC ⟨μ, hμ⟩).2
  have hU : 1 ≤ Fintype.card U := by
    rcases eR 0 with u | ℓ
    · exact Fintype.card_pos_iff.2 ⟨u⟩
    · exact Fintype.card_pos_iff.2 ⟨row ℓ.1⟩
  exact permanent_gt_of_gap_pos _ eR eC hAexp
    (terminal_gap_pos hG hbal hU hFI hmin hμ hpos fun k hk => hIH k (by omega))

/-- **Section 7, terminal branch, assuming Gurvits's inequality.**  Let `D` be
a terminal nearly decomposable support of order `m + 1 ≥ 3` and `A` a
permanent minimizer on the face `Ω(D)`.  Assume the Foregger bound on the
whole face of every nearly decomposable support of smaller order.  Then
`per A > 2^(-m)`: the terminal branch of the induction is strict.

By Lemma 2.1 the minimizer has support exactly `D`, so this is
`terminal_interior_strict`.  `hG` is Gurvits's capacity inequality, an
external theorem that is assumed, not proved.  The induction hypothesis `hIH`
is stated on whole faces; the manuscript's induction hypothesis is Theorem 1.1
in smaller order (a bound for matrices with nearly decomposable support),
which gives the whole-face bound through Lemma 2.1. -/
theorem terminal_branch_strict (hG : GurvitsCapacityInequality) {m : ℕ} (hn : 3 ≤ m + 1)
    (D : Fin (m + 1) → Fin (m + 1) → Prop) (hND : NearlyDecomposable D) (hterm : Terminal D)
    {A : Square (m + 1)} (hA : FaceMinimizer D A)
    (hIH : ∀ k, k < m + 1 → ∀ D' : Fin k → Fin k → Prop, NearlyDecomposable D' →
        ∀ B : Square k, InFace D' B → foreggerTarget k ≤ permanent B) :
    foreggerTarget (m + 1) < permanent A :=
  terminal_interior_strict hG hn D hND hterm hA.1
    (fun i j h => (faceMinimizer_support_eq_of_nearlyDecomposable hND hA i j).2 h) hIH

/-- **Section 7, terminal branch on the whole face, assuming Gurvits's
inequality.**  Let `D` be a terminal nearly decomposable support of order
`m + 1 ≥ 3`.  Assume the Foregger bound on the whole face of every nearly
decomposable support of smaller order.  Then every matrix `B ∈ Ω(D)` has
`per B > 2^(-m)`: the face is compact, so it has a permanent minimizer
(`exists_faceMinimizer`), to which `terminal_branch_strict` applies.  This is
the manuscript's final step ("its minimum is strictly greater than
`2^(1-n)`") for terminal supports, and it has the form of the induction
hypothesis `hIH` in order `m + 1`.  `hG` is Gurvits's capacity inequality, an
external theorem that is assumed, not proved; `hIH` is stated on whole faces,
as in `terminal_branch_strict`. -/
theorem terminal_face_strict (hG : GurvitsCapacityInequality) {m : ℕ} (hn : 3 ≤ m + 1)
    (D : Fin (m + 1) → Fin (m + 1) → Prop) (hND : NearlyDecomposable D) (hterm : Terminal D)
    (hIH : ∀ k, k < m + 1 → ∀ D' : Fin k → Fin k → Prop, NearlyDecomposable D' →
        ∀ B : Square k, InFace D' B → foreggerTarget k ≤ permanent B)
    {B : Square (m + 1)} (hB : InFace D B) : foreggerTarget (m + 1) < permanent B := by
  obtain ⟨A, hA⟩ := exists_faceMinimizer ⟨B, hB⟩
  exact (terminal_branch_strict hG hn D hND hterm hA hIH).trans_le (hA.2 B hB)

end LaviSection2
