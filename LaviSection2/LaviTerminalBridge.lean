import LaviSection2.LaviOneStar
import LaviSection2.LaviLemma25

/-!
# Lavi Section 7: between matrices on a terminal face and core flows

Section 7 of the manuscript treats a terminal nearly decomposable support `D`
of order `n ≥ 3`.  Lemma 2.5 writes `D = D_can(H)` for a balanced FI
occurrence core `H` of minimum occurrence degree at least three, every doubly
stochastic matrix on `D` is the expanded matrix `X_x` of a feasible core flow
`x`, and by (3.7) and Lemma 3.1 its permanent is controlled by the normalized
gap `G_{H,L(H)}(x)`.  This file contains the translations between the matrix
level (supports and faces on `Fin n`, as in Theorem 1.1) and the core level
(flows, laws on labelled matchings, the gap).  The terminal branch
(`LaviTerminalBranch`) uses them in both directions.

Here and in `LaviTerminalBranch` a flow `x` is called *feasible* when it is
the vector of marginals of a law on labelled perfect matchings
(`IsCoreLaw row col x μ`).  On a balanced core this is the manuscript's
condition (3.1), nonnegativity with unit sums at every row and column
(`exists_isCoreLaw_of_feasible`; conversely `IsCoreLaw.rowSet_sum`,
`IsCoreLaw.colSet_sum`).

From cores to matrices:

* `normalizedGap_mono`: `G_{H,L} ≤ G_{H,L'}` for `L ⊆ L'`, since the
  subdivision charges `δ` are nonnegative;
* `expAdj_univ_iff`, `expSupport_iff_expAdj`: when the occurrence set is the
  whole edge type, the combinatorial expansion `expAdj` of Section 2 is the
  support `expSupport` of the expanded multigraph of Sections 3-6;
* `nearlyDecomposable_expSupport_canonical_of_colOcc`,
  `nearlyDecomposable_expSupport_canonical`: the converse part of Lemma 2.5 in
  matrix coordinates (canonical expansions are nearly decomposable);
* `gap_nonneg_of_face_bound`: a Foregger bound on the whole face of an
  expansion gives `G ≥ 0` at every feasible flow (Lemma 3.1 and (3.7)).

From matrices to cores:

* `exists_isCoreLaw_of_aggregateMatrix`, `exists_isCoreLaw_of_feasible`,
  `exists_isCoreLaw_of_expandedMatrix`: a nonnegative flow whose aggregated
  (or expanded) matrix is doubly stochastic is the vector of marginals of a
  law on labelled perfect matchings;
* `exists_isCoreLaw_liftFlow`, `liftFlow_pos`: the flow lift of a matrix on an
  expanded face is feasible, and it is positive when the support of the
  matrix is the whole expansion;
* `permanent_expandedMatrix_ge_exp_gap`, `permanent_ge_exp_gap`:
  `per ≥ 2^(1-n) exp G` ((3.7) and the first inequality of (3.3)), and its
  consequences `permanent_expandedMatrix_gt_of_gap_pos`,
  `permanent_gt_of_gap_pos`: `G > 0` gives `per > 2^(1-n)`.

Lemma 2.5 on the whole edge type:

* `restrictRow`, `restrictCol` and the lemmas `*_restrict`: a core with
  occurrence set `O : Finset E` is the core on the subtype `↥O` whose
  occurrence set is everything, with the same full indecomposability,
  removable occurrences, occurrence degrees and canonical expansion;
* `lavi_lemma_2_5_univ`: Lemma 2.5 with the occurrence set equal to the whole
  edge type and the support in the form `expSupport`, as Sections 3-6 need.
-/

namespace LaviSection2

open Finset

section Gap

variable {U V E : Type*} [Fintype U] [Fintype V] [Fintype E]
  [DecidableEq U] [DecidableEq V] [DecidableEq E] {row : E → U} {col : E → V}

/-- Making more occurrences long only adds nonnegative subdivision charges:
`G_{H,L}(x) ≤ G_{H,L'}(x)` whenever `L ⊆ L'`.  This is the remark "making the
star paths long again adds only nonnegative `δ`-terms" in the cut-free case of
Section 7; it is immediate from the definition (3.6). -/
theorem normalizedGap_mono {L L' : Finset E} (h : L ⊆ L') (x : E → ℝ) :
    normalizedGap row col L x ≤ normalizedGap row col L' x := by
  unfold normalizedGap
  have := Finset.sum_le_sum_of_subset_of_nonneg h
    (f := fun ℓ => subdivCharge (x ℓ)) (fun ℓ _ _ => subdivCharge_nonneg (x ℓ))
  linarith

/-- With the whole edge type as occurrence set, the expansion `D(H, L)` of
Section 2 (`expAdj`, used by Lemma 2.5) has an edge between two lines exactly
when the expanded multigraph of Section 3 (`ExpEdge`) has one. -/
theorem expAdj_univ_iff (L : Finset E) (r : U ⊕ ↥L) (c : V ⊕ ↥L) :
    expAdj row col univ L r c ↔ ∃ f : ExpEdge L, expRow row L f = r ∧ expCol col L f = c := by
  rw [exists_expEdge_iff]
  rcases r with u | e <;> rcases c with v | e'
  · constructor
    · rintro ⟨e, -, heL, hu, hv⟩
      exact ⟨⟨e, heL⟩, hu, hv⟩
    · rintro ⟨d, hu, hv⟩
      exact ⟨d.1, mem_univ _, d.2, hu, hv⟩
  · exact Iff.rfl
  · exact Iff.rfl
  · exact Iff.rfl

/-- The support `expSupport` of the expansion in matrix coordinates (Sections
3-6) is the expansion `expAdj` of Section 2 with the whole edge type as
occurrence set, read through the same coordinates. -/
theorem expSupport_iff_expAdj {n : ℕ} (L : Finset E) (eR : Fin n ≃ U ⊕ ↥L)
    (eC : Fin n ≃ V ⊕ ↥L) (i j : Fin n) :
    expSupport row col L eR eC i j ↔ expAdj row col univ L (eR i) (eC j) :=
  (expAdj_univ_iff L (eR i) (eC j)).symm

/-- If the expansion `D(H, L)` is nearly decomposable on its vertex types
`U ⊕ L`, `V ⊕ L`, then its support is nearly decomposable in any matrix
coordinates. -/
theorem nearlyDecomposable_expSupport_of_expAdj {n : ℕ} (L : Finset E)
    (eR : Fin n ≃ U ⊕ ↥L) (eC : Fin n ≃ V ⊕ ↥L)
    (h : NearlyDecomposableOn (expAdj row col univ L)) :
    NearlyDecomposable (expSupport row col L eR eC) :=
  (nearlyDecomposableOn_fin_iff _).1
    ((nearlyDecomposableOn_relabel_iff eR eC (expSupport_iff_expAdj L eR eC)).2 h)

/-- **Lemma 2.5, converse part, in matrix coordinates.**  Let `H` be a
balanced FI core (occurrence set: the whole edge type) in which every column
carries at least two occurrences, and let its canonical expansion `D_can(H)`
have order `n ≥ 2`.  Then `D_can(H)` is nearly decomposable in any matrix
coordinates.

The manuscript states this for every FI core.  Among balanced FI cores the two
extra hypotheses exclude only the empty core and the core of order one with a
single occurrence, whose canonical expansion is the singleton support of
order one: that support is nearly decomposable by the manuscript's order-one
convention, which is not built into `NearlyDecomposable`.  No lower bound on
the occurrence degrees is assumed beyond two at the columns. -/
theorem nearlyDecomposable_expSupport_canonical_of_colOcc
    (hbal : Fintype.card U = Fintype.card V) (hFI : CoreFI row col univ)
    (hcol2 : ∀ v, 2 ≤ (colOcc col univ v).card) {n : ℕ} (hn : 2 ≤ n)
    (eR : Fin n ≃ U ⊕ ↥(removableSet row col univ))
    (eC : Fin n ≃ V ⊕ ↥(removableSet row col univ)) :
    NearlyDecomposable (expSupport row col (removableSet row col univ) eR eC) :=
  nearlyDecomposable_expSupport_of_expAdj _ eR eC
    (nearlyDecomposableOn_canonicalAdj univ hbal hFI hcol2
      (by rw [← Fintype.card_congr eR, Fintype.card_fin]; exact hn))

/-- **Lemma 2.5, converse part, in matrix coordinates, for order at least
two.**  The canonical expansion `D_can(H)` of a balanced FI core `H` of order
at least two (occurrence set: the whole edge type) is nearly decomposable in
any matrix coordinates.  No degree hypothesis is made: the marker of a
remainder in Section 7 may have occurrence degree two. -/
theorem nearlyDecomposable_expSupport_canonical (hbal : Fintype.card U = Fintype.card V)
    (hFI : CoreFI row col univ) (h2 : 2 ≤ Fintype.card U) {n : ℕ}
    (eR : Fin n ≃ U ⊕ ↥(removableSet row col univ))
    (eC : Fin n ≃ V ⊕ ↥(removableSet row col univ)) :
    NearlyDecomposable (expSupport row col (removableSet row col univ) eR eC) := by
  refine nearlyDecomposable_expSupport_canonical_of_colOcc hbal hFI
    (colOcc_two_of_coreFI hbal hFI h2) ?_ eR eC
  have hn := Fintype.card_congr eR
  rw [Fintype.card_fin, Fintype.card_sum] at hn
  omega

private theorem foreggerTarget_succ_pos (m : ℕ) : 0 < foreggerTarget (m + 1) := by
  unfold foreggerTarget
  positivity

private theorem log_foreggerTarget_succ (m : ℕ) :
    Real.log (foreggerTarget (m + 1)) = -((m : ℝ) * Real.log 2) := by
  unfold foreggerTarget
  rw [Nat.add_sub_cancel, Real.log_inv, Real.log_pow]

/-- **A whole-face bound gives `G ≥ 0`** (Lemma 3.1 and (3.7)).  If every
doubly stochastic matrix on the expansion `D(H, L)`, of order `n ≥ 1`, has
permanent at least `2^(1-n)`, then `G_{H,L}(x) ≥ 0` at every feasible flow `x`
of `H`, boundary flows included.  In Section 7 this is the step "Lemma 3.1 and
(3.7) then give `G_R ≥ 0` at every inherited marginal", applied to a remainder
`R`.  The hypothesis is the bound on the whole face `Ω(D(H, L))`; the
manuscript obtains it from the bound at full-support minimizers through
Lemma 2.1, a step that is not part of this lemma. -/
theorem gap_nonneg_of_face_bound {n : ℕ} (L : Finset E) (eR : Fin n ≃ U ⊕ ↥L)
    (eC : Fin n ≃ V ⊕ ↥L) {x : E → ℝ} {μ : LMatch row col → ℝ} (hμ : IsCoreLaw row col x μ)
    (hn : 1 ≤ n)
    (hbound : ∀ A : Square n, InFace (expSupport row col L eR eC) A →
      foreggerTarget n ≤ permanent A) :
    0 ≤ normalizedGap row col L x := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨h37, -⟩ := lavi_eq_3_7 eR eC ⟨μ, hμ⟩
  obtain ⟨Z, hZ, -, hlog⟩ :=
    exists_inFace_log_permanent_le_faceFunctional (inFace_expandedMatrix row col eR eC hμ)
  have hZb : Real.log (foreggerTarget (m + 1)) ≤ Real.log (permanent Z) :=
    Real.log_le_log (foreggerTarget_succ_pos m) (hbound Z hZ)
  rw [log_foreggerTarget_succ] at hZb
  rw [h37]
  push_cast
  linarith

end Gap

section Laws

variable {U V E : Type*} [Fintype U] [Fintype V] [Fintype E]
  [DecidableEq U] [DecidableEq V] [DecidableEq E] {row : E → U} {col : E → V}

/-- **Feasible flows have laws** (Section 3, the paragraph after (3.1)).  A
nonnegative occurrence flow whose aggregated matrix is doubly stochastic is
the vector of marginals of a law on labelled perfect matchings.  As in the
manuscript, a law on the permutations of the aggregated matrix
(`exists_isLaw`, which replaces the Birkhoff-von Neumann decomposition) is
lifted by choosing the label of each selected matrix edge with probability
proportional to its flow (`isCoreLaw_liftLaw`).  The order `n = 0` is allowed:
then the core is empty and its only matching is the empty one. -/
theorem exists_isCoreLaw_of_aggregateMatrix {n : ℕ} (eR : Fin n ≃ U) (eC : Fin n ≃ V)
    {x : E → ℝ} (hx0 : ∀ e, 0 ≤ x e)
    (hDS : DoublyStochastic (aggregateMatrix row col eR eC x)) :
    ∃ μ, IsCoreLaw row col x μ := by
  rcases n with _ | m
  · haveI : IsEmpty U := eR.symm.isEmpty
    haveI : IsEmpty V := eC.symm.isEmpty
    haveI : IsEmpty E := ⟨fun e => isEmptyElim (row e)⟩
    let M₀ : LMatch row col := ⟨fun u => isEmptyElim u, fun u => isEmptyElim u,
      fun u => isEmptyElim u, fun v => isEmptyElim v⟩
    refine ⟨fun _ => 1, fun _ => zero_le_one, ?_, funext fun e => isEmptyElim e⟩
    rw [Fintype.sum_eq_single M₀
      fun M hM => absurd (Subtype.ext (funext fun u => isEmptyElim u)) hM]
  · obtain ⟨ν, hν⟩ := exists_isLaw hDS
    have hcomp : (ν ∘ completeMatchEquiv eR eC) ∘ (completeMatchEquiv eR eC).symm = ν :=
      funext fun σ => by simp only [Function.comp_apply, Equiv.apply_symm_apply]
    have hκ : IsCoreLaw (Prod.fst : U × V → U) Prod.snd
        (mergeFlow (fun e => (row e, col e)) x) (ν ∘ completeMatchEquiv eR eC) := by
      rw [isCoreLaw_complete_iff eR eC, hcomp]
      exact hν
    exact ⟨_, isCoreLaw_liftLaw (row' := Prod.fst) (col' := Prod.snd)
      (fun e => (row e, col e)) (fun _ => rfl) (fun _ => rfl) hx0 hκ⟩

/-- **Feasible flows have laws, in the form (3.1).**  On a balanced core, a
nonnegative occurrence flow with unit sum at every row and at every column is
the vector of marginals of a law on labelled perfect matchings.  The converse
is `IsCoreLaw.nonneg_edge`, `IsCoreLaw.rowSet_sum`, `IsCoreLaw.colSet_sum`. -/
theorem exists_isCoreLaw_of_feasible (hbal : Fintype.card U = Fintype.card V) {x : E → ℝ}
    (hx0 : ∀ e, 0 ≤ x e) (hrow : ∀ u, ∑ e ∈ rowSet row u, x e = 1)
    (hcol : ∀ w, ∑ e ∈ (univ : Finset E).filter (fun e => col e = w), x e = 1) :
    ∃ μ, IsCoreLaw row col x μ := by
  refine exists_isCoreLaw_of_aggregateMatrix (Fintype.equivFin U).symm
    (Fintype.equivFinOfCardEq hbal.symm).symm hx0
    ⟨fun i j => Finset.sum_nonneg fun e _ => hx0 e, fun i => ?_, fun j => ?_⟩
  · rw [aggregateMatrix_row_sum]
    exact hrow _
  · rw [aggregateMatrix_col_sum]
    exact hcol _

omit [Fintype E] [DecidableEq E] in
/-- Expanded flows `(x_d ; x_ℓ, 1 - x_ℓ, x_ℓ)` are nonnegative when `x ≥ 0`
everywhere and `x ≤ 1` on the long occurrences. -/
theorem expFlow_nonneg {L : Finset E} {x : E → ℝ} (hx0 : ∀ e, 0 ≤ x e)
    (hx1 : ∀ e ∈ L, x e ≤ 1) (f : ExpEdge L) : 0 ≤ expFlow L x f := by
  rcases f with d | ℓ | ℓ | ℓ
  · exact hx0 d.1
  · exact hx0 ℓ.1
  · exact sub_nonneg.2 (hx1 ℓ.1 ℓ.2)
  · exact hx0 ℓ.1

/-- **Feasibility from the expanded matrix.**  A flow `x ≥ 0` with `x ≤ 1` on
the long occurrences whose expanded matrix `X_x` on `D(H, L)` is doubly
stochastic is the vector of marginals of a law on labelled perfect matchings
of `H`.  (Section 3: labelled matchings of `H` and of `D(H, L)` correspond.) -/
theorem exists_isCoreLaw_of_expandedMatrix {n : ℕ} {L : Finset E} (eR : Fin n ≃ U ⊕ ↥L)
    (eC : Fin n ≃ V ⊕ ↥L) {x : E → ℝ} (hx0 : ∀ e, 0 ≤ x e) (hx1 : ∀ e ∈ L, x e ≤ 1)
    (hDS : DoublyStochastic (expandedMatrix row col L eR eC x)) :
    ∃ μ, IsCoreLaw row col x μ := by
  obtain ⟨κ, hκ⟩ := exists_isCoreLaw_of_aggregateMatrix (row := expRow row L)
    (col := expCol col L) eR eC (expFlow_nonneg hx0 hx1) hDS
  have hcomp : (κ ∘ expMatchEquiv) ∘ (expMatchEquiv (row := row) (col := col) (L := L)).symm =
      κ := funext fun N => by simp only [Function.comp_apply, Equiv.apply_symm_apply]
  refine ⟨κ ∘ expMatchEquiv, (isCoreLaw_exp_iff (L := L) x _).2 ?_⟩
  rw [hcomp]
  exact hκ

/-- **The flow lift is feasible** (Section 3: "every doubly stochastic matrix
supported on `D(H, L)` admits a feasible flow lift").  For every matrix `A` in
the face of the expansion `D(H, L)`, Lavi's flow lift `liftFlow` of `A` is the
vector of marginals of a law on labelled perfect matchings of `H`. -/
theorem exists_isCoreLaw_liftFlow {n : ℕ} (L : Finset E) (eR : Fin n ≃ U ⊕ ↥L)
    (eC : Fin n ≃ V ⊕ ↥L) {A : Square n} (hA : InFace (expSupport row col L eR eC) A) :
    ∃ μ, IsCoreLaw row col (liftFlow row col L eR eC A) μ := by
  refine exists_isCoreLaw_of_expandedMatrix eR eC (liftFlow_nonneg hA)
    (fun e he => liftFlow_le_one hA he) ?_
  rw [← eq_expandedMatrix_liftFlow hA]
  exact hA.1

omit [Fintype U] [Fintype V] in
/-- **Interior points have positive lifts** (Section 3: "the matrix is
interior exactly when it admits a positive lift"; only this direction is
proved).  If the support of `A ∈ Ω(D(H, L))` is all of `D(H, L)`, the flow
lift of `A` is positive on every occurrence. -/
theorem liftFlow_pos {n : ℕ} (L : Finset E) (eR : Fin n ≃ U ⊕ ↥L) (eC : Fin n ≃ V ⊕ ↥L)
    {A : Square n} (hA : InFace (expSupport row col L eR eC) A)
    (hfull : ∀ i j, expSupport row col L eR eC i j → A i j ≠ 0) (e : E) :
    0 < liftFlow row col L eR eC A e := by
  have hentry : ∀ f : ExpEdge L,
      0 < A (eR.symm (expRow row L f)) (eC.symm (expCol col L f)) := fun f =>
    lt_of_le_of_ne (hA.1.1 _ _) (Ne.symm (hfull _ _
      ⟨f, (eR.apply_symm_apply _).symm, (eC.apply_symm_apply _).symm⟩))
  unfold liftFlow
  split_ifs with h
  · exact hentry (cE ⟨e, h⟩)
  · refine div_pos (hentry (dE ⟨e, h⟩)) ?_
    have : 0 < directMult row col L e :=
      Finset.card_pos.2 ⟨⟨e, h⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl, rfl⟩⟩
    exact_mod_cast this

/-- **`per X_x ≥ 2^(1-n) exp (G_{H,L}(x))`** ((3.7) and the first inequality
of (3.3)).  For a feasible flow `x` of `H`, the expanded matrix `X_x` on
`D(H, L)`, of order `m + 1`, has permanent at least `2^(-m) exp (G_{H,L}(x))`. -/
theorem permanent_expandedMatrix_ge_exp_gap {m : ℕ} {L : Finset E}
    (eR : Fin (m + 1) ≃ U ⊕ ↥L) (eC : Fin (m + 1) ≃ V ⊕ ↥L) {x : E → ℝ}
    {μ : LMatch row col → ℝ} (hμ : IsCoreLaw row col x μ) :
    foreggerTarget (m + 1) * Real.exp (normalizedGap row col L x) ≤
      permanent (expandedMatrix row col L eR eC x) := by
  obtain ⟨h37, -⟩ := lavi_eq_3_7 eR eC ⟨μ, hμ⟩
  have hX := (inFace_expandedMatrix row col eR eC hμ).1
  have hF := faceFunctional_le_log_permanent hX
  calc foreggerTarget (m + 1) * Real.exp (normalizedGap row col L x)
      = Real.exp (Real.log (foreggerTarget (m + 1)) + normalizedGap row col L x) := by
        rw [Real.exp_add, Real.exp_log (foreggerTarget_succ_pos m)]
    _ ≤ Real.exp (Real.log (permanent (expandedMatrix row col L eR eC x))) := by
        rw [Real.exp_le_exp, log_foreggerTarget_succ, h37]
        push_cast
        linarith
    _ = permanent (expandedMatrix row col L eR eC x) :=
        Real.exp_log (permanent_pos_of_doublyStochastic hX)

/-- **`per A ≥ 2^(1-n) exp (G_{H,L}(x))`, matrix form** ((3.7) and the first
inequality of (3.3)).  Every matrix `A` in the face of the expansion
`D(H, L)`, of order `m + 1`, has permanent at least `2^(-m) exp (G_{H,L}(x))`,
where `x` is the flow lift of `A`. -/
theorem permanent_ge_exp_gap {m : ℕ} (L : Finset E) (eR : Fin (m + 1) ≃ U ⊕ ↥L)
    (eC : Fin (m + 1) ≃ V ⊕ ↥L) {A : Square (m + 1)}
    (hA : InFace (expSupport row col L eR eC) A) :
    foreggerTarget (m + 1) * Real.exp (normalizedGap row col L (liftFlow row col L eR eC A)) ≤
      permanent A := by
  obtain ⟨μ, hμ⟩ := exists_isCoreLaw_liftFlow L eR eC hA
  have h := permanent_expandedMatrix_ge_exp_gap eR eC hμ
  rwa [← eq_expandedMatrix_liftFlow hA] at h

private theorem foreggerTarget_succ_lt_mul_exp (m : ℕ) {g : ℝ} (hg : 0 < g) :
    foreggerTarget (m + 1) < foreggerTarget (m + 1) * Real.exp g := by
  have h := mul_lt_mul_of_pos_left (Real.one_lt_exp_iff.2 hg) (foreggerTarget_succ_pos m)
  rwa [mul_one] at h

/-- **`G > 0` gives the strict bound, flow form** ((3.7) and the first
inequality of (3.3)).  If `G_{H,L}(x) > 0` at a feasible flow `x`, the expanded
matrix `X_x`, of order `m + 1`, has `per X_x > 2^(-m)`. -/
theorem permanent_expandedMatrix_gt_of_gap_pos {m : ℕ} {L : Finset E}
    (eR : Fin (m + 1) ≃ U ⊕ ↥L) (eC : Fin (m + 1) ≃ V ⊕ ↥L) {x : E → ℝ}
    {μ : LMatch row col → ℝ} (hμ : IsCoreLaw row col x μ)
    (hgap : 0 < normalizedGap row col L x) :
    foreggerTarget (m + 1) < permanent (expandedMatrix row col L eR eC x) :=
  (foreggerTarget_succ_lt_mul_exp m hgap).trans_le (permanent_expandedMatrix_ge_exp_gap eR eC hμ)

/-- **`G > 0` gives the strict bound, matrix form** ((3.7) and the first
inequality of (3.3); Section 3: "positivity of this gap at every positive flow
excludes an interior face minimum at or below `2^(1-n)`").  If `A` lies in the
face of the expansion `D(H, L)`, of order `m + 1`, and `G_{H,L}` is positive at
the flow lift of `A`, then `per A > 2^(-m)`. -/
theorem permanent_gt_of_gap_pos {m : ℕ} (L : Finset E) (eR : Fin (m + 1) ≃ U ⊕ ↥L)
    (eC : Fin (m + 1) ≃ V ⊕ ↥L) {A : Square (m + 1)}
    (hA : InFace (expSupport row col L eR eC) A)
    (hgap : 0 < normalizedGap row col L (liftFlow row col L eR eC A)) :
    foreggerTarget (m + 1) < permanent A :=
  (foreggerTarget_succ_lt_mul_exp m hgap).trans_le (permanent_ge_exp_gap L eR eC hA)

end Laws

section Restrict

variable {U V E : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] [DecidableEq E]
  (row : E → U) (col : E → V) (O : Finset E)

/-- The row endpoint of the core `(row, col, O)` on the occurrence subtype
`↥O`. -/
def restrictRow : ↥O → U := fun e => row e.1

/-- The column endpoint of the core `(row, col, O)` on the occurrence subtype
`↥O`. -/
def restrictCol : ↥O → V := fun e => col e.1

omit [DecidableEq E] in
private theorem map_subtype_univ :
    (univ : Finset ↥O).map (Function.Embedding.subtype _) = O := by
  ext e
  rw [Finset.mem_map]
  exact ⟨fun ⟨e', _, he'⟩ => he' ▸ e'.2, fun he => ⟨⟨e, he⟩, mem_univ _, rfl⟩⟩

private theorem map_subtype_erase (e : ↥O) :
    ((univ : Finset ↥O).erase e).map (Function.Embedding.subtype _) = O.erase e.1 := by
  ext f
  rw [Finset.mem_map, Finset.mem_erase]
  constructor
  · rintro ⟨f', hf', rfl⟩
    exact ⟨fun h => (Finset.mem_erase.1 hf').1 (Subtype.ext h), f'.2⟩
  · rintro ⟨hne, hf⟩
    exact ⟨⟨f, hf⟩, Finset.mem_erase.2 ⟨fun h => hne (congrArg Subtype.val h), mem_univ _⟩, rfl⟩

omit [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] [DecidableEq E] in
/-- Distinct-neighbor adjacency of a set `S` of restricted occurrences is that
of the same occurrences in the original core. -/
theorem coreAdj_restrict (S : Finset ↥O) (u : U) (v : V) :
    coreAdj (restrictRow row O) (restrictCol col O) S u v ↔
      coreAdj row col (S.map (Function.Embedding.subtype _)) u v := by
  constructor
  · rintro ⟨e, he, hu, hv⟩
    exact ⟨e.1, Finset.mem_map.2 ⟨e, he, rfl⟩, hu, hv⟩
  · rintro ⟨e, he, hu, hv⟩
    obtain ⟨e', he', rfl⟩ := Finset.mem_map.1 he
    exact ⟨e', he', hu, hv⟩

omit [DecidableEq E] in
/-- Full indecomposability of a set `S` of restricted occurrences is that of
the same occurrences in the original core. -/
theorem coreFI_restrict (S : Finset ↥O) :
    CoreFI (restrictRow row O) (restrictCol col O) S ↔
      CoreFI row col (S.map (Function.Embedding.subtype _)) := by
  unfold CoreFI
  refine and_congr (strictHallOn_congr (coreAdj_restrict row col O S))
    (forall_congr' fun u => ?_)
  constructor
  · rintro ⟨e, he, hu⟩
    exact ⟨e.1, Finset.mem_map.2 ⟨e, he, rfl⟩, hu⟩
  · rintro ⟨e, he, hu⟩
    obtain ⟨e', he', rfl⟩ := Finset.mem_map.1 he
    exact ⟨e', he', hu⟩

omit [DecidableEq E] in
/-- The restricted core, with all of `↥O` as occurrence set, is FI exactly
when the core `(row, col, O)` is. -/
theorem coreFI_restrict_univ :
    CoreFI (restrictRow row O) (restrictCol col O) univ ↔ CoreFI row col O := by
  rw [coreFI_restrict, map_subtype_univ]

/-- An occurrence is removable in the restricted core exactly when it is
removable in the core `(row, col, O)`. -/
theorem mem_removableSet_restrict (e : ↥O) :
    e ∈ removableSet (restrictRow row O) (restrictCol col O) univ ↔
      e.1 ∈ removableSet row col O := by
  rw [mem_removableSet, mem_removableSet, coreFI_restrict, map_subtype_erase]
  exact ⟨fun h => ⟨e.2, h.2⟩, fun h => ⟨mem_univ _, h.2⟩⟩

omit [Fintype U] [DecidableEq E] in
/-- Row occurrence degrees are unchanged by the restriction. -/
theorem card_rowOcc_restrict (u : U) :
    (rowOcc (restrictRow row O) univ u).card = (rowOcc row O u).card := by
  have h : (rowOcc (restrictRow row O) univ u).map (Function.Embedding.subtype _) =
      rowOcc row O u := by
    ext e
    simp only [rowOcc, Finset.mem_map, Finset.mem_filter]
    constructor
    · rintro ⟨e', ⟨-, hu⟩, rfl⟩
      exact ⟨e'.2, hu⟩
    · rintro ⟨he, hu⟩
      exact ⟨⟨e, he⟩, ⟨mem_univ _, hu⟩, rfl⟩
  rw [← h, Finset.card_map]

omit [Fintype V] [DecidableEq E] in
/-- Column occurrence degrees are unchanged by the restriction. -/
theorem card_colOcc_restrict (v : V) :
    (colOcc (restrictCol col O) univ v).card = (colOcc col O v).card := by
  have h : (colOcc (restrictCol col O) univ v).map (Function.Embedding.subtype _) =
      colOcc col O v := by
    ext e
    simp only [colOcc, Finset.mem_map, Finset.mem_filter]
    constructor
    · rintro ⟨e', ⟨-, hv⟩, rfl⟩
      exact ⟨e'.2, hv⟩
    · rintro ⟨he, hv⟩
      exact ⟨⟨e, he⟩, ⟨mem_univ _, hv⟩, rfl⟩
  rw [← h, Finset.card_map]

omit [Fintype U] [Fintype V] [DecidableEq E] in
/-- The restricted core has minimum occurrence degree at least three exactly
when the core `(row, col, O)` has. -/
theorem minOccDegreeThree_restrict :
    MinOccDegreeThree (restrictRow row O) (restrictCol col O) univ ↔
      MinOccDegreeThree row col O := by
  unfold MinOccDegreeThree
  simp only [card_rowOcc_restrict, card_colOcc_restrict]

/-- The removable occurrences of `(row, col, O)`, as removable occurrences of
the restricted core. -/
def removableRestrictEquiv :
    ↥(removableSet row col O) ≃
      ↥(removableSet (restrictRow row O) (restrictCol col O) univ) where
  toFun e := ⟨⟨e.1, ((mem_removableSet row col).1 e.2).1⟩,
    (mem_removableSet_restrict row col O _).2 e.2⟩
  invFun e := ⟨e.1.1, (mem_removableSet_restrict row col O e.1).1 e.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The canonical expansion `D_can` of the core `(row, col, O)` is the
canonical expansion of the restricted core, after relabelling the private
lines by `removableRestrictEquiv`. -/
theorem canonicalAdj_restrict (r : U ⊕ ↥(removableSet row col O))
    (c : V ⊕ ↥(removableSet row col O)) :
    canonicalAdj row col O r c ↔
      canonicalAdj (restrictRow row O) (restrictCol col O) univ
        (Sum.map id (removableRestrictEquiv row col O) r)
        (Sum.map id (removableRestrictEquiv row col O) c) := by
  rcases r with u | e <;> rcases c with v | e'
  · constructor
    · rintro ⟨d, hd, hdL, hu, hv⟩
      exact ⟨⟨d, hd⟩, mem_univ _,
        fun h => hdL ((mem_removableSet_restrict row col O _).1 h), hu, hv⟩
    · rintro ⟨d, -, hdL, hu, hv⟩
      exact ⟨d.1, d.2, fun h => hdL ((mem_removableSet_restrict row col O d).2 h), hu, hv⟩
  · exact Iff.rfl
  · exact Iff.rfl
  · exact (removableRestrictEquiv row col O).injective.eq_iff.symm

end Restrict

/-- **Lavi Lemma 2.5 (terminal classification), on the whole edge type.**  A
terminal nearly decomposable support `D` of order `n ≥ 3` is, in suitable
coordinates `eR`, `eC`, the canonical expansion `D_can(H) = D(H, L(H))` of a
balanced FI occurrence core `H` of minimum occurrence degree at least three.

This is `lavi_lemma_2_5` (the first assertion of Lemma 2.5) for the restricted
core: the occurrence set of `H` is its whole edge type `E`, as Sections 3-6
assume, and the support is given in their form `expSupport`.  As there, the
manuscript's hypothesis that `D` is not a cycle support is not needed, since
a cycle support of order at least three is not terminal. -/
theorem lavi_lemma_2_5_univ {n : ℕ} (hn : 3 ≤ n) (D : Fin n → Fin n → Prop)
    (hND : NearlyDecomposable D) (hterm : Terminal D) :
    ∃ (U V E : Type) (_ : Fintype U) (_ : Fintype V) (_ : Fintype E)
      (_ : DecidableEq U) (_ : DecidableEq V) (_ : DecidableEq E)
      (row : E → U) (col : E → V),
      Fintype.card U = Fintype.card V ∧ CoreFI row col univ ∧ MinOccDegreeThree row col univ ∧
      ∃ (eR : Fin n ≃ U ⊕ removableSet row col univ) (eC : Fin n ≃ V ⊕ removableSet row col univ),
        ∀ i j, D i j ↔ expSupport row col (removableSet row col univ) eR eC i j := by
  obtain ⟨U, V, E, iU, iV, iE, dU, dV, dE, row, col, O, hbal, hFI, hmin, eR, eC, hiso⟩ :=
    lavi_lemma_2_5 hn D hND hterm
  refine ⟨U, V, ↥O, iU, iV, inferInstance, dU, dV, inferInstance, restrictRow row O,
    restrictCol col O, hbal, (coreFI_restrict_univ row col O).2 hFI,
    (minOccDegreeThree_restrict row col O).2 hmin,
    eR.trans (Equiv.sumCongr (Equiv.refl U) (removableRestrictEquiv row col O)),
    eC.trans (Equiv.sumCongr (Equiv.refl V) (removableRestrictEquiv row col O)), fun i j => ?_⟩
  rw [hiso, canonicalAdj_restrict, expSupport_iff_expAdj]
  rfl

end LaviSection2
