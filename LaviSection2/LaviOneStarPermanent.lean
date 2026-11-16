import LaviSection2.LaviExpansionEntropy

/-!
# Lavi Section 5: the permanent of a shortened star, (5.2)

* `permanent_aggregateMatrix`: the permanent of an aggregated core matrix is
  the sum, over labelled perfect matchings, of the products of the occurrence
  weights.
* `permanent_expandedMatrix`: for the expansion `D(H, L)`, a selected long
  occurrence contributes `x_e · x_e` and an unselected one `1 - x_e`.
* `permanent_expandedMatrix_eq_elim`: with root row `v` and `L` the
  occurrences off `v`, the permanent equals that of Lavi's eliminated `k × k`
  matrix (5.2), whose entries are `∑ x_e` in the root row and
  `∑ x_e² ∏_{f ∈ S_i \ e} (1 - x_f)` elsewhere.
* `eq_expandedMatrix_liftFlow`: every doubly stochastic matrix supported on the
  expansion is `X_x` for a flow `x` (Lavi's flow lift), and `x` has unit row
  and column sums on the core.
-/

set_option linter.unusedSectionVars false

namespace LaviSection2

open Finset Equiv Real

open scoped BigOperators

section AggregatePermanent

variable {n : ℕ} {U V E : Type*} [Fintype U] [Fintype V] [Fintype E]
  [DecidableEq U] [DecidableEq V] [DecidableEq E] (row : E → U) (col : E → V)

/-- The permanent of an aggregated matrix sums matching weights. -/
theorem permanent_aggregateMatrix (eR : Fin n ≃ U) (eC : Fin n ≃ V) (z : E → ℝ) :
    permanent (aggregateMatrix row col eR eC z) = ∑ M : LMatch row col, ∏ u, z (M.1 u) := by
  classical
  set φ : E → U × V := fun e => (row e, col e)
  have hrow : ∀ e, (φ e).1 = row e := fun _ => rfl
  have hcol : ∀ e, (φ e).2 = col e := fun _ => rfl
  set Ψ := completeMatchEquiv (U := U) (V := V) eR eC
  unfold permanent
  rw [← Equiv.sum_comp Ψ,
    ← Finset.sum_fiberwise univ (pushMatch (row' := Prod.fst) (col' := Prod.snd) φ hrow hcol)
      (fun M => ∏ u, z (M.1 u))]
  refine Finset.sum_congr rfl fun M' _ => ?_
  rw [sum_fiber_prod φ hrow hcol M' (fun _ e => z e), ← Equiv.prod_comp eR]
  refine Finset.prod_congr rfl fun i _ => ?_
  show mergeFlow φ z (eR i, eC (Ψ M' i)) = _
  rw [completeMatchEquiv_apply, Equiv.apply_symm_apply]
  have : (eR i, (M'.1 (eR i)).2) = M'.1 (eR i) := Prod.ext (M'.2.1 (eR i)).symm rfl
  rw [this]
  rfl

theorem aggregateMatrix_row_sum (eR : Fin n ≃ U) (eC : Fin n ≃ V) (z : E → ℝ) (i : Fin n) :
    ∑ j, aggregateMatrix row col eR eC z i j =
      ∑ e ∈ (univ : Finset E).filter (fun e => row e = eR i), z e := by
  classical
  unfold aggregateMatrix mergeFlow
  rw [Equiv.sum_comp eC (fun w => ∑ e ∈ (univ : Finset E).filter
    (fun e => (row e, col e) = (eR i, w)), z e)]
  rw [← Finset.sum_fiberwise ((univ : Finset E).filter (fun e => row e = eR i)) col z]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr ?_ fun _ _ => rfl
  ext e; simp [Prod.ext_iff]

theorem aggregateMatrix_col_sum (eR : Fin n ≃ U) (eC : Fin n ≃ V) (z : E → ℝ) (j : Fin n) :
    ∑ i, aggregateMatrix row col eR eC z i j =
      ∑ e ∈ (univ : Finset E).filter (fun e => col e = eC j), z e := by
  classical
  unfold aggregateMatrix mergeFlow
  rw [Equiv.sum_comp eR (fun u => ∑ e ∈ (univ : Finset E).filter
    (fun e => (row e, col e) = (u, eC j)), z e)]
  rw [← Finset.sum_fiberwise ((univ : Finset E).filter (fun e => col e = eC j)) row z]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr ?_ fun _ _ => rfl
  ext e; simp [Prod.ext_iff, and_comm]

end AggregatePermanent

section ExpandedPermanent

variable {n : ℕ} {U V E : Type*} [Fintype U] [Fintype V] [Fintype E]
  [DecidableEq U] [DecidableEq V] [DecidableEq E] {row : E → U} {col : E → V} {L : Finset E}

theorem expFlow_expMatchFun_inl (M : LMatch row col) (x : E → ℝ) (u : U) :
    expFlow L x (expMatchFun (row := row) M.1 (Sum.inl u)) = x (M.1 u) := by
  show expFlow L x (if h : M.1 u ∈ L then aE ⟨M.1 u, h⟩ else dE ⟨M.1 u, h⟩) = _
  split_ifs <;> rfl

theorem expFlow_expMatchFun_inr (M : LMatch row col) (x : E → ℝ) (ℓ : ↥L) :
    expFlow L x (expMatchFun (row := row) M.1 (Sum.inr ℓ)) =
      if M.1 (row ℓ.1) = ℓ.1 then x ℓ.1 else 1 - x ℓ.1 := by
  show expFlow L x (if M.1 (row ℓ.1) = ℓ.1 then cE ℓ else bE ℓ) = _
  split_ifs <;> rfl

variable (row col L)

/-- **The permanent of an expansion.**  A selected long occurrence contributes
`x_e` at its core row and again `x_e` at its private row; an unselected one
contributes `1 - x_e`. -/
theorem permanent_expandedMatrix (eR : Fin n ≃ U ⊕ ↥L) (eC : Fin n ≃ V ⊕ ↥L) (x : E → ℝ) :
    permanent (expandedMatrix row col L eR eC x) =
      ∑ M : LMatch row col, (∏ u, x (M.1 u)) *
        ∏ ℓ ∈ L, if M.1 (row ℓ) = ℓ then x ℓ else 1 - x ℓ := by
  unfold expandedMatrix
  rw [permanent_aggregateMatrix, ← Equiv.sum_comp (expMatchEquiv (row := row) (col := col) (L := L))]
  refine Finset.sum_congr rfl fun M _ => ?_
  rw [Fintype.prod_sum_type]
  simp only [expMatchEquiv_apply, expFlow_expMatchFun_inl, expFlow_expMatchFun_inr]
  congr 1
  exact Finset.prod_coe_sort L (fun ℓ => if M.1 (row ℓ) = ℓ then x ℓ else 1 - x ℓ)

end ExpandedPermanent

section Elimination

variable {n k : ℕ} {U V E : Type*} [Fintype U] [Fintype V] [Fintype E]
  [DecidableEq U] [DecidableEq V] [DecidableEq E] (row : E → U) (col : E → V) (v : U)

/-- The occurrences at a core row, `S_u`. -/
def rowSet (u : U) : Finset E := (univ : Finset E).filter fun e => row e = u

/-- The occurrences off the root row `v`; these are expanded to paths. -/
def offRoot : Finset E := (univ : Finset E).filter fun e => row e ≠ v

/-- Lavi's eliminated weights (5.2): `x_e` at the root row, and
`x_e² ∏_{f ∈ S_i \ e} (1 - x_f)` at every other row. -/
noncomputable def elimWeight (x : E → ℝ) (e : E) : ℝ :=
  x e * if row e = v then 1 else x e * ∏ f ∈ (rowSet row (row e)).erase e, (1 - x f)

theorem offRoot_filter_row (u : U) :
    (offRoot row v).filter (fun e => row e = u) = if u = v then ∅ else rowSet row u := by
  ext e
  split_ifs with h
  · subst h; simp [offRoot]
  · simp only [offRoot, rowSet, mem_filter, mem_univ, true_and]
    constructor
    · exact fun h' => h'.2
    · intro h'; exact ⟨by rw [h']; exact h, h'⟩

/-- The product over a row of the private-row factors. -/
theorem prod_rowSet_ite (M : LMatch row col) (x : E → ℝ) (u : U) :
    ∏ e ∈ rowSet row u, (if M.1 (row e) = e then x e else 1 - x e) =
      x (M.1 u) * ∏ f ∈ (rowSet row u).erase (M.1 u), (1 - x f) := by
  have hmem : M.1 u ∈ rowSet row u := by
    simp only [rowSet, mem_filter, mem_univ, true_and]; exact M.2.1 u
  rw [← Finset.mul_prod_erase _ _ hmem]
  congr 1
  · rw [M.2.1 u, ite_eq_left rfl]
  · refine Finset.prod_congr rfl fun f hf => ?_
    have hru : row f = u := by
      have := (Finset.mem_erase.1 hf).2
      simpa [rowSet] using this
    rw [hru, ite_eq_right (Ne.symm (Finset.mem_erase.1 hf).1)]

/-- **Lavi (5.2), termwise.** The weight of a matching in the expansion equals
its weight in the eliminated matrix. -/
theorem prod_elimWeight (M : LMatch row col) (x : E → ℝ) :
    ∏ u, elimWeight row v x (M.1 u) =
      (∏ u, x (M.1 u)) * ∏ ℓ ∈ offRoot row v, if M.1 (row ℓ) = ℓ then x ℓ else 1 - x ℓ := by
  unfold elimWeight
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [← Finset.prod_fiberwise (offRoot row v) row]
  refine Finset.prod_congr rfl fun u _ => ?_
  rw [offRoot_filter_row, M.2.1 u]
  split_ifs with h
  · simp
  · rw [prod_rowSet_ite]

/-- **Lavi (5.2).**  The permanent of the shortened star equals the permanent
of the eliminated `k × k` matrix, including parallel occurrences. -/
theorem permanent_expandedMatrix_eq_elim (eR : Fin n ≃ U ⊕ ↥(offRoot row v))
    (eC : Fin n ≃ V ⊕ ↥(offRoot row v)) (eR' : Fin k ≃ U) (eC' : Fin k ≃ V) (x : E → ℝ) :
    permanent (expandedMatrix row col (offRoot row v) eR eC x) =
      permanent (aggregateMatrix row col eR' eC' (elimWeight row v x)) := by
  rw [permanent_expandedMatrix, permanent_aggregateMatrix]
  exact Finset.sum_congr rfl fun M _ => (prod_elimWeight row col v M x).symm

end Elimination

section Lift

variable {n : ℕ} {U V E : Type*} [Fintype U] [Fintype V] [Fintype E]
  [DecidableEq U] [DecidableEq V] [DecidableEq E] (row : E → U) (col : E → V) (L : Finset E)

/-- The support of the expansion `D(H, L)` in matrix coordinates. -/
def expSupport (eR : Fin n ≃ U ⊕ ↥L) (eC : Fin n ≃ V ⊕ ↥L) (i j : Fin n) : Prop :=
  ∃ f : ExpEdge L, expRow row L f = eR i ∧ expCol col L f = eC j

set_option linter.unusedSimpArgs false in
/-- Entries of the expanded matrix, by block. -/
theorem expandedMatrix_apply (eR : Fin n ≃ U ⊕ ↥L) (eC : Fin n ≃ V ⊕ ↥L) (x : E → ℝ)
    (r : U ⊕ ↥L) (c : V ⊕ ↥L) :
    expandedMatrix row col L eR eC x (eR.symm r) (eC.symm c) =
      match r, c with
      | Sum.inl u, Sum.inl w =>
          ∑ d ∈ (univ : Finset {e : E // e ∉ L}).filter (fun d => row d.1 = u ∧ col d.1 = w), x d.1
      | Sum.inl u, Sum.inr ℓ => if row ℓ.1 = u then x ℓ.1 else 0
      | Sum.inr ℓ, Sum.inr ℓ' => if ℓ = ℓ' then 1 - x ℓ.1 else 0
      | Sum.inr ℓ, Sum.inl w => if col ℓ.1 = w then x ℓ.1 else 0 := by
  classical
  unfold expandedMatrix aggregateMatrix mergeFlow
  simp only [Equiv.apply_symm_apply]
  rw [Finset.sum_filter, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  rcases r with u | ℓ <;> rcases c with w | ℓ'
  · simp only [expRow, expCol, expFlow, Prod.mk.injEq, Sum.inl.injEq, reduceCtorEq, and_false,
      false_and, ite_false, Finset.sum_const_zero, add_zero]
    rw [Finset.sum_filter]
  · simp only [expRow, expCol, expFlow, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq,
      and_false, false_and, ite_false, Finset.sum_const_zero, add_zero, zero_add]
    rw [Fintype.sum_eq_single ℓ' (fun b hb => by simp [hb])]
    by_cases h : row ℓ'.1 = u <;> simp [h]
  · simp only [expRow, expCol, expFlow, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq,
      and_false, false_and, ite_false, Finset.sum_const_zero, add_zero, zero_add]
    rw [Fintype.sum_eq_single ℓ (fun b hb => by simp [hb])]
    by_cases h : col ℓ.1 = w <;> simp [h]
  · simp only [expRow, expCol, expFlow, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq,
      and_false, false_and, ite_false, Finset.sum_const_zero, add_zero, zero_add]
    by_cases h : ℓ = ℓ'
    · subst h; simp
    · rw [ite_eq_right h]
      exact Finset.sum_eq_zero fun b _ => ite_eq_right fun hb => h (hb.1.symm.trans hb.2)

variable {row col L}

/-- The support of the expansion, block by block. -/
theorem exists_expEdge_iff (r : U ⊕ ↥L) (c : V ⊕ ↥L) :
    (∃ f : ExpEdge L, expRow row L f = r ∧ expCol col L f = c) ↔
      match r, c with
      | Sum.inl u, Sum.inl w => ∃ d : {e : E // e ∉ L}, row d.1 = u ∧ col d.1 = w
      | Sum.inl u, Sum.inr ℓ => row ℓ.1 = u
      | Sum.inr ℓ, Sum.inr ℓ' => ℓ = ℓ'
      | Sum.inr ℓ, Sum.inl w => col ℓ.1 = w := by
  constructor
  · rintro ⟨f, hr, hc⟩
    rcases f with d | ℓ | ℓ | ℓ <;> simp only [expRow, expCol] at hr hc <;> subst hr <;> subst hc
    · exact ⟨d, rfl, rfl⟩
    · rfl
    · rfl
    · rfl
  · rcases r with u | ℓ <;> rcases c with w | ℓ'
    · rintro ⟨d, hu, hw⟩; exact ⟨Sum.inl d, by simp [expRow, hu], by simp [expCol, hw]⟩
    · intro h; exact ⟨Sum.inr (Sum.inl ℓ'), by simp [expRow, h], rfl⟩
    · intro h; exact ⟨Sum.inr (Sum.inr (Sum.inr ℓ)), rfl, by simp [expCol, h]⟩
    · intro h; subst h; exact ⟨Sum.inr (Sum.inr (Sum.inl ℓ)), rfl, rfl⟩

variable {eR : Fin n ≃ U ⊕ ↥L} {eC : Fin n ≃ V ⊕ ↥L} {Y : Square n}

theorem entry_eq_zero (hY : InFace (expSupport row col L eR eC) Y) (r : U ⊕ ↥L) (c : V ⊕ ↥L)
    (h : ¬ ∃ f : ExpEdge L, expRow row L f = r ∧ expCol col L f = c) :
    Y (eR.symm r) (eC.symm c) = 0 := by
  by_contra h0
  obtain ⟨f, hf1, hf2⟩ := hY.2 _ _ h0
  rw [Equiv.apply_symm_apply] at hf1 hf2
  exact h ⟨f, hf1, hf2⟩

/-- The private column of `ℓ` meets only `row ℓ` and the private row. -/
theorem privateCol_sum (hY : InFace (expSupport row col L eR eC) Y) (ℓ : ↥L) :
    Y (eR.symm (Sum.inl (row ℓ.1))) (eC.symm (Sum.inr ℓ)) +
      Y (eR.symm (Sum.inr ℓ)) (eC.symm (Sum.inr ℓ)) = 1 := by
  have h := hY.1.2.2 (eC.symm (Sum.inr ℓ))
  rw [← Equiv.sum_comp eR.symm] at h
  rw [← h, Fintype.sum_eq_add (Sum.inl (row ℓ.1)) (Sum.inr ℓ) Sum.inl_ne_inr]
  rintro r ⟨h1, h2⟩
  refine entry_eq_zero hY r _ ?_
  rw [exists_expEdge_iff]
  rcases r with u | ℓ'
  · exact fun h' => h1 (by rw [← h'])
  · exact fun h' => h2 (by rw [h'])

/-- The private row of `ℓ` meets only the private column and `col ℓ`. -/
theorem privateRow_sum (hY : InFace (expSupport row col L eR eC) Y) (ℓ : ↥L) :
    Y (eR.symm (Sum.inr ℓ)) (eC.symm (Sum.inr ℓ)) +
      Y (eR.symm (Sum.inr ℓ)) (eC.symm (Sum.inl (col ℓ.1))) = 1 := by
  have h := hY.1.2.1 (eR.symm (Sum.inr ℓ))
  rw [← Equiv.sum_comp eC.symm] at h
  rw [← h, Fintype.sum_eq_add (Sum.inr ℓ) (Sum.inl (col ℓ.1)) Sum.inr_ne_inl]
  rintro c ⟨h1, h2⟩
  refine entry_eq_zero hY _ c ?_
  rw [exists_expEdge_iff]
  rcases c with w | ℓ'
  · exact fun h' => h2 (by rw [h'])
  · exact fun h' => h1 (by rw [h'])

variable (row col L)

/-- Number of direct occurrences parallel to `e`. -/
def directMult (e : E) : ℕ :=
  ((univ : Finset {d : E // d ∉ L}).filter fun d => row d.1 = row e ∧ col d.1 = col e).card

/-- Lavi's flow lift: long occurrences read their private row, and a direct
matrix entry is split equally among its parallel direct occurrences. -/
noncomputable def liftFlow (eR : Fin n ≃ U ⊕ ↥L) (eC : Fin n ≃ V ⊕ ↥L) (Y : Square n)
    (e : E) : ℝ :=
  if h : e ∈ L then Y (eR.symm (Sum.inr ⟨e, h⟩)) (eC.symm (Sum.inl (col e)))
  else Y (eR.symm (Sum.inl (row e))) (eC.symm (Sum.inl (col e))) / directMult row col L e

variable {row col L}

/-- **Lavi's flow lift.**  Every doubly stochastic matrix supported on the
expansion `D(H, L)` is the expanded matrix `X_x` of its lift. -/
theorem eq_expandedMatrix_liftFlow (hY : InFace (expSupport row col L eR eC) Y) :
    Y = expandedMatrix row col L eR eC (liftFlow row col L eR eC Y) := by
  funext i j
  rw [← eR.symm_apply_apply i, ← eC.symm_apply_apply j, expandedMatrix_apply]
  rcases eR i with u | ℓ <;> rcases eC j with w | ℓ' <;> dsimp only
  · -- direct block
    set S := (univ : Finset {d : E // d ∉ L}).filter (fun d => row d.1 = u ∧ col d.1 = w)
    have hterm : ∀ d ∈ S, liftFlow row col L eR eC Y d.1 =
        Y (eR.symm (Sum.inl u)) (eC.symm (Sum.inl w)) / S.card := by
      intro d hd
      obtain ⟨hu, hw⟩ := (Finset.mem_filter.1 hd).2
      unfold liftFlow directMult
      rw [dite_eq_right d.2, hu, hw]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
    rcases S.eq_empty_or_nonempty with h0 | hne
    · rw [h0, Finset.card_empty, Nat.cast_zero, zero_mul]
      refine entry_eq_zero hY _ _ ?_
      rw [exists_expEdge_iff]
      rintro ⟨d, hu, hw⟩
      have : d ∈ S := Finset.mem_filter.2 ⟨mem_univ _, hu, hw⟩
      rw [h0] at this; exact Finset.notMem_empty _ this
    · have hc : (S.card : ℝ) ≠ 0 := by exact_mod_cast hne.card_pos.ne'
      field_simp
  · -- core row to private column
    by_cases h : row ℓ'.1 = u
    · rw [ite_eq_left h]
      subst h
      have h1 := privateCol_sum hY ℓ'
      have h2 := privateRow_sum hY ℓ'
      unfold liftFlow
      rw [dite_eq_left ℓ'.2]
      linarith
    · rw [ite_eq_right h]
      exact entry_eq_zero hY _ _ (by rw [exists_expEdge_iff]; exact h)
  · -- private row to core column
    by_cases h : col ℓ.1 = w
    · rw [ite_eq_left h]
      subst h
      unfold liftFlow
      rw [dite_eq_left ℓ.2]
    · rw [ite_eq_right h]
      exact entry_eq_zero hY _ _ (by rw [exists_expEdge_iff]; exact h)
  · -- private block
    by_cases h : ℓ = ℓ'
    · rw [ite_eq_left h]
      subst h
      have h2 := privateRow_sum hY ℓ
      unfold liftFlow
      rw [dite_eq_left ℓ.2]
      linarith
    · rw [ite_eq_right h]
      exact entry_eq_zero hY _ _ (by rw [exists_expEdge_iff]; exact h)

theorem liftFlow_nonneg (hY : InFace (expSupport row col L eR eC) Y) (e : E) :
    0 ≤ liftFlow row col L eR eC Y e := by
  unfold liftFlow
  split_ifs
  · exact hY.1.1 _ _
  · exact div_nonneg (hY.1.1 _ _) (Nat.cast_nonneg _)

theorem liftFlow_le_one (hY : InFace (expSupport row col L eR eC) Y) {e : E} (he : e ∈ L) :
    liftFlow row col L eR eC Y e ≤ 1 := by
  have h2 := privateRow_sum hY ⟨e, he⟩
  have := hY.1.1 (eR.symm (Sum.inr ⟨e, he⟩)) (eC.symm (Sum.inr ⟨e, he⟩))
  unfold liftFlow
  rw [dite_eq_left he]
  linarith

variable (row col L)

theorem sum_expFlow_row (x : E → ℝ) (u : U) :
    ∑ f ∈ (univ : Finset (ExpEdge L)).filter (fun f => expRow row L f = Sum.inl u),
      expFlow L x f = ∑ e ∈ rowSet row u, x e := by
  classical
  rw [Finset.sum_filter, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [expRow, expFlow, reduceCtorEq, ite_false, Finset.sum_const_zero, add_zero,
    Sum.inl.injEq]
  rw [rowSet, Finset.sum_filter, ← Fintype.sum_subtype_add_sum_subtype (fun e => e ∈ L), add_comm]
  convert rfl

theorem sum_expFlow_col (x : E → ℝ) (w : V) :
    ∑ f ∈ (univ : Finset (ExpEdge L)).filter (fun f => expCol col L f = Sum.inl w),
      expFlow L x f = ∑ e ∈ (univ : Finset E).filter (fun e => col e = w), x e := by
  classical
  rw [Finset.sum_filter, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [expCol, expFlow, reduceCtorEq, ite_false, Finset.sum_const_zero, zero_add,
    Sum.inl.injEq]
  rw [Finset.sum_filter, ← Fintype.sum_subtype_add_sum_subtype (fun e => e ∈ L), add_comm]
  convert rfl

variable {row col L}

/-- A doubly stochastic expanded matrix has unit core row sums. -/
theorem rowSet_sum_of_DS {x : E → ℝ}
    (hX : DoublyStochastic (expandedMatrix row col L eR eC x)) (u : U) :
    ∑ e ∈ rowSet row u, x e = 1 := by
  have h := hX.2.1 (eR.symm (Sum.inl u))
  unfold expandedMatrix at h
  rw [aggregateMatrix_row_sum, Equiv.apply_symm_apply, sum_expFlow_row] at h
  exact h

/-- A doubly stochastic expanded matrix has unit core column sums. -/
theorem colSet_sum_of_DS {x : E → ℝ}
    (hX : DoublyStochastic (expandedMatrix row col L eR eC x)) (w : V) :
    ∑ e ∈ (univ : Finset E).filter (fun e => col e = w), x e = 1 := by
  have h := hX.2.2 (eC.symm (Sum.inl w))
  unfold expandedMatrix at h
  rw [aggregateMatrix_col_sum, Equiv.apply_symm_apply, sum_expFlow_col] at h
  exact h

end Lift

end LaviSection2
