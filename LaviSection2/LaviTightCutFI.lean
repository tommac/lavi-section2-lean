import LaviSection2.LaviTightCutEntropy
import LaviSection2.LaviLemma25

/-!
# Lavi Lemma 4.1, removability part (4.3)

For an oriented cut of a balanced core, full indecomposability splits across
the two closed factors:

`H[O]` is FI  ⟺  `H₁[O]` and `H₂[O]` are FI,

for every occurrence set `O` (`coreFI_cut_iff`).  Applied to `O = E - e` this
gives Lavi's (4.3) for a crossing occurrence and the internal assertion for an
internal one.

The proof is a strict-Hall computation on sum types (`fiRel_cut_iff`).  With
rows `α₁ ⊕ α₂`, columns `β₁ ⊕ β₂`, no edge from `α₂` to `β₁`, `|α₁| = |β₁| + 1`
and `|β₂| = |α₂| + 1`, the neighborhood of `A ⊕ B` splits as
`L(A) ⊕ (X(A) ∪ Q(B))`, where `L` are the internal neighbors in `β₁`, `X` the
crossing neighbors and `Q` the internal neighbors in `β₂`.  The factor
neighborhoods are `L(A) ⊕ [X(A) ≠ ∅]` and `[marker] X(all) ∪ Q(B)`, and the
Hall surpluses transfer in both directions.  This replaces the
2-connectivity argument in the text.
-/

set_option linter.unusedSectionVars false

namespace LaviSection2

open Finset

/-- Full indecomposability of a bipartite relation: strict Hall, and every
row has a neighbor (this is `CoreFI` for the adjacency of a core). -/
def FIRel {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (S : α → β → Prop) : Prop :=
  StrictHallOn S ∧ ∀ a, ∃ b, S a b

section CutHall

variable {α₁ α₂ β₁ β₂ : Type*} [Fintype α₁] [Fintype α₂] [Fintype β₁] [Fintype β₂]
  [DecidableEq α₁] [DecidableEq α₂] [DecidableEq β₁] [DecidableEq β₂]
  (S : α₁ ⊕ α₂ → β₁ ⊕ β₂ → Prop)

/-- The first factor: crossing edges go to a marker column. -/
def cutLeft : α₁ → β₁ ⊕ Unit → Prop
  | a, Sum.inl b => S (Sum.inl a) (Sum.inl b)
  | a, Sum.inr _ => ∃ b, S (Sum.inl a) (Sum.inr b)

/-- The second factor: crossing edges come from a marker row. -/
def cutRight : Unit ⊕ α₂ → β₂ → Prop
  | Sum.inl _, b => ∃ a, S (Sum.inl a) (Sum.inr b)
  | Sum.inr a, b => S (Sum.inr a) (Sum.inr b)

/-- Internal neighbors in `β₁` of rows `A ⊆ α₁`. -/
noncomputable def nbL (A : Finset α₁) : Finset β₁ := by
  classical exact univ.filter fun b => ∃ a ∈ A, S (Sum.inl a) (Sum.inl b)

/-- Crossing neighbors in `β₂` of rows `A ⊆ α₁`. -/
noncomputable def nbX (A : Finset α₁) : Finset β₂ := by
  classical exact univ.filter fun b => ∃ a ∈ A, S (Sum.inl a) (Sum.inr b)

/-- Internal neighbors in `β₂` of rows `B ⊆ α₂`. -/
noncomputable def nbQ (B : Finset α₂) : Finset β₂ := by
  classical exact univ.filter fun b => ∃ a ∈ B, S (Sum.inr a) (Sum.inr b)

/-- Some row of `A` has a crossing edge. -/
def CrossFrom (A : Finset α₁) : Prop := ∃ a ∈ A, ∃ b, S (Sum.inl a) (Sum.inr b)

variable {S}

@[simp] theorem mem_nbL {A : Finset α₁} {b : β₁} :
    b ∈ nbL S A ↔ ∃ a ∈ A, S (Sum.inl a) (Sum.inl b) := by
  classical simp [nbL]

@[simp] theorem mem_nbX {A : Finset α₁} {b : β₂} :
    b ∈ nbX S A ↔ ∃ a ∈ A, S (Sum.inl a) (Sum.inr b) := by
  classical simp [nbX]

@[simp] theorem mem_nbQ {B : Finset α₂} {b : β₂} :
    b ∈ nbQ S B ↔ ∃ a ∈ B, S (Sum.inr a) (Sum.inr b) := by
  classical simp [nbQ]

theorem nbX_nonempty_iff (A : Finset α₁) : (nbX S A).Nonempty ↔ CrossFrom S A := by
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨a, ha, h⟩ := mem_nbX.1 hb
    exact ⟨a, ha, b, h⟩
  · rintro ⟨a, ha, b, h⟩
    exact ⟨b, mem_nbX.2 ⟨a, ha, h⟩⟩

theorem card_rowNeighborsOn_sum (hS : ∀ a b, ¬ S (Sum.inr a) (Sum.inl b))
    (R : Finset (α₁ ⊕ α₂)) :
    (rowNeighborsOn S R).card =
      (nbL S R.toLeft).card + (nbX S R.toLeft ∪ nbQ S R.toRight).card := by
  classical
  have h : rowNeighborsOn S R = (nbL S R.toLeft).disjSum (nbX S R.toLeft ∪ nbQ S R.toRight) := by
    ext j
    cases j with
    | inl b =>
      simp only [mem_rowNeighborsOn, inl_mem_disjSum, mem_nbL, mem_toLeft]
      constructor
      · rintro ⟨i, hi, hS'⟩
        cases i with
        | inl a => exact ⟨a, hi, hS'⟩
        | inr a => exact absurd hS' (hS a b)
      · rintro ⟨a, ha, hS'⟩
        exact ⟨_, ha, hS'⟩
    | inr b =>
      simp only [mem_rowNeighborsOn, inr_mem_disjSum, mem_nbX, mem_nbQ, mem_union, mem_toLeft,
        mem_toRight]
      constructor
      · rintro ⟨i, hi, hS'⟩
        cases i with
        | inl a => exact Or.inl ⟨a, hi, hS'⟩
        | inr a => exact Or.inr ⟨a, hi, hS'⟩
      · rintro (⟨a, ha, hS'⟩ | ⟨a, ha, hS'⟩)
        · exact ⟨_, ha, hS'⟩
        · exact ⟨_, ha, hS'⟩
  rw [h, card_disjSum]

theorem card_rowNeighborsOn_cutLeft (A : Finset α₁) :
    (rowNeighborsOn (cutLeft S) A).card =
      (nbL S A).card + if (nbX S A).Nonempty then 1 else 0 := by
  classical
  have h : rowNeighborsOn (cutLeft S) A =
      (nbL S A).disjSum ((univ : Finset Unit).filter fun _ => (nbX S A).Nonempty) := by
    ext j
    cases j with
    | inl b =>
      simp [mem_rowNeighborsOn, cutLeft]
    | inr t =>
      simp only [mem_rowNeighborsOn, inr_mem_disjSum, mem_filter, mem_univ, true_and,
        nbX_nonempty_iff, CrossFrom, cutLeft]
  rw [h, card_disjSum]
  by_cases hP : (nbX S A).Nonempty <;> simp [hP]

theorem rowNeighborsOn_cutRight (R : Finset (Unit ⊕ α₂)) :
    rowNeighborsOn (cutRight S) R =
      (if Sum.inl () ∈ R then nbX S univ else ∅) ∪ nbQ S R.toRight := by
  classical
  ext b
  by_cases hm : Sum.inl () ∈ R
  · simp only [if_pos hm, mem_union, mem_rowNeighborsOn, mem_nbX, mem_nbQ, mem_toRight]
    constructor
    · rintro ⟨i, hi, hS'⟩
      cases i with
      | inl t => obtain ⟨a, ha⟩ := hS'; exact Or.inl ⟨a, mem_univ _, ha⟩
      | inr a => exact Or.inr ⟨a, hi, hS'⟩
    · rintro (⟨a, _, ha⟩ | ⟨a, ha, hS'⟩)
      · exact ⟨Sum.inl (), hm, a, ha⟩
      · exact ⟨Sum.inr a, ha, hS'⟩
  · simp only [if_neg hm, empty_union, mem_rowNeighborsOn, mem_nbQ, mem_toRight]
    constructor
    · rintro ⟨i, hi, hS'⟩
      cases i with
      | inl t => cases t; exact absurd hi hm
      | inr a => exact ⟨a, hi, hS'⟩
    · rintro ⟨a, ha, hS'⟩
      exact ⟨Sum.inr a, ha, hS'⟩

theorem nbL_empty : nbL S (∅ : Finset α₁) = ∅ := by
  ext b; simp

theorem nbX_empty : nbX S (∅ : Finset α₁) = ∅ := by
  ext b; simp

theorem nbQ_empty : nbQ S (∅ : Finset α₂) = ∅ := by
  ext b; simp

/-- **Strict Hall splits across an oriented cut.** -/
theorem fiRel_cut_iff (hS : ∀ a b, ¬ S (Sum.inr a) (Sum.inl b))
    (h1 : Fintype.card α₁ = Fintype.card β₁ + 1) (h2 : Fintype.card β₂ = Fintype.card α₂ + 1) :
    FIRel S ↔ FIRel (cutLeft S) ∧ FIRel (cutRight S) := by
  classical
  have hcardα : Fintype.card (α₁ ⊕ α₂) = Fintype.card α₁ + Fintype.card α₂ := Fintype.card_sum
  have hne₁ : (univ : Finset α₁).Nonempty := by
    rw [Finset.univ_nonempty_iff, ← Fintype.card_pos_iff]; omega
  have hLle : ∀ A : Finset α₁, (nbL S A).card ≤ Fintype.card β₁ := fun A => card_le_univ _
  have hXQle : ∀ (A : Finset α₁) (B : Finset α₂),
      (nbX S A ∪ nbQ S B).card ≤ Fintype.card β₂ := fun A B => card_le_univ _
  constructor
  · rintro ⟨hH, hcov⟩
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · -- strict Hall for the first factor
      intro A hA hAc
      have key := hH (A.disjSum univ) (by
        obtain ⟨a, ha⟩ := hA; exact ⟨Sum.inl a, inl_mem_disjSum.2 ha⟩)
        (by rw [card_disjSum, card_univ, hcardα]; omega)
      rw [card_rowNeighborsOn_sum hS, toLeft_disjSum, toRight_disjSum, card_disjSum,
        card_univ] at key
      rw [card_rowNeighborsOn_cutLeft]
      have := hXQle A univ
      by_cases hP : (nbX S A).Nonempty
      · rw [if_pos hP]; omega
      · rw [if_neg hP]
        have key2 := hH (A.disjSum ∅) (by
          obtain ⟨a, ha⟩ := hA; exact ⟨Sum.inl a, inl_mem_disjSum.2 ha⟩)
          (by rw [card_disjSum, card_empty, hcardα]; omega)
        rw [card_rowNeighborsOn_sum hS, toLeft_disjSum, toRight_disjSum, card_disjSum,
          card_empty, nbQ_empty, union_empty,
          Finset.not_nonempty_iff_eq_empty.1 hP,
          card_empty] at key2
        omega
    · intro a
      obtain ⟨c, hc⟩ := hcov (Sum.inl a)
      cases c with
      | inl b => exact ⟨Sum.inl b, hc⟩
      | inr b => exact ⟨Sum.inr (), b, hc⟩
    · -- strict Hall for the second factor
      intro R hR hRc
      rw [rowNeighborsOn_cutRight]
      have hsplit := card_toLeft_add_card_toRight (u := R)
      have hleft : R.toLeft.card ≤ 1 := by
        have := card_le_univ R.toLeft; rwa [Fintype.card_unit] at this
      rw [Fintype.card_sum, Fintype.card_unit] at hRc
      by_cases hm : Sum.inl () ∈ R
      · rw [if_pos hm]
        have hl1 : R.toLeft.card = 1 :=
          le_antisymm hleft (card_pos.2 ⟨(), mem_toLeft.2 hm⟩)
        have key := hH (univ.disjSum R.toRight) (by
          obtain ⟨a, ha⟩ := hne₁; exact ⟨Sum.inl a, inl_mem_disjSum.2 ha⟩)
          (by rw [card_disjSum, card_univ, hcardα]; omega)
        rw [card_rowNeighborsOn_sum hS, toLeft_disjSum, toRight_disjSum, card_disjSum,
          card_univ] at key
        have := hLle univ
        omega
      · rw [if_neg hm, empty_union]
        have hl0 : R.toLeft.card = 0 := by
          rw [card_eq_zero, eq_empty_iff_forall_notMem]
          intro t ht; cases t; exact hm (mem_toLeft.1 ht)
        have hRr : R.toRight.Nonempty := by
          rw [← card_pos]; have := card_pos.2 hR; omega
        have hRrc : R.toRight.card ≤ Fintype.card α₂ := card_le_univ _
        have key := hH ((∅ : Finset α₁).disjSum R.toRight) (by
          obtain ⟨a, ha⟩ := hRr; exact ⟨Sum.inr a, inr_mem_disjSum.2 ha⟩)
          (by rw [card_disjSum, card_empty, hcardα]; omega)
        rw [card_rowNeighborsOn_sum hS, toLeft_disjSum, toRight_disjSum, card_disjSum,
          card_empty, nbL_empty, nbX_empty, card_empty, empty_union] at key
        omega
    · intro r
      cases r with
      | inr a =>
        obtain ⟨c, hc⟩ := hcov (Sum.inr a)
        cases c with
        | inl b => exact absurd hc (hS a b)
        | inr b => exact ⟨b, hc⟩
      | inl t =>
        by_contra hno
        push Not at hno
        have hX : nbX S univ = ∅ := by
          rw [eq_empty_iff_forall_notMem]
          intro b hb
          obtain ⟨a, _, h⟩ := mem_nbX.1 hb
          exact hno b ⟨a, h⟩
        by_cases hα₂ : 0 < Fintype.card α₂
        · have key := hH (univ.disjSum ∅) (by
            obtain ⟨a, ha⟩ := hne₁; exact ⟨Sum.inl a, inl_mem_disjSum.2 ha⟩)
            (by rw [card_disjSum, card_univ, card_empty, hcardα]; omega)
          rw [card_rowNeighborsOn_sum hS, toLeft_disjSum, toRight_disjSum, card_disjSum,
            card_univ, card_empty, hX, nbQ_empty, union_empty, card_empty] at key
          have := hLle univ
          omega
        · have hα₂0 : Fintype.card α₂ = 0 := by omega
          have hemp : IsEmpty α₂ := Fintype.card_eq_zero_iff.1 hα₂0
          obtain ⟨b₀⟩ : Nonempty β₂ := Fintype.card_pos_iff.1 (by omega)
          by_cases hβ₁ : Fintype.card β₁ = 0
          · -- order one: the single row's neighbor must cross
            obtain ⟨a₀, -⟩ := hne₁
            obtain ⟨c, hc⟩ := hcov (Sum.inl a₀)
            cases c with
            | inl b => exact (Fintype.card_eq_zero_iff.1 hβ₁).elim b
            | inr b => exact hno b ⟨a₀, hc⟩
          · -- the column `b₀` would have no neighbor
            have hbal : Fintype.card (α₁ ⊕ α₂) = Fintype.card (β₁ ⊕ β₂) := by
              rw [hcardα, Fintype.card_sum]; omega
            have hT := (strictHallOn_transpose_iff hbal S).2 hH
            have := hT {Sum.inr b₀} (singleton_nonempty _)
              (by rw [card_singleton, Fintype.card_sum]; omega)
            rw [card_singleton] at this
            have hz : rowNeighborsOn (fun j i => S i j) {Sum.inr b₀} = ∅ := by
              rw [eq_empty_iff_forall_notMem]
              intro i hi
              obtain ⟨j, hj, hS'⟩ := mem_rowNeighborsOn.1 hi
              rw [mem_singleton.1 hj] at hS'
              cases i with
              | inl a => exact hno b₀ ⟨a, hS'⟩
              | inr a => exact hemp.elim a
            rw [hz, card_empty] at this
            omega
  · rintro ⟨⟨h1H, h1cov⟩, ⟨h2H, h2cov⟩⟩
    -- every column of `β₁` is reached from `α₁`
    have hLuniv : (nbL S univ).card = Fintype.card β₁ := by
      rw [← card_univ]
      congr 1
      rw [eq_univ_iff_forall]
      intro b
      have hbal : Fintype.card α₁ = Fintype.card (β₁ ⊕ Unit) := by
        rw [Fintype.card_sum, Fintype.card_unit]; exact h1
      have hT := (strictHallOn_transpose_iff hbal (cutLeft S)).2 h1H
      have := hT {Sum.inl b} (singleton_nonempty _)
        (by
          have : 0 < Fintype.card β₁ := Fintype.card_pos_iff.2 ⟨b⟩
          rw [card_singleton, Fintype.card_sum, Fintype.card_unit]; omega)
      rw [card_singleton] at this
      obtain ⟨a, ha⟩ := card_pos.1 (lt_trans zero_lt_one this)
      obtain ⟨j, hj, hS'⟩ := mem_rowNeighborsOn.1 ha
      rw [mem_singleton.1 hj] at hS'
      rw [mem_nbL]
      exact ⟨a, mem_univ _, hS'⟩
    -- Hall surpluses of the factors, in parent terms
    have hQ : ∀ B : Finset α₂, B.Nonempty → B.card < (nbQ S B).card := by
      intro B hB
      have := h2H ((∅ : Finset Unit).disjSum B) (by
        obtain ⟨a, ha⟩ := hB; exact ⟨Sum.inr a, inr_mem_disjSum.2 ha⟩)
        (by
          have := card_le_univ B
          rw [card_disjSum, card_empty, Fintype.card_sum, Fintype.card_unit]; omega)
      rw [rowNeighborsOn_cutRight, if_neg (by rw [inl_mem_disjSum]; exact notMem_empty _),
        empty_union, toRight_disjSum, card_disjSum, card_empty] at this
      omega
    have hXQ : ∀ B : Finset α₂, B.card < Fintype.card α₂ →
        B.card + 1 < (nbX S univ ∪ nbQ S B).card := by
      intro B hBc
      have := h2H ((univ : Finset Unit).disjSum B) ⟨Sum.inl (), inl_mem_disjSum.2 (mem_univ _)⟩
        (by rw [card_disjSum, card_univ, Fintype.card_sum, Fintype.card_unit]; omega)
      rw [rowNeighborsOn_cutRight, if_pos (inl_mem_disjSum.2 (mem_univ _)), toRight_disjSum,
        card_disjSum, card_univ, Fintype.card_unit] at this
      omega
    have hA : ∀ A : Finset α₁, A.Nonempty → A.card < Fintype.card α₁ →
        A.card < (nbL S A).card + if (nbX S A).Nonempty then 1 else 0 := by
      intro A hA hAc
      have := h1H A hA hAc
      rwa [card_rowNeighborsOn_cutLeft] at this
    refine ⟨?_, ?_⟩
    · intro R hR hRc
      rw [card_rowNeighborsOn_sum hS]
      have hsplit := card_toLeft_add_card_toRight (u := R)
      rw [hcardα] at hRc
      have hBc : R.toRight.card ≤ Fintype.card α₂ := card_le_univ _
      have hAc : R.toLeft.card ≤ Fintype.card α₁ := card_le_univ _
      have hQB : R.toRight.card ≤ (nbQ S R.toRight).card := by
        rcases R.toRight.eq_empty_or_nonempty with h | h
        · rw [h]; simp
        · exact (hQ _ h).le
      have hsub : nbQ S R.toRight ⊆ nbX S R.toLeft ∪ nbQ S R.toRight := subset_union_right
      have hQsub := card_le_card hsub
      rcases R.toLeft.eq_empty_or_nonempty with hA0 | hA0
      · -- no rows of `α₁`
        rw [hA0, nbL_empty, nbX_empty, card_empty, empty_union]
        rw [hA0, card_empty] at hsplit
        have hBne : R.toRight.Nonempty := by
          rw [← card_pos]; have := card_pos.2 hR; omega
        have := hQ _ hBne
        omega
      · by_cases hAu : R.toLeft.card = Fintype.card α₁
        · -- all rows of `α₁`
          have hAeq : R.toLeft = univ := eq_univ_of_card _ hAu
          rw [hAeq, hLuniv]
          have := hXQ R.toRight (by omega)
          omega
        · have hAlt : R.toLeft.card < Fintype.card α₁ := lt_of_le_of_ne hAc hAu
          have hHall := hA _ hA0 hAlt
          by_cases hP : (nbX S R.toLeft).Nonempty
          · rw [if_pos hP] at hHall
            rcases R.toRight.eq_empty_or_nonempty with hB0 | hB0
            · have hXne := hP
              have : 1 ≤ (nbX S R.toLeft ∪ nbQ S R.toRight).card :=
                card_pos.2 (hXne.mono subset_union_left)
              rw [hB0, card_empty] at hsplit
              omega
            · have := hQ _ hB0
              omega
          · rw [if_neg hP] at hHall
            omega
    · intro i
      cases i with
      | inl a =>
        obtain ⟨c, hc⟩ := h1cov a
        cases c with
        | inl b => exact ⟨Sum.inl b, hc⟩
        | inr t => obtain ⟨b, hb⟩ := hc; exact ⟨Sum.inr b, hb⟩
      | inr a =>
        obtain ⟨b, hb⟩ := h2cov (Sum.inr a)
        exact ⟨Sum.inr b, hb⟩

end CutHall

section Relabel

variable {α β α' β' : Type*} [Fintype α] [Fintype β] [Fintype α'] [Fintype β']
  [DecidableEq α] [DecidableEq β] [DecidableEq α'] [DecidableEq β']

theorem fiRel_relabel (eα : α ≃ α') (eβ : β ≃ β') {S : α → β → Prop} {T : α' → β' → Prop}
    (h : ∀ a b, S a b ↔ T (eα a) (eβ b)) : FIRel S ↔ FIRel T := by
  refine and_congr (strictHallOn_relabel_iff eα eβ h) ⟨fun hS a' => ?_, fun hT a => ?_⟩
  · obtain ⟨b, hb⟩ := hS (eα.symm a')
    exact ⟨eβ b, by simpa using (h _ _).1 hb⟩
  · obtain ⟨b', hb⟩ := hT (eα a)
    exact ⟨eβ.symm b', (h _ _).2 (by simpa using hb)⟩

theorem fiRel_congr {S T : α → β → Prop} (h : ∀ a b, S a b ↔ T a b) : FIRel S ↔ FIRel T :=
  fiRel_relabel (Equiv.refl _) (Equiv.refl _) h

end Relabel

section CoreCut

variable {U V E : Type*} [Fintype U] [Fintype V] [Fintype E]
  [DecidableEq U] [DecidableEq V] [DecidableEq E]

theorem coreFI_iff_fiRel (row : E → U) (col : E → V) (O : Finset E) :
    CoreFI row col O ↔ FIRel (coreAdj row col O) := by
  unfold CoreFI FIRel
  refine and_congr Iff.rfl (forall_congr' fun u => ?_)
  constructor
  · rintro ⟨e, he, hr⟩; exact ⟨col e, e, he, hr, rfl⟩
  · rintro ⟨v, e, he, hr, -⟩; exact ⟨e, he, hr⟩

variable {row : E → U} {col : E → V} (K : ShoreCut row col)

namespace ShoreCut

/-- The parent adjacency of `O` in shore coordinates. -/
def sumAdj (O : Finset E) : K.U₁ ⊕ K.U₂ → K.V₁ ⊕ K.V₂ → Prop :=
  fun i j => coreAdj row col O (Equiv.sumCompl K.sR i) (Equiv.sumCompl K.sC j)

theorem sumAdj_back (O : Finset E) (a : K.U₂) (b : K.V₁) :
    ¬ K.sumAdj O (Sum.inr a) (Sum.inl b) := by
  rintro ⟨e, -, hr, hc⟩
  simp only [Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr] at hr hc
  have := K.back e (by rw [hc]; exact b.2)
  rw [hr] at this
  exact a.2 this

theorem coreAdj₁_iff (O : Finset E) (a : K.U₁) (c : K.V₁ ⊕ Unit) :
    coreAdj K.row₁ K.col₁ (O.subtype fun e => K.sR (row e)) a c ↔ cutLeft (K.sumAdj O) a c := by
  cases c with
  | inl b =>
    simp only [cutLeft, sumAdj, coreAdj, Equiv.sumCompl_apply_inl, Finset.mem_subtype]
    constructor
    · rintro ⟨e, he, hr, hc⟩
      exact ⟨e.1, he, congrArg Subtype.val hr, K.col_of_col₁_eq_inl hc⟩
    · rintro ⟨e, he, hr, hc⟩
      have hs : K.sR (row e) := by rw [hr]; exact a.2
      refine ⟨⟨e, hs⟩, he, Subtype.ext hr, ?_⟩
      have hsc : K.sC (col e) := by rw [hc]; exact b.2
      unfold col₁
      rw [dif_pos hsc]
      exact congrArg Sum.inl (Subtype.ext hc)
  | inr t =>
    simp only [cutLeft, sumAdj, coreAdj, Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr,
      Finset.mem_subtype]
    constructor
    · rintro ⟨e, he, hr, hc⟩
      have hnc : ¬ K.sC (col e.1) := (K.col₁_eq_inr_iff e).1 (by cases t; exact hc)
      exact ⟨⟨col e.1, hnc⟩, e.1, he, congrArg Subtype.val hr, rfl⟩
    · rintro ⟨b, e, he, hr, hc⟩
      have hs : K.sR (row e) := by rw [hr]; exact a.2
      refine ⟨⟨e, hs⟩, he, Subtype.ext hr, ?_⟩
      cases t
      exact (K.col₁_eq_inr_iff _).2 (by show ¬ K.sC (col e); rw [hc]; exact b.2)

theorem coreAdj₂_iff (O : Finset E) (r : Unit ⊕ K.U₂) (b : K.V₂) :
    coreAdj K.row₂ K.col₂ (O.subtype fun e => ¬ K.sC (col e)) r b ↔ cutRight (K.sumAdj O) r b := by
  cases r with
  | inl t =>
    simp only [cutRight, sumAdj, coreAdj, Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr,
      Finset.mem_subtype]
    constructor
    · rintro ⟨e, he, hr, hc⟩
      have hs : K.sR (row e.1) := by
        by_contra h
        rw [K.row₂_of_not_sR h] at hr
        exact Sum.inr_ne_inl hr
      exact ⟨⟨row e.1, hs⟩, e.1, he, rfl, congrArg Subtype.val hc⟩
    · rintro ⟨a, e, he, hr, hc⟩
      have hnc : ¬ K.sC (col e) := by rw [hc]; exact b.2
      refine ⟨⟨e, hnc⟩, he, ?_, Subtype.ext hc⟩
      cases t
      exact K.row₂_of_sR (by show K.sR (row e); rw [hr]; exact a.2)
  | inr a =>
    simp only [cutRight, sumAdj, coreAdj, Equiv.sumCompl_apply_inr, Finset.mem_subtype]
    constructor
    · rintro ⟨e, he, hr, hc⟩
      exact ⟨e.1, he, K.row_of_row₂_eq_inr hr, congrArg Subtype.val hc⟩
    · rintro ⟨e, he, hr, hc⟩
      have hnc : ¬ K.sC (col e) := by rw [hc]; exact b.2
      refine ⟨⟨e, hnc⟩, he, ?_, Subtype.ext hc⟩
      have hns : ¬ K.sR (row e) := by rw [hr]; exact a.2
      rw [K.row₂_of_not_sR (e := ⟨e, hnc⟩) hns]
      exact congrArg Sum.inr (Subtype.ext hr)

/-- `S₂` has one extra column. -/
theorem card_V₂ (hbal : Fintype.card U = Fintype.card V) :
    Fintype.card K.V₂ = Fintype.card K.U₂ + 1 := by
  have h1 := Fintype.card_subtype_compl K.sR
  have h2 := Fintype.card_subtype_compl K.sC
  have h3 := Fintype.card_subtype_le K.sR
  have h4 := Fintype.card_subtype_le K.sC
  have h5 := K.card
  change Fintype.card {v // ¬ K.sC v} = Fintype.card {u // ¬ K.sR u} + 1
  omega

/-- **Full indecomposability splits across a tight cut**, for every occurrence
set `O`: `H[O]` is FI iff both closed factors `H₁[O]`, `H₂[O]` are FI. -/
theorem coreFI_cut_iff (hbal : Fintype.card U = Fintype.card V) (O : Finset E) :
    CoreFI row col O ↔ CoreFI K.row₁ K.col₁ (O.subtype fun e => K.sR (row e)) ∧
      CoreFI K.row₂ K.col₂ (O.subtype fun e => ¬ K.sC (col e)) := by
  rw [coreFI_iff_fiRel, coreFI_iff_fiRel, coreFI_iff_fiRel,
    fiRel_relabel (Equiv.sumCompl K.sR).symm (Equiv.sumCompl K.sC).symm (T := K.sumAdj O)
      (fun u v => by simp [sumAdj]),
    fiRel_congr (K.coreAdj₁_iff O), fiRel_congr (K.coreAdj₂_iff O)]
  exact fiRel_cut_iff (K.sumAdj_back O) K.card (K.card_V₂ hbal)

theorem subtype_univ_E₁ : ((univ : Finset E).subtype fun e => K.sR (row e)) = univ := by
  ext f; simp

theorem subtype_univ_E₂ : ((univ : Finset E).subtype fun e => ¬ K.sC (col e)) = univ := by
  ext f; simp

theorem subtype_erase_E₁ (e : E) (h : K.sR (row e)) :
    ((univ.erase e).subtype fun e => K.sR (row e)) = univ.erase ⟨e, h⟩ := by
  ext f; simp [Subtype.ext_iff]

theorem subtype_erase_E₂ (e : E) (h : ¬ K.sC (col e)) :
    ((univ.erase e).subtype fun e => ¬ K.sC (col e)) = univ.erase ⟨e, h⟩ := by
  ext f; simp [Subtype.ext_iff]

theorem subtype_erase_E₁_of_not (e : E) (h : ¬ K.sR (row e)) :
    ((univ.erase e).subtype fun e => K.sR (row e)) = univ := by
  ext f
  simp only [Finset.mem_subtype, Finset.mem_erase, Finset.mem_univ, and_true, iff_true]
  intro hf; exact h (hf ▸ f.2)

theorem subtype_erase_E₂_of_not (e : E) (h : K.sC (col e)) :
    ((univ.erase e).subtype fun e => ¬ K.sC (col e)) = univ := by
  ext f
  simp only [Finset.mem_subtype, Finset.mem_erase, Finset.mem_univ, and_true, iff_true]
  intro hf; exact f.2 (hf ▸ h)

/-- An FI core has FI closed factors. -/
theorem coreFI_factors (hbal : Fintype.card U = Fintype.card V) (hFI : CoreFI row col univ) :
    CoreFI K.row₁ K.col₁ univ ∧ CoreFI K.row₂ K.col₂ univ := by
  have := (K.coreFI_cut_iff hbal univ).1 hFI
  rwa [K.subtype_univ_E₁, K.subtype_univ_E₂] at this

/-- **Lavi (4.3).**  For a crossing occurrence `e`, whose label appears in both
factors, `H - e` is FI iff `H₁ - e` and `H₂ - e` are FI. -/
theorem lavi_eq_4_3 (hbal : Fintype.card U = Fintype.card V) {e : E} (hc : K.Crossing e) :
    CoreFI row col (univ.erase e) ↔
      CoreFI K.row₁ K.col₁ (univ.erase ⟨e, hc.1⟩) ∧ CoreFI K.row₂ K.col₂ (univ.erase ⟨e, hc.2⟩) := by
  rw [K.coreFI_cut_iff hbal, K.subtype_erase_E₁ e hc.1, K.subtype_erase_E₂ e hc.2]

/-- **Lemma 4.1, internal assertion (first shore).**  An internal occurrence of
`S₁` is removable in `H` exactly when it is removable in `H₁`. -/
theorem removable_internal₁ (hbal : Fintype.card U = Fintype.card V)
    (hFI : CoreFI row col univ) {e : E} (hs : K.sR (row e)) (hsc : K.sC (col e)) :
    CoreFI row col (univ.erase e) ↔ CoreFI K.row₁ K.col₁ (univ.erase ⟨e, hs⟩) := by
  rw [K.coreFI_cut_iff hbal, K.subtype_erase_E₁ e hs, K.subtype_erase_E₂_of_not e hsc]
  exact and_iff_left (K.coreFI_factors hbal hFI).2

/-- **Lemma 4.1, internal assertion (second shore).** -/
theorem removable_internal₂ (hbal : Fintype.card U = Fintype.card V)
    (hFI : CoreFI row col univ) {e : E} (hs : ¬ K.sR (row e)) (hsc : ¬ K.sC (col e)) :
    CoreFI row col (univ.erase e) ↔ CoreFI K.row₂ K.col₂ (univ.erase ⟨e, hsc⟩) := by
  rw [K.coreFI_cut_iff hbal, K.subtype_erase_E₁_of_not e hs, K.subtype_erase_E₂ e hsc]
  exact and_iff_right (K.coreFI_factors hbal hFI).1

end ShoreCut

end CoreCut

end LaviSection2
