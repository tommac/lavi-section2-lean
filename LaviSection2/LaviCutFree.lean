import LaviSection2.LaviOneStar
import LaviSection2.LaviTightCutAccounting
import LaviSection2.LaviTightCutOrientation

/-!
# Lavi Lemma 6.1: cut-free cores

A tight shore `(R, C)` of a core (rows `R`, columns `C`) is *nontrivial* if
both it and its complement have at least three vertices.  A core is
*cut-free* if it has no nontrivial tight shore.

**Lemma 6.1.**  Let `K` be a balanced FI core of order `k ≥ 3` with no
nontrivial tight cut.  Then every vertex has at least three distinct
neighbors, and every occurrence is removable.

The proof follows the manuscript.  A nonempty row set `S` with `|S| ≤ k - 2`
and `|N(S)| = |S| + 1` would make `S ∪ N(S)` a nontrivial tight shore, so
strict Hall holds with surplus two; one deletion removes at most one neighbor.
For `|S| = k - 1`, every column keeps a neighbor in `S`.  Tightness of a shore
with no outgoing (or no incoming) occurrences and the right size difference
is `isTightCut_of_forward` (`_of_backward`), the converse of Lavi's
orientation argument.
-/

set_option linter.unusedSectionVars false

namespace LaviSection2

open Finset

section CutFree

variable {U V E : Type*} [Fintype U] [Fintype V] [Fintype E]
  [DecidableEq U] [DecidableEq V] [DecidableEq E] (row : E → U) (col : E → V)

/-- The shore `(R, C)` is tight. -/
def IsTightShore (R : Finset U) (C : Finset V) : Prop := IsTightCut row col (· ∈ R) (· ∈ C)

/-- A nontrivial tight shore: both sides have at least three vertices. -/
def IsNontrivialShore (R : Finset U) (C : Finset V) : Prop :=
  IsTightShore row col R C ∧ 3 ≤ R.card + C.card ∧ 3 ≤ Rᶜ.card + Cᶜ.card

/-- A core with no nontrivial tight cut. -/
def CutFree : Prop := ∀ R C, ¬ IsNontrivialShore row col R C

variable {row col}

/-- A shore with no outgoing occurrences and one extra column is tight. -/
theorem isTightCut_of_forward (pR : U → Prop) (pC : V → Prop) [DecidablePred pR]
    [DecidablePred pC] (hfw : ∀ e, pR (row e) → pC (col e))
    (hc : (univ.filter pC).card = (univ.filter pR).card + 1) : IsTightCut row col pR pC := by
  intro M
  have h1 := crossing_count pR pC M
  have h2 := tight_split pR pC M
  have hout : (univ.filter fun u => pR u ∧ ¬ pC (col (M.1 u))).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro u - ⟨hr, hc'⟩
    exact hc' (hfw (M.1 u) (by rw [M.2.1]; exact hr))
  omega

/-- A shore with no incoming occurrences and one extra row is tight. -/
theorem isTightCut_of_backward (pR : U → Prop) (pC : V → Prop) [DecidablePred pR]
    [DecidablePred pC] (hbw : ∀ e, pC (col e) → pR (row e))
    (hc : (univ.filter pR).card = (univ.filter pC).card + 1) : IsTightCut row col pR pC := by
  intro M
  have h1 := crossing_count pR pC M
  have h2 := tight_split pR pC M
  have hin : (univ.filter fun u => ¬ pR u ∧ pC (col (M.1 u))).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro u - ⟨hr, hc'⟩
    exact hr (by have := hbw (M.1 u) hc'; rwa [M.2.1] at this)
  omega

/-- Tightness is symmetric under complementing the shore. -/
theorem isTightShore_compl {R : Finset U} {C : Finset V} :
    IsTightShore row col Rᶜ Cᶜ ↔ IsTightShore row col R C := by
  unfold IsTightShore IsTightCut
  refine forall_congr' fun M => ?_
  rw [show (univ.filter fun u => ¬ (u ∈ Rᶜ ↔ col (M.1 u) ∈ Cᶜ)) =
      univ.filter fun u => ¬ (u ∈ R ↔ col (M.1 u) ∈ C) by
    ext u; simp only [mem_filter, mem_univ, true_and, mem_compl]; tauto]

theorem isNontrivialShore_compl {R : Finset U} {C : Finset V} :
    IsNontrivialShore row col Rᶜ Cᶜ ↔ IsNontrivialShore row col R C := by
  unfold IsNontrivialShore
  rw [isTightShore_compl, compl_compl, compl_compl]
  tauto

theorem card_filter_mem {α : Type*} [Fintype α] [DecidableEq α] (s : Finset α) :
    (univ.filter (· ∈ s)).card = s.card := by
  congr 1; ext a; simp

theorem image_rowSet_eq (u : U) : (rowSet row u).image col = rowNeighborsOn (coreAdj row col univ) {u} := by
  ext w; simp [mem_rowNeighborsOn, coreAdj, rowSet]

theorem image_colSet_eq (w : V) :
    ((univ : Finset E).filter fun e => col e = w).image row =
      rowNeighborsOn (fun j i => coreAdj row col univ i j) {w} := by
  ext u; simp [mem_rowNeighborsOn, coreAdj, and_comm]

variable (hbal : Fintype.card U = Fintype.card V) (hFI : CoreFI row col univ)
  (hcut : CutFree row col)

include hbal hFI hcut in
/-- In a cut-free FI core, small row sets have Hall surplus two. -/
theorem nbr_surplus_two {R : Finset U} (hR : R.Nonempty) (hRc : R.card + 2 ≤ Fintype.card U) :
    R.card + 2 ≤ (rowNeighborsOn (coreAdj row col univ) R).card := by
  have hH := hFI.1 R hR (by omega)
  by_contra h
  have heq : (rowNeighborsOn (coreAdj row col univ) R).card = R.card + 1 := by
    omega
  refine hcut R (rowNeighborsOn (coreAdj row col univ) R) ⟨?_, ?_, ?_⟩
  · refine isTightCut_of_forward _ _ (fun e he => ?_) ?_
    · exact mem_rowNeighborsOn.2 ⟨row e, he, e, mem_univ _, rfl, rfl⟩
    · rw [card_filter_mem, card_filter_mem, heq]
  · have := hR.card_pos; omega
  · rw [card_compl, card_compl, heq]; omega

include hbal hFI hcut in
/-- In a cut-free FI core, small column sets have Hall surplus two. -/
theorem nbrT_surplus_two {C : Finset V} (hC : C.Nonempty) (hCc : C.card + 2 ≤ Fintype.card V) :
    C.card + 2 ≤ (rowNeighborsOn (fun j i => coreAdj row col univ i j) C).card := by
  have hT := (strictHallOn_transpose_iff hbal (coreAdj row col univ)).2 hFI.1
  have hH := hT C hC (by omega)
  by_contra h
  have heq : (rowNeighborsOn (fun j i => coreAdj row col univ i j) C).card = C.card + 1 := by
    omega
  refine hcut (rowNeighborsOn (fun j i => coreAdj row col univ i j) C) C ⟨?_, ?_, ?_⟩
  · refine isTightCut_of_backward _ _ (fun e he => ?_) ?_
    · exact mem_rowNeighborsOn.2 ⟨col e, he, e, mem_univ _, rfl, rfl⟩
    · rw [card_filter_mem, card_filter_mem, heq]
  · have := hC.card_pos; omega
  · rw [card_compl, card_compl, heq]; omega

include hbal hFI hcut in
/-- **Lemma 6.1, degrees.**  Every row has at least three distinct neighbors. -/
theorem three_le_rowNbrs (hk : 3 ≤ Fintype.card U) (u : U) :
    3 ≤ ((rowSet row u).image col).card := by
  rw [image_rowSet_eq]
  have := nbr_surplus_two hbal hFI hcut (singleton_nonempty u) (by rw [card_singleton]; omega)
  rwa [card_singleton] at this

include hbal hFI hcut in
/-- **Lemma 6.1, degrees.**  Every column has at least three distinct neighbors. -/
theorem three_le_colNbrs (hk : 3 ≤ Fintype.card U) (w : V) :
    3 ≤ (((univ : Finset E).filter fun e => col e = w).image row).card := by
  rw [image_colSet_eq]
  have := nbrT_surplus_two hbal hFI hcut (singleton_nonempty w) (by rw [card_singleton]; omega)
  rwa [card_singleton] at this

include hbal hFI hcut in
/-- **Lemma 6.1, removability.**  Every occurrence of a cut-free FI core of
order at least three is removable. -/
theorem coreFI_erase_of_cutFree (hk : 3 ≤ Fintype.card U) (e : E) :
    CoreFI row col (univ.erase e) := by
  refine ⟨fun R hR hRc => ?_, fun u => ?_⟩
  · have hsub : (rowNeighborsOn (coreAdj row col univ) R).erase (col e) ⊆
        rowNeighborsOn (coreAdj row col (univ.erase e)) R := by
      intro w hw
      obtain ⟨hwe, hw⟩ := Finset.mem_erase.1 hw
      obtain ⟨i, hi, f, -, hfr, hfc⟩ := mem_rowNeighborsOn.1 hw
      refine mem_rowNeighborsOn.2 ⟨i, hi, f, Finset.mem_erase.2 ⟨?_, mem_univ _⟩, hfr, hfc⟩
      rintro rfl; exact hwe hfc.symm
    have hcard := (Finset.pred_card_le_card_erase).trans (card_le_card hsub)
    rcases Nat.lt_or_ge (R.card + 1) (Fintype.card U) with hsmall | hlarge
    · have := nbr_surplus_two hbal hFI hcut hR (by omega)
      omega
    · -- `R` misses exactly one row; every column keeps a neighbor in `R`
      have hR1 : Rᶜ.card = 1 := by rw [card_compl]; omega
      have huniv : rowNeighborsOn (coreAdj row col (univ.erase e)) R = univ := by
        rw [eq_univ_iff_forall]
        intro w
        set T := ((univ : Finset E).filter fun f => col f = w).image row with hTdef
        have hT : 3 ≤ T.card := three_le_colNbrs hbal hFI hcut hk w
        have hout : (T.filter fun u => u ∉ R).card ≤ 1 := by
          rw [← hR1]
          exact card_le_card fun u hu => mem_compl.2 (mem_filter.1 hu).2
        have hin : 1 < (T.filter fun u => u ∈ R).card := by
          have := Finset.card_filter_add_card_filter_not (s := T) (fun u => u ∈ R)
          omega
        obtain ⟨u₁, u₂, hu₁, hu₂, hne⟩ := Finset.one_lt_card_iff.1 hin
        obtain ⟨hu₁T, hu₁R⟩ := mem_filter.1 hu₁
        obtain ⟨hu₂T, hu₂R⟩ := mem_filter.1 hu₂
        obtain ⟨f₁, hf₁, hf₁r⟩ := Finset.mem_image.1 hu₁T
        obtain ⟨f₂, hf₂, hf₂r⟩ := Finset.mem_image.1 hu₂T
        have hf₁c : col f₁ = w := (mem_filter.1 hf₁).2
        have hf₂c : col f₂ = w := (mem_filter.1 hf₂).2
        by_cases h1 : f₁ = e
        · have h2 : f₂ ≠ e := by
            rintro rfl; exact hne (by rw [← hf₁r, ← hf₂r, h1])
          exact mem_rowNeighborsOn.2 ⟨u₂, hu₂R, f₂, Finset.mem_erase.2 ⟨h2, mem_univ _⟩, hf₂r,
            hf₂c⟩
        · exact mem_rowNeighborsOn.2 ⟨u₁, hu₁R, f₁, Finset.mem_erase.2 ⟨h1, mem_univ _⟩, hf₁r,
            hf₁c⟩
      rw [huniv, card_univ, ← hbal]
      exact hRc
  · have h3 := three_le_rowNbrs hbal hFI hcut hk u
    have : 1 < (rowSet row u).card := by
      have := (h3.trans Finset.card_image_le); omega
    obtain ⟨f, hf, hfe⟩ := Finset.exists_mem_ne this e
    exact ⟨f, Finset.mem_erase.2 ⟨hfe, mem_univ _⟩, (Finset.mem_filter.1 hf).2⟩

include hbal hFI hcut in
/-- **Lavi Lemma 6.1 (a cut-free core).**  A balanced FI core of order
`k ≥ 3` with no nontrivial tight cut has at least three distinct neighbors at
every vertex, and every occurrence is removable. -/
theorem lavi_lemma_6_1 (hk : 3 ≤ Fintype.card U) :
    (∀ u, 3 ≤ ((rowSet row u).image col).card) ∧
      (∀ w, 3 ≤ (((univ : Finset E).filter fun e => col e = w).image row).card) ∧
      removableSet row col univ = univ := by
  refine ⟨three_le_rowNbrs hbal hFI hcut hk, three_le_colNbrs hbal hFI hcut hk, ?_⟩
  rw [eq_univ_iff_forall]
  intro e
  exact (mem_removableSet row col).2 ⟨mem_univ _, coreFI_erase_of_cutFree hbal hFI hcut hk e⟩

end CutFree

end LaviSection2
