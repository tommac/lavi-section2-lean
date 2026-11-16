import LaviSection2.LaviTightCut

/-!
# Lavi Section 4: tight cuts are oriented

Lavi defines a tight cut of a core as a partition of its vertices into two
shores such that every perfect matching uses exactly one occurrence across
it.  He then observes: if one shore has `a` rows and `b` columns, every
matching has (edges leaving its rows) − (edges entering its columns) `= a − b`,
so tightness forces `a − b = ±1`; and since every occurrence lies in some
matching, all crossing occurrences point the same way.

We prove this (`tightCut_orientation`) and conclude that one of the two shores
carries a `ShoreCut` (`exists_shoreCut_of_tight`), which is the form used in
the rest of Section 4.  The covering hypothesis holds, for instance, whenever
some feasible flow is positive on every occurrence
(`covered_of_positive_flow`).
-/

set_option linter.unusedSectionVars false

namespace LaviSection2

open Finset

section Orientation

variable {U V E : Type*} [Fintype U] [Fintype V] [Fintype E]
  [DecidableEq U] [DecidableEq V] [DecidableEq E]
  {row : E → U} {col : E → V}

/-- Lavi's tight cut: the shore `(pR, pC)` is crossed by exactly one occurrence
of every labelled perfect matching. -/
def IsTightCut (row : E → U) (col : E → V) (pR : U → Prop) (pC : V → Prop)
    [DecidablePred pR] [DecidablePred pC] : Prop :=
  ∀ M : LMatch row col, (univ.filter fun u => ¬ (pR u ↔ pC (col (M.1 u)))).card = 1

/-- Every occurrence lies in a labelled perfect matching if some feasible flow
is positive everywhere. -/
theorem covered_of_positive_flow {x : E → ℝ} {μ : LMatch row col → ℝ}
    (hμ : IsCoreLaw row col x μ) (hpos : ∀ e, 0 < x e) :
    ∀ e, ∃ M : LMatch row col, M.1 (row e) = e := by
  intro e
  by_contra h
  push Not at h
  have : x e = 0 := by
    rw [← hμ.2.2]
    unfold coreMarginal
    rw [Finset.filter_false_of_mem fun M _ => h M, Finset.sum_empty]
  exact absurd this (ne_of_gt (hpos e))

theorem card_filter_split {α : Type*} [Fintype α] (P Q : α → Prop) [DecidablePred P]
    [DecidablePred Q] :
    (univ.filter P).card =
      (univ.filter fun a => P a ∧ Q a).card + (univ.filter fun a => P a ∧ ¬ Q a).card := by
  rw [← Finset.card_filter_add_card_filter_not (s := univ.filter P) Q,
    Finset.filter_filter, Finset.filter_filter]

variable (pR : U → Prop) (pC : V → Prop) [DecidablePred pR] [DecidablePred pC]

/-- The crossing count of one matching: out minus in equals `a − b`. -/
theorem crossing_count (M : LMatch row col) :
    (univ.filter pR).card + (univ.filter fun u => ¬ pR u ∧ pC (col (M.1 u))).card =
      (univ.filter pC).card + (univ.filter fun u => pR u ∧ ¬ pC (col (M.1 u))).card := by
  have hb : (univ.filter pC).card = (univ.filter fun u => pC (col (M.1 u))).card := by
    symm
    refine Finset.card_bij (fun u _ => col (M.1 u)) ?_ ?_ ?_
    · intro u hu; exact mem_filter.2 ⟨mem_univ _, (mem_filter.1 hu).2⟩
    · intro u _ u' _ h; exact M.2.2.1 h
    · intro v hv
      obtain ⟨u, hu⟩ := M.2.2.2 v
      have hu : col (M.1 u) = v := hu
      exact ⟨u, mem_filter.2 ⟨mem_univ _, by rw [hu]; exact (mem_filter.1 hv).2⟩, hu⟩
  have ha := card_filter_split pR (fun u => pC (col (M.1 u)))
  have hb' := card_filter_split (fun u => pC (col (M.1 u))) pR
  have hsame : (univ.filter fun u => pR u ∧ pC (col (M.1 u))).card =
      (univ.filter fun u => pC (col (M.1 u)) ∧ pR u).card := by
    congr 1; ext u; simp [and_comm]
  have hin : (univ.filter fun u => pC (col (M.1 u)) ∧ ¬ pR u).card =
      (univ.filter fun u => ¬ pR u ∧ pC (col (M.1 u))).card := by
    congr 1; ext u; simp [and_comm]
  omega

/-- The crossing occurrences of a matching split into outgoing and incoming. -/
theorem tight_split (M : LMatch row col) :
    (univ.filter fun u => ¬ (pR u ↔ pC (col (M.1 u)))).card =
      (univ.filter fun u => pR u ∧ ¬ pC (col (M.1 u))).card +
        (univ.filter fun u => ¬ pR u ∧ pC (col (M.1 u))).card := by
  rw [card_filter_split (fun u => ¬ (pR u ↔ pC (col (M.1 u)))) pR]
  congr 2
  · ext u; simp only [mem_filter, mem_univ, true_and]; tauto
  · ext u; simp only [mem_filter, mem_univ, true_and]; tauto

/-- **Tight cuts are oriented.**  If every occurrence lies in a perfect
matching, a tight cut has one extra row on one shore and every crossing
occurrence leaves that shore's rows. -/
theorem tightCut_orientation (htight : IsTightCut row col pR pC)
    (hcov : ∀ e, ∃ M : LMatch row col, M.1 (row e) = e) (M₀ : LMatch row col) :
    ((∀ e, pC (col e) → pR (row e)) ∧ (univ.filter pR).card = (univ.filter pC).card + 1) ∨
      ((∀ e, pR (row e) → pC (col e)) ∧ (univ.filter pC).card = (univ.filter pR).card + 1) := by
  have hM : ∀ M : LMatch row col,
      (univ.filter pR).card + (univ.filter fun u => ¬ pR u ∧ pC (col (M.1 u))).card =
        (univ.filter pC).card + (univ.filter fun u => pR u ∧ ¬ pC (col (M.1 u))).card ∧
      (univ.filter fun u => pR u ∧ ¬ pC (col (M.1 u))).card +
        (univ.filter fun u => ¬ pR u ∧ pC (col (M.1 u))).card = 1 := fun M =>
    ⟨crossing_count pR pC M, (tight_split pR pC M).symm.trans (htight M)⟩
  obtain ⟨h0a, h0b⟩ := hM M₀
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (show (univ.filter fun u =>
      pR u ∧ ¬ pC (col (M₀.1 u))).card ≤ 1 by omega) with hout | hout
  · -- the extra column is on this shore: no occurrence leaves its rows
    right
    have hab : (univ.filter pC).card = (univ.filter pR).card + 1 := by omega
    refine ⟨fun e hr => ?_, hab⟩
    by_contra hc
    obtain ⟨M, hMe⟩ := hcov e
    obtain ⟨h1, h2⟩ := hM M
    have : 0 < (univ.filter fun u => pR u ∧ ¬ pC (col (M.1 u))).card :=
      card_pos.2 ⟨row e, mem_filter.2 ⟨mem_univ _, hr, by rw [hMe]; exact hc⟩⟩
    omega
  · left
    have hab : (univ.filter pR).card = (univ.filter pC).card + 1 := by omega
    refine ⟨fun e hc => ?_, hab⟩
    by_contra hr
    obtain ⟨M, hMe⟩ := hcov e
    obtain ⟨h1, h2⟩ := hM M
    have : 0 < (univ.filter fun u => ¬ pR u ∧ pC (col (M.1 u))).card :=
      card_pos.2 ⟨row e, mem_filter.2 ⟨mem_univ _, hr, by rw [hMe]; exact hc⟩⟩
    omega

/-- **One shore of every tight cut is an oriented `ShoreCut`**, with `S₁` the
shore that has the extra row (in a balanced core). -/
theorem exists_shoreCut_of_tight (hbal : Fintype.card U = Fintype.card V)
    (htight : IsTightCut row col pR pC)
    (hcov : ∀ e, ∃ M : LMatch row col, M.1 (row e) = e) (M₀ : LMatch row col) :
    ∃ K : ShoreCut row col,
      (K.sR = pR ∧ K.sC = pC) ∨ (K.sR = fun u => ¬ pR u) ∧ (K.sC = fun v => ¬ pC v) := by
  rcases tightCut_orientation pR pC htight hcov M₀ with ⟨hback, hcard⟩ | ⟨hback, hcard⟩
  · refine ⟨⟨pR, pC, hback, ?_⟩, Or.inl ⟨rfl, rfl⟩⟩
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact hcard
  · refine ⟨⟨fun u => ¬ pR u, fun v => ¬ pC v, fun e hc hr => hc (hback e hr), ?_⟩,
      Or.inr ⟨rfl, rfl⟩⟩
    rw [← Fintype.card_subtype, ← Fintype.card_subtype] at hcard
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl]
    have h1 := Fintype.card_subtype_le pR
    have h2 := Fintype.card_subtype_le pC
    omega

end Orientation

end LaviSection2
