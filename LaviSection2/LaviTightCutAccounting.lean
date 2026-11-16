import LaviSection2.LaviTightCutFI
import LaviSection2.LaviExpansionEntropy

/-!
# Lavi Section 4: expansion accounting across a tight cut, (4.4)–(4.5)

Choose one closed factor as the leaf.  Its *internal* removable occurrences
(those not at its marker) form `L_B`, so `B = D(H_leaf, L_B)` leaves all
marker-incident occurrences direct; the other factor is expanded canonically,
`R = D_can(H_other)`.  Let `N` be the crossing occurrences that are essential in
the leaf but removable in the other factor.  Then

* (4.4) `L(H) = L_B ⊔ (L(H_other) \ N)`, and
* (4.5) `G_{H,L(H)} = G_B + G_R - ∑_{e ∈ N} δ(x_e)`,

where all three gaps are evaluated at the same parent marginal.  Lavi allows
either factor as the leaf; we prove both choices: `lavi_eq_4_4`, `lavi_eq_4_5`
(leaf `H₁`, marker column) and `lavi_eq_4_4'`, `lavi_eq_4_5'` (leaf `H₂`,
marker row).
-/

set_option linter.unusedSectionVars false

namespace LaviSection2

open Finset Real

theorem mem_map_subtype_iff {E : Type*} {p : E → Prop} {s : Finset (Subtype p)} {e : E} :
    e ∈ s.map (Function.Embedding.subtype p) ↔ ∃ h : p e, (⟨e, h⟩ : Subtype p) ∈ s := by
  rw [Finset.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ⟨a.2, ha⟩
  · rintro ⟨h, hs⟩; exact ⟨_, hs, rfl⟩

section Accounting

variable {U V E : Type*} [Fintype U] [Fintype V] [Fintype E]
  [DecidableEq U] [DecidableEq V] [DecidableEq E]
  {row : E → U} {col : E → V} (K : ShoreCut row col)

namespace ShoreCut

/-- The removable occurrences of `H₁`, as parent labels. -/
noncomputable def remLabels₁ : Finset E :=
  (removableSet K.row₁ K.col₁ univ).map (Function.Embedding.subtype _)

/-- The removable occurrences of `H₂`, as parent labels. -/
noncomputable def remLabels₂ : Finset E :=
  (removableSet K.row₂ K.col₂ univ).map (Function.Embedding.subtype _)

/-- Leaf `H₁`: its removable occurrences away from the marker column. -/
noncomputable def leafLong₁ : Finset K.E₁ :=
  (removableSet K.row₁ K.col₁ univ).filter fun e => K.sC (col e.1)

/-- Leaf `H₂`: its removable occurrences away from the marker row. -/
noncomputable def leafLong₂ : Finset K.E₂ :=
  (removableSet K.row₂ K.col₂ univ).filter fun e => ¬ K.sR (row e.1)

/-- Leaf `H₁`: crossing occurrences essential in `H₁` but removable in `H₂`. -/
noncomputable def essential₁ : Finset E := (K.remLabels₂ \ K.remLabels₁).filter K.Crossing

/-- Leaf `H₂`: crossing occurrences essential in `H₂` but removable in `H₁`. -/
noncomputable def essential₂ : Finset E := (K.remLabels₁ \ K.remLabels₂).filter K.Crossing

theorem mem_remLabels₁ {e : E} :
    e ∈ K.remLabels₁ ↔ ∃ h : K.sR (row e), CoreFI K.row₁ K.col₁ (univ.erase ⟨e, h⟩) := by
  rw [remLabels₁, mem_map_subtype_iff]
  simp only [mem_removableSet, mem_univ, true_and]

theorem mem_remLabels₂ {e : E} :
    e ∈ K.remLabels₂ ↔ ∃ h : ¬ K.sC (col e), CoreFI K.row₂ K.col₂ (univ.erase ⟨e, h⟩) := by
  rw [remLabels₂, mem_map_subtype_iff]
  simp only [mem_removableSet, mem_univ, true_and]

theorem mem_leafLong₁ {e : E} :
    e ∈ K.leafLong₁.map (Function.Embedding.subtype _) ↔
      ∃ h : K.sR (row e), K.sC (col e) ∧ CoreFI K.row₁ K.col₁ (univ.erase ⟨e, h⟩) := by
  rw [mem_map_subtype_iff]
  simp only [leafLong₁, mem_filter, mem_removableSet, mem_univ, true_and]
  exact exists_congr fun _ => and_comm

theorem mem_leafLong₂ {e : E} :
    e ∈ K.leafLong₂.map (Function.Embedding.subtype _) ↔
      ∃ h : ¬ K.sC (col e), ¬ K.sR (row e) ∧ CoreFI K.row₂ K.col₂ (univ.erase ⟨e, h⟩) := by
  rw [mem_map_subtype_iff]
  simp only [leafLong₂, mem_filter, mem_removableSet, mem_univ, true_and]
  exact exists_congr fun _ => and_comm

variable (hbal : Fintype.card U = Fintype.card V) (hFI : CoreFI row col univ)

include hbal hFI in
/-- **Lavi (4.4), leaf `H₁`:** `L(H) = L_B ⊔ (L(H₂) \ N)`. -/
theorem lavi_eq_4_4 :
    removableSet row col univ =
        K.leafLong₁.map (Function.Embedding.subtype _) ∪ (K.remLabels₂ \ K.essential₁) ∧
      Disjoint (K.leafLong₁.map (Function.Embedding.subtype _)) (K.remLabels₂ \ K.essential₁) := by
  refine ⟨?_, ?_⟩
  · ext e
    rw [mem_removableSet, mem_union, mem_sdiff, essential₁, mem_filter, mem_sdiff,
      K.mem_leafLong₁]
    simp only [mem_univ, true_and]
    by_cases hs : K.sR (row e) <;> by_cases hsc : K.sC (col e)
    · rw [K.removable_internal₁ hbal hFI hs hsc]
      have h2 : e ∉ K.remLabels₂ := fun h => by
        obtain ⟨h', -⟩ := K.mem_remLabels₂.1 h; exact h' hsc
      simp only [h2, false_and, or_false]
      exact ⟨fun h => ⟨hs, hsc, h⟩, fun ⟨_, _, h⟩ => h⟩
    · have hc : K.Crossing e := ⟨hs, hsc⟩
      rw [K.lavi_eq_4_3 hbal hc]
      simp only [hsc, false_and, exists_false, false_or, hc, and_true, not_and, not_not]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨K.mem_remLabels₂.2 ⟨hsc, h2⟩, fun _ => K.mem_remLabels₁.2 ⟨hs, h1⟩⟩
      · rintro ⟨h2, h1⟩
        obtain ⟨_, h1⟩ := K.mem_remLabels₁.1 (h1 h2)
        obtain ⟨_, h2⟩ := K.mem_remLabels₂.1 h2
        exact ⟨h1, h2⟩
    · exact absurd (K.back e hsc) hs
    · rw [K.removable_internal₂ hbal hFI hs hsc]
      have hnc : ¬ K.Crossing e := fun h => hs h.1
      rw [or_iff_right (fun ⟨h, _⟩ => hs h)]
      simp only [hnc, and_false, not_false_eq_true, and_true]
      constructor
      · intro h; exact K.mem_remLabels₂.2 ⟨hsc, h⟩
      · intro h; obtain ⟨_, h⟩ := K.mem_remLabels₂.1 h; exact h
  · rw [Finset.disjoint_left]
    intro e h1 h2
    obtain ⟨_, hsc, -⟩ := K.mem_leafLong₁.1 h1
    obtain ⟨hnc, -⟩ := K.mem_remLabels₂.1 (mem_sdiff.1 h2).1
    exact hnc hsc

include hbal hFI in
/-- **Lavi (4.4), leaf `H₂`:** `L(H) = L_B ⊔ (L(H₁) \ N)`. -/
theorem lavi_eq_4_4' :
    removableSet row col univ =
        K.leafLong₂.map (Function.Embedding.subtype _) ∪ (K.remLabels₁ \ K.essential₂) ∧
      Disjoint (K.leafLong₂.map (Function.Embedding.subtype _)) (K.remLabels₁ \ K.essential₂) := by
  refine ⟨?_, ?_⟩
  · ext e
    rw [mem_removableSet, mem_union, mem_sdiff, essential₂, mem_filter, mem_sdiff,
      K.mem_leafLong₂]
    simp only [mem_univ, true_and]
    by_cases hs : K.sR (row e) <;> by_cases hsc : K.sC (col e)
    · rw [K.removable_internal₁ hbal hFI hs hsc]
      have hnc : ¬ K.Crossing e := fun h => h.2 hsc
      rw [or_iff_right (fun ⟨h, _⟩ => h hsc)]
      simp only [hnc, and_false, not_false_eq_true, and_true]
      constructor
      · intro h; exact K.mem_remLabels₁.2 ⟨hs, h⟩
      · intro h; obtain ⟨_, h⟩ := K.mem_remLabels₁.1 h; exact h
    · have hc : K.Crossing e := ⟨hs, hsc⟩
      rw [K.lavi_eq_4_3 hbal hc]
      simp only [hs, not_true_eq_false, false_and, exists_false, false_or, hc, and_true,
        not_and, not_not]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨K.mem_remLabels₁.2 ⟨hs, h1⟩, fun _ => K.mem_remLabels₂.2 ⟨hsc, h2⟩⟩
      · rintro ⟨h1, h2⟩
        obtain ⟨_, h2⟩ := K.mem_remLabels₂.1 (h2 h1)
        obtain ⟨_, h1⟩ := K.mem_remLabels₁.1 h1
        exact ⟨h1, h2⟩
    · exact absurd (K.back e hsc) hs
    · rw [K.removable_internal₂ hbal hFI hs hsc]
      have h1 : e ∉ K.remLabels₁ := fun h => by
        obtain ⟨h', -⟩ := K.mem_remLabels₁.1 h; exact hs h'
      simp only [h1, false_and, or_false]
      exact ⟨fun h => ⟨hsc, hs, h⟩, fun ⟨_, _, h⟩ => h⟩
  · rw [Finset.disjoint_left]
    intro e h2 h1
    obtain ⟨_, hs, -⟩ := K.mem_leafLong₂.1 h2
    obtain ⟨hr, -⟩ := K.mem_remLabels₁.1 (mem_sdiff.1 h1).1
    exact hs hr

/-- Sums over factor labels are sums over parent labels. -/
theorem sum_map_subtype {p : E → Prop} (s : Finset (Subtype p)) (f : E → ℝ) :
    ∑ e ∈ s, f e.1 = ∑ e ∈ s.map (Function.Embedding.subtype p), f e :=
  (Finset.sum_map s (Function.Embedding.subtype p) f).symm

theorem cast_order :
    ((Fintype.card U : ℝ) - 1) =
      ((Fintype.card K.U₁ : ℝ) - 1) + ((Fintype.card (Unit ⊕ K.U₂) : ℝ) - 1) := by
  have h := K.lavi_eq_4_1
  have : ((Fintype.card U : ℝ) + 1) =
      (Fintype.card K.U₁ : ℝ) + (Fintype.card (Unit ⊕ K.U₂) : ℝ) := by exact_mod_cast h
  linarith

include hbal hFI in
/-- **Lavi (4.5), leaf `H₁`:**
`G_{H,L(H)} = G_B + G_R - ∑_{e ∈ N} δ(x_e)`, with `B = D(H₁, L_B)` and
`R = D_can(H₂)`, all at the same parent marginal. -/
theorem lavi_eq_4_5 {x : E → ℝ} (hlaw : ∃ μ, IsCoreLaw row col x μ) :
    normalizedGap row col (removableSet row col univ) x =
      normalizedGap K.row₁ K.col₁ K.leafLong₁ (K.flow₁ x) +
        normalizedGap K.row₂ K.col₂ (removableSet K.row₂ K.col₂ univ) (K.flow₂ x) -
          ∑ e ∈ K.essential₁, subdivCharge (x e) := by
  obtain ⟨h44, hdisj⟩ := K.lavi_eq_4_4 hbal hFI
  have hsub : K.essential₁ ⊆ K.remLabels₂ := fun e he =>
    (mem_sdiff.1 (mem_filter.1 he).1).1
  have hB : ∑ ℓ ∈ K.leafLong₁, subdivCharge (K.flow₁ x ℓ) =
      ∑ e ∈ K.leafLong₁.map (Function.Embedding.subtype _), subdivCharge (x e) :=
    sum_map_subtype _ (fun e => subdivCharge (x e))
  have hR : ∑ ℓ ∈ removableSet K.row₂ K.col₂ univ, subdivCharge (K.flow₂ x ℓ) =
      ∑ e ∈ K.remLabels₂, subdivCharge (x e) :=
    sum_map_subtype _ (fun e => subdivCharge (x e))
  have hsplit := Finset.sum_sdiff hsub (f := fun e => subdivCharge (x e))
  unfold normalizedGap
  rw [K.lavi_lemma_4_1 hlaw, h44, Finset.sum_union hdisj, hB, hR, K.cast_order]
  linarith

include hbal hFI in
/-- **Lavi (4.5), leaf `H₂`:**
`G_{H,L(H)} = G_B + G_R - ∑_{e ∈ N} δ(x_e)`, with `B = D(H₂, L_B)` and
`R = D_can(H₁)`. -/
theorem lavi_eq_4_5' {x : E → ℝ} (hlaw : ∃ μ, IsCoreLaw row col x μ) :
    normalizedGap row col (removableSet row col univ) x =
      normalizedGap K.row₂ K.col₂ K.leafLong₂ (K.flow₂ x) +
        normalizedGap K.row₁ K.col₁ (removableSet K.row₁ K.col₁ univ) (K.flow₁ x) -
          ∑ e ∈ K.essential₂, subdivCharge (x e) := by
  obtain ⟨h44, hdisj⟩ := K.lavi_eq_4_4' hbal hFI
  have hsub : K.essential₂ ⊆ K.remLabels₁ := fun e he =>
    (mem_sdiff.1 (mem_filter.1 he).1).1
  have hB : ∑ ℓ ∈ K.leafLong₂, subdivCharge (K.flow₂ x ℓ) =
      ∑ e ∈ K.leafLong₂.map (Function.Embedding.subtype _), subdivCharge (x e) :=
    sum_map_subtype _ (fun e => subdivCharge (x e))
  have hR : ∑ ℓ ∈ removableSet K.row₁ K.col₁ univ, subdivCharge (K.flow₁ x ℓ) =
      ∑ e ∈ K.remLabels₁, subdivCharge (x e) :=
    sum_map_subtype _ (fun e => subdivCharge (x e))
  have hsplit := Finset.sum_sdiff hsub (f := fun e => subdivCharge (x e))
  unfold normalizedGap
  rw [K.lavi_lemma_4_1 hlaw, h44, Finset.sum_union hdisj, hB, hR, K.cast_order]
  linarith

end ShoreCut

end Accounting

end LaviSection2
