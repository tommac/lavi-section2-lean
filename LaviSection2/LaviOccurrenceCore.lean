import LaviSection2.LaviContractionND
import Mathlib.Data.Finset.Sum

/-!
# Occurrence cores and their expansions (Lavi §2.3)

An *occurrence core* is a balanced bipartite multigraph: core rows `U`, core
columns `V`, and a finite set `O` of labelled occurrences `e`, each joining
`row e` to `col e`.  Parallel occurrences count separately, but full
indecomposability (`CoreFI`) is strict Hall on *distinct* neighbors, plus at
least one occurrence at every row (which is the order-one convention).

For `L ⊆ O`, the expansion `D(H, L)` replaces every occurrence `e ∈ L` by a
private three-edge path `row e - c_e - r_e - col e`; occurrences outside `L`
stay direct.  Its rows are `U ⊕ L` (core rows and private rows `r_e`) and its
columns are `V ⊕ L` (core columns and private columns `c_e`).

Main results here:

* `strictHallOn_expAdj`: if the core satisfies strict Hall, is balanced, and
  every core column carries at least two occurrences, then every expansion
  satisfies strict Hall;
* `coreFI_of_expAdj`: conversely, strict Hall of an expansion implies that
  the core is fully indecomposable (suppression of private paths);
* `strictHallOn_relabel_iff`, `nearlyDecomposableOn_relabel_iff`: these
  predicates are invariant under relabelling rows and columns.
-/

namespace LaviSection2

open Finset

section Relabel

variable {α β α' β' : Type*} [Fintype α] [Fintype β] [Fintype α'] [Fintype β']
  [DecidableEq α] [DecidableEq β] [DecidableEq α'] [DecidableEq β']

theorem rowNeighborsOn_relabel (eα : α ≃ α') (eβ : β ≃ β')
    {S : α → β → Prop} {T : α' → β' → Prop} (h : ∀ a b, S a b ↔ T (eα a) (eβ b))
    (R : Finset α) :
    rowNeighborsOn T (R.map eα.toEmbedding) = (rowNeighborsOn S R).map eβ.toEmbedding := by
  classical
  ext y
  rw [Finset.mem_map_equiv, mem_rowNeighborsOn, mem_rowNeighborsOn]
  constructor
  · rintro ⟨x, hx, hT⟩
    rw [Finset.mem_map_equiv] at hx
    refine ⟨eα.symm x, hx, ?_⟩
    rw [h]
    simpa using hT
  · rintro ⟨a, ha, hS⟩
    refine ⟨eα a, by simpa using ha, ?_⟩
    rw [h] at hS
    simpa using hS

theorem strictHallOn_of_relabel (eα : α ≃ α') (eβ : β ≃ β')
    {S : α → β → Prop} {T : α' → β' → Prop} (h : ∀ a b, S a b ↔ T (eα a) (eβ b))
    (hT : StrictHallOn T) : StrictHallOn S := by
  intro R hR hRp
  have hcard : Fintype.card α = Fintype.card α' := Fintype.card_congr eα
  have := hT (R.map eα.toEmbedding) (hR.map) (by rw [Finset.card_map, ← hcard]; exact hRp)
  rwa [rowNeighborsOn_relabel eα eβ h, Finset.card_map, Finset.card_map] at this

theorem strictHallOn_relabel_iff (eα : α ≃ α') (eβ : β ≃ β')
    {S : α → β → Prop} {T : α' → β' → Prop} (h : ∀ a b, S a b ↔ T (eα a) (eβ b)) :
    StrictHallOn S ↔ StrictHallOn T := by
  refine ⟨fun hS => strictHallOn_of_relabel eα.symm eβ.symm (fun a b => ?_) hS,
    strictHallOn_of_relabel eα eβ h⟩
  rw [h]
  simp

theorem nearlyDecomposableOn_relabel_iff (eα : α ≃ α') (eβ : β ≃ β')
    {S : α → β → Prop} {T : α' → β' → Prop} (h : ∀ a b, S a b ↔ T (eα a) (eβ b)) :
    NearlyDecomposableOn S ↔ NearlyDecomposableOn T := by
  have hdel : ∀ a b x y, deleteEdgeOn S a b x y ↔
      deleteEdgeOn T (eα a) (eβ b) (eα x) (eβ y) := by
    intro a b x y
    simp only [deleteEdgeOn, h, EmbeddingLike.apply_eq_iff_eq]
  constructor
  · rintro ⟨hS, hmin⟩
    refine ⟨(strictHallOn_relabel_iff eα eβ h).1 hS, fun a' b' hab hdelT => ?_⟩
    have hab' : S (eα.symm a') (eβ.symm b') := by rw [h]; simpa using hab
    apply hmin _ _ hab'
    refine (strictHallOn_relabel_iff eα eβ (hdel _ _)).2 ?_
    simpa using hdelT
  · rintro ⟨hT, hmin⟩
    refine ⟨(strictHallOn_relabel_iff eα eβ h).2 hT, fun a b hab hdelS => ?_⟩
    exact hmin _ _ ((h a b).1 hab) ((strictHallOn_relabel_iff eα eβ (hdel a b)).1 hdelS)

end Relabel

section Core

variable {U V E : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
  [DecidableEq E]
variable (row : E → U) (col : E → V)

/-- Distinct-neighbor adjacency of the occurrence set `O`. -/
def coreAdj (O : Finset E) (u : U) (v : V) : Prop :=
  ∃ e ∈ O, row e = u ∧ col e = v

/-- A fully indecomposable occurrence core. -/
def CoreFI (O : Finset E) : Prop :=
  StrictHallOn (coreAdj row col O) ∧ ∀ u, ∃ e ∈ O, row e = u

/-- Occurrences at a core row. -/
def rowOcc (O : Finset E) (u : U) : Finset E := O.filter fun e => row e = u

/-- Occurrences at a core column. -/
def colOcc (O : Finset E) (v : V) : Finset E := O.filter fun e => col e = v

/-- Minimum occurrence degree at least three. -/
def MinOccDegreeThree (O : Finset E) : Prop :=
  (∀ u, 3 ≤ (rowOcc row O u).card) ∧ ∀ v, 3 ≤ (colOcc col O v).card

/-- The removable occurrences `L(H)`: deleting one leaves an FI core. -/
noncomputable def removableSet (O : Finset E) : Finset E := by
  classical
  exact O.filter fun e => CoreFI row col (O.erase e)

theorem mem_removableSet {O : Finset E} {e : E} :
    e ∈ removableSet row col O ↔ e ∈ O ∧ CoreFI row col (O.erase e) := by
  classical
  simp [removableSet]

/--
The expansion `D(H, L)`: rows `U ⊕ L`, columns `V ⊕ L`.  An occurrence
outside `L` is a direct edge; an occurrence `e ∈ L` becomes the private path
`row e - c_e - r_e - col e`.
-/
def expAdj (O L : Finset E) : U ⊕ L → V ⊕ L → Prop
  | Sum.inl u, Sum.inl v => ∃ e ∈ O, e ∉ L ∧ row e = u ∧ col e = v
  | Sum.inl u, Sum.inr e => row e.1 = u
  | Sum.inr e, Sum.inr e' => e = e'
  | Sum.inr e, Sum.inl v => col e.1 = v

/-- The canonical expansion `D_can(H) = D(H, L(H))`. -/
noncomputable def canonicalAdj (O : Finset E) :
    U ⊕ (removableSet row col O) → V ⊕ (removableSet row col O) → Prop :=
  expAdj row col O (removableSet row col O)

variable {row col}

/-- The expansion of the transposed core is the transposed expansion. -/
theorem expAdj_transpose (O L : Finset E) (i : U ⊕ L) (j : V ⊕ L) :
    expAdj col row O L j i ↔ expAdj row col O L i j := by
  rcases i with u | e <;> rcases j with v | e'
  · simp only [expAdj]
    constructor <;> rintro ⟨e, he, hL, h1, h2⟩ <;> exact ⟨e, he, hL, h2, h1⟩
  · exact Iff.rfl
  · exact Iff.rfl
  · exact eq_comm

section Bounds

variable [Fintype E] (O L : Finset E)

/-- Core rows of a set of expansion rows reach, through private columns, all
long occurrences starting there, plus the private rows themselves. -/
theorem toRight_rowNeighborsOn_expAdj_superset (X : Finset (U ⊕ L)) :
    ((Finset.univ : Finset L).filter fun e => row e.1 ∈ X.toLeft) ∪ X.toRight ⊆
      (rowNeighborsOn (expAdj row col O L) X).toRight := by
  classical
  intro e he
  rw [Finset.mem_toRight, mem_rowNeighborsOn]
  rcases Finset.mem_union.1 he with h | h
  · rw [Finset.mem_filter, Finset.mem_toLeft] at h
    exact ⟨Sum.inl (row e.1), h.2, rfl⟩
  · rw [Finset.mem_toRight] at h
    exact ⟨Sum.inr e, h, rfl⟩

/--
The basic counting bound: the expansion neighborhood of `X` has at least
`|N_H(X_U)| + |X_L|` elements.
-/
theorem card_rowNeighborsOn_expAdj_ge (hL : L ⊆ O) (X : Finset (U ⊕ L)) :
    (rowNeighborsOn (coreAdj row col O) X.toLeft).card + X.toRight.card ≤
      (rowNeighborsOn (expAdj row col O L) X).card := by
  classical
  have h1 := toRight_rowNeighborsOn_expAdj_superset (row := row) (col := col) O L X
  set N := rowNeighborsOn (expAdj row col O L) X
  set Lu : Finset L := (Finset.univ : Finset L).filter fun e => row e.1 ∈ X.toLeft
  set Dl := Lu \ X.toRight
  have h2 : rowNeighborsOn (coreAdj row col O) X.toLeft ⊆
      N.toLeft ∪ Dl.image fun e => col e.1 := by
    intro v hv
    obtain ⟨u, hu, e, he, hrow, hcol⟩ := mem_rowNeighborsOn.1 hv
    by_cases heL : e ∈ L
    · by_cases hX : (⟨e, heL⟩ : L) ∈ X.toRight
      · refine Finset.mem_union_left _ ?_
        rw [Finset.mem_toLeft, mem_rowNeighborsOn]
        exact ⟨Sum.inr ⟨e, heL⟩, Finset.mem_toRight.1 hX, hcol⟩
      · refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨⟨e, heL⟩, ?_, hcol⟩)
        refine Finset.mem_sdiff.2 ⟨?_, hX⟩
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hrow ▸ hu⟩
    · refine Finset.mem_union_left _ ?_
      rw [Finset.mem_toLeft, mem_rowNeighborsOn]
      exact ⟨Sum.inl u, Finset.mem_toLeft.1 hu, e, he, heL, hrow, hcol⟩
  have hc2 := (Finset.card_le_card h2).trans (Finset.card_union_le _ _)
  have hc3 := Finset.card_image_le (s := Dl) (f := fun e => col e.1)
  have hc1 := Finset.card_le_card h1
  have hunion : (Lu ∪ X.toRight).card = Dl.card + X.toRight.card :=
    (Finset.card_sdiff_add_card _ _).symm
  have hN : N.toLeft.card + N.toRight.card = N.card := Finset.card_toLeft_add_card_toRight
  omega

/--
Strict Hall passes from a core to every expansion, provided the core is
balanced and every core column carries at least two occurrences.  (The
excluded case is the order-one core with a single, long occurrence.)
-/
theorem strictHallOn_expAdj (hbal : Fintype.card U = Fintype.card V)
    (hL : L ⊆ O) (hO : StrictHallOn (coreAdj row col O))
    (hcol2 : ∀ v, 2 ≤ (colOcc col O v).card) :
    StrictHallOn (expAdj row col O L) := by
  classical
  intro X hX hXp
  have hcardX : X.toLeft.card + X.toRight.card = X.card :=
    Finset.card_toLeft_add_card_toRight
  have hbound := card_rowNeighborsOn_expAdj_ge (row := row) (col := col) O L hL X
  have hcardUL : Fintype.card (U ⊕ L) = Fintype.card U + L.card := by
    rw [Fintype.card_sum, Fintype.card_coe]
  have h1 := toRight_rowNeighborsOn_expAdj_superset (row := row) (col := col) O L X
  set N := rowNeighborsOn (expAdj row col O L) X with hNdef
  have hN : N.toLeft.card + N.toRight.card = N.card := Finset.card_toLeft_add_card_toRight
  by_cases hXu0 : X.toLeft = ∅
  · -- Only private rows.
    rw [hXu0, Finset.card_empty, zero_add] at hcardX
    obtain ⟨e, he⟩ : X.toRight.Nonempty := by
      rw [← Finset.card_pos, hcardX]
      exact Finset.card_pos.2 hX
    have hv : (col e.1) ∈ N.toLeft := by
      rw [Finset.mem_toLeft, hNdef, mem_rowNeighborsOn]
      exact ⟨Sum.inr e, Finset.mem_toRight.1 he, rfl⟩
    have hL1 : 0 < N.toLeft.card := Finset.card_pos.2 ⟨_, hv⟩
    have hR1 : X.toRight.card ≤ N.toRight.card :=
      Finset.card_le_card (Finset.subset_union_right.trans h1)
    omega
  by_cases hXuU : X.toLeft = Finset.univ
  · -- All core rows: count the columns that are missed.
    have hLu : ((Finset.univ : Finset L).filter fun e => row e.1 ∈ X.toLeft) =
        Finset.univ := by
      ext e
      simp [hXuU]
    rw [hLu, Finset.union_eq_left.2 (Finset.subset_univ _)] at h1
    have hRall : N.toRight.card = L.card := by
      have := Finset.card_le_card h1
      have := Finset.card_le_univ N.toRight
      rw [Finset.card_univ, Fintype.card_coe] at *
      omega
    rw [hXuU, Finset.card_univ] at hcardX
    set M := (N.toLeft)ᶜ
    set T : Finset E := (X.toRight)ᶜ.map (Function.Embedding.subtype _)
    have hTcard : T.card = L.card - X.toRight.card := by
      rw [Finset.card_map, Finset.card_compl, Fintype.card_coe]
    have hsub : M.biUnion (colOcc col O) ⊆ T := by
      intro e he
      obtain ⟨v, hvM, hev⟩ := Finset.mem_biUnion.1 he
      rw [colOcc, Finset.mem_filter] at hev
      rw [Finset.mem_compl, Finset.mem_toLeft, hNdef, mem_rowNeighborsOn] at hvM
      by_cases heL : e ∈ L
      · refine Finset.mem_map.2 ⟨⟨e, heL⟩, ?_, rfl⟩
        rw [Finset.mem_compl, Finset.mem_toRight]
        intro hX'
        exact hvM ⟨Sum.inr ⟨e, heL⟩, hX', hev.2⟩
      · exfalso
        refine hvM ⟨Sum.inl (row e), ?_, e, hev.1, heL, rfl, hev.2⟩
        rw [← Finset.mem_toLeft, hXuU]
        exact Finset.mem_univ _
    have hdisj : ∀ v ∈ M, ∀ w ∈ M, v ≠ w → Disjoint (colOcc col O v) (colOcc col O w) := by
      intro v _ w _ hvw
      rw [Finset.disjoint_left]
      intro e hv hw
      rw [colOcc, Finset.mem_filter] at hv hw
      exact hvw (hv.2.symm.trans hw.2)
    have hsum : M.card * 2 ≤ T.card := by
      calc M.card * 2 = ∑ _v ∈ M, 2 := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ ∑ v ∈ M, (colOcc col O v).card := Finset.sum_le_sum fun v _ => hcol2 v
        _ = (M.biUnion (colOcc col O)).card := (Finset.card_biUnion hdisj).symm
        _ ≤ T.card := Finset.card_le_card hsub
    have hMcard : N.toLeft.card = Fintype.card V - M.card := by
      rw [Finset.card_compl]
      have := Finset.card_le_univ N.toLeft
      omega
    have hMle : M.card ≤ Fintype.card V := Finset.card_le_univ M
    have hNleft : N.toLeft.card + M.card = Fintype.card V := by
      rw [Finset.card_compl]
      have := Finset.card_le_univ N.toLeft
      omega
    have hXr : X.toRight.card < L.card := by omega
    omega
  · -- A nonempty proper set of core rows.
    have hne : X.toLeft.Nonempty := Finset.nonempty_iff_ne_empty.2 hXu0
    have hprop : X.toLeft.card < Fintype.card U := by
      rw [← Finset.card_univ]
      exact Finset.card_lt_card (Finset.ssubset_univ_iff.2 hXuU)
    have := hO _ hne hprop
    omega

/--
Suppression of private paths: strict Hall of an expansion gives strict Hall
of its core.
-/
theorem strictHallOn_core_of_expAdj (hL : L ⊆ O)
    (hD : StrictHallOn (expAdj row col O L)) :
    StrictHallOn (coreAdj row col O) := by
  classical
  intro Xu hXu hXup
  set Lu : Finset L := (Finset.univ : Finset L).filter fun e => row e.1 ∈ Xu
  set X : Finset (U ⊕ L) := Xu.disjSum Lu
  have hXcard : X.card = Xu.card + Lu.card := Finset.card_disjSum _ _
  have hXne : X.Nonempty := by
    obtain ⟨u, hu⟩ := hXu
    exact ⟨Sum.inl u, Finset.inl_mem_disjSum.2 hu⟩
  have hLu : Lu.card ≤ L.card := by
    have := Finset.card_le_univ Lu
    rwa [Fintype.card_coe] at this
  have hXp : X.card < Fintype.card (U ⊕ L) := by
    rw [Fintype.card_sum, Fintype.card_coe]
    omega
  have h := hD X hXne hXp
  set N := rowNeighborsOn (expAdj row col O L) X
  have hR : N.toRight ⊆ Lu := by
    intro e he
    rw [Finset.mem_toRight, mem_rowNeighborsOn] at he
    obtain ⟨x, hx, hxe⟩ := he
    rcases x with u | e'
    · rw [Finset.inl_mem_disjSum] at hx
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (show row e.1 = u from hxe) ▸ hx⟩
    · rw [Finset.inr_mem_disjSum] at hx
      exact (show e' = e from hxe) ▸ hx
  have hLft : N.toLeft ⊆ rowNeighborsOn (coreAdj row col O) Xu := by
    intro v hv
    rw [Finset.mem_toLeft, mem_rowNeighborsOn] at hv
    obtain ⟨x, hx, hxv⟩ := hv
    rcases x with u | e
    · rw [Finset.inl_mem_disjSum] at hx
      obtain ⟨e, he, _, hrow, hcol⟩ := hxv
      exact mem_rowNeighborsOn.2 ⟨u, hx, e, he, hrow, hcol⟩
    · rw [Finset.inr_mem_disjSum, Finset.mem_filter] at hx
      exact mem_rowNeighborsOn.2 ⟨row e.1, hx.2, e.1, hL e.2, rfl, hxv⟩
  have hNc : N.toLeft.card + N.toRight.card = N.card := Finset.card_toLeft_add_card_toRight
  have := Finset.card_le_card hR
  have := Finset.card_le_card hLft
  omega

/-- Strict Hall of an expansion of order at least two gives a fully
indecomposable core. -/
theorem coreFI_of_expAdj (hL : L ⊆ O) (h2 : 2 ≤ Fintype.card (U ⊕ L))
    (hD : StrictHallOn (expAdj row col O L)) : CoreFI row col O := by
  classical
  refine ⟨strictHallOn_core_of_expAdj O L hL hD, fun u => ?_⟩
  have h := hD {Sum.inl u} (Finset.singleton_nonempty _) (by
    rw [Finset.card_singleton]
    omega)
  rw [Finset.card_singleton] at h
  obtain ⟨y, hy⟩ := Finset.card_pos.1 (by omega : 0 < (rowNeighborsOn (expAdj row col O L)
    {Sum.inl u}).card)
  obtain ⟨x, hx, hxy⟩ := mem_rowNeighborsOn.1 hy
  rw [Finset.mem_singleton.1 hx] at hxy
  rcases y with v | e
  · obtain ⟨e, he, _, hrow, _⟩ := hxy
    exact ⟨e, he, hrow⟩
  · exact ⟨e.1, hL e.2, hxy⟩

end Bounds

end Core

end LaviSection2
