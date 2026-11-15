import LaviSection2.LaviOccurrenceCore

/-!
# Lavi Lemma 2.5, Step 1: recovering the core of a terminal support

An ND support of order at least three is *terminal* if no contraction at a
degree-two row or column is ND.  This module proves the combinatorial half of
Lavi's Lemma 2.5: a terminal ND support is, up to relabelling rows and
columns, an expansion `D(H, L)` of an occurrence core `H` of minimum
occurrence degree at least three, in which the long occurrences `L` are the
row-column pairs of degree-two lines and the direct occurrences are the
hub-hub edges.

Proof (Lavi's Step 1).  Every line of an FI support of order at least two has
degree at least two.  By Lemma 2.4 and terminality, a degree-two column has
exactly one degree-two neighbour row and one hub neighbour row, and dually for
degree-two rows.  So the degree-two lines pair up into adjacent row-column
pairs, each the interior of a three-edge path between two hubs.  The hubs are
the core vertices; each such path is a long occurrence and each hub-hub edge a
direct occurrence.  Occurrences at a hub biject with its edges, so the minimum
occurrence degree is at least three.  A direct occurrence has no parallel
occurrence: distinct hub-hub edges have distinct endpoints, and a path
parallel to a hub-hub edge would create a four-cycle, excluded by Lemma 2.3.

Removability of the long occurrences and essentiality of the direct ones (the
rest of Lemma 2.5) are proved separately from this structure statement.
-/

namespace LaviSection2

open Finset

/-- Lavi: an ND support is terminal if no contraction at a degree-two line is ND. -/
def Terminal {n : ℕ} (D : Fin n → Fin n → Prop) : Prop :=
  (∀ r s c, r ≠ s → D r c → D s c → columnDegreeOn D c = 2 →
      ¬NearlyDecomposableOn (contractColumn D r s c)) ∧
  (∀ r c d, c ≠ d → D r c → D r d → rowDegreeOn D r = 2 →
      ¬NearlyDecomposableOn (contractRow D r c d))

section Degrees

variable {n : ℕ} {D : Fin n → Fin n → Prop}

theorem strictHallOn_of_fullyIndecomposable (h : FullyIndecomposable D) :
    StrictHallOn D :=
  (strictHallOn_fin_iff D).2 ((fullyIndecomposable_iff_strictHall D).1 h)

/-- Every row of an FI support of order at least two has degree at least two. -/
theorem two_le_rowDegreeOn (hn : 2 ≤ n) (hFI : FullyIndecomposable D) (x : Fin n) :
    2 ≤ rowDegreeOn D x := by
  have h := strictHallOn_of_fullyIndecomposable hFI {x} (Finset.singleton_nonempty x)
    (by rw [Finset.card_singleton, Fintype.card_fin]; omega)
  rw [Finset.card_singleton] at h
  unfold rowDegreeOn
  omega

/-- Every column of an FI support of order at least two has degree at least two. -/
theorem two_le_columnDegreeOn (hn : 2 ≤ n) (hFI : FullyIndecomposable D) (y : Fin n) :
    2 ≤ columnDegreeOn D y := by
  have hT : StrictHallOn (fun j i ↦ D i j) :=
    (strictHallOn_transpose_iff rfl D).2 (strictHallOn_of_fullyIndecomposable hFI)
  have h := hT {y} (Finset.singleton_nonempty y)
    (by rw [Finset.card_singleton, Fintype.card_fin]; omega)
  rw [Finset.card_singleton] at h
  unfold columnDegreeOn
  omega

theorem exists_pair_of_columnDegreeOn_eq_two {c : Fin n} (h : columnDegreeOn D c = 2) :
    ∃ r s, r ≠ s ∧ ∀ x, D x c ↔ x = r ∨ x = s := by
  classical
  unfold columnDegreeOn at h
  obtain ⟨r, s, hrs, hN⟩ := Finset.card_eq_two.1 h
  refine ⟨r, s, hrs, fun x => ?_⟩
  have hx : x ∈ rowNeighborsOn (fun j i ↦ D i j) {c} ↔ D x c := by
    simp [mem_rowNeighborsOn]
  rw [← hx, hN]
  simp

theorem exists_pair_of_rowDegreeOn_eq_two {r : Fin n} (h : rowDegreeOn D r = 2) :
    ∃ c d, c ≠ d ∧ ∀ y, D r y ↔ y = c ∨ y = d := by
  classical
  unfold rowDegreeOn at h
  obtain ⟨c, d, hcd, hN⟩ := Finset.card_eq_two.1 h
  refine ⟨c, d, hcd, fun y => ?_⟩
  have hy : y ∈ rowNeighborsOn D {r} ↔ D r y := by
    simp [mem_rowNeighborsOn]
  rw [← hy, hN]
  simp

/--
In a terminal ND support, a degree-two column has one degree-two neighbour
row and one hub neighbour row.
-/
theorem terminal_column_info (hn : 3 ≤ n) (hND : NearlyDecomposable D)
    (hterm : Terminal D) {c : Fin n} (hc : columnDegreeOn D c = 2) :
    ∃ r s, r ≠ s ∧ (∀ x, D x c ↔ x = r ∨ x = s) ∧
      rowDegreeOn D r = 2 ∧ 3 ≤ rowDegreeOn D s := by
  obtain ⟨r, s, hrs, hN⟩ := exists_pair_of_columnDegreeOn_eq_two hc
  have hrc : D r c := (hN r).2 (Or.inl rfl)
  have hsc : D s c := (hN s).2 (Or.inr rfl)
  have hr2 := two_le_rowDegreeOn (by omega) hND.1 r
  have hs2 := two_le_rowDegreeOn (by omega) hND.1 s
  have hnot := hterm.1 r s c hrs hrc hsc hc
  by_cases hr : rowDegreeOn D r = 2
  · by_cases hs : rowDegreeOn D s = 2
    · exact absurd (lavi_lemma_2_4_column hn D hND hrs hrc hsc hc (Or.inl ⟨hr, hs⟩)) hnot
    · exact ⟨r, s, hrs, hN, hr, by omega⟩
  · by_cases hs : rowDegreeOn D s = 2
    · exact ⟨s, r, hrs.symm, fun x => (hN x).trans or_comm, hs, by omega⟩
    · exact absurd (lavi_lemma_2_4_column hn D hND hrs hrc hsc hc
        (Or.inr ⟨by omega, by omega⟩)) hnot

/--
In a terminal ND support, a degree-two row has one degree-two neighbour
column and one hub neighbour column.
-/
theorem terminal_row_info (hn : 3 ≤ n) (hND : NearlyDecomposable D)
    (hterm : Terminal D) {r : Fin n} (hr : rowDegreeOn D r = 2) :
    ∃ c d, c ≠ d ∧ (∀ y, D r y ↔ y = c ∨ y = d) ∧
      columnDegreeOn D c = 2 ∧ 3 ≤ columnDegreeOn D d := by
  obtain ⟨c, d, hcd, hN⟩ := exists_pair_of_rowDegreeOn_eq_two hr
  have hrc : D r c := (hN c).2 (Or.inl rfl)
  have hrd : D r d := (hN d).2 (Or.inr rfl)
  have hc2 := two_le_columnDegreeOn (by omega) hND.1 c
  have hd2 := two_le_columnDegreeOn (by omega) hND.1 d
  have hnot := hterm.2 r c d hcd hrc hrd hr
  by_cases hc : columnDegreeOn D c = 2
  · by_cases hd : columnDegreeOn D d = 2
    · exact absurd (lavi_lemma_2_4_row hn D hND hcd hrc hrd hr (Or.inl ⟨hc, hd⟩)) hnot
    · exact ⟨c, d, hcd, hN, hc, by omega⟩
  · by_cases hd : columnDegreeOn D d = 2
    · exact ⟨d, c, hcd.symm, fun y => (hN y).trans or_comm, hd, by omega⟩
    · exact absurd (lavi_lemma_2_4_row hn D hND hcd hrc hrd hr
        (Or.inr ⟨by omega, by omega⟩)) hnot

end Degrees

section Structure

variable {n : ℕ} (D : Fin n → Fin n → Prop)

/-- Hub rows: rows of degree at least three. -/
abbrev HubRow := {x : Fin n // 3 ≤ rowDegreeOn D x}

/-- Hub columns: columns of degree at least three. -/
abbrev HubCol := {y : Fin n // 3 ≤ columnDegreeOn D y}

/-- Long occurrences: adjacent pairs of a degree-two row and a degree-two column. -/
noncomputable def longSet : Finset (Fin n × Fin n) := by
  classical
  exact Finset.univ.filter fun e =>
    rowDegreeOn D e.1 = 2 ∧ columnDegreeOn D e.2 = 2 ∧ D e.1 e.2

/-- Direct occurrences: hub-hub edges. -/
noncomputable def directSet : Finset (Fin n × Fin n) := by
  classical
  exact Finset.univ.filter fun e =>
    3 ≤ rowDegreeOn D e.1 ∧ 3 ≤ columnDegreeOn D e.2 ∧ D e.1 e.2

/-- All occurrences of the recovered core. -/
noncomputable def occSet : Finset (Fin n × Fin n) := by
  classical
  exact directSet D ∪ longSet D

variable {D}

theorem mem_longSet {e : Fin n × Fin n} :
    e ∈ longSet D ↔ rowDegreeOn D e.1 = 2 ∧ columnDegreeOn D e.2 = 2 ∧ D e.1 e.2 := by
  classical
  simp [longSet]

theorem mem_directSet {e : Fin n × Fin n} :
    e ∈ directSet D ↔ 3 ≤ rowDegreeOn D e.1 ∧ 3 ≤ columnDegreeOn D e.2 ∧ D e.1 e.2 := by
  classical
  simp [directSet]

theorem mem_occSet {e : Fin n × Fin n} :
    e ∈ occSet D ↔ e ∈ directSet D ∨ e ∈ longSet D := by
  classical
  simp [occSet]

theorem longSet_subset_occSet : longSet D ⊆ occSet D := fun _ h =>
  mem_occSet.2 (Or.inr h)

/--
Choice data for a terminal support.  For a degree-two row `x`, `rp x` is its
degree-two neighbour column and its hub column; for a degree-two column `y`,
`cp y` is its degree-two neighbour row and its hub row.  Off those lines the
second components are still hubs (junk values).
-/
structure TerminalData (D : Fin n → Fin n → Prop) where
  rp : Fin n → Fin n × Fin n
  cp : Fin n → Fin n × Fin n
  rp_hub : ∀ x, 3 ≤ columnDegreeOn D (rp x).2
  cp_hub : ∀ y, 3 ≤ rowDegreeOn D (cp y).2
  rp_spec : ∀ x, ¬3 ≤ rowDegreeOn D x →
    columnDegreeOn D (rp x).1 = 2 ∧ ∀ y, D x y ↔ y = (rp x).1 ∨ y = (rp x).2
  cp_spec : ∀ y, ¬3 ≤ columnDegreeOn D y →
    rowDegreeOn D (cp y).1 = 2 ∧ ∀ x, D x y ↔ x = (cp y).1 ∨ x = (cp y).2

namespace TerminalData

variable (T : TerminalData D)

/-- Core row of an occurrence: itself for a direct one, the hub row for a long one. -/
noncomputable def row (e : Fin n × Fin n) : HubRow D :=
  if h : 3 ≤ rowDegreeOn D e.1 then ⟨e.1, h⟩ else ⟨(T.cp e.2).2, T.cp_hub e.2⟩

/-- Core column of an occurrence. -/
noncomputable def col (e : Fin n × Fin n) : HubCol D :=
  if h : 3 ≤ columnDegreeOn D e.2 then ⟨e.2, h⟩ else ⟨(T.rp e.1).2, T.rp_hub e.1⟩

theorem row_of_hub {e : Fin n × Fin n} (h : 3 ≤ rowDegreeOn D e.1) :
    T.row e = ⟨e.1, h⟩ := dif_pos h

theorem col_of_hub {e : Fin n × Fin n} (h : 3 ≤ columnDegreeOn D e.2) :
    T.col e = ⟨e.2, h⟩ := dif_pos h

theorem row_val_of_long {e : Fin n × Fin n} (he : e ∈ longSet D) :
    (T.row e).1 = (T.cp e.2).2 := by
  have h := (mem_longSet.1 he).1
  rw [row, dif_neg (by omega)]

theorem col_val_of_long {e : Fin n × Fin n} (he : e ∈ longSet D) :
    (T.col e).1 = (T.rp e.1).2 := by
  have h := (mem_longSet.1 he).2.1
  rw [col, dif_neg (by omega)]

theorem rp_fst_of_long {e : Fin n × Fin n} (he : e ∈ longSet D) : (T.rp e.1).1 = e.2 := by
  obtain ⟨hr, hc, hD⟩ := mem_longSet.1 he
  rcases ((T.rp_spec e.1 (by omega)).2 e.2).1 hD with h | h
  · exact h.symm
  · exfalso
    have := T.rp_hub e.1
    rw [← h] at this
    omega

theorem cp_fst_of_long {e : Fin n × Fin n} (he : e ∈ longSet D) : (T.cp e.2).1 = e.1 := by
  obtain ⟨hr, hc, hD⟩ := mem_longSet.1 he
  rcases ((T.cp_spec e.2 (by omega)).2 e.1).1 hD with h | h
  · exact h.symm
  · exfalso
    have := T.cp_hub e.2
    rw [← h] at this
    omega

theorem mem_longSet_rp (hr2 : ∀ x, 2 ≤ rowDegreeOn D x) {x : Fin n} (hx : ¬3 ≤ rowDegreeOn D x) :
    (x, (T.rp x).1) ∈ longSet D := by
  have := hr2 x
  exact mem_longSet.2 ⟨(by omega : rowDegreeOn D x = 2), (T.rp_spec x hx).1,
    ((T.rp_spec x hx).2 _).2 (Or.inl rfl)⟩

theorem mem_longSet_cp (hc2 : ∀ y, 2 ≤ columnDegreeOn D y) {y : Fin n} (hy : ¬3 ≤ columnDegreeOn D y) :
    ((T.cp y).1, y) ∈ longSet D := by
  have := hc2 y
  exact mem_longSet.2 ⟨(T.cp_spec y hy).1, (by omega : columnDegreeOn D y = 2),
    ((T.cp_spec y hy).2 _).2 (Or.inl rfl)⟩

/-- Rows of the support as core rows plus private rows. -/
noncomputable def eR (hr2 : ∀ x, 2 ≤ rowDegreeOn D x) : Fin n ≃ HubRow D ⊕ longSet D where
  toFun x := if h : 3 ≤ rowDegreeOn D x then Sum.inl ⟨x, h⟩
    else Sum.inr ⟨(x, (T.rp x).1), T.mem_longSet_rp hr2 h⟩
  invFun := Sum.elim Subtype.val fun e => e.1.1
  left_inv x := by
    by_cases h : 3 ≤ rowDegreeOn D x
    · simp [h]
    · simp [h]
  right_inv := by
    rintro (u | e)
    · simp [u.2]
    · have hnh : ¬3 ≤ rowDegreeOn D e.1.1 := by
        have := (mem_longSet.1 e.2).1
        omega
      simp only [Sum.elim_inr, hnh, dif_neg, not_false_eq_true]
      congr 1
      apply Subtype.ext
      exact Prod.ext rfl (T.rp_fst_of_long e.2)

/-- Columns of the support as core columns plus private columns. -/
noncomputable def eC (hc2 : ∀ y, 2 ≤ columnDegreeOn D y) : Fin n ≃ HubCol D ⊕ longSet D where
  toFun y := if h : 3 ≤ columnDegreeOn D y then Sum.inl ⟨y, h⟩
    else Sum.inr ⟨((T.cp y).1, y), T.mem_longSet_cp hc2 h⟩
  invFun := Sum.elim Subtype.val fun e => e.1.2
  left_inv y := by
    by_cases h : 3 ≤ columnDegreeOn D y
    · simp [h]
    · simp [h]
  right_inv := by
    rintro (v | e)
    · simp [v.2]
    · have hnh : ¬3 ≤ columnDegreeOn D e.1.2 := by
        have := (mem_longSet.1 e.2).2.1
        omega
      simp only [Sum.elim_inr, hnh, dif_neg, not_false_eq_true]
      congr 1
      apply Subtype.ext
      exact Prod.ext (T.cp_fst_of_long e.2) rfl

theorem eR_hub (hr2 : ∀ x, 2 ≤ rowDegreeOn D x) {x : Fin n} (h : 3 ≤ rowDegreeOn D x) : T.eR hr2 x = Sum.inl ⟨x, h⟩ := by
  simp [eR, h]

theorem eR_low (hr2 : ∀ x, 2 ≤ rowDegreeOn D x) {x : Fin n} (h : ¬3 ≤ rowDegreeOn D x) :
    T.eR hr2 x = Sum.inr ⟨(x, (T.rp x).1), T.mem_longSet_rp hr2 h⟩ := by
  simp [eR, h]

theorem eC_hub (hc2 : ∀ y, 2 ≤ columnDegreeOn D y) {y : Fin n} (h : 3 ≤ columnDegreeOn D y) : T.eC hc2 y = Sum.inl ⟨y, h⟩ := by
  simp [eC, h]

theorem eC_low (hc2 : ∀ y, 2 ≤ columnDegreeOn D y) {y : Fin n} (h : ¬3 ≤ columnDegreeOn D y) :
    T.eC hc2 y = Sum.inr ⟨((T.cp y).1, y), T.mem_longSet_cp hc2 h⟩ := by
  simp [eC, h]

/-- The support is the expansion of the recovered core. -/
theorem iso (hr2 : ∀ x, 2 ≤ rowDegreeOn D x) (hc2 : ∀ y, 2 ≤ columnDegreeOn D y) (i j : Fin n) :
    D i j ↔ expAdj T.row T.col (occSet D) (longSet D) (T.eR hr2 i) (T.eC hc2 j) := by
  by_cases hi : 3 ≤ rowDegreeOn D i <;> by_cases hj : 3 ≤ columnDegreeOn D j
  · rw [T.eR_hub hr2 hi, T.eC_hub hc2 hj]
    show D i j ↔ ∃ e ∈ occSet D, e ∉ longSet D ∧ T.row e = ⟨i, hi⟩ ∧ T.col e = ⟨j, hj⟩
    constructor
    · intro h
      refine ⟨(i, j), mem_occSet.2 (Or.inl (mem_directSet.2 ⟨hi, hj, h⟩)), ?_,
        T.row_of_hub (e := (i, j)) hi, T.col_of_hub (e := (i, j)) hj⟩
      intro hL
      have h' : rowDegreeOn D i = 2 := (mem_longSet.1 hL).1
      omega
    · rintro ⟨e, heO, heL, hrow, hcol⟩
      have hdir : e ∈ directSet D := (mem_occSet.1 heO).resolve_right heL
      obtain ⟨h1, h2, hD⟩ := mem_directSet.1 hdir
      rw [T.row_of_hub h1] at hrow
      rw [T.col_of_hub h2] at hcol
      have hi' : e.1 = i := congrArg Subtype.val hrow
      have hj' : e.2 = j := congrArg Subtype.val hcol
      rw [← hi', ← hj']
      exact hD
  · rw [T.eR_hub hr2 hi, T.eC_low hc2 hj]
    show D i j ↔ T.row ((T.cp j).1, j) = ⟨i, hi⟩
    have hspec := T.cp_spec j hj
    rw [Subtype.ext_iff, T.row_val_of_long (T.mem_longSet_cp hc2 hj), hspec.2 i]
    constructor
    · rintro (h | h)
      · exfalso
        rw [h, hspec.1] at hi
        omega
      · exact h.symm
    · exact fun h => Or.inr h.symm
  · rw [T.eR_low hr2 hi, T.eC_hub hc2 hj]
    show D i j ↔ T.col (i, (T.rp i).1) = ⟨j, hj⟩
    have hspec := T.rp_spec i hi
    rw [Subtype.ext_iff, T.col_val_of_long (T.mem_longSet_rp hr2 hi), hspec.2 j]
    constructor
    · rintro (h | h)
      · exfalso
        rw [h, hspec.1] at hj
        omega
      · exact h.symm
    · exact fun h => Or.inr h.symm
  · rw [T.eR_low hr2 hi, T.eC_low hc2 hj]
    show D i j ↔ (⟨(i, (T.rp i).1), _⟩ : longSet D) = ⟨((T.cp j).1, j), _⟩
    rw [Subtype.ext_iff, Prod.ext_iff]
    have hri := T.rp_spec i hi
    have hcj := T.cp_spec j hj
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · rcases (hcj.2 i).1 h with h' | h'
        · exact h'
        · exfalso
          have := T.cp_hub j
          rw [← h'] at this
          exact hi this
      · rcases (hri.2 j).1 h with h' | h'
        · exact h'.symm
        · exfalso
          have := T.rp_hub i
          rw [← h'] at this
          exact hj this
    · rintro ⟨_, h2⟩
      exact (hri.2 j).2 (Or.inl h2.symm)

/-- Every hub row carries at least as many occurrences as its degree. -/
theorem three_le_rowOcc (hc2 : ∀ y, 2 ≤ columnDegreeOn D y) (u : HubRow D) :
    3 ≤ (rowOcc T.row (occSet D) u).card := by
  classical
  let f : Fin n → Fin n × Fin n := fun y =>
    if 3 ≤ columnDegreeOn D y then (u.1, y) else ((T.cp y).1, y)
  have hf2 : ∀ y, (f y).2 = y := by
    intro y
    by_cases hy : 3 ≤ columnDegreeOn D y <;> simp [f, hy]
  have hmaps : ∀ y ∈ rowNeighborsOn D {u.1}, f y ∈ rowOcc T.row (occSet D) u := by
    intro y hy
    have hD : D u.1 y := by simpa [mem_rowNeighborsOn] using hy
    rw [rowOcc, Finset.mem_filter]
    by_cases hyh : 3 ≤ columnDegreeOn D y
    · simp only [f, hyh, if_true]
      exact ⟨mem_occSet.2 (Or.inl (mem_directSet.2 ⟨u.2, hyh, hD⟩)),
        T.row_of_hub (e := (u.1, y)) u.2⟩
    · simp only [f, hyh, if_false]
      have hmem := T.mem_longSet_cp hc2 hyh
      refine ⟨longSet_subset_occSet hmem, Subtype.ext ?_⟩
      rw [T.row_val_of_long hmem]
      have hspec := T.cp_spec y hyh
      rcases (hspec.2 u.1).1 hD with h | h
      · exfalso
        have := u.2
        rw [h, hspec.1] at this
        omega
      · exact h.symm
  have hinj : Set.InjOn f (rowNeighborsOn D {u.1}) := by
    intro a _ b _ hab
    rw [← hf2 a, ← hf2 b, hab]
  have hle := Finset.card_le_card_of_injOn f hmaps hinj
  have hdeg := u.2
  unfold rowDegreeOn at hdeg
  omega

/-- Every hub column carries at least as many occurrences as its degree. -/
theorem three_le_colOcc (hr2 : ∀ x, 2 ≤ rowDegreeOn D x) (v : HubCol D) :
    3 ≤ (colOcc T.col (occSet D) v).card := by
  classical
  let f : Fin n → Fin n × Fin n := fun x =>
    if 3 ≤ rowDegreeOn D x then (x, v.1) else (x, (T.rp x).1)
  have hf1 : ∀ x, (f x).1 = x := by
    intro x
    by_cases hx : 3 ≤ rowDegreeOn D x <;> simp [f, hx]
  have hmaps : ∀ x ∈ rowNeighborsOn (fun j i ↦ D i j) {v.1},
      f x ∈ colOcc T.col (occSet D) v := by
    intro x hx
    have hD : D x v.1 := by simpa [mem_rowNeighborsOn] using hx
    rw [colOcc, Finset.mem_filter]
    by_cases hxh : 3 ≤ rowDegreeOn D x
    · simp only [f, hxh, if_true]
      exact ⟨mem_occSet.2 (Or.inl (mem_directSet.2 ⟨hxh, v.2, hD⟩)),
        T.col_of_hub (e := (x, v.1)) v.2⟩
    · simp only [f, hxh, if_false]
      have hmem := T.mem_longSet_rp hr2 hxh
      refine ⟨longSet_subset_occSet hmem, Subtype.ext ?_⟩
      rw [T.col_val_of_long hmem]
      have hspec := T.rp_spec x hxh
      rcases (hspec.2 v.1).1 hD with h | h
      · exfalso
        have := v.2
        rw [h, hspec.1] at this
        omega
      · exact h.symm
  have hinj : Set.InjOn f (rowNeighborsOn (fun j i ↦ D i j) {v.1}) := by
    intro a _ b _ hab
    rw [← hf1 a, ← hf1 b, hab]
  have hle := Finset.card_le_card_of_injOn f hmaps hinj
  have hdeg := v.2
  unfold columnDegreeOn at hdeg
  omega

/-- A direct occurrence has no parallel occurrence. -/
theorem no_parallel (hn : 3 ≤ n) (hND : NearlyDecomposable D)
    {d : Fin n × Fin n} (hd : d ∈ occSet D) (hdL : d ∉ longSet D)
    {e : Fin n × Fin n} (he : e ∈ occSet D) (hed : e ≠ d) :
    ¬(T.row e = T.row d ∧ T.col e = T.col d) := by
  rintro ⟨hrow, hcol⟩
  have hdir : d ∈ directSet D := (mem_occSet.1 hd).resolve_right hdL
  obtain ⟨hd1, hd2, hDd⟩ := mem_directSet.1 hdir
  rw [T.row_of_hub hd1] at hrow
  rw [T.col_of_hub hd2] at hcol
  rcases mem_occSet.1 he with heD | heL
  · obtain ⟨he1, he2, _⟩ := mem_directSet.1 heD
    rw [T.row_of_hub he1] at hrow
    rw [T.col_of_hub he2] at hcol
    exact hed (Prod.ext (congrArg Subtype.val hrow) (congrArg Subtype.val hcol))
  · have hr : (T.cp e.2).2 = d.1 := by
      rw [← T.row_val_of_long heL]
      exact congrArg Subtype.val hrow
    have hc : (T.rp e.1).2 = d.2 := by
      rw [← T.col_val_of_long heL]
      exact congrArg Subtype.val hcol
    obtain ⟨her, hec, hDe⟩ := mem_longSet.1 heL
    have hcs := T.cp_spec e.2 (by omega)
    have hrs := T.rp_spec e.1 (by omega)
    -- rows `d.1` and `e.1` share the columns `e.2` and `d.2`
    have h1 : D d.1 e.2 := by
      rw [← hr]
      exact (hcs.2 _).2 (Or.inr rfl)
    have h2 : D e.1 d.2 := by
      rw [← hc]
      exact (hrs.2 _).2 (Or.inr rfl)
    have hne : d.1 ≠ e.1 := by
      intro h
      rw [h] at hd1
      omega
    have := nearlyDecomposable_common_neighbor_unique hn hND hne h1 hDe hDd h2
    rw [this] at hd2
    omega

end TerminalData

end Structure

/--
Lavi Lemma 2.5, Step 1.  A terminal ND support of order at least three is,
up to relabelling rows and columns, an expansion `D(H, L)` of a balanced
occurrence core `H` of minimum occurrence degree at least three whose direct
occurrences have no parallel occurrence.
-/
theorem terminal_structure {n : ℕ} (hn : 3 ≤ n) (D : Fin n → Fin n → Prop)
    (hND : NearlyDecomposable D) (hterm : Terminal D) :
    ∃ (U V E : Type) (_ : Fintype U) (_ : Fintype V) (_ : Fintype E)
      (_ : DecidableEq U) (_ : DecidableEq V) (_ : DecidableEq E)
      (row : E → U) (col : E → V) (O L : Finset E),
      L ⊆ O ∧ Fintype.card U = Fintype.card V ∧ MinOccDegreeThree row col O ∧
      (∀ d ∈ O, d ∉ L → ∀ e ∈ O, e ≠ d → ¬(row e = row d ∧ col e = col d)) ∧
      ∃ (eR : Fin n ≃ U ⊕ L) (eC : Fin n ≃ V ⊕ L),
        ∀ i j, D i j ↔ expAdj row col O L (eR i) (eC j) := by
  have hr2 : ∀ x, 2 ≤ rowDegreeOn D x := two_le_rowDegreeOn (by omega) hND.1
  have hc2 : ∀ y, 2 ≤ columnDegreeOn D y := two_le_columnDegreeOn (by omega) hND.1
  have x0 : Fin n := ⟨0, by omega⟩
  -- A hub row and a hub column exist.
  obtain ⟨u0, hu0⟩ : ∃ u, 3 ≤ rowDegreeOn D u := by
    by_cases h : 3 ≤ rowDegreeOn D x0
    · exact ⟨x0, h⟩
    · obtain ⟨c, _, _, _, hc, _⟩ :=
        terminal_row_info hn hND hterm (show rowDegreeOn D x0 = 2 by
          have := hr2 x0
          omega)
      obtain ⟨_, s, _, _, _, hs⟩ := terminal_column_info hn hND hterm hc
      exact ⟨s, hs⟩
  obtain ⟨v0, hv0⟩ : ∃ v, 3 ≤ columnDegreeOn D v := by
    by_cases h : 3 ≤ columnDegreeOn D x0
    · exact ⟨x0, h⟩
    · obtain ⟨r, _, _, _, hr, _⟩ :=
        terminal_column_info hn hND hterm (show columnDegreeOn D x0 = 2 by
          have := hc2 x0
          omega)
      obtain ⟨_, d, _, _, _, hd⟩ := terminal_row_info hn hND hterm hr
      exact ⟨d, hd⟩
  have hrowData : ∀ x, ∃ p : Fin n × Fin n, 3 ≤ columnDegreeOn D p.2 ∧
      (¬3 ≤ rowDegreeOn D x →
        columnDegreeOn D p.1 = 2 ∧ ∀ y, D x y ↔ y = p.1 ∨ y = p.2) := by
    intro x
    by_cases hx : 3 ≤ rowDegreeOn D x
    · exact ⟨(x, v0), hv0, fun h => absurd hx h⟩
    · obtain ⟨c, d, _, hN, hc, hd⟩ := terminal_row_info (r := x) hn hND hterm (by
        have := hr2 x
        omega)
      exact ⟨(c, d), hd, fun _ => ⟨hc, hN⟩⟩
  have hcolData : ∀ y, ∃ p : Fin n × Fin n, 3 ≤ rowDegreeOn D p.2 ∧
      (¬3 ≤ columnDegreeOn D y →
        rowDegreeOn D p.1 = 2 ∧ ∀ x, D x y ↔ x = p.1 ∨ x = p.2) := by
    intro y
    by_cases hy : 3 ≤ columnDegreeOn D y
    · exact ⟨(y, u0), hu0, fun h => absurd hy h⟩
    · obtain ⟨r, s, _, hN, hr, hs⟩ := terminal_column_info (c := y) hn hND hterm (by
        have := hc2 y
        omega)
      exact ⟨(r, s), hs, fun _ => ⟨hr, hN⟩⟩
  choose rp hrp using hrowData
  choose cp hcp using hcolData
  let T : TerminalData D :=
    { rp := rp, cp := cp
      rp_hub := fun x => (hrp x).1, cp_hub := fun y => (hcp y).1
      rp_spec := fun x => (hrp x).2, cp_spec := fun y => (hcp y).2 }
  refine ⟨HubRow D, HubCol D, Fin n × Fin n, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, T.row, T.col, occSet D, longSet D,
    longSet_subset_occSet, ?_, ⟨T.three_le_rowOcc hc2, T.three_le_colOcc hr2⟩,
    fun d hd hdL e he hed => T.no_parallel hn hND hd hdL he hed,
    T.eR hr2, T.eC hc2, T.iso hr2 hc2⟩
  have h1 := Fintype.card_congr (T.eR hr2)
  have h2 := Fintype.card_congr (T.eC hc2)
  rw [Fintype.card_sum] at h1 h2
  omega

end LaviSection2
