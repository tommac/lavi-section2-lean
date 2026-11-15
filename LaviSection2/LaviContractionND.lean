import LaviSection2.LaviContraction

/-!
# Lavi Lemma 2.4: the two contraction mechanisms

Let `c` be a degree-two column of a nearly decomposable support of order at
least three, with neighboring rows `r` and `s`.  If both rows have degree two,
or both have degree at least three, then contracting at `c` gives a nearly
decomposable support.  The transposed statement holds for a degree-two row.

The key tool is `strictHallOn_of_contractColumn`: the reverse of contraction
(splitting the merged row back into `r - c - s`) preserves strict Hall,
provided `r` and `s` each keep a neighbor other than `c`.  Both edge cases of
Lemma 2.4 then follow from one argument: an edge deletion in the contraction
that kept strict Hall would expand to an edge deletion of the original
support that keeps strict Hall, contradicting near decomposability.  For an
edge at the merged row this uses Lemma 2.3 (no common neighbor other than
`c`), so the deleted edge has a unique preimage.  This replaces the
perfect-matching and tight-set arguments of the manuscript.
-/

namespace LaviSection2

open Function

section Expansion

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- A row set of the original support that avoids `s`, seen in `Drop s`. -/
noncomputable def dropRows (s : α) (R : Finset α) : Finset (Drop s) :=
  (R.erase s).subtype fun x => x ≠ s

theorem mem_dropRows {s : α} {R : Finset α} {i : Drop s} :
    i ∈ dropRows s R ↔ i.1 ∈ R := by
  simp [dropRows, Finset.mem_subtype, i.2]

theorem liftContractedRows_dropRows (s : α) (R : Finset α) :
    liftContractedRows (dropRows s R) = R.erase s := by
  ext i
  rw [mem_liftContractedRows]
  constructor
  · rintro ⟨hi, hmem⟩
    exact Finset.mem_erase.2 ⟨hi, mem_dropRows.1 hmem⟩
  · intro h
    exact ⟨(Finset.mem_erase.1 h).1, mem_dropRows.2 (Finset.mem_erase.1 h).2⟩

theorem card_dropRows (s : α) (R : Finset α) :
    (dropRows s R).card = (R.erase s).card := by
  rw [← card_liftContractedRows, liftContractedRows_dropRows]

/-- A column adjacent only to `r` and `s` is not adjacent to rows avoiding both. -/
theorem not_mem_rowNeighborsOn_of_avoid (S : α → β → Prop) {r s : α} {c : β}
    (hc : ∀ i, S i c ↔ i = r ∨ i = s) {T : Finset α} (hr : r ∉ T) (hs : s ∉ T) :
    c ∉ rowNeighborsOn S T := by
  intro hcN
  obtain ⟨i, hiT, hic⟩ := mem_rowNeighborsOn.1 hcN
  rcases (hc i).1 hic with rfl | rfl
  · exact hr hiT
  · exact hs hiT

/--
The expansion lemma.  If `c` is adjacent exactly to `r ≠ s`, each of `r, s`
has a neighbor other than `c`, and the contraction at `c` satisfies strict
Hall, then so does the original support.
-/
theorem strictHallOn_of_contractColumn (S : α → β → Prop) {r s : α} (hrs : r ≠ s)
    {c : β} (hc : ∀ i, S i c ↔ i = r ∨ i = s)
    (hr' : ∃ j, j ≠ c ∧ S r j) (hs' : ∃ j, j ≠ c ∧ S s j)
    (hHall : StrictHallOn (contractColumn S r s c)) :
    StrictHallOn S := by
  classical
  have hDropCard : Fintype.card (Drop s) = Fintype.card α - 1 := Set.card_ne_eq s
  have hαpos : 2 ≤ Fintype.card α := by
    have : ({r, s} : Finset α).card = 2 := Finset.card_pair hrs
    have := Finset.card_le_univ ({r, s} : Finset α)
    omega
  -- Case A: rows avoiding both `r` and `s`.
  have hA : ∀ T : Finset α, T.Nonempty → r ∉ T → s ∉ T →
      T.card < (rowNeighborsOn S T).card := by
    intro T hT hrT hsT
    have hmNot : (⟨r, hrs⟩ : Drop s) ∉ dropRows s T := fun h => hrT (mem_dropRows.1 h)
    have hlift : liftContractedRows (dropRows s T) = T := by
      rw [liftContractedRows_dropRows, Finset.erase_eq_of_notMem hsT]
    have hcardT : (dropRows s T).card = T.card := by
      rw [card_dropRows, Finset.erase_eq_of_notMem hsT]
    have hTsub : T ⊆ (Finset.univ.erase r).erase s := by
      intro x hx
      refine Finset.mem_erase.2 ⟨fun h => hsT (h ▸ hx), Finset.mem_erase.2
        ⟨fun h => hrT (h ▸ hx), Finset.mem_univ x⟩⟩
    have hTle := Finset.card_le_card hTsub
    rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hrs.symm, Finset.mem_univ s⟩),
      Finset.card_erase_of_mem (Finset.mem_univ r), Finset.card_univ] at hTle
    have hne : (dropRows s T).Nonempty := by
      rw [← Finset.card_pos, hcardT]
      exact Finset.card_pos.2 hT
    have hprop : (dropRows s T).card < Fintype.card (Drop s) := by
      rw [hcardT, hDropCard]
      omega
    have h := hHall _ hne hprop
    rw [rowNeighborsOn_contractColumn_of_merged_not_mem S hrs hc _ hmNot, hlift,
      card_restrictAway_eq, if_neg (not_mem_rowNeighborsOn_of_avoid S hc hrT hsT),
      Nat.sub_zero, hcardT] at h
    exact h
  -- Case C: exactly one merged row `x` present.
  have hC : ∀ (R : Finset α) (x : α), S x c → (∃ j, j ≠ c ∧ S x j) → x ∈ R →
      r ∉ R.erase x → s ∉ R.erase x → R.card < (rowNeighborsOn S R).card := by
    intro R x hxc hx' hxR hrT hsT
    obtain ⟨j, hjc, hxj⟩ := hx'
    have hsub : insert c (rowNeighborsOn S (R.erase x)) ⊆ rowNeighborsOn S R := by
      intro y hy
      rcases Finset.mem_insert.1 hy with rfl | hy
      · exact mem_rowNeighborsOn.2 ⟨x, hxR, hxc⟩
      · obtain ⟨i, hi, hiy⟩ := mem_rowNeighborsOn.1 hy
        exact mem_rowNeighborsOn.2 ⟨i, Finset.mem_of_mem_erase hi, hiy⟩
    have hcard1 := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (not_mem_rowNeighborsOn_of_avoid S hc hrT hsT)]
      at hcard1
    have hTcard : (R.erase x).card + 1 = R.card := Finset.card_erase_add_one hxR
    by_cases hT : (R.erase x).Nonempty
    · have := hA _ hT hrT hsT
      omega
    · rw [Finset.not_nonempty_iff_eq_empty] at hT
      rw [hT, Finset.card_empty] at hTcard
      have hpair : ({c, j} : Finset β) ⊆ rowNeighborsOn S R := by
        intro y hy
        rcases Finset.mem_insert.1 hy with rfl | hy
        · exact mem_rowNeighborsOn.2 ⟨x, hxR, hxc⟩
        · rw [Finset.mem_singleton.1 hy]
          exact mem_rowNeighborsOn.2 ⟨x, hxR, hxj⟩
      have := Finset.card_le_card hpair
      rw [Finset.card_pair hjc.symm] at this
      omega
  intro R hR hRproper
  by_cases hrR : r ∈ R <;> by_cases hsR : s ∈ R
  · -- Case B: both merged rows present.
    have hmMem : (⟨r, hrs⟩ : Drop s) ∈ dropRows s R :=
      mem_dropRows.2 hrR
    have hcardR : (dropRows s R).card + 1 = R.card := by
      rw [card_dropRows, Finset.card_erase_of_mem hsR]
      have := Finset.card_pos.2 hR
      omega
    have hne : (dropRows s R).Nonempty := ⟨_, hmMem⟩
    have hprop : (dropRows s R).card < Fintype.card (Drop s) := by
      rw [hDropCard]
      omega
    have h := hHall _ hne hprop
    have hins : insert s (liftContractedRows (dropRows s R)) = R := by
      rw [liftContractedRows_dropRows, Finset.insert_erase hsR]
    have hcN : c ∈ rowNeighborsOn S R :=
      mem_rowNeighborsOn.2 ⟨r, hrR, (hc r).2 (Or.inl rfl)⟩
    rw [rowNeighborsOn_contractColumn_of_merged_mem S hrs _ hmMem, hins,
      card_restrictAway_eq, if_pos hcN] at h
    omega
  · exact hC R r ((hc r).2 (Or.inl rfl)) hr' hrR (Finset.notMem_erase r R)
      (fun h => hsR (Finset.mem_of_mem_erase h))
  · exact hC R s ((hc s).2 (Or.inr rfl)) hs' hsR
      (fun h => hrR (Finset.mem_of_mem_erase h)) (Finset.notMem_erase s R)
  · exact hA R hR hrR hsR

end Expansion

section Lemma24

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- A row of degree at least two has a neighbor other than any given column. -/
theorem exists_neighbor_ne_of_two_le (S : α → β → Prop) {r : α} (c : β)
    (hdeg : 2 ≤ rowDegreeOn S r) : ∃ j, j ≠ c ∧ S r j := by
  classical
  have h1 := Finset.pred_card_le_card_erase (s := rowNeighborsOn S {r}) (a := c)
  unfold rowDegreeOn at hdeg
  obtain ⟨j, hj⟩ := Finset.card_pos.1 (show 0 < ((rowNeighborsOn S {r}).erase c).card by
    omega)
  obtain ⟨hjc, hjN⟩ := Finset.mem_erase.1 hj
  obtain ⟨i, hi, hij⟩ := mem_rowNeighborsOn.1 hjN
  rw [Finset.mem_singleton.1 hi] at hij
  exact ⟨j, hjc, hij⟩

/-- A row of degree at least three has a neighbor avoiding two given columns. -/
theorem exists_neighbor_ne_ne_of_three_le (S : α → β → Prop) {r : α} (c d : β)
    (hdeg : 3 ≤ rowDegreeOn S r) : ∃ j, j ≠ c ∧ j ≠ d ∧ S r j := by
  classical
  have h1 := Finset.pred_card_le_card_erase (s := rowNeighborsOn S {r}) (a := c)
  have h2 := Finset.pred_card_le_card_erase
    (s := (rowNeighborsOn S {r}).erase c) (a := d)
  unfold rowDegreeOn at hdeg
  obtain ⟨j, hj⟩ := Finset.card_pos.1
    (show 0 < (((rowNeighborsOn S {r}).erase c).erase d).card by omega)
  obtain ⟨hjd, hj'⟩ := Finset.mem_erase.1 hj
  obtain ⟨hjc, hjN⟩ := Finset.mem_erase.1 hj'
  obtain ⟨i, hi, hij⟩ := mem_rowNeighborsOn.1 hjN
  rw [Finset.mem_singleton.1 hi] at hij
  exact ⟨j, hjc, hjd, hij⟩

/-- Near decomposability is invariant under swapping equal finite bipartitions. -/
theorem nearlyDecomposableOn_transpose_iff
    (hcard : Fintype.card α = Fintype.card β) (S : α → β → Prop) :
    NearlyDecomposableOn (fun j i ↦ S i j) ↔ NearlyDecomposableOn S := by
  have hdel : ∀ (a : α) (b : β),
      deleteEdgeOn (fun j i ↦ S i j) b a = fun j i ↦ deleteEdgeOn S a b i j := by
    intro a b
    funext j i
    simp only [deleteEdgeOn]
    rw [and_comm (a := j = b)]
  constructor
  · rintro ⟨hH, hmin⟩
    refine ⟨(strictHallOn_transpose_iff hcard S).1 hH, fun a b hab hdelH => ?_⟩
    apply hmin b a hab
    rw [hdel]
    exact (strictHallOn_transpose_iff hcard (deleteEdgeOn S a b)).2 hdelH
  · rintro ⟨hH, hmin⟩
    refine ⟨(strictHallOn_transpose_iff hcard S).2 hH, fun b a hab hdelH => ?_⟩
    apply hmin a b hab
    rw [hdel] at hdelH
    exact (strictHallOn_transpose_iff hcard (deleteEdgeOn S a b)).1 hdelH

end Lemma24

/-- Near decomposability on `Fin n` is invariant under transposition. -/
theorem nearlyDecomposable_transpose {n : ℕ} {S : Fin n → Fin n → Prop}
    (hND : NearlyDecomposable S) : NearlyDecomposable (fun j i ↦ S i j) := by
  rw [← nearlyDecomposableOn_fin_iff] at hND ⊢
  exact (nearlyDecomposableOn_transpose_iff rfl S).2 hND

/--
Lavi Lemma 2.4, column form.  Let `c` be a degree-two column of a nearly
decomposable support of order at least three, with neighbors `r ≠ s`.  If both
rows have degree two, or both have degree at least three, the contraction at
`c` is nearly decomposable.
-/
theorem lavi_lemma_2_4_column {n : ℕ} (hn : 3 ≤ n) (S : Fin n → Fin n → Prop)
    (hND : NearlyDecomposable S) {r s c : Fin n} (hrs : r ≠ s)
    (hrc : S r c) (hsc : S s c) (hdegC : columnDegreeOn S c = 2)
    (hdeg : (rowDegreeOn S r = 2 ∧ rowDegreeOn S s = 2) ∨
      (3 ≤ rowDegreeOn S r ∧ 3 ≤ rowDegreeOn S s)) :
    NearlyDecomposableOn (contractColumn S r s c) := by
  classical
  have hc := column_neighbors_eq_pair_of_degree_two S hrs hrc hsc hdegC
  have hcommon : ∀ k, S r k → S s k → k = c := fun k hrk hsk =>
    nearlyDecomposable_common_neighbor_unique hn hND hrs hrc hsc hrk hsk
  have hdr2 : 2 ≤ rowDegreeOn S r := by omega
  have hds2 : 2 ≤ rowDegreeOn S s := by omega
  refine ⟨fullyIndecomposable_contractColumn_of_degree_two S hrs hrc hsc hdegC hND.1, ?_⟩
  -- An expanded edge deletion that keeps strict Hall contradicts minimality.
  have key : ∀ a b, S a b → b ≠ c →
      (∃ k, k ≠ c ∧ deleteEdge S a b r k) → (∃ k, k ≠ c ∧ deleteEdge S a b s k) →
      ¬StrictHallOn (contractColumn (deleteEdge S a b) r s c) := by
    intro a b hab hbc hr' hs' hH
    have hc' : ∀ x, deleteEdge S a b x c ↔ x = r ∨ x = s := by
      intro x
      simp only [deleteEdge, hc x]
      constructor
      · exact fun h => h.1
      · exact fun h => ⟨h, fun h' => hbc h'.2.symm⟩
    have hdel := strictHallOn_of_contractColumn _ hrs hc' hr' hs' hH
    exact hND.2 a b hab
      ((fullyIndecomposable_iff_strictHall _).2 ((strictHallOn_fin_iff _).1 hdel))
  intro i j hij hHall
  by_cases him : i.1 = r
  · have hi : i = ⟨r, hrs⟩ := Subtype.ext him
    subst hi
    rcases hdeg with ⟨hdr, hds⟩ | ⟨hdr, hds⟩
    · exact nearlyDecomposable_contractColumn_low_low_merged_edge hn S hrs hrc hsc
        hdegC hdr hds hND hij hHall
    · rcases (contractColumn_merged S hrs c j).1 hij with hrj | hsj
      · have hnsj : ¬S s j.1 := fun h => j.2 (hcommon _ hrj h)
        have heq : deleteEdgeOn (contractColumn S r s c) ⟨r, hrs⟩ j =
            contractColumn (deleteEdge S r j.1) r s c := by
          funext x y
          by_cases hx : x.1 = r
          · have hxe : x = ⟨r, hrs⟩ := Subtype.ext hx
            subst hxe
            simp only [deleteEdgeOn, contractColumn, deleteEdge, if_true, true_and,
              Subtype.ext_iff, (Ne.symm hrs), false_and, not_false_eq_true, and_true]
            by_cases hy : y.1 = j.1
            · simp [hy, hnsj]
            · simp [hy]
          · simp only [deleteEdgeOn, contractColumn, deleteEdge, hx, if_false,
              Subtype.ext_iff, false_and, not_false_eq_true, and_true]
        obtain ⟨k, hkc, hkj, hrk⟩ := exists_neighbor_ne_ne_of_three_le S c j.1 hdr
        obtain ⟨k', hk'c, hsk'⟩ := exists_neighbor_ne_of_two_le S c hds2
        exact key r j.1 hrj j.2 ⟨k, hkc, hrk, fun h => hkj h.2⟩
          ⟨k', hk'c, hsk', fun h => hrs h.1.symm⟩ (heq ▸ hHall)
      · have hnrj : ¬S r j.1 := fun h => j.2 (hcommon _ h hsj)
        have heq : deleteEdgeOn (contractColumn S r s c) ⟨r, hrs⟩ j =
            contractColumn (deleteEdge S s j.1) r s c := by
          funext x y
          by_cases hx : x.1 = r
          · have hxe : x = ⟨r, hrs⟩ := Subtype.ext hx
            subst hxe
            simp only [deleteEdgeOn, contractColumn, deleteEdge, if_true, true_and,
              Subtype.ext_iff, hrs, false_and, not_false_eq_true, and_true]
            by_cases hy : y.1 = j.1
            · simp [hy, hnrj]
            · simp [hy]
          · have hxs : x.1 ≠ s := x.2
            simp only [deleteEdgeOn, contractColumn, deleteEdge, hx, if_false,
              Subtype.ext_iff, hxs, false_and, not_false_eq_true, and_true]
        obtain ⟨k, hkc, hrk⟩ := exists_neighbor_ne_of_two_le S c hdr2
        obtain ⟨k', hk'c, hk'j, hsk'⟩ := exists_neighbor_ne_ne_of_three_le S c j.1 hds
        exact key s j.1 hsj j.2 ⟨k, hkc, hrk, fun h => hrs h.1⟩
          ⟨k', hk'c, hsk', fun h => hk'j h.2⟩ (heq ▸ hHall)
  · have his : i.1 ≠ s := i.2
    have hS : S i.1 j.1 := (contractColumn_unmerged S his him c j).1 hij
    have heq : deleteEdgeOn (contractColumn S r s c) i j =
        contractColumn (deleteEdge S i.1 j.1) r s c := by
      funext x y
      by_cases hx : x.1 = r
      · have hxi : x ≠ i := fun h => him (h ▸ hx)
        have hri : r ≠ i.1 := fun h => him h.symm
        have hsi : s ≠ i.1 := fun h => his h.symm
        simp only [deleteEdgeOn, contractColumn, deleteEdge, hx, if_true, hxi, hri, hsi,
          false_and, not_false_eq_true, and_true]
      · simp only [deleteEdgeOn, contractColumn, deleteEdge, hx, if_false,
          Subtype.ext_iff]
    obtain ⟨k, hkc, hrk⟩ := exists_neighbor_ne_of_two_le S c hdr2
    obtain ⟨k', hk'c, hsk'⟩ := exists_neighbor_ne_of_two_le S c hds2
    exact key i.1 j.1 hS j.2 ⟨k, hkc, hrk, fun h => him h.1.symm⟩
      ⟨k', hk'c, hsk', fun h => his h.1.symm⟩ (heq ▸ hHall)

/--
Lavi Lemma 2.4, row form (the transposed assertion).  Let `r` be a degree-two
row with neighbors `c ≠ d`.  If both columns have degree two, or both have
degree at least three, the contraction at `r` is nearly decomposable.
-/
theorem lavi_lemma_2_4_row {n : ℕ} (hn : 3 ≤ n) (S : Fin n → Fin n → Prop)
    (hND : NearlyDecomposable S) {r c d : Fin n} (hcd : c ≠ d)
    (hrc : S r c) (hrd : S r d) (hdegR : rowDegreeOn S r = 2)
    (hdeg : (columnDegreeOn S c = 2 ∧ columnDegreeOn S d = 2) ∨
      (3 ≤ columnDegreeOn S c ∧ 3 ≤ columnDegreeOn S d)) :
    NearlyDecomposableOn (contractRow S r c d) := by
  let ST : Fin n → Fin n → Prop := fun j i ↦ S i j
  have hT := lavi_lemma_2_4_column hn ST (nearlyDecomposable_transpose hND) hcd hrc hrd
    hdegR hdeg
  have hdrop : Fintype.card (Drop d) = Fintype.card (Drop r) := by
    exact (Set.card_ne_eq d).trans (Set.card_ne_eq r).symm
  have hTT := (nearlyDecomposableOn_transpose_iff hdrop (contractColumn ST c d r)).2 hT
  change NearlyDecomposableOn
    (fun (i : Drop r) (j : Drop d) ↦ if j.1 = c then S i.1 c ∨ S i.1 d else S i.1 j.1)
  simpa only [contractColumn, ST] using hTT

end LaviSection2
