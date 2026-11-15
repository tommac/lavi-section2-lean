import LaviSection2.LaviCanonicalExpansion
import LaviSection2.LaviTerminalStructure

/-!
# Lavi Lemma 2.5: terminal classification

Every terminal nearly decomposable support of order at least three is, up to
relabelling rows and columns, the canonical expansion `D_can(H)` of a
balanced fully indecomposable occurrence core `H` whose minimum occurrence
degree is at least three.

Together with `nearlyDecomposableOn_canonicalAdj` (canonical expansions are
nearly decomposable) and `privateContraction_canonical` /
`privateRowContraction_canonical` (for minimum occurrence degree three, every
private-line contraction is fully indecomposable but not nearly decomposable),
this is all of Lavi's Lemma 2.5.

The proof combines the combinatorial recovery `terminal_structure` with:
direct occurrences are essential (`direct_essential_of_nearlyDecomposableOn`),
and every long occurrence is removable, since otherwise contracting its
private column would be nearly decomposable
(`nearlyDecomposableOn_privateContraction_of_essential`), contradicting
terminality.  Hence the long occurrences are exactly the removable ones.

Lavi states the lemma for noncycle terminal supports.  The hypothesis is not
needed here: a cycle of order at least three is never terminal, by Lemma 2.4.
-/

namespace LaviSection2

open Finset

/-- Lavi Lemma 2.5: a terminal ND support is a canonical expansion. -/
theorem lavi_lemma_2_5 {n : ℕ} (hn : 3 ≤ n) (D : Fin n → Fin n → Prop)
    (hND : NearlyDecomposable D) (hterm : Terminal D) :
    ∃ (U V E : Type) (_ : Fintype U) (_ : Fintype V) (_ : Fintype E)
      (_ : DecidableEq U) (_ : DecidableEq V) (_ : DecidableEq E)
      (row : E → U) (col : E → V) (O : Finset E),
      Fintype.card U = Fintype.card V ∧ CoreFI row col O ∧ MinOccDegreeThree row col O ∧
      ∃ (eR : Fin n ≃ U ⊕ removableSet row col O)
        (eC : Fin n ≃ V ⊕ removableSet row col O),
        ∀ i j, D i j ↔ canonicalAdj row col O (eR i) (eC j) := by
  classical
  obtain ⟨U, V, E, iU, iV, iE, dU, dV, dE, row, col, O, L, hL, hbal, hmin, hpar, eR, eC,
    hiso⟩ := terminal_structure hn D hND hterm
  have hNDexp : NearlyDecomposableOn (expAdj row col O L) :=
    (nearlyDecomposableOn_relabel_iff eR eC hiso).1 ((nearlyDecomposableOn_fin_iff D).2 hND)
  have hcardUL : Fintype.card (U ⊕ L) = n := by
    rw [← Fintype.card_congr eR, Fintype.card_fin]
  have hO : CoreFI row col O := coreFI_of_expAdj O L hL (by omega) hNDexp.1
  have hess := direct_essential_of_nearlyDecomposableOn O L hbal hL hmin hNDexp hpar
  -- Every long occurrence is removable.
  have hlong : ∀ e (he : e ∈ L), CoreFI row col (O.erase e) := by
    intro e he
    by_contra hess₀
    have hcardErase : Fintype.card (U ⊕ (L.erase e)) = n - 1 := by
      rw [Fintype.card_sum, Fintype.card_coe, Finset.card_erase_of_mem he]
      rw [Fintype.card_sum, Fintype.card_coe] at hcardUL
      have : 0 < L.card := Finset.card_pos.2 ⟨e, he⟩
      omega
    have hNDc := nearlyDecomposableOn_privateContraction_of_essential O L hbal hL hO hmin
      hess hpar he hess₀ (by omega)
    -- Transport the contraction back to `D`.
    set r := eR.symm (Sum.inl (row e))
    set s := eR.symm (Sum.inr ⟨e, he⟩)
    set c := eC.symm (Sum.inr ⟨e, he⟩)
    have hrs : r ≠ s := fun h => Sum.inl_ne_inr (eR.symm.injective h)
    have hrc : D r c := by
      rw [hiso]
      simp [r, c, expAdj]
    have hsc : D s c := by
      rw [hiso]
      simp [s, c, expAdj]
    have hdeg : columnDegreeOn D c = 2 := by
      rw [columnDegreeOn_relabel eR eC hiso c]
      simp only [c, Equiv.apply_symm_apply]
      unfold columnDegreeOn
      have : rowNeighborsOn (fun j i => expAdj row col O L i j) {Sum.inr ⟨e, he⟩} =
          {Sum.inl (row e), Sum.inr ⟨e, he⟩} := by
        ext i
        rw [mem_rowNeighborsOn]
        simp only [Finset.mem_singleton, exists_eq_left, Finset.mem_insert]
        exact expAdj_private_column O L he i
      rw [this, Finset.card_pair Sum.inl_ne_inr]
    apply hterm.1 r s c hrs hrc hsc hdeg
    rw [nearlyDecomposableOn_relabel_iff (dropEquiv eR s) (dropEquiv eC c)
      (contractColumn_relabel eR eC hiso r s c)]
    simp only [r]
    rw [Equiv.apply_symm_apply eR, Equiv.apply_symm_apply eR, Equiv.apply_symm_apply eC]
    exact hNDc
  have hLeq : L = removableSet row col O := by
    ext e
    rw [mem_removableSet]
    constructor
    · intro he
      exact ⟨hL he, hlong e he⟩
    · rintro ⟨he, hFI⟩
      by_contra heL
      exact hess e he heL hFI
  subst hLeq
  exact ⟨U, V, E, iU, iV, iE, dU, dV, dE, row, col, O, hbal, hO, hmin, eR, eC, hiso⟩

end LaviSection2
