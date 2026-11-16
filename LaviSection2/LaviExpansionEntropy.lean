import LaviSection2.LaviCoreEntropy
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Lavi Section 3: the expansion identity (3.5) and the normalized gap

Let `H` be an occurrence core (edges `E`, endpoints `row`, `col`) and `L` a
set of long occurrences.  The expansion `D(H, L)` replaces each long
occurrence `ℓ` by a path `row ℓ — c_ℓ — s_ℓ — col ℓ` through a private column
`c_ℓ` and a private row `s_ℓ`.  As a multigraph its edges are

* `direct d` for `d ∉ L`,
* `a ℓ = (row ℓ, c_ℓ)`, `b ℓ = (s_ℓ, c_ℓ)`, `c ℓ = (s_ℓ, col ℓ)` for `ℓ ∈ L`,

with flows `x_d` and `(x_ℓ, 1 - x_ℓ, x_ℓ)`.  Labelled matchings of `H` and of
its expansion correspond bijectively (`ℓ` is used iff `a ℓ` and `c ℓ` are),
so `Ent*` is unchanged, while each private row contributes `h₂(x_ℓ)` to the
row entropy.  This gives Lavi's identity (3.5):

`F_{D(H,L)}(X_x) = F_H(x) - ∑_{ℓ ∈ L} h₂(x_ℓ)`,

stated both for the expanded multigraph and, through Lemma 3.2 and the bridge,
for the expanded flow matrix `X_x`.  The normalized gap (3.6) and its matrix
form (3.7) follow.
-/

set_option linter.unusedSectionVars false

namespace LaviSection2

open Finset Equiv Real

open scoped BigOperators

/-- Mathlib's binary entropy is `h₂(t) = -t log t - (1 - t) log (1 - t)`. -/
theorem binEntropy_eq (t : ℝ) :
    binEntropy t = -(t * log t) - (1 - t) * log (1 - t) := by
  rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub, Real.negMulLog, Real.negMulLog]
  ring

section Expansion

variable {U V E : Type*} [Fintype U] [Fintype V] [Fintype E]
  [DecidableEq U] [DecidableEq V] [DecidableEq E]
  (row : E → U) (col : E → V) (L : Finset E)

/-- Edges of the expansion `D(H, L)`. -/
abbrev ExpEdge (L : Finset E) : Type _ := {e : E // e ∉ L} ⊕ (↥L ⊕ (↥L ⊕ ↥L))

/-- The direct edge of `d ∉ L`. -/
abbrev dE {L : Finset E} (d : {e : E // e ∉ L}) : ExpEdge L := Sum.inl d
/-- `a ℓ = (row ℓ, c_ℓ)`. -/
abbrev aE {L : Finset E} (ℓ : ↥L) : ExpEdge L := Sum.inr (Sum.inl ℓ)
/-- `b ℓ = (s_ℓ, c_ℓ)`. -/
abbrev bE {L : Finset E} (ℓ : ↥L) : ExpEdge L := Sum.inr (Sum.inr (Sum.inl ℓ))
/-- `c ℓ = (s_ℓ, col ℓ)`. -/
abbrev cE {L : Finset E} (ℓ : ↥L) : ExpEdge L := Sum.inr (Sum.inr (Sum.inr ℓ))

/-- Row endpoints in the expansion (rows `U ⊕ L`, the second summand being the
private rows `s_ℓ`). -/
def expRow : ExpEdge L → U ⊕ ↥L
  | Sum.inl d => Sum.inl (row d.1)
  | Sum.inr (Sum.inl ℓ) => Sum.inl (row ℓ.1)
  | Sum.inr (Sum.inr (Sum.inl ℓ)) => Sum.inr ℓ
  | Sum.inr (Sum.inr (Sum.inr ℓ)) => Sum.inr ℓ

/-- Column endpoints in the expansion (columns `V ⊕ L`, the second summand
being the private columns `c_ℓ`). -/
def expCol : ExpEdge L → V ⊕ ↥L
  | Sum.inl d => Sum.inl (col d.1)
  | Sum.inr (Sum.inl ℓ) => Sum.inr ℓ
  | Sum.inr (Sum.inr (Sum.inl ℓ)) => Sum.inr ℓ
  | Sum.inr (Sum.inr (Sum.inr ℓ)) => Sum.inl (col ℓ.1)

/-- Expanded flows: `x_d` on direct edges and `(x_ℓ, 1 - x_ℓ, x_ℓ)` on paths. -/
def expFlow (x : E → ℝ) : ExpEdge L → ℝ
  | Sum.inl d => x d.1
  | Sum.inr (Sum.inl ℓ) => x ℓ.1
  | Sum.inr (Sum.inr (Sum.inl ℓ)) => 1 - x ℓ.1
  | Sum.inr (Sum.inr (Sum.inr ℓ)) => x ℓ.1

/-- The underlying occurrence of an expanded edge. -/
def baseEdge : ExpEdge L → E
  | Sum.inl d => d.1
  | Sum.inr (Sum.inl ℓ) => ℓ.1
  | Sum.inr (Sum.inr (Sum.inl ℓ)) => ℓ.1
  | Sum.inr (Sum.inr (Sum.inr ℓ)) => ℓ.1

variable {row col L}

/-- The expanded matching of a labelled matching of `H`. -/
def expMatchFun (M : U → E) : U ⊕ ↥L → ExpEdge L
  | Sum.inl u => if h : M u ∈ L then aE ⟨M u, h⟩ else dE ⟨M u, h⟩
  | Sum.inr ℓ => if M (row ℓ.1) = ℓ.1 then cE ℓ else bE ℓ

theorem expRow_expMatchFun (M : LMatch row col) (r : U ⊕ ↥L) :
    expRow row L (expMatchFun (row := row) M.1 r) = r := by
  rcases r with u | ℓ
  · simp only [expMatchFun]
    split_ifs <;> simp [expRow, M.2.1 u]
  · simp only [expMatchFun]
    split_ifs <;> simp [expRow]

theorem card_eq_of_lmatch (M : LMatch row col) : Fintype.card U = Fintype.card V :=
  Fintype.card_of_bijective M.2.2

theorem expCol_expMatchFun_injective (M : LMatch row col) :
    Function.Injective fun r => expCol col L (expMatchFun (row := row) M.1 r) := by
  have hinj := M.2.2.1
  have hrowM : ∀ u, row (M.1 u) = u := M.2.1
  rintro (u₁ | ℓ₁) (u₂ | ℓ₂) h
  · simp only [expMatchFun] at h
    split_ifs at h with h1 h2 h2 <;> simp only [expCol, Sum.inl.injEq, Sum.inr.injEq,
      Subtype.mk.injEq, reduceCtorEq] at h
    · rw [← hrowM u₁, h, hrowM u₂]
    · exact congrArg Sum.inl (hinj h)
  · simp only [expMatchFun] at h
    split_ifs at h with h1 h2 h2 <;> simp only [expCol, Sum.inl.injEq, Sum.inr.injEq,
      Subtype.mk.injEq, reduceCtorEq] at h
    · -- `M u₁ = ℓ₂` but `ℓ₂` is not used
      exact absurd (by rw [← h, hrowM u₁]) h2
    · -- `col (M u₁) = col ℓ₂ = col (M (row ℓ₂))`, so `u₁ = row ℓ₂` and `M u₁ = ℓ₂ ∈ L`
      have hu : u₁ = row ℓ₂.1 := hinj (by simp only; rw [h, h2])
      exact absurd (by rw [hu, h2]; exact ℓ₂.2) h1
  · simp only [expMatchFun] at h
    split_ifs at h with h1 h2 h2 <;> simp only [expCol, Sum.inl.injEq, Sum.inr.injEq,
      Subtype.mk.injEq, reduceCtorEq] at h
    · have hu : u₂ = row ℓ₁.1 := hinj (by simp only; rw [← h, h1])
      exact absurd (by rw [hu, h1]; exact ℓ₁.2) h2
    · exact absurd (by rw [h, hrowM u₂]) h1
  · simp only [expMatchFun] at h
    split_ifs at h with h1 h2 h2 <;> simp only [expCol, Sum.inl.injEq, Sum.inr.injEq,
      reduceCtorEq] at h
    · have hr : row ℓ₁.1 = row ℓ₂.1 := hinj (by simp only; rw [h1, h2, h])
      exact congrArg Sum.inr (Subtype.ext (by rw [← h1, ← h2, hr]))
    · exact congrArg Sum.inr h

/-- The expanded matching. -/
def expMatch (M : LMatch row col) : LMatch (expRow row L) (expCol col L) :=
  ⟨expMatchFun M.1, expRow_expMatchFun M, by
    refine (Fintype.bijective_iff_injective_and_card _).2
      ⟨expCol_expMatchFun_injective M, ?_⟩
    simp only [Fintype.card_sum, card_eq_of_lmatch M]⟩

theorem expMatch_injective : Function.Injective (expMatch (row := row) (col := col) (L := L)) := by
  intro M₁ M₂ h
  apply Subtype.ext
  funext u
  have := congrFun (congrArg Subtype.val h) (Sum.inl u)
  simp only [expMatch, expMatchFun] at this
  split_ifs at this <;> simp_all

/-- Structure of an expanded matching at a row of `U`. -/
theorem lmatch_exp_inl (N : LMatch (expRow row L) (expCol col L)) (u : U) :
    (∃ d : {e : E // e ∉ L}, N.1 (Sum.inl u) = dE d ∧ row d.1 = u) ∨
      (∃ ℓ : ↥L, N.1 (Sum.inl u) = aE ℓ ∧ row ℓ.1 = u) := by
  have h := N.2.1 (Sum.inl u)
  rcases hN : N.1 (Sum.inl u) with d | ℓ | ℓ | ℓ
  · rw [hN] at h; exact Or.inl ⟨d, rfl, by simpa [expRow] using h⟩
  · rw [hN] at h; exact Or.inr ⟨ℓ, rfl, by simpa [expRow] using h⟩
  · rw [hN] at h; simp [expRow] at h
  · rw [hN] at h; simp [expRow] at h

/-- Structure of an expanded matching at a private row. -/
theorem lmatch_exp_inr (N : LMatch (expRow row L) (expCol col L)) (ℓ : ↥L) :
    N.1 (Sum.inr ℓ) = bE ℓ ∨ N.1 (Sum.inr ℓ) = cE ℓ := by
  have h := N.2.1 (Sum.inr ℓ)
  rcases hN : N.1 (Sum.inr ℓ) with d | ℓ' | ℓ' | ℓ'
  · rw [hN] at h; simp [expRow] at h
  · rw [hN] at h; simp [expRow] at h
  · rw [hN] at h; simp only [expRow, Sum.inr.injEq] at h; exact Or.inl (by rw [h])
  · rw [hN] at h; simp only [expRow, Sum.inr.injEq] at h; exact Or.inr (by rw [h])

/-- A private row uses `c ℓ` exactly when `row ℓ` uses `a ℓ`. -/
theorem lmatch_exp_c_iff (N : LMatch (expRow row L) (expCol col L)) (ℓ : ↥L) :
    N.1 (Sum.inr ℓ) = cE ℓ ↔ N.1 (Sum.inl (row ℓ.1)) = aE ℓ := by
  constructor
  · intro hc
    obtain ⟨r, hr⟩ := N.2.2.2 (Sum.inr ℓ)
    simp only at hr
    rcases r with u | ℓ'
    · rcases lmatch_exp_inl N u with ⟨d, hd, -⟩ | ⟨ℓ'', hℓ'', hrow⟩
      · rw [hd] at hr; simp [expCol] at hr
      · rw [hℓ''] at hr
        simp only [expCol, Sum.inr.injEq] at hr
        subst hr; rw [hrow]; exact hℓ''
    · rcases lmatch_exp_inr N ℓ' with hb | hc'
      · rw [hb] at hr
        simp only [expCol, Sum.inr.injEq] at hr
        subst hr; rw [hb] at hc; simp at hc
      · rw [hc'] at hr; simp [expCol] at hr
  · intro ha
    rcases lmatch_exp_inr N ℓ with hb | hc
    · have hcol : expCol col L (N.1 (Sum.inl (row ℓ.1))) = expCol col L (N.1 (Sum.inr ℓ)) := by
        rw [ha, hb]; rfl
      have := N.2.2.1 hcol
      simp at this
    · exact hc

/-- Every expanded matching comes from a matching of `H`. -/
theorem expMatch_surjective :
    Function.Surjective (expMatch (row := row) (col := col) (L := L)) := by
  intro N
  set M : U → E := fun u => baseEdge L (N.1 (Sum.inl u)) with hMdef
  have hrowM : ∀ u, row (M u) = u := by
    intro u
    rcases lmatch_exp_inl N u with ⟨d, hd, hrow⟩ | ⟨ℓ, hℓ, hrow⟩
    · simp only [hMdef, hd, baseEdge]; exact hrow
    · simp only [hMdef, hℓ, baseEdge]; exact hrow
  -- the row of `N` that covers the column `col (M u)`
  let p : U → U ⊕ ↥L := fun u =>
    if h : M u ∈ L then Sum.inr ⟨M u, h⟩ else Sum.inl u
  have hp : ∀ u, expCol col L (N.1 (p u)) = Sum.inl (col (M u)) := by
    intro u
    simp only [p]
    split_ifs with h
    · have ha : N.1 (Sum.inl (row (M u))) = aE ⟨M u, h⟩ := by
        rw [hrowM u]
        rcases lmatch_exp_inl N u with ⟨d, hd, -⟩ | ⟨ℓ, hℓ, -⟩
        · simp only [hMdef, hd, baseEdge] at h; exact absurd h d.2
        · rw [hℓ]; congr 2; apply Subtype.ext; simp [hMdef, hℓ, baseEdge]
      have hc := (lmatch_exp_c_iff N ⟨M u, h⟩).2 ha
      rw [hc]; rfl
    · rcases lmatch_exp_inl N u with ⟨d, hd, -⟩ | ⟨ℓ, hℓ, -⟩
      · rw [hd]; simp [expCol, hMdef, hd, baseEdge]
      · simp only [hMdef, hℓ, baseEdge] at h; exact absurd ℓ.2 h
  have hpinj : Function.Injective p := by
    intro u₁ u₂ h
    simp only [p] at h
    split_ifs at h with h1 h2 h2 <;> simp only [Sum.inl.injEq, Sum.inr.injEq,
      Subtype.mk.injEq, reduceCtorEq] at h
    · rw [← hrowM u₁, h, hrowM u₂]
    · exact h
  have hcolinj : Function.Injective fun u => col (M u) := by
    intro u₁ u₂ h
    apply hpinj
    apply N.2.2.1
    simp only
    rw [hp u₁, hp u₂]
    exact congrArg Sum.inl h
  have hcard : Fintype.card U = Fintype.card V := by
    have := Fintype.card_of_bijective N.2.2
    simp only [Fintype.card_sum] at this
    omega
  refine ⟨⟨M, hrowM, (Fintype.bijective_iff_injective_and_card _).2 ⟨hcolinj, hcard⟩⟩, ?_⟩
  apply Subtype.ext
  funext r
  rcases r with u | ℓ
  · show expMatchFun (row := row) M (Sum.inl u) = N.1 (Sum.inl u)
    simp only [expMatchFun]
    rcases lmatch_exp_inl N u with ⟨d, hd, -⟩ | ⟨ℓ, hℓ, -⟩
    · have hM : M u = d.1 := by simp [hMdef, hd, baseEdge]
      rw [dite_eq_right (by rw [hM]; exact d.2), hd]
      simp only [hM]
    · have hM : M u = ℓ.1 := by simp [hMdef, hℓ, baseEdge]
      rw [dite_eq_left (by rw [hM]; exact ℓ.2), hℓ]
      simp only [hM]
  · show expMatchFun (row := row) M (Sum.inr ℓ) = N.1 (Sum.inr ℓ)
    simp only [expMatchFun]
    have hiff : M (row ℓ.1) = ℓ.1 ↔ N.1 (Sum.inl (row ℓ.1)) = aE ℓ := by
      constructor
      · intro h
        rcases lmatch_exp_inl N (row ℓ.1) with ⟨d, hd, -⟩ | ⟨ℓ', hℓ', -⟩
        · simp only [hMdef, hd, baseEdge] at h
          exact absurd (h ▸ ℓ.2) d.2
        · simp only [hMdef, hℓ', baseEdge] at h
          rw [hℓ']; congr 2; exact Subtype.ext h
      · intro h; simp [hMdef, h, baseEdge]
    split_ifs with h
    · exact ((lmatch_exp_c_iff N ℓ).2 (hiff.1 h)).symm
    · rcases lmatch_exp_inr N ℓ with hb | hc
      · exact hb.symm
      · exact absurd (hiff.2 ((lmatch_exp_c_iff N ℓ).1 hc)) h

/-- Labelled matchings of `H` and of its expansion correspond bijectively. -/
noncomputable def expMatchEquiv : LMatch row col ≃ LMatch (expRow row L) (expCol col L) :=
  Equiv.ofBijective expMatch ⟨expMatch_injective, expMatch_surjective⟩

theorem expMatchEquiv_apply (M : LMatch row col) (r : U ⊕ ↥L) :
    (expMatchEquiv M).1 r = expMatchFun (row := row) M.1 r := rfl

/-- Which expanded matchings contain a given expanded edge. -/
theorem expMatch_mem_iff (M : LMatch row col) (f : ExpEdge L) :
    (expMatchEquiv M).1 (expRow row L f) = f ↔
      match f with
      | Sum.inl d => M.1 (row d.1) = d.1
      | Sum.inr (Sum.inl ℓ) => M.1 (row ℓ.1) = ℓ.1
      | Sum.inr (Sum.inr (Sum.inl ℓ)) => M.1 (row ℓ.1) ≠ ℓ.1
      | Sum.inr (Sum.inr (Sum.inr ℓ)) => M.1 (row ℓ.1) = ℓ.1 := by
  rw [expMatchEquiv_apply]
  rcases f with d | ℓ | ℓ | ℓ
  · simp only [expRow, expMatchFun]
    split_ifs with h
    · simp only [reduceCtorEq, false_iff]
      intro h'; rw [h'] at h; exact d.2 h
    · simp only [Sum.inl.injEq]
      exact ⟨fun h' => congrArg Subtype.val h', fun h' => Subtype.ext h'⟩
  · simp only [expRow, expMatchFun]
    split_ifs with h
    · simp only [Sum.inr.injEq, Sum.inl.injEq]
      exact ⟨fun h' => congrArg Subtype.val h', fun h' => Subtype.ext h'⟩
    · simp only [reduceCtorEq, false_iff]
      intro h'; rw [h'] at h; exact h ℓ.2
  · simp only [expRow, expMatchFun]
    split_ifs with h <;> simp [h]
  · simp only [expRow, expMatchFun]
    split_ifs with h <;> simp [h]

end Expansion

section ExpansionIdentity

variable {U V E : Type*} [Fintype U] [Fintype V] [Fintype E]
  [DecidableEq U] [DecidableEq V] [DecidableEq E]
  {row : E → U} {col : E → V} {L : Finset E}

/-- Marginals of a transported law. -/
theorem coreMarginal_exp (μ : LMatch row col → ℝ) (f : ExpEdge L) :
    coreMarginal (expRow row L) (expCol col L) (μ ∘ expMatchEquiv.symm) f =
      ∑ M ∈ (univ : Finset (LMatch row col)).filter
        (fun M => (expMatchEquiv M).1 (expRow row L f) = f), μ M := by
  classical
  unfold coreMarginal
  rw [Finset.sum_filter, Finset.sum_filter,
    ← Equiv.sum_comp expMatchEquiv (fun N => if N.1 (expRow row L f) = f then
      (μ ∘ expMatchEquiv.symm) N else 0)]
  simp only [Function.comp_apply, Equiv.symm_apply_apply]

theorem coreMarginal_exp_dE (μ : LMatch row col → ℝ) (d : {e : E // e ∉ L}) :
    coreMarginal (expRow row L) (expCol col L) (μ ∘ expMatchEquiv.symm) (dE d) =
      coreMarginal row col μ d.1 := by
  rw [coreMarginal_exp]
  unfold coreMarginal
  exact Finset.sum_congr (Finset.filter_congr fun M _ => expMatch_mem_iff M (dE d)) fun _ _ => rfl

theorem coreMarginal_exp_aE (μ : LMatch row col → ℝ) (ℓ : ↥L) :
    coreMarginal (expRow row L) (expCol col L) (μ ∘ expMatchEquiv.symm) (aE ℓ) =
      coreMarginal row col μ ℓ.1 := by
  rw [coreMarginal_exp]
  unfold coreMarginal
  exact Finset.sum_congr (Finset.filter_congr fun M _ => expMatch_mem_iff M (aE ℓ)) fun _ _ => rfl

theorem coreMarginal_exp_cE (μ : LMatch row col → ℝ) (ℓ : ↥L) :
    coreMarginal (expRow row L) (expCol col L) (μ ∘ expMatchEquiv.symm) (cE ℓ) =
      coreMarginal row col μ ℓ.1 := by
  rw [coreMarginal_exp]
  unfold coreMarginal
  exact Finset.sum_congr (Finset.filter_congr fun M _ => expMatch_mem_iff M (cE ℓ)) fun _ _ => rfl

theorem coreMarginal_exp_bE (μ : LMatch row col → ℝ) (ℓ : ↥L) :
    coreMarginal (expRow row L) (expCol col L) (μ ∘ expMatchEquiv.symm) (bE ℓ) =
      ∑ M, μ M - coreMarginal row col μ ℓ.1 := by
  classical
  rw [coreMarginal_exp]
  unfold coreMarginal
  rw [Finset.sum_congr (Finset.filter_congr fun M _ => expMatch_mem_iff M (bE ℓ)) fun _ _ => rfl]
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun M : LMatch row col => M.1 (row ℓ.1) = ℓ.1)]
  ring

/-- Laws transport between `H` and its expansion. -/
theorem isCoreLaw_exp_iff (x : E → ℝ) (μ : LMatch row col → ℝ) :
    IsCoreLaw row col x μ ↔
      IsCoreLaw (expRow row L) (expCol col L) (expFlow L x) (μ ∘ expMatchEquiv.symm) := by
  have hsum : ∑ N : LMatch (expRow row L) (expCol col L), (μ ∘ expMatchEquiv.symm) N =
      ∑ M, μ M :=
    Equiv.sum_comp expMatchEquiv.symm μ
  constructor
  · rintro ⟨hnn, h1, hm⟩
    refine ⟨fun N => hnn _, by rw [hsum, h1], ?_⟩
    funext f
    rcases f with d | ℓ | ℓ | ℓ
    · rw [coreMarginal_exp_dE, hm]; rfl
    · rw [coreMarginal_exp_aE, hm]; rfl
    · rw [coreMarginal_exp_bE, hm, h1]; rfl
    · rw [coreMarginal_exp_cE, hm]; rfl
  · rintro ⟨hnn, h1, hm⟩
    refine ⟨fun M => by simpa using hnn (expMatchEquiv M), by rw [← hsum, h1], ?_⟩
    funext e
    by_cases he : e ∈ L
    · have := congrFun hm (aE ⟨e, he⟩)
      rw [coreMarginal_exp_aE] at this
      exact this
    · have := congrFun hm (dE ⟨e, he⟩)
      rw [coreMarginal_exp_dE] at this
      exact this

/-- `Ent*` is unchanged by expansion. -/
theorem coreMaxEntropy_exp (x : E → ℝ) :
    coreMaxEntropy (expRow row L) (expCol col L) (expFlow L x) = coreMaxEntropy row col x := by
  unfold coreMaxEntropy
  congr 1
  ext t
  constructor
  · rintro ⟨ν, hν, rfl⟩
    have hcomp : (ν ∘ expMatchEquiv) ∘ expMatchEquiv.symm = ν :=
      funext fun N => by simp only [Function.comp_apply, Equiv.apply_symm_apply]
    refine ⟨ν ∘ expMatchEquiv, (isCoreLaw_exp_iff x _).2 (by rw [hcomp]; exact hν), ?_⟩
    unfold coreLawEntropy
    exact Equiv.sum_comp expMatchEquiv (fun N => -(ν N * log (ν N)))
  · rintro ⟨μ, hμ, rfl⟩
    refine ⟨μ ∘ expMatchEquiv.symm, (isCoreLaw_exp_iff x μ).1 hμ, ?_⟩
    unfold coreLawEntropy
    exact Equiv.sum_comp expMatchEquiv.symm (fun M => -(μ M * log (μ M)))

/-- Each private row adds `h₂(x_ℓ)` to the edge entropy. -/
theorem edgeEntropy_exp (x : E → ℝ) :
    edgeEntropy (expFlow L x) = edgeEntropy x + ∑ ℓ ∈ L, binEntropy (x ℓ) := by
  classical
  set g : E → ℝ := fun e => x e * log (x e)
  have hsplit : ∑ d : {e : E // e ∉ L}, g d.1 + ∑ ℓ : ↥L, g ℓ.1 = ∑ e, g e := by
    rw [← Finset.sum_compl_add_sum L g, Finset.sum_coe_sort L g]
    congr 1
    exact (Finset.sum_subtype Lᶜ (fun e => Finset.mem_compl) g).symm
  have hbin : ∑ ℓ ∈ L, binEntropy (x ℓ) =
      ∑ ℓ : ↥L, (-(x ℓ.1 * log (x ℓ.1)) - (1 - x ℓ.1) * log (1 - x ℓ.1)) := by
    rw [← Finset.sum_coe_sort L]
    exact Finset.sum_congr rfl fun ℓ _ => binEntropy_eq _
  unfold edgeEntropy
  rw [hbin, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [expFlow]
  rw [← hsplit]
  simp only [g, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  ring

/-- **Lavi (3.5), multigraph form:** `F_{D(H,L)} = F_H - ∑_{ℓ ∈ L} h₂(x_ℓ)`. -/
theorem coreFunctional_exp (x : E → ℝ) :
    coreFunctional (expRow row L) (expCol col L) (expFlow L x) =
      coreFunctional row col x - ∑ ℓ ∈ L, binEntropy (x ℓ) := by
  unfold coreFunctional
  rw [coreMaxEntropy_exp, edgeEntropy_exp]
  ring

/-- The expanded flow matrix `X_x` of Lavi's (3.5), in coordinates
`eR : Fin n ≃ U ⊕ L`, `eC : Fin n ≃ V ⊕ L`: direct entries aggregate the
parallel direct-occurrence flows, and each long path carries
`(x_ℓ, 1 - x_ℓ, x_ℓ)`. -/
def expandedMatrix {n : ℕ} (row : E → U) (col : E → V) (L : Finset E)
    (eR : Fin n ≃ U ⊕ ↥L) (eC : Fin n ≃ V ⊕ ↥L) (x : E → ℝ) : Square n :=
  aggregateMatrix (expRow row L) (expCol col L) eR eC (expFlow L x)

/-- **Lavi (3.5):** for a feasible core flow `x`,
`F_{D(H,L)}(X_x) = F_H(x) - ∑_{ℓ ∈ L} h₂(x_ℓ)`. -/
theorem lavi_eq_3_5 {n : ℕ} (eR : Fin n ≃ U ⊕ ↥L) (eC : Fin n ≃ V ⊕ ↥L) {x : E → ℝ}
    (hlaw : ∃ μ, IsCoreLaw row col x μ) :
    faceFunctional (expandedMatrix row col L eR eC x) =
      coreFunctional row col x - ∑ ℓ ∈ L, binEntropy (x ℓ) := by
  obtain ⟨μ, hμ⟩ := hlaw
  unfold expandedMatrix
  rw [← coreFunctional_eq_faceFunctional eR eC ⟨_, (isCoreLaw_exp_iff x μ).1 hμ⟩,
    coreFunctional_exp]

/-- Lavi's subdivision charge `δ(t) = log 2 - h₂(t) ≥ 0`. -/
noncomputable def subdivCharge (t : ℝ) : ℝ := log 2 - binEntropy t

theorem subdivCharge_nonneg (t : ℝ) : 0 ≤ subdivCharge t := by
  unfold subdivCharge
  linarith [binEntropy_le_log_two (p := t)]

/-- Lavi's normalized gap (3.6):
`G_{H,L}(x) = F_H(x) + (h - 1) log 2 + ∑_{ℓ ∈ L} δ(x_ℓ)`, with `h = |U|`. -/
noncomputable def normalizedGap (row : E → U) (col : E → V) (L : Finset E) (x : E → ℝ) : ℝ :=
  coreFunctional row col x + ((Fintype.card U : ℝ) - 1) * log 2 + ∑ ℓ ∈ L, subdivCharge (x ℓ)

/-- **Lavi (3.7):** the normalized gap is the expanded functional shifted by
the order: `G_{H,L}(x) = F_{D(H,L)}(X_x) + (h + |L| - 1) log 2`. -/
theorem lavi_eq_3_7 {n : ℕ} (eR : Fin n ≃ U ⊕ ↥L) (eC : Fin n ≃ V ⊕ ↥L) {x : E → ℝ}
    (hlaw : ∃ μ, IsCoreLaw row col x μ) :
    normalizedGap row col L x =
      faceFunctional (expandedMatrix row col L eR eC x) + ((n : ℝ) - 1) * log 2 ∧
    n = Fintype.card U + L.card := by
  have hn : n = Fintype.card U + L.card := by
    rw [← Fintype.card_fin n, Fintype.card_congr eR, Fintype.card_sum, Fintype.card_coe]
  refine ⟨?_, hn⟩
  rw [lavi_eq_3_5 eR eC hlaw, normalizedGap, hn]
  unfold subdivCharge
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  push_cast
  ring

end ExpansionIdentity

end LaviSection2
