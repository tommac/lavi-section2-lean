import LaviSection2.LaviCoreEntropy

/-!
# Lavi Section 4: tight cuts and the two closed factors

A cut of an occurrence core `H = (row, col)` is given by predicates `sR` on rows
and `sC` on columns (the shore `S₁`).  We record the cut in the oriented form
Lavi derives from tightness: the shore `S₁` has one extra row, and no
occurrence runs from a row of `S₂` to a column of `S₁`.  Then every perfect
matching uses exactly one crossing occurrence.

The closed factors are

* `H₁`: rows `S₁`, columns `S₁ ⊕ {marker}`; its occurrences are those with
  row in `S₁`, and a crossing occurrence `e` becomes `(row e, marker)`;
* `H₂`: rows `{marker} ⊕ S₂`, columns `S₂`; its occurrences are those with
  column in `S₂`, and a crossing occurrence `e` becomes `(marker, col e)`.

Crossing occurrences keep their labels in both factors.  We prove that
labelled matchings of `H` correspond exactly to pairs of factor matchings
that choose the same crossing label (`sum_lmatch_eq_sum_pairs`), and Lavi's
order identity (4.1).
-/

set_option linter.unusedSectionVars false

namespace LaviSection2

open Finset Equiv Real

open scoped BigOperators

section TightCut

variable {U V E : Type*} [Fintype U] [Fintype V] [Fintype E]
  [DecidableEq U] [DecidableEq V] [DecidableEq E]

/-- An oriented cut of the core `(row, col)`: the shore `S₁ = sR ∪ sC` has one
more row than columns, and no occurrence enters `S₁`'s columns from a row of
`S₂`.  (Lavi shows that every tight cut has this form for one of its shores.) -/
structure ShoreCut (row : E → U) (col : E → V) where
  /-- Rows of the shore `S₁`. -/
  sR : U → Prop
  /-- Columns of the shore `S₁`. -/
  sC : V → Prop
  [decR : DecidablePred sR]
  [decC : DecidablePred sC]
  /-- No occurrence from a row of `S₂` to a column of `S₁`. -/
  back : ∀ e, sC (col e) → sR (row e)
  /-- `S₁` has exactly one extra row. -/
  card : Fintype.card {u // sR u} = Fintype.card {v // sC v} + 1

attribute [instance] ShoreCut.decR ShoreCut.decC

variable {row : E → U} {col : E → V} (K : ShoreCut row col)

namespace ShoreCut

/-- Occurrences of the factor `H₁`: those with row in `S₁`. -/
abbrev E₁ := {e : E // K.sR (row e)}
/-- Occurrences of the factor `H₂`: those with column in `S₂`. -/
abbrev E₂ := {e : E // ¬ K.sC (col e)}
/-- Rows of `S₁`. -/
abbrev U₁ := {u : U // K.sR u}
/-- Columns of `S₁`. -/
abbrev V₁ := {v : V // K.sC v}
/-- Rows of `S₂`. -/
abbrev U₂ := {u : U // ¬ K.sR u}
/-- Columns of `S₂`. -/
abbrev V₂ := {v : V // ¬ K.sC v}

/-- Rows of `H₁`. -/
def row₁ (e : K.E₁) : K.U₁ := ⟨row e.1, e.2⟩

/-- Columns of `H₁`; a crossing occurrence goes to the marker column. -/
def col₁ (e : K.E₁) : K.V₁ ⊕ Unit :=
  if h : K.sC (col e.1) then Sum.inl ⟨col e.1, h⟩ else Sum.inr ()

/-- Rows of `H₂`; a crossing occurrence comes from the marker row. -/
def row₂ (e : K.E₂) : Unit ⊕ K.U₂ :=
  if h : K.sR (row e.1) then Sum.inl () else Sum.inr ⟨row e.1, h⟩

/-- Columns of `H₂`. -/
def col₂ (e : K.E₂) : K.V₂ := ⟨col e.1, e.2⟩

/-- An occurrence crosses the cut: row in `S₁`, column in `S₂`. -/
def Crossing (e : E) : Prop := K.sR (row e) ∧ ¬ K.sC (col e)

instance : DecidablePred K.Crossing := fun _ => by unfold Crossing; infer_instance

theorem col₁_eq_inr_iff (e : K.E₁) : K.col₁ e = Sum.inr () ↔ ¬ K.sC (col e.1) := by
  unfold col₁
  split_ifs with h <;> simp [h]

theorem col_of_col₁_eq_inl {e : K.E₁} {v : K.V₁} (h : K.col₁ e = Sum.inl v) : col e.1 = v.1 := by
  unfold col₁ at h
  split_ifs at h with h'
  · exact congrArg Subtype.val (Sum.inl.inj h)

theorem col₁_congr {e e' : K.E₁} (h : col e.1 = col e'.1) : K.col₁ e = K.col₁ e' := by
  unfold col₁
  by_cases h₁ : K.sC (col e.1)
  · have h₂ : K.sC (col e'.1) := h ▸ h₁
    rw [dite_eq_left h₁, dite_eq_left h₂]
    exact congrArg Sum.inl (Subtype.ext h)
  · have h₂ : ¬ K.sC (col e'.1) := h ▸ h₁
    rw [dite_eq_right h₁, dite_eq_right h₂]

theorem row₂_of_sR {e : K.E₂} (h : K.sR (row e.1)) : K.row₂ e = Sum.inl () := by
  unfold row₂; rw [dite_eq_left h]

theorem row₂_of_not_sR {e : K.E₂} (h : ¬ K.sR (row e.1)) : K.row₂ e = Sum.inr ⟨row e.1, h⟩ := by
  unfold row₂; rw [dite_eq_right h]

theorem row_of_row₂_eq_inr {e : K.E₂} {u : K.U₂} (h : K.row₂ e = Sum.inr u) : row e.1 = u.1 := by
  unfold row₂ at h
  split_ifs at h with h'
  · exact congrArg Subtype.val (Sum.inr.inj h)

/-! ### Projecting a parent matching to the first factor -/

theorem proj₁_bij (M : LMatch row col) :
    Function.Bijective fun u : K.U₁ => K.col₁ ⟨M.1 u.1, by rw [M.2.1]; exact u.2⟩ := by
  rw [Fintype.bijective_iff_surjective_and_card]
  refine ⟨?_, by rw [Fintype.card_sum, Fintype.card_unit, K.card]⟩
  intro o
  cases o with
  | inr t =>
    by_contra hno
    push Not at hno
    have hs : ∀ u : K.U₁, K.sC (col (M.1 u.1)) := by
      intro u
      by_contra hc
      exact hno u (by cases t; exact (K.col₁_eq_inr_iff _).2 hc)
    have hinj : Function.Injective fun u : K.U₁ => (⟨col (M.1 u.1), hs u⟩ : K.V₁) := by
      intro u u' h
      exact Subtype.ext (M.2.2.1 (Subtype.ext_iff.1 h))
    have := Fintype.card_le_of_injective _ hinj
    rw [K.card] at this
    omega
  | inl v =>
    obtain ⟨u, hu⟩ := M.2.2.2 v.1
    have hu : col (M.1 u) = v.1 := hu
    have hsu : K.sR u := by
      have := K.back (M.1 u) (by rw [hu]; exact v.2)
      rwa [M.2.1] at this
    refine ⟨⟨u, hsu⟩, ?_⟩
    have hv : K.sC (col (M.1 u)) := by rw [hu]; exact v.2
    show K.col₁ ⟨M.1 u, _⟩ = Sum.inl v
    unfold col₁
    rw [dite_eq_left hv]
    exact congrArg Sum.inl (Subtype.ext hu)

/-- The projection of a parent matching to `H₁`. -/
def proj₁ (M : LMatch row col) : LMatch K.row₁ K.col₁ :=
  ⟨fun u => ⟨M.1 u.1, by rw [M.2.1]; exact u.2⟩, fun u => Subtype.ext (M.2.1 u.1), K.proj₁_bij M⟩

theorem proj₁_val (M : LMatch row col) (u : K.U₁) : ((K.proj₁ M).1 u).1 = M.1 u.1 := rfl

/-! ### The crossing label of a factor matching -/

/-- The row of `H₁` matched to the marker column. -/
noncomputable def markRow₁ (M₁ : LMatch K.row₁ K.col₁) : K.U₁ :=
  (Equiv.ofBijective _ M₁.2.2).symm (Sum.inr ())

/-- The crossing label chosen by a matching of `H₁`. -/
noncomputable def label₁ (M₁ : LMatch K.row₁ K.col₁) : E := (M₁.1 (K.markRow₁ M₁)).1

/-- The crossing label chosen by a matching of `H₂`. -/
def label₂ (M₂ : LMatch K.row₂ K.col₂) : E := (M₂.1 (Sum.inl ())).1

theorem col₁_markRow₁ (M₁ : LMatch K.row₁ K.col₁) :
    K.col₁ (M₁.1 (K.markRow₁ M₁)) = Sum.inr () :=
  Equiv.ofBijective_apply_symm_apply _ M₁.2.2 _

theorem eq_markRow₁ {M₁ : LMatch K.row₁ K.col₁} {u : K.U₁}
    (h : K.col₁ (M₁.1 u) = Sum.inr ()) : u = K.markRow₁ M₁ :=
  M₁.2.2.1 (h.trans (K.col₁_markRow₁ M₁).symm)

theorem label₁_crossing (M₁ : LMatch K.row₁ K.col₁) : K.Crossing (K.label₁ M₁) :=
  ⟨(M₁.1 _).2, (K.col₁_eq_inr_iff _).1 (K.col₁_markRow₁ M₁)⟩

theorem label₂_crossing (M₂ : LMatch K.row₂ K.col₂) : K.Crossing (K.label₂ M₂) := by
  refine ⟨?_, (M₂.1 _).2⟩
  by_contra h
  have := M₂.2.1 (Sum.inl ())
  rw [K.row₂_of_not_sR h] at this
  exact Sum.inr_ne_inl this

theorem label₁_eq_iff (M₁ : LMatch K.row₁ K.col₁) {c : E} (hc : K.Crossing c) :
    K.label₁ M₁ = c ↔ M₁.1 (K.row₁ ⟨c, hc.1⟩) = ⟨c, hc.1⟩ := by
  constructor
  · intro h
    have hm : M₁.1 (K.markRow₁ M₁) = ⟨c, hc.1⟩ := Subtype.ext h
    have hr : K.row₁ ⟨c, hc.1⟩ = K.markRow₁ M₁ := by rw [← hm]; exact M₁.2.1 _
    rw [hr, hm]
  · intro h
    have hr : K.row₁ ⟨c, hc.1⟩ = K.markRow₁ M₁ :=
      K.eq_markRow₁ (by rw [h]; exact (K.col₁_eq_inr_iff _).2 hc.2)
    unfold label₁
    rw [← hr, h]

theorem label₂_eq_iff (M₂ : LMatch K.row₂ K.col₂) {c : E} (hc : K.Crossing c) :
    K.label₂ M₂ = c ↔ M₂.1 (K.row₂ ⟨c, hc.2⟩) = ⟨c, hc.2⟩ := by
  rw [K.row₂_of_sR hc.1, label₂]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

/-! ### Projecting a parent matching to the second factor -/

/-- The crossing label of a parent matching. -/
noncomputable def label (M : LMatch row col) : E := K.label₁ (K.proj₁ M)

theorem not_sC_of_not_sR (M : LMatch row col) (u : K.U₂) : ¬ K.sC (col (M.1 u.1)) := by
  intro h
  have := K.back _ h
  rw [M.2.1] at this
  exact u.2 this

/-- The function underlying the projection to `H₂`. -/
noncomputable def proj₂Fun (M : LMatch row col) : Unit ⊕ K.U₂ → K.E₂
  | Sum.inl _ => ⟨K.label M, (K.label₁_crossing _).2⟩
  | Sum.inr u => ⟨M.1 u.1, K.not_sC_of_not_sR M u⟩

theorem label_eq (M : LMatch row col) : K.label M = M.1 (K.markRow₁ (K.proj₁ M)).1 := rfl

theorem proj₂_bij (M : LMatch row col) :
    Function.Bijective fun r => K.col₂ (K.proj₂Fun M r) := by
  constructor
  · intro r r' h
    have hc : col (K.proj₂Fun M r).1 = col (K.proj₂Fun M r').1 := Subtype.ext_iff.1 h
    have key : ∀ u : K.U₂, col (K.label M) = col (M.1 u.1) → False := by
      intro u hu
      rw [K.label_eq] at hu
      have := M.2.2.1 hu
      exact u.2 (this ▸ (K.markRow₁ (K.proj₁ M)).2)
    cases r with
    | inl t =>
      cases r' with
      | inl t' => cases t; cases t'; rfl
      | inr u' => exact (key u' hc).elim
    | inr u =>
      cases r' with
      | inl t' => exact (key u hc.symm).elim
      | inr u' => exact congrArg Sum.inr (Subtype.ext (M.2.2.1 hc))
  · intro v
    obtain ⟨u, hu⟩ := M.2.2.2 v.1
    have hu : col (M.1 u) = v.1 := hu
    by_cases hs : K.sR u
    · refine ⟨Sum.inl (), Subtype.ext ?_⟩
      have hm : (⟨u, hs⟩ : K.U₁) = K.markRow₁ (K.proj₁ M) := by
        apply K.eq_markRow₁
        rw [K.col₁_eq_inr_iff]
        show ¬ K.sC (col (M.1 u))
        rw [hu]; exact v.2
      show col (K.label M) = v.1
      rw [K.label_eq, ← hm]
      exact hu
    · exact ⟨Sum.inr ⟨u, hs⟩, Subtype.ext hu⟩

theorem proj₂_row (M : LMatch row col) (r : Unit ⊕ K.U₂) : K.row₂ (K.proj₂Fun M r) = r := by
  cases r with
  | inl t => cases t; exact K.row₂_of_sR (K.label₁_crossing _).1
  | inr u =>
    show K.row₂ ⟨M.1 u.1, _⟩ = _
    have h : ¬ K.sR (row (M.1 u.1)) := by rw [M.2.1]; exact u.2
    rw [K.row₂_of_not_sR h]
    exact congrArg Sum.inr (Subtype.ext (M.2.1 u.1))

/-- The projection of a parent matching to `H₂`. -/
noncomputable def proj₂ (M : LMatch row col) : LMatch K.row₂ K.col₂ :=
  ⟨K.proj₂Fun M, K.proj₂_row M, K.proj₂_bij M⟩

theorem label₂_proj₂ (M : LMatch row col) : K.label₂ (K.proj₂ M) = K.label₁ (K.proj₁ M) := rfl

/-! ### Gluing factor matchings that share a label -/

/-- The function underlying the glued matching. -/
def glueFun (M₁ : LMatch K.row₁ K.col₁) (M₂ : LMatch K.row₂ K.col₂) (u : U) : E :=
  if h : K.sR u then (M₁.1 ⟨u, h⟩).1 else (M₂.1 (Sum.inr ⟨u, h⟩)).1

theorem glueFun_row (M₁ : LMatch K.row₁ K.col₁) (M₂ : LMatch K.row₂ K.col₂) (u : U) :
    row (K.glueFun M₁ M₂ u) = u := by
  unfold glueFun
  split_ifs with h
  · exact congrArg Subtype.val (M₁.2.1 ⟨u, h⟩)
  · exact K.row_of_row₂_eq_inr (M₂.2.1 _)

theorem glueFun_bij (M₁ : LMatch K.row₁ K.col₁) (M₂ : LMatch K.row₂ K.col₂)
    (h : K.label₁ M₁ = K.label₂ M₂) :
    Function.Bijective fun u => col (K.glueFun M₁ M₂ u) := by
  -- a row of `S₁` and a row of `S₂` never share a column
  have mixed : ∀ (u : K.U₁) (u' : K.U₂), col (M₁.1 u).1 = col (M₂.1 (Sum.inr u')).1 → False := by
    intro u u' hc
    have hnot : ¬ K.sC (col (M₁.1 u).1) := by rw [hc]; exact (M₂.1 _).2
    have hu : u = K.markRow₁ M₁ := K.eq_markRow₁ ((K.col₁_eq_inr_iff _).2 hnot)
    have hlab : (M₁.1 u).1 = (M₂.1 (Sum.inl ())).1 := by
      rw [hu]; exact h
    have h2 : K.col₂ (M₂.1 (Sum.inl ())) = K.col₂ (M₂.1 (Sum.inr u')) :=
      Subtype.ext (by show col _ = col _; rw [← hlab]; exact hc)
    exact Sum.inl_ne_inr (M₂.2.2.1 h2)
  constructor
  · intro u u' hc
    simp only [glueFun] at hc
    by_cases hu : K.sR u <;> by_cases hu' : K.sR u'
    · rw [dite_eq_left hu, dite_eq_left hu'] at hc
      have := M₁.2.2.1 (K.col₁_congr hc)
      exact congrArg Subtype.val this
    · rw [dite_eq_left hu, dite_eq_right hu'] at hc
      exact (mixed _ _ hc).elim
    · rw [dite_eq_right hu, dite_eq_left hu'] at hc
      exact (mixed _ _ hc.symm).elim
    · rw [dite_eq_right hu, dite_eq_right hu'] at hc
      have := M₂.2.2.1 (Subtype.ext hc : K.col₂ (M₂.1 _) = K.col₂ (M₂.1 _))
      exact congrArg Subtype.val (Sum.inr.inj this)
  · intro v
    by_cases hv : K.sC v
    · obtain ⟨w, hw⟩ := M₁.2.2.2 (Sum.inl ⟨v, hv⟩)
      refine ⟨w.1, ?_⟩
      show col (K.glueFun M₁ M₂ w.1) = v
      unfold glueFun
      rw [dite_eq_left w.2]
      exact K.col_of_col₁_eq_inl hw
    · obtain ⟨r, hr⟩ := M₂.2.2.2 ⟨v, hv⟩
      have hr' : col (M₂.1 r).1 = v := Subtype.ext_iff.1 hr
      cases r with
      | inr w =>
        refine ⟨w.1, ?_⟩
        show col (K.glueFun M₁ M₂ w.1) = v
        unfold glueFun
        rw [dite_eq_right w.2]
        exact hr'
      | inl t =>
        cases t
        refine ⟨(K.markRow₁ M₁).1, ?_⟩
        show col (K.glueFun M₁ M₂ (K.markRow₁ M₁).1) = v
        unfold glueFun
        rw [dite_eq_left (K.markRow₁ M₁).2]
        have : (M₁.1 ⟨(K.markRow₁ M₁).1, (K.markRow₁ M₁).2⟩).1 = (M₂.1 (Sum.inl ())).1 := h
        rw [this]
        exact hr'

/-- The parent matching glued from two factor matchings with a common label. -/
def glue (M₁ : LMatch K.row₁ K.col₁) (M₂ : LMatch K.row₂ K.col₂)
    (h : K.label₁ M₁ = K.label₂ M₂) : LMatch row col :=
  ⟨K.glueFun M₁ M₂, K.glueFun_row M₁ M₂, K.glueFun_bij M₁ M₂ h⟩

theorem proj₁_glue (M₁ : LMatch K.row₁ K.col₁) (M₂ : LMatch K.row₂ K.col₂)
    (h : K.label₁ M₁ = K.label₂ M₂) : K.proj₁ (K.glue M₁ M₂ h) = M₁ := by
  refine Subtype.ext (funext fun u => Subtype.ext ?_)
  show K.glueFun M₁ M₂ u.1 = (M₁.1 u).1
  unfold glueFun
  rw [dite_eq_left u.2]

theorem proj₂_glue (M₁ : LMatch K.row₁ K.col₁) (M₂ : LMatch K.row₂ K.col₂)
    (h : K.label₁ M₁ = K.label₂ M₂) : K.proj₂ (K.glue M₁ M₂ h) = M₂ := by
  refine Subtype.ext (funext fun r => Subtype.ext ?_)
  cases r with
  | inl t =>
    cases t
    show K.label₁ (K.proj₁ (K.glue M₁ M₂ h)) = (M₂.1 (Sum.inl ())).1
    rw [K.proj₁_glue]
    exact h
  | inr u =>
    show K.glueFun M₁ M₂ u.1 = (M₂.1 (Sum.inr u)).1
    unfold glueFun
    rw [dite_eq_right u.2]

theorem glue_proj (M : LMatch row col) : K.glue (K.proj₁ M) (K.proj₂ M) rfl = M := by
  refine Subtype.ext (funext fun u => ?_)
  show K.glueFun (K.proj₁ M) (K.proj₂ M) u = M.1 u
  unfold glueFun
  split_ifs with h
  · rfl
  · rfl

/-- **Matchings glue exactly when they choose the same crossing label.**
Sums over parent matchings are sums over label-compatible factor pairs. -/
theorem sum_lmatch_eq_sum_pairs {β : Type*} [AddCommMonoid β]
    (F : LMatch K.row₁ K.col₁ → LMatch K.row₂ K.col₂ → β) :
    ∑ M : LMatch row col, F (K.proj₁ M) (K.proj₂ M) =
      ∑ M₁, ∑ M₂ ∈ (univ : Finset _).filter (fun M₂ => K.label₂ M₂ = K.label₁ M₁), F M₁ M₂ := by
  rw [Finset.sum_sigma']
  refine Finset.sum_bij' (fun M _ => ⟨K.proj₁ M, K.proj₂ M⟩)
    (fun p hp => K.glue p.1 p.2 ((Finset.mem_filter.1 (Finset.mem_sigma.1 hp).2).2).symm)
    ?_ ?_ ?_ ?_ ?_
  · intro M _
    exact Finset.mem_sigma.2 ⟨mem_univ _, Finset.mem_filter.2 ⟨mem_univ _, rfl⟩⟩
  · intro p _
    exact mem_univ _
  · intro M _
    exact K.glue_proj M
  · rintro ⟨M₁, M₂⟩ hp
    simp only [K.proj₁_glue, K.proj₂_glue]
  · intro M _
    rfl

/-- The same sum, grouped by the second factor. -/
theorem sum_lmatch_eq_sum_pairs' {β : Type*} [AddCommMonoid β]
    (F : LMatch K.row₁ K.col₁ → LMatch K.row₂ K.col₂ → β) :
    ∑ M : LMatch row col, F (K.proj₁ M) (K.proj₂ M) =
      ∑ M₂, ∑ M₁ ∈ (univ : Finset _).filter (fun M₁ => K.label₁ M₁ = K.label₂ M₂), F M₁ M₂ := by
  rw [sum_lmatch_eq_sum_pairs]
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun M₂ _ => Finset.sum_congr rfl fun M₁ _ => ?_
  simp only [eq_comm]

/-- **Lavi (4.1):** the orders satisfy `h = m₁ + m₂ - 1`. -/
theorem lavi_eq_4_1 :
    Fintype.card U + 1 = Fintype.card K.U₁ + Fintype.card (Unit ⊕ K.U₂) := by
  rw [Fintype.card_sum, Fintype.card_unit]
  have h := Fintype.card_subtype_compl K.sR
  have h2 := Fintype.card_subtype_le K.sR
  change Fintype.card U + 1 = Fintype.card {u // K.sR u} + (1 + Fintype.card {u // ¬ K.sR u})
  omega

end ShoreCut

end TightCut

end LaviSection2
