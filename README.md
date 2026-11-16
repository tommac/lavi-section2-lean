# Lean 4 formalization of Lavi's proof of Foregger's conjecture

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24254583.svg)](https://doi.org/10.5281/zenodo.24254583)
[![Lean build](https://github.com/tommac/lavi-section2-lean/actions/workflows/lean.yml/badge.svg)](https://github.com/tommac/lavi-section2-lean/actions/workflows/lean.yml)

This is a machine-checked Lean 4 / Mathlib formalization of **Sections 2–7** of

> Yair Lavi, *Foregger's Conjecture on Minimum Permanents of Nearly
> Decomposable Doubly Stochastic Matrices*, preprint, 4 November 2026
> (v1, [doi:10.5281/zenodo.23957650](https://doi.org/10.5281/zenodo.23957650));
> revised 13 November 2026
> (v2, [doi:10.5281/zenodo.24208987](https://doi.org/10.5281/zenodo.24208987)).

It ends with the paper's **Theorem 1.1 (Foregger's conjecture)**, proved in Lean
with no hypotheses beyond the theorem's own. Gurvits's degree-sensitive capacity
inequality, which the proof uses in Section 5 and which version 1.2.0 of this
repository assumed, is now proved as well. That proof builds on the Lean
formalization of Gurvits's stable-polynomial argument in the
[RealRooted](https://github.com/PerAlexandersson/RealRooted) library.

The mathematics is Lavi's (Lemmas 2.1 and 2.2 go back to Foregger, and the
capacity inequality is Gurvits's). The Lean formalization of Gurvits's argument
is RealRooted's (Per Alexandersson and contributors). This repository
contributes the formalization of Lavi's proof, the degree-sensitive form of the
capacity inequality and its translation to matrices, and the simplifications
and sharpenings listed below that came up while writing it.

## Status: what this does and does not establish

- **The main theorem** is in `LaviTheorem11Unconditional.lean`:

  ```lean
  theorem foregger_conjecture {n : ℕ} (hn : 2 ≤ n) {A : Square n}
      (hA : DoublyStochastic A) (hND : NearlyDecomposable (support A)) :
      (2 : ℝ) ^ ((1 : ℤ) - (n : ℤ)) ≤ permanent A ∧
        (permanent A = (2 : ℝ) ^ ((1 : ℤ) - (n : ℤ)) ↔
          ∃ σ τ : Equiv.Perm (Fin n), ∀ i j, A i j = halfCycleMatrix n (σ i) (τ j))
  ```

  Here `halfCycleMatrix n = (1/2) • (1 + (finRotate n).permMatrix ℝ)` is the
  paper's `½(I_n + P_n)`, with `P_n` the permutation matrix of an `n`-cycle.
  - The same statement is `lavi_theorem_1_1_unconditional`, and the
    inequality alone is `foregger_bound`.
  - `lavi_theorem_1_1_moreover_unconditional` is the paper's "Moreover" clause.
    For a nearly decomposable support that is not a cycle support (not both
    connected and 2-regular), the minimum of the permanent on the face `Ω(D)`
    is attained and is strictly larger than `2^(1−n)`.
  - `lavi_theorem_1_1_attained` shows that `½(I_n + P_n)` satisfies the matrix
    hypotheses and attains the bound in every order `n ≥ 2`.
- **Gurvits's inequality.** `GurvitsCapacityInequality` (in
  `LaviOneStarCapacity.lean`) is the paper's (5.5). For every nonnegative
  `n × n` matrix `M` with `Δ_j` nonzero entries in column `j`, it states
  `per M ≥ Cap(M) · ∏_{j=1}^{n} g(min(Δ_j, j))`.
  - This is L. Gurvits, Electron. J. Combin. 15 (2008), Theorem 2.4 and
    Corollary 2.7(a). It is stated in exactly this form by M. Laurent and
    A. Schrijver, Amer. Math. Monthly 117 (2010), Corollary 1a (eq. (32),
    p. 908).
  - It enters through Lemma 5.1, and Corollary 5.2, (6.1) and Theorem 1.1
    inherit it. Their Lean versions take it as an explicit hypothesis `hG`
    (`lavi_theorem_1_1` and `lavi_theorem_1_1_moreover` in
    `LaviTheorem11.lean` are the versions with `hG`).
  - `GurvitsRealRooted.lean` proves it as `gurvitsCapacityInequality`.
    - RealRooted proves the step `g(k+1) · Cap(p) ≤ Cap(∂p/∂x₀|_{x₀=0})` for
      real stable `p` with nonnegative coefficients and total degree at most
      `k + 1`.
    - Gurvits's degree-sensitive step replaces `k + 1` by the degree of `p` in
      `x₀`. RealRooted's proof gives it unchanged, once the degree of the
      one-variable restriction is bounded by `degreeOf 0 p`.
    - Iterating the step with a separate cap for each variable gives Gurvits's
      Theorem 2.4.
    - It is applied to `∏_i ∑_v M_{i, rev v} x_v`, with the columns in reverse
      order. Then the column with 0-based index `j` is eliminated when `j + 1`
      variables remain, which gives the cap `min(Δ_j, j)` in the paper's
      1-based indexing.
- **What the proof relies on:**
  - Lean's kernel with its three standard axioms (`propext`,
    `Classical.choice`, `Quot.sound`);
  - Mathlib `v4.35.0`;
  - RealRooted at commit `d667074269bb822fa18ca9142a14fdd90734dd57`, of which
    55 modules are imported.

  RealRooted is used only inside proofs. None of its definitions occur in the
  statements above. This repository contains no `sorry`, `admit`, `axiom` or
  `native_decide`.
- **Checks:**
  - `AxiomAudit.lean` prints the axioms of 79 theorems, including every
    theorem in the table below. `scripts/check_axioms.py` fails unless each
    one reports only the three standard axioms.
  - `scripts/kernel_check.sh` exports the dependency closure of the final
    theorems, Mathlib and RealRooted included. It re-checks that export with
    nanoda, an independent Lean type checker written in Rust, which allows
    only the standard axioms.
  - CI runs both checks on every push. On release tags it also replays the
    whole environment in a fresh kernel (`leanchecker --fresh`).
  - Before this release, the final theorems were also re-checked with
    `leanchecker --fresh`, lean4lean and con-leche. Their axioms were also
    collected by walking the proof terms directly, without the axiom lists
    stored in the compiled files.
- **Review status:**
  - The final statements and every definition they use were compared with
    the paper and found faithful for `n ≥ 2`.
  - The statements have not yet been reviewed by a second person.
  - Line numbers quoted in some docstrings refer to a plain-text extraction of
    v2 of the preprint.
- **Conventions:** Theorem 1.1 is for `n ≥ 2`, as in the paper. With these
  definitions the only nearly decomposable support of order one is the empty
  one, not the paper's singleton. Order one is therefore vacuous, so
  `foreggerSharpAt_all : ∀ n, ForeggerSharpAt n` says nothing about `n < 2`.

## Lemma map

The table lists the lemmas and numbered identities that are formalized as
separate theorems. Not every display of the paper has its own theorem.

| Lavi (2026) | Lean theorem | File |
|---|---|---|
| Lemma 2.1, cofactor equalities (2.1) | `faceMinimizer_cofactor_eq` | `LaviCofactorEqualization.lean` |
| Lemma 2.1, the support of a face minimizer is FI | `lavi_lemma_2_1` | `LaviMinimizerSupport.lean` |
| Lemma 2.1 on an ND face: the support is exactly `D` | `faceMinimizer_support_eq_of_nearlyDecomposable` | `LaviMinimizerSupport.lean` |
| Lemma 2.2, Foregger's contraction identity | `permanent_contractMatrix`; `faceMinimizer_contraction` (columns, no FI needed); `faceMinimizer_row_contraction_nd` (rows, with ND hypotheses) | `LaviContractionIdentity.lean`, `LaviCofactorEqualization.lean`, `LaviContractionBranch.lean` |
| Lemma 2.3, no four-cycles | `nearlyDecomposable_no_fourCycle`, `nearlyDecomposable_common_neighbor_unique` | `LaviNoFourCycles.lean` |
| Lemma 2.4, the two contraction mechanisms (column and row) | `lavi_lemma_2_4_column`, `lavi_lemma_2_4_row` | `LaviContractionND.lean` |
| Lemma 2.5, terminal ND supports are `D_can(H)` | `lavi_lemma_2_5`, `lavi_lemma_2_5_univ` | `LaviLemma25.lean`, `LaviTerminalBridge.lean` |
| Lemma 2.5, `D_can(H)` is ND (for cores with at least two occurrences in every column) | `nearlyDecomposableOn_canonicalAdj` | `LaviCanonicalExpansion.lean` |
| Lemma 2.5, private-line contractions are FI but not ND | `privateContraction_canonical`, `privateRowContraction_canonical` | `LaviCanonicalExpansion.lean` |
| Cycle supports: `per A ≥ 2^(1−n)`, equality only at `½(I + P)` | `cycleSupported_foregger_sharp` | `LaviCycleFace.lean` |
| Lemma 3.1, `log per Y ≤ F(X) ≤ log per X` on a face, equality at the minimizer | `lavi_lemma_3_1`, `faceFunctional_le_log_permanent` | `LaviFaceVariational.lean` |
| Lemma 3.2, merging parallel occurrences preserves `F_H` | `lavi_lemma_3_2` | `LaviCoreEntropy.lean` |
| `F_H(x)` of a complete core equals the matrix functional `F` | `coreFunctional_eq_faceFunctional` | `LaviCoreEntropy.lean` |
| (3.5), `F_{D(H,L)}(X_x) = F_H(x) − Σ_{ℓ∈L} h₂(x_ℓ)` | `lavi_eq_3_5` | `LaviExpansionEntropy.lean` |
| The subdivision charge `δ = log 2 − h₂ ≥ 0` (stated before (3.6)) | `subdivCharge_nonneg` | `LaviExpansionEntropy.lean` |
| (3.6), the normalized gap `G_{H,L}`; (3.7), `G_{H,L} = F_{D(H,L)}(X_x) + (n − 1) log 2` | `normalizedGap`, `lavi_eq_3_7` | `LaviExpansionEntropy.lean` |
| Section 4, a tight cut is oriented (given `hcov` and a matching `M₀`; `exists_shoreCut_of_tight` also takes balance) | `tightCut_orientation`, `exists_shoreCut_of_tight` | `LaviTightCutOrientation.lean` |
| Section 4, matchings glue along the crossing label; (4.1) | `ShoreCut.sum_lmatch_eq_sum_pairs`, `ShoreCut.lavi_eq_4_1` | `LaviTightCut.lean` |
| Lemma 4.1, (4.2): `F_H = F_{H₁} + F_{H₂}` | `ShoreCut.lavi_lemma_4_1` | `LaviTightCutEntropy.lean` |
| Lemma 4.1, internal occurrences are not removable (FI core) | `ShoreCut.removable_internal₁`, `ShoreCut.removable_internal₂` | `LaviTightCutFI.lean` |
| Lemma 4.1, (4.3): removability across the cut | `ShoreCut.coreFI_cut_iff`, `ShoreCut.lavi_eq_4_3` | `LaviTightCutFI.lean` |
| (4.4), (4.5), for either choice of leaf | `ShoreCut.lavi_eq_4_4`, `ShoreCut.lavi_eq_4_5` and primed versions | `LaviTightCutAccounting.lean` |
| (5.2), `per A = per M` | `permanent_expandedMatrix_eq_elim` | `LaviOneStarPermanent.lean` |
| (5.3)–(5.4), capacity bound, combined with the concavity step of line 573; the inequality of (5.6) | `capacity_elim_ge`, `sum_colCount_le` | `LaviOneStarCapacity.lean` |
| (5.5), Gurvits's capacity inequality | `gurvitsCapacityInequality` | `GurvitsRealRooted.lean` |
| (5.7), (5.10), the factors `A_d`, `C_d` | `rowFactor_secant`, `colFactor_secant` | `LaviOneStarConstants.lean` |
| Lemma 5.1, one-star bound at a root row (given `hG`) | `lavi_lemma_5_1` | `LaviOneStar.lean` |
| Corollary 5.2, row and column versions (given `hG`) | `lavi_corollary_5_2`, `lavi_corollary_5_2_col` | `LaviOneStar.lean`, `LaviLeafGap.lean` |
| Lemma 6.1, cut-free cores | `lavi_lemma_6_1` | `LaviCutFree.lean` |
| Lemma 6.2, the closure of a minimum shore is a leaf (given `hcov`, balance and `[Nonempty E]` in place of FI) | `ShoreCut.cutFree₁`, `ShoreCut.cutFree₂`, with the degree clause `ShoreCut.card_rowSet₁`, `card_colSet₁`, `card_rowSet₂`, `card_colSet₂`; the existential form used in Section 7 is `lavi_lemma_6_2` | `LaviMinShore.lean` |
| (6.1), leaf gap (given `hG`) | `ShoreCut.lavi_eq_6_1` and primed version | `LaviLeafGap.lean` |
| Lemma 6.3, four-vertex leaf; (6.5) | `ShoreCut.lavi_lemma_6_3`, `ShoreCut.lavi_eq_6_5` and primed versions | `LaviFourVertexLeaf.lean` |
| Section 7, contraction branch (7.1), given the induction hypothesis | `contraction_branch_column`, `contraction_branch_row` | `LaviContractionBranch.lean` |
| Section 7, order-one terminal cores, (7.2) | `lavi_eq_7_2` | `LaviTerminalBranch.lean` |
| Section 7, terminal branch is strict, given `hG` and the induction hypothesis | `terminal_branch_strict` | `LaviTerminalBranch.lean` |
| Section 7, equality forces a half cycle | `isHalfCycle_of_not_terminal`, from `isHalfCycle_of_half_entries` and `half_entries_of_contractMatrix` | `LaviEqualityCase.lean` |
| Section 7, the induction, given strictness on terminal supports | `foreggerSharpAt_of_terminal_strict` | `LaviInduction.lean` |
| Theorem 1.1 with the hypothesis `hG` | `lavi_theorem_1_1`, `lavi_theorem_1_1_moreover` | `LaviTheorem11.lean` |
| The bound is attained in every order `n ≥ 2` | `lavi_theorem_1_1_attained` | `LaviTheorem11.lean` |
| **Theorem 1.1 (Foregger's conjecture)** | `foregger_conjecture` (= `lavi_theorem_1_1_unconditional`), `lavi_theorem_1_1_moreover_unconditional`, `foregger_bound` | `LaviTheorem11Unconditional.lean` |

Basic definitions (permanent, doubly stochastic, support, fully
indecomposable, nearly decomposable) are in `Definitions.lean`. The
strict-Hall characterization of full indecomposability is derived in
`LaviStrictHall.lean`. Laws on permutations, matching entropy and the Gibbs
law are in `LaviMatchingEntropy.lean`. `Transpose.lean`,
`RelabelInvariance.lean` and `Arithmetic.lean` hold small supporting facts.
The polynomial lemmas behind `gurvitsCapacityInequality` are in the
`LaviGurvits` namespace of `GurvitsRealRooted.lean`.

## Differences from the text

- **Lemma 2.1:** the cofactor equalities hold at a permanent minimizer on any
  face `Ω(D)`, with no connectivity hypothesis. The proof perturbs along
  `X_ij = a_ij (per A(i|j) − per A)`.
- **Lemma 2.4:** proved by an expansion lemma. Splitting the merged line back
  preserves the strict Hall inequalities, and Lemma 2.3 finishes the argument.
  This replaces the scaling and tight-set argument in the text.
- **Lemma 2.5:**
  - The classification is proved for every terminal ND support of order
    `n ≥ 3`, without the "noncycle" hypothesis. A cycle of order at least
    three is never terminal, by Lemma 2.4 (`IsCycleSupport.not_terminal`), so
    cycle supports go through the contraction branch of Section 7.
  - The converse ("`D_can(H)` is ND") is stated for supports of order at least
    two, which excludes the degenerate order-one core with a single
    occurrence. It also assumes at least two occurrences in every column; for
    FI cores of order at least two this holds (`colOcc_two_of_coreFI`).
- **Lemma 3.1:** the lower bound is proved by minimizing
  `log per W − Σ x_ij log w_ij` over a compact sub-face, showing that the
  minimizer is interior, and perturbing along the difference between its Gibbs
  marginals and `X`. This avoids maximizer positivity, Lagrange multipliers and
  Sinkhorn scaling.
- **Lemma 3.2:** proved for an arbitrary endpoint-preserving merge map (any
  number of bundles at once), by comparing a law with its push-forward and with
  an independent relabelling lift. No entropy chain rule or concavity is used.
- **Section 3 encoding:**
  - `F` is defined with laws on all permutations (they charge only `supp X`,
    so this matches the text), and `Ent*` is a supremum.
  - In (3.5), `X_x` is defined as the aggregated flow of the expanded core:
    direct entries sum their parallel flows, and each long occurrence becomes a
    path carrying `(x, 1 − x, x)`.
  - A feasible flow is encoded as the existence of a law,
    `∃ μ, IsCoreLaw row col x μ`. On balanced cores this is equivalent to
    (3.1), by `exists_isCoreLaw_of_feasible`, `IsCoreLaw.rowSet_sum` and
    `IsCoreLaw.colSet_sum`.
- **Section 4:**
  - A cut is recorded in the oriented form that tightness forces: one extra row
    on a shore, and no occurrence entering its columns.
  - The orientation lemmas take `hcov`, "every occurrence lies in a perfect
    matching", in place of FI. FI ⇒ `hcov` is not formalized; Section 7
    obtains `hcov` from a positive law (`covered_of_positive_flow`).
  - Lemma 4.1's entropy identity is proved by projection and a Gibbs
    comparison with the glued law, with no conditional entropy.
  - The removability rule (4.3) is a strict-Hall computation in place of the
    2-connectivity argument.
- **Section 5:**
  - The secant bounds (5.10) are proved with Bernoulli's inequality instead of
    convexity.
  - Full indecomposability of the core is not needed for Lemma 5.1. The lemma
    is stated with a root row; the column form is used only through
    Corollary 5.2 (`lavi_corollary_5_2_col`, by transposition).
  - `capacity_elim_ge` is (5.4) after the concavity step of line 573: it is
    weaker than (5.4), does not depend on the flow, and also asks the root row
    to carry at least two occurrences.
- **Gurvits's inequality:** the degree-sensitive step and its iteration adapt
  RealRooted's proofs, as described above and in the header of
  `GurvitsRealRooted.lean`.
- **Section 6:** Lemma 6.2 is proved by transporting the orientation of a
  tight shore of the factor to the parent. It takes `hcov`, balance and
  `[Nonempty E]` in place of FI (FI ⇒ `hcov` is not formalized). In Section 7
  `hcov` comes from a positive feasible flow.
- **Section 7:**
  - The equality case carries "all entries are 0 or 1/2" back through the
    contraction with Lemma 2.3, where the text counts edges.
  - Minc's edge bound is not used: the case split is on whether the support is
    terminal.
  - With these definitions the order-one nearly decomposable support is the
    empty one, not the singleton of the paper's convention. Order one is
    therefore vacuous and order two is a base case. Theorem 1.1 is for
    `n ≥ 2`, so its statement is unaffected.
- **Encoding:** supports are relations `Fin n → Fin n → Prop`, and occurrence
  cores are given by endpoint maps `row : E → U`, `col : E → V` (with an
  occurrence set `O` in Section 2). Relabellings of rows and columns are
  explicit equivalences.

## Build and check

Requires Lean `v4.35.0` (see `lean-toolchain`), Mathlib `v4.35.0` and
RealRooted at the commit pinned in `lakefile.toml`. Versions up to 1.2.0 used
Lean and Mathlib `v4.32.0`. The move to `v4.35.0`, which RealRooted requires,
changed proofs only, not statements.

```bash
lake exe cache get        # download prebuilt Mathlib
lake build                # also builds the RealRooted modules it uses
lake env lean AxiomAudit.lean > axioms.txt
python3 scripts/check_axioms.py AxiomAudit.lean axioms.txt
scripts/kernel_check.sh   # independent kernel check with nanoda (about a minute)
lake env leanchecker --fresh LaviSection2.LaviTheorem11Unconditional   # optional, about 20 minutes
```

## Citation

Please cite this formalization as

> T. Maciejewski, *Lean 4 formalization of Lavi's proof of Foregger's
> conjecture*, Zenodo, 2026,
> [doi:10.5281/zenodo.24254583](https://doi.org/10.5281/zenodo.24254583).

That concept DOI always resolves to the latest version. Each release has its
own version DOI on Zenodo:
- 1.0.0 (Section 2 only):
  [doi:10.5281/zenodo.24254584](https://doi.org/10.5281/zenodo.24254584)
- 1.1.0 (Sections 2–3):
  [doi:10.5281/zenodo.24260452](https://doi.org/10.5281/zenodo.24260452)
- 1.2.0 (Sections 2–7, conditional on Gurvits's inequality):
  [doi:10.5281/zenodo.24267521](https://doi.org/10.5281/zenodo.24267521)
- 1.3.0 (Theorem 1.1 without hypotheses):
  [doi:10.5281/zenodo.24269323](https://doi.org/10.5281/zenodo.24269323)

GitHub's "Cite this repository" button reads `CITATION.cff`. Please also cite
Lavi's preprint for the mathematics, and RealRooted for the formalization of
Gurvits's argument.

## Credits

- **Mathematics:** Y. Lavi, for the proof of Theorem 1.1. L. Gurvits, for the
  capacity inequality (with the presentation of M. Laurent and A. Schrijver).
- **RealRooted:** the formalization of Gurvits's argument (real stability, the
  one-variable inequality, the capacity step and van der Waerden's bound) is by
  Per Alexandersson and the RealRooted contributors,
  <https://github.com/PerAlexandersson/RealRooted> (Apache License 2.0).

## Author

Formalization by Tom Maciejewski
([ORCID 0009-0004-5702-5302](https://orcid.org/0009-0004-5702-5302)).
Lean's kernel checks every proof. Whether each Lean statement says what the
paper says is a separate question; see "Review status" above.

Related work by the author: T. Maciejewski, *Foregger's Permanent Conjecture,
Part IV: A Trivalent Entropic Base Case and Verification Package*, Zenodo,
2 June 2026, [doi:10.5281/zenodo.20510494](https://doi.org/10.5281/zenodo.20510494).

## License

Apache License 2.0 (see `LICENSE`), the same license as Mathlib and RealRooted.
`GurvitsRealRooted.lean` adapts proofs from RealRooted; its header lists the
adapted declarations and the changes.
