# Lean 4 formalization of Lavi's proof of Foregger's conjecture, conditional on Gurvits's capacity inequality

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24254583.svg)](https://doi.org/10.5281/zenodo.24254583)
[![Lean build](https://github.com/tommac/lavi-section2-lean/actions/workflows/lean.yml/badge.svg)](https://github.com/tommac/lavi-section2-lean/actions/workflows/lean.yml)

This is a machine-checked Lean 4 / Mathlib formalization of **Sections 2–7** of

> Yair Lavi, *Foregger's Conjecture on Minimum Permanents of Nearly
> Decomposable Doubly Stochastic Matrices*, preprint, 4 November 2026
> (v1, [doi:10.5281/zenodo.23957650](https://doi.org/10.5281/zenodo.23957650));
> revised 13 November 2026
> (v2, [doi:10.5281/zenodo.24208987](https://doi.org/10.5281/zenodo.24208987)).

It ends with the paper's Theorem 1.1, proved in Lean **from one explicit
hypothesis that is assumed and not proved here**: Gurvits's degree-sensitive
capacity inequality for permanents.

The mathematics is Lavi's (Lemmas 2.1 and 2.2 go back to Foregger). This
repository contributes the formalization, along with the simplifications and
sharpenings listed below that came up while writing it.

## Status: what this does and does not establish

- **What is machine-checked:** every lemma and numbered identity of Sections
  2–6 listed in the table below, and the induction of Section 7. The final
  statements are in `LaviTheorem11.lean`:

  ```lean
  theorem lavi_theorem_1_1 (hG : GurvitsCapacityInequality) {n : ℕ} (hn : 2 ≤ n)
      {A : Square n} (hA : DoublyStochastic A) (hND : NearlyDecomposable (support A)) :
      (2 : ℝ) ^ ((1 : ℤ) - (n : ℤ)) ≤ permanent A ∧
        (permanent A = (2 : ℝ) ^ ((1 : ℤ) - (n : ℤ)) ↔
          ∃ σ τ : Equiv.Perm (Fin n), ∀ i j, A i j = halfCycleMatrix n (σ i) (τ j))
  ```

  where `halfCycleMatrix n = (1/2) • (1 + (finRotate n).permMatrix ℝ)` is the
  paper's `½(I_n + P_n)`. `lavi_theorem_1_1_moreover` is the strictness clause
  for supports that are not connected and 2-regular, and
  `lavi_theorem_1_1_attained` (no hypothesis) shows the bound is attained in
  every order `n ≥ 2`.
- **The one assumption:** `GurvitsCapacityInequality` (in
  `LaviOneStarCapacity.lean`) states, for every nonnegative `n × n` matrix `M`
  with `Δ_j` nonzero entries in column `j`,
  `per M ≥ Cap(M) · ∏_{j=1}^{n} g(min(Δ_j, j))`. It is a published theorem
  (L. Gurvits, Electron. J. Combin. 15 (2008), Theorem 2.4 and Corollary
  2.7(a); in exactly this form, M. Laurent and A. Schrijver, Amer. Math.
  Monthly 117 (2010), Corollary 1a). It is **not formalized here**. It is a
  hypothesis of the theorems that use it, not a Lean axiom, so it is visible in
  their statements. It enters through Lemma 5.1 and is inherited by Corollary
  5.2, equation (6.1) and Theorem 1.1.
- **Consequently this repository is a machine-checked reduction of Theorem 1.1
  to Gurvits's inequality. It is not a complete machine-checked proof of
  Foregger's conjecture**, and it makes no claim that the conjecture has been
  settled.
- **No gaps in what is checked:** there is no `sorry`, `admit`, `axiom` or
  `native_decide` anywhere. `AxiomAudit.lean` prints the axioms of every main
  theorem, and each one reports only Lean's standard
  `[propext, Classical.choice, Quot.sound]`.
- **Review status:** the Lean statements were translated from the paper with
  AI assistance and compared with the text by the author's tooling. They have
  not yet been independently reviewed by a second person. Line numbers quoted
  in some docstrings refer to a plain-text extraction of v2 of the preprint.

## Lemma map

| Lavi (2026) | Lean theorem | File |
|---|---|---|
| Lemma 2.1, cofactor equalities (2.1) | `faceMinimizer_cofactor_eq` | `LaviCofactorEqualization.lean` |
| Lemma 2.1, the support of a face minimizer is FI | `lavi_lemma_2_1` | `LaviMinimizerSupport.lean` |
| Lemma 2.1 on an ND face: the support is exactly `D` | `faceMinimizer_support_eq_of_nearlyDecomposable` | `LaviMinimizerSupport.lean` |
| Lemma 2.2, Foregger's contraction identity | `permanent_contractMatrix`, `faceMinimizer_contraction` | `LaviContractionIdentity.lean`, `LaviCofactorEqualization.lean` |
| Lemma 2.3, no four-cycles | `nearlyDecomposable_no_fourCycle`, `nearlyDecomposable_common_neighbor_unique` | `LaviNoFourCycles.lean` |
| Lemma 2.4, the two contraction mechanisms (column and row) | `lavi_lemma_2_4_column`, `lavi_lemma_2_4_row` | `LaviContractionND.lean` |
| Lemma 2.5, terminal ND supports are `D_can(H)` | `lavi_lemma_2_5`, `lavi_lemma_2_5_univ` | `LaviLemma25.lean`, `LaviTerminalBridge.lean` |
| Lemma 2.5, `D_can(H)` is ND | `nearlyDecomposableOn_canonicalAdj` | `LaviCanonicalExpansion.lean` |
| Lemma 2.5, private-line contractions are FI but not ND | `privateContraction_canonical`, `privateRowContraction_canonical` | `LaviCanonicalExpansion.lean` |
| Cycle supports: `per A ≥ 2^(1−n)`, equality only at `½(I + P)` | `cycleSupported_foregger_sharp` | `LaviCycleFace.lean` |
| Lemma 3.1, `log per Y ≤ F(X) ≤ log per X` on a face, equality at the minimizer | `lavi_lemma_3_1`, `faceFunctional_le_log_permanent` | `LaviFaceVariational.lean` |
| Lemma 3.2, merging parallel occurrences preserves `F_H` | `lavi_lemma_3_2` | `LaviCoreEntropy.lean` |
| `F_H(x)` of a complete core equals the matrix functional `F` | `coreFunctional_eq_faceFunctional` | `LaviCoreEntropy.lean` |
| (3.5), `F_{D(H,L)}(X_x) = F_H(x) − Σ_{ℓ∈L} h₂(x_ℓ)` | `lavi_eq_3_5` | `LaviExpansionEntropy.lean` |
| (3.6), subdivision charge `δ = log 2 − h₂ ≥ 0` | `subdivCharge_nonneg` | `LaviExpansionEntropy.lean` |
| (3.7), normalized gap `G_{H,L} = F_{D(H,L)}(X_x) + (n − 1) log 2` | `lavi_eq_3_7` | `LaviExpansionEntropy.lean` |
| Section 4, a tight cut is oriented | `tightCut_orientation`, `exists_shoreCut_of_tight` | `LaviTightCutOrientation.lean` |
| Section 4, matchings glue along the crossing label; (4.1) | `ShoreCut.sum_lmatch_eq_sum_pairs`, `ShoreCut.lavi_eq_4_1` | `LaviTightCut.lean` |
| Lemma 4.1, (4.2): `F_H = F_{H₁} + F_{H₂}` | `ShoreCut.lavi_lemma_4_1` | `LaviTightCutEntropy.lean` |
| Lemma 4.1, (4.3): removability across the cut | `ShoreCut.coreFI_cut_iff`, `ShoreCut.lavi_eq_4_3` | `LaviTightCutFI.lean` |
| (4.4), (4.5), for either choice of leaf | `ShoreCut.lavi_eq_4_4`, `ShoreCut.lavi_eq_4_5` and primed versions | `LaviTightCutAccounting.lean` |
| (5.2), `per A = per M` | `permanent_expandedMatrix_eq_elim` | `LaviOneStarPermanent.lean` |
| (5.3)–(5.4), capacity bound; (5.6) | `capacity_elim_ge`, `sum_colCount_le` | `LaviOneStarCapacity.lean` |
| (5.7), (5.10), the factors `A_d`, `C_d` | `rowFactor_secant`, `colFactor_secant` | `LaviOneStarConstants.lean` |
| Lemma 5.1, one-star bound (**assuming Gurvits**) | `lavi_lemma_5_1` | `LaviOneStar.lean` |
| Corollary 5.2, row and column versions (**assuming Gurvits**) | `lavi_corollary_5_2`, `lavi_corollary_5_2_col` | `LaviOneStar.lean`, `LaviLeafGap.lean` |
| Lemma 6.1, cut-free cores | `lavi_lemma_6_1` | `LaviCutFree.lean` |
| Lemma 6.2, a minimum shore closes to a leaf | `lavi_lemma_6_2` | `LaviMinShore.lean` |
| (6.1), leaf gap (**assuming Gurvits**) | `ShoreCut.lavi_eq_6_1` and primed version | `LaviLeafGap.lean` |
| Lemma 6.3, four-vertex leaf; (6.5) | `ShoreCut.lavi_lemma_6_3`, `ShoreCut.lavi_eq_6_5` and primed versions | `LaviFourVertexLeaf.lean` |
| Section 7, contraction branch (7.1) | `contraction_branch_column`, `contraction_branch_row` | `LaviContractionBranch.lean` |
| Section 7, order-one terminal cores, (7.2) | `lavi_eq_7_2` | `LaviTerminalBranch.lean` |
| Section 7, terminal branch is strict (**assuming Gurvits**) | `terminal_branch_strict` | `LaviTerminalBranch.lean` |
| Section 7, equality forces a half cycle | `isHalfCycle_of_half_entries`, `half_entries_of_contractMatrix` | `LaviEqualityCase.lean` |
| Section 7, the induction, given strictness on terminal supports | `foreggerSharpAt_of_terminal_strict` | `LaviInduction.lean` |
| Theorem 1.1 (**assuming Gurvits**) | `lavi_theorem_1_1`, `lavi_theorem_1_1_moreover` | `LaviTheorem11.lean` |
| The bound is attained in every order (no hypothesis) | `lavi_theorem_1_1_attained` | `LaviTheorem11.lean` |

Basic definitions (permanent, doubly stochastic, support, fully
indecomposable, nearly decomposable) are in `Definitions.lean`. The
strict-Hall characterization of full indecomposability is derived in
`LaviStrictHall.lean`. Laws on permutations, matching entropy and the Gibbs
law are in `LaviMatchingEntropy.lean`. `Transpose.lean`,
`RelabelInvariance.lean` and `Arithmetic.lean` hold small supporting facts.

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
    three is never terminal, by Lemma 2.4.
  - The converse ("`D_can(H)` is ND") is stated for supports of order at least
    two. This excludes the degenerate order-one core with a single occurrence.
- **Lemma 3.1:** the lower bound is proved by minimizing
  `log per W − Σ x_ij log w_ij` over a compact sub-face, showing that the
  minimizer is interior, and perturbing along the difference between its Gibbs
  marginals and `X`. This avoids maximizer positivity, Lagrange multipliers and
  Sinkhorn scaling.
- **Lemma 3.2:** proved for an arbitrary endpoint-preserving merge map (any
  number of bundles at once), by comparing a law with its push-forward and with
  an independent relabelling lift. No entropy chain rule or concavity is used.
- **Section 3 encoding:** `F` is defined with laws on all permutations (they
  charge only `supp X`, so this matches the text), and `Ent*` is a supremum.
  In (3.5), `X_x` is defined as the aggregated flow of the expanded core:
  direct entries sum their parallel flows and each long occurrence becomes a
  path carrying `(x, 1 − x, x)`.
- **Section 4:** a cut is recorded in the oriented form that tightness forces
  (one extra row on a shore, no occurrence entering its columns). Lemma 4.1's
  entropy identity is proved by projection and a Gibbs comparison with the
  glued law, with no conditional entropy. The removability rule (4.3) is a
  strict-Hall computation in place of the 2-connectivity argument.
- **Section 5:** the secant bounds (5.10) are proved with Bernoulli's
  inequality instead of convexity. Full indecomposability of the core is not
  needed for Lemma 5.1.
- **Section 6:** Lemma 6.2 is proved by transporting the orientation of a
  tight shore of the factor to the parent. It takes "every occurrence lies in
  a perfect matching" as a hypothesis; in Section 7 this comes from a positive
  feasible flow.
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

## Build

Requires Lean `v4.32.0` (see `lean-toolchain`) and Mathlib `v4.32.0`.

```bash
lake exe cache get        # download prebuilt Mathlib
lake build
lake env lean AxiomAudit.lean
```

## Citation

Please cite this formalization as

> T. Maciejewski, *Lean 4 formalization of Lavi's proof of Foregger's
> conjecture, conditional on Gurvits's capacity inequality*, Zenodo, 2026,
> [doi:10.5281/zenodo.24254583](https://doi.org/10.5281/zenodo.24254583).

That concept DOI always resolves to the latest version. Version 1.0.0
(Section 2 only) is
[doi:10.5281/zenodo.24254584](https://doi.org/10.5281/zenodo.24254584) and
version 1.1.0 (Sections 2–3) is
[doi:10.5281/zenodo.24260452](https://doi.org/10.5281/zenodo.24260452); each
later release gets its own version DOI on Zenodo. GitHub's "Cite this
repository" button reads `CITATION.cff`. Please also cite Lavi's preprint for
the mathematics.

## Author and AI assistance

Formalization by Tom Maciejewski
([ORCID 0009-0004-5702-5302](https://orcid.org/0009-0004-5702-5302)).
The Lean code was developed with AI coding assistants (Anthropic's Claude and
OpenAI's Codex), working under the author's direction. Correctness of the
proofs does not depend on them: Lean's kernel checks every proof. Whether each
Lean statement says what the paper says is a separate question; see "Review
status" above.

Related work by the author: T. Maciejewski, *Foregger's Permanent Conjecture,
Part IV: A Trivalent Entropic Base Case and Verification Package*, Zenodo,
2 June 2026, [doi:10.5281/zenodo.20510494](https://doi.org/10.5281/zenodo.20510494).

## License

Apache License 2.0 (see `LICENSE`), the same license as Mathlib.
