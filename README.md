# Lean 4 formalization of Sections 2–3 of Lavi's proof of Foregger's conjecture

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24254583.svg)](https://doi.org/10.5281/zenodo.24254583)
[![Lean build](https://github.com/tommac/lavi-section2-lean/actions/workflows/lean.yml/badge.svg)](https://github.com/tommac/lavi-section2-lean/actions/workflows/lean.yml)

This is a machine-checked Lean 4 / Mathlib formalization of **Section 2
(Lemmas 2.1–2.5)**, **Section 3 (Lemmas 3.1–3.2 and equations (3.5)–(3.7))**
and the **cycle-support case** of

> Yair Lavi, *Foregger's Conjecture on Minimum Permanents of Nearly
> Decomposable Doubly Stochastic Matrices*, preprint, 4 November 2026
> (v1, [doi:10.5281/zenodo.23957650](https://doi.org/10.5281/zenodo.23957650));
> revised 13 November 2026
> (v2, [doi:10.5281/zenodo.24208987](https://doi.org/10.5281/zenodo.24208987)).

The mathematics of the lemmas is Lavi's (Lemmas 2.1 and 2.2 go back to
Foregger). This repository contributes the formalization, along with the
simplifications and sharpenings listed below that came up while writing it.

## Scope: what this does and does not establish

- **Checked:** every lemma of Lavi's Sections 2 and 3, as stated in the table
  below, and the sharp bound with its equality case for cycle-supported faces.
- **No gaps:** there is no `sorry`, `admit`, `axiom` or `native_decide`
  anywhere. `AxiomAudit.lean` prints the axioms of every main theorem, and each
  one reports only Lean's standard `[propext, Classical.choice, Quot.sound]`.
- **Not formalized:** Sections 4–7 of the preprint (tight-cut decomposition,
  Gurvits's capacity bound, the one-star bound, tight-cut leaves and the final
  induction). **This repository therefore does not give a machine-checked
  proof of Foregger's conjecture**, and makes no claim that the conjecture has
  been settled.

## Lemma map

| Lavi (2026) | Lean theorem | File |
|---|---|---|
| Lemma 2.1, cofactor equalities (2.1) | `faceMinimizer_cofactor_eq` | `LaviCofactorEqualization.lean` |
| Lemma 2.1, the support of a face minimizer is FI | `lavi_lemma_2_1` | `LaviMinimizerSupport.lean` |
| Lemma 2.1 on an ND face: the support is exactly `D` | `faceMinimizer_support_eq_of_nearlyDecomposable` | `LaviMinimizerSupport.lean` |
| Lemma 2.2, Foregger's contraction identity | `permanent_contractMatrix`, `faceMinimizer_contraction` | `LaviContractionIdentity.lean`, `LaviCofactorEqualization.lean` |
| Lemma 2.3, no four-cycles | `nearlyDecomposable_no_fourCycle`, `nearlyDecomposable_common_neighbor_unique` | `LaviNoFourCycles.lean` |
| Lemma 2.4, the two contraction mechanisms (column and row) | `lavi_lemma_2_4_column`, `lavi_lemma_2_4_row` | `LaviContractionND.lean` |
| Lemma 2.5, terminal ND supports are `D_can(H)` | `lavi_lemma_2_5` | `LaviLemma25.lean` |
| Lemma 2.5, `D_can(H)` is ND | `nearlyDecomposableOn_canonicalAdj` | `LaviCanonicalExpansion.lean` |
| Lemma 2.5, private-line contractions are FI but not ND | `privateContraction_canonical`, `privateRowContraction_canonical` | `LaviCanonicalExpansion.lean` |
| Cycle supports: `per A ≥ 2^(1−n)`, equality only at `½(I + P)` | `cycleSupported_foregger_sharp` | `LaviCycleFace.lean` |
| Lemma 3.1, `log per Y ≤ F(X) ≤ log per X` on a face, equality at the minimizer | `lavi_lemma_3_1`, `faceFunctional_le_log_permanent` | `LaviFaceVariational.lean` |
| Lemma 3.2, merging parallel occurrences preserves `F_H` | `lavi_lemma_3_2` | `LaviCoreEntropy.lean` |
| `F_H(x)` of a complete core equals the matrix functional `F` | `coreFunctional_eq_faceFunctional` | `LaviCoreEntropy.lean` |
| (3.5), `F_{D(H,L)}(X_x) = F_H(x) − Σ_{ℓ∈L} h₂(x_ℓ)` | `lavi_eq_3_5` | `LaviExpansionEntropy.lean` |
| (3.6), subdivision charge `δ = log 2 − h₂ ≥ 0` | `subdivCharge_nonneg` | `LaviExpansionEntropy.lean` |
| (3.7), normalized gap `G_{H,L} = F_{D(H,L)}(X_x) + (n − 1) log 2` | `lavi_eq_3_7` | `LaviExpansionEntropy.lean` |

Basic definitions (permanent, doubly stochastic, support, fully
indecomposable, nearly decomposable) are in `Definitions.lean`. The
strict-Hall characterization of full indecomposability is derived in
`LaviStrictHall.lean`. `LaviOneStarArithmetic.lean` checks only the scalar
constant identities used in Lavi's one-star estimate (Section 5), not the
estimate itself. Laws on permutations, matching entropy and the Gibbs law
are in `LaviMatchingEntropy.lean`.

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
- **Encoding:** supports are relations `Fin n → Fin n → Prop`, and occurrence
  cores are tuples `(U, V, E, row, col, O)`. Relabellings of rows and columns
  are explicit equivalences.

## Build

Requires Lean `v4.32.0` (see `lean-toolchain`) and Mathlib `v4.32.0`.

```bash
lake exe cache get        # download prebuilt Mathlib
lake build
lake env lean AxiomAudit.lean
```

## Citation

Please cite this formalization as

> T. Maciejewski, *Lean 4 formalization of Sections 2–3 of Lavi's proof of
> Foregger's conjecture*, Zenodo, 2026,
> [doi:10.5281/zenodo.24254583](https://doi.org/10.5281/zenodo.24254583).

That concept DOI always resolves to the latest version. Version 1.0.0
(Section 2 only) is
[doi:10.5281/zenodo.24254584](https://doi.org/10.5281/zenodo.24254584); each
later release gets its own version DOI on Zenodo. GitHub's "Cite this repository" button
reads `CITATION.cff`. Please also cite Lavi's preprint for the mathematics.

## Author and AI assistance

Formalization by Tom Maciejewski
([ORCID 0009-0004-5702-5302](https://orcid.org/0009-0004-5702-5302)).
The Lean code was developed with AI coding assistants (Anthropic's Claude and
OpenAI's Codex), working under the author's direction. Correctness does not
depend on them: Lean's kernel checks every proof.

Related work by the author: T. Maciejewski, *Foregger's Permanent Conjecture,
Part IV: A Trivalent Entropic Base Case and Verification Package*, Zenodo,
2 June 2026, [doi:10.5281/zenodo.20510494](https://doi.org/10.5281/zenodo.20510494).

## License

Apache License 2.0 (see `LICENSE`), the same license as Mathlib.
