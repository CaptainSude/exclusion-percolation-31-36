# Exceptional times for nearest-neighbor exclusion percolation on the triangular lattice have Hausdorff dimension 31/36

**[Read the paper](paper/nearest-neighbor-31-36.pdf)** · **[Main theorem in Lean](ExceptionalTimes/PublishedNearestNeighborDimension.lean#L17)** · **[Proof guide](docs/proof-guide.md)** · **[Verify the proof](docs/verification.md)**

Color the sites of the triangular lattice independently black or white, each with probability one half. Each neighboring pair exchanges colors whenever its independent rate-one Poisson clock rings.

At every fixed time, there is almost surely no infinite black cluster. Nevertheless, such clusters appear at exceptional times. This paper proves that, almost surely, their times in **every nonempty time interval** have Hausdorff dimension **31/36**:

$$
\dim_{\mathrm H}\{t\in(a,b):\omega_t\text{ has an infinite black cluster}\}
=\frac{31}{36},\qquad 0\le a<b<\infty.
$$

This is the nearest-neighbor triangular-lattice case of [Garban–Vanneuville's Conjecture 1.7](https://arxiv.org/abs/1605.04766v3).

## Start here

| You want to… | Open |
| --- | --- |
| Read the argument | [Six-page paper](paper/nearest-neighbor-31-36.pdf) |
| Follow its formal structure | [Proof guide](docs/proof-guide.md) |
| Inspect the exact statement | [Main Lean theorem](ExceptionalTimes/PublishedNearestNeighborDimension.lean#L17) |
| Check a result imported from the literature | [24 definitions and their sources](docs/literature.md) |
| Reproduce the verification | [Build instructions](docs/verification.md) |
| Inspect the completed check | [Build log](verification/full-build.log) · [Source hashes](verification/status.json) |
| Edit or cite the paper | [LaTeX source](paper/nearest-neighbor-31-36.tex) · [BibTeX](paper/citation.bib) |

## Lean verification

The completed build checks **443 Lean files** and audits **8,241 declarations**, including **6,231 theorems**. The only transitive axioms are `propext`, `Classical.choice`, and `Quot.sound`.

The cited literature results and their stated specializations enter Lean as explicit hypotheses. The new comparison, forest estimates, clock control, energy bound and exceptional-time argument are proved in the development. The [literature index](docs/literature.md) makes that division precise.

With [Lean installed](https://lean-lang.org/install/), run from this folder in PowerShell:

```powershell
$env:LEAN_NUM_THREADS = '1'
lake exe cache get
lake --wfail build
```

The project pins **Lean 4.34.1** and its **mathlib revision**. The [build guide](docs/verification.md) also gives macOS/Linux commands. A manual **Verify Lean** workflow is included under GitHub Actions; [instructions](docs/verification.md#verify-on-github) explain how to run it.

## Repository layout

```text
paper/              PDF, LaTeX source and citation
ExceptionalTimes/   Main theorem and supporting Lean modules
docs/               Proof guide, literature index and build instructions
verification/       Completed build record and standalone Lean archive
scripts/            Fast source-integrity check
```

The three Lean files at the repository root contain the finite response, exchange and fractional-comparison lemmas used by the development.

For the first upload, see [Publishing on GitHub](docs/publishing.md). The [release notes](docs/release-notes.md) are ready to paste.
