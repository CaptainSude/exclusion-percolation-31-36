# Verify the proof

[Repository](../README.md) · [Main theorem](../ExceptionalTimes/PublishedNearestNeighborDimension.lean#L17) · [Completed verification](../verification/README.md)

## Build locally

Install Lean using the [official installation instructions](https://lean-lang.org/install/). Open a terminal in the repository folder, beside `lakefile.toml`.

On Windows, in PowerShell:

```powershell
$env:LEAN_NUM_THREADS = '1'
lake exe cache get
lake --wfail build
```

On macOS or Linux, in a POSIX shell:

```sh
export LEAN_NUM_THREADS=1
lake exe cache get
lake --wfail build
```

Using one Lean worker limits memory use. The cache command downloads precompiled mathlib dependencies. The build command checks the entire project, treats warnings as errors, and runs the project's [axiom audit](../ExceptionalTimes/AxiomAudit.lean). A successful build ends with `Build completed successfully` and an audit allowing only `propext`, `Classical.choice`, and `Quot.sound`.

The pins are already supplied:

| Dependency | Version |
| --- | --- |
| Lean | `leanprover/lean4:v4.34.1` |
| mathlib | `d13f23b723b8a846827a245b89c10fc7d3f11612` |
| Transitive packages | Exact revisions in [lake-manifest.json](../lake-manifest.json) |

Use the supplied toolchain and manifest to reproduce this release. The first full build takes substantially longer than opening the paper; the recorded Windows build took about an hour after dependency preparation.

## Save a new verification record

With PowerShell 7 and the pinned Lean toolchain installed, run from the repository root:

```powershell
lake exe cache get
./Verify.ps1
```

The script defaults to one Lean worker, checks the toolchain, confirms that the axiom-audit module imports every project module, builds the project with warnings treated as errors, and records before/after source hashes. Its outputs go to `verification/local/`; the published record is preserved.

## Check source identity without rebuilding

With Python 3 installed:

```sh
python scripts/check_sources.py
```

On systems where Python is named `python3`, use that command instead. This compares all Lean source bytes with the [recorded hashes](../verification/status.json), checks that the audit covers every module, and verifies the preserved Lean archive, dependency pins and build records. It is an integrity check, not a new Lean build. An intentional source edit will make the comparison fail until a new verification record is adopted.

The [Git attributes](../.gitattributes) preserve the sources' original line endings, so cloning on another operating system does not change their recorded hashes.

## Verify on GitHub

After publishing the repository:

1. Open **Actions** and select **Verify Lean**.
2. Click **Run workflow**, select the published branch, and start the run.
3. Open the run to read the build and axiom-audit output.

This workflow runs only when requested. It uses the repository's pinned Lean version, downloads the mathlib cache, and builds the complete project. The workflow definitions are pinned to exact action revisions. A GitHub result will appear after the first run; the completed verification shipped here is the local build recorded above.

The workflow uses the official [Lean action](https://github.com/leanprover/lean-action).
