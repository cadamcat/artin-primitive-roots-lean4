# Reproducing the verification

The project uses Lean `v4.34.1`, selected by [lean-toolchain](../lean-toolchain). Mathlib and the other package revisions are locked in [lake-manifest.json](../lake-manifest.json).

## Fresh checkout

From the repository root, prepare the dependencies and build the project:

```sh
lake update
scripts/apply-oai-patches.sh
lake exe cache get
lake build
```

OpenAI's Lake hook exits with an error beginning `iut: Lake resolved an unexpected checkout at …`. It has still resolved the dependencies and written `lake-manifest.json`; run the patch script after that error. The script applies the `*-lean4341.patch` files from OpenAI's package and skips patches that are already applied. The hook leaves unused package clones under `.lake/packages/OAI/lean/.lake/packages/`; those clones can be removed.

`lake exe cache get` provides compiled Mathlib only. `lake build` compiles this project and the modules it imports from OpenAI's library, ClassFieldTheory, TauCeti, AINTLIB, PrimeNumberTheoremAnd and rellich-kondrachov from source.

## Statement and axiom checks

Run the repository verification script with a bounded build thread count:

```sh
LEAN_NUM_THREADS=4 ./scripts/verify.sh
```

It builds the solution module `ArtinPrimitiveRoots.Target` and the challenge module `Challenge`, then runs three checks:

1. `scripts/check_statement_text.py` compares the definition of `S` and the statement of `artin_primitive_roots_infinite` in [Challenge.lean](../Challenge.lean) and [ArtinPrimitiveRoots/Target.lean](../ArtinPrimitiveRoots/Target.lean), with comments removed and whitespace normalized.
2. [Verification/ChallengeStatement.lean](../Verification/ChallengeStatement.lean) and [Verification/MainStatement.lean](../Verification/MainStatement.lean) check, by `rfl`, that `S` and the type of the theorem in each module equal one displayed statement. The two modules declare the same fully qualified names, so they are checked in separate Lean runs. [comparator.json](../comparator.json) configures Comparator to compare the modules directly.
3. [Verification/Axioms.lean](../Verification/Axioms.lean) prints the axioms of `ArtinPrimitiveRootsConjecture.artin_primitive_roots_infinite`, and `scripts/check_axioms.py` accepts only `propext`, `Classical.choice` and `Quot.sound`. An open proof is reported as `sorryAx` and makes the script exit with status 2; any other axiom, or a missing report, is a failure.

The Lean checks run with `--trust=0`. They check the project modules and the statement correspondence; they do not rebuild Mathlib from source. For a replay of every declaration by the kernel, including the dependencies, run `lake env leanchecker --fresh ArtinPrimitiveRoots.Target` after the build.
