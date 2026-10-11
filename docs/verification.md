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
2. [Verification/ChallengeStatement.lean](../Verification/ChallengeStatement.lean) and [Verification/MainStatement.lean](../Verification/MainStatement.lean) check, by `rfl`, that `S` and the type of the theorem in each module equal one displayed statement. The two modules declare the same fully qualified names, so they are checked in separate Lean runs. [comparator.json](../comparator.json) configures Comparator to compare the modules directly. Its `definition_names` is empty: Comparator treats names listed there as definition holes and checks only their name, type, universe levels and safety, so leaving `S` out makes it compare the definition of `S` in full.
3. [Verification/Axioms.lean](../Verification/Axioms.lean) prints the axioms of `ArtinPrimitiveRootsConjecture.artin_primitive_roots_infinite`, and `scripts/check_axioms.py` accepts only `propext`, `Classical.choice` and `Quot.sound`. An open proof is reported as `sorryAx` and makes the script exit with status 2; any other axiom, or a missing report, is a failure.

The Lean checks run with `--trust=0`. They check the project modules and the statement correspondence; they do not rebuild Mathlib from source. For a replay of every declaration by the kernel, including the dependencies, run `lake env leanchecker --fresh ArtinPrimitiveRoots.Target` after the build.

## Non-vacuity checks

[Verification/NonVacuity.lean](../Verification/NonVacuity.lean) checks that the theorem is not vacuous and says what the problem asks. It shows that `2`, `3` and `-2` satisfy both hypotheses, checks `S 2` on small primes (`3` and `5` in, `7` out) and at primes dividing the base, and derives from `artin_primitive_roots_infinite` the forms with Mathlib's `IsPrimitiveRoot (a : ZMod p) (p - 1)`, with a generator of `(ZMod p)ˣ`, and with a prime above every bound. Independently of the theorem, it proves that `S (-1)` and every `S (b ^ 2)` are finite, so both hypotheses are needed. Run `lake env lean Verification/NonVacuity.lean` after the build; it prints the axioms of each of its theorems, all among `propext`, `Classical.choice` and `Quot.sound`.

## Independent check of v1.0.0

On 9–10 October 2026 (UTC), release `v1.0.0` was cloned from GitHub into an empty scratch directory on a 32-core compute node and checked with the steps of [Fresh checkout](#fresh-checkout), in order:

| Step | Result |
|---|---|
| `lake update` | exit 1 with the `iut: Lake resolved an unexpected checkout at …` hook error described above; the revisions it resolved for all 43 packages equal those in `lake-manifest.json` |
| `scripts/apply-oai-patches.sh` | exit 0; patches applied to 23 of OpenAI's pinned packages |
| `lake exe cache get`, then `lake build` | exit 0 (12143 jobs, 87 minutes); no errors and no `sorry`. The Mathlib cache files were already in the local cache, so nothing was downloaded |
| `#print axioms ArtinPrimitiveRootsConjecture.artin_primitive_roots_infinite` | `propext`, `Classical.choice` and `Quot.sound` only |
| `lake env leanchecker --fresh ArtinPrimitiveRoots.Target` | exit 0 (56 minutes): the kernel replayed the declarations of the solution module and of everything it imports, including the cached dependency artifacts |

`scripts/verify.sh` and Comparator were not part of this run. At the time of the check, the release differed from the current tag `v1.0.0` (commit `c4e54a355cf5b96b389731e45676351fb23e0c0a`) only in seven lines of documentation comments, which were removed afterwards.

## Comparator check of v1.0.0

On 10–11 October 2026 (UTC), `v1.0.0` (commit `c4e54a355cf5b96b389731e45676351fb23e0c0a`) was cloned again from GitHub onto a 32-core Linux machine and built with the steps of [Fresh checkout](#fresh-checkout); `lake update` ended with the hook error described above and left `lake-manifest.json` unchanged, and `lake build` exited with status 0 (12143 jobs). [Comparator](https://github.com/leanprover/comparator) at `ca04cfc` then ran with [comparator.json](../comparator.json) and `"enable_nanoda": true`, which also replays the solution in [nanoda](https://github.com/ammkrn/nanoda_lib) (at `3a24072`), an independent type checker for Lean written in Rust, reading the export of `lean4export` at `076e8e5` (the `v4.34.0` source). Comparator exited with status 0: the statement matches the challenge, and both nanoda and the Lean kernel accept the solution with only `propext`, `Quot.sound` and `Classical.choice`.

At `v1.0.0`, `comparator.json` lists `ArtinPrimitiveRootsConjecture.S` in `definition_names`, so that run compared only the name, type, universe levels and safety of `S`. A second run from a separate clone of the same commit used a copy of `comparator.json` with `definition_names` empty, so that `S` was compared in full; it also exited with status 0, with both kernels accepting the solution. `comparator.json` on `main` has had `definition_names` empty since then.

Both runs used comparator's development stand-in for the `landrun` sandbox, so they checked the statement match and kernel acceptance without isolating the build from the code it checks. Before the runs, comparator's own test suite passed on the same machine, and nanoda rejected an export that uses `sorryAx` and an export with an altered numeral. To repeat them, build `lean4export` for the project's Lean version and nanoda (`cargo build --release` in a checkout of `nanoda_lib`), set `"enable_nanoda": true` in a copy of `comparator.json`, and run comparator with `COMPARATOR_LEAN4EXPORT`, `COMPARATOR_NANODA` (pointing to `target/release/nanoda_bin`) and `COMPARATOR_LANDRUN` set, as the Comparator repository describes.
