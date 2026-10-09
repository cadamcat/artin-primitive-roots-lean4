# Authors and attribution

Yao Xu ([@cadamcat](https://github.com/cadamcat)) is the author and maintainer of this formalization project.

The mathematical theorem was proved by OpenAI, in the paper [*Primitive roots for every admissible integer base*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf). This repository formalizes the infinitude assertion of Artin's primitive root conjecture, which the paper's main theorem implies; it does not claim a new mathematical solution. The formal proof follows the paper and uses OpenAI's Lean library for parts of the analytic number theory.

The author planned, dispatched and reviewed the work, set its acceptance criteria (only the standard axioms, fidelity of every frozen statement, replay by the Lean kernel) and decided on its publication. Claude Opus 5.5 in Claude Code coordinated the work, reviewed statements and proved some of the hardest steps. GPT-6 Luna in Codex wrote most of the Lean proofs. GPT-6.1 Sol in Codex checked statements for counterexamples, designed proofs of the hard steps and proved many of them. Gemini 3.8 Flash in Antigravity, Muse Spark 1.3 in OpenCode and Grok 4.7 in the Grok CLI proved smaller parts. The resulting proofs and their dependencies were checked by the Lean kernel.

Before release, intermediate declarations that the final theorem does not use and that were never proved were removed. One of them, a class and dyadic slicing lemma for the quadratic sieve, is false as stated because it lacks a positivity hypothesis on the row scale; the proof uses a corrected version with that hypothesis.

The project uses Mathlib, OpenAI's `openai/math` library and the packages it pins, and adapts files from several of them. Their authors and licenses are credited in [THIRD_PARTY.md](THIRD_PARTY.md) and [NOTICE](NOTICE).
