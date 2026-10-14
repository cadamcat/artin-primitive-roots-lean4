import Mathlib

/-!
# Target: the infinitude assertion of Artin's primitive root conjecture

The infinitude assertion of Artin's conjecture: each fixed integer that is neither `-1` nor a
perfect square is a primitive root modulo infinitely many primes.

`S` is copied verbatim from Formal Conjectures,
`FormalConjectures/Wikipedia/ArtinPrimitiveRootsConjecture.lean`
(google-deepmind/formal-conjectures at `9d259649abe0b02d7a25f7589b872db679b35e21`), where it is
`ArtinPrimitiveRootsConjecture.S`. That file states only the density forms, so the infinitude
statement below is written here. It uses Mathlib definitions only.
-/

namespace ArtinPrimitiveRootsConjecture

/-- Let $S(a)$ be the set of primes such that $a$ is a primitive root modulo $p$. -/
abbrev S (a : ℤ) : Set ℕ :=
  {p : ℕ | p.Prime ∧ orderOf (a : ZMod p) = (p-1 : ℕ)}

/-- **Artin's primitive root conjecture, infinitude form.** Every integer `a` that is neither `-1`
nor a perfect square is a primitive root modulo infinitely many primes. -/
theorem artin_primitive_roots_infinite :
    ∀ a : ℤ, a ≠ -1 → ¬ IsSquare a → (S a).Infinite := by
  sorry

end ArtinPrimitiveRootsConjecture
