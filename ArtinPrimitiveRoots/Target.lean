import ArtinPrimitiveRoots.Reduction

/-!
# The target

`S` and the statement are identical to `Challenge.lean` (with `S` copied verbatim from Formal
Conjectures' `ArtinPrimitiveRootsConjecture.S`); this module proves it.
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
