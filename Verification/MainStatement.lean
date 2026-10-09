import ArtinPrimitiveRoots.Target

/-!
Checks the solution declaration against the same displayed statement as ChallengeStatement.lean.
-/

namespace ArtinPrimitiveRootsConjecture.Verification

abbrev primitiveRootPrimes (a : ℤ) : Set ℕ :=
  {p : ℕ | p.Prime ∧ orderOf (a : ZMod p) = (p - 1 : ℕ)}

abbrev targetStatement : Prop :=
  ∀ a : ℤ, a ≠ -1 → ¬ IsSquare a → (primitiveRootPrimes a).Infinite

example : @ArtinPrimitiveRootsConjecture.S = primitiveRootPrimes := rfl

example : type_of% @ArtinPrimitiveRootsConjecture.artin_primitive_roots_infinite = targetStatement :=
  rfl

end ArtinPrimitiveRootsConjecture.Verification
