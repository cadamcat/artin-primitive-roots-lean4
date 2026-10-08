import ArtinPrimitiveRoots.TypeII.Proofs.pd2.Raw.RootQuantitativeDiscrepancy

namespace ArtinPrimitiveRoots.TypeII.PD

structure pd2a_RootCountingInputs where
  CK : ℝ
  CT : ℝ
  CK_pos : 0 < CK
  CT_pos : 0 < CT
  kloosterman : ∀ m : ℕ, ∀ hi : NeZero m, ∀ Ft : Fintype (ZMod m)ˣ, ∀ H K : ZMod m,
    ‖@pd2a_rootKSum m hi Ft H K‖ ≤ CK * (m : ℝ) ^ (3 / 4 + 1 / 100 : ℝ) *
      (Nat.gcd (Nat.gcd H.val K.val) m : ℝ) ^ (1 / 4 : ℝ)
  divisors : ∀ u : ℕ, 1 ≤ u → (u.divisors.card : ℝ) ≤ CT * (u : ℝ) ^ (1 / 100 : ℝ)

end ArtinPrimitiveRoots.TypeII.PD
