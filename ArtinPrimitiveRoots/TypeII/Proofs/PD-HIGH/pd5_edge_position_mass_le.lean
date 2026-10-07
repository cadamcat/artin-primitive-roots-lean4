import ArtinPrimitiveRoots.TypeII.Proofs.pd5b.PDHigh.pd5_majorKernel_volume_bound

set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
open ArtinPrimitiveRoots.TypeII
noncomputable section

/-- Uniform position sum before any label choices are integrated. Source primitivity, its
box and determinant divisibility remain in the hypotheses/guard; both multiplier parts and
both directions are included. Guide `runs/lanes/sol-thin-pd5/PROOFS.md:245–311`; uses
pd5_majorKernel_volume_bound, a fixed-number determinant-line count and compact cutoff bounds.
Feeds positive prescribed edge rows and low-rank positive edge envelopes. -/
theorem pd5_edge_position_mass_le (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁)
    (K : ℕ) (F : PDFix K) (hF : F.Valid) :
    ∃ Cgeom x₀ : ℝ, 0 < Cgeom ∧ 2 ≤ x₀ ∧
      ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
        ∀ w : ArchRoot, w.InRegion S → ∀ z : ℤ × ℤ,
          Int.gcd z.1 z.2 = 1 → envBox S w z →
          ∀ p q : PrimeLists S.x K, S.d₀ ≤ sharedProduct p →
            ∀ forward : Bool, ∀ Z : Finset (ℤ × ℤ),
              (∑ z' ∈ Z, if envBox S w z' ∧ (sharedProduct p : ℤ) ∣ det2 z z' then
                ‖edgeMultiplier F S forward true p q z z'‖ +
                  ‖edgeMultiplier F S forward false p q z z'‖ else 0) ≤
                Cgeom * Real.rpow S.L (3 * F.A₀) := by
  sorry

end
end ArtinPrimitiveRoots.TypeII.PD
