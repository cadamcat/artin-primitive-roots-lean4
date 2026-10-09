import ArtinPrimitiveRoots.TypeII.PD.Physical
import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.SignedMinor

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD

noncomputable section

/-- The actual geometric multiplier has the complementary major-arc integral. -/
theorem geometric_multiplier_minor_formula {K : ℕ} (F : PDFix K) (S : PDScale)
    (D aa bb : ℕ) (t : ℤ) :
    geometricMultiplier F S D aa bb t =
      (((S.d₀ : ℝ) / (D : ℝ) : ℝ) : ℂ) * (F.eta ((bb : ℝ) / S.Y) : ℂ) *
        (F.eta ((aa : ℝ) / S.Y) : ℂ) * (F.psi ((t : ℝ) / S.Y) : ℂ) *
        (∫ θ in (0 : ℝ)..1, if ¬ majorArc S.x S.Y F.A₀ θ then
          additiveCharacter (θ*((t : ℝ)-(bb : ℝ)+(aa : ℝ))) else 0) := by
  let e : ℂ := (((S.d₀ : ℝ) / (D : ℝ) : ℝ) : ℂ) *
    (F.eta ((bb : ℝ) / S.Y) : ℂ) * (F.eta ((aa : ℝ) / S.Y) : ℂ)
  change e * (if t = (bb : ℤ) - aa then (F.psi ((t : ℝ) / S.Y) : ℂ) else 0) -
    e * majorKernel S.x S.Y F.A₀ (t : ℝ) aa bb F.psi =
      e * (F.psi ((t : ℝ) / S.Y) : ℂ) * _
  rw [← mul_sub, signed_kernel_minor_integral]
  exact (mul_assoc _ _ _).symm

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
