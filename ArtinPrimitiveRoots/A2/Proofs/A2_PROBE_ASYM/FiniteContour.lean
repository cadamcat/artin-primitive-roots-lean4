import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-POISSON».P2.Contour

open Complex intervalIntegral

noncomputable section

namespace ArtinPrimitiveRoots.A2.ProbeAsym

/-- The finite rectangle identity, solved for the truncated vertical-edge difference. -/
theorem rectangle_vertical_difference {G : ℂ → ℂ} {a b H : ℝ}
    (hrect : ArtinPrimitiveRoots.A2.QSP2.rectInt G
      ((a : ℂ) - H * I) ((b : ℂ) + H * I) = 0) :
    I • ((∫ y : ℝ in -H..H, G ((b : ℂ) + y * I)) -
        ∫ y : ℝ in -H..H, G ((a : ℂ) + y * I)) =
      (∫ x : ℝ in a..b, G ((x : ℂ) + H * I)) -
        ∫ x : ℝ in a..b, G ((x : ℂ) + ((-H : ℝ) : ℂ) * I) := by
  have hza_re : (((a : ℂ) - H * I).re) = a := by simp
  have hza_im : (((a : ℂ) - H * I).im) = -H := by simp
  have hwb_re : (((b : ℂ) + H * I).re) = b := by simp
  have hwb_im : (((b : ℂ) + H * I).im) = H := by simp
  rw [ArtinPrimitiveRoots.A2.QSP2.rectInt, hza_re, hza_im, hwb_re, hwb_im] at hrect
  linear_combination hrect

end ArtinPrimitiveRoots.A2.ProbeAsym
