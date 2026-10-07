import ArtinPrimitiveRoots.Hecke.Theta.GaussianTheta

/-!
# Finite weighted sums of affine lattice theta functions

This is the residue-coset finite-sum layer: a finite set of translates of one sublattice, each
with its own complex weight, transforms into the corresponding finite weighted sum of dual
theta series with additive phases.
-/

set_option autoImplicit false

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

noncomputable section

namespace ArtinPrimitiveRoots.Hecke.Theta

variable {ι : Type*} [Fintype ι]

/-- A finite weighted sum of Gaussian theta series on affine translates of a lattice. -/
def affineGaussianTheta {R : Type*} [Fintype R]
    (L : Submodule ℤ (EuclideanSpace ℝ ι))
    (r : R → EuclideanSpace ℝ ι) (w : R → ℂ) (t : ℝ) : ℂ :=
  ∑ a : R, w a * ∑' v : L,
    gaussianCM (ι := ι) t (r a + (v : EuclideanSpace ℝ ι))

/-- Poisson transformation for a finite weighted sum of affine lattice theta functions. -/
theorem affineGaussianTheta_transform {R : Type*} [Fintype R]
    (L : Submodule ℤ (EuclideanSpace ℝ ι)) [DiscreteTopology L] [IsZLattice ℝ L]
    (r : R → EuclideanSpace ℝ ι) (w : R → ℂ) {t : ℝ} (ht : 0 < t) :
    affineGaussianTheta L r w t =
      ∑ a : R, w a * ((ZLattice.covolume L volume)⁻¹ •
        ∑' y : dualZLattice L,
          Real.fourierChar (⟪r a, (y : EuclideanSpace ℝ ι)⟫) •
            (((t ^ (-(Fintype.card ι : ℝ) / 2) : ℝ) : ℂ)
              * gaussianCM (ι := ι) t⁻¹ (y : EuclideanSpace ℝ ι))) := by
  classical
  unfold affineGaussianTheta
  apply Finset.sum_congr rfl
  intro a _
  rw [gaussianTheta_translate_transform L ht (r a)]

end ArtinPrimitiveRoots.Hecke.Theta

end
