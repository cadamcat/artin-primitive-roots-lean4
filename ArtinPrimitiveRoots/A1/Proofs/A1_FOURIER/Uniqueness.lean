import ArtinPrimitiveRoots.A1.Proofs.A1_FOURIER.EBasic

/-!
# A1-FOURIER part `a1_fourier_uniqueness` (LEAD)

Fourier uniqueness on the compact quotient `F_S / R`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Fourier uniqueness on `F_S / R`: a continuous `R`-periodic function all of whose Fourier
coefficients `∫_K Q(x) e(-x ν) dμ` (`ν ∈ R`) vanish is identically zero.

Proof plan: `F_S ⧸ R` is compact (`A1_LATTICE.diagR_has_compact_cover`) and Hausdorff (`R` is
discrete, hence closed: `A1_LATTICE.diagR_isDiscrete`). The characters `x ↦ e(x ν)` descend to
it (`hself`), are closed under products and conjugation, and separate points: if
`e(x ν) = e(y ν)` for all `ν` then `x - y` lies in the annihilator of `R`, hence in `R`
(`hann`). Stone–Weierstrass (`ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints`)
gives uniform approximation of `Q` by character polynomials, so `∫_K |Q|² = 0`; then `Q = 0`
a.e. on `K`, hence a.e. on `F_S` by periodicity, hence everywhere by continuity (Haar measures
charge nonempty open sets).
Uses: `a1_fourier_e_basic`. Used by: `a1_fourier_poisson_abstract`. -/
theorem a1_fourier_uniqueness (S : SData F CE condη) (D : FieldData F) (A : AddCharData F)
    {mS : MeasurableSpace S.FS} [BorelSpace S.FS]
    (μ : Measure S.FS) [μ.IsAddHaarMeasure]
    (K : Set S.FS) (hKm : MeasurableSet K)
    (hK : ∀ x : S.FS, ∃! p : S.R × S.FS, p.2 ∈ K ∧ x = S.diag (p.1 : F) + p.2)
    (hKμ : μ K = 1)
    (hself : ∀ r s : S.R, S.e A (S.diag (r : F) * S.diag (s : F)) = 1)
    (hann : ∀ y : S.FS, (∀ r : S.R, S.e A (S.diag (r : F) * y) = 1) →
      ∃ r : S.R, y = S.diag (r : F))
    (Q : S.FS → ℂ) (hQ : Continuous Q)
    (hper : ∀ (m : S.R) (x : S.FS), Q (x + S.diag (m : F)) = Q x)
    (hcoef : ∀ ν : S.R, ∫ x in K, Q x * S.e A (-(x * S.diag (ν : F))) ∂μ = 0) :
    ∀ x : S.FS, Q x = 0 := by
  sorry

end ArtinPrimitiveRoots.A1
