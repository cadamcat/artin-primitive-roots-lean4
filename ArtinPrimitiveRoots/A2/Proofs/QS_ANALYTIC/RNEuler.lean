import ArtinPrimitiveRoots.Hecke.Elementary

/-!
# QS-ANALYTIC, RN-E: the Euler product of `ζ_E` grouped over the places of `K`

For a finite extension `E/K` of number fields, every finite place `w` of `E` lies over a unique
finite place `qsaBelow K E w` of `K`, each fiber is finite, and the Euler product of `ζ_E`
(`Hecke.LSeriesRay_eulerProduct` for the trivial character of the trivial modulus) regroups into
fiber products (`HasProd.sigma`).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ClassFieldTheory
open scoped NumberField

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable (K E : Type*) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

/-- RN-E0: the finite place of `K` below a finite place of `E`. -/
def qsaBelow (w : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 K) where
  asIdeal := w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 E))
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    sorry

/-- RN-E1: the places of `E` above a place of `K` form a finite set. -/
theorem qsa_below_fiber_finite (v : HeightOneSpectrum (𝓞 K)) :
    Set.Finite {w : HeightOneSpectrum (𝓞 E) | qsaBelow K E w = v} := by
  sorry

/-- RN-E2: the Euler product of `ζ_E`, grouped over the places of `K`. -/
theorem qsa_dedekindZeta_hasProd_fiber {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun v : HeightOneSpectrum (𝓞 K) =>
      ∏ w ∈ (qsa_below_fiber_finite K E v).toFinset,
        (1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹) (dedekindZeta E s) := by
  sorry

end ArtinPrimitiveRoots.A2
