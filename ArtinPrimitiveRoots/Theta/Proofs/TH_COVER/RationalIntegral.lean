import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

set_option autoImplicit false
open IsDedekindDomain Filter
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.th_cover_sol

variable {R K : Type} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

theorem rational_eventually_integral (x : K) :
    ∀ᶠ v : HeightOneSpectrum R in cofinite,
      algebraMap K (v.adicCompletion K) x ∈ v.adicCompletionIntegers K := by
  simpa only [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.algebraMap_adicCompletion,
    Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply] using
    FiniteAdeleRing.cofinite_mem_adicCompletionIntegers
      (algebraMap K (FiniteAdeleRing R K) x)

theorem rationalUnit_eventually_integral (u : Kˣ) :
    ∀ᶠ v : HeightOneSpectrum R in cofinite,
      (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom u :
        v.adicCompletion K) ∈ v.adicCompletionIntegers K ∧
      (((Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom u)⁻¹ :
        (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
  filter_upwards [rational_eventually_integral (R := R) (u : K),
    rational_eventually_integral (R := R) ((u⁻¹ : Kˣ) : K)] with v hu hinv
  constructor
  · exact hu
  · rw [← map_inv]
    exact hinv

end ArtinPrimitiveRoots.Proofs.th_cover_sol
