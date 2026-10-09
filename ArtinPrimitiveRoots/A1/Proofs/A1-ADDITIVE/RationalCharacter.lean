import ArtinPrimitiveRoots.A1.Proofs.«A1-ADDITIVE».TateCharacter
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

set_option autoImplicit false

open NumberField IsDedekindDomain

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_bdata_sol

theorem rationalCompletionChar_exists (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ ψ : AddChar (v.adicCompletion ℚ) ℂ,
      (∀ x, ψ x = 1 ↔ x ∈ v.adicCompletionIntegers ℚ) ∧
      (∀ (a : ℤ) (n : ℕ),
        ψ (algebraMap ℚ (v.adicCompletion ℚ)
          ((a : ℚ) / ((Rat.HeightOneSpectrum.primesEquiv v).1 : ℚ) ^ n)) =
        Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) /
          ((Rat.HeightOneSpectrum.primesEquiv v).1 : ℂ) ^ n)) := by
  classical
  let : Fact (Rat.HeightOneSpectrum.primesEquiv v).1.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  obtain ⟨ψ, hker, hformula⟩ :=
    tateQpChar_exists (p := (Rat.HeightOneSpectrum.primesEquiv v).1)
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  let χ : AddChar (v.adicCompletion ℚ) ℂ :=
    ψ.compAddMonoidHom e.toAlgEquiv.toRingHom.toAddMonoidHom
  have hbij := Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v
  refine ⟨χ, ?_, ?_⟩
  · intro x
    change ψ (e x) = 1 ↔ x ∈ v.adicCompletionIntegers ℚ
    rw [hker]
    constructor
    · intro hx
      obtain ⟨y, hy, heq⟩ := hbij.surjOn hx
      have hxy : y = x := e.injective heq
      simpa only [hxy, SetLike.mem_coe] using hy
    · intro hx
      exact hbij.mapsTo hx
  · intro a n
    change ψ (e.toAlgEquiv (algebraMap ℚ (v.adicCompletion ℚ)
      ((a : ℚ) / ((Rat.HeightOneSpectrum.primesEquiv v).1 : ℚ) ^ n))) = _
    rw [e.toAlgEquiv.commutes]
    simpa only [map_div₀, map_pow, map_intCast, map_natCast] using hformula a n

end ArtinPrimitiveRoots.Proofs.a1_bdata_sol
