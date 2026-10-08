import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_WHIT.SphericalBound

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

/-- The squarefree integral ideal recording a finite set of ordinary places. -/
def whitPrimeSupportIdeal (t : Finset (FinPlace F)) : Ideal (𝓞 F) :=
  ∏ v ∈ t, v.asIdeal

/-- Prime support is recovered from its squarefree ideal, whose norm is the residue-size product. -/
theorem whit_prime_support_encoding :
    Function.Injective (whitPrimeSupportIdeal (F := F)) ∧
    (∀ t : Finset (FinPlace F), whitPrimeSupportIdeal t ≠ ⊥) ∧
    ∀ t : Finset (FinPlace F),
      (Ideal.absNorm (whitPrimeSupportIdeal t) : ℝ) = ∏ v ∈ t, qv v := by
  have hmem (t : Finset (FinPlace F)) (v : FinPlace F) :
      v.asIdeal ∣ whitPrimeSupportIdeal t ↔ v ∈ t := by
    rw [whitPrimeSupportIdeal, v.prime.dvd_finsetProd_iff]
    constructor
    · rintro ⟨w, hw, hvw⟩
      have heq : v = w := HeightOneSpectrum.asIdeal_injective
        (associated_iff_eq.mp (v.prime.associated_of_dvd w.prime hvw))
      simpa only [heq] using hw
    · intro hv
      exact ⟨v, hv, dvd_rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro t u h
    apply Finset.ext
    intro v
    rw [← hmem t v, ← hmem u v, h]
  · intro t
    change (∏ v ∈ t, v.asIdeal) ≠ 0
    exact Finset.prod_ne_zero_iff.mpr (fun v _ => v.ne_bot)
  · intro t
    change (Ideal.absNorm (∏ v ∈ t, v.asIdeal) : ℝ) =
      ∏ v ∈ t, (Ideal.absNorm v.asIdeal : ℝ)
    rw [map_prod, Nat.cast_prod]

end ArtinPrimitiveRoots.A1.Theta
