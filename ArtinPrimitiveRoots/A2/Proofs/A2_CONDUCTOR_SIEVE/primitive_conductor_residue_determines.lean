import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.primitive_conductor_residue_bridge

set_option autoImplicit false
open NumberField IsDedekindDomain ClassFieldTheory
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

private theorem conductorPrimeIdealValue_eq_primeValue
    (ω : A1.HeckeChar F) (v : A1.FinPlace F) :
    ω.idealValue v.asIdeal = ω.primeValue v := by
  classical
  unfold A1.HeckeChar.idealValue
  rw [UniqueFactorizationMonoid.normalizedFactors_irreducible v.irreducible,
    normalize_eq, Multiset.map_singleton, Multiset.prod_singleton]
  rw [dif_pos ⟨v.isPrime, v.ne_bot⟩]

private theorem conductorUnramifiedAt_of_not_dvd
    (ω : A1.HeckeChar F) (I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    (hcond : ω.ConductorDvd I) (v : A1.FinPlace F)
    (hv : ¬ v.asIdeal ∣ I) :
    ω.UnramifiedAt v := by
  have hexp : A1.idealExp v I = 0 := by
    unfold A1.idealExp
    by_contra hne
    have hI' : I ≠ 0 := by simpa [Ideal.zero_eq_bot] using hI
    exact hv ((Associates.count_ne_zero_iff_dvd hI' v.irreducible).mp hne)
  intro u hu huinv
  apply hcond v u hu huinv
  rw [hexp]
  have hsub : (u : v.adicCompletion F) - 1 ∈ v.adicCompletionIntegers F :=
    (v.adicCompletionIntegers F).sub_mem hu (v.adicCompletionIntegers F).one_mem
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at hsub
  simpa using hsub

/-- A common finite/infinite component and residue realization determine the
full idelic character. Guide: sol-thin-a2zf/PROOFS.md:680–693.
Uses HK-DICT-RAY prime-value uniqueness off the finite conductor support.
This is the injectivity clause needed to sum over a subset of residue characters. -/
theorem primitive_conductor_residue_determines (S : A1.SData F CE condη)
    (G : ConductorGenerators S) (ρ : ConductorResidues S)
    (ℓ : SLocalCharacter S) (τ : ConductorInfiniteLocal F)
    (q : S.ExtIdeal) (lambdaq : MulChar (ConductorResidueRing q) ℂ)
    (ω ω' : A1.HeckeChar F) (hω : IsOfFinOrder ω) (hω' : IsOfFinOrder ω')
    (f f' : Ideal (𝓞 F)) (hf : IsPrimitiveConductor ω f)
    (hf' : IsPrimitiveConductor ω' f')
    (hℓ : SComponent S ω = ℓ) (hℓ' : SComponent S ω' = ℓ)
    (hτ : conductorInfiniteComponent ω = τ) (hτ' : conductorInfiniteComponent ω' = τ)
    (h : ConductorResidueRealizes S G ρ ℓ τ q lambdaq ω)
    (h' : ConductorResidueRealizes S G ρ ℓ τ q lambdaq ω') : ω = ω' := by
  sorry

end ArtinPrimitiveRoots.A2
