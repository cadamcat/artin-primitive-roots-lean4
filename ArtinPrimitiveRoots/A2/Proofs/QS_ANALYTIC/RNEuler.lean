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
  ne_bot := mt Ideal.eq_bot_of_under_eq_bot w.ne_bot

/-- RN-E1: the places of `E` above a place of `K` form a finite set. -/
theorem qsa_below_fiber_finite (v : HeightOneSpectrum (𝓞 K)) :
    Set.Finite {w : HeightOneSpectrum (𝓞 E) | qsaBelow K E w = v} := by
  have hfin := IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 E)
  refine (hfin.preimage (Set.injOn_of_injective
    (fun w₁ w₂ h => HeightOneSpectrum.ext h))).subset ?_
  intro w hw
  have hw' : w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 E)) = v.asIdeal :=
    congrArg HeightOneSpectrum.asIdeal hw
  exact ⟨w.isPrime, ⟨hw'.symm⟩⟩

/-- RN-E2a: the Euler product of `ζ_F` over the finite places of `F`. -/
theorem qsa_dedekindZeta_hasProd (F : Type*) [Field F] [NumberField F] {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun w : HeightOneSpectrum (𝓞 F) =>
      (1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹) (dedekindZeta F s) := by
  classical
  have hE := Hecke.LSeriesRay_eulerProduct
    (1 : RayClassGroup (⟨0, ∅⟩ : RayClassModulus F) →* ℂˣ) hs
  rw [Hecke.LSeriesRay_trivial_eq_dedekindZeta] at hE
  have hone : ∀ w : HeightOneSpectrum (𝓞 F),
      Hecke.charValue (1 : RayClassGroup (⟨0, ∅⟩ : RayClassModulus F) →* ℂˣ) w.asIdeal = 1 := by
    intro w
    have hc : Hecke.IsCoprimeTo (⟨0, ∅⟩ : RayClassModulus F) w.asIdeal :=
      ⟨w.ne_bot, by intro v hv; simp at hv⟩
    simp [Hecke.charValue, hc]
  simpa only [hone, one_mul] using hE

/-- RN-E2: the Euler product of `ζ_E`, grouped over the places of `K`. -/
theorem qsa_dedekindZeta_hasProd_fiber {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun v : HeightOneSpectrum (𝓞 K) =>
      ∏ w ∈ (qsa_below_fiber_finite K E v).toFinset,
        (1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹) (dedekindZeta E s) := by
  classical
  have hE := qsa_dedekindZeta_hasProd E hs
  let F : HeightOneSpectrum (𝓞 E) → ℂ :=
    fun w => (1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹
  have h2 : HasProd (F ∘ Equiv.sigmaFiberEquiv (qsaBelow K E)) (dedekindZeta E s) :=
    (Equiv.hasProd_iff _).mpr hE
  refine h2.sigma (fun v => ?_)
  have hv := Finset.hasProd ((qsa_below_fiber_finite K E v).toFinset) F
  let e : {w // qsaBelow K E w = v} ≃
      ((((qsa_below_fiber_finite K E v).toFinset : Finset (HeightOneSpectrum (𝓞 E))) :
        Set (HeightOneSpectrum (𝓞 E)))) :=
    Equiv.subtypeEquivRight (fun w => by simp)
  exact (e.hasProd_iff).mpr hv

end ArtinPrimitiveRoots.A2
