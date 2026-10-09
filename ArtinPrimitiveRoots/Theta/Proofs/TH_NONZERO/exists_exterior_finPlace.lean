import ArtinPrimitiveRoots.A1.Field

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

/-- There is a finite place outside the finite exceptional set: lift a
rational prime exceeding the norms of all primes under that set. -/
theorem exists_exterior_finPlace {CE : ℕ} {condη : Ideal (𝓞 F)}
    (S : SData F CE condη) : ∃ v : FinPlace F, v ∉ S.Sf := by
  let N := S.Sf.sup (fun v => Ideal.absNorm (v.asIdeal.under ℤ))
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (N + 1)
  let : Fact (Nat.Prime p) := ⟨hp⟩
  let I : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hI : I ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  have hker : RingHom.ker (algebraMap ℤ (𝓞 F)) = ⊥ := by
    exact (RingHom.injective_iff_ker_eq_bot _).mp
      (FaithfulSMul.algebraMap_injective ℤ (𝓞 F))
  obtain ⟨Q, hQ, hUnder⟩ := I.exists_ideal_over_prime_of_isIntegral_of_isDomain
    (S := 𝓞 F) (by rw [hker]; exact bot_le)
  have hQne : Q ≠ ⊥ := by
    intro hzero
    apply hI
    rw [← hUnder, hzero, Ideal.under_bot]
  let v : FinPlace F := ⟨Q, hQ, hQne⟩
  refine ⟨v, ?_⟩
  intro hv
  have hnorm : Ideal.absNorm (v.asIdeal.under ℤ) = p := by
    rw [hUnder]
    simp [I]
  have hle : Ideal.absNorm (v.asIdeal.under ℤ) ≤ N :=
    Finset.le_sup (f := fun w : FinPlace F => Ideal.absNorm (w.asIdeal.under ℤ)) hv
  rw [hnorm] at hle
  omega

end ArtinPrimitiveRoots.A1.Theta
