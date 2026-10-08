import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.Defs

set_option autoImplicit false
open NumberField IsDedekindDomain ClassFieldTheory UniqueFactorizationMonoid
open ArtinPrimitiveRoots.A2
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_cond_b

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

private theorem exists_mem_multiset_prod_of_prime_dvd
    {α : Type*} [CommMonoidWithZero α] {p : α} (hp : Prime p)
    (s : Multiset α) (h : p ∣ s.prod) : ∃ a ∈ s, p ∣ a := by
  induction s using Multiset.induction with
  | empty => exact (hp.not_isUnit (isUnit_iff_dvd_one.mpr (by simpa using h))).elim
  | @cons a s ih =>
      rw [Multiset.prod_cons] at h
      rcases hp.dvd_mul.mp h with ha | hs
      · exact ⟨a, by simp, ha⟩
      · obtain ⟨q, hq, hqdiv⟩ := ih hs
        exact ⟨q, by simp [hq], hqdiv⟩

theorem conductorSPart_supported (S : A1.SData F CE condη)
    (I : Ideal (𝓞 F)) : ConductorSupportedAtS S (conductorSPart S I) := by
  classical
  let p : Ideal (𝓞 F) → Prop := fun Q => ∃ v ∈ S.Sf, Q = v.asIdeal
  have hne : (conductorSPart S I) ≠ ⊥ := by
    unfold conductorSPart
    apply Multiset.prod_ne_zero
    intro hzero
    have hmem := Multiset.mem_of_mem_filter hzero
    exact (UniqueFactorizationMonoid.prime_of_normalized_factor _ hmem).ne_zero rfl
  refine ⟨hne, ?_⟩
  intro v hv
  change v.asIdeal ∣ ((UniqueFactorizationMonoid.normalizedFactors I).filter p).prod at hv
  obtain ⟨Q, hQ, hvQ⟩ := exists_mem_multiset_prod_of_prime_dvd v.prime _ hv
  rcases (Multiset.mem_filter.mp hQ).2 with ⟨w, hwS, hQw⟩
  have hQprime : Prime Q :=
    UniqueFactorizationMonoid.prime_of_normalized_factor _ (Multiset.mem_of_mem_filter hQ)
  have hQeq : v.asIdeal = Q :=
    associated_iff_eq.mp ((Prime.dvd_prime_iff_associated v.prime hQprime).mp hvQ)
  have hvw : v = w := HeightOneSpectrum.ext (hQeq.trans hQw)
  simpa [hvw] using hwS

theorem conductorExteriorPart_exterior (S : A1.SData F CE condη)
    (I : Ideal (𝓞 F)) : S.IsExterior (conductorExteriorPart S I) := by
  classical
  let p : Ideal (𝓞 F) → Prop := fun Q => ∃ v ∈ S.Sf, Q = v.asIdeal
  have hne : (conductorExteriorPart S I) ≠ ⊥ := by
    unfold conductorExteriorPart
    apply Multiset.prod_ne_zero
    intro hzero
    have hmem := Multiset.mem_of_mem_filter hzero
    exact (UniqueFactorizationMonoid.prime_of_normalized_factor _ hmem).ne_zero rfl
  refine ⟨hne, ?_⟩
  intro v hvS hle
  have hvdiv : v.asIdeal ∣ conductorExteriorPart S I := Ideal.dvd_iff_le.mpr hle
  change v.asIdeal ∣ ((UniqueFactorizationMonoid.normalizedFactors I).filter (fun Q => ¬ p Q)).prod at hvdiv
  obtain ⟨Q, hQ, hvQ⟩ := exists_mem_multiset_prod_of_prime_dvd v.prime _ hvdiv
  have hnot : ¬ p Q := (Multiset.mem_filter.mp hQ).2
  have hQprime : Prime Q :=
    UniqueFactorizationMonoid.prime_of_normalized_factor _ (Multiset.mem_of_mem_filter hQ)
  have hQeq : Q = v.asIdeal :=
    (associated_iff_eq.mp ((Prime.dvd_prime_iff_associated v.prime hQprime).mp hvQ)).symm
  exact hnot ⟨v, hvS, hQeq⟩

theorem conductorParts_unique (S : A1.SData F CE condη)
    (I J E : Ideal (𝓞 F))
    (hJ : ConductorSupportedAtS S J) (hE : S.IsExterior E) (hIE : I = J * E) :
    conductorSPart S I = J ∧ conductorExteriorPart S I = E := by
  classical
  let p : Ideal (𝓞 F) → Prop := fun Q => ∃ v ∈ S.Sf, Q = v.asIdeal
  have hnorm : UniqueFactorizationMonoid.normalizedFactors I =
      UniqueFactorizationMonoid.normalizedFactors J + UniqueFactorizationMonoid.normalizedFactors E := by
    rw [hIE, UniqueFactorizationMonoid.normalizedFactors_mul hJ.1 hE.1]
  have hJall : ∀ Q ∈ UniqueFactorizationMonoid.normalizedFactors J, p Q := by
    intro Q hQ
    have hQprime : Prime Q := UniqueFactorizationMonoid.prime_of_normalized_factor Q hQ
    let v : HeightOneSpectrum (𝓞 F) := HeightOneSpectrum.ofPrime hQprime
    have hQle : J ≤ Q := (Ideal.mem_normalizedFactors_iff hJ.1).mp hQ |>.2
    have hvdiv : v.asIdeal ∣ J := Ideal.dvd_iff_le.mpr (by simpa [v] using hQle)
    exact ⟨v, hJ.2 v hvdiv, by simp [v]⟩
  have hEnot : ∀ Q ∈ UniqueFactorizationMonoid.normalizedFactors E, ¬ p Q := by
    intro Q hQ hPQ
    rcases hPQ with ⟨v, hvS, hQv⟩
    have hQle : E ≤ Q := (Ideal.mem_normalizedFactors_iff hE.1).mp hQ |>.2
    apply hE.2 v hvS
    simpa [hQv] using hQle
  have hJfilter :
      (UniqueFactorizationMonoid.normalizedFactors J).filter p =
        UniqueFactorizationMonoid.normalizedFactors J :=
    Multiset.filter_eq_self.mpr hJall
  have hEfilter :
      (UniqueFactorizationMonoid.normalizedFactors E).filter p = 0 :=
    Multiset.filter_eq_nil.mpr hEnot
  have hJfilterNot :
      (UniqueFactorizationMonoid.normalizedFactors J).filter (fun Q => ¬ p Q) = 0 :=
    Multiset.filter_eq_nil.mpr fun Q hQ => not_not.mpr (hJall Q hQ)
  have hEfilterNot :
      (UniqueFactorizationMonoid.normalizedFactors E).filter (fun Q => ¬ p Q) =
        UniqueFactorizationMonoid.normalizedFactors E :=
    Multiset.filter_eq_self.mpr hEnot
  constructor
  · change ((UniqueFactorizationMonoid.normalizedFactors I).filter p).prod = J
    rw [hnorm, Multiset.filter_add, hJfilter, hEfilter]
    simpa using (Ideal.prod_normalizedFactors_eq_self hJ.1)
  · change ((UniqueFactorizationMonoid.normalizedFactors I).filter (fun Q => ¬ p Q)).prod = E
    rw [hnorm, Multiset.filter_add, hJfilterNot, hEfilterNot]
    simpa using (Ideal.prod_normalizedFactors_eq_self hE.1)

theorem conductorSplit_factorization_of_ne_bot (S : A1.SData F CE condη)
    {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    I = conductorSPart S I * conductorExteriorPart S I := by
  calc
    I = (UniqueFactorizationMonoid.normalizedFactors I).prod :=
      (Ideal.prod_normalizedFactors_eq_self hI).symm
    _ = _ := by
      simpa [conductorSPart, conductorExteriorPart] using
        (Multiset.prod_filter_mul_prod_filter_not
          (p := fun P : Ideal (𝓞 F) => ∃ v ∈ S.Sf, P = v.asIdeal)
          (s := UniqueFactorizationMonoid.normalizedFactors I)).symm

theorem conductorSplit_norm_le (S : A1.SData F CE condη)
    {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    Ideal.absNorm (conductorSPart S I) ≤ Ideal.absNorm I ∧
      Ideal.absNorm (conductorExteriorPart S I) ≤ Ideal.absNorm I := by
  have hsplit := conductorSplit_factorization_of_ne_bot S hI
  have hS := conductorSPart_supported S I
  have hE := conductorExteriorPart_exterior S I
  have hEnorm : 1 ≤ Ideal.absNorm (conductorExteriorPart S I) :=
    Nat.one_le_iff_ne_zero.mpr (by
      intro hzero
      exact hE.1 (Ideal.absNorm_eq_zero_iff.mp hzero))
  have hSnorm : 1 ≤ Ideal.absNorm (conductorSPart S I) :=
    Nat.one_le_iff_ne_zero.mpr (by
      intro hzero
      exact hS.1 (Ideal.absNorm_eq_zero_iff.mp hzero))
  have hnorm : Ideal.absNorm I =
      Ideal.absNorm (conductorSPart S I) * Ideal.absNorm (conductorExteriorPart S I) := by
    have h := congrArg Ideal.absNorm hsplit
    simpa only [map_mul] using h
  constructor
  · calc
      Ideal.absNorm (conductorSPart S I) =
          Ideal.absNorm (conductorSPart S I) * 1 := by simp
      _ ≤ Ideal.absNorm (conductorSPart S I) *
          Ideal.absNorm (conductorExteriorPart S I) := Nat.mul_le_mul_left _ hEnorm
      _ = Ideal.absNorm I := hnorm.symm
  · calc
      Ideal.absNorm (conductorExteriorPart S I) =
          1 * Ideal.absNorm (conductorExteriorPart S I) := by simp
      _ ≤ Ideal.absNorm (conductorSPart S I) *
          Ideal.absNorm (conductorExteriorPart S I) := Nat.mul_le_mul_right _ hSnorm
      _ = Ideal.absNorm I := hnorm.symm

end ArtinPrimitiveRoots.Proofs.a2_cond_b
