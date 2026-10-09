import ArtinPrimitiveRoots.A1.Proofs.A1_BDATA.DegreeSum

set_option autoImplicit false
open NumberField IsDedekindDomain AlgebraicNumberTheory.Valuations
open scoped BigOperators
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_bdata_sol
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- The residue-prime degree factors in the local sixth-power count equal the global degree factor. -/
theorem residue_degree_product (D : FieldData F) (S : SData F CE condη) :
    (∏ v : S.Sf, nativeResidueCharacteristic v.1 ^
      (nativeCompletionDegree v.1 * padicValNat (nativeResidueCharacteristic v.1) 6)) =
      6 ^ (2 * numComplex F) := by
  classical
  let p (v : FinPlace F) := nativeResidueCharacteristic v
  let d (v : FinPlace F) := nativeCompletionDegree v
  let below (v : FinPlace F) := finitePlaceBelow (K := ℚ) v
  have hp_eq (v : FinPlace F) : p v = Rat.HeightOneSpectrum.natGenerator (below v) := by
    let e := finitePlaceExtensionEquivAbove (K := ℚ) (L := F) (below v)
    let a := e.symm ⟨v, rfl⟩
    have hc : finitePlaceExtensionCentre (K := ℚ) (L := F) (below v) a = v := by
      change (e a).1 = v
      exact congrArg Subtype.val (e.apply_symm_apply ⟨v, rfl⟩)
    have heq := (nativeCompletionInvariants_eq_absoluteInvariants (below v) a).1
    rw [hc] at heq
    exact heq
  have hp_prime (v : FinPlace F) : (p v).Prime := by
    rw [hp_eq]
    exact Rat.HeightOneSpectrum.prime_natGenerator (below v)
  have h6 (v : FinPlace F) : p v ∣ 6 ↔ (6 : 𝓞 F) ∈ v.asIdeal := by
    change nativeResidueCharacteristic v ∣ 6 ↔ (6 : 𝓞 F) ∈ v.asIdeal
    rw [nativeResidueCharacteristic_eq_ringChar, ← ringChar.spec,
      ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    norm_num
  let eQ : FinPlace ℚ ≃ Nat.Primes := Rat.HeightOneSpectrum.primesEquiv
  let w2 := eQ.symm ⟨2, Nat.prime_two⟩
  let w3 := eQ.symm ⟨3, Nat.prime_three⟩
  have hw2 : Rat.HeightOneSpectrum.natGenerator w2 = 2 :=
    congrArg Subtype.val (eQ.apply_symm_apply ⟨2, Nat.prime_two⟩)
  have hw3 : Rat.HeightOneSpectrum.natGenerator w3 = 3 :=
    congrArg Subtype.val (eQ.apply_symm_apply ⟨3, Nat.prime_three⟩)
  have hreal : InfinitePlace.nrRealPlaces F = 0 :=
    NumberField.InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt (by norm_num) D.hζ12
  have hcard := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := F)
  have harch := InfinitePlace.card_add_two_mul_card_eq_rank (K := F)
  rw [hreal, zero_add] at hcard harch
  change numComplex F = InfinitePlace.nrComplexPlaces F at hcard
  rw [← hcard] at harch
  have hdegree : Module.finrank ℚ F = 2 * numComplex F := harch.symm
  have hsum (q : ℕ) (w : FinPlace ℚ)
      (hw : Rat.HeightOneSpectrum.natGenerator w = q) (hq : q ∣ 6) :
      (∑ v : S.Sf, if p v.1 = q then d v.1 else 0) = Module.finrank ℚ F := by
    have hfibre (v : FinPlace F) : p v = q ↔ below v = w := by
      rw [hp_eq, ← hw]
      constructor
      · intro heq
        apply eQ.injective
        exact Subtype.ext heq
      · intro heq
        rw [heq]
    have hmem (v : FinPlace F) (hv : below v = w) : v ∈ S.Sf := by
      apply S.over6 v
      apply (h6 v).mp
      rwa [(hfibre v).mpr hv]
    let : Fintype {v : FinPlace F // below v = w} :=
      Fintype.ofFinset (S.Sf.filter (fun v => p v = q)) (by
        intro v
        simp only [Finset.mem_filter]
        exact ⟨fun h => (hfibre v).mp h.2,
          fun h => ⟨hmem v h, (hfibre v).mpr h⟩⟩)
    calc
      (∑ v : S.Sf, if p v.1 = q then d v.1 else 0) =
          ∑ v ∈ S.Sf, if p v = q then d v else 0 := by
        exact Finset.sum_coe_sort S.Sf (fun v => if p v = q then d v else 0)
      _ = ∑ v ∈ S.Sf.filter (fun v => p v = q), d v := by
        rw [Finset.sum_filter]
      _ = ∑ v : {v : FinPlace F // below v = w}, d v.1 := by
        apply Finset.sum_subtype
        intro v
        simp only [Finset.mem_filter]
        exact ⟨fun h => (hfibre v).mp h.2,
          fun h => ⟨hmem v h, (hfibre v).mpr h⟩⟩
      _ = Module.finrank ℚ F := native_degree_sum w
  have h2 := hsum 2 w2 hw2 (by norm_num)
  have h3 := hsum 3 w3 hw3 (by norm_num)
  have hval2 : padicValNat 2 6 = 1 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [show 6 = 2 * 3 by norm_num, padicValNat.mul (by norm_num) (by norm_num)]
    norm_num [padicValNat.self, padicValNat.eq_zero_of_not_dvd]
  have hval3 : padicValNat 3 6 = 1 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [show 6 = 2 * 3 by norm_num, padicValNat.mul (by norm_num) (by norm_num)]
    norm_num [padicValNat.self, padicValNat.eq_zero_of_not_dvd]
  have hfactor (v : FinPlace F) :
      p v ^ (d v * padicValNat (p v) 6) =
        2 ^ (if p v = 2 then d v else 0) *
        3 ^ (if p v = 3 then d v else 0) := by
    by_cases htwo : p v = 2
    · simp [htwo, hval2]
    by_cases hthree : p v = 3
    · simp [hthree, hval3]
    have hnot : ¬p v ∣ 6 := by
      intro hdiv
      have hdiv' : p v ∣ 2 ∨ p v ∣ 3 :=
        (hp_prime v).dvd_mul.mp (by simpa using hdiv)
      rcases hdiv' with hdiv' | hdiv'
      · exact htwo ((Nat.dvd_prime Nat.prime_two).mp hdiv' |>.resolve_left
          (hp_prime v).ne_one)
      · exact hthree ((Nat.dvd_prime Nat.prime_three).mp hdiv' |>.resolve_left
          (hp_prime v).ne_one)
    simp [htwo, hthree, padicValNat.eq_zero_of_not_dvd hnot]
  change (∏ v : S.Sf, p v.1 ^ (d v.1 * padicValNat (p v.1) 6)) = _
  calc
    (∏ v : S.Sf, p v.1 ^ (d v.1 * padicValNat (p v.1) 6)) =
        ∏ v : S.Sf, 2 ^ (if p v.1 = 2 then d v.1 else 0) *
          3 ^ (if p v.1 = 3 then d v.1 else 0) := by
      apply Finset.prod_congr rfl
      intro v hv
      exact hfactor v.1
    _ = 2 ^ Module.finrank ℚ F * 3 ^ Module.finrank ℚ F := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
        Finset.prod_pow_eq_pow_sum, h2, h3]
    _ = 6 ^ (2 * numComplex F) := by
      rw [← mul_pow, hdegree]
      norm_num

end ArtinPrimitiveRoots.Proofs.a1_bdata_sol
