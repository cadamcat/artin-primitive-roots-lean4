import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.Defs
import ArtinPrimitiveRoots.Proofs.a2_cond_b.Split

set_option autoImplicit false
open NumberField IsDedekindDomain ClassFieldTheory
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

private theorem conductorSupported_eq_of_counts (S : A1.SData F CE condη)
    {J K : Ideal (𝓞 F)} (hJ : ConductorSupportedAtS S J)
    (hK : ConductorSupportedAtS S K)
    (hcount : ∀ v : S.Sf,
      Multiset.count v.1.asIdeal (UniqueFactorizationMonoid.normalizedFactors J) =
        Multiset.count v.1.asIdeal (UniqueFactorizationMonoid.normalizedFactors K)) :
    J = K := by
  classical
  let p : Ideal (𝓞 F) → Prop := fun Q => ∃ v ∈ S.Sf, Q = v.asIdeal
  have hJall : ∀ Q ∈ UniqueFactorizationMonoid.normalizedFactors J, p Q := by
    intro Q hQ
    have hQprime : Prime Q := UniqueFactorizationMonoid.prime_of_normalized_factor Q hQ
    let v : HeightOneSpectrum (𝓞 F) := HeightOneSpectrum.ofPrime hQprime
    have hQle : J ≤ Q := (Ideal.mem_normalizedFactors_iff hJ.1).mp hQ |>.2
    have hvdiv : v.asIdeal ∣ J := Ideal.dvd_iff_le.mpr (by simpa [v] using hQle)
    exact ⟨v, hJ.2 v hvdiv, by simp [v]⟩
  have hKall : ∀ Q ∈ UniqueFactorizationMonoid.normalizedFactors K, p Q := by
    intro Q hQ
    have hQprime : Prime Q := UniqueFactorizationMonoid.prime_of_normalized_factor Q hQ
    let v : HeightOneSpectrum (𝓞 F) := HeightOneSpectrum.ofPrime hQprime
    have hQle : K ≤ Q := (Ideal.mem_normalizedFactors_iff hK.1).mp hQ |>.2
    have hvdiv : v.asIdeal ∣ K := Ideal.dvd_iff_le.mpr (by simpa [v] using hQle)
    exact ⟨v, hK.2 v hvdiv, by simp [v]⟩
  have hfac : UniqueFactorizationMonoid.normalizedFactors J =
      UniqueFactorizationMonoid.normalizedFactors K := by
    apply Multiset.ext.mpr
    intro Q
    by_cases hQ : p Q
    · rcases hQ with ⟨v, hv, hQv⟩
      simpa [hQv] using hcount ⟨v, hv⟩
    · have hJnot : Q ∉ UniqueFactorizationMonoid.normalizedFactors J := by
        intro hmem
        exact hQ (hJall Q hmem)
      have hKnot : Q ∉ UniqueFactorizationMonoid.normalizedFactors K := by
        intro hmem
        exact hQ (hKall Q hmem)
      simp [hJnot, hKnot]
  calc
    J = (UniqueFactorizationMonoid.normalizedFactors J).prod :=
      (Ideal.prod_normalizedFactors_eq_self hJ.1).symm
    _ = (UniqueFactorizationMonoid.normalizedFactors K).prod := by rw [hfac]
    _ = K := Ideal.prod_normalizedFactors_eq_self hK.1

private theorem conductorSupported_count_le_log (S : A1.SData F CE condη)
    {J : Ideal (𝓞 F)} (hJ : ConductorSupportedAtS S J) {n : ℕ}
    (hN : Ideal.absNorm J ≤ n) (v : S.Sf) :
    Multiset.count v.1.asIdeal (UniqueFactorizationMonoid.normalizedFactors J) ≤ Nat.log 2 n := by
  classical
  let e := Multiset.count v.1.asIdeal (UniqueFactorizationMonoid.normalizedFactors J)
  have hJpos : 0 < Ideal.absNorm J := by
    rw [Ideal.absNorm_pos_iff_mem_nonZeroDivisors]
    simpa using hJ.1
  have hpowdvd : v.1.asIdeal ^ e ∣ J := by
    have hmaxdvd : v.1.maxPowDividing J ∣ J := by
      change v.1.asIdeal ^
          (Associates.mk v.1.asIdeal).count (Associates.mk J).factors ∣ J
      rw [← Associates.mk_dvd_mk, Associates.mk_pow]
      exact (Associates.prime_pow_dvd_iff_le
        (Associates.mk_ne_zero.mpr hJ.1) v.1.associates_irreducible).2 le_rfl
    rw [← v.1.maxPowDividing_eq_pow_multiset_count hJ.1]
    exact hmaxdvd
  have hnormdvd : Ideal.absNorm (v.1.asIdeal ^ e) ∣ Ideal.absNorm J :=
    Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp hpowdvd)
  have hpowle : Ideal.absNorm (v.1.asIdeal ^ e) ≤ Ideal.absNorm J :=
    Nat.le_of_dvd hJpos hnormdvd
  have hvnorm : 2 ≤ Ideal.absNorm v.1.asIdeal := by
    have h := NumberField.HeightOneSpectrum.one_lt_absNorm v.1
    omega
  have hbase : 2 ^ e ≤ Ideal.absNorm J := by
    calc
      2 ^ e ≤ Ideal.absNorm v.1.asIdeal ^ e := Nat.pow_le_pow_left hvnorm e
      _ = Ideal.absNorm (v.1.asIdeal ^ e) := by simp
      _ ≤ Ideal.absNorm J := hpowle
  exact Nat.le_log_of_pow_le (by norm_num) (hbase.trans hN)

/-- Exact supported/exterior factorization, uniqueness, norm bounds, logarithmic
count, and square-mass partition. Guide: sol-thin-a2zf/PROOFS.md:652–657.
Uses the normalized ideal factorization API; feeds conductor_sieve_assemble and the bridge. -/
theorem ideal_S_exterior_split_count (S : A1.SData F CE condη) :
    (∀ I : Ideal (𝓞 F), I ≠ ⊥ →
      ConductorSupportedAtS S (conductorSPart S I) ∧
      S.IsExterior (conductorExteriorPart S I) ∧
      I = conductorSPart S I * conductorExteriorPart S I ∧
      Ideal.absNorm (conductorSPart S I) ≤ Ideal.absNorm I ∧
      Ideal.absNorm (conductorExteriorPart S I) ≤ Ideal.absNorm I ∧
      (∀ J E : Ideal (𝓞 F), ConductorSupportedAtS S J → S.IsExterior E →
        I = J * E → J = conductorSPart S I ∧ E = conductorExteriorPart S I)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 2 ≤ N →
      ((conductorSPieces S N).card : ℝ) ≤ C * (1 + Real.log N) ^ S.Sf.card) ∧
    (∀ (N : ℝ) (b : Ideal (𝓞 F) → ℂ),
      (∑ J ∈ conductorSPieces S N,
        ∑ I ∈ ((conductorIdealCutoff F N).filter (fun I => I ≠ ⊥ ∧ conductorSPart S I = J)),
          ‖b I‖ ^ 2) =
      ∑ I ∈ ((conductorIdealCutoff F N).filter (fun I => I ≠ ⊥)), ‖b I‖ ^ 2) := by
  refine ⟨?_, ?_, ?_⟩
  · intro I hI
    have hnorm := ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorSplit_norm_le S hI
    refine ⟨ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorSPart_supported S I,
      ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorExteriorPart_exterior S I,
      ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorSplit_factorization_of_ne_bot S hI,
      hnorm.1, hnorm.2, ?_⟩
    intro J E hJ hE hJE
    rcases ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorParts_unique S I J E hJ hE hJE with
      ⟨hJ', hE'⟩
    exact ⟨hJ'.symm, hE'.symm⟩
  · refine ⟨(1 + (Real.log 2)⁻¹) ^ S.Sf.card, ?_, ?_⟩
    · have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      positivity
    · intro N hN
      classical
      let n : ℕ := ⌊N⌋₊
      let k : ℕ := Nat.log 2 n
      let T : Finset (Ideal (𝓞 F)) :=
        (conductorIdealCutoff F N).filter (fun I => I ≠ ⊥)
      let coords : Ideal (𝓞 F) → S.Sf → Fin (k + 1) := fun J v =>
        ⟨min (Multiset.count v.1.asIdeal
          (UniqueFactorizationMonoid.normalizedFactors J)) k,
          Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
      have hdata : ∀ J ∈ conductorSPieces S N,
          ConductorSupportedAtS S J ∧
            (∀ v : S.Sf,
              Multiset.count v.1.asIdeal
                (UniqueFactorizationMonoid.normalizedFactors J) ≤ k) := by
        intro J hJ
        have hJ' : J ∈ T.image (conductorSPart S) := by
          simpa [conductorSPieces, T] using hJ
        obtain ⟨I, hI, hIJ⟩ := Finset.mem_image.mp hJ'
        have hIcut : I ∈ conductorIdealCutoff F N := (Finset.mem_filter.mp hI).1
        have hIne : I ≠ ⊥ := (Finset.mem_filter.mp hI).2
        have hIbound : Ideal.absNorm I ≤ n := by
          simpa [conductorIdealCutoff, n] using hIcut
        have hJbound : Ideal.absNorm J ≤ n := by
          rw [← hIJ]
          exact (ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorSplit_norm_le S hIne).1 |>.trans hIbound
        have hJsupport : ConductorSupportedAtS S J := by
          rw [← hIJ]
          exact ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorSPart_supported S I
        refine ⟨hJsupport, ?_⟩
        intro v
        exact conductorSupported_count_le_log S hJsupport hJbound v
      have hcard : (conductorSPieces S N).card ≤
          Fintype.card (S.Sf → Fin (k + 1)) := by
        refine Finset.card_le_card_of_injOn coords (s := conductorSPieces S N)
          (t := Finset.univ) (by simp) ?_
        intro J hJ K hK hcoords
        apply conductorSupported_eq_of_counts S (hdata J hJ).1 (hdata K hK).1
        intro v
        have hval := congrArg Fin.val (congrFun hcoords v)
        dsimp [coords] at hval
        rw [Nat.min_eq_left ((hdata J hJ).2 v),
          Nat.min_eq_left ((hdata K hK).2 v)] at hval
        exact hval
      have hcardNat : (conductorSPieces S N).card ≤ (k + 1) ^ S.Sf.card := by
        simpa [Fintype.card_fun, Fintype.card_fin] using hcard
      have hcardReal : ((conductorSPieces S N).card : ℝ) ≤
          ((k + 1 : ℕ) : ℝ) ^ S.Sf.card := by exact_mod_cast hcardNat
      have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hnle : (n : ℝ) ≤ N := by
        dsimp [n]
        exact Nat.floor_le (by linarith : 0 ≤ N)
      have hnfloor : 1 ≤ n := by
        dsimp [n]
        exact Nat.le_floor (by exact_mod_cast (show (1 : ℝ) ≤ N by linarith))
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnfloor
      have hNpos : 0 < N := by linarith
      have hpowNat : 2 ^ k ≤ n := by
        dsimp [k]
        exact Nat.pow_log_le_self 2 (by omega)
      have hpowReal : Real.rpow 2 (k : ℝ) ≤ (n : ℝ) := by
        calc
          Real.rpow 2 (k : ℝ) = (2 : ℝ) ^ k := Real.rpow_natCast 2 k
          _ ≤ (n : ℝ) := by exact_mod_cast hpowNat
      have hklogb : (k : ℝ) ≤ Real.logb 2 (n : ℝ) :=
        (Real.le_logb_iff_rpow_le (by norm_num) hnpos).2 hpowReal
      have hlogmono : Real.logb 2 (n : ℝ) ≤ Real.logb 2 N :=
        (Real.logb_le_logb (by norm_num) hnpos hNpos).2 hnle
      have hk : (k : ℝ) ≤ Real.log N / Real.log 2 := by
        calc
          (k : ℝ) ≤ Real.logb 2 (n : ℝ) := hklogb
          _ ≤ Real.logb 2 N := hlogmono
          _ = Real.log N / Real.log 2 := by simp [Real.logb]
      have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by linarith : 1 ≤ N)
      let A : ℝ := 1 + (Real.log 2)⁻¹
      have hA : 0 < A := by dsimp [A]; positivity
      have hscale : ((k + 1 : ℕ) : ℝ) ≤ A * (1 + Real.log N) := by
        rw [Nat.cast_add, Nat.cast_one]
        dsimp [A]
        calc
          (k : ℝ) + 1 ≤ Real.log N / Real.log 2 + 1 := by linarith [hk]
          _ = Real.log N * (Real.log 2)⁻¹ + 1 := by rw [div_eq_mul_inv]
          _ ≤ (1 + (Real.log 2)⁻¹) * (1 + Real.log N) := by
            have hrecip : 0 ≤ (Real.log 2)⁻¹ := inv_nonneg.mpr hl2.le
            nlinarith [mul_nonneg hrecip hlogN]
      have hpowScale : ((k + 1 : ℕ) : ℝ) ^ S.Sf.card ≤
          (A * (1 + Real.log N)) ^ S.Sf.card :=
        pow_le_pow_left₀ (by positivity) hscale _
      calc
        ((conductorSPieces S N).card : ℝ) ≤
            ((k + 1 : ℕ) : ℝ) ^ S.Sf.card := hcardReal
        _ ≤ A ^ S.Sf.card * (1 + Real.log N) ^ S.Sf.card := by
          calc
            _ ≤ (A * (1 + Real.log N)) ^ S.Sf.card := hpowScale
            _ = _ := by rw [mul_pow]
  · intro N b
    classical
    let T : Finset (Ideal (𝓞 F)) :=
      (conductorIdealCutoff F N).filter (fun I => I ≠ ⊥)
    have hfiber :
        (∑ J ∈ T.image (conductorSPart S),
          ∑ I ∈ T.filter (fun I => conductorSPart S I = J), ‖b I‖ ^ 2) =
          ∑ I ∈ T, ‖b I‖ ^ 2 := by
      exact Finset.sum_fiberwise_of_maps_to
        (fun I hI => Finset.mem_image_of_mem _ hI)
        (fun I => ‖b I‖ ^ 2)
    simpa [T, conductorSPieces, Finset.filter_filter, and_assoc, and_left_comm, and_comm]
      using hfiber

end ArtinPrimitiveRoots.A2
