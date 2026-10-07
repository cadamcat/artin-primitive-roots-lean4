import ArtinPrimitiveRoots.Spec.Geometry

/-! Reduction-theory nodes R1--R14. This first stage states the nodes that can start against
the frozen interface. -/

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- Every element of a number field has an integral multiple by a positive rational integer. -/
theorem exists_positive_denominatorBound (a : F) :
    ∃ D : ℕ, 0 < D ∧ HasDenominatorBound F D a := by
  have ha : IsAlgebraic ℤ a :=
    IsFractionRing.isAlgebraic_iff ℤ _ _ |>.mpr (.of_finite ℚ a)
  obtain ⟨D, b, hD, hb⟩ := ha.exists_nsmul_eq (𝓞 F)
  have hDpos : 0 < D := Nat.pos_of_ne_zero hD
  refine ⟨D, hDpos, ⟨b, ?_⟩⟩
  simpa [HasDenominatorBound, Nat.cast_mul, nsmul_eq_mul] using hb

theorem hasDenominatorBound_mono {D E : ℕ} (hDE : D ∣ E) {a : F}
    (ha : HasDenominatorBound F D a) : HasDenominatorBound F E a := by
  obtain ⟨b, hb⟩ := ha
  obtain ⟨k, rfl⟩ := hDE
  refine ⟨(k : 𝓞 F) * b, ?_⟩
  change ((D * k : ℕ) : F) * a = algebraMap (𝓞 F) F ((k : 𝓞 F) * b)
  rw [Nat.cast_mul]
  calc
    (D : F) * (k : F) * a = (k : F) * ((D : F) * a) := by ring
    _ = (k : F) * algebraMap (𝓞 F) F b := by rw [hb]
    _ = algebraMap (𝓞 F) F ((k : 𝓞 F) * b) := by simp

theorem hasDenominatorBound_mul {D E : ℕ} {a b : F}
    (ha : HasDenominatorBound F D a) (hb : HasDenominatorBound F E b) :
    HasDenominatorBound F (D * E) (a * b) := by
  obtain ⟨a₀, ha₀⟩ := ha
  obtain ⟨b₀, hb₀⟩ := hb
  refine ⟨a₀ * b₀, ?_⟩
  change ((D * E : ℕ) : F) * (a * b) =
    algebraMap (𝓞 F) F (a₀ * b₀)
  rw [Nat.cast_mul]
  calc
    (D : F) * (E : F) * (a * b) = ((D : F) * a) * ((E : F) * b) := by ring
    _ = algebraMap (𝓞 F) F a₀ * algebraMap (𝓞 F) F b₀ := by rw [ha₀, hb₀]
    _ = algebraMap (𝓞 F) F (a₀ * b₀) := by simp

theorem hasDenominatorBound_add {D E : ℕ} {a b : F}
    (ha : HasDenominatorBound F D a) (hb : HasDenominatorBound F E b) :
    HasDenominatorBound F (D * E) (a + b) := by
  obtain ⟨a₀, ha₀⟩ := ha
  obtain ⟨b₀, hb₀⟩ := hb
  refine ⟨(E : 𝓞 F) * a₀ + (D : 𝓞 F) * b₀, ?_⟩
  change ((D * E : ℕ) : F) * (a + b) =
    algebraMap (𝓞 F) F ((E : 𝓞 F) * a₀ + (D : 𝓞 F) * b₀)
  rw [Nat.cast_mul]
  calc
    (D : F) * (E : F) * (a + b) =
        (E : F) * ((D : F) * a) + (D : F) * ((E : F) * b) := by ring
    _ = (E : F) * algebraMap (𝓞 F) F a₀ + (D : F) * algebraMap (𝓞 F) F b₀ :=
      by rw [ha₀, hb₀]
    _ = algebraMap (𝓞 F) F ((E : 𝓞 F) * a₀ + (D : 𝓞 F) * b₀) := by simp

theorem exists_common_denominatorBound {ι : Type} [Fintype ι] (a : ι → F) :
    ∃ D : ℕ, 0 < D ∧ ∀ i, HasDenominatorBound F D (a i) := by
  classical
  choose d hd hbound using fun i : ι => exists_positive_denominatorBound (a i)
  refine ⟨∏ i, d i, Finset.prod_pos fun i hi => hd i, fun i => ?_⟩
  exact hasDenominatorBound_mono (Finset.dvd_prod_of_mem d (Finset.mem_univ i)) (hbound i)

theorem exists_matrix_denominatorBound (M : Matrix (Fin 2) (Fin 2) F) :
    ∃ D : ℕ, 0 < D ∧ ∀ i j, HasDenominatorBound F D (M i j) := by
  obtain ⟨D, hD, h⟩ := exists_common_denominatorBound (fun p : Fin 2 × Fin 2 => M p.1 p.2)
  exact ⟨D, hD, fun i j => h (i, j)⟩

theorem conjugated_lowerLeft_denominatorBound (σ σ' : SL(2,F)) :
    ∃ D : ℕ, 0 < D ∧ ∀ γ : SL(2,𝓞 F),
      HasDenominatorBound F D ((σ'⁻¹ * toSLF F γ * σ) 1 0) := by
  classical
  let A : Matrix (Fin 2) (Fin 2) F := (σ'⁻¹ : SL(2,F))
  let B : Matrix (Fin 2) (Fin 2) F := (σ : SL(2,F))
  obtain ⟨D₁, hD₁, hA⟩ := exists_matrix_denominatorBound A
  obtain ⟨D₂, hD₂, hB⟩ := exists_matrix_denominatorBound B
  let E := D₁ * D₂
  have hD : 0 < ((E * E) * (E * E)) := by
    dsimp [E]
    positivity
  refine ⟨(E * E) * (E * E), hD, ?_⟩
  intro γ
  let q : Fin 2 → Fin 2 → F := fun i j => A 1 i * algebraMap (𝓞 F) F (γ i j) * B j 0
  have hγ (i j : Fin 2) :
      HasDenominatorBound F 1 (algebraMap (𝓞 F) F (γ i j)) := by
    exact ⟨γ i j, by simp⟩
  have hq (i j : Fin 2) : HasDenominatorBound F E (q i j) := by
    simpa [q, E, mul_assoc] using
      hasDenominatorBound_mul (hasDenominatorBound_mul (hA 1 i) (hγ i j)) (hB j 0)
  have hsum : HasDenominatorBound F ((E * E) * (E * E))
      (q 0 0 + q 0 1 + (q 1 0 + q 1 1)) := by
    have hleft := hasDenominatorBound_add (hq 0 0) (hq 0 1)
    have hright := hasDenominatorBound_add (hq 1 0) (hq 1 1)
    simpa [Nat.mul_assoc] using hasDenominatorBound_add hleft hright
  have hentry : (σ'⁻¹ * toSLF F γ * σ) 1 0 =
      q 0 0 + q 0 1 + (q 1 0 + q 1 1) := by
    change ((A * (toSLF F γ : Matrix (Fin 2) (Fin 2) F) * B) 1 0) = _
    simp [q, toSLF, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  exact hentry ▸ hsum

theorem absFieldNorm_mul (a b : F) :
    absFieldNorm F (a * b) = absFieldNorm F a * absFieldNorm F b := by
  simp [absFieldNorm, Complex.norm_mul, mul_pow, Finset.prod_mul_distrib]

theorem absFieldNorm_pos_of_ne_zero {a : F} (ha : a ≠ 0) : 0 < absFieldNorm F a := by
  unfold absFieldNorm
  apply Finset.prod_pos
  intro w hw
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  exact (map_ne_zero_iff _ w.embedding.injective).mpr ha

theorem absFieldNorm_ge_one_of_ringInteger (a : 𝓞 F) (ha : a ≠ 0) :
    1 ≤ absFieldNorm F (algebraMap (𝓞 F) F a) := by
  rw [absFieldNorm_eq_abs_norm, ← Algebra.coe_norm_int]
  exact_mod_cast Int.one_le_abs (Algebra.norm_ne_zero_iff.mpr ha)

theorem absFieldNorm_inv_le_of_denominatorBound {D : ℕ} (hD : 0 < D) {a : F}
    (ha : HasDenominatorBound F D a) (ha0 : a ≠ 0) :
    (absFieldNorm F a)⁻¹ ≤ absFieldNorm F (D : F) := by
  obtain ⟨b, hb⟩ := ha
  have hD0 : (D : F) ≠ 0 := by exact_mod_cast hD.ne'
  have hb0 : b ≠ 0 := by
    intro hz
    subst b
    simp only [map_zero] at hb
    exact ha0 ((mul_eq_zero.mp (by simpa using hb)).resolve_left hD0)
  have hnormInt := absFieldNorm_ge_one_of_ringInteger b hb0
  have hnormMul : absFieldNorm F (algebraMap (𝓞 F) F b) =
      absFieldNorm F (D : F) * absFieldNorm F a := by
    rw [← hb, absFieldNorm_mul]
  rw [hnormMul] at hnormInt
  have hna := absFieldNorm_pos_of_ne_zero ha0
  have htmp : (1 : ℝ) * (absFieldNorm F a)⁻¹ ≤ absFieldNorm F (D : F) :=
    (mul_inv_le_iff₀' hna).2 (by simpa [mul_comm] using hnormInt)
  simpa using htmp

theorem cuspLattice_mem_iff (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F)) (μ : F) :
    μ ∈ cuspLattice F Γ σ ↔
      ∃ γ : Γ, σ * upperHom F (Multiplicative.ofAdd μ) * σ⁻¹ =
        toSLF F (γ : SL(2,𝓞 F)) := by
  constructor
  · intro h
    have hm : Multiplicative.ofAdd μ ∈
        (Γ.map (toSLF F)).comap
          ((MulAut.conj σ).toMonoidHom.comp (upperHom F)) := by
      simpa [cuspLattice] using h
    rcases Subgroup.mem_map.mp (Subgroup.mem_comap.mp hm) with ⟨γ, hγ, hEq⟩
    exact ⟨⟨γ, hγ⟩, hEq.symm⟩
  · rintro ⟨γ, hEq⟩
    have hm : Multiplicative.ofAdd μ ∈
        (Γ.map (toSLF F)).comap
          ((MulAut.conj σ).toMonoidHom.comp (upperHom F)) := by
      exact Subgroup.mem_comap.mpr <|
        Subgroup.mem_map.mpr ⟨(γ : SL(2,𝓞 F)), γ.property, hEq.symm⟩
    simpa [cuspLattice] using hm

theorem conjugate_signed_translation_entries (σ : SL(2,F)) (ε : (𝓞 F)ˣ) (μ : F)
    (hε : (algebraMap (𝓞 F) F (ε : 𝓞 F)) ^ 2 = 1) :
    ((σ * signedCuspTranslationMatrix F ε μ hε * σ⁻¹) 0 1 =
        algebraMap (𝓞 F) F (ε : 𝓞 F) * μ * (σ 0 0) ^ 2) ∧
    ((σ * signedCuspTranslationMatrix F ε μ hε * σ⁻¹) 1 0 =
        -(algebraMap (𝓞 F) F (ε : 𝓞 F) * μ * (σ 1 0) ^ 2)) := by
  constructor
  · simp only [Matrix.SpecialLinearGroup.coe_mul]
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      signedCuspTranslationMatrix, Matrix.mul_apply, Fin.sum_univ_two]
    <;> ring
  · simp only [Matrix.SpecialLinearGroup.coe_mul]
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      signedCuspTranslationMatrix, Matrix.mul_apply, Fin.sum_univ_two]
    <;> ring

theorem signedCuspTranslationMatrix_mul (ε η : (𝓞 F)ˣ) (μ ν : F)
    (hε : (algebraMap (𝓞 F) F (ε : 𝓞 F)) ^ 2 = 1)
    (hη : (algebraMap (𝓞 F) F (η : 𝓞 F)) ^ 2 = 1)
    (hεη : (algebraMap (𝓞 F) F ((ε * η : (𝓞 F)ˣ) : 𝓞 F)) ^ 2 = 1) :
    signedCuspTranslationMatrix F ε μ hε * signedCuspTranslationMatrix F η ν hη =
      signedCuspTranslationMatrix F (ε * η) (μ + ν) hεη := by
  apply Subtype.ext
  change !![algebraMap (𝓞 F) F (ε : 𝓞 F), algebraMap (𝓞 F) F (ε : 𝓞 F) * μ;
      0, algebraMap (𝓞 F) F (ε : 𝓞 F)] *
      !![algebraMap (𝓞 F) F (η : 𝓞 F), algebraMap (𝓞 F) F (η : 𝓞 F) * ν;
        0, algebraMap (𝓞 F) F (η : 𝓞 F)] =
    !![algebraMap (𝓞 F) F ((ε * η : (𝓞 F)ˣ) : 𝓞 F),
      algebraMap (𝓞 F) F ((ε * η : (𝓞 F)ˣ) : 𝓞 F) * (μ + ν);
      0, algebraMap (𝓞 F) F ((ε * η : (𝓞 F)ˣ) : 𝓞 F)]
  rw [Matrix.mul_fin_two]
  simp only [Units.val_mul, map_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

theorem signedCuspTranslations_zero (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F)) :
    (0 : F) ∈ signedCuspTranslations F Γ σ := by
  let h1 : (algebraMap (𝓞 F) F ((1 : (𝓞 F)ˣ) : 𝓞 F)) ^ 2 = 1 := by simp
  refine ⟨1, h1, 1, ?_⟩
  have hs : signedCuspTranslationMatrix F 1 0 h1 = 1 := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [signedCuspTranslationMatrix]
  simp [hs]

theorem signedCuspTranslations_add (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    {μ ν : F} (hμ : μ ∈ signedCuspTranslations F Γ σ)
    (hν : ν ∈ signedCuspTranslations F Γ σ) :
    μ + ν ∈ signedCuspTranslations F Γ σ := by
  rcases hμ with ⟨ε, hε, γ, hγ⟩
  rcases hν with ⟨η, hη, δ, hδ⟩
  let hεη : (algebraMap (𝓞 F) F ((ε * η : (𝓞 F)ˣ) : 𝓞 F)) ^ 2 = 1 := by
    change (algebraMap (𝓞 F) F (ε : 𝓞 F) * algebraMap (𝓞 F) F (η : 𝓞 F)) ^ 2 = 1
    rw [mul_pow, hε, hη]
    ring
  refine ⟨ε * η, hεη, γ * δ, ?_⟩
  calc
    σ⁻¹ * toSLF F ((γ * δ : Γ) : SL(2,𝓞 F)) * σ =
        (σ⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * σ) *
          (σ⁻¹ * toSLF F (δ : SL(2,𝓞 F)) * σ) := by
            have hm : toSLF F ((γ * δ : Γ) : SL(2,𝓞 F)) =
                toSLF F (γ : SL(2,𝓞 F)) * toSLF F (δ : SL(2,𝓞 F)) := by simp
            rw [hm]
            group
    _ = signedCuspTranslationMatrix F ε μ hε *
        signedCuspTranslationMatrix F η ν hη := by rw [hγ, hδ]
    _ = signedCuspTranslationMatrix F (ε * η) (μ + ν) hεη := by
      exact signedCuspTranslationMatrix_mul ε η μ ν hε hη hεη

theorem signedCuspTranslations_neg (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    {μ : F} (hμ : μ ∈ signedCuspTranslations F Γ σ) :
    -μ ∈ signedCuspTranslations F Γ σ := by
  rcases hμ with ⟨ε, hε, γ, hγ⟩
  have hmul : signedCuspTranslationMatrix F ε (-μ) hε *
      signedCuspTranslationMatrix F ε μ hε = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    dsimp only [signedCuspTranslationMatrix]
    change !![algebraMap (𝓞 F) F (ε : 𝓞 F),
        algebraMap (𝓞 F) F (ε : 𝓞 F) * (-μ); 0, algebraMap (𝓞 F) F (ε : 𝓞 F)] *
      !![algebraMap (𝓞 F) F (ε : 𝓞 F), algebraMap (𝓞 F) F (ε : 𝓞 F) * μ;
        0, algebraMap (𝓞 F) F (ε : 𝓞 F)] = (1 : Matrix (Fin 2) (Fin 2) F)
    rw [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [pow_two] using hε
    · simp <;> ring
    · simp
    · simpa [pow_two] using hε
  have hinv : (signedCuspTranslationMatrix F ε μ hε)⁻¹ =
      signedCuspTranslationMatrix F ε (-μ) hε :=
    (eq_inv_of_mul_eq_one_left hmul).symm
  refine ⟨ε, hε, γ⁻¹, ?_⟩
  calc
    σ⁻¹ * toSLF F ((γ⁻¹ : Γ) : SL(2,𝓞 F)) * σ =
        (σ⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * σ)⁻¹ := by
          have hm : toSLF F ((γ⁻¹ : Γ) : SL(2,𝓞 F)) =
              (toSLF F (γ : SL(2,𝓞 F)))⁻¹ := by simp
          rw [hm]
          group
    _ = signedCuspTranslationMatrix F ε (-μ) hε := by rw [hγ, hinv]

theorem signedCuspTranslationMatrix_inv (ε : (𝓞 F)ˣ) (μ : F)
    (hε : (algebraMap (𝓞 F) F (ε : 𝓞 F)) ^ 2 = 1) :
    (signedCuspTranslationMatrix F ε μ hε)⁻¹ =
      signedCuspTranslationMatrix F ε (-μ) hε := by
  have hmul : signedCuspTranslationMatrix F ε (-μ) hε *
      signedCuspTranslationMatrix F ε μ hε = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    dsimp only [signedCuspTranslationMatrix]
    change !![algebraMap (𝓞 F) F (ε : 𝓞 F),
        algebraMap (𝓞 F) F (ε : 𝓞 F) * (-μ); 0, algebraMap (𝓞 F) F (ε : 𝓞 F)] *
      !![algebraMap (𝓞 F) F (ε : 𝓞 F), algebraMap (𝓞 F) F (ε : 𝓞 F) * μ;
        0, algebraMap (𝓞 F) F (ε : 𝓞 F)] = (1 : Matrix (Fin 2) (Fin 2) F)
    rw [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [pow_two] using hε
    · simp <;> ring
    · simp
    · simpa [pow_two] using hε
  exact (eq_inv_of_mul_eq_one_left hmul).symm

theorem signedTranslationMatrix_one_eq_upperHom (μ : F) :
    signedCuspTranslationMatrix F 1 μ (by simp) =
      upperHom F (Multiplicative.ofAdd μ) := by
  let h1 : (algebraMap (𝓞 F) F ((1 : (𝓞 F)ˣ) : 𝓞 F)) ^ 2 = 1 := by simp
  have hU : (upperHom F (Multiplicative.ofAdd μ) : Matrix (Fin 2) (Fin 2) F) =
      !![1, μ; 0, 1] := by rfl
  have hT : (signedCuspTranslationMatrix F 1 μ h1 : Matrix (Fin 2) (Fin 2) F) =
      !![1, μ; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [signedCuspTranslationMatrix]
  apply Subtype.ext
  exact hT.trans hU.symm

theorem signedCuspTranslation_sign (ε : (𝓞 F)ˣ)
    (hε : (algebraMap (𝓞 F) F (ε : 𝓞 F)) ^ 2 = 1) : ε = 1 ∨ ε = -1 := by
  let x : F := algebraMap (𝓞 F) F (ε : 𝓞 F)
  have hfactor : (x - 1) * (x + 1) = 0 := by
    calc
      (x - 1) * (x + 1) = x ^ 2 - 1 := by ring
      _ = 0 := by dsimp [x]; rw [hε]; ring
  rcases mul_eq_zero.mp hfactor with hminus | hplus
  · have hx : x = 1 := sub_eq_zero.mp hminus
    left
    apply Units.ext
    apply (FaithfulSMul.algebraMap_injective (𝓞 F) F)
    simpa [x] using hx
  · have hx : x = -1 := by
      calc
        x = x + 1 - 1 := by ring
        _ = 0 - 1 := by rw [hplus]
        _ = -1 := by ring
    right
    apply Units.ext
    apply (FaithfulSMul.algebraMap_injective (𝓞 F) F)
    simpa [x] using hx

theorem cuspLattice_subset_signed (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F)) :
    cuspLattice F Γ σ ≤ (AddSubgroup.closure (signedCuspTranslations F Γ σ)) := by
  intro μ hμ
  obtain ⟨γ, hconj⟩ := (cuspLattice_mem_iff Γ σ μ).mp hμ
  have h1 : (algebraMap (𝓞 F) F ((1 : (𝓞 F)ˣ) : 𝓞 F)) ^ 2 = 1 := by simp
  refine AddSubgroup.subset_closure ⟨1, h1, γ, ?_⟩
  calc
    σ⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * σ =
        σ⁻¹ * (σ * upperHom F (Multiplicative.ofAdd μ) * σ⁻¹) * σ := by rw [hconj]
    _ = upperHom F (Multiplicative.ofAdd μ) := by group
    _ = signedCuspTranslationMatrix F 1 μ h1 := by
      symm
      exact signedTranslationMatrix_one_eq_upperHom μ

theorem cuspLattice_of_signed_unit_one (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (μ : F) (ε : (𝓞 F)ˣ) (hε : (algebraMap (𝓞 F) F (ε : 𝓞 F)) ^ 2 = 1)
    (γ : Γ) (hconj : σ⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * σ =
      signedCuspTranslationMatrix F ε μ hε) (he : ε = 1) :
    μ ∈ cuspLattice F Γ σ := by
  subst ε
  have h1 : (algebraMap (𝓞 F) F ((1 : (𝓞 F)ˣ) : 𝓞 F)) ^ 2 = 1 := by simp
  have hT : signedCuspTranslationMatrix F 1 μ hε =
      upperHom F (Multiplicative.ofAdd μ) := by
    have hT' := signedTranslationMatrix_one_eq_upperHom μ
    exact hT'
  have hfield : σ * upperHom F (Multiplicative.ofAdd μ) * σ⁻¹ =
      toSLF F (γ : SL(2,𝓞 F)) := by
    calc
      σ * upperHom F (Multiplicative.ofAdd μ) * σ⁻¹ =
          σ * signedCuspTranslationMatrix F 1 μ hε * σ⁻¹ := by rw [hT]
      _ = σ * (σ⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * σ) * σ⁻¹ := by rw [hconj]
      _ = toSLF F (γ : SL(2,𝓞 F)) := by group
  exact (cuspLattice_mem_iff Γ σ μ).2 ⟨γ, hfield⟩

def denominatorBoundSubgroup (D : ℕ) : AddSubgroup F where
  carrier := {μ | HasDenominatorBound F D μ}
  zero_mem' := by
    refine ⟨0, ?_⟩
    simp [HasDenominatorBound]
  add_mem' := by
    intro a b ha hb
    obtain ⟨a₀, ha₀⟩ := ha
    obtain ⟨b₀, hb₀⟩ := hb
    refine ⟨a₀ + b₀, ?_⟩
    change (D : F) * (a + b) = algebraMap (𝓞 F) F (a₀ + b₀)
    calc
      (D : F) * (a + b) = (D : F) * a + (D : F) * b := by ring
      _ = algebraMap (𝓞 F) F a₀ + algebraMap (𝓞 F) F b₀ := by rw [ha₀, hb₀]
      _ = algebraMap (𝓞 F) F (a₀ + b₀) := by simp
  neg_mem' := by
    intro a ha
    obtain ⟨a₀, ha₀⟩ := ha
    refine ⟨-a₀, ?_⟩
    change (D : F) * (-a) = algebraMap (𝓞 F) F (-a₀)
    calc
      (D : F) * (-a) = -((D : F) * a) := by ring
      _ = -algebraMap (𝓞 F) F a₀ := by rw [ha₀]
      _ = algebraMap (𝓞 F) F (-a₀) := by simp

theorem conjugate_upperHom_entries (σ : SL(2,F)) (μ : F) :
    ((σ * upperHom F (Multiplicative.ofAdd μ) * σ⁻¹) 0 1 = μ * (σ 0 0) ^ 2) ∧
    ((σ * upperHom F (Multiplicative.ofAdd μ) * σ⁻¹) 1 0 = -μ * (σ 1 0) ^ 2) := by
  let h1 : (algebraMap (𝓞 F) F ((1 : (𝓞 F)ˣ) : 𝓞 F)) ^ 2 = 1 := by simp
  have hT : signedCuspTranslationMatrix F 1 μ h1 =
      upperHom F (Multiplicative.ofAdd μ) := by
    exact signedTranslationMatrix_one_eq_upperHom μ
  simpa [hT] using conjugate_signed_translation_entries σ 1 μ h1

theorem conjugate_upperHom_formula (σ : SL(2,F)) (μ : F) :
    ((σ * upperHom F (Multiplicative.ofAdd μ) * σ⁻¹ : SL(2,F)) : Matrix (Fin 2) (Fin 2) F) =
      !![1 - μ * (σ 0 0) * (σ 1 0), μ * (σ 0 0) ^ 2;
        -μ * (σ 1 0) ^ 2, 1 + μ * (σ 0 0) * (σ 1 0)] := by
  have hdet : σ 0 0 * σ 1 1 - σ 0 1 * σ 1 0 = 1 := by
    have h := σ.property
    rw [Matrix.det_fin_two] at h
    exact h
  have hσ : (σ : Matrix (Fin 2) (Fin 2) F) =
      !![σ 0 0, σ 0 1; σ 1 0, σ 1 1] := Matrix.eta_fin_two _
  have hInv : ((σ⁻¹ : SL(2,F)) : Matrix (Fin 2) (Fin 2) F) =
      !![σ 1 1, -σ 0 1; -σ 1 0, σ 0 0] := by
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  have hU : (upperHom F (Multiplicative.ofAdd μ) : Matrix (Fin 2) (Fin 2) F) =
      !![1, μ; 0, 1] := by rfl
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  rw [hσ, hU, hInv, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · linear_combination hdet
  · ring
  · ring
  · linear_combination hdet

theorem exists_cusp_denominatorBounds (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F)) :
    ∃ D : ℕ, 0 < D ∧
      (∀ μ ∈ cuspLattice F Γ σ, HasDenominatorBound F D μ) ∧
      (∀ μ ∈ signedCuspTranslations F Γ σ, HasDenominatorBound F D μ) := by
  classical
  let a : F := σ 0 0
  let c : F := σ 1 0
  have hcolumn : a ≠ 0 ∨ c ≠ 0 := by
    by_contra h
    push_neg at h
    have hdet := σ.property
    rw [Matrix.det_fin_two] at hdet
    change a * (σ 1 1) - (σ 0 1) * c = 1 at hdet
    rw [h.1, h.2] at hdet
    norm_num at hdet
  obtain ⟨Da, hDa, hAinv⟩ := exists_positive_denominatorBound ((a ^ 2)⁻¹)
  obtain ⟨Dc, hDc, hCinv⟩ := exists_positive_denominatorBound ((c ^ 2)⁻¹)
  let D := Da * Dc
  have hD : 0 < D := by dsimp [D]; exact Nat.mul_pos hDa hDc
  have hAinvD : HasDenominatorBound F D ((a ^ 2)⁻¹) := by
    simpa [D] using hasDenominatorBound_mono (E := Da * Dc) ⟨Dc, rfl⟩ hAinv
  have hCinvD : HasDenominatorBound F D ((c ^ 2)⁻¹) := by
    simpa [D] using hasDenominatorBound_mono (E := Da * Dc) ⟨Da, by ac_rfl⟩ hCinv
  have hBound (μ : F) (hA : HasDenominatorBound F 1 (μ * a ^ 2))
      (hC : HasDenominatorBound F 1 (μ * c ^ 2)) : HasDenominatorBound F D μ := by
    rcases hcolumn with ha | hc
    · have h := hasDenominatorBound_mul hA hAinvD
      simpa [D, pow_two, ha, mul_assoc] using h
    · have h := hasDenominatorBound_mul hC hCinvD
      simpa [D, pow_two, hc, mul_assoc] using h
  have hOrdEntries (μ : F) (hμ : μ ∈ cuspLattice F Γ σ) :
      HasDenominatorBound F 1 (μ * a ^ 2) ∧ HasDenominatorBound F 1 (μ * c ^ 2) := by
    obtain ⟨γ, hγ⟩ := (cuspLattice_mem_iff Γ σ μ).mp hμ
    obtain ⟨h01, h10⟩ := conjugate_upperHom_entries σ μ
    have h01' : (σ * upperHom F (Multiplicative.ofAdd μ) * σ⁻¹) 0 1 =
        algebraMap (𝓞 F) F (((γ : SL(2,𝓞 F)) 0 1)) := by
      simpa [toSLF] using congrArg (fun g : SL(2,F) => g 0 1) hγ
    have h10' : (σ * upperHom F (Multiplicative.ofAdd μ) * σ⁻¹) 1 0 =
        algebraMap (𝓞 F) F (((γ : SL(2,𝓞 F)) 1 0)) := by
      simpa [toSLF] using congrArg (fun g : SL(2,F) => g 1 0) hγ
    have hA : μ * a ^ 2 = algebraMap (𝓞 F) F (((γ : SL(2,𝓞 F)) 0 1)) := by
      dsimp [a]
      exact h01.symm.trans h01'
    have hC : μ * c ^ 2 = algebraMap (𝓞 F) F (-((γ : SL(2,𝓞 F)) 1 0)) := by
      dsimp [c]
      have hp : -(μ * (σ 1 0) ^ 2) =
          algebraMap (𝓞 F) F ((γ : SL(2,𝓞 F)) 1 0) := by
        simpa [neg_mul] using h10.symm.trans h10'
      calc
        μ * (σ 1 0) ^ 2 = -(-(μ * (σ 1 0) ^ 2)) := by ring
        _ = -algebraMap (𝓞 F) F ((γ : SL(2,𝓞 F)) 1 0) := by rw [hp]
        _ = algebraMap (𝓞 F) F (-((γ : SL(2,𝓞 F)) 1 0)) := by simp
    exact ⟨⟨(γ : SL(2,𝓞 F)) 0 1, by simpa using hA⟩,
      ⟨-((γ : SL(2,𝓞 F)) 1 0), by simpa using hC⟩⟩
  have hSignedEntries (μ : F) (hμ : μ ∈ signedCuspTranslations F Γ σ) :
      HasDenominatorBound F 1 (μ * a ^ 2) ∧ HasDenominatorBound F 1 (μ * c ^ 2) := by
    rcases hμ with ⟨ε, hε, γ, hγ⟩
    have hconj :
        σ * signedCuspTranslationMatrix F ε μ hε * σ⁻¹ = toSLF F (γ : SL(2,𝓞 F)) := by
      rw [← hγ]
      group
    obtain ⟨h01, h10⟩ := conjugate_signed_translation_entries σ ε μ hε
    have h01' : (σ * signedCuspTranslationMatrix F ε μ hε * σ⁻¹) 0 1 =
        algebraMap (𝓞 F) F (((γ : SL(2,𝓞 F)) 0 1)) := by
      simpa [toSLF] using congrArg (fun g : SL(2,F) => g 0 1) hconj
    have h10' : (σ * signedCuspTranslationMatrix F ε μ hε * σ⁻¹) 1 0 =
        algebraMap (𝓞 F) F (((γ : SL(2,𝓞 F)) 1 0)) := by
      simpa [toSLF] using congrArg (fun g : SL(2,F) => g 1 0) hconj
    have hAentry : HasDenominatorBound F 1
        (algebraMap (𝓞 F) F (ε : 𝓞 F) * μ * a ^ 2) := by
      refine ⟨(γ : SL(2,𝓞 F)) 0 1, ?_⟩
      simpa [a] using h01.symm.trans h01'
    have hCentry : HasDenominatorBound F 1
        (-(algebraMap (𝓞 F) F (ε : 𝓞 F) * μ * c ^ 2)) := by
      refine ⟨(γ : SL(2,𝓞 F)) 1 0, ?_⟩
      simpa [c] using h10.symm.trans h10'
    have hEpsInv : HasDenominatorBound F 1
        ((algebraMap (𝓞 F) F (ε : 𝓞 F))⁻¹) := by
      exact ⟨((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F), by simp⟩
    have hNegEpsInv : HasDenominatorBound F 1
        (-((algebraMap (𝓞 F) F (ε : 𝓞 F))⁻¹)) := by
      exact ⟨-((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F), by simp⟩
    constructor
    · simpa [mul_assoc] using hasDenominatorBound_mul hEpsInv hAentry
    · simpa [mul_assoc] using hasDenominatorBound_mul hNegEpsInv hCentry
  refine ⟨D, hD, ?_, ?_⟩
  · intro μ hμ
    exact hBound μ (hOrdEntries μ hμ).1 (hOrdEntries μ hμ).2
  · intro μ hμ
    exact hBound μ (hSignedEntries μ hμ).1 (hSignedEntries μ hμ).2

/-- R1 `spec:cusp-lattice` — P-SPEC.md:214, 271–275. Integral multiples lie in the cusp
translation group, all translations have bounded denominators, and the embedded lattice has a
bounded measurable fundamental domain. The signed extension has at most two translation cosets. -/
theorem R1_cusp_lattice (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (σ : SL(2,F)) :
    (∃ m : ℕ, 0 < m ∧ ∀ a : 𝓞 F,
      algebraMap (𝓞 F) F ((m : 𝓞 F) * a) ∈ cuspLattice F Γ σ) ∧
    (∃ D : ℕ, 0 < D ∧
      (∀ μ ∈ cuspLattice F Γ σ, HasDenominatorBound F D μ) ∧
      (∀ μ ∈ cuspTranslationExtension F Γ σ, HasDenominatorBound F D μ)) ∧
    (∀ μ : F, μ ∈ cuspTranslationExtension F Γ σ ↔ μ ∈ signedCuspTranslations F Γ σ) ∧
    (IsFullZLattice (cuspTranslationsZ F Γ σ) ∧
      cuspLattice F Γ σ ≤ cuspTranslationExtension F Γ σ ∧
      ∃ μ₀ ∈ cuspTranslationExtension F Γ σ,
        ∀ μ ∈ cuspTranslationExtension F Γ σ,
          μ ∈ cuspLattice F Γ σ ∨ μ - μ₀ ∈ cuspLattice F Γ σ) ∧
    ∃ P : Set (InfinitePlace F → ℂ),
      IsAddFundamentalDomain (cuspTranslations F Γ σ) P ∧ Bornology.IsBounded P ∧
        MeasurableSet P := by
  classical
  let T : AddSubgroup F := {
    carrier := signedCuspTranslations F Γ σ
    zero_mem' := signedCuspTranslations_zero Γ σ
    add_mem' := signedCuspTranslations_add Γ σ
    neg_mem' := signedCuspTranslations_neg Γ σ
  }
  have hT : cuspTranslationExtension F Γ σ = T := by
    change AddSubgroup.closure (T : Set F) = T
    exact AddSubgroup.closure_eq T
  obtain ⟨D, hD, hLatD, hSignedD⟩ := exists_cusp_denominatorBounds Γ σ
  have hExtD : ∀ μ ∈ cuspTranslationExtension F Γ σ,
      HasDenominatorBound F D μ := by
    intro μ hμ
    have hμT : μ ∈ T := by simpa [hT] using hμ
    exact hSignedD μ (by simpa [T] using hμT)
  have hCoset : ∃ μ₀ ∈ cuspTranslationExtension F Γ σ,
      ∀ μ ∈ cuspTranslationExtension F Γ σ,
        μ ∈ cuspLattice F Γ σ ∨ μ - μ₀ ∈ cuspLattice F Γ σ := by
    by_cases hNonordinary : ∃ μ, μ ∈ signedCuspTranslations F Γ σ ∧
        μ ∉ cuspLattice F Γ σ
    · obtain ⟨μ₀, hμ₀, hμ₀not⟩ := hNonordinary
      refine ⟨μ₀, ?_, ?_⟩
      · rw [hT]
        exact hμ₀
      · intro μ hμ
        have hμset : μ ∈ signedCuspTranslations F Γ σ := by
          simpa [hT, T] using hμ
        rcases hμset with ⟨ε, hε, γ, hγ⟩
        rcases signedCuspTranslation_sign ε hε with hεone | hεneg
        · exact Or.inl <| cuspLattice_of_signed_unit_one Γ σ μ ε hε γ hγ hεone
        · rcases hμ₀ with ⟨η, hη, δ, hδ⟩
          rcases signedCuspTranslation_sign η hη with hηone | hηneg
          · exact (hμ₀not <| cuspLattice_of_signed_unit_one Γ σ μ₀ η hη δ hδ hηone).elim
          · right
            have hδinv : σ⁻¹ * toSLF F ((δ⁻¹ : Γ) : SL(2,𝓞 F)) * σ =
                signedCuspTranslationMatrix F η (-μ₀) hη := by
              calc
                σ⁻¹ * toSLF F ((δ⁻¹ : Γ) : SL(2,𝓞 F)) * σ =
                    (σ⁻¹ * toSLF F (δ : SL(2,𝓞 F)) * σ)⁻¹ := by
                      have hmap : toSLF F ((δ⁻¹ : Γ) : SL(2,𝓞 F)) =
                          (toSLF F (δ : SL(2,𝓞 F)))⁻¹ := by simp
                      rw [hmap]
                      group
                _ = signedCuspTranslationMatrix F η (-μ₀) hη := by
                  rw [hδ, signedCuspTranslationMatrix_inv]
            have hprod :
                σ⁻¹ * toSLF F ((γ * δ⁻¹ : Γ) : SL(2,𝓞 F)) * σ =
                  signedCuspTranslationMatrix F ε μ hε *
                    signedCuspTranslationMatrix F η (-μ₀) hη := by
              calc
                σ⁻¹ * toSLF F ((γ * δ⁻¹ : Γ) : SL(2,𝓞 F)) * σ =
                    (σ⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * σ) *
                      (σ⁻¹ * toSLF F ((δ⁻¹ : Γ) : SL(2,𝓞 F)) * σ) := by
                        have hmap : toSLF F ((γ * δ⁻¹ : Γ) : SL(2,𝓞 F)) =
                            toSLF F (γ : SL(2,𝓞 F)) *
                              toSLF F ((δ⁻¹ : Γ) : SL(2,𝓞 F)) := by simp
                        rw [hmap]
                        group
                _ = signedCuspTranslationMatrix F ε μ hε *
                      signedCuspTranslationMatrix F η (-μ₀) hη := by rw [hγ, hδinv]
            have hunit : ε * η = 1 := by rw [hεneg, hηneg]; simp
            have hεη :
                (algebraMap (𝓞 F) F ((ε * η : (𝓞 F)ˣ) : 𝓞 F)) ^ 2 = 1 := by
              rw [hunit]
              simp
            have hconjSigned :
                σ⁻¹ * toSLF F ((γ * δ⁻¹ : Γ) : SL(2,𝓞 F)) * σ =
                  signedCuspTranslationMatrix F (ε * η) (μ - μ₀) hεη := by
              rw [hprod]
              convert signedCuspTranslationMatrix_mul ε η μ (-μ₀) hε hη hεη using 1 <;> ring
            have hTdiff : signedCuspTranslationMatrix F (ε * η) (μ - μ₀) hεη =
                upperHom F (Multiplicative.ofAdd (μ - μ₀)) := by
              have hεval : algebraMap (𝓞 F) F (ε : 𝓞 F) = -1 := by
                rw [hεneg]
                simp
              have hηval : algebraMap (𝓞 F) F (η : 𝓞 F) = -1 := by
                rw [hηneg]
                simp
              have hU :
                  (upperHom F (Multiplicative.ofAdd (μ - μ₀)) : Matrix (Fin 2) (Fin 2) F) =
                    !![1, μ - μ₀; 0, 1] := by rfl
              have hTmatrix :
                  (signedCuspTranslationMatrix F (ε * η) (μ - μ₀) hεη :
                    Matrix (Fin 2) (Fin 2) F) = !![1, μ - μ₀; 0, 1] := by
                ext i j
                fin_cases i <;> fin_cases j <;>
                  simp [signedCuspTranslationMatrix, hεval, hηval]
              apply Subtype.ext
              exact hTmatrix.trans hU.symm
            have hconj : σ * upperHom F (Multiplicative.ofAdd (μ - μ₀)) * σ⁻¹ =
                toSLF F ((γ * δ⁻¹ : Γ) : SL(2,𝓞 F)) := by
              calc
                σ * upperHom F (Multiplicative.ofAdd (μ - μ₀)) * σ⁻¹ =
                    σ * signedCuspTranslationMatrix F (ε * η) (μ - μ₀) hεη * σ⁻¹ := by
                      rw [hTdiff.symm]
                _ = σ * (σ⁻¹ * toSLF F ((γ * δ⁻¹ : Γ) : SL(2,𝓞 F)) * σ) * σ⁻¹ := by
                      rw [hconjSigned]
                _ = toSLF F ((γ * δ⁻¹ : Γ) : SL(2,𝓞 F)) := by group
            exact (cuspLattice_mem_iff Γ σ (μ - μ₀)).2
              ⟨γ * δ⁻¹, hconj⟩
    · have hall : ∀ μ, μ ∈ signedCuspTranslations F Γ σ → μ ∈ cuspLattice F Γ σ := by
        intro μ hμ
        by_contra hnot
        exact hNonordinary ⟨μ, hμ, hnot⟩
      refine ⟨0, ?_, ?_⟩
      · rw [hT]
        exact signedCuspTranslations_zero Γ σ
      · intro μ hμ
        exact Or.inl (hall μ (by simpa [hT, T] using hμ))
  constructor
  · sorry
  constructor
  · exact ⟨D, hD, hLatD, hExtD⟩
  constructor
  · intro μ
    rw [hT]
    rfl
  constructor
  · refine ⟨?_, ?_⟩
    · sorry
    · exact ⟨by simpa [cuspTranslationExtension] using cuspLattice_subset_signed Γ σ, hCoset⟩
  · sorry

/-- R2 `spec:cusp-units` — P-SPEC.md:215, 277–280. The cusp diagonal units have finite index;
every stabilizer element has a bounded-denominator upper-triangular form; torsion units under a
free action are central; and the stabilizer acts by the stated affine and height maps. -/
theorem R2_cusp_units (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (hfree : FreeAction F Γ) (σ : SL(2,F)) :
    (cuspUnits F Γ σ).FiniteIndex ∧
    (∀ ε : (𝓞 F)ˣ, ε ∈ cuspUnits F Γ σ ↔ ε ∈ cuspUnitSet F Γ σ) ∧
    ∃ D : ℕ, 0 < D ∧
      (∀ γ : cuspStab F Γ σ, ∃ ε : (𝓞 F)ˣ, ε ∈ cuspUnits F Γ σ ∧ ∃ μ : F,
        HasDenominatorBound F D μ ∧
        σ⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * σ = cuspUnitMatrix F ε μ) ∧
    (∀ ε : (𝓞 F)ˣ, ε ∈ cuspUnits F Γ σ → IsOfFinOrder ε →
      ε = 1 ∨ ε = -1) ∧
    (∀ γ : cuspStab F Γ σ, ∀ x : InfinitePlace F → ℂ, ∀ y : InfinitePlace F → ℝ,
      (∀ w, 0 < y w) →
      ∃ ε : (𝓞 F)ˣ, ε ∈ cuspUnits F Γ σ ∧ ∃ μ : F,
        σ⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * σ = cuspUnitMatrix F ε μ ∧
        (γ : SL(2,𝓞 F)) • (σ • ptX' F x y) =
          σ • ptX' F
            (fun w => (w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))) ^ 2 * x w +
              w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F)) * w.embedding μ)
            (fun w => Complex.normSq (w.embedding
              (algebraMap (𝓞 F) F (ε : 𝓞 F))) * y w)) := by
  sorry

/-- R3 `spec:cusps-finite` — P-SPEC.md:216, 282–289. The finite cusp representatives give the
bijective decomposition of `B(F) \ SL(2,F)` consumed by P-EIS and P-REDUCTION; bottom-row ideal
classes have precisely the `SL(2,O_F)` orbits as fibres. -/
theorem R3_cusps_finite (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] :
    (∃ (ι : Type) (_ : Fintype ι) (σ : ι → SL(2,F)),
      Function.Bijective (fun p : (Σ i, CuspCosets F Γ (σ i)) =>
        Quotient.mk (QuotientGroup.rightRel (borelSL F))
          ((σ p.1)⁻¹ * toSLF F ((p.2.out : Γ) : SL(2,𝓞 F))))) ∧
    (∀ g : SL(2,F), bottomRowFractionalIdeal F g ≠ 0) ∧
    Function.Surjective (bottomRowClass F) ∧
    ∀ g h : SL(2,F),
      bottomRowClass F g = bottomRowClass F h ↔
        ∃ γ : SL(2,𝓞 F),
          Quotient.mk (QuotientGroup.rightRel (borelSL F)) g =
            Quotient.mk (QuotientGroup.rightRel (borelSL F)) (h * toSLF F γ) := by
  sorry

/-- R4 `spec:unit-balance` — P-SPEC.md:217, 290–293. Every positive height vector can be moved
by a finite-index unit subgroup into a uniformly bounded logarithmic balance region. -/
theorem R4_unit_balance (E : Subgroup ((𝓞 F)ˣ)) [E.FiniteIndex] :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : InfinitePlace F → ℝ, (∀ w, 0 < t w) →
      ∃ ε : (𝓞 F)ˣ, ε ∈ E ∧ ∀ w,
        |Real.log (‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ * t w) -
          (placeCount F)⁻¹ * ∑ w' : InfinitePlace F, Real.log (t w')| ≤ B := by
  sorry

/-- R5 `spec:lattice-sums` — P-SPEC.md:218, 295–298. Rows in a fixed denominator multiple of
`O_F²`, with no two representatives in the same unit orbit, have the stated summable norm weight. -/
theorem R5_lattice_sums (D : ℕ) (hD : 0 < D) (α : ℝ) (hα : 4 < α)
    {ι : Type*} (v : ι → F × F)
    (hvD : ∀ i, HasDenominatorBound F D (v i).1 ∧ HasDenominatorBound F D (v i).2)
    (hv0 : ∀ i, v i ≠ (0, 0))
    (huniq : ∀ i j, (∃ ε : (𝓞 F)ˣ,
      v i = ((algebraMap (𝓞 F) F (ε : 𝓞 F)) * (v j).1,
        (algebraMap (𝓞 F) F (ε : 𝓞 F)) * (v j).2)) → i = j) :
    Summable (fun i => ∏ w : InfinitePlace F, (rowNorm F (v i) w) ^ (-α)) := by
  sorry

/-- R6 `spec:two-heights` — P-SPEC.md:219, 300. A nonzero lower-left entry bounds the product
of the two heights, and denominator bounds make this uniform over the arithmetic subgroup. -/
theorem R6_two_heights (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] :
    (∀ g : SL(2,F), ∀ z : X F, g 1 0 ≠ 0 →
      normHeight F z * normHeight F (g • z) ≤ (absFieldNorm F (g 1 0))⁻¹) ∧
    (∀ σ σ' : SL(2,F),
      ∃ C : ℝ, 0 < C ∧ ∀ γ : Γ, ∀ z : X F,
        (σ'⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * σ) 1 0 ≠ 0 →
          normHeight F (σ⁻¹ • z) *
            normHeight F (σ'⁻¹ • ((γ : SL(2,𝓞 F)) • z)) ≤ C) := by
  rcases G2_x_action (F := F) with ⟨hFormula, hBorel, hUnit, hActionEquiv, hContinuous⟩
  have hheightGeneral : ∀ g : SL(2,F), ∀ z : X F, g 1 0 ≠ 0 →
      normHeight F z * normHeight F (g • z) ≤ (absFieldNorm F (g 1 0))⁻¹ := by
    intro g z h10
    let x : InfinitePlace F → ℂ := fun w => horiz (z w)
    let y : InfinitePlace F → ℝ := fun w => height (z w)
    let c : F := g 1 0
    have hy : ∀ w, 0 < y w := by
      intro w
      change 0 < height (z w)
      rw [height_eq_hyperbolicHeight]
      exact OAI.CubicEisenstein.hyperbolicHeight_pos (z w)
    have hz : z = ptX' F x y := by
      funext w
      exact (pt_horiz_height (z w)).symm
    have hNz : normHeight F z = ∏ w, y w := by
      simp [normHeight, y]
    have hNg : normHeight F (g • z) =
        ∏ w, y w /
          (Complex.normSq (w.embedding (g 1 0) * x w + w.embedding (g 1 1)) +
            Complex.normSq (w.embedding (g 1 0)) * y w ^ 2) := by
      rw [hz]
      exact hFormula g x y hy
    rw [hNz, hNg]
    let Q : InfinitePlace F → ℝ := fun w =>
      Complex.normSq (w.embedding (g 1 0) * x w + w.embedding (g 1 1)) +
        Complex.normSq (w.embedding (g 1 0)) * y w ^ 2
    change (∏ w, y w) * (∏ w, y w / Q w) ≤ (absFieldNorm F c)⁻¹
    have hc : c ≠ 0 := h10
    have hnorm (w : InfinitePlace F) : 0 < Complex.normSq (w.embedding c) := by
      rw [Complex.normSq_eq_norm_sq]
      apply sq_pos_of_pos
      apply norm_pos_iff.mpr
      exact (map_ne_zero_iff _ w.embedding.injective).mpr hc
    have hQ (w : InfinitePlace F) : 0 < Q w := by
      have hbase : 0 < Complex.normSq (w.embedding c) * y w ^ 2 :=
        mul_pos (hnorm w) (sq_pos_of_pos (hy w))
      dsimp [Q, c]
      linarith [Complex.normSq_nonneg
        (w.embedding (g 1 0) * x w + w.embedding (g 1 1))]
    have hlocal (w : InfinitePlace F) :
        y w * (y w / Q w) ≤ (Complex.normSq (w.embedding c))⁻¹ := by
      have hbase : 0 < Complex.normSq (w.embedding c) * y w ^ 2 :=
        mul_pos (hnorm w) (sq_pos_of_pos (hy w))
      have hden : Complex.normSq (w.embedding c) * y w ^ 2 ≤ Q w := by
        dsimp [Q, c]
        linarith [Complex.normSq_nonneg
          (w.embedding (g 1 0) * x w + w.embedding (g 1 1))]
      calc
        y w * (y w / Q w) = y w ^ 2 / Q w := by
          field_simp [ne_of_gt (hQ w)]
        _ ≤ y w ^ 2 / (Complex.normSq (w.embedding c) * y w ^ 2) :=
          div_le_div_of_nonneg_left (sq_nonneg _) hbase hden
        _ = (Complex.normSq (w.embedding c))⁻¹ := by
          field_simp [ne_of_gt (hnorm w), ne_of_gt (hy w)]
    have hprod :
        ∏ w : InfinitePlace F, y w * (y w / Q w) ≤
          ∏ w : InfinitePlace F, (Complex.normSq (w.embedding c))⁻¹ := by
      apply Finset.prod_le_prod₀
      · intro w hw
        exact le_of_lt (mul_pos (hy w) (div_pos (hy w) (hQ w)))
      · intro w hw
        exact hlocal w
    calc
      (∏ w, y w) * (∏ w, y w / Q w) = ∏ w, y w * (y w / Q w) := by
        rw [← Finset.prod_mul_distrib]
      _ ≤ ∏ w : InfinitePlace F, (Complex.normSq (w.embedding c))⁻¹ := hprod
      _ = (absFieldNorm F c)⁻¹ := by
        simp [absFieldNorm, Complex.normSq_eq_norm_sq, Finset.prod_inv_distrib]
  refine ⟨hheightGeneral, ?_⟩
  · intro σ σ'
    obtain ⟨D, hD, hden⟩ := conjugated_lowerLeft_denominatorBound σ σ'
    let C : ℝ := absFieldNorm F (D : F)
    have hC : 0 < C := by
      dsimp [C]
      apply absFieldNorm_pos_of_ne_zero
      exact_mod_cast hD.ne'
    refine ⟨C, hC, ?_⟩
    intro γ z hne
    let g : SL(2,F) := σ'⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * σ
    have hbound := absFieldNorm_inv_le_of_denominatorBound hD
      (hden (γ : SL(2,𝓞 F))) hne
    have hheight := hheightGeneral g (σ⁻¹ • z) (by simpa [g] using hne)
    have hact : g • (σ⁻¹ • z) = σ'⁻¹ • ((γ : SL(2,𝓞 F)) • z) := by
      calc
        g • (σ⁻¹ • z) =
            σ'⁻¹ • ((toSLF F (γ : SL(2,𝓞 F)) ) • z) := by simp [g, mul_smul]
        _ = σ'⁻¹ • ((γ : SL(2,𝓞 F)) • z) := by rfl
    calc
      normHeight F (σ⁻¹ • z) * normHeight F (σ'⁻¹ • ((γ : SL(2,𝓞 F)) • z))
          = normHeight F (σ⁻¹ • z) * normHeight F (g • (σ⁻¹ • z)) := by rw [hact]
      _ ≤ (absFieldNorm F (g 1 0))⁻¹ := hheight
      _ ≤ C := by
        dsimp [C, g]
        exact hbound

/-- R7 `spec:minkowski` — P-SPEC.md:220, 302–306. A uniform Minkowski bound for a nonzero
integral row in the height-dependent positive Hermitian forms. -/
theorem R7_minkowski :
    ∃ C_M : ℝ, 0 < C_M ∧ ∀ z : X F, ∃ v : 𝓞 F × 𝓞 F,
      v ≠ (0, 0) ∧
        ∏ w : InfinitePlace F,
          rowHeightForm F
            (algebraMap (𝓞 F) F v.1, algebraMap (𝓞 F) F v.2) z w ≤ C_M := by
  sorry

/-- R11 `spec:free-level` — P-SPEC.md:224, 330–336. A nonzero principal congruence subgroup
acts freely on the product hyperbolic space. -/
theorem R11_free_level :
    ∃ N : Ideal (𝓞 F), N ≠ ⊥ ∧ FreeAction F (congrSubgroup F N) := by
  sorry

end ArtinPrimitiveRoots.A1.Spec
