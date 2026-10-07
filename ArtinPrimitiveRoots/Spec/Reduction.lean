import ArtinPrimitiveRoots.Spec.Geometry

/-! Reduction-theory nodes R1--R14. This first stage states the nodes that can start against
the frozen interface. -/

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction nonZeroDivisors

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
  fin_cases i <;> fin_cases j <;> dsimp
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

theorem toSLF_injective : Function.Injective (toSLF F) := by
  intro a b hab
  apply Subtype.ext
  funext i j
  apply RingOfIntegers.coe_injective
  exact congrArg (fun g : SL(2,F) => g i j) hab

/-- Clearing the fixed conjugation coefficients gives an integral unipotent homomorphism. -/
theorem exists_integral_cusp_translation_hom (σ : SL(2,F)) :
    ∃ D : ℕ, 0 < D ∧ ∃ f : Multiplicative (𝓞 F) →* SL(2,𝓞 F),
      ∀ a : 𝓞 F, toSLF F (f (Multiplicative.ofAdd a)) =
        σ * upperHom F (Multiplicative.ofAdd (algebraMap (𝓞 F) F ((D : 𝓞 F) * a))) *
          σ⁻¹ := by
  classical
  obtain ⟨D, hD, hb⟩ := exists_common_denominatorBound
    (fun i : Fin 3 => ![(σ 0 0)^2, (σ 1 0)^2, σ 0 0 * σ 1 0] i)
  obtain ⟨A, hA⟩ := hb 0
  obtain ⟨B, hB⟩ := hb 1
  obtain ⟨C, hC⟩ := hb 2
  change (D : F) * (σ 0 0)^2 = algebraMap (𝓞 F) F A at hA
  change (D : F) * (σ 1 0)^2 = algebraMap (𝓞 F) F B at hB
  change (D : F) * (σ 0 0 * σ 1 0) = algebraMap (𝓞 F) F C at hC
  let M : 𝓞 F → Matrix (Fin 2) (Fin 2) (𝓞 F) :=
    fun a => !![1 - a * C, a * A; -a * B, 1 + a * C]
  have hM (a : 𝓞 F) : (M a).map (algebraMap (𝓞 F) F) =
      (σ * upperHom F (Multiplicative.ofAdd ((D : F) * algebraMap (𝓞 F) F a)) *
        σ⁻¹ : SL(2,F)) := by
    rw [conjugate_upperHom_formula]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [M, Matrix.map_apply, ← hA, ← hB, ← hC] <;> ring
  have hdet (a : 𝓞 F) : Matrix.det (M a) = 1 := by
    apply RingOfIntegers.coe_injective
    rw [map_one, (algebraMap (𝓞 F) F).map_det]
    change Matrix.det ((M a).map (algebraMap (𝓞 F) F)) = 1
    rw [hM]
    exact (σ * upperHom F (Multiplicative.ofAdd ((D : F) * algebraMap (𝓞 F) F a)) *
      σ⁻¹).property
  let g : 𝓞 F → SL(2,𝓞 F) := fun a => ⟨M a, hdet a⟩
  have hg (a : 𝓞 F) : toSLF F (g a) =
      σ * upperHom F (Multiplicative.ofAdd ((D : F) * algebraMap (𝓞 F) F a)) *
        σ⁻¹ := by
    apply Subtype.ext
    exact hM a
  let f : Multiplicative (𝓞 F) →* SL(2,𝓞 F) := {
    toFun := fun a => g a.toAdd
    map_one' := by
      apply toSLF_injective
      change toSLF F (g 0) = toSLF F (1 : SL(2,𝓞 F))
      rw [(toSLF F).map_one, hg]
      simp
    map_mul' := by
      intro a b
      apply toSLF_injective
      change toSLF F (g (a.toAdd + b.toAdd)) =
        toSLF F (g a.toAdd * g b.toAdd)
      rw [(toSLF F).map_mul, hg, hg, hg, (algebraMap (𝓞 F) F).map_add, mul_add]
      change σ * upperHom F
          (Multiplicative.ofAdd ((D : F) * algebraMap (𝓞 F) F a.toAdd) *
            Multiplicative.ofAdd ((D : F) * algebraMap (𝓞 F) F b.toAdd)) * σ⁻¹ = _
      rw [(upperHom F).map_mul]
      group
  }
  refine ⟨D, hD, f, fun a => ?_⟩
  simpa [f] using hg a

theorem exists_integral_multiple_in_cuspLattice
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (σ : SL(2,F)) :
    ∃ m : ℕ, 0 < m ∧ ∀ a : 𝓞 F,
      algebraMap (𝓞 F) F ((m : 𝓞 F) * a) ∈ cuspLattice F Γ σ := by
  classical
  obtain ⟨D, hD, f, hf⟩ := exists_integral_cusp_translation_hom σ
  let H : Subgroup (Multiplicative (𝓞 F)) := Γ.comap f
  have hidx : 0 < H.index :=
    Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := H))
  refine ⟨D * H.index, Nat.mul_pos hD hidx, fun a => ?_⟩
  have hpow : (Multiplicative.ofAdd a) ^ H.index ∈ H := H.pow_index_mem _
  have hγ : f ((Multiplicative.ofAdd a) ^ H.index) ∈ Γ := hpow
  apply (cuspLattice_mem_iff Γ σ _).2
  refine ⟨⟨f ((Multiplicative.ofAdd a) ^ H.index), hγ⟩, ?_⟩
  have heq : algebraMap (𝓞 F) F
      ((D : 𝓞 F) * ((Multiplicative.ofAdd a) ^ H.index).toAdd) =
        algebraMap (𝓞 F) F (((D * H.index : ℕ) : 𝓞 F) * a) := by
    simp [nsmul_eq_mul, Nat.cast_mul, mul_assoc]
  calc
    σ * upperHom F (Multiplicative.ofAdd
        (algebraMap (𝓞 F) F (((D * H.index : ℕ) : 𝓞 F) * a))) * σ⁻¹ =
      σ * upperHom F (Multiplicative.ofAdd
        (algebraMap (𝓞 F) F ((D : 𝓞 F) *
          ((Multiplicative.ofAdd a) ^ H.index).toAdd))) * σ⁻¹ := by rw [heq]
    _ = toSLF F (f ((Multiplicative.ofAdd a) ^ H.index)) :=
      (hf (((Multiplicative.ofAdd a) ^ H.index).toAdd)).symm

/-- For a totally complex field the mixed embedding space is the space of chosen complex places. -/
def complexPlaceLinearEquiv : mixedEmbedding.mixedSpace F ≃ₗ[ℝ] (InfinitePlace F → ℂ) where
  toFun x w := x.2 ⟨w, IsTotallyComplex.isComplex w⟩
  invFun x := (fun w => False.elim
    ((InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w.1)) w.2),
    fun w => x w.1)
  left_inv x := by
    apply Prod.ext
    · funext w
      exact ((InfinitePlace.not_isReal_iff_isComplex.mpr
        (IsTotallyComplex.isComplex w.1)) w.2).elim
    · funext w
      rfl
  right_inv x := rfl
  map_add' x y := rfl
  map_smul' c x := rfl

def complexIntegerLatticeBasis :
    Module.Basis (Module.Free.ChooseBasisIndex ℤ (𝓞 F)) ℝ (InfinitePlace F → ℂ) :=
  (mixedEmbedding.latticeBasis F).map (complexPlaceLinearEquiv (F := F))

theorem complexIntegerLatticeBasis_apply (i : Module.Free.ChooseBasisIndex ℤ (𝓞 F)) :
    complexIntegerLatticeBasis (F := F) i =
      infEmb F (algebraMap (𝓞 F) F (RingOfIntegers.basis F i)) := by
  change complexPlaceLinearEquiv (F := F) (mixedEmbedding.latticeBasis F i) = _
  rw [mixedEmbedding.latticeBasis_apply, integralBasis_apply]
  rfl

theorem infEmb_ringInteger_mem_span (a : 𝓞 F) :
    infEmb F (algebraMap (𝓞 F) F a) ∈
      Submodule.span ℤ (Set.range (complexIntegerLatticeBasis (F := F))) := by
  let f : 𝓞 F →ₗ[ℤ] (InfinitePlace F → ℂ) :=
    ((infEmb F).comp (algebraMap (𝓞 F) F)).toAddMonoidHom.toIntLinearMap
  have heq : Set.range (complexIntegerLatticeBasis (F := F)) =
      f '' Set.range (RingOfIntegers.basis F) := by
    rw [← Set.range_comp]
    congr 1
    funext i
    exact complexIntegerLatticeBasis_apply i
  rw [heq, ← Submodule.map_span, (RingOfIntegers.basis F).span_eq]
  exact Submodule.mem_map.mpr ⟨a, Submodule.mem_top, rfl⟩

theorem infEmb_nat_mul (n : ℕ) (a : F) :
    infEmb F ((n : F) * a) = (n : ℝ) • infEmb F a := by
  ext w
  simp [infEmb, Complex.real_smul]

theorem cuspTranslationsZ_eq_toIntSubmodule (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F)) :
    cuspTranslationsZ F Γ σ = (cuspTranslations F Γ σ).toIntSubmodule := by
  change Submodule.span ℤ
    ((cuspTranslations F Γ σ).toIntSubmodule : Set (InfinitePlace F → ℂ)) = _
  exact Submodule.span_eq _

theorem cuspTranslationsZ_toAddSubgroup (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F)) :
    (cuspTranslationsZ F Γ σ).toAddSubgroup = cuspTranslations F Γ σ := by
  rw [cuspTranslationsZ_eq_toIntSubmodule]
  exact AddSubgroup.toIntSubmodule_toAddSubgroup _

theorem cuspTranslations_isFullZLattice (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    {m D : ℕ} (hm : 0 < m)
    (hmlower : ∀ a : 𝓞 F, algebraMap (𝓞 F) F ((m : 𝓞 F) * a) ∈ cuspLattice F Γ σ)
    (hD : 0 < D) (hDupper : ∀ μ ∈ cuspLattice F Γ σ, HasDenominatorBound F D μ) :
    IsFullZLattice (cuspTranslationsZ F Γ σ) := by
  classical
  let E := InfinitePlace F → ℂ
  let b := complexIntegerLatticeBasis (F := F)
  let L₀ : Submodule ℤ E := Submodule.span ℤ (Set.range b)
  let scale : E →ₗ[ℝ] E := (D : ℝ) • LinearMap.id
  have hDne : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hmne : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hscaleCont : Continuous scale := LinearMap.continuous_of_finiteDimensional _
  have hscaleInj : Function.Injective scale := by
    intro x y hxy
    have h := congrArg (fun z : E => (D : ℝ)⁻¹ • z) hxy
    simpa [scale, smul_smul, hDne] using h
  let U : Submodule ℤ E := ZLattice.comap ℝ L₀ scale
  letI : DiscreteTopology L₀ := inferInstance
  have hUdisc : DiscreteTopology U :=
    ZLattice.comap_discreteTopology ℝ L₀ hscaleCont hscaleInj
  have hupper : cuspTranslationsZ F Γ σ ≤ U := by
    change Submodule.span ℤ (cuspTranslations F Γ σ : Set E) ≤ U
    apply Submodule.span_le.mpr
    intro x hx
    rcases AddSubgroup.mem_map.mp hx with ⟨μ, hμ, rfl⟩
    obtain ⟨a, ha⟩ := hDupper μ hμ
    change (D : ℝ) • infEmb F μ ∈ L₀
    have hemb := congrArg (infEmb F) ha
    rw [infEmb_nat_mul] at hemb
    rw [hemb]
    exact infEmb_ringInteger_mem_span a
  have hdisc : DiscreteTopology (cuspTranslationsZ F Γ σ) :=
    DiscreteTopology.of_subset hUdisc hupper
  letI := hdisc
  have hspan : Submodule.span ℝ (cuspTranslationsZ F Γ σ : Set E) = ⊤ := by
    apply top_unique
    rw [← b.span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have hmulmem : (m : ℝ) • b i ∈ cuspTranslationsZ F Γ σ := by
      apply Submodule.subset_span
      apply AddSubgroup.mem_map.mpr
      refine ⟨algebraMap (𝓞 F) F ((m : 𝓞 F) * RingOfIntegers.basis F i),
        hmlower _, ?_⟩
      change infEmb F (algebraMap (𝓞 F) F
        ((m : 𝓞 F) * RingOfIntegers.basis F i)) = (m : ℝ) • b i
      rw [(algebraMap (𝓞 F) F).map_mul, map_natCast, infEmb_nat_mul]
      rw [complexIntegerLatticeBasis_apply]
    have hreal := Submodule.subset_span (R := ℝ) hmulmem
    have hs := (Submodule.span ℝ (cuspTranslationsZ F Γ σ : Set E)).smul_mem
      (m : ℝ)⁻¹ hreal
    simpa [smul_smul, hmne] using hs
  exact ⟨hdisc, ⟨hspan⟩⟩

theorem exists_bounded_cusp_fundamentalDomain (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (hfull : IsFullZLattice (cuspTranslationsZ F Γ σ)) :
    ∃ P : Set (InfinitePlace F → ℂ),
      IsAddFundamentalDomain (cuspTranslations F Γ σ) P ∧ Bornology.IsBounded P ∧
        MeasurableSet P := by
  classical
  let L := cuspTranslationsZ F Γ σ
  obtain ⟨hdisc, hL⟩ := hfull
  letI := hdisc
  letI := hL
  letI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  letI : Module.Free ℤ L := ZLattice.module_free ℝ L
  let b := Module.Free.chooseBasis ℤ L
  have hfd : IsAddFundamentalDomain L.toAddSubgroup
      (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) :=
    ZLattice.isAddFundamentalDomain b volume
  have hgroup : L.toAddSubgroup = cuspTranslations F Γ σ :=
    cuspTranslationsZ_toAddSubgroup Γ σ
  rw [hgroup] at hfd
  exact ⟨_, hfd, ZSpan.fundamentalDomain_isBounded _,
    ZSpan.fundamentalDomain_measurableSet _⟩

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
  obtain ⟨m, hm, hmlower⟩ := exists_integral_multiple_in_cuspLattice Γ σ
  have hfull := cuspTranslations_isFullZLattice Γ σ hm hmlower hD hLatD
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
  · exact ⟨m, hm, hmlower⟩
  constructor
  · exact ⟨D, hD, hLatD, hExtD⟩
  constructor
  · intro μ
    rw [hT]
    rfl
  constructor
  · refine ⟨?_, ?_⟩
    · exact hfull
    · exact ⟨by simpa [cuspTranslationExtension] using cuspLattice_subset_signed Γ σ, hCoset⟩
  · exact exists_bounded_cusp_fundamentalDomain Γ σ hfull

theorem cuspUnitMatrix_one : cuspUnitMatrix F 1 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cuspUnitMatrix]

theorem cuspUnitMatrix_mul (ε η : (𝓞 F)ˣ) (μ ν : F) :
    cuspUnitMatrix F ε μ * cuspUnitMatrix F η ν =
      cuspUnitMatrix F (ε * η)
        (algebraMap (𝓞 F) F (ε : 𝓞 F) * ν +
          μ * (algebraMap (𝓞 F) F (η : 𝓞 F))⁻¹) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cuspUnitMatrix, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem cuspUnitMatrix_inv (ε : (𝓞 F)ˣ) (μ : F) :
    (cuspUnitMatrix F ε μ)⁻¹ = cuspUnitMatrix F ε⁻¹ (-μ) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_inv]
  rw [Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cuspUnitMatrix, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

def cuspUnitSubgroup (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F)) : Subgroup ((𝓞 F)ˣ) where
  carrier := cuspUnitSet F Γ σ
  one_mem' := by
    refine ⟨0, 1, ?_⟩
    simp [cuspUnitMatrix_one]
  mul_mem' := by
    rintro ε η ⟨μ, γ, hγ⟩ ⟨ν, δ, hδ⟩
    refine ⟨algebraMap (𝓞 F) F (ε : 𝓞 F) * ν +
      μ * (algebraMap (𝓞 F) F (η : 𝓞 F))⁻¹, γ * δ, ?_⟩
    have hmap : toSLF F ((γ * δ : Γ) : SL(2,𝓞 F)) =
        toSLF F (γ : SL(2,𝓞 F)) * toSLF F (δ : SL(2,𝓞 F)) := by simp
    have hconj : σ⁻¹ * toSLF F ((γ * δ : Γ) : SL(2,𝓞 F)) * σ =
        (σ⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * σ) *
          (σ⁻¹ * toSLF F (δ : SL(2,𝓞 F)) * σ) := by rw [hmap]; group
    rw [hconj, hγ, hδ, cuspUnitMatrix_mul]
  inv_mem' := by
    rintro ε ⟨μ, γ, hγ⟩
    refine ⟨-μ, γ⁻¹, ?_⟩
    have hmap : toSLF F ((γ⁻¹ : Γ) : SL(2,𝓞 F)) =
        (toSLF F (γ : SL(2,𝓞 F)))⁻¹ := by simp
    have hconj : σ⁻¹ * toSLF F ((γ⁻¹ : Γ) : SL(2,𝓞 F)) * σ =
        (σ⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * σ)⁻¹ := by rw [hmap]; group
    rw [hconj, hγ, cuspUnitMatrix_inv]

theorem cuspUnits_eq_subgroup (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F)) :
    cuspUnits F Γ σ = cuspUnitSubgroup Γ σ := by
  change Subgroup.closure (cuspUnitSubgroup Γ σ : Set ((𝓞 F)ˣ)) = _
  exact Subgroup.closure_eq _

theorem cuspUnits_mem_iff (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F)) (ε : (𝓞 F)ˣ) :
    ε ∈ cuspUnits F Γ σ ↔ ε ∈ cuspUnitSet F Γ σ := by
  rw [cuspUnits_eq_subgroup]
  rfl

theorem cuspStab_unit_form (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (γ : cuspStab F Γ σ) :
    ∃ ε : (𝓞 F)ˣ, ε ∈ cuspUnits F Γ σ ∧ ∃ μ : F,
      σ⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * σ = cuspUnitMatrix F ε μ := by
  have htri : σ⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * σ ∈ borelSL F := by
    simpa [cuspStab, MulAut.conj_apply] using γ.property
  obtain ⟨ε, hε, hnorm⟩ :=
    ((G2_x_action (F := F)).2.2.1 (γ : SL(2,𝓞 F)) σ htri).1
  let b : SL(2,F) := σ⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * σ
  have h10 : b 1 0 = 0 := htri
  have hdet : b 0 0 * b 1 1 = 1 := by
    have h := b.property
    rw [Matrix.det_fin_two, h10] at h
    simpa using h
  have hd : b 1 1 = (b 0 0)⁻¹ := eq_inv_of_mul_eq_one_right hdet
  change algebraMap (𝓞 F) F (ε : 𝓞 F) = b 0 0 at hε
  have hb : b = cuspUnitMatrix F ε (b 0 1) := by
    apply Subtype.ext
    funext i j
    fin_cases i <;> fin_cases j
    · exact hε.symm
    · rfl
    · exact h10
    · exact hd.trans (congrArg (fun a : F => a⁻¹) hε).symm
  refine ⟨ε, Subgroup.subset_closure ?_, b 0 1, hb⟩
  exact ⟨b 0 1, (γ : Γ), hb⟩

theorem conjugated_entry_denominatorBound (σ σ' : SL(2,F)) (i j : Fin 2) :
    ∃ D : ℕ, 0 < D ∧ ∀ γ : SL(2,𝓞 F),
      HasDenominatorBound F D ((σ'⁻¹ * toSLF F γ * σ) i j) := by
  classical
  let A : Matrix (Fin 2) (Fin 2) F := (σ'⁻¹ : SL(2,F))
  let B : Matrix (Fin 2) (Fin 2) F := (σ : SL(2,F))
  obtain ⟨D₁, hD₁, hA⟩ := exists_matrix_denominatorBound A
  obtain ⟨D₂, hD₂, hB⟩ := exists_matrix_denominatorBound B
  let E := D₁ * D₂
  have hD : 0 < ((E * E) * (E * E)) := by dsimp [E]; positivity
  refine ⟨(E * E) * (E * E), hD, ?_⟩
  intro γ
  let q : Fin 2 → Fin 2 → F :=
    fun k l => A i k * algebraMap (𝓞 F) F (γ k l) * B l j
  have hγ (k l : Fin 2) : HasDenominatorBound F 1
      (algebraMap (𝓞 F) F (γ k l)) := ⟨γ k l, by simp⟩
  have hq (k l : Fin 2) : HasDenominatorBound F E (q k l) := by
    simpa [q, E, mul_assoc] using
      hasDenominatorBound_mul (hasDenominatorBound_mul (hA i k) (hγ k l)) (hB l j)
  have hsum : HasDenominatorBound F ((E * E) * (E * E))
      (q 0 0 + q 0 1 + (q 1 0 + q 1 1)) := by
    simpa [Nat.mul_assoc] using
      hasDenominatorBound_add (hasDenominatorBound_add (hq 0 0) (hq 0 1))
        (hasDenominatorBound_add (hq 1 0) (hq 1 1))
  have hentry : (σ'⁻¹ * toSLF F γ * σ) i j =
      q 0 0 + q 0 1 + (q 1 0 + q 1 1) := by
    change ((A * (toSLF F γ : Matrix (Fin 2) (Fin 2) F) * B) i j) = _
    simp [q, toSLF, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  exact hentry ▸ hsum

theorem cuspStab_bounded_unit_form (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F)) :
    ∃ D : ℕ, 0 < D ∧ ∀ γ : cuspStab F Γ σ,
      ∃ ε : (𝓞 F)ˣ, ε ∈ cuspUnits F Γ σ ∧ ∃ μ : F,
        HasDenominatorBound F D μ ∧
        σ⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * σ = cuspUnitMatrix F ε μ := by
  obtain ⟨D, hD, hden⟩ := conjugated_entry_denominatorBound σ σ 0 1
  refine ⟨D, hD, fun γ => ?_⟩
  obtain ⟨ε, hε, μ, hform⟩ := cuspStab_unit_form Γ σ γ
  refine ⟨ε, hε, μ, ?_, hform⟩
  have h := hden (γ : SL(2,𝓞 F))
  have hμ : (σ⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * σ) 0 1 = μ := by
    rw [hform]
    rfl
  rwa [hμ] at h

theorem conjugate_cuspUnitMatrix_zero_entry (σ : SL(2,F)) (ε : (𝓞 F)ˣ) (i j : Fin 2) :
    (σ * cuspUnitMatrix F ε 0 * σ⁻¹) i j =
      algebraMap (𝓞 F) F (ε : 𝓞 F) * (σ i 0 * (σ⁻¹ : SL(2,F)) 0 j) +
        algebraMap (𝓞 F) F ((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) *
          (σ i 1 * (σ⁻¹ : SL(2,F)) 1 j) := by
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  simp [cuspUnitMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- Units congruent to one admit an integral conjugated diagonal homomorphism. -/
theorem exists_integral_cusp_diagonal_hom (σ : SL(2,F)) :
    ∃ K : Subgroup ((𝓞 F)ˣ), K.FiniteIndex ∧ ∃ f : K →* SL(2,𝓞 F),
      ∀ ε : K, toSLF F (f ε) = σ * cuspUnitMatrix F (ε : (𝓞 F)ˣ) 0 * σ⁻¹ := by
  classical
  obtain ⟨D, hD, hbound⟩ := exists_common_denominatorBound
    (fun p : Fin 2 × Fin 2 × Fin 2 => σ p.1 p.2.1 * (σ⁻¹ : SL(2,F)) p.2.1 p.2.2)
  choose B hB using hbound
  let J : Ideal (𝓞 F) := Ideal.span {(D : 𝓞 F)}
  have hJ : J ≠ ⊥ := by
    change Ideal.span {(D : 𝓞 F)} ≠ ⊥
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hD.ne'
  letI : Finite (𝓞 F ⧸ J) := J.finiteQuotientOfFreeOfNeBot hJ
  let q : (𝓞 F)ˣ →* (𝓞 F ⧸ J)ˣ := Units.map (Ideal.Quotient.mk J).toMonoidHom
  let K : Subgroup ((𝓞 F)ˣ) := q.ker
  have hK : K.FiniteIndex := inferInstance
  have hdiff (ε : K) : ∃ a : 𝓞 F,
      ((ε : (𝓞 F)ˣ) : 𝓞 F) - 1 = (D : 𝓞 F) * a := by
    have hu : q (ε : (𝓞 F)ˣ) = 1 := ε.property
    have hq : Ideal.Quotient.mk J ((ε : (𝓞 F)ˣ) : 𝓞 F) = 1 := by
      simpa [q] using congrArg (fun u : (𝓞 F ⧸ J)ˣ => (u : 𝓞 F ⧸ J)) hu
    have hmem : ((ε : (𝓞 F)ˣ) : 𝓞 F) - 1 ∈ J := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simp [map_sub, hq]
    exact Ideal.mem_span_singleton.mp hmem
  choose r hr using hdiff
  have hcoef (ε : K) : algebraMap (𝓞 F) F ((ε : (𝓞 F)ˣ) : 𝓞 F) =
      1 + (D : F) * algebraMap (𝓞 F) F (r ε) := by
    have h := congrArg (algebraMap (𝓞 F) F) (hr ε)
    simp only [map_sub, map_one, map_mul, map_natCast] at h
    linear_combination h
  let A₀ : Matrix (Fin 2) (Fin 2) (𝓞 F) := fun i j => B (i, 0, j)
  let A₁ : Matrix (Fin 2) (Fin 2) (𝓞 F) := fun i j => B (i, 1, j)
  let M : K → Matrix (Fin 2) (Fin 2) (𝓞 F) :=
    fun ε => 1 + r ε • A₀ + r ε⁻¹ • A₁
  have hM (ε : K) : (M ε).map (algebraMap (𝓞 F) F) =
      (σ * cuspUnitMatrix F (ε : (𝓞 F)ˣ) 0 * σ⁻¹ : SL(2,F)) := by
    ext i j
    rw [conjugate_cuspUnitMatrix_zero_entry]
    simp only [Matrix.map_apply, M, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, map_add, map_mul]
    have hI : algebraMap (𝓞 F) F ((1 : Matrix (Fin 2) (Fin 2) (𝓞 F)) i j) =
        (1 : Matrix (Fin 2) (Fin 2) F) i j := by
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    have hInv : algebraMap (𝓞 F) F (((ε : (𝓞 F)ˣ)⁻¹ : (𝓞 F)ˣ) : 𝓞 F) =
        1 + (D : F) * algebraMap (𝓞 F) F (r ε⁻¹) := hcoef ε⁻¹
    rw [hI, ← hB (i, 0, j), ← hB (i, 1, j), hcoef ε, hInv]
    have hmat : (σ : Matrix (Fin 2) (Fin 2) F) *
        ((σ⁻¹ : SL(2,F)) : Matrix (Fin 2) (Fin 2) F) = 1 :=
      congrArg (fun g : SL(2,F) => (g : Matrix (Fin 2) (Fin 2) F)) (mul_inv_cancel σ)
    have hconst : σ i 0 * (σ⁻¹ : SL(2,F)) 0 j +
        σ i 1 * (σ⁻¹ : SL(2,F)) 1 j = (1 : Matrix (Fin 2) (Fin 2) F) i j := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using
        congrArg (fun A : Matrix (Fin 2) (Fin 2) F => A i j) hmat
    linear_combination -hconst
  have hdet (ε : K) : Matrix.det (M ε) = 1 := by
    apply RingOfIntegers.coe_injective
    rw [map_one, (algebraMap (𝓞 F) F).map_det]
    change Matrix.det ((M ε).map (algebraMap (𝓞 F) F)) = 1
    rw [hM]
    exact (σ * cuspUnitMatrix F (ε : (𝓞 F)ˣ) 0 * σ⁻¹).property
  let g : K → SL(2,𝓞 F) := fun ε => ⟨M ε, hdet ε⟩
  have hg (ε : K) : toSLF F (g ε) =
      σ * cuspUnitMatrix F (ε : (𝓞 F)ˣ) 0 * σ⁻¹ := by
    apply Subtype.ext
    exact hM ε
  let f : K →* SL(2,𝓞 F) := {
    toFun := g
    map_one' := by
      apply toSLF_injective
      rw [(toSLF F).map_one, hg]
      simp [cuspUnitMatrix_one]
    map_mul' := by
      intro ε η
      apply toSLF_injective
      rw [(toSLF F).map_mul, hg, hg, hg]
      have hmul : cuspUnitMatrix F ((ε * η : K) : (𝓞 F)ˣ) 0 =
          cuspUnitMatrix F (ε : (𝓞 F)ˣ) 0 * cuspUnitMatrix F (η : (𝓞 F)ˣ) 0 := by
        simpa using (cuspUnitMatrix_mul (ε : (𝓞 F)ˣ) (η : (𝓞 F)ˣ) 0 0).symm
      rw [hmul]
      group
  }
  exact ⟨K, hK, f, hg⟩

theorem cuspUnits_finiteIndex (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (σ : SL(2,F)) :
    (cuspUnits F Γ σ).FiniteIndex := by
  classical
  obtain ⟨K, hK, f, hf⟩ := exists_integral_cusp_diagonal_hom σ
  letI := hK
  let H : Subgroup K := Γ.comap f
  let L : Subgroup ((𝓞 F)ˣ) := H.map K.subtype
  letI : L.FiniteIndex := ⟨by
    rw [Subgroup.index_map_subtype]
    exact mul_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := H)) hK.index_ne_zero⟩
  apply Subgroup.finiteIndex_of_le (H := L)
  intro ε hε
  rcases Subgroup.mem_map.mp hε with ⟨η, hη, rfl⟩
  apply Subgroup.subset_closure
  refine ⟨0, ⟨f η, hη⟩, ?_⟩
  change σ⁻¹ * toSLF F (f η) * σ = cuspUnitMatrix F (η : (𝓞 F)ˣ) 0
  rw [hf]
  group

theorem horiz_mk_upper (g : SL(2,ℂ)) (h10 : g 1 0 = 0) :
    horiz (QuotientGroup.mk g : H3) = g 0 1 / g 1 1 := by
  have hd : g 1 1 ≠ 0 := by
    intro hd
    have h := g.property
    rw [Matrix.det_fin_two, h10, hd] at h
    simp at h
  have hstar : star (g 1 1) ≠ 0 := by
    intro h
    apply hd
    have hh := congrArg star h
    simpa using hh
  change (((g : Matrix (Fin 2) (Fin 2) ℂ) * star (g : Matrix (Fin 2) (Fin 2) ℂ)) 0 1) /
    (((g : Matrix (Fin 2) (Fin 2) ℂ) * star (g : Matrix (Fin 2) (Fin 2) ℂ)) 1 1) = _
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
    h10, star_zero, zero_mul, mul_zero, zero_add, add_zero]
  field_simp [hd, hstar] <;> ring

theorem horiz_smul_pt_upper (g : SL(2,ℂ)) (h10 : g 1 0 = 0)
    (x : ℂ) (y : ℝ) (hy : 0 < y) :
    horiz (g • pt x y) = (g 0 0)^2 * x + g 0 0 * g 0 1 := by
  have hdet : g 0 0 * g 1 1 = 1 := by
    have h := g.property
    rw [Matrix.det_fin_two, h10] at h
    simpa using h
  have ha : g 0 0 ≠ 0 := by
    intro ha
    rw [ha, zero_mul] at hdet
    exact zero_ne_one hdet
  have hd : g 1 1 = (g 0 0)⁻¹ := eq_inv_of_mul_eq_one_right hdet
  have hs : (Real.sqrt y : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hy).ne'
  have hp : (g * ptMat x y hy) 1 0 = 0 := by
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    simp [ptMat, Matrix.mul_apply, Fin.sum_univ_two, h10]
  rw [pt, dif_pos hy]
  change horiz (QuotientGroup.mk (g * ptMat x y hy) : H3) = _
  rw [horiz_mk_upper _ hp]
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  simp [ptMat, Matrix.mul_apply, Fin.sum_univ_two, h10, hd]
  field_simp [hs, ha] <;> ring

theorem cuspUnitMatrix_smul_ptX' (ε : (𝓞 F)ˣ) (μ : F)
    (x : InfinitePlace F → ℂ) (y : InfinitePlace F → ℝ) (hy : ∀ w, 0 < y w) :
    cuspUnitMatrix F ε μ • ptX' F x y =
      ptX' F (fun w => (w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F)))^2 * x w +
        w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F)) * w.embedding μ)
        (fun w => Complex.normSq (w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))) * y w) := by
  funext w
  let g : SL(2,ℂ) := Matrix.SpecialLinearGroup.map w.embedding (cuspUnitMatrix F ε μ)
  let a : ℂ := w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))
  have h00 : g 0 0 = a := rfl
  have h01 : g 0 1 = w.embedding μ := rfl
  have h10 : g 1 0 = 0 := by
    change w.embedding (0 : F) = 0
    exact w.embedding.map_zero
  have h11 : g 1 1 = a⁻¹ := by
    change w.embedding ((algebraMap (𝓞 F) F (ε : 𝓞 F))⁻¹) = a⁻¹
    simp [a]
  have hx : horiz (g • pt (x w) (y w)) = a^2 * x w + a * w.embedding μ := by
    have h := horiz_smul_pt_upper g h10 (x w) (y w) (hy w)
    rwa [h00, h01] at h
  have hh : height (g • pt (x w) (y w)) = Complex.normSq a * y w := by
    have h := (G1_h3_basics (F := F)).2.2.1 g (x w) (y w) (hy w)
    rw [h10, h11] at h
    simpa [Complex.normSq_inv, div_inv_eq_mul, mul_comm] using h
  change g • pt (x w) (y w) = pt (a^2 * x w + a * w.embedding μ) (Complex.normSq a * y w)
  calc
    g • pt (x w) (y w) = pt (horiz (g • pt (x w) (y w)))
      (height (g • pt (x w) (y w))) := (pt_horiz_height _).symm
    _ = _ := by rw [hx, hh]

theorem cusp_conjugate_affine_action (γ : SL(2,𝓞 F)) (σ : SL(2,F))
    (ε : (𝓞 F)ˣ) (μ : F)
    (hform : σ⁻¹ * toSLF F γ * σ = cuspUnitMatrix F ε μ)
    (x : InfinitePlace F → ℂ) (y : InfinitePlace F → ℝ) (hy : ∀ w, 0 < y w) :
    γ • (σ • ptX' F x y) =
      σ • ptX' F (fun w => (w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F)))^2 * x w +
        w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F)) * w.embedding μ)
        (fun w => Complex.normSq (w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))) * y w) := by
  have heq : toSLF F γ * σ = σ * cuspUnitMatrix F ε μ := by
    calc
      toSLF F γ * σ = σ * (σ⁻¹ * toSLF F γ * σ) := by group
      _ = σ * cuspUnitMatrix F ε μ := by rw [hform]
  change toSLF F γ • (σ • ptX' F x y) = _
  rw [← mul_smul, heq, mul_smul, cuspUnitMatrix_smul_ptX' ε μ x y hy]

theorem cuspUnits_torsion_sign (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (hfree : FreeAction F Γ) (ε : (𝓞 F)ˣ)
    (hε : ε ∈ cuspUnits F Γ σ) (hfin : IsOfFinOrder ε) : ε = 1 ∨ ε = -1 := by
  classical
  by_cases hsign : ε = 1 ∨ ε = -1
  · exact hsign
  obtain ⟨μ, γ, hform⟩ := (cuspUnits_mem_iff Γ σ ε).mp hε
  have hsq : (algebraMap (𝓞 F) F (ε : 𝓞 F))^2 ≠ 1 := by
    intro h
    exact hsign (signedCuspTranslation_sign ε h)
  let a : InfinitePlace F → ℂ := fun w => w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))
  have hsqw (w : InfinitePlace F) : (a w)^2 - 1 ≠ 0 := by
    intro h
    apply hsq
    apply w.embedding.injective
    simpa [a] using sub_eq_zero.mp h
  have hnorm (w : InfinitePlace F) : Complex.normSq (a w) = 1 := by
    have hp : (a w) ^ orderOf ε = 1 := by
      have h := congrArg (fun u : (𝓞 F)ˣ =>
        w.embedding (algebraMap (𝓞 F) F (u : 𝓞 F))) (pow_orderOf_eq_one ε)
      simpa only [a, Units.val_pow_eq_pow_val, Units.val_one, map_pow, map_one] using h
    have hn := Complex.norm_eq_one_of_pow_eq_one hp hfin.orderOf_pos.ne'
    simp [Complex.normSq_eq_norm_sq, hn]
  let x : InfinitePlace F → ℂ := fun w => -(a w * w.embedding μ) / ((a w)^2 - 1)
  have hx : (fun w => (a w)^2 * x w + a w * w.embedding μ) = x := by
    funext w
    dsimp [x]
    field_simp [hsqw w] <;> ring
  have hy : (fun w => Complex.normSq (a w) * (1 : ℝ)) = fun _ => (1 : ℝ) := by
    funext w
    rw [hnorm]
    simp
  have hfix := cusp_conjugate_affine_action (γ : SL(2,𝓞 F)) σ ε μ hform
    x (fun _ => 1) (by intro w; norm_num)
  change (γ : SL(2,𝓞 F)) • (σ • ptX' F x (fun _ => 1)) =
    σ • ptX' F (fun w => (a w)^2 * x w + a w * w.embedding μ)
      (fun w => Complex.normSq (a w) * (1 : ℝ)) at hfix
  rw [hx, hy] at hfix
  have hγone : (γ : SL(2,𝓞 F)) = 1 := hfree _ γ.property _ hfix
  have hmat : cuspUnitMatrix F ε μ = 1 := by
    rw [← hform, hγone]
    simp
  have hentry : algebraMap (𝓞 F) F (ε : 𝓞 F) = 1 := by
    simpa [cuspUnitMatrix] using congrArg (fun g : SL(2,F) => g 0 0) hmat
  left
  apply Units.ext
  apply RingOfIntegers.coe_injective
  simpa using hentry

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
  obtain ⟨D, hD, hforms⟩ := cuspStab_bounded_unit_form Γ σ
  refine ⟨cuspUnits_finiteIndex Γ σ, cuspUnits_mem_iff Γ σ, D, hD, hforms, ?_, ?_⟩
  · exact fun ε hε hfin => cuspUnits_torsion_sign Γ σ hfree ε hε hfin
  · intro γ x y hy
    obtain ⟨ε, hε, μ, hμ, hform⟩ := hforms γ
    exact ⟨ε, hε, μ, hform,
      cusp_conjugate_affine_action (γ : SL(2,𝓞 F)) σ ε μ hform x y hy⟩

/-! ### SPEC-R3 helper lemmas -/

private lemma bottomRow_ne_zero (g : SL(2,F)) : (bottomRow F g) ≠ (0, 0) := by
  intro h
  have h₁ : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := congrArg Prod.fst h
  have h₂ : (g : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := congrArg Prod.snd h
  have hd : Matrix.det (g : Matrix (Fin 2) (Fin 2) F) = 1 := g.2
  rw [Matrix.det_fin_two] at hd
  simp [h₁, h₂] at hd

private lemma bottomRowFractionalIdeal_ne_zero (g : SL(2,F)) :
    bottomRowFractionalIdeal F g ≠ 0 := by
  rw [bottomRowFractionalIdeal, FractionalIdeal.spanFinset_ne_zero]
  have hrow : (bottomRow F g).1 ≠ 0 ∨ (bottomRow F g).2 ≠ 0 := by
    by_contra hn
    push Not at hn
    exact bottomRow_ne_zero g (Prod.ext hn.1 hn.2)
  rcases hrow with h | h
  · exact ⟨0, Finset.mem_univ _, by simpa [bottomRow] using h⟩
  · exact ⟨1, Finset.mem_univ _, by simpa [bottomRow] using h⟩

private lemma bottomRowFractionalIdeal_coe (g : SL(2,F)) :
    (bottomRowFractionalIdeal F g : Submodule (𝓞 F) F) =
      Submodule.span (𝓞 F) {g 1 0, g 1 1} := by
  rw [bottomRowFractionalIdeal, FractionalIdeal.spanFinset_coe]
  have hrange : Set.range (fun i : Fin 2 =>
      if i = 0 then (bottomRow F g).1 else (bottomRow F g).2) = {g 1 0, g 1 1} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [bottomRow]
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with h | h
      · exact ⟨0, by simp [bottomRow, h.symm]⟩
      · exact ⟨1, by simp [bottomRow, h.symm]⟩
  simp only [Finset.coe_univ, Set.image_univ, hrange]

private lemma bottomRowClass_eq_mk (g : SL(2,F)) :
    bottomRowClass F g =
      ClassGroup.mk F (Units.mk0 (bottomRowFractionalIdeal F g)
        (bottomRowFractionalIdeal_ne_zero g)) := by
  simp [bottomRowClass, bottomRowFractionalIdeal_ne_zero]

private lemma bottomRowFractionalIdeal_eq_coe_span (a b : 𝓞 F) (g : SL(2,F))
    (h₀ : g 1 0 = algebraMap (𝓞 F) F a)
    (h₁ : g 1 1 = algebraMap (𝓞 F) F b) :
    bottomRowFractionalIdeal F g = (Ideal.span ({a, b} : Set (𝓞 F)) :
      FractionalIdeal (𝓞 F)⁰ F) := by
  apply FractionalIdeal.coeToSubmodule_inj.mp
  rw [bottomRowFractionalIdeal_coe, FractionalIdeal.coe_coeIdeal,
    IsLocalization.coeSubmodule_span, h₀, h₁]
  congr 1
  ext x
  simp

private lemma bottomRowClass_eq_mk0 (I : (Ideal (𝓞 F))⁰)
    (g : SL(2,F)) (hrow : bottomRowFractionalIdeal F g =
      (I.1 : FractionalIdeal (𝓞 F)⁰ F)) :
    bottomRowClass F g = ClassGroup.mk0 I := by
  rw [bottomRowClass_eq_mk]
  have hu : Units.mk0 (bottomRowFractionalIdeal F g)
      (bottomRowFractionalIdeal_ne_zero g) = FractionalIdeal.mk0 F I := by
    apply Units.ext
    exact hrow
  rw [hu, ClassGroup.mk_mk0]

private lemma bottomRowClass_surjective : Function.Surjective (bottomRowClass F) := by
  classical
  intro C
  obtain ⟨I, hC⟩ := ClassGroup.mk0_surjective (R := 𝓞 F) C
  have hIbot : (I : Ideal (𝓞 F)) ≠ ⊥ := by
    simpa [Ideal.zero_eq_bot] using (mem_nonZeroDivisors_iff_ne_zero.mp I.2)
  obtain ⟨a, haI, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hIbot
  obtain ⟨b, hpair⟩ := IsDedekindDomain.exists_eq_span_pair haI ha
  let aF : F := algebraMap (𝓞 F) F a
  let bF : F := algebraMap (𝓞 F) F b
  have haF : aF ≠ 0 := by
    intro h
    apply ha
    apply FaithfulSMul.algebraMap_injective (𝓞 F) F
    simpa [aF] using h
  let g : SL(2,F) := ⟨!![0, -aF⁻¹; aF, bF], by
    rw [Matrix.det_fin_two_of]
    simp [haF]⟩
  have hrow : bottomRowFractionalIdeal F g = (I : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [bottomRowFractionalIdeal_eq_coe_span a b g]
    · rw [← hpair]
    · simp [g, aF]
    · simp [g, bF]
  exact ⟨g, (bottomRowClass_eq_mk0 I g hrow).trans hC⟩

private lemma classGroup_mk_eq_iff_scalar_multiple
    (I J : FractionalIdeal (𝓞 F)⁰ F) (hI : I ≠ 0) (hJ : J ≠ 0) :
    ClassGroup.mk F (Units.mk0 I hI) = ClassGroup.mk F (Units.mk0 J hJ) ↔
      ∃ a : F, a ≠ 0 ∧ I * FractionalIdeal.spanSingleton (𝓞 F)⁰ a = J := by
  constructor
  · intro h
    have hq := congrArg (ClassGroup.equiv (R := 𝓞 F) F) h
    have hmapI : Units.mapEquiv
        (↑(FractionalIdeal.canonicalEquiv (𝓞 F)⁰ F F)) (Units.mk0 I hI) =
          Units.mk0 I hI := by
      apply Units.ext
      simp [FractionalIdeal.canonicalEquiv_self]
    have hmapJ : Units.mapEquiv
        (↑(FractionalIdeal.canonicalEquiv (𝓞 F)⁰ F F)) (Units.mk0 J hJ) =
          Units.mk0 J hJ := by
      apply Units.ext
      simp [FractionalIdeal.canonicalEquiv_self]
    have hq' : QuotientGroup.mk' (toPrincipalIdeal (𝓞 F) F).range
          (Units.mk0 I hI) =
        QuotientGroup.mk' (toPrincipalIdeal (𝓞 F) F).range
          (Units.mk0 J hJ) := by
      rw [ClassGroup.equiv_mk F, ClassGroup.equiv_mk F] at hq
      rw [hmapI, hmapJ] at hq
      exact hq
    rcases (QuotientGroup.mk'_eq_mk' (toPrincipalIdeal (𝓞 F) F).range).mp hq' with
      ⟨u, hu, hmul⟩
    rcases MonoidHom.mem_range.mp hu with ⟨v, hv⟩
    refine ⟨v, v.ne_zero, ?_⟩
    have hval := congrArg (fun x : (FractionalIdeal (𝓞 F)⁰ F)ˣ =>
      (x : FractionalIdeal (𝓞 F)⁰ F)) hmul
    have hval' : I * FractionalIdeal.spanSingleton (𝓞 F)⁰ (v : F) = J := by
      simpa [← hv, Units.val_mul, coe_toPrincipalIdeal] using hval
    exact hval'
  · rintro ⟨a, ha, hmul⟩
    let u : Fˣ := Units.mk0 a ha
    have hu : toPrincipalIdeal (𝓞 F) F u ∈ (toPrincipalIdeal (𝓞 F) F).range :=
      ⟨u, rfl⟩
    have hmul' : Units.mk0 I hI * toPrincipalIdeal (𝓞 F) F u = Units.mk0 J hJ := by
      apply Units.ext
      simpa [u, Units.val_mul, coe_toPrincipalIdeal] using hmul
    apply (ClassGroup.equiv (R := 𝓞 F) F).injective
    have hq' : QuotientGroup.mk' (toPrincipalIdeal (𝓞 F) F).range
          (Units.mk0 I hI) =
        QuotientGroup.mk' (toPrincipalIdeal (𝓞 F) F).range
          (Units.mk0 J hJ) :=
      (QuotientGroup.mk'_eq_mk' (toPrincipalIdeal (𝓞 F) F).range).2
        ⟨toPrincipalIdeal (𝓞 F) F u, hu, hmul'⟩
    have hmapI : Units.mapEquiv
        (↑(FractionalIdeal.canonicalEquiv (𝓞 F)⁰ F F)) (Units.mk0 I hI) =
          Units.mk0 I hI := by
      apply Units.ext
      simp [FractionalIdeal.canonicalEquiv_self]
    have hmapJ : Units.mapEquiv
        (↑(FractionalIdeal.canonicalEquiv (𝓞 F)⁰ F F)) (Units.mk0 J hJ) =
          Units.mk0 J hJ := by
      apply Units.ext
      simp [FractionalIdeal.canonicalEquiv_self]
    rw [ClassGroup.equiv_mk F, ClassGroup.equiv_mk F]
    rw [hmapI, hmapJ]
    exact hq'

private lemma bottomRowClass_eq_iff_scalar_multiple (g h : SL(2,F)) :
    bottomRowClass F g = bottomRowClass F h ↔
      ∃ a : F, a ≠ 0 ∧
        bottomRowFractionalIdeal F g * FractionalIdeal.spanSingleton (𝓞 F)⁰ a =
          bottomRowFractionalIdeal F h := by
  rw [bottomRowClass_eq_mk, bottomRowClass_eq_mk]
  exact classGroup_mk_eq_iff_scalar_multiple _ _
    (bottomRowFractionalIdeal_ne_zero g) (bottomRowFractionalIdeal_ne_zero h)

private lemma exists_inverse_row_coefficients (g : SL(2,F)) :
    ∃ a b : F,
      a ∈ (bottomRowFractionalIdeal F g)⁻¹ ∧
      b ∈ (bottomRowFractionalIdeal F g)⁻¹ ∧
      a * g 1 0 + b * g 1 1 = 1 := by
  let I := bottomRowFractionalIdeal F g
  have hIne : I ≠ 0 := by exact bottomRowFractionalIdeal_ne_zero g
  have hIspan : (I : Submodule (𝓞 F) F) =
      Submodule.span (𝓞 F) {g 1 0, g 1 1} := by
    exact bottomRowFractionalIdeal_coe g
  let K : Submodule (𝓞 F) F := {
    carrier := {x | ∃ a b : F,
      a ∈ (I⁻¹ : FractionalIdeal (𝓞 F)⁰ F) ∧
      b ∈ (I⁻¹ : FractionalIdeal (𝓞 F)⁰ F) ∧ a * g 1 0 + b * g 1 1 = x}
    zero_mem' := by
      exact ⟨0, 0,
        Submodule.zero_mem ((I⁻¹ : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F),
        Submodule.zero_mem ((I⁻¹ : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F), by simp⟩
    add_mem' := by
      rintro x y ⟨a, b, ha, hb, rfl⟩ ⟨a', b', ha', hb', rfl⟩
      refine ⟨a + a', b + b', ?_, ?_, ?_⟩
      · exact Submodule.add_mem
          ((I⁻¹ : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) ha ha'
      · exact Submodule.add_mem
          ((I⁻¹ : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) hb hb'
      · ring
    smul_mem' := by
      intro r x hx
      rcases hx with ⟨a, b, ha, hb, hab⟩
      refine ⟨r • a, r • b,
        Submodule.smul_mem ((I⁻¹ : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) r ha,
        Submodule.smul_mem ((I⁻¹ : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) r hb, ?_⟩
      calc
        (r • a) * g 1 0 + (r • b) * g 1 1 =
            (r • (a * g 1 0 + b * g 1 1)) := by
          simp only [Algebra.smul_def]
          ring
        _ = r • x := by rw [hab]
  }
  have hprod_le :
      (I : Submodule (𝓞 F) F) *
        ((I⁻¹ : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) ≤ K := by
    rw [Submodule.mul_le]
    intro x hx y hy
    have hx' : x ∈ Submodule.span (𝓞 F) {g 1 0, g 1 1} := by
      rw [← hIspan]
      exact hx
    obtain ⟨r, s, hrs⟩ := Submodule.mem_span_pair.mp hx'
    refine ⟨r • y, s • y, Submodule.smul_mem _ r hy,
      Submodule.smul_mem _ s hy, ?_⟩
    calc
      (r • y) * g 1 0 + (s • y) * g 1 1 = (r • g 1 0 + s • g 1 1) * y := by
        simp only [Algebra.smul_def]
        ring
      _ = x * y := by rw [hrs]
  have hone : (1 : F) ∈ I * I⁻¹ := by
    rw [mul_inv_cancel₀ hIne]
    simp
  have hone' : (1 : F) ∈ (I : Submodule (𝓞 F) F) *
      ((I⁻¹ : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) := by
    simpa only [FractionalIdeal.coe_mul] using (FractionalIdeal.mem_coe).mpr hone
  rcases hprod_le hone' with ⟨a, b, ha, hb, hab⟩
  exact ⟨a, b, ha, hb, hab⟩

private lemma exists_row_completion (g : SL(2,F)) :
    ∃ M : SL(2,F),
      M 1 0 = g 1 0 ∧ M 1 1 = g 1 1 ∧
      M 0 0 ∈ (bottomRowFractionalIdeal F g)⁻¹ ∧
      M 0 1 ∈ (bottomRowFractionalIdeal F g)⁻¹ := by
  obtain ⟨a, b, ha, hb, hab⟩ := exists_inverse_row_coefficients g
  let M : SL(2,F) := ⟨!![b, -a; g 1 0, g 1 1], by
    rw [Matrix.det_fin_two_of]
    calc
      b * g 1 1 - (-a) * g 1 0 = a * g 1 0 + b * g 1 1 := by ring
      _ = 1 := hab⟩
  refine ⟨M, ?_, ?_, ?_, ?_⟩
  · simp [M]
  · simp [M]
  · simpa [M] using hb
  · change -a ∈ (bottomRowFractionalIdeal F g)⁻¹
    exact Submodule.neg_mem
      (((bottomRowFractionalIdeal F g)⁻¹ : FractionalIdeal (𝓞 F)⁰ F) :
        Submodule (𝓞 F) F) ha

private lemma same_bottomRow_borel (g h : SL(2,F))
    (hh : bottomRow F g = bottomRow F h) : h * g⁻¹ ∈ borelSL F := by
  change (h * g⁻¹ : SL(2,F)) 1 0 = 0
  have hc : g 1 0 = h 1 0 := congrArg Prod.fst hh
  have hd : g 1 1 = h 1 1 := congrArg Prod.snd hh
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.SL2_inv_expl]
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.tail_cons]
  rw [hc, hd]
  ring

private lemma quotient_eq_of_bottomRow_eq (g h : SL(2,F))
    (hh : bottomRow F g = bottomRow F h) :
    Quotient.mk (QuotientGroup.rightRel (borelSL F)) g =
      Quotient.mk (QuotientGroup.rightRel (borelSL F)) h := by
  apply Quotient.sound
  exact QuotientGroup.rightRel_apply.mpr (same_bottomRow_borel g h hh)

private lemma bottomRow_first_mem (g : SL(2,F)) :
    g 1 0 ∈ bottomRowFractionalIdeal F g := by
  change g 1 0 ∈ (bottomRowFractionalIdeal F g : Submodule (𝓞 F) F)
  rw [bottomRowFractionalIdeal_coe]
  exact Submodule.subset_span (by simp)

private lemma bottomRow_second_mem (g : SL(2,F)) :
    g 1 1 ∈ bottomRowFractionalIdeal F g := by
  change g 1 1 ∈ (bottomRowFractionalIdeal F g : Submodule (𝓞 F) F)
  rw [bottomRowFractionalIdeal_coe]
  exact Submodule.subset_span (by simp)

private lemma exists_integral_transition_of_equal_row_ideal
    (g h : SL(2,F))
    (hI : bottomRowFractionalIdeal F g = bottomRowFractionalIdeal F h) :
    ∃ γ : SL(2,𝓞 F),
      Quotient.mk (QuotientGroup.rightRel (borelSL F)) g =
        Quotient.mk (QuotientGroup.rightRel (borelSL F)) (h * toSLF F γ) := by
  classical
  obtain ⟨M, hMc, hMd, hM₀, hM₁⟩ := exists_row_completion g
  obtain ⟨N, hNc, hNd, hN₀, hN₁⟩ := exists_row_completion h
  let I := bottomRowFractionalIdeal F g
  have hIne : I ≠ 0 := bottomRowFractionalIdeal_ne_zero g
  have hIinv : (bottomRowFractionalIdeal F g)⁻¹ =
      (bottomRowFractionalIdeal F h)⁻¹ := congrArg (fun J : FractionalIdeal (𝓞 F)⁰ F => J⁻¹) hI
  have hM₀' : M 0 0 ∈ I⁻¹ := hM₀
  have hM₁' : M 0 1 ∈ I⁻¹ := hM₁
  have hM₂' : M 1 0 ∈ I := by rw [hMc]; exact bottomRow_first_mem g
  have hM₃' : M 1 1 ∈ I := by rw [hMd]; exact bottomRow_second_mem g
  have hN₀' : N 0 0 ∈ I⁻¹ := hIinv.symm ▸ hN₀
  have hN₁' : N 0 1 ∈ I⁻¹ := hIinv.symm ▸ hN₁
  have hN₂' : N 1 0 ∈ I := by
    change N 1 0 ∈ bottomRowFractionalIdeal F g
    rw [hI, hNc]
    exact bottomRow_first_mem h
  have hN₃' : N 1 1 ∈ I := by
    change N 1 1 ∈ bottomRowFractionalIdeal F g
    rw [hI, hNd]
    exact bottomRow_second_mem h
  have hIprod : I * I⁻¹ = (1 : FractionalIdeal (𝓞 F)⁰ F) :=
    mul_inv_cancel₀ hIne
  have prod01 (x : F) (y : F) (hx : x ∈ I) (hy : y ∈ I⁻¹) :
      x * y ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    have hp := FractionalIdeal.mul_mem_mul hx hy
    simpa [hIprod] using hp
  have prod10 (x : F) (y : F) (hx : x ∈ I⁻¹) (hy : y ∈ I) :
      x * y ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    have hp := FractionalIdeal.mul_mem_mul hy hx
    simpa [mul_comm, hIprod] using hp
  have h00 : M 1 1 * N 0 0 - M 0 1 * N 1 0 ∈
      (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    have hp := prod01 (M 1 1) (N 0 0) hM₃' hN₀'
    have hq := prod10 (M 0 1) (N 1 0) hM₁' hN₂'
    have hp' : M 1 1 * N 0 0 ∈ (1 : Submodule (𝓞 F) F) := by
      rw [← FractionalIdeal.coe_one]
      exact (FractionalIdeal.mem_coe).mpr hp
    have hq' : M 0 1 * N 1 0 ∈ (1 : Submodule (𝓞 F) F) := by
      rw [← FractionalIdeal.coe_one]
      exact (FractionalIdeal.mem_coe).mpr hq
    have hs := Submodule.sub_mem _ hp' hq'
    rw [← FractionalIdeal.coe_one] at hs
    exact (FractionalIdeal.mem_coe).mp hs
  have h01 : M 1 1 * N 0 1 - M 0 1 * N 1 1 ∈
      (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    have hp := prod01 (M 1 1) (N 0 1) hM₃' hN₁'
    have hq := prod10 (M 0 1) (N 1 1) hM₁' hN₃'
    have hp' : M 1 1 * N 0 1 ∈ (1 : Submodule (𝓞 F) F) := by
      rw [← FractionalIdeal.coe_one]
      exact (FractionalIdeal.mem_coe).mpr hp
    have hq' : M 0 1 * N 1 1 ∈ (1 : Submodule (𝓞 F) F) := by
      rw [← FractionalIdeal.coe_one]
      exact (FractionalIdeal.mem_coe).mpr hq
    have hs := Submodule.sub_mem _ hp' hq'
    rw [← FractionalIdeal.coe_one] at hs
    exact (FractionalIdeal.mem_coe).mp hs
  have h10 : -(M 1 0 * N 0 0) + M 0 0 * N 1 0 ∈
      (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    have hp := prod01 (M 1 0) (N 0 0) hM₂' hN₀'
    have hq := prod10 (M 0 0) (N 1 0) hM₀' hN₂'
    have hp' : M 1 0 * N 0 0 ∈ (1 : Submodule (𝓞 F) F) := by
      rw [← FractionalIdeal.coe_one]
      exact (FractionalIdeal.mem_coe).mpr hp
    have hq' : M 0 0 * N 1 0 ∈ (1 : Submodule (𝓞 F) F) := by
      rw [← FractionalIdeal.coe_one]
      exact (FractionalIdeal.mem_coe).mpr hq
    have hs := Submodule.add_mem _ (Submodule.neg_mem _ hp') hq'
    rw [← FractionalIdeal.coe_one] at hs
    exact (FractionalIdeal.mem_coe).mp hs
  have h11 : -(M 1 0 * N 0 1) + M 0 0 * N 1 1 ∈
      (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    have hp := prod01 (M 1 0) (N 0 1) hM₂' hN₁'
    have hq := prod10 (M 0 0) (N 1 1) hM₀' hN₃'
    have hp' : M 1 0 * N 0 1 ∈ (1 : Submodule (𝓞 F) F) := by
      rw [← FractionalIdeal.coe_one]
      exact (FractionalIdeal.mem_coe).mpr hp
    have hq' : M 0 0 * N 1 1 ∈ (1 : Submodule (𝓞 F) F) := by
      rw [← FractionalIdeal.coe_one]
      exact (FractionalIdeal.mem_coe).mpr hq
    have hs := Submodule.add_mem _ (Submodule.neg_mem _ hp') hq'
    rw [← FractionalIdeal.coe_one] at hs
    exact (FractionalIdeal.mem_coe).mp hs
  let T : SL(2,F) := M⁻¹ * N
  have hT00formula : T 0 0 = M 1 1 * N 0 0 - M 0 1 * N 1 0 := by
    change ((M⁻¹ * N : SL(2,F)) : Matrix (Fin 2) (Fin 2) F) 0 0 = _
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.SL2_inv_expl]
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hT01formula : T 0 1 = M 1 1 * N 0 1 - M 0 1 * N 1 1 := by
    change ((M⁻¹ * N : SL(2,F)) : Matrix (Fin 2) (Fin 2) F) 0 1 = _
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.SL2_inv_expl]
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hT10formula : T 1 0 = -(M 1 0 * N 0 0) + M 0 0 * N 1 0 := by
    change ((M⁻¹ * N : SL(2,F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = _
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.SL2_inv_expl]
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hT11formula : T 1 1 = -(M 1 0 * N 0 1) + M 0 0 * N 1 1 := by
    change ((M⁻¹ * N : SL(2,F)) : Matrix (Fin 2) (Fin 2) F) 1 1 = _
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.SL2_inv_expl]
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hT00 : T 0 0 ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [hT00formula]
    exact h00
  have hT01 : T 0 1 ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [hT01formula]
    exact h01
  have hT10 : T 1 0 ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [hT10formula]
    exact h10
  have hT11 : T 1 1 ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [hT11formula]
    exact h11
  have hTentries (i j : Fin 2) : T i j ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    fin_cases i <;> fin_cases j
    · exact hT00
    · exact hT01
    · exact hT10
    · exact hT11
  have hLift (i j : Fin 2) : ∃ a : 𝓞 F, algebraMap (𝓞 F) F a = T i j := by
    exact (FractionalIdeal.mem_one_iff (𝓞 F)⁰).mp (hTentries i j)
  let A : Matrix (Fin 2) (Fin 2) (𝓞 F) := fun i j => Classical.choose (hLift i j)
  have hAmap (i j : Fin 2) : algebraMap (𝓞 F) F (A i j) = T i j :=
    Classical.choose_spec (hLift i j)
  have hdetMap : algebraMap (𝓞 F) F (Matrix.det A) = 1 := by
    rw [RingHom.map_det (algebraMap (𝓞 F) F) A]
    calc
      Matrix.det (fun i j => algebraMap (𝓞 F) F (A i j)) =
          Matrix.det (T : Matrix (Fin 2) (Fin 2) F) := by
        congr 1
        ext i j
        exact hAmap i j
      _ = 1 := T.2
  have hdetA : Matrix.det A = 1 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 F) F
    simpa using hdetMap
  let δ : SL(2,𝓞 F) := ⟨A, hdetA⟩
  have hδ : toSLF F δ = T := by
    apply Subtype.ext
    change (algebraMap (𝓞 F) F).mapMatrix A = (T : Matrix (Fin 2) (Fin 2) F)
    ext i j
    exact hAmap i j
  have hMN : M * toSLF F δ = N := by
    rw [hδ]
    simp [T, mul_assoc]
  have hrowM : bottomRow F (g * toSLF F δ) = bottomRow F (M * toSLF F δ) := by
    simp [bottomRow, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two, hMc, hMd]
  have hrowN : bottomRow F (M * toSLF F δ) = bottomRow F N := congrArg (bottomRow F) hMN
  have hrowH : bottomRow F N = bottomRow F h := by simp [bottomRow, hNc, hNd]
  have hrow : bottomRow F (g * toSLF F δ) = bottomRow F h := hrowM.trans (hrowN.trans hrowH)
  have hrel : (h * toSLF F δ⁻¹) * g⁻¹ ∈ borelSL F := by
    simpa [_root_.mul_inv_rev, mul_assoc] using
      (same_bottomRow_borel (g * toSLF F δ) h hrow)
  refine ⟨δ⁻¹, ?_⟩
  apply Quotient.sound
  exact QuotientGroup.rightRel_apply.mpr hrel

private lemma bottomRowFractionalIdeal_left_borel
    (b : SL(2,F)) (hb : b ∈ borelSL F) (g : SL(2,F)) :
    b 1 1 ≠ 0 ∧ bottomRowFractionalIdeal F (b * g) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ (b 1 1) * bottomRowFractionalIdeal F g := by
  have hb₀ : b 1 0 = 0 := hb
  let u : F := b 1 1
  have hu : u ≠ 0 := by
    intro hu0
    have hdet : Matrix.det (b : Matrix (Fin 2) (Fin 2) F) = 1 := b.2
    rw [Matrix.det_fin_two] at hdet
    simp [hb₀, u, hu0] at hdet
  have hrow₀ : (b * g) 1 0 = u * g 1 0 := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    simp [u, hb₀]
  have hrow₁ : (b * g) 1 1 = u * g 1 1 := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    simp [u, hb₀]
  refine ⟨hu, ?_⟩
  have hrow : bottomRowFractionalIdeal F (b * g) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ u * bottomRowFractionalIdeal F g := by
    apply FractionalIdeal.coeToSubmodule_inj.mp
    rw [bottomRowFractionalIdeal_coe, FractionalIdeal.coe_mul,
      FractionalIdeal.coe_spanSingleton, bottomRowFractionalIdeal_coe,
      hrow₀, hrow₁, Submodule.span_mul_span]
    apply congrArg (Submodule.span (𝓞 F))
    ext x
    simp
  simpa [u] using hrow

private lemma bottomRowFractionalIdeal_right_early_le (g : SL(2,F))
    (γ : SL(2,𝓞 F)) :
    bottomRowFractionalIdeal F (g * toSLF F γ) ≤ bottomRowFractionalIdeal F g := by
  change (bottomRowFractionalIdeal F (g * toSLF F γ) : Submodule (𝓞 F) F) ≤
    (bottomRowFractionalIdeal F g : Submodule (𝓞 F) F)
  rw [bottomRowFractionalIdeal_coe, bottomRowFractionalIdeal_coe]
  apply Submodule.span_le.mpr
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  have hrow₀ : (g * toSLF F γ) 1 0 =
      g 1 0 * algebraMap (𝓞 F) F (γ 0 0) +
        g 1 1 * algebraMap (𝓞 F) F (γ 1 0) := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    simp [Matrix.mul_apply, Fin.sum_univ_two, toSLF]
  have hrow₁ : (g * toSLF F γ) 1 1 =
      g 1 0 * algebraMap (𝓞 F) F (γ 0 1) +
        g 1 1 * algebraMap (𝓞 F) F (γ 1 1) := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    simp [Matrix.mul_apply, Fin.sum_univ_two, toSLF]
  have hc : g 1 0 ∈ Submodule.span (𝓞 F) {g 1 0, g 1 1} :=
    Submodule.subset_span (by simp)
  have hd : g 1 1 ∈ Submodule.span (𝓞 F) {g 1 0, g 1 1} :=
    Submodule.subset_span (by simp)
  have hca : g 1 0 * algebraMap (𝓞 F) F (γ 0 0) ∈
      Submodule.span (𝓞 F) {g 1 0, g 1 1} := by
    simpa [Algebra.smul_def, mul_comm] using
      (Submodule.smul_mem (Submodule.span (𝓞 F) {g 1 0, g 1 1}) (γ 0 0) hc)
  have hdb : g 1 1 * algebraMap (𝓞 F) F (γ 1 0) ∈
      Submodule.span (𝓞 F) {g 1 0, g 1 1} := by
    simpa [Algebra.smul_def, mul_comm] using
      (Submodule.smul_mem (Submodule.span (𝓞 F) {g 1 0, g 1 1}) (γ 1 0) hd)
  have hca' : g 1 0 * algebraMap (𝓞 F) F (γ 0 1) ∈
      Submodule.span (𝓞 F) {g 1 0, g 1 1} := by
    simpa [Algebra.smul_def, mul_comm] using
      (Submodule.smul_mem (Submodule.span (𝓞 F) {g 1 0, g 1 1}) (γ 0 1) hc)
  have hdb' : g 1 1 * algebraMap (𝓞 F) F (γ 1 1) ∈
      Submodule.span (𝓞 F) {g 1 0, g 1 1} := by
    simpa [Algebra.smul_def, mul_comm] using
      (Submodule.smul_mem (Submodule.span (𝓞 F) {g 1 0, g 1 1}) (γ 1 1) hd)
  rcases hx with hx | hx
  · rw [hx, hrow₀]
    exact Submodule.add_mem _ hca hdb
  · rw [hx, hrow₁]
    exact Submodule.add_mem _ hca' hdb'

private lemma bottomRowFractionalIdeal_right_early (g : SL(2,F))
    (γ : SL(2,𝓞 F)) :
    bottomRowFractionalIdeal F (g * toSLF F γ) = bottomRowFractionalIdeal F g := by
  apply le_antisymm (bottomRowFractionalIdeal_right_early_le g γ)
  have hmul : (g * toSLF F γ) * toSLF F γ⁻¹ = g := by simp [mul_assoc]
  have h := bottomRowFractionalIdeal_right_early_le (g * toSLF F γ) γ⁻¹
  rw [hmul] at h
  exact h

private lemma bottomRowClass_left_borel
    (b : SL(2,F)) (hb : b ∈ borelSL F) (g : SL(2,F)) :
    bottomRowClass F (b * g) = bottomRowClass F g := by
  obtain ⟨hu, hrow⟩ := bottomRowFractionalIdeal_left_borel b hb g
  apply (bottomRowClass_eq_iff_scalar_multiple (b * g) g).2
  refine ⟨(b 1 1)⁻¹, inv_ne_zero hu, ?_⟩
  calc
    bottomRowFractionalIdeal F (b * g) *
        FractionalIdeal.spanSingleton (𝓞 F)⁰ (b 1 1)⁻¹ =
      (FractionalIdeal.spanSingleton (𝓞 F)⁰ (b 1 1) *
        bottomRowFractionalIdeal F g) *
          FractionalIdeal.spanSingleton (𝓞 F)⁰ (b 1 1)⁻¹ := by rw [hrow]
    _ = bottomRowFractionalIdeal F g := by
      calc
        _ = bottomRowFractionalIdeal F g *
            (FractionalIdeal.spanSingleton (𝓞 F)⁰ (b 1 1) *
              FractionalIdeal.spanSingleton (𝓞 F)⁰ (b 1 1)⁻¹) := by ac_rfl
        _ = bottomRowFractionalIdeal F g := by
          rw [FractionalIdeal.spanSingleton_mul_spanSingleton]
          simp [hu]

private lemma bottomRowClass_right_integral (g : SL(2,F)) (γ : SL(2,𝓞 F)) :
    bottomRowClass F (g * toSLF F γ) = bottomRowClass F g := by
  rw [bottomRowClass_eq_mk, bottomRowClass_eq_mk]
  apply congrArg (ClassGroup.mk F)
  apply Units.ext
  exact bottomRowFractionalIdeal_right_early g γ

private lemma quotient_eq_left_borel
    (b : SL(2,F)) (hb : b ∈ borelSL F) (g : SL(2,F)) :
    Quotient.mk (QuotientGroup.rightRel (borelSL F)) g =
      Quotient.mk (QuotientGroup.rightRel (borelSL F)) (b * g) := by
  apply Quotient.sound
  apply QuotientGroup.rightRel_apply.mpr
  simpa [mul_assoc] using hb

private lemma bottomRowClass_eq_iff_integral_orbit (g h : SL(2,F)) :
    bottomRowClass F g = bottomRowClass F h ↔
      ∃ γ : SL(2,𝓞 F),
        Quotient.mk (QuotientGroup.rightRel (borelSL F)) g =
          Quotient.mk (QuotientGroup.rightRel (borelSL F)) (h * toSLF F γ) := by
  constructor
  · intro hclass
    obtain ⟨a, ha, hscale⟩ :=
      (bottomRowClass_eq_iff_scalar_multiple g h).mp hclass
    let b : SL(2,F) := ⟨!![a⁻¹, 0; 0, a], by
      rw [Matrix.det_fin_two_of]
      simp [ha]⟩
    have hb : b ∈ borelSL F := by
      change (b : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
      simp [b]
    have hscale' : bottomRowFractionalIdeal F (b * g) =
        bottomRowFractionalIdeal F h := by
      calc
        bottomRowFractionalIdeal F (b * g) =
            FractionalIdeal.spanSingleton (𝓞 F)⁰ a * bottomRowFractionalIdeal F g := by
          simpa [b] using (bottomRowFractionalIdeal_left_borel b hb g).2
        _ = bottomRowFractionalIdeal F g * FractionalIdeal.spanSingleton (𝓞 F)⁰ a := by
          rw [mul_comm]
        _ = bottomRowFractionalIdeal F h := hscale
    obtain ⟨γ, htrans⟩ := exists_integral_transition_of_equal_row_ideal (b * g) h hscale'
    exact ⟨γ, (quotient_eq_left_borel b hb g).trans htrans⟩
  · rintro ⟨γ, hq⟩
    have hrel : (h * toSLF F γ) * g⁻¹ ∈ borelSL F :=
      QuotientGroup.rightRel_apply.mp (Quotient.exact hq)
    let b : SL(2,F) := (h * toSLF F γ) * g⁻¹
    have hb : b ∈ borelSL F := hrel
    have hbg : b * g = h * toSLF F γ := by simp [b, mul_assoc]
    calc
      bottomRowClass F g = bottomRowClass F (b * g) :=
        (bottomRowClass_left_borel b hb g).symm
      _ = bottomRowClass F (h * toSLF F γ) := congrArg (bottomRowClass F) hbg
      _ = bottomRowClass F h := bottomRowClass_right_integral h γ

private lemma quotient_right_mul_congr (x y δ : SL(2,F))
    (h : Quotient.mk (QuotientGroup.rightRel (borelSL F)) x =
      Quotient.mk (QuotientGroup.rightRel (borelSL F)) y) :
    Quotient.mk (QuotientGroup.rightRel (borelSL F)) (x * δ) =
      Quotient.mk (QuotientGroup.rightRel (borelSL F)) (y * δ) := by
  apply Quotient.sound
  apply QuotientGroup.rightRel_apply.mpr
  have hrel : y * x⁻¹ ∈ borelSL F := QuotientGroup.rightRel_apply.mp (Quotient.exact h)
  simpa [_root_.mul_inv_rev, mul_assoc] using hrel

private def cuspOrbitSetoid (Γ : Subgroup SL(2,𝓞 F)) (A : SL(2,F))
    (rep : (SL(2,𝓞 F) ⧸ Γ) → SL(2,𝓞 F)) : Setoid (SL(2,𝓞 F) ⧸ Γ) where
  r p q := ∃ γ : Γ,
    Quotient.mk (QuotientGroup.rightRel (borelSL F))
      (A * toSLF F (rep p)) =
    Quotient.mk (QuotientGroup.rightRel (borelSL F))
      (A * toSLF F (rep q) * toSLF F (γ : SL(2,𝓞 F)))
  iseqv := by
    constructor
    · intro p
      exact ⟨1, by simp⟩
    · intro p q hpq
      rcases hpq with ⟨γ, hγ⟩
      refine ⟨γ⁻¹, ?_⟩
      have hmul := quotient_right_mul_congr
        (A * toSLF F (rep p))
        (A * toSLF F (rep q) * toSLF F (γ : SL(2,𝓞 F)))
        (toSLF F ((γ⁻¹ : Γ) : SL(2,𝓞 F))) hγ
      simpa [mul_assoc] using hmul.symm
    · intro p q r hpq hqr
      rcases hpq with ⟨γ, hγ⟩
      rcases hqr with ⟨δ, hδ⟩
      refine ⟨δ * γ, ?_⟩
      have hmul := quotient_right_mul_congr
        (A * toSLF F (rep q))
        (A * toSLF F (rep r) * toSLF F (δ : SL(2,𝓞 F)))
        (toSLF F (γ : SL(2,𝓞 F))) hδ
      calc
        Quotient.mk (QuotientGroup.rightRel (borelSL F))
            (A * toSLF F (rep p)) =
          Quotient.mk (QuotientGroup.rightRel (borelSL F))
            (A * toSLF F (rep q) * toSLF F (γ : SL(2,𝓞 F))) := hγ
        _ = Quotient.mk (QuotientGroup.rightRel (borelSL F))
            (A * toSLF F (rep r) * toSLF F (δ : SL(2,𝓞 F)) *
              toSLF F (γ : SL(2,𝓞 F))) := hmul
        _ = Quotient.mk (QuotientGroup.rightRel (borelSL F))
            (A * toSLF F (rep r) * toSLF F ((δ * γ : Γ) : SL(2,𝓞 F))) := by
          simp [map_mul, mul_assoc]

private lemma mem_cuspStab_iff (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (γ : Γ) :
    γ ∈ cuspStab F Γ σ ↔
      σ⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * σ ∈ borelSL F := by
  simp only [cuspStab, Subgroup.mem_comap, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  rfl

private lemma cuspStab_transition_image (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (γ γ' : Γ) (h : γ' * γ⁻¹ ∈ cuspStab F Γ σ) :
    Quotient.mk (QuotientGroup.rightRel (borelSL F))
        (σ⁻¹ * toSLF F (γ : SL(2,𝓞 F))) =
      Quotient.mk (QuotientGroup.rightRel (borelSL F))
        (σ⁻¹ * toSLF F (γ' : SL(2,𝓞 F))) := by
  have hconj := (mem_cuspStab_iff Γ σ (γ' * γ⁻¹)).mp h
  have hrel : (σ⁻¹ * toSLF F (γ' : SL(2,𝓞 F))) *
      (σ⁻¹ * toSLF F (γ : SL(2,𝓞 F)))⁻¹ ∈ borelSL F := by
    simpa [map_mul, map_inv, _root_.mul_inv_rev, mul_assoc] using hconj
  apply Quotient.sound
  exact QuotientGroup.rightRel_apply.mpr hrel

private def cuspIndexSetoid (Γ : Subgroup SL(2,𝓞 F))
    (a : ClassGroup (𝓞 F) → SL(2,F))
    (rep : (SL(2,𝓞 F) ⧸ Γ) → SL(2,𝓞 F)) :
    Setoid (ClassGroup (𝓞 F) × (SL(2,𝓞 F) ⧸ Γ)) where
  r x y := x.1 = y.1 ∧
    cuspOrbitSetoid Γ (a x.1) rep x.2 y.2
  iseqv := by
    constructor
    · intro x
      exact ⟨rfl, (cuspOrbitSetoid Γ (a x.1) rep).iseqv.refl x.2⟩
    · rintro ⟨C, p⟩ ⟨C', q⟩ h
      rcases h with ⟨hC, hq⟩
      cases hC
      exact ⟨rfl, (cuspOrbitSetoid Γ (a C) rep).iseqv.symm hq⟩
    · rintro ⟨C, p⟩ ⟨C', q⟩ ⟨C'', r⟩ hxy hyz
      rcases hxy with ⟨hxyC, hxy⟩
      rcases hyz with ⟨hyzC, hyz⟩
      cases hxyC
      cases hyzC
      exact ⟨rfl, (cuspOrbitSetoid Γ (a C) rep).iseqv.trans hxy hyz⟩

set_option maxHeartbeats 500000 in
private theorem exists_cusp_reps_bijective (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] :
    ∃ (ι : Type) (_ : Fintype ι) (σ : ι → SL(2,F)),
      Function.Bijective (fun p : (Σ i, CuspCosets F Γ (σ i)) =>
        Quotient.mk (QuotientGroup.rightRel (borelSL F))
          ((σ p.1)⁻¹ * toSLF F ((p.2.out : Γ) : SL(2,𝓞 F)))) := by
  classical
  letI : Fintype (ClassGroup (𝓞 F)) := inferInstance
  let P := SL(2,𝓞 F) ⧸ Γ
  letI : Fintype P := Subgroup.fintypeQuotientOfFiniteIndex
  have hmkSurj : Function.Surjective
      (Quotient.mk (QuotientGroup.leftRel Γ) : SL(2,𝓞 F) → P) := Quotient.mk_surjective
  let rep : P → SL(2,𝓞 F) := fun p => Classical.choose (hmkSurj p)
  have hrep (p : P) : Quotient.mk (QuotientGroup.leftRel Γ) (rep p) = p :=
    Classical.choose_spec (hmkSurj p)
  let a : ClassGroup (𝓞 F) → SL(2,F) := fun C => Classical.choose (bottomRowClass_surjective C)
  have ha (C : ClassGroup (𝓞 F)) : bottomRowClass F (a C) = C :=
    Classical.choose_spec (bottomRowClass_surjective C)
  let ι := Quotient (cuspIndexSetoid Γ a rep)
  letI : Fintype ι := by
    dsimp [ι]
    infer_instance
  let indexRep : ι → ClassGroup (𝓞 F) × P := Quotient.out
  have hindexRep (i : ι) :
      Quotient.mk (cuspIndexSetoid Γ a rep) (indexRep i) = i := Quotient.out_eq' i
  let σ : ι → SL(2,F) := fun i =>
    (a (indexRep i).1 * toSLF F (rep (indexRep i).2))⁻¹
  have hσ (i : ι) : (σ i)⁻¹ = a (indexRep i).1 * toSLF F (rep (indexRep i).2) := by
    simp [σ]
  let Q := Quotient (QuotientGroup.rightRel (borelSL F))
  let f : (Σ i, CuspCosets F Γ (σ i)) → Q := fun p =>
    Quotient.mk (QuotientGroup.rightRel (borelSL F))
      ((σ p.1)⁻¹ * toSLF F ((p.2.out : Γ) : SL(2,𝓞 F)))
  refine ⟨ι, inferInstance, σ, ?_⟩
  change Function.Bijective f
  have hsurj : Function.Surjective f := by
    intro z
    let g : SL(2,F) := Quotient.out z
    have hg : Quotient.mk (QuotientGroup.rightRel (borelSL F)) g = z :=
      Quotient.out_eq' z
    let C : ClassGroup (𝓞 F) := bottomRowClass F g
    let C0 := C
    have hclass : bottomRowClass F g = bottomRowClass F (a C0) := by
      simpa [C0, C] using (ha C0).symm
    obtain ⟨δ, hδorbit⟩ :=
      (bottomRowClass_eq_iff_integral_orbit g (a C0)).mp hclass
    let pG : P := Quotient.mk (QuotientGroup.leftRel Γ) δ
    have hmk : Quotient.mk (QuotientGroup.leftRel Γ) (rep pG) =
        Quotient.mk (QuotientGroup.leftRel Γ) δ := by
      simpa [pG] using hrep pG
    have hleft : (rep pG)⁻¹ * δ ∈ Γ :=
      QuotientGroup.leftRel_apply.mp (Quotient.exact hmk)
    let β : Γ := ⟨(rep pG)⁻¹ * δ, hleft⟩
    have hδ : δ = rep pG * (β : SL(2,𝓞 F)) := by
      change δ = rep pG * ((rep pG)⁻¹ * δ)
      group
    have hgbase :
        Quotient.mk (QuotientGroup.rightRel (borelSL F)) g =
          Quotient.mk (QuotientGroup.rightRel (borelSL F))
            (a C0 * toSLF F (rep pG) * toSLF F (β : SL(2,𝓞 F))) := by
      simpa [hδ, map_mul, mul_assoc] using hδorbit
    let i : ι := Quotient.mk (cuspIndexSetoid Γ a rep) (C0, pG)
    have hidx : Quotient.mk (cuspIndexSetoid Γ a rep) (indexRep i) =
        Quotient.mk (cuspIndexSetoid Γ a rep) (C0, pG) := by
      simpa [i] using hindexRep i
    rcases Quotient.exact hidx with ⟨hC, hOrbit⟩
    let C1 := (indexRep i).1
    let p1 := (indexRep i).2
    have hclass1 : bottomRowClass F (a C1) = bottomRowClass F (a C0) := by
      calc
        _ = C1 := ha C1
        _ = C0 := hC
        _ = bottomRowClass F (a C0) := (ha C0).symm
    obtain ⟨ε, hε⟩ := hOrbit
    let α : Γ := ε⁻¹ * β
    have hmove :
        Quotient.mk (QuotientGroup.rightRel (borelSL F))
          ((a (indexRep i).1 * toSLF F (rep (indexRep i).2)) *
            toSLF F (α : SL(2,𝓞 F))) =
        Quotient.mk (QuotientGroup.rightRel (borelSL F))
          ((a C0 * toSLF F (rep pG)) * toSLF F (β : SL(2,𝓞 F))) := by
      have hm := quotient_right_mul_congr
        (a (indexRep i).1 * toSLF F (rep (indexRep i).2))
        (a (indexRep i).1 * toSLF F (rep pG) * toSLF F (ε : SL(2,𝓞 F)))
        (toSLF F (α : SL(2,𝓞 F))) hε
      simpa [α, hC, map_mul, mul_assoc] using hm
    have hfinal : Quotient.mk (QuotientGroup.rightRel (borelSL F)) g =
        Quotient.mk (QuotientGroup.rightRel (borelSL F))
          ((σ i)⁻¹ * toSLF F (α : SL(2,𝓞 F))) := by
      rw [hσ i]
      exact hgbase.trans hmove.symm
    let c : CuspCosets F Γ (σ i) :=
      Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ (σ i))) α
    have hcEq : Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ (σ i))) c.out =
        Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ (σ i))) α := by
      simpa [c] using (Quotient.out_eq' c)
    have hstab : α * c.out⁻¹ ∈ cuspStab F Γ (σ i) :=
      QuotientGroup.rightRel_apply.mp (Quotient.exact hcEq)
    have hcout := cuspStab_transition_image Γ (σ i) c.out α hstab
    refine ⟨⟨i, c⟩, ?_⟩
    dsimp [f]
    exact hcout.trans (hfinal.symm.trans hg)
  have hinj : Function.Injective f := by
    intro p p' hp
    rcases p with ⟨i, c⟩
    rcases p' with ⟨j, d⟩
    let γ : Γ := c.out
    let δ : Γ := d.out
    let x : ClassGroup (𝓞 F) × P := indexRep i
    let y : ClassGroup (𝓞 F) × P := indexRep j
    have hq : Quotient.mk (QuotientGroup.rightRel (borelSL F))
        ((a x.1 * toSLF F (rep x.2)) * toSLF F (γ : SL(2,𝓞 F))) =
      Quotient.mk (QuotientGroup.rightRel (borelSL F))
        ((a y.1 * toSLF F (rep y.2)) * toSLF F (δ : SL(2,𝓞 F))) := by
      simpa [f, hσ, γ, δ, x, y] using hp
    have hxi : bottomRowClass F
        ((a x.1 * toSLF F (rep x.2)) * toSLF F (γ : SL(2,𝓞 F))) = x.1 := by
      calc
        _ = bottomRowClass F (a x.1 * toSLF F (rep x.2)) :=
          bottomRowClass_right_integral _ γ
        _ = bottomRowClass F (a x.1) := bottomRowClass_right_integral _ _
        _ = x.1 := ha x.1
    have hyi : bottomRowClass F
        ((a y.1 * toSLF F (rep y.2)) * toSLF F (δ : SL(2,𝓞 F))) = y.1 := by
      calc
        _ = bottomRowClass F (a y.1 * toSLF F (rep y.2)) :=
          bottomRowClass_right_integral _ δ
        _ = bottomRowClass F (a y.1) := bottomRowClass_right_integral _ _
        _ = y.1 := ha y.1
    have hclassOut := (bottomRowClass_eq_iff_integral_orbit _ _).2 ⟨1, by simpa using hq⟩
    have hC : x.1 = y.1 := by
      calc
        x.1 = bottomRowClass F
            ((a x.1 * toSLF F (rep x.2)) * toSLF F (γ : SL(2,𝓞 F))) := hxi.symm
        _ = bottomRowClass F
            ((a y.1 * toSLF F (rep y.2)) * toSLF F (δ : SL(2,𝓞 F))) := hclassOut
        _ = y.1 := hyi
    have hmove :
        Quotient.mk (QuotientGroup.rightRel (borelSL F))
            (a x.1 * toSLF F (rep x.2)) =
          Quotient.mk (QuotientGroup.rightRel (borelSL F))
            ((a y.1 * toSLF F (rep y.2)) * toSLF F (δ * γ⁻¹ : SL(2,𝓞 F))) := by
      have hm := quotient_right_mul_congr
        ((a x.1 * toSLF F (rep x.2)) * toSLF F (γ : SL(2,𝓞 F)))
        ((a y.1 * toSLF F (rep y.2)) * toSLF F (δ : SL(2,𝓞 F)))
        (toSLF F ((γ⁻¹ : Γ) : SL(2,𝓞 F))) hq
      simpa [map_mul, mul_assoc] using hm
    have hOrbit : cuspOrbitSetoid Γ (a x.1) rep x.2 y.2 := by
      refine ⟨δ * γ⁻¹, ?_⟩
      simpa [hC, map_mul, mul_assoc] using hmove
    have hidxRel : (cuspIndexSetoid Γ a rep).r x y := ⟨hC, hOrbit⟩
    have hidx : Quotient.mk (cuspIndexSetoid Γ a rep) x =
        Quotient.mk (cuspIndexSetoid Γ a rep) y := Quotient.sound hidxRel
    have hij : i = j := by
      dsimp [x, y] at hidx
      rw [← hindexRep i, ← hindexRep j]
      exact hidx
    cases hij
    have hq' : Quotient.mk (QuotientGroup.rightRel (borelSL F))
        ((σ i)⁻¹ * toSLF F (γ : SL(2,𝓞 F))) =
      Quotient.mk (QuotientGroup.rightRel (borelSL F))
        ((σ i)⁻¹ * toSLF F (δ : SL(2,𝓞 F))) := by
      simpa [f] using hp
    have hrelB : (σ i)⁻¹ * toSLF F (δ : SL(2,𝓞 F)) *
        ((σ i)⁻¹ * toSLF F (γ : SL(2,𝓞 F)))⁻¹ ∈ borelSL F :=
      QuotientGroup.rightRel_apply.mp (Quotient.exact hq')
    have hconj : (σ i)⁻¹ * toSLF F (δ * γ⁻¹ : SL(2,𝓞 F)) * (σ i) ∈ borelSL F := by
      simpa [map_mul, map_inv, _root_.mul_inv_rev, mul_assoc] using hrelB
    have hstab : δ * γ⁻¹ ∈ cuspStab F Γ (σ i) :=
      (mem_cuspStab_iff Γ (σ i) (δ * γ⁻¹)).mpr hconj
    have hcd : c = d := by
      rw [← Quotient.out_eq' c, ← Quotient.out_eq' d]
      apply Quotient.sound
      exact QuotientGroup.rightRel_apply.mpr hstab
    exact congrArg (Sigma.mk i) hcd
  exact ⟨hinj, hsurj⟩

private lemma bottomRowFractionalIdeal_right_le (g : SL(2,F))
    (γ : SL(2,𝓞 F)) :
    bottomRowFractionalIdeal F (g * toSLF F γ) ≤ bottomRowFractionalIdeal F g := by
  change (bottomRowFractionalIdeal F (g * toSLF F γ) : Submodule (𝓞 F) F) ≤
    (bottomRowFractionalIdeal F g : Submodule (𝓞 F) F)
  rw [bottomRowFractionalIdeal_coe, bottomRowFractionalIdeal_coe]
  apply Submodule.span_le.mpr
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  have hrow₀ : (g * toSLF F γ) 1 0 =
      g 1 0 * algebraMap (𝓞 F) F (γ 0 0) +
        g 1 1 * algebraMap (𝓞 F) F (γ 1 0) := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    simp [Matrix.mul_apply, Fin.sum_univ_two, toSLF]
  have hrow₁ : (g * toSLF F γ) 1 1 =
      g 1 0 * algebraMap (𝓞 F) F (γ 0 1) +
        g 1 1 * algebraMap (𝓞 F) F (γ 1 1) := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    simp [Matrix.mul_apply, Fin.sum_univ_two, toSLF]
  have hc : g 1 0 ∈ Submodule.span (𝓞 F) {g 1 0, g 1 1} :=
    Submodule.subset_span (by simp)
  have hd : g 1 1 ∈ Submodule.span (𝓞 F) {g 1 0, g 1 1} :=
    Submodule.subset_span (by simp)
  have hca : g 1 0 * algebraMap (𝓞 F) F (γ 0 0) ∈
      Submodule.span (𝓞 F) {g 1 0, g 1 1} := by
    simpa [Algebra.smul_def, mul_comm] using
      (Submodule.smul_mem (Submodule.span (𝓞 F) {g 1 0, g 1 1}) (γ 0 0) hc)
  have hdb : g 1 1 * algebraMap (𝓞 F) F (γ 1 0) ∈
      Submodule.span (𝓞 F) {g 1 0, g 1 1} := by
    simpa [Algebra.smul_def, mul_comm] using
      (Submodule.smul_mem (Submodule.span (𝓞 F) {g 1 0, g 1 1}) (γ 1 0) hd)
  have hca' : g 1 0 * algebraMap (𝓞 F) F (γ 0 1) ∈
      Submodule.span (𝓞 F) {g 1 0, g 1 1} := by
    simpa [Algebra.smul_def, mul_comm] using
      (Submodule.smul_mem (Submodule.span (𝓞 F) {g 1 0, g 1 1}) (γ 0 1) hc)
  have hdb' : g 1 1 * algebraMap (𝓞 F) F (γ 1 1) ∈
      Submodule.span (𝓞 F) {g 1 0, g 1 1} := by
    simpa [Algebra.smul_def, mul_comm] using
      (Submodule.smul_mem (Submodule.span (𝓞 F) {g 1 0, g 1 1}) (γ 1 1) hd)
  rcases hx with hx | hx
  · rw [hx, hrow₀]
    exact Submodule.add_mem _ hca hdb
  · rw [hx, hrow₁]
    exact Submodule.add_mem _ hca' hdb'

private lemma bottomRowFractionalIdeal_right (g : SL(2,F))
    (γ : SL(2,𝓞 F)) :
    bottomRowFractionalIdeal F (g * toSLF F γ) = bottomRowFractionalIdeal F g := by
  apply le_antisymm (bottomRowFractionalIdeal_right_le g γ)
  have hmul : (g * toSLF F γ) * toSLF F γ⁻¹ = g := by simp [mul_assoc]
  have h := bottomRowFractionalIdeal_right_le (g * toSLF F γ) γ⁻¹
  rw [hmul] at h
  exact h

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
  exact ⟨exists_cusp_reps_bijective Γ,
    bottomRowFractionalIdeal_ne_zero,
    bottomRowClass_surjective,
    bottomRowClass_eq_iff_integral_orbit⟩

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
  have hFormula := (G2_x_action (F := F)).1
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
