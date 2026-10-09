import ArtinPrimitiveRoots.TypeII.Rough
import ArtinPrimitiveRoots.Construction.Proofs.c1.SupportHelpers

namespace ArtinPrimitiveRoots.Proofs.c_typeii_sol

open Classical Filter
open ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.Rough
open ArtinPrimitiveRoots.Construction

/-- Product character on a common modulus, with the usual zero extension on nonunits. -/
noncomputable def productCharacter {M k : ℕ}
    (χM : DirichletCharacter ℂ M) (χk : DirichletCharacter ℂ k) :
    DirichletCharacter ℂ (M * k) :=
  χM.changeLevel (Nat.dvd_mul_right M k) *
    χk.changeLevel (Nat.dvd_mul_left k M)

private theorem productCharacter_natCast {M k : ℕ}
    (χM : DirichletCharacter ℂ M) (χk : DirichletCharacter ℂ k) (m : ℕ) :
    productCharacter χM χk (m : ZMod (M * k)) =
      χM (m : ZMod M) * χk (m : ZMod k) := by
  by_cases hcop : Nat.Coprime m (M * k)
  · have hunit : (ZMod.unitOfCoprime m hcop : ZMod (M * k)) = m :=
      ZMod.coe_unitOfCoprime m hcop
    rw [← hunit, productCharacter, MulChar.mul_apply,
      DirichletCharacter.changeLevel_eq_cast_of_dvd,
      DirichletCharacter.changeLevel_eq_cast_of_dvd, hunit]
    simp only [ZMod.cast_natCast (Nat.dvd_mul_right M k),
      ZMod.cast_natCast (Nat.dvd_mul_left k M)]
  · have hzero : productCharacter χM χk (m : ZMod (M * k)) = 0 :=
      (productCharacter χM χk).map_nonunit
        (by simpa only [ZMod.isUnit_iff_coprime] using hcop)
    rw [hzero]
    by_cases hM : Nat.Coprime m M
    · have hk : ¬ Nat.Coprime m k := fun hk => hcop (hM.mul_right hk)
      rw [χk.map_nonunit (by simpa only [ZMod.isUnit_iff_coprime] using hk), mul_zero]
    · rw [χM.map_nonunit (by simpa only [ZMod.isUnit_iff_coprime] using hM), zero_mul]

/-- A bounded natural interval is empty or has finite endpoints, and the two sum domains agree. -/
private theorem natural_interval_endpoints (H : ℝ) (I : Set ℕ)
    (hI : IsNatInterval I)
    (hbox : I ⊆ {m : ℕ | H ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * H}) :
    ((dyadicIntegers H).filter (fun m => m ∈ I) = ∅) ∨
      ∃ l r : ℕ, H ≤ (l : ℝ) ∧ l ≤ r ∧ (r : ℝ) ≤ 2 * H ∧
        (dyadicIntegers H).filter (fun m => m ∈ I) =
          (Finset.range (⌊(r : ℝ)⌋₊ + 1)).filter
            (fun m : ℕ => (l : ℝ) ≤ (m : ℝ) ∧ (m : ℝ) ≤ (r : ℝ)) := by
  let S := (dyadicIntegers H).filter (fun m => m ∈ I)
  have hmem (m : ℕ) : m ∈ S ↔ m ∈ I := by
    constructor
    · exact fun hm => (Finset.mem_filter.mp hm).2
    · intro hm
      exact Finset.mem_filter.mpr
        ⟨mem_dyadicIntegers_of_bounds (hbox hm).1 (hbox hm).2, hm⟩
  rcases S.eq_empty_or_nonempty with hS | hS
  · exact Or.inl hS
  · right
    let l := S.min' hS
    let r := S.max' hS
    have hl : l ∈ I := (hmem l).mp (S.min'_mem hS)
    have hr : r ∈ I := (hmem r).mp (S.max'_mem hS)
    have hlr : l ≤ r := S.min'_le_max' hS
    refine ⟨l, r, (hbox hl).1, hlr, (hbox hr).2, ?_⟩
    change S = _
    ext m
    have hinterval : m ∈ S ↔ l ≤ m ∧ m ≤ r := by
      constructor
      · intro hm
        exact ⟨S.min'_le m hm, S.le_max' m hm⟩
      · rintro ⟨hlm, hmr⟩
        apply (hmem m).mpr
        apply hI hl hr
        · simpa only [min_eq_left hlr] using hlm
        · simpa only [max_eq_right hlr] using hmr
    rw [hinterval]
    simp only [Nat.floor_natCast, Finset.mem_filter, Finset.mem_range,
      Nat.cast_le]
    omega

/-- Common long-cancellation constants for every first-variable character twist. -/
theorem twisted_rough_long_cancellation
    (δ γ sMin sMax c₂ : ℝ) (M : ℕ)
    (hδ : 0 < δ) (hγ : 0 < γ) (hγs : γ < sMin)
    (hs : sMin < sMax) (hsMax : sMax < 1) (hc₂ : 0 < c₂) (hM : 0 < M) :
    ∀ A₀ B A : ℝ, 0 < A₀ → 0 < B → 0 < A →
      ∃ C₀ x₀ : ℝ, 0 < C₀ ∧ 2 ≤ x₀ ∧
        ∀ x : ℝ, x₀ ≤ x → ∀ Hm Hn : ℝ,
          Real.rpow x δ ≤ Hm → Real.rpow x δ ≤ Hn → Hm * Hn ≤ c₂ * x →
          Real.log Hm / Real.log x ∈ Set.Icc sMin sMax →
          Real.log (2 * Hm) / Real.log x ∈ Set.Icc sMin sMax →
          ∀ I : Set ℕ, IsNatInterval I →
            I ⊆ {m : ℕ | Hm ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * Hm} →
            ∀ v : ℝ, |v| ≤ Real.log x → ∀ χM : DirichletCharacter ℂ M,
              ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.rpow (Real.log x) A₀ →
                ∀ χk : DirichletCharacter ℂ k, ∀ t : ℝ,
                  |t| ≤ 2 * (Hm * Hn) * Real.rpow (Real.log x) B →
                    ‖∑ m ∈ (dyadicIntegers Hm).filter (fun m => m ∈ I),
                      (roughCoefficient x γ v m * χM (m : ZMod M)) *
                        χk (m : ZMod k) *
                          Complex.exp (Complex.I * t * Real.log (m : ℝ))‖ / Hm ≤
                      C₀ * Real.rpow (Real.log x) (-A) := by
  intro A₀ B A hA₀ hB hA
  let σ : ℝ := min δ (1 - sMax) / 2
  have hmin : 0 < min δ (1 - sMax) := lt_min hδ (by linarith)
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hσδ : σ ≤ δ := by
    dsimp [σ]
    nlinarith [min_le_left δ (1 - sMax)]
  have hσs : σ ≤ 1 - sMax := by
    dsimp [σ]
    nlinarith [min_le_right δ (1 - sMax)]
  let E : ℝ := max 2 (A₀ + 1)
  have hE : 0 < E := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  obtain ⟨B₂, CHigh, xHigh, hB₂, hCHigh, hxHigh, hHigh⟩ :=
    high_frequency γ sMin sMax σ E A hγ hγs hs hsMax hσ hE hA
      (B + 1) (by linarith)
  obtain ⟨CLow, xLow, hCLow, hxLow, hLow⟩ :=
    low_frequency γ sMin sMax 2 δ hγ hγs hs hδ (by norm_num)
      (A₀ + 1) A B₂ (by linarith) hA hB₂
  have hev : ∀ᶠ x : ℝ in atTop,
      2 ≤ x ∧ xHigh ≤ x ∧ xLow ≤ x ∧
        1 ≤ Real.log x ∧ (M : ℝ) ≤ Real.log x ∧ c₂ ≤ Real.log x :=
    (eventually_ge_atTop 2).and ((eventually_ge_atTop xHigh).and
      ((eventually_ge_atTop xLow).and
        ((Real.tendsto_log_atTop.eventually_ge_atTop 1).and
          ((Real.tendsto_log_atTop.eventually_ge_atTop (M : ℝ)).and
            (Real.tendsto_log_atTop.eventually_ge_atTop c₂)))))
  obtain ⟨x₀, hx₀⟩ := hev.exists_forall_of_atTop
  refine ⟨CLow + CHigh, x₀, by positivity, (hx₀ x₀ le_rfl).1, ?_⟩
  intro x hx Hm Hn hm hn hprod hw₁ hw₂ I hI hbox v hv χM k hk hkbound χk t ht
  obtain ⟨hx2, hxH, hxL, hL, hML, hcL⟩ := hx₀ x hx
  have hxpos : 0 < x := by linarith
  have hxone : 1 ≤ x := by linarith
  have hlogpos : 0 < Real.log x := lt_of_lt_of_le zero_lt_one hL
  have hHm : 0 < Hm := lt_of_lt_of_le (Real.rpow_pos_of_pos hxpos δ) hm
  have hHmUpper : Hm ≤ Real.rpow x sMax :=
    (Real.le_rpow_iff_log_le hHm hxpos).mpr ((div_le_iff₀ hlogpos).mp hw₁.2)
  have hScaleM : Real.rpow x σ ≤ Hm :=
    (Real.rpow_le_rpow_of_exponent_le hxone hσδ).trans hm
  have hScaleN : Real.rpow x σ ≤ x / Hm := by
    calc
      _ ≤ Real.rpow x (1 - sMax) :=
        Real.rpow_le_rpow_of_exponent_le hxone hσs
      _ = x / Real.rpow x sMax := by
        change x ^ (1 - sMax) = x / x ^ sMax
        rw [Real.rpow_sub hxpos, Real.rpow_one]
      _ ≤ x / Hm := div_le_div_of_nonneg_left hxpos.le hHm hHmUpper
  have hScaleProd : Hm * (x / Hm) = x := by field_simp
  have hModulus : ((M * k : ℕ) : ℝ) ≤ Real.rpow (Real.log x) (A₀ + 1) := by
    push_cast
    calc
      (M : ℝ) * (k : ℝ) ≤ Real.log x * Real.rpow (Real.log x) A₀ :=
        mul_le_mul hML hkbound (by positivity) hlogpos.le
      _ = Real.rpow (Real.log x) (A₀ + 1) := by
        change Real.log x * (Real.log x) ^ A₀ = (Real.log x) ^ (A₀ + 1)
        rw [Real.rpow_add_one hlogpos.ne']
        ring
  have hModulusHigh : ((M * k : ℕ) : ℝ) ≤ Real.rpow (Real.log x) E :=
    hModulus.trans (Real.rpow_le_rpow_of_exponent_le hL (le_max_right _ _))
  have hMk : 1 ≤ M * k := Nat.mul_pos hM hk
  have hpowB : 0 ≤ Real.rpow (Real.log x) B := (Real.rpow_pos_of_pos hlogpos B).le
  have hpowA : 0 ≤ Real.rpow (Real.log x) (-A) :=
    (Real.rpow_pos_of_pos hlogpos (-A)).le
  have hvLow : |v| ≤ Real.rpow (Real.log x) 2 := by
    calc
      |v| ≤ Real.log x := hv
      _ = Real.rpow (Real.log x) 1 := (Real.rpow_one _).symm
      _ ≤ Real.rpow (Real.log x) 2 :=
        Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have hvHigh : |v| ≤ Real.rpow (Real.log x) E :=
    hvLow.trans (Real.rpow_le_rpow_of_exponent_le hL (le_max_left _ _))
  have htHigh : |t| ≤ 2 * x * Real.rpow (Real.log x) (B + 1) := by
    calc
      |t| ≤ 2 * (Hm * Hn) * Real.rpow (Real.log x) B := ht
      _ ≤ 2 * (c₂ * x) * Real.rpow (Real.log x) B :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hprod (by norm_num)) hpowB
      _ ≤ 2 * (Real.log x * x) * Real.rpow (Real.log x) B :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hcL hxpos.le) (by norm_num)) hpowB
      _ = 2 * x * Real.rpow (Real.log x) (B + 1) := by
        change 2 * (Real.log x * x) * (Real.log x) ^ B =
          2 * x * (Real.log x) ^ (B + 1)
        rw [Real.rpow_add_one hlogpos.ne']
        ring
  rcases natural_interval_endpoints Hm I hI hbox with hempty | ⟨l, r, hl, hlr, hr, hterms⟩
  · rw [hempty, Finset.sum_empty, norm_zero, zero_div]
    exact mul_nonneg (by linarith) hpowA
  · have hsum :
        (∑ m ∈ (dyadicIntegers Hm).filter (fun m => m ∈ I),
          (roughCoefficient x γ v m * χM (m : ZMod M)) * χk (m : ZMod k) *
            Complex.exp (Complex.I * t * Real.log (m : ℝ))) =
        ∑ m ∈ (Finset.range (⌊(r : ℝ)⌋₊ + 1)).filter
            (fun m : ℕ => (l : ℝ) ≤ (m : ℝ) ∧ (m : ℝ) ≤ (r : ℝ)),
          roughCoefficient x γ v m * productCharacter χM χk (m : ZMod (M * k)) *
            Complex.exp (Complex.I * t * Real.log (m : ℝ)) := by
      rw [hterms]
      apply Finset.sum_congr rfl
      intro m hm
      rw [productCharacter_natCast]
      ring
    rw [hsum]
    have hlrReal : (l : ℝ) ≤ (r : ℝ) := by exact_mod_cast hlr
    by_cases htLow : |t| ≤ Real.rpow (Real.log x) B₂
    · have hbound := hLow x hxL Hm hm hw₁ (l : ℝ) (r : ℝ) hl hlrReal hr
        v t hvLow htLow (M * k) hMk hModulus (productCharacter χM χk)
      have hnorm := hbound
      simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hHm] at hnorm
      exact hnorm.trans (mul_le_mul_of_nonneg_right (by linarith) hpowA)
    · have hbound := hHigh x hxH Hm (x / Hm) hScaleM hScaleN
        (by rw [hScaleProd]; linarith) (by rw [hScaleProd]; linarith)
        hw₁ hw₂ (M * k) hMk hModulusHigh (productCharacter χM χk) v t
        (le_of_lt (lt_of_not_ge htLow))
        (by simpa only [hScaleProd] using htHigh) hvHigh
        (l : ℝ) (r : ℝ) hl hlrReal hr
      have hnorm := hbound
      simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hHm] at hnorm
      exact hnorm.trans (mul_le_mul_of_nonneg_right (by linarith) hpowA)

end ArtinPrimitiveRoots.Proofs.c_typeii_sol
