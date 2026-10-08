import /- Local package with a hyphenated directory name. -/ ArtinPrimitiveRoots.A2.Proofs.«A2-BRIDGES».COUNT

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A2
open ArtinPrimitiveRoots A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

private lemma bridge_prime_norm_pos (v : FinPlace F) :
    0 < idealNorm v.asIdeal := by
  change 0 < (Ideal.absNorm v.asIdeal : ℝ)
  have hN : 0 < Ideal.absNorm v.asIdeal :=
    Ideal.absNorm_pos_of_nonZeroDivisors
      ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩
  exact_mod_cast hN

private lemma bridge_prime_norm_ge_one (v : FinPlace F) :
    1 ≤ idealNorm v.asIdeal := by
  change 1 ≤ (Ideal.absNorm v.asIdeal : ℝ)
  have hN : 0 < Ideal.absNorm v.asIdeal :=
    Ideal.absNorm_pos_of_nonZeroDivisors
      ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩
  exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hN.ne')

private lemma bridge_finite_places_norm_le (Q : ℝ) (hQ : 0 ≤ Q) :
    {v : FinPlace F | idealNorm v.asIdeal ≤ Q}.Finite := by
  apply Set.Finite.of_injOn (f := fun v : FinPlace F => v.asIdeal)
    (s := {v : FinPlace F | idealNorm v.asIdeal ≤ Q})
    (t := {I : Ideal (𝓞 F) | Ideal.absNorm I ≤ ⌊Q⌋₊}) ?_ ?_
    (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊Q⌋₊)
  · intro v hv
    change Ideal.absNorm v.asIdeal ≤ ⌊Q⌋₊
    exact (Nat.le_floor_iff hQ).mpr (by simpa [idealNorm] using hv)
  · intro v hv w hw h
    exact HeightOneSpectrum.ext h

/-- Uniform fixed-base product over any finite prime set.
Guide: sol-thin-a2rp/PROOFS.md:65–66. Uses COUNT_finite and ideal norm finiteness. -/
theorem a2_bridge_SMALL_PRIME (B : ℝ) (hB : 1 < B) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ T : Finset (FinPlace F),
      (∏ _v ∈ T, B) ≤ C * Real.rpow (∏ v ∈ T, idealNorm v.asIdeal) ε := by
  classical
  let Q : ℝ := Real.rpow B (ε⁻¹)
  have hBpos : 0 < B := by linarith
  have hQpos : 0 < Q := by
    dsimp [Q]
    exact Real.rpow_pos_of_pos hBpos _
  have hQpow : Real.rpow Q ε = B := by
    dsimp [Q]
    calc
      Real.rpow (Real.rpow B ε⁻¹) ε = Real.rpow B (ε⁻¹ * ε) :=
        (Real.rpow_mul hBpos.le _ _).symm
      _ = B := by rw [inv_mul_cancel₀ hε.ne']; exact Real.rpow_one B
  have hQnonneg : 0 ≤ Q := hQpos.le
  have hfinite := bridge_finite_places_norm_le (F := F) Q hQnonneg
  let P : Finset (FinPlace F) := hfinite.toFinset
  let C : ℝ := B ^ P.card
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    exact one_le_pow₀ (le_of_lt hB)
  · intro T
    let small : Finset (FinPlace F) := T.filter fun v => idealNorm v.asIdeal ≤ Q
    have hsmall_subset : small ⊆ P := by
      intro v hv
      have hv' : v ∈ T ∧ idealNorm v.asIdeal ≤ Q := Finset.mem_filter.mp hv
      change v ∈ hfinite.toFinset
      rw [Set.Finite.mem_toFinset]
      exact hv'.2
    have hsmall_card : small.card ≤ P.card := Finset.card_le_card hsmall_subset
    have hqpow_ge_one (v : FinPlace F) :
        1 ≤ Real.rpow (idealNorm v.asIdeal) ε :=
      Real.one_le_rpow (bridge_prime_norm_ge_one v) hε.le
    have hbig_bound (v : FinPlace F) (hv : ¬ idealNorm v.asIdeal ≤ Q) :
        B ≤ Real.rpow (idealNorm v.asIdeal) ε := by
      have hq : Q < idealNorm v.asIdeal := lt_of_not_ge hv
      have hlt := Real.rpow_lt_rpow hQpos.le hq hε
      exact (hQpow.symm.trans_lt hlt).le
    have hcoeff :
        (∏ v ∈ T, if idealNorm v.asIdeal ≤ Q then B else 1) ≤ C := by
      rw [← Finset.prod_filter]
      dsimp [small, C]
      rw [Finset.prod_const]
      exact pow_le_pow_right₀ hB.le hsmall_card
    have htermprod :
        (∏ v ∈ T, B) ≤
          (∏ v ∈ T, (if idealNorm v.asIdeal ≤ Q then B else 1) *
            Real.rpow (idealNorm v.asIdeal) ε) := by
      apply Finset.prod_le_prod₀
      · intro v hv
        exact le_of_lt (lt_trans (by norm_num) hB)
      · intro v hv
        by_cases hs : idealNorm v.asIdeal ≤ Q
        · calc
            B = B * 1 := (mul_one B).symm
            _ ≤ B * Real.rpow (idealNorm v.asIdeal) ε :=
              mul_le_mul_of_nonneg_left (hqpow_ge_one v)
                (le_of_lt (lt_trans (by norm_num) hB))
            _ = (if idealNorm v.asIdeal ≤ Q then B else 1) *
                Real.rpow (idealNorm v.asIdeal) ε := by simp [hs]
        · calc
            B ≤ Real.rpow (idealNorm v.asIdeal) ε := hbig_bound v hs
            _ = (if idealNorm v.asIdeal ≤ Q then B else 1) *
                Real.rpow (idealNorm v.asIdeal) ε := by simp [hs]
    calc
      (∏ v ∈ T, B) ≤
          (∏ v ∈ T, if idealNorm v.asIdeal ≤ Q then B else 1) *
            ∏ v ∈ T, Real.rpow (idealNorm v.asIdeal) ε := by
        calc
          _ ≤ (∏ v ∈ T, (if idealNorm v.asIdeal ≤ Q then B else 1) *
                Real.rpow (idealNorm v.asIdeal) ε) := htermprod
          _ = _ := by rw [Finset.prod_mul_distrib]
      _ ≤ C * ∏ v ∈ T, Real.rpow (idealNorm v.asIdeal) ε :=
        mul_le_mul_of_nonneg_right hcoeff (Finset.prod_nonneg fun v hv =>
          (Real.rpow_pos_of_pos (bridge_prime_norm_pos v) ε).le)
      _ = C * Real.rpow (∏ v ∈ T, idealNorm v.asIdeal) ε := by
        congr 1
        exact Real.finsetProd_rpow T (fun v => idealNorm v.asIdeal)
          (by intro v hv; exact (bridge_prime_norm_pos v).le) ε

/-- Uniform decaying-factor product; constants precede the growing prime set.
Guide: sol-thin-a2rp/PROOFS.md:65–66. Uses SMALL_PRIME and threshold splitting. -/
theorem a2_bridge_SMALL_PRIME_decay (B δ : ℝ) (hB : 0 ≤ B) (hδ : 0 < δ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ T : Finset (FinPlace F),
      (∏ v ∈ T, (1 + B * Real.rpow (idealNorm v.asIdeal) (-δ))) ≤
        C * Real.rpow (∏ v ∈ T, idealNorm v.asIdeal) ε := by
  classical
  let B' : ℝ := max 2 (1 + B)
  have hB' : 1 < B' := by
    dsimp [B']
    exact lt_of_lt_of_le (by norm_num) (le_max_left 2 (1 + B))
  obtain ⟨C, hC, hbound⟩ :=
    a2_bridge_SMALL_PRIME (F := F) B' hB' ε hε
  refine ⟨C, hC, ?_⟩
  intro T
  calc
    (∏ v ∈ T, (1 + B * Real.rpow (idealNorm v.asIdeal) (-δ))) ≤
        ∏ v ∈ T, B' := by
      apply Finset.prod_le_prod₀
      · intro v hv
        exact add_nonneg (by norm_num) (mul_nonneg hB
          (Real.rpow_nonneg (bridge_prime_norm_pos v).le _))
      · intro v hv
        have hq : 1 ≤ idealNorm v.asIdeal := bridge_prime_norm_ge_one v
        have hpow : 0 ≤ Real.rpow (idealNorm v.asIdeal) (-δ) :=
          Real.rpow_nonneg (bridge_prime_norm_pos v).le _
        have hpow_le : Real.rpow (idealNorm v.asIdeal) (-δ) ≤ 1 := by
          rw [← Real.one_rpow (-δ)]
          exact Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1) hq
            (by linarith)
        have hfactor : 1 + B * Real.rpow (idealNorm v.asIdeal) (-δ) ≤ 1 + B := by
          nlinarith [mul_nonneg hB hpow,
            mul_le_mul_of_nonneg_left hpow_le hB]
        exact le_trans hfactor (by
          dsimp [B']
          exact le_max_of_le_right le_rfl)
    _ ≤ C * Real.rpow (∏ v ∈ T, idealNorm v.asIdeal) ε := hbound T

end ArtinPrimitiveRoots.A2
