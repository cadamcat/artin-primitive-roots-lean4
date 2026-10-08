import ArtinPrimitiveRoots.Proofs.qs_c_p.C3Helpers

/-! Uniform scaled transform sum for the original transition term. -/

set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain ClassFieldTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.qs_c3_sol

open ArtinPrimitiveRoots.A2

set_option maxHeartbeats 1000000 in
/-- On the original transition range, the scaled transform sum costs at most
four powers of the cutoff ratio, uniformly in the scale. -/
theorem orig_transition_tsum_bound {K : Type} [Field K] [NumberField K]
    [IsTotallyComplex K] (W : ℝ → ℝ) (hW : IsCapWeight W) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ X : ℝ), 1 ≤ Λ → 1 / Λ ≤ X →
      ‖∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
        qsTransform K (fun y => (W (y ^ 2) : ℂ)) (X * qsN b.1)‖ ≤ C * Λ ^ 4 := by
  classical
  let h : ℝ → ℂ := fun y => (W (y ^ 2) : ℂ)
  have hh : IsQSWeight h := by
    rcases hW.1 with ⟨hcont, hsupport, hnear⟩
    refine ⟨hcont.comp (contDiff_id.pow 2), ?_, ?_⟩
    · refine ⟨Real.sqrt (5 / 2), fun y hy => ?_⟩
      have hy0 : 0 ≤ y := le_trans (Real.sqrt_nonneg _) hy
      have hsquare : (5 / 2 : ℝ) ≤ y ^ 2 := by
        have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5 / 2)
        calc
          5 / 2 = Real.sqrt (5 / 2) ^ 2 := hs.symm
          _ ≤ y ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hy 2
      simp only [h, hW.2.2.2 (y ^ 2) hsquare, Complex.ofReal_zero]
    · obtain ⟨δ, hδ, hconst⟩ := hnear
      refine ⟨Real.sqrt δ, Real.sqrt_pos.2 hδ, ?_⟩
      intro y hy
      have hs := Real.sq_sqrt hδ.le
      have hsquare : y ^ 2 ≤ δ := by
        calc
          y ^ 2 ≤ Real.sqrt δ ^ 2 := pow_le_pow_left₀ hy.1 hy.2 2
          _ = δ := hs
      have hy2 : y ^ 2 ∈ Set.Icc (0 : ℝ) δ := ⟨sq_nonneg _, hsquare⟩
      simpa only [h, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hconst (y ^ 2) hy2
  obtain ⟨C₀, hC₀, hRaw⟩ := (qs_transform_bounds_P0 (K := K) h hh 4 0 1 (by norm_num)).2
  have hdecay : ∀ x : ℝ, 0 < x →
      (x ≤ 1 → ‖iteratedDeriv 0 (qsTransform K h) x‖ ≤ C₀ * x ^ (-1 : ℝ)) ∧
      (1 ≤ x → ‖iteratedDeriv 0 (qsTransform K h) x‖ ≤ C₀ * x ^ (-4 : ℝ)) := by
    intro x hx
    simpa using hRaw x hx
  have hbase₀ : Summable (fun I : Ideal (𝓞 K) =>
      ArtinPrimitiveRoots.Hecke.idealNormRpowTerm 2 I) :=
    ArtinPrimitiveRoots.Hecke.summable_idealNormRpow (K := K) (by norm_num)
  have hbase : Summable (fun b : {I : Ideal (𝓞 K) // I ≠ ⊥} =>
      ArtinPrimitiveRoots.Hecke.idealNormRpowTerm 2 b.1) :=
    hbase₀.subtype (fun I => I ≠ ⊥)
  let S : ℝ := ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
    ArtinPrimitiveRoots.Hecke.idealNormRpowTerm 2 b.1
  have hS : 0 ≤ S := by
    apply tsum_nonneg
    intro b
    simp only [ArtinPrimitiveRoots.Hecke.idealNormRpowTerm]
    split_ifs <;> positivity
  refine ⟨C₀ * S + 1, by positivity, ?_⟩
  intro Λ X hΛ hX
  have hpoint : ∀ b : {I : Ideal (𝓞 K) // I ≠ ⊥},
      ‖qsTransform K h (X * qsN b.1)‖ ≤
        C₀ * Λ ^ 4 * ArtinPrimitiveRoots.Hecke.idealNormRpowTerm 2 b.1 := by
    have hΛpos : 0 < Λ := by linarith
    have hXpos : 0 < X := lt_of_lt_of_le (one_div_pos.mpr hΛpos) hX
    intro b
    let N : ℝ := qsN b.1
    have hNpos : 0 < N := by
      dsimp [N, qsN]
      have hnat : 0 < Ideal.absNorm b.1 := Nat.pos_iff_ne_zero.mpr (by
        intro hz
        exact b.2 (Ideal.absNorm_eq_zero_iff.mp hz))
      exact_mod_cast hnat
    have hN1 : 1 ≤ N := by
      dsimp [N, qsN]
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by
        intro hz
        exact b.2 (Ideal.absNorm_eq_zero_iff.mp hz))
    have hxpos : 0 < X * N := mul_pos hXpos hNpos
    have hlow : N / Λ ≤ X * N := by
      have hh := mul_le_mul_of_nonneg_right hX (le_of_lt hNpos)
      simpa [div_eq_mul_inv, mul_comm] using hh
    have hsmall (hx : X * N ≤ 1) :
        ‖qsTransform K h (X * N)‖ ≤ C₀ * (X * N) ^ (-1 : ℝ) := by
      have hb := (hdecay (X * N) hxpos).1 hx
      simpa [iteratedDeriv_zero] using hb
    have hlarge (hx : 1 ≤ X * N) :
        ‖qsTransform K h (X * N)‖ ≤ C₀ * (X * N) ^ (-4 : ℝ) := by
      have hb := (hdecay (X * N) hxpos).2 hx
      simpa [iteratedDeriv_zero] using hb
    have htermEq : ArtinPrimitiveRoots.Hecke.idealNormRpowTerm 2 b.1 = N ^ (-2 : ℝ) := by
      simp [ArtinPrimitiveRoots.Hecke.idealNormRpowTerm, N, qsN,
        Ideal.absNorm_eq_zero_iff, b.2]
    by_cases hx : X * N ≤ 1
    · have hNΛ : N ≤ Λ := by
        have htmp : N / Λ ≤ 1 := le_trans hlow hx
        simpa using (div_le_iff₀ hΛpos).mp htmp
      have hinv : (X * N) ^ (-1 : ℝ) ≤ Λ / N := by
        have hmono := Real.rpow_le_rpow_of_nonpos (div_pos hNpos hΛpos) hlow
          (by norm_num : (-1 : ℝ) ≤ 0)
        have hEq : (N / Λ) ^ (-1 : ℝ) = Λ / N := by
          rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_one]
          field_simp
        exact hmono.trans_eq hEq
      have hlargePow : Λ / N ≤ Λ ^ 4 * N ^ (-2 : ℝ) := by
        have hNpow : N ^ (-2 : ℝ) = 1 / N ^ 2 := by
          rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hNpos.le]
          simp [one_div]
        rw [hNpow]
        have hΛ3 : Λ ≤ Λ ^ 3 := by
          calc
            Λ = Λ * 1 := by ring
            _ ≤ Λ * Λ ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith [hΛ]) hΛpos.le
            _ = Λ ^ 3 := by ring
        have hNΛ3 : N ≤ Λ ^ 3 := hNΛ.trans hΛ3
        have hcross : Λ * N ^ 2 ≤ Λ ^ 4 * N := by
          have hmul := mul_le_mul_of_nonneg_right hNΛ3
            (mul_nonneg hΛpos.le hNpos.le)
          nlinarith [hmul]
        have hfrac : Λ / N ≤ Λ ^ 4 / N ^ 2 :=
          (div_le_div_iff₀ hNpos (by positivity : 0 < N ^ 2)).2 hcross
        simpa [div_eq_mul_inv] using hfrac
      have hpoint : ‖qsTransform K h (X * N)‖ ≤ C₀ * (Λ / N) :=
        (hsmall hx).trans (mul_le_mul_of_nonneg_left hinv hC₀.le)
      calc
        _ ≤ C₀ * (Λ / N) := hpoint
        _ ≤ C₀ * (Λ ^ 4 * N ^ (-2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hlargePow hC₀.le
        _ = C₀ * Λ ^ 4 * ArtinPrimitiveRoots.Hecke.idealNormRpowTerm 2 b.1 := by
          rw [← htermEq]
          ring
    · have hx' : 1 ≤ X * N := le_of_not_ge hx
      have hlowInv : (X * N) ^ (-4 : ℝ) ≤ (N / Λ) ^ (-4 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (div_pos hNpos hΛpos) hlow
          (by norm_num : (-4 : ℝ) ≤ 0)
      have hscale : (N / Λ) ^ (-4 : ℝ) = Λ ^ 4 * N ^ (-4 : ℝ) := by
        rw [show (-4 : ℝ) = -(4 : ℝ) by norm_num,
          Real.div_rpow hNpos.le hΛpos.le, Real.rpow_neg hNpos.le,
          Real.rpow_neg hΛpos.le]
        field_simp [hNpos.ne', hΛpos.ne']
        exact Real.rpow_natCast Λ 4
      have hNpow : N ^ (-4 : ℝ) ≤ N ^ (-2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      have hpoint : ‖qsTransform K h (X * N)‖ ≤ C₀ * (Λ ^ 4 * N ^ (-4 : ℝ)) := by
        calc
          _ ≤ C₀ * (X * N) ^ (-4 : ℝ) := hlarge hx'
          _ ≤ C₀ * (N / Λ) ^ (-4 : ℝ) :=
            mul_le_mul_of_nonneg_left hlowInv hC₀.le
          _ = C₀ * (Λ ^ 4 * N ^ (-4 : ℝ)) := by rw [hscale]
      calc
        _ ≤ C₀ * (Λ ^ 4 * N ^ (-4 : ℝ)) := hpoint
        _ ≤ C₀ * Λ ^ 4 * N ^ (-2 : ℝ) := by
          calc
            _ = (C₀ * Λ ^ 4) * N ^ (-4 : ℝ) := by ring
            _ ≤ (C₀ * Λ ^ 4) * N ^ (-2 : ℝ) :=
              mul_le_mul_of_nonneg_left hNpow (by positivity)
            _ = C₀ * Λ ^ 4 * N ^ (-2 : ℝ) := by ring
        _ = C₀ * Λ ^ 4 * ArtinPrimitiveRoots.Hecke.idealNormRpowTerm 2 b.1 := by
          rw [← htermEq]
  have hmajorSum : HasSum (fun b : {I : Ideal (𝓞 K) // I ≠ ⊥} =>
      (C₀ * Λ ^ 4) * ArtinPrimitiveRoots.Hecke.idealNormRpowTerm 2 b.1)
      ((C₀ * Λ ^ 4) * S) := hbase.hasSum.mul_left (C₀ * Λ ^ 4)
  have hsum := tsum_of_norm_bounded hmajorSum hpoint
  calc
    _ ≤ (C₀ * Λ ^ 4) * S := hsum
    _ = (C₀ * S) * Λ ^ 4 := by ring
    _ ≤ (C₀ * S + 1) * Λ ^ 4 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)

end ArtinPrimitiveRoots.Proofs.qs_c3_sol
