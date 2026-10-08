import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.PadAbsoluteBounds

set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII Classical
noncomputable section

/-- The per-pair comparison absolute bound at a uniform Type II divisor second moment. -/
theorem comparisonPairSum_norm_le_secondMoment {K : ℕ} (F : PDFix K) (hF : F.Valid)
    (x Y R B : ℝ) (hY : 0 < Y) (hR : 0 ≤ R) (hL : 1 ≤ Real.log x) (hB : 0 ≤ B)
    (hBound : ∀ t : ℝ, |F.psi t| ≤ B) (hSupport : ∀ t : ℝ, F.psi t ≠ 0 → |t| ≤ R)
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂) (hMin : family.xMin ≤ x)
    (beta : ℕ → ℂ) (hbeta : ∀ n ∈ dyadicIntegers (family.Hn x), ‖beta n‖ ≤ Real.rpow (Real.log x) C)
    (hHm : 0 < family.Hm x) (hHn : 0 < family.Hn x)
    (hV : ∀ i : Fin K, 0 < bandMass x (F.a i))
    (κ Ct : ℝ)
    (hMoment : (∑ k ∈ Finset.range (⌊4 * (family.Hm x * family.Hn x)⌋₊ + 1), (tau k : ℝ) ^ 2) ≤
      Ct * (family.Hm x * family.Hn x) * Real.rpow (Real.log x) κ)
    (ta tb : Fin K → ℕ)
    (hηa : F.eta ((tupleProduct ta : ℝ) / Y) ≠ 0) (hηb : F.eta ((tupleProduct tb : ℝ) / Y) ≠ 0) :
    ‖comparisonPairSum F x Y family beta ta tb‖ ≤
      (∏ i : Fin K, (bandMass x (F.a i))⁻¹) ^ 2 *
        (32 * B * Real.rpow (Real.log x) (3 * F.A₀) / Y) *
        ((((⌈2 * R⌉₊ + 2 : ℕ) : ℝ)) * (Ct * (family.Hm x * family.Hn x) * Real.rpow (Real.log x) κ) *
          ((Real.rpow (Real.log x) C) ^ 2 * (Real.rpow (Real.log x) C) ^ 2)) := by
  let M := familyTerms family x
  let N := dyadicIntegers (family.Hn x)
  let X := family.Hm x * family.Hn x
  let Z := (Finset.range (⌊4 * X⌋₊ + 1)).filter fun k : ℕ => 1 ≤ k
  have hX : 0 < X := mul_pos hHm hHn
  have hM (m : ℕ) (hm : m ∈ M) : 0 < m ∧ (m : ℝ) ≤ 2 * family.Hm x := by
    have hb := family.interval_bounds x hMin m (Finset.mem_filter.mp hm).2
    exact ⟨by exact_mod_cast hHm.trans_le hb.1, hb.2⟩
  have hN (n : ℕ) (hn : n ∈ N) : 0 < n ∧ (n : ℝ) ≤ 2 * family.Hn x := by
    have hb := (Finset.mem_filter.mp hn).2
    exact ⟨by exact_mod_cast hHn.trans_le hb.1, hb.2⟩
  have hZpos (k : ℕ) (hk : k ∈ Z) : 0 < k := by
    have hb := (Finset.mem_filter.mp hk).2
    omega
  have hprod (m : ℕ) (hm : m ∈ M) (n : ℕ) (hn : n ∈ N) : m * n ∈ Z := by
    have hpos := Nat.mul_pos (hM m hm).1 (hN n hn).1
    have hmul := mul_le_mul (hM m hm).2 (hN n hn).2 (Nat.cast_nonneg (α := ℝ) n) (by positivity)
    have hhi : ((m * n : ℕ) : ℝ) ≤ 4 * X := by
      push_cast
      dsimp only [X]
      nlinarith
    have hfloor : m * n ≤ ⌊4 * X⌋₊ := (Nat.le_floor_iff (by positivity)).mpr hhi
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hfloor), Nat.succ_le_of_lt hpos⟩
  have hMomentZ : (∑ k ∈ Z, (tau k : ℝ) ^ 2) ≤ Ct * X * Real.rpow (Real.log x) κ := by
    apply le_trans _ hMoment
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun k hk hn => sq_nonneg _)
  have hDegree : 0 ≤ (((⌈2 * R⌉₊ + 2 : ℕ) : ℝ)) := Nat.cast_nonneg _
  have hDiv := mul_le_mul_of_nonneg_left hMomentZ hDegree
  have hα (m : ℕ) (hm : m ∈ M) : ‖family.alpha x m‖ ≤ Real.rpow (Real.log x) C :=
    family.coefficient_bound x hMin m (Finset.mem_filter.mp hm).2
  have hβ (n : ℕ) (hn : n ∈ N) : ‖beta n‖ ≤ Real.rpow (Real.log x) C := hbeta n hn
  have hPow : 0 ≤ Real.rpow (Real.log x) C := Real.rpow_nonneg (by linarith [hL]) _
  have haBounds := hF.2.2.2.2.1.2.1 hηa
  have hbBounds := hF.2.2.2.2.1.2.1 hηb
  have haLo : Y ≤ (tupleProduct ta : ℝ) := by simpa only [one_mul] using (le_div_iff₀ hY).mp haBounds.1
  have hbLo : Y ≤ (tupleProduct tb : ℝ) := by simpa only [one_mul] using (le_div_iff₀ hY).mp hbBounds.1
  have hquad := comparisonQuad_norm_sum_bound M N Z (tupleProduct ta) (tupleProduct tb) Y R
    ((((⌈2 * R⌉₊ + 2 : ℕ) : ℝ)) * (Ct * X * Real.rpow (Real.log x) κ))
    (Real.rpow (Real.log x) C) (Real.rpow (Real.log x) C)
    hY hR haLo hbLo hZpos hprod (family.alpha x) beta hPow hPow hα hβ hDiv
  have hquad' : (∑ q ∈ comparisonQuads M N (tupleProduct ta) (tupleProduct tb) Y R,
      ‖coefficientQuadProduct family x beta q‖) ≤
      ((((⌈2 * R⌉₊ + 2 : ℕ) : ℝ)) * (Ct * X * Real.rpow (Real.log x) κ)) *
        ((Real.rpow (Real.log x) C) ^ 2 * (Real.rpow (Real.log x) C) ^ 2) := by
    simpa only [coefficientQuadProduct] using hquad
  have hNorm := comparisonPairSum_norm_le F hF x Y R B hY hL hB hBound hSupport family beta ta tb hV
  apply hNorm.trans
  have hA₀pow : 0 ≤ Real.rpow (Real.log x) (3 * F.A₀) := Real.rpow_nonneg (by linarith [hL]) _
  exact mul_le_mul_of_nonneg_left hquad' (by positivity)

end
end ArtinPrimitiveRoots.TypeII.PD
