import ArtinPrimitiveRoots.Ext.SplittingInputs
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».ZeroDictionary
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false

open scoped NumberField Topology BigOperators
open NumberField IsDedekindDomain Complex Filter

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.s7sol_mellin

open ArtinPrimitiveRoots.Splitting ArtinPrimitiveRoots.Hecke
open ArtinPrimitiveRoots.Ext.SplittingInputs Classical

/-- Absolute Hadamard summability at 2 controls the inverse-square zero weights. -/
theorem zero_inverse_square_summable (K : Type*) [Field K] [NumberField K] :
    Summable (fun ρ : ℂ => if ρ ∈ nontrivialZeros K then
      (zeroMultiplicity K ρ : ℝ) / ‖ρ‖ ^ 2 else 0) := by
  have hspec := Classical.choose_spec (dedekind_completed K)
  have hxi : Differentiable ℂ (dedekindXi K) := hspec.1
  have hzero : dedekindXi K 0 ≠ 0 := (sharp_continuation K).2.2.2
  have hgrowth := dedekind_order_one K (dedekindXi K) hxi hspec.2.1
  obtain ⟨B, hHadamard⟩ := ext_hadamard_order_one (dedekindXi K) hxi hzero hgrowth
  have hdict := xi_zero_dictionary K
  have htwo : dedekindXi K 2 ≠ 0 := by
    intro h
    have hlt := ((hdict.1 2).mp h).2.1
    norm_num at hlt
  let H : ℂ → ℂ := fun ρ => if ρ ∈ nontrivialZeros K then
    (zeroMultiplicity K ρ : ℂ) * (((2 : ℂ) - ρ)⁻¹ + ρ⁻¹) else 0
  have hH : Summable H := by
    convert (hHadamard 2 htwo).1 using 1
    ext ρ
    by_cases hρ : ρ ∈ nontrivialZeros K
    · simp [H, hρ, (hdict.1 ρ).mpr hρ, hdict.2.1 ρ hρ]
    · have hnz : dedekindXi K ρ ≠ 0 := fun h => hρ ((hdict.1 ρ).mp h)
      simp [H, hρ, hnz]
  have hnb : {z : ℂ | dedekindXi K z ≠ 0} ∈ 𝓝 (0 : ℂ) := by
    exact hxi.continuous.continuousAt.preimage_mem_nhds
      (isOpen_compl_singleton.mem_nhds (by simpa using hzero))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnb
  have hgap (ρ : ℂ) (hρ : ρ ∈ nontrivialZeros K) : r ≤ ‖ρ‖ := by
    by_contra h
    have hmem : ρ ∈ Metric.ball 0 r := by
      simpa only [Metric.mem_ball, dist_zero_right] using lt_of_not_ge h
    exact (hball hmem) ((hdict.1 ρ).mpr hρ)
  let C : ℝ := 1 + 2 / r
  refine Summable.of_nonneg_of_le ?_ ?_ (hH.norm.mul_left (C / 2))
  · intro ρ
    split_ifs <;> positivity
  · intro ρ
    by_cases hρ : ρ ∈ nontrivialZeros K
    · have hnorm : 0 < ‖ρ‖ := hr.trans_le (hgap ρ hρ)
      have hρzero : ρ ≠ 0 := norm_pos_iff.mp hnorm
      have hdiff : (2 : ℂ) - ρ ≠ 0 := by
        intro h
        have heq : ρ = 2 := (sub_eq_zero.mp h).symm
        have hlt := hρ.2.1
        rw [heq] at hlt
        norm_num at hlt
      have hdiffnorm : 0 < ‖(2 : ℂ) - ρ‖ := norm_pos_iff.mpr hdiff
      have hcomb : ((2 : ℂ) - ρ)⁻¹ + ρ⁻¹ =
          (2 : ℂ) / (((2 : ℂ) - ρ) * ρ) := by
        field_simp [hρzero, hdiff] <;> ring
      have hcombNorm : ‖((2 : ℂ) - ρ)⁻¹ + ρ⁻¹‖ =
          2 / (‖(2 : ℂ) - ρ‖ * ‖ρ‖) := by
        rw [hcomb, norm_div, norm_mul, Complex.norm_two]
      have hratio : (2 : ℝ) ≤ (2 / r) * ‖ρ‖ := by
        have h := mul_le_mul_of_nonneg_left (hgap ρ hρ)
          (by positivity : 0 ≤ (2 : ℝ) / r)
        have heq : (2 / r) * r = (2 : ℝ) := by field_simp
        rwa [heq] at h
      have hlen : ‖(2 : ℂ) - ρ‖ ≤ C * ‖ρ‖ := by
        calc
          _ ≤ 2 + ‖ρ‖ := by simpa only [Complex.norm_two] using norm_sub_le (2 : ℂ) ρ
          _ ≤ C * ‖ρ‖ := by dsimp [C]; nlinarith
      have hden : ‖(2 : ℂ) - ρ‖ * ‖ρ‖ ≤ C * ‖ρ‖ ^ 2 := by
        calc
          _ ≤ (C * ‖ρ‖) * ‖ρ‖ := mul_le_mul_of_nonneg_right hlen hnorm.le
          _ = _ := by ring
      have hcompare : (1 : ℝ) / ‖ρ‖ ^ 2 ≤ C / (‖(2 : ℂ) - ρ‖ * ‖ρ‖) := by
        rw [div_le_div_iff₀ (sq_pos_of_pos hnorm) (mul_pos hdiffnorm hnorm)]
        simpa only [one_mul] using hden
      simp only [if_pos hρ]
      calc
        (zeroMultiplicity K ρ : ℝ) / ‖ρ‖ ^ 2 =
            (zeroMultiplicity K ρ : ℝ) * (1 / ‖ρ‖ ^ 2) := by ring
        _ ≤ (zeroMultiplicity K ρ : ℝ) * (C / (‖(2 : ℂ) - ρ‖ * ‖ρ‖)) :=
          mul_le_mul_of_nonneg_left hcompare (Nat.cast_nonneg _)
        _ = C / 2 * ‖H ρ‖ := by
          simp only [H, if_pos hρ, norm_mul, Complex.norm_natCast, hcombNorm]
          ring
    · simp [H, hρ]

/-- The inverse-square zero sum bounds xi's logarithmic derivative away from its zeros. -/
theorem xi_logderiv_bound (K : Type*) [Field K] [NumberField K] :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : ℂ) (ε : ℝ), 0 < ε →
      (∀ ρ : ℂ, ρ ∈ nontrivialZeros K → ε ≤ ‖s - ρ‖) →
      ‖deriv (dedekindXi K) s / dedekindXi K s‖ ≤
        C * (1 + ‖s‖ * (1 + ‖s‖ / ε)) := by
  have hspec := Classical.choose_spec (dedekind_completed K)
  have hxi : Differentiable ℂ (dedekindXi K) := hspec.1
  have hzero : dedekindXi K 0 ≠ 0 := (sharp_continuation K).2.2.2
  have hgrowth := dedekind_order_one K (dedekindXi K) hxi hspec.2.1
  obtain ⟨B, hHadamard⟩ := ext_hadamard_order_one (dedekindXi K) hxi hzero hgrowth
  have hdict := xi_zero_dictionary K
  let w : ℂ → ℝ := fun ρ => if ρ ∈ nontrivialZeros K then
    (zeroMultiplicity K ρ : ℝ) / ‖ρ‖ ^ 2 else 0
  have hw : Summable w := zero_inverse_square_summable K
  have hnonneg (ρ : ℂ) : 0 ≤ w ρ := by
    dsimp [w]
    split_ifs <;> positivity
  let M : ℝ := ∑' ρ : ℂ, w ρ
  have hM : 0 ≤ M := tsum_nonneg hnonneg
  let C : ℝ := ‖B‖ + M + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro s ε hε hsep
  have hs : dedekindXi K s ≠ 0 := by
    intro hz
    have h := hsep s ((hdict.1 s).mp hz)
    simp only [sub_self, norm_zero] at h
    exact not_le_of_gt hε h
  let H : ℂ → ℂ := fun ρ => if dedekindXi K ρ = 0 then
    (analyticOrderNatAt (dedekindXi K) ρ : ℂ) * ((s - ρ)⁻¹ + ρ⁻¹) else 0
  have hH : Summable H := (hHadamard s hs).1
  have hformula : deriv (dedekindXi K) s / dedekindXi K s = B + ∑' ρ : ℂ, H ρ :=
    (hHadamard s hs).2
  let Q : ℝ := ‖s‖ * (1 + ‖s‖ / ε)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hterm (ρ : ℂ) : ‖H ρ‖ ≤ Q * w ρ := by
    by_cases hρ : ρ ∈ nontrivialZeros K
    · have hz : dedekindXi K ρ = 0 := (hdict.1 ρ).mpr hρ
      have hρzero : ρ ≠ 0 := by
        intro h
        have hpos := hρ.1
        rw [h] at hpos
        norm_num at hpos
      have hR : 0 < ‖ρ‖ := norm_pos_iff.mpr hρzero
      have hD : 0 < ‖s - ρ‖ := hε.trans_le (hsep ρ hρ)
      have hdiff : s - ρ ≠ 0 := norm_pos_iff.mp hD
      have hcomb : (s - ρ)⁻¹ + ρ⁻¹ = s / ((s - ρ) * ρ) := by
        field_simp [hρzero, hdiff] <;> ring
      have hcombNorm : ‖(s - ρ)⁻¹ + ρ⁻¹‖ = ‖s‖ / (‖s - ρ‖ * ‖ρ‖) := by
        rw [hcomb, norm_div, norm_mul]
      have htri : ‖ρ‖ ≤ ‖s - ρ‖ + ‖s‖ := by
        calc
          ‖ρ‖ = ‖-(s - ρ) + s‖ := by congr 1; ring
          _ ≤ ‖-(s - ρ)‖ + ‖s‖ := norm_add_le _ _
          _ = _ := by rw [norm_neg]
      have hratio : ‖ρ‖ / ‖s - ρ‖ ≤ 1 + ‖s‖ / ε := by
        calc
          _ ≤ (‖s - ρ‖ + ‖s‖) / ‖s - ρ‖ := div_le_div_of_nonneg_right htri hD.le
          _ = 1 + ‖s‖ / ‖s - ρ‖ := by field_simp [hD.ne'] <;> ring
          _ ≤ 1 + ‖s‖ / ε := by
            have h := div_le_div_of_nonneg_left (norm_nonneg s) hε (hsep ρ hρ)
            linarith
      have hcombBound : ‖(s - ρ)⁻¹ + ρ⁻¹‖ ≤ Q / ‖ρ‖ ^ 2 := by
        calc
          _ = ‖s‖ / (‖s - ρ‖ * ‖ρ‖) := hcombNorm
          _ = ‖s‖ * (‖ρ‖ / ‖s - ρ‖) / ‖ρ‖ ^ 2 := by
            field_simp [hD.ne', hR.ne'] <;> ring
          _ ≤ ‖s‖ * (1 + ‖s‖ / ε) / ‖ρ‖ ^ 2 :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hratio (norm_nonneg s)) (sq_nonneg _)
          _ = Q / ‖ρ‖ ^ 2 := rfl
      calc
        ‖H ρ‖ = (zeroMultiplicity K ρ : ℝ) * ‖(s - ρ)⁻¹ + ρ⁻¹‖ := by
          simp only [H, if_pos hz, hdict.2.1 ρ hρ, norm_mul, Complex.norm_natCast]
        _ ≤ (zeroMultiplicity K ρ : ℝ) * (Q / ‖ρ‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hcombBound (Nat.cast_nonneg _)
        _ = Q * w ρ := by simp only [w, if_pos hρ]; ring
    · have hnz : dedekindXi K ρ ≠ 0 := fun h => hρ ((hdict.1 ρ).mp h)
      simp [H, w, hρ, hnz]
  have hnormsum : (∑' ρ : ℂ, ‖H ρ‖) ≤ Q * M := by
    calc
      _ ≤ ∑' ρ : ℂ, Q * w ρ := hH.norm.tsum_le_tsum hterm (hw.mul_left Q)
      _ = Q * M := hw.tsum_mul_left Q
  have hbound : ‖deriv (dedekindXi K) s / dedekindXi K s‖ ≤ ‖B‖ + Q * M := by
    calc
      _ = ‖B + ∑' ρ : ℂ, H ρ‖ := by rw [hformula]
      _ ≤ ‖B‖ + ‖∑' ρ : ℂ, H ρ‖ := norm_add_le _ _
      _ ≤ ‖B‖ + Q * M := by
        linarith [norm_tsum_le_tsum_norm hH.norm, hnormsum]
  have hCB : ‖B‖ ≤ C := by dsimp [C]; linarith
  have hCM : M ≤ C := by dsimp [C]; linarith [norm_nonneg B]
  calc
    _ ≤ ‖B‖ + Q * M := hbound
    _ ≤ C + Q * C := add_le_add hCB (mul_le_mul_of_nonneg_left hCM hQ)
    _ = C * (1 + ‖s‖ * (1 + ‖s‖ / ε)) := by dsimp [Q]; ring

end ArtinPrimitiveRoots.Proofs.s7sol_mellin
