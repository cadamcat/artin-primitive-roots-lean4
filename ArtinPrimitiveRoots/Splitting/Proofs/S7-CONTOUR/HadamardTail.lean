import ArtinPrimitiveRoots.Ext.SplittingInputs
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».ZeroDictionary
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false

open scoped NumberField Topology
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

end ArtinPrimitiveRoots.Proofs.s7sol_mellin
