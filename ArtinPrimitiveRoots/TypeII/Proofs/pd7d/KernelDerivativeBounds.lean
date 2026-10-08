import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.ProductJet
import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.SeparationCutoff

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical
open ArtinPrimitiveRoots.TypeII
set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable def pd7dJetSum (n : ℕ) (C D : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (i.factorial : ℝ) * C * D ^ i

lemma pd7dJetSum_nonneg (n : ℕ) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    0 ≤ pd7dJetSum n C D := by
  unfold pd7dJetSum
  apply Finset.sum_nonneg
  intro i hi
  positivity

lemma pd7dJetSum_mul (n : ℕ) (C D B : ℝ) :
    pd7dJetSum n (C * B) D = pd7dJetSum n C D * B := by
  unfold pd7dJetSum
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma pd7d_scaled_kernel_derivative_bound (κ ψ : ℝ → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hκ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) κ)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hκsupp : Function.support κ ⊆ Set.Icc (1 / 2 : ℝ) 32)
    (hψsupp : Function.support ψ ⊆ Set.Icc (-R) R) (n : ℕ) :
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ X lam : ℝ, 1 ≤ X → ∀ u : PDPlane,
      ‖iteratedFDeriv ℝ n (pd7dScaledKernel κ ψ X lam) u‖ ≤ Cn * (1 + |lam|) ^ n := by
  let κc : ℝ → ℂ := fun y => (κ y : ℂ)
  let ψc : ℝ → ℂ := fun y => (ψ y : ℂ)
  have hκc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) κc := Complex.ofRealCLM.contDiff.comp hκ
  have hψc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψc := Complex.ofRealCLM.contDiff.comp hψ
  have hκcompact : HasCompactSupport κ :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hκsupp
  have hψcompact : HasCompactSupport ψ :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hψsupp
  have hκcCompact : HasCompactSupport κc := hκcompact.comp_left (g := Complex.ofReal) (by simp)
  have hψcCompact : HasCompactSupport ψc := hψcompact.comp_left (g := Complex.ofReal) (by simp)
  obtain ⟨Cκ, hCκ, hκbound⟩ := hκcCompact.exists_bound_iteratedFDeriv hκc n
  obtain ⟨Cψ, hCψ, hψbound⟩ := hψcCompact.exists_bound_iteratedFDeriv hψc n
  let Dg : ℝ := R + (n : ℝ) * 32 * 2 ^ n + 1
  have hDg1 : 1 ≤ Dg := by
    have hh : 0 ≤ (n : ℝ) * 32 * (2 : ℝ) ^ n := by positivity
    dsimp [Dg]
    linarith
  have hDg : 0 ≤ Dg := by linarith
  let K := pd7dJetSum n Cκ 64
  let P := pd7dJetSum n Cψ Dg
  let Cphase : ℝ := (2 * Real.pi + 1) ^ n
  let Ph := pd7dJetSum n Cphase Dg
  let A01 := (2 : ℝ) ^ n * K * K
  let A012 := (2 : ℝ) ^ n * A01 * P
  let Cbase := (2 : ℝ) ^ n * A012 * Ph
  let Cn := Cbase + 1
  have hK : 0 ≤ K := pd7dJetSum_nonneg n Cκ 64 hCκ (by norm_num)
  have hP : 0 ≤ P := pd7dJetSum_nonneg n Cψ Dg hCψ hDg
  have hCphase : 0 ≤ Cphase := by dsimp [Cphase]; positivity
  have hPh : 0 ≤ Ph := pd7dJetSum_nonneg n Cphase Dg hCphase hDg
  have hA01 : 0 ≤ A01 := by dsimp [A01]; positivity
  have hA012 : 0 ≤ A012 := by dsimp [A012]; positivity
  have hCbase : 0 ≤ Cbase := by dsimp [Cbase]; positivity
  have hCn : 0 < Cn := by dsimp [Cn]; linarith
  refine ⟨Cn, hCn, ?_⟩
  intro X lam hX u
  by_cases hu : u ∈ tsupport (pd7dScaledKernel κ ψ X lam)
  · obtain ⟨hgv, he₁, he₀⟩ := pd7d_scaled_kernel_tsupport_data κ ψ X lam R hκsupp hψsupp u hu
    let g := pd7dScaledDifference X
    let e₀ : PDPlane → ℝ := fun y => Real.exp (pd7dZLinear y)
    let e₁ : PDPlane → ℝ := fun y => Real.exp (pd7dDifferenceLinear X y)
    let f₀ := κc ∘ e₀
    let f₁ := κc ∘ e₁
    let fp := ψc ∘ g
    let phase := pd7dLinearPhase (Complex.I * ((2 * Real.pi * lam : ℝ) : ℂ))
    let fph := phase ∘ g
    have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g := pd7d_scaled_difference_contDiff X
    have he₀smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) e₀ := Real.contDiff_exp.comp pd7dZLinear.contDiff
    have he₁smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) e₁ := Real.contDiff_exp.comp (pd7dDifferenceLinear X).contDiff
    have hf₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f₀ := hκc.comp he₀smooth
    have hf₁ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f₁ := hκc.comp he₁smooth
    have hfp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fp := hψc.comp hg
    have hphase : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) phase := pd7dLinearPhase_contDiff _
    have hfph : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fph := hphase.comp hg
    have hgJet : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i g u‖ ≤ Dg ^ i := by
      intro i hi₁ hi₂
      have hgBound := pd7d_scaled_difference_derivative_norm_le X R 32 hX hR (by norm_num) u hgv he₁ i
      have hpow : (2 : ℝ) ^ i ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hi₂
      have hic : (i : ℝ) ≤ (n : ℝ) := by exact_mod_cast hi₂
      have hcoeff : (i : ℝ) * 32 * 2 ^ i ≤ (n : ℝ) * 32 * 2 ^ n := by gcongr
      have hpower : Dg ≤ Dg ^ i := by simpa only [pow_one] using pow_le_pow_right₀ hDg1 hi₁
      exact hgBound.trans ((by dsimp [Dg]; linarith : R + (i : ℝ) * 32 * 2 ^ i ≤ Dg).trans hpower)
    have he₀Jet : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i e₀ u‖ ≤ (64 : ℝ) ^ i := by
      intro i hi _
      have hh := pd7d_exp_linear_jet_bound pd7dZLinear u 2 32 (by norm_num) (by norm_num)
        (pd7dZLinear_norm_le.trans (by norm_num)) he₀ i hi
      simpa only [show (32 : ℝ) * 2 = 64 by norm_num] using hh
    have he₁Jet : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i e₁ u‖ ≤ (64 : ℝ) ^ i := by
      intro i hi _
      have hh := pd7d_exp_linear_jet_bound (pd7dDifferenceLinear X) u 2 32 (by norm_num)
        (by norm_num) (pd7dDifferenceLinear_norm_le X hX) he₁ i hi
      simpa only [show (32 : ℝ) * 2 = 64 by norm_num] using hh
    have hf₀Jet : ∀ i ≤ n, ‖iteratedFDeriv ℝ i f₀ u‖ ≤ K := by
      intro i hi
      exact pd7d_composition_jet_bound e₀ κc u Cκ 64 n i hi hCκ (by norm_num)
        he₀smooth hκc hκbound he₀Jet
    have hf₁Jet : ∀ i ≤ n, ‖iteratedFDeriv ℝ i f₁ u‖ ≤ K := by
      intro i hi
      exact pd7d_composition_jet_bound e₁ κc u Cκ 64 n i hi hCκ (by norm_num)
        he₁smooth hκc hκbound he₁Jet
    have hfpJet : ∀ i ≤ n, ‖iteratedFDeriv ℝ i fp u‖ ≤ P := by
      intro i hi
      exact pd7d_composition_jet_bound g ψc u Cψ Dg n i hi hCψ hDg hg hψc hψbound hgJet
    let Blam := 1 + |lam|
    have hBlam : 1 ≤ Blam := by dsimp [Blam]; linarith [abs_nonneg lam]
    have hBlam0 : 0 ≤ Blam := by linarith
    have hphaseOuter : ∀ i ≤ n, ∀ y, ‖iteratedFDeriv ℝ i phase y‖ ≤ Cphase * Blam ^ n := by
      intro i hi y
      rw [pd7d_phase_derivative_norm]
      have hbase : |2 * Real.pi * lam| ≤ (2 * Real.pi + 1) * Blam := by
        rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
        dsimp [Blam]
        nlinarith [Real.pi_pos, abs_nonneg lam]
      have hprodOne : 1 ≤ (2 * Real.pi + 1) * Blam := by nlinarith [Real.pi_pos]
      calc
        _ ≤ ((2 * Real.pi + 1) * Blam) ^ i := pow_le_pow_left₀ (abs_nonneg _) hbase i
        _ ≤ ((2 * Real.pi + 1) * Blam) ^ n := pow_le_pow_right₀ hprodOne hi
        _ = _ := by rw [mul_pow]
    have hfphJet : ∀ i ≤ n, ‖iteratedFDeriv ℝ i fph u‖ ≤ Ph * Blam ^ n := by
      intro i hi
      have hh := pd7d_composition_jet_bound g phase u (Cphase * Blam ^ n) Dg n i hi
        (by positivity) hDg hg hphase hphaseOuter hgJet
      rw [← pd7dJetSum, pd7dJetSum_mul] at hh
      exact hh
    have h01Jet : ∀ i ≤ n, ‖iteratedFDeriv ℝ i (fun y => f₀ y * f₁ y) u‖ ≤ A01 := by
      intro i hi
      exact pd7d_product_jet_bound f₀ f₁ u K K n i hi hK hK hf₀ hf₁ hf₀Jet hf₁Jet
    have h012Jet : ∀ i ≤ n, ‖iteratedFDeriv ℝ i (fun y => f₀ y * f₁ y * fp y) u‖ ≤ A012 := by
      intro i hi
      exact pd7d_product_jet_bound (fun y => f₀ y * f₁ y) fp u A01 P n i hi hA01 hP
        (hf₀.mul hf₁) hfp h01Jet hfpJet
    have hkernel : pd7dScaledKernel κ ψ X lam = fun y => f₀ y * f₁ y * fp y * fph y := by
      funext y
      dsimp [f₀, f₁, fp, fph, κc, ψc, e₀, e₁, g, phase, pd7dScaledKernel,
        additiveCharacter, pd7dLinearPhase]
      rw [pd7dZLinear_apply, pd7dDifferenceLinear_apply]
      congr 1
      congr 1
      push_cast
      ring
    rw [hkernel]
    have hlast := pd7d_product_jet_bound (fun y => f₀ y * f₁ y * fp y) fph u A012
      (Ph * Blam ^ n) n n le_rfl hA012 (by positivity) ((hf₀.mul hf₁).mul hfp) hfph
      h012Jet hfphJet
    calc
      _ ≤ (2 : ℝ) ^ n * A012 * (Ph * Blam ^ n) := hlast
      _ = Cbase * Blam ^ n := by dsimp [Cbase]; ring
      _ ≤ Cn * Blam ^ n := mul_le_mul_of_nonneg_right (by dsimp [Cn]; linarith) (pow_nonneg hBlam0 n)
  · have hz : iteratedFDeriv ℝ n (pd7dScaledKernel κ ψ X lam) u = 0 := by
      by_contra hne
      exact hu ((support_iteratedFDeriv_subset (𝕜 := ℝ) (f := pd7dScaledKernel κ ψ X lam) n) hne)
    rw [hz, norm_zero]
    positivity

end ArtinPrimitiveRoots.TypeII.PD
