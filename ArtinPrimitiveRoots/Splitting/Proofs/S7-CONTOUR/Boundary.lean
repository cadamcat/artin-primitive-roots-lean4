/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
The asymptotic contradiction adapts TauCeti.LSeries.ne_zero_of_threeFourOne.
-/
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».ThreeFourOne
import ArtinPrimitiveRoots.Proofs.s7_euler_b.SharpZeta
import Mathlib.Analysis.Complex.Asymptotics
import Mathlib.Analysis.Asymptotics.Lemmas

set_option autoImplicit false

open scoped NumberField Topology
open NumberField Complex Filter Asymptotics

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.s7sol_mellin

open ArtinPrimitiveRoots.Splitting

/-- The sharp Dedekind zeta function does not vanish on the line through its pole. -/
theorem sharp_ne_zero_on_one (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hRe : s.re = 1) (hs : s ≠ 1) : dedekindZetaSharp K s ≠ 0 := by
  have hsform : s = 1 + I * s.im := by
    conv_lhs => rw [← re_add_im s, hRe, ofReal_one, mul_comm]
  have ht : s.im ≠ 0 := by
    intro ht
    apply hs
    simpa [ht] using hsform
  have h₁ : DifferentiableAt ℂ (dedekindZetaSharp K) (1 + I * s.im) :=
    (dedekindZetaSharp_analyticAt_core K (by simp)
      (by rwa [← hsform])).differentiableAt
  have h₂ : ContinuousAt (dedekindZetaSharp K) (1 + 2 * I * s.im) :=
    (dedekindZetaSharp_analyticAt_core K (by simp) (by simp [ht])).continuousAt
  have hmer : MeromorphicAt (dedekindZetaSharp K) 1 :=
    (sharp_continuation K).2.2.1 1 (Set.mem_univ 1)
  obtain ⟨g, hgan, _, hgerm⟩ :=
    (meromorphicOrderAt_eq_int_iff hmer).mp (sharp_pole_one K)
  have hG : g =O[𝓝[≠] (1 : ℂ)] fun _ : ℂ => (1 : ℂ) :=
    (hgan.continuousAt.tendsto.isBigO_one ℂ).mono nhdsWithin_le_nhds
  have hZ : dedekindZetaSharp K =O[𝓝[≠] (1 : ℂ)] fun z : ℂ => (z - 1)⁻¹ := by
    have h := (isBigO_refl (fun z : ℂ => (z - 1)⁻¹) (𝓝[≠] (1 : ℂ))).mul hG
    simp only [mul_one] at h
    refine h.congr' ?_ .rfl
    filter_upwards [hgerm] with z hz
    simpa only [zpow_neg_one, smul_eq_mul] using hz.symm
  have h₀ : (fun σ : ℝ => dedekindZetaSharp K σ) =O[𝓝[>] 1]
      fun σ : ℝ => (σ - 1)⁻¹ := by
    have h := (Complex.isBigO_comp_ofReal_nhds_ne (x := 1) hZ).mono
      (nhdsGT_le_nhdsNE 1)
    simpa only [← ofReal_one, ← ofReal_sub, ← ofReal_inv, isBigO_ofReal_right] using h
  have hbound : ∀ᶠ σ : ℝ in 𝓝[>] 1,
      1 ≤ ‖dedekindZetaSharp K σ ^ 3 * dedekindZetaSharp K (σ + I * s.im) ^ 4 *
        dedekindZetaSharp K (σ + 2 * I * s.im)‖ := by
    filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
    rw [dedekindZetaSharp_eq_core K (s := (σ : ℂ)) (by simpa using hσ),
      dedekindZetaSharp_eq_core K (s := (σ : ℂ) + I * s.im) (by simpa using hσ),
      dedekindZetaSharp_eq_core K (s := (σ : ℂ) + 2 * I * s.im) (by simpa using hσ)]
    exact dedekind_three_four_one K hσ s.im
  intro hz
  have hz' : dedekindZetaSharp K (1 + I * s.im) = 0 := by rwa [← hsform]
  have hline (c : ℂ) : Tendsto (fun σ : ℝ => (σ : ℂ) + c)
      (𝓝[>] 1) (𝓝 (1 + c)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds ?_
    exact (continuous_ofReal.add continuous_const).tendsto' (1 : ℝ) (1 + c) (by simp)
  have H₁ : (fun σ : ℝ => dedekindZetaSharp K (σ + I * s.im)) =O[𝓝[>] 1]
      fun σ : ℝ => σ - 1 := by
    have h := h₁.isBigO_sub.comp_tendsto (hline (I * s.im))
    simp only [Function.comp_def, hz', sub_zero, add_sub_add_right_eq_sub] at h
    exact h.trans (isBigO_of_le _ fun σ => by rw [← ofReal_one, ← ofReal_sub, norm_real])
  have H₂ : (fun σ : ℝ => dedekindZetaSharp K (σ + 2 * I * s.im)) =O[𝓝[>] 1]
      fun _ : ℝ => (1 : ℝ) := by
    have h := h₂.tendsto.comp (hline (2 * I * s.im))
    simp only [Function.comp_def] at h
    exact h.isBigO_one ℝ
  have H : (fun σ : ℝ => dedekindZetaSharp K σ ^ 3 *
      dedekindZetaSharp K (σ + I * s.im) ^ 4 *
      dedekindZetaSharp K (σ + 2 * I * s.im)) =o[𝓝[>] 1]
        fun _ : ℝ => (1 : ℝ) := by
    have hlin : (fun σ : ℝ => σ - 1) =o[𝓝[>] 1] fun _ : ℝ => (1 : ℝ) :=
      (isLittleO_one_iff ℝ).mpr <| tendsto_nhdsWithin_of_tendsto_nhds <|
        (continuous_id.sub continuous_const).tendsto' (1 : ℝ) 0 (sub_self 1)
    refine (((h₀.pow 3).mul (H₁.pow 4)).mul H₂).trans_isLittleO (hlin.congr' ?_ .rfl)
    filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
    have hne : σ - 1 ≠ 0 := sub_ne_zero.mpr hσ.ne'
    field_simp
  exact isLittleO_irrefl (.of_forall fun _ => one_ne_zero) <|
    (IsBigO.of_bound' (by simpa using hbound)).trans_isLittleO H

end ArtinPrimitiveRoots.Proofs.s7sol_mellin
