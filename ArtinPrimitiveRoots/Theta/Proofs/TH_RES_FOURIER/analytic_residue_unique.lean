import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_FOURIER.Defs

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Equality up to a scalar on the convergence ball gives the same scalar relation between
residues. Both functions are analytic on the same connected punctured domain.
Uses Spec.C1_domain and analytic uniqueness.
Feeds Fourier domain independence, diagonal transport, equivariance, and regularized_residue_eval. -/
theorem analytic_residue_unique (η : ℝ) (hη : 0 < η)
    (f f' : ℂ → ℂ) (r r' q : ℂ)
    (hf : AnalyticOnNhd ℂ f (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) η))
    (hf' : AnalyticOnNhd ℂ f' (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) η))
    (hr : ∃ Ψ : ℂ → ℂ, AnalyticOnNhd ℂ Ψ (Metric.ball (1 / 6 : ℂ) η) ∧
      Ψ (1 / 6) = r ∧ ∀ s ∈ Metric.ball (1 / 6 : ℂ) η, s ≠ 1 / 6 →
        Ψ s = (s - 1 / 6) * f s)
    (hr' : ∃ Ψ : ℂ → ℂ, AnalyticOnNhd ℂ Ψ (Metric.ball (1 / 6 : ℂ) η) ∧
      Ψ (1 / 6) = r' ∧ ∀ s ∈ Metric.ball (1 / 6 : ℂ) η, s ≠ 1 / 6 →
        Ψ s = (s - 1 / 6) * f' s)
    (heq : ∀ s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2), f s = q * f' s) :
  r = q * r' := by
  let U := ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) η
  have hqf : AnalyticOnNhd ℂ (fun s : ℂ => q * f' s) U := by
    exact (analyticOnNhd_const.mul hf')
  have hanchorConv : (5 / 2 : ℂ) ∈ Metric.ball (5 / 2 : ℂ) (1 / 2) := by
    simp
  have hconvSubset : Metric.ball (5 / 2 : ℂ) (1 / 2) ⊆ U := by
    intro s hs
    simp only [U, ArtinPrimitiveRoots.A1.Spec.contDomain, Set.mem_union]
    exact Or.inl (Or.inr hs)
  have heventually : f =ᶠ[𝓝 (5 / 2 : ℂ)] (fun s => q * f' s) :=
    Filter.Eventually.mono
      (Metric.isOpen_ball.mem_nhds hanchorConv)
      (fun s hs => heq s hs)
  have hfqf : Set.EqOn f (fun s => q * f' s) U := by
    exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      hf hqf
      (ArtinPrimitiveRoots.A1.Spec.isPreconnected_contDomain (1 / 6) η
        (by norm_num) (by norm_num) hη)
      (hconvSubset hanchorConv) heventually

  obtain ⟨Ψ, hΨ, hΨcenter, hΨvalue⟩ := hr
  obtain ⟨Ψ', hΨ', hΨ'center, hΨ'value⟩ := hr'
  let c : ℂ := 1 / 6
  let V : Set ℂ := Metric.ball c η
  have hqΨ' : AnalyticOnNhd ℂ (fun s : ℂ => q * Ψ' s) V := by
    exact (analyticOnNhd_const.mul hΨ')
  have hpunctured : Set.EqOn Ψ (fun s => q * Ψ' s) (V \ {c}) := by
    intro s hs
    have hsV : s ∈ V := hs.1
    have hs_ne : s ≠ c := by simpa using hs.2
    have hsV' : s ∈ Metric.ball (1 / 6 : ℂ) η := by
      simpa [V, c] using hsV
    have hs_ne' : s ≠ (1 / 6 : ℂ) := by simpa [c] using hs_ne
    have hcenterReal : ((1 / 6 : ℝ) : ℂ) = (1 / 6 : ℂ) := by norm_num
    have hsVspec : s ∈ Metric.ball ((1 / 6 : ℝ) : ℂ) η := by
      rw [hcenterReal]
      exact hsV'
    have hs_neSpec : s ≠ ((1 / 6 : ℝ) : ℂ) := by
      rw [hcenterReal]
      exact hs_ne'
    have hsU : s ∈ U := by
      simp only [U, ArtinPrimitiveRoots.A1.Spec.contDomain, Set.mem_union]
      exact Or.inr ⟨hsVspec, hs_neSpec⟩
    change Ψ s = q * Ψ' s
    rw [hΨvalue s hsV' hs_ne', hΨ'value s hsV' hs_ne', hfqf hsU]
    ring
  let anchor : ℂ := c + ((η / 2 : ℝ) : ℂ)
  have hanchorV : anchor ∈ V := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hdiff : anchor - c = ((η / 2 : ℝ) : ℂ) := by
      simp [anchor, c]
    rw [hdiff, Complex.norm_real, Real.norm_of_nonneg (by positivity : 0 ≤ η / 2)]
    linarith
  have hanchor_ne : anchor ≠ c := by
    intro h
    have hzero : ((η / 2 : ℝ) : ℂ) = 0 := by
      apply add_left_cancel (a := c)
      simpa [anchor] using h
    have hzeroR : η / 2 = 0 := by exact_mod_cast hzero
    linarith
  have hpuncturedOpen : IsOpen (V \ {c}) := by
    rw [Set.sdiff_eq]
    exact Metric.isOpen_ball.inter isOpen_compl_singleton
  have hanchorPunctured : anchor ∈ V \ {c} := by
    exact ⟨hanchorV, by simpa using hanchor_ne⟩
  have heventuallyΨ : Ψ =ᶠ[𝓝 anchor] (fun s => q * Ψ' s) :=
    Filter.Eventually.mono (hpuncturedOpen.mem_nhds hanchorPunctured) hpunctured
  have hΨeq : Set.EqOn Ψ (fun s => q * Ψ' s) V := by
    exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      hΨ hqΨ' (convex_ball c η).isPreconnected hanchorV heventuallyΨ
  have hcV : c ∈ V := Metric.mem_ball_self hη
  have hcEq := hΨeq hcV
  change Ψ (1 / 6 : ℂ) = q * Ψ' (1 / 6 : ℂ) at hcEq
  rw [hΨcenter, hΨ'center] at hcEq
  exact hcEq

end ArtinPrimitiveRoots.A1.Theta
