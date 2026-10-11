import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_FOURIER.analytic_residue_unique

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Evaluate a regularized identity after continuation from the convergence ball.
Uses analytic_residue_unique.
This is the analytic assembly step owned by the lead in theta_constantTerm. -/
theorem regularized_residue_eval (η : ℝ) (hη : 0 < η) (hηle : η ≤ (1 / 6 : ℝ))
    (f B : ℂ → ℂ) (r : ℂ)
    (hf : AnalyticOnNhd ℂ f (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) η))
    (hB : AnalyticOnNhd ℂ B {s | 0 < s.re})
    (hr : ∃ Ψ : ℂ → ℂ, AnalyticOnNhd ℂ Ψ (Metric.ball (1 / 6 : ℂ) η) ∧
      Ψ (1 / 6) = r ∧ ∀ s ∈ Metric.ball (1 / 6 : ℂ) η, s ≠ 1 / 6 →
        Ψ s = (s - 1 / 6) * f s)
    (heq : ∀ s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2), (s - 1 / 6) * f s = B s) :
    r = B (1 / 6) := by
  have hball (z : ℂ) (hz : z ∈ Metric.ball (1 / 6 : ℂ) η) : 0 < z.re := by
    have hr : |z.re - (1 / 6 : ℝ)| < η := by
      exact lt_of_le_of_lt
        (by simpa using Complex.abs_re_le_norm (z - (1 / 6 : ℂ)))
        (by simpa [Complex.dist_eq] using Metric.mem_ball.mp hz)
    have := (abs_lt.mp hr).1
    linarith
  have hconv (z : ℂ) (hz : z ∈ Metric.ball (5 / 2 : ℂ) (1 / 2)) : 2 < z.re := by
    have hr : |z.re - (5 / 2 : ℝ)| < (1 / 2 : ℝ) := by
      exact lt_of_le_of_lt
        (by simpa using Complex.abs_re_le_norm (z - (5 / 2 : ℂ)))
        (by simpa [Complex.dist_eq] using Metric.mem_ball.mp hz)
    have := (abs_lt.mp hr).1
    linarith
  let U := ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) η
  have hpos : U ⊆ {s : ℂ | 0 < s.re} := by
    intro z hz
    simp only [U, ArtinPrimitiveRoots.A1.Spec.contDomain, Set.mem_union] at hz
    rcases hz with (hz | hz) | hz
    · exact hz.1
    · exact lt_trans (by norm_num) (hconv z hz)
    · exact hball z (by convert hz.1 using 1 <;> norm_num)
  have hne : ∀ z ∈ U, z - (1 / 6 : ℂ) ≠ 0 := by
    intro z hz heqz
    have hz0 : z = (1 / 6 : ℂ) := sub_eq_zero.mp heqz
    subst z
    simp only [U, ArtinPrimitiveRoots.A1.Spec.contDomain, Set.mem_union] at hz
    rcases hz with (hz | hz) | hz
    · norm_num at hz
    · have h := hconv (1 / 6) hz
      norm_num at h
    · exact hz.2 (by simp)
  let f' : ℂ → ℂ := fun s => B s / (s - 1 / 6)
  have hf' : AnalyticOnNhd ℂ f' U := by
    have hd : AnalyticOnNhd ℂ (fun s : ℂ => s - 1 / 6) U := by fun_prop
    exact (hB.mono hpos).div hd hne
  have hr' : ∃ Ψ : ℂ → ℂ, AnalyticOnNhd ℂ Ψ (Metric.ball (1 / 6 : ℂ) η) ∧
      Ψ (1 / 6) = B (1 / 6) ∧ ∀ s ∈ Metric.ball (1 / 6 : ℂ) η, s ≠ 1 / 6 →
        Ψ s = (s - 1 / 6) * f' s := by
    refine ⟨B, hB.mono hball, rfl, ?_⟩
    intro s hs hns
    dsimp [f']
    exact (mul_div_cancel₀ (B s) (sub_ne_zero.mpr hns)).symm
  have heq' : ∀ s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2), f s = 1 * f' s := by
    intro s hs
    have hsU : s ∈ U := by
      simp only [U, ArtinPrimitiveRoots.A1.Spec.contDomain, Set.mem_union]
      exact Or.inl (Or.inr hs)
    dsimp [f']
    rw [one_mul]
    apply (eq_div_iff (hne s hsU)).mpr
    simpa only [mul_comm] using heq s hs
  simpa only [one_mul] using
    analytic_residue_unique η hη f f' r (B (1 / 6)) 1 hf hf' hr hr' heq'

end ArtinPrimitiveRoots.A1.Theta
