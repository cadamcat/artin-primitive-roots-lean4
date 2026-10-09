import ArtinPrimitiveRoots.Theta.Proofs.«TH-PROFILE».Differentiation

set_option autoImplicit false

open MeasureTheory Filter
open scoped Classical Topology

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_probe_sol

/-- Bounds on each bounded scale interval suffice for differentiating a radial integral
of every order. -/
theorem local_radial_integral_smooth {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (D : ℕ → ℝ → X → ℂ)
    (hmeas : ∀ j t, AEStronglyMeasurable (D j t) ν)
    (hdiff : ∀ j, ∀ᵐ x ∂ν, ∀ t,
      HasDerivAt (fun s : ℝ => D j s x) (D (j + 1) t x) t)
    (hbound : ∀ (j : ℕ) (a b : ℝ), a ≤ b →
      ∃ g : X → ℝ, Integrable g ν ∧
        ∀ᵐ x ∂ν, ∀ t ∈ Set.Icc a b, ‖D j t x‖ ≤ g x) :
    (∀ j t, Integrable (D j t) ν) ∧
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => ∫ x, D 0 t x ∂ν) ∧
    ∀ j t, iteratedDeriv j (fun s : ℝ => ∫ x, D 0 s x ∂ν) t = ∫ x, D j t x ∂ν := by
  have hi (j : ℕ) (t : ℝ) : Integrable (D j t) ν := by
    obtain ⟨g, hg, hgd⟩ := hbound j t t le_rfl
    exact hg.mono' (hmeas j t) (hgd.mono fun x hx => hx t ⟨le_rfl, le_rfl⟩)
  have hder (j : ℕ) (t : ℝ) :
      HasDerivAt (fun s : ℝ => ∫ x, D j s x ∂ν) (∫ x, D (j + 1) t x ∂ν) t := by
    obtain ⟨g, hg, hgd⟩ := hbound (j + 1) (t - 1) (t + 1) (by linarith)
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := ν) (F := D j) (F' := D (j + 1)) (s := Set.Icc (t - 1) (t + 1))
      (x₀ := t) (bound := g) (Icc_mem_nhds (by linarith) (by linarith))
      (Eventually.of_forall fun s => hmeas j s) (hi j t)
      (hmeas (j + 1) t) hgd hg ?_).2
    exact (hdiff j).mono fun x hx t _ => hx t
  have hId (j : ℕ) :
      iteratedDeriv j (fun t : ℝ => ∫ x, D 0 t x ∂ν) =
        fun t : ℝ => ∫ x, D j t x ∂ν := by
    induction j with
    | zero => simp only [iteratedDeriv_zero]
    | succ j ih =>
      rw [iteratedDeriv_succ, ih]
      funext t
      exact (hder j t).deriv
  refine ⟨hi, ?_, fun j t => congrFun (hId j) t⟩
  apply contDiff_of_differentiable_iteratedDeriv
  intro j hj
  rw [hId j]
  intro t
  exact (hder j t).differentiableAt

end ArtinPrimitiveRoots.Proofs.a2_probe_sol
