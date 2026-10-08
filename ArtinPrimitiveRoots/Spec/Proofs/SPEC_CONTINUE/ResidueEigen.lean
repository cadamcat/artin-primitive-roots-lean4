import ArtinPrimitiveRoots.Spec.Proofs.SPEC_CONTINUE.SeedProperties
import ArtinPrimitiveRoots.Spec.Domain
import Mathlib.Analysis.Analytic.IsolatedZeros

set_option autoImplicit false

open NumberField Matrix Filter
open scoped MatrixGroups ContDiff BoundedContinuousFunction Topology

noncomputable section

open ArtinPrimitiveRoots.A1.Spec
open ArtinPrimitiveRoots.Proofs.spec_continue_p

namespace ArtinPrimitiveRoots.Proofs.spec_cont_sol

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- Analytic coordinate derivatives continue the series eigenfunction equation; their
Laurent numerators give the same partial Laplacian equation for the residue. -/
theorem residue_eigen_of_derivative_families (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (σ : SL(2,F)) (s₁ ε : ℝ) (hs₀ : 0 < s₁) (hs₁ : s₁ < 4) (hε : 0 < ε)
    (E : ℂ → X F → ℂ) (r : X F → ℂ)
    (hseries : ∀ s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2), ∀ z,
      E s z = eisSeries F Γ σ s z)
    (hanalytic : ∀ K : Set (Coord F), IsCompact K → K ⊆ posSet F →
      ∀ (n : ℕ) (v : Fin n → Coord F),
      ∃ Φ : ℂ → (K →ᵇ ℂ), AnalyticOnNhd ℂ Φ (contDomain s₁ ε) ∧
        ∀ s ∈ contDomain s₁ ε, ∀ p : K,
          Φ s p = iteratedFDeriv ℝ n (fun q => E s (ptX F q)) p.1 v)
    (hlaurent : ∀ K : Set (Coord F), IsCompact K → K ⊆ posSet F →
      ∀ (n : ℕ) (v : Fin n → Coord F),
      ∃ Ψ : ℂ → (K →ᵇ ℂ), AnalyticOnNhd ℂ Ψ (Metric.ball (s₁ : ℂ) ε) ∧
        (∀ p : K, Ψ s₁ p = iteratedFDeriv ℝ n (fun q => r (ptX F q)) p.1 v) ∧
        ∀ s ∈ Metric.ball (s₁ : ℂ) ε, s ≠ s₁ → ∀ p : K,
          Ψ s p = (s - s₁) * iteratedFDeriv ℝ n (fun q => E s (ptX F q)) p.1 v) :
    ∀ w z, partialLap F w r z = (1 - 4 * (s₁ : ℂ) ^ 2) * r z := by
  classical
  intro w z
  let p : Coord F := coordsX F z
  let K : Set (Coord F) := {p}
  have hK : IsCompact K := isCompact_singleton
  have hKpos : K ⊆ posSet F := by
    intro q hq
    have hqp : q = p := Set.mem_singleton_iff.mp hq
    subst q
    exact specCoordsX_mem_pos z
  let pp : K := ⟨p, Set.mem_singleton p⟩
  let T : (K →ᵇ ℂ) →L[ℂ] ℂ := BoundedContinuousFunction.evalCLM ℂ pp
  let e1 : Coord F := Pi.single w ((1 : ℂ), (0 : ℝ))
  let e2 : Coord F := Pi.single w (Complex.I, (0 : ℝ))
  let e3 : Coord F := Pi.single w ((0 : ℂ), (1 : ℝ))
  let vY : Fin 1 → Coord F := ![e3]
  let y : ℂ := (p w).2
  let S : Set ℂ := contDomain s₁ ε
  obtain ⟨Φ0, hΦ0, hΦ0val⟩ := hanalytic K hK hKpos 0 Fin.elim0
  obtain ⟨Φy, hΦy, hΦyval⟩ := hanalytic K hK hKpos 1 vY
  obtain ⟨Φ1, hΦ1, hΦ1val⟩ := hanalytic K hK hKpos 2 ![e1, e1]
  obtain ⟨Φ2, hΦ2, hΦ2val⟩ := hanalytic K hK hKpos 2 ![e2, e2]
  obtain ⟨Φ3, hΦ3, hΦ3val⟩ := hanalytic K hK hKpos 2 ![e3, e3]
  let D : ℂ → ℂ := fun s => y * Φy s pp -
    y ^ 2 * (Φ1 s pp + Φ2 s pp + Φ3 s pp) - (1 - 4 * s ^ 2) * Φ0 s pp
  have hy : AnalyticOnNhd ℂ (fun _ : ℂ => y) S := analyticOnNhd_const
  have hy2 : AnalyticOnNhd ℂ (fun _ : ℂ => y ^ 2) S := analyticOnNhd_const
  have hEigenScalar : AnalyticOnNhd ℂ (fun s : ℂ => 1 - 4 * s ^ 2) S := by fun_prop
  have hD : AnalyticOnNhd ℂ D S :=
    ((hy.mul (T.comp_analyticOnNhd hΦy)).sub
      (hy2.mul (((T.comp_analyticOnNhd hΦ1).add
        (T.comp_analyticOnNhd hΦ2)).add (T.comp_analyticOnNhd hΦ3)))).sub
      (hEigenScalar.mul (T.comp_analyticOnNhd hΦ0))
  have hDval (s : ℂ) (hs : s ∈ S) :
      D s = partialLap F w (E s) z - (1 - 4 * s ^ 2) * E s z := by
    dsimp [D]
    rw [hΦyval s hs pp, hΦ1val s hs pp, hΦ2val s hs pp,
      hΦ3val s hs pp, hΦ0val s hs pp]
    simp only [pp, p, iteratedFDeriv_zero_apply, iteratedFDeriv_one_apply,
      specPtX_coordsX]
    rfl
  have hDball (s : ℂ) (hs : s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2)) : D s = 0 := by
    have hn : ‖(5 / 2 : ℂ) - s‖ < 1 / 2 := by
      rw [norm_sub_rev]
      simpa only [dist_eq_norm] using Metric.mem_ball.mp hs
    have hr := (Complex.re_le_norm ((5 / 2 : ℂ) - s)).trans_lt hn
    norm_num [Complex.sub_re] at hr
    have hsre : 1 / 2 < s.re := by linarith only [hr]
    have hEs : E s = eisSeries F Γ σ s := funext (hseries s hs)
    rw [hDval s (Or.inl (Or.inr hs)), hEs,
      (E3_eis_smooth Γ σ s hsre).2.1 w z, sub_self]
  have hDbase : D =ᶠ[𝓝 (5 / 2 : ℂ)] 0 := by
    filter_upwards [Metric.ball_mem_nhds (5 / 2 : ℂ)
      (by norm_num : (0 : ℝ) < 1 / 2)] with s hs
    exact hDball s hs
  have hcenter : (5 / 2 : ℂ) ∈ S :=
    Or.inl (Or.inr (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2)))
  have hDzero := hD.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (C1_domain s₁ ε hs₀ hs₁ hε).2 hcenter hDbase
  have hEeigen (s : ℂ) (hs : s ∈ S) :
      partialLap F w (E s) z = (1 - 4 * s ^ 2) * E s z := by
    have hzero : D s = 0 := hDzero hs
    rw [hDval s hs] at hzero
    exact sub_eq_zero.mp hzero
  let c : ℂ := s₁
  let B : Set ℂ := Metric.ball c ε
  obtain ⟨Ψ0, hΨ0, hΨ0center, hΨ0val⟩ := hlaurent K hK hKpos 0 Fin.elim0
  obtain ⟨Ψy, hΨy, hΨycenter, hΨyval⟩ := hlaurent K hK hKpos 1 vY
  obtain ⟨Ψ1, hΨ1, hΨ1center, hΨ1val⟩ := hlaurent K hK hKpos 2 ![e1, e1]
  obtain ⟨Ψ2, hΨ2, hΨ2center, hΨ2val⟩ := hlaurent K hK hKpos 2 ![e2, e2]
  obtain ⟨Ψ3, hΨ3, hΨ3center, hΨ3val⟩ := hlaurent K hK hKpos 2 ![e3, e3]
  let P : ℂ → ℂ := fun s => y * Ψy s pp -
    y ^ 2 * (Ψ1 s pp + Ψ2 s pp + Ψ3 s pp) - (1 - 4 * s ^ 2) * Ψ0 s pp
  have hyB : AnalyticOnNhd ℂ (fun _ : ℂ => y) B := analyticOnNhd_const
  have hy2B : AnalyticOnNhd ℂ (fun _ : ℂ => y ^ 2) B := analyticOnNhd_const
  have hEigenScalarBall : AnalyticOnNhd ℂ (fun s : ℂ => 1 - 4 * s ^ 2) B := by fun_prop
  have hP : AnalyticOnNhd ℂ P B :=
    ((hyB.mul (T.comp_analyticOnNhd hΨy)).sub
      (hy2B.mul (((T.comp_analyticOnNhd hΨ1).add
        (T.comp_analyticOnNhd hΨ2)).add (T.comp_analyticOnNhd hΨ3)))).sub
      (hEigenScalarBall.mul (T.comp_analyticOnNhd hΨ0))
  have hPval (s : ℂ) (hs : s ∈ B) (hsne : s ≠ c) :
      P s = (s - c) * (partialLap F w (E s) z - (1 - 4 * s ^ 2) * E s z) := by
    dsimp [P, c]
    rw [hΨyval s hs hsne pp, hΨ1val s hs hsne pp, hΨ2val s hs hsne pp,
      hΨ3val s hs hsne pp, hΨ0val s hs hsne pp]
    simp only [pp, p, y, vY, e1, e2, e3, iteratedFDeriv_zero_apply,
      iteratedFDeriv_one_apply, Matrix.cons_val_zero, specPtX_coordsX,
      partialLap, Function.comp_def]
    ring
  have hPcenter : P c = partialLap F w r z - (1 - 4 * c ^ 2) * r z := by
    dsimp [P, c]
    rw [hΨycenter pp, hΨ1center pp, hΨ2center pp, hΨ3center pp, hΨ0center pp]
    simp only [pp, p, iteratedFDeriv_zero_apply, iteratedFDeriv_one_apply,
      specPtX_coordsX]
    rfl
  have hpuncture : P =ᶠ[𝓝[≠] c] 0 := by
    filter_upwards [show B ∈ 𝓝[≠] c from
      nhdsWithin_le_nhds (Metric.ball_mem_nhds c hε), self_mem_nhdsWithin]
      with s hs hsne
    have hsne' : s ≠ c := by simpa using hsne
    have hdom : s ∈ S := Or.inr ⟨hs, by simpa [c] using hsne'⟩
    rw [hPval s hs hsne', hEeigen s hdom, sub_self, mul_zero]
    rfl
  have hPLim : Tendsto P (𝓝[≠] c) (𝓝 (P c)) :=
    (hP c (Metric.mem_ball_self hε)).continuousAt.mono_left nhdsWithin_le_nhds
  have hPzero : P c = 0 :=
    tendsto_nhds_unique_of_eventuallyEq hPLim tendsto_const_nhds hpuncture
  rw [hPcenter] at hPzero
  exact sub_eq_zero.mp hPzero

end ArtinPrimitiveRoots.Proofs.spec_cont_sol
