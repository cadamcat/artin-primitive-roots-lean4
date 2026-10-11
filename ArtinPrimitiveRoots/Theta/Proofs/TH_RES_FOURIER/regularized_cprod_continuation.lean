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

/-- A regularization of the Euler product on the positive half-plane, with its residue
identified by the same real-sided limit used in resCprod.
Uses FourierEulerHyp, supplied by the frozen cprod_eq_zeta_ratio and the existing
resLSeries_eq_zetaT0 helper at the Res boundary. Feeds theta_constantTerm. -/
theorem regularized_cprod_continuation (T0 : Finset (FinPlace F))
    (hEuler : FourierEulerHyp T0) :
    ∃ B : ℂ → ℂ, AnalyticOnNhd ℂ B {s | 0 < s.re} ∧
      B (1 / 6) = limUnder (𝓝[>] (1 / 6 : ℝ))
        (fun t : ℝ => ((t : ℂ) - 1 / 6) * cprod T0 (t : ℂ)) ∧
      ∀ s : ℂ, 1 / 6 < s.re → B s = (s - 1 / 6) * cprod T0 s := by
  rcases hEuler with ⟨L, N, hLanalytic, hLne, hNdifferentiable, hNeq, hcprod⟩
  let U : Set ℂ := {s | 0 < s.re}
  let B : ℂ → ℂ := fun s => (1 / 6 : ℂ) * N (6 * s) / L (6 * s + 1)
  have hNanalytic : AnalyticOnNhd ℂ N Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr hNdifferentiable
  have hmap1 (s : ℂ) (hs : s ∈ U) : 1 < (6 * s + 1).re := by
    have hre : (6 * s + 1).re = 6 * s.re + 1 := by simp
    rw [hre]
    dsimp [U] at hs
    nlinarith
  have hNcomp : AnalyticOnNhd ℂ (fun s : ℂ => N (6 * s)) U := by
    have hinner : AnalyticOnNhd ℂ (fun s : ℂ => 6 * s) U := by fun_prop
    exact hNanalytic.comp hinner (by intro s hs; simp)
  have hLcomp : AnalyticOnNhd ℂ (fun s : ℂ => L (6 * s + 1)) U := by
    have hinner : AnalyticOnNhd ℂ (fun s : ℂ => 6 * s + 1) U := by fun_prop
    exact hLanalytic.comp hinner hmap1
  have hnum : AnalyticOnNhd ℂ (fun s : ℂ => (1 / 6 : ℂ) * N (6 * s)) U := by
    have hconst : AnalyticOnNhd ℂ (fun _ : ℂ => (1 / 6 : ℂ)) U := by fun_prop
    exact hconst.mul hNcomp
  have hBanalytic : AnalyticOnNhd ℂ B U := by
    have hden : ∀ s ∈ U, L (6 * s + 1) ≠ 0 := by
      intro s hs
      exact hLne (6 * s + 1) (hmap1 s hs)
    simpa [B] using hnum.div hLcomp hden
  have hB_eq (s : ℂ) (hs : 1 / 6 < s.re) :
      B s = (s - 1 / 6) * cprod T0 s := by
    have hsU : s ∈ U := by dsimp [U]; linarith
    have hs0 : 1 < (6 * s).re := by
      have hre : (6 * s).re = 6 * s.re := by simp
      rw [hre]
      linarith
    have hs1 : 1 < (6 * s + 1).re := hmap1 s hsU
    have hN := hNeq (6 * s) hs0
    have hprod := hcprod s hs
    dsimp [B]
    rw [hN, hprod]
    have hL0 : L (6 * s) ≠ 0 := hLne (6 * s) hs0
    have hL1 : L (6 * s + 1) ≠ 0 := hLne (6 * s + 1) hs1
    field_simp
  have hcenter : (1 / 6 : ℂ) ∈ U := by dsimp [U]; norm_num
  have hBcast : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] (1 / 6 : ℝ))
      (𝓝 (1 / 6 : ℂ)) := by
    have hcast := (Complex.continuous_ofReal.tendsto (1 / 6 : ℝ)).mono_left
      (show 𝓝[>] (1 / 6 : ℝ) ≤ 𝓝 (1 / 6 : ℝ) from nhdsWithin_le_nhds)
    simpa using hcast
  have hBlim : Tendsto (fun t : ℝ => B (t : ℂ)) (𝓝[>] (1 / 6 : ℝ))
      (𝓝 (B (1 / 6))) :=
    (hBanalytic (1 / 6) hcenter).continuousAt.tendsto.comp hBcast
  have hmatch : (fun t : ℝ => B (t : ℂ)) =ᶠ[𝓝[>] (1 / 6 : ℝ)]
      (fun t : ℝ => ((t : ℂ) - 1 / 6) * cprod T0 (t : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    apply hB_eq
    simpa using ht
  have hlim : Tendsto
      (fun t : ℝ => ((t : ℂ) - 1 / 6) * cprod T0 (t : ℂ))
      (𝓝[>] (1 / 6 : ℝ)) (𝓝 (B (1 / 6))) := hBlim.congr' hmatch
  refine ⟨B, hBanalytic, ?_, hB_eq⟩
  exact hlim.limUnder_eq.symm

end ArtinPrimitiveRoots.A1.Theta
