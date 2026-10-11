import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.IndexValue
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.HaarScale
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.w_c.GaussianCutoff
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.w_c.GaussianNormSq
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.w_c.GaussianScaleMeasure

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

local instance measurableGaussianModulus (v : FinPlace F) : MeasurableSpace (v.adicCompletion F) := borel _
local instance borelGaussianModulus (v : FinPlace F) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

/-- The ratio modulus with arbitrary Haar normalization; all constants cancel against I(1).
Uses: local_haar_scale; finite Fubini; character orthogonality. -/
theorem stable_quadratic_integral_modulus (A : AddCharData F) (v : FinPlace F) (μ : Measure (v.adicCompletion F))
    (hμ : Measure.IsAddHaarMeasure μ) (hψ : LocalCharacterRegular A v)
    (a : (v.adicCompletion F)ˣ) (N M : ℕ)
    (hN : StabilizesAt A v μ a N) (hM : StabilizesAt A v μ 1 M) :
    absFin v (a : v.adicCompletion F) * ‖quadraticIntegral A v μ a N‖ ^ 2 =
      ‖quadraticIntegral A v μ 1 M‖ ^ 2 := by
  classical
  obtain ⟨Nqa, hNqa⟩ :=
    ArtinPrimitiveRoots.Proofs.a1_weil_sol_w_c.quadraticBallAnnihilator_eventually_trivial
      A v hψ a
  obtain ⟨Nq1, hNq1⟩ :=
    ArtinPrimitiveRoots.Proofs.a1_weil_sol_w_c.quadraticBallAnnihilator_eventually_trivial
      A v hψ 1
  obtain ⟨Nla, hNla⟩ :=
    ArtinPrimitiveRoots.Proofs.a1_weil_sol_w_c.linearBallAnnihilator_eventually_scalar_invariant
      A v hψ a
  obtain ⟨Nl1, hNl1⟩ :=
    ArtinPrimitiveRoots.Proofs.a1_weil_sol_w_c.linearBallAnnihilator_eventually_scalar_invariant
      A v hψ 1
  let L := max N (max M (max Nqa (max Nq1 (max Nla Nl1))))
  have hNL : N ≤ L := by
    simp only [L]
    omega
  have hML : M ≤ L := by
    simp only [L]
    omega
  have hNqaL : Nqa ≤ L := by
    simp only [L]
    omega
  have hNq1L : Nq1 ≤ L := by
    simp only [L]
    omega
  have hNlaL : Nla ≤ L := by
    simp only [L]
    omega
  have hNl1L : Nl1 ≤ L := by
    simp only [L]
    omega
  have hquadA : ∀ t ∈
      ArtinPrimitiveRoots.Proofs.a1_weil_sol_w_c.quadraticBallAnnihilator A v L a,
      A.ψ v ((a : v.adicCompletion F) * t ^ 2) = 1 := hNqa L hNqaL
  have hquad1 : ∀ t ∈
      ArtinPrimitiveRoots.Proofs.a1_weil_sol_w_c.quadraticBallAnnihilator A v L 1,
      A.ψ v ((1 : v.adicCompletion F) * t ^ 2) = 1 := hNq1 L hNq1L
  have htailA : ∀ s ∈
      ArtinPrimitiveRoots.Proofs.a1_weil_sol_w_c.linearBallAnnihilator A v L,
      s ∈ localBall v L ∧ (a : v.adicCompletion F)⁻¹ * s ∈ localBall v L :=
    hNla L hNlaL
  have htail1 : ∀ s ∈
      ArtinPrimitiveRoots.Proofs.a1_weil_sol_w_c.linearBallAnnihilator A v L,
      s ∈ localBall v L ∧ (1 : (v.adicCompletion F)ˣ)⁻¹ * s ∈ localBall v L :=
    by simpa using hNl1 L hNl1L
  have hnormA :=
    ArtinPrimitiveRoots.Proofs.a1_weil_sol_w_c.quadraticBall_normSq_of_annihilator_condition
      A v μ hμ hψ a L hquadA
  have hnorm1 :=
    ArtinPrimitiveRoots.Proofs.a1_weil_sol_w_c.quadraticBall_normSq_of_annihilator_condition
      A v μ hμ hψ 1 L hquad1
  have hscale :=
    ArtinPrimitiveRoots.Proofs.a1_weil_sol_w_c.quadraticBallAnnihilator_measure_scale
      A v μ hμ hψ a L htailA htail1
  have habs : 0 < absFin v (a : v.adicCompletion F) :=
    (local_absolute_value v).2.1 a
  have hnormCommon :
      absFin v (a : v.adicCompletion F) *
          Complex.normSq (quadraticIntegral A v μ a L) =
        Complex.normSq (quadraticIntegral A v μ 1 L) := by
    rw [hnormA, hnorm1, hscale]
    have hne : absFin v (a : v.adicCompletion F) ≠ 0 := habs.ne'
    field_simp [hne]
  have hnorms :
      absFin v (a : v.adicCompletion F) *
          ‖quadraticIntegral A v μ a L‖ ^ 2 =
        ‖quadraticIntegral A v μ 1 L‖ ^ 2 := by
    simpa only [Complex.normSq_eq_norm_sq] using hnormCommon
  simpa only [hN L hNL, hM L hML] using hnorms

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
