import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.IndexValue
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.HaarScale
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.w_c.GaussianAnnihilatorPositive

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory
open scoped ENNReal

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

local instance measurableGaussianNonzero (v : FinPlace F) : MeasurableSpace (v.adicCompletion F) := borel _
local instance borelGaussianNonzero (v : FinPlace F) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

/-- The stabilized one-dimensional Gaussian integral is nonzero.
Uses: local_haar_scale; LocalCharacterRegular; finite coset orthogonality. -/
theorem stable_quadratic_integral_ne_zero (A : AddCharData F) (v : FinPlace F) (μ : Measure (v.adicCompletion F))
    (hμ : Measure.IsAddHaarMeasure μ) (hψ : LocalCharacterRegular A v)
    (a : (v.adicCompletion F)ˣ) (N : ℕ) (hN : StabilizesAt A v μ a N) :
    quadraticIntegral A v μ a N ≠ 0 := by
  classical
  obtain ⟨N₀, hN₀⟩ :=
    ArtinPrimitiveRoots.Proofs.a1_weil_sol_w_c.quadraticBallAnnihilator_eventually_trivial
      A v hψ a
  let L := max N N₀
  have hNL : N ≤ L := le_max_left _ _
  have hN₀L : N₀ ≤ L := le_max_right _ _
  have hquad : ∀ t ∈ ArtinPrimitiveRoots.Proofs.a1_weil_sol_w_c.quadraticBallAnnihilator A v L a,
      A.ψ v ((a : v.adicCompletion F) * t ^ 2) = 1 := hN₀ L hN₀L
  have hformula := ArtinPrimitiveRoots.Proofs.a1_weil_sol_w_c.quadraticBall_normSq_of_annihilator_condition
    A v μ hμ hψ a L hquad
  have hBopen : IsOpen (localBall v L) :=
    ArtinPrimitiveRoots.Proofs.a1_weil_sol_w_c.localBall_isOpen v L
  have hBnonempty : (localBall v L).Nonempty := by
    refine ⟨0, ?_⟩
    change Valued.v (0 : v.adicCompletion F) ≤ WithZero.exp (L : ℤ)
    simp
  letI : Measure.IsAddHaarMeasure μ := hμ
  have hBpos : 0 < μ (localBall v L) := hBopen.measure_pos μ hBnonempty
  have hBfinite : μ (localBall v L) ≠ ∞ :=
    (ArtinPrimitiveRoots.Proofs.a1_weil_sol_w_c.localBall_isCompact v L).measure_ne_top
  have hDpos : 0 < μ (ArtinPrimitiveRoots.Proofs.a1_weil_sol_w_c.quadraticBallAnnihilator A v L a) :=
    ArtinPrimitiveRoots.Proofs.a1_weil_sol_w_c.quadraticBallAnnihilator_measure_pos A v μ hμ a L
  have hDfinite :
      μ (ArtinPrimitiveRoots.Proofs.a1_weil_sol_w_c.quadraticBallAnnihilator A v L a) ≠ ∞ := by
    apply ne_of_lt
    exact (measure_mono (by
      intro x hx
      exact hx.1)).trans_lt
        ((ArtinPrimitiveRoots.Proofs.a1_weil_sol_w_c.localBall_isCompact v L).measure_lt_top)
  have hmassB : 0 < μ.real (localBall v L) := ENNReal.toReal_pos hBpos.ne' hBfinite
  have hmassD :
      0 < μ.real (ArtinPrimitiveRoots.Proofs.a1_weil_sol_w_c.quadraticBallAnnihilator A v L a) :=
    ENNReal.toReal_pos hDpos.ne' hDfinite
  have hnorm : 0 < Complex.normSq (quadraticIntegral A v μ a L) := by
    rw [hformula]
    exact mul_pos hmassB hmassD
  have hIL : quadraticIntegral A v μ a L ≠ 0 :=
    Complex.normSq_pos.mp hnorm
  intro hI
  apply hIL
  calc
    quadraticIntegral A v μ a L = quadraticIntegral A v μ a N := hN L hNL
    _ = 0 := hI

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
