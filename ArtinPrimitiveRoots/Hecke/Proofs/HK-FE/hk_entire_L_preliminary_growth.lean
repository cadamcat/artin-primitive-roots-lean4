import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_mellin_FE_completed
import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_completed_gamma_product
import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_entire_L_agreement


set_option autoImplicit false
open NumberField ClassFieldTheory MeasureTheory
open scoped NumberField
noncomputable section
namespace ArtinPrimitiveRoots.Hecke
variable {K : Type*} [Field K] [NumberField K]

/-- Preliminary exponential growth on a fixed real strip, sufficient for later PL.
Guide: sol-thin-hk2/PROOFS.md:1547–1592. Uses the split completed Mellin integral,
hk_mellin_FE_completed, reciprocal Gamma reflection/recurrence and compact continuity.
The constants may depend on this character; polynomial growth is supplied by HK-H3. -/
theorem hk_entire_L_preliminary_growth [IsTotallyComplex K] {m : RayClassModulus K}
    (ψ : RayClassGroup m →* ℂˣ) (hψ : ψ ≠ 1) (hp : HKPrimitive ψ)
    (a b : ℝ) (hab : a ≤ b) :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖hkEntireL ψ s‖ ≤ C * Real.exp (B * (1 + |s.im|)) := by
  sorry

end ArtinPrimitiveRoots.Hecke
