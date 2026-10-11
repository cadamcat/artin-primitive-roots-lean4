import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SMOOTHING.radialKernel_compact_control

set_option autoImplicit false
open NumberField MeasureTheory
open scoped ContDiff

noncomputable section
namespace ArtinPrimitiveRoots.A1.Spec
variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- Representatives equal a.e. on each compact set have equal smoothing at every point.
Uses `radialKernel_compact_control` and frozen
`G1_h3_basics`; provides the stronger representative-independence needed by S3.
No integrability hypothesis is needed for equality of the Bochner integrals. -/
theorem smoothing_representative_independent (k₀ : ℝ → ℝ)
    (hkSmooth : ContDiff ℝ ∞ k₀)
    (hkSupport : {t | k₀ t ≠ 0} ⊆ Set.Icc 1 (1 + 1 / 100))
    (f f' : X F → ℂ)
    (hff' : ∀ W : Set (X F), IsCompact W →
      ∀ᵐ z ∂(volX F), z ∈ W → f z = f' z) (z : X F) :
    smoothingOperator F k₀ f z = smoothingOperator F k₀ f' z := by
  classical
  rcases G1_h3_basics (F := F) with
    ⟨_, _, _, _, _, _, hcoords, hpt, _, _, _, _⟩
  let p : Coord F := coordsX F z
  have hpPos : p ∈ posSet F := by
    intro w
    change 0 < height (z w)
    rw [height_eq_hyperbolicHeight]
    exact OAI.CubicEisenstein.hyperbolicHeight_pos (z w)
  have hptz : ptX F p = z := by
    simpa [p] using hpt z
  let K : Set (Coord F) := {p}
  have hK : IsCompact K := by simp [K]
  have hKpos : K ⊆ posSet F := by
    intro q hq
    rw [Set.mem_singleton_iff.mp hq]
    exact hpPos
  obtain ⟨U, W, hU, hKU, hUpos, hW, hcontrol⟩ :=
    radialKernel_compact_control (F := F) k₀ hkSmooth hkSupport K hK hKpos
  have hpU : p ∈ U := hKU (by simp [K])
  have hzero (w : X F) (hw : w ∉ W) : radialKernel F k₀ z w = 0 := by
    have hs := hcontrol.support 0 p hpU w hw
    have happly := congrArg (fun A => A (fun _ : Fin 0 => p)) hs
    have hzero' : radialKernel F k₀ (ptX F p) w = 0 := by
      simpa only [iteratedFDeriv_zero_apply, zero_apply] using happly
    simpa [hptz] using hzero'
  have hEq : (fun w => radialKernel F k₀ z w * f w) =ᵐ[volX F]
      (fun w => radialKernel F k₀ z w * f' w) := by
    filter_upwards [hff' W hW] with w hw
    by_cases hmem : w ∈ W
    · rw [hw hmem]
    · simp [hzero w hmem]
  calc
    smoothingOperator F k₀ f z = ∫ w, radialKernel F k₀ z w * f w ∂(volX F) := rfl
    _ = ∫ w, radialKernel F k₀ z w * f' w ∂(volX F) := integral_congr_ae hEq
    _ = smoothingOperator F k₀ f' z := rfl

end ArtinPrimitiveRoots.A1.Spec
