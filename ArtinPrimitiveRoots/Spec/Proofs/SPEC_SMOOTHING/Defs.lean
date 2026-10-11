import ArtinPrimitiveRoots.Spec.Energy
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Shared hypotheses for local differentiation of the radial smoothing integral. -/

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable (F : Type) [Field F] [NumberField F]

/-- Control of all coordinate derivatives on one common neighborhood and compact integration
set. The bounds are operator norms, so differentiation can be iterated before evaluating a
multilinear derivative on directions.
Used by `radialKernel_compact_control` and `param_deriv_integral_formula`. -/
structure SmoothingKernelControl (k₀ : ℝ → ℝ)
    (U : Set (Coord F)) (W : Set (X F)) : Prop where
  smooth : ∀ w : X F,
    ContDiffOn ℝ ∞ (fun p => radialKernel F k₀ (ptX F p) w) U
  measurable : ∀ (n : ℕ) (p : Coord F), p ∈ U →
    AEStronglyMeasurable
      (fun w => iteratedFDeriv ℝ n (fun q => radialKernel F k₀ (ptX F q) w) p)
      (volX F)
  support : ∀ (n : ℕ) (p : Coord F), p ∈ U → ∀ w : X F, w ∉ W →
    iteratedFDeriv ℝ n (fun q => radialKernel F k₀ (ptX F q) w) p = 0
  bound : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : Coord F), p ∈ U → ∀ w : X F,
    ‖iteratedFDeriv ℝ n (fun q => radialKernel F k₀ (ptX F q) w) p‖ ≤ C

end ArtinPrimitiveRoots.A1.Spec
