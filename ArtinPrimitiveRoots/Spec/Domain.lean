import ArtinPrimitiveRoots.Spec.Defs

/-! Continuation-domain node C1. -/

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

/-- C1 `spec:domain` — P-SPEC.md:248, 427–429. The continuation domain is open and preconnected
for the positive parameters used by P-SPEC. -/
theorem C1_domain (s₁ ε : ℝ) (h₀ : 0 < s₁) (h₁ : s₁ < 4) (hε : 0 < ε) :
    IsOpen (contDomain s₁ ε) ∧ IsPreconnected (contDomain s₁ ε) := by
  exact ⟨isOpen_contDomain s₁ ε,
    isPreconnected_contDomain s₁ ε h₀ h₁ hε⟩

end ArtinPrimitiveRoots.A1.Spec
