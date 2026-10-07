import ArtinPrimitiveRoots.Spec.Defs

/-! Functional-analysis nodes F1--F2. -/

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- The inverse of the spectral pencil where it is a unit, extended by zero elsewhere. -/
noncomputable def faInverse (D : FAEnergySpace H G) (z : ℂ) : D.V →L[ℂ] D.V := by
  classical
  exact if h : IsUnit (D.A z) then (↑((h.unit)⁻¹) : D.V →L[ℂ] D.V) else 0

/-- The resolvent of the mass form on a closed energy graph. -/
noncomputable def faResolvent (D : FAEnergySpace H G) (z : ℂ) : H →L[ℂ] H := by
  letI : CompleteSpace D.V := D.closedV.completeSpace_coe
  exact D.M.comp ((faInverse D z).comp D.M.adjoint)

/-- F1 `spec:fa-fredholm` — P-SPEC.md:235, 370–377. The form identity, self-adjointness on the
real axis, and Fredholm property below the coercivity threshold for the abstract energy graph. -/
theorem F1_fredholm (D : FAEnergySpace H G) (K : D.V →L[ℂ] H)
    (hK : IsCompactOperator K) (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C)
    (hest : ∀ x : D.V, ‖D.M x‖ ^ 2 ≤ c * ‖D.Gr x‖ ^ 2 + C * ‖K x‖ ^ 2) :
    (∀ z : ℂ, ∀ x : D.V,
      inner ℂ x (D.A z x) = (‖D.Gr x‖ ^ 2 : ℂ) - z * (‖D.M x‖ ^ 2 : ℂ)) ∧
    (∀ lam : ℝ,
      IsSelfAdjoint (D.A (lam : ℂ)) ∧
      (lam < 1 / c → (D.A (lam : ℂ)).IsFredholm)) := by
  sorry

/-- F2 `spec:fa-resolvent` — P-SPEC.md:236, 370–377. The pencil is invertible and analytically
invertible off the nonnegative real axis; its finite-dimensional kernel gives the local simple-pole
expansion; weak solutions are represented by the mass resolvent; and the kernel projection obeys
the stated norm identity. -/
theorem F2_resolvent (D : FAEnergySpace H G) (K : D.V →L[ℂ] H)
    (hK : IsCompactOperator K) (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C)
    (hest : ∀ x : D.V, ‖D.M x‖ ^ 2 ≤ c * ‖D.Gr x‖ ^ 2 + C * ‖K x‖ ^ 2) :
    (∀ z : ℂ, ∀ x : D.V,
      inner ℂ x (D.A z x) = (‖D.Gr x‖ ^ 2 : ℂ) - z * (‖D.M x‖ ^ 2 : ℂ)) ∧
    (∀ lam : ℝ,
      IsSelfAdjoint (D.A (lam : ℂ)) ∧
      (lam < 1 / c → (D.A (lam : ℂ)).IsFredholm)) ∧
    (∀ z : ℂ, ¬ (z.im = 0 ∧ 0 ≤ z.re) → IsUnit (D.A z)) ∧
    (AnalyticOnNhd ℂ (faInverse D)
      {z : ℂ | ¬ (z.im = 0 ∧ 0 ≤ z.re)}) ∧
    (∀ lam₁ : ℝ, 0 ≤ lam₁ → lam₁ < 1 / c →
      let N : Submodule ℂ D.V := (D.A (lam₁ : ℂ)).toLinearMap.ker
      FiniteDimensional ℂ N ∧
      (∀ x ∈ N, D.T x = (((lam₁ + 1)⁻¹ : ℝ) : ℂ) • x) ∧
      ∃ (P : D.V →L[ℂ] D.V) (δ : ℝ) (B : ℂ → D.V →L[ℂ] D.V),
        0 < δ ∧ P.comp P = P ∧ P.range = N ∧ IsSelfAdjoint P ∧
        AnalyticOnNhd ℂ B (Metric.ball (lam₁ : ℂ) δ) ∧
        ∀ z ∈ Metric.ball (lam₁ : ℂ) δ, z ≠ (lam₁ : ℂ) →
          IsUnit (D.A z) ∧
          faInverse D z =
            (((lam₁ + 1 : ℝ) : ℂ) * (lam₁ - z)⁻¹) • P + B z) ∧
    (∀ (S : Set D.V), Dense S → ∀ z : ℂ, IsUnit (D.A z) →
      ∀ (x : D.V) (f : H),
        (∀ v ∈ S,
          inner ℂ (D.Gr v) (D.Gr x) - z * inner ℂ (D.M v) (D.M x) =
            inner ℂ (D.M v) f) →
        D.M x = faResolvent D z f) ∧
    (∀ lam₁ : ℝ, 0 ≤ lam₁ → lam₁ < 1 / c →
      let N : Submodule ℂ D.V := (D.A (lam₁ : ℂ)).toLinearMap.ker
      ∃ P : D.V →L[ℂ] D.V,
        P.comp P = P ∧ P.range = N ∧ IsSelfAdjoint P ∧
        ∀ G₀ : H,
          (‖D.M (P (D.M.adjoint G₀))‖ ^ 2 : ℂ) =
            (((lam₁ + 1)⁻¹ : ℝ) : ℂ) *
              inner ℂ G₀ (D.M (P (D.M.adjoint G₀)))) := by
  sorry

end ArtinPrimitiveRoots.A1.Spec
