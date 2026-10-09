import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.BasePrincipalProduct

/-! The algebraic ramified correction on global field units.
It is unitary and trivial on quotients of primary integers. Extending it
continuously to the ramified completion remains a separate construction. -/

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical Topology
noncomputable section

attribute [local instance 2000] CyclotomicField.instNumberField

namespace ArtinPrimitiveRoots.Proofs.a1_lambda_sol

/-- The prescribed angular homomorphism on global Eisenstein field units. -/
def baseFieldAngular (σ : E →+* ℂ) (a : ContinuousMonoidHom ℂˣ ℂˣ) : Eˣ →* ℂˣ :=
  a.toMonoidHom.comp (Units.map σ.toMonoidHom)

theorem baseFieldAngular_value (σ : E →+* ℂ) (a : ContinuousMonoidHom ℂˣ ℂˣ)
    (ha : ∀ z : ℂˣ, (a z : ℂ) = (z : ℂ) / ‖(z : ℂ)‖) (t : Eˣ) :
    baseFieldAngular σ a t = normalizedComplexUnit (σ (t : E))
      (by simpa only [map_zero] using σ.injective.ne t.ne_zero) := by
  apply Units.ext
  exact ha (Units.map σ.toMonoidHom t)

theorem baseFieldAngular_unitary (σ : E →+* ℂ) (a : ContinuousMonoidHom ℂˣ ℂˣ)
    (ha : ∀ z : ℂˣ, (a z : ℂ) = (z : ℂ) / ‖(z : ℂ)‖) (t : Eˣ) :
    ‖(baseFieldAngular σ a t : ℂ)‖ = 1 := by
  rw [baseFieldAngular_value σ a ha t]
  exact normalizedComplexUnit_norm _ _

/-- The angular value divided by the already prescribed finite factors. -/
def baseFieldCorrection (σ : E →+* ℂ) (a : ContinuousMonoidHom ℂˣ ℂˣ) :
    Eˣ →* ℂˣ := baseFieldAngular σ a / exteriorFieldProduct σ

theorem baseFieldCorrection_principal (σ : E →+* ℂ)
    (a : ContinuousMonoidHom ℂˣ ℂˣ) (t : Eˣ) :
    baseFieldCorrection σ a t * exteriorFieldProduct σ t = baseFieldAngular σ a t := by
  change (baseFieldAngular σ a t / exteriorFieldProduct σ t) *
    exteriorFieldProduct σ t = baseFieldAngular σ a t
  exact div_mul_cancel _ _

theorem baseFieldCorrection_unitary (σ : E →+* ℂ)
    (a : ContinuousMonoidHom ℂˣ ℂˣ)
    (ha : ∀ z : ℂˣ, (a z : ℂ) = (z : ℂ) / ‖(z : ℂ)‖) (t : Eˣ) :
    ‖(baseFieldCorrection σ a t : ℂ)‖ = 1 := by
  change ‖((baseFieldAngular σ a t / exteriorFieldProduct σ t : ℂˣ) : ℂ)‖ = 1
  rw [Units.val_div_eq_div_val, norm_div, baseFieldAngular_unitary σ a ha t,
    exteriorFieldProduct_unitary σ t, div_self (one_ne_zero : (1 : ℝ) ≠ 0)]

/-- The primary principal formula kills the correction on primary integers. -/
theorem baseFieldCorrection_primary (σ : E →+* ℂ) (φ : Ideal OE →*₀ ℂ)
    (hφ : ∀ I : Ideal OE,
      φ I = integerComplex σ (primary I) / ‖integerComplex σ (primary I)‖)
    (a : ContinuousMonoidHom ℂˣ ℂˣ)
    (ha : ∀ z : ℂˣ, (a z : ℂ) = (z : ℂ) / ‖(z : ℂ)‖)
    (n : OE) (hn : n ≠ 0) (hprimary : lambda ^ 2 ∣ n - 1) :
    baseFieldCorrection σ a (integerFieldUnit n hn) = 1 := by
  change baseFieldAngular σ a (integerFieldUnit n hn) /
    exteriorFieldProduct σ (integerFieldUnit n hn) = 1
  rw [baseFieldAngular_value σ a ha, exteriorFieldProduct_primary σ φ hφ n hn hprimary]
  simp [integerFieldUnit, integerComplex]

/-- The primary kernel is closed under ratios, as needed for local fractions. -/
theorem baseFieldCorrection_primary_div (σ : E →+* ℂ) (φ : Ideal OE →*₀ ℂ)
    (hφ : ∀ I : Ideal OE,
      φ I = integerComplex σ (primary I) / ‖integerComplex σ (primary I)‖)
    (a : ContinuousMonoidHom ℂˣ ℂˣ)
    (ha : ∀ z : ℂˣ, (a z : ℂ) = (z : ℂ) / ‖(z : ℂ)‖)
    (n d : OE) (hn : n ≠ 0) (hd : d ≠ 0)
    (hnprimary : lambda ^ 2 ∣ n - 1) (hdprimary : lambda ^ 2 ∣ d - 1) :
    baseFieldCorrection σ a (integerFieldUnit n hn / integerFieldUnit d hd) = 1 := by
  rw [map_div, baseFieldCorrection_primary σ φ hφ a ha n hn hnprimary,
    baseFieldCorrection_primary σ φ hφ a ha d hd hdprimary, one_div_one]

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
