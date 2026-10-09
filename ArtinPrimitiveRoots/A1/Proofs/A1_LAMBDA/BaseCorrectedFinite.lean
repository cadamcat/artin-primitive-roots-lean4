import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.BaseLocalCorrection

/-! The primary finite family with its single ramified correction. -/

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical Topology
noncomputable section
attribute [local instance 2000] CyclotomicField.instNumberField

namespace ArtinPrimitiveRoots.Proofs.a1_lambda_sol
open ArtinPrimitiveRoots.A1

/-- Put the completion correction at its own place and one elsewhere. -/
def ramifiedOnly (κ : ContinuousMonoidHom (lambdaPlace.adicCompletion E)ˣ ℂˣ)
    (v : FinPlace E) : ContinuousMonoidHom (v.adicCompletion E)ˣ ℂˣ :=
  if h : v = lambdaPlace then h.symm ▸ κ else 1

theorem ramifiedOnly_self (κ : ContinuousMonoidHom (lambdaPlace.adicCompletion E)ˣ ℂˣ) :
    ramifiedOnly κ lambdaPlace = κ := by simp [ramifiedOnly]

theorem ramifiedOnly_other (κ : ContinuousMonoidHom (lambdaPlace.adicCompletion E)ˣ ℂˣ)
    (v : FinPlace E) (hv : v ≠ lambdaPlace) : ramifiedOnly κ v = 1 := by
  simp [ramifiedOnly, hv]

/-- The finite family after the conductor-(3) correction. -/
def correctedFinite (σ : E →+* ℂ)
    (κ : ContinuousMonoidHom (lambdaPlace.adicCompletion E)ˣ ℂˣ) (v : FinPlace E) :
    ContinuousMonoidHom (v.adicCompletion E)ˣ ℂˣ :=
  ramifiedOnly κ v * baseFiniteCharacter σ v

theorem correctedFinite_unitary (σ : E →+* ℂ)
    (κ : ContinuousMonoidHom (lambdaPlace.adicCompletion E)ˣ ℂˣ)
    (hκ : ∀ u, ‖(κ u : ℂ)‖ = 1) (v : FinPlace E) (u : (v.adicCompletion E)ˣ) :
    ‖(correctedFinite σ κ v u : ℂ)‖ = 1 := by
  have hc : ‖(ramifiedOnly κ v u : ℂ)‖ = 1 := by
    by_cases hv : v = lambdaPlace
    · subst v
      rw [ramifiedOnly_self]
      exact hκ u
    · rw [ramifiedOnly_other κ v hv]
      simp
  change ‖((ramifiedOnly κ v u * baseFiniteCharacter σ v u : ℂˣ) : ℂ)‖ = 1
  rw [Units.val_mul, norm_mul, hc, baseFiniteCharacter_unitary σ v u, one_mul]

theorem correctedFinite_exterior (σ : E →+* ℂ)
    (κ : ContinuousMonoidHom (lambdaPlace.adicCompletion E)ˣ ℂˣ)
    (v : FinPlace E) (hv : lambda ∉ v.asIdeal) :
    correctedFinite σ κ v = baseFiniteCharacter σ v := by
  have hne : v ≠ lambdaPlace := fun h => hv ((lambdaPlace_unique v).mpr h)
  apply ContinuousMonoidHom.ext
  intro u
  change ramifiedOnly κ v u * baseFiniteCharacter σ v u = baseFiniteCharacter σ v u
  rw [ramifiedOnly_other κ v hne]
  exact one_mul _

theorem correctedFinite_eventually_unit_trivial (σ : E →+* ℂ)
    (κ : ContinuousMonoidHom (lambdaPlace.adicCompletion E)ˣ ℂˣ) :
    ∀ᶠ v : FinPlace E in Filter.cofinite,
      ∀ u : (v.adicCompletion E)ˣ, localUnit v u → correctedFinite σ κ v u = 1 := by
  filter_upwards [Filter.eventually_cofinite_ne lambdaPlace] with v hv
  intro u hu
  change ramifiedOnly κ v u * baseFiniteCharacter σ v u = 1
  rw [ramifiedOnly_other κ v hv]
  change 1 * baseFiniteCharacter σ v u = 1
  rw [one_mul]
  exact baseFiniteCharacter_localUnit σ v u hu

theorem ramifiedOnly_principal_support
    (κ : ContinuousMonoidHom (lambdaPlace.adicCompletion E)ˣ ℂˣ) (t : Eˣ) :
    Function.HasFiniteMulSupport (fun v : FinPlace E => ramifiedOnly κ v (toLoc v t)) := by
  apply (Set.finite_singleton lambdaPlace).subset
  intro v hv
  by_contra hne
  apply hv
  change ramifiedOnly κ v (toLoc v t) = 1
  rw [ramifiedOnly_other κ v (fun h => hne (Set.mem_singleton_iff.mpr h))]
  rfl

theorem correctedFinite_product (σ : E →+* ℂ)
    (κ : ContinuousMonoidHom (lambdaPlace.adicCompletion E)ˣ ℂˣ) (t : Eˣ) :
    (∏ᶠ v : FinPlace E, correctedFinite σ κ v (toLoc v t)) =
      κ (toLoc lambdaPlace t) * exteriorFieldProduct σ t := by
  change (∏ᶠ v : FinPlace E, ramifiedOnly κ v (toLoc v t) *
    baseFiniteCharacter σ v (toLoc v t)) = _
  rw [finprod_mul_distrib (ramifiedOnly_principal_support κ t)
    (baseFiniteCharacter_principal_support σ t)]
  rw [finprod_eq_single _ lambdaPlace (fun v hv => by
    rw [ramifiedOnly_other κ v hv]; rfl), ramifiedOnly_self]
  rfl

theorem correctedFinite_principal (σ : E →+* ℂ)
    (a : ContinuousMonoidHom ℂˣ ℂˣ)
    (κ : ContinuousMonoidHom (lambdaPlace.adicCompletion E)ˣ ℂˣ)
    (hκ : ∀ t : Eˣ, κ (toLoc lambdaPlace t) = baseFieldCorrection σ a t) (t : Eˣ) :
    (∏ᶠ v : FinPlace E, correctedFinite σ κ v (toLoc v t)) = baseFieldAngular σ a t := by
  rw [correctedFinite_product, hκ]
  exact baseFieldCorrection_principal σ a t

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
