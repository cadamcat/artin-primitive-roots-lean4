import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.BaseFieldCorrection
import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.AngularNormTransport
import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings

/-! The inverse angular infinity factor of the Eisenstein primary character. -/

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical Topology
noncomputable section
attribute [local instance 2000] CyclotomicField.instNumberField

namespace ArtinPrimitiveRoots.Proofs.a1_lambda_sol
open ArtinPrimitiveRoots.A1

theorem eisensteinInfinitePlace_subsingleton : Subsingleton (InfinitePlace E) := by
  apply Fintype.card_le_one_iff_subsingleton.mp
  have hr := IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero E (n := 3) (by decide)
  have hc := IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two 3 E
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, hr, hc]
  norm_num [Nat.totient_prime Nat.prime_three]

/-- The selected complex coordinate of a completion, on units. -/
def complexCompletionUnits (w : InfinitePlace E) :
    ContinuousMonoidHom w.Completionˣ ℂˣ :=
  ⟨Units.map (InfinitePlace.Completion.extensionEmbedding w).toMonoidHom,
    (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.units_map _⟩

theorem complexCompletionUnits_principal (w : InfinitePlace E) (t : Eˣ) :
    complexCompletionUnits w (Dictionary.ideleInfiniteCoordUnit w
      (NumberField.IdeleGroup.unitEmbedding OE E t)) = Units.map w.embedding.toMonoidHom t := by
  apply Units.ext
  change InfinitePlace.Completion.extensionEmbedding w
    (algebraMap E w.Completion (t : E)) = w.embedding (t : E)
  exact InfinitePlace.Completion.extensionEmbedding_coe w
    ((WithAbs.equiv w.1).symm (t : E))

theorem complexCompletionUnits_coordinate (w : InfinitePlace E) (hw : w.IsComplex) (z : ℂˣ) :
    complexCompletionUnits w (Units.map
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toMonoidHom z) = z := by
  apply Units.ext
  change InfinitePlace.Completion.extensionEmbedding w
    ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm (z : ℂ)) = (z : ℂ)
  exact (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).apply_symm_apply (z : ℂ)

theorem angular_unit_norm (a : ContinuousMonoidHom ℂˣ ℂˣ)
    (ha : ∀ z : ℂˣ, (a z : ℂ) = (z : ℂ) / ‖(z : ℂ)‖) (z : ℂˣ) :
    ‖(a z : ℂ)‖ = 1 := by
  have heq : a z = normalizedComplexUnit (z : ℂ) z.ne_zero := Units.ext (ha z)
  rw [heq]
  exact normalizedComplexUnit_norm _ _

/-- Choose the angular sign matching the supplied global complex embedding. -/
def baseInfiniteCharacter (σ : E →+* ℂ) (a : ContinuousMonoidHom ℂˣ ℂˣ)
    (w : InfinitePlace E) : ContinuousMonoidHom w.Completionˣ ℂˣ :=
  if w.embedding = σ then (a.comp (complexCompletionUnits w))⁻¹
  else a.comp (complexCompletionUnits w)

theorem baseInfiniteCharacter_unitary (σ : E →+* ℂ) (a : ContinuousMonoidHom ℂˣ ℂˣ)
    (ha : ∀ z : ℂˣ, (a z : ℂ) = (z : ℂ) / ‖(z : ℂ)‖)
    (w : InfinitePlace E) (u : w.Completionˣ) :
    ‖(baseInfiniteCharacter σ a w u : ℂ)‖ = 1 := by
  by_cases h : w.embedding = σ
  · rw [baseInfiniteCharacter, ite_eq_left h]
    change ‖(((a (complexCompletionUnits w u))⁻¹ : ℂˣ) : ℂ)‖ = 1
    rw [Units.val_inv_eq_inv_val, norm_inv, angular_unit_norm a ha, inv_one]
  · rw [baseInfiniteCharacter, ite_eq_right h]
    exact angular_unit_norm a ha _

theorem baseInfiniteCharacter_angular (σ : E →+* ℂ) (a : ContinuousMonoidHom ℂˣ ℂˣ)
    (ha : ∀ z : ℂˣ, (a z : ℂ) = (z : ℂ) / ‖(z : ℂ)‖)
    (w : InfinitePlace E) (hw : w.IsComplex) :
    ∃ m : ℤ, (m = 1 ∨ m = -1) ∧ ∀ z : ℂˣ,
      (baseInfiniteCharacter σ a w (Units.map
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toMonoidHom z) : ℂ) =
      ((z : ℂ) / ‖(z : ℂ)‖) ^ m := by
  by_cases h : w.embedding = σ
  · refine ⟨-1, Or.inr rfl, fun z => ?_⟩
    rw [baseInfiniteCharacter, ite_eq_left h]
    change (((a (complexCompletionUnits w _))⁻¹ : ℂˣ) : ℂ) = _
    rw [complexCompletionUnits_coordinate, Units.val_inv_eq_inv_val, ha, zpow_neg_one]
  · refine ⟨1, Or.inl rfl, fun z => ?_⟩
    rw [baseInfiniteCharacter, ite_eq_right h]
    change (a (complexCompletionUnits w _) : ℂ) = _
    rw [complexCompletionUnits_coordinate, ha, zpow_one]

theorem baseInfiniteCharacter_principal (σ : E →+* ℂ) (a : ContinuousMonoidHom ℂˣ ℂˣ)
    (ha : ∀ z : ℂˣ, (a z : ℂ) = (z : ℂ) / ‖(z : ℂ)‖)
    (w : InfinitePlace E) (t : Eˣ) :
    baseInfiniteCharacter σ a w (Dictionary.ideleInfiniteCoordUnit w
      (NumberField.IdeleGroup.unitEmbedding OE E t)) = (baseFieldAngular σ a t)⁻¹ := by
  letI := eisensteinInfinitePlace_subsingleton
  have he : w.embedding = σ ∨ w.embedding = ComplexEmbedding.conjugate σ := by
    rw [Subsingleton.elim w (InfinitePlace.mk σ)]
    exact InfinitePlace.embedding_mk_eq σ
  by_cases h : w.embedding = σ
  · rw [baseInfiniteCharacter, ite_eq_left h]
    change (a (complexCompletionUnits w _))⁻¹ = _
    rw [complexCompletionUnits_principal, h]
    rfl
  · have hc := he.resolve_left h
    rw [baseInfiniteCharacter, ite_eq_right h]
    change a (complexCompletionUnits w _) = _
    rw [complexCompletionUnits_principal, hc]
    apply Units.ext
    rw [ha, Units.val_inv_eq_inv_val]
    change star (σ (t : E)) / ‖star (σ (t : E))‖ =
      (a (Units.map σ.toMonoidHom t) : ℂ)⁻¹
    rw [ha]
    exact conjugate_angular_coordinate (Units.map σ.toMonoidHom t)

theorem baseInfiniteCharacter_product (σ : E →+* ℂ) (a : ContinuousMonoidHom ℂˣ ℂˣ)
    (ha : ∀ z : ℂˣ, (a z : ℂ) = (z : ℂ) / ‖(z : ℂ)‖) (t : Eˣ) :
    (∏ w : InfinitePlace E, baseInfiniteCharacter σ a w (Dictionary.ideleInfiniteCoordUnit w
      (NumberField.IdeleGroup.unitEmbedding OE E t))) = (baseFieldAngular σ a t)⁻¹ := by
  letI := eisensteinInfinitePlace_subsingleton
  rw [Fintype.prod_subsingleton _ (InfinitePlace.mk σ)]
  exact baseInfiniteCharacter_principal σ a ha _ t

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
