import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.CompletionNorm
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion
import ValuedFieldTheory.Valuation.Henselian.Complete

/-! The completed integer rings form the actual integral closure for the
canonical completion algebra. This supplies integral and unit norm transport. -/

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical Topology WithZero Valued LambdaCompletion
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_lambda_sol

open AlgebraicNumberTheory.Valuations

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
variable [w.asIdeal.LiesOver v.asIdeal]

/-- The existing completion norm, bundled as an absolute value. -/
def completionAbs : AbsoluteValue (v.adicCompletion K) ℝ where
  toFun := norm
  map_mul' := norm_mul
  nonneg' := norm_nonneg
  eq_zero' := fun _ => norm_eq_zero
  add_le' := norm_add_le

theorem completionAbs_nonarch :
    LubinTate.Valuations.NonarchimedeanAbsoluteValue (completionAbs v) := by
  refine ⟨1, fun n => ?_⟩
  change ‖(n : v.adicCompletion K)‖ ≤ 1
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih (by simp))

theorem completionAbs_complete : IsCompleteForAbsoluteValue (completionAbs v) := by
  apply (absoluteValueCompleteness_completeSpace_withAbs_iff_complete (completionAbs v)).1
  let e : WithAbs (completionAbs v) ≃ᵢ v.adicCompletion K :=
    { toEquiv := (WithAbs.equiv (completionAbs v)).toEquiv
      isometry_toFun := by
        rw [isometry_iff_dist_eq]
        intro x y
        simp only [dist_eq_norm_sub, WithAbs.norm_eq_apply_ofAbs, WithAbs.ofAbs_sub]
        rfl }
  exact e.completeSpace_iff.mpr inferInstance

theorem completionAbs_integers :
    absoluteValueValuationSubring (completionAbs v) (completionAbs_nonarch v) =
      v.adicCompletionIntegers K := by
  ext x
  rw [mem_absoluteValueValuationSubring_iff, HeightOneSpectrum.mem_adicCompletionIntegers]
  exact Valued.toNormedField.norm_le_one_iff

theorem completionInteger_hensel :
    ValuationTheory.DiscreteValuationField.HenselFactorizationProperty
      (v.adicCompletionIntegers K) := by
  have h : ValuationTheory.DiscreteValuationField.HenselFactorizationProperty
      (absoluteValueValuationSubring (completionAbs v) (completionAbs_nonarch v)) :=
    @henselFactorization_of_complete _ _ (completionAbs v) (completionAbs_complete v)
      (completionAbs_nonarch v)
  rw [completionAbs_integers] at h
  exact @h

/-- Restriction of the canonical completion map to the integer rings. -/
def completionIntegerMap : v.adicCompletionIntegers K →+* w.adicCompletionIntegers L :=
  ((completionMap v w).comp (algebraMap (v.adicCompletionIntegers K)
    (v.adicCompletion K))).codRestrict (w.adicCompletionIntegers L).toSubring
      (fun x => (completionMap_integer_iff v w x).mpr x.property)

@[reducible] def completionIntegerAlgebra :
    Algebra (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) :=
  (completionIntegerMap v w).toAlgebra

scoped[LambdaCompletion] attribute [instance]
  ArtinPrimitiveRoots.Proofs.a1_lambda_sol.completionIntegerAlgebra

@[reducible] def completionIntegerFieldAlgebra :
    Algebra (v.adicCompletionIntegers K) (w.adicCompletion L) :=
  ((completionMap v w).comp
    (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))).toAlgebra

scoped[LambdaCompletion] attribute [instance]
  ArtinPrimitiveRoots.Proofs.a1_lambda_sol.completionIntegerFieldAlgebra

theorem completionIntegerTower :
    IsScalarTower (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)
      (w.adicCompletion L) := IsScalarTower.of_algebraMap_eq fun _ => rfl

scoped[LambdaCompletion] attribute [instance]
  ArtinPrimitiveRoots.Proofs.a1_lambda_sol.completionIntegerTower

theorem completionIntegerFieldTower :
    IsScalarTower (v.adicCompletionIntegers K) (v.adicCompletion K)
      (w.adicCompletion L) := IsScalarTower.of_algebraMap_eq fun _ => rfl

scoped[LambdaCompletion] attribute [instance]
  ArtinPrimitiveRoots.Proofs.a1_lambda_sol.completionIntegerFieldTower

theorem completionInteger_hasExtension :
    (v.adicCompletionIntegers K).valuation.HasExtension
      (Valued.v : Valuation (w.adicCompletion L) ℤᵐ⁰) := by
  apply Valuation.HasExtension.ofComapInteger
  rw [ValuationSubring.integer_valuation]
  ext x
  change completionMap v w x ∈ w.adicCompletionIntegers L ↔
    x ∈ v.adicCompletionIntegers K
  exact completionMap_integer_iff v w x

theorem completionAbs_integral_iff (x : w.adicCompletion L) :
    IsIntegral (absoluteValueValuationSubring (completionAbs v) (completionAbs_nonarch v)) x ↔
      IsIntegral (v.adicCompletionIntegers K) x := by
  let e : absoluteValueValuationSubring (completionAbs v) (completionAbs_nonarch v) ≃+*
      v.adicCompletionIntegers K :=
    RingEquiv.subringCongr (congrArg ValuationSubring.toSubring (completionAbs_integers v))
  apply e.isIntegral_iff
  ext r
  rfl

theorem completionInteger_integralClosure_eq :
    (w.adicCompletionIntegers L).toSubring =
      (integralClosure (v.adicCompletionIntegers K) (w.adicCompletion L)).toSubring := by
  let V := absoluteValueValuationSubring (completionAbs v) (completionAbs_nonarch v)
  let : V.valuation.HasExtension (Valued.v : Valuation (w.adicCompletion L) ℤᵐ⁰) := by
    apply Valuation.HasExtension.ofComapInteger
    rw [ValuationSubring.integer_valuation]
    ext x
    change completionMap v w x ∈ w.adicCompletionIntegers L ↔ x ∈ V
    rw [completionMap_integer_iff]
    dsimp only [V]
    rw [completionAbs_integers]
  have hval : ∀ z : w.adicCompletion L,
      z ∈ (integralClosure V.valuation.valuationSubring
        (w.adicCompletion L)).toSubring ∨
      z⁻¹ ∈ (integralClosure V.valuation.valuationSubring
        (w.adicCompletion L)).toSubring := by
    rw [ValuationSubring.valuationSubring_valuation]
    intro z
    exact normFormula_algebraic_integralClosure_mem_or_inv_of_henselFactorization
      (L := w.adicCompletion L) (completionAbs v) (completionAbs_nonarch v)
      (@henselFactorization_of_complete _ _ (completionAbs v) (completionAbs_complete v)
        (completionAbs_nonarch v)) z
  have h := DiscreteValuationField.Valuation.normFormula_extension_valuationSubring_eq_integralClosure_of_mem_or_inv
      V hval
      (Valued.v : Valuation (w.adicCompletion L) ℤᵐ⁰)
  have hs := congrArg ValuationSubring.toSubring h
  change (Valued.v : Valuation (w.adicCompletion L) ℤᵐ⁰).valuationSubring.toSubring =
    (integralClosure V.valuation.valuationSubring (w.adicCompletion L)).toSubring at hs
  rw [ValuationSubring.valuationSubring_valuation] at hs
  ext x
  change x ∈ w.adicCompletionIntegers L ↔
    x ∈ integralClosure (v.adicCompletionIntegers K) (w.adicCompletion L)
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, mem_integralClosure_iff]
  have hx : (Valued.v : Valuation (w.adicCompletion L) ℤᵐ⁰) x ≤ 1 ↔ IsIntegral V x := by
    change x ∈ (Valued.v : Valuation (w.adicCompletion L) ℤᵐ⁰).valuationSubring.toSubring ↔ _
    rw [hs, Subalgebra.mem_toSubring, mem_integralClosure_iff]
  exact hx.trans (completionAbs_integral_iff v w x)

/-- The actual local integer ring is the integral closure of the base local integer ring. -/
theorem completionInteger_isIntegralClosure :
    IsIntegralClosure (w.adicCompletionIntegers L) (v.adicCompletionIntegers K)
      (w.adicCompletion L) where
  algebraMap_injective := Subtype.val_injective
  isIntegral_iff {x} := by
    rw [← mem_integralClosure_iff]
    change x ∈ (integralClosure (v.adicCompletionIntegers K) (w.adicCompletion L)).toSubring ↔ _
    rw [← completionInteger_integralClosure_eq v w]
    exact ⟨fun h => ⟨⟨x, h⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.property⟩

scoped[LambdaCompletion] attribute [instance]
  ArtinPrimitiveRoots.Proofs.a1_lambda_sol.completionInteger_isIntegralClosure

theorem completionInteger_finite :
    Module.Finite (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) :=
  IsIntegralClosure.finite (v.adicCompletionIntegers K) (v.adicCompletion K)
    (w.adicCompletion L) (w.adicCompletionIntegers L)

scoped[LambdaCompletion] attribute [instance]
  ArtinPrimitiveRoots.Proofs.a1_lambda_sol.completionInteger_finite

theorem completionNorm_integer (x : w.adicCompletionIntegers L) :
    Algebra.norm (v.adicCompletion K) (x : w.adicCompletion L) ∈
      v.adicCompletionIntegers K := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  apply (HeightOneSpectrum.adicCompletionIntegers.integers K v).isIntegral_iff_v_le_one.mp
  apply Algebra.isIntegral_norm (v.adicCompletion K)
  exact (IsIntegralClosure.isIntegral_iff (R := v.adicCompletionIntegers K)
    (A := w.adicCompletionIntegers L) (B := w.adicCompletion L)).mpr ⟨x, rfl⟩

theorem completionNorm_localUnit (u : (w.adicCompletion L)ˣ) (hu : localUnit w u) :
    localUnit v (completionNorm v w u) := by
  rcases hu with ⟨hu, hui⟩
  have h₁ := completionNorm_integer v w
    (⟨(u : w.adicCompletion L), hu⟩ : w.adicCompletionIntegers L)
  have h₂ := completionNorm_integer v w
    (⟨((u⁻¹ : (w.adicCompletion L)ˣ) : w.adicCompletion L), hui⟩ :
      w.adicCompletionIntegers L)
  refine ⟨h₁, ?_⟩
  rw [← map_inv]
  exact h₂

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
