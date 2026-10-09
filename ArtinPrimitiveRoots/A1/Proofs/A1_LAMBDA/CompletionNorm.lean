import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.Definitions

/-! Canonical maps and norm homomorphisms for the completions used by Λ.
The completion-map construction follows TauCeti's AdicCompletionExtension
(Apache-2.0), using only its already available Mathlib inputs. -/

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical Topology WithZero Valued
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_lambda_sol

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
variable [w.asIdeal.LiesOver v.asIdeal]

/-- The extension of the field embedding to the completions. -/
def completionMap : v.adicCompletion K →+* w.adicCompletion L :=
  (HeightOneSpectrum.adicCompletion.equiv L w).symm.toRingHom.comp <|
    (UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L)))
      (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver
        (K := K) (L := L) v w).continuous).comp
      (HeightOneSpectrum.adicCompletion.equiv K v).toRingHom

theorem completionMap_toCompletion (x : v.adicCompletion K) :
    (completionMap v w x).toCompletion =
      UniformSpace.Completion.map
        (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L)))
        x.toCompletion := rfl

theorem completionMap_coe (x : K) :
    completionMap v w (x : v.adicCompletion K) =
      (algebraMap K L x : w.adicCompletion L) := by
  apply HeightOneSpectrum.adicCompletion.ext
  rw [completionMap_toCompletion, HeightOneSpectrum.adicCompletion.coe_toCompletion,
    UniformSpace.Completion.map_coe
      (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver
        (K := K) (L := L) v w)]
  rw [WithVal.algebraMap_left_apply, WithVal.algebraMap_right_apply]

theorem completionMap_continuous : Continuous (completionMap v w) :=
  (HeightOneSpectrum.adicCompletion.continuous_ofCompletion L w).comp
    (UniformSpace.Completion.continuous_map.comp
      (HeightOneSpectrum.adicCompletion.continuous_toCompletion K v))

theorem completionMap_unique (f : v.adicCompletion K →+* w.adicCompletion L)
    (hf : Continuous f)
    (hcomp : ∀ x : K, f (x : v.adicCompletion K) =
      (algebraMap K L x : w.adicCompletion L)) :
    f = completionMap v w := by
  apply DFunLike.coe_injective
  apply (v.denseRange_algebraMap K).equalizer hf (completionMap_continuous v w)
  funext x
  simpa only [Function.comp_apply, HeightOneSpectrum.algebraMap_adicCompletion,
    Algebra.algebraMap_self_apply, completionMap_coe] using hcomp x

open WithZeroTopology in
theorem completionMap_valuation (x : v.adicCompletion K) :
    Valued.v (completionMap v w x) =
      Valued.v x ^ v.asIdeal.ramificationIdx' w.asIdeal := by
  rw [← HeightOneSpectrum.adicCompletion.valued_toCompletion L w (completionMap v w x),
    completionMap_toCompletion, ← HeightOneSpectrum.adicCompletion.valued_toCompletion K v x]
  have hK : Function.Surjective
      (⇑(Valued.v : Valuation (v.valuation K).Completion ℤᵐ⁰)) :=
    Valued.valuedCompletion_surjective_iff.mpr <| .of_comp (v.valuation_surjective K)
  have hL : Function.Surjective
      (⇑(Valued.v : Valuation (w.valuation L).Completion ℤᵐ⁰)) :=
    Valued.valuedCompletion_surjective_iff.mpr <| .of_comp (w.valuation_surjective L)
  generalize x.toCompletion = y
  revert y
  apply funext_iff.mp
  symm
  apply UniformSpace.Completion.ext
  · exact (Valued.continuous_valuation_of_surjective hK).pow _
  · exact (Valued.continuous_valuation_of_surjective hL).comp
      UniformSpace.Completion.continuous_map
  intro a
  rw [UniformSpace.Completion.map_coe
      (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver (K := K) (L := L) v w),
    Valued.valuedCompletion_apply, Valued.valuedCompletion_apply]
  exact HeightOneSpectrum.valuation_liesOver (K := K) L v w
    (WithVal.equiv (v.valuation K) a)

theorem completionMap_integer_iff (x : v.adicCompletion K) :
    completionMap v w x ∈ w.adicCompletionIntegers L ↔
      x ∈ v.adicCompletionIntegers K := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers,
    HeightOneSpectrum.mem_adicCompletionIntegers, completionMap_valuation]
  simpa only [one_pow] using
    (pow_le_pow_iff_left₀ (a := Valued.v x) (b := (1 : ℤᵐ⁰)) zero_le zero_le
      (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal v.ne_bot))

theorem completionMap_localUnit_iff (u : (v.adicCompletion K)ˣ) :
    localUnit w (Units.map (completionMap v w).toMonoidHom u) ↔ localUnit v u := by
  simp only [localUnit, Units.val_inv_eq_inv_val, Units.coe_map]
  change ((completionMap v w) (u : v.adicCompletion K) ∈ w.adicCompletionIntegers L ∧
    ((completionMap v w) (u : v.adicCompletion K))⁻¹ ∈ w.adicCompletionIntegers L) ↔
    ((u : v.adicCompletion K) ∈ v.adicCompletionIntegers K ∧
    (u : v.adicCompletion K)⁻¹ ∈ v.adicCompletionIntegers K)
  simpa only [map_inv₀, Units.val_inv_eq_inv_val] using
    and_congr (completionMap_integer_iff v w (u : v.adicCompletion K))
      (completionMap_integer_iff v w ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K))

/-- The canonical algebra structure, scoped to avoid a self-extension diamond. -/
@[reducible] def completionAlgebra : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
  (completionMap v w).toAlgebra

scoped[LambdaCompletion] attribute [instance]
  ArtinPrimitiveRoots.Proofs.a1_lambda_sol.completionAlgebra
open scoped LambdaCompletion

theorem completionAlgebra_map :
    algebraMap (v.adicCompletion K) (w.adicCompletion L) = completionMap v w :=
  RingHom.algebraMap_toAlgebra _

theorem completionScalarTower : IsScalarTower K (v.adicCompletion K) (w.adicCompletion L) :=
  IsScalarTower.of_algebraMap_eq fun x => by
    rw [completionAlgebra_map]
    simpa only [HeightOneSpectrum.algebraMap_adicCompletion,
      Function.comp_apply, Algebra.algebraMap_self_apply] using
      (completionMap_coe v w x).symm

scoped[LambdaCompletion] attribute [instance]
  ArtinPrimitiveRoots.Proofs.a1_lambda_sol.completionScalarTower

theorem completionContinuousSMul :
    ContinuousSMul (v.adicCompletion K) (w.adicCompletion L) where
  continuous_smul := (completionMap_continuous v w).comp continuous_fst |>.mul continuous_snd

scoped[LambdaCompletion] attribute [instance]
  ArtinPrimitiveRoots.Proofs.a1_lambda_sol.completionContinuousSMul

theorem completion_finite : Module.Finite (v.adicCompletion K) (w.adicCompletion L) :=
  inferInstance

/-- The field norm is a determinant of a continuous finite-dimensional linear map. -/
theorem completion_norm_continuous :
    Continuous (Algebra.norm (v.adicCompletion K) : w.adicCompletion L → v.adicCompletion K) := by
  let b := Module.Free.chooseBasis (v.adicCompletion K) (w.adicCompletion L)
  rw [show (Algebra.norm (v.adicCompletion K) : w.adicCompletion L → v.adicCompletion K) =
      fun x => (Algebra.leftMulMatrix b x).det by
    funext x
    exact Algebra.norm_eq_matrix_det b x]
  apply Continuous.matrix_det
  exact (Algebra.leftMulMatrix b).toLinearMap.continuous_of_finiteDimensional

/-- The local norm, including continuity, on the groups of units. -/
def completionNorm : ContinuousMonoidHom (w.adicCompletion L)ˣ (v.adicCompletion K)ˣ where
  toMonoidHom := Units.map (Algebra.norm (v.adicCompletion K))
  continuous_toFun := Continuous.units_map _ (completion_norm_continuous v w)

theorem completionNorm_coe (x : (w.adicCompletion L)ˣ) :
    (completionNorm v w x : v.adicCompletion K) =
      Algebra.norm (v.adicCompletion K) (x : w.adicCompletion L) := rfl

theorem completionNorm_map (x : (v.adicCompletion K)ˣ) :
    completionNorm v w (Units.map (completionMap v w).toMonoidHom x) =
      x ^ Module.finrank (v.adicCompletion K) (w.adicCompletion L) := by
  apply Units.ext
  change Algebra.norm (v.adicCompletion K) (completionMap v w (x : v.adicCompletion K)) = _
  rw [← completionAlgebra_map, Algebra.norm_algebraMap]
  rfl

/-- Local-unit membership is the valuation-one condition for the existing A1 predicate. -/
theorem localUnit_iff_valuation (u : (v.adicCompletion K)ˣ) :
    localUnit v u ↔ Valued.v (u : v.adicCompletion K) = 1 :=
  HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one

/-- A valuation formula gives the exact uniformizer-times-unit form needed by the norm. -/
theorem uniformizer_unit_factor (u : (v.adicCompletion K)ˣ) (n : ℕ)
    (hu : Valued.v (u : v.adicCompletion K) = WithZero.exp (-1 : ℤ) ^ n) :
    ∃ b : (v.adicCompletion K)ˣ, localUnit v b ∧
      u = ArtinPrimitiveRoots.A1.toLoc v
        (ArtinPrimitiveRoots.A1.KummerProofs.uniformizerUnit v) ^ n * b := by
  let π := ArtinPrimitiveRoots.A1.toLoc v
    (ArtinPrimitiveRoots.A1.KummerProofs.uniformizerUnit v)
  have hπ : Valued.v (π : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
    change Valued.v (algebraMap K (v.adicCompletion K)
      (ArtinPrimitiveRoots.A1.KummerProofs.uniformizer v)) = _
    rw [HeightOneSpectrum.algebraMap_adicCompletion]
    simpa only [ArtinPrimitiveRoots.A1.KummerProofs.uniformizer,
      Function.comp_apply, Algebra.algebraMap_self_apply,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] using
      (v.valuation_exists_uniformizer K).choose_spec
  refine ⟨u / π ^ n, ?_, ?_⟩
  · rw [localUnit_iff_valuation]
    simp only [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val, map_div₀, map_pow, hπ, hu]
    exact div_self (pow_ne_zero n WithZero.exp_ne_zero)
  · dsimp only [π]
    simp [div_eq_mul_inv]

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
