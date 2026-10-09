import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.IdeleNormTransport
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.OnePlaceBaseNorm

/-! Finite local specifications for the exact Mathlib idele norm.
The single-place comparison is adapted from ClassFieldTheory's
MathlibComparison (Apache-2.0); that module has no shared artifact.
Local norm order and single-place norm formulas use prebuilt CFT modules. -/

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical Topology WithZero Valued LambdaCompletion
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_lambda_sol

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]

/-- The topology comparison preserves finite single-place ideles. -/
theorem ideleContinuousEquiv_finitePlaceIdele
    (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    ideleContinuousEquiv K (_root_.IdeleGroup.finitePlaceIdele v x) =
      NumberField.IdeleGroup.ofAdicCompletion (𝓞 K) K v x := by
  apply Units.ext
  apply Prod.ext
  · rfl
  · apply RestrictedProduct.ext
    intro w
    change ((_root_.IdeleGroup.finitePlaceIdele v x).2 w : w.adicCompletion K) =
      (RestrictedProduct.mulSingle
        (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletionIntegers K)
        v (x : v.adicCompletion K)) w
    by_cases hw : w = v
    · subst w
      rw [RestrictedProduct.mulSingle_eq_same]
      exact congrArg (fun u : (v.adicCompletion K)ˣ => (u : v.adicCompletion K))
        (_root_.IdeleGroup.finitePlaceIdele_finiteComponent_same v x)
    · rw [RestrictedProduct.mulSingle_eq_of_ne
        (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletionIntegers K)
        (x : v.adicCompletion K) hw]
      exact congrArg (fun u : (w.adicCompletion K)ˣ => (u : w.adicCompletion K))
        (_root_.IdeleGroup.finitePlaceIdele_finiteComponent_of_ne v w x hw)

variable [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
variable [w.asIdeal.LiesOver v.asIdeal]

/-- CFT's contracted finite place is the given place below. -/
theorem finitePlaceBelow_eq_of_liesOver :
    _root_.finitePlaceBelow (K := K) w = v := by
  apply HeightOneSpectrum.ext
  exact (Ideal.over_def w.asIdeal v.asIdeal).symm

/-- The CFT completion map agrees with the canonical map already constructed. -/
theorem completionMap_eq_finitePlaceAdicCompletionMap :
    completionMap v w = _root_.finitePlaceAdicCompletionMap K L v
      ⟨w, finitePlaceBelow_eq_of_liesOver v w⟩ := by
  symm
  apply completionMap_unique v w
  · exact _root_.finitePlaceAdicCompletionMap_continuous K L v _
  · exact _root_.finitePlaceAdicCompletionMap_coe K L v _

/-- Norm transport at one finite place in the frozen Mathlib idele groups. -/
theorem ideleNorm_ofAdicCompletion (u : (w.adicCompletion L)ˣ) :
    ideleNorm K L (NumberField.IdeleGroup.ofAdicCompletion (𝓞 L) L w u) =
      NumberField.IdeleGroup.ofAdicCompletion (𝓞 K) K v (completionNorm v w u) := by
  let W : {W : HeightOneSpectrum (𝓞 L) // _root_.finitePlaceBelow (K := K) W = v} :=
    ⟨w, finitePlaceBelow_eq_of_liesOver v w⟩
  have h := _root_.IdeleGroup.norm_finitePlaceIdele_eq_finitePlaceIdele_normUnits
    (K := K) (L := L) v W u
  rw [← completionMap_eq_finitePlaceAdicCompletionMap v w] at h
  rw [← ideleContinuousEquiv_finitePlaceIdele w u]
  change ideleContinuousEquiv K (_root_.IdeleGroup.norm K L
    ((ideleContinuousEquiv L).symm
      (ideleContinuousEquiv L (_root_.IdeleGroup.finitePlaceIdele w u)))) = _
  rw [ContinuousMulEquiv.symm_apply_apply, h]
  exact ideleContinuousEquiv_finitePlaceIdele v (completionNorm v w u)

/-- The valuation of the completed field norm is the inertia-degree power. -/
theorem completionNorm_valuation (u : (w.adicCompletion L)ˣ) :
    Valued.v (completionNorm v w u : v.adicCompletion K) =
      Valued.v (u : w.adicCompletion L) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  let W : {W : HeightOneSpectrum (𝓞 L) // _root_.finitePlaceBelow (K := K) W = v} :=
    ⟨w, finitePlaceBelow_eq_of_liesOver v w⟩
  have h := FiniteIdeleGroup.localOrder_normUnits K L v W u
  rw [← completionMap_eq_finitePlaceAdicCompletionMap v w] at h
  change -WithZero.log (Valued.v (completionNorm v w u : v.adicCompletion K)) =
    (w.asIdeal.inertiaDeg (𝓞 K) : ℤ) *
      -WithZero.log (Valued.v (u : w.adicCompletion L)) at h
  have hnorm : Valued.v (completionNorm v w u : v.adicCompletion K) ≠ 0 := by simp
  have hu : Valued.v (u : w.adicCompletion L) ≠ 0 := by simp
  rw [← WithZero.exp_log hnorm,
    ← WithZero.exp_log (pow_ne_zero (w.asIdeal.inertiaDeg (𝓞 K)) hu)]
  congr 1
  rw [WithZero.log_pow, nsmul_eq_mul]
  linarith

/-- The norm of a local unit is supported at the base place and remains a local unit. -/
theorem ideleNorm_localUnit (u : (w.adicCompletion L)ˣ) (hu : localUnit w u) :
    ∃ b : (v.adicCompletion K)ˣ, localUnit v b ∧
      ideleNorm K L (NumberField.IdeleGroup.ofAdicCompletion (𝓞 L) L w u) =
        NumberField.IdeleGroup.ofAdicCompletion (𝓞 K) K v b :=
  ⟨completionNorm v w u, completionNorm_localUnit v w u hu,
    ideleNorm_ofAdicCompletion v w u⟩

/-- Uniformizers have local order one in the chosen normalization. -/
theorem uniformizer_valuation :
    Valued.v (ArtinPrimitiveRoots.A1.toLoc w
      (ArtinPrimitiveRoots.A1.KummerProofs.uniformizerUnit w) : w.adicCompletion L) =
      WithZero.exp (-1 : ℤ) := by
  change Valued.v (algebraMap L (w.adicCompletion L)
    (ArtinPrimitiveRoots.A1.KummerProofs.uniformizer w)) = _
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  simpa only [ArtinPrimitiveRoots.A1.KummerProofs.uniformizer,
    Function.comp_apply, Algebra.algebraMap_self_apply,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] using
    (w.valuation_exists_uniformizer L).choose_spec

/-- The norm of a prime uniformizer is the inertia-degree power times a local unit. -/
theorem ideleNorm_uniformizer :
    ∃ b : (v.adicCompletion K)ˣ, localUnit v b ∧
      ideleNorm K L (NumberField.IdeleGroup.ofAdicCompletion (𝓞 L) L w
        (ArtinPrimitiveRoots.A1.toLoc w
          (ArtinPrimitiveRoots.A1.KummerProofs.uniformizerUnit w))) =
        NumberField.IdeleGroup.ofAdicCompletion (𝓞 K) K v
          (ArtinPrimitiveRoots.A1.toLoc v
            (ArtinPrimitiveRoots.A1.KummerProofs.uniformizerUnit v) ^
            w.asIdeal.inertiaDeg (𝓞 K) * b) := by
  obtain ⟨b, hb, hnorm⟩ := uniformizer_unit_factor v
    (completionNorm v w (ArtinPrimitiveRoots.A1.toLoc w
      (ArtinPrimitiveRoots.A1.KummerProofs.uniformizerUnit w)))
    (w.asIdeal.inertiaDeg (𝓞 K)) (by
      rw [completionNorm_valuation v w, uniformizer_valuation])
  refine ⟨b, hb, ?_⟩
  rw [ideleNorm_ofAdicCompletion v w, hnorm]

-- Preserve the original Eisenstein instances in the Lambda interfaces.
attribute [local instance 2000] CyclotomicField.instNumberField

variable {F : Type} [Field F] [NumberField F]

/-- The exact Lambda base place is CFT's contraction for the chosen embedding. -/
theorem basePlace_eq_finitePlaceBelow (ι : E →ₐ[ℚ] F)
    (v : ArtinPrimitiveRoots.A1.FinPlace F) :
    letI : Algebra E F := ι.toRingHom.toAlgebra
    basePlace ι v = _root_.finitePlaceBelow (K := E) v := by
  letI : Algebra E F := ι.toRingHom.toAlgebra
  apply HeightOneSpectrum.ext
  rfl

/-- The frozen residue-degree definition is the inertia degree of the prime. -/
theorem residueDegree_eq_inertiaDeg (ι : E →ₐ[ℚ] F)
    (v : ArtinPrimitiveRoots.A1.FinPlace F) :
    letI : Algebra E F := ι.toRingHom.toAlgebra
    residueDegree ι v = v.asIdeal.inertiaDeg OE := by
  letI : Algebra E F := ι.toRingHom.toAlgebra
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : (basePlace ι v).asIdeal.IsMaximal := (basePlace ι v).isMaximal
  letI : v.asIdeal.LiesOver (basePlace ι v).asIdeal := ⟨rfl⟩
  have h := (Ideal.inertiaDeg_eq_of_isMaximal
    (basePlace ι v).asIdeal v.asIdeal).symm
  have hAlg : Ideal.Quotient.algebraOfLiesOver v.asIdeal (basePlace ι v).asIdeal =
      residueAlgebra ι v := by
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  rw [hAlg] at h
  simpa only [residueDegree] using h

/-- The exact Lambda norm for a chosen Eisenstein embedding. -/
def relativeIdeleNorm (ι : E →ₐ[ℚ] F) :
    NumberField.IdeleGroup (𝓞 F) F →* NumberField.IdeleGroup OE E :=
  letI : Algebra E F := ι.toRingHom.toAlgebra
  ideleNorm E F

theorem relativeIdeleNorm_continuous (ι : E →ₐ[ℚ] F) :
    Continuous (relativeIdeleNorm ι) := by
  letI : Algebra E F := ι.toRingHom.toAlgebra
  exact ideleNorm_continuous E F

theorem relativeIdeleNorm_principal (ι : E →ₐ[ℚ] F) (a : Fˣ) :
    letI : Algebra E F := ι.toRingHom.toAlgebra
    relativeIdeleNorm ι (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a) =
      NumberField.IdeleGroup.unitEmbedding OE E (Units.map (Algebra.norm E) a) := by
  letI : Algebra E F := ι.toRingHom.toAlgebra
  exact ideleNorm_principal E F a

/-- The finite unit specification in the exact frozen Lambda interface. -/
theorem relativeIdeleNorm_unit_norm (ι : E →ₐ[ℚ] F)
    (v : ArtinPrimitiveRoots.A1.FinPlace F) (u : (v.adicCompletion F)ˣ)
    (hu : localUnit v u) :
    ∃ b : ((basePlace ι v).adicCompletion E)ˣ, localUnit (basePlace ι v) b ∧
      relativeIdeleNorm ι (NumberField.IdeleGroup.ofAdicCompletion (𝓞 F) F v u) =
        NumberField.IdeleGroup.ofAdicCompletion OE E (basePlace ι v) b := by
  letI : Algebra E F := ι.toRingHom.toAlgebra
  letI : v.asIdeal.LiesOver (basePlace ι v).asIdeal := ⟨rfl⟩
  exact ideleNorm_localUnit (basePlace ι v) v u hu

/-- The finite uniformizer specification in the exact frozen Lambda interface. -/
theorem relativeIdeleNorm_uniformizer_norm (ι : E →ₐ[ℚ] F)
    (v : ArtinPrimitiveRoots.A1.FinPlace F) :
    ∃ b : ((basePlace ι v).adicCompletion E)ˣ, localUnit (basePlace ι v) b ∧
      relativeIdeleNorm ι (NumberField.IdeleGroup.ofAdicCompletion (𝓞 F) F v
        (ArtinPrimitiveRoots.A1.toLoc v (ArtinPrimitiveRoots.A1.KummerProofs.uniformizerUnit v))) =
        NumberField.IdeleGroup.ofAdicCompletion OE E (basePlace ι v)
          (ArtinPrimitiveRoots.A1.toLoc (basePlace ι v)
            (ArtinPrimitiveRoots.A1.KummerProofs.uniformizerUnit (basePlace ι v)) ^
            residueDegree ι v * b) := by
  letI : Algebra E F := ι.toRingHom.toAlgebra
  letI : v.asIdeal.LiesOver (basePlace ι v).asIdeal := ⟨rfl⟩
  obtain ⟨b, hb, hnorm⟩ := ideleNorm_uniformizer (basePlace ι v) v
  refine ⟨b, hb, ?_⟩
  rw [residueDegree_eq_inertiaDeg ι v]
  exact hnorm

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
