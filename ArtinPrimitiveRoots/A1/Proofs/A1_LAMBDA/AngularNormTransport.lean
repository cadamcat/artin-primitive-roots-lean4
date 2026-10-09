import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.FiniteNormTransport
import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings

/-! Archimedean single-place norm transport and its angular specification.
The component argument and compatible complex equivalences use the prebuilt
ClassFieldTheory norm APIs (Apache-2.0). -/

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical Topology NumberField.LiesOver
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_lambda_sol

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]

/-- The topology comparison preserves archimedean single-place ideles. -/
theorem ideleContinuousEquiv_infinitePlaceIdele
    (v : InfinitePlace K) (x : v.Completionˣ) :
    ideleContinuousEquiv K (_root_.IdeleGroup.infinitePlaceIdele v x) =
      NumberField.IdeleGroup.ofCompletion (𝓞 K) K v x := by
  apply Units.ext
  apply Prod.ext
  · funext w
    change ((_root_.IdeleGroup.infinitePlaceIdele v x).1 : InfiniteAdeleRing K) w =
      (Pi.mulSingle v (x : v.Completion)) w
    by_cases hw : w = v
    · subst w
      rw [Pi.mulSingle_eq_same]
      exact congrArg (fun u : v.Completionˣ => (u : v.Completion))
        (_root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_same v x)
    · rw [Pi.mulSingle_eq_of_ne hw]
      exact congrArg (fun u : w.Completionˣ => (u : w.Completion))
        (_root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne v w x hw)
  · apply RestrictedProduct.ext
    intro w
    rfl

variable [Algebra K L]

/-- The norm of an archimedean one-place idele is the completed local norm
supported at the contracted place. -/
theorem norm_infinitePlaceIdele (w : InfinitePlace L) (x : w.Completionˣ) :
    let v := _root_.infinitePlaceBelow (K := K) w
    letI : w.LiesOver v := ⟨rfl⟩
    _root_.IdeleGroup.norm K L (_root_.IdeleGroup.infinitePlaceIdele w x) =
      _root_.IdeleGroup.infinitePlaceIdele v
        (LocalFieldTheory.normUnits v.Completion w.Completion x) := by
  let v := _root_.infinitePlaceBelow (K := K) w
  let : w.LiesOver v := ⟨rfl⟩
  let W₀ : {W : InfinitePlace L // _root_.infinitePlaceBelow (K := K) W = v} :=
    ⟨w, rfl⟩
  apply Prod.ext
  · apply ContinuousMulEquiv.piUnits.injective
    funext r
    change _root_.IdeleGroup.infiniteComponent r
        (_root_.IdeleGroup.norm K L (_root_.IdeleGroup.infinitePlaceIdele w x)) =
      _root_.IdeleGroup.infiniteComponent r
        (_root_.IdeleGroup.infinitePlaceIdele v
          (LocalFieldTheory.normUnits v.Completion w.Completion x))
    by_cases hr : r = v
    · subst r
      rw [_root_.IdeleGroup.infiniteComponent_norm_eq_prod,
        _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_same]
      rw [Finset.prod_eq_single W₀]
      · rw [_root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_same]
      · intro W _ hW
        have hWw : W.1 ≠ w := fun h => hW (Subtype.ext h)
        rw [_root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne w W.1 x hWw,
          map_one]
      · simp
    · rw [_root_.IdeleGroup.infiniteComponent_norm_eq_prod,
        _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne v r _ hr]
      apply Finset.prod_eq_one
      intro W _
      have hWw : W.1 ≠ w := by
        intro h
        apply hr
        exact W.2.symm.trans (congrArg (_root_.infinitePlaceBelow (K := K)) h)
      rw [_root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne w W.1 x hWw,
        map_one]
  · apply Subtype.ext
    funext r
    change _root_.IdeleGroup.finiteComponent r
        (_root_.IdeleGroup.norm K L (_root_.IdeleGroup.infinitePlaceIdele w x)) =
      _root_.IdeleGroup.finiteComponent r
        (_root_.IdeleGroup.infinitePlaceIdele v
          (LocalFieldTheory.normUnits v.Completion w.Completion x))
    rw [_root_.IdeleGroup.finiteComponent_norm_eq_prod,
      _root_.IdeleGroup.infinitePlaceIdele_finiteComponent]
    apply Finset.prod_eq_one
    intro W _
    rw [_root_.IdeleGroup.infinitePlaceIdele_finiteComponent, map_one]

/-- The exact Mathlib norm preserves the archimedean one-place support. -/
theorem ideleNorm_ofCompletion (w : InfinitePlace L) (x : w.Completionˣ) :
    let v := _root_.infinitePlaceBelow (K := K) w
    letI : w.LiesOver v := ⟨rfl⟩
    ideleNorm K L (NumberField.IdeleGroup.ofCompletion (𝓞 L) L w x) =
      NumberField.IdeleGroup.ofCompletion (𝓞 K) K v
        (LocalFieldTheory.normUnits v.Completion w.Completion x) := by
  rw [← ideleContinuousEquiv_infinitePlaceIdele w x]
  change ideleContinuousEquiv K (_root_.IdeleGroup.norm K L
    ((ideleContinuousEquiv L).symm
      (ideleContinuousEquiv L (_root_.IdeleGroup.infinitePlaceIdele w x)))) = _
  rw [ContinuousMulEquiv.symm_apply_apply, norm_infinitePlaceIdele]
  exact ideleContinuousEquiv_infinitePlaceIdele _ _

omit [NumberField K] [NumberField L] in
/-- Between complex completions the local norm preserves the complex
coordinate or conjugates it, according to the chosen embeddings. -/
theorem complex_norm_coordinates (v : InfinitePlace K) (w : InfinitePlace L)
    [w.LiesOver v] (hv : v.IsComplex) (hw : w.IsComplex) :
    (∀ z : ℂˣ, LocalFieldTheory.normUnits v.Completion w.Completion
        (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toMonoidHom z) =
      Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm.toMonoidHom z) ∨
    (∀ z : ℂˣ, LocalFieldTheory.normUnits v.Completion w.Completion
        (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toMonoidHom z) =
      Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm.toMonoidHom
        (Units.map (starRingAut (R := ℂ)).toMonoidHom z)) := by
  let eBase := InfinitePlace.Completion.ringEquivComplexOfIsComplex hv
  rcases InfinitePlace.LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq
    w v with hEmbedding | hConjugate
  · let eExtension := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
    let : NumberField.ComplexEmbedding.LiesOver w.embedding v.embedding := ⟨hEmbedding⟩
    let : NumberField.ComplexEmbedding.LiesOver
        (InfinitePlace.Completion.extensionEmbedding w)
        (InfinitePlace.Completion.extensionEmbedding v) :=
      InfinitePlace.Completion.liesOver_extensionEmbedding w v
    have hCompatible : RingHom.comp (algebraMap ℂ ℂ) eBase.toRingHom =
        RingHom.comp eExtension.toRingHom (algebraMap v.Completion w.Completion) := by
      ext a
      change InfinitePlace.Completion.extensionEmbedding v a =
        InfinitePlace.Completion.extensionEmbedding w
          ((algebraMap v.Completion w.Completion) a)
      exact (InfinitePlace.Completion.liesOver_extensionEmbedding_apply w (v := v)).symm
    left
    intro z
    apply (Units.mapEquiv eBase.toMulEquiv).injective
    apply Units.ext
    have h := congrArg (fun u : ℂˣ => (u : ℂ))
      (LocalClassFieldTheory.normUnits_map_ringEquiv eBase eExtension hCompatible
        (Units.map eExtension.symm.toMonoidHom z))
    simpa [LocalFieldTheory.normUnits_apply_coe, Algebra.norm_self,
      eBase, eExtension] using h
  · let eExtension := (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).trans
      (starRingAut (R := ℂ))
    let : NumberField.ComplexEmbedding.LiesOver
        (ComplexEmbedding.conjugate w.embedding) v.embedding := ⟨hConjugate⟩
    let : NumberField.ComplexEmbedding.LiesOver
        (ComplexEmbedding.conjugate (InfinitePlace.Completion.extensionEmbedding w))
        (InfinitePlace.Completion.extensionEmbedding v) :=
      InfinitePlace.Completion.liesOver_conjugate_extensionEmbedding w v
    have hCompatible : RingHom.comp (algebraMap ℂ ℂ) eBase.toRingHom =
        RingHom.comp eExtension.toRingHom (algebraMap v.Completion w.Completion) := by
      ext a
      simp [eBase, eExtension, ← ComplexEmbedding.conjugate_coe_eq]
    right
    intro z
    apply (Units.mapEquiv eBase.toMulEquiv).injective
    apply Units.ext
    have h := congrArg (fun u : ℂˣ => (u : ℂ))
      (LocalClassFieldTheory.normUnits_map_ringEquiv eBase eExtension hCompatible
        (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toMonoidHom z))
    simpa [LocalFieldTheory.normUnits_apply_coe, Algebra.norm_self,
      eBase, eExtension] using h

/-- Complex conjugation inverts the normalized angular coordinate. -/
theorem conjugate_angular_coordinate (z : ℂˣ) :
    star (z : ℂ) / ‖star (z : ℂ)‖ = ((z : ℂ) / ‖(z : ℂ)‖)⁻¹ := by
  rw [norm_star, inv_div]
  apply (div_eq_div_iff (by exact_mod_cast norm_ne_zero_iff.mpr z.ne_zero) z.ne_zero).mpr
  simpa [Complex.star_def, pow_two] using Complex.conj_mul' (z : ℂ)

-- Keep the number-field instance used by the frozen Eisenstein interfaces.
attribute [local instance 2000] CyclotomicField.instNumberField

variable {F : Type} [Field F] [NumberField F]

/-- The angular specification for the exact Lambda relative idele norm. -/
theorem relativeIdeleNorm_angular_norm (D : ArtinPrimitiveRoots.A1.FieldData F)
    (ι : E →ₐ[ℚ] F) (χ : LambdaChar E) (hχ : simpleAngularType χ)
    (w : InfinitePlace F) :
    ∃ m : ℤ, (m = 1 ∨ m = -1) ∧ ∀ z : ℂˣ,
      ((χ (QuotientGroup.mk (relativeIdeleNorm ι
        (NumberField.IdeleGroup.ofCompletion (𝓞 F) F w
          (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
            (D.isTotallyComplex.isComplex w)).symm.toMonoidHom z)))) : ℂˣ) : ℂ) =
        ((z : ℂ) / ‖(z : ℂ)‖) ^ m := by
  let : Algebra E F := ι.toRingHom.toAlgebra
  let v := _root_.infinitePlaceBelow (K := E) w
  let : w.LiesOver v := ⟨rfl⟩
  have hv : v.IsComplex :=
    (IsCyclotomicExtension.Rat.isTotallyComplex (n := 3) E (by norm_num)).isComplex v
  let hw := D.isTotallyComplex.isComplex w
  obtain ⟨m, hm, hformula⟩ := hχ v hv
  have hsingle (z : ℂˣ) :
      relativeIdeleNorm ι (NumberField.IdeleGroup.ofCompletion (𝓞 F) F w
        (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toMonoidHom z)) =
      NumberField.IdeleGroup.ofCompletion OE E v
        (LocalFieldTheory.normUnits v.Completion w.Completion
          (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toMonoidHom z)) :=
    ideleNorm_ofCompletion w _
  rcases complex_norm_coordinates v w hv hw with hnorm | hnorm
  · refine ⟨m, hm, ?_⟩
    intro z
    rw [hsingle z, hnorm z]
    exact hformula z
  · refine ⟨-m, ?_, ?_⟩
    · rcases hm with hm | hm <;> simp [hm]
    · intro z
      rw [hsingle z, hnorm z]
      change ((infiniteComponent χ v (Units.map
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm.toMonoidHom
          (Units.map (starRingAut (R := ℂ)).toMonoidHom z)) : ℂˣ) : ℂ) = _
      rw [hformula]
      change (star (z : ℂ) / ‖star (z : ℂ)‖) ^ m = _
      rw [conjugate_angular_coordinate, inv_zpow, zpow_neg]

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
