import ArtinPrimitiveRoots.Hecke.Defs
import ArtinPrimitiveRoots.Hecke.Theta.RayUnits
import ClassFieldTheory.AlgebraicNumberTheory.Idele.LocallyCompact

/-!
# Finiteness of local ray quotients

The compiled CFT local-compactness API supplies the finite residue-field fact needed by the
standard finite-quotient instance for powers of the local maximal ideal.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace ArtinPrimitiveRoots.Hecke

open ClassFieldTheory

variable {K : Type} [Field K] [NumberField K]

noncomputable def rayLocalIntegerRingHom (v : HeightOneSpectrum (𝓞 K)) :
    (𝓞 K) →+* v.adicCompletionIntegers K :=
  RingHom.codRestrict (algebraMap (𝓞 K) (v.adicCompletion K))
    (v.adicCompletionIntegers K) (fun x =>
      HeightOneSpectrum.coe_mem_adicCompletionIntegers (K := K) (R := 𝓞 K) v x)

noncomputable def rayLocalIntegralUnitMap (v : HeightOneSpectrum (𝓞 K)) :
    (𝓞 K)ˣ →* (v.adicCompletionIntegers K)ˣ :=
  Units.map (rayLocalIntegerRingHom v).toMonoidHom

noncomputable def rayLocalReductionUnitsHom (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    (𝓞 K)ˣ →* ((v.adicCompletionIntegers K) ⧸
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n)ˣ :=
  (rayLocalHigherUnitMap v n).comp
    ((v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType.symm.toMonoidHom.comp
      (rayLocalIntegralUnitMap v))

theorem rayLocalIntegralUnitMap_subtype (v : HeightOneSpectrum (𝓞 K)) (u : (𝓞 K)ˣ) :
    (v.adicCompletionIntegers K).units.subtype
        ((v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType.symm
          (rayLocalIntegralUnitMap v u)) =
      finitePlaceUnitEmbedding v
        (Units.map (algebraMap (𝓞 K) K).toMonoidHom u) := by
  apply Units.ext
  rfl

theorem rayLocalHigherUnitGroup_mem_iff_reduction_eq_one
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) (u : (𝓞 K)ˣ) :
    finitePlaceUnitEmbedding v (Units.map (algebraMap (𝓞 K) K).toMonoidHom u) ∈
        rayLocalHigherUnitGroup v n ↔ rayLocalReductionUnitsHom v n u = 1 := by
  rw [rayLocalHigherUnitGroup, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, heq⟩
    have hx_eq : x = (v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType.symm
        (rayLocalIntegralUnitMap v u) := by
      apply Subtype.ext
      have hlocal := rayLocalIntegralUnitMap_subtype v u
      have hcomp := heq.trans hlocal.symm
      exact hcomp
    rw [hx_eq] at hx
    exact hx
  · intro h
    refine ⟨(v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType.symm
      (rayLocalIntegralUnitMap v u), h, ?_⟩
    exact rayLocalIntegralUnitMap_subtype v u

theorem finite_rayLocalResidueField (v : HeightOneSpectrum (𝓞 K)) :
    Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) := by
  exact finite_adicCompletion_residueField K v

theorem finite_rayLocalMaximalIdealQuotient (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Finite ((v.adicCompletionIntegers K) ⧸
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n) := by
  haveI : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) :=
    finite_rayLocalResidueField v
  exact IsLocalRing.instFiniteQuotientIdealHPowNatMaximalIdealOfIsNoetherianRingOfResidueField
    (R := v.adicCompletionIntegers K) n

theorem finite_rayLocalMaximalIdealQuotientUnits (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Finite (((v.adicCompletionIntegers K) ⧸
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n)ˣ) := by
  let Q := (v.adicCompletionIntegers K) ⧸
    (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n
  letI : Finite Q := finite_rayLocalMaximalIdealQuotient v n
  exact Finite.of_injective (fun u : Qˣ => (u : Q)) (fun a b h => Units.ext h)

theorem finiteIndex_rayLocalReductionKernel (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    (rayLocalReductionUnitsHom v n).ker.FiniteIndex := by
  let Q := (v.adicCompletionIntegers K) ⧸
    (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n
  haveI : Finite Qˣ := finite_rayLocalMaximalIdealQuotientUnits v n
  haveI : Finite (rayLocalReductionUnitsHom v n).range :=
    Finite.of_injective (fun x => (x : Qˣ)) Subtype.val_injective
  infer_instance

noncomputable def rayIntegralReductionHom (m : RayClassModulus K) :
    (𝓞 K)ˣ →* ∀ v : {v : HeightOneSpectrum (𝓞 K) // v ∈ m.finitePart.support},
      ((v.1.adicCompletionIntegers K) ⧸
        (IsLocalRing.maximalIdeal (v.1.adicCompletionIntegers K)) ^ m.finitePart v.1)ˣ :=
  MonoidHom.pi fun v => rayLocalReductionUnitsHom v.1 (m.finitePart v.1)

theorem finite_rayIntegralReductionTarget (m : RayClassModulus K) :
    Finite (∀ v : {v : HeightOneSpectrum (𝓞 K) // v ∈ m.finitePart.support},
      ((v.1.adicCompletionIntegers K) ⧸
        (IsLocalRing.maximalIdeal (v.1.adicCompletionIntegers K)) ^ m.finitePart v.1)ˣ) := by
  classical
  letI : ∀ v : {v : HeightOneSpectrum (𝓞 K) // v ∈ m.finitePart.support},
      Finite (((v.1.adicCompletionIntegers K) ⧸
        (IsLocalRing.maximalIdeal (v.1.adicCompletionIntegers K)) ^ m.finitePart v.1)ˣ) :=
    fun v => finite_rayLocalMaximalIdealQuotientUnits v.1 (m.finitePart v.1)
  infer_instance

theorem finiteIndex_rayIntegralReductionKernel (m : RayClassModulus K) :
    (rayIntegralReductionHom m).ker.FiniteIndex := by
  let Q := ∀ v : {v : HeightOneSpectrum (𝓞 K) // v ∈ m.finitePart.support},
      ((v.1.adicCompletionIntegers K) ⧸
        (IsLocalRing.maximalIdeal (v.1.adicCompletionIntegers K)) ^ m.finitePart v.1)ˣ
  haveI : Finite Q := finite_rayIntegralReductionTarget m
  haveI : Finite (rayIntegralReductionHom m).range :=
    Finite.of_injective (fun x => (x : Q)) Subtype.val_injective
  infer_instance

theorem rayCongruentIntegralUnits_eq_reductionKernel [IsTotallyComplex K]
    (m : RayClassModulus K) :
    rayCongruentIntegralUnits m = (rayIntegralReductionHom m).ker := by
  classical
  ext u
  change IsRayCongruent m (Units.map (algebraMap (𝓞 K) K).toMonoidHom u) ↔
    rayIntegralReductionHom m u = 1
  rw [IsRayCongruent, rayClassModulus_infinitePart_eq_empty (K := K) m]
  constructor
  · rintro ⟨hfin, hinf⟩
    apply funext
    intro v
    exact (rayLocalHigherUnitGroup_mem_iff_reduction_eq_one
      v.1 (m.finitePart v.1) u).mp (hfin v.1 v.2)
  · intro h
    constructor
    · intro v hv
      have hval := congrArg (fun f => f ⟨v, hv⟩) h
      have hred : rayLocalReductionUnitsHom v (m.finitePart v) u = 1 := by
        simpa [rayIntegralReductionHom] using hval
      exact (rayLocalHigherUnitGroup_mem_iff_reduction_eq_one
        v (m.finitePart v) u).mpr hred
    · intro v hv
      simp at hv

theorem rayCongruentIntegralUnits_finiteIndex [IsTotallyComplex K]
    (m : RayClassModulus K) : (rayCongruentIntegralUnits m).FiniteIndex := by
  rw [rayCongruentIntegralUnits_eq_reductionKernel m]
  exact finiteIndex_rayIntegralReductionKernel m


end ArtinPrimitiveRoots.Hecke

end
