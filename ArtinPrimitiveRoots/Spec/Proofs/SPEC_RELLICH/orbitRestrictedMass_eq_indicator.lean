import ArtinPrimitiveRoots.Spec.Proofs.SPEC_RELLICH.Defs
import Mathlib.LinearAlgebra.Countable
import Mathlib.Basic.Countable.Basic
import Mathlib.Topology.Bases

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff ArtinPrimitiveRoots.A1.Spec.RellichChart
noncomputable section
namespace ArtinPrimitiveRoots.A1.Spec
variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- Indicator multiplication on the measurable orbit saturation of a compact set.
Uses G1_h3_basics and countability of Γ;
provides the representative and contraction consumed by T6_rellich. -/
theorem orbitRestrictedMass_eq_indicator
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (K : Set (X F)) (hK : IsCompact K) :
    MeasurableSet (orbitSaturation F Γ K) ∧
    ∃ I : L2Space F D →L[ℂ] L2Space F D, RellichIndicator Γ D K I := by
  classical
  have hCountF : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  have hCountO : Countable (𝓞 F) :=
    Function.Injective.countable (f := fun x : 𝓞 F => (x : F)) Subtype.val_injective
  letI : Countable (𝓞 F) := hCountO
  have hCountMatrix : Countable (Matrix (Fin 2) (Fin 2) (𝓞 F)) := by
    let f : Matrix (Fin 2) (Fin 2) (𝓞 F) →
        ((𝓞 F × 𝓞 F) × (𝓞 F × 𝓞 F)) :=
      fun A => ((A 0 0, A 0 1), (A 1 0, A 1 1))
    have hf : Function.Injective f := by
      intro A B h
      have h00 : A 0 0 = B 0 0 := congrArg (fun t : (𝓞 F × 𝓞 F) × (𝓞 F × 𝓞 F) => t.1.1) h
      have h01 : A 0 1 = B 0 1 := congrArg (fun t : (𝓞 F × 𝓞 F) × (𝓞 F × 𝓞 F) => t.1.2) h
      have h10 : A 1 0 = B 1 0 := congrArg (fun t : (𝓞 F × 𝓞 F) × (𝓞 F × 𝓞 F) => t.2.1) h
      have h11 : A 1 1 = B 1 1 := congrArg (fun t : (𝓞 F × 𝓞 F) × (𝓞 F × 𝓞 F) => t.2.2) h
      ext i j
      fin_cases i <;> fin_cases j <;> first
        | exact_mod_cast h00
        | exact_mod_cast h01
        | exact_mod_cast h10
        | exact_mod_cast h11
    exact Function.Injective.countable hf
  letI : Countable (Matrix (Fin 2) (Fin 2) (𝓞 F)) := hCountMatrix
  have hCountSL : Countable (SL(2,𝓞 F)) :=
    Function.Injective.countable
      (f := fun x : SL(2,𝓞 F) => (x : Matrix (Fin 2) (Fin 2) (𝓞 F)))
      Subtype.val_injective
  letI : Countable (SL(2,𝓞 F)) := hCountSL
  have hCountΓ : Countable Γ :=
    Function.Injective.countable (f := fun x : Γ => (x : SL(2,𝓞 F)))
      Subtype.val_injective
  letI : Countable Γ := hCountΓ
  haveI : BorelSpace H3 := ⟨rfl⟩
  haveI : SecondCountableTopology (Fin 2 → Fin 2 → ℂ) := inferInstance
  have hCountMatrix2 : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) := by
    change SecondCountableTopology (Fin 2 → Fin 2 → ℂ)
    infer_instance
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) := hCountMatrix2
  have hCountSL2C : SecondCountableTopology (SL(2,ℂ)) := by
    apply (Topology.IsEmbedding.subtypeVal :
      Topology.IsEmbedding (fun g : SL(2,ℂ) => (g : Matrix (Fin 2) (Fin 2) ℂ))).secondCountableTopology
  haveI : SecondCountableTopology (SL(2,ℂ)) := hCountSL2C
  letI : ContinuousMul (SL(2,ℂ)) := ⟨by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)⟩
  have hCountH3 : SecondCountableTopology H3 := by
    letI : SecondCountableTopology (SL(2,ℂ)) := hCountSL2C
    exact Topology.IsOpenQuotientMap.secondCountableTopology
      (QuotientGroup.isOpenQuotientMap_mk (N := SU2))
  haveI : SecondCountableTopology H3 := hCountH3
  haveI : OpensMeasurableSpace H3 := inferInstance
  haveI : OpensMeasurableSpace (X F) := inferInstance
  have hT2 : T2Space (X F) := by
    rcases G1_h3_basics (F := F) with
      ⟨_, _, _, _, _, _, _, _, _, _, _, ⟨e, _, _⟩⟩
    exact e.t2Space
  let S := orbitSaturation F Γ K
  have hS_eq : S = ⋃ γ : Γ, (fun z : X F => (γ : SL(2,𝓞 F)) • z) '' K := by
    ext z
    simp [S, orbitSaturation]
  have hS : MeasurableSet S := by
    letI : T2Space (X F) := hT2
    rw [hS_eq]
    apply MeasurableSet.iUnion
    intro γ
    let g : InfinitePlace F → SL(2,ℂ) :=
      fun w => toInf F (toSLF F (γ : SL(2,𝓞 F))) w
    obtain ⟨e, he, _⟩ := (G2_x_action (F := F)).2.2.2.1 g
    have hmap : (fun z : X F => (γ : SL(2,𝓞 F)) • z) = e := by
      funext z
      change actAtPlaces F g z = e z
      rw [← he z]
    rw [hmap]
    have hcompact : IsCompact (e '' K) := hK.image e.continuous
    have hclosed : IsClosed (e '' K) :=
      @IsCompact.isClosed (X F) _ hT2 (e '' K) hcompact
    exact hclosed.measurableSet
  let hmem (u : L2Space F D) : MemLp (S.indicator (u : X F → ℂ)) 2
      ((volX F).restrict D) := MemLp.indicator hS (Lp.memLp u)
  let ind (u : L2Space F D) : L2Space F D :=
    MemLp.toLp (S.indicator (u : X F → ℂ)) (hmem u)
  have hind_add (u v : L2Space F D) : ind (u + v) = ind u + ind v := by
    apply Lp.ext
    filter_upwards
      [MemLp.coeFn_toLp (hmem (u + v)), MemLp.coeFn_toLp (hmem u),
        MemLp.coeFn_toLp (hmem v), Lp.coeFn_add (ind u) (ind v),
        Lp.coeFn_add u v] with z hsum hu hv hadd hsource
    rw [hsum, hadd]
    change S.indicator ((u + v : L2Space F D) : X F → ℂ) z =
      (((ind u : L2Space F D) : X F → ℂ) z + ((ind v : L2Space F D) : X F → ℂ) z)
    have hu' : ((ind u : L2Space F D) : X F → ℂ) z =
        S.indicator ((u : L2Space F D) : X F → ℂ) z := by simpa [ind] using hu
    have hv' : ((ind v : L2Space F D) : X F → ℂ) z =
        S.indicator ((v : L2Space F D) : X F → ℂ) z := by simpa [ind] using hv
    rw [hu', hv']
    by_cases hz : z ∈ S
    · simp only [Set.indicator_of_mem hz]
      simpa only [Pi.add_apply] using hsource
    · simp [Set.indicator_of_notMem hz]
  have hind_smul (c : ℂ) (u : L2Space F D) : ind (c • u) = c • ind u := by
    apply Lp.ext
    filter_upwards
      [MemLp.coeFn_toLp (hmem (c • u)), MemLp.coeFn_toLp (hmem u),
        Lp.coeFn_smul c (ind u), Lp.coeFn_smul c u] with z hscaled hu htarget hsource
    rw [hscaled, htarget]
    change S.indicator ((c • u : L2Space F D) : X F → ℂ) z =
      c • ((ind u : L2Space F D) : X F → ℂ) z
    have hu' : ((ind u : L2Space F D) : X F → ℂ) z =
        S.indicator ((u : L2Space F D) : X F → ℂ) z := by simpa [ind] using hu
    rw [hu']
    by_cases hz : z ∈ S
    · simp only [Set.indicator_of_mem hz]
      simpa only [Pi.smul_apply] using hsource
    · simp [Set.indicator_of_notMem hz]
  let L : L2Space F D →ₗ[ℂ] L2Space F D :=
    { toFun := ind
      map_add' := hind_add
      map_smul' := hind_smul }
  have hbound : ∀ u : L2Space F D, ‖L u‖ ≤ 1 * ‖u‖ := by
    intro u
    rw [Lp.norm_def, Lp.norm_def, one_mul]
    apply ENNReal.toReal_mono (Lp.eLpNorm_ne_top u)
    calc
      eLpNorm (L u) 2 ((volX F).restrict D) =
          eLpNorm (S.indicator (u : X F → ℂ)) 2 ((volX F).restrict D) := by
        exact eLpNorm_congr_ae (MemLp.coeFn_toLp (hmem u))
      _ ≤ eLpNorm (u : X F → ℂ) 2 ((volX F).restrict D) :=
        eLpNorm_indicator_le (u : X F → ℂ) hS
  let I : L2Space F D →L[ℂ] L2Space F D := L.mkContinuous 1 (by
    intro u
    simpa only [one_mul] using hbound u)
  refine ⟨hS, ⟨I, ?_⟩⟩
  constructor
  · intro u
    simpa [I] using hbound u
  · intro u
    apply (ae_restrict_iff'₀ hD.nullMeasurableSet).1
    filter_upwards [MemLp.coeFn_toLp (hmem u)] with z hz
    simpa [I, L, ind, S] using hz


end ArtinPrimitiveRoots.A1.Spec
