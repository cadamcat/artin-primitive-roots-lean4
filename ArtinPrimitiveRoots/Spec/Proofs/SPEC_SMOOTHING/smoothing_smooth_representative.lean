import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SMOOTHING.radialKernel_compact_control
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SMOOTHING.param_deriv_integral_formula
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SMOOTHING.localLiftCLM

set_option autoImplicit false
open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff ENNReal

noncomputable section
namespace ArtinPrimitiveRoots.A1.Spec
variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- Smoothing every quotient L2 vector gives a smooth representative in positive coordinates.
Guide: `sol-thin-spec/PROOFS.md:408`. Uses `radialKernel_compact_control`,
`param_deriv_integral_formula`, `localLiftCLM`, and frozen `G3_volume`, `T1_l2`.
Supplies the smoothness conjunct of frozen `S1_smoothing`. -/
theorem smoothing_smooth_representative (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (k₀ : ℝ → ℝ) (hkSmooth : ContDiff ℝ ∞ k₀)
    (hkSupport : {t | k₀ t ≠ 0} ⊆ Set.Icc 1 (1 + 1 / 100))
    (u : L2Space F D) :
    IsSmoothX F (smoothingOperator F k₀ (l2Lift F Γ D u)) := by
  classical
  have hsecondX : SecondCountableTopology (X F) := by
    rcases G1_h3_basics (F := F) with
      ⟨_, _, _, _, _, _, _, _, _, _, _, ⟨e, _, _⟩⟩
    exact e.symm.secondCountableTopology
  have hT2X : T2Space (X F) := by
    rcases G1_h3_basics (F := F) with
      ⟨_, _, _, _, _, _, _, _, _, _, _, ⟨e, _, _⟩⟩
    exact e.t2Space
  have hsecondH3 : SecondCountableTopology H3 := by
    letI : SecondCountableTopology (X F) := hsecondX
    let w₀ : InfinitePlace F := Classical.choice inferInstance
    let c : H3 → X F := fun z _ => z
    let eval : X F → H3 := fun z => z w₀
    have hc : Continuous c := by
      change Continuous (fun z : H3 => fun _ : InfinitePlace F => z)
      exact continuous_pi fun _ => continuous_id
    have heval : Continuous eval := continuous_apply w₀
    have hleft : Function.LeftInverse eval c := by
      intro z
      simp [eval, c]
    exact hleft.isEmbedding heval hc |>.secondCountableTopology
  letI : SecondCountableTopology H3 := hsecondH3
  letI : BorelSpace H3 := ⟨rfl⟩
  letI : Countable (InfinitePlace F) := Finite.to_countable
  letI : BorelSpace (X F) := by
    change BorelSpace (∀ w : InfinitePlace F, H3)
    exact Pi.borelSpace
  letI : T2Space (X F) := hT2X
  change ContDiffOn ℝ ∞
    (fun p => smoothingOperator F k₀ (l2Lift F Γ D u) (ptX F p)) (posSet F)
  apply contDiffOn_of_locally_contDiffOn
  intro p hp
  let K : Set (Coord F) := {p}
  have hK : IsCompact K := by simp [K]
  have hKpos : K ⊆ posSet F := by
    intro q hq
    rw [Set.mem_singleton_iff.mp hq]
    exact hp
  obtain ⟨U, W, hU, hKU, hUpos, hW, hcontrol⟩ :=
    radialKernel_compact_control (F := F) k₀ hkSmooth hkSupport K hK hKpos
  have hpU : p ∈ U := hKU (by simp [K])
  have hWmeas : MeasurableSet W := hW.isClosed.measurableSet
  have hWvol : (volX F) W < ⊤ := (G3_volume (F := F)).2.2.1 W hW
  letI : IsFiniteMeasure ((volX F).restrict W) := ⟨by
    simpa using hWvol
  ⟩
  obtain ⟨T, hTbound, hTrep⟩ := localLiftCLM (F := F) Γ D hD W hW
  have hTInt : Integrable (T u) ((volX F).restrict W) :=
    (Lp.memLp (T u)).integrable (by norm_num : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞))
  have hLiftEq : T u =ᵐ[(volX F).restrict W] l2Lift F Γ D u := by
    filter_upwards [hTrep u, ae_restrict_mem hWmeas] with z hrep hz
    exact hrep
  have hLiftInt : Integrable (l2Lift F Γ D u) ((volX F).restrict W) :=
    hTInt.congr hLiftEq
  have hLiftMeas : AEStronglyMeasurable (l2Lift F Γ D u) (volX F) :=
    ((T1_l2 (F := F) Γ D hD).1 u).1
  have hsmooth := (param_deriv_integral_formula (F := F) k₀ U hU hUpos W hW
    hcontrol (l2Lift F Γ D u) hLiftMeas hLiftInt).1
  refine ⟨U, hU, hpU, ?_⟩
  exact hsmooth.mono fun q hq => hq.2

end ArtinPrimitiveRoots.A1.Spec
