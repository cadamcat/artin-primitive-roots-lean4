import ArtinPrimitiveRoots.A1.Proofs.A1_FOURIER.Defs
import ArtinPrimitiveRoots.Proofs.a2_bridges_impl2.FiniteRadial
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.Pi

/-!
# A1-FOURIER part `a1_fourier_tensor_integrable` (IMPL)

Continuity and integrability of tensor sums for every Haar measure on `F_S`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- A tensor sum is continuous and integrable for every additive Haar measure on `F_S`.

Proof hint: by Haar uniqueness (`MeasureTheory.Measure.isAddHaarMeasure_eq_smul`; `F_S` is
locally compact, second countable) reduce to the product measure
`(Measure.pi μ_v).prod (Measure.pi volume)` (product of Haar measures is Haar; compare the proof
of `a2_probe_sol.schwartz_tensor_fourier` and `covol_sFS_prod_eq_borel` in `A1/SLattice.lean`
for the Borel = product σ-algebra bridge). Each tensor is a product of an integrable function of
`x.1` (continuous, compact support) and of `x.2` (`SchwartzMap.integrable`); use
`Integrable.mul_prod` and `integrable_finset_sum`.
Used by: the glue of `SData.poisson` (`A1/SLattice.lean`). -/
theorem a1_fourier_tensor_integrable (S : SData F CE condη)
    {mS : MeasurableSpace S.FS} [BorelSpace S.FS]
    (g : S.FS → ℂ) (hg : S.IsFSTensorSum g)
    (μ : Measure S.FS) [μ.IsAddHaarMeasure] :
    Continuous g ∧ Integrable g μ := by
  classical
  rcases hg with ⟨n, φ, Φ, hφ, hrepr⟩

  have hcont : Continuous g := by
    rw [funext hrepr]
    apply continuous_finsetSum
    intro i hi
    apply Continuous.mul
    · apply continuous_finsetProd
      intro v hv
      exact (hφ i v).1.comp ((continuous_apply v).comp continuous_fst)
    · exact (Φ i).continuous.comp continuous_snd

  letI : ∀ v : S.Sf, ProperSpace (v.1.adicCompletion F) := fun v =>
    ArtinPrimitiveRoots.A2.bridgeFin_properSpace v.1
  letI : ∀ v : S.Sf, MeasurableSpace (v.1.adicCompletion F) := fun _ => borel _
  letI : ∀ v : S.Sf, BorelSpace (v.1.adicCompletion F) := fun _ => ⟨rfl⟩
  let νfin : ∀ v : S.Sf, Measure (v.1.adicCompletion F) := fun _ => Measure.addHaar
  letI : ∀ v : S.Sf, Measure.IsAddHaarMeasure (νfin v) := fun _ => by
    dsimp [νfin]
    infer_instance
  letI : ∀ v : S.Sf, SigmaFinite (νfin v) := fun _ => by
    apply Measure.IsAddHaarMeasure.sigmaFinite

  let νarch : Measure (InfinitePlace F → ℂ) :=
    Measure.pi fun _ : InfinitePlace F => (volume : Measure ℂ)
  have hνfin : Measure.IsAddHaarMeasure (Measure.pi νfin) := by
    infer_instance
  have hνarch : Measure.IsAddHaarMeasure νarch := by
    dsimp [νarch]
    infer_instance

  let m0 : MeasurableSpace S.FS := Prod.instMeasurableSpace
  have hmS : mS = borel S.FS := by
    letI : MeasurableSpace S.FS := mS
    exact BorelSpace.measurable_eq
  have hm0 : m0 = borel S.FS := by
    letI : MeasurableSpace S.FS := m0
    letI : BorelSpace S.FS := inferInstance
    exact BorelSpace.measurable_eq
  have hB0 := by
    letI : MeasurableSpace S.FS := m0
    exact (show BorelSpace S.FS from ⟨hm0⟩)
  have hBm := by
    letI : MeasurableSpace S.FS := mS
    exact (show BorelSpace S.FS from ⟨hmS⟩)
  have hOpen0 := by
    letI : MeasurableSpace S.FS := m0
    letI : BorelSpace S.FS := hB0
    exact (inferInstance : OpensMeasurableSpace S.FS)
  have hOpenM := by
    letI : MeasurableSpace S.FS := mS
    letI : BorelSpace S.FS := hBm
    exact (inferInstance : OpensMeasurableSpace S.FS)

  let ν0 : @Measure S.FS m0 := (Measure.pi νfin).prod νarch
  have hν0 : @Measure.IsAddHaarMeasure S.FS _ _ m0 ν0 := by
    letI : MeasurableSpace S.FS := m0
    letI : BorelSpace S.FS := hB0
    letI : Measure.IsAddHaarMeasure (Measure.pi νfin) := hνfin
    letI : Measure.IsAddHaarMeasure νarch := hνarch
    dsimp [ν0, m0]
    infer_instance

  let e : @MeasurableEquiv S.FS S.FS m0 mS :=
    @MeasurableEquiv.mk S.FS S.FS m0 mS (Equiv.refl S.FS)
      (@Continuous.measurable S.FS S.FS _ m0 hOpen0 _ mS hBm id continuous_id)
      (@Continuous.measurable S.FS S.FS _ mS hOpenM _ m0 hB0 id continuous_id)
  let eAdd : S.FS ≃+ S.FS := AddEquiv.refl S.FS
  letI : MeasurableSpace S.FS := mS
  letI : BorelSpace S.FS := hBm
  let ν : @Measure S.FS mS := @Measure.map S.FS S.FS m0 mS e ν0
  have hν : @Measure.IsAddHaarMeasure S.FS _ _ mS ν := by
    change @Measure.IsAddHaarMeasure S.FS _ _ mS
      (@Measure.map S.FS S.FS m0 mS (eAdd : S.FS → S.FS) ν0)
    exact @AddEquiv.isAddHaarMeasure_map S.FS m0 _ _ ν0 hν0 hB0
      (inferInstance : ContinuousAdd S.FS) S.FS _ _ mS hBm
      (inferInstance : IsTopologicalAddGroup S.FS) eAdd continuous_id continuous_id

  have hpure (i : Fin n) :
      Integrable
        (fun x : S.FS => (∏ v : S.Sf, φ i v (x.1 v)) * Φ i x.2) ν0 := by
    have hfinite : Integrable
        (fun x : ∀ v : S.Sf, v.1.adicCompletion F =>
          ∏ v : S.Sf, φ i v (x v)) (Measure.pi νfin) := by
      apply Integrable.fintype_prod_dep
      intro v
      exact (hφ i v).1.integrable_of_hasCompactSupport (hφ i v).2.1
    have harch : Integrable (Φ i) νarch := by
      rw [show νarch = Measure.pi (fun _ : InfinitePlace F => (volume : Measure ℂ)) from rfl]
      rw [← volume_pi]
      exact (Φ i).integrable
    change Integrable
      (fun x : (∀ v : S.Sf, v.1.adicCompletion F) × (InfinitePlace F → ℂ) =>
        (∏ v : S.Sf, φ i v (x.1 v)) * Φ i x.2)
      ((Measure.pi νfin).prod νarch)
    exact hfinite.mul_prod harch

  have hsum0 : Integrable
      (fun x : S.FS => ∑ i : Fin n, (∏ v : S.Sf, φ i v (x.1 v)) * Φ i x.2) ν0 := by
    apply integrable_finsetSum Finset.univ
    intro i hi
    exact hpure i

  have hsum0g : Integrable g ν0 := by
    convert hsum0 using 1
    funext x
    exact hrepr x
  have hsum : Integrable g ν := by
    change Integrable g (@Measure.map S.FS S.FS m0 mS e ν0)
    exact (integrable_map_equiv e g).2 (by
      convert hsum0g using 1
      funext x
      rfl)

  letI : MeasurableSpace S.FS := mS
  letI : BorelSpace S.FS := hBm
  letI : Measure.IsAddHaarMeasure ν := hν
  have hmeasure : μ = Measure.addHaarScalarFactor μ ν • ν :=
    Measure.isAddLeftInvariant_eq_smul μ ν
  refine ⟨hcont, ?_⟩
  rw [hmeasure]
  exact hsum.smul_measure_nnreal

end ArtinPrimitiveRoots.A1
