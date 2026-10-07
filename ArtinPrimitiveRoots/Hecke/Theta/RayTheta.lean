import ArtinPrimitiveRoots.Hecke.Theta.RayArithmetic
import ArtinPrimitiveRoots.Hecke.Theta.FiniteFEPair
import ArtinPrimitiveRoots.Hecke.Theta.PoissonLattice
import DedekindResidue.CompletedZeta.MellinAgreement

/-!
Ray class theta series on integral ideal lattices.

The analytic ingredients are from AINTLIB's `DedekindResidue.CompletedZeta` project
(Apache-2.0); this file supplies the ray residue weight and its affine-lattice decomposition.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ClassFieldTheory
open NumberField.mixedEmbedding
open NumberField.InfinitePlace
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open DedekindResidue
open ArtinPrimitiveRoots.Hecke.Theta
open MeasureTheory
open TopologicalSpace
open scoped NumberField nonZeroDivisors Real Classical FourierTransform RealInnerProductSpace

noncomputable section

namespace ArtinPrimitiveRoots.Hecke

/-- Poisson summation for a translated anisotropic Gaussian, using AINTLIB's Fourier transform
and comparison bounds together with the translated lattice formula in `PoissonLattice`. -/
theorem weightedGaussian_translate_transform {ι : Type*} [Fintype ι]
    (L : Submodule ℤ (EuclideanSpace ℝ ι)) [DiscreteTopology L] [IsZLattice ℝ L]
    (r : EuclideanSpace ℝ ι) {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {a B : ℝ} (ha : 0 < a) (hca : ∀ i, a ≤ c i)
    (hB : 0 < B) (hcB : ∀ i, c i ≤ B) :
    ∑' v : L, weightedGaussianCM c (r + (v : EuclideanSpace ℝ ι)) =
      (ZLattice.covolume L volume)⁻¹ •
        ∑' w : ArtinPrimitiveRoots.Hecke.Theta.dualZLattice L,
          Real.fourierChar (⟪r, (w : EuclideanSpace ℝ ι)⟫) •
            ((Real.sqrt (∏ i, c i))⁻¹ •
              weightedGaussianCM (fun i => (c i)⁻¹) (w : EuclideanSpace ℝ ι)) := by
  let g := weightedGaussianCM (ι := ι) c
  have hnorm : ∀ K : Compacts (EuclideanSpace ℝ ι), Summable fun v : L =>
      ‖((g.comp (ContinuousMap.addRight r)).comp
          (ContinuousMap.addRight (v : EuclideanSpace ℝ ι))).restrict (K : Set _)‖ := by
    intro K
    let K' : Compacts (EuclideanSpace ℝ ι) :=
      ⟨(fun x : EuclideanSpace ℝ ι => r + x) '' (K : Set _),
        K.2.image (continuous_const.add continuous_id)⟩
    have hbase := summable_norm_restrict_weightedGaussianCM L ha hca K'
    apply hbase.of_norm_bounded
    intro v
    have hbound :
        ‖((g.comp (ContinuousMap.addRight r)).comp
            (ContinuousMap.addRight (v : EuclideanSpace ℝ ι))).restrict (K : Set _)‖ ≤
          ‖(g.comp (ContinuousMap.addRight (v : EuclideanSpace ℝ ι))).restrict
            (K' : Set _)‖ := by
      apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
      intro x
      have hx' : (r + x.1) ∈ (K' : Set _) := ⟨x.1, x.2, rfl⟩
      have hval :
          ((g.comp (ContinuousMap.addRight r)).comp
            (ContinuousMap.addRight (v : EuclideanSpace ℝ ι))).restrict (K : Set _) x =
          (g.comp (ContinuousMap.addRight (v : EuclideanSpace ℝ ι))).restrict
          (K' : Set _) ⟨r + x.1, hx'⟩ := by
        change g ((x.1 + (v : EuclideanSpace ℝ ι)) + r) =
          g ((r + x.1) + (v : EuclideanSpace ℝ ι))
        congr 1
        abel
      rw [hval]
      exact ContinuousMap.norm_coe_le_norm
        ((g.comp (ContinuousMap.addRight (v : EuclideanSpace ℝ ι))).restrict
          (K' : Set _)) ⟨r + x.1, hx'⟩
    simpa only [norm_norm] using hbound
  have hbase : Summable fun w : ArtinPrimitiveRoots.Hecke.Theta.dualZLattice L =>
      𝓕 (⇑g) (w : EuclideanSpace ℝ ι) := by
    simpa only [ArtinPrimitiveRoots.Hecke.Theta.dualZLattice,
      DedekindResidue.dualZLattice] using
      DedekindResidue.summable_fourier_weightedGaussianCM L hc hB hcB
  have hsum : Summable fun w : ArtinPrimitiveRoots.Hecke.Theta.dualZLattice L =>
      𝓕 (⇑(g.comp (ContinuousMap.addRight r))) (w : EuclideanSpace ℝ ι) := by
    apply Summable.of_norm
    have hbase := hbase.norm
    refine hbase.congr (fun w => ?_)
    have hshift :
        𝓕 (⇑(g.comp (ContinuousMap.addRight r))) (w : EuclideanSpace ℝ ι) =
          Real.fourierChar (⟪r, (w : EuclideanSpace ℝ ι)⟫) •
            𝓕 (⇑g) (w : EuclideanSpace ℝ ι) := by
      change 𝓕 (fun y : EuclideanSpace ℝ ι => g (y + r))
        (w : EuclideanSpace ℝ ι) = _
      exact congrFun (fourier_translate (⇑g) r) (w : EuclideanSpace ℝ ι)
    rw [hshift]
    simp
  rw [ArtinPrimitiveRoots.Hecke.Theta.tsum_eq_tsum_fourier_zlattice_translate_phase
    L r hnorm hsum]
  congr 1
  apply tsum_congr
  intro w
  rw [fourier_weightedGaussianCM hc]

variable {K : Type*} [Field K] [NumberField K]

local instance rayModulusQuotientFinite (m : RayClassModulus K) :
    Finite ((𝓞 K) ⧸ modulusIdeal m) := by
  letI : NeZero (modulusIdeal m) := ⟨modulusIdeal_ne_bot m⟩
  infer_instance

local instance rayAcceptedResiduesFinite (m : RayClassModulus K) :
    Finite (acceptedResidues m) :=
  Finite.of_injective (fun r : acceptedResidues m => r.1) Subtype.val_injective

local instance rayAcceptedResiduesFintype (m : RayClassModulus K) :
    Fintype (acceptedResidues m) := Fintype.ofFinite _

private theorem embeddingCoords_injective : Function.Injective (embeddingCoords K) := by
  intro x y hxy
  apply mixedEmbedding_injective K
  have h := congrArg
    (fun z => (NumberField.mixedEmbedding.euclidean.toMixed K)
      ((NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis K).repr.symm z)) hxy
  simpa [embeddingCoords] using h

private noncomputable def integralIdealCoordPreimage (J : Ideal (𝓞 K)) (hJ : J ≠ ⊥)
    (v : idealZLattice K (idealUnit J hJ)) : J := by
  classical
  let hmem : ∃ x ∈ (idealUnit J hJ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K),
      embeddingCoords K x = (v : EuclideanSpace ℝ (index K)) :=
    (mem_idealZLattice K (idealUnit J hJ) v.1).mp v.2
  have hxcoe : (Classical.choose hmem) ∈
      (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    have h := (Classical.choose_spec hmem).1
    change (Classical.choose hmem) ∈
      (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) at h
    exact h
  let himage : ∃ a ∈ J, algebraMap (𝓞 K) K a = Classical.choose hmem :=
    (FractionalIdeal.mem_coeIdeal (nonZeroDivisors (𝓞 K))).mp hxcoe
  exact ⟨Classical.choose himage, (Classical.choose_spec himage).1⟩

private theorem integralIdealCoordPreimage_spec (J : Ideal (𝓞 K)) (hJ : J ≠ ⊥)
    (v : idealZLattice K (idealUnit J hJ)) :
    embeddingCoords K (algebraMap (𝓞 K) K
      (integralIdealCoordPreimage J hJ v).1) =
        (v : EuclideanSpace ℝ (index K)) := by
  classical
  let hmem : ∃ x ∈ (idealUnit J hJ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K),
      embeddingCoords K x = (v : EuclideanSpace ℝ (index K)) :=
    (mem_idealZLattice K (idealUnit J hJ) v.1).mp v.2
  have hxcoe : (Classical.choose hmem) ∈
      (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    have h := (Classical.choose_spec hmem).1
    change (Classical.choose hmem) ∈
      (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) at h
    exact h
  let himage : ∃ a ∈ J, algebraMap (𝓞 K) K a = Classical.choose hmem :=
    (FractionalIdeal.mem_coeIdeal (nonZeroDivisors (𝓞 K))).mp hxcoe
  change embeddingCoords K (algebraMap (𝓞 K) K (Classical.choose himage)) = _
  rw [(Classical.choose_spec himage).2]
  exact (Classical.choose_spec hmem).2

/-- Integral elements of a nonzero ideal, in AINTLIB's Euclidean lattice coordinates. -/
noncomputable def integralIdealCoordMap (J : Ideal (𝓞 K)) (hJ : J ≠ ⊥) :
    J → idealZLattice K (idealUnit J hJ) := fun x =>
  ⟨embeddingCoords K (algebraMap (𝓞 K) K x.1),
    (mem_idealZLattice K (idealUnit J hJ) _).mpr ⟨
      algebraMap (𝓞 K) K x.1,
      by
        change algebraMap (𝓞 K) K x.1 ∈
          (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
        exact FractionalIdeal.mem_coeIdeal_of_mem (nonZeroDivisors (𝓞 K)) x.2,
      rfl⟩⟩

noncomputable def integralIdealCoordEquiv (J : Ideal (𝓞 K)) (hJ : J ≠ ⊥) :
    J ≃ idealZLattice K (idealUnit J hJ) where
  toFun := integralIdealCoordMap J hJ
  invFun := integralIdealCoordPreimage J hJ
  left_inv x := by
    apply Subtype.ext
    apply (FaithfulSMul.algebraMap_injective (𝓞 K) K)
    apply embeddingCoords_injective
    change embeddingCoords K (algebraMap (𝓞 K) K
        (integralIdealCoordPreimage J hJ (integralIdealCoordMap J hJ x)).1) =
      embeddingCoords K (algebraMap (𝓞 K) K x.1)
    rw [integralIdealCoordPreimage_spec]
    rfl
  right_inv v := by
    apply Subtype.ext
    exact integralIdealCoordPreimage_spec J hJ v

theorem integralIdealCoordMap_eq_zero_iff (J : Ideal (𝓞 K)) (hJ : J ≠ ⊥)
    (x : J) : integralIdealCoordMap J hJ x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    have hzero : integralIdealCoordMap J hJ (0 : J) = 0 := by
      apply Subtype.ext
      simp [integralIdealCoordMap, embeddingCoords]
    exact (integralIdealCoordEquiv J hJ).injective (hx.trans hzero.symm)
  · intro hx
    rw [hx]
    apply Subtype.ext
    simp [integralIdealCoordMap, embeddingCoords]

private theorem embeddingCoords_add (x y : K) :
    embeddingCoords K (x + y) = embeddingCoords K x + embeddingCoords K y := by
  simp [embeddingCoords]

/-- A chosen integral lift in `J` of each residue represented by an integral unit. -/
noncomputable def acceptedResidueLift (m : RayClassModulus K) (J : Ideal (𝓞 K))
    (hJM : J ⊔ modulusIdeal m = ⊤) (r : acceptedResidues m) : J :=
  Classical.choose (integral_residue_surjective_of_sup_eq m J hJM r.1)

theorem acceptedResidueLift_spec (m : RayClassModulus K) (J : Ideal (𝓞 K))
    (hJM : J ⊔ modulusIdeal m = ⊤) (r : acceptedResidues m) :
    Ideal.Quotient.mk (modulusIdeal m) (acceptedResidueLift m J hJM r).1 = r.1 :=
  Classical.choose_spec (integral_residue_surjective_of_sup_eq m J hJM r.1)

/-- The points selected by the ray kernel in an integral ideal. -/
def rayKernelPoints [IsTotallyComplex K] (m : RayClassModulus K) (J : Ideal (𝓞 K)) :=
  {x : J // rayKernelWeight m (algebraMap (𝓞 K) K x.1) = 1}

/-- The real anisotropic Gaussian at an integral ideal element. -/
noncomputable def integralIdealGaussian (c : index K → ℝ) (x : 𝓞 K) : ℝ :=
  Real.exp (-Real.pi * ∑ i : index K,
    c i * (embeddingCoords K (algebraMap (𝓞 K) K x) i) ^ 2)

theorem summable_integralIdealGaussian [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K))
    (hcop : IsCoprimeTo m J) (c : index K → ℝ)
    {a : ℝ} (ha : 0 < a) (hca : ∀ i, a ≤ c i) :
    Summable (fun x : rayKernelPoints m J => integralIdealGaussian c x.1.1) := by
  have hlat := DedekindResidue.summable_real_weightedGaussian
    (idealZLattice K (idealUnit J hcop.1)) ha hca
  let e := integralIdealCoordEquiv J hcop.1
  have hfull : Summable (fun x : J => integralIdealGaussian c x.1) := by
    have hcomp : Summable (fun x : J =>
        Real.exp (-Real.pi * ∑ i : index K,
          c i * ((e x : EuclideanSpace ℝ (index K)) i) ^ 2)) :=
      (Equiv.summable_iff e).mpr hlat
    simpa [integralIdealGaussian, e, integralIdealCoordEquiv,
      integralIdealCoordMap] using hcomp
  exact hfull.subtype (fun x : J =>
    rayKernelWeight m (algebraMap (𝓞 K) K x.1) = 1)

/-- The ray theta sum over the integral elements selected by the principal ray kernel. -/
noncomputable def rayTheta [IsTotallyComplex K] (m : RayClassModulus K)
    (J : Ideal (𝓞 K)) (hcop : IsCoprimeTo m J) (c : InfinitePlace K → ℝ) : ℝ :=
  ∑' x : rayKernelPoints m J, integralIdealGaussian (placeWeights K c) x.1.1

/-- The ray theta with its zero lattice point removed. -/
noncomputable def rayThetaTail [IsTotallyComplex K] (m : RayClassModulus K)
    (J : Ideal (𝓞 K)) (hcop : IsCoprimeTo m J) (c : InfinitePlace K → ℝ) : ℝ :=
  ∑' x : rayKernelPoints m J,
    if x.1.1 = 0 then 0 else integralIdealGaussian (placeWeights K c) x.1.1

theorem rayTheta_eq_delta_add_tail [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hcop : IsCoprimeTo m J)
    (c : InfinitePlace K → ℝ) {a : ℝ} (ha : 0 < a)
    (hca : ∀ i, a ≤ placeWeights K c i) :
    rayTheta m J hcop c =
      (if m.finitePart = 0 then 1 else 0) + rayThetaTail m J hcop c := by
  classical
  by_cases hm : m.finitePart = 0
  · have hzweight : rayKernelWeight m (algebraMap (𝓞 K) K (0 : 𝓞 K)) = 1 := by
      simp [rayKernelWeight, hm]
    let z : rayKernelPoints m J := ⟨0, hzweight⟩
    have hs := summable_integralIdealGaussian m J hcop
      (placeWeights K c) ha hca
    have hsplit := hs.tsum_eq_add_tsum_ite z
    rw [rayTheta, rayThetaTail, hsplit]
    have hterm : integralIdealGaussian (placeWeights K c) z.1.1 = 1 := by
      simp [integralIdealGaussian, embeddingCoords, z]
    rw [hterm]
    rw [if_pos hm]
    congr 1
    apply tsum_congr
    intro x
    have hcond : (x = z) ↔ x.1.1 = 0 := by
      constructor
      · intro h
        have := congrArg (fun y : rayKernelPoints m J => y.1.1) h
        simpa [z] using this
      · intro hx
        apply Subtype.ext
        apply Subtype.ext
        exact hx
    simp [hcond]
  · have hx : ∀ x : rayKernelPoints m J, x.1.1 ≠ 0 := by
      intro x hx0
      have hw := x.2
      simp [rayKernelWeight, hx0, hm] at hw
    rw [rayTheta, rayThetaTail]
    simp [hm, hx]

private theorem rayThetaTail_nonneg [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hcop : IsCoprimeTo m J)
    (c : InfinitePlace K → ℝ) : 0 ≤ rayThetaTail m J hcop c := by
  unfold rayThetaTail
  refine tsum_nonneg (fun x => ?_)
  by_cases hx : x.1.1 = 0
  · simp [hx]
  · simp only [if_neg hx]
    unfold integralIdealGaussian
    exact Real.exp_nonneg _

private theorem place_lower_of_coordinate_lower (c : InfinitePlace K → ℝ)
    {a : ℝ} (hca : ∀ i : index K, a ≤ placeWeights K c i) :
    ∀ w, a ≤ c w := by
  intro w
  by_cases hw : IsReal w
  · simpa [placeWeights] using hca (Sum.inl ⟨w, hw⟩)
  · have hcomplex : IsComplex w := (not_isReal_iff_isComplex).mp hw
    simpa [placeWeights] using hca (Sum.inr (⟨w, hcomplex⟩, 0))

/-- The nonzero ray theta tail is dominated by the ordinary ideal theta tail. -/
private theorem rayThetaTail_le_heckeTheta_tail [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hcop : IsCoprimeTo m J)
    (c : InfinitePlace K → ℝ) {a : ℝ} (ha : 0 < a)
    (hca : ∀ i, a ≤ placeWeights K c i) :
    rayThetaTail m J hcop c ≤
      heckeTheta K (idealUnit J hcop.1) c - 1 := by
  classical
  let L := idealZLattice K (idealUnit J hcop.1)
  let φ : rayKernelPoints m J → L := fun x => integralIdealCoordMap J hcop.1 x.1
  have hφ : Function.Injective φ := by
    intro x y hxy
    apply Subtype.ext
    exact (integralIdealCoordEquiv J hcop.1).injective hxy
  let gaussian : L → ℝ := fun v =>
    Real.exp (-Real.pi * ∑ i : index K,
      placeWeights K c i * ((v : EuclideanSpace ℝ (index K)) i) ^ 2)
  let tail : L → ℝ := fun v => if v = 0 then 0 else gaussian v
  have hlat := DedekindResidue.summable_real_weightedGaussian L ha hca
  have htail : Summable tail := by
    apply hlat.of_nonneg_of_le
    · intro v
      by_cases hv : v = 0
      · simp [tail, hv]
      · simp [tail, hv, gaussian]
        positivity
    · intro v
      by_cases hv : v = 0
      · simp [tail, hv, gaussian]
      · simp [tail, hv, gaussian]
  have htail_nonneg (v : L) : 0 ≤ tail v := by
    by_cases hv : v = 0
    · simp [tail, hv]
    · simp [tail, hv, gaussian]
      positivity
  have hle := tsum_comp_le_tsum_of_inj htail htail_nonneg (i := φ) hφ
  have hsourceEq : rayThetaTail m J hcop c = ∑' x : rayKernelPoints m J, tail (φ x) := by
    unfold rayThetaTail
    apply tsum_congr
    intro x
    have hzero := integralIdealCoordMap_eq_zero_iff J hcop.1 x.1
    have hcond : φ x = 0 ↔ x.1.1 = 0 := by
      change integralIdealCoordMap J hcop.1 x.1 = 0 ↔ x.1.1 = 0
      rw [hzero]
      simp
    have hgauss : gaussian (φ x) =
        integralIdealGaussian (placeWeights K c) x.1.1 := by
      simp [gaussian, φ, integralIdealGaussian, integralIdealCoordMap]
    change (if x.1.1 = 0 then 0 else
        integralIdealGaussian (placeWeights K c) x.1.1) =
      (if φ x = 0 then 0 else gaussian (φ x))
    exact if_congr hcond.symm (by rfl) hgauss.symm
  have hplace : ∀ w, a ≤ c w := place_lower_of_coordinate_lower c hca
  have htheta := DedekindResidue.heckeTheta_eq_one_add K
    (idealUnit J hcop.1) ha hplace
  have htarget : ∑' v : L, tail v =
      heckeTheta K (idealUnit J hcop.1) c - 1 := by
    rw [htheta]
    simp [tail, gaussian, L]
  calc
    rayThetaTail m J hcop c = ∑' x : rayKernelPoints m J, tail (φ x) := hsourceEq
    _ ≤ ∑' v : L, tail v := hle
    _ = heckeTheta K (idealUnit J hcop.1) c - 1 := htarget

private theorem rayTheta_nonneg [IsTotallyComplex K] (m : RayClassModulus K)
    (J : Ideal (𝓞 K)) (hcop : IsCoprimeTo m J) (c : InfinitePlace K → ℝ)
    {a : ℝ} (ha : 0 < a) (hca : ∀ i, a ≤ placeWeights K c i) :
    0 ≤ rayTheta m J hcop c := by
  rw [rayTheta_eq_delta_add_tail m J hcop c ha hca]
  apply add_nonneg
  · by_cases hm : m.finitePart = 0 <;> simp [hm]
  · unfold rayThetaTail
    exact tsum_nonneg fun x => by
      by_cases hx : x.1.1 = 0
      · simp [hx]
      · simp only [if_neg hx]
        unfold integralIdealGaussian
        exact Real.exp_nonneg _

private theorem rayTheta_nonneg_any [IsTotallyComplex K] (m : RayClassModulus K)
    (J : Ideal (𝓞 K)) (hcop : IsCoprimeTo m J) (c : InfinitePlace K → ℝ) :
    0 ≤ rayTheta m J hcop c := by
  unfold rayTheta
  exact tsum_nonneg fun x => by
    unfold integralIdealGaussian
    exact Real.exp_nonneg _

/-- Pointwise domination of the ray theta by its full ideal theta. -/
private theorem rayTheta_le_heckeTheta [IsTotallyComplex K] (m : RayClassModulus K)
    (J : Ideal (𝓞 K)) (hcop : IsCoprimeTo m J) (c : InfinitePlace K → ℝ)
    {a : ℝ} (ha : 0 < a) (hca : ∀ i, a ≤ placeWeights K c i) :
    rayTheta m J hcop c ≤ heckeTheta K (idealUnit J hcop.1) c := by
  rw [rayTheta_eq_delta_add_tail m J hcop c ha hca]
  have hδ : (if m.finitePart = 0 then (1 : ℝ) else 0) ≤ 1 := by
    by_cases hm : m.finitePart = 0 <;> simp [hm]
  have ht := rayThetaTail_le_heckeTheta_tail m J hcop c ha hca
  linarith

private theorem integralIdealGaussian_place (c : InfinitePlace K → ℝ) (x : 𝓞 K) :
    integralIdealGaussian (placeWeights K c) x =
      Real.exp (-Real.pi * ∑ w : InfinitePlace K,
        c w * (w (algebraMap (𝓞 K) K x)) ^ 2) := by
  unfold integralIdealGaussian
  rw [← DedekindResidue.sum_placeWeights_embeddingCoords_sq]

private noncomputable def rayKernelPointMulUnit [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (u : (𝓞 K)ˣ)
    (x : rayKernelPoints m J) : rayKernelPoints m J := by
  let y : J := ⟨(u : 𝓞 K) * x.1.1, J.mul_mem_left (u : 𝓞 K) x.1.2⟩
  have hy : rayKernelWeight m (algebraMap (𝓞 K) K y.1) = 1 := by
    rw [map_mul, rayKernelWeight_integralUnit]
    exact x.2
  exact ⟨y, hy⟩

private noncomputable def rayKernelPointMulUnitInv [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (u : (𝓞 K)ˣ)
    (x : rayKernelPoints m J) : rayKernelPoints m J := by
  let ui : (𝓞 K)ˣ := u⁻¹
  let y : J := ⟨(ui : 𝓞 K) * x.1.1, J.mul_mem_left (ui : 𝓞 K) x.1.2⟩
  have hy : rayKernelWeight m (algebraMap (𝓞 K) K y.1) = 1 := by
    rw [map_mul, rayKernelWeight_integralUnit]
    exact x.2
  exact ⟨y, hy⟩

private noncomputable def rayKernelPointsUnitMulEquiv [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (u : (𝓞 K)ˣ) :
    rayKernelPoints m J ≃ rayKernelPoints m J where
  toFun := rayKernelPointMulUnit m J u
  invFun := rayKernelPointMulUnitInv m J u
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    dsimp [rayKernelPointMulUnit, rayKernelPointMulUnitInv]
    change ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * ((u : 𝓞 K) * x.1.1) = x.1.1
    simp [mul_assoc]
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    dsimp [rayKernelPointMulUnit, rayKernelPointMulUnitInv]
    change (u : 𝓞 K) * (((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * x.1.1) = x.1.1
    simp [mul_assoc]

/-- The ray theta is periodic under the logarithms of integral units. -/
theorem rayTheta_unit_mul [IsTotallyComplex K] (m : RayClassModulus K)
    (J : Ideal (𝓞 K)) (hcop : IsCoprimeTo m J) (u : (𝓞 K)ˣ)
    (c : InfinitePlace K → ℝ) :
    rayTheta m J hcop (fun w =>
      (w (algebraMap (𝓞 K) K (u : 𝓞 K))) ^ 2 * c w) = rayTheta m J hcop c := by
  unfold rayTheta
  let e := rayKernelPointsUnitMulEquiv m J u
  calc
    ∑' x : rayKernelPoints m J,
        integralIdealGaussian
          (placeWeights K (fun w =>
            (w (algebraMap (𝓞 K) K (u : 𝓞 K))) ^ 2 * c w)) x.1.1
      = ∑' x : rayKernelPoints m J,
          integralIdealGaussian (placeWeights K c) (e x).1.1 := by
            apply tsum_congr
            intro x
            rw [integralIdealGaussian_place, integralIdealGaussian_place]
            have hxval : (e x).1.1 = (u : 𝓞 K) * x.1.1 := rfl
            rw [hxval]
            simp_rw [map_mul, mul_pow]
            congr 1
            apply congrArg (fun z : ℝ => -Real.pi * z)
            apply Finset.sum_congr rfl
            intro w _
            ring
    _ = ∑' x : rayKernelPoints m J, integralIdealGaussian (placeWeights K c) x.1.1 :=
      Equiv.tsum_eq e (fun x => integralIdealGaussian (placeWeights K c) x.1.1)

/-- Periodicity of the ray theta in the logarithmic directions of integral units. -/
theorem rayTheta_heckeWeights_periodic [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hcop : IsCoprimeTo m J)
    (t : ℝ) (v : logSpace K) (u : (𝓞 K)ˣ) :
    rayTheta m J hcop (heckeWeights K t (v + logEmbedding K (Additive.ofMul u))) =
      rayTheta m J hcop (heckeWeights K t v) := by
  rw [heckeWeights_add_logEmbedding]
  exact rayTheta_unit_mul m J hcop u (heckeWeights K t v)

/-- The unit-box average of the ray theta attached to an integral prime-to ideal. -/
noncomputable def rayG [IsTotallyComplex K] (m : RayClassModulus K)
    (J : Ideal (𝓞 K)) (hcop : IsCoprimeTo m J) (t : ℝ) : ℝ :=
  (torsionOrder K : ℝ)⁻¹ *
    ∫ v in ZSpan.fundamentalDomain
      ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis ℝ),
      rayTheta m J hcop (heckeWeights K t v)

/-- The norm-normalized primal theta function of an integral ray ideal. -/
noncomputable def rayF [IsTotallyComplex K] (m : RayClassModulus K)
    (J : Ideal (𝓞 K)) (hcop : IsCoprimeTo m J) (t : ℝ) : ℝ :=
  let I : NumberFieldFractionalIdealGroup K := idealUnit J hcop.1
  rayG m J hcop ((idealNormR K I)⁻¹ ^ 2 * heckeBeta K * t)

/-- The dual component dictated by the weight-one-half functional equation. -/
noncomputable def rayDualF [IsTotallyComplex K] (m : RayClassModulus K)
    (J : Ideal (𝓞 K)) (hcop : IsCoprimeTo m J) (t : ℝ) : ℝ :=
  t ^ (-(1 : ℝ) / 2) * rayF m J hcop (1 / t)

/-- The common large-parameter constant term of all ray classes. -/
noncomputable def rayPrimalConstant [IsTotallyComplex K] (m : RayClassModulus K) : ℝ :=
  (if m.finitePart = 0 then 1 else 0) *
    (torsionOrder K : ℝ)⁻¹ * unitBoxVol K

/-- The common small-parameter dual constant, normalized by the finite modulus norm. -/
noncomputable def rayDualConstant [IsTotallyComplex K] (m : RayClassModulus K) : ℝ :=
  (residueCount m : ℝ) / (modulusNorm m : ℝ) *
    (torsionOrder K : ℝ)⁻¹ * unitBoxVol K

private theorem rayTheta_complex [IsTotallyComplex K] (m : RayClassModulus K)
    (J : Ideal (𝓞 K)) (hcop : IsCoprimeTo m J) (c : InfinitePlace K → ℝ)
    {a : ℝ} (ha : 0 < a) (hca : ∀ i, a ≤ placeWeights K c i) :
    ((rayTheta m J hcop c : ℝ) : ℂ) =
      ∑' x : rayKernelPoints m J,
        weightedGaussianCM (placeWeights K c)
          (embeddingCoords K (algebraMap (𝓞 K) K x.1.1)) := by
  have hs := summable_integralIdealGaussian (m := m) J hcop
    (placeWeights K c) ha hca
  unfold rayTheta
  rw [show ((∑' x : rayKernelPoints m J,
      integralIdealGaussian (placeWeights K c) x.1.1 : ℝ) : ℂ) =
        Complex.ofRealCLM (∑' x : rayKernelPoints m J,
          integralIdealGaussian (placeWeights K c) x.1.1) from rfl]
  rw [ContinuousLinearMap.map_tsum Complex.ofRealCLM hs]
  apply tsum_congr
  intro x
  change Complex.ofReal (Real.exp (-Real.pi * ∑ i : index K,
      placeWeights K c i *
        (embeddingCoords K (algebraMap (𝓞 K) K x.1.1) i) ^ 2)) =
    Complex.exp (-(Real.pi : ℂ) * ∑ i : index K,
      (placeWeights K c i : ℂ) *
        ((embeddingCoords K (algebraMap (𝓞 K) K x.1.1) i : ℂ) ^ 2))
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring_nf

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 5000000 in
-- Joint continuity of the ray theta in the positive ray parameter and log-unit variable.
theorem continuousAt_rayTheta_heckeWeights [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hcop : IsCoprimeTo m J)
    {p : ℝ × logSpace K} (hp : 0 < p.1) :
    ContinuousAt (fun q : ℝ × logSpace K =>
      rayTheta m J hcop (heckeWeights K q.1 q.2)) p := by
  classical
  set a : ℝ := p.1 / 2 with ha_def
  have ha : 0 < a := by positivity
  set R : ℝ := ‖p.2‖ + 1 with hR_def
  have hR : 0 ≤ R := by positivity
  set m₀ : ℝ := Real.exp (-(2 * (Fintype.card (InfinitePlace K)) * R)) with hm_def
  have hm : 0 < m₀ := Real.exp_pos _
  set a' : ℝ := m₀ * a ^ ((1 : ℝ) / (Module.finrank ℚ K)) with ha'_def
  have ha' : 0 < a' := by
    have : 0 < a ^ ((1 : ℝ) / (Module.finrank ℚ K)) := Real.rpow_pos_of_pos ha _
    positivity
  have hsub := DedekindResidue.le_placeWeights_heckeWeights_on_box K a m₀ R a'
    ha hR ha'_def hm_def
  let S : Set (ℝ × logSpace K) := Set.Ioi a ×ˢ Metric.ball (0 : logSpace K) R
  let term : rayKernelPoints m J → (ℝ × logSpace K) → ℝ := fun x q =>
    integralIdealGaussian (placeWeights K (heckeWeights K q.1 q.2)) x.1.1
  let majorant : rayKernelPoints m J → ℝ := fun x =>
    integralIdealGaussian (fun _ : index K => a') x.1.1
  have hsum : Summable majorant :=
    summable_integralIdealGaussian m J hcop (fun _ : index K => a') ha' (fun _ => le_rfl)
  have hterms : ∀ x : rayKernelPoints m J, ContinuousOn (term x) S := by
    intro x
    unfold term integralIdealGaussian
    refine ContinuousOn.rexp ?_
    refine ContinuousOn.mul continuousOn_const ?_
    refine continuousOn_finsetSum _ (fun i _ => ?_)
    refine ContinuousOn.mul ?_ continuousOn_const
    rcases i with w | ⟨w, j⟩ <;>
      simpa [placeWeights] using
        (DedekindResidue.continuousOn_heckeWeights_apply K a R ha w)
  have hbound : ∀ x : rayKernelPoints m J, ∀ q : ℝ × logSpace K,
      q ∈ S → ‖term x q‖ ≤ majorant x := by
    intro x q hq
    have hweights := hsub q hq
    change |integralIdealGaussian
        (placeWeights K (heckeWeights K q.1 q.2)) x.1.1| ≤
      integralIdealGaussian (fun _ : index K => a') x.1.1
    rw [integralIdealGaussian, integralIdealGaussian,
      abs_of_pos (Real.exp_pos _)]
    exact DedekindResidue.exp_weighted_le_exp_iso hweights
      (embeddingCoords K (algebraMap (𝓞 K) K x.1.1))
  have hcts : ContinuousOn (fun q => ∑' x : rayKernelPoints m J, term x q) S :=
    continuousOn_tsum hterms hsum hbound
  refine ContinuousOn.continuousAt (s := S) ?_ ?_
  · change ContinuousOn (fun q => ∑' x : rayKernelPoints m J, term x q) S
    exact hcts
  · refine IsOpen.mem_nhds (IsOpen.prod isOpen_Ioi Metric.isOpen_ball) ?_
    refine ⟨?_, ?_⟩
    · show a < p.1
      rw [ha_def]
      linarith
    · show p.2 ∈ Metric.ball (0 : logSpace K) R
      rw [Metric.mem_ball, dist_zero_right, hR_def]
      linarith

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 5000000 in
theorem continuousAt_rayG [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hcop : IsCoprimeTo m J)
    {t₀ : ℝ} (ht₀ : 0 < t₀) : ContinuousAt (rayG m J hcop) t₀ := by
  classical
  obtain ⟨R, hR, hbox⟩ := DedekindResidue.exists_box_coord_bound K
  set m₀ : ℝ := Real.exp (-(2 * (Fintype.card (InfinitePlace K)) * R)) with hm_def
  have hm : 0 < m₀ := Real.exp_pos _
  set a' : ℝ := m₀ * (t₀ / 2) ^ ((1 : ℝ) / (Module.finrank ℚ K)) with ha'_def
  have ha' : 0 < a' := by
    have : 0 < (t₀ / 2) ^ ((1 : ℝ) / (Module.finrank ℚ K)) :=
      Real.rpow_pos_of_pos (by positivity) _
    positivity
  let I : NumberFieldFractionalIdealGroup K := idealUnit J hcop.1
  have hG : rayG m J hcop = fun t => (torsionOrder K : ℝ)⁻¹ *
      ∫ u in ZSpan.fundamentalDomain
        ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis ℝ),
        rayTheta m J hcop (heckeWeights K t u) := by
    funext t
    rfl
  rw [hG]
  refine ContinuousAt.mul continuousAt_const ?_
  refine MeasureTheory.continuousAt_of_dominated (bound := fun _ =>
    ∑' v : idealZLattice K I,
      Real.exp (-Real.pi * ∑ i : index K, a' *
        ((v : EuclideanSpace ℝ (index K)) i) ^ 2)) ?_ ?_ ?_ ?_
  · refine Filter.eventually_of_mem (Ioi_mem_nhds (show t₀ / 2 < t₀ by linarith)) ?_
    intro t ht
    have hcont : Continuous (fun u : logSpace K =>
        rayTheta m J hcop (heckeWeights K t u)) := by
      rw [continuous_iff_continuousAt]
      intro u
      have hj := continuousAt_rayTheta_heckeWeights m J hcop
        (p := ((t : ℝ), u)) (lt_trans (by positivity) ht)
      have hin : ContinuousAt (fun u' : logSpace K => ((t : ℝ), u')) u :=
        (continuous_const.prodMk continuous_id).continuousAt
      exact ContinuousAt.comp (x := u) hj hin
    exact hcont.aestronglyMeasurable
  · refine Filter.eventually_of_mem (Ioi_mem_nhds (show t₀ / 2 < t₀ by linarith)) ?_
    intro t ht
    refine (MeasureTheory.ae_restrict_iff'
      (ZSpan.fundamentalDomain_measurableSet
        ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis ℝ))).mpr ?_
    refine Filter.Eventually.of_forall (fun u hu => ?_)
    have hplace : ∀ w, a' ≤ heckeWeights K t u w := by
      intro w
      refine le_trans ?_ (DedekindResidue.le_heckeWeights_of_bounded K hR
        (hbox u hu) (le_of_lt (lt_trans (by positivity) ht)) w)
      rw [ha'_def, hm_def]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      exact Real.rpow_le_rpow (by positivity) (le_of_lt ht) (by positivity)
    have hcoord : ∀ i, a' ≤ placeWeights K (heckeWeights K t u) i := by
      rintro (w | ⟨w, j⟩) <;> exact hplace _
    have hbound : rayTheta m J hcop (heckeWeights K t u) ≤
        ∑' v : idealZLattice K I,
          Real.exp (-Real.pi * ∑ i : index K, a' *
            ((v : EuclideanSpace ℝ (index K)) i) ^ 2) := by
      calc
        rayTheta m J hcop (heckeWeights K t u) ≤ heckeTheta K I
            (heckeWeights K t u) := rayTheta_le_heckeTheta m J hcop
              (heckeWeights K t u) ha' hcoord
        _ ≤ _ := DedekindResidue.heckeTheta_le_iso K I ha' hplace
    rw [Real.norm_eq_abs, abs_of_nonneg
      (rayTheta_nonneg m J hcop (heckeWeights K t u) ha' hcoord)]
    exact hbound
  · exact MeasureTheory.integrableOn_const
      (ne_top_of_lt (ZSpan.fundamentalDomain_isBounded
        ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis ℝ)).measure_lt_top)
  · refine Filter.Eventually.of_forall (fun u => ?_)
    have hj := continuousAt_rayTheta_heckeWeights m J hcop
      (p := ((t₀ : ℝ), u)) ht₀
    have hin : ContinuousAt (fun t : ℝ => ((t : ℝ), u)) t₀ :=
      (continuous_id.prodMk continuous_const).continuousAt
    exact ContinuousAt.comp (x := t₀) hj hin

theorem continuousOn_rayG [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hcop : IsCoprimeTo m J) :
    ContinuousOn (rayG m J hcop) (Set.Ioi 0) := by
  intro t ht
  exact (continuousAt_rayG m J hcop ht).continuousWithinAt

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 5000000 in
theorem continuousOn_rayF [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hcop : IsCoprimeTo m J) :
    ContinuousOn (rayF m J hcop) (Set.Ioi 0) := by
  let I : NumberFieldFractionalIdealGroup K := idealUnit J hcop.1
  let scale : ℝ := (idealNormR K I)⁻¹ ^ 2 * heckeBeta K
  have hN : 0 < idealNormR K I := DedekindResidue.idealNormR_pos K I
  have hβ : 0 < heckeBeta K := DedekindResidue.heckeBeta_pos K
  have hscale : 0 < scale := by
    dsimp [scale]
    positivity
  change ContinuousOn (fun t => rayG m J hcop (scale * t)) (Set.Ioi 0)
  refine ContinuousOn.comp (g := rayG m J hcop) (f := fun t : ℝ => scale * t)
    (t := Set.Ioi 0) (continuousOn_rayG m J hcop)
    ((continuous_const.mul continuous_id).continuousOn) ?_
  intro t ht
  exact Set.mem_Ioi.mpr (mul_pos hscale (Set.mem_Ioi.mp ht))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 5000000 in
theorem continuousOn_rayDualF [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hcop : IsCoprimeTo m J) :
    ContinuousOn (rayDualF m J hcop) (Set.Ioi 0) := by
  have hinv : ContinuousOn (fun t : ℝ => 1 / t) (Set.Ioi 0) := by
    simpa only [one_div] using
      (continuousOn_inv₀.mono (by intro t ht; exact ne_of_gt (Set.mem_Ioi.mp ht)))
  have hpow : ContinuousOn (fun t : ℝ => t ^ (-(1 : ℝ) / 2)) (Set.Ioi 0) :=
    ContinuousOn.rpow_const continuousOn_id (fun t ht =>
      Or.inl (ne_of_gt (Set.mem_Ioi.mp ht)))
  have hcomp : ContinuousOn (fun t : ℝ => rayF m J hcop (1 / t)) (Set.Ioi 0) := by
    refine ContinuousOn.comp (g := rayF m J hcop) (f := fun t : ℝ => 1 / t)
      (t := Set.Ioi 0) (continuousOn_rayF m J hcop) hinv ?_
    intro t ht
    exact Set.mem_Ioi.mpr (one_div_pos.mpr (Set.mem_Ioi.mp ht))
  change ContinuousOn (fun t : ℝ => t ^ (-(1 : ℝ) / 2) * rayF m J hcop (1 / t))
    (Set.Ioi 0)
  exact hpow.mul hcomp

/-- Exponential approach of the unit-box average to its common ray zero term. -/
theorem exists_rayG_dev_bound [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hcop : IsCoprimeTo m J) :
    ∃ C c' : ℝ, 0 < C ∧ 0 < c' ∧ ∀ {t : ℝ}, 1 ≤ t →
      |rayG m J hcop t - rayPrimalConstant m| ≤
        C * Real.exp (-c' * t ^ ((1 : ℝ) / (Module.finrank ℚ K))) := by
  classical
  let I : NumberFieldFractionalIdealGroup K := idealUnit J hcop.1
  obtain ⟨Cθ, c', hCθ, hc', hthetaDev⟩ :=
    DedekindResidue.exists_heckeTheta_dev_bound K I
  have hw : 0 < (torsionOrder K : ℝ)⁻¹ := by
    have hpos : 0 < torsionOrder K := torsionOrder_pos K
    have hposReal : 0 < (torsionOrder K : ℝ) := by exact_mod_cast hpos
    positivity
  have hunitVol : 0 < unitBoxVol K := DedekindResidue.unitBoxVol_pos K
  refine ⟨(torsionOrder K : ℝ)⁻¹ * unitBoxVol K * Cθ, c', ?_, hc', fun {t} ht => ?_⟩
  · positivity
  · have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
    let B := ZSpan.fundamentalDomain
      ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis ℝ)
    have hBmeas : MeasurableSet B := ZSpan.fundamentalDomain_measurableSet _
    have hBfin : volume B < ⊤ := (ZSpan.fundamentalDomain_isBounded _).measure_lt_top
    let δ : ℝ := if m.finitePart = 0 then 1 else 0
    -- Use the uniform box bound from AINTLIB; this is the same lower bound used by the
    -- ordinary Hecke theta tail estimate.
    obtain ⟨R, hR, hbox⟩ := DedekindResidue.exists_box_coord_bound K
    let m₁ : ℝ := Real.exp (-(2 * (Fintype.card (InfinitePlace K)) * R))
    have hm₁ : 0 < m₁ := Real.exp_pos _
    let a' : ℝ := m₁ * t ^ ((1 : ℝ) / (Module.finrank ℚ K))
    have ha' : 0 < a' := by positivity
    have hdevRay : ∀ u ∈ B,
        0 ≤ rayTheta m J hcop (heckeWeights K t u) - δ ∧
          rayTheta m J hcop (heckeWeights K t u) - δ ≤
            Cθ * Real.exp (-c' * t ^ ((1 : ℝ) / (Module.finrank ℚ K))) := by
      intro u hu
      have hplace : ∀ w, a' ≤ heckeWeights K t u w := by
        intro w
        have hbase := DedekindResidue.le_heckeWeights_of_bounded K hR
          (hbox u hu) ht0.le w
        simpa [a', m₁] using hbase
      have hcoord : ∀ i, a' ≤ placeWeights K (heckeWeights K t u) i := by
        rintro (w | ⟨w, j⟩) <;> exact hplace _
      have hsplit := rayTheta_eq_delta_add_tail m J hcop
        (heckeWeights K t u) ha' hcoord
      have htail : rayTheta m J hcop (heckeWeights K t u) - δ =
          rayThetaTail m J hcop (heckeWeights K t u) := by
        rw [hsplit]
        simp [δ]
      have htail0 := rayThetaTail_nonneg m J hcop (heckeWeights K t u)
      obtain ⟨h0, h1⟩ := hthetaDev ht u hu
      have hle := rayThetaTail_le_heckeTheta_tail m J hcop
        (heckeWeights K t u) ha' hcoord
      constructor
      · rw [htail]
        exact htail0
      · rw [htail]
        exact le_trans hle h1
    have hcontu : Continuous fun u : logSpace K =>
        rayTheta m J hcop (heckeWeights K t u) := by
      rw [continuous_iff_continuousAt]
      intro u
      have hj := continuousAt_rayTheta_heckeWeights m J hcop
        (p := ((t : ℝ), u)) ht0
      have hin : ContinuousAt (fun u' : logSpace K => ((t : ℝ), u')) u :=
        (continuous_const.prodMk continuous_id).continuousAt
      exact ContinuousAt.comp (x := u) hj hin
    have hint : IntegrableOn (fun u : logSpace K =>
        rayTheta m J hcop (heckeWeights K t u)) B := by
      refine MeasureTheory.Integrable.mono'
        (MeasureTheory.integrableOn_const (C := 1 + Cθ *
          Real.exp (-c' * t ^ ((1 : ℝ) / (Module.finrank ℚ K))))
          (ne_top_of_lt hBfin))
        hcontu.aestronglyMeasurable.restrict ?_
      refine (MeasureTheory.ae_restrict_iff' hBmeas).mpr ?_
      refine Filter.Eventually.of_forall (fun u hu => ?_)
      obtain ⟨h0, h1⟩ := hdevRay u hu
      have hδ : δ ≤ 1 := by
        by_cases hm : m.finitePart = 0 <;> simp [δ, hm]
      have hnonneg : 0 ≤ rayTheta m J hcop (heckeWeights K t u) := by
        exact rayTheta_nonneg_any m J hcop (heckeWeights K t u)
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      linarith
    have hsplitIntegral :
        (∫ u in B, rayTheta m J hcop (heckeWeights K t u)) =
          δ * unitBoxVol K + ∫ u in B,
            (rayTheta m J hcop (heckeWeights K t u) - δ) := by
      have hvol : volume.real B = unitBoxVol K := by
        rw [DedekindResidue.unitBoxVol]
        rfl
      have hconst : (∫ u in B, δ) = δ * unitBoxVol K := by
        rw [MeasureTheory.setIntegral_const, smul_eq_mul, hvol]
        ring
      have hsub :
          (∫ u in B, (rayTheta m J hcop (heckeWeights K t u) - δ)) =
            (∫ u in B, rayTheta m J hcop (heckeWeights K t u)) -
              (∫ u in B, δ) :=
        MeasureTheory.integral_sub hint
          (MeasureTheory.integrableOn_const (C := δ) (ne_top_of_lt hBfin))
      rw [hsub, hconst]
      ring
    have hGdiff : rayG m J hcop t - rayPrimalConstant m =
        (torsionOrder K : ℝ)⁻¹ *
          ∫ u in B, (rayTheta m J hcop (heckeWeights K t u) - δ) := by
      rw [rayG, rayPrimalConstant, hsplitIntegral]
      dsimp [δ]
      ring
    have htailbound :
        |∫ u in B, (rayTheta m J hcop (heckeWeights K t u) - δ)| ≤
          Cθ * Real.exp (-c' * t ^ ((1 : ℝ) / (Module.finrank ℚ K))) * (volume B).toReal := by
      rw [← Real.norm_eq_abs]
      refine MeasureTheory.norm_setIntegral_le_of_norm_le_const hBfin (fun u hu => ?_)
      obtain ⟨h0, h1⟩ := hdevRay u hu
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact h1
    rw [hGdiff, abs_mul, abs_of_pos hw]
    calc
      (torsionOrder K : ℝ)⁻¹ *
          |∫ u in B, (rayTheta m J hcop (heckeWeights K t u) - δ)|
        ≤ (torsionOrder K : ℝ)⁻¹ *
            (Cθ * Real.exp (-c' * t ^ ((1 : ℝ) / (Module.finrank ℚ K))) *
              (volume B).toReal) := mul_le_mul_of_nonneg_left htailbound hw.le
      _ = (torsionOrder K : ℝ)⁻¹ * unitBoxVol K * Cθ *
            Real.exp (-c' * t ^ ((1 : ℝ) / (Module.finrank ℚ K))) := by
        have hvol : (volume B).toReal = unitBoxVol K := by
          rw [DedekindResidue.unitBoxVol]
        rw [hvol]
        ring

/-- Large-parameter decay for the norm-normalized primal ray theta. -/
theorem exists_rayF_dev_bound [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hcop : IsCoprimeTo m J) :
    ∃ C c' t₀ : ℝ, 0 < C ∧ 0 < c' ∧ 1 ≤ t₀ ∧
      ∀ {t : ℝ}, t₀ ≤ t →
        |rayF m J hcop t - rayPrimalConstant m| ≤
          C * Real.exp (-c' * t ^ ((1 : ℝ) / (Module.finrank ℚ K))) := by
  classical
  let I : NumberFieldFractionalIdealGroup K := idealUnit J hcop.1
  let scale : ℝ := (idealNormR K I)⁻¹ ^ 2 * heckeBeta K
  have hN : 0 < idealNormR K I := DedekindResidue.idealNormR_pos K I
  have hβ : 0 < heckeBeta K := DedekindResidue.heckeBeta_pos K
  have hscale : 0 < scale := by
    dsimp [scale]
    positivity
  have hp : 0 < (1 : ℝ) / (Module.finrank ℚ K) :=
    div_pos one_pos (finrank_pos_real K)
  obtain ⟨C, c₀, hC, hc₀, hdev⟩ := exists_rayG_dev_bound m J hcop
  refine ⟨C, c₀ * scale ^ ((1 : ℝ) / (Module.finrank ℚ K)), max 1 scale⁻¹,
    hC, ?_, le_max_left _ _, fun {t} ht => ?_⟩
  · have hpow : 0 < scale ^ ((1 : ℝ) / (Module.finrank ℚ K)) :=
      Real.rpow_pos_of_pos hscale _
    positivity
  · have ht0 : 0 < t := lt_of_lt_of_le one_pos (le_trans (le_max_left _ _) ht)
    have hscaleInv : scale⁻¹ ≤ t := le_trans (le_max_right _ _) ht
    have hscaleT : 1 ≤ scale * t := by
      calc
        (1 : ℝ) = scale * scale⁻¹ := (mul_inv_cancel₀ hscale.ne').symm
        _ ≤ scale * t := mul_le_mul_of_nonneg_left hscaleInv hscale.le
    have hbase := hdev hscaleT
    have hpow : (scale * t) ^ ((1 : ℝ) / (Module.finrank ℚ K)) =
        scale ^ ((1 : ℝ) / (Module.finrank ℚ K)) *
          t ^ ((1 : ℝ) / (Module.finrank ℚ K)) :=
      Real.mul_rpow hscale.le ht0.le
    have harg : (idealNormR K I)⁻¹ ^ 2 * heckeBeta K * t = scale * t := by
      dsimp [scale]
    rw [rayF]
    rw [harg]
    rw [hpow] at hbase
    simpa [hpow, mul_assoc] using hbase

private theorem idealNormR_idealUnit_integral (J : Ideal (𝓞 K)) (hJ : J ≠ ⊥) :
    idealNormR K (idealUnit J hJ) = ((Ideal.absNorm J : ℕ) : ℝ) := by
  simp [DedekindResidue.idealNormR, idealUnit, FractionalIdeal.coeIdeal_absNorm]

/-- Covolume normalization for the product ideal `𝔪J`. -/
theorem covolume_ray_scaled [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hcop : IsCoprimeTo m J)
    (hMJ : modulusIdeal m * J ≠ ⊥) :
    ZLattice.covolume
        (idealZLattice K (idealUnit (modulusIdeal m * J) hMJ)) volume *
      Real.sqrt ((idealNormR K (idealUnit J hcop.1))⁻¹ ^ 2 * heckeBeta K) =
        (modulusNorm m : ℝ) := by
  classical
  let I : NumberFieldFractionalIdealGroup K := idealUnit J hcop.1
  let M : Ideal (𝓞 K) := modulusIdeal m
  let MJ : Ideal (𝓞 K) := M * J
  let I' : NumberFieldFractionalIdealGroup K := idealUnit MJ hMJ
  have hN : idealNormR K I = ((Ideal.absNorm J : ℕ) : ℝ) := by
    simpa [I] using idealNormR_idealUnit_integral J hcop.1
  have hmod : Ideal.absNorm M = modulusNorm m := by
    simpa [M] using modulusIdeal_absNorm m
  have hN' : idealNormR K I' = (modulusNorm m : ℝ) * idealNormR K I := by
    rw [idealNormR_idealUnit_integral, idealNormR_idealUnit_integral]
    change (Ideal.absNorm (M * J) : ℝ) = _
    rw [map_mul, hmod]
    norm_cast
  have hD : 0 < (((discr K).natAbs : ℕ) : ℝ) := natAbs_discr_pos K
  have hNpos : 0 < idealNormR K I := DedekindResidue.idealNormR_pos K I
  have hDroot : 0 < Real.sqrt (((discr K).natAbs : ℕ) : ℝ) := Real.sqrt_pos.mpr hD
  have hDD : |((discr K : ℤ) : ℝ)| = (((discr K).natAbs : ℕ) : ℝ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
  have hsq : (idealNormR K I)⁻¹ ^ 2 * heckeBeta K =
      ((idealNormR K I)⁻¹ * 2 ^ nrComplexPlaces K /
        Real.sqrt (((discr K).natAbs : ℕ) : ℝ)) ^ 2 := by
    rw [heckeBeta, div_pow, mul_pow, Real.sq_sqrt hD.le, ← pow_mul,
      show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul,
      mul_comm (nrComplexPlaces K) 2, mul_div_assoc]
  have hroot : Real.sqrt ((idealNormR K I)⁻¹ ^ 2 * heckeBeta K) =
      (idealNormR K I)⁻¹ * 2 ^ nrComplexPlaces K /
        Real.sqrt (((discr K).natAbs : ℕ) : ℝ) := by
    rw [hsq, Real.sqrt_sq (by positivity)]
  have hcovol :
      ZLattice.covolume (idealZLattice K I') volume =
        idealNormR K I' * (2⁻¹) ^ nrComplexPlaces K * Real.sqrt |discr K| := by
    rw [DedekindResidue.covolume_idealZLattice]
    rfl
  rw [hcovol, hN', hroot, hDD]
  field_simp [hNpos.ne', hDroot.ne']
  have hpow : (2⁻¹ : ℝ) ^ nrComplexPlaces K *
      (2 : ℝ) ^ nrComplexPlaces K = 1 := by
    rw [inv_pow]
    exact inv_mul_cancel₀ (pow_ne_zero _ (by norm_num))
  have hpow' : (1 / 2 : ℝ) ^ nrComplexPlaces K *
      (2 : ℝ) ^ nrComplexPlaces K = 1 := by
    simpa only [one_div] using hpow
  calc
    (modulusNorm m : ℝ) * (1 / 2 : ℝ) ^ nrComplexPlaces K *
        (2 : ℝ) ^ nrComplexPlaces K =
      (modulusNorm m : ℝ) *
        ((1 / 2 : ℝ) ^ nrComplexPlaces K * (2 : ℝ) ^ nrComplexPlaces K) := by ring
    _ = (modulusNorm m : ℝ) := by rw [hpow']; ring

/-- Encode a selected ideal element by its accepted residue and its difference from the chosen
lift. -/
noncomputable def rayKernelPointsToCoset [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hcop : IsCoprimeTo m J) :
    rayKernelPoints m J → acceptedResidues m × (modulusIdeal m * J) := by
  classical
  let hJM := (isCoprimeTo_iff_sup m J).mp hcop |>.2
  let lift := acceptedResidueLift m J hJM
  let hLift := acceptedResidueLift_spec m J hJM
  intro x
  have hxresExists : ∃ u : (𝓞 K)ˣ,
      Ideal.Quotient.mk (modulusIdeal m) (u : 𝓞 K) =
        Ideal.Quotient.mk (modulusIdeal m) x.1.1 := by
    by_cases hex : ∃ u : (𝓞 K)ˣ,
        Ideal.Quotient.mk (modulusIdeal m) (u : 𝓞 K) =
          Ideal.Quotient.mk (modulusIdeal m) x.1.1
    · exact hex
    · have hxweight := x.2
      rw [rayKernelWeight_integral_residue] at hxweight
      simp [hex] at hxweight
  let r : acceptedResidues m := ⟨
    Ideal.Quotient.mk (modulusIdeal m) x.1.1,
    by
      rcases hxresExists with ⟨u, hu⟩
      exact ⟨u, hu⟩⟩
  let z : modulusIdeal m * J := ⟨x.1.1 - (lift r).1, by
    have hxmk : Ideal.Quotient.mk (modulusIdeal m) x.1.1 = r.1 := rfl
    have hlmk : Ideal.Quotient.mk (modulusIdeal m) (lift r).1 = r.1 := hLift r
    have hzero : Ideal.Quotient.mk (modulusIdeal m)
        (x.1.1 - (lift r).1) = 0 := by
      rw [map_sub, hxmk, hlmk, sub_self]
    have hzJ : x.1.1 - (lift r).1 ∈ J := J.sub_mem x.1.2 (lift r).2
    exact (integral_residue_kernel_of_sup_eq m J hJM
      ⟨x.1.1 - (lift r).1, hzJ⟩).mp hzero⟩
  exact (r, z)

/-- Reconstruct the selected ideal element from its residue and the product-ideal offset. -/
noncomputable def rayKernelPointsFromCoset [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hcop : IsCoprimeTo m J) :
    (acceptedResidues m × (modulusIdeal m * J)) → rayKernelPoints m J := by
  classical
  let hJM := (isCoprimeTo_iff_sup m J).mp hcop |>.2
  let lift := acceptedResidueLift m J hJM
  let hLift := acceptedResidueLift_spec m J hJM
  intro p
  let x : J := ⟨(lift p.1).1 + p.2.1,
    J.add_mem (lift p.1).2 (Ideal.mul_le_right p.2.2)⟩
  have hxres : Ideal.Quotient.mk (modulusIdeal m) x.1 = p.1.1 := by
    dsimp [x]
    rw [map_add, hLift]
    have hzM : p.2.1 ∈ modulusIdeal m := Ideal.mul_le_left p.2.2
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hzM, add_zero]
  have hxweight : rayKernelWeight m (algebraMap (𝓞 K) K x.1) = 1 := by
    rw [rayKernelWeight_integral_residue]
    have hu : ∃ u : (𝓞 K)ˣ,
        Ideal.Quotient.mk (modulusIdeal m) (u : 𝓞 K) =
          Ideal.Quotient.mk (modulusIdeal m) x.1 := by
      rcases p.1.2 with ⟨u, hu⟩
      exact ⟨u, hu.trans hxres.symm⟩
    simp [hu]
  exact ⟨x, hxweight⟩

private theorem rayKernelPointsToCoset_snd [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hcop : IsCoprimeTo m J)
    (x : rayKernelPoints m J) :
    (rayKernelPointsToCoset m J hcop x).2.1 = x.1.1 -
      (acceptedResidueLift m J ((isCoprimeTo_iff_sup m J).mp hcop |>.2)
        (rayKernelPointsToCoset m J hcop x).1).1 := rfl

private theorem rayKernelPointsFromCoset_residue [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hcop : IsCoprimeTo m J)
    (p : acceptedResidues m × (modulusIdeal m * J)) :
    Ideal.Quotient.mk (modulusIdeal m)
      (rayKernelPointsFromCoset m J hcop p).1.1 = p.1.1 := by
  classical
  let hJM := (isCoprimeTo_iff_sup m J).mp hcop |>.2
  let lift := acceptedResidueLift m J hJM
  have hLift := acceptedResidueLift_spec m J hJM
  change Ideal.Quotient.mk (modulusIdeal m) ((lift p.1).1 + p.2.1) = p.1.1
  rw [map_add, hLift]
  have hzM : p.2.1 ∈ modulusIdeal m := Ideal.mul_le_left p.2.2
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hzM, add_zero]

private theorem rayKernelPointsToCoset_fst_fromCoset [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hcop : IsCoprimeTo m J)
    (p : acceptedResidues m × (modulusIdeal m * J)) :
    (rayKernelPointsToCoset m J hcop (rayKernelPointsFromCoset m J hcop p)).1 = p.1 := by
  apply Subtype.ext
  exact rayKernelPointsFromCoset_residue m J hcop p

private theorem rayKernelPointsFromCoset_toCoset [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hcop : IsCoprimeTo m J)
    (x : rayKernelPoints m J) :
    rayKernelPointsFromCoset m J hcop (rayKernelPointsToCoset m J hcop x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  change (acceptedResidueLift m J
      ((isCoprimeTo_iff_sup m J).mp hcop |>.2)
      (rayKernelPointsToCoset m J hcop x).1).1 +
      (rayKernelPointsToCoset m J hcop x).2.1 = x.1.1
  rw [rayKernelPointsToCoset_snd]
  ring

private theorem rayKernelPointsToCoset_fromCoset [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hcop : IsCoprimeTo m J)
    (p : acceptedResidues m × (modulusIdeal m * J)) :
    rayKernelPointsToCoset m J hcop (rayKernelPointsFromCoset m J hcop p) = p := by
  apply Prod.ext
  · exact rayKernelPointsToCoset_fst_fromCoset m J hcop p
  · apply Subtype.ext
    change (rayKernelPointsFromCoset m J hcop p).1.1 -
        (acceptedResidueLift m J ((isCoprimeTo_iff_sup m J).mp hcop |>.2)
          (rayKernelPointsToCoset m J hcop
            (rayKernelPointsFromCoset m J hcop p)).1).1 = p.2.1
    rw [rayKernelPointsToCoset_fst_fromCoset]
    simp [rayKernelPointsFromCoset]

/-- Each selected point is uniquely a residue lift plus an element of `𝔪J`. -/
noncomputable def rayKernelPointsEquiv [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hcop : IsCoprimeTo m J) :
    rayKernelPoints m J ≃ acceptedResidues m × (modulusIdeal m * J) :=
  Equiv.ofBijective (rayKernelPointsToCoset m J hcop) ⟨
    fun x y hxy => by
      have h := congrArg (rayKernelPointsFromCoset m J hcop) hxy
      rw [rayKernelPointsFromCoset_toCoset, rayKernelPointsFromCoset_toCoset] at h
      exact h,
    fun p => ⟨rayKernelPointsFromCoset m J hcop p,
      rayKernelPointsToCoset_fromCoset m J hcop p⟩⟩

/-- The finite additive residue decomposition of a summable ray theta. -/
theorem tsum_rayKernelPoints_eq_residue_cosets [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hcop : IsCoprimeTo m J)
    (f : J → ℂ) (hf : Summable (fun x : rayKernelPoints m J => f x.1)) :
    ∑' x : rayKernelPoints m J, f x.1 =
      ∑ r : acceptedResidues m, ∑' z : modulusIdeal m * J,
        f (rayKernelPointsFromCoset m J hcop (r, z)).1 := by
  classical
  let e := rayKernelPointsEquiv m J hcop
  let g : acceptedResidues m × (modulusIdeal m * J) → ℂ :=
    fun p => f (rayKernelPointsFromCoset m J hcop p).1
  have hfeq (x : rayKernelPoints m J) : g (e x) = f x.1 := by
    change f (rayKernelPointsFromCoset m J hcop
      (rayKernelPointsToCoset m J hcop x)).1 = f x.1
    rw [rayKernelPointsFromCoset_toCoset]
  have hsource : Summable (fun x : rayKernelPoints m J => g (e x)) := by
    exact hf.congr (fun x => (hfeq x).symm)
  have htarget : Summable g := (Equiv.summable_iff e).mp hsource
  calc
    ∑' x : rayKernelPoints m J, f x.1 = ∑' x : rayKernelPoints m J, g (e x) := by
      exact tsum_congr (fun x => (hfeq x).symm)
    _ = ∑' p : acceptedResidues m × (modulusIdeal m * J), g p := Equiv.tsum_eq e g
    _ = ∑' r : acceptedResidues m, ∑' z : modulusIdeal m * J, g (r, z) :=
      htarget.tsum_prod
    _ = ∑ r : acceptedResidues m, ∑' z : modulusIdeal m * J,
        f (rayKernelPointsFromCoset m J hcop (r, z)).1 := by
      simpa only [g, tsum_fintype]

/-- The ray theta is a finite sum of Gaussian sums on the affine cosets of `𝔪J`. -/
theorem rayTheta_eq_residue_cosets [IsTotallyComplex K] (m : RayClassModulus K)
    (J : Ideal (𝓞 K)) (hcop : IsCoprimeTo m J)
    (hMJ : modulusIdeal m * J ≠ ⊥) (c : InfinitePlace K → ℝ)
    {a : ℝ} (ha : 0 < a) (hca : ∀ i, a ≤ placeWeights K c i) :
    ((rayTheta m J hcop c : ℝ) : ℂ) =
      ∑ r : acceptedResidues m, ∑' z : modulusIdeal m * J,
        weightedGaussianCM (placeWeights K c)
          (embeddingCoords K
            (algebraMap (𝓞 K) K
              (acceptedResidueLift m J
                ((isCoprimeTo_iff_sup m J).mp hcop |>.2) r).1) +
            (integralIdealCoordMap (modulusIdeal m * J) hMJ z :
              EuclideanSpace ℝ (index K))) := by
  let hJM := (isCoprimeTo_iff_sup m J).mp hcop |>.2
  let f : J → ℂ := fun x => weightedGaussianCM (placeWeights K c)
    (embeddingCoords K (algebraMap (𝓞 K) K x.1))
  have hreal := summable_integralIdealGaussian m J hcop
    (placeWeights K c) ha hca
  have hf : Summable (fun x : rayKernelPoints m J => f x.1) := by
    apply Summable.of_norm
    simpa [f, integralIdealGaussian, norm_weightedGaussianCM_apply] using hreal
  calc
    ((rayTheta m J hcop c : ℝ) : ℂ) =
        ∑' x : rayKernelPoints m J, f x.1 := by
          exact rayTheta_complex m J hcop c ha hca
    _ = ∑ r : acceptedResidues m, ∑' z : modulusIdeal m * J,
        f (rayKernelPointsFromCoset m J hcop (r, z)).1 :=
          tsum_rayKernelPoints_eq_residue_cosets m J hcop f hf
    _ = ∑ r : acceptedResidues m, ∑' z : modulusIdeal m * J,
        weightedGaussianCM (placeWeights K c)
          (embeddingCoords K
            (algebraMap (𝓞 K) K (acceptedResidueLift m J hJM r).1) +
            (integralIdealCoordMap (modulusIdeal m * J) hMJ z :
              EuclideanSpace ℝ (index K))) := by
        apply Finset.sum_congr rfl
        intro r _
        apply tsum_congr
        intro z
        change weightedGaussianCM (placeWeights K c)
          (embeddingCoords K (algebraMap (𝓞 K) K
            ((acceptedResidueLift m J hJM r).1 + z.1))) = _
        rw [map_add, embeddingCoords_add]
        rfl

/-- Poisson inversion of the ray theta: each accepted residue contributes a translated dual
Gaussian sum, with its additive Fourier phase. -/
theorem rayTheta_poisson [IsTotallyComplex K] (m : RayClassModulus K)
    (J : Ideal (𝓞 K)) (hcop : IsCoprimeTo m J)
    (hMJ : modulusIdeal m * J ≠ ⊥) (c : InfinitePlace K → ℝ)
    {a B : ℝ} (ha : 0 < a) (hca : ∀ i, a ≤ placeWeights K c i)
    (hB : 0 < B) (hcB : ∀ i, placeWeights K c i ≤ B) :
    ((rayTheta m J hcop c : ℝ) : ℂ) =
      ∑ r : acceptedResidues m,
        (ZLattice.covolume
          (idealZLattice K (idealUnit (modulusIdeal m * J) hMJ)) volume)⁻¹ •
          ∑' w : ArtinPrimitiveRoots.Hecke.Theta.dualZLattice
              (idealZLattice K (idealUnit (modulusIdeal m * J) hMJ)),
            Real.fourierChar (⟪embeddingCoords K
                (algebraMap (𝓞 K) K
                  (acceptedResidueLift m J
                    ((isCoprimeTo_iff_sup m J).mp hcop |>.2) r).1),
                (w : EuclideanSpace ℝ (index K))⟫) •
              ((Real.sqrt (∏ i, placeWeights K c i))⁻¹ •
                weightedGaussianCM (fun i => (placeWeights K c i)⁻¹)
                  (w : EuclideanSpace ℝ (index K))) := by
  rw [rayTheta_eq_residue_cosets m J hcop hMJ c ha hca]
  apply Finset.sum_congr rfl
  intro r _
  let L := idealZLattice K (idealUnit (modulusIdeal m * J) hMJ)
  let e := integralIdealCoordEquiv (modulusIdeal m * J) hMJ
  let shift := embeddingCoords K (algebraMap (𝓞 K) K
    (acceptedResidueLift m J ((isCoprimeTo_iff_sup m J).mp hcop |>.2) r).1)
  change (∑' z : modulusIdeal m * J,
      weightedGaussianCM (placeWeights K c) (shift + e z)) = _
  rw [Equiv.tsum_eq e (fun w =>
    weightedGaussianCM (placeWeights K c) (shift + (w : EuclideanSpace ℝ (index K))))]
  exact weightedGaussian_translate_transform L shift
    (fun i => lt_of_lt_of_le ha (hca i)) ha hca hB hcB

end ArtinPrimitiveRoots.Hecke

end
