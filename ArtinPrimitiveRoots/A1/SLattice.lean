import ArtinPrimitiveRoots.A1.AddChar
import ArtinPrimitiveRoots.A1.Proofs.A1_LATTICE.Core
import ArtinPrimitiveRoots.Arith.SUnit
import ArtinPrimitiveRoots.Theta.LocalInt
import ArtinPrimitiveRoots.A2.Proofs.A2_ZF_TOP.ArchFourier
import Mathlib.MeasureTheory.Group.Measure

/-!
# A1 arithmetic base: the S-integer lattice

This file records the Lean statements corresponding to `lem:s-lattice` and
`ar:balanced-compact` in the A1 blueprint.  The analytic objects are stated using the product
space `S.FS`, its diagonal S-integer subgroup, finite sums of standard archimedean Schwartz and
finite-place test functions, and a self-dual Haar measure for the character `S.e`.
The lattice outcomes take `D : FieldData F`, which supplies the paper's `μ₁₂ ⊂ F` hypothesis and
the required total-complexity property.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory
open ArtinPrimitiveRoots.A1.Theta
open scoped Classical SchwartzMap nonZeroDivisors

noncomputable section

namespace ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

local instance instMeasurableFS (S : SData F CE condη) : MeasurableSpace S.FS :=
  borel S.FS
local instance instBorelFS (S : SData F CE condη) : BorelSpace S.FS := ⟨rfl⟩

/-! ## Test functions and the self-dual measure -/

/-- Locally constant compactly supported test functions at a finite place in `S`. -/
def SData.FiniteTest (S : SData F CE condη) (v : S.Sf) :=
  {f : v.1.adicCompletion F → ℂ // Continuous f ∧ HasCompactSupport f ∧ IsLocallyConstant f}

/-- Archimedean Schwartz functions on the product of complex places. -/
abbrev SData.ArchSchwartz (F : Type) [Field F] [NumberField F] :=
  SchwartzMap (InfinitePlace F → ℂ) ℂ

/-- A pure tensor in the standard Bruhat--Schwartz space on `F_S`. -/
def SData.tensorFunction (S : SData F CE condη) (arch : SData.ArchSchwartz F)
    (finite : ∀ v : S.Sf, S.FiniteTest v) : S.FS → ℂ :=
  fun x => arch x.2 * ∏ v : S.Sf, (finite v).1 (x.1 v)

/-- The Bruhat--Schwartz space: finite linear combinations of archimedean Schwartz functions
tensored with locally constant compactly supported functions at the places in `S_f`. -/
def SData.BruhatSchwartz (S : SData F CE condη) : Submodule ℂ (S.FS → ℂ) :=
  Submodule.span ℂ (Set.range fun p : SData.ArchSchwartz F ×
      (∀ v : S.Sf, S.FiniteTest v) => S.tensorFunction p.1 p.2)

/-- The Fourier transform associated to `e` and a Haar measure on `F_S`. -/
def SData.fourier (S : SData F CE condη) (A : AddCharData F)
    (μ : Measure S.FS) (f : S.FS → ℂ) : S.FS → ℂ :=
  fun y => ∫ x, f x * S.e A (-(x * y)) ∂μ

/-- A self-dual Haar measure for the additive character `e`, characterized by Fourier inversion
on the Bruhat--Schwartz space. -/
structure SData.SelfDualMeasure (S : SData F CE condη) (A : AddCharData F) where
  measure : Measure S.FS
  isHaar : Measure.IsAddHaarMeasure measure
  fourier_inversion : ∀ f : S.BruhatSchwartz, ∀ x : S.FS,
    S.fourier A measure (S.fourier A measure (f : S.FS → ℂ)) x = (f : S.FS → ℂ) (-x)

/-! ## The lattice and its annihilator -/

/-- The diagonal image of the S-integers in `F_S`. -/
def SData.diagR (S : SData F CE condη) : Set S.FS :=
  Set.range fun x : S.R => S.diag (x : F)

/-- The annihilator of a subset of `F_S` under the pairing `e(xy)`. -/
def SData.annihilator (S : SData F CE condη) (A : AddCharData F) (Γ : Set S.FS) : Set S.FS :=
  {y | ∀ x ∈ Γ, S.e A (x * y) = 1}

/-- A measurable fundamental domain for the diagonal S-integer lattice. -/
def SData.IsLatticeFundamentalDomain (S : SData F CE condη) (K : Set S.FS) : Prop :=
  ∀ x : S.FS, ∃! p : S.R × S.FS, p.2 ∈ K ∧ x = S.diag (p.1 : F) + p.2

/-- The diagonal S-integer lattice is discrete and has compact quotient.  The compact set in the
second clause is a compact set of representatives modulo the diagonal image. -/
theorem SData.diagR_discrete_cocompact (S : SData F CE condη) (D : FieldData F) :
    IsDiscrete (S.diagR : Set S.FS) ∧
      ∃ K : Set S.FS, IsCompact K ∧
        ∀ x : S.FS, ∃ r : S.R, ∃ k ∈ K, x = S.diag (r : F) + k := by
  refine ⟨?_, ?_⟩
  · simpa [SData.diagR] using
      ArtinPrimitiveRoots.Proofs.A1_LATTICE.diagR_isDiscrete S D
  · exact ArtinPrimitiveRoots.Proofs.A1_LATTICE.diagR_has_compact_cover S D

/-- The S-integer lattice is its own annihilator for the pairing `e(xy)`. -/
theorem SData.diagR_eq_annihilator (S : SData F CE condη) (D : FieldData F)
    (A : AddCharData F) :
    S.diagR = S.annihilator A S.diagR := by
  sorry

private noncomputable def covolArchToMixedEquiv (D : FieldData F) :
    (InfinitePlace F → ℂ) ≃L[ℝ] NumberField.mixedEmbedding.mixedSpace F := by
  let e : (InfinitePlace F → ℂ) ≃ₗ[ℝ] NumberField.mixedEmbedding.mixedSpace F :=
    { toFun := fun z =>
        (fun w : {w : InfinitePlace F // NumberField.InfinitePlace.IsReal w} =>
          False.elim
            ((NumberField.InfinitePlace.not_isComplex_iff_isReal.mpr w.2)
              (D.isTotallyComplex.isComplex w.1)),
          fun w : {w : InfinitePlace F // NumberField.InfinitePlace.IsComplex w} => z w.1)
      invFun := fun z w => z.2 ⟨w, D.isTotallyComplex.isComplex w⟩
      left_inv := by intro z; rfl
      right_inv := by
        intro z
        apply Prod.ext
        · funext w
          exact False.elim
            ((NumberField.InfinitePlace.not_isComplex_iff_isReal.mpr w.2)
              (D.isTotallyComplex.isComplex w.1))
        · funext w
          rfl
      map_add' := by
        intro x y
        apply Prod.ext
        · funext w
          exact False.elim
            ((NumberField.InfinitePlace.not_isComplex_iff_isReal.mpr w.2)
              (D.isTotallyComplex.isComplex w.1))
        · funext w
          rfl
      map_smul' := by
        intro c x
        apply Prod.ext
        · funext w
          exact False.elim
            ((NumberField.InfinitePlace.not_isComplex_iff_isReal.mpr w.2)
              (D.isTotallyComplex.isComplex w.1))
        · funext w
          simp }
  have hecont : Continuous e := by
    refine continuous_prodMk.mpr ⟨continuous_const, continuous_pi ?_⟩
    intro w
    exact continuous_apply w.1
  exact e.toContinuousLinearEquivOfContinuous hecont

private theorem covol_complexPiSelfDualHaar_eq_smul_volume
    (ι : Type*) [Fintype ι] :
    ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiSelfDualHaar ι =
      ENNReal.ofReal ((2 : ℝ) ^ Fintype.card ι) • (volume : Measure (ι → ℂ)) := by
  classical
  let eArch : PiLp 2 (fun _ : ι => ℂ) ≃ᵐ (ι → ℂ) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℂ)).toHomeomorph.toMeasurableEquiv
  let b : OrthonormalBasis (Σ _ : ι, Fin 2) ℝ (PiLp 2 (fun _ : ι => ℂ)) :=
    Pi.orthonormalBasis (fun i : ι => Complex.orthonormalBasisOneI)
  let eArchCoord : PiLp 2 (fun _ : ι => ℂ) ≃ᵐ ((Σ _ : ι, Fin 2) → ℝ) :=
    b.repr.toMeasurableEquiv.trans
      (MeasurableEquiv.toLp 2 ((Σ _ : ι, Fin 2) → ℝ)).symm
  let ePiCoord : (ι → ℂ) ≃ᵐ ((Σ _ : ι, Fin 2) → ℝ) :=
    (MeasurableEquiv.piCongrRight (fun _ : ι => Complex.measurableEquivPi)).trans
      (MeasurableEquiv.piCurry (fun _ : ι => fun _ : Fin 2 => ℝ)).symm
  have hPiPoint : MeasurePreserving
      (MeasurableEquiv.piCongrRight (fun _ : ι => Complex.measurableEquivPi)) := by
    change MeasurePreserving
      (fun x : ι → ℂ => fun i => Complex.measurableEquivPi (x i))
    exact MeasureTheory.measurePreserving_pi (fun _ : ι => volume) (fun _ : ι => volume)
      (fun _ => Complex.volume_preserving_equiv_pi)
  have hPiCurry : MeasurePreserving
      (MeasurableEquiv.piCurry (fun _ : ι => fun _ : Fin 2 => ℝ)).symm := by
    refine ⟨(MeasurableEquiv.piCurry (fun _ : ι => fun _ : Fin 2 => ℝ)).symm.measurable, ?_⟩
    apply (Measure.pi_eq (μ := fun _ : Σ _ : ι, Fin 2 => (volume : Measure ℝ))
      (μ' := (volume : Measure (ι → Fin 2 → ℝ)).map
        (MeasurableEquiv.piCurry (fun _ : ι => fun _ : Fin 2 => ℝ)).symm) ?_).symm
    intro s hs
    rw [Measure.map_apply
      (MeasurableEquiv.piCurry (fun _ : ι => fun _ : Fin 2 => ℝ)).symm.measurable
      (MeasurableSet.univ_pi hs)]
    have hpre : (MeasurableEquiv.piCurry (fun _ : ι => fun _ : Fin 2 => ℝ)).symm ⁻¹'
        Set.pi Set.univ s = Set.pi Set.univ (fun i => Set.pi Set.univ (fun j => s ⟨i, j⟩)) := by
      ext x
      simp only [Set.mem_preimage, MeasurableEquiv.coe_piCurry_symm, Set.mem_pi,
        Set.mem_univ, true_implies, Sigma.uncurry]
      constructor
      · intro hx i j
        exact hx ⟨i, j⟩
      · intro hx ⟨i, j⟩
        exact hx i j
    rw [hpre]
    simp only [volume_pi_pi, Fintype.prod_sigma]
  have hPiCoord : MeasurePreserving ePiCoord := by
    dsimp [ePiCoord]
    exact hPiPoint.trans hPiCurry
  have hArchCoord : MeasurePreserving eArchCoord := by
    dsimp [eArchCoord]
    exact (LinearIsometryEquiv.measurePreserving b.repr).trans
      (PiLp.volume_preserving_ofLp (Σ _ : ι, Fin 2))
  have hcoordEq : eArchCoord = eArch.trans ePiCoord := by
    ext x ij
    rcases ij with ⟨i, j⟩
    change (b.repr (WithLp.toLp 2 (WithLp.ofLp x))).ofLp ⟨i, j⟩ =
      Complex.measurableEquivPi (WithLp.ofLp x i) j
    rw [Pi.orthonormalBasis_repr]
    simp [Complex.orthonormalBasisOneI_repr_apply]
  have hcoordFun : (fun x => ePiCoord (eArch x)) = eArchCoord := by
    funext x
    have hfun := congrArg (fun e : _ ≃ᵐ _ => (e : _ → _)) hcoordEq
    change (ePiCoord ∘ eArch) x = eArchCoord x
    exact (congrFun hfun x).symm
  have hArch : MeasurePreserving eArch := by
    refine ⟨eArch.measurable, ?_⟩
    apply (ePiCoord.measurableEmbedding).map_injective
    calc
      (volume.map eArch).map ePiCoord = volume.map (fun x => ePiCoord (eArch x)) := by
        simpa only [Function.comp_def] using
          (Measure.map_map ePiCoord.measurable eArch.measurable (μ := volume))
      _ = volume := by
        simpa only [hcoordFun] using hArchCoord.map_eq
      _ = volume.map ePiCoord := hPiCoord.map_eq.symm
  change Measure.map eArch
      (ENNReal.ofReal ((2 : ℝ) ^ Fintype.card ι) •
        (volume : Measure (PiLp 2 (fun _ : ι => ℂ)))) = _
  rw [Measure.map_smul _ eArch.measurable.aemeasurable, hArch.map_eq]

private theorem covolArchToMixedEquiv_volumePreserving (D : FieldData F) :
    MeasurePreserving (covolArchToMixedEquiv D) := by
  classical
  let R := {w : InfinitePlace F // NumberField.InfinitePlace.IsReal w}
  let C := {w : InfinitePlace F // NumberField.InfinitePlace.IsComplex w}
  let N := {w : InfinitePlace F // ¬ NumberField.InfinitePlace.IsReal w}
  letI : IsEmpty R := ⟨fun w =>
    (NumberField.InfinitePlace.not_isComplex_iff_isReal.mpr w.2)
      (D.isTotallyComplex.isComplex w.1)⟩
  let eSplit := MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : InfinitePlace F => ℂ) (fun w => NumberField.InfinitePlace.IsReal w)
  let eIndex : N ≃ C := Equiv.subtypeEquivRight
    (fun w => NumberField.InfinitePlace.not_isReal_iff_isComplex)
  let eRealCUnit : (R → ℂ) ≃ᵐ Unit :=
    MeasurableEquiv.ofUniqueOfUnique (R → ℂ) Unit
  let eRealRUnit : (R → ℝ) ≃ᵐ Unit :=
    MeasurableEquiv.ofUniqueOfUnique (R → ℝ) Unit
  let eReal : (R → ℂ) ≃ᵐ (R → ℝ) := eRealCUnit.trans eRealRUnit.symm
  let eComplex : (N → ℂ) ≃ᵐ (C → ℂ) :=
    MeasurableEquiv.piCongrLeft (fun _ : C => ℂ) eIndex
  let eMix := MeasurableEquiv.prodCongr eReal eComplex
  have hSplit : MeasurePreserving eSplit := by
    simpa [eSplit, volume_pi] using
      (MeasureTheory.volume_preserving_piEquivPiSubtypeProd
        (fun _ : InfinitePlace F => ℂ) (fun w => NumberField.InfinitePlace.IsReal w))
  have hRC : MeasurePreserving eRealCUnit := by
    change MeasurePreserving
      (MeasurableEquiv.ofUniqueOfUnique (R → ℂ) Unit) volume volume
    exact MeasureTheory.volume_preserving_pi_empty (fun _ : R => ℂ)
  have hRR : MeasurePreserving eRealRUnit := by
    change MeasurePreserving
      (MeasurableEquiv.ofUniqueOfUnique (R → ℝ) Unit) volume volume
    exact MeasureTheory.volume_preserving_pi_empty (fun _ : R => ℝ)
  have hReal : MeasurePreserving eReal := by
    dsimp [eReal]
    exact hRC.trans hRR.symm
  have hComplex : MeasurePreserving eComplex := by
    dsimp [eComplex]
    exact MeasureTheory.volume_measurePreserving_piCongrLeft
      (fun _ : C => ℂ) eIndex
  have hMix : MeasurePreserving eMix := by
    dsimp [eMix]
    exact MeasurePreserving.prod hReal hComplex
  have hAll : MeasurePreserving (eSplit.trans eMix) := by
    have h := hSplit.trans hMix
    simpa [volume_pi] using h
  have hfun : (covolArchToMixedEquiv D :
      (InfinitePlace F → ℂ) → NumberField.mixedEmbedding.mixedSpace F) =
      (eSplit.trans eMix) := by
    funext z
    apply Prod.ext
    · funext w
      exact isEmptyElim w
    · funext w
      change z w.1 = z (eIndex.symm w).1
      congr 1
  simpa only [hfun] using hAll

private noncomputable def covol_arch_fundamental_region
    (D : FieldData F) : Set (InfinitePlace F → ℂ) :=
  (covolArchToMixedEquiv D).symm ''
    ZSpan.fundamentalDomain (NumberField.mixedEmbedding.latticeBasis F)

private theorem covol_arch_fundamental_region_measure
    (D : FieldData F) :
    ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiSelfDualHaar (InfinitePlace F)
      (covol_arch_fundamental_region D) =
    ENNReal.ofReal (Real.sqrt (Ideal.absNorm (differentIdeal ℤ (𝓞 F)) : ℝ)) := by
  classical
  let e := covolArchToMixedEquiv D
  let P : Set (NumberField.mixedEmbedding.mixedSpace F) :=
    ZSpan.fundamentalDomain (NumberField.mixedEmbedding.latticeBasis F)
  have hPmeas : MeasurableSet P := ZSpan.fundamentalDomain_measurableSet _
  have hregion : covol_arch_fundamental_region D = e ⁻¹' P := by
    change e.symm '' P = e ⁻¹' P
    ext z
    constructor
    · rintro ⟨p, hp, rfl⟩
      simpa using hp
    · intro hz
      exact ⟨e z, hz, e.symm_apply_apply z⟩
  have hvol : volume (covol_arch_fundamental_region D) = volume P := by
    rw [hregion]
    exact (covolArchToMixedEquiv_volumePreserving D).measure_preimage
      hPmeas.nullMeasurableSet
  have hcard : Fintype.card (InfinitePlace F) = NumberField.InfinitePlace.nrComplexPlaces F := by
    change Fintype.card (InfinitePlace F) = Fintype.card
      {w : InfinitePlace F // NumberField.InfinitePlace.IsComplex w}
    exact Fintype.card_congr
      { toFun := fun w => ⟨w, D.isTotallyComplex.isComplex w⟩
        invFun := fun w => w.1
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hdiff : (Ideal.absNorm (differentIdeal ℤ (𝓞 F)) : ℝ) =
      ‖(discr F : ℝ)‖ := by
    rw [NumberField.absNorm_differentIdeal F (𝓞 F)]
    norm_cast
    simp [Int.norm_eq_abs]
  rw [covol_complexPiSelfDualHaar_eq_smul_volume]
  simp only [Measure.smul_apply]
  rw [hvol, NumberField.mixedEmbedding.volume_fundamentalDomain_latticeBasis]
  rw [hcard]
  have hscale : ENNReal.ofReal ((2 : ℝ) ^ NumberField.InfinitePlace.nrComplexPlaces F) =
      (2 : ENNReal) ^ NumberField.InfinitePlace.nrComplexPlaces F := by
    rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [hscale]
  have hcancel : (2 : ENNReal) ^ NumberField.InfinitePlace.nrComplexPlaces F *
      ((2 : ENNReal)⁻¹ ^ NumberField.InfinitePlace.nrComplexPlaces F) = 1 := by
    rw [← mul_pow,
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
  simp only [smul_eq_mul]
  rw [← mul_assoc, hcancel, one_mul]
  have hrootCast :
      (NNReal.sqrt ‖(discr F : ℝ)‖₊ : ℝ) =
        Real.sqrt (Ideal.absNorm (differentIdeal ℤ (𝓞 F)) : ℝ) := by
    calc
      (NNReal.sqrt ‖(discr F : ℝ)‖₊ : ℝ) =
          Real.sqrt (‖(discr F : ℝ)‖₊ : ℝ) := by rw [Real.coe_sqrt]
      _ = Real.sqrt (Ideal.absNorm (differentIdeal ℤ (𝓞 F)) : ℝ) := by
          rw [coe_nnnorm, hdiff.symm]
  have hrootENN : (NNReal.sqrt ‖discr F‖₊ : ENNReal) =
      ENNReal.ofReal (Real.sqrt (Ideal.absNorm (differentIdeal ℤ (𝓞 F)) : ℝ)) := by
    calc
      (NNReal.sqrt ‖discr F‖₊ : ENNReal) =
          ENNReal.ofReal (NNReal.sqrt ‖discr F‖₊ : ℝ) := by
            rw [← ENNReal.ofReal_coe_nnreal]
      _ = ENNReal.ofReal (NNReal.sqrt ‖(discr F : ℝ)‖₊ : ℝ) := by
            congr 1
      _ = _ := by rw [hrootCast]
  simpa [hdiff, Int.norm_eq_abs] using hrootENN

private noncomputable def covol_standard_fundamental_domain
    (S : SData F CE condη) (D : FieldData F) : Set S.FS :=
  (Set.pi Set.univ (fun v : S.Sf =>
    (v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F)))) ×ˢ
      covol_arch_fundamental_region D

private theorem covol_arch_fundamental_reduction (D : FieldData F)
    (z : InfinitePlace F → ℂ) :
    ∃ a : 𝓞 F, ∃ p ∈ (covolArchToMixedEquiv D).symm ''
        ZSpan.fundamentalDomain (NumberField.mixedEmbedding.latticeBasis F),
      z = (fun w => w.embedding (a : F)) + p := by
  classical
  let e := covolArchToMixedEquiv D
  let P : Set (NumberField.mixedEmbedding.mixedSpace F) :=
    ZSpan.fundamentalDomain (NumberField.mixedEmbedding.latticeBasis F)
  let zM : NumberField.mixedEmbedding.mixedSpace F := e z
  obtain ⟨y, hy⟩ :=
    ZSpan.exist_unique_vadd_mem_fundamentalDomain
      (NumberField.mixedEmbedding.latticeBasis F) zM
  have hyP : (y : NumberField.mixedEmbedding.mixedSpace F) + zM ∈ P := by
    have hy' : (y : NumberField.mixedEmbedding.mixedSpace F) +ᵥ zM ∈ P := hy.1
    simpa only [vadd_eq_add] using hy'
  have hyInt : (y : NumberField.mixedEmbedding.mixedSpace F) ∈
      NumberField.mixedEmbedding.integerLattice F :=
    (NumberField.mixedEmbedding.mem_span_latticeBasis F).mp y.property
  have hnegInt : -(y : NumberField.mixedEmbedding.mixedSpace F) ∈
      NumberField.mixedEmbedding.integerLattice F :=
    (NumberField.mixedEmbedding.integerLattice F).neg_mem hyInt
  change ∃ a : 𝓞 F,
      NumberField.mixedEmbedding F (algebraMap (𝓞 F) F a) =
        -(y : NumberField.mixedEmbedding.mixedSpace F) at hnegInt
  obtain ⟨a, ha⟩ := hnegInt
  let pM : NumberField.mixedEmbedding.mixedSpace F := (y : _) + zM
  have hpM : pM ∈ P := by simpa [pM] using hyP
  have heDiag : e (fun w : InfinitePlace F => w.embedding (a : F)) =
      NumberField.mixedEmbedding F (a : F) := by
    apply Prod.ext
    · funext w
      exact False.elim
        ((NumberField.InfinitePlace.not_isComplex_iff_isReal.mpr w.2)
          (D.isTotallyComplex.isComplex w.1))
    · funext w
      rfl
  have hzM : zM = NumberField.mixedEmbedding F (a : F) + pM := by
    calc
      zM = -(y : NumberField.mixedEmbedding.mixedSpace F) + pM := by
        dsimp [pM, zM]
        abel
      _ = NumberField.mixedEmbedding F (a : F) + pM := by rw [← ha]
  refine ⟨a, e.symm pM, ⟨pM, hpM, rfl⟩, ?_⟩
  apply e.injective
  rw [map_add, heDiag, e.apply_symm_apply]
  exact hzM

private theorem covol_arch_fundamental_unique (D : FieldData F) (a : 𝓞 F)
    {p q : InfinitePlace F → ℂ}
    (hp : covolArchToMixedEquiv D p ∈ ZSpan.fundamentalDomain
      (NumberField.mixedEmbedding.latticeBasis F))
    (hq : covolArchToMixedEquiv D q ∈ ZSpan.fundamentalDomain
      (NumberField.mixedEmbedding.latticeBasis F))
    (h : (fun w : InfinitePlace F => w.embedding (a : F)) + p = q) :
    a = 0 ∧ p = q := by
  classical
  let e := covolArchToMixedEquiv D
  let L : Submodule ℤ (NumberField.mixedEmbedding.mixedSpace F) :=
    Submodule.span ℤ (Set.range (NumberField.mixedEmbedding.latticeBasis F))
  letI : Fintype (Module.Free.ChooseBasisIndex ℤ (𝓞 F)) := Fintype.ofFinite _
  have heDiag : e (fun w : InfinitePlace F => w.embedding (a : F)) =
      NumberField.mixedEmbedding F (a : F) := by
    apply Prod.ext
    · funext w
      exact False.elim
        ((NumberField.InfinitePlace.not_isComplex_iff_isReal.mpr w.2)
          (D.isTotallyComplex.isComplex w.1))
    · funext w
      rfl
  have hmix : NumberField.mixedEmbedding F (a : F) + e p = e q := by
    have h' := congrArg e h
    rw [map_add, heDiag] at h'
    exact h'
  have haInt' : NumberField.mixedEmbedding F (a : F) ∈
      NumberField.mixedEmbedding.integerLattice F := by
    change ∃ b : 𝓞 F, NumberField.mixedEmbedding F (algebraMap (𝓞 F) F b) = _
    exact ⟨a, rfl⟩
  have haInt : NumberField.mixedEmbedding F (a : F) ∈ L :=
    (NumberField.mixedEmbedding.mem_span_latticeBasis F).2 haInt'
  let d : L := ⟨NumberField.mixedEmbedding F (a : F), haInt⟩
  have hzero : (0 : L) +ᵥ e q ∈
      ZSpan.fundamentalDomain (NumberField.mixedEmbedding.latticeBasis F) := by
    simpa using hq
  have hshift : (-d) +ᵥ e q ∈
      ZSpan.fundamentalDomain (NumberField.mixedEmbedding.latticeBasis F) := by
    have htrans : -(NumberField.mixedEmbedding F (a : F)) + e q = e p := by
      calc
        -(NumberField.mixedEmbedding F (a : F)) + e q =
            -(NumberField.mixedEmbedding F (a : F)) +
              (NumberField.mixedEmbedding F (a : F) + e p) := by rw [← hmix]
        _ = e p := by abel
    have hshiftAdd : ((-d : L) : NumberField.mixedEmbedding.mixedSpace F) + e q ∈
        ZSpan.fundamentalDomain (NumberField.mixedEmbedding.latticeBasis F) := by
      change -(NumberField.mixedEmbedding F (a : F)) + e q ∈ _
      rw [htrans]
      exact hp
    change ((-d : L) : NumberField.mixedEmbedding.mixedSpace F) + e q ∈ _
    exact hshiftAdd
  have hzeroFloor := (ZSpan.vadd_mem_fundamentalDomain
    (NumberField.mixedEmbedding.latticeBasis F) (0 : L) (e q)).mp hzero
  have hshiftFloor := (ZSpan.vadd_mem_fundamentalDomain
    (NumberField.mixedEmbedding.latticeBasis F) (-d) (e q)).mp hshift
  have hd : d = 0 := by
    have h0d : (0 : L) = -d := hzeroFloor.trans hshiftFloor.symm
    have hneg := congrArg (fun x : L => -x) h0d
    simpa using hneg.symm
  have hmix0 : NumberField.mixedEmbedding F (a : F) = 0 := congrArg Subtype.val hd
  have haF : (a : F) = 0 := NumberField.mixedEmbedding_injective F (by simpa using hmix0)
  have ha : a = 0 := Subtype.ext haF
  refine ⟨ha, ?_⟩
  subst a
  funext w
  simpa using congrFun h w

private theorem covol_standard_fundamental_domain_measurable_fd
    (S : SData F CE condη) (D : FieldData F) :
    MeasurableSet (covol_standard_fundamental_domain S D) ∧
      S.IsLatticeFundamentalDomain (covol_standard_fundamental_domain S D) := by
  classical
  letI : MeasurableSpace (∀ v : S.Sf, v.1.adicCompletion F) :=
    borel (∀ v : S.Sf, v.1.adicCompletion F)
  letI : BorelSpace (∀ v : S.Sf, v.1.adicCompletion F) := ⟨rfl⟩
  let O : ∀ v : S.Sf, Set (v.1.adicCompletion F) :=
    fun v => v.1.adicCompletionIntegers F
  let B : Set (∀ v : S.Sf, v.1.adicCompletion F) := Set.pi Set.univ O
  have hOopen (v : S.Sf) : IsOpen (O v) := Valued.isOpen_valuationSubring _
  have hBopen : IsOpen B := by
    apply isOpen_set_pi Set.finite_univ
    intro v hv
    exact hOopen v
  have hBmeas : MeasurableSet B := hBopen.measurableSet
  have hcompletion (v : S.Sf) (z : F) (hz : v.1.valuation F z ≤ 1) :
      algebraMap F (v.1.adicCompletion F) z ∈ v.1.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    change Valued.v (z : v.1.adicCompletion F) ≤ 1
    rw [v.1.valuedAdicCompletion_eq_valuation']
    exact hz
  let e := covolArchToMixedEquiv D
  let P : Set (NumberField.mixedEmbedding.mixedSpace F) :=
    ZSpan.fundamentalDomain (NumberField.mixedEmbedding.latticeBasis F)
  let C : Set (InfinitePlace F → ℂ) := e.symm '' P
  have hPmeas : MeasurableSet P := ZSpan.fundamentalDomain_measurableSet _
  have hCeq : C = e ⁻¹' P := by
    ext z
    constructor
    · rintro ⟨p, hp, rfl⟩
      simpa using hp
    · intro hz
      exact ⟨e z, hz, e.symm_apply_apply z⟩
  have hCmeas : MeasurableSet C := by
    rw [hCeq]
    exact e.continuous.measurable hPmeas
  let K : Set S.FS := B ×ˢ C
  have hKeq : K = Prod.fst ⁻¹' B ∩ Prod.snd ⁻¹' C := by
    ext z
    simp [K]
  have hKmeas : MeasurableSet K := by
    rw [hKeq]
    exact (continuous_fst.measurable hBmeas).inter
      (continuous_snd.measurable hCmeas)
  have hfund : S.IsLatticeFundamentalDomain K := by
    intro x
    obtain ⟨r₀, hr₀⟩ := ArtinPrimitiveRoots.Proofs.A1_LATTICE.s_integer_finite_approx S x.1
    obtain ⟨a, p, hp, harch⟩ := covol_arch_fundamental_reduction D
      (x.2 - fun w => w.embedding (r₀ : F))
    let aR : S.R := algebraMap (𝓞 F) (S.R) a
    let r : S.R := r₀ + aR
    have hrCast : (r : F) = (r₀ : F) + (a : F) := by
      simp [r, aR]
    let k : S.FS := x - S.diag (r : F)
    have hkB : k.1 ∈ B := by
      change ∀ v : S.Sf, v ∈ Set.univ → k.1 v ∈ O v
      intro v _
      have h₁ := hr₀ v
      have h₂ : algebraMap F (v.1.adicCompletion F) (a : F) ∈ O v := by
        simpa [O] using hcompletion v (a : F) (v.1.valuation_le_one a)
      have hsub := (v.1.adicCompletionIntegers F).sub_mem h₁ h₂
      change x.1 v - algebraMap F (v.1.adicCompletion F) (r : F) ∈ O v
      rw [hrCast, map_add]
      simpa [O, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsub
    have hkArch : k.2 ∈ C := by
      have hfun : (fun w : InfinitePlace F => x.2 w - w.embedding (r : F)) = p := by
        funext w
        have hw := congrFun harch w
        have hw' : x.2 w - w.embedding (r₀ : F) = w.embedding (a : F) + p w := by
          simpa using hw
        rw [hrCast, map_add]
        calc
          x.2 w - (w.embedding (r₀ : F) + w.embedding (a : F)) =
              (x.2 w - w.embedding (r₀ : F)) - w.embedding (a : F) := by abel
          _ = (w.embedding (a : F) + p w) - w.embedding (a : F) := by rw [hw']
          _ = p w := by abel
      change (fun w : InfinitePlace F => x.2 w - w.embedding (r : F)) ∈ C
      rw [hfun]
      exact hp
    have hk : k ∈ K := ⟨hkB, hkArch⟩
    have hrep : x = S.diag (r : F) + k := by
      dsimp [k]
      abel
    refine ⟨(r, k), ⟨hk, hrep⟩, ?_⟩
    intro q hq
    rcases q with ⟨s, l⟩
    have hlB : l.1 ∈ B := hq.1.1
    have hlC : l.2 ∈ C := hq.1.2
    have hKfinite (z : S.FS) (hz : z ∈ K) (v : S.Sf) : z.1 v ∈ O v := by
      have hzB : z.1 ∈ B := hz.1
      exact hzB v (by simp)
    have hkO (v : S.Sf) : k.1 v ∈ O v := hKfinite k hk v
    have hlO (v : S.Sf) : l.1 v ∈ O v := by
      exact hKfinite l ⟨hlB, hlC⟩ v
    have hdeltaLocal (v : S.Sf) :
        algebraMap F (v.1.adicCompletion F) ((s : F) - (r : F)) ∈
          v.1.adicCompletionIntegers F := by
      have hkr : x.1 v =
          algebraMap F (v.1.adicCompletion F) (r : F) + k.1 v := by
        have h := congrArg (fun z : S.FS => z.1 v) hrep
        simpa [ArtinPrimitiveRoots.A1.SData.diag] using h
      have hsl : x.1 v =
          algebraMap F (v.1.adicCompletion F) (s : F) + l.1 v := by
        have h := congrArg (fun z : S.FS => z.1 v) hq.2
        simpa [ArtinPrimitiveRoots.A1.SData.diag] using h
      have hR : algebraMap F (v.1.adicCompletion F) (r : F) = x.1 v - k.1 v := by
        calc
          algebraMap F (v.1.adicCompletion F) (r : F) =
              (algebraMap F (v.1.adicCompletion F) (r : F) + k.1 v) - k.1 v := by abel
          _ = x.1 v - k.1 v := by rw [← hkr]
      have hS : algebraMap F (v.1.adicCompletion F) (s : F) = x.1 v - l.1 v := by
        calc
          algebraMap F (v.1.adicCompletion F) (s : F) =
              (algebraMap F (v.1.adicCompletion F) (s : F) + l.1 v) - l.1 v := by abel
          _ = x.1 v - l.1 v := by rw [← hsl]
      have hdelta : algebraMap F (v.1.adicCompletion F) ((s : F) - (r : F)) =
          k.1 v - l.1 v := by
        rw [map_sub]
        calc
          algebraMap F (v.1.adicCompletion F) (s : F) -
              algebraMap F (v.1.adicCompletion F) (r : F) =
              (x.1 v - l.1 v) - (x.1 v - k.1 v) := by rw [hS, hR]
          _ = k.1 v - l.1 v := by abel
      rw [hdelta]
      exact (v.1.adicCompletionIntegers F).sub_mem (hkO v) (hlO v)
    have hval (v : HeightOneSpectrum (𝓞 F)) : v.valuation F ((s : F) - (r : F)) ≤ 1 := by
      by_cases hv : v ∈ S.Sf
      · let vS : S.Sf := ⟨v, hv⟩
        have hvint := hdeltaLocal vS
        simp [HeightOneSpectrum.algebraMap_adicCompletion] at hvint
        rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hvint
        rw [vS.1.valuedAdicCompletion_eq_valuation'] at hvint
        exact hvint
      · exact (s - r).property v hv
    obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F
      ((s : F) - (r : F)) hval
    have hlC' : l.2 ∈ C := hq.1.2
    change l.2 ∈ e.symm '' P at hlC'
    change k.2 ∈ e.symm '' P at hkArch
    obtain ⟨pL, hpL, hpLeq⟩ := hlC'
    obtain ⟨pK, hpK, hpKeq⟩ := hkArch
    have heL : e l.2 = pL := by rw [← hpLeq]; exact e.apply_symm_apply pL
    have heK : e k.2 = pK := by rw [← hpKeq]; exact e.apply_symm_apply pK
    have harchRel : (fun w : InfinitePlace F => w.embedding (b : F)) + l.2 = k.2 := by
      funext w
      have hkr : x.2 w = w.embedding (r : F) + k.2 w := by
        have h := congrArg (fun z : S.FS => z.2 w) hrep
        simpa [ArtinPrimitiveRoots.A1.SData.diag] using h
      have hsl : x.2 w = w.embedding (s : F) + l.2 w := by
        have h := congrArg (fun z : S.FS => z.2 w) hq.2
        simpa [ArtinPrimitiveRoots.A1.SData.diag] using h
      calc
        w.embedding (b : F) + l.2 w =
            w.embedding ((s : F) - (r : F)) + l.2 w := by rw [← hb]
        _ = (w.embedding (s : F) - w.embedding (r : F)) + l.2 w := by rw [map_sub]
        _ = (w.embedding (s : F) + l.2 w) - w.embedding (r : F) := by abel
        _ = x.2 w - w.embedding (r : F) := by rw [← hsl]
        _ = (w.embedding (r : F) + k.2 w) - w.embedding (r : F) := by rw [hkr]
        _ = k.2 w := by abel
    have hbL : e l.2 ∈ P := by rw [heL]; exact hpL
    have hbK : e k.2 ∈ P := by rw [heK]; exact hpK
    obtain ⟨hb0, hklArch⟩ := covol_arch_fundamental_unique D b hbL hbK harchRel
    have hdelta0 : (s : F) - (r : F) = 0 := by
      rw [hb0] at hb
      simpa using hb.symm
    have hsr : s = r := Subtype.ext (sub_eq_zero.mp hdelta0)
    have hsum : S.diag (r : F) + k = S.diag (s : F) + l := hrep.symm.trans hq.2
    rw [hsr] at hsum
    have hkl : k = l := add_left_cancel hsum
    exact Prod.ext hsr hkl.symm
  have hKdef : K = covol_standard_fundamental_domain S D := rfl
  constructor
  · rw [← hKdef]
    exact hKmeas
  · rw [← hKdef]
    exact hfund

private instance covolAdicCompletionSeparableSpace (v : FinPlace F) :
    TopologicalSpace.SeparableSpace (v.adicCompletion F) := by
  letI : Countable F := by
    letI : Countable ℚ := inferInstance
    exact Finsupp.Countable.of_moduleFinite (R := ℚ) (M := F)
  exact TopologicalSpace.SeparableSpace.of_denseRange
    (algebraMap F (v.adicCompletion F)) (v.denseRange_algebraMap (K := F))

private instance covolAdicCompletionSecondCountable (v : FinPlace F) :
    SecondCountableTopology (v.adicCompletion F) :=
  UniformSpace.secondCountable_of_separable (v.adicCompletion F)

private instance covolAdicCompletionLocallyCompactSpace (v : FinPlace F) :
    LocallyCompactSpace (v.adicCompletion F) := by
  have hK : IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    ArtinPrimitiveRoots.Proofs.A1_LATTICE.adicCompletionIntegers_compact v
  have hO : IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    Valued.isOpen_valuationSubring _
  have hz : (0 : v.adicCompletion F) ∈ v.adicCompletionIntegers F :=
    (v.adicCompletionIntegers F).zero_mem
  exact IsCompact.locallyCompactSpace_of_mem_nhds_of_addGroup hK
    (hO.mem_nhds hz)

private theorem covol_self_dual_measure_unique
    (S : SData F CE condη) (A : AddCharData F)
    (μ ν : S.SelfDualMeasure A) (f : S.BruhatSchwartz)
    (hf : (f : S.FS → ℂ) 0 ≠ 0) : μ.measure = ν.measure := by
  classical
  letI : ∀ v : S.Sf, SecondCountableTopology (v.1.adicCompletion F) :=
    fun v => inferInstance
  letI : ∀ v : S.Sf, LocallyCompactSpace (v.1.adicCompletion F) :=
    fun v => inferInstance
  letI : SecondCountableTopology S.FS := inferInstance
  letI : LocallyCompactSpace S.FS := inferInstance
  letI : Measure.IsAddHaarMeasure μ.measure := μ.isHaar
  letI : Measure.IsAddHaarMeasure ν.measure := ν.isHaar
  let c : NNReal := Measure.addHaarScalarFactor μ.measure ν.measure
  have hmeasure : μ.measure = (c : ENNReal) • ν.measure := by
    simpa [c] using Measure.isAddLeftInvariant_eq_smul μ.measure ν.measure
  have hF (g : S.FS → ℂ) :
      S.fourier A μ.measure g = fun y => (c : ℂ) * S.fourier A ν.measure g y := by
    funext y
    simp only [SData.fourier]
    rw [hmeasure, MeasureTheory.integral_smul_measure]
    simp [c, smul_eq_mul]
  have hF_smul (d : ℂ) (g : S.FS → ℂ) :
      S.fourier A ν.measure (fun y => d * g y) =
        (fun x => d * S.fourier A ν.measure g x) := by
    funext x
    simp only [SData.fourier]
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    funext y
    ring
  have hdouble (x : S.FS) :
      S.fourier A μ.measure (S.fourier A μ.measure (f : S.FS → ℂ)) x =
        (c : ℂ) ^ 2 *
          S.fourier A ν.measure (S.fourier A ν.measure (f : S.FS → ℂ)) x := by
    calc
      _ = (c : ℂ) * S.fourier A ν.measure
          (S.fourier A μ.measure (f : S.FS → ℂ)) x := by rw [hF]
      _ = (c : ℂ) * S.fourier A ν.measure
          (fun y => (c : ℂ) * S.fourier A ν.measure (f : S.FS → ℂ) y) x := by rw [hF f]
      _ = _ := by rw [hF_smul]; ring
  have hμ := μ.fourier_inversion f 0
  rw [hdouble, ν.fourier_inversion f 0] at hμ
  have hc2 : (c : ℂ) ^ 2 = 1 := (mul_eq_right₀ hf).mp (by simpa using hμ)
  have hcReal : (c : ℝ) ^ 2 = 1 := by exact_mod_cast hc2
  have hc : c = 1 := by
    apply Subtype.ext
    rcases sq_eq_one_iff.mp hcReal with h | h
    · exact h
    · have hcNonneg : 0 ≤ (c : ℝ) := NNReal.coe_nonneg c
      linarith
  simpa [hc] using hmeasure

private noncomputable def covol_arch_bump :
    ContDiffBump (0 : InfinitePlace F → ℂ) :=
  ⟨1, 2, by norm_num, by norm_num⟩

private noncomputable def covol_arch_test : SData.ArchSchwartz F :=
  (covol_arch_bump.hasCompactSupport.toSchwartzMap covol_arch_bump.contDiff).postcompCLM
    Complex.ofRealCLM

private theorem covol_arch_test_zero : covol_arch_test (0 : InfinitePlace F → ℂ) = 1 := by
  change Complex.ofReal (covol_arch_bump.toFun (0 : InfinitePlace F → ℂ)) =
    Complex.ofReal (1 : ℝ)
  exact congrArg Complex.ofReal covol_arch_bump.eventuallyEq_one.eq_of_nhds

private theorem covol_local_integer_compact (v : FinPlace F) :
    IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
  ArtinPrimitiveRoots.Proofs.A1_LATTICE.adicCompletionIntegers_compact v

private theorem covol_local_integer_clopen (v : FinPlace F) :
    IsClopen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  exact ⟨(covol_local_integer_compact v).isClosed,
    Valued.isOpen_valuationSubring _⟩

private theorem covol_local_integer_indicator_locallyConstant (v : FinPlace F) :
    IsLocallyConstant
      ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator
        (fun _ => (1 : ℂ))) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  by_cases hx : x ∈ v.adicCompletionIntegers F
  · refine ⟨v.adicCompletionIntegers F, (covol_local_integer_clopen v).isOpen, hx, ?_⟩
    intro y hy
    simp [hx, hy]
  · refine ⟨(v.adicCompletionIntegers F)ᶜ,
      (covol_local_integer_clopen v).isClosed.isOpen_compl, hx, ?_⟩
    intro y hy
    have hy' : y ∉ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
      simpa only [Set.mem_compl_iff] using hy
    simp [hx, hy']

private theorem covol_local_integer_indicator_hasCompactSupport (v : FinPlace F) :
    HasCompactSupport
      ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator
        (fun _ => (1 : ℂ))) := by
  apply HasCompactSupport.intro' (covol_local_integer_compact v)
    (covol_local_integer_clopen v).isClosed
  intro x hx
  simp [hx]

private theorem covol_nonzero_bruhat_test (S : SData F CE condη) :
    ∃ f : S.BruhatSchwartz, (f : S.FS → ℂ) 0 ≠ 0 := by
  classical
  let finite : ∀ v : S.Sf, S.FiniteTest v := fun v =>
    ⟨(v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F)).indicator
        (fun _ => (1 : ℂ)),
      ⟨(covol_local_integer_indicator_locallyConstant v.1).continuous,
        covol_local_integer_indicator_hasCompactSupport v.1,
        covol_local_integer_indicator_locallyConstant v.1⟩⟩
  let p : SData.ArchSchwartz F × (∀ v : S.Sf, S.FiniteTest v) :=
    ⟨covol_arch_test, finite⟩
  let g : S.FS → ℂ := S.tensorFunction p.1 p.2
  let f : S.BruhatSchwartz :=
    ⟨g, Submodule.subset_span ⟨p, rfl⟩⟩
  refine ⟨f, ?_⟩
  have hfinite (v : S.Sf) : (finite v).1 0 = 1 := by
    simp [finite]
  change g 0 ≠ 0
  simp [g, SData.tensorFunction, p, covol_arch_test_zero, hfinite]

private theorem covol_addchar_nontrivial (D : FieldData F) (S : SData F CE condη)
    (A : AddCharData F) (v : S.Sf) :
    ∃ x : v.1.adicCompletion F, A.ψ v.1 x ≠ 1 := by
  classical
  by_contra h
  push Not at h
  let y : S.FS := (fun w => if w = v then 1 else 0, fun _ => 0)
  have hyann : y ∈ S.annihilator A S.diagR := by
    intro z hz
    rcases hz with ⟨r, rfl⟩
    have hfin (q : S.Sf) :
        A.ψ q.1 ((S.diag (r : F) * y).1 q) = 1 := by
      by_cases hq : q = v
      · subst q
        simpa [y] using h ((S.diag (r : F)).1 v)
      · simp [y, hq]
    have harch (q : InfinitePlace F) :
        psiC ((S.diag (r : F) * y).2 q) = 1 := by
      simp [psiC, y]
    change (∏ q : S.Sf, A.ψ q.1 ((S.diag (r : F) * y).1 q)) *
      ∏ q : InfinitePlace F, psiC ((S.diag (r : F) * y).2 q) = 1
    rw [Finset.prod_eq_one (fun q _ => hfin q),
      Finset.prod_eq_one (fun q _ => harch q)]
    simp
  have hdual := S.diagR_eq_annihilator D A
  have hyr : y ∈ S.diagR := by rw [hdual]; exact hyann
  obtain ⟨r, hr⟩ := hyr
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hrw : w.embedding (r : F) = 0 := by
    have h := congrArg (fun z : S.FS => z.2 w) hr
    simpa [y, SData.diag] using h
  have hr0 : (r : F) = 0 := (RingHom.injective w.embedding) (by simpa using hrw)
  have hrv : algebraMap F (v.1.adicCompletion F) (r : F) = 1 := by
    have h := congrArg (fun z : S.FS => z.1 v) hr
    simpa [y, SData.diag] using h
  have h01 : (0 : v.1.adicCompletion F) = 1 := by simpa [hr0] using hrv
  exact zero_ne_one h01

private theorem covol_local_addchar_conductor (D : FieldData F) (S : SData F CE condη)
    (A : AddCharData F) (v : S.Sf) :
    ∃ c : ℤ, 0 ≤ c ∧
      (∀ x, Valued.v x ≤ WithZero.exp c → A.ψ v.1 x = 1) ∧
      ∃ x, Valued.v x ≤ WithZero.exp (c + 1) ∧ A.ψ v.1 x ≠ 1 := by
  let P : ℤ → Prop := fun n => ∀ x : v.1.adicCompletion F,
    Valued.v x ≤ WithZero.exp n → A.ψ v.1 x = 1
  have hP0 : P 0 := by
    intro x hx
    apply A.integral v.1
    change Valued.v x ≤ 1
    simpa using hx
  obtain ⟨a, ha⟩ := covol_addchar_nontrivial D S A v
  have hav : Valued.v a ≠ 0 := by
    intro hv
    have ha0 : a = 0 := (Valuation.zero_iff (Valued.v : Valuation _ _)).mp hv
    exact ha (by simpa [ha0])
  lift Valued.v a to ℤ using hav with k hk
  have hbound : ∃ b : ℤ, ∀ n : ℤ, P n → n ≤ b := by
    refine ⟨k - 1, ?_⟩
    intro n hn
    by_contra hnot
    have hkn : k ≤ n := by omega
    have hball : Valued.v a ≤ WithZero.exp n := by
      rw [← hk]
      exact (WithZero.exp_le_exp).2 hkn
    exact ha (hn a hball)
  obtain ⟨c, hc, hcmax⟩ := Int.exists_greatest_of_bdd hbound ⟨0, hP0⟩
  have hnot : ¬ P (c + 1) := by
    intro hp
    have hle := hcmax (c + 1) hp
    omega
  change ¬ (∀ x : v.1.adicCompletion F,
    Valued.v x ≤ WithZero.exp (c + 1) → A.ψ v.1 x = 1) at hnot
  push Not at hnot
  obtain ⟨x, hx, hψ⟩ := hnot
  have hc_nonneg : 0 ≤ c := by
    have hzero := hcmax 0 hP0
    omega
  exact ⟨c, hc_nonneg, hc, x, hx, hψ⟩

private theorem covol_addchar_eq_trace_exp (S : SData F CE condη)
    (A : AddCharData F) (v : S.Sf) (r : S.R)
    (hrq : ∀ q : S.Sf, q ≠ v →
      algebraMap F (q.1.adicCompletion F) (r : F) ∈ q.1.adicCompletionIntegers F) :
    A.ψ v.1 (algebraMap F (v.1.adicCompletion F) (r : F)) =
      Complex.exp (2 * Real.pi * Complex.I * (Algebra.trace ℚ F (r : F) : ℂ)) := by
  classical
  let f : FinPlace F → ℂ := fun w =>
    A.ψ w (algebraMap F (w.adicCompletion F) (r : F))
  have houtside (w : FinPlace F) (hw : w ∉ S.Sf) : f w = 1 := by
    apply A.integral w
    change ((r : F) : w.adicCompletion F) ∈ w.adicCompletionIntegers F
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact r.property w hw
  have hinside (q : S.Sf) (hq : q ≠ v) : f q.1 = 1 := by
    apply A.integral q.1
    exact hrq q hq
  have hother (w : FinPlace F) (hw : w ≠ v.1) : f w = 1 := by
    by_cases hwS : w ∈ S.Sf
    · let q : S.Sf := ⟨w, hwS⟩
      have hq : q ≠ v := by
        intro h
        exact hw (congrArg Subtype.val h)
      simpa [f, q] using hinside q hq
    · exact houtside w hwS
  have hfin : (∏ᶠ w : FinPlace F, f w) = f v.1 :=
    finprod_eq_single f v.1 (fun w hw => hother w hw)
  have hglobal := (A.trivial_on_F (r : F)).2
  change (∏ᶠ w : FinPlace F, f w) *
      Complex.exp (-(2 * Real.pi * Complex.I * (Algebra.trace ℚ F (r : F) : ℂ))) = 1
    at hglobal
  rw [hfin] at hglobal
  have hψ : f v.1 =
      Complex.exp (2 * Real.pi * Complex.I * (Algebra.trace ℚ F (r : F) : ℂ)) := by
    have h := eq_inv_of_mul_eq_one_right hglobal
    rw [Complex.exp_neg] at h
    exact ((inv_inj).mp h).symm
  simpa [f] using hψ

private lemma covol_count_spanSingleton_div (v : FinPlace F) (x y : F)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (x / y)) =
      FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) x) -
        FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) y) := by
  rw [← FractionalIdeal.spanSingleton_div_spanSingleton, div_eq_mul_inv,
    FractionalIdeal.count_mul F v
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx)
      (inv_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hy)),
    FractionalIdeal.count_inv]
  ring

private lemma covol_count_spanSingleton_eq_neg_log_intValuation
    (v : FinPlace F) (r : 𝓞 F) (hr : r ≠ 0) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
          (algebraMap (𝓞 F) F r)) = -WithZero.log (v.intValuation r) := by
  have hspan : (Ideal.span {r} : Ideal (𝓞 F)) ≠ 0 := by
    simpa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hr
  rw [← FractionalIdeal.coeIdeal_span_singleton, hspan |> fun h =>
      FractionalIdeal.count_coe F v h, v.intValuation_if_neg hr, WithZero.log_exp]
  ring

set_option linter.unnecessarySimpa false in
private lemma covol_count_spanSingleton_eq_neg_log_valuation
    (v : FinPlace F) (z : F) (hz : z ≠ 0) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) z) =
      -WithZero.log (HeightOneSpectrum.valuation F v z) := by
  obtain ⟨n, d, hnd⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors (𝓞 F)) z
  have hn : n ≠ 0 := by
    intro hn
    apply hz
    rw [← hnd, IsFractionRing.mk'_eq_div, hn, map_zero, zero_div]
  have hd : (d : 𝓞 F) ≠ 0 := nonZeroDivisors.ne_zero d.2
  have hmapn : (algebraMap (𝓞 F) F n) ≠ 0 := by
    intro h
    exact hn ((IsFractionRing.injective (𝓞 F) F) (by simpa using h))
  have hmapd : (algebraMap (𝓞 F) F (d : 𝓞 F)) ≠ 0 := by
    intro h
    exact hd ((IsFractionRing.injective (𝓞 F) F) (by simpa using h))
  have hval : HeightOneSpectrum.valuation F v z =
      v.intValuation n / v.intValuation (d : 𝓞 F) := by
    rw [← hnd]
    exact v.valuation_of_mk'
  rw [hval, ← hnd, IsFractionRing.mk'_eq_div,
    covol_count_spanSingleton_div v (algebraMap (𝓞 F) F n)
      (algebraMap (𝓞 F) F (d : 𝓞 F)) hmapn hmapd,
    covol_count_spanSingleton_eq_neg_log_intValuation v n hn,
    covol_count_spanSingleton_eq_neg_log_intValuation v (d : 𝓞 F) hd,
    WithZero.log_div (v.intValuation_ne_zero n hn) (v.intValuation_ne_zero (d : 𝓞 F) hd)]
  ring

private abbrev covolCodifferent : FractionalIdeal (𝓞 F)⁰ F :=
  FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F)

private theorem covol_traceDual_valuation_bound (v : FinPlace F) {z : F}
    (hz0 : z ≠ 0)
    (hdual : z ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 F) F)) :
    v.valuation F z ≤ WithZero.exp
      (FractionalIdeal.count F v (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F)) := by
  let D := differentIdeal ℤ (𝓞 F)
  have hD0 : D ≠ ⊥ := differentIdeal_ne_bot
  have hDcod : (D : FractionalIdeal (𝓞 F)⁰ F) = covolCodifferent⁻¹ := by
    simpa [D, covolCodifferent] using (coeIdeal_differentIdeal ℤ ℚ F (𝓞 F))
  have hcodcount : FractionalIdeal.count F v covolCodifferent =
      -FractionalIdeal.count F v (D : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [hDcod, FractionalIdeal.count_inv]
    ring
  have hzCod : z ∈ (covolCodifferent (F := F) : Submodule (𝓞 F) F) := by
    simpa [covolCodifferent, FractionalIdeal.coe_dual_one] using hdual
  have hspanle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) z ≤
      covolCodifferent :=
    FractionalIdeal.spanSingleton_le_iff_mem.mpr hzCod
  have hcountle := FractionalIdeal.count_mono F v
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hz0) hspanle
  have hcountz := covol_count_spanSingleton_eq_neg_log_valuation v z hz0
  have hlogle : WithZero.log (v.valuation F z) ≤
      FractionalIdeal.count F v (D : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [hcountz, hcodcount] at hcountle
    linarith
  exact (WithZero.log_le_iff_le_exp
    ((v.valuation F).ne_zero_iff.mpr hz0)).mp hlogle

private theorem covol_different_mem_valuation_bound (v : FinPlace F)
    {a : 𝓞 F} (ha : a ∈ differentIdeal ℤ (𝓞 F)) :
    v.valuation F (a : F) ≤ WithZero.exp
      (-FractionalIdeal.count F v
        (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F)) := by
  by_cases ha0 : a = 0
  · simp [ha0]
  have haF0 : (a : F) ≠ 0 := by
    intro h
    apply ha0
    exact (FaithfulSMul.algebraMap_injective (𝓞 F) F) (by simpa using h)
  let D := differentIdeal ℤ (𝓞 F)
  have hspan : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F) ≤
      (D : FractionalIdeal (𝓞 F)⁰ F) := by
    apply FractionalIdeal.spanSingleton_le_iff_mem.mpr
    apply FractionalIdeal.mem_coe.mpr
    exact FractionalIdeal.mem_coeIdeal_of_mem (nonZeroDivisors (𝓞 F)) ha
  have hcount := FractionalIdeal.count_mono F v
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr haF0) hspan
  have hcountA := covol_count_spanSingleton_eq_neg_log_valuation v (a : F) haF0
  have hlog : WithZero.log (v.valuation F (a : F)) ≤
      -FractionalIdeal.count F v (D : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [hcountA] at hcount
    linarith
  exact (WithZero.log_le_iff_le_exp
    ((v.valuation F).ne_zero_iff.mpr haF0)).mp hlog

private theorem covol_traceDual_of_local_bounds {z : F}
    (hval : ∀ v : FinPlace F, v.valuation F z ≤ WithZero.exp
      (FractionalIdeal.count F v
        (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F))) :
    z ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 F) F) := by
  by_cases hz0 : z = 0
  · simp [hz0]
  let D := differentIdeal ℤ (𝓞 F)
  have hD0 : D ≠ ⊥ := differentIdeal_ne_bot
  have hDFrac0 : (D : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
    exact FractionalIdeal.coeIdeal_ne_zero.mpr hD0
  have hzInv : z ∈ (D : FractionalIdeal (𝓞 F)⁰ F)⁻¹ := by
    apply (FractionalIdeal.mem_inv_iff hDFrac0).2
    intro y hy
    obtain ⟨a, ha, hya⟩ :=
      (FractionalIdeal.mem_coeIdeal (nonZeroDivisors (𝓞 F))).mp hy
    have hprod (v : FinPlace F) : v.valuation F (z * y) ≤ 1 := by
      rw [map_mul, ← hya]
      calc
        v.valuation F z * v.valuation F (algebraMap (𝓞 F) F a) ≤
            WithZero.exp (FractionalIdeal.count F v
              (D : FractionalIdeal (𝓞 F)⁰ F)) *
              WithZero.exp (-FractionalIdeal.count F v
                (D : FractionalIdeal (𝓞 F)⁰ F)) := by
                  exact mul_le_mul (hval v)
                    (covol_different_mem_valuation_bound v ha) bot_le bot_le
        _ = 1 := by rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
    have hglobal := HeightOneSpectrum.mem_integers_of_valuation_le_one F (z * y) hprod
    exact (FractionalIdeal.mem_one_iff (nonZeroDivisors (𝓞 F))).mpr hglobal
  have hDcod : (D : FractionalIdeal (𝓞 F)⁰ F) = covolCodifferent⁻¹ := by
    simpa [D, covolCodifferent] using (coeIdeal_differentIdeal ℤ ℚ F (𝓞 F))
  have hzCod : z ∈ covolCodifferent := by
    rw [hDcod, inv_inv] at hzInv
    exact hzInv
  have hzCodSub : z ∈ (covolCodifferent (F := F) : Submodule (𝓞 F) F) :=
    FractionalIdeal.mem_coe.mpr hzCod
  simpa [covolCodifferent, FractionalIdeal.coe_dual_one] using hzCodSub

private theorem covol_local_character_trivial_on_different_ball
    (D : FieldData F) (S : SData F CE condη) (A : AddCharData F)
    (v : S.Sf) (x : v.1.adicCompletion F)
    (hx : Valued.v x ≤ WithZero.exp
      (FractionalIdeal.count F v.1
        (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F))) :
    A.ψ v.1 x = 1 := by
  classical
  let d := FractionalIdeal.count F v.1
    (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F)
  let target : ∀ q : S.Sf, q.1.adicCompletion F := fun q =>
    dite (q = v) (fun h => h.symm ▸ x) (fun _ => 0)
  obtain ⟨r, hrApprox⟩ :=
    ArtinPrimitiveRoots.Proofs.A1_LATTICE.s_integer_finite_approx S target
  have hres : x - algebraMap F (v.1.adicCompletion F) (r : F) ∈
      v.1.adicCompletionIntegers F := by
    simpa [target] using hrApprox v
  have hcompletionIntVal (q : FinPlace F) {y : q.adicCompletion F}
      (hy : y ∈ q.adicCompletionIntegers F) : Valued.v y ≤ 1 := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hy
    exact hy
  have hd_nonneg : 0 ≤ d := by
    simpa [d] using (FractionalIdeal.count_coe_nonneg F v.1
      (differentIdeal ℤ (𝓞 F)))
  have hOneLeD : 1 ≤ WithZero.exp d := WithZero.one_le_exp_iff.mpr hd_nonneg
  have hresVal : Valued.v (x - algebraMap F (v.1.adicCompletion F) (r : F)) ≤ 1 :=
    hcompletionIntVal v.1 hres
  have hresBound : Valued.v (x - algebraMap F (v.1.adicCompletion F) (r : F)) ≤
      WithZero.exp d := hresVal.trans hOneLeD
  have hrValComp : Valued.v (algebraMap F (v.1.adicCompletion F) (r : F)) ≤
      WithZero.exp d := by
    have h := (Valued.v : Valuation (v.1.adicCompletion F) _).map_sub_le hx hresBound
    simpa [sub_sub_cancel] using h
  have hrVal : v.1.valuation F (r : F) ≤ WithZero.exp d := by
    change Valued.v ((r : F) : v.1.adicCompletion F) ≤ WithZero.exp d at hrValComp
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hrValComp
    exact hrValComp
  have hother (q : S.Sf) (hqv : q ≠ v) :
      algebraMap F (q.1.adicCompletion F) (r : F) ∈ q.1.adicCompletionIntegers F := by
    have hneg : -(algebraMap F (q.1.adicCompletion F) (r : F)) ∈
        q.1.adicCompletionIntegers F := by
      simpa [target, hqv] using hrApprox q
    simpa using (q.1.adicCompletionIntegers F).neg_mem _ hneg
  have hDnonneg (q : FinPlace F) :
      0 ≤ FractionalIdeal.count F q
        (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F) := by
    simpa using (FractionalIdeal.count_coe_nonneg F q (differentIdeal ℤ (𝓞 F)))
  have hrGlobalBound (q : FinPlace F) : q.valuation F (r : F) ≤
      WithZero.exp (FractionalIdeal.count F q
        (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F)) := by
    have hOneLe : 1 ≤ WithZero.exp (FractionalIdeal.count F q
        (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F)) :=
      WithZero.one_le_exp_iff.mpr (hDnonneg q)
    by_cases hqS : q ∈ S.Sf
    · let qS : S.Sf := ⟨q, hqS⟩
      by_cases hqv : qS = v
      · have hq : q = v.1 := congrArg Subtype.val hqv
        rw [hq]
        simpa [d] using hrVal
      · have hqInt := hother qS hqv
        have hqValComp := hcompletionIntVal q hqInt
        change Valued.v ((r : F) : qS.1.adicCompletion F) ≤ 1 at hqValComp
        rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hqValComp
        exact hqValComp.trans hOneLe
    · exact (r.property q hqS).trans hOneLe
  have hrDual : (r : F) ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 F) F) :=
    covol_traceDual_of_local_bounds hrGlobalBound
  have htrace := (Submodule.mem_traceDual.mp hrDual) 1 (by simp)
  have htraceRange : Algebra.trace ℚ F (r : F) ∈ (algebraMap ℤ ℚ).range := by
    simpa only [Algebra.traceForm_apply, mul_one] using htrace
  obtain ⟨n, hn⟩ := RingHom.mem_range.mp htraceRange
  have htraceC : (Algebra.trace ℚ F (r : F) : ℂ) = (n : ℂ) := by
    exact_mod_cast hn.symm
  have hexp : Complex.exp (2 * Real.pi * Complex.I *
      (Algebra.trace ℚ F (r : F) : ℂ)) = 1 := by
    rw [htraceC]
    have harg : 2 * Real.pi * Complex.I * (n : ℂ) =
        (n : ℂ) * (2 * Real.pi * Complex.I) := by ring
    rw [harg]
    exact Complex.exp_int_mul_two_pi_mul_I n
  have hrq : ∀ q : S.Sf, q ≠ v →
      algebraMap F (q.1.adicCompletion F) (r : F) ∈ q.1.adicCompletionIntegers F :=
    fun q hqv => hother q hqv
  have hψr := covol_addchar_eq_trace_exp S A v r hrq
  rw [hexp] at hψr
  have hsum : x = algebraMap F (v.1.adicCompletion F) (r : F) +
      (x - algebraMap F (v.1.adicCompletion F) (r : F)) := by abel
  calc
    A.ψ v.1 x = A.ψ v.1
        (algebraMap F (v.1.adicCompletion F) (r : F) +
          (x - algebraMap F (v.1.adicCompletion F) (r : F))) :=
            congrArg (A.ψ v.1) hsum
    _ = A.ψ v.1 (algebraMap F (v.1.adicCompletion F) (r : F)) *
        A.ψ v.1 (x - algebraMap F (v.1.adicCompletion F) (r : F)) :=
          (A.ψ v.1).map_add_eq_mul _ _
    _ = 1 := by rw [hψr, A.integral v.1 _ hres]; simp

private theorem covol_local_character_nontrivial_at_different_successor
    (D : FieldData F) (S : SData F CE condη) (A : AddCharData F)
    (v : S.Sf) :
    ∃ x : v.1.adicCompletion F,
      Valued.v x ≤ WithZero.exp
        (FractionalIdeal.count F v.1
          (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F) + 1) ∧
      A.ψ v.1 x ≠ 1 := by
  classical
  let d := FractionalIdeal.count F v.1
    (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F)
  have hd_nonneg : 0 ≤ d := by
    simpa [d] using (FractionalIdeal.count_coe_nonneg F v.1
      (differentIdeal ℤ (𝓞 F)))
  have hboundary : 1 < WithZero.exp (d + 1) :=
    WithZero.one_lt_exp_iff.mpr (by omega)
  have hπval : Valued.v (unifLoc v.1 : v.1.adicCompletion F) =
      WithZero.exp (-1 : ℤ) := by
    have hπcoerce : (unifLoc v.1 : v.1.adicCompletion F) =
        algebraMap F (v.1.adicCompletion F) (unif (F := F) v.1) := by
      simp [unifLoc, toLoc]
    rw [hπcoerce]
    change Valued.v ((unif (F := F) v.1 : F) : v.1.adicCompletion F) = _
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    simpa [unif] using (HeightOneSpectrum.valuation_exists_uniformizer F v.1).choose_spec
  let x₀ : v.1.adicCompletion F :=
    ((unifLoc v.1 ^ (-(d + 1) : ℤ) : (v.1.adicCompletion F)ˣ) : v.1.adicCompletion F)
  have hx₀val : Valued.v x₀ = WithZero.exp (d + 1) := by
    change Valued.v
      ((unifLoc v.1 ^ (-(d + 1) : ℤ) : (v.1.adicCompletion F)ˣ) : v.1.adicCompletion F) = _
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hπval,
      ← WithZero.exp_zsmul]
    congr 1
    push_cast
    ring
  let target : ∀ q : S.Sf, q.1.adicCompletion F := fun q =>
    dite (q = v) (fun h => h.symm ▸ x₀) (fun _ => 0)
  obtain ⟨r, hrApprox⟩ :=
    ArtinPrimitiveRoots.Proofs.A1_LATTICE.s_integer_finite_approx S target
  have hres : x₀ - algebraMap F (v.1.adicCompletion F) (r : F) ∈
      v.1.adicCompletionIntegers F := by
    simpa [target] using hrApprox v
  have hresVal : Valued.v (x₀ - algebraMap F (v.1.adicCompletion F) (r : F)) ≤ 1 := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hres
    exact hres
  have hother (q : S.Sf) (hqv : q ≠ v) :
      algebraMap F (q.1.adicCompletion F) (r : F) ∈ q.1.adicCompletionIntegers F := by
    have hneg : -(algebraMap F (q.1.adicCompletion F) (r : F)) ∈
        q.1.adicCompletionIntegers F := by
      simpa [target, hqv] using hrApprox q
    simpa using (q.1.adicCompletionIntegers F).neg_mem _ hneg
  have hresLt : Valued.v (x₀ - algebraMap F (v.1.adicCompletion F) (r : F)) <
      Valued.v x₀ := lt_of_le_of_lt hresVal (by rw [hx₀val]; exact hboundary)
  have hrValComp : Valued.v (algebraMap F (v.1.adicCompletion F) (r : F)) =
      WithZero.exp (d + 1) := by
    have h := (Valued.v : Valuation (v.1.adicCompletion F) _).map_sub_eq_of_lt_left hresLt
    have hsub : x₀ - (x₀ - algebraMap F (v.1.adicCompletion F) (r : F)) =
        algebraMap F (v.1.adicCompletion F) (r : F) := by abel
    rw [hsub, hx₀val] at h
    exact h
  have hrVal : v.1.valuation F (r : F) = WithZero.exp (d + 1) := by
    change Valued.v ((r : F) : v.1.adicCompletion F) = WithZero.exp (d + 1) at hrValComp
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hrValComp
    exact hrValComp
  have hr0 : (r : F) ≠ 0 :=
    (v.1.valuation F).ne_zero_iff.mp (by rw [hrVal]; exact ne_of_gt WithZero.exp_pos)
  have hrNotDual : (r : F) ∉ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 F) F) := by
    intro hdual
    have hbound := covol_traceDual_valuation_bound v.1 hr0 hdual
    rw [hrVal] at hbound
    have hbound' : WithZero.exp (d + 1) ≤ WithZero.exp d := by
      simpa [d] using hbound
    exact (not_le_of_gt (WithZero.exp_lt_exp.mpr (by omega))) hbound'
  have htraceWitness : ∃ a : 𝓞 F,
      Algebra.trace ℚ F ((r : F) * (a : F)) ∉ (algebraMap ℤ ℚ).range := by
    by_contra h
    push_neg at h
    apply hrNotDual
    rw [Submodule.mem_traceDual]
    intro y hy
    have hyRange : ∃ a₀ : 𝓞 F, algebraMap (𝓞 F) F a₀ = y := by
      rw [Submodule.one_eq_range] at hy
      exact hy
    obtain ⟨a₀, ha₀⟩ := hyRange
    simpa only [Algebra.traceForm_apply, ha₀, mul_comm] using h a₀
  obtain ⟨a, haTrace⟩ := htraceWitness
  have hexpNe : Complex.exp
      (2 * Real.pi * Complex.I * (Algebra.trace ℚ F ((r : F) * (a : F)) : ℂ)) ≠ 1 := by
    intro hexp
    let q : ℚ := Algebra.trace ℚ F ((r : F) * (a : F))
    have harg : ((2 * Real.pi * (q : ℝ) : ℝ) : ℂ) * Complex.I =
        2 * Real.pi * Complex.I *
          (Algebra.trace ℚ F ((r : F) * (a : F)) : ℂ) := by
      simp only [q]
      push_cast
      ring
    have hexp' : Complex.exp (((2 * Real.pi * (q : ℝ) : ℝ) : ℂ) * Complex.I) = 1 := by
      rw [harg]
      exact hexp
    have hexp'' : Complex.exp (((2 * Real.pi * (q : ℝ) : ℝ) : ℂ) * Complex.I) =
        Complex.exp 0 := by simpa using hexp'
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp''
    have him := congrArg Complex.im hn
    have hreal : (2 * Real.pi : ℝ) * (q : ℝ) =
        (n : ℝ) * (2 * Real.pi) := by
      simpa [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] using him
    have hreal' : (q : ℝ) = (n : ℝ) := by
      apply (mul_left_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0))
      calc
        (2 * Real.pi : ℝ) * (q : ℝ) = (n : ℝ) * (2 * Real.pi) := hreal
        _ = (2 * Real.pi : ℝ) * (n : ℝ) := by ring
    have hq : (n : ℚ) = q := by exact_mod_cast hreal'.symm
    exact haTrace ⟨n, by simpa [q] using hq⟩
  let t : S.R := r * algebraMap (𝓞 F) (S.R) a
  have htCast : (t : F) = (r : F) * (a : F) := by simp [t]
  have harchInt (q : S.Sf) :
      algebraMap F (q.1.adicCompletion F) (a : F) ∈ q.1.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    change Valued.v ((a : F) : q.1.adicCompletion F) ≤ 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact q.1.valuation_le_one a
  have htOther (q : S.Sf) (hqv : q ≠ v) :
      algebraMap F (q.1.adicCompletion F) (t : F) ∈ q.1.adicCompletionIntegers F := by
    rw [htCast, map_mul]
    exact (q.1.adicCompletionIntegers F).mul_mem _ _ (hother q hqv) (harchInt q)
  have hψt := covol_addchar_eq_trace_exp S A v t htOther
  have hψtNe : A.ψ v.1 (algebraMap F (v.1.adicCompletion F) (t : F)) ≠ 1 := by
    rw [hψt]
    simpa [htCast] using hexpNe
  have haVal : v.1.valuation F (a : F) ≤ 1 := v.1.valuation_le_one a
  have htVal : v.1.valuation F (t : F) ≤ WithZero.exp (d + 1) := by
    rw [htCast, map_mul, hrVal]
    exact (mul_le_mul_of_nonneg_left haVal bot_le).trans_eq (by simp)
  refine ⟨algebraMap F (v.1.adicCompletion F) (t : F), ?_, hψtNe⟩
  change Valued.v ((t : F) : v.1.adicCompletion F) ≤ WithZero.exp (d + 1)
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  simpa [d] using htVal

private theorem covol_local_addchar_conductor_eq_different
    (D : FieldData F) (S : SData F CE condη) (A : AddCharData F)
    (v : S.Sf) :
    ∃ c : ℤ, 0 ≤ c ∧
      c = FractionalIdeal.count F v.1
        (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F) ∧
      (∀ x, Valued.v x ≤ WithZero.exp c → A.ψ v.1 x = 1) ∧
      ∃ x, Valued.v x ≤ WithZero.exp (c + 1) ∧ A.ψ v.1 x ≠ 1 := by
  obtain ⟨c, hc0, hc, hcBoundary⟩ := covol_local_addchar_conductor D S A v
  let d := FractionalIdeal.count F v.1
    (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F)
  have hd0 : 0 ≤ d := by
    simpa [d] using (FractionalIdeal.count_coe_nonneg F v.1
      (differentIdeal ℤ (𝓞 F)))
  have htriv : ∀ x : v.1.adicCompletion F, Valued.v x ≤ WithZero.exp d →
      A.ψ v.1 x = 1 := by
    intro x hx
    exact covol_local_character_trivial_on_different_ball D S A v x (by simpa [d] using hx)
  obtain ⟨xD, hxD, hxDne⟩ := covol_local_character_nontrivial_at_different_successor D S A v
  have hcdUpper : c ≤ d := by
    by_contra hnot
    have hlt : d < c := lt_of_not_ge hnot
    have hstep : d + 1 ≤ c := by omega
    have hxle : Valued.v xD ≤ WithZero.exp c :=
      hxD.trans (WithZero.exp_le_exp.mpr hstep)
    exact hxDne (hc xD hxle)
  have hdcLower : d ≤ c := by
    by_contra hnot
    have hlt : c < d := lt_of_not_ge hnot
    have hstep : c + 1 ≤ d := by omega
    obtain ⟨xc, hxc, hxcne⟩ := hcBoundary
    have hxc' : Valued.v xc ≤ WithZero.exp d :=
      hxc.trans (WithZero.exp_le_exp.mpr hstep)
    exact hxcne (htriv xc hxc')
  have hcd : c = d := le_antisymm hcdUpper hdcLower
  exact ⟨c, hc0, by simpa [d] using hcd, hc, hcBoundary⟩

private noncomputable def covol_local_conductor_exponent
    (D : FieldData F) (S : SData F CE condη) (A : AddCharData F) (v : S.Sf) : ℕ :=
  (Classical.choose (covol_local_addchar_conductor D S A v)).toNat

private theorem covol_local_conductor_exponent_eq_different
    (D : FieldData F) (S : SData F CE condη) (A : AddCharData F)
    (v : S.Sf) :
    covol_local_conductor_exponent D S A v =
      (FractionalIdeal.count F v.1
        (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F)).toNat := by
  classical
  let c := Classical.choose (covol_local_addchar_conductor D S A v)
  have hc : 0 ≤ c ∧
      (∀ x, Valued.v x ≤ WithZero.exp c → A.ψ v.1 x = 1) ∧
      ∃ x, Valued.v x ≤ WithZero.exp (c + 1) ∧ A.ψ v.1 x ≠ 1 := by
    simpa [c] using Classical.choose_spec (covol_local_addchar_conductor D S A v)
  obtain ⟨cD, hcD0, hcD_eq, hcD_triv, hcD_boundary⟩ :=
    covol_local_addchar_conductor_eq_different D S A v
  have hcD_eq' : cD = FractionalIdeal.count F v.1
      (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F) := hcD_eq
  let d := FractionalIdeal.count F v.1
    (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F)
  have hcD_eq'' : cD = d := by simpa [d] using hcD_eq'
  subst cD
  have hcUpper : c ≤ d := by
    by_contra hnot
    have hlt : d < c := lt_of_not_ge hnot
    have hstep : d + 1 ≤ c := by omega
    obtain ⟨x, hx, hxne⟩ := hcD_boundary
    have hx' : Valued.v x ≤ WithZero.exp c :=
      hx.trans (WithZero.exp_le_exp.mpr hstep)
    exact hxne (hc.2.1 x hx')
  have hcLower : d ≤ c := by
    by_contra hnot
    have hlt : c < d := lt_of_not_ge hnot
    have hstep : c + 1 ≤ d := by omega
    obtain ⟨x, hx, hxne⟩ := hc.2.2
    have hx' : Valued.v x ≤ WithZero.exp d :=
      hx.trans (WithZero.exp_le_exp.mpr hstep)
    exact hxne (hcD_triv x hx')
  have hcd : c = d := le_antisymm hcUpper hcLower
  unfold covol_local_conductor_exponent
  change c.toNat = (FractionalIdeal.count F v.1
    (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F)).toNat
  simpa [d] using congrArg Int.toNat hcd

private theorem covol_different_absNorm_factorization (S : SData F CE condη) :
    (Ideal.absNorm (differentIdeal ℤ (𝓞 F)) : ℝ) =
      ∏ v : S.Sf, (Ideal.absNorm v.1.asIdeal : ℝ) ^
        (FractionalIdeal.count F v.1
          (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F)).toNat := by
  classical
  let I : Ideal (𝓞 F) := differentIdeal ℤ (𝓞 F)
  let factor : FinPlace F → Ideal (𝓞 F) := fun q => q.maxPowDividing I
  let normReal : Ideal (𝓞 F) →* ℝ :=
    (Nat.castRingHom ℝ).toMonoidHom.comp Ideal.absNorm.toMonoidHom
  have hIne : I ≠ ⊥ := by simpa [I] using differentIdeal_ne_bot
  have hfactor : (∏ᶠ q : FinPlace F, factor q) = I := by
    simpa [factor] using (Ideal.finprod_heightOneSpectrum_factorization hIne)
  have hpreimageOne : ∀ J : Ideal (𝓞 F), normReal J = 1 → J = 1 := by
    intro J hJ
    have hcast : (Ideal.absNorm J : ℝ) = 1 := by
      change ((Ideal.absNorm J : ℕ) : ℝ) = 1 at hJ
      exact hJ
    have hnat : Ideal.absNorm J = 1 := by exact_mod_cast hcast
    simpa using (Ideal.absNorm_eq_one_iff.mp hnat)
  have hnormMap : normReal (∏ᶠ q : FinPlace F, factor q) =
      ∏ᶠ q : FinPlace F, normReal (factor q) :=
    normReal.map_finprod_of_preimage_one hpreimageOne factor
  have hsupport : Function.mulSupport factor ⊆ S.Sf := by
    intro q hq
    change factor q ≠ 1 at hq
    by_contra hqS
    have hDnot : ¬ I ≤ q.asIdeal := by
      intro hle
      apply hqS
      exact S.different_mem q (by simpa [I] using hle)
    have hcount : (Associates.mk q.asIdeal).count (Associates.mk I).factors = 0 := by
      by_contra hcount
      have hdvd := (Associates.count_ne_zero_iff_dvd hIne q.irreducible).mp hcount
      exact hDnot (Ideal.dvd_iff_le.mp hdvd)
    have hfactorOne : factor q = 1 := by
      simp [factor, IsDedekindDomain.HeightOneSpectrum.maxPowDividing, hcount]
    exact hq hfactorOne
  have hnormSupport : Function.mulSupport (fun q => normReal (factor q)) ⊆ S.Sf := by
    intro q hq
    change normReal (factor q) ≠ 1 at hq
    by_contra hqS
    have hfactorOne : factor q = 1 := by
      by_contra hfactorNe
      exact hqS (hsupport hfactorNe)
    apply hq
    rw [hfactorOne]
    simpa using normReal.map_one
  have hcountToNat (q : FinPlace F) :
      (FractionalIdeal.count F q (I : FractionalIdeal (𝓞 F)⁰ F)).toNat =
        (Associates.mk q.asIdeal).count (Associates.mk I).factors := by
    rw [FractionalIdeal.count_coe F q hIne]
    simp
  have hterm (q : FinPlace F) :
      normReal (factor q) = (Ideal.absNorm q.asIdeal : ℝ) ^
        (FractionalIdeal.count F q (I : FractionalIdeal (𝓞 F)⁰ F)).toNat := by
    calc
      normReal (factor q) = (Ideal.absNorm q.asIdeal : ℝ) ^
          (Associates.mk q.asIdeal).count (Associates.mk I).factors := by
            simp [normReal, factor, IsDedekindDomain.HeightOneSpectrum.maxPowDividing]
      _ = _ := by rw [← hcountToNat q]
  have hfinite : (Ideal.absNorm I : ℝ) =
      ∏ q ∈ S.Sf, (Ideal.absNorm q.asIdeal : ℝ) ^
        (FractionalIdeal.count F q (I : FractionalIdeal (𝓞 F)⁰ F)).toNat := by
    calc
      (Ideal.absNorm I : ℝ) = normReal I := by simp [normReal]
      _ = normReal (∏ᶠ q : FinPlace F, factor q) := by rw [hfactor]
      _ = ∏ᶠ q : FinPlace F, normReal (factor q) := hnormMap
      _ = ∏ q ∈ S.Sf, normReal (factor q) :=
        finprod_eq_finsetProd_of_mulSupport_subset _ hnormSupport
      _ = _ := by
        apply Finset.prod_congr rfl
        intro q hq
        exact hterm q
  change (Ideal.absNorm (differentIdeal ℤ (𝓞 F)) : ℝ) =
    ∏ v ∈ S.Sf.attach, (Ideal.absNorm v.1.asIdeal : ℝ) ^
      (FractionalIdeal.count F v.1
        (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F)).toNat
  calc
    _ = ∏ q ∈ S.Sf, (Ideal.absNorm q.asIdeal : ℝ) ^
        (FractionalIdeal.count F q
          (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F)).toNat := by
          simpa [I] using hfinite
    _ = _ := (Finset.prod_attach S.Sf fun q => (Ideal.absNorm q.asIdeal : ℝ) ^
      (FractionalIdeal.count F q
        (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F)).toNat).symm

private theorem covol_unifLoc_valuation (v : FinPlace F) :
    Valued.v (unifLoc v : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
  have hπcoerce : (unifLoc v : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) (unif (F := F) v) := by
    simp [unifLoc, toLoc]
  rw [hπcoerce]
  change Valued.v ((unif (F := F) v : F) : v.adicCompletion F) = WithZero.exp (-1 : ℤ)
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  simpa [unif] using (HeightOneSpectrum.valuation_exists_uniformizer F v).choose_spec

private theorem covol_absFin_unifLoc_zpow (v : FinPlace F) (n : ℤ) :
    absFin v ((unifLoc v ^ n : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      (qv v) ^ (-n) := by
  let K := v.adicCompletion F
  let q : NNReal := (Ideal.absNorm v.asIdeal : NNReal)
  have hπnorm : ‖(unifLoc v : K)‖₊ = q⁻¹ := by
    apply NNReal.coe_injective
    rw [coe_nnnorm, ← absFin_eq_norm]
    unfold absFin
    rw [dif_pos (HeightOneSpectrum.absNorm_ne_zero v), covol_unifLoc_valuation v]
    have hqexp : WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v)
        (WithZero.exp (-1 : ℤ)) = q⁻¹ := by
      rw [WithZeroMulInt.toNNReal_neg_apply (HeightOneSpectrum.absNorm_ne_zero v) (by simp)]
      rw [WithZero.toAdd_unzero_eq_log (by simp)]
      simp [q]
    rw [hqexp]
  have hπabs : absFin v (unifLoc v : K) = (qv v)⁻¹ := by
    calc
      absFin v (unifLoc v : K) = ‖(unifLoc v : K)‖ := absFin_eq_norm v _
      _ = ((‖(unifLoc v : K)‖₊ : NNReal) : ℝ) := by simp
      _ = ((q⁻¹ : NNReal) : ℝ) := by rw [hπnorm]
      _ = (qv v)⁻¹ := by simp [q, qv]
  have hpow : absFin v ((unifLoc v ^ n : Kˣ) : K) =
      absFin v (unifLoc v : K) ^ n := by
    rw [absFin_eq_norm, absFin_eq_norm]
    simp [norm_zpow]
  rw [hpow, hπabs, inv_zpow']

private theorem covol_local_ball_image (v : FinPlace F) (n : ℤ) :
    ball v n = (fun x : v.adicCompletion F =>
      ((unifLoc v ^ n : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x) ''
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  let K := v.adicCompletion F
  let π : Kˣ := unifLoc v
  have hπval : Valued.v (π : K) = WithZero.exp (-1 : ℤ) :=
    covol_unifLoc_valuation v
  have hπpow : Valued.v ((π ^ n : Kˣ) : K) = WithZero.exp (-n) := by
    have hpow : Valued.v ((π ^ n : Kˣ) : K) = Valued.v (π : K) ^ n := by simp
    rw [hpow, hπval, ← WithZero.exp_zsmul]
    congr 1
    simp
  ext x
  constructor
  · intro hx
    refine ⟨((π ^ n : Kˣ)⁻¹ : K) * x, ?_, ?_⟩
    · change Valued.v (((π ^ n : Kˣ)⁻¹ : K) * x) ≤ 1
      rw [map_mul, map_inv₀, hπpow]
      calc
        _ = WithZero.exp n * Valued.v x := by simp
        _ ≤ WithZero.exp n * WithZero.exp (-n) :=
          mul_le_mul_of_nonneg_left hx WithZero.exp_pos.le
        _ = 1 := by rw [← WithZero.exp_add]; simp
    · change ((π ^ n : Kˣ) : K) * (((π ^ n : Kˣ)⁻¹ : K) * x) = x
      have hne : ((π ^ n : Kˣ) : K) ≠ 0 := Units.ne_zero _
      calc
        _ = (((π ^ n : Kˣ) : K) * ((π ^ n : Kˣ) : K)⁻¹) * x := by rw [mul_assoc]
        _ = 1 * x := by rw [mul_inv_cancel₀ hne]
        _ = x := by simp
  · rintro ⟨x, hx, rfl⟩
    change Valued.v (((π ^ n : Kˣ) : K) * x) ≤ WithZero.exp (-n)
    rw [map_mul, hπpow]
    calc
      _ ≤ WithZero.exp (-n) * 1 := by
        have hx' : Valued.v x ≤ (1 : WithZero (Multiplicative ℤ)) := by
          change Valued.v x ≤ 1 at hx
          exact hx
        exact mul_le_mul_of_nonneg_left hx' WithZero.exp_pos.le
      _ = WithZero.exp (-n) := by simp

private theorem covol_locHaar_real_ball (v : FinPlace F) (μ : LocHaar v) (n : ℤ) :
    μ.μ.real (ball v n) = absFin v (unifLoc v ^ n) := by
  let K := v.adicCompletion F
  let O : Set K := v.adicCompletionIntegers F
  let u : Kˣ := unifLoc v ^ n
  have hOopen : IsOpen O := Valued.isOpen_valuationSubring K
  have hBopen : IsOpen (ball v n) :=
    v.isOpen_setOf_valued_le (K := F) WithZero.exp_ne_zero
  have hImage : ball v n = (fun x : K => (u : K) * x) '' O := by
    simpa [u] using covol_local_ball_image v n
  have hpre : (fun x : K => (u : K) * x) ⁻¹' ball v n = O := by
    rw [hImage]
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      have hcancel : y = x := mul_left_cancel₀ (Units.ne_zero u) hxy
      simpa [hcancel] using hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  let f : K → ℝ := Set.indicator (ball v n) 1
  have hf : (fun x : K => f ((u : K) * x)) = Set.indicator O 1 := by
    funext x
    have hxmem : (u : K) * x ∈ ball v n ↔ x ∈ O := by
      change x ∈ (fun x : K => (u : K) * x) ⁻¹' ball v n ↔ x ∈ O
      rw [hpre]
    by_cases hx : x ∈ O <;> simp [f, hx, hxmem]
  have hscale := LocHaar.integral_comp_mul μ u f
  rw [hf] at hscale
  have hOint : ∫ x : K, Set.indicator O 1 x ∂μ.μ = μ.μ.real O :=
    integral_indicator_one (μ := μ.μ) hOopen.measurableSet
  have hBint : ∫ x : K, Set.indicator (ball v n) 1 x ∂μ.μ =
      μ.μ.real (ball v n) := integral_indicator_one (μ := μ.μ) hBopen.measurableSet
  rw [hOint, hBint] at hscale
  have hOvol : μ.μ.real O = 1 := by
    change (μ.μ O).toReal = 1
    rw [μ.norm_O]
    rfl
  change μ.μ.real O = (absFin v u)⁻¹ * μ.μ.real (ball v n) at hscale
  rw [hOvol] at hscale
  have hnonzero : absFin v u ≠ 0 := (absFin_pos (Units.ne_zero u)).ne'
  field_simp [hnonzero] at hscale
  simpa [u] using hscale.symm

private noncomputable def covol_local_selfdual_scale (v : FinPlace F) (d : ℕ) : ℝ :=
  (Real.sqrt (absFin v (unifLoc v ^ (-(d : ℤ)))))⁻¹

private noncomputable def covol_local_selfdual_measure (v : FinPlace F)
    (μ : LocHaar v) (d : ℕ) : Measure (v.adicCompletion F) :=
  ENNReal.ofReal (covol_local_selfdual_scale v d) • μ.μ

private theorem covol_local_selfdual_scale_pos (v : FinPlace F) (d : ℕ) :
    0 < covol_local_selfdual_scale v d := by
  have hunit : (unifLoc v : v.adicCompletion F) ^ (-(d : ℤ)) ≠ 0 :=
    zpow_ne_zero _ (Units.ne_zero (unifLoc v))
  have ha : 0 < absFin v (unifLoc v ^ (-(d : ℤ))) := absFin_pos hunit
  unfold covol_local_selfdual_scale
  exact inv_pos.mpr (Real.sqrt_pos.2 ha)

private theorem covol_local_selfdual_scale_square (v : FinPlace F) (d : ℕ) :
    covol_local_selfdual_scale v d ^ 2 * absFin v (unifLoc v ^ (-(d : ℤ))) = 1 := by
  let a : ℝ := absFin v (unifLoc v ^ (-(d : ℤ)))
  have ha : 0 < a := by
    dsimp [a]
    have hunit : (unifLoc v : v.adicCompletion F) ^ (-(d : ℤ)) ≠ 0 :=
      zpow_ne_zero _ (Units.ne_zero (unifLoc v))
    exact absFin_pos hunit
  change (Real.sqrt a)⁻¹ ^ 2 * a = 1
  have hsq : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  have hsqrtne : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  calc
    (Real.sqrt a)⁻¹ ^ 2 * a = (Real.sqrt a)⁻¹ ^ 2 * Real.sqrt a ^ 2 := by rw [hsq]
    _ = 1 := by field_simp [hsqrtne]

private theorem covol_local_selfdual_measure_isHaar (v : FinPlace F)
    (μ : LocHaar v) (d : ℕ) :
    Measure.IsAddHaarMeasure (covol_local_selfdual_measure v μ d) := by
  let c : ENNReal := ENNReal.ofReal (covol_local_selfdual_scale v d)
  have hc0 : c ≠ 0 := by
    dsimp [c]
    exact ENNReal.ofReal_ne_zero_iff.mpr (covol_local_selfdual_scale_pos v d)
  have hctop : c < ⊤ := by
    dsimp [c]
    exact (ENNReal.ofReal_lt_top : ENNReal.ofReal (covol_local_selfdual_scale v d) < ⊤)
  change Measure.IsAddHaarMeasure (c • μ.μ)
  exact Measure.IsAddHaarMeasure.smul μ.μ hc0 hctop.ne

private theorem covol_local_selfdual_measure_real_ball (v : FinPlace F)
    (μ : LocHaar v) (d : ℕ) (n : ℤ) :
    (covol_local_selfdual_measure v μ d).real (ball v n) =
      covol_local_selfdual_scale v d * absFin v (unifLoc v ^ n) := by
  simp [covol_local_selfdual_measure, covol_local_selfdual_scale,
    covol_locHaar_real_ball]

private theorem covol_local_selfdual_measure_ball_pair (v : FinPlace F)
    (μ : LocHaar v) (d : ℕ) (n : ℤ) :
    (covol_local_selfdual_measure v μ d).real (ball v n) *
      (covol_local_selfdual_measure v μ d).real (ball v (- (d : ℤ) - n)) = 1 := by
  rw [covol_local_selfdual_measure_real_ball, covol_local_selfdual_measure_real_ball]
  have hnorm' : absFin v ((unifLoc v : v.adicCompletion F) ^ n *
      (unifLoc v : v.adicCompletion F) ^ (-(d : ℤ) - n)) =
      absFin v ((unifLoc v : v.adicCompletion F) ^ n) *
        absFin v ((unifLoc v : v.adicCompletion F) ^ (-(d : ℤ) - n)) := by
    calc
      _ = ‖(unifLoc v : v.adicCompletion F) ^ n *
          (unifLoc v : v.adicCompletion F) ^ (-(d : ℤ) - n)‖ := absFin_eq_norm _ _
      _ = ‖(unifLoc v : v.adicCompletion F) ^ n‖ *
          ‖(unifLoc v : v.adicCompletion F) ^ (-(d : ℤ) - n)‖ := norm_mul _ _
      _ = _ := by rw [← absFin_eq_norm, ← absFin_eq_norm]
  have hpow : unifLoc v ^ n * unifLoc v ^ (-(d : ℤ) - n) =
      unifLoc v ^ (-(d : ℤ)) := by
    rw [← zpow_add]
    congr 1 <;> ring
  have hpow' : ((unifLoc v ^ n : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
      ((unifLoc v ^ (-(d : ℤ) - n) : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
        ((unifLoc v ^ (-(d : ℤ)) : (v.adicCompletion F)ˣ) : v.adicCompletion F) :=
    congrArg (fun u : (v.adicCompletion F)ˣ => (u : v.adicCompletion F)) hpow
  have hpow'' : (unifLoc v : v.adicCompletion F) ^ n *
      (unifLoc v : v.adicCompletion F) ^ (-(d : ℤ) - n) =
        (unifLoc v : v.adicCompletion F) ^ (-(d : ℤ)) := by
    simpa only [Units.val_zpow_eq_zpow_val] using hpow'
  calc
    _ = covol_local_selfdual_scale v d ^ 2 *
        (absFin v (unifLoc v ^ n) * absFin v (unifLoc v ^ (-(d : ℤ) - n))) := by ring
    _ = covol_local_selfdual_scale v d ^ 2 *
        absFin v (unifLoc v ^ n * unifLoc v ^ (-(d : ℤ) - n)) :=
          congrArg (fun x : ℝ => covol_local_selfdual_scale v d ^ 2 * x) hnorm'.symm
    _ = covol_local_selfdual_scale v d ^ 2 * absFin v (unifLoc v ^ (-(d : ℤ))) := by
          rw [hpow'']
    _ = 1 := covol_local_selfdual_scale_square v d

private theorem covol_local_ball_add (v : FinPlace F) (n : ℤ)
    {x y : v.adicCompletion F} (hx : x ∈ ball v n) (hy : y ∈ ball v n) :
    x + y ∈ ball v n := by
  change Valued.v (x + y) ≤ WithZero.exp (-n)
  exact (Valued.v.map_add x y).trans (max_le hx hy)

private theorem covol_local_ball_neg (v : FinPlace F) (n : ℤ)
    {x : v.adicCompletion F} (hx : x ∈ ball v n) : -x ∈ ball v n := by
  change Valued.v (-x) ≤ WithZero.exp (-n)
  change Valued.v x ≤ WithZero.exp (-n) at hx
  simpa using hx

private def covol_local_ann_set (v : FinPlace F) (ψ : AddChar (v.adicCompletion F) ℂ)
    (n : ℤ) : Set (v.adicCompletion F) :=
  {a | ∀ x, Valued.v x ≤ WithZero.exp (-n) → ψ (a * x) = 1}

private theorem covol_local_ann_ball (v : FinPlace F)
    (ψ : AddChar (v.adicCompletion F) ℂ) (c n : ℤ)
    (hc : ∀ x, Valued.v x ≤ WithZero.exp c → ψ x = 1)
    (hboundary : ∃ x, Valued.v x ≤ WithZero.exp (c + 1) ∧ ψ x ≠ 1) :
    covol_local_ann_set v ψ n = {y | Valued.v y ≤ WithZero.exp (c + n)} := by
  unfold covol_local_ann_set
  ext y
  constructor
  · intro hy
    by_cases hy0 : y = 0
    · simp [hy0]
    · have hyv : Valued.v y ≠ 0 := by simpa using hy0
      lift Valued.v y to ℤ using hyv with k hk
      by_contra hnot
      have hnotExp : ¬ WithZero.exp k ≤ WithZero.exp (c + n) := by
        intro hle
        exact hnot (by simpa [hk] using hle)
      have hkn : c + n < k := by
        have hnk : ¬ k ≤ c + n := by
          intro hle
          exact hnotExp ((WithZero.exp_le_exp).2 hle)
        omega
      obtain ⟨z, hzv, hzψ⟩ := hboundary
      have hz0 : z ≠ 0 := by
        intro hz
        subst z
        exact hzψ ψ.map_zero_eq_one
      have hzv0 : Valued.v z ≠ 0 := by simpa using hz0
      lift Valued.v z to ℤ using hzv0 with j hj
      have hjle : j ≤ c + 1 := (WithZero.exp_le_exp).1 hzv
      have hxval : Valued.v (z / y) ≤ WithZero.exp (-n) := by
        have hval : Valued.v (z / y) = WithZero.exp (j - k) := by
          rw [map_div₀, ← hj, ← hk, ← WithZero.exp_sub]
        rw [hval]
        exact (WithZero.exp_le_exp).2 (by omega)
      have hxy : y * (z / y) = z := by
        calc
          y * (z / y) = (z / y) * y := mul_comm _ _
          _ = z := div_mul_cancel₀ z hy0
      have hψ : ψ (y * (z / y)) = 1 := hy (z / y) hxval
      rw [hxy] at hψ
      exact hzψ hψ
  · intro hy x hx
    by_cases hy0 : y = 0
    · simp [hy0]
    · have hyv : Valued.v y ≠ 0 := by simpa using hy0
      lift Valued.v y to ℤ using hyv with k hk
      have hval : Valued.v (x * y) ≤ WithZero.exp c := by
        calc
          Valued.v (x * y) = Valued.v x * Valued.v y := by simp
          _ ≤ WithZero.exp (-n) * WithZero.exp k := by
            exact mul_le_mul' hx (by rw [← hk])
          _ = WithZero.exp (-n + k) := by rw [← WithZero.exp_add]
          _ ≤ WithZero.exp c := (WithZero.exp_le_exp).2 (by
            have hybound : k ≤ c + n := by
              have hy' : WithZero.exp k ≤ WithZero.exp (c + n) := by
                rw [hk]
                exact hy
              exact (WithZero.exp_le_exp).1 hy'
            omega)
      exact hc _ (by simpa [mul_comm] using hval)

private theorem covol_local_char_integral_ball (v : FinPlace F)
    (ψ : AddChar (v.adicCompletion F) ℂ) (μ : Measure (v.adicCompletion F))
    [Measure.IsAddHaarMeasure μ] (n : ℤ) (a : v.adicCompletion F) :
    ∫ x, (ball v n).indicator (fun x => ψ (-(a * x))) x ∂μ =
      (covol_local_ann_set v ψ n).indicator
        (fun _ => (μ.real (ball v n) : ℂ)) a := by
  classical
  have hBopen : IsOpen (ball v n) :=
    v.isOpen_setOf_valued_le (K := F) WithZero.exp_ne_zero
  by_cases ha : a ∈ covol_local_ann_set v ψ n
  · have hf : (fun x => (ball v n).indicator (fun x => ψ (-(a * x))) x) =
        (ball v n).indicator (fun _ => (1 : ℂ)) := by
      funext x
      by_cases hx : x ∈ ball v n
      · have hψ : ψ (-(a * x)) = 1 := by
          rw [ψ.map_neg_eq_inv, ha x (by simpa [ball] using hx), inv_one]
        simp [hx, hψ]
      · simp [hx]
    have hmass : ∫ x, (ball v n).indicator (fun x => ψ (-(a * x))) x ∂μ =
        (μ.real (ball v n) : ℂ) := by
      calc
        _ = ∫ x, (ball v n).indicator (fun _ => (1 : ℂ)) x ∂μ := by rw [hf]
        _ = μ.real (ball v n) • (1 : ℂ) :=
          integral_indicator_const (1 : ℂ) hBopen.measurableSet
        _ = (μ.real (ball v n) : ℂ) := by simp
    have hind : (covol_local_ann_set v ψ n).indicator
        (fun _ => (μ.real (ball v n) : ℂ)) a =
        (μ.real (ball v n) : ℂ) := by simp [ha]
    exact hmass.trans hind.symm
  · have hfalse : ¬ (∀ x, Valued.v x ≤ WithZero.exp (-n) → ψ (a * x) = 1) := by
      simpa [covol_local_ann_set] using ha
    push Not at hfalse
    obtain ⟨b, hb, hψb⟩ := hfalse
    have hψbneg : ψ (-(a * b)) ≠ 1 := by
      rw [ψ.map_neg_eq_inv]
      intro h
      exact hψb (inv_eq_one.mp h)
    let f : v.adicCompletion F → ℂ :=
      fun x => (ball v n).indicator (fun x => ψ (-(a * x))) x
    have hcoset (x : v.adicCompletion F) : b + x ∈ ball v n ↔ x ∈ ball v n := by
      constructor
      · intro hbx
        have h := covol_local_ball_add v n hbx (covol_local_ball_neg v n hb)
        simpa [add_assoc] using h
      · intro hx
        have h := covol_local_ball_add v n hb hx
        simpa [add_comm] using h
    have hchar (x : v.adicCompletion F) :
        ψ (-(a * (b + x))) = ψ (-(a * b)) * ψ (-(a * x)) := by
      calc
        ψ (-(a * (b + x))) = ψ (-(a * b) + -(a * x)) := by congr 1 <;> ring
        _ = ψ (-(a * b)) * ψ (-(a * x)) := ψ.map_add_eq_mul _ _
    have htrans (x : v.adicCompletion F) :
        f (b + x) = ψ (-(a * b)) * f x := by
      by_cases hx : x ∈ ball v n
      · have hbx : b + x ∈ ball v n := (hcoset x).2 hx
        simp [f, hx, hbx, hchar x]
      · have hbx : b + x ∉ ball v n := fun h => hx ((hcoset x).1 h)
        simp [f, hx, hbx]
    let I : ℂ := ∫ x, f x ∂μ
    have hI : I = ψ (-(a * b)) * I := by
      calc
        I = ∫ x, f (b + x) ∂μ := (integral_add_left_eq_self f b).symm
        _ = ∫ x, ψ (-(a * b)) * f x ∂μ := by
          rw [show (fun x => f (b + x)) =
            fun x => ψ (-(a * b)) * f x from funext htrans]
        _ = ψ (-(a * b)) * I := by rw [integral_const_mul]
    have hprod : (ψ (-(a * b)) - 1) * I = 0 := by
      calc
        (ψ (-(a * b)) - 1) * I = ψ (-(a * b)) * I - I := by ring
        _ = I - I := by rw [← hI]
        _ = 0 := by ring
    have hI0 : I = 0 := by
      rcases mul_eq_zero.mp hprod with h | h
      · exact (hψbneg (sub_eq_zero.mp h)).elim
      · exact h
    have hmass : ∫ x, (ball v n).indicator (fun x => ψ (-(a * x))) x ∂μ = 0 := by
      simpa [I, f] using hI0
    have hind : (covol_local_ann_set v ψ n).indicator
        (fun _ => (μ.real (ball v n) : ℂ)) a = 0 := by simp [ha]
    exact hmass.trans hind.symm

private noncomputable def covol_local_fourier (v : FinPlace F)
    (ψ : AddChar (v.adicCompletion F) ℂ) (μ : Measure (v.adicCompletion F))
    (f : v.adicCompletion F → ℂ) (x : v.adicCompletion F) : ℂ :=
  ∫ y, ψ (-(x * y)) * f y ∂μ

private theorem covol_local_fourier_ball_formula (v : FinPlace F)
    (ψ : AddChar (v.adicCompletion F) ℂ) (μ : Measure (v.adicCompletion F))
    [Measure.IsAddHaarMeasure μ] (n : ℤ) (a : v.adicCompletion F) :
    covol_local_fourier v ψ μ ((ball v n).indicator (fun _ => (1 : ℂ))) a =
      (covol_local_ann_set v ψ n).indicator
        (fun _ => (μ.real (ball v n) : ℂ)) a := by
  have hfun : (fun y => ψ (-(a * y)) *
      (ball v n).indicator (fun _ => (1 : ℂ)) y) =
      (ball v n).indicator (fun y => ψ (-(a * y))) := by
    funext y
    by_cases hy : y ∈ ball v n <;> simp [hy]
  change ∫ y, ψ (-(a * y)) * (ball v n).indicator (fun _ => (1 : ℂ)) y ∂μ = _
  rw [hfun]
  exact covol_local_char_integral_ball v ψ μ n a

private theorem covol_local_fourier_const_mul (v : FinPlace F)
    (ψ : AddChar (v.adicCompletion F) ℂ) (μ : Measure (v.adicCompletion F))
    (c : ℂ) (f : v.adicCompletion F → ℂ) (x : v.adicCompletion F) :
    covol_local_fourier v ψ μ (fun y => c * f y) x =
      c * covol_local_fourier v ψ μ f x := by
  unfold covol_local_fourier
  have hfun : (fun y => ψ (-(x * y)) * (c * f y)) =
      fun y => c * (ψ (-(x * y)) * f y) := by
    funext y
    ring
  rw [hfun, integral_const_mul]

private theorem covol_local_fourier_ball_inversion (v : FinPlace F)
    (ψ : AddChar (v.adicCompletion F) ℂ) (μ : Measure (v.adicCompletion F))
    [Measure.IsAddHaarMeasure μ] (c n : ℤ)
    (hc : ∀ x, Valued.v x ≤ WithZero.exp c → ψ x = 1)
    (hboundary : ∃ x, Valued.v x ≤ WithZero.exp (c + 1) ∧ ψ x ≠ 1)
    (hvol : μ.real (ball v n) * μ.real (ball v (-c - n)) = 1)
    (x : v.adicCompletion F) :
    covol_local_fourier v ψ μ
      (covol_local_fourier v ψ μ ((ball v n).indicator (fun _ => (1 : ℂ))) ) x =
        (ball v n).indicator (fun _ => (1 : ℂ)) (-x) := by
  let B' : Set (v.adicCompletion F) := ball v (-c - n)
  let mB : ℂ := (μ.real (ball v n) : ℂ)
  have hAnn1Set : covol_local_ann_set v ψ n = B' := by
    have h := covol_local_ann_ball v ψ c n hc hboundary
    have hs : -(-c - n) = c + n := by omega
    simpa [B', ball, hs] using h
  have hAnn2Set : covol_local_ann_set v ψ (-c - n) = ball v n := by
    have h := covol_local_ann_ball v ψ c (-c - n) hc hboundary
    have hs : c + (-c - n) = -n := by omega
    rw [hs] at h
    simpa [ball] using h
  have hFhat : covol_local_fourier v ψ μ
      ((ball v n).indicator (fun _ => (1 : ℂ))) =
      B'.indicator (fun _ => mB) := by
    funext y
    calc
      covol_local_fourier v ψ μ ((ball v n).indicator (fun _ => (1 : ℂ))) y =
          (covol_local_ann_set v ψ n).indicator
            (fun _ => (μ.real (ball v n) : ℂ)) y :=
              covol_local_fourier_ball_formula v ψ μ n y
      _ = B'.indicator (fun _ => mB) y := by rw [hAnn1Set]
  have htrans (y : v.adicCompletion F) :
      ψ (-(x * y)) * B'.indicator (fun _ => mB) y =
        mB * B'.indicator (fun y => ψ (-(x * y))) y := by
    by_cases hy : y ∈ B' <;> simp [hy, mul_comm]
  have hsecond : covol_local_fourier v ψ μ (B'.indicator (fun _ => mB)) x =
      mB * (ball v n).indicator (fun _ => (μ.real B' : ℂ)) x := by
    unfold covol_local_fourier
    rw [show (fun y => ψ (-(x * y)) * B'.indicator (fun _ => mB) y) =
      fun y => mB * B'.indicator (fun y => ψ (-(x * y))) y from funext htrans,
      integral_const_mul, covol_local_char_integral_ball]
    rw [hAnn2Set]
  have hvolC : mB * (μ.real B' : ℂ) = 1 := by
    dsimp [mB, B']
    exact_mod_cast hvol
  have hxneg : -x ∈ ball v n ↔ x ∈ ball v n := by
    constructor
    · intro hx
      simpa using covol_local_ball_neg v n hx
    · intro hx
      exact covol_local_ball_neg v n hx
  have hresult : covol_local_fourier v ψ μ
      (covol_local_fourier v ψ μ ((ball v n).indicator (fun _ => (1 : ℂ)))) x =
      mB * (ball v n).indicator (fun _ => (μ.real B' : ℂ)) x := by
    calc
      _ = covol_local_fourier v ψ μ (B'.indicator (fun _ => mB)) x := by rw [hFhat]
      _ = mB * (ball v n).indicator (fun _ => (μ.real B' : ℂ)) x := hsecond
  by_cases hx : x ∈ ball v n
  · calc
      covol_local_fourier v ψ μ
          (covol_local_fourier v ψ μ ((ball v n).indicator (fun _ => (1 : ℂ)))) x =
          mB * (μ.real B' : ℂ) := by rw [hresult]; simp [hx]
      _ = 1 := hvolC
      _ = (ball v n).indicator (fun _ => (1 : ℂ)) (-x) := by simp [hxneg, hx]
  · calc
      covol_local_fourier v ψ μ
          (covol_local_fourier v ψ μ ((ball v n).indicator (fun _ => (1 : ℂ)))) x =
          0 := by rw [hresult]; simp [hx]
      _ = (ball v n).indicator (fun _ => (1 : ℂ)) (-x) := by simp [hxneg, hx]

private noncomputable def covol_base_locHaar (v : FinPlace F) : LocHaar v :=
  Classical.choice (LocHaar.nonempty v)

private noncomputable def covol_local_selfdual_at
    (D : FieldData F) (S : SData F CE condη) (A : AddCharData F) (v : S.Sf) :
    Measure (v.1.adicCompletion F) :=
  covol_local_selfdual_measure v.1 (covol_base_locHaar v.1)
    (covol_local_conductor_exponent D S A v)

private theorem covol_local_selfdual_at_isHaar
    (D : FieldData F) (S : SData F CE condη) (A : AddCharData F) (v : S.Sf) :
    Measure.IsAddHaarMeasure (covol_local_selfdual_at D S A v) := by
  exact covol_local_selfdual_measure_isHaar v.1 (covol_base_locHaar v.1)
    (covol_local_conductor_exponent D S A v)

private theorem covol_local_integer_ball (v : FinPlace F) :
    ball v 0 = (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  ext x
  rw [ball]
  change Valued.v x ≤ WithZero.exp (-(0 : ℤ)) ↔ x ∈ v.adicCompletionIntegers F
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  simp

private theorem covol_local_integer_indicator_fourier_inversion
    (D : FieldData F) (S : SData F CE condη) (A : AddCharData F) (v : S.Sf)
    (x : v.1.adicCompletion F) :
    covol_local_fourier v.1 (A.ψ v.1) (covol_local_selfdual_at D S A v)
      (covol_local_fourier v.1 (A.ψ v.1) (covol_local_selfdual_at D S A v)
        ((v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F)).indicator
          (fun _ => (1 : ℂ)))) x =
      ((v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F)).indicator
        (fun _ => (1 : ℂ))) (-x) := by
  let c : ℤ := Classical.choose (covol_local_addchar_conductor D S A v)
  let d : ℕ := covol_local_conductor_exponent D S A v
  let ν : Measure (v.1.adicCompletion F) := covol_local_selfdual_at D S A v
  letI : Measure.IsAddHaarMeasure ν := covol_local_selfdual_at_isHaar D S A v
  have hspec := Classical.choose_spec (covol_local_addchar_conductor D S A v)
  have hc : ∀ y, Valued.v y ≤ WithZero.exp c → A.ψ v.1 y = 1 := hspec.2.1
  have hbdy : ∃ y, Valued.v y ≤ WithZero.exp (c + 1) ∧ A.ψ v.1 y ≠ 1 := hspec.2.2
  have hcd : (d : ℤ) = c := by
    dsimp [d, covol_local_conductor_exponent, c]
    exact Int.toNat_of_nonneg hspec.1
  have hvol : ν.real (ball v.1 0) * ν.real (ball v.1 (-c - 0)) = 1 := by
    change (covol_local_selfdual_measure v.1 (covol_base_locHaar v.1) d).real
        (ball v.1 0) *
      (covol_local_selfdual_measure v.1 (covol_base_locHaar v.1) d).real
      (ball v.1 (-c - 0)) = 1
    have hpair := covol_local_selfdual_measure_ball_pair v.1
      (covol_base_locHaar v.1) d 0
    simpa [hcd] using hpair
  have hinv := covol_local_fourier_ball_inversion v.1 (A.ψ v.1) ν c 0 hc hbdy hvol x
  have hO := covol_local_integer_ball v.1
  simpa [ν, hO] using hinv

private theorem covol_local_selfdual_integer_mass
    (D : FieldData F) (S : SData F CE condη) (A : AddCharData F)
    (v : S.Sf) :
    (covol_local_selfdual_at D S A v).real
      (v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F)) =
    covol_local_selfdual_scale v.1 (covol_local_conductor_exponent D S A v) := by
  let d := covol_local_conductor_exponent D S A v
  change (covol_local_selfdual_measure v.1 (covol_base_locHaar v.1) d).real
      (v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F)) =
    covol_local_selfdual_scale v.1 d
  rw [← covol_local_integer_ball, covol_local_selfdual_measure_real_ball]
  have hOne : absFin v.1 (1 : v.1.adicCompletion F) = 1 := by
    unfold absFin
    rw [dif_pos (HeightOneSpectrum.absNorm_ne_zero v.1)]
    simp
  simp [hOne]

private theorem covol_local_selfdual_integer_mass_ennreal
    (D : FieldData F) (S : SData F CE condη) (A : AddCharData F)
    (v : S.Sf) :
    (covol_local_selfdual_at D S A v)
      (v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F)) =
    ENNReal.ofReal (covol_local_selfdual_scale v.1
      (covol_local_conductor_exponent D S A v)) := by
  let d := covol_local_conductor_exponent D S A v
  let μ := covol_base_locHaar v.1
  have hO : μ.μ (v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F)) = 1 :=
    μ.norm_O
  change (covol_local_selfdual_measure v.1 μ d)
      (v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F)) =
    ENNReal.ofReal (covol_local_selfdual_scale v.1 d)
  rw [covol_local_selfdual_measure, Measure.smul_apply, hO]
  simp

private theorem covol_finite_selfdual_integer_mass_product
    (D : FieldData F) (S : SData F CE condη) (A : AddCharData F) :
    ∏ v : S.Sf, (covol_local_selfdual_at D S A v).real
      (v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F)) =
    (Real.sqrt (Ideal.absNorm (differentIdeal ℤ (𝓞 F)) : ℝ))⁻¹ := by
  classical
  have hlocal (v : S.Sf) :
      (covol_local_selfdual_at D S A v).real
        (v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F)) =
      (Real.sqrt ((qv v.1) ^
        (FractionalIdeal.count F v.1
          (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F)).toNat))⁻¹ := by
    let K := v.1.adicCompletion F
    have hpow (n : ℤ) :
        absFin v.1 ((unifLoc v.1 : K) ^ n) =
          absFin v.1 (unifLoc v.1 : K) ^ n := by
      rw [absFin_eq_norm, absFin_eq_norm]
      simp [norm_zpow]
    have hπ : absFin v.1 (unifLoc v.1 : K) = (qv v.1)⁻¹ := by
      simpa using covol_absFin_unifLoc_zpow v.1 1
    rw [covol_local_selfdual_integer_mass,
      covol_local_conductor_exponent_eq_different,
      covol_local_selfdual_scale]
    rw [hpow, hπ, inv_zpow']
    have hcount0 : 0 ≤ FractionalIdeal.count F v.1
        (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F) :=
      FractionalIdeal.count_coe_nonneg F v.1 (differentIdeal ℤ (𝓞 F))
    have hnat :
        ((FractionalIdeal.count F v.1
          (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F)).toNat : ℤ) =
          FractionalIdeal.count F v.1
            (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F) :=
      Int.toNat_of_nonneg hcount0
    rw [← zpow_natCast, hnat]
    simp
  have hnorm :
      (Ideal.absNorm (differentIdeal ℤ (𝓞 F)) : ℝ) =
        ∏ v : S.Sf, (qv v.1) ^
          (FractionalIdeal.count F v.1
            (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F)).toNat := by
    simpa [qv] using covol_different_absNorm_factorization S
  have hqv (v : S.Sf) : 0 < qv v.1 := by
    have hqv0 : qv v.1 ≠ 0 := by
      change (Ideal.absNorm v.1.asIdeal : ℝ) ≠ 0
      exact_mod_cast HeightOneSpectrum.absNorm_ne_zero v.1
    exact lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hqv0)
  calc
    ∏ v : S.Sf, (covol_local_selfdual_at D S A v).real
        (v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F)) =
      ∏ v : S.Sf, (Real.sqrt ((qv v.1) ^
        (FractionalIdeal.count F v.1
          (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F)).toNat))⁻¹ := by
            apply Finset.prod_congr rfl
            intro v hv
            exact hlocal v
    _ = (Real.sqrt (∏ v : S.Sf, (qv v.1) ^
          (FractionalIdeal.count F v.1
            (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F)).toNat))⁻¹ := by
          rw [Finset.prod_inv_distrib,
            ← Real.sqrt_prod Finset.univ (by
              intro v hv
              exact (pow_nonneg (hqv v).le _))]
    _ = (Real.sqrt (Ideal.absNorm (differentIdeal ℤ (𝓞 F)) : ℝ))⁻¹ := by
          rw [← hnorm]

private theorem covol_arch_test_fourier_inversion (x : InfinitePlace F → ℂ) :
    ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiFourier
      (fun y => ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiFourier
        (covol_arch_test : (InfinitePlace F → ℂ) → ℂ) y) x = covol_arch_test (-x) :=
  ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiFourier_inversion covol_arch_test x

private theorem covol_sFS_prod_eq_borel (S : SData F CE condη) :
    (Prod.instMeasurableSpace : MeasurableSpace S.FS) = borel S.FS := by
  letI : MeasurableSpace S.FS := Prod.instMeasurableSpace
  letI : BorelSpace S.FS := inferInstance
  exact BorelSpace.measurable_eq

@[instance_reducible] private noncomputable def covol_sFSProductMeas
    (S : SData F CE condη) : MeasurableSpace S.FS := Prod.instMeasurableSpace

@[instance_reducible] private noncomputable def covol_sFSBorelMeas
    (S : SData F CE condη) : MeasurableSpace S.FS := borel S.FS

private theorem covol_sFSProductMeas_eq_borel (S : SData F CE condη) :
    covol_sFSProductMeas S = covol_sFSBorelMeas S := by
  letI : MeasurableSpace S.FS := covol_sFSProductMeas S
  letI : BorelSpace S.FS := inferInstance
  exact BorelSpace.measurable_eq

private noncomputable abbrev covol_sFSULiftProductMeas (S : SData F CE condη) :
    MeasurableSpace (ULift.{0} S.FS) :=
  @ULift.instMeasurableSpace S.FS (covol_sFSProductMeas S)

@[instance_reducible] private noncomputable local instance covol_instMeasurableULiftProd
    (S : SData F CE condη) : MeasurableSpace (ULift.{0} S.FS) :=
  covol_sFSULiftProductMeas S

private noncomputable def covol_sFSUpAddEquiv (S : SData F CE condη) :
    S.FS ≃+ ULift.{0} S.FS where
  toFun := ULift.up
  invFun := ULift.down
  left_inv _ := rfl
  right_inv := fun x => by cases x; rfl
  map_add' _ _ := rfl

private theorem covol_sFSUp_measurable_prod (S : SData F CE condη) :
    @Measurable S.FS (ULift.{0} S.FS) (covol_sFSProductMeas S)
      (covol_sFSULiftProductMeas S) ULift.up := by
  letI : MeasurableSpace S.FS := covol_sFSProductMeas S
  letI : MeasurableSpace (ULift.{0} S.FS) := covol_sFSULiftProductMeas S
  exact measurable_up

private theorem covol_sFSDown_measurable_prod (S : SData F CE condη) :
    @Measurable (ULift.{0} S.FS) S.FS (covol_sFSULiftProductMeas S)
      (covol_sFSProductMeas S) ULift.down := by
  letI : MeasurableSpace S.FS := covol_sFSProductMeas S
  letI : MeasurableSpace (ULift.{0} S.FS) := covol_sFSULiftProductMeas S
  exact measurable_down

private noncomputable def covol_sFSUpProdMeasEquiv (S : SData F CE condη) :
    @MeasurableEquiv S.FS (ULift.{0} S.FS) (covol_sFSProductMeas S)
      (covol_sFSULiftProductMeas S) := by
  letI : MeasurableSpace S.FS := covol_sFSProductMeas S
  letI : MeasurableSpace (ULift.{0} S.FS) := covol_sFSULiftProductMeas S
  exact @MeasurableEquiv.mk S.FS (ULift.{0} S.FS) (covol_sFSProductMeas S)
    (covol_sFSULiftProductMeas S) (covol_sFSUpAddEquiv S).toEquiv
    (covol_sFSUp_measurable_prod S) (covol_sFSDown_measurable_prod S)

private noncomputable def covol_sFSDownAddEquiv (S : SData F CE condη) :
    ULift.{0} S.FS ≃+ S.FS := (covol_sFSUpAddEquiv S).symm

private noncomputable def covol_sFSDownBorelMeasEquiv (S : SData F CE condη) :
    @MeasurableEquiv (ULift.{0} S.FS) S.FS (covol_sFSULiftProductMeas S)
      (covol_sFSBorelMeas S) := by
  letI : MeasurableSpace (ULift.{0} S.FS) := covol_sFSULiftProductMeas S
  letI : MeasurableSpace S.FS := covol_sFSBorelMeas S
  have hProdBorel := covol_sFSProductMeas_eq_borel S
  have hdown : @Measurable (ULift.{0} S.FS) S.FS (covol_sFSULiftProductMeas S)
      (covol_sFSBorelMeas S) ULift.down :=
    @Measurable.of_le_map (ULift.{0} S.FS) S.FS (covol_sFSULiftProductMeas S)
      (covol_sFSBorelMeas S) ULift.down (by
        change covol_sFSBorelMeas S ≤
          (covol_sFSULiftProductMeas S).map ULift.down
        calc
          _ = covol_sFSProductMeas S := hProdBorel.symm
          _ ≤ _ := (covol_sFSDown_measurable_prod S).le_map)
  have hup : @Measurable S.FS (ULift.{0} S.FS) (covol_sFSBorelMeas S)
      (covol_sFSULiftProductMeas S) ULift.up :=
    @Measurable.of_le_map S.FS (ULift.{0} S.FS) (covol_sFSBorelMeas S)
      (covol_sFSULiftProductMeas S) ULift.up (by
        change covol_sFSULiftProductMeas S ≤
          (covol_sFSBorelMeas S).map ULift.up
        calc
          _ ≤ (covol_sFSProductMeas S).map ULift.up :=
            (covol_sFSUp_measurable_prod S).le_map
          _ = _ := congrArg (fun m : MeasurableSpace S.FS => m.map ULift.up)
            hProdBorel)
  exact @MeasurableEquiv.mk (ULift.{0} S.FS) S.FS (covol_sFSULiftProductMeas S)
    (covol_sFSBorelMeas S) (covol_sFSDownAddEquiv S).toEquiv hdown hup

private theorem covol_sFSULiftProduct_borel (S : SData F CE condη) :
    @BorelSpace (ULift.{0} S.FS) (inferInstance : TopologicalSpace (ULift.{0} S.FS))
      (covol_sFSULiftProductMeas S) := by
  letI : MeasurableSpace S.FS := covol_sFSProductMeas S
  letI : BorelSpace S.FS := ⟨by
    change covol_sFSProductMeas S = borel S.FS
    exact covol_sFSProductMeas_eq_borel S⟩
  letI : MeasurableSpace (ULift.{0} S.FS) := covol_sFSULiftProductMeas S
  exact ULift.instBorelSpace

private noncomputable def covol_selfdual_measure_prod
    (D : FieldData F) (S : SData F CE condη) (A : AddCharData F) :
    @Measure S.FS Prod.instMeasurableSpace :=
  (Measure.pi fun v : S.Sf => covol_local_selfdual_at D S A v).prod
    (ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiSelfDualHaar (InfinitePlace F))

private noncomputable def covol_selfdual_measure_candidate
    (D : FieldData F) (S : SData F CE condη) (A : AddCharData F) : Measure S.FS := by
  exact @Measure.map (ULift.{0} S.FS) S.FS (covol_sFSULiftProductMeas S)
    (covol_sFSBorelMeas S) (covol_sFSDownBorelMeasEquiv S) <|
      @Measure.map S.FS (ULift.{0} S.FS) (covol_sFSProductMeas S)
        (covol_sFSULiftProductMeas S) (covol_sFSUpProdMeasEquiv S)
        (covol_selfdual_measure_prod D S A)

private theorem covol_isAddHaarMeasure_pi {ι : Type*} [Fintype ι] {G : ι → Type*}
    [∀ i, AddCommGroup (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, MeasurableSpace (G i)]
    [∀ i, SigmaCompactSpace (G i)] [∀ i, MeasurableAdd (G i)]
    (μ : ∀ i, Measure (G i)) (hμ : ∀ i, Measure.IsAddHaarMeasure (μ i)) :
    Measure.IsAddHaarMeasure (Measure.pi μ) := by
  letI : ∀ i, Measure.IsAddHaarMeasure (μ i) := hμ
  letI : ∀ i, SigmaFinite (μ i) := fun i => inferInstance
  refine {
    toIsFiniteMeasureOnCompacts := inferInstance
    toIsAddLeftInvariant := {
      map_add_left_eq_self := by
        intro a
        have hcoord (i : ι) : MeasurePreserving (fun x : G i => a i + x) (μ i) (μ i) :=
          measurePreserving_add_left (μ i) (a i)
        exact (MeasureTheory.measurePreserving_pi μ μ (f := fun i x => a i + x)
          hcoord).map_eq }
    toIsOpenPosMeasure := inferInstance }

private theorem covol_selfdual_measure_candidate_isHaar
    (D : FieldData F) (S : SData F CE condη) (A : AddCharData F) :
    Measure.IsAddHaarMeasure (covol_selfdual_measure_candidate D S A) := by
  letI : ∀ v : S.Sf, MeasurableAdd (v.1.adicCompletion F) := fun _ => inferInstance
  have hfin : Measure.IsAddHaarMeasure
      (Measure.pi fun v : S.Sf => covol_local_selfdual_at D S A v) :=
    covol_isAddHaarMeasure_pi (fun v : S.Sf => covol_local_selfdual_at D S A v)
      (fun v => covol_local_selfdual_at_isHaar D S A v)
  have hprod : @Measure.IsAddHaarMeasure S.FS _ _ Prod.instMeasurableSpace
      (covol_selfdual_measure_prod D S A) := by
    letI : MeasurableSpace S.FS := Prod.instMeasurableSpace
    letI : Measure.IsAddHaarMeasure
        (Measure.pi fun v : S.Sf => covol_local_selfdual_at D S A v) := hfin
    letI : Measure.IsAddHaarMeasure
        (ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiSelfDualHaar (InfinitePlace F)) :=
      ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiSelfDualHaar_isAddHaar
    dsimp [covol_selfdual_measure_prod]
    infer_instance
  have hUp : @Measure.IsAddHaarMeasure (ULift.{0} S.FS) _ _
      (covol_sFSULiftProductMeas S)
      (@Measure.map S.FS (ULift.{0} S.FS) (covol_sFSProductMeas S)
        (covol_sFSULiftProductMeas S) (covol_sFSUpAddEquiv S)
        (covol_selfdual_measure_prod D S A)) := by
    letI : MeasurableSpace S.FS := covol_sFSProductMeas S
    have hBP : @BorelSpace S.FS (inferInstance : TopologicalSpace S.FS)
        (covol_sFSProductMeas S) := inferInstance
    have hBU := covol_sFSULiftProduct_borel S
    exact @AddEquiv.isAddHaarMeasure_map S.FS (covol_sFSProductMeas S) _ _
      (covol_selfdual_measure_prod D S A) hprod hBP
      (inferInstance : ContinuousAdd S.FS) (ULift.{0} S.FS) _ _
      (covol_sFSULiftProductMeas S) hBU inferInstance (covol_sFSUpAddEquiv S)
      Homeomorph.ulift.symm.continuous Homeomorph.ulift.continuous
  have hDown : @Measure.IsAddHaarMeasure S.FS _ _ (covol_sFSBorelMeas S)
      (@Measure.map (ULift.{0} S.FS) S.FS (covol_sFSULiftProductMeas S)
        (covol_sFSBorelMeas S) (covol_sFSDownAddEquiv S)
        (@Measure.map S.FS (ULift.{0} S.FS) (covol_sFSProductMeas S)
          (covol_sFSULiftProductMeas S) (covol_sFSUpAddEquiv S)
          (covol_selfdual_measure_prod D S A))) := by
    letI : Measure.IsAddHaarMeasure
        (@Measure.map S.FS (ULift.{0} S.FS) (covol_sFSProductMeas S)
          (covol_sFSULiftProductMeas S) (covol_sFSUpAddEquiv S)
          (covol_selfdual_measure_prod D S A)) := hUp
    have hBU := covol_sFSULiftProduct_borel S
    have hBTarget : @BorelSpace S.FS (inferInstance : TopologicalSpace S.FS)
        (covol_sFSBorelMeas S) := ⟨rfl⟩
    exact @AddEquiv.isAddHaarMeasure_map (ULift.{0} S.FS)
      (covol_sFSULiftProductMeas S) _ _
      (@Measure.map S.FS (ULift.{0} S.FS) (covol_sFSProductMeas S)
        (covol_sFSULiftProductMeas S) (covol_sFSUpAddEquiv S)
        (covol_selfdual_measure_prod D S A)) hUp hBU
      (inferInstance : ContinuousAdd (ULift.{0} S.FS)) S.FS _ _
      (covol_sFSBorelMeas S) hBTarget inferInstance (covol_sFSDownAddEquiv S)
      Homeomorph.ulift.continuous Homeomorph.ulift.symm.continuous
  change Measure.IsAddHaarMeasure (covol_selfdual_measure_candidate D S A)
  exact hDown

private theorem covol_local_selfdual_at_sigmaFinite
    (D : FieldData F) (S : SData F CE condη) (A : AddCharData F) (v : S.Sf) :
    SigmaFinite (covol_local_selfdual_at D S A v) := by
  letI : SigmaCompactSpace (v.1.adicCompletion F) := inferInstance
  letI : Measure.IsAddHaarMeasure (covol_local_selfdual_at D S A v) :=
    covol_local_selfdual_at_isHaar D S A v
  infer_instance

private theorem covol_fourier_product_formula
    (D : FieldData F) (S : SData F CE condη) (A : AddCharData F)
    (fFin : ∀ v : S.Sf, v.1.adicCompletion F → ℂ)
    (fArch : (InfinitePlace F → ℂ) → ℂ) (x : S.FS) :
    S.fourier A (covol_selfdual_measure_candidate D S A)
      (fun y : S.FS => (∏ v : S.Sf, fFin v (y.1 v)) * fArch y.2) x =
      (∏ v : S.Sf, covol_local_fourier v.1 (A.ψ v.1)
        (covol_local_selfdual_at D S A v) (fFin v) (x.1 v)) *
        ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiFourier fArch x.2 := by
  classical
  let μFin : Measure (∀ v : S.Sf, v.1.adicCompletion F) :=
    Measure.pi fun v : S.Sf => covol_local_selfdual_at D S A v
  let μArch : Measure (InfinitePlace F → ℂ) :=
    ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiSelfDualHaar (InfinitePlace F)
  have hfinHaar : Measure.IsAddHaarMeasure μFin :=
    covol_isAddHaarMeasure_pi (fun v : S.Sf => covol_local_selfdual_at D S A v)
      (fun v => covol_local_selfdual_at_isHaar D S A v)
  letI : ∀ v : S.Sf, SigmaFinite (covol_local_selfdual_at D S A v) :=
    fun v => covol_local_selfdual_at_sigmaFinite D S A v
  letI : Measure.IsAddHaarMeasure μFin := hfinHaar
  letI : Measure.IsAddHaarMeasure μArch :=
    ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiSelfDualHaar_isAddHaar
  have hFinSigma : SigmaFinite μFin := inferInstance
  letI : SigmaFinite μFin := hFinSigma
  letI : SigmaCompactSpace (InfinitePlace F → ℂ) := inferInstance
  letI : SigmaFinite μArch := Measure.IsAddHaarMeasure.sigmaFinite μArch
  letI : SFinite μFin := inferInstance
  letI : SFinite μArch := inferInstance
  let finTerm : (∀ v : S.Sf, v.1.adicCompletion F) → ℂ := fun y =>
    ∏ v : S.Sf, fFin v (y v) * A.ψ v.1 (-(x.1 v * y v))
  let archTerm : (InfinitePlace F → ℂ) → ℂ := fun y =>
    fArch y * ∏ w : InfinitePlace F, psiC (-(x.2 w * y w))
  have hintegrand (p : S.FS) :
      (∏ v : S.Sf, fFin v (p.1 v)) * fArch p.2 * S.e A (-(p * x)) =
        finTerm p.1 * archTerm p.2 := by
    rcases p with ⟨pf, pa⟩
    simp only [Prod.fst, Prod.snd]
    simp only [finTerm, archTerm]
    change ((∏ v : S.Sf, fFin v (pf v)) * fArch pa) *
        ((∏ v : S.Sf, A.ψ v.1 (-(pf v * x.1 v))) *
          ∏ w : InfinitePlace F, psiC (-(pa w * x.2 w))) =
      (∏ v : S.Sf, fFin v (pf v) * A.ψ v.1 (-(x.1 v * pf v))) *
        (fArch pa * ∏ w : InfinitePlace F, psiC (-(x.2 w * pa w)))
    have hswap (v : S.Sf) :
        A.ψ v.1 (-(pf v * x.1 v)) = A.ψ v.1 (-(x.1 v * pf v)) := by
      congr 1
      rw [mul_comm]
    have harchSwap (w : InfinitePlace F) :
        psiC (-(pa w * x.2 w)) = psiC (-(x.2 w * pa w)) := by
      congr 1
      rw [mul_comm]
    calc
      _ = (∏ v : S.Sf, fFin v (pf v)) *
          (∏ v : S.Sf, A.ψ v.1 (-(pf v * x.1 v))) *
          (fArch pa * ∏ w : InfinitePlace F, psiC (-(pa w * x.2 w))) := by ring
      _ = (∏ v : S.Sf, fFin v (pf v)) *
          (∏ v : S.Sf, A.ψ v.1 (-(x.1 v * pf v))) *
          (fArch pa * ∏ w : InfinitePlace F, psiC (-(x.2 w * pa w))) := by
            congr 2
            · exact congrArg _ (funext hswap)
            · exact congrArg _ (funext harchSwap)
      _ = (∏ v : S.Sf, fFin v (pf v) * A.ψ v.1 (-(x.1 v * pf v))) *
          (fArch pa * ∏ w : InfinitePlace F, psiC (-(x.2 w * pa w))) := by
            congr 1
            simpa only [Finset.prod_mul_distrib]
  have hglobal : S.fourier A (covol_selfdual_measure_candidate D S A)
      (fun y : S.FS => (∏ v : S.Sf, fFin v (y.1 v)) * fArch y.2) x =
      ∫ p, finTerm p.1 * archTerm p.2 ∂(μFin.prod μArch) := by
    unfold ArtinPrimitiveRoots.A1.SData.fourier covol_selfdual_measure_candidate
    rw [MeasureTheory.integral_map_equiv (covol_sFSDownBorelMeasEquiv S)]
    rw [MeasureTheory.integral_map_equiv (covol_sFSUpProdMeasEquiv S)]
    unfold covol_selfdual_measure_prod
    apply integral_congr_ae
    filter_upwards with p
    simpa [covol_sFSUpProdMeasEquiv, covol_sFSDownBorelMeasEquiv,
      covol_sFSUpAddEquiv, covol_sFSDownAddEquiv] using hintegrand p
  have hprod : (∫ p, finTerm p.1 * archTerm p.2 ∂(μFin.prod μArch)) =
      (∫ y, finTerm y ∂μFin) * ∫ y, archTerm y ∂μArch :=
    MeasureTheory.integral_prod_mul (μ := μFin) (ν := μArch) finTerm archTerm
  have hFin : (∫ y, finTerm y ∂μFin) =
      ∏ v : S.Sf, covol_local_fourier v.1 (A.ψ v.1)
        (covol_local_selfdual_at D S A v) (fFin v) (x.1 v) := by
    dsimp [finTerm, μFin]
    have hPi :
        (∫ y : ∀ v : S.Sf, v.1.adicCompletion F,
          ∏ v : S.Sf, fFin v (y v) * A.ψ v.1 (-(x.1 v * y v))
            ∂(Measure.pi fun v : S.Sf => covol_local_selfdual_at D S A v)) =
          ∏ v : S.Sf, ∫ y, fFin v y * A.ψ v.1 (-(x.1 v * y))
            ∂(covol_local_selfdual_at D S A v) :=
      MeasureTheory.integral_fintype_prod_eq_prod
        (fun v y => fFin v y * A.ψ v.1 (-(x.1 v * y)))
    calc
      _ = ∏ v : S.Sf, ∫ y, fFin v y * A.ψ v.1 (-(x.1 v * y))
            ∂(covol_local_selfdual_at D S A v) := hPi
      _ = ∏ v : S.Sf, covol_local_fourier v.1 (A.ψ v.1)
            (covol_local_selfdual_at D S A v) (fFin v) (x.1 v) := by
              apply Finset.prod_congr rfl
              intro v hv
              unfold covol_local_fourier
              apply integral_congr_ae
              filter_upwards with y
              ring
  have hArch : (∫ y, archTerm y ∂μArch) =
      ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiFourier fArch x.2 := by
    unfold ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiFourier
    dsimp [archTerm, μArch]
    apply integral_congr_ae
    filter_upwards with y
    change fArch y * ∏ w : InfinitePlace F, psiC (-(x.2 w * y w)) =
      (∏ w : InfinitePlace F, psiC (-(x.2 w * y w))) * fArch y
    ring
  rw [hglobal]
  calc
    (∫ p, finTerm p.1 * archTerm p.2 ∂(μFin.prod μArch)) =
        (∫ y, finTerm y ∂μFin) * ∫ y, archTerm y ∂μArch := hprod
    _ = _ := by rw [hFin, hArch]

private theorem covol_selfdual_measure_candidate_eq
    (D : FieldData F) (S : SData F CE condη) (A : AddCharData F)
    (μ : S.SelfDualMeasure A) :
    μ.measure = covol_selfdual_measure_candidate D S A := by
  classical
  letI : ∀ v : S.Sf, SecondCountableTopology (v.1.adicCompletion F) :=
    fun v => inferInstance
  letI : ∀ v : S.Sf, LocallyCompactSpace (v.1.adicCompletion F) :=
    fun v => inferInstance
  letI : SecondCountableTopology S.FS := inferInstance
  letI : LocallyCompactSpace S.FS := inferInstance
  letI : Measure.IsAddHaarMeasure μ.measure := μ.isHaar
  let ν : Measure S.FS := covol_selfdual_measure_candidate D S A
  letI : Measure.IsAddHaarMeasure ν := covol_selfdual_measure_candidate_isHaar D S A
  let finite : ∀ v : S.Sf, S.FiniteTest v := fun v =>
    ⟨(v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F)).indicator
        (fun _ => (1 : ℂ)),
      ⟨(covol_local_integer_indicator_locallyConstant v.1).continuous,
        covol_local_integer_indicator_hasCompactSupport v.1,
        covol_local_integer_indicator_locallyConstant v.1⟩⟩
  let p : SData.ArchSchwartz F × (∀ v : S.Sf, S.FiniteTest v) :=
    ⟨covol_arch_test, finite⟩
  let ffun : S.FS → ℂ := S.tensorFunction p.1 p.2
  let f : S.BruhatSchwartz := ⟨ffun, Submodule.subset_span ⟨p, rfl⟩⟩
  let fFin : ∀ v : S.Sf, v.1.adicCompletion F → ℂ := fun v => (finite v).1
  let fArch : (InfinitePlace F → ℂ) → ℂ := covol_arch_test
  let fFinHat : ∀ v : S.Sf, v.1.adicCompletion F → ℂ := fun v x =>
    covol_local_fourier v.1 (A.ψ v.1) (covol_local_selfdual_at D S A v) (fFin v) x
  let fArchHat : (InfinitePlace F → ℂ) → ℂ :=
    ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiFourier fArch
  have hinput :
      (fun y : S.FS => (∏ v : S.Sf, fFin v (y.1 v)) * fArch y.2) = ffun := by
    funext y
    simp [fFin, fArch, ffun, p, SData.tensorFunction]
    ring
  have hfinite0 (v : S.Sf) : (finite v).1 0 = 1 := by
    simp [finite]
  have hfun0 : ffun 0 = 1 := by
    simp [ffun, p, SData.tensorFunction, covol_arch_test_zero, hfinite0]
  have hinner : S.fourier A ν ffun =
      fun y : S.FS => (∏ v : S.Sf, fFinHat v (y.1 v)) * fArchHat y.2 := by
    funext y
    rw [← hinput]
    simpa [fFinHat, fArchHat, fFin, fArch] using
      (covol_fourier_product_formula D S A fFin fArch y)
  have hlocal (v : S.Sf) :
      covol_local_fourier v.1 (A.ψ v.1) (covol_local_selfdual_at D S A v)
        (fFinHat v) 0 = 1 := by
    have h := covol_local_integer_indicator_fourier_inversion D S A v 0
    simpa [fFinHat, fFin, finite] using h
  have harch : ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiFourier fArchHat 0 = 1 := by
    have h := covol_arch_test_fourier_inversion (0 : InfinitePlace F → ℂ)
    simpa [fArchHat, fArch, covol_arch_test_zero] using h
  have hdoubleν : S.fourier A ν (S.fourier A ν ffun) 0 = 1 := by
    calc
      S.fourier A ν (S.fourier A ν ffun) 0 =
          S.fourier A ν
            (fun y : S.FS => (∏ v : S.Sf, fFinHat v (y.1 v)) * fArchHat y.2) 0 := by
              rw [hinner]
      _ = (∏ v : S.Sf, covol_local_fourier v.1 (A.ψ v.1)
            (covol_local_selfdual_at D S A v) (fFinHat v) 0) *
          ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiFourier fArchHat 0 :=
            covol_fourier_product_formula D S A fFinHat fArchHat 0
      _ = 1 := by simp [hlocal, harch]
  let c : NNReal := Measure.addHaarScalarFactor μ.measure ν
  have hmeasure : μ.measure = (c : ENNReal) • ν := by
    simpa [c] using Measure.isAddLeftInvariant_eq_smul μ.measure ν
  have hF (g : S.FS → ℂ) :
      S.fourier A μ.measure g = fun y => (c : ℂ) * S.fourier A ν g y := by
    funext y
    simp only [SData.fourier]
    rw [hmeasure, MeasureTheory.integral_smul_measure]
    simp [c, smul_eq_mul]
  have hF_smul (d : ℂ) (g : S.FS → ℂ) :
      S.fourier A ν (fun y => d * g y) = fun x => d * S.fourier A ν g x := by
    funext x
    simp only [SData.fourier]
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    funext y
    ring
  have hdoubleμ (x : S.FS) :
      S.fourier A μ.measure (S.fourier A μ.measure ffun) x =
        (c : ℂ) ^ 2 * S.fourier A ν (S.fourier A ν ffun) x := by
    calc
      _ = (c : ℂ) * S.fourier A ν (S.fourier A μ.measure ffun) x := by rw [hF]
      _ = (c : ℂ) * S.fourier A ν
          (fun y => (c : ℂ) * S.fourier A ν ffun y) x := by rw [hF ffun]
      _ = _ := by rw [hF_smul]; ring
  have hinv := μ.fourier_inversion f 0
  have hcoe : (f : S.FS → ℂ) = ffun := rfl
  rw [hcoe, neg_zero] at hinv
  rw [hdoubleμ, hdoubleν, hfun0] at hinv
  have hc2 : (c : ℂ) ^ 2 = 1 := by simpa using hinv
  have hcReal : (c : ℝ) ^ 2 = 1 := by exact_mod_cast hc2
  have hc : c = 1 := by
    apply Subtype.ext
    rcases sq_eq_one_iff.mp hcReal with h | h
    · exact h
    · have hcNonneg : 0 ≤ (c : ℝ) := NNReal.coe_nonneg c
      linarith
  simpa [hc] using hmeasure

private theorem covol_selfdual_measure_candidate_standard_domain_mass
    (D : FieldData F) (S : SData F CE condη) (A : AddCharData F) :
    covol_selfdual_measure_candidate D S A
      (covol_standard_fundamental_domain S D) = 1 := by
  classical
  letI : MeasurableSpace S.FS := covol_sFSBorelMeas S
  let O : ∀ v : S.Sf, Set (v.1.adicCompletion F) :=
    fun v => v.1.adicCompletionIntegers F
  let B : Set (∀ v : S.Sf, v.1.adicCompletion F) := Set.pi Set.univ O
  let C : Set (InfinitePlace F → ℂ) := covol_arch_fundamental_region D
  let K : Set S.FS := B ×ˢ C
  have hOopen (v : S.Sf) : IsOpen (O v) := Valued.isOpen_valuationSubring _
  have hBmeas : MeasurableSet B := by
    apply MeasurableSet.univ_pi
    intro v
    exact (hOopen v).measurableSet
  let e := covolArchToMixedEquiv D
  let P : Set (NumberField.mixedEmbedding.mixedSpace F) :=
    ZSpan.fundamentalDomain (NumberField.mixedEmbedding.latticeBasis F)
  have hPmeas : MeasurableSet P := ZSpan.fundamentalDomain_measurableSet _
  have hCeq : C = e ⁻¹' P := by
    ext z
    constructor
    · rintro ⟨p, hp, rfl⟩
      simpa [e, P] using hp
    · intro hz
      exact ⟨e z, hz, e.symm_apply_apply z⟩
  have hCmeas : MeasurableSet C := by
    rw [hCeq]
    exact e.continuous.measurable hPmeas
  have hKeq : K = Prod.fst ⁻¹' B ∩ Prod.snd ⁻¹' C := by
    ext z
    simp [K]
  have hKmeas : MeasurableSet K := by
    rw [hKeq]
    exact (continuous_fst.measurable hBmeas).inter
      (continuous_snd.measurable hCmeas)
  have hKdef : K = covol_standard_fundamental_domain S D := rfl
  have htransport : covol_selfdual_measure_candidate D S A K =
      covol_selfdual_measure_prod D S A K := by
    unfold covol_selfdual_measure_candidate
    change
      (@Measure.map (ULift.{0} S.FS) S.FS (covol_sFSULiftProductMeas S)
        (covol_sFSBorelMeas S) (covol_sFSDownBorelMeasEquiv S)
        (@Measure.map S.FS (ULift.{0} S.FS) (covol_sFSProductMeas S)
          (covol_sFSULiftProductMeas S) (covol_sFSUpProdMeasEquiv S)
          (covol_selfdual_measure_prod D S A))) K =
      (covol_selfdual_measure_prod D S A) K
    rw [MeasurableEquiv.map_apply (covol_sFSDownBorelMeasEquiv S) K]
    rw [MeasurableEquiv.map_apply (covol_sFSUpProdMeasEquiv S)
      ((covol_sFSDownBorelMeasEquiv S) ⁻¹' K)]
    have hback : (covol_sFSUpProdMeasEquiv S) ⁻¹'
        ((covol_sFSDownBorelMeasEquiv S) ⁻¹' K) = K := by
      ext x
      rfl
    rw [hback]
  let μFin : Measure (∀ v : S.Sf, v.1.adicCompletion F) :=
    Measure.pi fun v : S.Sf => covol_local_selfdual_at D S A v
  let μArch : Measure (InfinitePlace F → ℂ) :=
    ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiSelfDualHaar (InfinitePlace F)
  letI : ∀ v : S.Sf, SigmaFinite (covol_local_selfdual_at D S A v) :=
    fun v => covol_local_selfdual_at_sigmaFinite D S A v
  letI : SigmaFinite μFin := by
    dsimp [μFin]
    infer_instance
  letI : Measure.IsAddHaarMeasure μArch :=
    ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiSelfDualHaar_isAddHaar
  letI : SigmaCompactSpace (InfinitePlace F → ℂ) := inferInstance
  letI : SigmaFinite μArch := Measure.IsAddHaarMeasure.sigmaFinite μArch
  letI : SFinite μFin := inferInstance
  letI : SFinite μArch := inferInstance
  have hrect : covol_selfdual_measure_prod D S A K = μFin B * μArch C := by
    change (μFin.prod μArch) (B ×ˢ C) = μFin B * μArch C
    rw [Measure.prod_prod]
  have hlocal (v : S.Sf) : (covol_local_selfdual_at D S A v) (O v) =
      ENNReal.ofReal (covol_local_selfdual_scale v.1
        (covol_local_conductor_exponent D S A v)) := by
    simpa [O] using covol_local_selfdual_integer_mass_ennreal D S A v
  have hfinB : μFin B = ∏ v : S.Sf,
      (covol_local_selfdual_at D S A v) (O v) := by
    dsimp [μFin, B]
    rw [Measure.pi_pi]
    simp only [Finset.univ_eq_attach]
  have hscaleProd :
      ∏ v : S.Sf, covol_local_selfdual_scale v.1
        (covol_local_conductor_exponent D S A v) =
      (Real.sqrt (Ideal.absNorm (differentIdeal ℤ (𝓞 F)) : ℝ))⁻¹ := by
    simpa only [covol_local_selfdual_integer_mass] using
      covol_finite_selfdual_integer_mass_product D S A
  have hfinENN : μFin B = ENNReal.ofReal
      ((Real.sqrt (Ideal.absNorm (differentIdeal ℤ (𝓞 F)) : ℝ))⁻¹) := by
    calc
      μFin B = ∏ v : S.Sf, (covol_local_selfdual_at D S A v) (O v) := hfinB
      _ = ∏ v : S.Sf, ENNReal.ofReal (covol_local_selfdual_scale v.1
          (covol_local_conductor_exponent D S A v)) := by
            apply Finset.prod_congr rfl
            intro v hv
            exact hlocal v
      _ = ENNReal.ofReal (∏ v : S.Sf, covol_local_selfdual_scale v.1
          (covol_local_conductor_exponent D S A v)) := by
            symm
            apply ENNReal.ofReal_prod_of_nonneg
            intro v hv
            exact (covol_local_selfdual_scale_pos v.1
              (covol_local_conductor_exponent D S A v)).le
      _ = _ := by rw [hscaleProd]
  have harch : μArch C = ENNReal.ofReal
      (Real.sqrt (Ideal.absNorm (differentIdeal ℤ (𝓞 F)) : ℝ)) := by
    exact covol_arch_fundamental_region_measure D
  have hNormNat : 0 < Ideal.absNorm (differentIdeal ℤ (𝓞 F)) := by
    rw [Ideal.absNorm_pos_iff_mem_nonZeroDivisors, mem_nonZeroDivisors_iff_ne_zero]
    exact differentIdeal_ne_bot
  have hNormPos : 0 < (Ideal.absNorm (differentIdeal ℤ (𝓞 F)) : ℝ) := by
    exact_mod_cast hNormNat
  have hrootPos : 0 < Real.sqrt (Ideal.absNorm (differentIdeal ℤ (𝓞 F)) : ℝ) :=
    Real.sqrt_pos.2 hNormPos
  calc
    covol_selfdual_measure_candidate D S A
        (covol_standard_fundamental_domain S D) =
      covol_selfdual_measure_prod D S A K := by
        rw [← hKdef]
        exact htransport
    _ = μFin B * μArch C := hrect
    _ = ENNReal.ofReal ((Real.sqrt (Ideal.absNorm (differentIdeal ℤ (𝓞 F)) : ℝ))⁻¹) *
        ENNReal.ofReal (Real.sqrt (Ideal.absNorm (differentIdeal ℤ (𝓞 F)) : ℝ)) := by
          rw [hfinENN, harch]
    _ = 1 := by
          rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hrootPos.le),
            inv_mul_cancel₀ hrootPos.ne']
          simp

private theorem covol_candidate_fundamental_domain_mass_eq
    (D : FieldData F) (S : SData F CE condη) (A : AddCharData F)
    (K : Set S.FS) (hK : MeasurableSet K ∧ S.IsLatticeFundamentalDomain K) :
    covol_selfdual_measure_candidate D S A K =
      covol_selfdual_measure_candidate D S A (covol_standard_fundamental_domain S D) := by
  classical
  let ν : Measure S.FS := covol_selfdual_measure_candidate D S A
  letI : Measure.IsAddHaarMeasure ν := covol_selfdual_measure_candidate_isHaar D S A
  letI : AddAction S.R S.FS :=
    { vadd := fun r x => S.diag (r : F) + x
      add_vadd := by
        intro r s x
        change S.diag ((r + s : S.R) : F) + x =
          S.diag (r : F) + (S.diag (s : F) + x)
        simp only [Subalgebra.coe_add, map_add]
        abel
      zero_vadd := by
        intro x
        change S.diag (0 : F) + x = x
        simp }
  letI : MeasurableConstVAdd S.R S.FS := ⟨fun r => by
    change Measurable (fun x : S.FS => S.diag (r : F) + x)
    fun_prop⟩
  letI : VAddInvariantMeasure S.R S.FS ν := ⟨by
    intro r T _hT
    change ν ((fun x : S.FS => S.diag (r : F) + x) ⁻¹' T) = ν T
    let e : S.FS ≃ᵐ S.FS := MeasurableEquiv.addLeft (S.diag (r : F))
    have hmap : Measure.map e ν = ν := by
      simpa [e] using
        Measure.IsAddLeftInvariant.map_add_left_eq_self (S.diag (r : F))
    calc
      ν ((fun x : S.FS => S.diag (r : F) + x) ⁻¹' T) = Measure.map e ν T := by
        symm
        exact e.map_apply T
      _ = ν T := congrArg (fun m : Measure S.FS => m T) hmap⟩
  letI : Countable F := by
    letI : Countable ℚ := inferInstance
    exact Finsupp.Countable.of_moduleFinite (R := ℚ) (M := F)
  letI : Countable S.R := inferInstance
  have htoFD (T : Set S.FS)
      (hT : MeasurableSet T ∧ S.IsLatticeFundamentalDomain T) :
      MeasureTheory.IsAddFundamentalDomain S.R T ν := by
    have hexact : ∀ x : S.FS, ∃! r : S.R, r +ᵥ x ∈ T := by
      intro x
      obtain ⟨p, hp, huniq⟩ := hT.2 x
      rcases p with ⟨r, k⟩
      rcases hp with ⟨hk, hrep⟩
      refine ⟨-r, ?_, ?_⟩
      · change S.diag ((-r : S.R) : F) + x ∈ T
        rw [hrep]
        simpa [map_neg, add_assoc] using hk
      · intro g hg
        have hrep' : x = S.diag ((-g : S.R) : F) + (g +ᵥ x) := by
          change x = S.diag ((-g : S.R) : F) + (S.diag (g : F) + x)
          simp [map_neg, add_assoc]
        have hpair :
            ((-g : S.R), g +ᵥ x).2 ∈ T ∧
              x = S.diag (((-g : S.R), g +ᵥ x).1 : F) + ((-g : S.R), g +ᵥ x).2 := by
          exact ⟨hg, hrep'⟩
        have hchosen : (r, k).2 ∈ T ∧ x = S.diag ((r, k).1 : F) + (r, k).2 :=
          ⟨hk, hrep⟩
        have heq := huniq (-g, g +ᵥ x) hpair
        have hfirst : -g = r := congrArg Prod.fst heq
        simpa using congrArg (fun a : S.R => -a) hfirst
    exact MeasureTheory.IsAddFundamentalDomain.mk' hT.1.nullMeasurableSet hexact
  have hKfd := htoFD K hK
  have hstd := covol_standard_fundamental_domain_measurable_fd S D
  have hstdFD := htoFD (covol_standard_fundamental_domain S D) hstd
  simpa [ν] using hKfd.measure_eq hstdFD

private theorem measurable_fundamental_domain_measure_one
    (S : SData F CE condη) (D : FieldData F) (A : AddCharData F)
    (μ : S.SelfDualMeasure A) (K : Set S.FS)
    (hK : MeasurableSet K ∧ S.IsLatticeFundamentalDomain K) :
    μ.measure K = 1 := by
  calc
    μ.measure K = covol_selfdual_measure_candidate D S A K := by
      rw [covol_selfdual_measure_candidate_eq D S A μ]
    _ = covol_selfdual_measure_candidate D S A
        (covol_standard_fundamental_domain S D) :=
          covol_candidate_fundamental_domain_mass_eq D S A K hK
    _ = 1 := covol_selfdual_measure_candidate_standard_domain_mass D S A

/-- The diagonal copy of `R` has covolume one for the self-dual Haar measure. -/
theorem SData.diagR_covolume_one (S : SData F CE condη) (D : FieldData F)
    (A : AddCharData F)
    (μ : S.SelfDualMeasure A) :
    ∃ K : Set S.FS, MeasurableSet K ∧ S.IsLatticeFundamentalDomain K ∧ μ.measure K = 1 := by
  obtain ⟨hmeas, hfund⟩ := covol_standard_fundamental_domain_measurable_fd S D
  refine ⟨covol_standard_fundamental_domain S D, hmeas, hfund, ?_⟩
  exact measurable_fundamental_domain_measure_one S D A μ
    (covol_standard_fundamental_domain S D) ⟨hmeas, hfund⟩

/-- Poisson summation on `R` for Bruhat--Schwartz functions on `F_S`, including absolute
convergence of both lattice sums. -/
theorem SData.poisson (S : SData F CE condη) (D : FieldData F) (A : AddCharData F)
    (μ : S.SelfDualMeasure A) (f : S.BruhatSchwartz) :
    Summable (fun m : S.R => ‖(f : S.FS → ℂ) (S.diag (m : F))‖) ∧
      Summable (fun ν : S.R => ‖S.fourier A μ.measure (f : S.FS → ℂ) (S.diag (ν : F))‖) ∧
      ∑' m : S.R, (f : S.FS → ℂ) (S.diag (m : F)) =
        ∑' ν : S.R, S.fourier A μ.measure (f : S.FS → ℂ) (S.diag (ν : F)) := by
  sorry

/-! ## Scaling and the norm identity -/

/-- The annihilator of `aR` is `a⁻¹R`. -/
theorem SData.annihilator_diag_mul (S : SData F CE condη) (D : FieldData F)
    (A : AddCharData F)
    (a : Fˣ) :
    S.annihilator A (Set.range fun x : S.R => S.diag ((a : F) * (x : F))) =
      Set.range fun x : S.R => S.diag ((a : F)⁻¹ * (x : F)) := by
  classical
  have hself := S.diagR_eq_annihilator D A
  have ha0 : (a : F) ≠ 0 := Units.ne_zero a
  ext y
  constructor
  · intro hy
    have hmul_ann : S.diag (a : F) * y ∈ S.annihilator A S.diagR := by
      intro x hx
      rcases hx with ⟨r, rfl⟩
      have h := hy (S.diag ((a : F) * (r : F))) ⟨r, rfl⟩
      simpa [map_mul, mul_assoc, mul_comm, mul_left_comm] using h
    have hmul_mem : S.diag (a : F) * y ∈ S.diagR := hself.symm ▸ hmul_ann
    rcases hmul_mem with ⟨r, hr⟩
    change S.diag (r : F) = S.diag (a : F) * y at hr
    refine ⟨r, ?_⟩
    calc
      S.diag ((a : F)⁻¹ * (r : F)) =
          S.diag ((a : F)⁻¹) * S.diag (r : F) := by rw [map_mul]
      _ = S.diag ((a : F)⁻¹) * (S.diag (a : F) * y) := by rw [hr]
      _ = y := by
        calc
          S.diag ((a : F)⁻¹) * (S.diag (a : F) * y) =
              (S.diag ((a : F)⁻¹) * S.diag (a : F)) * y := by rw [mul_assoc]
          _ = S.diag (1 : F) * y := by rw [← map_mul, inv_mul_cancel₀ ha0]
          _ = y := by simp
  · intro hy
    rcases hy with ⟨r, hr⟩
    subst y
    intro x hx
    rcases hx with ⟨s, rfl⟩
    have hr_diag : S.diag (r : F) ∈ S.diagR := ⟨r, rfl⟩
    have hr_ann : S.diag (r : F) ∈ S.annihilator A S.diagR :=
      hself ▸ hr_diag
    have h := hr_ann (S.diag (s : F)) ⟨s, rfl⟩
    have hpair :
        S.diag ((a : F) * (s : F)) * S.diag ((a : F)⁻¹ * (r : F)) =
          S.diag (s : F) * S.diag (r : F) := by
      calc
        S.diag ((a : F) * (s : F)) * S.diag ((a : F)⁻¹ * (r : F)) =
            S.diag (((a : F) * (s : F)) * ((a : F)⁻¹ * (r : F))) := by
              simp only [map_mul]
        _ = S.diag ((s : F) * (r : F)) := by
          congr 1
          field_simp [ha0]
        _ = S.diag (s : F) * S.diag (r : F) := by simp only [map_mul]
    change S.e A
      (S.diag ((a : F) * (s : F)) * S.diag ((a : F)⁻¹ * (r : F))) = 1
    rw [hpair]
    exact h

/-- The norm identity in `lem:s-lattice` with the total-complexity hypothesis made explicit.
This is the corrected version of the frozen `SData.absS_diag_eq_norm`, whose interface omits
`FieldData F`. -/
theorem SData.absS_diag_eq_norm_ofFieldData (S : SData F CE condη) (D : FieldData F)
    (x : F) (I : Ideal (𝓞 F)) (hI : S.IsExterior I) (hx : S.IsGen x I) :
    S.absS (S.diag x) = Ideal.absNorm I := by
  have : IsTotallyComplex F := D.isTotallyComplex
  exact S.absS_diag_eq_norm x I hI hx

/-- Scaling Poisson summation from `R` to the exterior fractional ideal `aR`. -/
theorem SData.poisson_scaled (S : SData F CE condη) (D : FieldData F) (A : AddCharData F)
    (μ : S.SelfDualMeasure A) (f : S.BruhatSchwartz) (a : Fˣ) (I : Ideal (𝓞 F))
    (hI : S.IsExterior I) (ha : S.IsGen (a : F) I) :
    ∑' m : S.R, (f : S.FS → ℂ) (S.diag ((a : F) * (m : F))) =
      ((Ideal.absNorm I : ℝ) : ℂ)⁻¹ *
        ∑' ν : S.R, S.fourier A μ.measure (f : S.FS → ℂ)
          (S.diag ((a : F)⁻¹ * (ν : F))) := by
  sorry

/-- Every nonzero S-integer has S-norm at least one. -/
theorem SData.absS_diag_ge_one (S : SData F CE condη) (D : FieldData F)
    (x : S.R) (hx : (x : F) ≠ 0) :
    1 ≤ S.absS (S.diag (x : F)) := by
  have : IsTotallyComplex F := D.isTotallyComplex
  have hprod := prod_abs_eq_one hx
  have hf_supp : (Function.mulSupport fun v => ‖FinitePlace.embedding v (x : F)‖).Finite :=
    finitePlace_mk_hasFiniteMulSupport hx
  have h_split : (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖FinitePlace.embedding v (x : F)‖) =
      (∏ v ∈ S.Sf, ‖FinitePlace.embedding v (x : F)‖) * ∏ᶠ v ∉ S.Sf, ‖FinitePlace.embedding v (x : F)‖ := by
    have h_union := finprod_mem_union' (hst := disjoint_compl_right)
      (hs := S.Sf.finite_toSet.inter_of_left _)
      (ht := Set.Finite.subset hf_supp Set.inter_subset_right)
      (f := fun v => ‖FinitePlace.embedding v (x : F)‖)
    rw [Set.union_compl_self, finprod_mem_univ] at h_union
    rw [finprod_mem_coe_finset] at h_union
    exact h_union
  have h_prod_decomp : (∏ᶠ w : FinitePlace F, w (x : F)) =
      (∏ v ∈ S.Sf, ‖FinitePlace.embedding v (x : F)‖) * ∏ᶠ v ∉ S.Sf, ‖FinitePlace.embedding v (x : F)‖ := by
    rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
    change (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖FinitePlace.embedding v (x : F)‖) = _
    exact h_split
  rw [h_prod_decomp] at hprod
  have h_absS : S.absS (S.diag (x : F)) =
      (∏ v ∈ S.Sf, ‖FinitePlace.embedding v (x : F)‖) * ∏ w : InfinitePlace F, w (x : F) ^ w.mult :=
    absS_diag_eq S (x : F)
  have h_prod_absS : S.absS (S.diag (x : F)) * (∏ᶠ v ∉ S.Sf, ‖FinitePlace.embedding v (x : F)‖) = 1 := by
    rw [h_absS]
    calc ((∏ v ∈ S.Sf, ‖FinitePlace.embedding v (x : F)‖) * ∏ w : InfinitePlace F, w (x : F) ^ w.mult) *
          (∏ᶠ v ∉ S.Sf, ‖FinitePlace.embedding v (x : F)‖)
      _ = (∏ w : InfinitePlace F, w (x : F) ^ w.mult) *
          ((∏ v ∈ S.Sf, ‖FinitePlace.embedding v (x : F)‖) * ∏ᶠ v ∉ S.Sf, ‖FinitePlace.embedding v (x : F)‖) := by ring
      _ = 1 := hprod
  have h_eq : (∏ᶠ v ∉ S.Sf, ‖FinitePlace.embedding v (x : F)‖) =
      ∏ v ∈ hf_supp.toFinset with v ∉ S.Sf, ‖FinitePlace.embedding v (x : F)‖ :=
    finprod_mem_eq_prod_filter (fun v => ‖FinitePlace.embedding v (x : F)‖) ((S.Sf : Set _)ᶜ) hf_supp
  have hP_le_one : (∏ᶠ v ∉ S.Sf, ‖FinitePlace.embedding v (x : F)‖) ≤ 1 := by
    rw [h_eq]
    refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun v hv =>
      norm_embedding_le_one_of_valuation_le_one v (x : F) (x.property v (Finset.mem_filter.mp hv).2)
  have h_absS_nonneg : 0 ≤ S.absS (S.diag (x : F)) := by
    rw [h_absS]
    refine mul_nonneg (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      (Finset.prod_nonneg fun w _ => ?_)
    exact pow_nonneg (w.1.nonneg _) _
  calc 1
    _ = S.absS (S.diag (x : F)) * (∏ᶠ v ∉ S.Sf, ‖FinitePlace.embedding v (x : F)‖) := h_prod_absS.symm
    _ ≤ S.absS (S.diag (x : F)) * 1 := mul_le_mul_of_nonneg_left hP_le_one h_absS_nonneg
    _ = S.absS (S.diag (x : F)) := mul_one _

/-! ## Compactness modulo sixth powers of S-units -/

/-- The norm-one subgroup of `F_Sˣ`. -/
def SData.FSOne (S : SData F CE condη) :=
  {x : S.FSˣ // S.absS (x : S.FS) = 1}

/-- Two norm-one elements differ by the sixth power of a diagonal S-unit. -/
def SData.fsOneRel (S : SData F CE condη) (x y : S.FSOne) : Prop :=
  ∃ u : S.US, x.1 = (S.diagU (u : Fˣ)) ^ 6 * y.1

/-- The equivalence relation defining `F_S^1 / U_S^6`. -/
def SData.fsOneSetoid (S : SData F CE condη) : Setoid S.FSOne where
  r := S.fsOneRel
  iseqv := {
    refl := by
      intro x
      change ∃ u : S.US, x.1 = (S.diagU (u : Fˣ)) ^ 6 * x.1
      refine ⟨1, ?_⟩
      simp
    symm := by
      intro x y h
      rcases h with ⟨u, hu⟩
      refine ⟨u⁻¹, ?_⟩
      have hmap : S.diagU ((u⁻¹ : S.US) : Fˣ) = (S.diagU (u : Fˣ))⁻¹ := by
        rw [show ((u⁻¹ : S.US) : Fˣ) = (u : Fˣ)⁻¹ by rfl, map_inv]
      rw [hmap, hu]
      group
    trans := by
      intro x y z hxy hyz
      rcases hxy with ⟨u, hu⟩
      rcases hyz with ⟨v, hv⟩
      refine ⟨u * v, ?_⟩
      have hmap : S.diagU ((u * v : S.US) : Fˣ) =
          S.diagU (u : Fˣ) * S.diagU (v : Fˣ) := by
        rw [show ((u * v : S.US) : Fˣ) = (u : Fˣ) * (v : Fˣ) by rfl, map_mul]
      rw [hmap]
      calc
        x.1 = (S.diagU (u : Fˣ)) ^ 6 * y.1 := hu
        _ = (S.diagU (u : Fˣ) * S.diagU (v : Fˣ)) ^ 6 * z.1 := by
          rw [hv, mul_pow]
          group
  }

private theorem S_units_finite_mod_six (S : SData F CE condη) :
    Finite (S.US ⧸ (powMonoidHom 6 : S.US →* S.US).range) := by
  have hfg : Monoid.FG S.US := by
    change Monoid.FG ((S.Sf : Set (HeightOneSpectrum (𝓞 F))).unit F)
    exact ArtinPrimitiveRoots.Arith.sUnit_fg F S.Sf
  letI : Group.FG S.US := Group.fg_iff_monoid_fg.mpr hfg
  have hindex : (powMonoidHom (α := S.US) 6).range.FiniteIndex :=
    Subgroup.finiteIndex_range_powMonoidHom_of_fg S.US (by norm_num)
  exact Subgroup.finiteIndex_iff_finite_quotient.mp hindex

open Module NumberField.Units NumberField.Units.dirichletUnitTheorem

private theorem covol_unit_balance (D : FieldData F)
    (E : Subgroup (𝓞 F)ˣ) [E.FiniteIndex] :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : InfinitePlace F → ℝ, (∀ w, 0 < t w) →
      ∃ ε : (𝓞 F)ˣ, ε ∈ E ∧ ∀ w,
        |Real.log (‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ * t w) -
          (Fintype.card (InfinitePlace F) : ℝ)⁻¹ *
            ∑ w' : InfinitePlace F, Real.log (t w')| ≤ B := by
  classical
  letI : IsTotallyComplex F := D.isTotallyComplex
  let w₀ : InfinitePlace F := dirichletUnitTheorem.w₀
  let b : Basis (Fin (Units.rank F)) ℝ (dirichletUnitTheorem.logSpace F) :=
    (Units.basisUnitLattice F).ofZLatticeBasis ℝ (Units.unitLattice F)
  let C : ℝ := ∑ i, ‖b i‖
  let n : ℕ := E.index
  let r : ℝ := Fintype.card (InfinitePlace F)
  have hr : 0 < r := by
    dsimp [r]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (InfinitePlace F))
  have hn0 : n ≠ 0 := by
    dsimp [n]
    exact Subgroup.FiniteIndex.index_ne_zero
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨r * n * C, mul_nonneg (mul_nonneg hr.le (Nat.cast_nonneg _)) hC, ?_⟩
  intro t ht
  let m : ℝ := r⁻¹ * ∑ w : InfinitePlace F, Real.log (t w)
  let x : dirichletUnitTheorem.logSpace F := fun w => -2 * (Real.log (t w.val) - m)
  let q : dirichletUnitTheorem.logSpace F := (n : ℝ)⁻¹ • x
  let l : dirichletUnitTheorem.logSpace F := (ZSpan.floor b q : dirichletUnitTheorem.logSpace F)
  let p : dirichletUnitTheorem.logSpace F := ZSpan.fract b q
  have hp : ‖p‖ ≤ C := by
    dsimp [p, C]
    exact ZSpan.norm_fract_le b q
  have hcoord (w : {w : InfinitePlace F // w ≠ w₀}) : |p w| ≤ C := by
    have hc : ‖p w‖ ≤ ‖p‖ := by
      rw [Pi.norm_def]
      have hs : ‖p w‖₊ ≤ Finset.univ.sup
          (fun b : {w : InfinitePlace F // w ≠ w₀} => ‖p b‖₊) :=
        Finset.le_sup (f := fun b : {w : InfinitePlace F // w ≠ w₀} => ‖p b‖₊)
          (Finset.mem_univ w)
      exact NNReal.coe_le_coe.mpr hs
    rw [← Real.norm_eq_abs]
    exact hc.trans hp
  have hlattice : (l : dirichletUnitTheorem.logSpace F) ∈ Units.unitLattice F := by
    have hspan : l ∈ Submodule.span ℤ (Set.range b) := by
      dsimp [l]
      exact (ZSpan.floor b q).property
    have heq : Submodule.span ℤ (Set.range b) = Units.unitLattice F :=
      Module.Basis.ofZLatticeBasis_span ℝ (Units.unitLattice F)
        (Units.basisUnitLattice F)
    exact heq ▸ hspan
  change l ∈ Submodule.map (logEmbedding F).toIntLinearMap ⊤ at hlattice
  obtain ⟨z, hz, hzl⟩ := Submodule.mem_map.mp hlattice
  let η : (𝓞 F)ˣ := z.toMul
  have hη : logEmbedding F (Additive.ofMul η) = l := by
    simpa [η] using hzl
  let ε : (𝓞 F)ˣ := η ^ n
  have hεE : ε ∈ E := by
    dsimp [ε, η]
    exact E.pow_index_mem z.toMul
  have hεlog : logEmbedding F (Additive.ofMul ε) = n • l := by
    rw [show ε = η ^ n by rfl, ofMul_pow, map_nsmul, hη]
  have hcenter : ∑ w : InfinitePlace F, (Real.log (t w) - m) = 0 := by
    dsimp [m, r]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp [Nat.cast_ne_zero.mpr (Fintype.card_pos.ne' :
      Fintype.card (InfinitePlace F) ≠ 0)]
    ring
  have hunit : ∑ w : InfinitePlace F,
      Real.log ‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ = 0 := by
    have hu := Units.sum_mult_mul_log ε
    have hu' : ∑ w : InfinitePlace F,
        2 * Real.log ‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ = 0 := by
      simpa [IsTotallyComplex.mult_eq, ← InfinitePlace.norm_embedding_eq] using hu
    have hsum := hu'
    rw [← Finset.mul_sum] at hsum
    nlinarith
  let d : InfinitePlace F → ℝ := fun w =>
      Real.log ‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ + Real.log (t w) - m
  have hdsum : ∑ w : InfinitePlace F, d w = 0 := by
    dsimp [d]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hunit]
    have hc : (∑ w : InfinitePlace F, Real.log (t w)) -
        (∑ w : InfinitePlace F, m) = 0 := by
      simpa only [Finset.sum_sub_distrib] using hcenter
    linarith [hc]
  have hretained (w : {w : InfinitePlace F // w ≠ w₀}) : |d w.val| ≤ (n : ℝ) * C := by
    have hlog : 2 * Real.log
        ‖w.val.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ =
          (n : ℝ) * (ZSpan.floor b q : dirichletUnitTheorem.logSpace F) w := by
      simpa [logEmbedding_component, IsTotallyComplex.mult_eq,
        InfinitePlace.norm_embedding_eq, Pi.smul_apply, smul_eq_mul, l]
        using congrFun hεlog w
    have hqcoord : q w = (n : ℝ)⁻¹ * x w := by simp [q, Pi.smul_apply]
    have hfract : p w = q w - (ZSpan.floor b q : dirichletUnitTheorem.logSpace F) w := by
      simp [p, ZSpan.fract_apply]
    have hxmul : (n : ℝ) * q w = x w := by
      rw [hqcoord]
      field_simp [hn.ne']
    have hldiff :
        (n : ℝ) * (ZSpan.floor b q : dirichletUnitTheorem.logSpace F) w - x w =
          -(n : ℝ) * p w := by
      rw [← hxmul, hfract]
      ring
    have hvalue : d w.val =
        ((n : ℝ) * (ZSpan.floor b q : dirichletUnitTheorem.logSpace F) w - x w) / 2 := by
      dsimp [d, x]
      rw [← hlog]
      ring
    calc
      |d w.val| = |-(n : ℝ) * p w / 2| := by rw [hvalue, hldiff]
      _ = (n : ℝ) * |p w| / 2 := by
        rw [abs_div, abs_mul, abs_neg, abs_of_nonneg (Nat.cast_nonneg n)]
        norm_num
      _ ≤ (n : ℝ) * C / 2 := by gcongr; exact hcoord w
      _ ≤ (n : ℝ) * C := by nlinarith [mul_nonneg (Nat.cast_nonneg n) hC]
  have hsplit := Fintype.sum_eq_add_sum_subtype_ne d w₀
  have hw₀ : d w₀ = -∑ w : {w : InfinitePlace F // w ≠ w₀}, d w.val := by
    have h := hdsum
    rw [hsplit] at h
    linarith
  have hdrop : |d w₀| ≤ r * (n : ℝ) * C := by
    rw [hw₀, abs_neg]
    calc
      |∑ w : {w : InfinitePlace F // w ≠ w₀}, d w.val| ≤
          ∑ w : {w : InfinitePlace F // w ≠ w₀}, |d w.val| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ w : {w : InfinitePlace F // w ≠ w₀}, (n : ℝ) * C :=
          Finset.sum_le_sum fun w hw => hretained w
      _ = (Fintype.card {w : InfinitePlace F // w ≠ w₀} : ℝ) * ((n : ℝ) * C) := by simp
      _ ≤ r * (n : ℝ) * C := by
          have hcard : Fintype.card {w : InfinitePlace F // w ≠ w₀} ≤
              Fintype.card (InfinitePlace F) := Fintype.card_subtype_le _
          have hreal : (Fintype.card {w : InfinitePlace F // w ≠ w₀} : ℝ) ≤ r := by
            dsimp [r]
            exact_mod_cast hcard
          calc
            (Fintype.card {w : InfinitePlace F // w ≠ w₀} : ℝ) * ((n : ℝ) * C) ≤
                r * ((n : ℝ) * C) := mul_le_mul_of_nonneg_right hreal
                  (mul_nonneg (Nat.cast_nonneg n) hC)
            _ = r * (n : ℝ) * C := by ring
  have hr1 : 1 ≤ r := by
    dsimp [r]
    have hc : 0 < Fintype.card (InfinitePlace F) := Fintype.card_pos
    exact_mod_cast (show 1 ≤ Fintype.card (InfinitePlace F) by omega)
  have hnormpos (w : InfinitePlace F) :
      0 < ‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ := by
    apply norm_pos_iff.mpr
    have hO : (ε : 𝓞 F) ≠ 0 := Units.ne_zero ε
    have hF : algebraMap (𝓞 F) F (ε : 𝓞 F) ≠ 0 :=
      (map_ne_zero_iff (algebraMap (𝓞 F) F)
        (FaithfulSMul.algebraMap_injective (𝓞 F) F)).mpr hO
    exact (map_ne_zero_iff w.embedding w.embedding.injective).mpr hF
  have htarget (w : InfinitePlace F) :
      Real.log (‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ * t w) -
        r⁻¹ * ∑ w' : InfinitePlace F, Real.log (t w') = d w := by
    rw [Real.log_mul (hnormpos w).ne' (ht w).ne']
  refine ⟨ε, hεE, ?_⟩
  intro w
  by_cases hw : w = w₀
  · subst w
    rw [htarget]
    exact hdrop
  · have hd := hretained ⟨w, hw⟩
    have hbound : (n : ℝ) * C ≤ r * (n : ℝ) * C := by
      have hnc : 0 ≤ (n : ℝ) * C := mul_nonneg (Nat.cast_nonneg n) hC
      nlinarith [mul_nonneg (sub_nonneg.mpr hr1) hnc]
    rw [htarget]
    exact hd.trans hbound

private theorem fsOne_compact_representatives (S : SData F CE condη) (D : FieldData F) :
    ∃ K : Set S.FS, IsCompact K ∧
      ∀ x : S.FSOne, ∃ y : S.FSOne, (y.1 : S.FS) ∈ K ∧ S.fsOneRel x y := by
  sorry

/-- Compactness of `F_S^1/U_S^6`, stated as a compact set of representatives for its quotient. -/
theorem SData.FSOne_quotient_compact (S : SData F CE condη) (D : FieldData F) :
    ∃ K : Set S.FS, IsCompact K ∧
      ∀ x : S.FSOne, ∃ y : S.FSOne, (y.1 : S.FS) ∈ K ∧ S.fsOneRel x y := by
  exact fsOne_compact_representatives S D

end ArtinPrimitiveRoots.A1
