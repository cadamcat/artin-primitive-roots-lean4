import ArtinPrimitiveRoots.Spec.Energy
import Mathlib.Analysis.Normed.Operator.CompleteCodomain
import Mathlib.Analysis.Complex.CauchyIntegral
import OAI.NumberTheory.DirichletL.Eisenstein.SeedHeight
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SMOOTH_SEED.E5

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction Topology Pointwise
open Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.spec_seed_p

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

private lemma rowNorm_pos (v : F × F) (hv : v ≠ (0, 0)) (w : InfinitePlace F) :
    0 < ArtinPrimitiveRoots.A1.Spec.rowNorm F v w := by
  have hentry : w.embedding v.1 ≠ 0 ∨ w.embedding v.2 ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv (Prod.ext (w.embedding.injective (by simpa using h.1))
      (w.embedding.injective (by simpa using h.2)))
  unfold ArtinPrimitiveRoots.A1.Spec.rowNorm
  rw [Real.sqrt_pos]
  rcases hentry with hc | hd
  · exact add_pos_of_pos_of_nonneg (Complex.normSq_pos.mpr hc) (Complex.normSq_nonneg _)
  · exact add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _) (Complex.normSq_pos.mpr hd)

private lemma rowPower_summable (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (σ : SL(2,F)) (α : ℝ) (hα : 4 < α) :
    Summable (fun q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ =>
      (∏ w : InfinitePlace F, ArtinPrimitiveRoots.A1.Spec.rowNorm F
        (ArtinPrimitiveRoots.A1.Spec.bottomRow F
          (σ⁻¹ * ArtinPrimitiveRoots.A1.Spec.toSLF F
            ((q.out : Γ) : SL(2,𝓞 F)))) w) ^ (-α)) := by
  let v : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ → F × F := fun q =>
    ArtinPrimitiveRoots.A1.Spec.bottomRow F
      (σ⁻¹ * ArtinPrimitiveRoots.A1.Spec.toSLF F ((q.out : Γ) : SL(2,𝓞 F)))
  let P : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ → ℝ := fun q =>
    ∏ w : InfinitePlace F, ArtinPrimitiveRoots.A1.Spec.rowNorm F (v q) w
  obtain ⟨D, hD, hrows⟩ := ArtinPrimitiveRoots.A1.Spec.E1_eis_def.2 Γ σ (1 : SL(2,F))
  rcases hrows with ⟨hprop, huniq⟩
  have hprops (q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ) :
      v q ≠ (0, 0) ∧
        ArtinPrimitiveRoots.A1.Spec.HasDenominatorBound F D (v q).1 ∧
        ArtinPrimitiveRoots.A1.Spec.HasDenominatorBound F D (v q).2 := by
    simpa [v] using hprop q
  have huniqV : ∀ q q', (∃ ε : (𝓞 F)ˣ,
      v q = ((algebraMap (𝓞 F) F (ε : 𝓞 F)) * (v q').1,
        (algebraMap (𝓞 F) F (ε : 𝓞 F)) * (v q').2)) → q = q' := by
    intro q q' h
    apply huniq q q'
    simpa [v, ArtinPrimitiveRoots.A1.Spec.unitAssociatedRows] using h
  have hsum := ArtinPrimitiveRoots.A1.Spec.R5_lattice_sums D hD α hα v
    (fun q => ⟨(hprops q).2.1, (hprops q).2.2⟩)
    (fun q => (hprops q).1) huniqV
  have hrowpos (q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ) (w : InfinitePlace F) :
      0 < ArtinPrimitiveRoots.A1.Spec.rowNorm F (v q) w := rowNorm_pos (v q) (hprops q).1 w
  have hprod (q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ) :
      (P q) ^ (-α) = ∏ w : InfinitePlace F,
        (ArtinPrimitiveRoots.A1.Spec.rowNorm F (v q) w) ^ (-α) := by
    dsimp [P]
    rw [Real.finsetProd_rpow Finset.univ
      (fun w : InfinitePlace F => ArtinPrimitiveRoots.A1.Spec.rowNorm F (v q) w)
      (fun w hw => (hrowpos q w).le) (-α)]
  have hsumP : Summable (fun q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ => (P q) ^ (-α)) := by
    exact hsum.congr fun q => (hprod q).symm
  simpa [P, v] using hsumP

private abbrev RowFamily := InfinitePlace F → Fin 2 → ℂ

private def rowUnitSet : Set (RowFamily (F := F)) :=
  Set.pi Set.univ (fun _ : InfinitePlace F =>
    {u : Fin 2 → ℂ | OAI.CubicEisenstein.rowEnergy u = 1})

private theorem rowUnitSet_compact : IsCompact (rowUnitSet (F := F)) := by
  exact isCompact_univ_pi
    (fun _ : InfinitePlace F => OAI.CubicEisenstein.rowEnergy_unit_isCompact)

private def botRow (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ) : F × F :=
  ArtinPrimitiveRoots.A1.Spec.bottomRow F
    (σ⁻¹ * ArtinPrimitiveRoots.A1.Spec.toSLF F ((q.out : Γ) : SL(2,𝓞 F)))

private theorem botRow_ne_zero (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (σ : SL(2,F)) (q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ) :
    botRow Γ σ q ≠ (0, 0) := by
  intro h
  have hg : (σ⁻¹ * ArtinPrimitiveRoots.A1.Spec.toSLF F
      ((q.out : Γ) : SL(2,𝓞 F))) 1 0 = 0 := congrArg Prod.fst h
  have hg' : (σ⁻¹ * ArtinPrimitiveRoots.A1.Spec.toSLF F
      ((q.out : Γ) : SL(2,𝓞 F))) 1 1 = 0 := congrArg Prod.snd h
  have hdet := (σ⁻¹ * ArtinPrimitiveRoots.A1.Spec.toSLF F
    ((q.out : Γ) : SL(2,𝓞 F))).property
  rw [Matrix.det_fin_two] at hdet
  simp [hg, hg'] at hdet

private def embeddedRow (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ) (w : InfinitePlace F) : Fin 2 → ℂ :=
  ![w.embedding (botRow Γ σ q).1, w.embedding (botRow Γ σ q).2]

private def normalizedRows (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ) : RowFamily (F := F) :=
  fun w => OAI.CubicEisenstein.normalizedComplexRow (embeddedRow Γ σ q w)

private theorem normalizedRows_mem (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (σ : SL(2,F)) (q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ) :
    normalizedRows Γ σ q ∈ rowUnitSet (F := F) := by
  intro w hw
  apply OAI.CubicEisenstein.normalizedComplexRow_energy
  intro h
  have hv : botRow Γ σ q = (0, 0) := by
    apply Prod.ext
    · apply w.embedding.injective
      simpa [embeddedRow] using congrFun h 0
    · apply w.embedding.injective
      simpa [embeddedRow] using congrFun h 1
  have hg : (σ⁻¹ * ArtinPrimitiveRoots.A1.Spec.toSLF F ((q.out : Γ) : SL(2,𝓞 F))) 1 0 = 0 :=
    congrArg Prod.fst hv
  have hg' : (σ⁻¹ * ArtinPrimitiveRoots.A1.Spec.toSLF F ((q.out : Γ) : SL(2,𝓞 F))) 1 1 = 0 :=
    congrArg Prod.snd hv
  have hdet := (σ⁻¹ * ArtinPrimitiveRoots.A1.Spec.toSLF F
    ((q.out : Γ) : SL(2,𝓞 F))).property
  rw [Matrix.det_fin_two] at hdet
  simp [hg, hg'] at hdet

private def rowProduct (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ) : ℝ :=
  ∏ w : InfinitePlace F,
    ArtinPrimitiveRoots.A1.Spec.rowNorm F (botRow Γ σ q) w

private theorem rowProduct_pos (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (σ : SL(2,F)) (q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ) :
    0 < rowProduct Γ σ q := by
  apply Finset.prod_pos
  intro w hw
  exact rowNorm_pos _ (botRow_ne_zero Γ σ q) w

private def rowScalar (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F)) (s : ℂ)
    (q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ) : ℂ :=
  ((((rowProduct Γ σ q) ^ 2)⁻¹ : ℝ) : ℂ) ^ (1 + 2 * s)

private theorem rowScalar_norm (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (σ : SL(2,F)) (s : ℂ) (q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ) :
    ‖rowScalar Γ σ s q‖ = (rowProduct Γ σ q) ^ (-2 * (1 + 2 * s.re)) := by
  have hP : 0 < rowProduct Γ σ q := rowProduct_pos Γ σ q
  have hbase : 0 < ((rowProduct Γ σ q) ^ 2)⁻¹ := inv_pos.mpr (sq_pos_of_pos hP)
  unfold rowScalar
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hbase]
  have hre : (1 + 2 * s).re = 1 + 2 * s.re := by simp
  rw [hre]
  calc
    (((rowProduct Γ σ q) ^ 2)⁻¹) ^ (1 + 2 * s.re) =
        ((rowProduct Γ σ q) ^ 2) ^ (-(1 + 2 * s.re)) := by
          rw [← Real.rpow_neg_eq_inv_rpow]
    _ = ((rowProduct Γ σ q) ^ (2 : ℝ)) ^ (-(1 + 2 * s.re)) := by
          rw [← Real.rpow_two]
    _ = (rowProduct Γ σ q) ^ (2 * (-(1 + 2 * s.re))) := by
          rw [Real.rpow_mul hP.le]
    _ = (rowProduct Γ σ q) ^ (-2 * (1 + 2 * s.re)) := by ring_nf

private theorem rowScalar_summable (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (σ : SL(2,F)) (s : ℂ) (hs : 1 / 2 < s.re) :
    Summable (fun q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ =>
      ‖rowScalar Γ σ s q‖) := by
  let α : ℝ := 2 * (1 + 2 * s.re)
  have hα : 4 < α := by dsimp [α]; linarith
  have hsum := rowPower_summable Γ σ α hα
  have hsum' : Summable (fun q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ =>
      (rowProduct Γ σ q) ^ (-2 * (1 + 2 * s.re))) := by
    refine hsum.congr ?_
    intro q
    congr 1
    dsimp [α]
    ring
  exact hsum'.congr fun q => (rowScalar_norm Γ σ s q).symm

private def spatialOfCoord (c : ℂ × ℝ) : OAI.CubicEisenstein.SpatialCoordinates :=
  ![c.1.re, c.1.im, c.2]

private def regularizedKernel (s : ℂ) (δ : ℝ) (u : RowFamily (F := F))
    (p : ArtinPrimitiveRoots.A1.Spec.Coord F) : ℂ :=
  ∏ w : InfinitePlace F,
    OAI.CubicEisenstein.regularRowKernel (1 + 2 * s) δ (u w) (spatialOfCoord (p w))

private def cutoffFamily (s : ℂ) (δ : ℝ) (ψ : ArtinPrimitiveRoots.A1.Spec.Coord F → ℂ)
    (u : RowFamily (F := F)) (p : ArtinPrimitiveRoots.A1.Spec.Coord F) : ℂ :=
  ψ p * regularizedKernel s δ u p

private theorem spatialOfCoord_contDiff :
    ContDiff ℝ ∞ spatialOfCoord := by
  apply contDiff_pi.2
  intro i
  fin_cases i
  · exact Complex.reCLM.contDiff.comp (contDiff_fst)
  · exact Complex.imCLM.contDiff.comp (contDiff_fst)
  · exact contDiff_snd

private theorem cutoffFamily_contDiffAt
    (s : ℂ) (δ : ℝ) (hδ : 0 < δ) (ψ : ArtinPrimitiveRoots.A1.Spec.Coord F → ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (u : RowFamily (F := F)) (hu : u ∈ rowUnitSet (F := F))
    (p : ArtinPrimitiveRoots.A1.Spec.Coord F) :
    ContDiffAt ℝ ∞ (Function.uncurry (cutoffFamily s δ ψ)) (u,p) := by
  classical
  have hrow (w : InfinitePlace F) : u w ≠ 0 := by
    intro h
    have hu' : OAI.CubicEisenstein.rowEnergy (u w) = 1 := hu w (Set.mem_univ w)
    simp [h, OAI.CubicEisenstein.rowEnergy] at hu'
  have hrowSmooth (w : InfinitePlace F) :
      ContDiffAt ℝ ∞
        (fun z : RowFamily (F := F) × ArtinPrimitiveRoots.A1.Spec.Coord F =>
          OAI.CubicEisenstein.regularRowKernel (1 + 2 * s) δ (z.1 w)
            (spatialOfCoord (z.2 w))) (u,p) := by
    have huEval : ContDiff ℝ ∞
        (fun z : RowFamily (F := F) × ArtinPrimitiveRoots.A1.Spec.Coord F => z.1 w) := by
      exact (contDiff_apply ℝ (Fin 2 → ℂ) w).comp contDiff_fst
    have hpEval : ContDiff ℝ ∞
        (fun z : RowFamily (F := F) × ArtinPrimitiveRoots.A1.Spec.Coord F =>
          spatialOfCoord (z.2 w)) := by
      exact spatialOfCoord_contDiff.comp
        ((contDiff_apply ℝ (ℂ × ℝ) w).comp contDiff_snd)
    have huAt := huEval.contDiffAt (x := (u,p))
    have hpAt := hpEval.contDiffAt (x := (u,p))
    have hinput : ContDiffAt ℝ ∞
        (fun z : RowFamily (F := F) × ArtinPrimitiveRoots.A1.Spec.Coord F =>
          (z.1 w, spatialOfCoord (z.2 w))) (u,p) :=
      huAt.prodMk hpAt
    have hkernel : ContDiffAt ℝ ∞
        (Function.uncurry (OAI.CubicEisenstein.regularRowKernel (1 + 2 * s) δ))
        (u w, spatialOfCoord (p w)) :=
      OAI.CubicEisenstein.regularRowKernel_contDiffAt (1 + 2 * s) δ hδ
        (u w) (hrow w) (spatialOfCoord (p w))
    convert hkernel.comp (u,p) hinput using 1 <;> rfl
  have hprod : ContDiffAt ℝ ∞ (fun z : RowFamily (F := F) ×
      ArtinPrimitiveRoots.A1.Spec.Coord F =>
      ∏ w : InfinitePlace F, OAI.CubicEisenstein.regularRowKernel (1 + 2 * s) δ
          (z.1 w) (spatialOfCoord (z.2 w))) (u,p) := by
    simpa only [Finset.prod_apply] using
      contDiffAt_prod (t := Finset.univ) (fun w hw => hrowSmooth w)
  have hψ' : ContDiffAt ℝ ∞ (fun z : RowFamily (F := F) ×
      ArtinPrimitiveRoots.A1.Spec.Coord F => ψ z.2) (u,p) :=
    hψ.contDiffAt.comp (u,p) contDiffAt_snd
  exact hψ'.mul hprod

private theorem ofReal_cpow_finset_prod {ι : Type*} (t : Finset ι) (f : ι → ℝ)
    (a : ℂ) (hf : ∀ i ∈ t, 0 ≤ f i) :
    (((∏ i ∈ t, f i : ℝ) : ℂ) ^ a) =
      ∏ i ∈ t, ((f i : ℝ) : ℂ) ^ a := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
      have hft : ∀ j ∈ t, 0 ≤ f j := fun j hj => hf j (Finset.mem_insert_of_mem hj)
      have hfi : 0 ≤ f i := hf i (Finset.mem_insert_self _ _)
      rw [Finset.prod_insert hi, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg hfi
          (Finset.prod_nonneg fun j hj => hft j hj) a,
        ih hft]
      simp [Finset.prod_insert, hi]

private theorem embeddedRow_energy (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ) (w : InfinitePlace F) :
    OAI.CubicEisenstein.rowEnergy (embeddedRow Γ σ q w) =
      (ArtinPrimitiveRoots.A1.Spec.rowNorm F (botRow Γ σ q) w) ^ 2 := by
  unfold ArtinPrimitiveRoots.A1.Spec.rowNorm
  rw [Real.sq_sqrt]
  · simp [OAI.CubicEisenstein.rowEnergy, embeddedRow, Complex.normSq_eq_norm_sq]
  · exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

private def localDenominator (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ)
    (p : ArtinPrimitiveRoots.A1.Spec.Coord F) (w : InfinitePlace F) : ℝ :=
  Complex.normSq (w.embedding (botRow Γ σ q).1 * (p w).1 +
      w.embedding (botRow Γ σ q).2) +
    Complex.normSq (w.embedding (botRow Γ σ q).1) * (p w).2 ^ 2

private theorem localDenominator_pos (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (σ : SL(2,F)) (q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ)
    (p : ArtinPrimitiveRoots.A1.Spec.Coord F) (hp : p ∈ ArtinPrimitiveRoots.A1.Spec.posSet F)
    (w : InfinitePlace F) : 0 < localDenominator Γ σ q p w := by
  have hv : botRow Γ σ q ≠ (0, 0) := by
    exact botRow_ne_zero Γ σ q
  have he : w.embedding (botRow Γ σ q).1 ≠ 0 ∨
      w.embedding (botRow Γ σ q).2 ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv (Prod.ext (w.embedding.injective (by simpa using h.1))
      (w.embedding.injective (by simpa using h.2)))
  rcases he with hc | hd
  · exact lt_of_lt_of_le
      (mul_pos (Complex.normSq_pos.mpr hc) (sq_pos_of_pos (hp w)))
      (le_add_of_nonneg_left (Complex.normSq_nonneg _))
  · by_cases hc0 : w.embedding (botRow Γ σ q).1 = 0
    · have hfirst : 0 < Complex.normSq
          (w.embedding (botRow Γ σ q).1 * (p w).1 + w.embedding (botRow Γ σ q).2) := by
        rw [hc0, zero_mul, zero_add]
        exact Complex.normSq_pos.mpr hd
      exact lt_of_lt_of_le hfirst
        (le_add_of_nonneg_right
          (mul_nonneg (Complex.normSq_nonneg _) (sq_nonneg _)))
    · exact lt_of_lt_of_le
        (mul_pos (Complex.normSq_pos.mpr hc0) (sq_pos_of_pos (hp w)))
        (le_add_of_nonneg_left (Complex.normSq_nonneg _))

private theorem rowFactor_eq_regularizedKernel
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (σ : SL(2,F)) (s : ℂ)
    (q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ)
    (p : ArtinPrimitiveRoots.A1.Spec.Coord F) (hp : p ∈ ArtinPrimitiveRoots.A1.Spec.posSet F)
    (w : InfinitePlace F) (δ : ℝ) (hδ : 0 < δ) (hδy : δ ≤ (p w).2) :
    (((((p w).2 / localDenominator Γ σ q p w : ℝ) : ℂ) ^ (1 + 2 * s)) =
      ((((ArtinPrimitiveRoots.A1.Spec.rowNorm F (botRow Γ σ q) w) ^ 2)⁻¹ : ℝ) : ℂ) ^
          (1 + 2 * s) *
        OAI.CubicEisenstein.regularRowKernel (1 + 2 * s) δ
          (normalizedRows Γ σ q w) (spatialOfCoord (p w))) := by
  let u := embeddedRow Γ σ q w
  let ur := normalizedRows Γ σ q w
  let r := ArtinPrimitiveRoots.A1.Spec.rowNorm F (botRow Γ σ q) w
  let y := (p w).2
  let x := (p w).1
  have hu : u ≠ 0 := by
    intro h
    have hv : botRow Γ σ q = (0, 0) := by
      apply Prod.ext
      · apply w.embedding.injective
        simpa [u, embeddedRow] using congrFun h 0
      · apply w.embedding.injective
        simpa [u, embeddedRow] using congrFun h 1
    exact botRow_ne_zero Γ σ q hv
  have hr : 0 < r := rowNorm_pos _ (botRow_ne_zero Γ σ q) w
  have hyr : 0 < y := hp w
  have hQ : 0 < localDenominator Γ σ q p w := localDenominator_pos Γ σ q p hp w
  have hQn : 0 < OAI.CubicEisenstein.heightDenominator x y ur := by
    exact OAI.CubicEisenstein.heightDenominator_pos
      x y hyr ur
      (OAI.CubicEisenstein.rowEnergy_unit_ne_zero ur
        (normalizedRows_mem Γ σ q w (Set.mem_univ w)))
  have henergy : OAI.CubicEisenstein.rowEnergy u = r ^ 2 := by
    simpa [u, r] using embeddedRow_energy Γ σ q w
  have hQorig : OAI.CubicEisenstein.heightDenominator x y u =
      localDenominator Γ σ q p w := by
    simp [OAI.CubicEisenstein.heightDenominator, localDenominator,
      x, y, u, embeddedRow, ← Complex.normSq_eq_norm_sq]
  have hQscale : OAI.CubicEisenstein.heightDenominator x y ur =
      localDenominator Γ σ q p w / r ^ 2 := by
    calc
      OAI.CubicEisenstein.heightDenominator x y ur =
          OAI.CubicEisenstein.heightDenominator x y u /
            OAI.CubicEisenstein.rowEnergy u := by
        simpa [ur, normalizedRows] using
          OAI.CubicEisenstein.heightDenominator_normalized x y u
      _ = localDenominator Γ σ q p w / r ^ 2 := by rw [hQorig, henergy]
  have hratio : y / localDenominator Γ σ q p w = ((r ^ 2)⁻¹) *
      (y / OAI.CubicEisenstein.heightDenominator x y ur) := by
    rw [hQscale]
    field_simp [ne_of_gt hr, ne_of_gt hQ, ne_of_gt hQn]
  let ratioNorm : ℝ := (r ^ 2)⁻¹ *
    (y / OAI.CubicEisenstein.heightDenominator x y ur)
  have hcast : ((y / localDenominator Γ σ q p w : ℝ) : ℂ) =
      (ratioNorm : ℂ) := by
    simpa [ratioNorm] using congrArg Complex.ofReal hratio
  have hpow : (((y / localDenominator Γ σ q p w : ℝ) : ℂ) ^ (1 + 2 * s)) =
      ((((r ^ 2)⁻¹ : ℝ) : ℂ) ^ (1 + 2 * s)) *
        (((y / OAI.CubicEisenstein.heightDenominator x y ur : ℝ) : ℂ) ^ (1 + 2 * s)) := by
    calc
      (((y / localDenominator Γ σ q p w : ℝ) : ℂ) ^ (1 + 2 * s)) =
          (ratioNorm : ℂ) ^ (1 + 2 * s) :=
          congrArg (fun z : ℂ => z ^ (1 + 2 * s)) hcast
      _ = ((((r ^ 2)⁻¹ : ℝ) : ℂ) ^ (1 + 2 * s)) *
          (((y / OAI.CubicEisenstein.heightDenominator x y ur : ℝ) : ℂ) ^ (1 + 2 * s)) := by
          simpa [ratioNorm, Complex.ofReal_mul] using
            (Complex.mul_cpow_ofReal_nonneg (inv_nonneg.mpr (sq_nonneg r))
              (div_nonneg hyr.le hQn.le) (1 + 2 * s))
  have hreg : OAI.CubicEisenstein.regularRowKernel (1 + 2 * s) δ ur
      (spatialOfCoord (p w)) =
      (((y / OAI.CubicEisenstein.heightDenominator x y ur : ℝ) : ℂ) ^ (1 + 2 * s)) := by
    have hhor : OAI.CubicEisenstein.spatialHorizontal (spatialOfCoord (p w)) = x := by
      apply Complex.ext <;> simp [OAI.CubicEisenstein.spatialHorizontal, spatialOfCoord, x]
    unfold OAI.CubicEisenstein.regularRowKernel
    rw [OAI.CubicEisenstein.regularSpatialHeight_eq δ hδ (spatialOfCoord (p w))]
    · rw [hhor]
      exact OAI.CubicEisenstein.logRatioPower_eq_cpow (1 + 2 * s) hyr hQn
    · simpa [spatialOfCoord, y] using hδy
  simpa [r, y, ur, normalizedRows] using (calc
    (((y / localDenominator Γ σ q p w : ℝ) : ℂ) ^ (1 + 2 * s)) =
        ((((r ^ 2)⁻¹ : ℝ) : ℂ) ^ (1 + 2 * s)) *
          (((y / OAI.CubicEisenstein.heightDenominator x y ur : ℝ) : ℂ) ^ (1 + 2 * s)) := hpow
    _ = ((((r ^ 2)⁻¹ : ℝ) : ℂ) ^ (1 + 2 * s)) *
          OAI.CubicEisenstein.regularRowKernel (1 + 2 * s) δ ur
            (spatialOfCoord (p w)) := by rw [hreg])

private theorem term_eq_rowScalar_regularized
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (σ : SL(2,F)) (s : ℂ)
    (q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ)
    (p : ArtinPrimitiveRoots.A1.Spec.Coord F) (hp : p ∈ ArtinPrimitiveRoots.A1.Spec.posSet F)
    (δ : ℝ) (hδ : 0 < δ) (hδy : ∀ w, δ ≤ (p w).2) :
    ArtinPrimitiveRoots.A1.Spec.eisTerm F Γ σ s (ArtinPrimitiveRoots.A1.Spec.ptX F p) q =
      rowScalar Γ σ s q * regularizedKernel s δ (normalizedRows Γ σ q) p := by
  let g := σ⁻¹ * ArtinPrimitiveRoots.A1.Spec.toSLF F ((q.out : Γ) : SL(2,𝓞 F))
  let x : InfinitePlace F → ℂ := fun w => (p w).1
  let y : InfinitePlace F → ℝ := fun w => (p w).2
  have hy : ∀ w, 0 < y w := fun w => hp w
  have hpt : ArtinPrimitiveRoots.A1.Spec.ptX' F x y =
      ArtinPrimitiveRoots.A1.Spec.ptX F p := by
    funext w
    rfl
  have haction : ArtinPrimitiveRoots.A1.Spec.normHeight F
      (g • ArtinPrimitiveRoots.A1.Spec.ptX F p) =
      ∏ w : InfinitePlace F, y w / localDenominator Γ σ q p w := by
    have hG := (ArtinPrimitiveRoots.A1.Spec.G2_x_action (F := F)).1 g x y hy
    calc
      ArtinPrimitiveRoots.A1.Spec.normHeight F (g • ArtinPrimitiveRoots.A1.Spec.ptX F p) =
          ArtinPrimitiveRoots.A1.Spec.normHeight F (g • ArtinPrimitiveRoots.A1.Spec.ptX' F x y) := by
            rw [hpt]
      _ = ∏ w : InfinitePlace F, y w /
          (Complex.normSq (w.embedding (g 1 0) * x w + w.embedding (g 1 1)) +
            Complex.normSq (w.embedding (g 1 0)) * y w ^ 2) := hG
      _ = ∏ w : InfinitePlace F, y w / localDenominator Γ σ q p w := by
            apply Finset.prod_congr rfl
            intro w hw
            simp [g, x, y, localDenominator, botRow,
              ArtinPrimitiveRoots.A1.Spec.bottomRow]
  have hact : σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • ArtinPrimitiveRoots.A1.Spec.ptX F p) =
      g • ArtinPrimitiveRoots.A1.Spec.ptX F p := by
    change σ⁻¹ • ((ArtinPrimitiveRoots.A1.Spec.toSLF F
      ((q.out : Γ) : SL(2,𝓞 F))) • ArtinPrimitiveRoots.A1.Spec.ptX F p) = _
    simpa [g] using
      smul_smul σ⁻¹ (ArtinPrimitiveRoots.A1.Spec.toSLF F
        ((q.out : Γ) : SL(2,𝓞 F))) (ArtinPrimitiveRoots.A1.Spec.ptX F p)
  have hpos (w : InfinitePlace F) : 0 < y w / localDenominator Γ σ q p w :=
    div_pos (hy w) (localDenominator_pos Γ σ q p hp w)
  have hcpow := ofReal_cpow_finset_prod (Finset.univ : Finset (InfinitePlace F))
    (fun w => y w / localDenominator Γ σ q p w) (1 + 2 * s)
    (fun w hw => (hpos w).le)
  have hrpos (w : InfinitePlace F) :
      0 < ArtinPrimitiveRoots.A1.Spec.rowNorm F (botRow Γ σ q) w :=
    rowNorm_pos _ (botRow_ne_zero Γ σ q) w
  have hrowProdPower :
      (∏ w : InfinitePlace F,
        ((ArtinPrimitiveRoots.A1.Spec.rowNorm F (botRow Γ σ q) w) ^ 2)⁻¹) =
        ((rowProduct Γ σ q) ^ 2)⁻¹ := by
    rw [Finset.prod_inv_distrib, Finset.prod_pow]
    rfl
  have hscalarProd :
      (∏ w : InfinitePlace F,
        ((((ArtinPrimitiveRoots.A1.Spec.rowNorm F (botRow Γ σ q) w) ^ 2)⁻¹ : ℝ) : ℂ) ^
          (1 + 2 * s)) = rowScalar Γ σ s q := by
    calc
      _ = (((∏ w : InfinitePlace F,
            ((ArtinPrimitiveRoots.A1.Spec.rowNorm F (botRow Γ σ q) w) ^ 2)⁻¹ : ℝ) : ℂ) ^
              (1 + 2 * s)) := by
        symm
        exact ofReal_cpow_finset_prod (Finset.univ : Finset (InfinitePlace F))
          (fun w => ((ArtinPrimitiveRoots.A1.Spec.rowNorm F (botRow Γ σ q) w) ^ 2)⁻¹)
          (1 + 2 * s) (fun w hw => inv_nonneg.mpr (sq_nonneg _))
      _ = rowScalar Γ σ s q := by rw [hrowProdPower]; rfl
  unfold ArtinPrimitiveRoots.A1.Spec.eisTerm
  rw [hact, haction, Complex.ofReal_prod]
  calc
    (∏ w : InfinitePlace F, ((y w / localDenominator Γ σ q p w : ℝ) : ℂ)) ^
        (1 + 2 * s) =
      ∏ w : InfinitePlace F,
        ((y w / localDenominator Γ σ q p w : ℝ) : ℂ) ^ (1 + 2 * s) := by
      simpa using hcpow
    _ = ∏ w : InfinitePlace F,
        ((((ArtinPrimitiveRoots.A1.Spec.rowNorm F (botRow Γ σ q) w) ^ 2)⁻¹ : ℝ) : ℂ) ^
            (1 + 2 * s) *
          OAI.CubicEisenstein.regularRowKernel (1 + 2 * s) δ
            (normalizedRows Γ σ q w) (spatialOfCoord (p w)) := by
      apply Finset.prod_congr rfl
      intro w hw
      exact rowFactor_eq_regularizedKernel Γ σ s q p hp w δ hδ (hδy w)
    _ = (∏ w : InfinitePlace F,
          ((((ArtinPrimitiveRoots.A1.Spec.rowNorm F (botRow Γ σ q) w) ^ 2)⁻¹ : ℝ) : ℂ) ^
            (1 + 2 * s)) *
        regularizedKernel s δ (normalizedRows Γ σ q) p := by
      rw [Finset.prod_mul_distrib]
      rfl
    _ = rowScalar Γ σ s q * regularizedKernel s δ (normalizedRows Γ σ q) p := by
      rw [← hscalarProd]

private abbrev PosCoord := {p : ArtinPrimitiveRoots.A1.Spec.Coord F //
  p ∈ ArtinPrimitiveRoots.A1.Spec.posSet F}

private def localHeightFloor (p : PosCoord (F := F)) : ℝ :=
  (2 * ∑ w : InfinitePlace F, ((p.1 w).2)⁻¹)⁻¹

private theorem localHeightFloor_pos (p : PosCoord (F := F)) :
    0 < localHeightFloor p := by
  classical
  have hsum : 0 < ∑ w : InfinitePlace F, ((p.1 w).2)⁻¹ := by
    apply Finset.sum_pos
    · intro w hw
      exact inv_pos.mpr (p.2 w)
    · exact Finset.univ_nonempty
  exact inv_pos.mpr (mul_pos (by norm_num) hsum)

private theorem localHeightFloor_lt (p : PosCoord (F := F)) (w : InfinitePlace F) :
    localHeightFloor p < (p.1 w).2 := by
  classical
  let S : ℝ := ∑ v : InfinitePlace F, ((p.1 v).2)⁻¹
  have hS : 0 < S := by
    dsimp [S]
    apply Finset.sum_pos
    · intro v hv
      exact inv_pos.mpr (p.2 v)
    · exact Finset.univ_nonempty
  have hsingle : ((p.1 w).2)⁻¹ ≤ S := by
    dsimp [S]
    exact Finset.single_le_sum
      (fun v hv => inv_nonneg.mpr (le_of_lt (p.2 v))) (Finset.mem_univ w)
  have hmul : 1 ≤ S * (p.1 w).2 := by
    have h := mul_le_mul_of_nonneg_left hsingle (le_of_lt (p.2 w))
    have hcancel : (p.1 w).2 * ((p.1 w).2)⁻¹ = 1 := by
      field_simp [ne_of_gt (p.2 w)]
    calc
      1 = (p.1 w).2 * ((p.1 w).2)⁻¹ := hcancel.symm
      _ ≤ (p.1 w).2 * S := h
      _ = S * (p.1 w).2 := by ring
  have hSinv : S⁻¹ ≤ (p.1 w).2 :=
    (inv_le_iff_one_le_mul₀' hS).2 hmul
  have hstrict : (2 * S)⁻¹ < S⁻¹ := by
    have htwice : S < 2 * S := by nlinarith
    simpa [one_div] using one_div_lt_one_div_of_lt hS htwice
  exact lt_of_lt_of_le (by simpa [localHeightFloor, S] using hstrict) hSinv

private def localHeightAbove (δ : ℝ) : Set (ArtinPrimitiveRoots.A1.Spec.Coord F) :=
  {p | ∀ w : InfinitePlace F, δ < (p w).2}

private theorem localHeightAbove_open (δ : ℝ) : IsOpen (localHeightAbove (F := F) δ) := by
  rw [localHeightAbove, Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun w => by
    have hc : Continuous (fun p : ArtinPrimitiveRoots.A1.Spec.Coord F => (p w).2) :=
      continuous_snd.comp (continuous_apply w)
    exact isOpen_lt continuous_const hc

private structure LocalCutoff (p : PosCoord (F := F)) where
  bump : ContDiffBump p.1
  supportAbove : ∀ x ∈ tsupport bump, ∀ w : InfinitePlace F,
    localHeightFloor p < (x w).2

private theorem localCutoff_exists (p : PosCoord (F := F)) : Nonempty (LocalCutoff p) := by
  classical
  let δ := localHeightFloor p
  obtain ⟨ε, hε, hball⟩ := (Metric.isOpen_iff.mp (localHeightAbove_open (F := F) δ))
    p.1 (fun w => localHeightFloor_lt p w)
  let χ : ContDiffBump p.1 := ⟨ε / 2, 3 * ε / 4, by positivity, by nlinarith⟩
  have hrOut : χ.rOut < ε := by dsimp [χ]; nlinarith
  refine ⟨⟨χ, ?_⟩⟩
  intro x hx w
  have hxClosed : x ∈ Metric.closedBall p.1 χ.rOut := by
    simpa [χ.tsupport_eq] using hx
  have hdist : dist x p.1 ≤ χ.rOut := Metric.mem_closedBall.mp hxClosed
  have hxBall : x ∈ Metric.ball p.1 ε :=
    Metric.mem_ball.mpr (lt_of_le_of_lt hdist hrOut)
  exact hball hxBall w

private noncomputable def localCutoff (p : PosCoord (F := F)) : LocalCutoff p :=
  Classical.choice (localCutoff_exists p)

private theorem localCutoff_supportAbove (p : PosCoord (F := F))
    (x : ArtinPrimitiveRoots.A1.Spec.Coord F) (hx : x ∈ tsupport (localCutoff p).bump)
    (w : InfinitePlace F) : localHeightFloor p < (x w).2 :=
  (localCutoff p).supportAbove x hx w

private def localPsi (p : PosCoord (F := F))
    (x : ArtinPrimitiveRoots.A1.Spec.Coord F) : ℂ :=
  ((localCutoff p).bump x : ℝ)

private theorem localPsi_contDiff (p : PosCoord (F := F)) :
    ContDiff ℝ ∞ (localPsi p) := by
  exact Complex.ofRealCLM.contDiff.comp (localCutoff p).bump.contDiff

private theorem localPsi_hasCompactSupport (p : PosCoord (F := F)) :
    HasCompactSupport (localPsi p) := by
  have hsupp : Function.support (localPsi p) = Function.support (localCutoff p).bump := by
    ext x
    simp [localPsi, Function.mem_support]
  change IsCompact (closure (Function.support (localPsi p)))
  rw [hsupp]
  exact (localCutoff p).bump.hasCompactSupport

private theorem localPsi_eq_one_eventually (p : PosCoord (F := F))
    {x : ArtinPrimitiveRoots.A1.Spec.Coord F}
    (hx : x ∈ Metric.ball p.1 (localCutoff p).bump.rIn) :
    localPsi p =ᶠ[𝓝 x] 1 := by
  filter_upwards [(localCutoff p).bump.eventuallyEq_one_of_mem_ball hx] with y hy
  simp [localPsi, hy]

private def localizedSeries (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F)) (s : ℂ)
    (p : PosCoord (F := F)) : ArtinPrimitiveRoots.A1.Spec.Coord F → ℂ :=
  fun x => ∑' q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ,
    rowScalar Γ σ s q * cutoffFamily s (localHeightFloor p) (localPsi p)
      (normalizedRows Γ σ q) x

private theorem localized_family_data
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (σ : SL(2,F)) (s : ℂ)
    (p : PosCoord (F := F)) :
    (∀ u ∈ rowUnitSet (F := F), ∀ x,
      ContDiffAt ℝ ∞ (Function.uncurry
        (cutoffFamily s (localHeightFloor p) (localPsi p))) (u,x)) ∧
    (∀ u ∈ rowUnitSet (F := F),
      tsupport (cutoffFamily s (localHeightFloor p) (localPsi p) u) ⊆
        tsupport (localPsi p)) := by
  constructor
  · intro u hu x
    exact cutoffFamily_contDiffAt s (localHeightFloor p) (localHeightFloor_pos p)
      (localPsi p) (localPsi_contDiff p) u hu x
  · intro u hu
    change tsupport (fun x => localPsi p x * regularizedKernel s (localHeightFloor p) u x) ⊆
      tsupport (localPsi p)
    exact tsupport_mul_subset_left

private theorem localizedSeries_contDiff
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (σ : SL(2,F)) (s : ℂ)
    (hs : 1 / 2 < s.re) (p : PosCoord (F := F)) :
    ContDiff ℝ ∞ (localizedSeries Γ σ s p) := by
  classical
  rcases localized_family_data Γ σ s p with ⟨hF, hsupp⟩
  exact OAI.CubicEisenstein.compact_smooth_family_tsum
    (cutoffFamily s (localHeightFloor p) (localPsi p))
    (rowUnitSet (F := F)) (tsupport (localPsi p))
    rowUnitSet_compact (localPsi_hasCompactSupport p) hF hsupp
    (normalizedRows Γ σ) (fun q => normalizedRows_mem Γ σ q)
    (rowScalar Γ σ s) (rowScalar_summable Γ σ s hs)

private theorem localizedDerivativeConstant
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (σ : SL(2,F)) (s : ℂ)
    (hs : 1 / 2 < s.re) (p : PosCoord (F := F)) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ,
      ∀ x : ArtinPrimitiveRoots.A1.Spec.Coord F,
        ‖iteratedFDeriv ℝ n
          (fun y => rowScalar Γ σ s q * cutoffFamily s (localHeightFloor p)
            (localPsi p) (normalizedRows Γ σ q) y) x‖ ≤ C * ‖rowScalar Γ σ s q‖ := by
  classical
  rcases localized_family_data Γ σ s p with ⟨hF, hsupp⟩
  obtain ⟨C, hC, hbound⟩ :=
    OAI.CubicEisenstein.compact_family_derivative_bound
      (cutoffFamily s (localHeightFloor p) (localPsi p))
      (rowUnitSet (F := F)) (tsupport (localPsi p))
      rowUnitSet_compact (localPsi_hasCompactSupport p) hF hsupp n
  refine ⟨C, hC, ?_⟩
  intro q x
  let u := normalizedRows Γ σ q
  have hu : u ∈ rowUnitSet (F := F) := normalizedRows_mem Γ σ q
  have hFAt : ContDiffAt ℝ ∞
      (fun y => cutoffFamily s (localHeightFloor p) (localPsi p) u y) x := by
    have hpair : ContDiffAt ℝ ∞
        (fun y : ArtinPrimitiveRoots.A1.Spec.Coord F => (u,y)) x :=
      contDiffAt_const.prodMk contDiffAt_id
    exact (hF u hu x).comp x hpair
  have hFn : ContDiffAt ℝ n
      (fun y => cutoffFamily s (localHeightFloor p) (localPsi p) u y) x :=
    hFAt.of_le (by simp)
  have hderiv :
      iteratedFDeriv ℝ n
        (fun y => rowScalar Γ σ s q * cutoffFamily s (localHeightFloor p)
          (localPsi p) u y) x =
        rowScalar Γ σ s q • iteratedFDeriv ℝ n
          (fun y => cutoffFamily s (localHeightFloor p) (localPsi p) u y) x := by
    simpa only [smul_eq_mul] using
      (iteratedFDeriv_const_smul_apply' (a := rowScalar Γ σ s q) (i := n) (x := x) hFn)
  calc
    ‖iteratedFDeriv ℝ n
        (fun y => rowScalar Γ σ s q * cutoffFamily s (localHeightFloor p)
          (localPsi p) u y) x‖ =
        ‖rowScalar Γ σ s q‖ *
          ‖iteratedFDeriv ℝ n
            (fun y => cutoffFamily s (localHeightFloor p) (localPsi p) u y) x‖ := by
      rw [hderiv, norm_smul]
    _ ≤ ‖rowScalar Γ σ s q‖ * C :=
      mul_le_mul_of_nonneg_left (hbound u hu x) (norm_nonneg _)
    _ = C * ‖rowScalar Γ σ s q‖ := by ring

private theorem localPsi_height_at_one (p : PosCoord (F := F))
    (x : ArtinPrimitiveRoots.A1.Spec.Coord F) (hx : localPsi p x = 1)
    (w : InfinitePlace F) : localHeightFloor p < (x w).2 := by
  have hreal : (localCutoff p).bump x = 1 := by
    apply Complex.ofReal_injective
    simpa [localPsi] using hx
  have hmem : x ∈ Function.support (localCutoff p).bump := by
    simp [Function.mem_support, hreal]
  exact localCutoff_supportAbove p x (subset_closure hmem) w

private theorem localTerm_eq_weighted
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (σ : SL(2,F)) (s : ℂ)
    (p : PosCoord (F := F)) (x : ArtinPrimitiveRoots.A1.Spec.Coord F)
    (hψ : localPsi p x = 1) (q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ) :
    ArtinPrimitiveRoots.A1.Spec.eisTerm F Γ σ s (ArtinPrimitiveRoots.A1.Spec.ptX F x) q =
      rowScalar Γ σ s q * cutoffFamily s (localHeightFloor p) (localPsi p)
        (normalizedRows Γ σ q) x := by
  have hpos : x ∈ ArtinPrimitiveRoots.A1.Spec.posSet F := by
    intro w
    exact lt_trans (localHeightFloor_pos p) (localPsi_height_at_one p x hψ w)
  have hdelta : ∀ w, localHeightFloor p ≤ (x w).2 := fun w =>
    (localPsi_height_at_one p x hψ w).le
  rw [term_eq_rowScalar_regularized Γ σ s q x hpos
    (localHeightFloor p) (localHeightFloor_pos p) hdelta]
  simp [cutoffFamily, hψ]

private theorem localTerm_eventually_eq_weighted
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (σ : SL(2,F)) (s : ℂ)
    (p : PosCoord (F := F)) (x : ArtinPrimitiveRoots.A1.Spec.Coord F)
    (hx : x ∈ Metric.ball p.1 (localCutoff p).bump.rIn)
    (q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ) :
    (fun y => ArtinPrimitiveRoots.A1.Spec.eisTerm F Γ σ s
      (ArtinPrimitiveRoots.A1.Spec.ptX F y) q) =ᶠ[𝓝 x]
      (fun y => rowScalar Γ σ s q * cutoffFamily s (localHeightFloor p) (localPsi p)
        (normalizedRows Γ σ q) y) := by
  filter_upwards [localPsi_eq_one_eventually p hx] with y hψ
  exact localTerm_eq_weighted Γ σ s p y hψ q

private theorem eisSeries_local_eventually_eq
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (σ : SL(2,F)) (s : ℂ)
    (p : PosCoord (F := F)) :
    (fun x => ArtinPrimitiveRoots.A1.Spec.eisSeries F Γ σ s
      (ArtinPrimitiveRoots.A1.Spec.ptX F x)) =ᶠ[𝓝 p.1] localizedSeries Γ σ s p := by
  have hx : p.1 ∈ Metric.ball p.1 (localCutoff p).bump.rIn :=
    Metric.mem_ball_self (localCutoff p).bump.rIn_pos
  filter_upwards [localPsi_eq_one_eventually p hx] with x hψ
  have hpos : x ∈ ArtinPrimitiveRoots.A1.Spec.posSet F := by
    intro w
    exact lt_trans (localHeightFloor_pos p) (localPsi_height_at_one p x hψ w)
  have hdelta : ∀ w, localHeightFloor p ≤ (x w).2 := fun w =>
    (localPsi_height_at_one p x hψ w).le
  change (∑' q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ,
      ArtinPrimitiveRoots.A1.Spec.eisTerm F Γ σ s
        (ArtinPrimitiveRoots.A1.Spec.ptX F x) q) =
    (∑' q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ,
      rowScalar Γ σ s q * cutoffFamily s (localHeightFloor p) (localPsi p)
        (normalizedRows Γ σ q) x)
  apply tsum_congr
  intro q
  exact localTerm_eq_weighted Γ σ s p x hψ q

private theorem eisSeries_contDiffAt
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (σ : SL(2,F)) (s : ℂ)
    (hs : 1 / 2 < s.re) (p : PosCoord (F := F)) :
    ContDiffAt ℝ ∞
      (fun x => ArtinPrimitiveRoots.A1.Spec.eisSeries F Γ σ s
        (ArtinPrimitiveRoots.A1.Spec.ptX F x)) p.1 := by
  exact (localizedSeries_contDiff Γ σ s hs p).contDiffAt.congr_of_eventuallyEq
    (eisSeries_local_eventually_eq Γ σ s p)

private theorem localTermDerivativeBound
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (σ : SL(2,F)) (s : ℂ)
    (hs : 1 / 2 < s.re) (p : PosCoord (F := F)) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ,
      ∀ x : ArtinPrimitiveRoots.A1.Spec.Coord F,
        x ∈ Metric.ball p.1 (localCutoff p).bump.rIn →
        ‖iteratedFDeriv ℝ n
          (fun y => ArtinPrimitiveRoots.A1.Spec.eisTerm F Γ σ s
            (ArtinPrimitiveRoots.A1.Spec.ptX F y) q) x‖ ≤ C * ‖rowScalar Γ σ s q‖ := by
  obtain ⟨C, hC, hbound⟩ := localizedDerivativeConstant Γ σ s hs p n
  refine ⟨C, hC, ?_⟩
  intro q x hx
  have hEq := localTerm_eventually_eq_weighted Γ σ s p x hx q
  have hDerEq := hEq.iteratedFDeriv ℝ n
  rw [hDerEq.eq_of_nhds]
  exact hbound q x

private theorem eisSeries_isSmooth
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (σ : SL(2,F)) (s : ℂ)
    (hs : 1 / 2 < s.re) :
    ArtinPrimitiveRoots.A1.Spec.IsSmoothX F (ArtinPrimitiveRoots.A1.Spec.eisSeries F Γ σ s) := by
  change ContDiffOn ℝ ∞
    (fun p => ArtinPrimitiveRoots.A1.Spec.eisSeries F Γ σ s
      (ArtinPrimitiveRoots.A1.Spec.ptX F p)) (ArtinPrimitiveRoots.A1.Spec.posSet F)
  intro p hp
  exact (eisSeries_contDiffAt Γ σ s hs ⟨p,hp⟩).contDiffWithinAt

private theorem rowScalar_finset_summable
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (σ : SL(2,F)) (s : ℂ)
    (hs : 1 / 2 < s.re) (t : Finset (PosCoord (F := F))) (C : PosCoord (F := F) → ℝ) :
    Summable (fun q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ =>
      t.sum (fun p => C p * ‖rowScalar Γ σ s q‖)) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert p t hp ih =>
      simpa [Finset.sum_insert, hp] using
        ((rowScalar_summable Γ σ s hs).mul_left (C p)).add ih

private theorem eisTerm_derivative_majorant
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (σ : SL(2,F)) (s : ℂ)
    (hs : 1 / 2 < s.re) (K : Set (ArtinPrimitiveRoots.A1.Spec.Coord F))
    (hK : IsCompact K) (hKpos : K ⊆ ArtinPrimitiveRoots.A1.Spec.posSet F)
    (n : ℕ) (v : Fin n → ArtinPrimitiveRoots.A1.Spec.Coord F) :
    ∃ m : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ → ℝ, Summable m ∧
      ∀ q p, p ∈ K →
        ‖iteratedFDeriv ℝ n
          (fun p => ArtinPrimitiveRoots.A1.Spec.eisTerm F Γ σ s
            (ArtinPrimitiveRoots.A1.Spec.ptX F p) q) p v‖ ≤ m q := by
  classical
  by_cases hKempty : K = ∅
  · subst K
    refine ⟨fun _ => 0, summable_zero, ?_⟩
    intro q p hp
    simpa using hp
  let U : PosCoord (F := F) → Set (ArtinPrimitiveRoots.A1.Spec.Coord F) := fun p =>
    Metric.ball p.1 (localCutoff p).bump.rIn
  have hUopen (p : PosCoord (F := F)) : IsOpen (U p) := Metric.isOpen_ball
  have hcover : K ⊆ ⋃ p : PosCoord (F := F), U p := by
    intro x hx
    let p : PosCoord (F := F) := ⟨x, hKpos hx⟩
    refine Set.mem_iUnion.2 ⟨p, ?_⟩
    exact Metric.mem_ball_self (localCutoff p).bump.rIn_pos
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hUopen hcover
  have hchoose : ∀ p : PosCoord (F := F), ∃ C : ℝ, 0 ≤ C ∧
      ∀ q x, x ∈ U p →
        ‖iteratedFDeriv ℝ n
          (fun y => ArtinPrimitiveRoots.A1.Spec.eisTerm F Γ σ s
            (ArtinPrimitiveRoots.A1.Spec.ptX F y) q) x‖ ≤ C * ‖rowScalar Γ σ s q‖ := by
    intro p
    exact localTermDerivativeBound Γ σ s hs p n
  choose C hC hBound using hchoose
  let V : ℝ := ∏ i : Fin n, ‖v i‖
  let m : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ → ℝ := fun q =>
    V * t.sum (fun p => C p * ‖rowScalar Γ σ s q‖)
  have hV : 0 ≤ V := by
    dsimp [V]
    exact Finset.prod_nonneg fun i hi => norm_nonneg _
  have hsum := rowScalar_finset_summable Γ σ s hs t C
  refine ⟨m, ?_, ?_⟩
  · simpa [m] using hsum.mul_left V
  · intro q x hxK
    rcases Set.mem_iUnion₂.1 (ht hxK) with ⟨p, hpt, hxU⟩
    let D : ContinuousMultilinearMap ℝ (fun _ : Fin n => ArtinPrimitiveRoots.A1.Spec.Coord F) ℂ :=
      iteratedFDeriv ℝ n
        (fun y => ArtinPrimitiveRoots.A1.Spec.eisTerm F Γ σ s
          (ArtinPrimitiveRoots.A1.Spec.ptX F y) q) x
    have hD := hBound p q x hxU
    have hEval : ‖D v‖ ≤ ‖D‖ * V := by
      simpa [D, V] using D.le_opNorm v
    have hterm : C p * ‖rowScalar Γ σ s q‖ ≤
        t.sum (fun p' => C p' * ‖rowScalar Γ σ s q‖) := by
      simpa using (Finset.single_le_sum
        (f := fun p' : PosCoord (F := F) => C p' * ‖rowScalar Γ σ s q‖)
        (s := t) (fun p' hp' => mul_nonneg (hC p') (norm_nonneg _)) hpt)
    calc
      ‖iteratedFDeriv ℝ n
          (fun y => ArtinPrimitiveRoots.A1.Spec.eisTerm F Γ σ s
            (ArtinPrimitiveRoots.A1.Spec.ptX F y) q) x v‖ ≤ ‖D‖ * V := hEval
      _ ≤ (C p * ‖rowScalar Γ σ s q‖) * V :=
        mul_le_mul_of_nonneg_right hD hV
      _ = V * (C p * ‖rowScalar Γ σ s q‖) := by ring
      _ ≤ V * t.sum (fun p' => C p' * ‖rowScalar Γ σ s q‖) :=
        mul_le_mul_of_nonneg_left hterm hV
      _ = m q := by rfl

private theorem posSet_isOpen : IsOpen (ArtinPrimitiveRoots.A1.Spec.posSet F) := by
  rw [ArtinPrimitiveRoots.A1.Spec.posSet, Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun w => by
    exact isOpen_lt continuous_const
      (continuous_snd.comp (continuous_apply w))

private def coordY (w : InfinitePlace F) (p : ArtinPrimitiveRoots.A1.Spec.Coord F) : ℝ :=
  (p w).2

private def coordYCLM (w : InfinitePlace F) :
    ArtinPrimitiveRoots.A1.Spec.Coord F →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℂ ℝ).comp
    (ContinuousLinearMap.proj (R := ℝ) (ι := InfinitePlace F) w)

private theorem coordY_smooth (w : InfinitePlace F) :
    ContDiff ℝ ∞ (coordY (F := F) w) := by
  fun_prop [coordY]

private theorem coordY_deriv (v w : InfinitePlace F) (j : Fin 3)
    (p : ArtinPrimitiveRoots.A1.Spec.Coord F) :
    fderiv ℝ (coordY (F := F) v) p
      (ArtinPrimitiveRoots.A1.Spec.placeDirection F w j) =
      if v = w ∧ j = 2 then 1 else 0 := by
  have hlin : coordY (F := F) v = coordYCLM (F := F) v := by rfl
  rw [hlin, (coordYCLM (F := F) v).hasFDerivAt.fderiv]
  fin_cases j <;> by_cases hvw : v = w <;>
    simp [coordYCLM, ArtinPrimitiveRoots.A1.Spec.placeDirection, Pi.single,
      Function.update, hvw, eq_comm]

private def coordHeightProduct (t : Finset (InfinitePlace F))
    (p : ArtinPrimitiveRoots.A1.Spec.Coord F) : ℝ :=
  ∏ w ∈ t, coordY (F := F) w p

private theorem coordHeightProduct_smooth (t : Finset (InfinitePlace F)) :
    ContDiff ℝ ∞ (coordHeightProduct (F := F) t) := by
  unfold coordHeightProduct
  exact contDiff_prod (fun w hw => coordY_smooth w)

private def coordHessian (f : ArtinPrimitiveRoots.A1.Spec.Coord F → ℝ)
    (p v w : ArtinPrimitiveRoots.A1.Spec.Coord F) : ℝ :=
  (fderiv ℝ (fun y => fderiv ℝ f y) p v) w

private theorem coordHessian_eq_iteratedFDeriv
    (f : ArtinPrimitiveRoots.A1.Spec.Coord F → ℝ) (p v w : ArtinPrimitiveRoots.A1.Spec.Coord F) :
    coordHessian (F := F) f p v w = iteratedFDeriv ℝ 2 f p ![v,w] := by
  rw [coordHessian, iteratedFDeriv_succ_apply_right, iteratedFDeriv_one_apply]
  rw [show Fin.init ![v,w] 0 = v from rfl]
  rw [show ![v,w] (Fin.last 1) = w from rfl]

private theorem coordHessian_mul {f g : ArtinPrimitiveRoots.A1.Spec.Coord F → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (p v w : ArtinPrimitiveRoots.A1.Spec.Coord F) :
    coordHessian (F := F) (fun x => f x * g x) p v w =
      f p * coordHessian (F := F) g p v w +
        g p * coordHessian (F := F) f p v w +
        fderiv ℝ f p v * fderiv ℝ g p w +
        fderiv ℝ g p v * fderiv ℝ f p w := by
  have hf' (x : ArtinPrimitiveRoots.A1.Spec.Coord F) :=
    (hf.differentiable (by simp) x).hasFDerivAt
  have hg' (x : ArtinPrimitiveRoots.A1.Spec.Coord F) :=
    (hg.differentiable (by simp) x).hasFDerivAt
  have hG : (fun y => fderiv ℝ (fun z => f z * g z) y) =
      (fun y => f y • fderiv ℝ g y + g y • fderiv ℝ f y) := by
    funext y
    exact ((hf' y).mul (hg' y)).fderiv
  have hfd : Differentiable ℝ (fun y => fderiv ℝ f y) :=
    (hf.fderiv_right (m := (∞ : ℕ∞ω)) (by simp)).differentiable (by simp)
  have hgd : Differentiable ℝ (fun y => fderiv ℝ g y) :=
    (hg.fderiv_right (m := (∞ : ℕ∞ω)) (by simp)).differentiable (by simp)
  have hd := ((hf' p).smul (hgd p).hasFDerivAt).add
    ((hg' p).smul (hfd p).hasFDerivAt)
  unfold coordHessian
  change ((fderiv ℝ (fun y => fderiv ℝ (fun z => f z * g z) y) p) v) w = _
  rw [hG]
  change ((fderiv ℝ ((f • fun y => fderiv ℝ g y) +
    g • fun y => fderiv ℝ f y) p) v) w = _
  rw [hd.fderiv]
  simp only [_root_.add_apply, _root_.smul_apply, ContinuousLinearMap.smulRight_apply,
    smul_eq_mul]
  ring_nf

private theorem coordY_hessian (v w : InfinitePlace F) (j : Fin 3)
    (p : ArtinPrimitiveRoots.A1.Spec.Coord F) :
    coordHessian (F := F) (coordY (F := F) v) p
      (ArtinPrimitiveRoots.A1.Spec.placeDirection F w j)
      (ArtinPrimitiveRoots.A1.Spec.placeDirection F w j) = 0 := by
  have hder (x : ArtinPrimitiveRoots.A1.Spec.Coord F) :
      fderiv ℝ (coordY (F := F) v) x = coordYCLM (F := F) v := by
    exact (coordYCLM (F := F) v).hasFDerivAt.fderiv
  unfold coordHessian
  change (fderiv ℝ (fun x => fderiv ℝ (coordY (F := F) v) x) p)
      (ArtinPrimitiveRoots.A1.Spec.placeDirection F w j)
      (ArtinPrimitiveRoots.A1.Spec.placeDirection F w j) = 0
  rw [show (fun x => fderiv ℝ (coordY (F := F) v) x) =
      fun _ => coordYCLM (F := F) v from funext hder]
  simp

private theorem coordHeightProduct_fderiv (t : Finset (InfinitePlace F))
    (w : InfinitePlace F) (j : Fin 3) (p : ArtinPrimitiveRoots.A1.Spec.Coord F) :
    fderiv ℝ (coordHeightProduct (F := F) t) p
      (ArtinPrimitiveRoots.A1.Spec.placeDirection F w j) =
      if j = 2 ∧ w ∈ t then
        ∏ v ∈ t.erase w, coordY (F := F) v p else 0 := by
  classical
  have hformula : fderiv ℝ (coordHeightProduct (F := F) t) p =
      ∑ v ∈ t, (∏ q ∈ t.erase v, coordY (F := F) q p) •
        fderiv ℝ (coordY (F := F) v) p := by
    unfold coordHeightProduct
    exact fderiv_finsetProd (fun v hv =>
      (coordY_smooth (F := F) v).differentiable (by simp) p)
  rw [hformula]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  simp_rw [coordY_deriv]
  by_cases hj : j = 2 <;> by_cases hw : w ∈ t <;> simp [hj, hw]

private theorem coordHeightProduct_hessian (t : Finset (InfinitePlace F))
    (w : InfinitePlace F) (j : Fin 3) (p : ArtinPrimitiveRoots.A1.Spec.Coord F) :
    coordHessian (F := F) (coordHeightProduct (F := F) t) p
      (ArtinPrimitiveRoots.A1.Spec.placeDirection F w j)
      (ArtinPrimitiveRoots.A1.Spec.placeDirection F w j) = 0 := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      change (fderiv ℝ (fun y => fderiv ℝ (fun _ : ArtinPrimitiveRoots.A1.Spec.Coord F =>
        (1 : ℝ)) y) p (ArtinPrimitiveRoots.A1.Spec.placeDirection F w j))
        (ArtinPrimitiveRoots.A1.Spec.placeDirection F w j) = 0
      simp [coordHessian]
  | @insert i t hit ih =>
      have hprod : coordHeightProduct (F := F) (insert i t) = fun p =>
          coordY (F := F) i p * coordHeightProduct (F := F) t p := by
        funext p
        simp [coordHeightProduct, hit]
      rw [hprod, coordHessian_mul (coordY_smooth (F := F) i)
        (coordHeightProduct_smooth (F := F) t)]
      rw [ih, coordY_hessian]
      rw [coordHeightProduct_fderiv]
      rw [coordY_deriv]
      by_cases hiw : i = w
      · have hws : w ∉ t := by simpa [hiw] using hit
        simp [hiw, hws]
      · simp [hiw]

private theorem coordHessian_scalar_comp {f : ArtinPrimitiveRoots.A1.Spec.Coord F → ℝ}
    {g g' g'' : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ∀ t, HasDerivAt g (g' t) t) (hg' : ∀ t, HasDerivAt g' (g'' t) t)
    (p v w : ArtinPrimitiveRoots.A1.Spec.Coord F) :
    coordHessian (F := F) (g ∘ f) p v w =
      g'' (f p) * fderiv ℝ f p v * fderiv ℝ f p w +
        g' (f p) * coordHessian (F := F) f p v w := by
  have hf' (x : ArtinPrimitiveRoots.A1.Spec.Coord F) :=
    (hf.differentiable (by simp) x).hasFDerivAt
  have hG : (fun y => fderiv ℝ (g ∘ f) y) =
      (fun y => g' (f y) • fderiv ℝ f y) := by
    funext y
    exact ((hg (f y)).comp_hasFDerivAt y (hf' y)).fderiv
  have hfd : Differentiable ℝ (fun y => fderiv ℝ f y) :=
    (hf.fderiv_right (m := (∞ : ℕ∞ω)) (by simp)).differentiable (by simp)
  have hd := ((hg' (f p)).comp_hasFDerivAt p (hf' p)).smul
    (hfd p).hasFDerivAt
  unfold coordHessian
  change ((fderiv ℝ (fun y => fderiv ℝ (g ∘ f) y) p) v) w = _
  rw [hG]
  change ((fderiv ℝ ((g' ∘ f) • fun y => fderiv ℝ f y) p) v) w = _
  rw [hd.fderiv]
  simp only [_root_.add_apply, ContinuousLinearMap.smulRight_apply,
    _root_.smul_apply, smul_eq_mul]
  rw [show (g' ∘ f) p = g' (f p) by rfl]
  rw [mul_comm (g' (f p))
    ((fderiv ℝ (fun y => fderiv ℝ f y) p v) w)]
  ac_rfl

private theorem coordFDeriv_realCompAt {u : ArtinPrimitiveRoots.A1.Spec.Coord F → ℝ}
    {ψ ψ' : ℝ → ℝ} (p v : ArtinPrimitiveRoots.A1.Spec.Coord F)
    (hu : DifferentiableAt ℝ u p) (hψ : ∀ t, HasDerivAt ψ (ψ' t) t) :
    fderiv ℝ (ψ ∘ u) p v = ψ' (u p) * fderiv ℝ u p v := by
  have hcomp := (hψ (u p)).hasFDerivAt.comp p hu.hasFDerivAt
  rw [hcomp.fderiv]
  simp [ContinuousLinearMap.comp_apply]
  ring

private theorem coordNormHeight_ptX (p : ArtinPrimitiveRoots.A1.Spec.Coord F)
    (hp : p ∈ ArtinPrimitiveRoots.A1.Spec.posSet F) :
    ArtinPrimitiveRoots.A1.Spec.normHeight F (ArtinPrimitiveRoots.A1.Spec.ptX F p) =
      coordHeightProduct (F := F) Finset.univ p := by
  unfold ArtinPrimitiveRoots.A1.Spec.normHeight coordHeightProduct coordY
  simp only [ArtinPrimitiveRoots.A1.Spec.ptX, ArtinPrimitiveRoots.A1.Spec.height]
  congr 1
  funext w
  exact (ArtinPrimitiveRoots.A1.Spec.G1_h3_basics (F := F)).1
    (p w).1 (p w).2 (hp w)

private theorem coordFDeriv_ofReal {u : ArtinPrimitiveRoots.A1.Spec.Coord F → ℝ}
    (p v : ArtinPrimitiveRoots.A1.Spec.Coord F) (hu : DifferentiableAt ℝ u p) :
    fderiv ℝ (fun q => (u q : ℂ)) p v = (fderiv ℝ u p v : ℂ) := by
  have h := Complex.ofRealCLM.hasFDerivAt.comp p hu.hasFDerivAt
  change (fderiv ℝ (Complex.ofRealCLM ∘ u) p) v = _
  rw [h.fderiv]
  simp [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]

private theorem coordIteratedFDeriv_ofReal
    {u : ArtinPrimitiveRoots.A1.Spec.Coord F → ℝ}
    (p v w : ArtinPrimitiveRoots.A1.Spec.Coord F) (hu : ContDiff ℝ ∞ u) :
    iteratedFDeriv ℝ 2 (fun q => (u q : ℂ)) p ![v,w] =
      (iteratedFDeriv ℝ 2 u p ![v,w] : ℂ) := by
  have h := (Complex.ofRealCLM).iteratedFDeriv_comp_left
    (f := u) (x := p) hu.contDiffAt (by norm_num : 2 ≤ (∞ : ℕ∞ω))
  have happ := congrArg (fun D => D ![v,w]) h
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply] at happ
  have hfun : (fun q => (u q : ℂ)) = Complex.ofRealCLM ∘ u := rfl
  rw [hfun]
  exact happ

private theorem partialLap_realChart (u : ArtinPrimitiveRoots.A1.Spec.Coord F → ℝ)
    (hu : ContDiff ℝ ∞ u) (p : ArtinPrimitiveRoots.A1.Spec.Coord F)
    (hp : p ∈ ArtinPrimitiveRoots.A1.Spec.posSet F) (w : InfinitePlace F) :
    ArtinPrimitiveRoots.A1.Spec.partialLap F w
      (fun z => (u (ArtinPrimitiveRoots.A1.Spec.coordsX F z) : ℂ))
      (ArtinPrimitiveRoots.A1.Spec.ptX F p) =
      ((p w).2 : ℂ) * (fderiv ℝ u p (ArtinPrimitiveRoots.A1.Spec.placeDirection F w 2) : ℂ) -
        ((p w).2 : ℂ) ^ 2 *
          ((coordHessian (F := F) u p
              (ArtinPrimitiveRoots.A1.Spec.placeDirection F w 0)
              (ArtinPrimitiveRoots.A1.Spec.placeDirection F w 0) : ℂ) +
            (coordHessian (F := F) u p
              (ArtinPrimitiveRoots.A1.Spec.placeDirection F w 1)
              (ArtinPrimitiveRoots.A1.Spec.placeDirection F w 1) : ℂ) +
            (coordHessian (F := F) u p
              (ArtinPrimitiveRoots.A1.Spec.placeDirection F w 2)
              (ArtinPrimitiveRoots.A1.Spec.placeDirection F w 2) : ℂ)) := by
  classical
  have hcoords : ArtinPrimitiveRoots.A1.Spec.coordsX F
      (ArtinPrimitiveRoots.A1.Spec.ptX F p) = p := by
    rcases ArtinPrimitiveRoots.A1.Spec.G1_h3_basics (F := F) with
      ⟨_, _, _, _, _, _, hcoords, _, _, _, _, _⟩
    exact hcoords p hp
  have hEq : (fun q : ArtinPrimitiveRoots.A1.Spec.Coord F =>
      ((u (ArtinPrimitiveRoots.A1.Spec.coordsX F
        (ArtinPrimitiveRoots.A1.Spec.ptX F q)) : ℝ) : ℂ)) =ᶠ[𝓝 p]
      (fun q => (u q : ℂ)) := by
    filter_upwards [(posSet_isOpen (F := F)).mem_nhds hp] with q hq
    rw [(show ArtinPrimitiveRoots.A1.Spec.coordsX F
        (ArtinPrimitiveRoots.A1.Spec.ptX F q) = q from by
          rcases ArtinPrimitiveRoots.A1.Spec.G1_h3_basics (F := F) with
            ⟨_, _, _, _, _, _, hcoords, _, _, _, _, _⟩
          exact hcoords q hq)]
  have h1 := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hEq
  have h2 := (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hEq 2).self_of_nhds
  dsimp [ArtinPrimitiveRoots.A1.Spec.partialLap]
  simp only [Function.comp_def]
  rw [hcoords]
  simp only [ArtinPrimitiveRoots.A1.Spec.placeDirection]
  rw [h1]
  rw [coordFDeriv_ofReal _ _ ((hu.differentiable (by simp) p))]
  rw [h2]
  rw [coordIteratedFDeriv_ofReal p (Pi.single w (1,0)) (Pi.single w (1,0)) hu,
    coordIteratedFDeriv_ofReal p (Pi.single w (Complex.I,0)) (Pi.single w (Complex.I,0)) hu,
    coordIteratedFDeriv_ofReal p (Pi.single w (0,1)) (Pi.single w (0,1)) hu]
  rw [← coordHessian_eq_iteratedFDeriv, ← coordHessian_eq_iteratedFDeriv,
    ← coordHessian_eq_iteratedFDeriv]

private theorem partialLap_normHeight_realProfile (ψ : ℝ → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (p : ArtinPrimitiveRoots.A1.Spec.Coord F)
    (hp : p ∈ ArtinPrimitiveRoots.A1.Spec.posSet F) (w : InfinitePlace F) :
    ArtinPrimitiveRoots.A1.Spec.partialLap F w
      (fun z => (ψ (ArtinPrimitiveRoots.A1.Spec.normHeight F z) : ℂ))
      (ArtinPrimitiveRoots.A1.Spec.ptX F p) =
      (((coordHeightProduct (F := F) Finset.univ p * deriv ψ
            (coordHeightProduct (F := F) Finset.univ p) -
          (coordHeightProduct (F := F) Finset.univ p) ^ 2 *
            deriv (deriv ψ) (coordHeightProduct (F := F) Finset.univ p) : ℝ) : ℂ)) := by
  classical
  let H : ArtinPrimitiveRoots.A1.Spec.Coord F → ℝ :=
    coordHeightProduct (F := F) Finset.univ
  let u : ArtinPrimitiveRoots.A1.Spec.Coord F → ℝ := ψ ∘ H
  have hH : H = coordHeightProduct (F := F) Finset.univ := by rfl
  have hHs : ContDiff ℝ ∞ H := by
    rw [hH]
    exact coordHeightProduct_smooth Finset.univ
  have hu : ContDiff ℝ ∞ u := hψ.comp hHs
  have hchart : (fun q : ArtinPrimitiveRoots.A1.Spec.Coord F =>
      ((ψ (ArtinPrimitiveRoots.A1.Spec.normHeight F
        (ArtinPrimitiveRoots.A1.Spec.ptX F q)) : ℝ) : ℂ)) =ᶠ[𝓝 p]
      (fun q => (u q : ℂ)) := by
    filter_upwards [(posSet_isOpen (F := F)).mem_nhds hp] with q hq
    rw [coordNormHeight_ptX q hq]
    rfl
  have h1 := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hchart
  have h2 := (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hchart 2).self_of_nhds
  have hψder : ContDiff ℝ ∞ (deriv ψ) := hψ.deriv'
  have hψHas (t : ℝ) : HasDerivAt ψ (deriv ψ t) t :=
    (hψ.differentiable (by simp) t).hasDerivAt
  have hψderHas (t : ℝ) : HasDerivAt (deriv ψ) (deriv (deriv ψ) t) t :=
    (hψder.differentiable (by simp) t).hasDerivAt
  have hHgrad (j : Fin 3) :
      fderiv ℝ H p (ArtinPrimitiveRoots.A1.Spec.placeDirection F w j) =
        if j = 2 then ∏ v ∈ Finset.univ.erase w, coordY (F := F) v p else 0 := by
    rw [hH]
    rw [coordHeightProduct_fderiv]
    by_cases hj : j = 2 <;> simp [hj]
  have hHhess (j : Fin 3) :
      coordHessian (F := F) H p (ArtinPrimitiveRoots.A1.Spec.placeDirection F w j)
        (ArtinPrimitiveRoots.A1.Spec.placeDirection F w j) = 0 := by
    rw [hH]
    exact coordHeightProduct_hessian Finset.univ w j p
  have hHderivErase :
      (p w).2 * (∏ v ∈ Finset.univ.erase w, coordY (F := F) v p) = H p := by
    rw [hH]
    change (p w).2 * (∏ v ∈ Finset.univ.erase w, coordY (F := F) v p) =
      ∏ v ∈ Finset.univ, coordY (F := F) v p
    exact Finset.mul_prod_erase Finset.univ (fun v => coordY (F := F) v p)
      (Finset.mem_univ w)
  have hUgrad (j : Fin 3) :
      fderiv ℝ u p (ArtinPrimitiveRoots.A1.Spec.placeDirection F w j) =
        deriv ψ (H p) * fderiv ℝ H p (ArtinPrimitiveRoots.A1.Spec.placeDirection F w j) := by
    exact coordFDeriv_realCompAt p (ArtinPrimitiveRoots.A1.Spec.placeDirection F w j)
      (hHs.differentiable (by simp) p) hψHas
  have hUhess (j : Fin 3) :
      coordHessian (F := F) u p (ArtinPrimitiveRoots.A1.Spec.placeDirection F w j)
        (ArtinPrimitiveRoots.A1.Spec.placeDirection F w j) =
        deriv (deriv ψ) (H p) *
          fderiv ℝ H p (ArtinPrimitiveRoots.A1.Spec.placeDirection F w j) *
            fderiv ℝ H p (ArtinPrimitiveRoots.A1.Spec.placeDirection F w j) +
        deriv ψ (H p) * coordHessian (F := F) H p
          (ArtinPrimitiveRoots.A1.Spec.placeDirection F w j)
          (ArtinPrimitiveRoots.A1.Spec.placeDirection F w j) := by
    simpa [u] using coordHessian_scalar_comp hHs hψHas hψderHas p
      (ArtinPrimitiveRoots.A1.Spec.placeDirection F w j)
      (ArtinPrimitiveRoots.A1.Spec.placeDirection F w j)
  have hreal : ArtinPrimitiveRoots.A1.Spec.partialLap F w
      (fun z => (u (ArtinPrimitiveRoots.A1.Spec.coordsX F z) : ℂ))
      (ArtinPrimitiveRoots.A1.Spec.ptX F p) =
      ((H p * deriv ψ (H p) - H p ^ 2 * deriv (deriv ψ) (H p) : ℝ) : ℂ) := by
    rw [partialLap_realChart u hu p hp w]
    rw [hUgrad 2]
    rw [hUhess 0, hUhess 1, hUhess 2]
    simp_rw [hHhess, hHgrad]
    push_cast
    have hprodC :
        (↑(p w).2 : ℂ) *
          (∏ i ∈ Finset.univ.erase w, (coordY (F := F) i p : ℂ)) = (H p : ℂ) := by
      exact_mod_cast hHderivErase
    have hfirst :
        (↑(p w).2 : ℂ) *
            (((deriv ψ (H p) : ℝ) : ℂ) *
              ∏ i ∈ Finset.univ.erase w, (coordY (F := F) i p : ℂ)) =
          (H p : ℂ) * ((deriv ψ (H p) : ℝ) : ℂ) := by
      calc
        _ = ((deriv ψ (H p) : ℝ) : ℂ) *
            ((↑(p w).2 : ℂ) *
              ∏ i ∈ Finset.univ.erase w, (coordY (F := F) i p : ℂ)) := by ring
        _ = _ := by rw [hprodC]; ring
    have hsecond :
        (↑(p w).2 : ℂ) ^ 2 *
            (((deriv (deriv ψ) (H p) : ℝ) : ℂ) *
              (∏ i ∈ Finset.univ.erase w, (coordY (F := F) i p : ℂ)) ^ 2) =
          (H p : ℂ) ^ 2 * ((deriv (deriv ψ) (H p) : ℝ) : ℂ) := by
      calc
        _ = ((deriv (deriv ψ) (H p) : ℝ) : ℂ) *
            ((↑(p w).2 : ℂ) *
              ∏ i ∈ Finset.univ.erase w, (coordY (F := F) i p : ℂ)) ^ 2 := by ring
        _ = _ := by rw [hprodC]; ring
    ring_nf
    linear_combination hfirst - hsecond
  have hfun : (fun z => (ψ (ArtinPrimitiveRoots.A1.Spec.normHeight F z) : ℂ)) =
      (fun z => (u (ArtinPrimitiveRoots.A1.Spec.coordsX F z) : ℂ)) := by
    funext z
    simp [u, H, coordHeightProduct, coordY,
      ArtinPrimitiveRoots.A1.Spec.normHeight, ArtinPrimitiveRoots.A1.Spec.coordsX]
  rw [hfun]
  simpa [H, u] using hreal

private def coordinateLap (u : ArtinPrimitiveRoots.A1.Spec.Coord F → ℂ)
    (p : ArtinPrimitiveRoots.A1.Spec.Coord F) (w : InfinitePlace F) : ℂ :=
  (p w).2 • fderiv ℝ u p (ArtinPrimitiveRoots.A1.Spec.placeDirection F w 2) -
    (p w).2 ^ 2 •
      (iteratedFDeriv ℝ 2 u p ![ArtinPrimitiveRoots.A1.Spec.placeDirection F w 0,
        ArtinPrimitiveRoots.A1.Spec.placeDirection F w 0] +
       iteratedFDeriv ℝ 2 u p ![ArtinPrimitiveRoots.A1.Spec.placeDirection F w 1,
        ArtinPrimitiveRoots.A1.Spec.placeDirection F w 1] +
       iteratedFDeriv ℝ 2 u p ![ArtinPrimitiveRoots.A1.Spec.placeDirection F w 2,
        ArtinPrimitiveRoots.A1.Spec.placeDirection F w 2])

private theorem partialLap_from_chart
    (f : ArtinPrimitiveRoots.A1.Spec.X F → ℂ)
    (u : ArtinPrimitiveRoots.A1.Spec.Coord F → ℂ)
    (p : ArtinPrimitiveRoots.A1.Spec.Coord F) (hp : p ∈ ArtinPrimitiveRoots.A1.Spec.posSet F)
    (w : InfinitePlace F)
    (hEq : (fun q => f (ArtinPrimitiveRoots.A1.Spec.ptX F q)) =ᶠ[𝓝 p] u) :
    ArtinPrimitiveRoots.A1.Spec.partialLap F w f (ArtinPrimitiveRoots.A1.Spec.ptX F p) =
      coordinateLap u p w := by
  have hcoords : ArtinPrimitiveRoots.A1.Spec.coordsX F
      (ArtinPrimitiveRoots.A1.Spec.ptX F p) = p := by
    rcases ArtinPrimitiveRoots.A1.Spec.G1_h3_basics (F := F) with
      ⟨_, _, _, _, _, _, hcoords, _, _, _, _, _⟩
    exact hcoords p hp
  have h1 := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hEq
  have h2 := (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hEq 2).self_of_nhds
  unfold ArtinPrimitiveRoots.A1.Spec.partialLap coordinateLap
  simp only [Function.comp_def]
  rw [hcoords, h1, h2]
  simp only [ArtinPrimitiveRoots.A1.Spec.placeDirection]
  simp only [RCLike.real_smul_eq_coe_mul, RCLike.ofReal_pow]
  rfl

private theorem coordinateLap_add
    (u v : ArtinPrimitiveRoots.A1.Spec.Coord F → ℂ)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (p : ArtinPrimitiveRoots.A1.Spec.Coord F) (w : InfinitePlace F) :
    coordinateLap (u + v) p w = coordinateLap u p w + coordinateLap v p w := by
  have hu1 := hu.contDiffAt (x := p)
  have hv1 := hv.contDiffAt (x := p)
  have hfd := fderiv_add
    ((hu1.of_le (by norm_num : (1 : ℕ∞ω) ≤ ∞)).differentiableAt (by norm_num))
    ((hv1.of_le (by norm_num : (1 : ℕ∞ω) ≤ ∞)).differentiableAt (by norm_num))
  have h2 := iteratedFDeriv_add_apply
    (hu1.of_le (by norm_num : (2 : ℕ∞ω) ≤ ∞))
    (hv1.of_le (by norm_num : (2 : ℕ∞ω) ≤ ∞))
  unfold coordinateLap
  rw [hfd, h2]
  simp only [ContinuousLinearMap.add_apply, smul_add]
  module

private theorem coordinateLap_clm (L : ℂ →L[ℝ] ℂ)
    (u : ArtinPrimitiveRoots.A1.Spec.Coord F → ℂ)
    (hu : ContDiff ℝ ∞ u) (p : ArtinPrimitiveRoots.A1.Spec.Coord F)
    (w : InfinitePlace F) :
    coordinateLap (L ∘ u) p w = L (coordinateLap u p w) := by
  have huAt := hu.contDiffAt (x := p)
  have hdiff := (huAt.of_le (by norm_num : (1 : ℕ∞ω) ≤ ∞)).differentiableAt (by norm_num)
  have hfd : fderiv ℝ (L ∘ u) p = L.comp (fderiv ℝ u p) := by
    have h := (L.hasFDerivAt.comp p hdiff.hasFDerivAt).fderiv
    simpa [Function.comp_def, ContinuousLinearMap.comp_apply] using h
  have h2 : iteratedFDeriv ℝ 2 (L ∘ u) p =
      L.compContinuousMultilinearMap (iteratedFDeriv ℝ 2 u p) :=
    L.iteratedFDeriv_comp_left huAt (by norm_num : 2 ≤ (∞ : ℕ∞ω))
  unfold coordinateLap
  rw [hfd, h2]
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply]
  calc
    _ = (p w).2 • L (fderiv ℝ u p (ArtinPrimitiveRoots.A1.Spec.placeDirection F w 2)) -
        (p w).2 ^ 2 • L (
          iteratedFDeriv ℝ 2 u p ![ArtinPrimitiveRoots.A1.Spec.placeDirection F w 0,
            ArtinPrimitiveRoots.A1.Spec.placeDirection F w 0] +
          iteratedFDeriv ℝ 2 u p ![ArtinPrimitiveRoots.A1.Spec.placeDirection F w 1,
            ArtinPrimitiveRoots.A1.Spec.placeDirection F w 1] +
          iteratedFDeriv ℝ 2 u p ![ArtinPrimitiveRoots.A1.Spec.placeDirection F w 2,
            ArtinPrimitiveRoots.A1.Spec.placeDirection F w 2]) := by
      rw [← map_add, ← map_add]
    _ = L ((p w).2 • fderiv ℝ u p (ArtinPrimitiveRoots.A1.Spec.placeDirection F w 2) -
        (p w).2 ^ 2 • (
          iteratedFDeriv ℝ 2 u p ![ArtinPrimitiveRoots.A1.Spec.placeDirection F w 0,
            ArtinPrimitiveRoots.A1.Spec.placeDirection F w 0] +
          iteratedFDeriv ℝ 2 u p ![ArtinPrimitiveRoots.A1.Spec.placeDirection F w 1,
            ArtinPrimitiveRoots.A1.Spec.placeDirection F w 1] +
          iteratedFDeriv ℝ 2 u p ![ArtinPrimitiveRoots.A1.Spec.placeDirection F w 2,
            ArtinPrimitiveRoots.A1.Spec.placeDirection F w 2])) := by
      rw [map_sub, map_smul, map_smul]

private def radialHeightLift (t : ℝ) : OAI.CubicEisenstein.SpatialCoordinates :=
  ![0, 0, t]

private theorem radialHeightLift_smooth :
    ContDiff ℝ ∞ radialHeightLift := by
  apply contDiff_pi.2
  intro i
  fin_cases i
  · exact contDiff_const
  · exact contDiff_const
  · exact contDiff_id

private def regularHeight (δ t : ℝ) : ℝ :=
  OAI.CubicEisenstein.regularSpatialHeight δ (radialHeightLift t)

private theorem regularHeight_smooth (δ : ℝ) :
    ContDiff ℝ ∞ (regularHeight δ) := by
  exact OAI.CubicEisenstein.regularSpatialHeight_contDiff δ |>.comp
    radialHeightLift_smooth

private theorem regularHeight_pos (δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    0 < regularHeight δ t :=
  OAI.CubicEisenstein.regularSpatialHeight_pos δ hδ (radialHeightLift t)

private theorem regularHeight_eq (δ : ℝ) (hδ : 0 < δ) (t : ℝ)
    (ht : δ ≤ t) : regularHeight δ t = t := by
  unfold regularHeight
  rw [OAI.CubicEisenstein.regularSpatialHeight_eq δ hδ (radialHeightLift t)]
  · rfl
  · simpa [radialHeightLift] using ht

private def complexPowerProfile (a : ℂ) (δ : ℝ) (t : ℝ) : ℂ :=
  Complex.exp (a * ((Real.log (regularHeight δ t) : ℝ) : ℂ))

private theorem complexPowerProfile_smooth (a : ℂ) (δ : ℝ) (hδ : 0 < δ) :
    ContDiff ℝ ∞ (complexPowerProfile a δ) := by
  have hH : ContDiff ℝ ∞ (regularHeight δ) := regularHeight_smooth δ
  have hlog : ContDiff ℝ ∞ (fun t => Real.log (regularHeight δ t)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro t
    exact (Real.contDiffAt_log.mpr (ne_of_gt (regularHeight_pos δ hδ t))).comp t
      hH.contDiffAt
  have hlogC : ContDiff ℝ ∞ (fun t =>
      ((Real.log (regularHeight δ t) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hlog
  have harg : ContDiff ℝ ∞ (fun t => a *
      ((Real.log (regularHeight δ t) : ℝ) : ℂ)) :=
    contDiff_const.mul hlogC
  change ContDiff ℝ ∞ (fun t => Complex.exp
    (a * ((Real.log (regularHeight δ t) : ℝ) : ℂ)))
  exact Complex.contDiff_exp.comp harg

private theorem complexPowerProfile_eq_cpow (a : ℂ) (δ : ℝ) (hδ : 0 < δ)
    (t : ℝ) (ht : δ ≤ t) :
    complexPowerProfile a δ t = ((t : ℝ) : ℂ) ^ a := by
  have htpos : 0 < t := lt_of_lt_of_le hδ ht
  rw [complexPowerProfile, regularHeight_eq δ hδ t ht,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr htpos.ne'),
    Complex.ofReal_log htpos.le]
  congr 1
  ring

private theorem complexPowerProfile_eq_eventually_cpow (a : ℂ) (δ : ℝ)
    (hδ : 0 < δ) (t : ℝ) (ht : δ < t) :
    complexPowerProfile a δ =ᶠ[𝓝 t] fun y => ((y : ℝ) : ℂ) ^ a := by
  filter_upwards [isOpen_Ioi.mem_nhds ht] with y hy
  exact complexPowerProfile_eq_cpow a δ hδ y (le_of_lt hy)

private theorem complexPowerProfile_deriv (a : ℂ) (δ : ℝ) (hδ : 0 < δ)
    (t : ℝ) (ht : δ < t) (ha : a ≠ 0) :
    deriv (complexPowerProfile a δ) t = a * (t : ℂ) ^ (a - 1) := by
  rw [(complexPowerProfile_eq_eventually_cpow a δ hδ t ht).deriv_eq]
  exact Complex.deriv_ofReal_cpow_const (ne_of_gt (lt_trans hδ ht)) ha

private theorem complexPowerProfile_deriv2 (a : ℂ) (δ : ℝ) (hδ : 0 < δ)
    (t : ℝ) (ht : δ < t) (ha : a ≠ 0) (ha1 : a - 1 ≠ 0) :
    deriv (deriv (complexPowerProfile a δ)) t =
      a * (a - 1) * (t : ℂ) ^ (a - 2) := by
  have hpowEq := complexPowerProfile_eq_eventually_cpow a δ hδ t ht
  have hderivCpow : deriv (fun y : ℝ => ((y : ℝ) : ℂ) ^ a) =ᶠ[𝓝 t]
      fun y => a * ((y : ℝ) : ℂ) ^ (a - 1) := by
    filter_upwards [isOpen_Ioi.mem_nhds (lt_trans hδ ht)] with y hy
    exact Complex.deriv_ofReal_cpow_const (ne_of_gt hy) ha
  have hEq1 := hpowEq.deriv
  calc
    deriv (deriv (complexPowerProfile a δ)) t =
        deriv (deriv (fun y : ℝ => ((y : ℝ) : ℂ) ^ a)) t := hEq1.deriv_eq
    _ = deriv (fun y : ℝ => a * ((y : ℝ) : ℂ) ^ (a - 1)) t := hderivCpow.deriv_eq
    _ = a * (a - 1) * (t : ℂ) ^ (a - 2) := by
      have hpow : HasDerivAt (fun y : ℝ => ((y : ℝ) : ℂ) ^ (a - 1))
          ((a - 1) * (t : ℂ) ^ (a - 2)) t :=
        by
          convert hasDerivAt_ofReal_cpow_const (ne_of_gt (lt_trans hδ ht)) ha1 using 1
          <;> ring_nf
      simpa [mul_assoc] using (hpow.const_mul a).deriv

private def iMulCLM : ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.mulLeftRight ℝ ℂ) Complex.I 1

private theorem iMulCLM_apply (z : ℂ) : iMulCLM z = Complex.I * z := by
  simp [iMulCLM, ContinuousLinearMap.mulLeftRight_apply]

private theorem deriv_re_eq (ψ : ℝ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (t : ℝ) :
    deriv (fun x => (ψ x).re) t = (deriv ψ t).re := by
  have hψAt : HasDerivAt ψ (deriv ψ t) t :=
    (hψ.differentiable (by simp) t).hasDerivAt
  have hcomp : fderiv ℝ (Complex.reCLM ∘ ψ) t =
      Complex.reCLM ∘SL ContinuousLinearMap.toSpanSingleton ℝ (deriv ψ t) :=
    (Complex.reCLM.hasFDerivAt.comp t hψAt.hasFDerivAt).fderiv
  change fderiv ℝ (Complex.reCLM ∘ ψ) t 1 = (fderiv ℝ ψ t 1).re
  rw [hcomp]
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, Complex.reCLM_apply,
    ContinuousLinearMap.one_apply, one_smul]
  rfl

private theorem deriv_im_eq (ψ : ℝ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (t : ℝ) :
    deriv (fun x => (ψ x).im) t = (deriv ψ t).im := by
  have hψAt : HasDerivAt ψ (deriv ψ t) t :=
    (hψ.differentiable (by simp) t).hasDerivAt
  have hcomp : fderiv ℝ (Complex.imCLM ∘ ψ) t =
      Complex.imCLM ∘SL ContinuousLinearMap.toSpanSingleton ℝ (deriv ψ t) :=
    (Complex.imCLM.hasFDerivAt.comp t hψAt.hasFDerivAt).fderiv
  change fderiv ℝ (Complex.imCLM ∘ ψ) t 1 = (fderiv ℝ ψ t 1).im
  rw [hcomp]
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, Complex.imCLM_apply,
    ContinuousLinearMap.one_apply, one_smul]
  rfl

private theorem partialLap_normHeight_complexProfile (ψ : ℝ → ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (p : ArtinPrimitiveRoots.A1.Spec.Coord F)
    (hp : p ∈ ArtinPrimitiveRoots.A1.Spec.posSet F) (w : InfinitePlace F) :
    ArtinPrimitiveRoots.A1.Spec.partialLap F w
      (fun z => ψ (ArtinPrimitiveRoots.A1.Spec.normHeight F z))
      (ArtinPrimitiveRoots.A1.Spec.ptX F p) =
      ((coordHeightProduct (F := F) Finset.univ p : ℝ) : ℂ) *
          deriv ψ (coordHeightProduct (F := F) Finset.univ p) -
        ((coordHeightProduct (F := F) Finset.univ p : ℝ) : ℂ) ^ 2 *
          deriv (deriv ψ) (coordHeightProduct (F := F) Finset.univ p) := by
  let H : ArtinPrimitiveRoots.A1.Spec.Coord F → ℝ :=
    coordHeightProduct (F := F) Finset.univ
  let ψRe : ℝ → ℝ := fun t => (ψ t).re
  let ψIm : ℝ → ℝ := fun t => (ψ t).im
  let uRe : ArtinPrimitiveRoots.A1.Spec.Coord F → ℂ := fun q =>
    ((ψRe (H q) : ℝ) : ℂ)
  let uIm : ArtinPrimitiveRoots.A1.Spec.Coord F → ℂ := fun q =>
    ((ψIm (H q) : ℝ) : ℂ)
  let uComplex : ArtinPrimitiveRoots.A1.Spec.Coord F → ℂ :=
    uRe + iMulCLM ∘ uIm
  have hH : ContDiff ℝ ∞ H := coordHeightProduct_smooth Finset.univ
  have hψRe : ContDiff ℝ ∞ ψRe :=
    Complex.reCLM.contDiff.comp hψ
  have hψIm : ContDiff ℝ ∞ ψIm :=
    Complex.imCLM.contDiff.comp hψ
  have hReReal : ContDiff ℝ ∞ (fun q => ψRe (H q)) := hψRe.comp hH
  have hImReal : ContDiff ℝ ∞ (fun q => ψIm (H q)) := hψIm.comp hH
  have hRe : ContDiff ℝ ∞ uRe :=
    Complex.ofRealCLM.contDiff.comp hReReal
  have hIm : ContDiff ℝ ∞ uIm :=
    Complex.ofRealCLM.contDiff.comp hImReal
  have hICLM : ContDiff ℝ ∞ (iMulCLM ∘ uIm) := iMulCLM.contDiff.comp hIm
  have hUC : ContDiff ℝ ∞ uComplex := hRe.add hICLM
  have hfun (q : ArtinPrimitiveRoots.A1.Spec.Coord F) : uComplex q = ψ (H q) := by
    apply Complex.ext
    · simp [uComplex, uRe, uIm, ψRe, ψIm, iMulCLM_apply]
    · simp [uComplex, uRe, uIm, ψRe, ψIm, iMulCLM_apply]
  have hNpt (q : ArtinPrimitiveRoots.A1.Spec.Coord F)
      (hq : q ∈ ArtinPrimitiveRoots.A1.Spec.posSet F) :
      ArtinPrimitiveRoots.A1.Spec.normHeight F
        (ArtinPrimitiveRoots.A1.Spec.ptX F q) = H q := by
    simpa [H] using coordNormHeight_ptX q hq
  have hchart :
      (fun q => ψ (ArtinPrimitiveRoots.A1.Spec.normHeight F
        (ArtinPrimitiveRoots.A1.Spec.ptX F q))) =ᶠ[𝓝 p] uComplex := by
    filter_upwards [(posSet_isOpen (F := F)).mem_nhds hp] with q hq
    rw [hNpt q hq]
    exact (hfun q).symm
  have hradial := partialLap_from_chart
    (fun z => ψ (ArtinPrimitiveRoots.A1.Spec.normHeight F z)) uComplex p hp w hchart
  have hRechart :
      (fun q => ((ψRe (ArtinPrimitiveRoots.A1.Spec.normHeight F
        (ArtinPrimitiveRoots.A1.Spec.ptX F q)) : ℝ) : ℂ)) =ᶠ[𝓝 p] uRe := by
    filter_upwards [(posSet_isOpen (F := F)).mem_nhds hp] with q hq
    rw [hNpt q hq]
  have hImchart :
      (fun q => ((ψIm (ArtinPrimitiveRoots.A1.Spec.normHeight F
        (ArtinPrimitiveRoots.A1.Spec.ptX F q)) : ℝ) : ℂ)) =ᶠ[𝓝 p] uIm := by
    filter_upwards [(posSet_isOpen (F := F)).mem_nhds hp] with q hq
    rw [hNpt q hq]
  have hReCoord : coordinateLap uRe p w =
      ((H p * deriv ψRe (H p) - H p ^ 2 * deriv (deriv ψRe) (H p) : ℝ) : ℂ) := by
    have h1 := partialLap_from_chart
      (fun z => ((ψRe (ArtinPrimitiveRoots.A1.Spec.normHeight F z) : ℝ) : ℂ)) uRe p hp w hRechart
    have h2 := partialLap_normHeight_realProfile ψRe hψRe p hp w
    exact h1.symm.trans h2
  have hImCoord : coordinateLap uIm p w =
      ((H p * deriv ψIm (H p) - H p ^ 2 * deriv (deriv ψIm) (H p) : ℝ) : ℂ) := by
    have h1 := partialLap_from_chart
      (fun z => ((ψIm (ArtinPrimitiveRoots.A1.Spec.normHeight F z) : ℝ) : ℂ)) uIm p hp w hImchart
    have h2 := partialLap_normHeight_realProfile ψIm hψIm p hp w
    exact h1.symm.trans h2
  have hLapSplit := coordinateLap_add uRe (iMulCLM ∘ uIm) hRe hICLM p w
  have hLapI := coordinateLap_clm iMulCLM uIm hIm p w
  have hLap : coordinateLap uComplex p w =
      ((H p * deriv ψRe (H p) - H p ^ 2 * deriv (deriv ψRe) (H p) : ℝ) : ℂ) +
        iMulCLM ((H p * deriv ψIm (H p) -
          H p ^ 2 * deriv (deriv ψIm) (H p) : ℝ) : ℂ) := by
    rw [hLapSplit, hLapI, hReCoord, hImCoord]
  have hderRe := deriv_re_eq ψ hψ (H p)
  have hderIm := deriv_im_eq ψ hψ (H p)
  have hderRe2 := deriv_re_eq (deriv ψ) (hψ.deriv') (H p)
  have hderIm2 := deriv_im_eq (deriv ψ) (hψ.deriv') (H p)
  have hReFun : deriv ψRe = fun x => (deriv ψ x).re := by
    funext x
    exact deriv_re_eq ψ hψ x
  have hImFun : deriv ψIm = fun x => (deriv ψ x).im := by
    funext x
    exact deriv_im_eq ψ hψ x
  have hderRe2' : deriv (deriv ψRe) (H p) = (deriv (deriv ψ) (H p)).re := by
    rw [hReFun]
    exact hderRe2
  have hderIm2' : deriv (deriv ψIm) (H p) = (deriv (deriv ψ) (H p)).im := by
    rw [hImFun]
    exact hderIm2
  have hderRe' : deriv ψRe (H p) = (deriv ψ (H p)).re := by
    simpa [ψRe] using hderRe
  have hderIm' : deriv ψIm (H p) = (deriv ψ (H p)).im := by
    simpa [ψIm] using hderIm
  have hpowRe : ((((H p : ℝ) : ℂ) ^ 2).re) = H p ^ 2 := by
    simp only [pow_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hpowIm : ((((H p : ℝ) : ℂ) ^ 2).im) = 0 := by
    simp only [pow_two, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hsplit :
      ((H p : ℝ) : ℂ) * deriv ψ (H p) - ((H p : ℝ) : ℂ) ^ 2 *
          deriv (deriv ψ) (H p) =
        ((H p * deriv ψRe (H p) - H p ^ 2 * deriv (deriv ψRe) (H p) : ℝ) : ℂ) +
          iMulCLM ((H p * deriv ψIm (H p) -
            H p ^ 2 * deriv (deriv ψIm) (H p) : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.sub_re, iMulCLM_apply, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      rw [hpowRe, hpowIm, hderRe', hderRe2']
      ring
    · simp only [Complex.add_im, Complex.sub_im, iMulCLM_apply,
        Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      rw [hpowRe, hpowIm, hderIm', hderIm2']
      ring
  have hHpoint : H p = coordHeightProduct (F := F) Finset.univ p := rfl
  calc
    ArtinPrimitiveRoots.A1.Spec.partialLap F w
        (fun z => ψ (ArtinPrimitiveRoots.A1.Spec.normHeight F z))
        (ArtinPrimitiveRoots.A1.Spec.ptX F p) = coordinateLap uComplex p w := hradial
    _ = ((H p * deriv ψRe (H p) -
          H p ^ 2 * deriv (deriv ψRe) (H p) : ℝ) : ℂ) +
        iMulCLM ((H p * deriv ψIm (H p) -
          H p ^ 2 * deriv (deriv ψIm) (H p) : ℝ) : ℂ) := hLap
    _ = _ := by
      rw [← hHpoint]
      exact hsplit.symm

private theorem normHeight_real_smooth :
    ArtinPrimitiveRoots.A1.Spec.IsSmoothRealX F
      (ArtinPrimitiveRoots.A1.Spec.normHeight F) := by
  change ContDiffOn ℝ ∞
    (fun p => ArtinPrimitiveRoots.A1.Spec.normHeight F
      (ArtinPrimitiveRoots.A1.Spec.ptX F p)) (ArtinPrimitiveRoots.A1.Spec.posSet F)
  exact (coordHeightProduct_smooth (F := F) Finset.univ).contDiffOn.congr
    (fun p hp => coordNormHeight_ptX p hp)

private theorem normHeight_complex_smooth :
    ArtinPrimitiveRoots.A1.Spec.IsSmoothX F
      (fun z => ((ArtinPrimitiveRoots.A1.Spec.normHeight F z : ℝ) : ℂ)) := by
  change ContDiffOn ℝ ∞
    (fun p => ((ArtinPrimitiveRoots.A1.Spec.normHeight F
      (ArtinPrimitiveRoots.A1.Spec.ptX F p) : ℝ) : ℂ))
    (ArtinPrimitiveRoots.A1.Spec.posSet F)
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn normHeight_real_smooth

private theorem complexProfile_normHeight_smooth (a : ℂ) (δ : ℝ) (hδ : 0 < δ) :
    ArtinPrimitiveRoots.A1.Spec.IsSmoothX F
      (fun z => complexPowerProfile a δ
        (ArtinPrimitiveRoots.A1.Spec.normHeight F z)) := by
  change ContDiffOn ℝ ∞
    (fun p => complexPowerProfile a δ
      (ArtinPrimitiveRoots.A1.Spec.normHeight F
        (ArtinPrimitiveRoots.A1.Spec.ptX F p)))
    (ArtinPrimitiveRoots.A1.Spec.posSet F)
  exact (complexPowerProfile_smooth a δ hδ).comp_contDiffOn
    normHeight_real_smooth

private theorem partialLap_normHeight_complexProfile_at (ψ : ℝ → ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (z : ArtinPrimitiveRoots.A1.Spec.X F)
    (w : InfinitePlace F) :
    ArtinPrimitiveRoots.A1.Spec.partialLap F w
      (fun x => ψ (ArtinPrimitiveRoots.A1.Spec.normHeight F x)) z =
      ((ArtinPrimitiveRoots.A1.Spec.normHeight F z : ℝ) : ℂ) *
          deriv ψ (ArtinPrimitiveRoots.A1.Spec.normHeight F z) -
        ((ArtinPrimitiveRoots.A1.Spec.normHeight F z : ℝ) : ℂ) ^ 2 *
          deriv (deriv ψ) (ArtinPrimitiveRoots.A1.Spec.normHeight F z) := by
  let p := ArtinPrimitiveRoots.A1.Spec.coordsX F z
  have hp : p ∈ ArtinPrimitiveRoots.A1.Spec.posSet F := by
    intro v
    change 0 < ArtinPrimitiveRoots.A1.Spec.height (z v)
    rw [ArtinPrimitiveRoots.A1.Spec.height_eq_hyperbolicHeight]
    exact OAI.CubicEisenstein.hyperbolicHeight_pos (z v)
  have hpt : ArtinPrimitiveRoots.A1.Spec.ptX F p = z := by
    rcases ArtinPrimitiveRoots.A1.Spec.G1_h3_basics (F := F) with
      ⟨_, _, _, _, _, _, _, hpt, _, _, _, _⟩
    exact hpt z
  have hN : ArtinPrimitiveRoots.A1.Spec.normHeight F z =
      coordHeightProduct (F := F) Finset.univ p := by
    rw [← hpt]
    exact coordNormHeight_ptX p hp
  calc
    _ = ArtinPrimitiveRoots.A1.Spec.partialLap F w
        (fun x => ψ (ArtinPrimitiveRoots.A1.Spec.normHeight F x))
        (ArtinPrimitiveRoots.A1.Spec.ptX F p) := by rw [hpt]
    _ = _ := by rw [partialLap_normHeight_complexProfile ψ hψ p hp w, ← hN]

private theorem partialLap_cpow_normHeight_action (b : SL(2,F)) (a : ℂ)
    (ha : 2 < a.re) (z : ArtinPrimitiveRoots.A1.Spec.X F)
    (w : InfinitePlace F) :
    ArtinPrimitiveRoots.A1.Spec.partialLap F w
      (fun x => ((ArtinPrimitiveRoots.A1.Spec.normHeight F (b • x) : ℝ) : ℂ) ^ a) z =
      a * (2 - a) *
        ((ArtinPrimitiveRoots.A1.Spec.normHeight F (b • z) : ℝ) : ℂ) ^ a := by
  let N : ℝ := ArtinPrimitiveRoots.A1.Spec.normHeight F (b • z)
  have hN : 0 < N := by
    dsimp [N, ArtinPrimitiveRoots.A1.Spec.normHeight]
    apply Finset.prod_pos
    intro v hv
    rw [ArtinPrimitiveRoots.A1.Spec.height_eq_hyperbolicHeight]
    exact OAI.CubicEisenstein.hyperbolicHeight_pos ((b • z) v)
  let δ : ℝ := N / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδN : δ < N := by dsimp [δ]; linarith
  have ha0 : a ≠ 0 := by
    intro h
    rw [h] at ha
    norm_num at ha
  have ha1 : a - 1 ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    linarith
  let p : ArtinPrimitiveRoots.A1.Spec.Coord F :=
    ArtinPrimitiveRoots.A1.Spec.coordsX F z
  have hp : p ∈ ArtinPrimitiveRoots.A1.Spec.posSet F := by
    intro v
    change 0 < ArtinPrimitiveRoots.A1.Spec.height (z v)
    rw [ArtinPrimitiveRoots.A1.Spec.height_eq_hyperbolicHeight]
    exact OAI.CubicEisenstein.hyperbolicHeight_pos (z v)
  have hpt : ArtinPrimitiveRoots.A1.Spec.ptX F p = z := by
    rcases ArtinPrimitiveRoots.A1.Spec.G1_h3_basics (F := F) with
      ⟨_, _, _, _, _, _, _, hpt, _, _, _, _⟩
    exact hpt z
  let T : ArtinPrimitiveRoots.A1.Spec.Coord F → ℝ := fun q =>
    ArtinPrimitiveRoots.A1.Spec.normHeight F (b • ArtinPrimitiveRoots.A1.Spec.ptX F q)
  let g : InfinitePlace F → SL(2,ℂ) := ArtinPrimitiveRoots.A1.Spec.toInf F b
  have hAct (x : ArtinPrimitiveRoots.A1.Spec.X F) :
      ArtinPrimitiveRoots.A1.Spec.actAtPlaces F g x = b • x := by
    funext v
    rfl
  have hTcomplex : ContDiffOn ℝ ∞ (fun q => ((T q : ℝ) : ℂ))
      (ArtinPrimitiveRoots.A1.Spec.posSet F) := by
    have h := ArtinPrimitiveRoots.A1.Spec.g5IsSmoothX_action
      g (fun x => ((ArtinPrimitiveRoots.A1.Spec.normHeight F x : ℝ) : ℂ))
      normHeight_complex_smooth
    change ContDiffOn ℝ ∞
      (fun q => ((ArtinPrimitiveRoots.A1.Spec.normHeight F
        (ArtinPrimitiveRoots.A1.Spec.actAtPlaces F g
          (ArtinPrimitiveRoots.A1.Spec.ptX F q)) : ℝ) : ℂ))
      (ArtinPrimitiveRoots.A1.Spec.posSet F) at h
    apply h.congr
    intro q hq
    simpa [T] using congrArg
      (fun x : ArtinPrimitiveRoots.A1.Spec.X F =>
        ((ArtinPrimitiveRoots.A1.Spec.normHeight F x : ℝ) : ℂ))
      (hAct (ArtinPrimitiveRoots.A1.Spec.ptX F q)).symm
  have hT : ContDiffOn ℝ ∞ T (ArtinPrimitiveRoots.A1.Spec.posSet F) := by
    have h := Complex.reCLM.contDiff.comp_contDiffOn hTcomplex
    change ContDiffOn ℝ ∞
      (fun q => Complex.reCLM ((T q : ℝ) : ℂ))
      (ArtinPrimitiveRoots.A1.Spec.posSet F) at h
    apply h.congr
    intro q hq
    simp [Complex.reCLM_apply]
  have hTval : T p = N := by
    dsimp [T, N, p]
    rw [hpt]
  have hTcontinuousAt : ContinuousAt T p :=
    hT.continuousOn.continuousAt (posSet_isOpen.mem_nhds hp)
  have hTabove : ∀ᶠ q in 𝓝 p, δ < T q := by
    exact hTcontinuousAt.eventually
      (isOpen_Ioi.mem_nhds (by rw [hTval]; exact hδN))
  have hprofileEq :
      (fun q => ((ArtinPrimitiveRoots.A1.Spec.normHeight F
        (b • ArtinPrimitiveRoots.A1.Spec.ptX F q) : ℝ) : ℂ) ^ a) =ᶠ[𝓝 p]
      (fun q => complexPowerProfile a δ (T q)) := by
    filter_upwards [hTabove] with q hq
    exact (complexPowerProfile_eq_cpow a δ hδ (T q) (le_of_lt hq)).symm
  have hprofileChart :
      (fun q => complexPowerProfile a δ
        (ArtinPrimitiveRoots.A1.Spec.normHeight F
          (b • ArtinPrimitiveRoots.A1.Spec.ptX F q))) =ᶠ[𝓝 p]
      (fun q => complexPowerProfile a δ (T q)) :=
    Filter.Eventually.of_forall fun q => rfl
  have htermLap := partialLap_from_chart
    (fun x => ((ArtinPrimitiveRoots.A1.Spec.normHeight F (b • x) : ℝ) : ℂ) ^ a)
    (fun q => complexPowerProfile a δ (T q)) p hp w hprofileEq
  have hprofileLap := partialLap_from_chart
    (fun x => complexPowerProfile a δ
      (ArtinPrimitiveRoots.A1.Spec.normHeight F (b • x)))
    (fun q => complexPowerProfile a δ (T q)) p hp w hprofileChart
  have htermEq :
      ArtinPrimitiveRoots.A1.Spec.partialLap F w
        (fun x => ((ArtinPrimitiveRoots.A1.Spec.normHeight F (b • x) : ℝ) : ℂ) ^ a) z =
      ArtinPrimitiveRoots.A1.Spec.partialLap F w
        (fun x => complexPowerProfile a δ
          (ArtinPrimitiveRoots.A1.Spec.normHeight F (b • x))) z := by
    calc
      _ = ArtinPrimitiveRoots.A1.Spec.partialLap F w
          (fun x => ((ArtinPrimitiveRoots.A1.Spec.normHeight F (b • x) : ℝ) : ℂ) ^ a)
          (ArtinPrimitiveRoots.A1.Spec.ptX F p) := by rw [hpt]
      _ = coordinateLap (fun q => complexPowerProfile a δ (T q)) p w := htermLap
      _ = ArtinPrimitiveRoots.A1.Spec.partialLap F w
          (fun x => complexPowerProfile a δ
            (ArtinPrimitiveRoots.A1.Spec.normHeight F (b • x)))
          (ArtinPrimitiveRoots.A1.Spec.ptX F p) := hprofileLap.symm
      _ = _ := by rw [hpt]
  have hbaseSmooth : ArtinPrimitiveRoots.A1.Spec.IsSmoothX F
      (fun x => complexPowerProfile a δ
        (ArtinPrimitiveRoots.A1.Spec.normHeight F x)) :=
    complexProfile_normHeight_smooth (F := F) a δ hδ
  have hcov := ArtinPrimitiveRoots.A1.Spec.g5PartialLap_action_pointwise
    g (fun x => complexPowerProfile a δ
      (ArtinPrimitiveRoots.A1.Spec.normHeight F x)) hbaseSmooth w z
  have hcov' :
      ArtinPrimitiveRoots.A1.Spec.partialLap F w
        (fun x => complexPowerProfile a δ
          (ArtinPrimitiveRoots.A1.Spec.normHeight F (b • x))) z =
      ArtinPrimitiveRoots.A1.Spec.partialLap F w
        (fun x => complexPowerProfile a δ
          (ArtinPrimitiveRoots.A1.Spec.normHeight F x)) (b • z) := by
    simpa [hAct] using hcov
  have hradial := partialLap_normHeight_complexProfile_at
    (complexPowerProfile a δ) (complexPowerProfile_smooth a δ hδ) (b • z) w
  have hderiv := complexPowerProfile_deriv a δ hδ N hδN ha0
  have hderiv2 := complexPowerProfile_deriv2 a δ hδ N hδN ha0 ha1
  have hNcomplex : ((N : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hN.ne'
  have hpow1 : ((N : ℝ) : ℂ) * ((N : ℝ) : ℂ) ^ (a - 1) =
      ((N : ℝ) : ℂ) ^ a := by
    calc
      _ = ((N : ℝ) : ℂ) ^ (a - 1) * ((N : ℝ) : ℂ) := by ring
      _ = ((N : ℝ) : ℂ) ^ (a - 1) * ((N : ℝ) : ℂ) ^ (1 : ℂ) := by simp
      _ = ((N : ℝ) : ℂ) ^ ((a - 1) + 1) :=
        (Complex.cpow_add _ _ hNcomplex).symm
      _ = ((N : ℝ) : ℂ) ^ a := by congr 1 <;> ring
  have hpow2 : (((N : ℝ) : ℂ) ^ 2) * ((N : ℝ) : ℂ) ^ (a - 2) =
      ((N : ℝ) : ℂ) ^ a := by
    calc
      _ = ((N : ℝ) : ℂ) ^ (2 : ℂ) * ((N : ℝ) : ℂ) ^ (a - 2) := by
        rw [← Complex.cpow_two]
      _ = ((N : ℝ) : ℂ) ^ ((2 : ℂ) + (a - 2)) :=
        (Complex.cpow_add _ _ hNcomplex).symm
      _ = ((N : ℝ) : ℂ) ^ a := by congr 1 <;> ring
  calc
    _ = ArtinPrimitiveRoots.A1.Spec.partialLap F w
        (fun x => complexPowerProfile a δ
          (ArtinPrimitiveRoots.A1.Spec.normHeight F x)) (b • z) :=
          htermEq.trans hcov'
    _ = ((N : ℝ) : ℂ) * deriv (complexPowerProfile a δ) N -
        ((N : ℝ) : ℂ) ^ 2 * deriv (deriv (complexPowerProfile a δ)) N := by
          simpa [N] using hradial
    _ = a * (2 - a) * ((N : ℝ) : ℂ) ^ a := by
      rw [hderiv, hderiv2]
      calc
        _ = a * (((N : ℝ) : ℂ) * ((N : ℝ) : ℂ) ^ (a - 1)) -
            (a * (a - 1)) * (((N : ℝ) : ℂ) ^ 2 *
              ((N : ℝ) : ℂ) ^ (a - 2)) := by ring
        _ = a * ((N : ℝ) : ℂ) ^ a - a * (a - 1) * ((N : ℝ) : ℂ) ^ a := by
          rw [hpow1, hpow2]
        _ = a * (2 - a) * ((N : ℝ) : ℂ) ^ a := by ring

private theorem eisTerm_partialLap (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (σ : SL(2,F)) (s : ℂ) (hs : 1 / 2 < s.re)
    (q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ)
    (z : ArtinPrimitiveRoots.A1.Spec.X F) (w : InfinitePlace F) :
    ArtinPrimitiveRoots.A1.Spec.partialLap F w
      (fun x => ArtinPrimitiveRoots.A1.Spec.eisTerm F Γ σ s x q) z =
      (1 - 4 * s ^ 2) * ArtinPrimitiveRoots.A1.Spec.eisTerm F Γ σ s z q := by
  let γ : SL(2,𝓞 F) := (q.out : Γ)
  let b : SL(2,F) := σ⁻¹ * ArtinPrimitiveRoots.A1.Spec.toSLF F γ
  let a : ℂ := 1 + 2 * s
  have ha : 2 < a.re := by
    dsimp [a]
    simp
    linarith
  have hact (x : ArtinPrimitiveRoots.A1.Spec.X F) :
      σ⁻¹ • ((γ : SL(2,𝓞 F)) • x) = b • x := by
    change σ⁻¹ • (ArtinPrimitiveRoots.A1.Spec.toSLF F γ • x) = b • x
    simpa [b] using
      (smul_smul σ⁻¹ (ArtinPrimitiveRoots.A1.Spec.toSLF F γ) x)
  have hterm (x : ArtinPrimitiveRoots.A1.Spec.X F) :
      ArtinPrimitiveRoots.A1.Spec.eisTerm F Γ σ s x q =
        ((ArtinPrimitiveRoots.A1.Spec.normHeight F (b • x) : ℝ) : ℂ) ^ a := by
    simp only [ArtinPrimitiveRoots.A1.Spec.eisTerm]
    rw [hact x]
  have hcoef : a * (2 - a) = 1 - 4 * s ^ 2 := by
    dsimp [a]
    ring
  calc
    ArtinPrimitiveRoots.A1.Spec.partialLap F w
        (fun x => ArtinPrimitiveRoots.A1.Spec.eisTerm F Γ σ s x q) z =
      ArtinPrimitiveRoots.A1.Spec.partialLap F w
        (fun x => ((ArtinPrimitiveRoots.A1.Spec.normHeight F (b • x) : ℝ) : ℂ) ^ a) z := by
          rw [show (fun x => ArtinPrimitiveRoots.A1.Spec.eisTerm F Γ σ s x q) =
            (fun x => ((ArtinPrimitiveRoots.A1.Spec.normHeight F (b • x) : ℝ) : ℂ) ^ a) from by
              funext x
              exact hterm x]
    _ = a * (2 - a) *
        ((ArtinPrimitiveRoots.A1.Spec.normHeight F (b • z) : ℝ) : ℂ) ^ a :=
          partialLap_cpow_normHeight_action b a ha z w
    _ = (1 - 4 * s ^ 2) * ArtinPrimitiveRoots.A1.Spec.eisTerm F Γ σ s z q := by
      rw [hcoef, ← hterm z]

set_option maxHeartbeats 1000000 in
private theorem localizedSeries_coordinateLap_tsum
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (σ : SL(2,F)) (s : ℂ)
    (hs : 1 / 2 < s.re) (p : PosCoord (F := F)) (w : InfinitePlace F) :
    coordinateLap (localizedSeries Γ σ s p) p.1 w =
      ∑' q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ,
        coordinateLap (fun x => rowScalar Γ σ s q *
          cutoffFamily s (localHeightFloor p) (localPsi p)
            (normalizedRows Γ σ q) x) p.1 w := by
  classical
  let f : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ →
      ArtinPrimitiveRoots.A1.Spec.Coord F → ℂ := fun q x =>
    rowScalar Γ σ s q * cutoffFamily s (localHeightFloor p) (localPsi p)
      (normalizedRows Γ σ q) x
  have hterms : ∀ q, ContDiff ℝ (2 : ℕ∞ω) (f q) := by
    intro q
    apply contDiff_iff_contDiffAt.mpr
    intro x
    rcases localized_family_data Γ σ s p with ⟨hF, _⟩
    let u := normalizedRows Γ σ q
    have hu : u ∈ rowUnitSet (F := F) := normalizedRows_mem Γ σ q
    have hcut : ContDiffAt ℝ ∞
        (fun y => cutoffFamily s (localHeightFloor p) (localPsi p) u y) x := by
      have hpair : ContDiffAt ℝ ∞ (fun y : ArtinPrimitiveRoots.A1.Spec.Coord F => (u,y)) x :=
        contDiffAt_const.prodMk contDiffAt_id
      exact (hF u hu x).comp x hpair
    have hterm : ContDiffAt ℝ ∞ (f q) x := by
      dsimp [f, u]
      exact contDiffAt_const.mul hcut
    exact hterm.of_le (by norm_num : (2 : ℕ∞ω) ≤ ∞)
  have hConst (k : ℕ) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ q x,
        ‖iteratedFDeriv ℝ k (f q) x‖ ≤ C * ‖rowScalar Γ σ s q‖ := by
    obtain ⟨C, hC, hbound⟩ := localizedDerivativeConstant Γ σ s hs p k
    refine ⟨C, hC, ?_⟩
    intro q x
    simpa [f] using hbound q x
  choose C hC hBound using hConst
  let v (k : ℕ) (q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ) : ℝ :=
    C k * ‖rowScalar Γ σ s q‖
  have hv (k : ℕ) (hk : (k : ℕ∞) ≤ (2 : ℕ∞)) : Summable (v k) := by
    exact (rowScalar_summable Γ σ s hs).mul_left (C k)
  have h'f : ∀ (k : ℕ) q x, (k : ℕ∞) ≤ (2 : ℕ∞) →
      ‖iteratedFDeriv ℝ k (f q) x‖ ≤ v k q := by
    intro k q x hk
    simpa [v] using hBound k q x
  have hderiv1 := iteratedFDeriv_tsum (f := f) (N := (2 : ℕ∞))
    hterms hv h'f (k := 1) (by norm_num)
  have hderiv2 := iteratedFDeriv_tsum (f := f) (N := (2 : ℕ∞))
    hterms hv h'f (k := 2) (by norm_num)
  have hderiv1' :
      iteratedFDeriv ℝ 1 (localizedSeries Γ σ s p) =
        fun x => ∑' q, iteratedFDeriv ℝ 1 (f q) x := by
    change iteratedFDeriv ℝ 1 (fun x => ∑' q, f q x) =
      fun x => ∑' q, iteratedFDeriv ℝ 1 (f q) x
    exact hderiv1
  have hderiv2' :
      iteratedFDeriv ℝ 2 (localizedSeries Γ σ s p) =
        fun x => ∑' q, iteratedFDeriv ℝ 2 (f q) x := by
    change iteratedFDeriv ℝ 2 (fun x => ∑' q, f q x) =
      fun x => ∑' q, iteratedFDeriv ℝ 2 (f q) x
    exact hderiv2
  let e0 := ArtinPrimitiveRoots.A1.Spec.placeDirection F w 0
  let e1 := ArtinPrimitiveRoots.A1.Spec.placeDirection F w 1
  let e2 := ArtinPrimitiveRoots.A1.Spec.placeDirection F w 2
  let d1 : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ → ℂ := fun q =>
    fderiv ℝ (f q) p.1 e2
  let d20 : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ → ℂ := fun q =>
    iteratedFDeriv ℝ 2 (f q) p.1 ![e0,e0]
  let d21 : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ → ℂ := fun q =>
    iteratedFDeriv ℝ 2 (f q) p.1 ![e1,e1]
  let d22 : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ → ℂ := fun q =>
    iteratedFDeriv ℝ 2 (f q) p.1 ![e2,e2]
  have hDsum (k : ℕ) (hk : k ≤ 2) :
      Summable (fun q => iteratedFDeriv ℝ k (f q) p.1) := by
    letI : CompleteSpace
        (ContinuousMultilinearMap ℝ (fun _ : Fin k => ArtinPrimitiveRoots.A1.Spec.Coord F) ℂ) := by
      let w₀ : InfinitePlace F := Classical.choice (inferInstance : Nonempty (InfinitePlace F))
      have hm : ∀ i : Fin k,
          (fun _ : InfinitePlace F => ((1 : ℂ), (0 : ℝ))) ≠
            (0 : ArtinPrimitiveRoots.A1.Spec.Coord F) := by
        intro i hi
        have hval := congrFun hi w₀
        norm_num at hval
      exact (SeparatingDual.completeSpace_continuousMultilinearMap_iff ℝ ℂ
        (m := fun _ : Fin k => fun _ : InfinitePlace F => ((1 : ℂ), (0 : ℝ))) hm).2
        inferInstance
    apply Summable.of_norm_bounded
      ((rowScalar_summable Γ σ s hs).mul_left (C k))
    intro q
    exact hBound k q p.1
  have hfirst : fderiv ℝ (localizedSeries Γ σ s p) p.1 e2 = ∑' q, d1 q := by
    have hMid := congrArg (fun D => D ![e2]) (congrFun hderiv1' p.1)
    have hmap := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 =>
      ArtinPrimitiveRoots.A1.Spec.Coord F) ℂ ![e2]).map_tsum
        (hDsum 1 (by norm_num))
    calc
      fderiv ℝ (localizedSeries Γ σ s p) p.1 e2 =
          iteratedFDeriv ℝ 1 (localizedSeries Γ σ s p) p.1 ![e2] := by
            simp [iteratedFDeriv_one_apply]
      _ = (∑' q, iteratedFDeriv ℝ 1 (f q) p.1) ![e2] := hMid
      _ = ∑' q, iteratedFDeriv ℝ 1 (f q) p.1 ![e2] := by
            simpa [ContinuousMultilinearMap.apply_apply] using hmap
      _ = ∑' q, d1 q := by simp [d1, iteratedFDeriv_one_apply]
  have hsecond0 :
      iteratedFDeriv ℝ 2 (localizedSeries Γ σ s p) p.1 ![e0,e0] = ∑' q, d20 q := by
    have hMid := congrArg (fun D => D ![e0,e0]) (congrFun hderiv2' p.1)
    have hmap := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 =>
      ArtinPrimitiveRoots.A1.Spec.Coord F) ℂ ![e0,e0]).map_tsum
        (hDsum 2 (by norm_num))
    calc
      _ = (∑' q, iteratedFDeriv ℝ 2 (f q) p.1) ![e0,e0] := hMid
      _ = ∑' q, iteratedFDeriv ℝ 2 (f q) p.1 ![e0,e0] := by
            simpa [ContinuousMultilinearMap.apply_apply] using hmap
      _ = ∑' q, d20 q := by simp [d20]
  have hsecond1 :
      iteratedFDeriv ℝ 2 (localizedSeries Γ σ s p) p.1 ![e1,e1] = ∑' q, d21 q := by
    have hMid := congrArg (fun D => D ![e1,e1]) (congrFun hderiv2' p.1)
    have hmap := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 =>
      ArtinPrimitiveRoots.A1.Spec.Coord F) ℂ ![e1,e1]).map_tsum
        (hDsum 2 (by norm_num))
    calc
      _ = (∑' q, iteratedFDeriv ℝ 2 (f q) p.1) ![e1,e1] := hMid
      _ = ∑' q, iteratedFDeriv ℝ 2 (f q) p.1 ![e1,e1] := by
            simpa [ContinuousMultilinearMap.apply_apply] using hmap
      _ = ∑' q, d21 q := by simp [d21]
  have hsecond2 :
      iteratedFDeriv ℝ 2 (localizedSeries Γ σ s p) p.1 ![e2,e2] = ∑' q, d22 q := by
    have hMid := congrArg (fun D => D ![e2,e2]) (congrFun hderiv2' p.1)
    have hmap := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 =>
      ArtinPrimitiveRoots.A1.Spec.Coord F) ℂ ![e2,e2]).map_tsum
        (hDsum 2 (by norm_num))
    calc
      _ = (∑' q, iteratedFDeriv ℝ 2 (f q) p.1) ![e2,e2] := hMid
      _ = ∑' q, iteratedFDeriv ℝ 2 (f q) p.1 ![e2,e2] := by
            simpa [ContinuousMultilinearMap.apply_apply] using hmap
      _ = ∑' q, d22 q := by simp [d22]
  have hfirstExp :
      fderiv ℝ (fun x => ∑' q, f q x) p.1 e2 = ∑' q, d1 q := by
    change fderiv ℝ (localizedSeries Γ σ s p) p.1 e2 = ∑' q, d1 q
    exact hfirst
  have hsecond0Exp :
      iteratedFDeriv ℝ 2 (fun x => ∑' q, f q x) p.1 ![e0,e0] = ∑' q, d20 q := by
    change iteratedFDeriv ℝ 2 (localizedSeries Γ σ s p) p.1 ![e0,e0] = ∑' q, d20 q
    exact hsecond0
  have hsecond1Exp :
      iteratedFDeriv ℝ 2 (fun x => ∑' q, f q x) p.1 ![e1,e1] = ∑' q, d21 q := by
    change iteratedFDeriv ℝ 2 (localizedSeries Γ σ s p) p.1 ![e1,e1] = ∑' q, d21 q
    exact hsecond1
  have hsecond2Exp :
      iteratedFDeriv ℝ 2 (fun x => ∑' q, f q x) p.1 ![e2,e2] = ∑' q, d22 q := by
    change iteratedFDeriv ℝ 2 (localizedSeries Γ σ s p) p.1 ![e2,e2] = ∑' q, d22 q
    exact hsecond2
  have hEvalSummable (k : ℕ) (hk : k ≤ 2) (u : Fin k → ArtinPrimitiveRoots.A1.Spec.Coord F) :
      Summable (fun q => iteratedFDeriv ℝ k (f q) p.1 u) := by
    let V : ℝ := ∏ i : Fin k, ‖u i‖
    have hV : 0 ≤ V := by
      dsimp [V]
      exact Finset.prod_nonneg fun i hi => norm_nonneg _
    apply Summable.of_norm_bounded
      ((rowScalar_summable Γ σ s hs).mul_left (C k * V))
    intro q
    let D := iteratedFDeriv ℝ k (f q) p.1
    have hEval : ‖D u‖ ≤ ‖D‖ * V := by
      simpa [D, V] using D.le_opNorm u
    calc
      ‖iteratedFDeriv ℝ k (f q) p.1 u‖ ≤ ‖D‖ * V := by simpa [D] using hEval
      _ ≤ (C k * ‖rowScalar Γ σ s q‖) * V :=
        mul_le_mul_of_nonneg_right (hBound k q p.1) hV
      _ = (C k * V) * ‖rowScalar Γ σ s q‖ := by ring
  have hs1 : Summable d1 := by
    simpa [d1, iteratedFDeriv_one_apply] using
      hEvalSummable 1 (by norm_num) ![e2]
  have hs20 : Summable d20 := by simpa [d20] using hEvalSummable 2 (by norm_num) ![e0,e0]
  have hs21 : Summable d21 := by simpa [d21] using hEvalSummable 2 (by norm_num) ![e1,e1]
  have hs22 : Summable d22 := by simpa [d22] using hEvalSummable 2 (by norm_num) ![e2,e2]
  have hs2 : Summable (fun q => d20 q + d21 q + d22 q) := (hs20.add hs21).add hs22
  have hsum2 :
      (∑' q, d20 q) + (∑' q, d21 q) + (∑' q, d22 q) =
        ∑' q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ,
          (d20 q + d21 q + d22 q) := by
    rw [← hs20.tsum_add hs21, ← (hs20.add hs21).tsum_add hs22]
  have hs1sm : Summable (fun q => (p.1 w).2 • d1 q) := hs1.const_smul (p.1 w).2
  have hs2sm : Summable (fun q => (p.1 w).2 ^ 2 • (d20 q + d21 q + d22 q)) :=
    hs2.const_smul ((p.1 w).2 ^ 2)
  calc
    coordinateLap (fun x => ∑' q, f q x) p.1 w =
    (p.1 w).2 • (∑' q, d1 q) -
          (p.1 w).2 ^ 2 • ((∑' q, d20 q) + (∑' q, d21 q) + (∑' q, d22 q)) := by
      unfold coordinateLap
      rw [hfirstExp, hsecond0Exp, hsecond1Exp, hsecond2Exp]
    _ = (∑' q, (p.1 w).2 • d1 q) -
          ∑' q, (p.1 w).2 ^ 2 • (d20 q + d21 q + d22 q) := by
      rw [← hs1.tsum_const_smul (p.1 w).2, hsum2,
        ← hs2.tsum_const_smul ((p.1 w).2 ^ 2)]
    _ = ∑' q, ((p.1 w).2 • d1 q -
        (p.1 w).2 ^ 2 • (d20 q + d21 q + d22 q)) :=
      (hs1sm.tsum_sub hs2sm).symm
    _ = ∑' q, coordinateLap (f q) p.1 w := by
      apply tsum_congr
      intro q
      rfl

private theorem eisSeries_partialLap (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (σ : SL(2,F)) (s : ℂ) (hs : 1 / 2 < s.re)
    (w : InfinitePlace F) (z : ArtinPrimitiveRoots.A1.Spec.X F) :
    ArtinPrimitiveRoots.A1.Spec.partialLap F w
      (ArtinPrimitiveRoots.A1.Spec.eisSeries F Γ σ s) z =
      (1 - 4 * s ^ 2) * ArtinPrimitiveRoots.A1.Spec.eisSeries F Γ σ s z := by
  let x : ArtinPrimitiveRoots.A1.Spec.Coord F :=
    ArtinPrimitiveRoots.A1.Spec.coordsX F z
  have hx : x ∈ ArtinPrimitiveRoots.A1.Spec.posSet F := by
    intro v
    change 0 < ArtinPrimitiveRoots.A1.Spec.height (z v)
    rw [ArtinPrimitiveRoots.A1.Spec.height_eq_hyperbolicHeight]
    exact OAI.CubicEisenstein.hyperbolicHeight_pos (z v)
  have hpt : ArtinPrimitiveRoots.A1.Spec.ptX F x = z := by
    rcases ArtinPrimitiveRoots.A1.Spec.G1_h3_basics (F := F) with
      ⟨_, _, _, _, _, _, _, hpt, _, _, _, _⟩
    exact hpt z
  let p : PosCoord (F := F) := ⟨x, hx⟩
  have hball : x ∈ Metric.ball x (localCutoff p).bump.rIn :=
    Metric.mem_ball_self (localCutoff p).bump.rIn_pos
  have hSeriesEq := eisSeries_local_eventually_eq Γ σ s p
  have hSeriesLap := partialLap_from_chart
    (ArtinPrimitiveRoots.A1.Spec.eisSeries F Γ σ s)
    (localizedSeries Γ σ s p) x hx w hSeriesEq
  have hLocalLapSum := localizedSeries_coordinateLap_tsum Γ σ s hs p w
  have htermLap (q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ) :
      coordinateLap (fun y => rowScalar Γ σ s q * cutoffFamily s
        (localHeightFloor p) (localPsi p) (normalizedRows Γ σ q) y) x w =
      (1 - 4 * s ^ 2) *
        ArtinPrimitiveRoots.A1.Spec.eisTerm F Γ σ s
          (ArtinPrimitiveRoots.A1.Spec.ptX F x) q := by
    have hlocal := localTerm_eventually_eq_weighted Γ σ s p x hball q
    have hLapTerm := partialLap_from_chart
      (fun y => ArtinPrimitiveRoots.A1.Spec.eisTerm F Γ σ s y q)
      (fun y => rowScalar Γ σ s q * cutoffFamily s
        (localHeightFloor p) (localPsi p) (normalizedRows Γ σ q) y)
      x hx w hlocal
    calc
      _ = ArtinPrimitiveRoots.A1.Spec.partialLap F w
          (fun y => ArtinPrimitiveRoots.A1.Spec.eisTerm F Γ σ s y q)
          (ArtinPrimitiveRoots.A1.Spec.ptX F x) := hLapTerm.symm
      _ = _ := eisTerm_partialLap Γ σ s hs q (ArtinPrimitiveRoots.A1.Spec.ptX F x) w
  let lam : ℂ := 1 - 4 * s ^ 2
  have hTermSum : Summable (fun q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ =>
      ArtinPrimitiveRoots.A1.Spec.eisTerm F Γ σ s (ArtinPrimitiveRoots.A1.Spec.ptX F x) q) := by
    let σ₀ : ℝ := (1 / 2 + s.re) / 2
    have hσ₀ : 1 / 2 < σ₀ := by dsimp [σ₀]; linarith
    have hσ₀le : σ₀ ≤ s.re := by dsimp [σ₀]; linarith
    obtain ⟨m, hm, hmBound⟩ :=
      (ArtinPrimitiveRoots.A1.Spec.E2_eis_converge (F := F) Γ σ).1
        {ArtinPrimitiveRoots.A1.Spec.ptX F x} isCompact_singleton σ₀ s.re hσ₀
    apply Summable.of_norm_bounded hm
    intro q
    exact hmBound (ArtinPrimitiveRoots.A1.Spec.ptX F x) (by simp) s
      hσ₀le le_rfl q
  have hscaled :
      ∑' q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ,
        lam * ArtinPrimitiveRoots.A1.Spec.eisTerm F Γ σ s
          (ArtinPrimitiveRoots.A1.Spec.ptX F x) q =
        lam * ∑' q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ,
          ArtinPrimitiveRoots.A1.Spec.eisTerm F Γ σ s
            (ArtinPrimitiveRoots.A1.Spec.ptX F x) q :=
    hTermSum.tsum_const_smul lam
  have hseriesValue : ArtinPrimitiveRoots.A1.Spec.eisSeries F Γ σ s
      (ArtinPrimitiveRoots.A1.Spec.ptX F x) = localizedSeries Γ σ s p x :=
    hSeriesEq.eq_of_nhds
  calc
    ArtinPrimitiveRoots.A1.Spec.partialLap F w
        (ArtinPrimitiveRoots.A1.Spec.eisSeries F Γ σ s) z =
      ArtinPrimitiveRoots.A1.Spec.partialLap F w
        (ArtinPrimitiveRoots.A1.Spec.eisSeries F Γ σ s)
        (ArtinPrimitiveRoots.A1.Spec.ptX F x) := by rw [hpt]
    _ = coordinateLap (localizedSeries Γ σ s p) x w := hSeriesLap
    _ = ∑' q, coordinateLap (fun y => rowScalar Γ σ s q * cutoffFamily s
        (localHeightFloor p) (localPsi p) (normalizedRows Γ σ q) y) x w := hLocalLapSum
    _ = ∑' q, lam * ArtinPrimitiveRoots.A1.Spec.eisTerm F Γ σ s
        (ArtinPrimitiveRoots.A1.Spec.ptX F x) q := by
      apply tsum_congr
      intro q
      simpa [lam] using htermLap q
    _ = lam * ArtinPrimitiveRoots.A1.Spec.eisSeries F Γ σ s
        (ArtinPrimitiveRoots.A1.Spec.ptX F x) := by
      simpa [ArtinPrimitiveRoots.A1.Spec.eisSeries, lam] using hscaled
    _ = lam * localizedSeries Γ σ s p x := by rw [hseriesValue]
    _ = lam * ArtinPrimitiveRoots.A1.Spec.eisSeries F Γ σ s
        (ArtinPrimitiveRoots.A1.Spec.ptX F x) := by rw [← hseriesValue]
    _ = (1 - 4 * s ^ 2) * ArtinPrimitiveRoots.A1.Spec.eisSeries F Γ σ s z := by
      dsimp [lam]
      rw [hpt]

theorem e3Result (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (σ : SL(2,F)) (s : ℂ) (hs : 1 / 2 < s.re) :
    ArtinPrimitiveRoots.A1.Spec.IsSmoothX F
      (ArtinPrimitiveRoots.A1.Spec.eisSeries F Γ σ s) ∧
    (∀ w z, ArtinPrimitiveRoots.A1.Spec.partialLap F w
      (ArtinPrimitiveRoots.A1.Spec.eisSeries F Γ σ s) z =
      (1 - 4 * s ^ 2) * ArtinPrimitiveRoots.A1.Spec.eisSeries F Γ σ s z) ∧
    (∀ K : Set (ArtinPrimitiveRoots.A1.Spec.Coord F), IsCompact K →
      K ⊆ ArtinPrimitiveRoots.A1.Spec.posSet F →
      ∀ n : ℕ, ∀ v : Fin n → ArtinPrimitiveRoots.A1.Spec.Coord F,
        ∃ m : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ → ℝ, Summable m ∧
          ∀ q p, p ∈ K →
            ‖iteratedFDeriv ℝ n
              (fun p => ArtinPrimitiveRoots.A1.Spec.eisTerm F Γ σ s
                (ArtinPrimitiveRoots.A1.Spec.ptX F p) q) p v‖ ≤ m q) := by
  refine ⟨eisSeries_isSmooth Γ σ s hs, ?_, ?_⟩
  · exact eisSeries_partialLap Γ σ s hs
  · exact eisTerm_derivative_majorant Γ σ s hs

private def seedLogProfile (τ : ℝ → ℝ) (a : ℂ) (u : ℝ) : ℂ :=
  (τ (Real.exp u) : ℂ) * Complex.exp (a * (u : ℂ))

private theorem seedLogProfile_contDiff (τ : ℝ → ℝ) (a : ℂ)
    (hτ : ContDiff ℝ ∞ τ) : ContDiff ℝ ∞ (seedLogProfile τ a) := by
  have hτ' : ContDiff ℝ ∞ (fun u : ℝ => τ (Real.exp u)) :=
    hτ.comp Real.contDiff_exp
  have hτC : ContDiff ℝ ∞ (fun u : ℝ => (τ (Real.exp u) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hτ'
  have harg : ContDiff ℝ ∞ (fun u : ℝ => a * (u : ℂ)) := by
    have h := (Complex.ofRealCLM.smulRight a).contDiff (n := ∞)
    convert h using 1 <;> ext u <;>
      simp [Complex.ofRealCLM_apply, ContinuousLinearMap.smulRight_apply,
        smul_eq_mul, mul_comm]
  change ContDiff ℝ ∞ (fun u : ℝ =>
    (τ (Real.exp u) : ℂ) * Complex.exp (a * (u : ℂ)))
  exact hτC.mul (Complex.contDiff_exp.comp harg)

private theorem seedLogProfile_log (τ : ℝ → ℝ) (a : ℂ) {h : ℝ} (hh : 0 < h) :
    seedLogProfile τ a (Real.log h) = (τ h : ℂ) * (h : ℂ) ^ a := by
  have hne : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh.ne'
  rw [seedLogProfile, Real.exp_log hh,
    Complex.cpow_def_of_ne_zero hne, Complex.ofReal_log hh.le]
  congr 1
  ring

private lemma seedNormHeight_pos (z : ArtinPrimitiveRoots.A1.Spec.X F) :
    0 < ArtinPrimitiveRoots.A1.Spec.normHeight F z := by
  unfold ArtinPrimitiveRoots.A1.Spec.normHeight
  apply Finset.prod_pos
  intro w hw
  rw [ArtinPrimitiveRoots.A1.Spec.height_eq_hyperbolicHeight]
  exact OAI.CubicEisenstein.hyperbolicHeight_pos (z w)

private theorem seedHeight_action_smooth (b : SL(2,F)) :
    ContDiffOn ℝ ∞
      (fun p : ArtinPrimitiveRoots.A1.Spec.Coord F =>
        ArtinPrimitiveRoots.A1.Spec.normHeight F (b • ArtinPrimitiveRoots.A1.Spec.ptX F p))
      (ArtinPrimitiveRoots.A1.Spec.posSet F) := by
  let g : InfinitePlace F → SL(2,ℂ) := ArtinPrimitiveRoots.A1.Spec.toInf F b
  have hbase := normHeight_complex_smooth (F := F)
  have hcomp := ArtinPrimitiveRoots.A1.Spec.g5IsSmoothX_action g
    (fun z => ((ArtinPrimitiveRoots.A1.Spec.normHeight F z : ℝ) : ℂ)) hbase
  have hact (z : ArtinPrimitiveRoots.A1.Spec.X F) :
      ArtinPrimitiveRoots.A1.Spec.actAtPlaces F g z = b • z := by
    funext w
    rfl
  have hc : ContDiffOn ℝ ∞
      (fun p : ArtinPrimitiveRoots.A1.Spec.Coord F =>
        ((ArtinPrimitiveRoots.A1.Spec.normHeight F
          (b • ArtinPrimitiveRoots.A1.Spec.ptX F p) : ℝ) : ℂ))
      (ArtinPrimitiveRoots.A1.Spec.posSet F) := by
    change ContDiffOn ℝ ∞
      (fun p => ((ArtinPrimitiveRoots.A1.Spec.normHeight F
        (ArtinPrimitiveRoots.A1.Spec.actAtPlaces F g
          (ArtinPrimitiveRoots.A1.Spec.ptX F p)) : ℝ) : ℂ))
      (ArtinPrimitiveRoots.A1.Spec.posSet F)
    apply hcomp.congr
    intro p hp
    rfl
  have hr := Complex.reCLM.contDiff.comp_contDiffOn hc
  apply hr.congr
  intro p hp
  simp [Complex.reCLM_apply]

private def seedExpCoeff (b ell : ArtinPrimitiveRoots.A1.Spec.Coord F → ℂ) :
    (n : ℕ) → (v : Fin n → ArtinPrimitiveRoots.A1.Spec.Coord F) →
      ℕ → ArtinPrimitiveRoots.A1.Spec.Coord F → ℂ
  | 0, _, k, p => if k = 0 then b p else 0
  | n + 1, v, k, p =>
      fderiv ℝ (seedExpCoeff b ell n (fun i => v i.succ) k) p (v 0) +
        if k = 0 then 0 else
          fderiv ℝ ell p (v 0) * seedExpCoeff b ell n (fun i => v i.succ) (k - 1) p

private theorem seedExpCoeff_contDiffOn
    (b ell : ArtinPrimitiveRoots.A1.Spec.Coord F → ℂ)
    (hb : ContDiffOn ℝ ∞ b (ArtinPrimitiveRoots.A1.Spec.posSet F))
    (hell : ContDiffOn ℝ ∞ ell (ArtinPrimitiveRoots.A1.Spec.posSet F)) :
    ∀ n (v : Fin n → ArtinPrimitiveRoots.A1.Spec.Coord F) k,
      ContDiffOn ℝ ∞ (seedExpCoeff b ell n v k) (ArtinPrimitiveRoots.A1.Spec.posSet F) := by
  intro n
  induction n with
  | zero =>
      intro v k
      by_cases hk : k = 0
      · simp [seedExpCoeff, hk, hb]
      · simpa [seedExpCoeff, hk] using
          (contDiffOn_const : ContDiffOn ℝ ∞
            (fun _ : ArtinPrimitiveRoots.A1.Spec.Coord F => (0 : ℂ))
            (ArtinPrimitiveRoots.A1.Spec.posSet F))
  | succ n ih =>
      intro v k
      let vt : Fin n → ArtinPrimitiveRoots.A1.Spec.Coord F := fun i => v i.succ
      have hc : ContDiffOn ℝ ∞ (seedExpCoeff b ell n vt k)
          (ArtinPrimitiveRoots.A1.Spec.posSet F) := ih vt k
      have hcd : ContDiffOn ℝ ∞
          (fun p => fderiv ℝ (seedExpCoeff b ell n vt k) p (v 0))
          (ArtinPrimitiveRoots.A1.Spec.posSet F) := by
        have h : ContDiffOn ℝ ∞ (fderiv ℝ (seedExpCoeff b ell n vt k))
            (ArtinPrimitiveRoots.A1.Spec.posSet F) :=
          hc.fderiv_of_isOpen (m := ∞) (posSet_isOpen (F := F)) (by simp)
        exact h.clm_apply contDiffOn_const
      have held : ContDiffOn ℝ ∞
          (fun p => fderiv ℝ ell p (v 0)) (ArtinPrimitiveRoots.A1.Spec.posSet F) := by
        have h : ContDiffOn ℝ ∞ (fderiv ℝ ell) (ArtinPrimitiveRoots.A1.Spec.posSet F) :=
          hell.fderiv_of_isOpen (m := ∞) (posSet_isOpen (F := F)) (by simp)
        exact h.clm_apply contDiffOn_const
      by_cases hk : k = 0
      · simpa [seedExpCoeff, vt, hk] using hcd
      · have hprev : ContDiffOn ℝ ∞
            (seedExpCoeff b ell n vt (k - 1))
            (ArtinPrimitiveRoots.A1.Spec.posSet F) := ih vt (k - 1)
        simpa [seedExpCoeff, vt, hk] using hcd.add (held.mul hprev)

private theorem seedExpCoeff_eq_zero_of_gt
    (b ell : ArtinPrimitiveRoots.A1.Spec.Coord F → ℂ) :
    ∀ n (v : Fin n → ArtinPrimitiveRoots.A1.Spec.Coord F) k
      (p : ArtinPrimitiveRoots.A1.Spec.Coord F),
      n < k → seedExpCoeff b ell n v k p = 0 := by
  intro n
  induction n with
  | zero =>
      intro v k p hk
      simp [seedExpCoeff, Nat.ne_of_gt hk]
  | succ n ih =>
      intro v k p hk
      let vt : Fin n → ArtinPrimitiveRoots.A1.Spec.Coord F := fun i => v i.succ
      have hk0 : k ≠ 0 := by omega
      have hkn : n < k := by omega
      have hkle : n < k - 1 := by omega
      have hc : seedExpCoeff b ell n vt k = 0 := by
        funext x
        exact ih vt k x hkn
      have hp : seedExpCoeff b ell n vt (k - 1) p = 0 := by
        exact ih vt (k - 1) p (by omega)
      simp [seedExpCoeff, vt, hk0, hc, hp]

private def seedExpPoly (b ell : ArtinPrimitiveRoots.A1.Spec.Coord F → ℂ)
    (n : ℕ) (v : Fin n → ArtinPrimitiveRoots.A1.Spec.Coord F)
    (a : ℂ) (p : ArtinPrimitiveRoots.A1.Spec.Coord F) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), a ^ k * seedExpCoeff b ell n v k p

private theorem seedExpCoeff_shift_sum (c : ℕ → ℂ) (a d : ℂ) :
    ∀ n : ℕ,
      (∑ k ∈ Finset.range (n + 1), a ^ k *
        (if k = 0 then 0 else d * c (k - 1))) =
        a * d * (∑ k ∈ Finset.range n, a ^ k * c k) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      conv_lhs => rw [Finset.sum_range_succ]
      rw [ih]
      conv_rhs => rw [Finset.sum_range_succ]
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one, pow_succ]
      ring

private theorem seedComplexExp_comp_fderiv
    (ell : ArtinPrimitiveRoots.A1.Spec.Coord F → ℂ)
    (hell : ContDiffOn ℝ ∞ ell (ArtinPrimitiveRoots.A1.Spec.posSet F))
    (a : ℂ) (p : ArtinPrimitiveRoots.A1.Spec.Coord F)
    (hp : p ∈ ArtinPrimitiveRoots.A1.Spec.posSet F)
    (v : ArtinPrimitiveRoots.A1.Spec.Coord F) :
    fderiv ℝ (fun x => Complex.exp (a * ell x)) p v =
      Complex.exp (a * ell p) * a * fderiv ℝ ell p v := by
  have hEllAt := hell.contDiffAt
    (ArtinPrimitiveRoots.Proofs.spec_seed_p.posSet_isOpen.mem_nhds hp)
  have hEllDiff : DifferentiableAt ℝ ell p := hEllAt.differentiableAt (by simp)
  have hArgDiff : DifferentiableAt ℝ (fun x => a * ell x) p :=
    (differentiableAt_const a).mul hEllDiff
  have hArgDeriv : fderiv ℝ (fun x => a * ell x) p = a • fderiv ℝ ell p :=
    fderiv_fun_const_smul hEllDiff a
  have hArg : HasFDerivAt (fun x => a * ell x) (a • fderiv ℝ ell p) p := by
    convert hArgDiff.hasFDerivAt using 1
    exact hArgDeriv.symm
  have hExp : HasFDerivAt Complex.exp
      (Complex.exp (a * ell p) • (1 : ℂ →L[ℝ] ℂ)) (a * ell p) := by
    have h := (Complex.hasDerivAt_exp (a * ell p)).hasFDerivAt.restrictScalars ℝ
    have heq :
        ContinuousLinearMap.restrictScalars ℝ
          (ContinuousLinearMap.toSpanSingleton ℂ (Complex.exp (a * ell p))) =
        Complex.exp (a * ell p) • (1 : ℂ →L[ℝ] ℂ) := by
      ext z
      simp [ContinuousLinearMap.toSpanSingleton_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul, mul_comm]
    rw [heq] at h
    exact h
  have hcomp := hExp.comp p hArg
  have hcompFderiv : fderiv ℝ (fun x => Complex.exp (a * ell x)) p =
      (Complex.exp (a * ell p) • (1 : ℂ →L[ℝ] ℂ)).comp
        (a • fderiv ℝ ell p) := by
    simpa only [Function.comp_def] using hcomp.fderiv
  rw [hcompFderiv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

set_option maxHeartbeats 1000000 in
private theorem seedExpPoly_succ
    (b ell : ArtinPrimitiveRoots.A1.Spec.Coord F → ℂ)
    (hb : ContDiffOn ℝ ∞ b (ArtinPrimitiveRoots.A1.Spec.posSet F))
    (hell : ContDiffOn ℝ ∞ ell (ArtinPrimitiveRoots.A1.Spec.posSet F))
    (n : ℕ) (v : Fin (n + 1) → ArtinPrimitiveRoots.A1.Spec.Coord F)
    (a : ℂ) (p : ArtinPrimitiveRoots.A1.Spec.Coord F)
    (hp : p ∈ ArtinPrimitiveRoots.A1.Spec.posSet F) :
    seedExpPoly b ell (n + 1) v a p =
      fderiv ℝ (fun x => seedExpPoly b ell n (Fin.tail v) a x) p (v 0) +
        a * fderiv ℝ ell p (v 0) * seedExpPoly b ell n (Fin.tail v) a p := by
  let vt : Fin n → ArtinPrimitiveRoots.A1.Spec.Coord F := Fin.tail v
  let c : ℕ → ArtinPrimitiveRoots.A1.Spec.Coord F → ℂ :=
    fun k => seedExpCoeff b ell n vt k
  let d : ℂ := fderiv ℝ ell p (v 0)
  have hsplit :
      (∑ k ∈ Finset.range (n + 2), a ^ k *
        (fderiv ℝ (c k) p (v 0) + if k = 0 then 0 else d * c (k - 1) p)) =
      (∑ k ∈ Finset.range (n + 2), a ^ k * fderiv ℝ (c k) p (v 0)) +
        (∑ k ∈ Finset.range (n + 2), a ^ k *
          (if k = 0 then 0 else d * c (k - 1) p)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have htop : c (n + 1) = 0 := by
    funext x
    exact seedExpCoeff_eq_zero_of_gt b ell n vt (n + 1) x (by omega)
  have hfirst :
      (∑ k ∈ Finset.range (n + 2), a ^ k * fderiv ℝ (c k) p (v 0)) =
        fderiv ℝ (fun x => seedExpPoly b ell n vt a x) p (v 0) := by
    rw [Finset.sum_range_succ]
    have hlast : fderiv ℝ (c (n + 1)) p (v 0) = 0 := by
      rw [htop]
      simp
    have hderiv :
        fderiv ℝ (fun x => ∑ k ∈ Finset.range (n + 1), a ^ k * c k x) p =
          ∑ k ∈ Finset.range (n + 1), fderiv ℝ (fun x => a ^ k * c k x) p := by
      apply fderiv_fun_sum
      intro k hk
      have hck : ContDiffOn ℝ ∞ (c k) (ArtinPrimitiveRoots.A1.Spec.posSet F) :=
        seedExpCoeff_contDiffOn b ell hb hell n vt k
      have hAt := hck.contDiffAt
        (ArtinPrimitiveRoots.Proofs.spec_seed_p.posSet_isOpen.mem_nhds hp)
      have hconst : DifferentiableAt ℝ
          (fun _ : ArtinPrimitiveRoots.A1.Spec.Coord F => a ^ k) p := by fun_prop
      exact hconst.mul (hAt.differentiableAt (by simp))
    have hpoint (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
        fderiv ℝ (fun x => a ^ k * c k x) p (v 0) =
          a ^ k * fderiv ℝ (c k) p (v 0) := by
      have hck : ContDiffOn ℝ ∞ (c k) (ArtinPrimitiveRoots.A1.Spec.posSet F) :=
        seedExpCoeff_contDiffOn b ell hb hell n vt k
      have hAt := hck.contDiffAt
        (ArtinPrimitiveRoots.Proofs.spec_seed_p.posSet_isOpen.mem_nhds hp)
      simpa only [ContinuousLinearMap.smul_apply, smul_eq_mul] using
        congrArg (fun g : ArtinPrimitiveRoots.A1.Spec.Coord F →L[ℝ] ℂ => g (v 0))
          (fderiv_fun_const_smul (hAt.differentiableAt (by simp)) (a ^ k))
    have hpolyfun :
        (fun x => seedExpPoly b ell n vt a x) =
          (fun x => ∑ k ∈ Finset.range (n + 1), a ^ k * c k x) := by
      funext x
      rfl
    rw [hpolyfun, hderiv]
    have happly :
        (∑ k ∈ Finset.range (n + 1), fderiv ℝ (fun x => a ^ k * c k x) p) (v 0) =
          ∑ k ∈ Finset.range (n + 1), fderiv ℝ (fun x => a ^ k * c k x) p (v 0) := by
      simp
    rw [happly]
    have hsumEq :
        (∑ k ∈ Finset.range (n + 1), a ^ k * fderiv ℝ (c k) p (v 0)) =
          ∑ k ∈ Finset.range (n + 1), fderiv ℝ (fun x => a ^ k * c k x) p (v 0) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact (hpoint k hk).symm
    rw [← hsumEq, hlast]
    simp
  have hsecond := seedExpCoeff_shift_sum (fun k => c k p) a d (n + 1)
  change (∑ k ∈ Finset.range (n + 2), a ^ k *
      (fderiv ℝ (c k) p (v 0) + if k = 0 then 0 else d * c (k - 1) p)) =
    fderiv ℝ (fun x => seedExpPoly b ell n vt a x) p (v 0) +
      (a * d) * (∑ k ∈ Finset.range (n + 1), a ^ k * c k p)
  rw [hsplit, hfirst, hsecond]

private theorem seedExpPoly_contDiffOn
    (b ell : ArtinPrimitiveRoots.A1.Spec.Coord F → ℂ)
    (hb : ContDiffOn ℝ ∞ b (ArtinPrimitiveRoots.A1.Spec.posSet F))
    (hell : ContDiffOn ℝ ∞ ell (ArtinPrimitiveRoots.A1.Spec.posSet F))
    (n : ℕ) (v : Fin n → ArtinPrimitiveRoots.A1.Spec.Coord F) (a : ℂ) :
    ContDiffOn ℝ ∞ (seedExpPoly b ell n v a) (ArtinPrimitiveRoots.A1.Spec.posSet F) := by
  unfold seedExpPoly
  apply ContDiffOn.sum
  intro k hk
  exact contDiffOn_const.mul (seedExpCoeff_contDiffOn b ell hb hell n v k)

set_option maxHeartbeats 1000000 in
private theorem seedExpProfile_iteratedFDeriv
    (b ell : ArtinPrimitiveRoots.A1.Spec.Coord F → ℂ)
    (hb : ContDiffOn ℝ ∞ b (ArtinPrimitiveRoots.A1.Spec.posSet F))
    (hell : ContDiffOn ℝ ∞ ell (ArtinPrimitiveRoots.A1.Spec.posSet F))
    (a : ℂ) :
    ∀ n (v : Fin n → ArtinPrimitiveRoots.A1.Spec.Coord F)
      (p : ArtinPrimitiveRoots.A1.Spec.Coord F),
      p ∈ ArtinPrimitiveRoots.A1.Spec.posSet F →
      iteratedFDeriv ℝ n (fun x => b x * Complex.exp (a * ell x)) p v =
        Complex.exp (a * ell p) * seedExpPoly b ell n v a p := by
  intro n
  induction n with
  | zero =>
      intro v p hp
      simp [seedExpPoly, seedExpCoeff] <;> ring
  | succ n ih =>
      intro v p hp
      let f : ArtinPrimitiveRoots.A1.Spec.Coord F → ℂ :=
        fun x => b x * Complex.exp (a * ell x)
      have hf : ContDiffOn ℝ ∞ f (ArtinPrimitiveRoots.A1.Spec.posSet F) := by
        have harg : ContDiffOn ℝ ∞ (fun x => a * ell x)
            (ArtinPrimitiveRoots.A1.Spec.posSet F) := contDiffOn_const.mul hell
        have hexp : ContDiffOn ℝ ∞ (fun x => Complex.exp (a * ell x))
            (ArtinPrimitiveRoots.A1.Spec.posSet F) :=
          Complex.contDiff_exp.comp_contDiffOn harg
        exact hb.mul hexp
      have hfAt := hf.contDiffAt
        (ArtinPrimitiveRoots.Proofs.spec_seed_p.posSet_isOpen.mem_nhds hp)
      have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ n f) p :=
        hfAt.differentiableAt_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top n)
      have hnear :
          (fun x => iteratedFDeriv ℝ n f x (Fin.tail v)) =ᶠ[𝓝 p]
            (fun x => Complex.exp (a * ell x) *
              seedExpPoly b ell n (Fin.tail v) a x) := by
        filter_upwards [ArtinPrimitiveRoots.Proofs.spec_seed_p.posSet_isOpen.mem_nhds hp]
          with x hx
        exact ih (Fin.tail v) x hx
      have hpoly : ContDiffOn ℝ ∞ (seedExpPoly b ell n (Fin.tail v) a)
          (ArtinPrimitiveRoots.A1.Spec.posSet F) :=
        seedExpPoly_contDiffOn b ell hb hell n (Fin.tail v) a
      have hpolyAt := hpoly.contDiffAt
        (ArtinPrimitiveRoots.Proofs.spec_seed_p.posSet_isOpen.mem_nhds hp)
      have hargDiff : DifferentiableAt ℝ (fun x => a * ell x) p := by
        have hEllAt := hell.contDiffAt
          (ArtinPrimitiveRoots.Proofs.spec_seed_p.posSet_isOpen.mem_nhds hp)
        exact (differentiableAt_const a).mul (hEllAt.differentiableAt (by simp))
      have hexpDiff : DifferentiableAt ℝ (fun x => Complex.exp (a * ell x)) p :=
        Complex.differentiableAt_exp.comp p hargDiff
      have hmul := fderiv_fun_mul hexpDiff (hpolyAt.differentiableAt (by simp))
      rw [DifferentiableAt.iteratedFDeriv_succ_apply_left' hdiff,
        hnear.fderiv_eq, hmul]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [seedComplexExp_comp_fderiv ell hell a p hp (v 0)]
      rw [seedExpPoly_succ b ell hb hell n v a p hp]
      ring_nf

private theorem seedTerm_smooth_action
    (Γ : Subgroup SL(2,𝓞 F)) (σ bσ : SL(2,F))
    (τ : ℝ → ℝ) (hτ : ContDiff ℝ ∞ τ) (s : ℂ)
    (q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ) :
    ArtinPrimitiveRoots.A1.Spec.IsSmoothX F
      (fun z => ArtinPrimitiveRoots.A1.Spec.seedTerm F Γ σ τ s (bσ • z) q) := by
  let b : SL(2,F) := σ⁻¹ *
    ArtinPrimitiveRoots.A1.Spec.toSLF F ((q.out : Γ) : SL(2,𝓞 F))
    * bσ
  let a : ℂ := 1 + 2 * s
  let H : ArtinPrimitiveRoots.A1.Spec.Coord F → ℝ := fun p =>
    ArtinPrimitiveRoots.A1.Spec.normHeight F (b • ArtinPrimitiveRoots.A1.Spec.ptX F p)
  have hH : ContDiffOn ℝ ∞ H (ArtinPrimitiveRoots.A1.Spec.posSet F) :=
    seedHeight_action_smooth b
  have hHpos (p : ArtinPrimitiveRoots.A1.Spec.Coord F)
      (hp : p ∈ ArtinPrimitiveRoots.A1.Spec.posSet F) : 0 < H p := by
    dsimp [H]
    exact seedNormHeight_pos _
  have hlog : ContDiffOn ℝ ∞ (fun p => Real.log (H p))
      (ArtinPrimitiveRoots.A1.Spec.posSet F) :=
    hH.log fun p hp => (hHpos p hp).ne'
  have hprofile : ContDiffOn ℝ ∞
      (fun p => seedLogProfile τ a (Real.log (H p)))
      (ArtinPrimitiveRoots.A1.Spec.posSet F) :=
    (seedLogProfile_contDiff τ a hτ).comp_contDiffOn hlog
  have hAct (z : ArtinPrimitiveRoots.A1.Spec.X F) :
      b • z = σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • (bσ • z)) := by
    calc
      b • z = (σ⁻¹ * ArtinPrimitiveRoots.A1.Spec.toSLF F
          ((q.out : Γ) : SL(2,𝓞 F)) * bσ) • z := rfl
      _ = σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • (bσ • z)) := by
        rw [mul_smul, mul_smul]
        rfl
  change ContDiffOn ℝ ∞
    (fun p => ArtinPrimitiveRoots.A1.Spec.seedTerm F Γ σ τ s
      (bσ • ArtinPrimitiveRoots.A1.Spec.ptX F p) q)
    (ArtinPrimitiveRoots.A1.Spec.posSet F)
  apply hprofile.congr
  intro p hp
  have hEqHeight : H p = ArtinPrimitiveRoots.A1.Spec.normHeight F
      (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • (bσ • ArtinPrimitiveRoots.A1.Spec.ptX F p))) := by
    dsimp [H]
    rw [← hAct]
  unfold ArtinPrimitiveRoots.A1.Spec.seedTerm
  rw [← hEqHeight]
  simpa [a] using (seedLogProfile_log τ a (hHpos p hp)).symm

private theorem seedHighCosets_finite
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (σ : SL(2,F))
    (A : ℝ) (hA : 0 < A) (p : ArtinPrimitiveRoots.A1.Spec.Coord F)
    (hp : p ∈ ArtinPrimitiveRoots.A1.Spec.posSet F) :
    ∃ Q : Set (ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ), Q.Finite ∧
      (∀ q, A ≤ ArtinPrimitiveRoots.A1.Spec.normHeight F
        (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • ArtinPrimitiveRoots.A1.Spec.ptX F p)) → q ∈ Q) ∧
      ∃ U : Set (ArtinPrimitiveRoots.A1.Spec.Coord F), IsOpen U ∧ p ∈ U ∧
        U ⊆ ArtinPrimitiveRoots.A1.Spec.posSet F ∧
        ∀ x ∈ U, ∀ q ∉ Q,
          ArtinPrimitiveRoots.A1.Spec.normHeight F
            (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • ArtinPrimitiveRoots.A1.Spec.ptX F x)) ≤ A := by
  classical
  rcases ArtinPrimitiveRoots.A1.Spec.G1_h3_basics (F := F) with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hex⟩
  obtain ⟨e, he, hesym⟩ := hex
  obtain ⟨ε, hε, hεball⟩ := (Metric.isOpen_iff.mp
    (posSet_isOpen (F := F)) p hp)
  let r : ℝ := ε / 2
  let Kcoord : Set (ArtinPrimitiveRoots.A1.Spec.Coord F) := Metric.closedBall p r
  have hKcoord : IsCompact Kcoord := isCompact_closedBall p r
  have hKcoordPos : Kcoord ⊆ ArtinPrimitiveRoots.A1.Spec.posSet F := by
    intro p' hp'
    apply hεball
    have hclosed : dist p' p ≤ r := by simpa [Kcoord] using hp'
    have hrε : r < ε := by dsimp [r]; linarith
    exact Metric.mem_ball.mpr (lt_of_le_of_lt hclosed hrε)
  let fPos : Kcoord → {p : ArtinPrimitiveRoots.A1.Spec.Coord F //
      p ∈ ArtinPrimitiveRoots.A1.Spec.posSet F} := fun p' => ⟨p'.1, hKcoordPos p'.2⟩
  have hfPos : Continuous fPos :=
    Continuous.subtype_mk continuous_subtype_val (fun p' => hKcoordPos p'.2)
  have hmap : Continuous (fun p' : Kcoord =>
      ArtinPrimitiveRoots.A1.Spec.ptX F p'.1) := by
    exact e.continuous.comp hfPos |>.congr fun p' => by
      simpa [fPos] using he (fPos p')
  let Kx : Set (ArtinPrimitiveRoots.A1.Spec.X F) :=
    Set.range (fun p' : Kcoord => ArtinPrimitiveRoots.A1.Spec.ptX F p'.1)
  have hKx : IsCompact Kx := by
    change IsCompact (Set.range (fun p' : Kcoord =>
      ArtinPrimitiveRoots.A1.Spec.ptX F p'.1))
    exact isCompact_range hmap
  let Q : Set (ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ) :=
    {q | ∃ z ∈ Kx, A ≤ ArtinPrimitiveRoots.A1.Spec.normHeight F
      (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • z))}
  have hQ : Q.Finite :=
    (ArtinPrimitiveRoots.A1.Spec.R10_cusp_separation (F := F) Γ).2.2 σ Kx hKx A hA
  have hpKcoord : p ∈ Kcoord := by
    change dist p p ≤ r
    rw [dist_self]
    exact le_of_lt (by dsimp [r]; linarith [hε])
  have hpK : ArtinPrimitiveRoots.A1.Spec.ptX F p ∈ Kx := ⟨⟨p, hpKcoord⟩, rfl⟩
  let U : Set (ArtinPrimitiveRoots.A1.Spec.Coord F) := Metric.ball p r
  refine ⟨Q, hQ, ?_, U, Metric.isOpen_ball,
    Metric.mem_ball_self (by dsimp [r]; linarith [hε]), ?_, ?_⟩
  · intro q hhigh
    exact ⟨ArtinPrimitiveRoots.A1.Spec.ptX F p, hpK, hhigh⟩
  · intro x hx
    apply hKcoordPos
    change x ∈ Metric.closedBall p r
    exact Metric.mem_closedBall.mpr (le_of_lt hx)
  ·
    intro x hx q hq
    have hxK : x ∈ Kcoord := by
      change x ∈ Metric.closedBall p r
      exact Metric.mem_closedBall.mpr (le_of_lt hx)
    have hpt : ArtinPrimitiveRoots.A1.Spec.ptX F x ∈ Kx := ⟨⟨x, hxK⟩, rfl⟩
    have hnot : ¬ A ≤ ArtinPrimitiveRoots.A1.Spec.normHeight F
        (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • ArtinPrimitiveRoots.A1.Spec.ptX F x)) := by
      intro hhigh
      exact hq ⟨ArtinPrimitiveRoots.A1.Spec.ptX F x, hpt, hhigh⟩
    exact le_of_not_ge hnot

private theorem eisSeed_local_sum
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (σ : SL(2,F))
    (A : ℝ) (τ : ℝ → ℝ) (hτ : ArtinPrimitiveRoots.A1.Spec.IsCuspCutoff A τ)
    (hA : 0 < A) (s : ℂ)
    (p : ArtinPrimitiveRoots.A1.Spec.Coord F)
    (hp : p ∈ ArtinPrimitiveRoots.A1.Spec.posSet F) :
    ∃ T : Finset (ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ),
      ∃ U : Set (ArtinPrimitiveRoots.A1.Spec.Coord F), IsOpen U ∧ p ∈ U ∧
        U ⊆ ArtinPrimitiveRoots.A1.Spec.posSet F ∧
        (∀ q, A ≤ ArtinPrimitiveRoots.A1.Spec.normHeight F
          (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • ArtinPrimitiveRoots.A1.Spec.ptX F p)) → q ∈ T) ∧
        ∀ x ∈ U,
          ArtinPrimitiveRoots.A1.Spec.eisSeed F Γ σ τ s
              (ArtinPrimitiveRoots.A1.Spec.ptX F x) =
            ∑ q ∈ T, ArtinPrimitiveRoots.A1.Spec.seedTerm F Γ σ τ s
              (ArtinPrimitiveRoots.A1.Spec.ptX F x) q := by
  classical
  obtain ⟨Q, hQ, hQcenter, U, hU, hpU, hUpos, hzero⟩ :=
    seedHighCosets_finite Γ σ A hA p hp
  let T := hQ.toFinset
  refine ⟨T, ⟨U, ?_⟩⟩
  have hTcenter : ∀ q, A ≤ ArtinPrimitiveRoots.A1.Spec.normHeight F
      (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • ArtinPrimitiveRoots.A1.Spec.ptX F p)) → q ∈ T := by
    intro q hhigh
    have hqQ : q ∈ Q := hQcenter q hhigh
    simpa [T] using hqQ
  have hlocal : ∀ x ∈ U,
      ArtinPrimitiveRoots.A1.Spec.eisSeed F Γ σ τ s
          (ArtinPrimitiveRoots.A1.Spec.ptX F x) =
        ∑ q ∈ T, ArtinPrimitiveRoots.A1.Spec.seedTerm F Γ σ τ s
          (ArtinPrimitiveRoots.A1.Spec.ptX F x) q := by
    intro x hx
    have hzero' : ∀ q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ,
        q ∉ T → ArtinPrimitiveRoots.A1.Spec.seedTerm F Γ σ τ s
          (ArtinPrimitiveRoots.A1.Spec.ptX F x) q = 0 := by
      intro q hq
      have hqQ : q ∉ Q := by simpa [T] using hq
      dsimp [ArtinPrimitiveRoots.A1.Spec.seedTerm]
      have hh := hzero x hx q hqQ
      rw [hτ.2.2.1 _ hh]
      simp
    change (∑' q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ,
        ArtinPrimitiveRoots.A1.Spec.seedTerm F Γ σ τ s
          (ArtinPrimitiveRoots.A1.Spec.ptX F x) q) =
      ∑ q ∈ T, ArtinPrimitiveRoots.A1.Spec.seedTerm F Γ σ τ s
        (ArtinPrimitiveRoots.A1.Spec.ptX F x) q
    exact tsum_eq_sum (s := T) hzero'
  exact ⟨hU, ⟨hpU, ⟨hUpos, ⟨hTcenter, hlocal⟩⟩⟩⟩

private theorem eisSeed_isSmooth
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (σ : SL(2,F))
    (A : ℝ) (hA : 0 < A) (τ : ℝ → ℝ)
    (hτ : ArtinPrimitiveRoots.A1.Spec.IsCuspCutoff A τ) (s : ℂ) :
    ArtinPrimitiveRoots.A1.Spec.IsSmoothX F
      (ArtinPrimitiveRoots.A1.Spec.eisSeed F Γ σ τ s) := by
  change ContDiffOn ℝ ∞
    (fun p => ArtinPrimitiveRoots.A1.Spec.eisSeed F Γ σ τ s
      (ArtinPrimitiveRoots.A1.Spec.ptX F p)) (ArtinPrimitiveRoots.A1.Spec.posSet F)
  intro p hp
  obtain ⟨T, hT⟩ := eisSeed_local_sum Γ σ A τ hτ hA s p hp
  obtain ⟨U, hconj⟩ := hT
  rcases hconj with ⟨hU, hconj⟩
  rcases hconj with ⟨hpU, hconj⟩
  rcases hconj with ⟨hUpos, hconj⟩
  rcases hconj with ⟨_, hlocal⟩
  have hterm (q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ) :
      ContDiffAt ℝ ∞ (fun x => ArtinPrimitiveRoots.A1.Spec.seedTerm F Γ σ τ s
        (ArtinPrimitiveRoots.A1.Spec.ptX F x) q) p := by
    have h := seedTerm_smooth_action Γ σ 1 τ hτ.1 s q
    change ContDiffOn ℝ ∞
      (fun x => ArtinPrimitiveRoots.A1.Spec.seedTerm F Γ σ τ s
        (1 • ArtinPrimitiveRoots.A1.Spec.ptX F x) q)
      (ArtinPrimitiveRoots.A1.Spec.posSet F) at h
    have h' : ContDiffOn ℝ ∞
        (fun x => ArtinPrimitiveRoots.A1.Spec.seedTerm F Γ σ τ s
          (ArtinPrimitiveRoots.A1.Spec.ptX F x) q)
        (ArtinPrimitiveRoots.A1.Spec.posSet F) := by
      simpa using h
    exact (h' p hp).contDiffAt
      (ArtinPrimitiveRoots.Proofs.spec_seed_p.posSet_isOpen.mem_nhds hp)
  have hsum : ContDiffAt ℝ ∞
      (fun x => ∑ q ∈ T, ArtinPrimitiveRoots.A1.Spec.seedTerm F Γ σ τ s
        (ArtinPrimitiveRoots.A1.Spec.ptX F x) q) p := by
    apply ContDiffAt.sum
    intro q hq
    exact hterm q
  have hEq : (fun x => ArtinPrimitiveRoots.A1.Spec.eisSeed F Γ σ τ s
      (ArtinPrimitiveRoots.A1.Spec.ptX F x)) =ᶠ[𝓝 p]
      (fun x => ∑ q ∈ T, ArtinPrimitiveRoots.A1.Spec.seedTerm F Γ σ τ s
        (ArtinPrimitiveRoots.A1.Spec.ptX F x) q) := by
    filter_upwards [hU.mem_nhds hpU] with x hx
    exact hlocal x hx
  exact hsum.congr_of_eventuallyEq hEq |>.contDiffWithinAt

open ArtinPrimitiveRoots.A1.Spec
open Submodule

private lemma seed_cusp_height_rightRel (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (γ γ' : Γ)
    (h : QuotientGroup.rightRel (cuspStab F Γ σ) γ γ') (z : X F) :
    normHeight F (σ⁻¹ • ((γ' : Γ) • z)) =
      normHeight F (σ⁻¹ • ((γ : Γ) • z)) := by
  have hstab : γ' * γ⁻¹ ∈ cuspStab F Γ σ := QuotientGroup.rightRel_apply.mp h
  have htri := hstab
  simp only [cuspStab, Subgroup.mem_comap, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at htri
  let δ : Γ := γ' * γ⁻¹
  have hγ' : (γ' : Γ) • z = toSLF F ((γ' : Γ) : SL(2,𝓞 F)) • z := rfl
  have hγ : (γ : Γ) • z = toSLF F ((γ : Γ) : SL(2,𝓞 F)) • z := rfl
  have hgroup : γ' = δ * γ := by
    dsimp [δ]
    group
  have hcoerce : ((δ * γ : Γ) : SL(2,𝓞 F)) =
      (δ : SL(2,𝓞 F)) * (γ : SL(2,𝓞 F)) := rfl
  have hoperator :
      σ⁻¹ * toSLF F ((γ' : Γ) : SL(2,𝓞 F)) =
        (σ⁻¹ * toSLF F (δ : SL(2,𝓞 F)) * σ) *
          (σ⁻¹ * toSLF F ((γ : Γ) : SL(2,𝓞 F))) := by
    calc
      σ⁻¹ * toSLF F ((γ' : Γ) : SL(2,𝓞 F)) =
          σ⁻¹ * toSLF F ((δ * γ : Γ) : SL(2,𝓞 F)) :=
        congrArg (fun x : Γ => σ⁻¹ * toSLF F (x : SL(2,𝓞 F))) hgroup
      _ = σ⁻¹ * toSLF F ((δ : SL(2,𝓞 F)) * (γ : SL(2,𝓞 F))) := by rw [hcoerce]
      _ = σ⁻¹ * (toSLF F (δ : SL(2,𝓞 F)) *
          toSLF F ((γ : Γ) : SL(2,𝓞 F))) := by rw [map_mul]
      _ = (σ⁻¹ * toSLF F (δ : SL(2,𝓞 F)) * σ) *
          (σ⁻¹ * toSLF F ((γ : Γ) : SL(2,𝓞 F))) := by group
  have hmove :
      σ⁻¹ • ((γ' : Γ) • z) =
        (σ⁻¹ * toSLF F ((γ' * γ⁻¹ : Γ) : SL(2,𝓞 F)) * σ) •
          (σ⁻¹ • ((γ : Γ) • z)) := by
    rw [hγ', hγ]
    simp only [smul_smul]
    exact congrArg (fun g : SL(2,F) => g • z) hoperator
  rw [hmove]
  exact (G2_x_action (F := F)).2.2.1 ((δ : Γ) : SL(2,𝓞 F)) σ htri |>.2 _

private lemma seed_rightRel_mul_right (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (δ : Γ) {x y : Γ} (h : QuotientGroup.rightRel (cuspStab F Γ σ) x y) :
    QuotientGroup.rightRel (cuspStab F Γ σ) (x * δ) (y * δ) := by
  apply QuotientGroup.rightRel_apply.mpr
  have h' := QuotientGroup.rightRel_apply.mp h
  simpa [_root_.mul_inv_rev, mul_assoc] using h'

private def seed_rightMulEquiv (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F)) (δ : Γ) :
    CuspCosets F Γ σ ≃ CuspCosets F Γ σ where
  toFun := Quotient.map (fun x : Γ => x * δ)
    (fun {_ _} h => seed_rightRel_mul_right Γ σ δ h)
  invFun := Quotient.map (fun x : Γ => x * δ⁻¹)
    (fun {_ _} h => seed_rightRel_mul_right Γ σ δ⁻¹ h)
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    simp [mul_assoc]
  right_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    simp [mul_assoc]

private theorem eisSeed_isGammaInvariant
    (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F)) (τ : ℝ → ℝ) (s : ℂ) :
    IsGammaInvariant F Γ (eisSeed F Γ σ τ s) := by
  intro γ hγ z
  let δ : Γ := ⟨γ, hγ⟩
  let e : CuspCosets F Γ σ ≃ CuspCosets F Γ σ := seed_rightMulEquiv Γ σ δ
  have hmap (q : CuspCosets F Γ σ) :
      e q = Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ σ))
        ((q.out : Γ) * δ) := by
    calc
      e q = e (Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ σ)) q.out) :=
        congrArg e (Quotient.out_eq q).symm
      _ = Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ σ)) (q.out * δ) := by
        change Quotient.map (fun x : Γ => x * δ)
          (fun {_ _} h => seed_rightRel_mul_right Γ σ δ h)
          (Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ σ)) q.out) = _
        rw [Quotient.map_mk]
  have hrepRel (q : CuspCosets F Γ σ) :
      QuotientGroup.rightRel (cuspStab F Γ σ) (e q).out ((q.out : Γ) * δ) := by
    have hout : (e q).out =
        (Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ σ)) ((q.out : Γ) * δ)).out :=
      congrArg Quotient.out (hmap q)
    rw [hout]
    exact Quotient.mk_out ((q.out : Γ) * δ)
  have hterm (q : CuspCosets F Γ σ) :
      seedTerm F Γ σ τ s (δ • z) q = seedTerm F Γ σ τ s z (e q) := by
    have hheight :
        normHeight F (σ⁻¹ • ((q.out : Γ) • (δ • z))) =
          normHeight F (σ⁻¹ • ((e q).out • z)) := by
      calc
        normHeight F (σ⁻¹ • ((q.out : Γ) • (δ • z))) =
            normHeight F (σ⁻¹ • (((q.out : Γ) * δ) • z)) := by
              congr 2
              exact smul_smul (q.out : Γ) δ z
        _ = normHeight F (σ⁻¹ • ((e q).out • z)) :=
          seed_cusp_height_rightRel Γ σ (e q).out ((q.out : Γ) * δ) (hrepRel q) z
    dsimp [seedTerm]
    exact congrArg (fun t : ℝ => (τ t : ℂ) * (t : ℂ) ^ (1 + 2 * s)) hheight
  unfold eisSeed
  calc
    (∑' q : CuspCosets F Γ σ, seedTerm F Γ σ τ s (δ • z) q) =
        ∑' q : CuspCosets F Γ σ, seedTerm F Γ σ τ s z (e q) := tsum_congr hterm
    _ = ∑' q : CuspCosets F Γ σ, seedTerm F Γ σ τ s z q :=
      e.tsum_eq (fun q => seedTerm F Γ σ τ s z q)

private theorem eisSeedDefect_isGammaInvariant
    (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F)) (τ : ℝ → ℝ) (s : ℂ)
    (hsm : IsSmoothX F (eisSeed F Γ σ τ s))
    (hinv : IsGammaInvariant F Γ (eisSeed F Γ σ τ s)) :
    IsGammaInvariant F Γ (eisSeedDefect F Γ σ τ s) := by
  intro γ hγ z
  let g : InfinitePlace F → SL(2,ℂ) := toInf F (toSLF F γ)
  have hAct (x : X F) : actAtPlaces F g x = (γ : SL(2,𝓞 F)) • x := by
    funext w
    rfl
  have hLap (w : InfinitePlace F) :
      partialLap F w (eisSeed F Γ σ τ s) ((γ : SL(2,𝓞 F)) • z) =
        partialLap F w (eisSeed F Γ σ τ s) z := by
    have hcomm := g5PartialLap_action_pointwise g
      (eisSeed F Γ σ τ s) hsm w z
    have hfun : (fun x => eisSeed F Γ σ τ s (actAtPlaces F g x)) =
        eisSeed F Γ σ τ s := by
      funext x
      rw [hAct, hinv γ hγ x]
    calc
      _ = partialLap F w (eisSeed F Γ σ τ s) (actAtPlaces F g z) := by
        rw [hAct]
      _ = partialLap F w (fun x => eisSeed F Γ σ τ s (actAtPlaces F g x)) z := hcomm.symm
      _ = partialLap F w (eisSeed F Γ σ τ s) z := by rw [hfun]
  have htotal : totalLap F (eisSeed F Γ σ τ s)
      ((γ : SL(2,𝓞 F)) • z) = totalLap F (eisSeed F Γ σ τ s) z := by
    unfold totalLap
    apply Finset.sum_congr rfl
    intro w hw
    exact hLap w
  simp [eisSeedDefect, htotal, hinv γ hγ z]

private def seedProfile (τ : ℝ → ℝ) (a : ℂ) (δ t : ℝ) : ℂ :=
  (τ t : ℂ) * complexPowerProfile a δ t

private theorem seedProfile_contDiff (τ : ℝ → ℝ) (a : ℂ) (δ : ℝ)
    (hτ : ContDiff ℝ ∞ τ) (hδ : 0 < δ) :
    ContDiff ℝ ∞ (seedProfile τ a δ) := by
  have hτc : ContDiff ℝ ∞ (fun t : ℝ => (τ t : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hτ
  exact hτc.mul (complexPowerProfile_smooth a δ hδ)

private theorem complexPowerProfile_deriv_all (a : ℂ) (δ : ℝ) (hδ : 0 < δ)
    (t : ℝ) (ht : δ < t) :
    deriv (complexPowerProfile a δ) t = a * (t : ℂ) ^ (a - 1) := by
  by_cases ha : a = 0
  · subst a
    have heq : complexPowerProfile 0 δ =ᶠ[𝓝 t] fun _ : ℝ => (1 : ℂ) := by
      filter_upwards [complexPowerProfile_eq_eventually_cpow 0 δ hδ t ht] with y hy
      simp [hy]
    rw [heq.deriv_eq]
    simp
  · exact complexPowerProfile_deriv a δ hδ t ht ha

private theorem complexPowerProfile_deriv2_all (a : ℂ) (δ : ℝ) (hδ : 0 < δ)
    (t : ℝ) (ht : δ < t) :
    deriv (deriv (complexPowerProfile a δ)) t =
      a * (a - 1) * (t : ℂ) ^ (a - 2) := by
  by_cases ha0 : a = 0
  · subst a
    have heq : complexPowerProfile 0 δ =ᶠ[𝓝 t] fun _ : ℝ => (1 : ℂ) := by
      filter_upwards [complexPowerProfile_eq_eventually_cpow 0 δ hδ t ht] with y hy
      simp [hy]
    have heq' := heq.deriv
    rw [heq'.deriv_eq]
    simp
  · by_cases ha1 : a = 1
    · subst a
      have heq : complexPowerProfile 1 δ =ᶠ[𝓝 t] fun y : ℝ => (y : ℂ) := by
        filter_upwards [complexPowerProfile_eq_eventually_cpow 1 δ hδ t ht] with y hy
        simp [hy]
      have heq' : deriv (complexPowerProfile 1 δ) =ᶠ[𝓝 t] fun _ : ℝ => (1 : ℂ) := by
        filter_upwards [isOpen_Ioi.mem_nhds ht] with y hy
        rw [complexPowerProfile_deriv_all 1 δ hδ y hy]
        simp
      rw [heq'.deriv_eq]
      simp
    · have ha1' : a - 1 ≠ 0 := by
        intro h
        have h' : a = 1 := by
          have hh := congrArg (fun x : ℂ => x + 1) h
          simpa using hh
        exact ha1 h'
      exact complexPowerProfile_deriv2 a δ hδ t ht ha0 ha1'

private theorem seedProfile_derivatives (τ : ℝ → ℝ) (a : ℂ) (δ : ℝ)
    (hτ : ContDiff ℝ ∞ τ) (hδ : 0 < δ) (t : ℝ) (ht : δ < t) :
    deriv (seedProfile τ a δ) t =
        deriv (fun y : ℝ => (τ y : ℂ)) t * (t : ℂ) ^ a +
          (τ t : ℂ) * (a * (t : ℂ) ^ (a - 1)) ∧
    deriv (deriv (seedProfile τ a δ)) t =
        deriv (deriv (fun y : ℝ => (τ y : ℂ))) t * (t : ℂ) ^ a +
          2 * deriv (fun y : ℝ => (τ y : ℂ)) t * (a * (t : ℂ) ^ (a - 1)) +
          (τ t : ℂ) * (a * (a - 1) * (t : ℂ) ^ (a - 2)) := by
  let τc : ℝ → ℂ := fun y => (τ y : ℂ)
  let P : ℝ → ℂ := complexPowerProfile a δ
  have hτc : ContDiff ℝ ∞ τc := by
    exact Complex.ofRealCLM.contDiff.comp hτ
  have hP : ContDiff ℝ ∞ P := complexPowerProfile_smooth a δ hδ
  have hτc' : ContDiff ℝ ∞ (deriv τc) := hτc.deriv'
  have hP' : ContDiff ℝ ∞ (deriv P) := hP.deriv'
  have hfirst : deriv (seedProfile τ a δ) = fun y => deriv τc y * P y + τc y * deriv P y := by
    funext y
    dsimp [seedProfile, τc, P]
    exact deriv_mul (hτc.differentiable (by simp) y) (hP.differentiable (by simp) y)
  have hsecond : deriv (deriv (seedProfile τ a δ)) = fun y =>
      deriv (deriv τc) y * P y + deriv τc y * deriv P y +
        (deriv τc y * deriv P y + τc y * deriv (deriv P) y) := by
    rw [hfirst]
    funext y
    have hleft : DifferentiableAt ℝ (fun v => deriv τc v * P v) y :=
      (hτc'.differentiable (by simp) y).mul (hP.differentiable (by simp) y)
    have hright : DifferentiableAt ℝ (fun v => τc v * deriv P v) y :=
      (hτc.differentiable (by simp) y).mul (hP'.differentiable (by simp) y)
    change deriv (fun v => deriv τc v * P v + τc v * deriv P v) y = _
    rw [deriv_fun_add hleft hright,
      deriv_fun_mul (hτc'.differentiable (by simp) y) (hP.differentiable (by simp) y),
      deriv_fun_mul (hτc.differentiable (by simp) y) (hP'.differentiable (by simp) y)]
  constructor
  · rw [hfirst]
    dsimp [τc, P]
    rw [complexPowerProfile_eq_cpow a δ hδ t (le_of_lt ht),
      complexPowerProfile_deriv_all a δ hδ t ht]
  · rw [hsecond]
    dsimp [τc, P]
    rw [complexPowerProfile_eq_cpow a δ hδ t (le_of_lt ht),
      complexPowerProfile_deriv_all a δ hδ t ht,
      complexPowerProfile_deriv2_all a δ hδ t ht]
    ring

private theorem seedTerm_partialLap_action
    (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F)) (τ : ℝ → ℝ)
    (hτ : ContDiff ℝ ∞ τ) (s : ℂ)
    (q : CuspCosets F Γ σ) (z : X F) (w : InfinitePlace F) :
    let b : SL(2,F) := σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F))
    let a : ℂ := 1 + 2 * s
    let N : ℝ := normHeight F (b • z)
    let δ : ℝ := N / 2
    let ψ : ℝ → ℂ := seedProfile τ a δ
    partialLap F w (fun x => seedTerm F Γ σ τ s x q) z =
      ((N : ℝ) : ℂ) * deriv ψ N - ((N : ℝ) : ℂ) ^ 2 * deriv (deriv ψ) N := by
  let b : SL(2,F) := σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F))
  let a : ℂ := 1 + 2 * s
  let N : ℝ := normHeight F (b • z)
  let δ : ℝ := N / 2
  let ψ : ℝ → ℂ := seedProfile τ a δ
  have hN : 0 < N := by
    dsimp [N]
    exact seedNormHeight_pos _
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδN : δ < N := by dsimp [δ]; linarith
  let p : Coord F := coordsX F z
  have hp : p ∈ posSet F := by
    intro v
    change 0 < height (z v)
    rw [height_eq_hyperbolicHeight]
    exact OAI.CubicEisenstein.hyperbolicHeight_pos (z v)
  have hpt : ptX F p = z := by
    rcases G1_h3_basics (F := F) with
      ⟨_, _, _, _, _, _, _, hpt, _, _, _, _⟩
    exact hpt z
  have hbAct (x : X F) :
      b • x = σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • x) := by
    calc
      b • x = (σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F))) • x := rfl
      _ = σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • x) := by
        rw [mul_smul]
        rfl
  let H : Coord F → ℝ := fun p' => normHeight F (b • ptX F p')
  have hH : ContDiffOn ℝ ∞ H (posSet F) := seedHeight_action_smooth b
  have hHp : H p = N := by
    dsimp [H, N]
    rw [hpt]
  have hHcont : ContinuousAt H p :=
    hH.continuousOn.continuousAt (posSet_isOpen.mem_nhds hp)
  have hHabove : ∀ᶠ p' in 𝓝 p, δ < H p' := by
    exact hHcont.eventually (isOpen_Ioi.mem_nhds (hHp ▸ hδN))
  have hcoordEq :
      (fun p' => seedTerm F Γ σ τ s (ptX F p') q) =ᶠ[𝓝 p]
        (fun p' => ψ (H p')) := by
    filter_upwards [hHabove] with p' hp'
    have hheight : normHeight F
        (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • ptX F p')) = H p' := by
      dsimp [H]
      rw [← hbAct]
    dsimp [seedTerm, ψ, seedProfile]
    calc
      (τ (normHeight F (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • ptX F p'))) : ℂ) *
          (normHeight F (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • ptX F p')) : ℂ) ^ a =
        (τ (H p') : ℂ) * (H p' : ℂ) ^ a := congrArg
          (fun t : ℝ => (τ t : ℂ) * (t : ℂ) ^ a) hheight
      _ = (τ (H p') : ℂ) * complexPowerProfile a δ (H p') := by
        rw [complexPowerProfile_eq_cpow a δ hδ (H p') (le_of_lt hp')]
  have hprofile : ContDiffOn ℝ ∞ (fun p' => ψ (H p')) (posSet F) :=
    (seedProfile_contDiff τ a δ hτ hδ).comp_contDiffOn hH
  have hpartial := partialLap_from_chart
    (fun x => seedTerm F Γ σ τ s x q) (fun p' => ψ (H p')) p hp w hcoordEq
  have hother := partialLap_from_chart
    (fun x => ψ (normHeight F (b • x))) (fun p' => ψ (H p')) p hp w
    (Filter.Eventually.of_forall fun _ => rfl)
  have hbase : IsSmoothX F (fun x => ψ (normHeight F x)) := by
    change ContDiffOn ℝ ∞
      (fun p' => ψ (normHeight F (ptX F p'))) (posSet F)
    exact (seedProfile_contDiff τ a δ hτ hδ).comp_contDiffOn normHeight_real_smooth
  have hAct (x : X F) : actAtPlaces F (toInf F b) x = b • x := by
    funext v
    rfl
  have hcov := g5PartialLap_action_pointwise (toInf F b)
    (fun x => ψ (normHeight F x)) hbase w z
  have hcov' : partialLap F w (fun x => ψ (normHeight F (b • x))) z =
      partialLap F w (fun x => ψ (normHeight F x)) (b • z) := by
    simpa only [hAct] using hcov
  have hrad := partialLap_normHeight_complexProfile_at ψ
    (seedProfile_contDiff τ a δ hτ hδ) (b • z) w
  calc
    partialLap F w (fun x => seedTerm F Γ σ τ s x q) z =
        partialLap F w (fun x => seedTerm F Γ σ τ s x q) (ptX F p) := by rw [hpt]
    _ = coordinateLap (fun p' => ψ (H p')) p w := hpartial
    _ = partialLap F w (fun x => ψ (normHeight F (b • x))) (ptX F p) := hother.symm
    _ = partialLap F w (fun x => ψ (normHeight F (b • x))) z := by rw [hpt]
    _ = partialLap F w (fun x => ψ (normHeight F x)) (b • z) := hcov'
    _ = ((N : ℝ) : ℂ) * deriv ψ N - ((N : ℝ) : ℂ) ^ 2 * deriv (deriv ψ) N := by
      simpa [ψ, N] using hrad

private theorem seedTerm_lap_defect
    (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F)) (τ : ℝ → ℝ)
    (hτ : ContDiff ℝ ∞ τ) (s : ℂ)
    (q : CuspCosets F Γ σ) (z : X F) :
    let h := normHeight F (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • z))
    totalLap F (fun x => seedTerm F Γ σ τ s x q) z -
        spectralParameter F s * seedTerm F Γ σ τ s z q =
      -(placeCount F : ℂ) *
        ((((h : ℝ) : ℂ) ^ 2 * deriv (deriv (fun t : ℝ => (τ t : ℂ))) h +
          (1 + 4 * s) * ((h : ℝ) : ℂ) * deriv (fun t : ℝ => (τ t : ℂ)) h) *
          ((h : ℝ) : ℂ) ^ (1 + 2 * s)) := by
  let b : SL(2,F) := σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F))
  let a : ℂ := 1 + 2 * s
  let h : ℝ := normHeight F (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • z))
  let N : ℝ := normHeight F (b • z)
  let δ : ℝ := N / 2
  let ψ : ℝ → ℂ := seedProfile τ a δ
  have hh : h = N := by
    dsimp [h, N, b]
    rw [show σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • z) =
      (σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F))) • z by
        rw [mul_smul]
        rfl]
  have hh' : normHeight F
      (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • z)) = N := by
    simpa [h] using hh
  have hN : 0 < N := by dsimp [N]; exact seedNormHeight_pos _
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδN : δ < N := by dsimp [δ]; linarith
  have hvalue : seedTerm F Γ σ τ s z q = (τ N : ℂ) * (N : ℂ) ^ a := by
    dsimp [seedTerm, a]
    rw [← hh]
  have hpartial (w : InfinitePlace F) :
      partialLap F w (fun x => seedTerm F Γ σ τ s x q) z =
        ((N : ℝ) : ℂ) * deriv ψ N - ((N : ℝ) : ℂ) ^ 2 * deriv (deriv ψ) N := by
    simpa [N, ψ, b, a] using seedTerm_partialLap_action Γ σ τ hτ s q z w
  have htotal : totalLap F (fun x => seedTerm F Γ σ τ s x q) z =
      (placeCount F : ℂ) *
        (((N : ℝ) : ℂ) * deriv ψ N - ((N : ℝ) : ℂ) ^ 2 * deriv (deriv ψ) N) := by
    unfold totalLap
    simp_rw [hpartial]
    simp [placeCount, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  obtain ⟨hψ', hψ''⟩ := seedProfile_derivatives τ a δ hτ hδ N hδN
  have hpow1 : ((N : ℝ) : ℂ) * ((N : ℝ) : ℂ) ^ (a - 1) =
      ((N : ℝ) : ℂ) ^ a := by
    calc
      _ = ((N : ℝ) : ℂ) ^ (a - 1) * ((N : ℝ) : ℂ) := by ring
      _ = ((N : ℝ) : ℂ) ^ (a - 1) * ((N : ℝ) : ℂ) ^ (1 : ℂ) := by simp
      _ = ((N : ℝ) : ℂ) ^ ((a - 1) + 1) :=
        (Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hN.ne')).symm
      _ = ((N : ℝ) : ℂ) ^ a := by congr 1 <;> ring
  have hpow2 : ((N : ℝ) : ℂ) ^ 2 * ((N : ℝ) : ℂ) ^ (a - 2) =
      ((N : ℝ) : ℂ) ^ a := by
    calc
      _ = ((N : ℝ) : ℂ) ^ (2 : ℂ) * ((N : ℝ) : ℂ) ^ (a - 2) := by
        rw [← Complex.cpow_two]
      _ = ((N : ℝ) : ℂ) ^ ((2 : ℂ) + (a - 2)) :=
        (Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hN.ne')).symm
      _ = ((N : ℝ) : ℂ) ^ a := by congr 1 <;> ring
  have hcoef : a * (2 - a) = 1 - 4 * s ^ 2 := by dsimp [a]; ring
  have hcoef' : 2 * a - 1 = 1 + 4 * s := by dsimp [a]; ring
  have hcoefU : a - a * (a - 1) = 1 - 4 * s ^ 2 := by
    calc
      _ = a * (2 - a) := by ring
      _ = _ := hcoef
  have hcoefV : 1 - 2 * a + (1 + 4 * s) = 0 := by
    rw [← hcoef']
    ring
  let x : ℂ := (N : ℂ)
  let u : ℂ := (τ N : ℂ)
  let u₁ : ℂ := deriv (fun y : ℝ => (τ y : ℂ)) N
  let u₂ : ℂ := deriv (deriv (fun y : ℝ => (τ y : ℂ))) N
  have hmon1 : x * (u * (a * x ^ (a - 1))) = u * a * x ^ a := by
    calc
      _ = u * a * (x * x ^ (a - 1)) := by ring
      _ = u * a * x ^ a := by rw [hpow1]
  have hmon2 : x ^ 2 * (u * (a * (a - 1) * x ^ (a - 2))) =
      u * a * (a - 1) * x ^ a := by
    calc
      _ = u * a * (a - 1) * (x ^ 2 * x ^ (a - 2)) := by ring
      _ = u * a * (a - 1) * x ^ a := by rw [hpow2]
  have hmon3 : x ^ 2 * (2 * u₁ * (a * x ^ (a - 1))) =
      2 * u₁ * a * x * x ^ a := by
    calc
      _ = 2 * u₁ * a * (x * (x * x ^ (a - 1))) := by ring
      _ = 2 * u₁ * a * x * x ^ a := by
        rw [hpow1]
        all_goals ring
  dsimp [h]
  rw [hh']
  rw [htotal, hvalue, spectralParameter, hψ', hψ'']
  change (placeCount F : ℂ) *
      (x * (u₁ * x ^ a + u * (a * x ^ (a - 1))) -
        x ^ 2 * (u₂ * x ^ a + 2 * u₁ * (a * x ^ (a - 1)) +
          u * (a * (a - 1) * x ^ (a - 2)))) -
      (placeCount F : ℂ) * (1 - 4 * s ^ 2) * (u * x ^ a) =
    -(placeCount F : ℂ) *
      ((x ^ 2 * u₂ + (1 + 4 * s) * x * u₁) * x ^ a)
  simp only [mul_add]
  rw [hmon1, hmon2, hmon3]
  linear_combination (placeCount F : ℂ) * (u * x ^ a) * hcoefU +
    (placeCount F : ℂ) * (x * u₁ * x ^ a) * hcoefV

private theorem seedCutoffDeriv_zero_below (A : ℝ) (τ : ℝ → ℝ)
    (hτ : IsCuspCutoff A τ) (t : ℝ) (ht : t < A) :
    deriv (fun u : ℝ => (τ u : ℂ)) t = 0 := by
  have heq : (fun u : ℝ => (τ u : ℂ)) =ᶠ[𝓝 t] fun _ => (0 : ℂ) := by
    filter_upwards [isOpen_Iio.mem_nhds ht] with u hu
    simp [hτ.2.2.1 u hu.le]
  rw [heq.deriv_eq]
  simp

private theorem seedCutoffDeriv2_zero_below (A : ℝ) (τ : ℝ → ℝ)
    (hτ : IsCuspCutoff A τ) (t : ℝ) (ht : t < A) :
    deriv (deriv (fun u : ℝ => (τ u : ℂ))) t = 0 := by
  have heq : (fun u : ℝ => (τ u : ℂ)) =ᶠ[𝓝 t] fun _ => (0 : ℂ) := by
    filter_upwards [isOpen_Iio.mem_nhds ht] with u hu
    simp [hτ.2.2.1 u hu.le]
  have heq' := heq.deriv
  rw [heq'.deriv_eq]
  simp

private theorem seedCutoffDeriv_zero_above (A : ℝ) (τ : ℝ → ℝ)
    (hτ : IsCuspCutoff A τ) (t : ℝ) (ht : 2 * A < t) :
    deriv (fun u : ℝ => (τ u : ℂ)) t = 0 := by
  have heq : (fun u : ℝ => (τ u : ℂ)) =ᶠ[𝓝 t] fun _ => (1 : ℂ) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with u hu
    simp [hτ.2.2.2 u hu.le]
  rw [heq.deriv_eq]
  simp

private theorem seedCutoffDeriv2_zero_above (A : ℝ) (τ : ℝ → ℝ)
    (hτ : IsCuspCutoff A τ) (t : ℝ) (ht : 2 * A < t) :
    deriv (deriv (fun u : ℝ => (τ u : ℂ))) t = 0 := by
  have heq : (fun u : ℝ => (τ u : ℂ)) =ᶠ[𝓝 t] fun _ => (1 : ℂ) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with u hu
    simp [hτ.2.2.2 u hu.le]
  have heq' := heq.deriv
  rw [heq'.deriv_eq]
  simp

private theorem seedTermDefect_height_band
    (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F)) (A : ℝ) (τ : ℝ → ℝ)
    (hτ : IsCuspCutoff A τ) (s : ℂ)
    (q : CuspCosets F Γ σ) (z : X F)
    (hneq : totalLap F (fun x => seedTerm F Γ σ τ s x q) z -
        spectralParameter F s * seedTerm F Γ σ τ s z q ≠ 0) :
    A ≤ normHeight F (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • z)) ∧
      normHeight F (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • z)) ≤ 2 * A := by
  let t := normHeight F (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • z))
  by_cases htlo : t < A
  · have hz := seedTerm_lap_defect Γ σ τ hτ.1 s q z
    have hd1 := seedCutoffDeriv_zero_below A τ hτ t htlo
    have hd2 := seedCutoffDeriv2_zero_below A τ hτ t htlo
    have hzero : totalLap F (fun x => seedTerm F Γ σ τ s x q) z -
        spectralParameter F s * seedTerm F Γ σ τ s z q = 0 := by
      rw [hz]
      simp [t, hd1, hd2]
    exact (hneq hzero).elim
  by_cases hthi : 2 * A < t
  · have hz := seedTerm_lap_defect Γ σ τ hτ.1 s q z
    have hd1 := seedCutoffDeriv_zero_above A τ hτ t hthi
    have hd2 := seedCutoffDeriv2_zero_above A τ hτ t hthi
    have hzero : totalLap F (fun x => seedTerm F Γ σ τ s x q) z -
        spectralParameter F s * seedTerm F Γ σ τ s z q = 0 := by
      rw [hz]
      simp [t, hd1, hd2]
    exact (hneq hzero).elim
  constructor
  · exact le_of_not_gt htlo
  · exact le_of_not_gt hthi

private theorem coordinateLap_addAt
    (u v : Coord F → ℂ) (p : Coord F)
    (hu : ContDiffAt ℝ ∞ u p) (hv : ContDiffAt ℝ ∞ v p)
    (w : InfinitePlace F) :
    coordinateLap (u + v) p w = coordinateLap u p w + coordinateLap v p w := by
  have hfd := fderiv_add
    ((hu.of_le (by norm_num : (1 : ℕ∞ω) ≤ ∞)).differentiableAt (by norm_num))
    ((hv.of_le (by norm_num : (1 : ℕ∞ω) ≤ ∞)).differentiableAt (by norm_num))
  have h2 := iteratedFDeriv_add_apply
    (hu.of_le (by norm_num : (2 : ℕ∞ω) ≤ ∞))
    (hv.of_le (by norm_num : (2 : ℕ∞ω) ≤ ∞))
  unfold coordinateLap
  rw [hfd, h2]
  simp only [ContinuousLinearMap.add_apply, smul_add]
  module

private theorem coordinateLap_sumAt {ι : Type*} (T : Finset ι)
    (u : ι → Coord F → ℂ) (p : Coord F)
    (hu : ∀ i ∈ T, ContDiffAt ℝ ∞ (u i) p) (w : InfinitePlace F) :
    coordinateLap (fun p => ∑ i ∈ T, u i p) p w =
      ∑ i ∈ T, coordinateLap (u i) p w := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [coordinateLap]
  | @insert i T hi ih =>
      have hsum : ContDiffAt ℝ ∞ (fun p => ∑ j ∈ T, u j p) p := by
        apply ContDiffAt.sum
        intro j hj
        exact hu j (Finset.mem_insert_of_mem hj)
      have hsumEq : (fun p => ∑ j ∈ insert i T, u j p) =
          u i + (fun p => ∑ j ∈ T, u j p) := by
        funext p
        simp [Finset.sum_insert, hi]
      rw [hsumEq, coordinateLap_addAt (u i) _ p (hu i (Finset.mem_insert_self i T))
        hsum w, ih (fun j hj => hu j (Finset.mem_insert_of_mem hj))]
      simp [Finset.sum_insert, hi]

private theorem partialLap_finite_local_sum
    {ι : Type*} (T : Finset ι) (f : X F → ℂ) (g : ι → X F → ℂ)
    (p : Coord F) (hp : p ∈ posSet F) (z : X F) (hz : ptX F p = z)
    (U : Set (Coord F)) (hU : IsOpen U) (hpU : p ∈ U)
    (hlocal : ∀ p' ∈ U, f (ptX F p') = ∑ i ∈ T, g i (ptX F p'))
    (hsm : ∀ i ∈ T, IsSmoothX F (g i)) (w : InfinitePlace F) :
    partialLap F w f z = ∑ i ∈ T, partialLap F w (g i) z := by
  have hEq : (fun p' => f (ptX F p')) =ᶠ[𝓝 p]
      (fun p' => ∑ i ∈ T, g i (ptX F p')) := by
    filter_upwards [hU.mem_nhds hpU] with p' hp'
    exact hlocal p' hp'
  let us : Coord F → ℂ := fun p' => ∑ i ∈ T, g i (ptX F p')
  have hu (i : ι) (hi : i ∈ T) :
      ContDiffAt ℝ ∞ (fun p' => g i (ptX F p')) p := by
    have hgi := hsm i hi
    change ContDiffOn ℝ ∞ (fun p' => g i (ptX F p')) (posSet F) at hgi
    exact (hgi p hp).contDiffAt (posSet_isOpen.mem_nhds hp)
  have hsumLap := partialLap_from_chart f us p hp w hEq
  have hcoordSum := coordinateLap_sumAt T (fun i p' => g i (ptX F p')) p hu w
  calc
    partialLap F w f z = partialLap F w f (ptX F p) := by rw [hz]
    _ = coordinateLap us p w := hsumLap
    _ = ∑ i ∈ T, coordinateLap (fun p' => g i (ptX F p')) p w := hcoordSum
    _ = ∑ i ∈ T, partialLap F w (g i) z := by
      apply Finset.sum_congr rfl
      intro i hi
      have hterm := partialLap_from_chart (g i) (fun p' => g i (ptX F p')) p hp w
        (Filter.Eventually.of_forall fun _ => rfl)
      rw [← hz]
      exact hterm.symm

private theorem eisSeedDefect_local_sum
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (σ : SL(2,F))
    (A : ℝ) (hA : 0 < A) (τ : ℝ → ℝ)
    (hτ : IsCuspCutoff A τ) (s : ℂ)
    (p : Coord F) (hp : p ∈ posSet F) :
    ∃ T : Finset (CuspCosets F Γ σ),
      ∃ U : Set (Coord F), IsOpen U ∧ p ∈ U ∧
        U ⊆ posSet F ∧
        (∀ q, A ≤ normHeight F
          (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • ptX F p)) → q ∈ T) ∧
        ∀ p' ∈ U,
          eisSeedDefect F Γ σ τ s (ptX F p') =
            ∑ q ∈ T,
              (totalLap F (fun x => seedTerm F Γ σ τ s x q) (ptX F p') -
                spectralParameter F s * seedTerm F Γ σ τ s (ptX F p') q) := by
  classical
  obtain ⟨T, hT⟩ := eisSeed_local_sum Γ σ A τ hτ hA s p hp
  obtain ⟨U, hconj⟩ := hT
  rcases hconj with ⟨hU, hconj⟩
  rcases hconj with ⟨hpU, hconj⟩
  rcases hconj with ⟨hUpos, hconj⟩
  rcases hconj with ⟨hTcenter, hlocal⟩
  refine ⟨T, U, hU, hpU, hUpos, hTcenter, ?_⟩
  intro p' hp'
  have hterm (q : CuspCosets F Γ σ) : IsSmoothX F (fun x =>
      seedTerm F Γ σ τ s x q) := by
    simpa only [one_smul] using seedTerm_smooth_action Γ σ 1 τ hτ.1 s q
  have htotal : totalLap F (eisSeed F Γ σ τ s) (ptX F p') =
      ∑ q ∈ T, totalLap F (fun x => seedTerm F Γ σ τ s x q) (ptX F p') := by
    unfold totalLap
    calc
      (∑ w : InfinitePlace F, partialLap F w (eisSeed F Γ σ τ s) (ptX F p')) =
          ∑ w : InfinitePlace F, ∑ q ∈ T,
            partialLap F w (fun x => seedTerm F Γ σ τ s x q) (ptX F p') := by
        apply Finset.sum_congr rfl
        intro w hw
        exact partialLap_finite_local_sum T
          (fun z => eisSeed F Γ σ τ s z)
          (fun q z => seedTerm F Γ σ τ s z q)
          p' (hUpos hp') (ptX F p') rfl U hU hp'
          (fun x hx => hlocal x hx) (fun q hq => hterm q) w
      _ = ∑ q ∈ T, totalLap F (fun x => seedTerm F Γ σ τ s x q) (ptX F p') := by
        simp only [totalLap]
        rw [Finset.sum_comm]
  have hval := hlocal p' hp'
  unfold eisSeedDefect
  rw [htotal, hval, Finset.mul_sum, ← Finset.sum_sub_distrib]

private theorem seedCuspTranslationDomain (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (hfull : IsFullZLattice (cuspTranslationsZ F Γ σ)) :
    ∃ P : Set (InfinitePlace F → ℂ),
      IsAddFundamentalDomain (cuspTranslations F Γ σ) P ∧
      Bornology.IsBounded P ∧ MeasurableSet P ∧
      ∀ x, ∃ μ ∈ cuspTranslations F Γ σ, μ + x ∈ P := by
  classical
  let L : Submodule ℤ (InfinitePlace F → ℂ) := cuspTranslationsZ F Γ σ
  rcases hfull with ⟨hdisc, hZ⟩
  letI : DiscreteTopology L := hdisc
  letI : IsZLattice ℝ L := hZ
  letI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  let bZ := Module.Free.chooseBasis ℤ L
  letI : Fintype (Module.Free.ChooseBasisIndex ℤ L) :=
    Module.Free.ChooseBasisIndex.fintype ℤ L
  let b := bZ.ofZLatticeBasis ℝ
  let P := ZSpan.fundamentalDomain b
  have hspan : span ℤ (Set.range b) = L := bZ.ofZLatticeBasis_span ℝ
  have hL : L = (cuspTranslations F Γ σ).toIntSubmodule := by
    apply le_antisymm
    · exact Submodule.span_le.2 (by intro x hx; exact hx)
    · intro x hx
      exact Submodule.subset_span hx
  have hLadd : L.toAddSubgroup = cuspTranslations F Γ σ := by
    simpa using congrArg Submodule.toAddSubgroup hL
  have hspanAdd : (span ℤ (Set.range b)).toAddSubgroup = L.toAddSubgroup :=
    congrArg Submodule.toAddSubgroup hspan
  have hfdL : IsAddFundamentalDomain
      (span ℤ (Set.range b)).toAddSubgroup P (volume : Measure (InfinitePlace F → ℂ)) := by
    simpa [P] using
      (ZSpan.isAddFundamentalDomain' b (volume : Measure (InfinitePlace F → ℂ)))
  have hfd : IsAddFundamentalDomain (cuspTranslations F Γ σ) P := by
    rw [← hLadd, ← hspanAdd]
    exact hfdL
  have hbounded : Bornology.IsBounded P := ZSpan.fundamentalDomain_isBounded b
  have hmeas : MeasurableSet P := ZSpan.fundamentalDomain_measurableSet b
  have hcover : ∀ x, ∃ μ ∈ cuspTranslations F Γ σ, μ + x ∈ P := by
    intro x
    obtain ⟨μ, hμ, -⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain b x
    have hμL : (μ : InfinitePlace F → ℂ) ∈ L :=
      (congrArg (fun S : Submodule ℤ (InfinitePlace F → ℂ) =>
        (μ : InfinitePlace F → ℂ) ∈ S) hspan).mp μ.property
    have hμtrans : (μ : InfinitePlace F → ℂ) ∈ cuspTranslations F Γ σ := by
      have : (μ : InfinitePlace F → ℂ) ∈ L.toAddSubgroup := hμL
      simpa [hLadd] using this
    refine ⟨(μ : InfinitePlace F → ℂ), hμtrans, ?_⟩
    change (μ : InfinitePlace F → ℂ) + x ∈ P
    rw [← vadd_eq_add]
    exact hμ
  exact ⟨P, hfd, hbounded, hmeas, hcover⟩

private theorem seedUnitHeightAction_product (ε : (𝓞 F)ˣ) (y : InfinitePlace F → ℝ) :
    (∏ w : InfinitePlace F, unitHeightAction F ε y w) = ∏ w : InfinitePlace F, y w := by
  have hnorm : absUnitNorm F ε = 1 := by
    simpa [absUnitNorm, absFieldNorm_eq_abs_norm] using (NumberField.Units.norm F ε)
  unfold unitHeightAction
  rw [Finset.prod_mul_distrib]
  have hp : (∏ w : InfinitePlace F,
      Complex.normSq (w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F)))) = 1 := by
    simpa [absUnitNorm, absFieldNorm, Complex.normSq_eq_norm_sq] using hnorm
  rw [hp, one_mul]

private theorem seedUnitAction_balanced (ε : (𝓞 F)ˣ) (y : InfinitePlace F → ℝ)
    (hy : ∀ w, 0 < y w) (B : ℝ)
    (hB : ∀ w, |Real.log (‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ *
        Real.sqrt (y w)) - (placeCount F)⁻¹ *
          ∑ w' : InfinitePlace F, Real.log (Real.sqrt (y w'))| ≤ B) :
    IsBalancedHeights F (2 * B) (unitHeightAction F ε y) := by
  let t : InfinitePlace F → ℝ := fun w => Real.sqrt (y w)
  have ht : ∀ w, 0 < t w := fun w => Real.sqrt_pos.mpr (hy w)
  have hFunit : algebraMap (𝓞 F) F (ε : 𝓞 F) ≠ 0 := by
    intro h
    apply ε.ne_zero
    exact FaithfulSMul.algebraMap_injective (𝓞 F) F h
  have hEmbed (w : InfinitePlace F) :
      w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F)) ≠ 0 := by
    intro h
    apply hFunit
    apply w.embedding.injective
    simpa using h
  have hnormpos (w : InfinitePlace F) :
      0 < ‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ := norm_pos_iff.mpr (hEmbed w)
  have hargpos (w : InfinitePlace F) :
      0 < ‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ * t w := mul_pos (hnormpos w) (ht w)
  have hlog (w : InfinitePlace F) :
      Real.log (unitHeightAction F ε y w) =
        2 * Real.log (‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ * t w) := by
    have hsq : unitHeightAction F ε y w =
        (‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ * t w) ^ 2 := by
      change Complex.normSq (w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))) * y w = _
      rw [Complex.normSq_eq_norm_sq]
      have ht2 : t w ^ 2 = y w := by dsimp [t]; exact Real.sq_sqrt (hy w).le
      rw [← ht2]
      ring
    rw [hsq, Real.log_pow]
    norm_num
  have hfieldnorm : absFieldNorm F (algebraMap (𝓞 F) F (ε : 𝓞 F)) = 1 := by
    simpa [absFieldNorm_eq_abs_norm] using (NumberField.Units.norm F ε)
  have hprodSq : (∏ w : InfinitePlace F,
      ‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖) ^ 2 = 1 := by
    calc
      _ = ∏ w : InfinitePlace F,
          ‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ ^ 2 := by rw [Finset.prod_pow]
      _ = absFieldNorm F (algebraMap (𝓞 F) F (ε : 𝓞 F)) := by simp [absFieldNorm]
      _ = 1 := hfieldnorm
  have hprodPos : 0 < ∏ w : InfinitePlace F,
      ‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ := by
    apply Finset.prod_pos
    intro w hw
    exact hnormpos w
  have hprodOne : ∏ w : InfinitePlace F,
      ‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ = 1 := by nlinarith [hprodSq]
  have hsumNorm : ∑ w : InfinitePlace F,
      Real.log ‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ = 0 := by
    calc
      _ = Real.log (∏ w : InfinitePlace F,
          ‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖) := by
        symm
        apply Real.log_prod
        intro w hw
        exact (hnormpos w).ne'
      _ = 0 := by rw [hprodOne]; simp
  have hsum :
      (∑ w : InfinitePlace F, Real.log (unitHeightAction F ε y w)) =
        2 * ∑ w : InfinitePlace F, Real.log (t w) := by
    calc
      _ = ∑ w : InfinitePlace F,
          2 * Real.log (‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ * t w) := by
        apply Finset.sum_congr rfl
        intro w hw
        exact hlog w
      _ = 2 * ∑ w : InfinitePlace F,
          Real.log (‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ * t w) := by rw [← Finset.mul_sum]
      _ = 2 * (∑ w : InfinitePlace F,
          Real.log ‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ +
            ∑ w : InfinitePlace F, Real.log (t w)) := by
        congr 1
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro w hw
        exact Real.log_mul (hnormpos w).ne' (ht w).ne'
      _ = 2 * ∑ w : InfinitePlace F, Real.log (t w) := by rw [hsumNorm, zero_add]
  constructor
  · intro w
    unfold unitHeightAction
    exact mul_pos (Complex.normSq_pos.mpr (hEmbed w)) (hy w)
  · intro w
    change |Real.log (unitHeightAction F ε y w) -
      (placeCount F)⁻¹ * ∑ w' : InfinitePlace F,
        Real.log (unitHeightAction F ε y w')| ≤ 2 * B
    have hrewrite :
        Real.log (unitHeightAction F ε y w) -
            (placeCount F)⁻¹ * ∑ w' : InfinitePlace F,
              Real.log (unitHeightAction F ε y w') =
          2 * (Real.log (‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ * t w) -
            (placeCount F)⁻¹ * ∑ w' : InfinitePlace F, Real.log (t w')) := by
      rw [hlog w, hsum]
      ring
    rw [hrewrite]
    simpa only [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] using
      (mul_le_mul_of_nonneg_left (hB w) (by norm_num : 0 ≤ (2:ℝ)))

private theorem seedBalancedHeightBounds (A B : ℝ) (hA : 0 < A)
    (y : InfinitePlace F → ℝ) (hbal : IsBalancedHeights F (2 * B) y)
    (hlo : A ≤ ∏ w : InfinitePlace F, y w)
    (hhi : (∏ w : InfinitePlace F, y w) ≤ 2 * A) :
    ∀ w, Real.exp (Real.log A / (placeCount F) - 2 * B) ≤ y w ∧
      y w ≤ Real.exp (Real.log (2 * A) / (placeCount F) + 2 * B) := by
  have hn : 0 < (placeCount F : ℝ) := by
    dsimp [placeCount]
    exact_mod_cast (Fintype.card_pos_iff.mpr
      (inferInstance : Nonempty (InfinitePlace F)))
  have hprod : 0 < ∏ w : InfinitePlace F, y w := by
    apply Finset.prod_pos
    intro w hw
    exact hbal.1 w
  have hlogProd :
      (∑ w : InfinitePlace F, Real.log (y w)) =
        Real.log (∏ w : InfinitePlace F, y w) := by
    symm
    apply Real.log_prod
    intro w hw
    exact (hbal.1 w).ne'
  have hmean : (placeCount F : ℝ)⁻¹ *
      ∑ w : InfinitePlace F, Real.log (y w) =
        Real.log (∏ w : InfinitePlace F, y w) / (placeCount F : ℝ) := by
    rw [hlogProd]
    field_simp [ne_of_gt hn]
  have hloglo : Real.log A ≤ Real.log (∏ w : InfinitePlace F, y w) :=
    Real.log_le_log hA hlo
  have hloghi : Real.log (∏ w : InfinitePlace F, y w) ≤ Real.log (2 * A) :=
    Real.log_le_log (by positivity) hhi
  have hmeanlo : Real.log A / (placeCount F : ℝ) ≤
      (placeCount F : ℝ)⁻¹ * ∑ w : InfinitePlace F, Real.log (y w) := by
    rw [hmean]
    exact div_le_div_of_nonneg_right hloglo hn.le
  have hmeanhi : (placeCount F : ℝ)⁻¹ *
      ∑ w : InfinitePlace F, Real.log (y w) ≤
        Real.log (2 * A) / (placeCount F : ℝ) := by
    rw [hmean]
    exact div_le_div_of_nonneg_right hloghi hn.le
  intro w
  have hleft := (abs_le.mp (hbal.2 w)).1
  have hright := (abs_le.mp (hbal.2 w)).2
  have hmeanlo' : Real.log A / (Fintype.card (InfinitePlace F) : ℝ) ≤
      (Fintype.card (InfinitePlace F) : ℝ)⁻¹ *
        ∑ w : InfinitePlace F, Real.log (y w) := by
    simpa [placeCount] using hmeanlo
  have hmeanhi' : (Fintype.card (InfinitePlace F) : ℝ)⁻¹ *
      ∑ w : InfinitePlace F, Real.log (y w) ≤
        Real.log (2 * A) / (Fintype.card (InfinitePlace F) : ℝ) := by
    simpa [placeCount] using hmeanhi
  have hylo : Real.log A / (placeCount F : ℝ) - 2 * B ≤ Real.log (y w) := by
    simpa [placeCount] using (show Real.log A / (Fintype.card (InfinitePlace F) : ℝ) - 2 * B ≤
      Real.log (y w) by linarith [hleft, hmeanlo'])
  have hyhi : Real.log (y w) ≤
      Real.log (2 * A) / (placeCount F : ℝ) + 2 * B := by
    simpa [placeCount] using (show Real.log (y w) ≤
      Real.log (2 * A) / (Fintype.card (InfinitePlace F) : ℝ) + 2 * B by
        linarith [hright, hmeanhi'])
  constructor
  · rw [← Real.exp_log (hbal.1 w)]
    exact Real.exp_le_exp.mpr hylo
  · rw [← Real.exp_log (hbal.1 w)]
    exact Real.exp_le_exp.mpr hyhi

private theorem seedCompactCuspBand
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (σ : SL(2,F))
    (P : Set (InfinitePlace F → ℂ)) (hPbounded : Bornology.IsBounded P)
    (A B : ℝ) (hA : 0 < A) (hB : 0 ≤ B) :
    ∃ K : Set (X F), IsCompact K ∧
      ∀ x y, x ∈ closure P →
        IsBalancedHeights F (2 * B) y →
        A ≤ ∏ w : InfinitePlace F, y w →
        (∏ w : InfinitePlace F, y w) ≤ 2 * A →
        σ • ptX' F x y ∈ K := by
  classical
  let Xbar : Set (InfinitePlace F → ℂ) := closure P
  have hXbar : IsCompact Xbar := by
    exact hPbounded.isCompact_closure
  let lo : ℝ := Real.exp (Real.log A / (placeCount F) - 2 * B)
  let hi : ℝ := Real.exp (Real.log (2 * A) / (placeCount F) + 2 * B)
  have hlo : 0 < lo := by dsimp [lo]; exact Real.exp_pos _
  have hhi : 0 < hi := by dsimp [hi]; exact Real.exp_pos _
  let Ybox : Set (InfinitePlace F → ℝ) := {y | ∀ w, y w ∈ Set.Icc lo hi}
  have hYbox : IsCompact Ybox :=
    isCompact_pi_infinite (fun _ : InfinitePlace F => isCompact_Icc)
  let Base : Set ((InfinitePlace F → ℂ) × (InfinitePlace F → ℝ)) := Xbar ×ˢ Ybox
  have hBase : IsCompact Base := hXbar.prod hYbox
  let toCoord : (InfinitePlace F → ℂ) × (InfinitePlace F → ℝ) → Coord F :=
    fun v w => (v.1 w, v.2 w)
  have htoCoord : Continuous toCoord := by
    apply continuous_pi
    intro w
    fun_prop
  let C : Set (Coord F) := toCoord '' Base
  have hC : IsCompact C := hBase.image htoCoord
  rcases G1_h3_basics (F := F) with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hex⟩
  obtain ⟨e, he, hesym⟩ := hex
  let posCoord : C → PosCoord (F := F) := fun p => ⟨p.1, by
    rcases p.2 with ⟨v, hvBase, hv⟩
    have hvY : v.2 ∈ Ybox := (Set.mem_prod.mp hvBase).2
    intro w
    have hy := hvY w
    have hcoord : (toCoord v w).2 = (p.1 w).2 := congrArg (fun q : Coord F => (q w).2) hv
    rw [← hcoord]
    exact lt_of_lt_of_le hlo (by simpa [toCoord] using (Set.mem_Icc.mp hy).1)⟩
  have hposCoord : Continuous posCoord :=
    Continuous.subtype_mk continuous_subtype_val (fun p => by
      rcases p.2 with ⟨v, hvBase, hv⟩
      have hvY : v.2 ∈ Ybox := (Set.mem_prod.mp hvBase).2
      intro w
      have hy := hvY w
      have hcoord : (toCoord v w).2 = (p.1 w).2 := congrArg (fun q : Coord F => (q w).2) hv
      rw [← hcoord]
      exact lt_of_lt_of_le hlo (by simpa [toCoord] using (Set.mem_Icc.mp hy).1))
  have hpt : Continuous (fun p : C => ptX F p.1) := by
    exact e.continuous.comp hposCoord |>.congr fun p => by
      simpa [posCoord] using he (posCoord p)
  have hact : Continuous (fun z : X F => σ • z) := by
    obtain ⟨eAct, hAct, _⟩ := (G2_x_action (F := F)).2.2.2.1 (toInf F σ)
    have heq : (fun z : X F => σ • z) = eAct := by
      funext z
      calc
        σ • z = actAtPlaces F (toInf F σ) z := rfl
        _ = eAct z := (hAct z).symm
    rw [heq]
    exact eAct.continuous
  let K : Set (X F) := Set.range (fun p : C => σ • ptX F p.1)
  have hK : IsCompact K := by
    letI : CompactSpace C := isCompact_iff_compactSpace.mp hC
    change IsCompact (Set.range (fun p : C => σ • ptX F p.1))
    exact isCompact_range (hact.comp hpt)
  refine ⟨K, hK, ?_⟩
  intro x y hx hbal hloBand hhiBand
  have hbounds := seedBalancedHeightBounds A B hA y hbal hloBand hhiBand
  have hxbar : x ∈ Xbar := by simpa [Xbar] using hx
  have hybox : y ∈ Ybox := by
    intro w
    exact Set.mem_Icc.mpr (hbounds w)
  let v : (InfinitePlace F → ℂ) × (InfinitePlace F → ℝ) := (x, y)
  have hvBase : v ∈ Base := Set.mem_prod.mpr ⟨hxbar, hybox⟩
  refine ⟨⟨toCoord v, ⟨v, hvBase, rfl⟩⟩, ?_⟩
  change σ • ptX F (toCoord v) = σ • ptX' F x y
  apply congrArg (fun z => σ • z)
  funext w
  rfl

private theorem seedNormHeight_ptX' (x : InfinitePlace F → ℂ)
    (y : InfinitePlace F → ℝ) (hy : ∀ w, 0 < y w) :
    normHeight F (ptX' F x y) = ∏ w : InfinitePlace F, y w := by
  unfold normHeight
  apply Finset.prod_congr rfl
  intro w hw
  exact (G1_h3_basics (F := F)).1 (x w) (y w) (hy w)

private theorem seedCuspBandReduction
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (σ : SL(2,F))
    (A : ℝ) (hA : 0 < A) :
    ∃ K : Set (X F), IsCompact K ∧ ∀ z : X F,
      A ≤ normHeight F (σ⁻¹ • z) → normHeight F (σ⁻¹ • z) ≤ 2 * A →
        ∃ γ : Γ, (γ : SL(2,𝓞 F)) • z ∈ K := by
  classical
  letI : (cuspUnits F Γ σ).FiniteIndex := cuspUnits_finiteIndex Γ σ
  obtain ⟨B, hB, hbalance⟩ := R4_unit_balance (cuspUnits F Γ σ)
  obtain ⟨P, hPfd, hPbounded, hPmeas, hPcover⟩ :=
    seedCuspTranslationDomain Γ σ ((R1_cusp_lattice Γ σ).2.2.2.1.1)
  obtain ⟨K, hK, hKband⟩ := seedCompactCuspBand Γ σ P hPbounded A B hA hB
  refine ⟨K, hK, ?_⟩
  intro z hlo hhi
  let z0 : X F := σ⁻¹ • z
  let p0 : Coord F := coordsX F z0
  let x : InfinitePlace F → ℂ := fun w => (p0 w).1
  let y : InfinitePlace F → ℝ := fun w => (p0 w).2
  have hy : ∀ w, 0 < y w := by
    intro w
    change 0 < height (z0 w)
    rw [height_eq_hyperbolicHeight]
    exact OAI.CubicEisenstein.hyperbolicHeight_pos (z0 w)
  rcases G1_h3_basics (F := F) with
    ⟨_, _, _, _, _, _, _, hptCoord, _, _, _, _⟩
  have hrec0 : ptX' F x y = z0 := by
    calc
      ptX' F x y = ptX F p0 := rfl
      _ = z0 := hptCoord z0
  have hnorm0 : normHeight F (ptX' F x y) = ∏ w : InfinitePlace F, y w := by
    exact seedNormHeight_ptX' x y hy
  have hheight0 : normHeight F (σ⁻¹ • z) = ∏ w : InfinitePlace F, y w := by
    rw [show σ⁻¹ • z = z0 by rfl, ← hrec0]
    exact hnorm0
  have hloBand : A ≤ ∏ w : InfinitePlace F, y w := by simpa [hheight0] using hlo
  have hhiBand : (∏ w : InfinitePlace F, y w) ≤ 2 * A := by simpa [hheight0] using hhi
  have hstart : z = σ • ptX' F x y := by
    calc
      z = σ • (σ⁻¹ • z) := by simp
      _ = σ • z0 := by rw [show σ⁻¹ • z = z0 from rfl]
      _ = σ • ptX' F x y := congrArg (fun q : X F => σ • q) hrec0.symm
  obtain ⟨ε, hε, hεbalance⟩ := hbalance (fun w => Real.sqrt (y w))
    (fun w => Real.sqrt_pos.mpr (hy w))
  have hyUpos : ∀ w, 0 < unitHeightAction F ε y w :=
    (seedUnitAction_balanced ε y hy B hεbalance).1
  have hbalU : IsBalancedHeights F (2 * B) (unitHeightAction F ε y) :=
    seedUnitAction_balanced ε y hy B hεbalance
  have hprodU := seedUnitHeightAction_product ε y
  obtain ⟨μU, γU, hformU⟩ := (cuspUnits_mem_iff Γ σ ε).mp hε
  let xU : InfinitePlace F → ℂ := fun w =>
    (w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))) ^ 2 * x w +
      w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F)) * w.embedding μU
  let yU : InfinitePlace F → ℝ := unitHeightAction F ε y
  have hmoveU : (γU : SL(2,𝓞 F)) • z = σ • ptX' F xU yU := by
    rw [hstart]
    change (γU : SL(2,𝓞 F)) • (σ • ptX' F x y) =
      σ • ptX' F
        (fun w => (w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))) ^ 2 * x w +
          w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F)) * w.embedding μU)
        (fun w => Complex.normSq (w.embedding
          (algebraMap (𝓞 F) F (ε : 𝓞 F))) * y w)
    exact cusp_conjugate_affine_action
      (γU : SL(2,𝓞 F)) σ ε μU hformU x y hy
  have hloU : A ≤ ∏ w : InfinitePlace F, yU w := by
    rw [hprodU]
    exact hloBand
  have hhiU : (∏ w : InfinitePlace F, yU w) ≤ 2 * A := by
    rw [hprodU]
    exact hhiBand
  obtain ⟨t, ht, htrans⟩ := hPcover xU
  rcases AddSubgroup.mem_map.mp ht with ⟨μT, hμT, htEq⟩
  obtain ⟨γT, hfieldT⟩ := (cuspLattice_mem_iff Γ σ μT).mp hμT
  have hconjT : σ⁻¹ * toSLF F (γT : SL(2,𝓞 F)) * σ =
      upperHom F (Multiplicative.ofAdd μT) := by
    calc
      σ⁻¹ * toSLF F (γT : SL(2,𝓞 F)) * σ =
          σ⁻¹ * (σ * upperHom F (Multiplicative.ofAdd μT) * σ⁻¹) * σ := by rw [← hfieldT]
      _ = upperHom F (Multiplicative.ofAdd μT) := by group
  have hupper : upperHom F (Multiplicative.ofAdd μT) = cuspUnitMatrix F 1 μT := by
    have hsc : signedCuspTranslationMatrix F 1 μT (by simp) = cuspUnitMatrix F 1 μT := by
      apply Subtype.ext
      ext i j <;> fin_cases i <;> fin_cases j <;>
        simp [signedCuspTranslationMatrix, cuspUnitMatrix]
    exact (signedTranslationMatrix_one_eq_upperHom μT).symm.trans hsc
  have hformT : σ⁻¹ * toSLF F (γT : SL(2,𝓞 F)) * σ = cuspUnitMatrix F 1 μT :=
    hconjT.trans hupper
  let xFinal : InfinitePlace F → ℂ := fun w => xU w + w.embedding μT
  have hxFinal : xFinal ∈ closure P := by
    have hxt : xU + t ∈ P := by
      have hcomm : xU + t = t + xU := by
        ext w
        exact add_comm _ _
      rw [hcomm]
      exact htrans
    have heq : xFinal = xU + t := by
      funext w
      dsimp [xFinal]
      have hcomponent := congrArg (fun f : InfinitePlace F → ℂ => xU w + f w) htEq
      simpa [infEmb] using hcomponent
    rw [heq]
    exact subset_closure hxt
  have hmoveT : (γT : SL(2,𝓞 F)) • (σ • ptX' F xU yU) =
      σ • ptX' F xFinal yU := by
    have h := cusp_conjugate_affine_action (γT : SL(2,𝓞 F)) σ 1 μT hformT
      xU yU hyUpos
    simpa [xFinal] using h
  have hfinal : ((γT * γU : Γ) : SL(2,𝓞 F)) • z =
      σ • ptX' F xFinal yU := by
    calc
      ((γT * γU : Γ) : SL(2,𝓞 F)) • z =
          (γT : SL(2,𝓞 F)) • ((γU : SL(2,𝓞 F)) • z) := by
            simp [Subgroup.coe_mul, mul_smul]
      _ = (γT : SL(2,𝓞 F)) • (σ • ptX' F xU yU) := by rw [hmoveU]
      _ = σ • ptX' F xFinal yU := hmoveT
  have hcompact := hKband xFinal yU hxFinal hbalU hloU hhiU
  refine ⟨γT * γU, ?_⟩
  rw [hfinal]
  exact hcompact

private theorem eisSeedDefect_compactSupport
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (σ : SL(2,F))
    (A₀ A : ℝ) (hA₀ : 1 ≤ A₀) (hA : A₀ ≤ A)
    (τ : ℝ → ℝ) (hτ : IsCuspCutoff A τ) :
    ∃ K : Set (X F), IsCompact K ∧ ∀ s,
      {z | eisSeedDefect F Γ σ τ s z ≠ 0} ⊆ orbitSaturation F Γ K := by
  have hApos : 0 < A := lt_of_lt_of_le (by linarith) hA
  obtain ⟨K, hK, hreduce⟩ := seedCuspBandReduction Γ σ A hApos
  refine ⟨K, hK, ?_⟩
  intro s z hz
  let p : Coord F := coordsX F z
  have hp : p ∈ posSet F := by
    intro w
    change 0 < height (z w)
    rw [height_eq_hyperbolicHeight]
    exact OAI.CubicEisenstein.hyperbolicHeight_pos (z w)
  have hpt : ptX F p = z := by
    rcases G1_h3_basics (F := F) with
      ⟨_, _, _, _, _, _, _, hptCoord, _, _, _, _⟩
    exact hptCoord z
  obtain ⟨T, hT⟩ := eisSeedDefect_local_sum Γ σ A hApos τ hτ s p hp
  obtain ⟨U, hconj⟩ := hT
  rcases hconj with ⟨hU, hconj⟩
  rcases hconj with ⟨hpU, hconj⟩
  rcases hconj with ⟨hUpos, hconj⟩
  rcases hconj with ⟨_, hlocal⟩
  have hdef : eisSeedDefect F Γ σ τ s (ptX F p) ≠ 0 := by simpa [hpt] using hz
  have hsome : ∃ q ∈ T,
      totalLap F (fun x => seedTerm F Γ σ τ s x q) (ptX F p) -
        spectralParameter F s * seedTerm F Γ σ τ s (ptX F p) q ≠ 0 := by
    by_contra hnone
    push_neg at hnone
    have hsumzero : ∑ q ∈ T,
        (totalLap F (fun x => seedTerm F Γ σ τ s x q) (ptX F p) -
          spectralParameter F s * seedTerm F Γ σ τ s (ptX F p) q) = 0 :=
      Finset.sum_eq_zero (fun q hq => hnone q hq)
    have hzero : eisSeedDefect F Γ σ τ s (ptX F p) = 0 := by
      rw [hlocal p hpU, hsumzero]
    exact hdef hzero
  rcases hsome with ⟨q, hqT, hqdef⟩
  have hband := seedTermDefect_height_band Γ σ A τ hτ s q (ptX F p) hqdef
  let zq : X F := ((q.out : Γ) : SL(2,𝓞 F)) • z
  have hloq : A ≤ normHeight F (σ⁻¹ • zq) := by
    simpa [zq, hpt] using hband.1
  have hhiq : normHeight F (σ⁻¹ • zq) ≤ 2 * A := by
    simpa [zq, hpt] using hband.2
  obtain ⟨γ, hγ⟩ := hreduce zq hloq hhiq
  refine ⟨(γ * q.out)⁻¹, ⟨γ • zq, hγ, ?_⟩⟩
  change ((γ * q.out)⁻¹ : Γ) •
      ((γ : Γ) • ((q.out : Γ) • z)) = z
  calc
    ((γ * q.out)⁻¹ : Γ) • ((γ : Γ) • ((q.out : Γ) • z)) =
        ((γ * q.out)⁻¹ : Γ) • ((γ * q.out : Γ) • z) := by rw [mul_smul]
    _ = z := inv_smul_smul _ _

private theorem eisSeed_compact_local_sum_open
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (σ : SL(2,F))
    (A : ℝ) (hA : 0 < A) (τ : ℝ → ℝ) (hτ : IsCuspCutoff A τ)
    (K : Set (Coord F)) (hK : IsCompact K) (hKpos : K ⊆ posSet F) :
    ∃ T : Finset (CuspCosets F Γ σ),
      ∀ p, p ∈ K → ∃ U : Set (Coord F), IsOpen U ∧ p ∈ U ∧ U ⊆ posSet F ∧
        ∀ s x, x ∈ U → eisSeed F Γ σ τ s (ptX F x) =
          ∑ q ∈ T, seedTerm F Γ σ τ s (ptX F x) q := by
  classical
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hdata (p : K) :
      ∃ Q : Set (CuspCosets F Γ σ), Q.Finite ∧
        (∀ q, A ≤ normHeight F
          (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • ptX F p.1)) → q ∈ Q) ∧
        ∃ U : Set (Coord F), IsOpen U ∧ p.1 ∈ U ∧ U ⊆ posSet F ∧
          ∀ x ∈ U, ∀ q ∉ Q, normHeight F
            (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • ptX F x)) ≤ A := by
    exact seedHighCosets_finite Γ σ A hA p.1 (hKpos p.2)
  choose Q hQ hcenter hUData using hdata
  choose U hUopen hUcenter hUpos hbelow using hUData
  have hcover : (K : Set (Coord F)) ⊆ ⋃ p : K, U p := by
    intro x hx
    let p : K := ⟨x, hx⟩
    exact Set.mem_iUnion.mpr ⟨p, hUcenter p⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hUopen hcover
  let T : Finset (CuspCosets F Γ σ) :=
    t.biUnion (fun p => (hQ p).toFinset)
  have hqnot (i : K) (hi : i ∈ t) (q : CuspCosets F Γ σ) (hqT : q ∉ T) :
      q ∉ Q i := by
    intro hqi
    apply hqT
    change q ∈ t.biUnion (fun p => (hQ p).toFinset)
    apply Finset.mem_biUnion.mpr
    refine ⟨i, hi, ?_⟩
    simpa using hqi
  refine ⟨T, ?_⟩
  intro p hp
  rcases Set.mem_iUnion.mp (ht hp) with ⟨i, hip⟩
  rcases Set.mem_iUnion.mp hip with ⟨hi, hpi⟩
  refine ⟨U i, hUopen i, hpi, hUpos i, ?_⟩
  intro s x hx
  have hzero (q : CuspCosets F Γ σ) (hq : q ∉ T) :
      seedTerm F Γ σ τ s (ptX F x) q = 0 := by
    have hqi := hqnot i hi q hq
    have hheight := hbelow i x hx q hqi
    simp [seedTerm, hτ.2.2.1 _ hheight]
  unfold eisSeed
  exact tsum_eq_sum (s := T) hzero


private def seedRadialDefect (r : ℝ) (τ : ℝ → ℝ) (s : ℂ) (h : ℝ) : ℂ :=
  -(r : ℂ) *
    (((h : ℂ) ^ 2 * deriv (deriv (fun t : ℝ => (τ t : ℂ))) h +
      (1 + 4 * s) * (h : ℂ) * deriv (fun t : ℝ => (τ t : ℂ)) h) *
      (h : ℂ) ^ (1 + 2 * s))

private theorem seedRadialDefect_compact_bcf_entire
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (σ : SL(2,F))
    (τ : ℝ → ℝ) (hτ : ContDiff ℝ ∞ τ)
    (K : Set (Coord F)) (hK : IsCompact K) (hKpos : K ⊆ posSet F)
    (q : CuspCosets F Γ σ) :
    ∃ Φ : ℂ → (K →ᵇ ℂ), AnalyticOnNhd ℂ Φ Set.univ ∧
      ∀ s p, Φ s p = seedRadialDefect (placeCount F) τ s
        (normHeight F (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • ptX F p.1))) := by
  classical
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let b : SL(2,F) := σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F))
  let H : Coord F → ℝ := fun p =>
    normHeight F (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • ptX F p))
  have hHbase : ContDiffOn ℝ ∞
      (fun p => normHeight F (b • ptX F p)) (posSet F) := seedHeight_action_smooth b
  have hHdef : H = fun p => normHeight F (b • ptX F p) := by
    funext p
    dsimp [H, b]
    rw [mul_smul]
    rfl
  have hH : ContDiffOn ℝ ∞ H (posSet F) := by
    rw [hHdef]
    exact hHbase
  have hHpos (p : Coord F) (hp : p ∈ posSet F) : 0 < H p := by
    dsimp [H]
    exact seedNormHeight_pos
      (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • ptX F p))
  have hHcont : Continuous (fun p : K => H p.1) :=
    hH.continuousOn.comp_continuous continuous_subtype_val
      (fun p => hKpos p.2)
  let τC : ℝ → ℂ := fun t => (τ t : ℂ)
  have hτC : ContDiff ℝ ∞ τC := Complex.ofRealCLM.contDiff.comp hτ
  have hτ₁ : ContDiff ℝ ∞ (deriv τC) := hτC.deriv'
  have hτ₂ : ContDiff ℝ ∞ (deriv (deriv τC)) := hτ₁.deriv'
  let hCoord : C(K,ℂ) := ⟨fun p => (H p.1 : ℂ),
    Complex.ofRealCLM.continuous.comp hHcont⟩
  let logCoord : C(K,ℂ) := ⟨fun p => (Real.log (H p.1) : ℂ), by
    have hlog : Continuous (fun p : K => Real.log (H p.1)) :=
      hHcont.log (fun p => (hHpos p.1 (hKpos p.2)).ne')
    exact Complex.ofRealCLM.continuous.comp hlog⟩
  let d₁Coord : C(K,ℂ) := ⟨fun p => deriv τC (H p.1),
    hτ₁.continuous.comp hHcont⟩
  let d₂Coord : C(K,ℂ) := ⟨fun p => deriv (deriv τC) (H p.1),
    hτ₂.continuous.comp hHcont⟩
  let hB : K →ᵇ ℂ := BoundedContinuousFunction.mkOfCompact hCoord
  let logB : K →ᵇ ℂ := BoundedContinuousFunction.mkOfCompact logCoord
  let d₁B : K →ᵇ ℂ := BoundedContinuousFunction.mkOfCompact d₁Coord
  let d₂B : K →ᵇ ℂ := BoundedContinuousFunction.mkOfCompact d₂Coord
  let B₀ : K →ᵇ ℂ := hB ^ 2 * d₂B + hB * d₁B
  let B₁ : K →ᵇ ℂ := (4 : ℂ) • hB * d₁B
  let Φ : ℂ → (K →ᵇ ℂ) := fun s =>
    (-(placeCount F : ℂ)) •
      ((B₀ + s • B₁) * NormedSpace.exp ((1 + 2 * s) • logB))
  have hBval (p : K) : hB p = (H p.1 : ℂ) := by
    rfl
  have hd₁val (p : K) : d₁B p = deriv τC (H p.1) := by
    rfl
  have hd₂val (p : K) : d₂B p = deriv (deriv τC) (H p.1) := by
    rfl
  have hB₀val (p : K) : B₀ p =
      (H p.1 : ℂ) ^ 2 * deriv (deriv τC) (H p.1) +
        (H p.1 : ℂ) * deriv τC (H p.1) := by
    simp [B₀, hBval, hd₁val, hd₂val]
  have hB₁val (p : K) : B₁ p =
      4 * (H p.1 : ℂ) * deriv τC (H p.1) := by
    simp [B₁, hBval, hd₁val]
    ring
  have hSum : AnalyticOnNhd ℂ (fun s : ℂ => B₀ + s • B₁) Set.univ := by
    intro s hs
    fun_prop
  have hArg : AnalyticOnNhd ℂ (fun s : ℂ => (1 + 2 * s) • logB) Set.univ := by
    intro s hs
    fun_prop
  have hExp : AnalyticOnNhd ℂ
      (fun s : ℂ => NormedSpace.exp ((1 + 2 * s) • logB)) Set.univ := by
    intro s hs
    exact (NormedSpace.exp_analytic _).comp (hArg s hs)
  have hPhi : AnalyticOnNhd ℂ Φ Set.univ := by
    intro s hs
    have hconst : AnalyticAt ℂ (fun _ : ℂ => (-(placeCount F : ℂ))) s := by
      fun_prop
    change AnalyticAt ℂ
      (fun z : ℂ => (-(placeCount F : ℂ)) •
        ((B₀ + z • B₁) * NormedSpace.exp ((1 + 2 * z) • logB))) s
    exact hconst.smul ((hSum s hs).mul (hExp s hs))
  refine ⟨Φ, hPhi, ?_⟩
  intro s p
  let ev : (K →ᵇ ℂ) →+* ℂ :=
    { toFun := fun f => f p
      map_one' := by simp
      map_mul' _ _ := by simp
      map_zero' := by simp
      map_add' _ _ := by simp }
  have hev : Continuous ev := by
    change Continuous (fun f : K →ᵇ ℂ => f p)
    exact (BoundedContinuousFunction.evalCLM ℂ p).continuous
  have hmap := NormedSpace.map_exp ev hev ((1 + 2 * s) • logB)
  have hexp : (NormedSpace.exp ((1 + 2 * s) • logB)) p =
      Complex.exp ((1 + 2 * s) * (Real.log (H p.1) : ℂ)) := by
    change ev (NormedSpace.exp ((1 + 2 * s) • logB)) = _
    rw [hmap, ← Complex.exp_eq_exp_ℂ]
    congr 1
  have hpow : (H p.1 : ℂ) ^ (1 + 2 * s) =
      Complex.exp ((1 + 2 * s) * (Real.log (H p.1) : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr
      (hHpos p.1 (hKpos p.2)).ne')]
    rw [← Complex.ofReal_log (le_of_lt (hHpos p.1 (hKpos p.2))), mul_comm]
  have hheight : H p.1 = normHeight F
      (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • ptX F p.1)) := rfl
  dsimp [Φ]
  change -(placeCount F : ℂ) *
      ((B₀ p + s * B₁ p) * (NormedSpace.exp ((1 + 2 * s) • logB)) p) = _
  rw [hexp, ← hheight]
  dsimp [seedRadialDefect]
  rw [hB₀val, hB₁val]
  rw [hpow]
  ring

private theorem eisSeedDefect_compact_local_sum
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (σ : SL(2,F))
    (A : ℝ) (hA : 0 < A) (τ : ℝ → ℝ) (hτ : IsCuspCutoff A τ)
    (K : Set (Coord F)) (hK : IsCompact K) (hKpos : K ⊆ posSet F) :
    ∃ T : Finset (CuspCosets F Γ σ),
      ∀ p, p ∈ K → ∀ s,
        eisSeedDefect F Γ σ τ s (ptX F p) =
          ∑ q ∈ T,
            (totalLap F (fun x => seedTerm F Γ σ τ s x q) (ptX F p) -
              spectralParameter F s * seedTerm F Γ σ τ s (ptX F p) q) := by
  classical
  obtain ⟨T, hseed⟩ :=
    eisSeed_compact_local_sum_open Γ σ A hA τ hτ K hK hKpos
  refine ⟨T, ?_⟩
  intro p hp s
  obtain ⟨U, hU, hpU, hUpos, hlocal⟩ := hseed p hp
  have hterm (q : CuspCosets F Γ σ) : IsSmoothX F (fun x =>
      seedTerm F Γ σ τ s x q) := by
    simpa only [one_smul] using seedTerm_smooth_action Γ σ 1 τ hτ.1 s q
  have htotal : totalLap F (eisSeed F Γ σ τ s) (ptX F p) =
      ∑ q ∈ T, totalLap F (fun x => seedTerm F Γ σ τ s x q) (ptX F p) := by
    unfold totalLap
    calc
      (∑ w : InfinitePlace F, partialLap F w (eisSeed F Γ σ τ s) (ptX F p)) =
          ∑ w : InfinitePlace F, ∑ q ∈ T,
            partialLap F w (fun x => seedTerm F Γ σ τ s x q) (ptX F p) := by
        apply Finset.sum_congr rfl
        intro w hw
        exact partialLap_finite_local_sum T
          (fun z => eisSeed F Γ σ τ s z)
          (fun q z => seedTerm F Γ σ τ s z q)
          p (hUpos hpU) (ptX F p) rfl U hU hpU
          (fun x hx => hlocal s x hx) (fun q hq => hterm q) w
      _ = ∑ q ∈ T, totalLap F (fun x => seedTerm F Γ σ τ s x q) (ptX F p) := by
        simp only [totalLap]
        rw [Finset.sum_comm]
  have hval : eisSeed F Γ σ τ s (ptX F p) =
      ∑ q ∈ T, seedTerm F Γ σ τ s (ptX F p) q := hlocal s p hpU
  unfold eisSeedDefect
  rw [htotal, hval, Finset.mul_sum, ← Finset.sum_sub_distrib]

private theorem eisSeedDefect_compact_bcf_entire
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (σ : SL(2,F))
    (A : ℝ) (hA : 0 < A) (τ : ℝ → ℝ) (hτ : IsCuspCutoff A τ)
    (K : Set (Coord F)) (hK : IsCompact K) (hKpos : K ⊆ posSet F) :
    ∃ Φ : ℂ → (K →ᵇ ℂ), AnalyticOnNhd ℂ Φ Set.univ ∧
      ∀ s p, Φ s p = eisSeedDefect F Γ σ τ s (ptX F p.1) := by
  classical
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨T, hdefect⟩ :=
    eisSeedDefect_compact_local_sum Γ σ A hA τ hτ K hK hKpos
  let f : CuspCosets F Γ σ → ℂ → (K →ᵇ ℂ) := fun q =>
    Classical.choose (seedRadialDefect_compact_bcf_entire Γ σ τ hτ.1 K hK hKpos q)
  have hfa (q : CuspCosets F Γ σ) (hq : q ∈ T) :
      AnalyticOnNhd ℂ (f q) Set.univ := by
    exact (Classical.choose_spec
      (seedRadialDefect_compact_bcf_entire Γ σ τ hτ.1 K hK hKpos q)).1
  have hfval (q : CuspCosets F Γ σ) (s : ℂ) (p : K) :
      f q s p = seedRadialDefect (placeCount F) τ s
        (normHeight F (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • ptX F p.1)) ) :=
    (Classical.choose_spec
      (seedRadialDefect_compact_bcf_entire Γ σ τ hτ.1 K hK hKpos q)).2 s p
  let Φ : ℂ → (K →ᵇ ℂ) := ∑ q ∈ T, f q
  have hΦ : AnalyticOnNhd ℂ Φ Set.univ :=
    Finset.analyticOnNhd_sum T (fun q hq => hfa q hq)
  refine ⟨Φ, hΦ, ?_⟩
  intro s p
  calc
    Φ s p = ∑ q ∈ T,
        seedRadialDefect (placeCount F) τ s
          (normHeight F (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • ptX F p.1))) := by
      simp only [Φ, Finset.sum_apply, BoundedContinuousFunction.sum_apply]
      apply Finset.sum_congr rfl
      intro q hq
      exact hfval q s p
    _ = ∑ q ∈ T,
        (totalLap F (fun x => seedTerm F Γ σ τ s x q) (ptX F p.1) -
          spectralParameter F s * seedTerm F Γ σ τ s (ptX F p.1) q) := by
      apply Finset.sum_congr rfl
      intro q hq
      simpa [seedRadialDefect] using
        (seedTerm_lap_defect Γ σ τ hτ.1 s q (ptX F p.1)).symm
    _ = eisSeedDefect F Γ σ τ s (ptX F p.1) := (hdefect p.1 p.2 s).symm

private theorem gammaTest_l2_sup_bound
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (K : Set (X F)) (hK : IsCompact K) :
    ∃ L : testSubmodule F Γ →ₗ[ℂ] L2Space F D, ∃ C : ℝ, 0 ≤ C ∧
      (∀ f : testSubmodule F Γ,
        {z | (f : X F → ℂ) z ≠ 0} ⊆ orbitSaturation F Γ K →
        ∀ B : ℝ, 0 ≤ B → (∀ z ∈ K, ‖(f : X F → ℂ) z‖ ≤ B) →
          ‖L f‖ ≤ C * B) ∧
      (∀ f : X F → ℂ, f ∈ testSubmodule F Γ ↔ IsGammaTest F Γ f) ∧
      (∀ f : testSubmodule F Γ, ∀ᵐ z ∂(volX F),
        z ∈ D → (L f) z = (f : X F → ℂ) z) := by
  classical
  letI : Finite (InfinitePlace F) := inferInstance
  letI : Countable (InfinitePlace F) := Finite.to_countable
  letI : BorelSpace H3 := ⟨rfl⟩
  letI : OpensMeasurableSpace H3 := BorelSpace.opensMeasurable
  letI : ∀ w : InfinitePlace F,
      OpensMeasurableSpace ((fun _ : InfinitePlace F => H3) w) := fun _ => inferInstance
  have hsecX : SecondCountableTopology (X F) := by
    rcases G1_h3_basics (F := F) with
      ⟨_, _, _, _, _, _, _, _, _, _, _, ⟨chart, _, _⟩⟩
    exact chart.symm.secondCountableTopology
  letI : SecondCountableTopology (X F) := hsecX
  haveI : Nonempty (InfinitePlace F) := inferInstance
  let w₀ : InfinitePlace F := Classical.choice (inferInstance : Nonempty (InfinitePlace F))
  let diag : H3 → X F := fun z _ => z
  have hdiag : Continuous diag := by
    apply continuous_pi
    intro w
    exact continuous_id
  have hleft : Function.LeftInverse (fun z : X F => z w₀) diag := by
    intro z
    rfl
  letI : SecondCountableTopology H3 :=
    (hleft.isEmbedding (continuous_apply w₀) hdiag).secondCountableTopology
  letI : OpensMeasurableSpace (X F) := by
    exact @Pi.opensMeasurableSpace (InfinitePlace F) (fun _ => H3) Finite.to_countable
      (fun _ => inferInstance) (fun _ => inferInstance)
      (fun _ => inferInstance) (fun _ => BorelSpace.opensMeasurable)
  have hT2X : T2Space (X F) := by
    rcases G1_h3_basics (F := F) with
      ⟨_, _, _, _, _, _, _, _, _, _, _, ⟨chart, _, _⟩⟩
    exact chart.t2Space
  letI : T2Space (X F) := hT2X
  letI : IsFiniteMeasureOnCompacts (volX F) :=
    ⟨fun C hC => (G3_volume (F := F)).2.2.1 C hC⟩
  rcases (T2_tests Γ D hD) with ⟨hmem, ⟨L, gradL2, hLrep, hGradrep, hrest⟩⟩
  obtain ⟨ψ, hψsmooth, hψcompact, hψnonneg, hψlocal, hψpart, hψrecon⟩ := hrest K hK
  rcases hψpart with ⟨U, hUopen, hUsat, hperiod⟩
  have hψcont : Continuous ψ :=
    RellichChartMeasure.continuous_of_isSmoothRealX hψsmooth
  have hψcompactReal : HasCompactSupport ψ := by
    obtain ⟨Cψ, hCψ, hψsupp⟩ := hψcompact
    have hsub : {z | ψ z ≠ 0} ⊆ Cψ := by
      intro z hz
      exact hψsupp (by simpa using hz)
    exact HasCompactSupport.of_support_subset_isCompact hCψ hsub
  have hψint : Integrable ψ (volX F) :=
    hψcont.integrable_of_hasCompactSupport hψcompactReal
  let C : ℝ := Real.sqrt (∫ z, ψ z ∂(volX F))
  have hCnonneg : 0 ≤ C := by dsimp [C]; exact Real.sqrt_nonneg _
  have hψintNonneg : 0 ≤ ∫ z, ψ z ∂(volX F) :=
    integral_nonneg_of_ae (ae_of_all _ hψnonneg)
  let μD : Measure (X F) := (volX F).restrict D
  refine ⟨L, C, hCnonneg, ?_, hmem, hLrep⟩
  intro fTest hfsupport B hB hfb
  let f : X F → ℂ := fTest
  have hfTest : IsGammaTest F Γ f := (hmem f).mp fTest.property
  let gL2 : L2Space F D := L fTest
  have hfcont : Continuous f :=
    RellichChartMeasure.continuous_of_isSmoothX hfTest.2.1
  let fPeriodReal : X F → ℝ := fun z => ψ z * ‖f z‖ ^ 2
  have hfPeriodRealCont : Continuous fPeriodReal :=
    hψcont.mul (hfcont.norm.pow 2)
  have hfPeriodRealCompact : HasCompactSupport fPeriodReal := by
    obtain ⟨Cψ, hCψ, hψsupp⟩ := hψcompact
    have hsub : {z | fPeriodReal z ≠ 0} ⊆ Cψ := by
      intro z hz
      have hψz : ψ z ≠ 0 := by
        intro hzero
        apply hz
        simp [fPeriodReal, hzero]
      exact hψsupp (by
        change ((ψ z : ℂ) ≠ 0)
        exact Complex.ofReal_ne_zero.mpr hψz)
    exact HasCompactSupport.of_support_subset_isCompact hCψ hsub
  let fPeriod : X F → ℂ := fun z => (fPeriodReal z : ℂ)
  have hfPeriodCont : Continuous fPeriod :=
    Complex.ofRealCLM.continuous.comp hfPeriodRealCont
  have hfPeriodCompact : HasCompactSupport fPeriod := by
    obtain ⟨Cψ, hCψ, hψsupp⟩ := hψcompact
    have hsub : {z | fPeriod z ≠ 0} ⊆ Cψ := by
      intro z hz
      have hreal : fPeriodReal z ≠ 0 := by
        intro hzero
        apply hz
        simp [fPeriod, hzero]
      have hψz : ψ z ≠ 0 := by
        intro hzero
        apply hreal
        simp [fPeriodReal, hzero]
      exact hψsupp (by
        change ((ψ z : ℂ) ≠ 0)
        exact Complex.ofReal_ne_zero.mpr hψz)
    exact HasCompactSupport.of_support_subset_isCompact hCψ hsub
  let fComplex : X F → ℂ := fPeriod
  have hfPeriodInt : Integrable fComplex (volX F) :=
    hfPeriodCont.integrable_of_hasCompactSupport hfPeriodCompact
  have hUnfold := (T1_l2 Γ D hD).2.2.1 fComplex hfPeriodInt
  have hL2int := specGapLpTwo_integrable_norm_sq μD gL2
  have hL2rep := hLrep fTest
  have hL2repD : ∀ᵐ z ∂μD, z ∈ D → gL2 z = f z :=
    ae_restrict_of_ae (μ := volX F) (s := D) hL2rep
  have hL2repAE : ∀ᵐ z ∂μD, gL2 z = f z := by
    filter_upwards [hL2repD, ae_restrict_mem₀ hD.nullMeasurableSet] with z hzrep hzD
    exact hzrep hzD
  have hL2normAE :
      (fun z => ‖gL2 z‖ ^ 2) =ᵐ[μD] (fun z => ‖f z‖ ^ 2) := by
    filter_upwards [hL2repAE] with z hz
    rw [hz]
  have hfSqInt : Integrable (fun z => ‖f z‖ ^ 2) μD := hL2int.congr hL2normAE
  have hNormEq : ‖gL2‖ ^ 2 = ∫ z, ‖f z‖ ^ 2 ∂μD := by
    calc
      ‖gL2‖ ^ 2 = ∫ z, ‖gL2 z‖ ^ 2 ∂μD :=
        specGapLpTwo_norm_sq_eq_integral μD gL2
      _ = ∫ z, ‖f z‖ ^ 2 ∂μD := by
        apply integral_congr_ae
        filter_upwards [hL2repAE] with z hz
        rw [hz]
  have hnormBound (z : X F) : ‖f z‖ ≤ B := by
    by_cases hzero : f z = 0
    · simp [hzero, hB]
    · obtain ⟨γ, x, hxK, hzx⟩ := hfsupport hzero
      calc
        ‖f z‖ = ‖f ((γ : SL(2,𝓞 F)) • x)‖ := by rw [hzx]
        _ = ‖f x‖ := by rw [hfTest.1 γ γ.property x]
        _ ≤ B := hfb x hxK
  have hperiodComplex (z : X F) :
      (∑' γ : Γ, fComplex ((γ : SL(2,𝓞 F)) • z)) =
        ((‖f z‖ ^ 2 : ℝ) : ℂ) := by
    by_cases hzero : f z = 0
    · have hzero' (γ : Γ) : f ((γ : SL(2,𝓞 F)) • z) = 0 :=
        by rw [hfTest.1 γ γ.property z, hzero]
      have hterm (γ : Γ) : fComplex ((γ : SL(2,𝓞 F)) • z) = 0 := by
        change Complex.ofReal (ψ ((γ : SL(2,𝓞 F)) • z) *
          ‖f ((γ : SL(2,𝓞 F)) • z)‖ ^ 2) = 0
        rw [hzero' γ]
        simp
      calc
        _ = ∑' γ : Γ, (0 : ℂ) := tsum_congr hterm
        _ = _ := by simp [hzero]
    · have hsat : z ∈ orbitSaturation F Γ K := hfsupport hzero
      have hrec := hψrecon fTest fTest.property hfsupport z
      have hfac : f z =
          (∑' γ : Γ, (ψ ((γ : SL(2,𝓞 F)) • z) : ℂ)) * f z := by
        calc
          f z = ∑' γ : Γ,
              (ψ ((γ : SL(2,𝓞 F)) • z) : ℂ) *
                f ((γ : SL(2,𝓞 F)) • z) := hrec
          _ = ∑' γ : Γ,
              (ψ ((γ : SL(2,𝓞 F)) • z) : ℂ) * f z := by
            apply tsum_congr
            intro γ
            rw [hfTest.1 γ γ.property z]
          _ = _ := by rw [tsum_mul_right]
      have hsumψ : ∑' γ : Γ, (ψ ((γ : SL(2,𝓞 F)) • z) : ℂ) = 1 := by
        have hdiv := congrArg (fun w : ℂ => w / f z) hfac
        have hOne : (1 : ℂ) =
            ∑' γ : Γ, (ψ ((γ : SL(2,𝓞 F)) • z) : ℂ) := by
          simpa [hzero, div_eq_mul_inv, mul_assoc] using hdiv
        exact hOne.symm
      have hterm (γ : Γ) :
          fComplex ((γ : SL(2,𝓞 F)) • z) =
            (ψ ((γ : SL(2,𝓞 F)) • z) : ℂ) * ((‖f z‖ ^ 2 : ℝ) : ℂ) := by
        change Complex.ofReal (ψ ((γ : SL(2,𝓞 F)) • z) *
          ‖f ((γ : SL(2,𝓞 F)) • z)‖ ^ 2) = _
        rw [Complex.ofReal_mul, hfTest.1 γ γ.property z]
      calc
        _ = ∑' γ : Γ,
              (ψ ((γ : SL(2,𝓞 F)) • z) : ℂ) * ((‖f z‖ ^ 2 : ℝ) : ℂ) := by
          exact tsum_congr hterm
        _ = (∑' γ : Γ, (ψ ((γ : SL(2,𝓞 F)) • z) : ℂ)) *
              ((‖f z‖ ^ 2 : ℝ) : ℂ) := by rw [tsum_mul_right]
        _ = _ := by rw [hsumψ]; simp
  have hcastNormInt : Integrable (fun z => ((‖f z‖ ^ 2 : ℝ) : ℂ)) μD := by
    simpa using Complex.ofRealCLM.integrable_comp hfSqInt
  have hperiodComplexInt :
      Integrable (fun z => ∑' γ : Γ, fComplex ((γ : SL(2,𝓞 F)) • z)) μD :=
    hcastNormInt.congr (ae_of_all _ fun z => (hperiodComplex z).symm)
  have hUnfoldReal :
      ∫ z in D, ‖f z‖ ^ 2 ∂(volX F) =
        ∫ z, ψ z * ‖f z‖ ^ 2 ∂(volX F) := by
    calc
      _ = ∫ z, ‖f z‖ ^ 2 ∂μD := rfl
      _ = ∫ z, Complex.re ((‖f z‖ ^ 2 : ℝ) : ℂ) ∂μD := by
        apply integral_congr_ae
        filter_upwards [] with z
        change ‖f z‖ ^ 2 = Complex.re (Complex.ofReal (‖f z‖ ^ 2))
        rw [Complex.ofReal_re]
      _ = ∫ z, Complex.re
            (∑' γ : Γ, fComplex ((γ : SL(2,𝓞 F)) • z)) ∂μD := by
          apply integral_congr_ae
          exact ae_of_all _ fun z => congrArg Complex.re (hperiodComplex z).symm
      _ = Complex.re
            (∫ z, (∑' γ : Γ, fComplex ((γ : SL(2,𝓞 F)) • z)) ∂μD) :=
          Complex.reCLM.integral_comp_comm hperiodComplexInt
      _ = Complex.re
            (∫ z in D, (∑' γ : Γ, fComplex ((γ : SL(2,𝓞 F)) • z)) ∂(volX F)) := rfl
      _ = Complex.re (∫ z, fComplex z ∂(volX F)) := congrArg Complex.re hUnfold
      _ = ∫ z, Complex.re (fComplex z) ∂(volX F) :=
        (Complex.reCLM.integral_comp_comm hfPeriodInt).symm
      _ = ∫ z, ψ z * ‖f z‖ ^ 2 ∂(volX F) := by
        apply integral_congr_ae
        filter_upwards [] with z
        dsimp [fComplex, fPeriod, fPeriodReal]
  have hpoint : ∀ z, ψ z * ‖f z‖ ^ 2 ≤ ψ z * B ^ 2 := by
    intro z
    have hsqf : ‖f z‖ ^ 2 ≤ B ^ 2 := by
      nlinarith [hnormBound z, norm_nonneg (f z), hB]
    exact mul_le_mul_of_nonneg_left hsqf
      (hψnonneg z)
  have hmajor : Integrable (fun z => ψ z * B ^ 2) (volX F) := by
    simpa [mul_comm] using hψint.const_mul (B ^ 2)
  have hfPeriodIntReal : Integrable fPeriodReal (volX F) :=
    hfPeriodRealCont.integrable_of_hasCompactSupport hfPeriodRealCompact
  have hpointFunc : fPeriodReal ≤ fun z => ψ z * B ^ 2 := by
    intro z
    simpa [fPeriodReal] using hpoint z
  have hIntBound := integral_mono hfPeriodIntReal hmajor hpointFunc
  have hCeq : C ^ 2 = ∫ z, ψ z ∂(volX F) := by
    dsimp [C]
    rw [Real.sq_sqrt hψintNonneg]
  have hsq : ‖gL2‖ ^ 2 ≤ B ^ 2 * C ^ 2 := by
    calc
      _ = ∫ z in D, ‖f z‖ ^ 2 ∂(volX F) := hNormEq
      _ = ∫ z, ψ z * ‖f z‖ ^ 2 ∂(volX F) := hUnfoldReal
      _ ≤ ∫ z, ψ z * B ^ 2 ∂(volX F) := hIntBound
      _ = B ^ 2 * (∫ z, ψ z ∂(volX F)) := by rw [integral_mul_const]; ring
      _ = B ^ 2 * C ^ 2 := by rw [hCeq]
  have hnonneg : 0 ≤ ‖gL2‖ := norm_nonneg _
  apply (sq_le_sq₀ hnonneg (mul_nonneg hCnonneg hB)).1
  nlinarith [hsq]

private theorem analyticOnNhd_closedSubmodule
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (S : Submodule ℂ E) (hS : IsClosed (S : Set E))
    (f : ℂ → E) (hf : AnalyticOnNhd ℂ f Set.univ)
    (hvals : ∀ z, f z ∈ S) :
    AnalyticOnNhd ℂ (fun z => (⟨f z, hvals z⟩ : S)) Set.univ := by
  letI : CompleteSpace S := hS.completeSpace_coe
  have hdifferentiable : Differentiable ℂ (fun z => (⟨f z, hvals z⟩ : S)) := by
    intro z
    have hfderiv : HasDerivAt f (deriv f z) z :=
      ((hf z (Set.mem_univ z)).differentiableAt).hasDerivAt
    have hderiv_mem : deriv f z ∈ S := by
      apply hS.mem_of_tendsto hfderiv.tendsto_slope
      filter_upwards [] with w
      rw [slope_def_module]
      exact S.smul_mem _ (S.sub_mem (hvals w) (hvals z))
    let g : ℂ → S := fun w => ⟨f w, hvals w⟩
    let d : S := ⟨deriv f z, hderiv_mem⟩
    have hsmallS :
        (fun w => g w - g z - (w - z) • d) =o[𝓝 z] fun w => w - z := by
      have hsmall := hfderiv.isLittleO
      rw [Asymptotics.isLittleO_iff_nat_mul_le] at hsmall ⊢
      intro n
      filter_upwards [hsmall n] with w hw
      simpa [g, d] using hw
    exact (HasDerivAt.of_isLittleO hsmallS).differentiableAt
  exact hdifferentiable.differentiableOn.analyticOnNhd isOpen_univ

private def supportedTestSubmodule
    (Γ : Subgroup SL(2,𝓞 F)) (K : Set (X F)) :
    Submodule ℂ (testSubmodule F Γ) where
  carrier := {f | {z | (f : X F → ℂ) z ≠ 0} ⊆ orbitSaturation F Γ K}
  zero_mem' := by
    intro z hz
    simp at hz
  add_mem' := by
    intro f g hf hg z hz
    have hfg : (f : X F → ℂ) z ≠ 0 ∨ (g : X F → ℂ) z ≠ 0 := by
      by_contra h
      push_neg at h
      apply hz
      simp [h.1, h.2]
    exact hfg.elim (fun h => hf (by simpa using h)) (fun h => hg (by simpa using h))
  smul_mem' := by
    intro c f hf z hz
    have hne : (f : X F → ℂ) z ≠ 0 := by
      intro hzero
      apply hz
      simp [hzero]
    exact hf (by simpa using hne)

private theorem seedPtX_continuousOn : ContinuousOn (ptX F) (posSet F) := by
  rcases G1_h3_basics (F := F) with
    ⟨_, _, _, _, _, _, _, _, _, _, _, ⟨e, he, _⟩⟩
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun p : {p : Coord F // p ∈ posSet F} => ptX F p.1)
  have heq : (fun p : {p : Coord F // p ∈ posSet F} => ptX F p.1) = e :=
    funext fun p => (he p).symm
  rw [heq]
  exact e.continuous

private theorem seedPtX_coordsX (z : X F) : ptX F (coordsX F z) = z := by
  rcases G1_h3_basics (F := F) with
    ⟨_, _, _, _, _, _, _, hptCoord, _, _, _, _⟩
  exact hptCoord z

set_option maxHeartbeats 1000000 in
private theorem gammaTest_l2_factor_compact_restriction
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (Kx : Set (X F)) (hKx : IsCompact Kx)
    (Kc : Set (Coord F)) (hKc : IsCompact Kc)
    (hKcpos : Kc ⊆ posSet F)
    (hKxSub : Kx ⊆ ptX F '' Kc)
    (L : testSubmodule F Γ →ₗ[ℂ] L2Space F D) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ f : testSubmodule F Γ,
      {z | (f : X F → ℂ) z ≠ 0} ⊆ orbitSaturation F Γ Kx →
      ∀ B : ℝ, 0 ≤ B → (∀ z ∈ Kx, ‖(f : X F → ℂ) z‖ ≤ B) →
        ‖L f‖ ≤ C * B)
    (hmem : ∀ f : X F → ℂ,
      f ∈ testSubmodule F Γ ↔ IsGammaTest F Γ f) :
    ∃ R : supportedTestSubmodule Γ Kx →ₗ[ℂ] (Kc →ᵇ ℂ),
      ∃ Q : (LinearMap.range R).topologicalClosure →L[ℂ] L2Space F D,
        (∀ f p, R f p = (f.1 : X F → ℂ) (ptX F p.1)) ∧
        ∀ f : supportedTestSubmodule Γ Kx,
          Q ⟨R f, (LinearMap.range R).le_topologicalClosure ⟨f, rfl⟩⟩ = L f.1 := by
  classical
  letI : CompactSpace Kc := isCompact_iff_compactSpace.mp hKc
  let V : Submodule ℂ (testSubmodule F Γ) := supportedTestSubmodule Γ Kx
  letI : AddCommGroup (↥V) := inferInstance
  letI : Module ℂ (↥V) := inferInstance
  have hptXpos : Continuous (fun p : {p : Coord F // p ∈ posSet F} => ptX F p.1) := by
    change Continuous ((posSet F).domRestrict (ptX F))
    exact (continuousOn_iff_continuous_domRestrict).mp
      (seedPtX_continuousOn (F := F))
  let incl : Kc → {p : Coord F // p ∈ posSet F} :=
    fun p => ⟨p.1, hKcpos p.2⟩
  have hincl : Continuous incl :=
    Continuous.subtype_mk continuous_subtype_val (fun p => hKcpos p.2)
  have hptX : Continuous (fun p : Kc => ptX F p.1) := by
    change Continuous (fun p => ptX F (incl p).1)
    exact hptXpos.comp hincl
  let R : V →ₗ[ℂ] (Kc →ᵇ ℂ) := {
    toFun := fun f => BoundedContinuousFunction.mkOfCompact
      ⟨fun p => (f.1 : X F → ℂ) (ptX F p.1),
        (RellichChartMeasure.continuous_of_isSmoothX
          ((hmem (f.1 : X F → ℂ)).mp f.1.property).2.1).comp hptX⟩
    map_add' := by
      intro f g
      ext p
      rfl
    map_smul' := by
      intro c f
      ext p
      rfl
  }
  let L' : V →ₗ[ℂ] L2Space F D := L.comp V.subtype
  have hker : R.ker ≤ L'.ker := by
    intro f hf
    apply LinearMap.mem_ker.mpr
    have hfb : ∀ z ∈ Kx, ‖(f.1 : X F → ℂ) z‖ ≤ 0 := by
      intro z hz
      obtain ⟨p, hp, hzp⟩ := hKxSub hz
      have heval := congrArg (fun g : Kc →ᵇ ℂ => g ⟨p, hp⟩)
        (LinearMap.mem_ker.mp hf)
      have hzero : (f.1 : X F → ℂ) z = 0 := by
        have hpoint : R f ⟨p, hp⟩ = 0 := by simpa using heval
        simpa [R, hzp] using hpoint
      simp [hzero]
    have hnorm := hbound f.1 f.2 0 (by norm_num) hfb
    have hzero : ‖L' f‖ = 0 := le_antisymm (by simpa [L'] using hnorm) (norm_nonneg _)
    exact norm_eq_zero.mp hzero
  let Qquot : (↥V ⧸ R.ker) →ₗ[ℂ] L2Space F D := R.ker.liftQ L' hker
  let Qrange : LinearMap.range R →ₗ[ℂ] L2Space F D :=
    Qquot.comp R.quotKerEquivRange.symm.toLinearMap
  let S : Submodule ℂ (Kc →ᵇ ℂ) := (LinearMap.range R).topologicalClosure
  have hRS : LinearMap.range R ≤ S := (LinearMap.range R).le_topologicalClosure
  let inclRange : LinearMap.range R →ₗ[ℂ] S := Submodule.inclusion hRS
  have hRange : Set.range (fun x : LinearMap.range R => (inclRange x : Kc →ᵇ ℂ)) =
      Set.range (R : V → (Kc →ᵇ ℂ)) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨f, hf⟩ := x.2
      exact ⟨f, hf⟩
    · rintro ⟨f, rfl⟩
      exact ⟨⟨R f, LinearMap.mem_range_self R f⟩, rfl⟩
  have hRangeComp : Set.range (Subtype.val ∘ inclRange) =
      Set.range (R : V → (Kc →ᵇ ℂ)) := by
    simpa only [Function.comp_def] using hRange
  have hDense : DenseRange inclRange := by
    rw [DenseRange, Subtype.dense_iff]
    change (S : Set (Kc →ᵇ ℂ)) ⊆ closure (Subtype.val '' Set.range inclRange)
    rw [← Set.range_comp]
    rw [hRangeComp]
    exact Set.Subset.rfl
  have hQbound : ∀ x : LinearMap.range R, ‖Qrange x‖ ≤ C * ‖inclRange x‖ := by
    intro x
    obtain ⟨f, hRf⟩ := x.2
    have hfb : ∀ z ∈ Kx, ‖(f.1 : X F → ℂ) z‖ ≤ ‖x‖ := by
      intro z hz
      obtain ⟨p, hp, hzp⟩ := hKxSub hz
      calc
        ‖(f.1 : X F → ℂ) z‖ = ‖(f.1 : X F → ℂ) (ptX F p)‖ := by rw [hzp]
        _ = ‖R f ⟨p, hp⟩‖ := rfl
        _ ≤ ‖R f‖ := (R f).norm_coe_le_norm ⟨p, hp⟩
        _ = ‖x‖ := by rw [hRf]; rfl
    have hboundf := hbound f.1 f.2 ‖x‖ (norm_nonneg _) hfb
    have hQx : Qrange x = L' f := by
      have hx : x = ⟨R f, LinearMap.mem_range_self R f⟩ := Subtype.ext hRf.symm
      rw [hx]
      change Qquot (R.quotKerEquivRange.symm ⟨R f, LinearMap.mem_range_self R f⟩) = L' f
      rw [R.quotKerEquivRange_symm_apply_image f (LinearMap.mem_range_self R f)]
      exact R.ker.liftQ_apply L' (h := hker) f
    calc
      ‖Qrange x‖ = ‖L' f‖ := by rw [hQx]
      _ = ‖L f.1‖ := rfl
      _ ≤ C * ‖x‖ := hboundf
      _ = C * ‖inclRange x‖ := by rfl
  let Q : S →L[ℂ] L2Space F D := Qrange.extendOfNorm inclRange
  refine ⟨R, Q, ?_, ?_⟩
  · intro f p
    rfl
  intro f
  have hQrepr : Qrange ⟨R f, LinearMap.mem_range_self R f⟩ = L' f := by
    change Qquot (R.quotKerEquivRange.symm ⟨R f, LinearMap.mem_range_self R f⟩) = L' f
    rw [R.quotKerEquivRange_symm_apply_image f (LinearMap.mem_range_self R f)]
    exact R.ker.liftQ_apply L' (h := hker) f
  change Qrange.extendOfNorm inclRange (inclRange ⟨R f, LinearMap.mem_range_self R f⟩) = L f.1
  rw [LinearMap.extendOfNorm_eq hDense ⟨C, hQbound⟩
    ⟨R f, LinearMap.mem_range_self R f⟩]
  simpa [L'] using hQrepr

set_option maxHeartbeats 1000000 in
private theorem seedTotalLap_isSmooth (f : X F → ℂ) (hf : IsSmoothX F f) :
    IsSmoothX F (totalLap F f) := by
  change ContDiffOn ℝ ∞ (fun p => totalLap F f (ptX F p)) (posSet F)
  let q : Coord F → ℂ := fun p => f (ptX F p)
  have hq : ContDiffOn ℝ ∞ q (posSet F) := hf
  have hfd : ContDiffOn ℝ ∞ (fun p => fderiv ℝ q p) (posSet F) :=
    hq.fderiv_of_isOpen (posSet_isOpen (F := F)) (by norm_num)
  have hfd2 : ContDiffOn ℝ ∞ (fun p => fderiv ℝ (fderiv ℝ q) p) (posSet F) :=
    hfd.fderiv_of_isOpen (posSet_isOpen (F := F)) (by norm_num)
  have hfirstEval (v : Coord F) :
      ContDiffOn ℝ ∞ (fun p => fderiv ℝ q p v) (posSet F) :=
    hfd.clm_apply contDiffOn_const
  have hsecondEval (v u : Coord F) :
      ContDiffOn ℝ ∞ (fun p => iteratedFDeriv ℝ 2 q p ![v, u]) (posSet F) := by
    have hEvalV : ContDiffOn ℝ ∞
        (fun p => fderiv ℝ (fderiv ℝ q) p v) (posSet F) :=
      hfd2.clm_apply contDiffOn_const
    have hEvalVU : ContDiffOn ℝ ∞
        (fun p => fderiv ℝ (fderiv ℝ q) p v u) (posSet F) :=
      hEvalV.clm_apply contDiffOn_const
    apply hEvalVU.congr
    intro p hp
    change iteratedFDeriv ℝ 2 q p ![v, u] = fderiv ℝ (fderiv ℝ q) p v u
    simp [iteratedFDeriv_two_apply]
  rcases G1_h3_basics (F := F) with
    ⟨_, _, _, _, _, _, hcoordPt, _, _, _, _, _⟩
  have hpartial (w : InfinitePlace F) :
      ContDiffOn ℝ ∞ (fun p => partialLap F w f (ptX F p)) (posSet F) := by
    let e1 : Coord F := Pi.single w ((1 : ℂ), (0 : ℝ))
    let e2 : Coord F := Pi.single w (Complex.I, (0 : ℝ))
    let e3 : Coord F := Pi.single w ((0 : ℂ), (1 : ℝ))
    have hy : ContDiffOn ℝ ∞ (fun p : Coord F => ((p w).2 : ℂ)) (posSet F) := by
      have hyReal : ContDiff ℝ ∞ (fun p : Coord F => (p w).2) := by fun_prop
      have hyComplex : ContDiff ℝ ∞ (fun p : Coord F => ((p w).2 : ℂ)) := by
        simpa [Function.comp_def, Complex.ofRealCLM_apply] using
          Complex.ofRealCLM.contDiff.comp hyReal
      exact hyComplex.contDiffOn
    have hsum : ContDiffOn ℝ ∞
        (fun p => iteratedFDeriv ℝ 2 q p ![e1, e1] +
          iteratedFDeriv ℝ 2 q p ![e2, e2] +
          iteratedFDeriv ℝ 2 q p ![e3, e3]) (posSet F) := by
      exact ((hsecondEval e1 e1).add (hsecondEval e2 e2)).add (hsecondEval e3 e3)
    have hmodel : ContDiffOn ℝ ∞
        (fun p => ((p w).2 : ℂ) * fderiv ℝ q p e3 -
          ((p w).2 : ℂ) ^ 2 *
            (iteratedFDeriv ℝ 2 q p ![e1, e1] +
              iteratedFDeriv ℝ 2 q p ![e2, e2] +
              iteratedFDeriv ℝ 2 q p ![e3, e3])) (posSet F) := by
      exact (hy.mul (hfirstEval e3)).sub ((hy.pow 2).mul hsum)
    have hformula : ∀ p, p ∈ posSet F →
        partialLap F w f (ptX F p) =
          ((p w).2 : ℂ) * fderiv ℝ q p e3 -
            ((p w).2 : ℂ) ^ 2 *
              (iteratedFDeriv ℝ 2 q p ![e1, e1] +
                iteratedFDeriv ℝ 2 q p ![e2, e2] +
                iteratedFDeriv ℝ 2 q p ![e3, e3]) := by
      intro p hp
      have hcoords := hcoordPt p hp
      simp [partialLap, q, hcoords, e1, e2, e3, Function.comp_def]
    apply hmodel.congr
    intro p hp
    exact hformula p hp
  unfold totalLap
  exact ContDiffOn.sum (fun w hw => hpartial w)

set_option maxHeartbeats 1000000 in
private theorem eisSeedDefect_l2_entire
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (σ : SL(2,F)) (A₀ A : ℝ) (hA₀ : 1 ≤ A₀) (hA : A₀ ≤ A)
    (hsep : ∀ γ γ' : Γ, ∀ z : X F,
      A₀ ≤ normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
      A₀ ≤ normHeight F (σ⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
      γ' * γ⁻¹ ∈ cuspStab F Γ σ)
    (τ : ℝ → ℝ) (hτ : IsCuspCutoff A τ) :
    ∃ G : ℂ → L2Space F D, AnalyticOnNhd ℂ G Set.univ ∧
      ∀ s, ∀ᵐ z ∂(volX F), z ∈ D → G s z = eisSeedDefect F Γ σ τ s z := by
  classical
  obtain ⟨Kx, hKx, hDefectSupport⟩ :=
    eisSeedDefect_compactSupport Γ σ A₀ A hA₀ hA τ hτ
  let Kc : Set (Coord F) := coordsX F '' Kx
  have hKc : IsCompact Kc := hKx.image RellichChartMeasure.coordsX_continuous
  have hKcpos : Kc ⊆ posSet F := by
    rintro p ⟨z, hz, rfl⟩
    exact RellichChartMeasure.coordsX_mem_pos z
  have hKxSub : Kx ⊆ ptX F '' Kc := by
    intro z hz
    refine ⟨coordsX F z, ⟨z, hz, rfl⟩, seedPtX_coordsX z⟩
  rcases gammaTest_l2_sup_bound Γ D hD Kx hKx with
    ⟨L, C, hC, hbound, hmem, hLrep⟩
  rcases gammaTest_l2_factor_compact_restriction Γ D hD Kx hKx Kc hKc hKcpos
      hKxSub L C hC hbound hmem with ⟨R, Q, hRrep, hFactor⟩
  let S : Submodule ℂ (Kc →ᵇ ℂ) := (LinearMap.range R).topologicalClosure
  have hSclosed : IsClosed (S : Set (Kc →ᵇ ℂ)) :=
    (LinearMap.range R).isClosed_topologicalClosure
  rcases eisSeedDefect_compact_bcf_entire Γ σ A
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_trans hA₀ hA))
      τ hτ Kc hKc hKcpos with ⟨Φ, hΦ, hΦvalue⟩
  have hApos : 0 < A :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_trans hA₀ hA)
  have hseedSmooth (s : ℂ) : IsSmoothX F (eisSeed F Γ σ τ s) :=
    eisSeed_isSmooth Γ σ A hApos τ hτ s
  have hdefectSmooth (s : ℂ) : IsSmoothX F (eisSeedDefect F Γ σ τ s) := by
    have hseed := hseedSmooth s
    have htotal := seedTotalLap_isSmooth (eisSeed F Γ σ τ s) hseed
    change ContDiffOn ℝ ∞
      (fun p => totalLap F (eisSeed F Γ σ τ s) (ptX F p) -
        spectralParameter F s * eisSeed F Γ σ τ s (ptX F p)) (posSet F)
    exact htotal.sub (contDiffOn_const.mul hseed)
  have hdefectInv (s : ℂ) : IsGammaInvariant F Γ (eisSeedDefect F Γ σ τ s) :=
    eisSeedDefect_isGammaInvariant Γ σ τ s (hseedSmooth s)
      (eisSeed_isGammaInvariant Γ σ τ s)
  let fTest : ℂ → testSubmodule F Γ := fun s =>
    ⟨eisSeedDefect F Γ σ τ s,
      (hmem _).mpr ⟨hdefectInv s, hdefectSmooth s,
        ⟨Kx, hKx, hDefectSupport s⟩⟩⟩
  have htestSupport (s : ℂ) :
      {z | (fTest s : X F → ℂ) z ≠ 0} ⊆ orbitSaturation F Γ Kx := by
    exact hDefectSupport s
  let fV : ℂ → supportedTestSubmodule Γ Kx := fun s =>
    ⟨fTest s, htestSupport s⟩
  have hRvalue (s : ℂ) : R (fV s) = Φ s := by
    apply BoundedContinuousFunction.ext
    intro p
    calc
      (R (fV s)) p = ((fV s).1 : X F → ℂ) (ptX F p.1) := hRrep (fV s) p
      _ = eisSeedDefect F Γ σ τ s (ptX F p.1) := rfl
      _ = Φ s p := (hΦvalue s p).symm
  have hPhiRange (s : ℂ) : Φ s ∈ LinearMap.range R := by
    rw [← hRvalue s]
    exact ⟨fV s, rfl⟩
  have hPhiMem (s : ℂ) : Φ s ∈ S :=
    (LinearMap.range R).le_topologicalClosure (hPhiRange s)
  let ΦS : ℂ → S := fun s => ⟨Φ s, hPhiMem s⟩
  have hPhiS : AnalyticOnNhd ℂ ΦS Set.univ :=
    analyticOnNhd_closedSubmodule S hSclosed Φ hΦ hPhiMem
  let G : ℂ → L2Space F D := fun s => Q (ΦS s)
  have hPhiSDiff : Differentiable ℂ ΦS := fun s =>
    (hPhiS s (Set.mem_univ s)).differentiableAt
  have hGDiff : Differentiable ℂ G := by
    intro s
    exact (differentiableAt_const Q).clm_apply (hPhiSDiff s)
  have hGanalytic : AnalyticOnNhd ℂ G Set.univ :=
    hGDiff.differentiableOn.analyticOnNhd isOpen_univ
  have hGvalue (s : ℂ) : G s = L (fTest s) := by
    have hsub : ΦS s =
        ⟨R (fV s), (LinearMap.range R).le_topologicalClosure
          (LinearMap.mem_range_self R (fV s))⟩ := by
      apply Subtype.ext
      exact (hRvalue s).symm
    change Q (ΦS s) = L (fTest s)
    rw [hsub]
    exact hFactor (fV s)
  refine ⟨G, hGanalytic, ?_⟩
  intro s
  have hrep := hLrep (fTest s)
  filter_upwards [hrep] with z hz
  intro hzD
  rw [hGvalue s]
  exact hz hzD

private theorem eisSeedDefect_tail_formula
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (σ : SL(2,F))
    (A₀ A : ℝ) (hA₀ : 1 ≤ A₀) (hA : A₀ ≤ A)
    (hsep : ∀ γ γ' : Γ, ∀ z : X F,
      A₀ ≤ normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
      A₀ ≤ normHeight F (σ⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
      γ' * γ⁻¹ ∈ cuspStab F Γ σ)
    (τ : ℝ → ℝ) (hτ : IsCuspCutoff A τ) (s : ℂ) (z : X F)
    (hz : z ∈ cuspTail F Γ σ A₀) :
    ∃ γ : Γ,
      eisSeedDefect F Γ σ τ s z = seedRadialDefect (placeCount F) τ s
        (normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z))) := by
  classical
  rcases hz with ⟨γ₀, hγ₀⟩
  let q₀ : CuspCosets F Γ σ := Quotient.mk _ γ₀
  have hrep : QuotientGroup.rightRel (cuspStab F Γ σ) q₀.out γ₀ :=
    Quotient.mk_out γ₀
  have hheightRep : normHeight F (σ⁻¹ • ((q₀.out : Γ) • z)) =
      normHeight F (σ⁻¹ • ((γ₀ : Γ) • z)) :=
    (seed_cusp_height_rightRel Γ σ q₀.out γ₀ hrep z).symm
  have hq₀high : A₀ < normHeight F (σ⁻¹ • ((q₀.out : Γ) • z)) := by
    rw [hheightRep]
    exact hγ₀
  let p : Coord F := coordsX F z
  have hp : p ∈ posSet F := by
    intro w
    change 0 < height (z w)
    rw [height_eq_hyperbolicHeight]
    exact OAI.CubicEisenstein.hyperbolicHeight_pos (z w)
  have hpt : ptX F p = z := by
    rcases G1_h3_basics (F := F) with
      ⟨_, _, _, _, _, _, _, hptCoord, _, _, _, _⟩
    exact hptCoord z
  have hApos : 0 < A := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    (le_trans hA₀ hA)
  obtain ⟨T, hT⟩ := eisSeedDefect_local_sum Γ σ A hApos τ hτ s p hp
  obtain ⟨U, hconj⟩ := hT
  rcases hconj with ⟨hU, hconj⟩
  rcases hconj with ⟨hpU, hconj⟩
  rcases hconj with ⟨hUpos, hconj⟩
  rcases hconj with ⟨hTcenter, hlocal⟩
  have hdefLocal : eisSeedDefect F Γ σ τ s (ptX F p) =
      ∑ q ∈ T,
        (totalLap F (fun x => seedTerm F Γ σ τ s x q) (ptX F p) -
          spectralParameter F s * seedTerm F Γ σ τ s (ptX F p) q) := hlocal p hpU
  have hunique (q : CuspCosets F Γ σ) (hq : q ∈ T)
      (hqnz : totalLap F (fun x => seedTerm F Γ σ τ s x q) (ptX F p) -
        spectralParameter F s * seedTerm F Γ σ τ s (ptX F p) q ≠ 0) : q = q₀ := by
    have hband := seedTermDefect_height_band Γ σ A τ hτ s q (ptX F p) hqnz
    have hqhi : A₀ ≤ normHeight F (σ⁻¹ • ((q.out : Γ) • z)) := by
      have hcoord : normHeight F
          (σ⁻¹ • ((q.out : Γ) • (ptX F p))) =
            normHeight F (σ⁻¹ • ((q.out : Γ) • z)) := by rw [hpt]
      rw [← hcoord]
      exact le_trans hA hband.1
    have hq₀ : A₀ ≤ normHeight F (σ⁻¹ • ((q₀.out : Γ) • z)) := hq₀high.le
    have hstab := hsep q₀.out q.out z hq₀ hqhi
    have hrel : QuotientGroup.rightRel (cuspStab F Γ σ) q₀.out q.out :=
      QuotientGroup.rightRel_apply.mpr hstab
    calc
      q = Quotient.mk _ q.out := (Quotient.out_eq' q).symm
      _ = Quotient.mk _ q₀.out := (Quotient.sound hrel).symm
      _ = q₀ := Quotient.out_eq' q₀
  let R : CuspCosets F Γ σ → ℂ := fun q =>
    totalLap F (fun x => seedTerm F Γ σ τ s x q) (ptX F p) -
      spectralParameter F s * seedTerm F Γ σ τ s (ptX F p) q
  have hRzero (q : CuspCosets F Γ σ) (hqT : q ∈ T) (hqne : q ≠ q₀) :
      R q = 0 := by
    by_contra hnz
    have hqeq := hunique q hqT (by simpa [R] using hnz)
    exact hqne hqeq
  have hsumEq : (∑ q ∈ T, R q) = R q₀ := by
    by_cases hq₀T : q₀ ∈ T
    · apply Finset.sum_eq_single_of_mem q₀ hq₀T
      intro q hqT hqne
      exact hRzero q hqT hqne
    · have hRq₀ : R q₀ = 0 := by
        by_contra hnz
        have hband := seedTermDefect_height_band Γ σ A τ hτ s q₀ (ptX F p) (by simpa [R] using hnz)
        exact hq₀T (hTcenter q₀ hband.1)
      have hzeros : ∀ q ∈ T, R q = 0 := by
        intro q hqT
        by_cases hq : q = q₀
        · subst q
          exact (hq₀T hqT).elim
        · exact hRzero q hqT hq
      calc
        _ = 0 := Finset.sum_eq_zero hzeros
        _ = R q₀ := hRq₀.symm
  have hdefEq : eisSeedDefect F Γ σ τ s (ptX F p) = R q₀ := by
    rw [hdefLocal, hsumEq]
  refine ⟨q₀.out, ?_⟩
  calc
    eisSeedDefect F Γ σ τ s z = eisSeedDefect F Γ σ τ s (ptX F p) := by rw [hpt]
    _ = R q₀ := hdefEq
    _ = _ := by
      simpa [R, seedRadialDefect, hpt] using
        (seedTerm_lap_defect Γ σ τ hτ.1 s q₀ (ptX F p))

private theorem seedTerm_compact_bcf_entire
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (σ : SL(2,F))
    (A : ℝ) (τ : ℝ → ℝ) (hτ : IsCuspCutoff A τ)
    (K : Set (Coord F)) (hK : IsCompact K) (hKpos : K ⊆ posSet F)
    (q : CuspCosets F Γ σ) :
    ∃ Φ : ℂ → (K →ᵇ ℂ), AnalyticOnNhd ℂ Φ Set.univ ∧
      ∀ s p, Φ s p = seedTerm F Γ σ τ s (ptX F p.1) q := by
  classical
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let b : SL(2,F) := σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F))
  let H : Coord F → ℝ := fun p =>
    normHeight F (σ⁻¹ • ((q.out : Γ) • ptX F p))
  have hHbase : ContDiffOn ℝ ∞
      (fun p => normHeight F (b • ptX F p)) (posSet F) := seedHeight_action_smooth b
  have hHdef : H = fun p => normHeight F (b • ptX F p) := by
    funext p
    dsimp [H, b]
    rw [mul_smul]
    rfl
  have hH : ContDiffOn ℝ ∞ H (posSet F) := by
    rw [hHdef]
    exact hHbase
  have hHpos (p : Coord F) (hp : p ∈ posSet F) : 0 < H p := by
    dsimp [H]
    exact seedNormHeight_pos (σ⁻¹ • ((q.out : Γ) • ptX F p))
  have hHcont : Continuous (fun p : K => H p.1) :=
    hH.continuousOn.comp_continuous continuous_subtype_val
      (fun p => hKpos p.2)
  let hC : C(K,ℝ) := ⟨fun p => H p.1, hHcont⟩
  let hLog : C(K,ℂ) := ⟨fun p => (Real.log (H p.1) : ℂ), by
    have hlog : Continuous (fun p : K => Real.log (H p.1)) :=
      hHcont.log (fun p => (hHpos p.1 (hKpos p.2)).ne')
    exact Complex.ofRealCLM.continuous.comp hlog⟩
  let hTau : C(K,ℂ) := ⟨fun p => (τ (H p.1) : ℂ), by
    exact Complex.ofRealCLM.continuous.comp (hτ.1.continuous.comp hHcont)⟩
  let logB : K →ᵇ ℂ := BoundedContinuousFunction.mkOfCompact hLog
  let tauB : K →ᵇ ℂ := BoundedContinuousFunction.mkOfCompact hTau
  let Φ : ℂ → (K →ᵇ ℂ) := fun s =>
    tauB * NormedSpace.exp ((1 + 2 * s) • logB)
  have hArg : AnalyticOnNhd ℂ (fun s : ℂ => (1 + 2 * s) • logB) Set.univ := by
    intro s hs
    fun_prop
  have hExp : AnalyticOnNhd ℂ (fun s : ℂ =>
      NormedSpace.exp ((1 + 2 * s) • logB)) Set.univ := by
    intro s hs
    exact (NormedSpace.exp_analytic _).comp (hArg s hs)
  have hΦ : AnalyticOnNhd ℂ Φ Set.univ := by
    fun_prop
  refine ⟨Φ, hΦ, ?_⟩
  intro s p
  let ev : (K →ᵇ ℂ) →+* ℂ :=
    { toFun := fun f => f p
      map_one' := by simp
      map_mul' _ _ := by simp
      map_zero' := by simp
      map_add' _ _ := by simp }
  have hev : Continuous ev := by
    change Continuous (fun f : K →ᵇ ℂ => f p)
    exact (BoundedContinuousFunction.evalCLM ℂ p).continuous
  have hmap := NormedSpace.map_exp ev hev ((1 + 2 * s) • logB)
  have hexp : (NormedSpace.exp ((1 + 2 * s) • logB)) p =
      Complex.exp ((1 + 2 * s) * (Real.log (H p.1) : ℂ)) := by
    change ev (NormedSpace.exp ((1 + 2 * s) • logB)) = _
    rw [hmap]
    rw [← Complex.exp_eq_exp_ℂ]
    congr 1
  have hpow : (H p.1 : ℂ) ^ (1 + 2 * s) =
      Complex.exp ((1 + 2 * s) * (Real.log (H p.1) : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr
      (hHpos p.1 (hKpos p.2)).ne')]
    rw [← Complex.ofReal_log (le_of_lt (hHpos p.1 (hKpos p.2))), mul_comm]
  have hheight : H p.1 =
      normHeight F
        (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • ptX F p.1)) := rfl
  change tauB p * (NormedSpace.exp ((1 + 2 * s) • logB)) p = _
  rw [hexp]
  change (τ (H p.1) : ℂ) *
      Complex.exp ((1 + 2 * s) * (Real.log (H p.1) : ℂ)) = _
  simp only [seedTerm]
  rw [← hheight, hpow]

set_option maxHeartbeats 1000000 in
private theorem seedTerm_compact_deriv_bcf_entire
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (σ : SL(2,F))
    (A : ℝ) (τ : ℝ → ℝ) (hτ : IsCuspCutoff A τ)
    (K : Set (Coord F)) (hK : IsCompact K) (hKpos : K ⊆ posSet F)
    (q : CuspCosets F Γ σ) (n : ℕ) (v : Fin n → Coord F) :
    ∃ Φ : ℂ → (K →ᵇ ℂ), AnalyticOnNhd ℂ Φ Set.univ ∧
      ∀ s p, Φ s p = iteratedFDeriv ℝ n
        (fun x => seedTerm F Γ σ τ s (ptX F x) q) p.1 v := by
  classical
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let bmat : SL(2,F) := σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F))
  let H : Coord F → ℝ := fun p =>
    normHeight F (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • ptX F p))
  have hHbase : ContDiffOn ℝ ∞
      (fun p => normHeight F (bmat • ptX F p)) (posSet F) :=
    seedHeight_action_smooth bmat
  have hHdef : H = fun p => normHeight F (bmat • ptX F p) := by
    funext p
    dsimp [H, bmat]
    rw [mul_smul]
    rfl
  have hH : ContDiffOn ℝ ∞ H (posSet F) := by
    rw [hHdef]
    exact hHbase
  have hHpos (p : Coord F) (hp : p ∈ posSet F) : 0 < H p := by
    dsimp [H]
    exact seedNormHeight_pos
      (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • ptX F p))
  let b : Coord F → ℂ := fun p => (τ (H p) : ℂ)
  let ell : Coord F → ℂ := fun p => (Real.log (H p) : ℂ)
  have hb : ContDiffOn ℝ ∞ b (posSet F) := by
    have htauH : ContDiffOn ℝ ∞ (fun p => τ (H p)) (posSet F) := hτ.1.comp_contDiffOn hH
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn htauH
  have hell : ContDiffOn ℝ ∞ ell (posSet F) := by
    have hlog : ContDiffOn ℝ ∞ (fun p => Real.log (H p)) (posSet F) :=
      hH.log (fun p hp => (hHpos p hp).ne')
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn hlog
  have hcoeff (k : ℕ) : ContDiffOn ℝ ∞
      (seedExpCoeff b ell n v k) (posSet F) :=
    seedExpCoeff_contDiffOn b ell hb hell n v k
  have hcoeffCont (k : ℕ) : Continuous (fun p : K => seedExpCoeff b ell n v k p.1) :=
    (hcoeff k).continuousOn.comp_continuous continuous_subtype_val
      (fun p => hKpos p.2)
  let coeffC (k : ℕ) : C(K,ℂ) :=
    ⟨fun p => seedExpCoeff b ell n v k p.1, hcoeffCont k⟩
  let coeffB (k : ℕ) : K →ᵇ ℂ := BoundedContinuousFunction.mkOfCompact (coeffC k)
  have hcoeffBval (k : ℕ) (p : K) : coeffB k p = seedExpCoeff b ell n v k p.1 := rfl
  have hlogCont : Continuous (fun p : K => ell p.1) :=
    hell.continuousOn.comp_continuous continuous_subtype_val (fun p => hKpos p.2)
  let ellC : C(K,ℂ) := ⟨fun p => ell p.1, hlogCont⟩
  let ellB : K →ᵇ ℂ := BoundedContinuousFunction.mkOfCompact ellC
  have hellBval (p : K) : ellB p = ell p.1 := rfl
  let aParam : ℂ → ℂ := fun s => 1 + 2 * s
  let polyB : ℂ → (K →ᵇ ℂ) := fun s =>
    ∑ k ∈ Finset.range (n + 1), (aParam s) ^ k • coeffB k
  let expB : ℂ → (K →ᵇ ℂ) := fun s => NormedSpace.exp (aParam s • ellB)
  let Φ : ℂ → (K →ᵇ ℂ) := fun s => expB s * polyB s
  have harg : AnalyticOnNhd ℂ (fun s : ℂ => aParam s • ellB) Set.univ := by
    intro s hs
    fun_prop
  have hexp : AnalyticOnNhd ℂ expB Set.univ := by
    intro s hs
    exact (NormedSpace.exp_analytic _).comp (harg s hs)
  have hpoly : AnalyticOnNhd ℂ polyB Set.univ := by
    intro s hs
    fun_prop
  have hΦ : AnalyticOnNhd ℂ Φ Set.univ := by
    intro s hs
    exact (hexp s hs).mul (hpoly s hs)
  have hExpVal (s : ℂ) (p : K) : expB s p =
      Complex.exp (aParam s * ell p.1) := by
    let ev : (K →ᵇ ℂ) →+* ℂ :=
      { toFun := fun f => f p
        map_one' := by simp
        map_mul' _ _ := by simp
        map_zero' := by simp
        map_add' _ _ := by simp }
    have hev : Continuous ev := by
      change Continuous (fun f : K →ᵇ ℂ => f p)
      exact (BoundedContinuousFunction.evalCLM ℂ p).continuous
    have hmap := NormedSpace.map_exp ev hev (aParam s • ellB)
    have hsmul : ev (aParam s • ellB) = aParam s * ell p.1 := by
      change (aParam s • ellB) p = _
      simp [hellBval, smul_eq_mul]
    change ev (NormedSpace.exp (aParam s • ellB)) = _
    rw [hmap, hsmul, ← Complex.exp_eq_exp_ℂ]
  have hpolyVal (s : ℂ) (p : K) : polyB s p =
      ∑ k ∈ Finset.range (n + 1), (aParam s) ^ k * seedExpCoeff b ell n v k p.1 := by
    simp [polyB, Finset.sum_apply, BoundedContinuousFunction.sum_apply,
      coeffB, hcoeffBval, smul_eq_mul]
  have hEqProfile (s : ℂ) (p : Coord F) (hp : p ∈ posSet F) :
      seedTerm F Γ σ τ s (ptX F p) q = b p * Complex.exp (aParam s * ell p) := by
    have hpow := seedLogProfile_log τ (aParam s) (hHpos p hp)
    change (τ (H p) : ℂ) * (H p : ℂ) ^ (aParam s) =
      (τ (H p) : ℂ) * Complex.exp (aParam s * (Real.log (H p) : ℂ))
    rw [← hpow]
    simp [seedLogProfile, Real.exp_log (hHpos p hp)]
  refine ⟨Φ, hΦ, ?_⟩
  intro s p
  have hlocalEq :
      (fun x => seedTerm F Γ σ τ s (ptX F x) q) =ᶠ[𝓝 p.1]
        (fun x => b x * Complex.exp (aParam s * ell x)) := by
    filter_upwards [ArtinPrimitiveRoots.Proofs.spec_seed_p.posSet_isOpen.mem_nhds
      (hKpos p.2)]
      with x hx
    exact hEqProfile s x hx
  have hderivEq := hlocalEq.iteratedFDeriv ℝ n
  have hderivAt := congrArg (fun D => D v) hderivEq.eq_of_nhds
  have hprofile := seedExpProfile_iteratedFDeriv b ell hb hell (aParam s) n v p.1
    (hKpos p.2)
  calc
    Φ s p = Complex.exp (aParam s * ell p.1) *
        (∑ k ∈ Finset.range (n + 1), (aParam s)^k * seedExpCoeff b ell n v k p.1) := by
      simp only [Φ, BoundedContinuousFunction.mul_apply]
      rw [hExpVal, hpolyVal]
    _ = iteratedFDeriv ℝ n
        (fun x => b x * Complex.exp (aParam s * ell x)) p.1 v := hprofile.symm
    _ = iteratedFDeriv ℝ n
        (fun x => seedTerm F Γ σ τ s (ptX F x) q) p.1 v := hderivAt.symm

private theorem eisSeed_compact_local_sum
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (σ : SL(2,F))
    (A : ℝ) (hA : 0 < A) (τ : ℝ → ℝ) (hτ : IsCuspCutoff A τ)
    (K : Set (Coord F)) (hK : IsCompact K) (hKpos : K ⊆ posSet F) :
    ∃ T : Finset (CuspCosets F Γ σ),
      ∀ s p, p ∈ K → eisSeed F Γ σ τ s (ptX F p) =
        ∑ q ∈ T, seedTerm F Γ σ τ s (ptX F p) q := by
  classical
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  rcases G1_h3_basics (F := F) with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hchart⟩
  obtain ⟨e, he, _⟩ := hchart
  let posCoord : K → PosCoord (F := F) := fun p => ⟨p.1, hKpos p.2⟩
  have hposCoord : Continuous posCoord :=
    Continuous.subtype_mk continuous_subtype_val (fun p => hKpos p.2)
  have hpt : Continuous (fun p : K => ptX F p.1) := by
    exact e.continuous.comp hposCoord |>.congr fun p => by
      simpa [posCoord] using he (posCoord p)
  let Kx : Set (X F) := Set.range (fun p : K => ptX F p.1)
  have hKx : IsCompact Kx := by
    change IsCompact (Set.range (fun p : K => ptX F p.1))
    exact isCompact_range hpt
  let Q : Set (CuspCosets F Γ σ) :=
    {q | ∃ z ∈ Kx, A ≤ normHeight F
      (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • z))}
  have hQ : Q.Finite :=
    (R10_cusp_separation (F := F) Γ).2.2 σ Kx hKx A hA
  let T : Finset (CuspCosets F Γ σ) := hQ.toFinset
  have hzero (s : ℂ) (p : Coord F) (hp : p ∈ K)
      (q : CuspCosets F Γ σ) (hq : q ∉ T) :
      seedTerm F Γ σ τ s (ptX F p) q = 0 := by
    have hqQ : q ∉ Q := by simpa [T] using hq
    have hptmem : ptX F p ∈ Kx := ⟨⟨p, hp⟩, rfl⟩
    have hnot : ¬ A ≤ normHeight F
        (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • ptX F p)) := by
      intro hhigh
      exact hqQ ⟨ptX F p, hptmem, hhigh⟩
    have hlt : normHeight F
        (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • ptX F p)) < A := lt_of_not_ge hnot
    simp [seedTerm, hτ.2.2.1 _ hlt.le]
  refine ⟨T, ?_⟩
  intro s p hp
  unfold eisSeed
  exact tsum_eq_sum (s := T) (fun q hq => hzero s p hp q hq)

private theorem eisSeed_compact_bcf_entire
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (σ : SL(2,F))
    (A : ℝ) (hA : 0 < A) (τ : ℝ → ℝ) (hτ : IsCuspCutoff A τ)
    (K : Set (Coord F)) (hK : IsCompact K) (hKpos : K ⊆ posSet F) :
    ∃ Φ : ℂ → (K →ᵇ ℂ), AnalyticOnNhd ℂ Φ Set.univ ∧
      ∀ s p, Φ s p = eisSeed F Γ σ τ s (ptX F p.1) := by
  classical
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨T, hlocal⟩ := eisSeed_compact_local_sum Γ σ A hA τ hτ K hK hKpos
  let f : CuspCosets F Γ σ → ℂ → (K →ᵇ ℂ) := fun q =>
    Classical.choose (seedTerm_compact_bcf_entire Γ σ A τ hτ K hK hKpos q)
  have hfa (q : CuspCosets F Γ σ) (hq : q ∈ T) :
      AnalyticOnNhd ℂ (f q) Set.univ := by
    exact (Classical.choose_spec
      (seedTerm_compact_bcf_entire Γ σ A τ hτ K hK hKpos q)).1
  have hfval (q : CuspCosets F Γ σ) (s : ℂ) (p : K) :
      f q s p = seedTerm F Γ σ τ s (ptX F p.1) q :=
    (Classical.choose_spec
      (seedTerm_compact_bcf_entire Γ σ A τ hτ K hK hKpos q)).2 s p
  let Φ : ℂ → (K →ᵇ ℂ) := ∑ q ∈ T, f q
  have hΦ : AnalyticOnNhd ℂ Φ Set.univ := by
    exact Finset.analyticOnNhd_sum T (fun q hq => hfa q hq)
  refine ⟨Φ, hΦ, ?_⟩
  intro s p
  calc
    Φ s p = ∑ q ∈ T, seedTerm F Γ σ τ s (ptX F p.1) q := by
      simp only [Φ, Finset.sum_apply, BoundedContinuousFunction.sum_apply]
      apply Finset.sum_congr rfl
      intro q hq
      exact hfval q s p
    _ = eisSeed F Γ σ τ s (ptX F p.1) := (hlocal s p.1 p.2).symm

set_option maxHeartbeats 1000000 in
private theorem eisSeed_compact_deriv_bcf_entire
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (σ : SL(2,F))
    (A : ℝ) (hA : 0 < A) (τ : ℝ → ℝ) (hτ : IsCuspCutoff A τ)
    (K : Set (Coord F)) (hK : IsCompact K) (hKpos : K ⊆ posSet F)
    (n : ℕ) (v : Fin n → Coord F) :
    ∃ Φ : ℂ → (K →ᵇ ℂ), AnalyticOnNhd ℂ Φ Set.univ ∧
      ∀ s p, Φ s p = iteratedFDeriv ℝ n
        (fun q => eisSeed F Γ σ τ s (ptX F q)) p.1 v := by
  classical
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨T, hlocal⟩ := eisSeed_compact_local_sum_open Γ σ A hA τ hτ K hK hKpos
  let f : CuspCosets F Γ σ → ℂ → (K →ᵇ ℂ) := fun q =>
    Classical.choose
      (seedTerm_compact_deriv_bcf_entire Γ σ A τ hτ K hK hKpos q n v)
  have hfa (q : CuspCosets F Γ σ) (hq : q ∈ T) :
      AnalyticOnNhd ℂ (f q) Set.univ := by
    exact (Classical.choose_spec
      (seedTerm_compact_deriv_bcf_entire Γ σ A τ hτ K hK hKpos q n v)).1
  have hfval (q : CuspCosets F Γ σ) (s : ℂ) (p : K) :
      f q s p = iteratedFDeriv ℝ n
        (fun x => seedTerm F Γ σ τ s (ptX F x) q) p.1 v :=
    (Classical.choose_spec
      (seedTerm_compact_deriv_bcf_entire Γ σ A τ hτ K hK hKpos q n v)).2 s p
  let Φ : ℂ → (K →ᵇ ℂ) := ∑ q ∈ T, f q
  have hΦ : AnalyticOnNhd ℂ Φ Set.univ :=
    Finset.analyticOnNhd_sum T (fun q hq => hfa q hq)
  refine ⟨Φ, hΦ, ?_⟩
  intro s p
  obtain ⟨U, hUopen, hpU, hUpos, hlocalSeed⟩ := hlocal p.1 p.2
  have hlocalEq :
      (fun x => eisSeed F Γ σ τ s (ptX F x)) =ᶠ[𝓝 p.1]
        (fun x => ∑ q ∈ T, seedTerm F Γ σ τ s (ptX F x) q) := by
    filter_upwards [hUopen.mem_nhds hpU] with x hx
    exact hlocalSeed s x hx
  have hderivEq := hlocalEq.iteratedFDeriv ℝ n
  have hderivAt := congrArg (fun D => D v) hderivEq.eq_of_nhds
  have htermAt (q : CuspCosets F Γ σ) (hq : q ∈ T) :
      ContDiffAt ℝ ∞ (fun x => seedTerm F Γ σ τ s (ptX F x) q) p.1 := by
    have hsmooth : IsSmoothX F (fun z => seedTerm F Γ σ τ s z q) := by
      simpa only [one_smul] using seedTerm_smooth_action Γ σ 1 τ hτ.1 s q
    change ContDiffOn ℝ ∞ (fun x => seedTerm F Γ σ τ s (ptX F x) q) (posSet F) at hsmooth
    exact (hsmooth p.1 (hKpos p.2)).contDiffAt
      (ArtinPrimitiveRoots.Proofs.spec_seed_p.posSet_isOpen.mem_nhds (hKpos p.2))
  have hsumDeriv :
      iteratedFDeriv ℝ n (fun x => ∑ q ∈ T, seedTerm F Γ σ τ s (ptX F x) q) p.1 =
        ∑ q ∈ T, iteratedFDeriv ℝ n
          (fun x => seedTerm F Γ σ τ s (ptX F x) q) p.1 :=
    iteratedFDeriv_fun_sum_apply (fun q hq => (htermAt q hq).of_le (by simp))
  have hsumAt0 := congrArg (fun D => D v) hsumDeriv
  have hsumEval :
      (∑ q ∈ T, iteratedFDeriv ℝ n
        (fun x => seedTerm F Γ σ τ s (ptX F x) q) p.1) v =
        ∑ q ∈ T, (iteratedFDeriv ℝ n
          (fun x => seedTerm F Γ σ τ s (ptX F x) q) p.1) v := by
    induction T using Finset.induction_on with
    | empty => simp
    | @insert q T hq ih =>
        simp [Finset.sum_insert, hq, ih]
  have hsumAt :
      (iteratedFDeriv ℝ n
        (fun x => ∑ q ∈ T, seedTerm F Γ σ τ s (ptX F x) q) p.1) v =
        ∑ q ∈ T, (iteratedFDeriv ℝ n
          (fun x => seedTerm F Γ σ τ s (ptX F x) q) p.1) v :=
    hsumAt0.trans hsumEval
  calc
    Φ s p = ∑ q ∈ T, iteratedFDeriv ℝ n
        (fun x => seedTerm F Γ σ τ s (ptX F x) q) p.1 v := by
      simp only [Φ, Finset.sum_apply, BoundedContinuousFunction.sum_apply]
      apply Finset.sum_congr rfl
      intro q hq
      exact hfval q s p
    _ = iteratedFDeriv ℝ n
        (fun x => ∑ q ∈ T, seedTerm F Γ σ τ s (ptX F x) q) p.1 v := by
      exact hsumAt.symm
    _ = iteratedFDeriv ℝ n
        (fun x => eisSeed F Γ σ τ s (ptX F x)) p.1 v := hderivAt.symm

theorem e5AnalyticClauses
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (σ : SL(2,F)) (A₀ A : ℝ) (hA₀ : 1 ≤ A₀) (hA : A₀ ≤ A)
    (hsep : ∀ γ γ' : Γ, ∀ z : X F,
      A₀ ≤ normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
      A₀ ≤ normHeight F (σ⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
      γ' * γ⁻¹ ∈ cuspStab F Γ σ)
    (τ : ℝ → ℝ) (hτ : IsCuspCutoff A τ) :
    (∃ G : ℂ → L2Space F D, AnalyticOnNhd ℂ G Set.univ ∧
      ∀ s, ∀ᵐ z ∂(volX F), z ∈ D → G s z = eisSeedDefect F Γ σ τ s z) ∧
    (∀ K : Set (Coord F), IsCompact K → K ⊆ posSet F →
      ∀ n : ℕ, ∀ v : Fin n → Coord F,
        ∃ Φ : ℂ → (K →ᵇ ℂ), AnalyticOnNhd ℂ Φ Set.univ ∧
          ∀ s p, Φ s p = iteratedFDeriv ℝ n
            (fun q => eisSeed F Γ σ τ s (ptX F q)) p v) := by
  refine ⟨?_, ?_⟩
  · exact eisSeedDefect_l2_entire Γ D hD σ A₀ A hA₀ hA hsep τ hτ
  · intro K hK hKpos n v
    exact eisSeed_compact_deriv_bcf_entire Γ σ A (lt_of_lt_of_le
      (by norm_num : (0 : ℝ) < 1) (le_trans hA₀ hA)) τ hτ K hK hKpos n v

theorem e5EasyClauses
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (σ : SL(2,F)) (A₀ A : ℝ) (hA₀ : 1 ≤ A₀) (hA : A₀ ≤ A)
    (hsep : ∀ γ γ' : Γ, ∀ z : X F,
      A₀ ≤ normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
      A₀ ≤ normHeight F (σ⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
      γ' * γ⁻¹ ∈ cuspStab F Γ σ)
    (τ : ℝ → ℝ) (hτ : IsCuspCutoff A τ) :
    (∀ s z,
      {q : CuspCosets F Γ σ | seedTerm F Γ σ τ s z q ≠ 0}.Finite ∧
      (Nat.card {q : CuspCosets F Γ σ | seedTerm F Γ σ τ s z q ≠ 0} ≤ 1)) ∧
    (∀ s, IsSmoothX F (eisSeed F Γ σ τ s) ∧
      IsGammaInvariant F Γ (eisSeed F Γ σ τ s) ∧
      ∀ z, totalLap F (eisSeed F Γ σ τ s) z -
        spectralParameter F s * eisSeed F Γ σ τ s z = eisSeedDefect F Γ σ τ s z) ∧
    (∃ K : Set (X F), IsCompact K ∧ ∀ s,
      {z | eisSeedDefect F Γ σ τ s z ≠ 0} ⊆ orbitSaturation F Γ K) ∧
    (∀ s z, z ∈ cuspTail F Γ σ A₀ →
      ∃ γ : Γ,
        eisSeedDefect F Γ σ τ s z =
          -(placeCount F : ℂ) *
            (((normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) : ℝ) : ℂ) ^ 2 *
                deriv (deriv (fun t : ℝ => (τ t : ℂ)))
                  (normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z))) +
              (1 + 4 * s) *
                ((normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) : ℝ) : ℂ) *
                deriv (fun t : ℝ => (τ t : ℂ))
                  (normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) ) ) *
            ((normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) : ℝ) : ℂ) ^ (1 + 2 * s)) := by
  refine ⟨?_, ?_⟩
  · intro s z
    exact seedActiveFiniteOne Γ σ A₀ A hA₀ hA hsep τ hτ s z
  refine ⟨?_, ?_⟩
  · intro s
    refine ⟨eisSeed_isSmooth Γ σ A (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (le_trans hA₀ hA)) τ hτ s, ?_⟩
    refine ⟨eisSeed_isGammaInvariant Γ σ τ s, ?_⟩
    intro z
    rfl
  refine ⟨eisSeedDefect_compactSupport Γ σ A₀ A hA₀ hA τ hτ, ?_⟩
  intro s z hz
  obtain ⟨γ, hγ⟩ := eisSeedDefect_tail_formula Γ σ A₀ A hA₀ hA hsep τ hτ s z hz
  refine ⟨γ, ?_⟩
  rw [hγ]
  simp only [seedRadialDefect]
  ring

end ArtinPrimitiveRoots.Proofs.spec_seed_p
