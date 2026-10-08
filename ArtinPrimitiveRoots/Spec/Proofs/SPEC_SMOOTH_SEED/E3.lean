import ArtinPrimitiveRoots.Spec.Energy
import Mathlib.Analysis.Normed.Operator.CompleteCodomain
import OAI.NumberTheory.DirichletL.Eisenstein.SeedHeight

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

end ArtinPrimitiveRoots.Proofs.spec_seed_p
