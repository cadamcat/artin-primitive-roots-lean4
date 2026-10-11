import ArtinPrimitiveRoots.TypeII.Proofs.«PD-HIGH».Defs
import Mathlib.MeasureTheory.Measure.Real

set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
open MeasureTheory
open ArtinPrimitiveRoots.TypeII
open scoped ENNReal
noncomputable section

private theorem pd5_majorArc_measurable (x Y A₀ : ℝ) :
    MeasurableSet {θ : ℝ | majorArc x Y A₀ θ} := by
  let T := Real.rpow (Real.log x) A₀
  let r := 2 * T / Y
  have hclosed (h : ℤ) (k : ℕ) (z : ℤ) :
      MeasurableSet {θ : ℝ | |θ - (h : ℝ) / k - z| ≤ r} := by
    apply measurableSet_le
    · exact (continuous_abs.comp
        ((continuous_id.sub continuous_const).sub continuous_const)).measurable
    · exact measurable_const
  have hEq : {θ : ℝ | majorArc x Y A₀ θ} =
      ⋃ h : ℤ, ⋃ k : ℕ, ⋃ z : ℤ,
        if 1 ≤ k ∧ (k : ℝ) ≤ T ∧ Int.gcd h k = 1 then
          {θ : ℝ | |θ - (h : ℝ) / k - z| ≤ r} else ∅ := by
    ext θ
    simp [majorArc, T, r, Set.mem_iUnion, and_assoc]
  rw [hEq]
  exact MeasurableSet.iUnion fun h => MeasurableSet.iUnion fun k =>
    MeasurableSet.iUnion fun z => by
      by_cases hc : 1 ≤ k ∧ (k : ℝ) ≤ T ∧ Int.gcd h k = 1
      · simpa [hc] using hclosed h k z
      · simp [hc]

private theorem pd5_additiveCharacter_norm (t : ℝ) :
    ‖additiveCharacter t‖ = 1 := by
  simp [additiveCharacter, Complex.norm_exp, Complex.mul_re]

private def pd5_majorArcCenters (T : ℝ) : Finset (ℕ × ℤ) :=
  ((Finset.range (Nat.floor T + 1)).filter (fun k => 0 < k)).biUnion fun k =>
    (Finset.Icc (-(k : ℤ)) (2 * (k : ℤ))).image fun m => (k, m)

private theorem pd5_majorArc_cover (x Y A₀ : ℝ)
    (hT : 1 ≤ Real.rpow (Real.log x) A₀)
    (hrad : 2 * Real.rpow (Real.log x) A₀ / Y ≤ 1) :
    {θ : ℝ | majorArc x Y A₀ θ} ∩ Set.Ioc 0 1 ⊆
      ⋃ i ∈ pd5_majorArcCenters (Real.rpow (Real.log x) A₀),
        Set.Icc ((i.2 : ℝ) / i.1 -
          2 * Real.rpow (Real.log x) A₀ / Y)
          ((i.2 : ℝ) / i.1 + 2 * Real.rpow (Real.log x) A₀ / Y) := by
  intro θ hθ
  rcases hθ with ⟨hθarc, hθ01⟩
  rcases hθarc with ⟨h, k, hk, hkT, hgcd, z, hz⟩
  let T := Real.rpow (Real.log x) A₀
  let r := 2 * T / Y
  let m : ℤ := h + (k : ℤ) * z
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hr : r ≤ 1 := by simpa [r, T] using hrad
  have hkfloor : k ≤ Nat.floor T := (Nat.le_floor_iff (by linarith : 0 ≤ T)).2 hkT
  have hkmem : k ∈ (Finset.range (Nat.floor T + 1)).filter (fun n => 0 < n) := by
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by omega⟩
  have hcenter : (m : ℝ) / k = (h : ℝ) / k + z := by
    dsimp [m]
    push_cast
    field_simp
  have hzle : |θ - (h : ℝ) / k - z| ≤ r := by simpa [T, r] using hz
  have hcenterBounds : -1 ≤ (m : ℝ) / k ∧ (m : ℝ) / k ≤ 2 := by
    rw [hcenter]
    have habs := abs_le.mp hzle
    constructor <;> rcases hθ01 with ⟨hθ0, hθ1⟩ <;> linarith
  have hmlo : -(k : ℝ) ≤ (m : ℝ) := by
    simpa using (le_div_iff₀ hkpos).mp hcenterBounds.1
  have hmhi : (m : ℝ) ≤ 2 * k := by
    exact (div_le_iff₀ hkpos).mp hcenterBounds.2
  have hmIcc : m ∈ Finset.Icc (-(k : ℤ)) (2 * (k : ℤ)) := by
    rw [Finset.mem_Icc]
    exact ⟨by exact_mod_cast hmlo, by exact_mod_cast hmhi⟩
  have hmem : (k, m) ∈ pd5_majorArcCenters T := by
    apply Finset.mem_biUnion.mpr
    refine ⟨k, hkmem, ?_⟩
    exact Finset.mem_image.mpr ⟨m, hmIcc, rfl⟩
  simp only [Set.mem_iUnion]
  refine ⟨(k, m), ?_, ?_⟩
  · simpa [T] using hmem
  · change θ ∈ Set.Icc ((m : ℝ) / (k : ℝ) - r) ((m : ℝ) / (k : ℝ) + r)
    have habs : |θ - (m : ℝ) / (k : ℝ)| ≤ r := by
      rw [hcenter]
      convert hzle using 1 <;> ring
    rw [Set.mem_Icc]
    constructor <;> rcases hθ01 with ⟨hθ0, hθ1⟩ <;>
      have habs' := abs_le.mp habs <;> linarith

private theorem pd5_majorArcCenters_card (T : ℝ) (hT : 1 ≤ T) :
    (pd5_majorArcCenters T).card ≤ 8 * T ^ 2 := by
  let N := Nat.floor T
  let ks := (Finset.range (N + 1)).filter (fun k => 0 < k)
  have hTnonneg : 0 ≤ T := by linarith
  have hNleT : (N : ℝ) ≤ T := Nat.floor_le hTnonneg
  have hNpos : 1 ≤ N := (Nat.le_floor_iff hTnonneg).2 (by exact_mod_cast hT)
  have hNpos' : 0 < N := by omega
  have hksCard : ks.card ≤ N + 1 := by
    dsimp [ks]
    exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
  have hnum (k : ℕ) (hk : k ∈ ks) :
      ((Finset.Icc (-(k : ℤ)) (2 * (k : ℤ))).image fun m => (k, m)).card ≤ 4 * N := by
    have hkpos : 0 < k := (Finset.mem_filter.mp hk).2
    have hkle : k ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hk).1)
    have hcardInt :
        ((Finset.Icc (-(k : ℤ)) (2 * (k : ℤ))).card : ℤ) = 3 * (k : ℤ) + 1 := by
      rw [Int.card_Icc_of_le (-(k : ℤ)) (2 * (k : ℤ)) (by omega)]
      ring
    have hcardBoundInt :
        ((Finset.Icc (-(k : ℤ)) (2 * (k : ℤ))).card : ℤ) ≤ (4 * N : ℕ) := by
      rw [hcardInt]
      have hkle' : (k : ℤ) ≤ N := by exact_mod_cast hkle
      omega
    have hcardBound :
        (Finset.Icc (-(k : ℤ)) (2 * (k : ℤ))).card ≤ 4 * N := by
      exact_mod_cast hcardBoundInt
    exact (Finset.card_image_le).trans hcardBound
  have hcardNat : (pd5_majorArcCenters T).card ≤ 8 * N ^ 2 := by
    dsimp [pd5_majorArcCenters, N]
    calc
      _ ≤ ks.card * (4 * Nat.floor T) :=
        Finset.card_biUnion_le_card_mul ks _ _ (by simpa [N] using hnum)
      _ ≤ (N + 1) * (4 * N) := Nat.mul_le_mul_right _ hksCard
      _ ≤ 8 * N ^ 2 := by nlinarith
  have hcardReal : ((pd5_majorArcCenters T).card : ℝ) ≤ 8 * (N : ℝ) ^ 2 := by
    exact_mod_cast hcardNat
  calc
    ((pd5_majorArcCenters T).card : ℝ) ≤ 8 * (N : ℝ) ^ 2 := hcardReal
    _ ≤ 8 * T ^ 2 := by nlinarith [sq_nonneg (T - (N : ℝ))]

private theorem pd5_majorArc_volume_bound (x Y A₀ : ℝ)
    (hY : 1 ≤ Y) (hT : 1 ≤ Real.rpow (Real.log x) A₀)
    (hrad : 2 * Real.rpow (Real.log x) A₀ / Y ≤ 1) :
    volume.real ({θ : ℝ | majorArc x Y A₀ θ} ∩ Set.Ioc 0 1) ≤
      32 * (Real.rpow (Real.log x) A₀) ^ 3 / Y := by
  let T := Real.rpow (Real.log x) A₀
  let r := 2 * T / Y
  let C := pd5_majorArcCenters T
  have hTpos : 0 < T := by linarith
  have hYpos : 0 < Y := by linarith
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hCover : {θ : ℝ | majorArc x Y A₀ θ} ∩ Set.Ioc 0 1 ⊆
      ⋃ i ∈ C, Set.Icc ((i.2 : ℝ) / i.1 - r) ((i.2 : ℝ) / i.1 + r) := by
    simpa [C, T, r] using pd5_majorArc_cover x Y A₀ hT hrad
  have hCoverNotTop : volume
      (⋃ i ∈ C, Set.Icc ((i.2 : ℝ) / i.1 - r) ((i.2 : ℝ) / i.1 + r)) ≠ ∞ := by
    exact (MeasureTheory.measure_biUnion_lt_top C.finite_toSet
      (fun _ _ => measure_Icc_lt_top)).ne
  have hMeasure := MeasureTheory.measureReal_mono hCover hCoverNotTop
  calc
    volume.real ({θ : ℝ | majorArc x Y A₀ θ} ∩ Set.Ioc 0 1) ≤
        volume.real (⋃ i ∈ C,
          Set.Icc ((i.2 : ℝ) / i.1 - r) ((i.2 : ℝ) / i.1 + r)) := hMeasure
    _ ≤ ∑ i ∈ C, volume.real
          (Set.Icc ((i.2 : ℝ) / i.1 - r) ((i.2 : ℝ) / i.1 + r)) :=
        MeasureTheory.measureReal_biUnion_finset_le C _
    _ = ∑ _i ∈ C, 4 * T / Y := by
      apply Finset.sum_congr rfl
      intro i hi
      have hwidth : ((i.2 : ℝ) / i.1 - r) ≤ ((i.2 : ℝ) / i.1 + r) := by linarith
      rw [Real.volume_real_Icc_of_le hwidth]
      dsimp [r]
      ring
    _ = (C.card : ℝ) * (4 * T / Y) := by simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (8 * T ^ 2) * (4 * T / Y) := by
      exact mul_le_mul_of_nonneg_right
        (by simpa [C, T] using pd5_majorArcCenters_card T hT) (by positivity)
    _ = 32 * T ^ 3 / Y := by ring

/-- Elementary major-arc volume bound, retaining the actual integer-lift definition and
finite interval integral. Uses measurable
countable unions of closed intervals, at most 4k centres for each denominator k, and the
unit norm of additiveCharacter. Feeds pd5_edge_position_mass_le and positive edge rows. -/
theorem pd5_majorKernel_volume_bound (x Y A₀ P t : ℝ) (a b : ℕ) (psi : ℝ → ℝ)
    (hx : 2 ≤ x) (hY : 1 ≤ Y) (hT : 1 ≤ Real.rpow (Real.log x) A₀)
    (hrad : 2 * Real.rpow (Real.log x) A₀ / Y ≤ 1) (hP : 0 ≤ P)
    (hpsi : ∀ u : ℝ, |psi u| ≤ P) :
    ‖majorKernel x Y A₀ t a b psi‖ ≤
      32 * P * (Real.rpow (Real.log x) A₀) ^ 3 / Y := by
  let T := Real.rpow (Real.log x) A₀
  let M : Set ℝ := {θ | majorArc x Y A₀ θ}
  let f : ℝ → ℂ := M.indicator (fun θ => additiveCharacter (θ * (t - (b : ℝ) + (a : ℝ))))
  let g : ℝ → ℝ := M.indicator (fun _ => (1 : ℝ))
  have hM : MeasurableSet M := by
    simpa [M] using pd5_majorArc_measurable x Y A₀
  have hfg (θ : ℝ) : ‖f θ‖ ≤ g θ := by
    by_cases hθ : θ ∈ M
    · simp [f, g, hθ, pd5_additiveCharacter_norm]
    · simp [f, g, hθ]
  have hgMeas : Measurable g := measurable_const.indicator hM
  have hgbdd : ∀ᵐ θ ∂volume.restrict (Set.Ioc (0 : ℝ) 1), ‖g θ‖ ≤ (1 : ℝ) := by
    filter_upwards with θ
    by_cases hθ : θ ∈ M <;> simp [g, hθ]
  have hgOn : IntegrableOn g (Set.Ioc 0 1) volume := by
    exact Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
      hgMeas.aestronglyMeasurable hgbdd
  have hgInt : IntervalIntegrable g volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le
      (μ := volume) (f := g) (by norm_num)).2 hgOn
  have hAE : ∀ᵐ θ ∂volume.restrict (Set.uIoc (0 : ℝ) 1), ‖f θ‖ ≤ g θ :=
    Filter.Eventually.of_forall hfg
  have hIntegral : ‖∫ θ in (0 : ℝ)..1, f θ ∂volume‖ ≤
      |∫ θ in (0 : ℝ)..1, g θ ∂volume| :=
    intervalIntegral.norm_integral_le_abs_of_norm_le hAE hgInt
  have hGIntegral : ∫ θ in (0 : ℝ)..1, g θ ∂volume =
      volume.real (M ∩ Set.Ioc 0 1) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      ← integral_indicator measurableSet_Ioc]
    have hind : (Set.Ioc (0 : ℝ) 1).indicator g =
        (M ∩ Set.Ioc 0 1).indicator (fun _ => (1 : ℝ)) := by
      funext θ
      by_cases hθI : θ ∈ Set.Ioc (0 : ℝ) 1 <;> by_cases hθM : θ ∈ M <;>
        simp [g, hθI, hθM]
    rw [hind]
    change ∫ θ, (M ∩ Set.Ioc 0 1).indicator 1 θ ∂volume = _
    exact integral_indicator_one (μ := volume) (s := M ∩ Set.Ioc 0 1)
      (hM.inter measurableSet_Ioc)
  have hVol := pd5_majorArc_volume_bound x Y A₀ hY hT hrad
  have hIntNonneg : 0 ≤ ∫ θ in (0 : ℝ)..1, g θ ∂volume := by
    rw [hGIntegral]
    exact MeasureTheory.measureReal_nonneg
  have hGbound : ∫ θ in (0 : ℝ)..1, g θ ∂volume ≤ 32 * T ^ 3 / Y := by
    rw [hGIntegral]
    simpa [M, T] using hVol
  have hIntBound : ‖∫ θ in (0 : ℝ)..1, f θ ∂volume‖ ≤ 32 * T ^ 3 / Y := by
    calc
      ‖∫ θ in (0 : ℝ)..1, f θ ∂volume‖ ≤
          |∫ θ in (0 : ℝ)..1, g θ ∂volume| := hIntegral
      _ = ∫ θ in (0 : ℝ)..1, g θ ∂volume := abs_of_nonneg hIntNonneg
      _ ≤ 32 * T ^ 3 / Y := hGbound
  have hKernelEq : majorKernel x Y A₀ t a b psi =
      (psi (t / Y) : ℂ) * ∫ θ in (0 : ℝ)..1, f θ ∂volume := by
    simp [majorKernel, f, M, Set.indicator]
  calc
    ‖majorKernel x Y A₀ t a b psi‖ =
        ‖(psi (t / Y) : ℂ)‖ * ‖∫ θ in (0 : ℝ)..1, f θ ∂volume‖ := by
      rw [hKernelEq, norm_mul]
    _ ≤ P * (32 * T ^ 3 / Y) := by
      apply mul_le_mul
      · simpa [Complex.norm_real, Real.norm_eq_abs] using hpsi (t / Y)
      · exact hIntBound
      · exact norm_nonneg _
      · exact hP
    _ = 32 * P * (Real.rpow (Real.log x) A₀) ^ 3 / Y := by
      dsimp [T]
      ring

end
end ArtinPrimitiveRoots.TypeII.PD
