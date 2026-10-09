import Mathlib
import ArtinPrimitiveRoots.Sieve.Density.B_DENSITY.Coordinates

/-! Finite rectangular approximations of the reciprocal simplex integral. -/

namespace ArtinPrimitiveRoots.Proofs.b_density_sol

open MeasureTheory Filter
open scoped Topology

noncomputable def exponentGridLower {k : ℕ} (γ : ℝ) (n : ℕ)
    (u : Fin k → ℕ) : Fin k → ℝ := fun i => γ + (u i : ℝ) / n

noncomputable def exponentGridUpper {k : ℕ} (γ : ℝ) (n : ℕ)
    (u : Fin k → ℕ) : Fin k → ℝ := fun i => γ + ((u i + 1 : ℕ) : ℝ) / n

noncomputable def exponentBoxSet {k : ℕ} (a b : Fin k → ℝ) : Set (Fin k → ℝ) :=
  Set.pi Set.univ fun i => Set.Ioc (a i) (b i)

lemma volume_simplexCoordinate_level {k : ℕ} {γ : ℝ}
    (hγ : 0 < γ) (hγ1 : γ < 1) (c : Option (Fin k)) :
    volume {x : Fin k → ℝ | simplexCoordinate x c = γ} = 0 := by
  let S : AffineSubspace ℝ (Fin k → ℝ) :=
    ({γ} : AffineSubspace ℝ ℝ).comap (simplexCoordinateAffine c)
  have hcoe : (S : Set (Fin k → ℝ)) =
      {x : Fin k → ℝ | simplexCoordinate x c = γ} := by
    ext x
    simp [S, AffineSubspace.mem_comap, simplexCoordinateAffine_apply]
  have hproper : S ≠ ⊤ := by
    intro htop
    have htopSet : (S : Set (Fin k → ℝ)) = Set.univ :=
      congrArg (fun T : AffineSubspace ℝ (Fin k → ℝ) => (T : Set (Fin k → ℝ))) htop
    have hmem : (0 : Fin k → ℝ) ∈ (S : Set (Fin k → ℝ)) := by
      rw [htopSet]
      simp
    rw [hcoe] at hmem
    cases c with
    | none => simp [simplexCoordinate] at hmem; linarith
    | some i => simp [simplexCoordinate] at hmem; linarith
  rw [← hcoe]
  exact MeasureTheory.Measure.addHaar_affineSubspace volume S hproper

lemma ae_simplexCoordinate_ne_level {k : ℕ} {γ : ℝ}
    (hγ : 0 < γ) (hγ1 : γ < 1) :
    ∀ᵐ x : Fin k → ℝ ∂volume, ∀ c : Option (Fin k), simplexCoordinate x c ≠ γ := by
  rw [ae_all_iff]
  intro c
  rw [ae_iff]
  simpa [not_not] using volume_simplexCoordinate_level hγ hγ1 c

noncomputable def exponentGridBoxes (k : ℕ) (γ : ℝ) (n : ℕ) : Finset (Fin k → ℕ) :=
  (Fintype.piFinset fun _ : Fin k => Finset.range n).filter fun u =>
    (∑ i : Fin k, exponentGridUpper γ n u i) < 1 - γ

lemma exponentGridBox_valid {k : ℕ} {γ : ℝ} (hγ : 0 < γ) {n : ℕ} (hn : 0 < n)
    {u : Fin k → ℕ} (hu : u ∈ exponentGridBoxes k γ n) :
    (∀ i, γ ≤ exponentGridLower γ n u i) ∧
      (∀ i, exponentGridLower γ n u i < exponentGridUpper γ n u i) ∧
      (∑ i : Fin k, exponentGridLower γ n u i) < 1 ∧
      (∑ i : Fin k, exponentGridUpper γ n u i) < 1 - γ := by
  have hstep : (0 : ℝ) < 1 / (n : ℝ) := by
    exact one_div_pos.mpr (by exact_mod_cast hn)
  have hsumUpper := (Finset.mem_filter.mp hu).2
  have hsumLower : (∑ i : Fin k, exponentGridLower γ n u i) ≤
      ∑ i : Fin k, exponentGridUpper γ n u i := by
    apply Finset.sum_le_sum
    intro i hi
    have hadd : ((u i + 1 : ℕ) : ℝ) / n =
        (u i : ℝ) / n + 1 / (n : ℝ) := by push_cast; ring
    rw [exponentGridLower, exponentGridUpper, hadd]
    linarith [hstep]
  refine ⟨?_, ?_, ?_, hsumUpper⟩
  · intro i
    simp only [exponentGridLower]
    have huNonneg : 0 ≤ (u i : ℝ) / n := div_nonneg (Nat.cast_nonneg _) (by positivity)
    linarith
  · intro i
    have hadd : ((u i + 1 : ℕ) : ℝ) / n =
        (u i : ℝ) / n + 1 / (n : ℝ) := by push_cast; ring
    rw [exponentGridLower, exponentGridUpper, hadd]
    linarith [hstep]
  · linarith [hsumLower, hsumUpper, hγ]

lemma exponentGridUpper_le_lower {k : ℕ} {γ : ℝ} {n : ℕ} (hn : 0 < n)
    (u v : Fin k → ℕ) (i : Fin k) (h : u i + 1 ≤ v i) :
    exponentGridUpper γ n u i ≤ exponentGridLower γ n v i := by
  dsimp [exponentGridUpper, exponentGridLower]
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcast : ((u i + 1 : ℕ) : ℝ) ≤ (v i : ℝ) := by exact_mod_cast h
  exact add_le_add_right (div_le_div_of_nonneg_right hcast hnR.le) γ

lemma exponentGridBoxUpperSeparated {k : ℕ} {γ : ℝ} {n : ℕ} (hn : 0 < n)
    {u v : Fin k → ℕ} (huv : u ≠ v) :
    ∃ i, exponentGridUpper γ n u i ≤ exponentGridLower γ n v i ∨
      exponentGridUpper γ n v i ≤ exponentGridLower γ n u i := by
  classical
  have hdiff : ∃ i, u i ≠ v i := by
    by_contra h
    apply huv
    funext i
    exact not_ne_iff.mp (not_exists.mp h i)
  obtain ⟨i, hneq⟩ := hdiff
  by_cases hlt : u i < v i
  · exact ⟨i, Or.inl (exponentGridUpper_le_lower hn u v i (by omega))⟩
  · have hlt' : v i < u i := by omega
    exact ⟨i, Or.inr (exponentGridUpper_le_lower hn v u i (by omega))⟩

lemma exponentGridBoxSets_disjoint {k : ℕ} {γ : ℝ} {n : ℕ} (hn : 0 < n)
    {u v : Fin k → ℕ} (huv : u ≠ v) :
    Disjoint (exponentBoxSet (exponentGridLower γ n u) (exponentGridUpper γ n u))
      (exponentBoxSet (exponentGridLower γ n v) (exponentGridUpper γ n v)) := by
  obtain ⟨i, hgap | hgap⟩ := exponentGridBoxUpperSeparated hn huv
  · apply Set.disjoint_left.mpr
    intro x hx₁ hx₂
    have h₁ := (Set.mem_pi.mp hx₁) i (Set.mem_univ i)
    have h₂ := (Set.mem_pi.mp hx₂) i (Set.mem_univ i)
    exact (not_lt_of_ge (h₁.2.trans hgap)) h₂.1
  · apply Set.disjoint_left.mpr
    intro x hx₁ hx₂
    have h₁ := (Set.mem_pi.mp hx₁) i (Set.mem_univ i)
    have h₂ := (Set.mem_pi.mp hx₂) i (Set.mem_univ i)
    exact (not_lt_of_ge (h₂.2.trans hgap)) h₁.1

noncomputable def exponentGridCellIndex (γ y : ℝ) (n : ℕ) : ℕ :=
  ⌈(n : ℝ) * (y - γ)⌉₊ - 1

lemma exponentGridCellIndex_spec {γ y : ℝ} (hγ : 0 < γ) (hγy : γ < y) (hy1 : y < 1)
    {n : ℕ} (hn : 0 < n) :
    exponentGridCellIndex γ y n < n ∧
      γ + (exponentGridCellIndex γ y n : ℝ) / n < y ∧
      y ≤ γ + ((exponentGridCellIndex γ y n + 1 : ℕ) : ℝ) / n := by
  let r : ℝ := (n : ℝ) * (y - γ)
  let m : ℕ := exponentGridCellIndex γ y n
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hrpos : 0 < r := by
    dsimp [r]
    exact mul_pos hnR (sub_pos.mpr hγy)
  have hceilPos : 0 < ⌈r⌉₊ := (Nat.ceil_pos).2 hrpos
  have hceilLe : 1 ≤ ⌈r⌉₊ := hceilPos
  have hmadd : m + 1 = ⌈r⌉₊ := by
    dsimp [m, exponentGridCellIndex, r]
    exact Nat.sub_add_cancel hceilLe
  have hmaddCast : (m : ℝ) + 1 = (⌈r⌉₊ : ℝ) := by exact_mod_cast hmadd
  have hmLtR : (m : ℝ) < r := by
    have hceil := Nat.ceil_lt_add_one hrpos.le
    rw [← hmaddCast] at hceil
    dsimp [r] at hceil ⊢
    nlinarith
  have hrLeM : r ≤ ((m + 1 : ℕ) : ℝ) := by
    have hceil := Nat.le_ceil r
    rw [← hmadd] at hceil
    exact hceil
  have hyγlt : y - γ < 1 := by linarith
  have hr_lt_n : r < (n : ℝ) := by
    dsimp [r]
    calc
      (n : ℝ) * (y - γ) < (n : ℝ) * 1 := mul_lt_mul_of_pos_left hyγlt hnR
      _ = (n : ℝ) := by ring
  have hceilNat : ⌈r⌉₊ ≤ n := (Nat.ceil_le).2 (le_of_lt hr_lt_n)
  have hmNat : m < n := by omega
  have hmDiv : (m : ℝ) / n < y - γ := by
    apply (div_lt_iff₀ hnR).2
    calc
      (m : ℝ) < r := hmLtR
      _ = (y - γ) * n := by dsimp [r]; ring
  have hmAddDiv : y - γ ≤ ((m + 1 : ℕ) : ℝ) / n := by
    apply (le_div_iff₀ hnR).2
    have hrLe : (n : ℝ) * (y - γ) ≤ ((m + 1 : ℕ) : ℝ) := by
      simpa [r] using hrLeM
    nlinarith
  refine ⟨hmNat, ?_, ?_⟩ <;> linarith

lemma tendsto_exponentGridCellLower {γ y : ℝ} (hγ : 0 < γ) (hγy : γ < y) (hy1 : y < 1) :
    Tendsto (fun n : ℕ => γ + (exponentGridCellIndex γ y n : ℝ) / n) atTop (𝓝 y) := by
  have hInv : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := by
    have hInv' : Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) atTop (𝓝 0) := by
      exact (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).congr'
        (Eventually.of_forall fun n => rfl)
    simpa only [one_div] using hInv'
  have hleft : Tendsto (fun n : ℕ => y - 1 / (n : ℝ)) atTop (𝓝 y) :=
    by simpa using tendsto_const_nhds.sub hInv
  have hbounds : ∀ᶠ n : ℕ in atTop,
      y - 1 / (n : ℝ) ≤ γ + (exponentGridCellIndex γ y n : ℝ) / n ∧
        γ + (exponentGridCellIndex γ y n : ℝ) / n ≤ y := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hcell := exponentGridCellIndex_spec hγ hγy hy1 hn
    have hadd : ((exponentGridCellIndex γ y n + 1 : ℕ) : ℝ) / n =
        (exponentGridCellIndex γ y n : ℝ) / n + 1 / (n : ℝ) := by
      push_cast
      ring
    rw [hadd] at hcell
    constructor
    · linarith [hcell.2.2]
    · exact le_of_lt hcell.2.1
  have hlow := hbounds.mono fun n h => h.1
  have hupp := hbounds.mono fun n h => h.2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hleft tendsto_const_nhds hlow hupp

lemma tendsto_exponentGridLowerVector {k : ℕ} {γ : ℝ} (hγ : 0 < γ)
    (x : Fin k → ℝ) (hxγ : ∀ i, γ < x i) (hx1 : ∀ i, x i < 1) :
    Tendsto (fun n : ℕ => exponentGridLower γ n
      (fun i => exponentGridCellIndex γ (x i) n)) atTop (𝓝 x) := by
  apply tendsto_pi_nhds.2
  intro i
  exact tendsto_exponentGridCellLower hγ (hxγ i) (hx1 i)

lemma tendsto_exponentGridLowerSum {k : ℕ} {γ : ℝ} (hγ : 0 < γ)
    (x : Fin k → ℝ) (hxγ : ∀ i, γ < x i) (hx1 : ∀ i, x i < 1) :
    Tendsto (fun n : ℕ => ∑ i : Fin k,
      exponentGridLower γ n (fun i => exponentGridCellIndex γ (x i) n) i)
      atTop (𝓝 (∑ i : Fin k, x i)) := by
  apply tendsto_finsetSum Finset.univ
  intro i hi
  exact tendsto_pi_nhds.1
    (tendsto_exponentGridLowerVector hγ x hxγ hx1) i

lemma tendsto_exponentGridDenominatorInv {k : ℕ} {γ : ℝ} (hγ : 0 < γ)
    (x : Fin k → ℝ) (hxγ : ∀ i, γ < x i) (hx1 : ∀ i, x i < 1)
    (hsum : (∑ i : Fin k, x i) < 1) :
    Tendsto (fun n : ℕ =>
      (1 - ∑ i : Fin k,
        exponentGridLower γ n (fun i => exponentGridCellIndex γ (x i) n) i)⁻¹)
      atTop (𝓝 ((1 - ∑ i : Fin k, x i)⁻¹)) := by
  have hsumLimit := tendsto_exponentGridLowerSum hγ x hxγ hx1
  have hdenom : Tendsto (fun n : ℕ =>
      1 - ∑ i : Fin k,
        exponentGridLower γ n (fun i => exponentGridCellIndex γ (x i) n) i)
      atTop (𝓝 (1 - ∑ i : Fin k, x i)) :=
    tendsto_const_nhds.sub hsumLimit
  have hne : 1 - ∑ i : Fin k, x i ≠ 0 := by linarith
  exact hdenom.inv₀ hne

lemma eventually_exponentGridBox_covers_interior {k : ℕ} {γ : ℝ} (hγ : 0 < γ)
    (x : Fin k → ℝ) (hx : ∀ c : Option (Fin k), γ < simplexCoordinate x c) :
    ∀ᶠ n : ℕ in atTop,
      (fun i => exponentGridCellIndex γ (x i) n) ∈ exponentGridBoxes k γ n ∧
        x ∈ exponentBoxSet (exponentGridLower γ n
          (fun i => exponentGridCellIndex γ (x i) n))
          (exponentGridUpper γ n (fun i => exponentGridCellIndex γ (x i) n)) := by
  have hsumX : (∑ i : Fin k, x i) < 1 - γ := by
    have h := hx none
    simp only [simplexCoordinate] at h
    linarith
  have hxpos (i : Fin k) : 0 < x i := lt_trans hγ (hx (some i))
  have hxlt1 (i : Fin k) : x i < 1 := by
    have hle : x i ≤ ∑ j : Fin k, x j :=
      Finset.single_le_sum (fun j hj => (le_of_lt (hxpos j))) (Finset.mem_univ i)
    linarith [hsumX, hγ]
  have hinv : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := by
    have hinv' : Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) atTop (𝓝 0) := by
      exact (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).congr'
        (Eventually.of_forall fun n => rfl)
    simpa only [one_div] using hinv'
  let gap : ℝ := 1 - γ - ∑ i : Fin k, x i
  have hgap : 0 < gap := by dsimp [gap]; linarith [hsumX]
  have hmesh : Tendsto (fun n : ℕ =>
      ((Finset.univ : Finset (Fin k)).card : ℝ) * (1 / (n : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
      ((Finset.univ : Finset (Fin k)).card : ℝ)) atTop
        (𝓝 ((Finset.univ : Finset (Fin k)).card : ℝ))).mul hinv
  have hsmall : ∀ᶠ n : ℕ in atTop,
      ((Finset.univ : Finset (Fin k)).card : ℝ) / (n : ℝ) < gap := by
    have heq : ∀ᶠ n : ℕ in atTop,
        ((Finset.univ : Finset (Fin k)).card : ℝ) / (n : ℝ) =
          ((Finset.univ : Finset (Fin k)).card : ℝ) * (1 / (n : ℝ)) := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
      field_simp [ne_of_gt hnR]
    have hmesh' := hmesh.congr' (heq.mono fun n h => h.symm)
    exact hmesh'.eventually (Iio_mem_nhds hgap)
  filter_upwards [eventually_gt_atTop (0 : ℕ), hsmall] with n hn hsmall
  let u : Fin k → ℕ := fun i => exponentGridCellIndex γ (x i) n
  have hcell (i : Fin k) :
      u i < n ∧ exponentGridLower γ n u i < x i ∧ x i ≤ exponentGridUpper γ n u i := by
    have hxiγ : γ < x i := by simpa [simplexCoordinate] using hx (some i)
    simpa [u, exponentGridLower, exponentGridUpper] using
      (exponentGridCellIndex_spec hγ hxiγ (hxlt1 i) hn)
  have hupper (i : Fin k) : exponentGridUpper γ n u i ≤ x i + 1 / (n : ℝ) := by
    have hadd : ((u i + 1 : ℕ) : ℝ) / n = (u i : ℝ) / n + 1 / (n : ℝ) := by
      push_cast
      ring
    have huppEq : exponentGridUpper γ n u i =
        exponentGridLower γ n u i + 1 / (n : ℝ) := by
      dsimp [exponentGridUpper, exponentGridLower]
      rw [hadd]
      ring
    rw [huppEq]
    have hle := (hcell i).2.2
    rw [huppEq] at hle
    linarith [(hcell i).2.1]
  have hsumUpper : (∑ i : Fin k, exponentGridUpper γ n u i) < 1 - γ := by
    have hsumBound : (∑ i : Fin k, exponentGridUpper γ n u i) ≤
        (∑ i : Fin k, x i) +
          ((Finset.univ : Finset (Fin k)).card : ℝ) / (n : ℝ) := by
      calc
        _ ≤ ∑ i : Fin k, (x i + 1 / (n : ℝ)) := Finset.sum_le_sum fun i hi => hupper i
        _ = (∑ i : Fin k, x i) +
            ((Finset.univ : Finset (Fin k)).card : ℝ) / (n : ℝ) := by
              rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
              simp [div_eq_mul_inv, mul_comm]
              <;> ring
    have hsmall' := hsmall
    dsimp [gap] at hsmall'
    linarith
  have hbase : u ∈ Fintype.piFinset (fun _ : Fin k => Finset.range n) := by
    rw [Fintype.mem_piFinset]
    intro i
    exact Finset.mem_range.mpr (hcell i).1
  have hu : u ∈ exponentGridBoxes k γ n := Finset.mem_filter.mpr ⟨hbase, hsumUpper⟩
  have hxbox : x ∈ exponentBoxSet (exponentGridLower γ n u) (exponentGridUpper γ n u) := by
    simp only [exponentBoxSet, Set.mem_pi]
    intro i hi
    exact ⟨(hcell i).2.1, (hcell i).2.2⟩
  exact ⟨hu, hxbox⟩

lemma integral_indicator_inv_Ioc {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∫ t : ℝ, Set.indicator (Set.Ioc a b) (fun t => 1 / t) t = Real.log (b / a) := by
  have hle : a ≤ b := le_of_lt hab
  have hIcc : ∀ t ∈ Set.Icc a b, t ≠ 0 := by
    intro t ht
    exact ne_of_gt (lt_of_lt_of_le ha ht.1)
  have hb : 0 < b := lt_trans ha hab
  have hinvContinuous : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Icc a b) :=
    continuousOn_id.inv₀ hIcc
  have hIocSubset : Set.Ioc a b ⊆ Set.Icc a b := by
    intro t ht
    exact ⟨ht.1.le, ht.2⟩
  have hinvInt : IntegrableOn (fun t : ℝ => t⁻¹) (Set.Ioc a b) :=
    hinvContinuous.integrableOn_Icc.mono_set hIocSubset
  have hinterval : IntervalIntegrable (fun t : ℝ => 1 / t) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle]
    simpa [one_div] using hinvInt
  have hlogCont : ContinuousOn Real.log (Set.Icc a b) :=
    Real.continuousOn_log.mono fun t ht => hIcc t ht
  have hderivInt : ∫ t in a..b, (1 / t) = Real.log b - Real.log a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle hlogCont
      (fun t ht => by
        have htIcc : t ∈ Set.Icc a b := ⟨ht.1.le, ht.2.le⟩
        simpa [one_div] using Real.hasDerivAt_log (hIcc t htIcc)) hinterval
  calc
    ∫ t : ℝ, Set.indicator (Set.Ioc a b) (fun t => 1 / t) t =
        ∫ t in Set.Ioc a b, (1 / t) := by
          rw [integral_indicator measurableSet_Ioc]
    _ = ∫ t in a..b, (1 / t) := (intervalIntegral.integral_of_le hle).symm
    _ = Real.log b - Real.log a := hderivInt
    _ = Real.log (b / a) := (Real.log_div hb.ne' ha.ne').symm

lemma exponentGridBoxSet_subset_simplexGoodSet {k : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {n : ℕ} (hn : 0 < n) {u : Fin k → ℕ}
    (hu : u ∈ exponentGridBoxes k γ n) :
    exponentBoxSet (exponentGridLower γ n u) (exponentGridUpper γ n u) ⊆
      simplexGoodSet γ := by
  have hvalid := exponentGridBox_valid hγ hn hu
  intro x hx c
  cases c with
  | none =>
      simp only [simplexCoordinate]
      have hsumX : (∑ i : Fin k, x i) ≤
          ∑ i : Fin k, exponentGridUpper γ n u i := by
        apply Finset.sum_le_sum
        intro i hi
        exact ((Set.mem_pi.mp hx) i (Set.mem_univ i)).2
      linarith [hvalid.2.2.2]
  | some i =>
      have hi := (Set.mem_pi.mp hx) i (Set.mem_univ i)
      simpa [simplexCoordinate] using (hvalid.1 i).trans (le_of_lt hi.1)

lemma exponentBoxSet_indicator_prod {k : ℕ} (a b : Fin k → ℝ) (x : Fin k → ℝ) :
    Set.indicator (exponentBoxSet a b) (fun x => ∏ i : Fin k, (1 / x i)) x =
      ∏ i : Fin k, Set.indicator (Set.Ioc (a i) (b i)) (fun t => 1 / t) (x i) := by
  classical
  by_cases hx : x ∈ exponentBoxSet a b
  · have hxi : ∀ i, x i ∈ Set.Ioc (a i) (b i) := by
      simpa [exponentBoxSet, Set.mem_pi] using hx
    simp [exponentBoxSet, Set.indicator_of_mem hx, hxi]
  · have hex : ∃ i, x i ∉ Set.Ioc (a i) (b i) := by
      by_contra h
      apply hx
      simp only [exponentBoxSet, Set.mem_pi]
      intro i hi
      by_contra hnot
      exact h ⟨i, hnot⟩
    obtain ⟨i, hi⟩ := hex
    have hi0 : Set.indicator (Set.Ioc (a i) (b i)) (fun t => 1 / t) (x i) = 0 :=
      Set.indicator_of_notMem hi _
    have hprod0 :
        (∏ j : Fin k, Set.indicator (Set.Ioc (a j) (b j))
          (fun t => 1 / t) (x j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hi0
    have hlhs : Set.indicator (exponentBoxSet a b)
        (fun x => ∏ i : Fin k, (1 / x i)) x = 0 :=
      Set.indicator_of_notMem hx _
    rw [hlhs, hprod0]

lemma integrable_indicator_inv_Ioc {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Integrable (Set.indicator (Set.Ioc a b) (fun t : ℝ => 1 / t)) volume := by
  have hIcc : ∀ t ∈ Set.Icc a b, t ≠ 0 := by
    intro t ht
    exact ne_of_gt (lt_of_lt_of_le ha ht.1)
  have hinvContinuous : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Icc a b) :=
    continuousOn_id.inv₀ hIcc
  have hIocSubset : Set.Ioc a b ⊆ Set.Icc a b := by
    intro t ht
    exact ⟨ht.1.le, ht.2⟩
  have hinvInt : IntegrableOn (fun t : ℝ => t⁻¹) (Set.Ioc a b) :=
    hinvContinuous.integrableOn_Icc.mono_set hIocSubset
  exact (integrable_indicator_iff measurableSet_Ioc).2 (by simpa [one_div] using hinvInt)

lemma integral_exponentBox_reciprocal {k : ℕ} (a b : Fin k → ℝ)
    (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i) :
    ∫ x : Fin k → ℝ,
        Set.indicator (exponentBoxSet a b) (fun x => ∏ i : Fin k, (1 / x i)) x =
      ∏ i : Fin k, Real.log (b i / a i) := by
  classical
  have hpoint (x : Fin k → ℝ) :
      Set.indicator (exponentBoxSet a b) (fun x => ∏ i : Fin k, (1 / x i)) x =
        ∏ i : Fin k, Set.indicator (Set.Ioc (a i) (b i)) (fun t => 1 / t) (x i) := by
    by_cases hx : x ∈ exponentBoxSet a b
    · have hxi : ∀ i, x i ∈ Set.Ioc (a i) (b i) := by
        simpa [exponentBoxSet, Set.mem_pi] using hx
      simp [exponentBoxSet, Set.indicator_of_mem hx, hxi]
    · have hex : ∃ i, x i ∉ Set.Ioc (a i) (b i) := by
        by_contra h
        apply hx
        simp only [exponentBoxSet, Set.mem_pi]
        intro i hi
        by_contra hnot
        exact h ⟨i, hnot⟩
      obtain ⟨i, hi⟩ := hex
      have hi0 : Set.indicator (Set.Ioc (a i) (b i)) (fun t => 1 / t) (x i) = 0 :=
        Set.indicator_of_notMem hi _
      have hprod0 :
          (∏ j : Fin k, Set.indicator (Set.Ioc (a j) (b j))
            (fun t => 1 / t) (x j)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) hi0
      have hlhs : Set.indicator (exponentBoxSet a b)
          (fun x => ∏ i : Fin k, (1 / x i)) x = 0 :=
        Set.indicator_of_notMem hx _
      rw [hlhs, hprod0]
  calc
    ∫ x : Fin k → ℝ,
        Set.indicator (exponentBoxSet a b) (fun x => ∏ i : Fin k, (1 / x i)) x =
      ∫ x : Fin k → ℝ,
        ∏ i : Fin k, Set.indicator (Set.Ioc (a i) (b i)) (fun t => 1 / t) (x i) := by
          apply integral_congr_ae
          filter_upwards [] with x
          exact hpoint x
    _ = ∏ i : Fin k,
        ∫ t : ℝ, Set.indicator (Set.Ioc (a i) (b i)) (fun t => 1 / t) t :=
          MeasureTheory.integral_fintype_prod_volume_eq_prod _
    _ = ∏ i : Fin k, Real.log (b i / a i) := by
          apply Finset.prod_congr rfl
          intro i hi
          exact integral_indicator_inv_Ioc (ha i) (hab i)

lemma integrable_exponentBox_reciprocal {k : ℕ} (a b : Fin k → ℝ)
    (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i) :
    Integrable (Set.indicator (exponentBoxSet a b)
      (fun x : Fin k → ℝ => ∏ i : Fin k, (1 / x i))) volume := by
  have hprodPi : Integrable (fun x : Fin k → ℝ =>
      ∏ i : Fin k, Set.indicator (Set.Ioc (a i) (b i)) (fun t => 1 / t) (x i))
      (Measure.pi fun _ : Fin k => (volume : Measure ℝ)) :=
    MeasureTheory.Integrable.fin_nat_prod
      (μ := fun _ : Fin k => (volume : Measure ℝ))
      (fun i => integrable_indicator_inv_Ioc (ha i) (hab i))
  have hprod : Integrable (fun x : Fin k → ℝ =>
      ∏ i : Fin k, Set.indicator (Set.Ioc (a i) (b i)) (fun t => 1 / t) (x i)) volume := by
    rw [MeasureTheory.volume_pi]
    exact hprodPi
  have heq : (Set.indicator (exponentBoxSet a b)
      (fun x : Fin k → ℝ => ∏ i : Fin k, (1 / x i))) =ᵐ[volume]
        (fun x => ∏ i : Fin k,
          Set.indicator (Set.Ioc (a i) (b i)) (fun t => 1 / t) (x i)) := by
    filter_upwards [] with x
    exact exponentBoxSet_indicator_prod a b x
  exact hprod.congr heq.symm

noncomputable def exponentGridStepIntegrand {k : ℕ} (γ : ℝ) (n : ℕ)
    (x : Fin k → ℝ) : ℝ :=
  ∑ u ∈ exponentGridBoxes k γ n,
    Set.indicator (exponentBoxSet (exponentGridLower γ n u) (exponentGridUpper γ n u))
      (fun x => (1 / (1 - ∑ i : Fin k, exponentGridLower γ n u i)) *
        ∏ i : Fin k, (1 / x i)) x

lemma exponentGridBoxTerm_le_simplexIntegrand {k : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {n : ℕ} (hn : 0 < n) {u : Fin k → ℕ}
    (hu : u ∈ exponentGridBoxes k γ n) (x : Fin k → ℝ)
    (hx : x ∈ exponentBoxSet (exponentGridLower γ n u) (exponentGridUpper γ n u)) :
    Set.indicator (exponentBoxSet (exponentGridLower γ n u) (exponentGridUpper γ n u))
        (fun x => (1 / (1 - ∑ i : Fin k, exponentGridLower γ n u i)) *
          ∏ i : Fin k, (1 / x i)) x ≤ simplexIntegrand γ x := by
  have hvalid := exponentGridBox_valid hγ hn hu
  have hxi (i : Fin k) :
      x i ∈ Set.Ioc (exponentGridLower γ n u i) (exponentGridUpper γ n u i) :=
    (Set.mem_pi.mp hx) i (Set.mem_univ i)
  have hsumLower :
      (∑ i : Fin k, exponentGridLower γ n u i) ≤ ∑ i : Fin k, x i := by
    apply Finset.sum_le_sum
    intro i hi
    exact le_of_lt (hxi i).1
  have hsumX : (∑ i : Fin k, x i) ≤
      ∑ i : Fin k, exponentGridUpper γ n u i := by
    apply Finset.sum_le_sum
    intro i hi
    exact (hxi i).2
  have hgood : x ∈ simplexGoodSet γ := by
    intro c
    cases c with
    | none =>
        simp only [simplexCoordinate]
        have hlast : γ ≤ 1 - ∑ i : Fin k, x i := by
          have := hvalid.2.2.2
          linarith [hsumX]
        exact hlast
    | some i =>
        have hle : γ ≤ x i := le_trans (hvalid.1 i) (le_of_lt (hxi i).1)
        simpa [simplexCoordinate] using hle
  have hsumXlt : (∑ i : Fin k, x i) < 1 := by
    have hlast := hgood none
    simpa [simplexCoordinate] using (lt_of_lt_of_le hγ hlast)
  have hdenLower : 0 < 1 - ∑ i : Fin k, exponentGridLower γ n u i := by
    linarith [hvalid.2.2.1]
  have hdenX : 0 < 1 - ∑ i : Fin k, x i := by linarith
  have hdenLe : 1 - ∑ i : Fin k, x i ≤
      1 - ∑ i : Fin k, exponentGridLower γ n u i := by linarith
  have hcoeff :
      1 / (1 - ∑ i : Fin k, exponentGridLower γ n u i) ≤
        1 / (1 - ∑ i : Fin k, x i) :=
    one_div_le_one_div_of_le hdenX hdenLe
  have hprod : 0 ≤ ∏ i : Fin k, (1 / (x i : ℝ)) := by
    apply Finset.prod_nonneg
    intro i hi
    exact div_nonneg (by norm_num) (le_of_lt (lt_of_lt_of_le hγ (hgood (some i))))
  have hweight : simplexWeight x =
      (1 / (1 - ∑ i : Fin k, x i)) * ∏ i : Fin k, (1 / (x i : ℝ)) := by
    simp [simplexWeight, simplexCoordinate, Fintype.prod_option]
    <;> ring
  calc
    Set.indicator (exponentBoxSet (exponentGridLower γ n u) (exponentGridUpper γ n u))
        (fun x => (1 / (1 - ∑ i : Fin k, exponentGridLower γ n u i)) *
          ∏ i : Fin k, (1 / x i)) x =
        (1 / (1 - ∑ i : Fin k, exponentGridLower γ n u i)) *
          ∏ i : Fin k, (1 / x i) := Set.indicator_of_mem hx _
    _ ≤ (1 / (1 - ∑ i : Fin k, x i)) * ∏ i : Fin k, (1 / x i) :=
      mul_le_mul_of_nonneg_right hcoeff hprod
    _ = simplexIntegrand γ x := by
      simp [simplexIntegrand, hgood, hweight]

lemma simplexIntegrand_nonneg {k : ℕ} {γ : ℝ} (hγ : 0 < γ) (x : Fin k → ℝ) :
    0 ≤ simplexIntegrand γ x := by
  unfold simplexIntegrand
  by_cases hx : x ∈ simplexGoodSet γ
  · rw [Set.indicator_of_mem hx]
    apply Finset.prod_nonneg
    intro c hc
    exact div_nonneg (by norm_num) (le_of_lt (lt_of_lt_of_le hγ (hx c)))
  · simp [Set.indicator_of_notMem hx]

lemma exponentGridStepIntegrand_le_simplexIntegrand {k : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {n : ℕ} (hn : 0 < n) (x : Fin k → ℝ) :
    exponentGridStepIntegrand (k := k) γ n x ≤ simplexIntegrand γ x := by
  classical
  let boxes := exponentGridBoxes k γ n
  let term : (Fin k → ℕ) → ℝ := fun u =>
    Set.indicator (exponentBoxSet (exponentGridLower γ n u) (exponentGridUpper γ n u))
      (fun x => (1 / (1 - ∑ i : Fin k, exponentGridLower γ n u i)) *
        ∏ i : Fin k, (1 / x i)) x
  by_cases hex : ∃ u ∈ boxes,
      x ∈ exponentBoxSet (exponentGridLower γ n u) (exponentGridUpper γ n u)
  · obtain ⟨u, hu, hxu⟩ := hex
    have hsum : (∑ v ∈ boxes, term v) = term u := by
      apply Finset.sum_eq_single u
      · intro v hv hvu
        have hdisj := exponentGridBoxSets_disjoint (γ := γ) hn hvu
        have hxv : x ∉ exponentBoxSet (exponentGridLower γ n v)
            (exponentGridUpper γ n v) := by
          intro hxv
          exact (Set.disjoint_left.mp hdisj) hxv hxu
        simp [term, Set.indicator_of_notMem hxv]
      · intro hnot
        exact (hnot hu).elim
    rw [exponentGridStepIntegrand, hsum]
    exact exponentGridBoxTerm_le_simplexIntegrand hγ hn hu x hxu
  · have hzero : ∀ u ∈ boxes, term u = 0 := by
      intro u hu
      have hxnot : x ∉ exponentBoxSet (exponentGridLower γ n u)
          (exponentGridUpper γ n u) := by
        intro hxu
        exact hex ⟨u, hu, hxu⟩
      simp [term, Set.indicator_of_notMem hxnot]
    rw [exponentGridStepIntegrand, Finset.sum_eq_zero hzero]
    exact simplexIntegrand_nonneg hγ x

lemma exponentGridStepIntegrand_eq_term_of_cover {k : ℕ} {γ : ℝ} {n : ℕ}
    (hn : 0 < n) (x : Fin k → ℝ) {u : Fin k → ℕ}
    (hu : u ∈ exponentGridBoxes k γ n)
    (hx : x ∈ exponentBoxSet (exponentGridLower γ n u) (exponentGridUpper γ n u)) :
    exponentGridStepIntegrand (k := k) γ n x =
      (1 / (1 - ∑ i : Fin k, exponentGridLower γ n u i)) *
        ∏ i : Fin k, (1 / x i) := by
  classical
  let boxes := exponentGridBoxes k γ n
  let term : (Fin k → ℕ) → ℝ := fun v =>
    Set.indicator (exponentBoxSet (exponentGridLower γ n v) (exponentGridUpper γ n v))
      (fun x => (1 / (1 - ∑ i : Fin k, exponentGridLower γ n v i)) *
        ∏ i : Fin k, (1 / x i)) x
  have hsum : (∑ v ∈ boxes, term v) = term u := by
    apply Finset.sum_eq_single u
    · intro v hv hvu
      have hdisj := exponentGridBoxSets_disjoint (γ := γ) hn hvu
      have hxv : x ∉ exponentBoxSet (exponentGridLower γ n v)
          (exponentGridUpper γ n v) := by
        intro hxv
        exact (Set.disjoint_left.mp hdisj) hxv hx
      simp [term, Set.indicator_of_notMem hxv]
    · intro hnot
      exact (hnot hu).elim
  rw [exponentGridStepIntegrand, hsum]
  simp [term, Set.indicator_of_mem hx]

lemma exponentGridStepIntegrand_eq_zero_of_not_good {k : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {n : ℕ} (hn : 0 < n) (x : Fin k → ℝ)
    (hx : x ∉ simplexGoodSet γ) : exponentGridStepIntegrand (k := k) γ n x = 0 := by
  classical
  unfold exponentGridStepIntegrand
  apply Finset.sum_eq_zero
  intro u hu
  have hnot : x ∉ exponentBoxSet (exponentGridLower γ n u) (exponentGridUpper γ n u) := by
    intro hbox
    exact hx (exponentGridBoxSet_subset_simplexGoodSet hγ hn hu hbox)
  simp [Set.indicator_of_notMem hnot]

lemma tendsto_exponentGridStepIntegrand_interior {k : ℕ} {γ : ℝ}
    (hγ : 0 < γ) (x : Fin k → ℝ)
    (hx : ∀ c : Option (Fin k), γ < simplexCoordinate x c) :
    Tendsto (fun n : ℕ => exponentGridStepIntegrand (k := k) γ n x) atTop
      (𝓝 (simplexIntegrand γ x)) := by
  have hsum : (∑ i : Fin k, x i) < 1 - γ := by
    have h := hx none
    simp only [simplexCoordinate] at h
    linarith
  have hxγ : ∀ i, γ < x i := fun i => by simpa [simplexCoordinate] using hx (some i)
  have hxpos : ∀ i, 0 < x i := fun i => lt_trans hγ (hxγ i)
  have hxlt1 : ∀ i, x i < 1 := by
    intro i
    have hle : x i ≤ ∑ j : Fin k, x j :=
      Finset.single_le_sum (fun j hj => le_of_lt (hxpos j)) (Finset.mem_univ i)
    linarith [hsum, hγ]
  let P : ℝ := ∏ i : Fin k, (1 / x i)
  have hdenom := tendsto_exponentGridDenominatorInv hγ x hxγ hxlt1 (by linarith [hsum, hγ])
  have hcoeff : Tendsto (fun n : ℕ =>
      (1 - ∑ i : Fin k, exponentGridLower γ n
        (fun i => exponentGridCellIndex γ (x i) n) i)⁻¹ * P) atTop
      (𝓝 ((1 - ∑ i : Fin k, x i)⁻¹ * P)) :=
    hdenom.mul tendsto_const_nhds
  have hcover := eventually_exponentGridBox_covers_interior hγ x hx
  have heq : ∀ᶠ n : ℕ in atTop,
      exponentGridStepIntegrand (k := k) γ n x =
        (1 - ∑ i : Fin k, exponentGridLower γ n
          (fun i => exponentGridCellIndex γ (x i) n) i)⁻¹ * P := by
    filter_upwards [eventually_gt_atTop (0 : ℕ), hcover] with n hn hc
    let u : Fin k → ℕ := fun i => exponentGridCellIndex γ (x i) n
    have hval := exponentGridStepIntegrand_eq_term_of_cover hn x hc.1 hc.2
    simpa [P, u] using hval
  have hgood : x ∈ simplexGoodSet γ := fun c => le_of_lt (hx c)
  have hweight : simplexWeight x =
      (1 / (1 - ∑ i : Fin k, x i)) * P := by
    simp [P, simplexWeight, simplexCoordinate, Fintype.prod_option]
    <;> ring
  have htarget : (1 - ∑ i : Fin k, x i)⁻¹ * P = simplexIntegrand γ x := by
    simp [simplexIntegrand, hgood, hweight, one_div]
  have hconv := hcoeff.congr' (heq.mono fun n h => h.symm)
  simpa [htarget] using hconv

lemma tendsto_exponentGridStepIntegrand_ae {k : ℕ} {γ : ℝ}
    (hγ : 0 < γ) (hγ1 : γ < 1) :
    ∀ᵐ x : Fin k → ℝ ∂volume,
      Tendsto (fun n : ℕ => exponentGridStepIntegrand (k := k) γ n x) atTop
        (𝓝 (simplexIntegrand γ x)) := by
  filter_upwards [ae_simplexCoordinate_ne_level hγ hγ1] with x hxcoord
  by_cases hgood : x ∈ simplexGoodSet γ
  · have hstrict : ∀ c : Option (Fin k), γ < simplexCoordinate x c := by
      intro c
      exact lt_of_le_of_ne (hgood c) (Ne.symm (hxcoord c))
    exact tendsto_exponentGridStepIntegrand_interior hγ x hstrict
  · have hsimplex : simplexIntegrand γ x = 0 := by
      simp [simplexIntegrand, hgood]
    have heq : ∀ᶠ n : ℕ in atTop,
        exponentGridStepIntegrand (k := k) γ n x = simplexIntegrand γ x := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      rw [exponentGridStepIntegrand_eq_zero_of_not_good hγ hn x hgood, hsimplex]
    have hconst : Tendsto (fun _ : ℕ => simplexIntegrand γ x) atTop
        (𝓝 (simplexIntegrand γ x)) := tendsto_const_nhds
    exact hconst.congr' (heq.mono fun n h => h.symm)

lemma exponentGridStepIntegrand_nonneg {k : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {n : ℕ} (hn : 0 < n) (x : Fin k → ℝ) :
    0 ≤ exponentGridStepIntegrand (k := k) γ n x := by
  classical
  unfold exponentGridStepIntegrand
  apply Finset.sum_nonneg
  intro u hu
  have hvalid := exponentGridBox_valid hγ hn hu
  by_cases hx : x ∈ exponentBoxSet (exponentGridLower γ n u) (exponentGridUpper γ n u)
  · rw [Set.indicator_of_mem hx]
    apply mul_nonneg
    · exact div_nonneg (by norm_num) (by linarith [hvalid.2.2.1])
    · apply Finset.prod_nonneg
      intro i hi
      have hxi := (Set.mem_pi.mp hx) i (Set.mem_univ i)
      have hγle : γ ≤ x i := le_trans (hvalid.1 i) (le_of_lt hxi.1)
      have hpos : 0 < x i := lt_of_lt_of_le hγ hγle
      exact div_nonneg (by norm_num) hpos.le
  · simp [Set.indicator_of_notMem hx]

lemma integrable_exponentGridStepIntegrand {k : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {n : ℕ} (hn : 0 < n) :
    Integrable (exponentGridStepIntegrand (k := k) γ n) volume := by
  classical
  unfold exponentGridStepIntegrand
  apply integrable_finsetSum
  intro u hu
  have hvalid := exponentGridBox_valid hγ hn hu
  have hcoeffpos : 0 < 1 - ∑ i : Fin k, exponentGridLower γ n u i := by
    linarith [hvalid.2.2.1]
  let c : ℝ := 1 / (1 - ∑ i : Fin k, exponentGridLower γ n u i)
  have hbox := integrable_exponentBox_reciprocal
    (exponentGridLower γ n u) (exponentGridUpper γ n u)
    (fun i => lt_of_lt_of_le hγ (hvalid.1 i)) hvalid.2.1
  have hfun :
      (fun x : Fin k → ℝ => Set.indicator
        (exponentBoxSet (exponentGridLower γ n u) (exponentGridUpper γ n u))
        (fun x => c * ∏ i : Fin k, (1 / x i)) x) =
        fun x => c * Set.indicator
          (exponentBoxSet (exponentGridLower γ n u) (exponentGridUpper γ n u))
          (fun x => ∏ i : Fin k, (1 / x i)) x := by
    funext x
    by_cases hx : x ∈ exponentBoxSet (exponentGridLower γ n u) (exponentGridUpper γ n u)
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have hterm : Integrable (fun x : Fin k → ℝ => Set.indicator
      (exponentBoxSet (exponentGridLower γ n u) (exponentGridUpper γ n u))
      (fun x => c * ∏ i : Fin k, (1 / x i)) x) volume := by
    rw [hfun]
    exact hbox.const_mul c
  simpa [c] using hterm

lemma tendsto_integral_exponentGridStepIntegrand {k : ℕ} {γ : ℝ}
    (hγ : 0 < γ) (hγ1 : γ < 1) :
    Tendsto (fun n : ℕ => ∫ x : Fin k → ℝ, exponentGridStepIntegrand (k := k) γ n x)
      atTop (𝓝 (∫ x : Fin k → ℝ, simplexIntegrand γ x)) := by
  have hFmeas : ∀ᶠ n : ℕ in atTop,
      AEStronglyMeasurable (exponentGridStepIntegrand (k := k) γ n) volume := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact (integrable_exponentGridStepIntegrand hγ hn).aestronglyMeasurable
  have hBound : ∀ᶠ n : ℕ in atTop, ∀ᵐ x : Fin k → ℝ ∂volume,
      ‖exponentGridStepIntegrand (k := k) γ n x‖ ≤ simplexIntegrand γ x := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (exponentGridStepIntegrand_nonneg hγ hn x)]
    exact exponentGridStepIntegrand_le_simplexIntegrand hγ hn x
  exact MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (bound := fun x : Fin k → ℝ => simplexIntegrand γ x) hFmeas hBound
    (simplexIntegrand_integrable hγ) (tendsto_exponentGridStepIntegrand_ae hγ hγ1)

lemma integral_exponentGridStepIntegrand {k : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {n : ℕ} (hn : 0 < n) :
    ∫ x : Fin k → ℝ, exponentGridStepIntegrand (k := k) γ n x =
      ∑ u ∈ exponentGridBoxes k γ n,
        (1 / (1 - ∑ i : Fin k, exponentGridLower γ n u i)) *
          ∏ i : Fin k, Real.log (exponentGridUpper γ n u i /
            exponentGridLower γ n u i) := by
  classical
  have hterms (u : Fin k → ℕ) (hu : u ∈ exponentGridBoxes k γ n) :
      Integrable (fun x : Fin k → ℝ => Set.indicator
        (exponentBoxSet (exponentGridLower γ n u) (exponentGridUpper γ n u))
        (fun x => (1 / (1 - ∑ i : Fin k, exponentGridLower γ n u i)) *
          ∏ i : Fin k, (1 / x i)) x) volume := by
    have hvalid := exponentGridBox_valid hγ hn hu
    have hbox := integrable_exponentBox_reciprocal
      (exponentGridLower γ n u) (exponentGridUpper γ n u)
      (fun i => lt_of_lt_of_le hγ (hvalid.1 i)) hvalid.2.1
    let c : ℝ := 1 / (1 - ∑ i : Fin k, exponentGridLower γ n u i)
    have hfun :
        (fun x : Fin k → ℝ => Set.indicator
          (exponentBoxSet (exponentGridLower γ n u) (exponentGridUpper γ n u))
          (fun x => c * ∏ i : Fin k, (1 / x i)) x) =
          fun x => c * Set.indicator
            (exponentBoxSet (exponentGridLower γ n u) (exponentGridUpper γ n u))
            (fun x => ∏ i : Fin k, (1 / x i)) x := by
      funext x
      by_cases hx : x ∈ exponentBoxSet (exponentGridLower γ n u) (exponentGridUpper γ n u)
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
    have hterm : Integrable (fun x : Fin k → ℝ => Set.indicator
        (exponentBoxSet (exponentGridLower γ n u) (exponentGridUpper γ n u))
        (fun x => c * ∏ i : Fin k, (1 / x i)) x) volume := by
      rw [hfun]
      exact hbox.const_mul c
    simpa [c] using hterm
  calc
    ∫ x : Fin k → ℝ, exponentGridStepIntegrand (k := k) γ n x =
        ∑ u ∈ exponentGridBoxes k γ n, ∫ x : Fin k → ℝ,
          Set.indicator (exponentBoxSet (exponentGridLower γ n u)
            (exponentGridUpper γ n u))
            (fun x => (1 / (1 - ∑ i : Fin k, exponentGridLower γ n u i)) *
              ∏ i : Fin k, (1 / x i)) x := by
          simp only [exponentGridStepIntegrand]
          rw [integral_finsetSum]
          exact hterms
    _ = ∑ u ∈ exponentGridBoxes k γ n,
          (1 / (1 - ∑ i : Fin k, exponentGridLower γ n u i)) *
            ∏ i : Fin k, Real.log (exponentGridUpper γ n u i /
              exponentGridLower γ n u i) := by
          apply Finset.sum_congr rfl
          intro u hu
          have hvalid := exponentGridBox_valid hγ hn hu
          rw [show (fun x : Fin k → ℝ => Set.indicator
              (exponentBoxSet (exponentGridLower γ n u) (exponentGridUpper γ n u))
              (fun x => (1 / (1 - ∑ i : Fin k, exponentGridLower γ n u i)) *
                ∏ i : Fin k, (1 / x i)) x) =
              fun x => (1 / (1 - ∑ i : Fin k, exponentGridLower γ n u i)) *
                Set.indicator (exponentBoxSet (exponentGridLower γ n u)
                  (exponentGridUpper γ n u)) (fun x => ∏ i : Fin k, (1 / x i)) x by
                funext x
                by_cases hx : x ∈ exponentBoxSet (exponentGridLower γ n u)
                    (exponentGridUpper γ n u)
                · simp [Set.indicator_of_mem hx]
                · simp [Set.indicator_of_notMem hx]]
          rw [integral_const_mul, integral_exponentBox_reciprocal]
          · exact fun i => lt_of_lt_of_le hγ (hvalid.1 i)
          · exact hvalid.2.1

/-- The exact integral of the grid step function, written as a finite box sum. -/
noncomputable def exponentGridSum (k : ℕ) (b : ℝ) (n : ℕ) : ℝ :=
  ∑ u ∈ exponentGridBoxes k b n,
    (1 / (1 - ∑ i : Fin k, exponentGridLower b n u i)) *
      ∏ i : Fin k, Real.log (exponentGridUpper b n u i / exponentGridLower b n u i)

/-- Finite grid sums weighted by the factorial of the full prime-factor length. -/
noncomputable def exponentGridFamilySum (K : Finset ℕ) (b : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ K, exponentGridSum k b n / ((k + 1).factorial : ℝ)

lemma tendsto_exponentGridSum (k : ℕ) {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    Tendsto (fun n : ℕ => exponentGridSum k b n) atTop
      (𝓝 (∫ x : Fin k → ℝ, simplexIntegrand b x)) := by
  have hlim := tendsto_integral_exponentGridStepIntegrand (k := k) hb hb1
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact integral_exponentGridStepIntegrand hb hn

lemma tendsto_exponentGridFamilySum_integrals (K : Finset ℕ) {b : ℝ}
    (hb : 0 < b) (hb1 : b < 1) :
    Tendsto (fun n : ℕ => exponentGridFamilySum K b n) atTop
      (𝓝 (∑ k ∈ K,
        (∫ x : Fin k → ℝ, simplexIntegrand b x) / ((k + 1).factorial : ℝ))) := by
  unfold exponentGridFamilySum
  apply tendsto_finsetSum K
  intro k hk
  exact (tendsto_exponentGridSum k hb hb1).div_const _

end ArtinPrimitiveRoots.Proofs.b_density_sol
