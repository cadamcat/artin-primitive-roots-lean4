import Mathlib
import ArtinPrimitiveRoots.Sieve.Density.B_DENSITY.Coordinates
import ArtinPrimitiveRoots.Sieve.Density.B_DENSITY.Arithmetic
import ArtinPrimitiveRoots.Sieve.Density.B_DENSITY.Grid
import ArtinPrimitiveRoots.Sieve.Density.B_DENSITY.Counting
import ArtinPrimitiveRoots.Sieve.Density.B_DENSITY.BlockSieve

/-!
# Buchstab's rough-number densities (paper: (8.x) `eq:rough-density-definition`, Lemma `lem:density`)

Sources: definition `08-type-ii.tex`, lines 254–273; Lemma `lem:density`, `11-sieve.tex`,
lines 146–251.
-/

namespace ArtinPrimitiveRoots.Sieve

open MeasureTheory

/-- The term `D_{γ,j}(w)` of `eq:rough-density-definition`: `D_{γ,1}(w) = 1/w`, and for `j ≥ 2`,
`(1/j!) ∫ 1/(w - ∑_{i<j} t_i) ∏_{i<j} dt_i/t_i` over `t_i ≥ γ` (`1 ≤ i < j`) with
`∑_{i<j} t_i ≤ w - γ`. The index `j = 0` contributes `0`. -/
noncomputable def roughDensityTerm (γ w : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then 0
  else if j = 1 then 1 / w
  else (1 / (j.factorial : ℝ)) *
    ∫ t : Fin (j - 1) → ℝ,
      Set.indicator {t : Fin (j - 1) → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w - γ}
        (fun t => (1 / (w - ∑ i, t i)) * ∏ i, (1 / t i)) t

/-- `D_γ(w) = ∑_{j ≥ 1} D_{γ,j}(w)` (`eq:rough-density-definition`); for `w > γ > 0` only finitely
many terms are nonzero. -/
noncomputable def roughDensity (γ w : ℝ) : ℝ := ∑' j : ℕ, roughDensityTerm γ w j

namespace b_density_sol

open Filter
open scoped Topology

open ArtinPrimitiveRoots.Proofs.b_density_sol

/-- A term with at least two prime factors vanishes once the lower bounds on all
coordinates force their sum past the allowed simplex. -/
lemma roughDensityTerm_eq_zero_of_lt_mul {γ w : ℝ} {j : ℕ}
    (hj : 2 ≤ j) (hγw : w < (j : ℝ) * γ) :
    roughDensityTerm γ w j = 0 := by
  have hj0 : j ≠ 0 := by omega
  have hj1 : j ≠ 1 := by omega
  have hset :
      {t : Fin (j - 1) → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w - γ} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro t ht
    simp only [Set.mem_ofPred_eq] at ht
    have hsum : ∑ i : Fin (j - 1), γ ≤ ∑ i, t i :=
      Finset.sum_le_sum fun i _ => ht.1 i
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    have hjcast : (j : ℝ) = ((j - 1 : ℕ) : ℝ) + 1 := by
      exact_mod_cast (Nat.sub_add_cancel (show 1 ≤ j by omega)).symm
    rw [hjcast] at hγw
    have hcontra : (j : ℝ) * γ ≤ w := by
      rw [hjcast]
      linarith
    linarith
  simp [roughDensityTerm, hj0, hj1, hset]

/-- The defining series is a finite sum whenever the cutoff has passed the `N`-th term. -/
lemma roughDensity_eq_sum_range_of_lt_mul {γ w : ℝ} {N : ℕ}
    (hγ : 0 < γ) (hN : 2 ≤ N) (hcut : w < (N : ℝ) * γ) :
    roughDensity γ w = ∑ j ∈ Finset.range N, roughDensityTerm γ w j := by
  unfold roughDensity
  apply tsum_eq_sum (s := Finset.range N)
  intro j hj
  have hNj : N ≤ j := by simpa using hj
  apply roughDensityTerm_eq_zero_of_lt_mul (j := j) (by omega) ?_
  exact lt_of_lt_of_le hcut (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hNj) hγ.le)

/-- The density series is locally finite on its defining domain `w > γ > 0`. -/
lemma finite_density_sum {γ w : ℝ} (hγ : 0 < γ) :
    ∃ N : ℕ, 2 ≤ N ∧ w < (N : ℝ) * γ ∧
      roughDensity γ w = ∑ j ∈ Finset.range N, roughDensityTerm γ w j := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (w / γ))
  have hNgt : max 1 (w / γ) < (N : ℝ) := hN
  have h1 : (1 : ℝ) < N := lt_of_le_of_lt (le_max_left _ _) hNgt
  have hNtwo : 2 ≤ N := by
    have hNnat : 1 < N := by exact_mod_cast h1
    omega
  have hcut : w < (N : ℝ) * γ := by
    have hdiv : w / γ < (N : ℝ) := lt_of_le_of_lt (le_max_right _ _) hNgt
    have := (div_lt_iff₀ hγ).mp hdiv
    nlinarith
  refine ⟨N, hNtwo, hcut, ?_⟩
  exact roughDensity_eq_sum_range_of_lt_mul hγ hNtwo hcut

/-- A fixed `j ≥ 2` rough-density term is the reciprocal-coordinate integral over
the full simplex, written in a symmetric coordinate chart. -/
lemma roughDensityTerm_succ_eq_simplexIntegral {γ : ℝ} (n : ℕ) (hn : 0 < n) :
    roughDensityTerm γ 1 (n + 1) =
      (1 / ((n + 1).factorial : ℝ)) *
        ∫ x : Fin n → ℝ, simplexIntegrand γ x := by
  classical
  have hj0 : n + 1 ≠ 0 := by omega
  have hj1 : n + 1 ≠ 1 := by omega
  simp only [roughDensityTerm, if_neg hj0, if_neg hj1]
  rw [show n + 1 - 1 = n by omega]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  have hset : simplexGoodSet γ x ↔
      (∀ i, γ ≤ x i) ∧ ∑ i, x i ≤ 1 - γ := by
    constructor
    · intro hx
      refine ⟨fun i => hx (some i), ?_⟩
      have h := hx none
      simp only [simplexCoordinate] at h
      linarith
    · rintro ⟨hx, hsum⟩ c
      cases c with
      | none =>
        simp only [simplexCoordinate]
        linarith
      | some i => exact hx i
  have hweight : simplexWeight x =
      (1 / (1 - ∑ i, x i)) * ∏ i, (1 / x i) := by
    simp [simplexWeight, simplexCoordinate, Fintype.prod_option]
    ring
  unfold simplexIntegrand
  rw [Set.indicator_apply, Set.indicator_apply]
  have hmem : x ∈ {t : Fin n → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ 1 - γ} ↔
      x ∈ simplexGoodSet γ := hset.symm
  simp only [hmem, hweight]

lemma simplexMinChart_integral_eq_term {k : ℕ} {b t : ℝ}
    (hb : 0 < b) (hbt : b ≤ t) (ht : t ≤ 1 / 2) :
    ∫ u : Fin k → ℝ, simplexMinChartIntegrand b t u =
      ((k + 1).factorial : ℝ) * roughDensityTerm t (1 - t) (k + 1) / t := by
  classical
  have ht0 : 0 < t := lt_of_lt_of_le hb hbt
  by_cases hk : k = 0
  · subst k
    have ht2 : 2 * t ≤ 1 := by linarith
    have hmass0 : volume (Set.univ : Set (Fin 0 → ℝ)) = 1 := by
      change Measure.pi (fun _ : Fin 0 => (volume : Measure ℝ)) Set.univ = 1
      exact MeasureTheory.Measure.pi_empty_univ _
    have hvol0 : volume.real (Set.univ : Set (Fin 0 → ℝ)) = 1 := by
      change (volume (Set.univ : Set (Fin 0 → ℝ))).toReal = 1
      rw [hmass0]
      simp
    simp [simplexMinChartIntegrand, simplexMinChartSet, simplexMinChartKernel,
      roughDensityTerm, hbt, ht2, ht0, hvol0]
    <;> ring
    <;> field_simp [ne_of_gt ht0, (show 1 - t ≠ 0 by linarith)] <;> ring
  · have hj0 : k + 1 ≠ 0 := by omega
    have hj1 : k + 1 ≠ 1 := by omega
    let S : Set (Fin k → ℝ) :=
      {u | (∀ i, t ≤ u i) ∧ ∑ i, u i ≤ (1 - t) - t}
    have hsumEq : (1 - t) - t = 1 - 2 * t := by ring
    have hset : {u : Fin k → ℝ | simplexMinChartSet b t u} = S := by
      ext u
      simp [simplexMinChartSet, S, hbt, hsumEq]
    have hpoint (u : Fin k → ℝ) :
        simplexMinChartIntegrand b t u =
          (1 / t) * Set.indicator S
            (fun u => (1 / ((1 - t) - ∑ i, u i)) * ∏ i, (1 / u i)) u := by
      unfold simplexMinChartIntegrand simplexMinChartKernel
      by_cases hu : u ∈ {u : Fin k → ℝ | simplexMinChartSet b t u}
      · have huS : u ∈ S := by rw [← hset]; exact hu
        simp only [Set.indicator_of_mem hu, Set.indicator_of_mem huS]
        ring
      · have huS : u ∉ S := by rw [← hset]; exact hu
        simp only [Set.indicator_of_notMem hu, Set.indicator_of_notMem huS]
        simp
    have hterm : roughDensityTerm t (1 - t) (k + 1) =
        (1 / ((k + 1).factorial : ℝ)) *
          ∫ u : Fin k → ℝ, Set.indicator S
            (fun u => (1 / ((1 - t) - ∑ i, u i)) * ∏ i, (1 / u i)) u := by
      simp only [roughDensityTerm, if_neg hj0, if_neg hj1]
      rw [show k + 1 - 1 = k by omega]
    have hpointAE :
        (fun u : Fin k → ℝ => simplexMinChartIntegrand b t u) =ᵐ[volume]
          (fun u => (1 / t) * Set.indicator S
            (fun u => (1 / ((1 - t) - ∑ i, u i)) * ∏ i, (1 / u i)) u) := by
      filter_upwards [] with u
      exact hpoint u
    calc
      ∫ u : Fin k → ℝ, simplexMinChartIntegrand b t u =
          (1 / t) * ∫ u : Fin k → ℝ, Set.indicator S
            (fun u => (1 / ((1 - t) - ∑ i, u i)) * ∏ i, (1 / u i)) u := by
        rw [integral_congr_ae hpointAE, integral_const_mul]
      _ = ((k + 1).factorial : ℝ) * roughDensityTerm t (1 - t) (k + 1) / t := by
        rw [hterm]
        have hfac : (k + 1).factorial ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (k + 1)
        field_simp
        <;> ring

lemma simplexMin_sector_eq_interval_integral {k : ℕ} {b : ℝ}
    (hb : 0 < b) (hbhalf : b ≤ 1 / 2) :
    (1 / ((k + 1).factorial : ℝ)) *
        ∫ x : Fin (k + 1) → ℝ, simplexMinIntegrand b (some 0) x =
      ∫ t in b..(1 / 2), roughDensityTerm t (1 - t) (k + 1) / t := by
  classical
  let chartInner : ℝ → ℝ := fun t =>
    ∫ u : Fin k → ℝ, simplexMinChartIntegrand b t u
  have hzero (t : ℝ) (ht : t < b ∨ 1 / 2 < t) : chartInner t = 0 := by
    have hset : {u : Fin k → ℝ | simplexMinChartSet b t u} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro u hu
      simp only [Set.mem_setOf_eq, simplexMinChartSet] at hu
      rcases ht with htb | hthalf
      · linarith [hu.1]
      · have hterm : ∀ i, 0 ≤ u i := by
          intro i
          have htpos : 0 < t := by linarith
          exact le_trans (le_of_lt htpos) (hu.2.1 i)
        have hsum : 0 ≤ ∑ i, u i := Finset.sum_nonneg fun i _ => hterm i
        have hneg : 1 - 2 * t < 0 := by linarith
        linarith [hu.2.2]
    dsimp [chartInner]
    calc
      ∫ u : Fin k → ℝ, simplexMinChartIntegrand b t u = ∫ _ : Fin k → ℝ, (0 : ℝ) := by
        apply integral_congr_ae
        filter_upwards [] with u
        simp [simplexMinChartIntegrand, hset]
      _ = 0 := by simp
  have hpoint : ∀ᵐ t : ℝ ∂volume,
      chartInner t = Set.indicator (Set.Ioc b (1 / 2))
        (fun t => ((k + 1).factorial : ℝ) * roughDensityTerm t (1 - t) (k + 1) / t) t := by
    have htn : ∀ᵐ t : ℝ ∂volume, t ≠ b := by
      rw [ae_iff]
      simp
    filter_upwards [htn] with t htb
    by_cases hlo : b < t
    · by_cases hhi : t ≤ 1 / 2
      · have hmem : t ∈ Set.Ioc b (1 / 2) := ⟨hlo, hhi⟩
        have hval : chartInner t =
            ((k + 1).factorial : ℝ) * roughDensityTerm t (1 - t) (k + 1) / t := by
          dsimp [chartInner]
          exact simplexMinChart_integral_eq_term hb (le_of_lt hlo) hhi
        rw [hval, Set.indicator_of_mem hmem]
      · have hgt : 1 / 2 < t := lt_of_not_ge hhi
        have hz := hzero t (Or.inr hgt)
        have hmem : t ∉ Set.Ioc b (1 / 2) := fun h => hhi h.2
        rw [hz, Set.indicator_of_notMem hmem]
    · have hlt : t < b := lt_of_le_of_ne (le_of_not_gt hlo) htb
      have hz := hzero t (Or.inl hlt)
      have hmem : t ∉ Set.Ioc b (1 / 2) := fun h => (not_lt_of_ge (le_of_lt hlt)) h.1
      rw [hz, Set.indicator_of_notMem hmem]
  have hscaled :
      (fun t => (1 / ((k + 1).factorial : ℝ)) * chartInner t) =ᵐ[volume]
        (fun t => Set.indicator (Set.Ioc b (1 / 2))
          (fun t => roughDensityTerm t (1 - t) (k + 1) / t) t) := by
    filter_upwards [hpoint] with t ht
    by_cases hm : t ∈ Set.Ioc b (1 / 2)
    · have hval : chartInner t =
          ((k + 1).factorial : ℝ) * roughDensityTerm t (1 - t) (k + 1) / t := by
        rw [Set.indicator_of_mem hm] at ht
        exact ht
      rw [hval, Set.indicator_of_mem hm]
      have hfac : (k + 1).factorial ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (k + 1)
      field_simp
      <;> ring
    · have hval : chartInner t = 0 := by
        rw [Set.indicator_of_notMem hm] at ht
        exact ht
      rw [hval, Set.indicator_of_notMem hm]
      simp
  calc
    (1 / ((k + 1).factorial : ℝ)) *
        ∫ x : Fin (k + 1) → ℝ, simplexMinIntegrand b (some 0) x =
      (1 / ((k + 1).factorial : ℝ)) * ∫ t : ℝ, chartInner t := by
        rw [ArtinPrimitiveRoots.Proofs.b_density_sol.integral_simplexMinIntegrand_finCons hb]
    _ = ∫ t : ℝ, (1 / ((k + 1).factorial : ℝ)) * chartInner t := by
      rw [integral_const_mul]
    _ = ∫ t : ℝ, Set.indicator (Set.Ioc b (1 / 2))
          (fun t => roughDensityTerm t (1 - t) (k + 1) / t) t :=
        integral_congr_ae hscaled
    _ = ∫ t in b..(1 / 2), roughDensityTerm t (1 - t) (k + 1) / t := by
      rw [integral_indicator measurableSet_Ioc]
      exact (intervalIntegral.integral_of_le hbhalf).symm

lemma intervalIntegrable_roughDensityTerm_div {k : ℕ} {b : ℝ}
    (hb : 0 < b) (hbhalf : b ≤ 1 / 2) :
    IntervalIntegrable (fun t => roughDensityTerm t (1 - t) (k + 1) / t)
      volume b (1 / 2) := by
  let chartInner : ℝ → ℝ := fun t =>
    ∫ u : Fin k → ℝ, simplexMinChartIntegrand b t u
  let c : ℝ := 1 / ((k + 1).factorial : ℝ)
  have hchart : Integrable chartInner volume := by
    simpa [chartInner] using
      ArtinPrimitiveRoots.Proofs.b_density_sol.integrable_simplexMinChartInner (k := k) hb
  have hscaled : Integrable (fun t => c * chartInner t) volume := hchart.const_mul c
  have hfac : (0 : ℝ) < ((k + 1).factorial : ℝ) := by positivity
  have hEq : (fun t => roughDensityTerm t (1 - t) (k + 1) / t) =ᵐ[
      volume.restrict (Set.Ioc b (1 / 2))] (fun t => c * chartInner t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hterm := simplexMinChart_integral_eq_term (k := k) hb ht.1.le ht.2
    dsimp [c, chartInner]
    rw [hterm]
    field_simp [ne_of_gt hfac]
    <;> ring
  have hscaledOn : Integrable (fun t => c * chartInner t)
      (volume.restrict (Set.Ioc b (1 / 2))) := hscaled.mono_measure Measure.restrict_le_self
  have htermOn : Integrable (fun t => roughDensityTerm t (1 - t) (k + 1) / t)
      (volume.restrict (Set.Ioc b (1 / 2))) := hscaledOn.congr hEq.symm
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hbhalf]
  exact htermOn

lemma integral_simplexIntegrand_eq_card_mul_min {n : ℕ} {b : ℝ} (hb : 0 < b) :
    ∫ x : Fin n → ℝ, simplexIntegrand b x =
      (Fintype.card (Option (Fin n)) : ℝ) *
        ∫ x : Fin n → ℝ, simplexMinIntegrand b none x := by
  rw [integral_simplexIntegrand_eq_sum_min hb, Fintype.sum_option]
  simp_rw [integral_simplexMinIntegrand_swap]
  simp [Fintype.card_option, Finset.sum_const]
  <;> ring

lemma roughDensityTerm_eq_interval_integral {b : ℝ} (hb : 0 < b)
    (hbhalf : b ≤ 1 / 2) (k : ℕ) :
    roughDensityTerm b 1 (k + 2) =
      ∫ t in b..(1 / 2), roughDensityTerm t (1 - t) (k + 1) / t := by
  have hj : 0 < k + 1 := by omega
  have htotal := integral_simplexIntegrand_eq_card_mul_min (n := k + 1) hb
  have hsectorEq :
      ∫ x : Fin (k + 1) → ℝ, simplexMinIntegrand b none x =
        ∫ x : Fin (k + 1) → ℝ, simplexMinIntegrand b (some 0) x :=
    (integral_simplexMinIntegrand_swap b (0 : Fin (k + 1))).symm
  have hcard : (Fintype.card (Option (Fin (k + 1))) : ℝ) = (k + 2 : ℝ) := by
    simp [Fintype.card_option, Fintype.card_fin]
    ring
  have hfactor : (k + 2).factorial = (k + 2) * (k + 1).factorial := by
    simp [Nat.factorial_succ]
  have hfacpos : (0 : ℝ) < ((k + 1).factorial : ℝ) := by positivity
  have hjpos : (0 : ℝ) < (k + 2 : ℝ) := by positivity
  calc
    roughDensityTerm b 1 (k + 2) =
        (1 / ((k + 2).factorial : ℝ)) *
          ∫ x : Fin (k + 1) → ℝ, simplexIntegrand b x := by
      simpa [Nat.add_assoc] using
        (roughDensityTerm_succ_eq_simplexIntegral (γ := b) (n := k + 1) hj)
    _ = (1 / ((k + 2).factorial : ℝ)) *
          ((k + 2 : ℝ) * ∫ x : Fin (k + 1) → ℝ,
            simplexMinIntegrand b (some 0) x) := by
      rw [htotal, hsectorEq, hcard]
    _ = (1 / ((k + 1).factorial : ℝ)) *
          ∫ x : Fin (k + 1) → ℝ, simplexMinIntegrand b (some 0) x := by
      rw [show ((k + 2).factorial : ℝ) = (k + 2 : ℝ) * ((k + 1).factorial : ℝ) by
        exact_mod_cast hfactor]
      field_simp [ne_of_gt hfacpos, ne_of_gt hjpos]
      <;> ring
    _ = ∫ t in b..(1 / 2), roughDensityTerm t (1 - t) (k + 1) / t :=
      simplexMin_sector_eq_interval_integral hb hbhalf

lemma density_identity :
    ∀ b : ℝ, 0 < b → b < 1 / 2 →
      ∫ t in b..(1 / 2), roughDensity t (1 - t) / t = roughDensity b 1 - 1 := by
  intro b hb hbhalf
  obtain ⟨N, hN, hcut, _hfinite⟩ := finite_density_sum (γ := b) (w := 1) hb
  have hcutPlus : 1 < (N + 1 : ℝ) * b := by
    have hmono : (N : ℝ) * b ≤ (N + 1 : ℝ) * b := by nlinarith [hb]
    exact hcut.trans_le hmono
  have hcutPlusNat : 1 < ((N + 1 : ℕ) : ℝ) * b := by
    simpa only [Nat.cast_add, Nat.cast_one] using hcutPlus
  have hDb : roughDensity b 1 =
      ∑ j ∈ Finset.range (N + 1), roughDensityTerm b 1 j :=
    roughDensity_eq_sum_range_of_lt_mul hb (by omega) hcutPlusNat
  have hDpoint : ∀ t : ℝ, b ≤ t →
      roughDensity t (1 - t) =
        ∑ j ∈ Finset.range N, roughDensityTerm t (1 - t) j := by
    intro t hbt
    have ht : 0 < t := lt_of_lt_of_le hb hbt
    have hmono : (N : ℝ) * b ≤ (N : ℝ) * t :=
      mul_le_mul_of_nonneg_left hbt (by positivity)
    have hcutT : 1 - t < (N : ℝ) * t := by linarith
    exact roughDensity_eq_sum_range_of_lt_mul ht hN hcutT
  have hpoint : ∀ t : ℝ, t ∈ Set.Ioc b (1 / 2) →
      roughDensity t (1 - t) / t =
        ∑ j ∈ Finset.range N, roughDensityTerm t (1 - t) j / t := by
    intro t ht
    rw [hDpoint t ht.1.le, Finset.sum_div]
  have hInt : ∀ j ∈ Finset.range N,
      IntervalIntegrable (fun t => roughDensityTerm t (1 - t) j / t) volume b (1 / 2) := by
    intro j hj
    by_cases hj0 : j = 0
    · subst j
      simp [roughDensityTerm]
    · obtain ⟨k, hk⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      rw [hk]
      exact intervalIntegrable_roughDensityTerm_div (k := k) hb hbhalf.le
  have houter :
      ∫ t in b..(1 / 2), roughDensity t (1 - t) / t =
        ∑ j ∈ Finset.range N,
          ∫ t in b..(1 / 2), roughDensityTerm t (1 - t) j / t := by
    calc
      ∫ t in b..(1 / 2), roughDensity t (1 - t) / t =
          ∫ t in b..(1 / 2), ∑ j ∈ Finset.range N,
            roughDensityTerm t (1 - t) j / t := by
              apply intervalIntegral.integral_congr_ae'
              · filter_upwards [] with t ht
                exact hpoint t ht
              · filter_upwards [] with t ht
                exfalso
                linarith [hbhalf, ht.1, ht.2]
      _ = ∑ j ∈ Finset.range N,
          ∫ t in b..(1 / 2), roughDensityTerm t (1 - t) j / t :=
            intervalIntegral.integral_finsetSum hInt
  have houterSum :
      (∑ j ∈ Finset.range N,
        ∫ t in b..(1 / 2), roughDensityTerm t (1 - t) j / t) =
          ∑ k ∈ Finset.range (N - 1), roughDensityTerm b 1 (k + 2) := by
    rw [show N = (N - 1) + 1 by omega, Finset.sum_range_succ']
    have hzero : ∫ t in b..(1 / 2), roughDensityTerm t (1 - t) 0 / t = 0 := by
      simp [roughDensityTerm]
    rw [hzero, add_zero]
    rw [show N - 1 + 1 - 1 = N - 1 by omega]
    apply Finset.sum_congr rfl
    intro k hk
    exact (roughDensityTerm_eq_interval_integral hb hbhalf.le k).symm
  have hDbSplit : roughDensity b 1 - 1 =
      ∑ k ∈ Finset.range (N - 1), roughDensityTerm b 1 (k + 2) := by
    rw [hDb]
    rw [Finset.sum_range_succ']
    rw [show N = (N - 1) + 1 by omega, Finset.sum_range_succ']
    simp [roughDensityTerm]
  rw [houter, houterSum, hDbSplit]

/-- The simplex bridge includes the one-prime term, whose independent space is empty. -/
lemma roughDensityTerm_succ_eq_simplexIntegral_all {b : ℝ} (hb1 : b < 1) (k : ℕ) :
    roughDensityTerm b 1 (k + 1) =
      (∫ x : Fin k → ℝ, simplexIntegrand b x) / ((k + 1).factorial : ℝ) := by
  by_cases hk : k = 0
  · subst k
    have hmass : volume (Set.univ : Set (Fin 0 → ℝ)) = 1 := by
      change Measure.pi (fun _ : Fin 0 => (volume : Measure ℝ)) Set.univ = 1
      exact MeasureTheory.Measure.pi_empty_univ _
    have hvol : volume.real (Set.univ : Set (Fin 0 → ℝ)) = 1 := by
      change (volume (Set.univ : Set (Fin 0 → ℝ))).toReal = 1
      rw [hmass]
      simp
    have hfun : (simplexIntegrand b : (Fin 0 → ℝ) → ℝ) = fun _ => 1 := by
      funext x
      have hmem : x ∈ simplexGoodSet b := by
        intro c
        cases c with
        | none => simpa [simplexCoordinate] using hb1.le
        | some i => exact Fin.elim0 i
      have hw : simplexWeight x = 1 := by
        unfold simplexWeight
        rw [Fintype.prod_option]
        simp [simplexCoordinate]
      simp [simplexIntegrand, hmem, hw]
    simp [roughDensityTerm, hfun, hvol]
  · simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using
      (roughDensityTerm_succ_eq_simplexIntegral (γ := b) k (Nat.pos_of_ne_zero hk))

/-- Reindex the finite density sum by the number of independent coordinates. -/
lemma roughDensity_eq_sum_simplexIntegral {b : ℝ} {J : ℕ}
    (hb : 0 < b) (hb1 : b < 1) (hJ : 2 ≤ J) (hcut : 1 < (J : ℝ) * b) :
    roughDensity b 1 = ∑ k ∈ Finset.range (J - 1),
      (∫ x : Fin k → ℝ, simplexIntegrand b x) / ((k + 1).factorial : ℝ) := by
  have hzero : roughDensityTerm b 1 0 = 0 := by simp [roughDensityTerm]
  calc
    roughDensity b 1 = ∑ j ∈ Finset.range J, roughDensityTerm b 1 j :=
      roughDensity_eq_sum_range_of_lt_mul hb hJ hcut
    _ = ∑ k ∈ Finset.range (J - 1), roughDensityTerm b 1 (k + 1) := by
      conv_lhs => rw [show J = (J - 1) + 1 by omega, Finset.sum_range_succ']
      rw [hzero, add_zero]
    _ = ∑ k ∈ Finset.range (J - 1),
        (∫ x : Fin k → ℝ, simplexIntegrand b x) / ((k + 1).factorial : ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact roughDensityTerm_succ_eq_simplexIntegral_all hb1 k

/-- A finite family of grids converges to the frozen density, including its one-prime term. -/
lemma tendsto_exponentGridFamilySum_density {b : ℝ} {J : ℕ}
    (hb : 0 < b) (hb1 : b < 1) (hJ : 2 ≤ J) (hcut : 1 < (J : ℝ) * b) :
    Tendsto (fun n : ℕ => exponentGridFamilySum (Finset.range (J - 1)) b n)
      atTop (𝓝 (roughDensity b 1)) := by
  rw [roughDensity_eq_sum_simplexIntegral hb hb1 hJ hcut]
  exact tendsto_exponentGridFamilySum_integrals (Finset.range (J - 1)) hb hb1

/-- The uniform upper bound with the frozen exponential rate. -/
lemma density_upper_bound :
    ∃ b₀ : ℝ, 0 < b₀ ∧ ∃ C_d : ℝ, 0 < C_d ∧ ∀ b : ℝ, 0 < b → b < b₀ →
      roughDensity b 1 ≤
        Real.exp (-Real.eulerMascheroniConstant) / b *
          (1 + C_d * Real.exp (-(1 / 20) / b)) := by
  sorry

end b_density_sol

/-- **Lemma `lem:density`.** For `0 < b < 1/2`, `∫_b^{1/2} D_t(1 - t) dt/t = D_b(1) - 1`; and there
are absolute constants `b₀, C_d > 0` with `D_b(1) ≤ e^{-γ_E}/b · (1 + C_d e^{-1/(20 b)})` for
`0 < b < b₀` (the paper's `c_d = 1/20`). -/
theorem lem_density :
    (∀ b : ℝ, 0 < b → b < 1 / 2 →
      ∫ t in b..(1 / 2), roughDensity t (1 - t) / t = roughDensity b 1 - 1) ∧
    ∃ b₀ : ℝ, 0 < b₀ ∧ ∃ C_d : ℝ, 0 < C_d ∧ ∀ b : ℝ, 0 < b → b < b₀ →
      roughDensity b 1 ≤
        Real.exp (-Real.eulerMascheroniConstant) / b * (1 + C_d * Real.exp (-(1 / 20) / b)) := by
  exact ⟨b_density_sol.density_identity, b_density_sol.density_upper_bound⟩

end ArtinPrimitiveRoots.Sieve
