import Mathlib
import OAI.NumberTheory.PrimeGaps.Main
import ArtinPrimitiveRoots.TypeII.Defs

namespace ArtinPrimitiveRoots.Ext.Proofs.SWBV

open Classical MeasureTheory intervalIntegral Finset
open ArtinPrimitiveRoots.TypeII

noncomputable def primeClassWeight (q c n : ℕ) : ℝ :=
  if n.Prime ∧ (n : ZMod q) = (c : ZMod q) then Real.log n else 0

noncomputable def primeClassTheta (x : ℝ) (q c : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, primeClassWeight q c n

noncomputable def primeClassCount (x : ℝ) (q c : ℕ) : ℕ :=
  ((primesUpTo x).filter fun n : ℕ => (n : ZMod q) = (c : ZMod q)).card

noncomputable def primeClassPsi (x : ℝ) (q c : ℕ) : ℝ :=
  OAI.LargePrimeGaps.residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c

theorem primeClassPsi_eq_sum {x : ℝ} {q c : ℕ} (hq : 0 < q) (hc : c < q) :
    primeClassPsi x q c =
      ∑ n ∈ Finset.Icc 0 ⌊x⌋₊,
        if (n : ZMod q) = (c : ZMod q) then ArithmeticFunction.vonMangoldt n else 0 := by
  let g : ℕ → ℝ := fun n =>
    if (n : ZMod q) = (c : ZMod q) then ArithmeticFunction.vonMangoldt n else 0
  have hcast (n : ℕ) : (n : ZMod q) = (c : ZMod q) ↔ n % q = c := by
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hc]
  have hzero : g 0 = 0 := by
    simp [g, ArithmeticFunction.vonMangoldt_apply, not_isPrimePow_zero]
  have hIoc : Finset.Ioc 0 ⌊x⌋₊ = (Finset.Icc 0 ⌊x⌋₊).erase 0 := by
    ext n
    simp
  have hremove :
      (∑ n ∈ (Finset.Icc 0 ⌊x⌋₊).erase 0, g n) =
        ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, g n := by
    apply Finset.sum_subset (Finset.erase_subset _ _)
    intro n hn hn'
    have hn0 : n = 0 := by
      by_contra hne
      exact hn' (Finset.mem_erase.mpr ⟨hne, hn⟩)
    subst n
    exact hzero
  unfold primeClassPsi OAI.LargePrimeGaps.residuePrefix
    OAI.LargePrimeGaps.residueSlice
  rw [Finset.sum_filter]
  change (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
      if n % q = c then ArithmeticFunction.vonMangoldt n else 0) = _
  calc
    _ = ∑ n ∈ (Finset.Icc 0 ⌊x⌋₊).erase 0, g n := by
      rw [hIoc]
      apply Finset.sum_congr rfl
      intro n hn
      simp [g, hcast]
    _ = ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, g n := hremove

theorem primeClassPsi_bounds (x : ℝ) {q c : ℕ} (hq : 0 < q) (hc : c < q) :
    0 ≤ primeClassPsi x q c ∧ primeClassPsi x q c ≤ Chebyshev.psi x := by
  rw [primeClassPsi_eq_sum hq hc, Chebyshev.psi_eq_sum_Icc]
  constructor
  · exact Finset.sum_nonneg fun n hn => by
      split_ifs <;> positivity
  · apply Finset.sum_le_sum
    intro n hn
    by_cases h : (n : ZMod q) = (c : ZMod q)
    · simp [h]
    · simp [h, ArithmeticFunction.vonMangoldt_nonneg]

theorem endpointClassError_le_real (x : ℝ) {q c : ℕ}
    (hc : c < q) (hcop : Nat.Coprime c q) :
    |primeClassPsi x q c - x / (q.totient : ℝ)| ≤
      (OAI.LargePrimeGaps.endpointError x q : ℝ) := by
  have h := Finset.le_sup (f := fun v => if Nat.Coprime v q then
      NNReal.mk
        (|OAI.LargePrimeGaps.residuePrefix ArithmeticFunction.vonMangoldt
            ⌊x⌋₊ q v - x / (q.totient : ℝ)|)
        (abs_nonneg _) else 0) (Finset.mem_range.mpr hc)
  have h' := h
  simp only [if_pos hcop] at h'
  have h'' : NNReal.mk (|primeClassPsi x q c - x / (q.totient : ℝ)|)
      (abs_nonneg _) ≤ OAI.LargePrimeGaps.endpointError x q := by
    simpa [primeClassPsi, OAI.LargePrimeGaps.endpointError] using h'
  simpa using (NNReal.coe_le_coe.mpr h'')

theorem endpointError_le_linear {x : ℝ} (hx : 2 ≤ x) {q : ℕ} (hq : 0 < q) :
    (OAI.LargePrimeGaps.endpointError x q : ℝ) ≤
      (Real.log 4 + 5) * x := by
  have hphi : (1 : ℝ) ≤ (q.totient : ℝ) := by
    exact_mod_cast (Nat.totient_pos.mpr hq)
  have hpsi := Chebyshev.psi_le_const_mul_self (by linarith : 0 ≤ x)
  have hnn : 0 ≤ (Real.log 4 + 5) * x := by positivity
  let B : NNReal := ⟨(Real.log 4 + 5) * x, hnn⟩
  change (OAI.LargePrimeGaps.endpointError x q : ℝ) ≤ (B : ℝ)
  apply NNReal.coe_le_coe.mpr
  unfold OAI.LargePrimeGaps.endpointError
  apply Finset.sup_le
  intro c hc
  by_cases hcop : Nat.Coprime c q
  · have hcq : c < q := Finset.mem_range.mp hc
    have hclass := primeClassPsi_bounds x hq hcq
    have herror := endpointClassError_le_real x hcq hcop
    have hmain : 0 ≤ x / (q.totient : ℝ) := by positivity
    have hmain' : x / (q.totient : ℝ) ≤ x := by
      exact (div_le_iff₀ (by exact_mod_cast Nat.totient_pos.mpr hq)).2 (by nlinarith)
    have habs : |primeClassPsi x q c - x / (q.totient : ℝ)| ≤
        primeClassPsi x q c + x / (q.totient : ℝ) := by
      rw [abs_le]
      constructor <;> nlinarith [hclass.1, hmain]
    have hbound : |primeClassPsi x q c - x / (q.totient : ℝ)| ≤
        (Real.log 4 + 5) * x := by
      calc
        _ ≤ Chebyshev.psi x + x := by nlinarith [habs, hclass.2, hmain']
        _ ≤ (Real.log 4 + 5) * x := by nlinarith [hpsi]
    simp only [if_pos hcop]
    have hReal :
        (NNReal.mk
          (|OAI.LargePrimeGaps.residuePrefix ArithmeticFunction.vonMangoldt
              ⌊x⌋₊ q c - x / (q.totient : ℝ)|)
          (abs_nonneg _) : ℝ) ≤ (B : ℝ) := by
      change |primeClassPsi x q c - x / (q.totient : ℝ)| ≤
        (Real.log 4 + 5) * x
      exact hbound
    exact NNReal.coe_le_coe.mp hReal
  · simp only [if_neg hcop]
    exact bot_le

theorem measurable_endpointError {q : ℕ} (hq : 0 < q) :
    Measurable (fun x : ℝ => (OAI.LargePrimeGaps.endpointError x q : ℝ)) := by
  have hpref (c : ℕ) : Measurable (fun x : ℝ =>
      OAI.LargePrimeGaps.residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c) := by
    exact (Measurable.of_discrete (f := fun n : ℕ =>
      OAI.LargePrimeGaps.residuePrefix ArithmeticFunction.vonMangoldt n q c)).comp
        Nat.measurable_floor
  have hterm (c : ℕ) : Measurable (fun x : ℝ =>
      if Nat.Coprime c q then
        NNReal.mk
          (|OAI.LargePrimeGaps.residuePrefix ArithmeticFunction.vonMangoldt
              ⌊x⌋₊ q c - x / (q.totient : ℝ)|)
          (abs_nonneg _) else 0) := by
    by_cases hcop : Nat.Coprime c q
    · simp only [if_pos hcop]
      have hphi : (q.totient : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.totient_pos.mpr hq).ne'
      have hlin : Measurable (fun x : ℝ => x / (q.totient : ℝ)) :=
        measurable_id.div_const _
      exact ((hpref c).sub hlin).abs.subtype_mk (h := fun _ => abs_nonneg _)
    · simp [hcop]
  have hs (s : Finset ℕ) : Measurable (fun x : ℝ => s.sup (fun c =>
      if Nat.Coprime c q then
        NNReal.mk
          (|OAI.LargePrimeGaps.residuePrefix ArithmeticFunction.vonMangoldt
              ⌊x⌋₊ q c - x / (q.totient : ℝ)|)
          (abs_nonneg _) else 0)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert c s hc ih =>
      simp only [Finset.sup_insert, hc]
      exact (hterm c).sup ih
  unfold OAI.LargePrimeGaps.endpointError
  exact NNReal.continuous_coe.measurable.comp (hs (Finset.range q))

lemma vonMangoldt_sub_primeLog_nonneg (n : ℕ) :
    0 ≤ ArithmeticFunction.vonMangoldt n -
      (if n.Prime then Real.log n else 0) := by
  by_cases hp : n.Prime
  · rw [if_pos hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
    norm_num
  · simp [hp, ArithmeticFunction.vonMangoldt_nonneg]

lemma chebyshev_psi_sub_theta_eq_sum (x : ℝ) :
    Chebyshev.psi x - Chebyshev.theta x =
      ∑ n ∈ Finset.Icc 0 ⌊x⌋₊,
        (ArithmeticFunction.vonMangoldt n -
          (if n.Prime then Real.log n else 0)) := by
  rw [Chebyshev.psi_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
  rw [← Finset.sum_sub_distrib]

lemma primeClassPsi_sub_theta_eq_sum (x : ℝ) {q c : ℕ} (hq : 0 < q) (hc : c < q) :
    primeClassPsi x q c - primeClassTheta x q c =
      ∑ n ∈ Finset.Icc 0 ⌊x⌋₊,
        if (n : ZMod q) = (c : ZMod q) then
          ArithmeticFunction.vonMangoldt n -
            (if n.Prime then Real.log n else 0) else 0 := by
  rw [primeClassPsi_eq_sum hq hc, primeClassTheta]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hr : (n : ZMod q) = (c : ZMod q)
  · by_cases hp : n.Prime
    · simp [primeClassWeight, hr, hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
    · simp [primeClassWeight, hr, hp]
  · simp [primeClassWeight, hr]

lemma primeClassPsi_sub_theta_bounds (x : ℝ) {q c : ℕ} (hq : 0 < q) (hc : c < q) :
    0 ≤ primeClassPsi x q c - primeClassTheta x q c ∧
      primeClassPsi x q c - primeClassTheta x q c ≤
        Chebyshev.psi x - Chebyshev.theta x := by
  rw [primeClassPsi_sub_theta_eq_sum x hq hc, chebyshev_psi_sub_theta_eq_sum]
  constructor
  · apply Finset.sum_nonneg
    intro n hn
    by_cases hr : (n : ZMod q) = (c : ZMod q)
    · simpa only [if_pos hr] using vonMangoldt_sub_primeLog_nonneg n
    · simp only [if_neg hr]
      norm_num
  · apply Finset.sum_le_sum
    intro n hn
    by_cases hr : (n : ZMod q) = (c : ZMod q)
    · simp only [if_pos hr]
      exact le_rfl
    · simpa only [if_neg hr] using vonMangoldt_sub_primeLog_nonneg n

lemma primeClassTheta_error_le (x : ℝ) {q c : ℕ} (hq : 0 < q) (hc : c < q)
    (hcop : Nat.Coprime c q) (C : ℝ)
    (hC : ∀ x : ℝ, Chebyshev.psi x - Chebyshev.theta x ≤ C * Real.sqrt x) :
    |primeClassTheta x q c - x / (q.totient : ℝ)| ≤
      (OAI.LargePrimeGaps.endpointError x q : ℝ) +
        (|C| + 1) * Real.sqrt x := by
  have hψ := endpointClassError_le_real x hc hcop
  have hδ := primeClassPsi_sub_theta_bounds x hq hc
  have hδ' : primeClassPsi x q c - primeClassTheta x q c ≤
      (|C| + 1) * Real.sqrt x := by
    calc
      _ ≤ C * Real.sqrt x := (hδ.2).trans (hC x)
      _ ≤ (|C| + 1) * Real.sqrt x := by
        have hs : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
        nlinarith [le_abs_self C]
  have hdecomp : primeClassTheta x q c - x / (q.totient : ℝ) =
      (primeClassPsi x q c - x / (q.totient : ℝ)) -
        (primeClassPsi x q c - primeClassTheta x q c) := by ring
  calc
    _ = |(primeClassPsi x q c - x / (q.totient : ℝ)) -
          (primeClassPsi x q c - primeClassTheta x q c)| := by rw [hdecomp]
    _ ≤ |primeClassPsi x q c - x / (q.totient : ℝ)| +
          |primeClassPsi x q c - primeClassTheta x q c| := abs_sub _ _
    _ ≤ (OAI.LargePrimeGaps.endpointError x q : ℝ) +
          (|C| + 1) * Real.sqrt x := by
      rw [abs_of_nonneg hδ.1]
      exact add_le_add hψ hδ'

lemma integrable_endpointError_kernel {y : ℝ} (hy : 2 ≤ y) (q : ℕ) (hq : 0 < q) :
    IntegrableOn (fun t : ℝ =>
      (OAI.LargePrimeGaps.endpointError t q : ℝ) / (t * Real.log t ^ 2))
      (Set.Icc 2 y) := by
  have hE : Measurable (fun t : ℝ =>
      (OAI.LargePrimeGaps.endpointError t q : ℝ)) := measurable_endpointError hq
  have hden : Measurable (fun t : ℝ => t * Real.log t ^ 2) := by fun_prop
  have hf : Measurable (fun t : ℝ =>
      (OAI.LargePrimeGaps.endpointError t q : ℝ) / (t * Real.log t ^ 2)) := hE.div hden
  let K : ℝ := (Real.log 4 + 5) * y / (2 * (Real.log 2) ^ 2)
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  refine IntegrableOn.of_bound (μ := volume) (s := Set.Icc 2 y) ?_
    hf.aestronglyMeasurable K ?_
  · exact isCompact_Icc.measure_lt_top
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have ht2 : 2 ≤ t := ht.1
    have hty : t ≤ y := ht.2
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog : Real.log 2 ≤ Real.log t :=
      Real.log_le_log (by norm_num) ht2
    have hlogtpos : 0 < Real.log t := lt_of_lt_of_le hlog2 hlog
    have hsq : (Real.log 2) ^ 2 ≤ (Real.log t) ^ 2 := by
      have hsum : 0 ≤ Real.log t + Real.log 2 := by linarith
      nlinarith [mul_nonneg (sub_nonneg.mpr hlog) hsum]
    have hden : 0 < t * Real.log t ^ 2 :=
      mul_pos (by linarith) (sq_pos_of_pos hlogtpos)
    have hdenLower : 2 * (Real.log 2) ^ 2 ≤ t * Real.log t ^ 2 := by
      calc
        2 * (Real.log 2) ^ 2 ≤ 2 * (Real.log t) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (by norm_num)
        _ ≤ t * (Real.log t) ^ 2 := by
          have htminus : 0 ≤ t - 2 := by linarith
          nlinarith [mul_nonneg htminus (sq_nonneg (Real.log t))]
    have hEbound := endpointError_le_linear ht2 hq
    have hEpos : 0 ≤ (OAI.LargePrimeGaps.endpointError t q : ℝ) := by positivity
    have hEnum : |(OAI.LargePrimeGaps.endpointError t q : ℝ)| ≤
        (Real.log 4 + 5) * y := by
      rw [abs_of_nonneg hEpos]
      calc
        _ ≤ (Real.log 4 + 5) * t := hEbound
        _ ≤ (Real.log 4 + 5) * y := by gcongr
    have hratio :
        |(OAI.LargePrimeGaps.endpointError t q : ℝ) /
            (t * Real.log t ^ 2)| ≤ K := by
      rw [abs_div, abs_of_pos hden]
      change _ ≤ (Real.log 4 + 5) * y / (2 * (Real.log 2) ^ 2)
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      calc
        _ ≤ (Real.log 4 + 5) * y * (2 * (Real.log 2) ^ 2) :=
          mul_le_mul_of_nonneg_right hEnum (by positivity)
        _ ≤ (Real.log 4 + 5) * y * (t * Real.log t ^ 2) :=
          mul_le_mul_of_nonneg_left hdenLower (by positivity)
    simpa only [Real.norm_eq_abs] using hratio

noncomputable def logIntegralFromTwo (y : ℝ) : ℝ :=
  ∫ t in (2 : ℝ)..y, 1 / Real.log t

theorem li_parts_identity {y : ℝ} (hy : 2 ≤ y) :
    y / Real.log y + ∫ t in (2 : ℝ)..y, 1 / Real.log t ^ 2 =
      logIntegralFromTwo y + 2 / Real.log 2 := by
  let F : ℝ → ℝ := fun t => t / Real.log t
  let F' : ℝ → ℝ := fun t => 1 / Real.log t - 1 / Real.log t ^ 2
  have hderiv : ∀ t ∈ Set.uIcc (2 : ℝ) y, HasDerivAt F (F' t) t := by
    intro t ht
    have ht' : t ∈ Set.Icc (2 : ℝ) y := by simpa [Set.uIcc_of_le hy] using ht
    have ht2 : 2 ≤ t := ht'.1
    have ht0 : t ≠ 0 := by linarith
    have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
    have h := (hasDerivAt_id t).div (Real.hasDerivAt_log ht0) hlog
    change HasDerivAt (fun t => t / Real.log t) _ t at h
    change HasDerivAt (fun t => t / Real.log t)
      (1 / Real.log t - 1 / Real.log t ^ 2) t
    convert h using 1 <;> field_simp [hlog, ht0] <;> simp only [id_eq] <;> ring
  have h1 : IntervalIntegrable (fun t : ℝ => 1 / Real.log t) volume 2 y := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hy]
    refine ContinuousOn.integrableOn_Icc fun t ht => ?_
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith [ht.1]))
    fun_prop
  have h2 : IntervalIntegrable (fun t : ℝ => 1 / Real.log t ^ 2) volume 2 y := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hy]
    refine ContinuousOn.integrableOn_Icc fun t ht => ?_
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith [ht.1]))
    have hlog2 : Real.log t ^ 2 ≠ 0 := pow_ne_zero 2 hlog
    have hlogsq : ContinuousWithinAt (fun u : ℝ => Real.log u ^ 2)
        (Set.Icc 2 y) t := by fun_prop
    exact (continuousWithinAt_const (b := (1 : ℝ))).div hlogsq hlog2
  have hFint : IntervalIntegrable F' volume 2 y := by
    simpa [F'] using h1.sub h2
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (2 : ℝ)) (b := y) hderiv hFint
  have hFendpoint : F y - F 2 = y / Real.log y - 2 / Real.log 2 := by
    rfl
  rw [hFendpoint, intervalIntegral.integral_sub h1 h2] at hFTC
  dsimp [logIntegralFromTwo]
  nlinarith [hFTC]

lemma intervalIntegrable_primeClassTheta_kernel {y : ℝ} (hy : 2 ≤ y) (q c : ℕ) :
    IntervalIntegrable
      (fun t : ℝ => primeClassTheta t q c / (t * Real.log t ^ 2)) volume 2 y := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hy]
  have hkernel : IntegrableOn (fun t : ℝ => 1 / (t * Real.log t ^ 2))
      (Set.Icc 2 y) := by
    refine ContinuousOn.integrableOn_Icc fun t ht => ?_
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith [ht.1]))
    have hlog2 : Real.log t ^ 2 ≠ 0 := pow_ne_zero 2 hlog
    have hden : t * Real.log t ^ 2 ≠ 0 := mul_ne_zero ht0 hlog2
    have hdenCont : ContinuousWithinAt (fun u : ℝ => u * Real.log u ^ 2)
        (Set.Icc 2 y) t := by fun_prop
    exact (continuousWithinAt_const (b := (1 : ℝ))).div hdenCont hden
  have hmul := integrableOn_mul_sum_Icc (c := primeClassWeight q c) (m := 0)
    (a := (2 : ℝ)) (b := y) (by norm_num) hkernel
  simpa [primeClassTheta, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul

theorem primeClassCount_eq_theta_formula {x : ℝ} (hx : 2 ≤ x) (q c : ℕ) :
    (primeClassCount x q c : ℝ) =
      primeClassTheta x q c / Real.log x +
        ∫ t in (2 : ℝ)..x, primeClassTheta t q c / (t * Real.log t ^ 2) := by
  let a : ℕ → ℝ := primeClassWeight q c
  let f : ℝ → ℝ := fun t => (Real.log t)⁻¹
  have ha0 : a 0 = 0 := by simp [a, primeClassWeight]
  have ha1 : a 1 = 0 := by simp [a, primeClassWeight]
  have hsum : (primeClassCount x q c : ℝ) =
      ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, f n * a n := by
    have hset :
        (primesUpTo x).filter (fun n : ℕ => (n : ZMod q) = (c : ZMod q)) =
          (Finset.Icc 0 ⌊x⌋₊ : Finset ℕ).filter
            (fun n : ℕ => n.Prime ∧ (n : ZMod q) = (c : ZMod q)) := by
      ext n
      simp [primesUpTo, and_assoc]
    unfold primeClassCount
    rw [hset, Finset.card_eq_sum_ones, Finset.sum_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hp : n.Prime ∧ (n : ZMod q) = (c : ZMod q)
    · have hlog : Real.log (n : ℝ) ≠ 0 := by
        apply Real.log_ne_zero_of_pos_of_ne_one
        · exact_mod_cast hp.1.pos
        · exact_mod_cast hp.1.ne_one
      simp [a, f, primeClassWeight, hp, hlog]
    · simp [a, f, primeClassWeight, hp]
  have habel := sum_mul_eq_sub_integral_mul₁ a ha0 ha1 x
    (f := f) (by
      intro z hz
      have hz0 : z ≠ 0 := by linarith [hz.1]
      have hzlog : Real.log z ≠ 0 := by
        exact ne_of_gt (Real.log_pos (by linarith [hz.1]))
      change DifferentiableAt ℝ (fun t => (Real.log t)⁻¹) z
      exact (Real.differentiableAt_log hz0).inv hzlog)
    (by
      refine ContinuousOn.integrableOn_Icc fun z hz => ?_
      refine ContinuousWithinAt.congr ?_
        (fun _ _ => Real.deriv_inv_log_apply) Real.deriv_inv_log_apply
      have hz0 : z ≠ 0 := by linarith [hz.1]
      have hzlog0 : Real.log z ≠ 0 := by
        exact Real.log_ne_zero_of_pos_of_ne_one (by linarith [hz.1]) (by linarith [hz.1])
      have hzlog : Real.log z ^ 2 ≠ 0 := by
        exact pow_ne_zero 2 hzlog0
      exact ContinuousAt.continuousWithinAt <| by fun_prop)
  have habel' :
      (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, f n * a n) =
        f x * primeClassTheta x q c -
          ∫ t in Set.Ioc (2 : ℝ) x, deriv f t * primeClassTheta t q c := by
    simpa [primeClassTheta, a] using habel
  have hderiv {t : ℝ} (ht : t ∈ Set.Icc (2 : ℝ) x) :
      deriv f t * primeClassTheta t q c =
        -primeClassTheta t q c / (t * Real.log t ^ 2) := by
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have htlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith [ht.1]))
    simp only [f, Real.deriv_inv_log_apply]
    field_simp [ht0, htlog]
  have hinter :
      (∫ t in (2 : ℝ)..x, deriv f t * primeClassTheta t q c) =
        -(∫ t in (2 : ℝ)..x,
          primeClassTheta t q c / (t * Real.log t ^ 2)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    simpa only [neg_div] using hderiv (by simpa [Set.uIcc_of_le hx] using ht)
  have habel'' :
      (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, f n * a n) =
        f x * primeClassTheta x q c +
          ∫ t in (2 : ℝ)..x, primeClassTheta t q c / (t * Real.log t ^ 2) := by
    calc
      _ = f x * primeClassTheta x q c -
          ∫ t in Set.Ioc (2 : ℝ) x, deriv f t * primeClassTheta t q c := habel'
      _ = f x * primeClassTheta x q c -
          ∫ t in (2 : ℝ)..x, deriv f t * primeClassTheta t q c := by
        rw [← intervalIntegral.integral_of_le hx]
      _ = _ := by rw [hinter]; ring
  rw [hsum, habel'']
  simp [f, div_eq_mul_inv, mul_comm]

theorem primeClassCount_li_error_eq {y : ℝ} (hy : 2 ≤ y) {q c : ℕ} (hq : 0 < q) :
    (primeClassCount y q c : ℝ) - logIntegralFromTwo y / (q.totient : ℝ) =
      (primeClassTheta y q c - y / (q.totient : ℝ)) / Real.log y +
        (∫ t in (2 : ℝ)..y,
          (primeClassTheta t q c - t / (q.totient : ℝ)) /
            (t * Real.log t ^ 2)) +
        (2 / Real.log 2) / (q.totient : ℝ) := by
  have hphi : (q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hq).ne'
  have hlogy : Real.log y ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
  have hthetaInt := intervalIntegrable_primeClassTheta_kernel hy q c
  have hsqInt : IntervalIntegrable (fun t : ℝ => 1 / Real.log t ^ 2) volume 2 y := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hy]
    refine ContinuousOn.integrableOn_Icc fun t ht => ?_
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith [ht.1]))
    have hlog2 : Real.log t ^ 2 ≠ 0 := pow_ne_zero 2 hlog
    have hlogsq : ContinuousWithinAt (fun u : ℝ => Real.log u ^ 2)
        (Set.Icc 2 y) t := by fun_prop
    exact (continuousWithinAt_const (b := (1 : ℝ))).div hlogsq hlog2
  let mKernel : ℝ → ℝ := fun t => (1 / (q.totient : ℝ)) * (1 / Real.log t ^ 2)
  have hmInt : IntervalIntegrable mKernel volume 2 y := by
    simpa [mKernel] using hsqInt.const_mul (1 / (q.totient : ℝ))
  have hmainKernelEq {t : ℝ} (ht : t ∈ Set.uIcc (2 : ℝ) y) :
      (t / (q.totient : ℝ)) / (t * Real.log t ^ 2) = mKernel t := by
    have htIcc : t ∈ Set.Icc (2 : ℝ) y := by simpa [Set.uIcc_of_le hy] using ht
    have ht0 : t ≠ 0 := by linarith [htIcc.1]
    have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith [htIcc.1]))
    dsimp [mKernel]
    field_simp [hphi, ht0, hlog]
  have hsub :
      (∫ t in (2 : ℝ)..y, primeClassTheta t q c / (t * Real.log t ^ 2)) -
        (∫ t in (2 : ℝ)..y, mKernel t) =
          ∫ t in (2 : ℝ)..y,
            (primeClassTheta t q c - t / (q.totient : ℝ)) /
              (t * Real.log t ^ 2) := by
    rw [← intervalIntegral.integral_sub hthetaInt hmInt]
    apply intervalIntegral.integral_congr
    intro t ht
    have htIcc : t ∈ Set.Icc (2 : ℝ) y := by simpa [Set.uIcc_of_le hy] using ht
    have ht0 : t ≠ 0 := by linarith [htIcc.1]
    have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith [htIcc.1]))
    change primeClassTheta t q c / (t * Real.log t ^ 2) - mKernel t =
      (primeClassTheta t q c - t / (q.totient : ℝ)) /
        (t * Real.log t ^ 2)
    rw [← hmainKernelEq ht]
    field_simp [hphi, ht0, hlog]
  have hmainInt :
      (∫ t in (2 : ℝ)..y, mKernel t) =
        (1 / (q.totient : ℝ)) * (∫ t in (2 : ℝ)..y, 1 / Real.log t ^ 2) := by
    simp [mKernel, intervalIntegral.integral_const_mul]
  have hpartsDiv :
      (y / Real.log y) / (q.totient : ℝ) +
          ∫ t in (2 : ℝ)..y, mKernel t =
        logIntegralFromTwo y / (q.totient : ℝ) +
          (2 / Real.log 2) / (q.totient : ℝ) := by
    have h := congrArg (fun z : ℝ => z / (q.totient : ℝ)) (li_parts_identity hy)
    rw [hmainInt]
    convert h using 1 <;> field_simp [hphi] <;> ring
  have hratio :
      (primeClassTheta y q c - y / (q.totient : ℝ)) / Real.log y =
        primeClassTheta y q c / Real.log y -
          (y / Real.log y) / (q.totient : ℝ) := by
    field_simp [hphi, hlogy]
  rw [primeClassCount_eq_theta_formula hy q c]
  have hAD : primeClassTheta y q c / Real.log y =
      (primeClassTheta y q c - y / (q.totient : ℝ)) / Real.log y +
        (y / Real.log y) / (q.totient : ℝ) := by
    linarith [hratio]
  have hBD :
      (∫ t in (2 : ℝ)..y, primeClassTheta t q c / (t * Real.log t ^ 2)) =
        (∫ t in (2 : ℝ)..y,
          (primeClassTheta t q c - t / (q.totient : ℝ)) /
            (t * Real.log t ^ 2)) + (∫ t in (2 : ℝ)..y, mKernel t) := by
    linarith [hsub]
  have hconst :
      (y / Real.log y) / (q.totient : ℝ) +
        (∫ t in (2 : ℝ)..y, mKernel t) -
          logIntegralFromTwo y / (q.totient : ℝ) =
        (2 / Real.log 2) / (q.totient : ℝ) := by
    linarith [hpartsDiv]
  calc
    _ = (primeClassTheta y q c - y / (q.totient : ℝ)) / Real.log y +
          (∫ t in (2 : ℝ)..y,
            (primeClassTheta t q c - t / (q.totient : ℝ)) /
              (t * Real.log t ^ 2)) +
          ((y / Real.log y) / (q.totient : ℝ) +
            (∫ t in (2 : ℝ)..y, mKernel t) -
              logIntegralFromTwo y / (q.totient : ℝ)) := by
      rw [hAD, hBD]
      ring
    _ = _ := by
      let A : ℝ :=
        (primeClassTheta y q c - y / (q.totient : ℝ)) / Real.log y +
          ∫ t in (2 : ℝ)..y,
            (primeClassTheta t q c - t / (q.totient : ℝ)) /
              (t * Real.log t ^ 2)
      calc
        _ = A + ((y / Real.log y) / (q.totient : ℝ) +
            (∫ t in (2 : ℝ)..y, mKernel t) -
              logIntegralFromTwo y / (q.totient : ℝ)) := by rfl
        _ = A + (2 / Real.log 2) / (q.totient : ℝ) :=
          congrArg (fun z : ℝ => A + z) hconst
        _ = _ := by dsimp [A]

lemma totient_reciprocal_le_divisorCount (q : ℕ) (hq : 0 < q) :
    (1 : ℝ) / (q.totient : ℝ) ≤ (Nat.divisors q).card / (q : ℝ) := by
  let P := ∏ p ∈ q.primeFactors, p
  let R := ∏ p ∈ q.primeFactors, (p - 1)
  have htwo : 2 ^ q.primeFactors.card ≤ (Nat.divisors q).card := by
    rw [Nat.card_divisors hq.ne']
    calc
      _ = ∏ p ∈ q.primeFactors, 2 := by simp
      _ ≤ ∏ p ∈ q.primeFactors, (q.factorization p + 1) := by
        apply Finset.prod_le_prod
        intro p hp
        have hp0 := (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd
          hq.ne' (Nat.dvd_of_mem_primeFactors hp)
        omega
  have hprod : P ≤ (Nat.divisors q).card * R := by
    dsimp [P, R]
    calc
      _ ≤ ∏ p ∈ q.primeFactors, 2 * (p - 1) := by
        apply Finset.prod_le_prod
        intro p hp
        have hp' := (Nat.prime_of_mem_primeFactors hp).two_le
        omega
      _ = (∏ p ∈ q.primeFactors, 2) * ∏ p ∈ q.primeFactors, (p - 1) := by
        rw [Finset.prod_mul_distrib]
      _ = 2 ^ q.primeFactors.card * ∏ p ∈ q.primeFactors, (p - 1) := by simp
      _ ≤ (Nat.divisors q).card * ∏ p ∈ q.primeFactors, (p - 1) := by
        gcongr
  have hRpos : 0 < R := by
    dsimp [R]
    exact Finset.prod_pos fun p hp => Nat.sub_pos_of_lt
      (Nat.prime_of_mem_primeFactors hp).one_lt
  have htot := Nat.totient_mul_prod_primeFactors q
  have hmul : q * R ≤ q.totient * (Nat.divisors q).card * R := by
    calc
      _ = q.totient * P := htot.symm
      _ ≤ q.totient * ((Nat.divisors q).card * R) := Nat.mul_le_mul_left _ hprod
      _ = _ := by ring
  have hnat : q ≤ q.totient * (Nat.divisors q).card :=
    Nat.le_of_mul_le_mul_right hmul hRpos
  apply (div_le_div_iff₀ (by exact_mod_cast Nat.totient_pos.mpr hq)
    (by exact_mod_cast hq)).2
  norm_num
  exact_mod_cast (by simpa [Nat.mul_comm] using hnat)

lemma divisorCount_div_eq_antidiagonal (q : ℕ) (hq : 0 < q) :
    (Nat.divisors q).card / (q : ℝ) =
      ∑ p ∈ q.divisorsAntidiagonal, (1 : ℝ) / (p.1 * p.2) := by
  have hcard : (Nat.divisors q).card = q.divisorsAntidiagonal.card := by
    rw [← Nat.map_div_right_divisors]
    simp
  rw [hcard, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' := Nat.mem_divisorsAntidiagonal.mp hp
  rw [← Nat.cast_mul, hp'.1]

lemma sum_reciprocal_totient_le_harmonic_sq (Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, (1 : ℝ) / (q.totient : ℝ)) ≤
      (harmonic Q : ℝ) ^ 2 := by
  let S := Finset.Icc 1 Q
  let s := Finset.Ioc 0 Q ×ˢ Finset.Ioc 0 Q
  let g : ℕ × ℕ → ℕ := fun p => p.1 * p.2
  let f : ℕ × ℕ → ℝ := fun p => (1 : ℝ) / ((p.1 : ℝ) * (p.2 : ℝ))
  have hle (q : ℕ) (hq : q ∈ S) :
      (1 : ℝ) / (q.totient : ℝ) ≤ ∑ p ∈ q.divisorsAntidiagonal, f p := by
    have hqpos : 0 < q := (Finset.mem_Icc.mp hq).1
    rw [← divisorCount_div_eq_antidiagonal q hqpos]
    exact totient_reciprocal_le_divisorCount q hqpos
  have hfiber (q : ℕ) (hq : q ∈ S) :
      (∑ p ∈ q.divisorsAntidiagonal, f p) =
        ∑ p ∈ s with g p = q, f p := by
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hqQ : q ≤ Q := (Finset.mem_Icc.mp hq).2
    have hq0 : q ≠ 0 := by omega
    exact congrArg (fun set => ∑ p ∈ set, f p)
      (Nat.divisorsAntidiagonal_eq_prod_filter_of_le hq0 hqQ)
  have hbound : (∑ q ∈ S, ∑ p ∈ s with g p = q, f p) ≤ ∑ p ∈ s, f p := by
    apply Finset.sum_fiberwise_le_sum_of_sum_fiber_nonneg (s := s) (t := S) (g := g) (f := f)
    intro y hy
    exact Finset.sum_nonneg fun p hp => by positivity
  have hprod :
      (∑ p ∈ s, f p) =
        (∑ a ∈ Finset.Ioc 0 Q, (1 : ℝ) / (a : ℝ)) *
          ∑ b ∈ Finset.Ioc 0 Q, (1 : ℝ) / (b : ℝ) := by
    dsimp [s, f]
    rw [Finset.sum_product]
    have heq (a b : ℕ) : (1 : ℝ) / ((a : ℝ) * (b : ℝ)) = (1 / (a : ℝ)) * (1 / (b : ℝ)) := by
      ring
    simp_rw [heq, ← Finset.mul_sum, ← Finset.sum_mul]
  have hIoc : Finset.Ioc 0 Q = Finset.Icc 1 Q := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have hharm : (∑ a ∈ Finset.Ioc 0 Q, (1 : ℝ) / (a : ℝ)) = (harmonic Q : ℝ) := by
    rw [hIoc, harmonic_eq_sum_Icc]
    push_cast
    simp only [one_div]
  calc
    (∑ q ∈ S, (1 : ℝ) / (q.totient : ℝ)) ≤
        ∑ q ∈ S, ∑ p ∈ q.divisorsAntidiagonal, f p := Finset.sum_le_sum hle
    _ = ∑ q ∈ S, ∑ p ∈ s with g p = q, f p := Finset.sum_congr rfl hfiber
    _ ≤ ∑ p ∈ s, f p := hbound
    _ = (harmonic Q : ℝ) * (harmonic Q : ℝ) := by rw [hprod, hharm]
    _ = (harmonic Q : ℝ) ^ 2 := by ring

lemma logIntegralFromTwo_le {x : ℝ} (hx : 2 ≤ x) :
    logIntegralFromTwo x ≤ x / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hintegrable : IntervalIntegrable (fun t : ℝ => 1 / Real.log t) volume 2 x := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
    refine ContinuousOn.integrableOn_Icc fun t ht => ?_
    have ht2 : 2 ≤ t := ht.1
    have ht0 : t ≠ 0 := by linarith
    have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
    fun_prop
  have hbound : ∀ t ∈ Set.Icc (2 : ℝ) x, 1 / Real.log t ≤ 1 / Real.log 2 := by
    intro t ht
    have ht2 : 2 ≤ t := ht.1
    have hlogt : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht2
    exact one_div_le_one_div_of_le hlog2 hlogt
  have hconst : IntervalIntegrable (fun _ : ℝ => 1 / Real.log 2) volume 2 x :=
    intervalIntegrable_const
  dsimp [logIntegralFromTwo]
  have hle := intervalIntegral.integral_mono_on hx hintegrable hconst hbound
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_mul] at hle
  have heq : x * (1 / Real.log 2) = x / Real.log 2 := by ring
  have hpos2 : 0 ≤ 2 * (1 / Real.log 2) := by positivity
  calc
    (∫ t in (2 : ℝ)..x, 1 / Real.log t) ≤ x * (1 / Real.log 2) - 2 * (1 / Real.log 2) := hle
    _ ≤ x / Real.log 2 := by linarith [heq, hpos2]

lemma primeClassCount_le (x : ℝ) (hx : 2 ≤ x) {q c : ℕ} (hq : 0 < q) (hc : c < q) :
    (primeClassCount x q c : ℝ) ≤ x / (q : ℝ) + 1 := by
  let S := (primesUpTo x).filter fun n : ℕ => (n : ZMod q) = (c : ZMod q)
  let T := (Finset.range (⌊x⌋₊ + 1)).filter fun n : ℕ => (n : ZMod q) = (c : ZMod q)
  have hS_sub : S ⊆ T := by
    intro n hn
    have hmem : n ∈ primesUpTo x ∧ (n : ZMod q) = (c : ZMod q) := Finset.mem_filter.mp hn
    have hrange : n ∈ Finset.range (⌊x⌋₊ + 1) := by
      have hp := hmem.1
      unfold primesUpTo at hp
      exact (Finset.mem_filter.mp hp).1
    exact Finset.mem_filter.mpr ⟨hrange, hmem.2⟩
  have hinj : Set.InjOn (fun n : ℕ => n / q) (T : Set ℕ) := by
    intro n1 hn1 n2 hn2 heq
    dsimp at heq
    have h1 := (Finset.mem_filter.mp hn1).2
    have h2 := (Finset.mem_filter.mp hn2).2
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hc] at h1 h2
    have hdiv1 := Nat.div_add_mod n1 q
    have hdiv2 := Nat.div_add_mod n2 q
    rw [← hdiv1, ← hdiv2, h1, h2, heq]
  have hmaps : ∀ n ∈ T, n / q ∈ Finset.range (⌊x⌋₊ / q + 1) := by
    intro n hn
    have hnrange := (Finset.mem_filter.mp hn).1
    rw [Finset.mem_range] at hnrange ⊢
    have : n ≤ ⌊x⌋₊ := by omega
    have : n / q ≤ ⌊x⌋₊ / q := Nat.div_le_div_right this
    omega
  have hcardT : T.card ≤ (Finset.range (⌊x⌋₊ / q + 1)).card :=
    Finset.card_le_card_of_injOn (fun n => n / q) hmaps hinj
  rw [Finset.card_range] at hcardT
  have hcardS : S.card ≤ ⌊x⌋₊ / q + 1 :=
    (Finset.card_le_card hS_sub).trans hcardT
  unfold primeClassCount
  change (S.card : ℝ) ≤ x / (q : ℝ) + 1
  have hpos : (0 : ℝ) ≤ x := by linarith
  have h1 : ((⌊x⌋₊ / q : ℕ) : ℝ) ≤ (⌊x⌋₊ : ℝ) / (q : ℝ) := Nat.cast_div_le
  have h2 : (⌊x⌋₊ : ℝ) / (q : ℝ) ≤ x / (q : ℝ) :=
    div_le_div_of_nonneg_right (Nat.floor_le hpos) (by positivity)
  have h3 : ((⌊x⌋₊ / q : ℕ) : ℝ) ≤ x / (q : ℝ) := h1.trans h2
  have hcardS_cast : (S.card : ℝ) ≤ ((⌊x⌋₊ / q : ℕ) : ℝ) + 1 := by
    have : (S.card : ℝ) ≤ ((⌊x⌋₊ / q + 1 : ℕ) : ℝ) := by exact_mod_cast hcardS
    have heq : ((⌊x⌋₊ / q + 1 : ℕ) : ℝ) = ((⌊x⌋₊ / q : ℕ) : ℝ) + 1 := by simp
    linarith
  linarith [hcardS_cast, h3]

lemma primeClassTheta_le_log_mul_count (x : ℝ) (hx : 2 ≤ x) {q c : ℕ} :
    primeClassTheta x q c ≤ Real.log x * (primeClassCount x q c : ℝ) := by
  have hlogx_nonneg : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  unfold primeClassTheta primeClassWeight primeClassCount
  have hset :
      (primesUpTo x).filter (fun n : ℕ => (n : ZMod q) = (c : ZMod q)) =
        (Finset.Icc 0 ⌊x⌋₊).filter fun n : ℕ => n.Prime ∧ (n : ZMod q) = (c : ZMod q) := by
    ext n
    simp only [primesUpTo, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc, Nat.lt_succ_iff,
      Nat.zero_le, true_and]
    tauto
  rw [hset, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.mul_sum]
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro n hn
  by_cases hp : n.Prime ∧ (n : ZMod q) = (c : ZMod q)
  · simp only [if_pos hp, mul_one]
    have hnle : (n : ℝ) ≤ x := by
      have := (Finset.mem_Icc.mp hn).2
      exact (Nat.cast_le.mpr this).trans (Nat.floor_le (by linarith))
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hp.1.pos
    have hlog : Real.log (n : ℝ) ≤ Real.log x := Real.log_le_log hnpos hnle
    exact hlog
  · simp [hp]

end ArtinPrimitiveRoots.Ext.Proofs.SWBV
