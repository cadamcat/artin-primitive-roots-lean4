import Mathlib
import ArtinPrimitiveRoots.TypeII.Defs
import OAI.NumberTheory.PrimeGaps.Main

/-! External analytic inputs used by the Type II and construction arguments. -/

namespace ArtinPrimitiveRoots.Ext.TypeIIInputs

open Classical MeasureTheory
open scoped FourierTransform
open ArtinPrimitiveRoots.TypeII

/-- The Meissel–Mertens constant, defined as the limit of the reciprocal-prime sum error. -/
noncomputable def meisselMertensConstant : ℝ :=
  Filter.limUnder Filter.atTop (fun y : ℝ =>
    (∑ p ∈ primesUpTo y, 1 / (p : ℝ)) - Real.log (Real.log y))

/-- Prime-counting function on a real interval, with primes counted by an explicit finite set. -/
noncomputable def primeIntervalCount (y₁ y₂ : ℝ) : ℝ :=
  ((primesUpTo y₂).filter fun p => y₁ < (p : ℝ)).card

/-- `Li(y)` with lower endpoint `2`. -/
noncomputable def logarithmicIntegral (y : ℝ) : ℝ :=
  ∫ t in (2 : ℝ)..y, 1 / Real.log t

/-- Maximum prime progression error, in the `π` form used by §12. Binders typed `ℕ` on 2026-10-07: untyped,
Lean coerced the prime set into `ZMod q` before filtering (lane `c2b`). -/
noncomputable def primeProgressionError (y : ℝ) (q : ℕ) : ℝ :=
  ((Finset.range q).filter (fun v : ℕ => Nat.Coprime v q)).fold max 0 fun v : ℕ =>
    |(((primesUpTo y).filter (fun p : ℕ => ((p : ℕ) : ZMod q) = ((v : ℕ) : ZMod q))).card : ℝ) -
      logarithmicIntegral y / (Nat.totient q : ℝ)|

section SWBVHelpers

open intervalIntegral Finset

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

theorem li_parts_identity {y : ℝ} (hy : 2 ≤ y) :
    y / Real.log y + ∫ t in (2 : ℝ)..y, 1 / Real.log t ^ 2 =
      logarithmicIntegral y + 2 / Real.log 2 := by
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
  dsimp [logarithmicIntegral]
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
    (primeClassCount y q c : ℝ) - logarithmicIntegral y / (q.totient : ℝ) =
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
        logarithmicIntegral y / (q.totient : ℝ) +
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
          logarithmicIntegral y / (q.totient : ℝ) =
        (2 / Real.log 2) / (q.totient : ℝ) := by
    linarith [hpartsDiv]
  calc
    _ = (primeClassTheta y q c - y / (q.totient : ℝ)) / Real.log y +
          (∫ t in (2 : ℝ)..y,
            (primeClassTheta t q c - t / (q.totient : ℝ)) /
              (t * Real.log t ^ 2)) +
          ((y / Real.log y) / (q.totient : ℝ) +
            (∫ t in (2 : ℝ)..y, mKernel t) -
              logarithmicIntegral y / (q.totient : ℝ)) := by
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
              logarithmicIntegral y / (q.totient : ℝ)) := by rfl
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

lemma logarithmicIntegral_le {x : ℝ} (hx : 2 ≤ x) :
    logarithmicIntegral x ≤ x / Real.log 2 := by
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
  dsimp [logarithmicIntegral]
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



lemma primeProgressionError_eq_zero_of_q_eq_zero (y : ℝ) :
    primeProgressionError y 0 = 0 := by
  dsimp [primeProgressionError]
  simp

lemma fold_max_le {α : Type*} (s : Finset α) (f : α → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hf : ∀ x ∈ s, f x ≤ B) :
    s.fold max 0 f ≤ B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hB]
  | insert a s has ih =>
    rw [Finset.fold_insert has]
    have hfa := hf a (Finset.mem_insert_self a s)
    have hih := ih (fun x hx => hf x (Finset.mem_insert_of_mem hx))
    exact max_le hfa hih

lemma primeProgressionError_le_of_forall (y : ℝ) (q : ℕ) (B : ℝ)
    (hB : 0 ≤ B)
    (hf : ∀ v < q, Nat.Coprime v q →
      |(primeClassCount y q v : ℝ) - logarithmicIntegral y / (q.totient : ℝ)| ≤ B) :
    primeProgressionError y q ≤ B := by
  by_cases hq : q = 0
  · subst hq
    rw [primeProgressionError_eq_zero_of_q_eq_zero]
    exact hB
  · unfold primeProgressionError
    apply fold_max_le _ _ B hB
    intro v hv
    rw [Finset.mem_filter, Finset.mem_range] at hv
    exact hf v hv.1 hv.2

lemma sum_range_primeProgressionError_eq_sum_Icc (y : ℝ) (Q : ℕ) :
    (∑ q ∈ Finset.range (Q + 1), primeProgressionError y q) =
      ∑ q ∈ Finset.Icc 1 Q, primeProgressionError y q := by
  have hrange : Finset.range (Q + 1) = insert 0 (Finset.Icc 1 Q) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have h0 : 0 ∉ Finset.Icc 1 Q := by simp
  rw [hrange, Finset.sum_insert h0, primeProgressionError_eq_zero_of_q_eq_zero, zero_add]

lemma integral_one_div_log_sq_le {t₀ : ℝ} (ht₀ : 2 ≤ t₀) :
    (∫ t in (2 : ℝ)..t₀, 1 / Real.log t ^ 2) ≤ t₀ / (Real.log 2) ^ 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsq2 : 0 < Real.log 2 ^ 2 := sq_pos_of_pos hlog2
  have hintegrable : IntervalIntegrable (fun t : ℝ => 1 / Real.log t ^ 2) volume 2 t₀ := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht₀]
    refine ContinuousOn.integrableOn_Icc fun t ht => ?_
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith [ht.1]))
    have hlogsq : ContinuousWithinAt (fun u : ℝ => Real.log u ^ 2) (Set.Icc 2 t₀) t := by fun_prop
    exact (continuousWithinAt_const (b := (1 : ℝ))).div hlogsq (pow_ne_zero 2 hlog)
  have hconst : IntervalIntegrable (fun _ : ℝ => 1 / (Real.log 2) ^ 2) volume 2 t₀ :=
    intervalIntegrable_const
  have hbound : ∀ t ∈ Set.Icc (2 : ℝ) t₀, 1 / Real.log t ^ 2 ≤ 1 / (Real.log 2) ^ 2 := by
    intro t ht
    have ht2 : 2 ≤ t := ht.1
    have hlogt : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht2
    have hsq : Real.log 2 ^ 2 ≤ Real.log t ^ 2 := by
      have : 0 ≤ Real.log 2 + Real.log t := by linarith
      nlinarith [sub_nonneg.mpr hlogt]
    exact one_div_le_one_div_of_le hsq2 hsq
  have hle := intervalIntegral.integral_mono_on ht₀ hintegrable hconst hbound
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_mul] at hle
  have heq : t₀ * (1 / (Real.log 2) ^ 2) = t₀ / (Real.log 2) ^ 2 := by ring
  have hpos2 : 0 ≤ 2 * (1 / (Real.log 2) ^ 2) := by positivity
  calc
    (∫ t in (2 : ℝ)..t₀, 1 / Real.log t ^ 2) ≤ t₀ * (1 / (Real.log 2) ^ 2) - 2 * (1 / (Real.log 2) ^ 2) := hle
    _ ≤ t₀ / (Real.log 2) ^ 2 := by linarith [heq, hpos2]

lemma integral_theta_sub_linear_le_on_low {t₀ : ℝ} (ht₀2 : 2 ≤ t₀) {q c : ℕ} (hq : 0 < q) (hc : c < q) :
    |(∫ t in (2 : ℝ)..t₀,
        (primeClassTheta t q c - t / (q.totient : ℝ)) / (t * Real.log t ^ 2))| ≤
      t₀ / (q : ℝ) + 1 + (t₀ / (Real.log 2) ^ 2) / (q.totient : ℝ) := by
  have hphi : (q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hq).ne'
  have hthetaInt := intervalIntegrable_primeClassTheta_kernel ht₀2 q c
  have hsqInt : IntervalIntegrable (fun t : ℝ => 1 / Real.log t ^ 2) volume 2 t₀ := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht₀2]
    refine ContinuousOn.integrableOn_Icc fun t ht => ?_
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith [ht.1]))
    have hlogsq : ContinuousWithinAt (fun u : ℝ => Real.log u ^ 2) (Set.Icc 2 t₀) t := by fun_prop
    exact (continuousWithinAt_const (b := (1 : ℝ))).div hlogsq (pow_ne_zero 2 hlog)
  let mKernel : ℝ → ℝ := fun t => (1 / (q.totient : ℝ)) * (1 / Real.log t ^ 2)
  have hmInt : IntervalIntegrable mKernel volume 2 t₀ := by
    simpa [mKernel] using hsqInt.const_mul (1 / (q.totient : ℝ))
  have hmainKernelEq {t : ℝ} (ht : t ∈ Set.uIcc (2 : ℝ) t₀) :
      (t / (q.totient : ℝ)) / (t * Real.log t ^ 2) = mKernel t := by
    have htIcc : t ∈ Set.Icc (2 : ℝ) t₀ := by simpa [Set.uIcc_of_le ht₀2] using ht
    have ht0 : t ≠ 0 := by linarith [htIcc.1]
    have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith [htIcc.1]))
    dsimp [mKernel]
    field_simp [hphi, ht0, hlog]
  have hsub :
      (∫ t in (2 : ℝ)..t₀, primeClassTheta t q c / (t * Real.log t ^ 2)) -
        (∫ t in (2 : ℝ)..t₀, mKernel t) =
          ∫ t in (2 : ℝ)..t₀,
            (primeClassTheta t q c - t / (q.totient : ℝ)) /
              (t * Real.log t ^ 2) := by
    rw [← intervalIntegral.integral_sub hthetaInt hmInt]
    apply intervalIntegral.integral_congr
    intro t ht
    have htIcc : t ∈ Set.Icc (2 : ℝ) t₀ := by simpa [Set.uIcc_of_le ht₀2] using ht
    have ht0 : t ≠ 0 := by linarith [htIcc.1]
    have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith [htIcc.1]))
    change primeClassTheta t q c / (t * Real.log t ^ 2) - mKernel t =
      (primeClassTheta t q c - t / (q.totient : ℝ)) /
        (t * Real.log t ^ 2)
    rw [← hmainKernelEq ht]
    field_simp [hphi, ht0, hlog]
  have hformula := primeClassCount_eq_theta_formula ht₀2 q c
  have htheta_pos : 0 ≤ primeClassTheta t₀ q c / Real.log t₀ := by
    have h1 : 0 ≤ primeClassTheta t₀ q c := Finset.sum_nonneg fun n _ => by
      dsimp [primeClassWeight]
      split_ifs <;> positivity
    have h2 : 0 < Real.log t₀ := Real.log_pos (by linarith)
    positivity
  have hcount_le := primeClassCount_le t₀ ht₀2 hq hc
  have htheta_int_nonneg : 0 ≤ ∫ t in (2 : ℝ)..t₀, primeClassTheta t q c / (t * Real.log t ^ 2) := by
    apply intervalIntegral.integral_nonneg ht₀2
    intro t ht
    have h1 : 0 ≤ primeClassTheta t q c := Finset.sum_nonneg fun n _ => by
      dsimp [primeClassWeight]
      split_ifs <;> positivity
    have ht0 : 0 < t := by linarith [ht.1]
    have hlog : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    positivity
  have htheta_int_le : (∫ t in (2 : ℝ)..t₀, primeClassTheta t q c / (t * Real.log t ^ 2)) ≤
      t₀ / (q : ℝ) + 1 := by
    calc
      _ ≤ (primeClassCount t₀ q c : ℝ) := by linarith [hformula, htheta_pos]
      _ ≤ t₀ / (q : ℝ) + 1 := hcount_le
  have hmInt_eq : (∫ t in (2 : ℝ)..t₀, mKernel t) =
      (1 / (q.totient : ℝ)) * (∫ t in (2 : ℝ)..t₀, 1 / Real.log t ^ 2) := by
    simp [mKernel, intervalIntegral.integral_const_mul]
  have hmInt_nonneg : 0 ≤ ∫ t in (2 : ℝ)..t₀, mKernel t := by
    rw [hmInt_eq]
    have h1 : 0 ≤ (1 : ℝ) / (q.totient : ℝ) := by positivity
    have h2 : 0 ≤ ∫ t in (2 : ℝ)..t₀, 1 / Real.log t ^ 2 := by
      apply intervalIntegral.integral_nonneg ht₀2
      intro t ht
      have hlog : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
      positivity
    positivity
  have hmInt_le : (∫ t in (2 : ℝ)..t₀, mKernel t) ≤
      (t₀ / (Real.log 2) ^ 2) / (q.totient : ℝ) := by
    rw [hmInt_eq]
    have h1 : 0 ≤ (1 : ℝ) / (q.totient : ℝ) := by positivity
    have h2 := integral_one_div_log_sq_le ht₀2
    have h3 := mul_le_mul_of_nonneg_left h2 h1
    calc
      (1 / (q.totient : ℝ)) * (∫ t in (2 : ℝ)..t₀, 1 / Real.log t ^ 2) ≤
        (1 / (q.totient : ℝ)) * (t₀ / (Real.log 2) ^ 2) := h3
      _ = (t₀ / (Real.log 2) ^ 2) / (q.totient : ℝ) := by ring
  rw [← hsub, abs_le]
  constructor
  · linarith
  · linarith

lemma intervalIntegrable_upper_kernel {y : ℝ} (hy : 2 ≤ y) {t₀ : ℝ} (ht₀2 : 2 ≤ t₀) (ht₀y : t₀ ≤ y)
    (q : ℕ) (hq : 0 < q) (C : ℝ) :
    IntervalIntegrable (fun t : ℝ =>
      (OAI.LargePrimeGaps.endpointError t q + (|C| + 1) * Real.sqrt t) / (t * Real.log t ^ 2))
      volume t₀ y := by
  have hsub : Set.Icc t₀ y ⊆ Set.Icc 2 y := Set.Icc_subset_Icc ht₀2 le_rfl
  have hg1_int : IntegrableOn (fun t : ℝ =>
      (OAI.LargePrimeGaps.endpointError t q : ℝ) / (t * Real.log t ^ 2)) (Set.Icc t₀ y) :=
    (integrable_endpointError_kernel hy q hq).mono_set hsub
  have hg1 : IntervalIntegrable (fun t : ℝ =>
      (OAI.LargePrimeGaps.endpointError t q : ℝ) / (t * Real.log t ^ 2)) volume t₀ y := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht₀y]
    exact hg1_int
  have hg2_cont : ContinuousOn (fun t : ℝ =>
      ((|C| + 1) * Real.sqrt t) / (t * Real.log t ^ 2)) (Set.Icc t₀ y) := by
    have hnz : Set.Icc t₀ y ⊆ {0}ᶜ := fun t ht =>
      ne_of_gt (by linarith [ht₀2.trans ht.1])
    have hlog : ContinuousOn Real.log (Set.Icc t₀ y) :=
      Real.continuousOn_log.mono hnz
    have hden : ContinuousOn (fun t => t * Real.log t ^ 2) (Set.Icc t₀ y) :=
      continuousOn_id.mul (hlog.pow 2)
    have hnum : ContinuousOn (fun t => (|C| + 1) * Real.sqrt t) (Set.Icc t₀ y) :=
      continuousOn_const.mul Real.continuous_sqrt.continuousOn
    refine ContinuousOn.div hnum hden ?_
    intro t ht
    have ht2 : 2 ≤ t := ht₀2.trans ht.1
    have ht0 : t ≠ 0 := by linarith
    have hlogpos : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
    positivity
  have hg2 : IntervalIntegrable (fun t : ℝ =>
      ((|C| + 1) * Real.sqrt t) / (t * Real.log t ^ 2)) volume t₀ y := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht₀y]
    exact hg2_cont.integrableOn_Icc
  have heq : (fun t : ℝ =>
      (OAI.LargePrimeGaps.endpointError t q + (|C| + 1) * Real.sqrt t) / (t * Real.log t ^ 2)) =
      (fun t : ℝ =>
        (OAI.LargePrimeGaps.endpointError t q : ℝ) / (t * Real.log t ^ 2) +
        ((|C| + 1) * Real.sqrt t) / (t * Real.log t ^ 2)) := by
    ext t
    ring
  rw [heq]
  exact hg1.add hg2

lemma primeProgressionError_le_bound {y : ℝ} (hy : 2 ≤ y) {t₀ : ℝ} (ht₀2 : 2 ≤ t₀) (ht₀y : t₀ ≤ y)
    {q : ℕ} (hq : 0 < q)
    (C : ℝ) (hC : ∀ x : ℝ, Chebyshev.psi x - Chebyshev.theta x ≤ C * Real.sqrt x) :
    primeProgressionError y q ≤
      (OAI.LargePrimeGaps.endpointError y q + (|C| + 1) * Real.sqrt y) / Real.log y +
      (∫ t in t₀..y, (OAI.LargePrimeGaps.endpointError t q + (|C| + 1) * Real.sqrt t) / (t * Real.log t ^ 2)) +
      (t₀ / (q : ℝ) + 1) +
      (t₀ / (Real.log 2) ^ 2 + 2 / Real.log 2) / (q.totient : ℝ) := by
  let K : ℝ → ℝ := fun t =>
    (OAI.LargePrimeGaps.endpointError t q + (|C| + 1) * Real.sqrt t) / (t * Real.log t ^ 2)
  let B : ℝ :=
    (OAI.LargePrimeGaps.endpointError y q + (|C| + 1) * Real.sqrt y) / Real.log y +
    (∫ t in t₀..y, K t) +
    (t₀ / (q : ℝ) + 1) +
    (t₀ / (Real.log 2) ^ 2 + 2 / Real.log 2) / (q.totient : ℝ)
  have hK_nonneg : ∀ t ∈ Set.Icc t₀ y, 0 ≤ K t := by
    intro t ht
    have ht2 : 2 ≤ t := ht₀2.trans ht.1
    have ht0 : 0 < t := by linarith
    have hlog : 0 < Real.log t := Real.log_pos (by linarith)
    have h1 : 0 ≤ OAI.LargePrimeGaps.endpointError t q := by positivity
    have h2 : 0 ≤ (|C| + 1) * Real.sqrt t := by positivity
    dsimp [K]
    positivity
  have hK_int : IntervalIntegrable K volume t₀ y :=
    intervalIntegrable_upper_kernel hy ht₀2 ht₀y q hq C
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    have h1 : 0 ≤ (OAI.LargePrimeGaps.endpointError y q + (|C| + 1) * Real.sqrt y) / Real.log y := by
      have : 0 < Real.log y := Real.log_pos (by linarith)
      positivity
    have h2 : 0 ≤ ∫ t in t₀..y, K t :=
      intervalIntegral.integral_nonneg ht₀y hK_nonneg
    have h3 : 0 ≤ t₀ / (q : ℝ) + 1 := by positivity
    have h4 : 0 ≤ (t₀ / (Real.log 2) ^ 2 + 2 / Real.log 2) / (q.totient : ℝ) := by positivity
    linarith [h1, h2, h3, h4]
  apply primeProgressionError_le_of_forall y q B hB_nonneg
  intro v hv hcop
  have hphi : (q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hq).ne'
  have hthetaInt := intervalIntegrable_primeClassTheta_kernel hy q v
  have hsqInt : IntervalIntegrable (fun t : ℝ => 1 / Real.log t ^ 2) volume 2 y := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hy]
    refine ContinuousOn.integrableOn_Icc fun t ht => ?_
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith [ht.1]))
    have hlogsq : ContinuousWithinAt (fun u : ℝ => Real.log u ^ 2) (Set.Icc 2 y) t := by fun_prop
    exact (continuousWithinAt_const (b := (1 : ℝ))).div hlogsq (pow_ne_zero 2 hlog)
  let mKernel : ℝ → ℝ := fun t => (1 / (q.totient : ℝ)) * (1 / Real.log t ^ 2)
  have hmInt : IntervalIntegrable mKernel volume 2 y := by
    simpa [mKernel] using hsqInt.const_mul (1 / (q.totient : ℝ))
  let F : ℝ → ℝ := fun t =>
    (primeClassTheta t q v - t / (q.totient : ℝ)) / (t * Real.log t ^ 2)
  let fDiff : ℝ → ℝ := fun t =>
    primeClassTheta t q v / (t * Real.log t ^ 2) - mKernel t
  have hDiff_int : IntervalIntegrable fDiff volume 2 y :=
    hthetaInt.sub hmInt
  have hsub1 : Set.uIcc (2 : ℝ) t₀ ⊆ Set.uIcc (2 : ℝ) y := by
    rw [Set.uIcc_of_le ht₀2, Set.uIcc_of_le hy]
    exact Set.Icc_subset_Icc le_rfl ht₀y
  have hsub2 : Set.uIcc t₀ y ⊆ Set.uIcc (2 : ℝ) y := by
    rw [Set.uIcc_of_le ht₀y, Set.uIcc_of_le hy]
    exact Set.Icc_subset_Icc ht₀2 le_rfl
  have hF_eq_diff : ∀ t ∈ Set.Icc (2 : ℝ) y, F t = fDiff t := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith [ht.1]))
    dsimp [F, fDiff, mKernel]
    field_simp [hphi, ht0, hlog]
  have hF_int : IntervalIntegrable F volume 2 y := by
    apply hDiff_int.congr
    intro t ht
    rw [Set.uIoc_of_le hy] at ht
    have htIcc : t ∈ Set.Icc (2 : ℝ) y := ⟨le_of_lt ht.1, ht.2⟩
    exact (hF_eq_diff t htIcc).symm
  have hF_2_t0 : IntervalIntegrable F volume 2 t₀ := hF_int.mono_set hsub1
  have hF_t0_y : IntervalIntegrable F volume t₀ y := hF_int.mono_set hsub2
  have hF_split : (∫ t in (2 : ℝ)..y, F t) =
      (∫ t in (2 : ℝ)..t₀, F t) + (∫ t in t₀..y, F t) :=
    (integral_add_adjacent_intervals hF_2_t0 hF_t0_y).symm
  have hle_low := integral_theta_sub_linear_le_on_low ht₀2 hq hv
  have hF_le_K : ∀ t ∈ Set.Icc t₀ y, F t ≤ K t := by
    intro t ht
    have ht2 : 2 ≤ t := ht₀2.trans ht.1
    have ht0 : 0 < t := by linarith
    have hlog : 0 < Real.log t := Real.log_pos (by linarith)
    have hden : 0 < t * Real.log t ^ 2 := mul_pos ht0 (sq_pos_of_pos hlog)
    have herr := primeClassTheta_error_le t hq hv hcop C hC
    have hdiv := div_le_div_of_nonneg_right (le_trans (le_abs_self _) herr) (le_of_lt hden)
    exact hdiv
  have hnegF_le_K : ∀ t ∈ Set.Icc t₀ y, -F t ≤ K t := by
    intro t ht
    have ht2 : 2 ≤ t := ht₀2.trans ht.1
    have ht0 : 0 < t := by linarith
    have hlog : 0 < Real.log t := Real.log_pos (by linarith)
    have hden : 0 < t * Real.log t ^ 2 := mul_pos ht0 (sq_pos_of_pos hlog)
    have herr := primeClassTheta_error_le t hq hv hcop C hC
    have hdiv := div_le_div_of_nonneg_right (le_trans (neg_le_abs _) herr) (le_of_lt hden)
    dsimp [F]
    rw [← neg_div]
    exact hdiv
  have hle_up1 := intervalIntegral.integral_mono_on ht₀y hF_t0_y hK_int hF_le_K
  have hle_up2 : -(∫ t in t₀..y, F t) ≤ ∫ t in t₀..y, K t := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_mono_on ht₀y hF_t0_y.neg hK_int hnegF_le_K
  have habs_up : |∫ t in t₀..y, F t| ≤ ∫ t in t₀..y, K t := by
    rw [abs_le]
    exact ⟨by linarith [hle_up2], hle_up1⟩
  have habs_total_int : |∫ t in (2 : ℝ)..y, F t| ≤
      (t₀ / (q : ℝ) + 1 + (t₀ / (Real.log 2) ^ 2) / (q.totient : ℝ)) +
        ∫ t in t₀..y, K t := by
    rw [hF_split]
    calc
      |(∫ t in (2 : ℝ)..t₀, F t) + (∫ t in t₀..y, F t)| ≤
        |∫ t in (2 : ℝ)..t₀, F t| + |∫ t in t₀..y, F t| := abs_add_le _ _
      _ ≤ _ := add_le_add hle_low habs_up
  have hmain_eq := primeClassCount_li_error_eq hy hq (c := v)
  have hy_log : 0 < Real.log y := Real.log_pos (by linarith)
  have herr_y := primeClassTheta_error_le y hq hv hcop C hC
  have habs_y : |(primeClassTheta y q v - y / (q.totient : ℝ)) / Real.log y| ≤
      (OAI.LargePrimeGaps.endpointError y q + (|C| + 1) * Real.sqrt y) / Real.log y := by
    rw [abs_div, abs_of_pos hy_log]
    exact div_le_div_of_nonneg_right herr_y (le_of_lt hy_log)
  have hD_nonneg : 0 ≤ (2 / Real.log 2) / (q.totient : ℝ) := by positivity
  have hsum_le :
      |(primeClassCount y q v : ℝ) - logarithmicIntegral y / (q.totient : ℝ)| ≤
        |(primeClassTheta y q v - y / (q.totient : ℝ)) / Real.log y| +
        |∫ t in (2 : ℝ)..y, F t| +
        (2 / Real.log 2) / (q.totient : ℝ) := by
    rw [hmain_eq]
    have h1 := abs_add_le ((primeClassTheta y q v - y / (q.totient : ℝ)) / Real.log y +
        ∫ t in (2 : ℝ)..y, F t) ((2 / Real.log 2) / (q.totient : ℝ))
    have h2 := abs_add_le ((primeClassTheta y q v - y / (q.totient : ℝ)) / Real.log y)
        (∫ t in (2 : ℝ)..y, F t)
    rw [abs_of_nonneg hD_nonneg] at h1
    linarith
  have hdiv_add :
      (t₀ / (Real.log 2) ^ 2) / (q.totient : ℝ) + (2 / Real.log 2) / (q.totient : ℝ) =
        (t₀ / (Real.log 2) ^ 2 + 2 / Real.log 2) / (q.totient : ℝ) := by
    ring
  have hB_eq : (OAI.LargePrimeGaps.endpointError y q + (|C| + 1) * Real.sqrt y) / Real.log y +
      ((t₀ / (q : ℝ) + 1 + (t₀ / (Real.log 2) ^ 2) / (q.totient : ℝ)) + ∫ t in t₀..y, K t) +
      (2 / Real.log 2) / (q.totient : ℝ) = B := by
    dsimp [B]
    rw [← hdiv_add]
    ring
  calc
    |(primeClassCount y q v : ℝ) - logarithmicIntegral y / (q.totient : ℝ)| ≤ _ := hsum_le
    _ ≤ (OAI.LargePrimeGaps.endpointError y q + (|C| + 1) * Real.sqrt y) / Real.log y +
        ((t₀ / (q : ℝ) + 1 + (t₀ / (Real.log 2) ^ 2) / (q.totient : ℝ)) + ∫ t in t₀..y, K t) +
        (2 / Real.log 2) / (q.totient : ℝ) := by gcongr
    _ = B := hB_eq

lemma eventually_log_rpow_le_rpow (r s : ℝ) (hs : 0 < s) :
    ∀ᶠ x in Filter.atTop, Real.log x ^ r ≤ x ^ s := by
  have ho := isLittleO_log_rpow_rpow_atTop r hs
  have hb := ho.eventuallyLE
  have h2 : ∀ᶠ x in Filter.atTop, (2 : ℝ) ≤ x := Filter.eventually_ge_atTop 2
  refine (hb.and h2).mono fun x ⟨hx, hx2⟩ => ?_
  have hxpos : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)] at hx
  exact hx

lemma intervalIntegral_le_const_mul {a b B : ℝ} (hab : a ≤ b) (ha : 0 ≤ a)
    {g : ℝ → ℝ} (hg : IntervalIntegrable g volume a b)
    (hB : ∀ t ∈ Set.Icc a b, g t ≤ B) (hB0 : 0 ≤ B) :
    (∫ t in a..b, g t) ≤ B * b := by
  have hconst : IntervalIntegrable (fun _ => B) volume a b := intervalIntegrable_const
  have hle := intervalIntegral.integral_mono_on hab hg hconst hB
  rw [intervalIntegral.integral_const, smul_eq_mul] at hle
  calc (∫ t in a..b, g t) ≤ (b - a) * B := hle
  _ ≤ b * B := by nlinarith
  _ = B * b := by ring

lemma sum_Icc_endpointError_le
    {x : ℝ} {Q : ℕ} {b M : ℝ} {A₁ : ℝ} (x₀ : ℝ)
    (hBV : ∀ u : ℝ, x₀ ≤ u →
      (∑ q ∈ Finset.Icc 1 ⌊u^(1/2:ℝ) * (Real.log u)^(-b)⌋₊,
        (OAI.LargePrimeGaps.endpointError u q : ℝ)) ≤ M * u * (Real.log u)^(-A₁))
    (hx : x₀ ≤ x)
    (hQ : (Q : ℝ) ≤ x^(1/2:ℝ) * (Real.log x)^(-b)) :
    (∑ q ∈ Finset.Icc 1 Q, (OAI.LargePrimeGaps.endpointError x q : ℝ)) ≤
      M * x * (Real.log x)^(-A₁) := by
  have hQ_floor : Q ≤ ⌊x^(1/2:ℝ) * (Real.log x)^(-b)⌋₊ := Nat.le_floor hQ
  let s := Finset.Icc 1 Q
  let t := Finset.Icc 1 ⌊x^(1/2:ℝ) * (Real.log x)^(-b)⌋₊
  have hsub : s ⊆ t := Finset.Icc_subset_Icc le_rfl hQ_floor
  calc (∑ q ∈ s, (OAI.LargePrimeGaps.endpointError x q : ℝ)) ≤
      ∑ q ∈ t, (OAI.LargePrimeGaps.endpointError x q : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => NNReal.coe_nonneg _)
    _ ≤ M * x * (Real.log x)^(-A₁) := hBV x hx

lemma Q_le_x_pow_log_neg_b {y t₀ x : ℝ} (hy : 2 ≤ y)
    {η η' b : ℝ} (hη : 0 < η) (hη' : 0 < η') (hη'η : η' ≤ η / 2) (hb : 0 < b)
    (ht₀ : t₀ = y ^ (1 - η'))
    (ht₀2 : 2 ≤ t₀)
    (hx_mem : x ∈ Set.Icc t₀ y)
    (hlog_b : Real.log y ^ b ≤ y ^ (η - η' / 2)) :
    (⌊Real.rpow y (1 / 2 - η)⌋₊ : ℝ) ≤ x ^ (1 / 2 : ℝ) * Real.log x ^ (-b) := by
  have hypos : 0 < y := by linarith
  have hlogy_pos : 0 < Real.log y := Real.log_pos (by linarith)
  have hxpos : 0 < x := by linarith [ht₀2.trans hx_mem.1]
  have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith [ht₀2.trans hx_mem.1])
  have hQ_le : (⌊Real.rpow y (1 / 2 - η)⌋₊ : ℝ) ≤ y ^ (1 / 2 - η) :=
    Nat.floor_le (Real.rpow_nonneg (by linarith [hy]) _)
  have hsqrt : t₀ ^ (1 / 2 : ℝ) ≤ x ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (by linarith [ht₀2]) hx_mem.1 (by norm_num)
  have hlog_le : Real.log x ≤ Real.log y := Real.log_le_log hxpos hx_mem.2
  have hlogb_le : Real.log x ^ b ≤ Real.log y ^ b :=
    Real.rpow_le_rpow (by positivity) hlog_le (le_of_lt hb)
  have hlogneg : Real.log y ^ (-b) ≤ Real.log x ^ (-b) := by
    rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
    exact (inv_le_inv₀ (Real.rpow_pos_of_pos hlogy_pos b) (Real.rpow_pos_of_pos hlogx_pos b)).mpr hlogb_le
  have ht0_half : t₀ ^ (1 / 2 : ℝ) = y ^ ((1 - η') / 2) := by
    rw [ht₀, ← Real.rpow_mul (le_of_lt hypos)]
    congr 1
    ring
  have hlog_inv : y ^ (-(η - η' / 2)) ≤ Real.log y ^ (-b) := by
    rw [Real.rpow_neg (le_of_lt hypos), Real.rpow_neg (by positivity)]
    exact (inv_le_inv₀ (Real.rpow_pos_of_pos hypos (η - η' / 2)) (Real.rpow_pos_of_pos hlogy_pos b)).mpr hlog_b
  have hpow_eq : y ^ ((1 - η') / 2) * y ^ (-(η - η' / 2)) = y ^ (1 / 2 - η) := by
    rw [← Real.rpow_add hypos]
    congr 1
    ring
  have hprod : y ^ (1 / 2 - η) ≤ t₀ ^ (1 / 2 : ℝ) * Real.log y ^ (-b) := by
    rw [← hpow_eq, ht0_half]
    have ht0_pos : 0 ≤ y ^ ((1 - η') / 2) := by positivity
    exact mul_le_mul_of_nonneg_left hlog_inv ht0_pos
  calc
    (⌊Real.rpow y (1 / 2 - η)⌋₊ : ℝ) ≤ y ^ (1 / 2 - η) := hQ_le
    _ ≤ t₀ ^ (1 / 2 : ℝ) * Real.log y ^ (-b) := hprod
    _ ≤ x ^ (1 / 2 : ℝ) * Real.log x ^ (-b) := by
      have ht0_pos : 0 ≤ t₀ ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by linarith [ht₀2]) _
      have hx_pos : 0 ≤ x ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by linarith [ht₀2.trans hx_mem.1]) _
      have hlogneg_pos : 0 ≤ Real.log y ^ (-b) := by positivity
      exact mul_le_mul hsqrt hlogneg hlogneg_pos hx_pos

lemma sum_Icc_primeProgressionError_le
    {y : ℝ} (hy : 2 ≤ y) {t₀ : ℝ} (ht₀2 : 2 ≤ t₀) (ht₀y : t₀ ≤ y)
    (Q : ℕ)
    (C : ℝ) (hC : ∀ x : ℝ, Chebyshev.psi x - Chebyshev.theta x ≤ C * Real.sqrt x) :
    (∑ q ∈ Finset.Icc 1 Q, primeProgressionError y q) ≤
      ((∑ q ∈ Finset.Icc 1 Q, (OAI.LargePrimeGaps.endpointError y q : ℝ)) + (Q : ℝ) * ((|C| + 1) * Real.sqrt y)) / Real.log y +
      (∫ t in t₀..y, ((∑ q ∈ Finset.Icc 1 Q, (OAI.LargePrimeGaps.endpointError t q : ℝ)) + (Q : ℝ) * ((|C| + 1) * Real.sqrt t)) / (t * Real.log t ^ 2)) +
      (t₀ * (harmonic Q : ℝ) + (Q : ℝ)) +
      (t₀ / (Real.log 2) ^ 2 + 2 / Real.log 2) * (harmonic Q : ℝ) ^ 2 := by
  let s := Finset.Icc 1 Q
  have hq_pos : ∀ q ∈ s, 0 < q := fun q hq => (Finset.mem_Icc.mp hq).1
  have hcard : (s.card : ℝ) = (Q : ℝ) := by
    dsimp [s]
    by_cases hQ : 1 ≤ Q
    · rw [Nat.card_Icc, Nat.add_sub_cancel_right]
    · have : Q = 0 := by omega
      subst this
      simp
  have hharm : (∑ q ∈ s, (1 : ℝ) / (q : ℝ)) = (harmonic Q : ℝ) := by
    dsimp [s]
    rw [harmonic_eq_sum_Icc]
    push_cast
    simp only [one_div]
  have hle_q : ∀ q ∈ s, primeProgressionError y q ≤
      (OAI.LargePrimeGaps.endpointError y q + (|C| + 1) * Real.sqrt y) / Real.log y +
      (∫ t in t₀..y, (OAI.LargePrimeGaps.endpointError t q + (|C| + 1) * Real.sqrt t) / (t * Real.log t ^ 2)) +
      (t₀ / (q : ℝ) + 1) +
      (t₀ / (Real.log 2) ^ 2 + 2 / Real.log 2) / (q.totient : ℝ) :=
    fun q hq => primeProgressionError_le_bound hy ht₀2 ht₀y (hq_pos q hq) C hC
  have hsum_le := Finset.sum_le_sum hle_q
  have h1 : (∑ q ∈ s, (OAI.LargePrimeGaps.endpointError y q + (|C| + 1) * Real.sqrt y) / Real.log y) =
      ((∑ q ∈ s, (OAI.LargePrimeGaps.endpointError y q : ℝ)) + (Q : ℝ) * ((|C| + 1) * Real.sqrt y)) / Real.log y := by
    rw [← Finset.sum_div, Finset.sum_add_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul, hcard]
  have h2 : (∑ q ∈ s, ∫ t in t₀..y, (OAI.LargePrimeGaps.endpointError t q + (|C| + 1) * Real.sqrt t) / (t * Real.log t ^ 2)) =
      ∫ t in t₀..y, ((∑ q ∈ s, (OAI.LargePrimeGaps.endpointError t q : ℝ)) + (Q : ℝ) * ((|C| + 1) * Real.sqrt t)) / (t * Real.log t ^ 2) := by
    rw [← intervalIntegral.integral_finsetSum (s := s) (f := fun q t =>
      (OAI.LargePrimeGaps.endpointError t q + (|C| + 1) * Real.sqrt t) / (t * Real.log t ^ 2))]
    · apply intervalIntegral.integral_congr
      intro t _
      dsimp
      rw [← Finset.sum_div, Finset.sum_add_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, hcard]
    · intro q hq
      exact intervalIntegrable_upper_kernel hy ht₀2 ht₀y q (hq_pos q hq) C
  have h3 : (∑ q ∈ s, (t₀ / (q : ℝ) + 1)) = t₀ * (harmonic Q : ℝ) + (Q : ℝ) := by
    rw [Finset.sum_add_distrib]
    have hdiv (q : ℕ) : t₀ / (q : ℝ) = t₀ * ((1 : ℝ) / (q : ℝ)) := by ring
    simp_rw [hdiv, ← Finset.mul_sum]
    rw [hharm]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, hcard]
  have h4 : (∑ q ∈ s, (t₀ / (Real.log 2) ^ 2 + 2 / Real.log 2) / (q.totient : ℝ)) ≤
      (t₀ / (Real.log 2) ^ 2 + 2 / Real.log 2) * (harmonic Q : ℝ) ^ 2 := by
    have hdiv (q : ℕ) : (t₀ / (Real.log 2) ^ 2 + 2 / Real.log 2) / (q.totient : ℝ) =
        (t₀ / (Real.log 2) ^ 2 + 2 / Real.log 2) * (1 / (q.totient : ℝ)) := by ring
    simp_rw [hdiv, ← Finset.mul_sum]
    have hpos : 0 ≤ t₀ / (Real.log 2) ^ 2 + 2 / Real.log 2 := by positivity
    have htot := sum_reciprocal_totient_le_harmonic_sq Q
    dsimp [s]
    exact mul_le_mul_of_nonneg_left htot hpos
  calc
    (∑ q ∈ s, primeProgressionError y q) ≤
        ∑ q ∈ s, ((OAI.LargePrimeGaps.endpointError y q + (|C| + 1) * Real.sqrt y) / Real.log y +
          (∫ t in t₀..y, (OAI.LargePrimeGaps.endpointError t q + (|C| + 1) * Real.sqrt t) / (t * Real.log t ^ 2)) +
          (t₀ / (q : ℝ) + 1) +
          (t₀ / (Real.log 2) ^ 2 + 2 / Real.log 2) / (q.totient : ℝ)) := hsum_le
    _ = (∑ q ∈ s, (OAI.LargePrimeGaps.endpointError y q + (|C| + 1) * Real.sqrt y) / Real.log y) +
        (∑ q ∈ s, ∫ t in t₀..y, (OAI.LargePrimeGaps.endpointError t q + (|C| + 1) * Real.sqrt t) / (t * Real.log t ^ 2)) +
        (∑ q ∈ s, (t₀ / (q : ℝ) + 1)) +
        (∑ q ∈ s, (t₀ / (Real.log 2) ^ 2 + 2 / Real.log 2) / (q.totient : ℝ)) := by
      simp only [add_assoc, Finset.sum_add_distrib]
    _ ≤ _ := by
      rw [h1, h2, h3]
      gcongr

lemma upper_integral_le {y t₀ : ℝ} (hy : 2 ≤ y) (ht₀2 : 2 ≤ t₀) (ht₀y : t₀ ≤ y)
    (Q : ℕ) (C : ℝ) (M A₁ : ℝ) (hM : 0 ≤ M) (hA₁ : 0 ≤ A₁)
    (h_end : ∀ t ∈ Set.Icc t₀ y, (∑ q ∈ Finset.Icc 1 Q, (OAI.LargePrimeGaps.endpointError t q : ℝ)) ≤ M * t * Real.log t ^ (-A₁)) :
    (∫ t in t₀..y, ((∑ q ∈ Finset.Icc 1 Q, (OAI.LargePrimeGaps.endpointError t q : ℝ)) + (Q : ℝ) * ((|C| + 1) * Real.sqrt t)) / (t * Real.log t ^ 2)) ≤
      (M * Real.log t₀ ^ (-A₁) / (Real.log 2 ^ 2) + (Q : ℝ) * (|C| + 1) * Real.sqrt y / (t₀ * Real.log 2 ^ 2)) * y := by
  let s := Finset.Icc 1 Q
  let K : ℕ → ℝ → ℝ := fun q t =>
    (OAI.LargePrimeGaps.endpointError t q + (|C| + 1) * Real.sqrt t) / (t * Real.log t ^ 2)
  have hq_pos : ∀ q ∈ s, 0 < q := fun q hq => (Finset.mem_Icc.mp hq).1
  have hK_int : ∀ q ∈ s, IntervalIntegrable (K q) volume t₀ y :=
    fun q hq => intervalIntegrable_upper_kernel hy ht₀2 ht₀y q (hq_pos q hq) C
  have hcard : (s.card : ℝ) = (Q : ℝ) := by
    dsimp [s]
    by_cases hQ : 1 ≤ Q
    · rw [Nat.card_Icc, Nat.add_sub_cancel_right]
    · have : Q = 0 := by omega
      subst this
      simp
  have hsum_int_gen : ∀ (u : Finset ℕ), (∀ q ∈ u, IntervalIntegrable (K q) volume t₀ y) →
      IntervalIntegrable (fun t => ∑ q ∈ u, K q t) volume t₀ y := by
    intro u
    refine Finset.induction_on u ?_ ?_
    · intro _
      simp only [Finset.sum_empty]
      exact intervalIntegrable_const
    · intro i u' hi ih hK
      simp only [Finset.sum_insert hi]
      exact IntervalIntegrable.add (hK i (Finset.mem_insert_self i u'))
        (ih (fun q hq => hK q (Finset.mem_insert_of_mem hq)))
  have hsum_int := hsum_int_gen s hK_int
  have heq : (fun t => ((∑ q ∈ s, (OAI.LargePrimeGaps.endpointError t q : ℝ)) + (Q : ℝ) * ((|C| + 1) * Real.sqrt t)) / (t * Real.log t ^ 2)) =
      (fun t => ∑ q ∈ s, K q t) := by
    ext t
    dsimp [K]
    rw [← Finset.sum_div, Finset.sum_add_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul, hcard]
  have hg_int : IntervalIntegrable (fun t => ((∑ q ∈ s, (OAI.LargePrimeGaps.endpointError t q : ℝ)) + (Q : ℝ) * ((|C| + 1) * Real.sqrt t)) / (t * Real.log t ^ 2)) volume t₀ y := by
    rw [heq]
    exact hsum_int
  let B := M * Real.log t₀ ^ (-A₁) / (Real.log 2 ^ 2) + (Q : ℝ) * (|C| + 1) * Real.sqrt y / (t₀ * Real.log 2 ^ 2)
  have hB0 : 0 ≤ B := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have ht0_pos : 0 < t₀ := by linarith [ht₀2]
    have hlogt0 : 0 < Real.log t₀ := Real.log_pos (by linarith [ht₀2])
    have h1 : 0 ≤ M * Real.log t₀ ^ (-A₁) / (Real.log 2 ^ 2) := by positivity
    have h2 : 0 ≤ (Q : ℝ) * (|C| + 1) * Real.sqrt y / (t₀ * Real.log 2 ^ 2) := by positivity
    linarith
  have hB : ∀ t ∈ Set.Icc t₀ y,
      ((∑ q ∈ s, (OAI.LargePrimeGaps.endpointError t q : ℝ)) + (Q : ℝ) * ((|C| + 1) * Real.sqrt t)) / (t * Real.log t ^ 2) ≤ B := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht₀2.trans ht.1]
    have hlogt : 0 < Real.log t := Real.log_pos (by linarith [ht₀2.trans ht.1])
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hden : 0 < t * Real.log t ^ 2 := mul_pos ht0 (sq_pos_of_pos hlogt)
    have hden_min : 0 < t * Real.log 2 ^ 2 := mul_pos ht0 (sq_pos_of_pos hlog2)
    have hden2_min : 0 < t₀ * Real.log 2 ^ 2 := mul_pos (by linarith [ht₀2]) (sq_pos_of_pos hlog2)
    have hlog_le : Real.log 2 ≤ Real.log t :=
      Real.log_le_log (by norm_num) (by linarith [ht₀2, ht.1])
    have hlog2_nonneg : 0 ≤ Real.log 2 := by positivity
    have hsq_le : Real.log 2 ^ 2 ≤ Real.log t ^ 2 := by nlinarith [hlog_le, hlog2_nonneg]
    have hden_le1 : t * Real.log 2 ^ 2 ≤ t * Real.log t ^ 2 := by nlinarith [hsq_le, ht0]
    have hden_le2 : t₀ * Real.log 2 ^ 2 ≤ t * Real.log t ^ 2 := by
      have : t₀ * Real.log 2 ^ 2 ≤ t * Real.log 2 ^ 2 := by nlinarith [ht.1, hlog2_nonneg]
      linarith [hden_le1]
    have hsum := h_end t ht
    have hterm1 : (∑ q ∈ s, (OAI.LargePrimeGaps.endpointError t q : ℝ)) / (t * Real.log t ^ 2) ≤
        M * Real.log t₀ ^ (-A₁) / (Real.log 2 ^ 2) := by
      have hlog_le_t0 : Real.log t₀ ≤ Real.log t := Real.log_le_log (by linarith [ht₀2]) ht.1
      have hexp : -A₁ ≤ 0 := by linarith
      have hpow_le : Real.log t ^ (-A₁) ≤ Real.log t₀ ^ (-A₁) :=
        Real.rpow_le_rpow_of_nonpos (Real.log_pos (by linarith [ht₀2])) hlog_le_t0 hexp
      have hnum_le : (∑ q ∈ s, (OAI.LargePrimeGaps.endpointError t q : ℝ)) ≤
          t * (M * Real.log t₀ ^ (-A₁)) := by
        calc
          (∑ q ∈ s, (OAI.LargePrimeGaps.endpointError t q : ℝ)) ≤ M * t * Real.log t ^ (-A₁) := hsum
          _ = t * (M * Real.log t ^ (-A₁)) := by ring
          _ ≤ t * (M * Real.log t₀ ^ (-A₁)) := by
            gcongr
      have hlogt0_pos : 0 ≤ Real.log t₀ := Real.log_nonneg (by linarith [ht₀2])
      have hpow_pos : 0 ≤ Real.log t₀ ^ (-A₁) := Real.rpow_nonneg hlogt0_pos _
      have hnum_pos : 0 ≤ t * (M * Real.log t₀ ^ (-A₁)) := by
        have : 0 ≤ M * Real.log t₀ ^ (-A₁) := mul_nonneg hM hpow_pos
        exact mul_nonneg (le_of_lt ht0) this
      calc
        (∑ q ∈ s, (OAI.LargePrimeGaps.endpointError t q : ℝ)) / (t * Real.log t ^ 2) ≤
            (t * (M * Real.log t₀ ^ (-A₁))) / (t * Real.log t ^ 2) :=
          div_le_div_of_nonneg_right hnum_le (le_of_lt hden)
        _ ≤ (t * (M * Real.log t₀ ^ (-A₁))) / (t * Real.log 2 ^ 2) :=
          div_le_div_of_nonneg_left hnum_pos hden_min hden_le1
        _ = M * Real.log t₀ ^ (-A₁) / (Real.log 2 ^ 2) := by
          field_simp [ne_of_gt ht0]
    have hterm2 : (Q : ℝ) * ((|C| + 1) * Real.sqrt t) / (t * Real.log t ^ 2) ≤
        (Q : ℝ) * (|C| + 1) * Real.sqrt y / (t₀ * Real.log 2 ^ 2) := by
      have hsqrt_le : Real.sqrt t ≤ Real.sqrt y := Real.sqrt_le_sqrt ht.2
      have hnum_le : (Q : ℝ) * ((|C| + 1) * Real.sqrt t) ≤ (Q : ℝ) * (|C| + 1) * Real.sqrt y := by
        have : 0 ≤ (Q : ℝ) * (|C| + 1) := by positivity
        nlinarith
      have hnum_pos : 0 ≤ (Q : ℝ) * (|C| + 1) * Real.sqrt y := by positivity
      calc
        (Q : ℝ) * ((|C| + 1) * Real.sqrt t) / (t * Real.log t ^ 2) ≤
            ((Q : ℝ) * (|C| + 1) * Real.sqrt y) / (t * Real.log t ^ 2) :=
          div_le_div_of_nonneg_right hnum_le (le_of_lt hden)
        _ ≤ ((Q : ℝ) * (|C| + 1) * Real.sqrt y) / (t₀ * Real.log 2 ^ 2) :=
          div_le_div_of_nonneg_left hnum_pos hden2_min hden_le2
    have hsum_split : ((∑ q ∈ s, (OAI.LargePrimeGaps.endpointError t q : ℝ)) + (Q : ℝ) * ((|C| + 1) * Real.sqrt t)) / (t * Real.log t ^ 2) =
        (∑ q ∈ s, (OAI.LargePrimeGaps.endpointError t q : ℝ)) / (t * Real.log t ^ 2) +
        (Q : ℝ) * ((|C| + 1) * Real.sqrt t) / (t * Real.log t ^ 2) := by
      ring
    rw [hsum_split]
    exact add_le_add hterm1 hterm2
  have hle := intervalIntegral_le_const_mul ht₀y (by linarith [ht₀2]) hg_int hB hB0
  exact hle

/-- `ext:bombieri-vinogradov`, 12-construction.tex:286-292 (`con:bv-input`); matching OAI
`bombieriVinogradov` (`PrimeGaps/Main.lean:158`), converted to the prime-counting form. -/
theorem bombieri_vinogradov :
    ∀ A η : ℝ, 0 < A → 0 < η →
      ∃ C y₀ : ℝ, 0 < C ∧ 2 ≤ y₀ ∧
        ∀ y : ℝ, y₀ ≤ y →
          (∑ q ∈ Finset.range (⌊Real.rpow y (1 / 2 - η)⌋₊ + 1),
            primeProgressionError y q) ≤ C * y * Real.rpow (Real.log y) (-A) := by
  sorry

end SWBVHelpers

lemma primeCharacterPrefix_eq_range {d : ℕ} (χ : DirichletCharacter ℂ d) (x : ℝ) :
    OAI.LargePrimeGaps.primeCharacterPrefix x χ =
      (∑ n ∈ Finset.range (⌊x⌋₊ + 1),
        (χ (n : ZMod d) : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ)) := by
  classical
  let f : ℕ → ℂ := fun n =>
    (χ (n : ZMod d) : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ)
  have hzero : f 0 = 0 := by
    simp [f, ArithmeticFunction.vonMangoldt_apply, not_isPrimePow_zero]
  have hrange : Finset.range (⌊x⌋₊ + 1) = Finset.Icc 0 ⌊x⌋₊ := by
    ext n
    simp
  have hioc : Finset.Ioc 0 ⌊x⌋₊ = (Finset.Icc 0 ⌊x⌋₊).erase 0 := by
    ext n
    simp
  have hremove :
      (∑ n ∈ (Finset.Icc 0 ⌊x⌋₊).erase 0, f n) =
        ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, f n := by
    apply Finset.sum_subset (Finset.erase_subset _ _)
    intro n hn hn'
    have hn0 : n = 0 := by
      by_contra hne
      exact hn' (Finset.mem_erase.mpr ⟨hne, hn⟩)
    subst n
    exact hzero
  change (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, f n) = _
  calc
    _ = ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, f n := by rw [hioc, hremove]
    _ = ∑ n ∈ Finset.range (⌊x⌋₊ + 1), f n := by rw [← hrange]

/-- `ext:siegel-walfisz`, PP `01-preliminaries.tex:24-40`, Proposition 2.1; matching OAI
`siegelWalfisz` (`PrimeGaps/Main.lean:142`). -/
theorem siegel_walfisz :
    ∀ A B : ℝ, 0 < A → 0 < B →
      ∃ C x₀ : ℝ, 0 < C ∧ 1 < x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          ∀ d : ℕ, 0 < d → (d : ℝ) ≤ Real.rpow (Real.log x) B →
            ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive →
              ‖(∑ n ∈ Finset.range (⌊x⌋₊ + 1),
                  (χ (n : ZMod d) : ℂ) *
                    (ArithmeticFunction.vonMangoldt n : ℂ)) -
                    (if χ = 1 then (x : ℂ) else 0)‖ ≤
                  C * x * Real.rpow (Real.log x) (-A) := by
  intro A B hA hB
  obtain ⟨M, hM, x₀, hx₀, hSW⟩ := OAI.LargePrimeGaps.siegelWalfisz A B hA hB
  refine ⟨M, x₀, hM, hx₀, ?_⟩
  intro x hx d hd hdlog χ hχ
  have h := hSW x hx d hd hdlog χ hχ
  rw [OAI.LargePrimeGaps.primeCharacterError, primeCharacterPrefix_eq_range] at h
  exact h

/-- `ext:mertens`, PD Lemma 2.1; 11-sieve.tex:159-164; 12-construction.tex:398-402. The
first assertion is the second Mertens theorem; the second is its product form. Matching PNT+
`mertens_second_theorem` (`RosserSchoenfeldPrime.lean:824-825`) and `E₃.bound''`
(`Mertens.lean:2419). -/
theorem mertens :
    (∀ ε : ℝ, 0 < ε → ∃ y₀ : ℝ, 2 < y₀ ∧
      ∀ y : ℝ, y₀ ≤ y →
        |(∑ p ∈ primesUpTo y, 1 / (p : ℝ)) - Real.log (Real.log y) -
          meisselMertensConstant| ≤ ε) ∧
    (∀ ε : ℝ, 0 < ε → ∃ y₀ : ℝ, 2 < y₀ ∧
      ∀ y : ℝ, y₀ ≤ y →
        |roughSieveProduct y * Real.log y - Real.exp (-Real.eulerMascheroniConstant)| ≤ ε) := by
  sorry

/-- `ext:dirichlet-orthogonality`, 12-construction.tex:116-120; matching Mathlib
`DirichletCharacter.sum_char_inv_mul_char_eq` (`Orthogonality.lean:79`). -/
theorem dirichlet_orthogonality (M : ℕ) (hM : 0 < M)
    (u v : ZMod M) (hu : IsUnit u) :
    (if v = u then (1 : ℂ) else 0) =
      (1 / (Nat.totient M : ℂ)) *
        ∑ χ : DirichletCharacter ℂ M,
          star (χ u) * χ v := by
  letI : NeZero M := ⟨Nat.ne_of_gt hM⟩
  have hstar (χ : DirichletCharacter ℂ M) : star (χ u) = χ (u⁻¹) := by
    calc
      star (χ u) = (χ u)⁻¹ := by
        simpa using (Complex.inv_eq_conj (χ.unit_norm_eq_one hu.unit)).symm
      _ = χ (u⁻¹) := by
        have hmul : χ u * χ (u⁻¹) = 1 := by
          rw [← map_mul, ZMod.mul_inv_of_unit u hu, map_one]
        exact (eq_inv_of_mul_eq_one_right hmul).symm
  have hsum :
      (∑ χ : DirichletCharacter ℂ M, χ (u⁻¹) * χ v) =
        if u = v then (Nat.totient M : ℂ) else 0 := by
    simpa using DirichletCharacter.sum_char_inv_mul_char_eq (R := ℂ) hu v
  rw [show (∑ χ : DirichletCharacter ℂ M, star (χ u) * χ v) =
      ∑ χ : DirichletCharacter ℂ M, χ (u⁻¹) * χ v from by
        apply Finset.sum_congr rfl
        intro χ hχ
        rw [hstar]]
  rw [hsum]
  by_cases hv : v = u
  · subst v
    have htotient : (Nat.totient M : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.totient_pos.mpr hM))
    simp [htotient]
  · simp [hv, Ne.symm hv]

/-- The Mellin-Fourier transform of the logarithmic-coordinate test function used in §12. -/
noncomputable def logFourierTransform (Ψ : ℝ → ℝ) (v : ℝ) : ℂ :=
  (1 / (2 * Real.pi : ℝ) : ℂ) *
    ∫ s : ℝ, (Ψ (Real.exp s) : ℂ) * Complex.exp (-Complex.I * v * s)

/-- `ext:fourier-inversion`, 12-construction.tex:133-140; matching Mathlib
`Continuous.fourierInv_fourier_eq` (`Analysis/Fourier/Inversion.lean:174`). -/
theorem fourier_inversion (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ)
    (hsupp : Function.support Ψ ⊆ Set.Ioo 1 2) :
    (∀ y : ℝ, 0 < y →
      (Ψ y : ℂ) = ∫ v : ℝ,
        logFourierTransform Ψ v * Complex.exp (Complex.I * v * Real.log y)) ∧
    (∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ v : ℝ, ‖logFourierTransform Ψ v‖ ≤
        C * Real.rpow (1 + |v|) (-(N : ℝ))) := by
  classical
  let ψlog : ℝ → ℂ := fun s => (Ψ (Real.exp s) : ℂ)
  have hψreal : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s => Ψ (Real.exp s)) :=
    hΨ.comp Real.contDiff_exp
  have hψsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψlog := by
    dsimp [ψlog]
    exact Complex.ofRealCLM.contDiff.comp hψreal
  have hψsupport : Function.support ψlog ⊆ Set.Icc 0 (Real.log 2) := by
    intro s hs
    have hs' : ψlog s ≠ 0 := by simpa only [Function.mem_support] using hs
    have hne : Ψ (Real.exp s) ≠ 0 := by
      intro hz
      apply hs'
      simp [ψlog, hz]
    have hmem : Real.exp s ∈ Function.support Ψ := by
      simpa only [Function.mem_support] using hne
    rcases hsupp hmem with ⟨hlo, hhi⟩
    constructor
    · have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 1) hlo
      exact le_of_lt (by simpa using h)
    · have h := Real.log_lt_log (Real.exp_pos s) hhi
      exact le_of_lt (by simpa using h)
  have hψcompact : HasCompactSupport ψlog :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hψsupport
  let F : SchwartzMap ℝ ℂ := hψcompact.toSchwartzMap hψsmooth
  have hFcoe : (F : ℝ → ℂ) = ψlog := rfl
  have hFT (v : ℝ) :
      logFourierTransform Ψ v =
        (1 / (2 * Real.pi : ℝ) : ℂ) * 𝓕 (F : ℝ → ℂ) (v / (2 * Real.pi)) := by
    unfold logFourierTransform
    rw [Real.fourier_eq']
    congr 1
    apply integral_congr_ae
    filter_upwards [] with s
    rw [hFcoe, Real.inner_apply]
    simp only [smul_eq_mul]
    have harg :
        (↑(-2 * Real.pi * (s * (v / (2 * Real.pi))) : ℝ) : ℂ) * Complex.I =
          -Complex.I * (v : ℂ) * s := by
      push_cast
      field_simp [Real.pi_ne_zero]
    rw [harg]
    ring
  constructor
  · intro y hy
    let x := Real.log y
    let H : ℝ → ℂ := fun v => logFourierTransform Ψ v * Complex.exp (Complex.I * v * x)
    have hπ : 0 < 2 * Real.pi := by positivity
    have hchange : (∫ v : ℝ, H v) = (2 * Real.pi : ℝ) • ∫ w : ℝ, H ((2 * Real.pi) * w) := by
      have h := Measure.integral_comp_mul_left H (2 * Real.pi)
      rw [abs_of_pos (inv_pos.mpr hπ)] at h
      calc
        (∫ v : ℝ, H v) = (2 * Real.pi : ℝ) •
            ((2 * Real.pi : ℝ)⁻¹ • ∫ v : ℝ, H v) := by
              rw [smul_smul, mul_inv_cancel₀ hπ.ne', one_smul]
        _ = (2 * Real.pi : ℝ) • ∫ w : ℝ, H ((2 * Real.pi) * w) := by rw [h.symm]
    have hscaled (w : ℝ) :
        (2 * Real.pi : ℝ) • H ((2 * Real.pi) * w) =
          Complex.exp ((↑(2 * Real.pi * (w * x) : ℝ) : ℂ) * Complex.I) *
            𝓕 (F : ℝ → ℂ) w := by
      dsimp [H]
      rw [hFT]
      have hfreq : (2 * Real.pi * w) / (2 * Real.pi) = w := by
        field_simp [Real.pi_ne_zero]
      rw [hfreq]
      have hexpArg :
          Complex.I * (↑(2 * Real.pi * w : ℝ) : ℂ) * (x : ℂ) =
            (↑(2 * Real.pi * (w * x) : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
      have hexp : Complex.exp (Complex.I * (↑(2 * Real.pi * w : ℝ) : ℂ) * (x : ℂ)) =
          Complex.exp ((↑(2 * Real.pi * (w * x) : ℝ) : ℂ) * Complex.I) :=
        congrArg Complex.exp hexpArg
      rw [hexp]
      have hcoef :
          ((2 * Real.pi : ℝ) : ℂ) * (1 / (2 * Real.pi : ℝ) : ℂ) = 1 := by
        push_cast
        field_simp [Real.pi_ne_zero]
      calc
        ((2 * Real.pi : ℝ) : ℂ) *
            (((1 / (2 * Real.pi : ℝ) : ℂ) * 𝓕 (F : ℝ → ℂ) w) *
              Complex.exp ((↑(2 * Real.pi * (w * x) : ℝ) : ℂ) * Complex.I)) =
          (((2 * Real.pi : ℝ) : ℂ) * (1 / (2 * Real.pi : ℝ) : ℂ)) *
            𝓕 (F : ℝ → ℂ) w *
              Complex.exp ((↑(2 * Real.pi * (w * x) : ℝ) : ℂ) * Complex.I) := by ring
        _ = _ := by rw [hcoef]; ring
    have hInvSch : 𝓕⁻ (𝓕 F) = F := by
      ext z
      rw [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe]
      exact congrFun (F.continuous.fourierInv_fourier_eq F.integrable (𝓕 F).integrable) z
    have hInv : 𝓕⁻ (𝓕 (F : ℝ → ℂ)) x = F x := by
      have h := congrArg (fun G : SchwartzMap ℝ ℂ => (G : ℝ → ℂ)) hInvSch
      simpa only [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe] using congrFun h x
    have hInvIntegral :
        𝓕⁻ (𝓕 (F : ℝ → ℂ)) x =
          ∫ w : ℝ, Complex.exp ((↑(2 * Real.pi * (w * x) : ℝ) : ℂ) * Complex.I) *
            𝓕 (F : ℝ → ℂ) w := by
      rw [Real.fourierInv_eq']
      apply integral_congr_ae
      filter_upwards [] with w
      rw [Real.inner_apply]
      simp only [smul_eq_mul]
    have hInvToIntegral : (∫ v : ℝ, H v) = 𝓕⁻ (𝓕 (F : ℝ → ℂ)) x := by
      calc
        (∫ v : ℝ, H v) = (2 * Real.pi : ℝ) • ∫ w : ℝ, H ((2 * Real.pi) * w) := hchange
        _ = ∫ w : ℝ, (2 * Real.pi : ℝ) • H ((2 * Real.pi) * w) := by rw [← integral_smul]
        _ = ∫ w : ℝ,
              Complex.exp ((↑(2 * Real.pi * (w * x) : ℝ) : ℂ) * Complex.I) *
                𝓕 (F : ℝ → ℂ) w := by
          apply integral_congr_ae
          filter_upwards [] with w
          exact hscaled w
        _ = 𝓕⁻ (𝓕 (F : ℝ → ℂ)) x := hInvIntegral.symm
    calc
      (Ψ y : ℂ) = ψlog x := by simp [ψlog, x, Real.exp_log hy]
      _ = F x := rfl
      _ = 𝓕⁻ (𝓕 (F : ℝ → ℂ)) x := hInv.symm
      _ = ∫ v : ℝ, H v := hInvToIntegral.symm
      _ = ∫ v : ℝ,
            logFourierTransform Ψ v * Complex.exp (Complex.I * v * Real.log y) := by
          simp [H, x]
  · intro N
    obtain ⟨C0, hC0, hC0bound⟩ := (𝓕 F).decay 0 0
    obtain ⟨CN, hCN, hCNbound⟩ := (𝓕 F).decay N 0
    have hsmallBound (w : ℝ) : ‖(𝓕 F) w‖ ≤ C0 := by
      have h := hC0bound w
      simpa using h
    have hpowerBound (w : ℝ) : |w| ^ N * ‖(𝓕 F) w‖ ≤ CN := by
      have h := hCNbound w
      simpa [Real.norm_eq_abs] using h
    let Cw : ℝ := 2 ^ N * max C0 CN
    have hCw : 0 < Cw := by positivity
    have hrapid (w : ℝ) :
        ‖(𝓕 F) w‖ * (1 + |w|) ^ N ≤ Cw := by
      by_cases hw : |w| ≤ 1
      · have hbase : 1 + |w| ≤ 2 := by linarith
        have hpow : (1 + |w|) ^ N ≤ (2 : ℝ) ^ N :=
          pow_le_pow_left₀ (by positivity) hbase N
        calc
          ‖(𝓕 F) w‖ * (1 + |w|) ^ N ≤ C0 * (1 + |w|) ^ N :=
            mul_le_mul_of_nonneg_right (hsmallBound w) (by positivity)
          _ ≤ C0 * (2 : ℝ) ^ N := mul_le_mul_of_nonneg_left hpow (by positivity)
          _ ≤ Cw := by
            dsimp [Cw]
            calc
              C0 * (2 : ℝ) ^ N = (2 : ℝ) ^ N * C0 := by ring
              _ ≤ (2 : ℝ) ^ N * max C0 CN :=
                mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
      · have hw' : 1 ≤ |w| := le_of_not_ge hw
        have hbase : 1 + |w| ≤ 2 * |w| := by linarith
        have hpow : (1 + |w|) ^ N ≤ (2 * |w|) ^ N :=
          pow_le_pow_left₀ (by positivity) hbase N
        calc
          ‖(𝓕 F) w‖ * (1 + |w|) ^ N ≤ ‖(𝓕 F) w‖ * (2 * |w|) ^ N :=
            mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
          _ = (2 : ℝ) ^ N * (|w| ^ N * ‖(𝓕 F) w‖) := by rw [mul_pow]; ring
          _ ≤ (2 : ℝ) ^ N * CN :=
            mul_le_mul_of_nonneg_left (hpowerBound w) (by positivity)
          _ ≤ Cw := by
            dsimp [Cw]
            exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
    let Cbase : ℝ := Cw
    have hCbasePos : 0 < Cbase := hCw
    have hCbase (w : ℝ) : ‖(𝓕 F) w‖ * (1 + |w|) ^ N ≤ Cbase := hrapid w
    let Cfinal : ℝ := (1 / (2 * Real.pi)) * Cbase * (1 + 2 * Real.pi) ^ N
    have hCfinal : 0 < Cfinal := by positivity
    refine ⟨Cfinal, hCfinal, fun v => ?_⟩
    let ξ := v / (2 * Real.pi)
    have hπ : 0 < 2 * Real.pi := by positivity
    have hv : v = (2 * Real.pi) * ξ := by
      dsimp [ξ]
      field_simp [Real.pi_ne_zero]
    have hbase : 1 + |v| ≤ (1 + 2 * Real.pi) * (1 + |ξ|) := by
      rw [hv, abs_mul, abs_of_pos hπ]
      nlinarith [abs_nonneg ξ, Real.pi_pos]
    have hpow : (1 + |v|) ^ N ≤
        (1 + 2 * Real.pi) ^ N * (1 + |ξ|) ^ N := by
      calc
        (1 + |v|) ^ N ≤ ((1 + 2 * Real.pi) * (1 + |ξ|)) ^ N :=
          pow_le_pow_left₀ (by positivity) hbase N
        _ = _ := by rw [mul_pow]
    have hFdecay := hCbase ξ
    have hFscaled : ‖(𝓕 F) ξ‖ * (1 + |v|) ^ N ≤
        Cbase * (1 + 2 * Real.pi) ^ N := by
      calc
        _ ≤ ‖(𝓕 F) ξ‖ * ((1 + 2 * Real.pi) ^ N * (1 + |ξ|) ^ N) :=
          mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
        _ = (‖(𝓕 F) ξ‖ * (1 + |ξ|) ^ N) * (1 + 2 * Real.pi) ^ N := by ring
        _ ≤ Cbase * (1 + 2 * Real.pi) ^ N :=
          mul_le_mul_of_nonneg_right hFdecay (by positivity)
    have hcoef : ‖(1 / (2 * Real.pi : ℝ) : ℂ)‖ = 1 / (2 * Real.pi) := by
      rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hπ]
    have hlog : ‖logFourierTransform Ψ v‖ * (1 + |v|) ^ N ≤ Cfinal := by
      rw [hFT, norm_mul, hcoef]
      calc
        (1 / (2 * Real.pi)) * ‖𝓕 (F : ℝ → ℂ) ξ‖ * (1 + |v|) ^ N =
            (1 / (2 * Real.pi)) * (‖𝓕 (F : ℝ → ℂ) ξ‖ * (1 + |v|) ^ N) := by ring
        _ ≤
          (1 / (2 * Real.pi)) * (Cbase * (1 + 2 * Real.pi) ^ N) :=
            mul_le_mul_of_nonneg_left hFscaled (by positivity)
        _ = Cfinal := by dsimp [Cfinal]; ring
    have hdiv : ‖logFourierTransform Ψ v‖ ≤ Cfinal / (1 + |v|) ^ N :=
      (le_div_iff₀ (by positivity)).2 hlog
    have hrpow : Real.rpow (1 + |v|) (-(N : ℝ)) = ((1 + |v|) ^ N)⁻¹ := by
      change (1 + |v|) ^ (-(N : ℝ)) = ((1 + |v|) ^ N)⁻¹
      calc
        (1 + |v|) ^ (-(N : ℝ)) = ((1 + |v|) ^ (N : ℝ))⁻¹ :=
          Real.rpow_neg (show 0 ≤ 1 + |v| by positivity) (N : ℝ)
        _ = _ := by rw [Real.rpow_natCast]
    simpa [hrpow, div_eq_mul_inv] using hdiv

/-! The following discrete derivative estimate is adapted from
OAI/NumberTheory/EgyptianFractions/DiscreteFirstDerivative.lean (Apache-2.0). Its prebuilt module
is unavailable in the shared checkout, so the small collection of required lemmas is proved here. -/
namespace DerivativeTestProof

open scoped BigOperators

noncomputable def phase (x : ℝ) : ℂ := Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)

noncomputable def phaseWeight (x : ℝ) : ℂ :=
  -(1 : ℂ) / 2 - (Real.cot (Real.pi * x) : ℂ) * Complex.I / 2

lemma phase_eq_additiveCharacter (x : ℝ) :
    phase x = ArtinPrimitiveRoots.TypeII.additiveCharacter x := by
  unfold phase ArtinPrimitiveRoots.TypeII.additiveCharacter
  congr 1
  push_cast
  ring

lemma phase_norm (x : ℝ) : ‖phase x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

lemma phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma cot_antitone_unit {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y < 1) :
    Real.cot (Real.pi * y) ≤ Real.cot (Real.pi * x) := by
  have hpi := Real.pi_pos
  have hxpi : 0 < Real.pi * x := mul_pos hpi hx
  have hypi : 0 < Real.pi * y := by nlinarith
  have hxpi' : Real.pi * x < Real.pi := by nlinarith
  have hypi' : Real.pi * y < Real.pi := by nlinarith
  have hsx := Real.sin_pos_of_pos_of_lt_pi hxpi hxpi'
  have hsy := Real.sin_pos_of_pos_of_lt_pi hypi hypi'
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin]
  apply (div_le_div_iff₀ hsy hsx).2
  have hs : 0 ≤ Real.sin (Real.pi * y - Real.pi * x) := by
    apply Real.sin_nonneg_of_mem_Icc
    constructor <;> nlinarith
  rw [Real.sin_sub] at hs
  nlinarith

lemma sin_pi_lower {β x : ℝ} (hβ : 0 < β) (hlo : β ≤ x) (hhi : x ≤ 1 - β) :
    2 * β ≤ Real.sin (Real.pi * x) := by
  have hp := Real.pi_pos
  by_cases hx : x ≤ 1 / 2
  · have h := Real.mul_le_sin (x := Real.pi * x) (by nlinarith) (by nlinarith)
    have heq : 2 / Real.pi * (Real.pi * x) = 2 * x := by field_simp
    rw [heq] at h
    linarith
  · have h := Real.mul_le_sin (x := Real.pi * (1 - x)) (by nlinarith) (by nlinarith)
    have heq : 2 / Real.pi * (Real.pi * (1 - x)) = 2 * (1 - x) := by field_simp
    rw [heq] at h
    have harg : Real.pi * (1 - x) = Real.pi - Real.pi * x := by ring
    rw [harg, Real.sin_pi_sub] at h
    linarith

lemma abs_cot_pi_le {β x : ℝ} (hβ : 0 < β) (hlo : β ≤ x) (hhi : x ≤ 1 - β) :
    |Real.cot (Real.pi * x)| ≤ 1 / (2 * β) := by
  have hs := sin_pi_lower hβ hlo hhi
  have hsp : 0 < Real.sin (Real.pi * x) := by linarith
  rw [Real.cot_eq_cos_div_sin, abs_div, abs_of_pos hsp]
  exact (div_le_div_of_nonneg_right (Real.abs_cos_le_one _) hsp.le).trans
    (one_div_le_one_div_of_le (by positivity) hs)

lemma phaseWeight_identity {x : ℝ} (hx : 0 < x) (hx' : x < 1) :
    (phase x - 1) * phaseWeight x = 1 := by
  have hs : Real.sin (Real.pi * x) ≠ 0 := ne_of_gt
    (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos]))
  unfold phase phaseWeight
  rw [Complex.exp_ofReal_mul_I]
  rw [show 2 * Real.pi * x = 2 * (Real.pi * x) by ring]
  rw [Real.sin_two_mul, Real.cos_two_mul, Real.cot_eq_cos_div_sin]
  simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_ofNat, Complex.ofReal_div]
  have hsc : (Real.sin (Real.pi * x) : ℂ) ^ 2 +
      (Real.cos (Real.pi * x) : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq (Real.pi * x)
  have hsC : (Real.sin (Real.pi * x) : ℂ) ≠ 0 := by exact_mod_cast hs
  field_simp
  ring_nf
  norm_num only [Complex.ofReal_one, Complex.I_sq]
  linear_combination -2 * (Real.cos (Real.pi * x) : ℂ) * Complex.I * hsc

lemma phaseWeight_norm_le {β x : ℝ} (hβ : 0 < β) (hlo : β ≤ x) (hhi : x ≤ 1 - β) :
    ‖phaseWeight x‖ ≤ 1 / 2 + 1 / (4 * β) := by
  have hc := abs_cot_pi_le hβ hlo hhi
  have hn2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
  calc
    ‖phaseWeight x‖ ≤ ‖-(1 : ℂ) / 2‖ + ‖(Real.cot (Real.pi * x) : ℂ) * Complex.I / 2‖ :=
      norm_sub_le _ _
    _ = 1 / 2 + |Real.cot (Real.pi * x)| / 2 := by
      simp only [norm_div, norm_neg, norm_one, norm_mul, Complex.norm_I,
        Complex.norm_real, Real.norm_eq_abs, hn2, mul_one]
    _ ≤ 1 / 2 + (1 / (2 * β)) / 2 := by gcongr
    _ = 1 / 2 + 1 / (4 * β) := by ring

lemma phaseWeight_difference_norm {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y < 1) :
    ‖phaseWeight x - phaseWeight y‖ =
      (Real.cot (Real.pi * x) - Real.cot (Real.pi * y)) / 2 := by
  have hc := cot_antitone_unit hx hxy hy
  have heq : phaseWeight x - phaseWeight y =
      (((Real.cot (Real.pi * x) - Real.cot (Real.pi * y)) / 2 : ℝ) : ℂ) * (-Complex.I) := by
    unfold phaseWeight
    push_cast
    ring
  rw [heq, norm_mul, norm_neg, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by linarith)]

lemma phase_step_weight (f : ℕ → ℝ) (i : ℕ)
    (hlo : 0 < f (i + 1) - f i) (hhi : f (i + 1) - f i < 1) :
    (phase (f (i + 1)) - phase (f i)) * phaseWeight (f (i + 1) - f i) = phase (f i) := by
  have heq : phase (f (i + 1)) = phase (f i) * phase (f (i + 1) - f i) := by
    rw [← phase_add]
    congr 1
    ring
  rw [heq]
  calc
    (phase (f i) * phase (f (i + 1) - f i) - phase (f i)) *
        phaseWeight (f (i + 1) - f i) =
      phase (f i) * ((phase (f (i + 1) - f i) - 1) *
        phaseWeight (f (i + 1) - f i)) := by ring
    _ = phase (f i) := by rw [phaseWeight_identity hlo hhi, mul_one]

lemma weighted_telescope (z w : ℕ → ℂ) (N : ℕ)
    (hstep : ∀ i < N, (z (i + 1) - z i) * w i = z i) :
    (∑ i ∈ Finset.range N, z i) = z N * w N - z 0 * w 0 +
      ∑ i ∈ Finset.range N, z (i + 1) * (w i - w (i + 1)) := by
  calc
    (∑ i ∈ Finset.range N, z i) =
        ∑ i ∈ Finset.range N,
          ((z (i + 1) * w (i + 1) - z i * w i) + z (i + 1) * (w i - w (i + 1))) := by
      apply Finset.sum_congr rfl
      intro i hi
      have h := hstep i (Finset.mem_range.mp hi)
      linear_combination -h
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_range_sub (fun i => z i * w i)]

theorem first_derivative_sum_bound_core (f : ℕ → ℝ) (N : ℕ) (β : ℝ) (hβ : 0 < β)
    (hlo : ∀ i ≤ N, β ≤ f (i + 1) - f i)
    (hhi : ∀ i ≤ N, f (i + 1) - f i ≤ 1 - β)
    (hmono : MonotoneOn (fun i => f (i + 1) - f i) (Set.Iic N)) :
    ‖∑ i ∈ Finset.range N, phase (f i)‖ ≤ 2 / β := by
  let d : ℕ → ℝ := fun i => f (i + 1) - f i
  let w : ℕ → ℂ := fun i => phaseWeight (d i)
  have hdlo : ∀ i ≤ N, 0 < d i := fun i hi => lt_of_lt_of_le hβ (hlo i hi)
  have hdhi : ∀ i ≤ N, d i < 1 := by
    intro i hi
    have := hhi i hi
    dsimp [d]
    linarith
  have htel := weighted_telescope (fun i => phase (f i)) w N (by
    intro i hi
    exact phase_step_weight f i (hdlo i hi.le) (hdhi i hi.le))
  have hvariation : (∑ i ∈ Finset.range N, ‖w i - w (i + 1)‖) =
      (Real.cot (Real.pi * d 0) - Real.cot (Real.pi * d N)) / 2 := by
    calc
      (∑ i ∈ Finset.range N, ‖w i - w (i + 1)‖) =
          ∑ i ∈ Finset.range N,
            (Real.cot (Real.pi * d i) - Real.cot (Real.pi * d (i + 1))) / 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        have hiN : i < N := Finset.mem_range.mp hi
        exact phaseWeight_difference_norm (hdlo i hiN.le)
          (hmono (show i ≤ N from hiN.le) (show i + 1 ≤ N by omega) (by omega))
          (hdhi (i + 1) (by omega))
      _ = _ := by rw [← Finset.sum_div, Finset.sum_range_sub']
  have hc0 := abs_cot_pi_le hβ (hlo 0 (Nat.zero_le N)) (hhi 0 (Nat.zero_le N))
  have hcN := abs_cot_pi_le hβ (hlo N le_rfl) (hhi N le_rfl)
  have hvbound : (∑ i ∈ Finset.range N, ‖w i - w (i + 1)‖) ≤ 1 / (2 * β) := by
    rw [hvariation]
    have h0 := (abs_le.mp hc0).2
    have hN := (abs_le.mp hcN).1
    change Real.cot (Real.pi * d 0) ≤ _ at h0
    change _ ≤ Real.cot (Real.pi * d N) at hN
    linarith
  have hw0 := phaseWeight_norm_le hβ (hlo 0 (Nat.zero_le N)) (hhi 0 (Nat.zero_le N))
  have hwN := phaseWeight_norm_le hβ (hlo N le_rfl) (hhi N le_rfl)
  have hsum : ‖∑ i ∈ Finset.range N, phase (f (i + 1)) * (w i - w (i + 1))‖ ≤
      ∑ i ∈ Finset.range N, ‖w i - w (i + 1)‖ := by
    calc
      _ ≤ ∑ i ∈ Finset.range N, ‖phase (f (i + 1)) * (w i - w (i + 1))‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_mul, phase_norm, one_mul]
  have hβle : β ≤ 1 := by
    have := hlo 0 (Nat.zero_le N)
    have := hhi 0 (Nat.zero_le N)
    linarith
  have hinv : 1 ≤ 1 / β := (le_div_iff₀ hβ).2 (by simpa using hβle)
  rw [htel]
  calc
    _ ≤ ‖phase (f N) * w N - phase (f 0) * w 0‖ +
        ‖∑ i ∈ Finset.range N, phase (f (i + 1)) * (w i - w (i + 1))‖ := norm_add_le _ _
    _ ≤ (‖phase (f N) * w N‖ + ‖phase (f 0) * w 0‖) +
        ∑ i ∈ Finset.range N, ‖w i - w (i + 1)‖ := add_le_add (norm_sub_le _ _) hsum
    _ = (‖w N‖ + ‖w 0‖) + ∑ i ∈ Finset.range N, ‖w i - w (i + 1)‖ := by
      simp only [norm_mul, phase_norm, one_mul]
    _ ≤ (1 / 2 + 1 / (4 * β)) + (1 / 2 + 1 / (4 * β)) + 1 / (2 * β) :=
      add_le_add (add_le_add hwN hw0) hvbound
    _ = 1 + 1 / β := by ring
    _ ≤ 1 / β + 1 / β := by simpa [add_comm] using add_le_add_right hinv (1 / β)
    _ = 2 / β := by ring

end DerivativeTestProof

/-- `ext:derivative-test` — PP `01-preliminaries.tex:88-106`, Proposition 2.3; matching OAI
`first_derivative_sum_bound` (`DiscreteFirstDerivative.lean:147-151`). -/
theorem derivative_test (f : ℕ → ℝ) (N : ℕ) (β : ℝ) (hβ : 0 < β)
    (hlo : ∀ i < N, β ≤ f (i + 1) - f i)
    (hhi : ∀ i < N, f (i + 1) - f i ≤ 1 - β)
    (hmono : MonotoneOn (fun i => f (i + 1) - f i) (Set.Icc 0 N)) :
    ‖∑ i ∈ Finset.range N, additiveCharacter (f i)‖ ≤ 2 / β := by
  by_cases hN : N = 0
  · subst N
    simp
    positivity
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  let g : ℕ → ℝ := Function.update f (N + 1) (f N + (f N - f (N - 1)))
  have hg_le (i : ℕ) (hi : i ≤ N) : g i = f i := by
    have hne : i ≠ N + 1 := by omega
    simp [g, hne]
  have hg_step (i : ℕ) (hi : i < N) : g (i + 1) - g i = f (i + 1) - f i := by
    rw [hg_le (i + 1) (Nat.succ_le_of_lt hi), hg_le i hi.le]
  have hg_last : g (N + 1) - g N = f N - f (N - 1) := by
    have hnew : g (N + 1) = f N + (f N - f (N - 1)) := by simp [g]
    rw [hnew, hg_le N le_rfl]
    ring
  have hmonoBase : MonotoneOn (fun i => f (i + 1) - f i) (Set.Iic N) := by
    intro i hi j hj hij
    apply hmono <;> simp_all
  have hlo' : ∀ i ≤ N, β ≤ g (i + 1) - g i := by
    intro i hi
    by_cases hil : i < N
    · rw [hg_step i hil]
      exact hlo i hil
    · have hiN : i = N := by omega
      subst i
      rw [hg_last]
      have hprev : N - 1 < N := by omega
      have h := hlo (N - 1) hprev
      have heq : N - 1 + 1 = N := by omega
      simpa [heq] using h
  have hhi' : ∀ i ≤ N, g (i + 1) - g i ≤ 1 - β := by
    intro i hi
    by_cases hil : i < N
    · rw [hg_step i hil]
      exact hhi i hil
    · have hiN : i = N := by omega
      subst i
      rw [hg_last]
      have hprev : N - 1 < N := by omega
      have h := hhi (N - 1) hprev
      have heq : N - 1 + 1 = N := by omega
      simpa [heq] using h
  have hmono' : MonotoneOn (fun i => g (i + 1) - g i) (Set.Iic N) := by
    intro i hi j hj hij
    have hiN : i ≤ N := by simpa using hi
    have hjN : j ≤ N := by simpa using hj
    by_cases hjlt : j < N
    · have hilt : i < N := lt_of_le_of_lt hij hjlt
      change g (i + 1) - g i ≤ g (j + 1) - g j
      rw [hg_step i hilt, hg_step j hjlt]
      exact hmonoBase hi hj hij
    · have hjEq : j = N := by omega
      subst j
      by_cases hilt : i < N
      · change g (i + 1) - g i ≤ g (N + 1) - g N
        rw [hg_step i hilt, hg_last]
        have hprev : N - 1 < N := by omega
        have hcmp : i ≤ N - 1 := Nat.le_sub_one_of_lt hilt
        have h := hmonoBase (show i ∈ Set.Iic N from hi)
          (show N - 1 ∈ Set.Iic N by exact Nat.sub_le N 1) hcmp
        have heq : N - 1 + 1 = N := by omega
        simpa [heq] using h
      · have hiEq : i = N := by omega
        subst i
        rfl
  have hsum :
      (∑ i ∈ Finset.range N, DerivativeTestProof.phase (g i)) =
        ∑ i ∈ Finset.range N, additiveCharacter (f i) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hil : i < N := Finset.mem_range.mp hi
    rw [hg_le i hil.le, DerivativeTestProof.phase_eq_additiveCharacter]
  rw [← hsum]
  exact DerivativeTestProof.first_derivative_sum_bound_core g N β hβ hlo' hhi' hmono'

/-- `ext:pnt` — PD Lemma 2.1 and 11-sieve.tex:223-226; matching PNT+ `pi_asymp`
(`Consequences.lean:786`). -/
theorem pnt :
    ∀ ε : ℝ, 0 < ε → ∃ y₀ : ℝ, 2 ≤ y₀ ∧
      ∀ y : ℝ, y₀ ≤ y →
        |primeIntervalCount y (2 * y) - y / Real.log y| ≤ ε * y / Real.log y := by
  sorry

/-- `ext:dirichlet-L` — PP `02-long-prime.tex:312-323`; matching Mathlib
`DirichletCharacter.LFunction` and `differentiable_LFunction` (`DirichletContinuation.lean:98`).
Correction 9 from review lane `rev-b` records meromorphic continuation for all characters. -/
theorem dirichlet_L (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) :
    (∀ s : ℂ, 1 < s.re →
      DirichletCharacter.LFunction χ s = LSeries (χ ·) s) ∧
    (∀ s : ℂ, MeromorphicAt (DirichletCharacter.LFunction χ) s) ∧
    (χ ≠ 1 → Differentiable ℂ (DirichletCharacter.LFunction χ)) := by
  sorry

private theorem ncard_zero_le_divisor (g : ℂ → ℂ) (c : ℂ) (r R : ℝ)
    (hr : 0 < r) (hR : r < R)
    (hg : AnalyticOnNhd ℂ g (Metric.closedBall c R)) (hgc : g c ≠ 0) :
    Set.ncard {z : ℂ | z ∈ Metric.closedBall c r ∧ g z = 0} ≤
      ∑ᶠ z, (MeromorphicOn.divisor g (Metric.closedBall c r) z : ℝ) := by
  classical
  let S : Set ℂ := {z : ℂ | z ∈ Metric.closedBall c r ∧ g z = 0}
  let D := MeromorphicOn.divisor g (Metric.closedBall c r)
  have hsmall : AnalyticOnNhd ℂ g (Metric.closedBall c r) :=
    hg.mono (Metric.closedBall_subset_closedBall hR.le)
  have hcenter : analyticOrderAt g c = 0 :=
    (hsmall c (by simpa using hr.le)).analyticOrderAt_eq_zero.mpr hgc
  have hcenterNeTop : analyticOrderAt g c ≠ ⊤ := by simp [hcenter]
  have hDpos (z : ℂ) (hz : z ∈ S) : (1 : ℤ) ≤ D z := by
    have hzsmall : z ∈ Metric.closedBall c r := hz.1
    have horderNe0 : analyticOrderAt g z ≠ 0 :=
      (hsmall z hzsmall).analyticOrderAt_ne_zero.mpr hz.2
    have hpre : IsPreconnected (Metric.closedBall c r) := by
      simpa [abs_of_pos hr] using (convex_closedBall c |r|).isPreconnected
    have horderNeTop : analyticOrderAt g z ≠ ⊤ :=
      hsmall.analyticOrderAt_ne_top_of_isPreconnected
        hpre (by simpa using hr.le) hzsmall hcenterNeTop
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp horderNeTop
    have hkpos : 1 ≤ k := by
      have horderPos : (1 : ℕ∞) ≤ analyticOrderAt g z :=
        Order.one_le_iff_ne_zero.mpr horderNe0
      have hkpos' : (1 : ℕ∞) ≤ (k : ℕ∞) := by
        calc
          (1 : ℕ∞) ≤ analyticOrderAt g z := horderPos
          _ = (k : ℕ∞) := hk.symm
      exact_mod_cast hkpos'
    rw [hsmall.meromorphicOn.divisor_apply hzsmall,
      (hsmall z hzsmall).meromorphicOrderAt_eq]
    have hkz : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hkpos
    have hmap : (1 : WithTop ℤ) ≤
        (analyticOrderAt g z).map (fun n : ℕ => (n : ℤ)) := by
      rw [← hk]
      simp only [ENat.map_natCast]
      exact WithTop.coe_le_coe.mpr hkz
    have hmapNeTop : (analyticOrderAt g z).map (fun n : ℕ => (n : ℤ)) ≠ ⊤ := by
      rw [← hk]
      simp only [ENat.map_natCast]
      simp
    exact WithTop.untop₀_le_untop₀ hmapNeTop hmap
  have hSsub : S ⊆ D.support := by
    intro z hz
    rw [Function.mem_support]
    exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℤ) < 1) (hDpos z hz))
  have hcompact : IsCompact (Metric.closedBall c r) := by
    simpa [abs_of_pos hr] using isCompact_closedBall c |r|
  have hDfinite := D.finiteSupport hcompact
  have hSfinite : S.Finite := hDfinite.subset hSsub
  have hSsum :
      (hSfinite.toFinset.card : ℝ) ≤
        ∑ z ∈ hSfinite.toFinset, (D z : ℝ) := by
    have h := Finset.card_nsmul_le_sum hSfinite.toFinset (fun z => (D z : ℝ))
      (1 : ℝ) (by
        intro z hz
        exact_mod_cast hDpos z ((Set.Finite.mem_toFinset hSfinite).1 hz))
    simpa using h
  have hSub : hSfinite.toFinset ⊆ hDfinite.toFinset := by
    intro z hz
    exact (Set.Finite.mem_toFinset hDfinite).2
      (hSsub ((Set.Finite.mem_toFinset hSfinite).1 hz))
  have hcastSupport : Function.support (fun z : ℂ => (D z : ℝ)) ⊆ hDfinite.toFinset := by
    intro z hz
    have hzcast : (D z : ℝ) ≠ 0 := by
      simpa only [Function.mem_support] using hz
    have hzD : D z ≠ 0 := by
      intro hzero
      apply hzcast
      simp [hzero]
    exact (Set.Finite.mem_toFinset hDfinite).2 hzD
  have hDnonneg (z : ℂ) : (0 : ℝ) ≤ (D z : ℝ) := by
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hsmall z
  calc
    (Set.ncard S : ℝ) = (hSfinite.toFinset.card : ℝ) := by
      exact_mod_cast Set.ncard_eq_toFinset_card S hSfinite
    _ ≤ ∑ z ∈ hSfinite.toFinset, (D z : ℝ) := hSsum
    _ ≤ ∑ z ∈ hDfinite.toFinset, (D z : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hSub (fun z hz _ => hDnonneg z)
    _ = ∑ᶠ z, (D z : ℝ) := (finsum_eq_sum_of_support_subset _ hcastSupport).symm

/-- `ext:jensen` — PP `02-long-prime.tex:392-394`; matching Mathlib
`AnalyticOnNhd.sum_divisor_le` (`JensenFormula.lean:389-392`). -/
theorem jensen (f : ℂ → ℂ) (c : ℂ) (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R)) (hfc : f c ≠ 0) :
    Set.ncard {z : ℂ | z ∈ Metric.closedBall c r ∧ f z = 0} ≤
      (Real.log (⨆ z ∈ Metric.closedBall c R, ‖f z‖) - Real.log ‖f c‖) /
        Real.log (R / r) := by
  classical
  have hRpos : 0 < R := hr.trans hR
  have hboundSet : BddAbove
      (⋃ z : ℂ, Set.range (fun _ : z ∈ Metric.closedBall c R => ‖f z‖)) := by
    have hset : (⋃ z : ℂ, Set.range (fun _ : z ∈ Metric.closedBall c R => ‖f z‖)) =
        (fun z => ‖f z‖) '' Metric.closedBall c R := by
      ext x
      simp [Set.mem_iUnion, Set.mem_range, Set.mem_image, eq_comm]
    rw [hset]
    have hcompactR : IsCompact (Metric.closedBall c R) := by
      simpa [abs_of_pos hRpos] using isCompact_closedBall c |R|
    exact hcompactR.bddAbove_image hf.continuousOn.norm
  let Smax : ℝ := ⨆ z ∈ Metric.closedBall c R, ‖f z‖
  have hSmaxFc : ‖f c‖ ≤ Smax := by
    have hcball : c ∈ Metric.closedBall c R := by simpa using hRpos.le
    exact le_ciSup₂ hboundSet c hcball
  have hnormFc : 0 < ‖f c‖ := norm_pos_iff.mpr hfc
  have hSmaxPos : 0 < Smax := lt_of_lt_of_le hnormFc hSmaxFc
  let M : ℝ := Smax / ‖f c‖
  have hM : 1 ≤ M := (le_div_iff₀ hnormFc).2 (by simpa using hSmaxFc)
  let g : ℂ → ℂ := fun z => f z / f c
  have hg : AnalyticOnNhd ℂ g (Metric.closedBall c R) := by
    exact hf.div_const
  have hgc : g c = 1 := by
    simp [g, hfc]
  have hgc0 : g c ≠ 0 := by rw [hgc]; norm_num
  have hgBound : ∀ z ∈ Metric.sphere c R, ‖g z‖ ≤ M := by
    intro z hz
    have hzle : ‖f z‖ ≤ Smax := le_ciSup₂ hboundSet z (Metric.sphere_subset_closedBall hz)
    dsimp [g, M, Smax]
    rw [norm_div]
    exact div_le_div_of_nonneg_right hzle (norm_nonneg _)
  have hgAbs : AnalyticOnNhd ℂ g (Metric.closedBall c |R|) := by
    simpa [abs_of_pos hRpos] using hg
  have hgBoundAbs : ∀ z ∈ Metric.sphere c |R|, ‖g z‖ ≤ M := by
    simpa [abs_of_pos hRpos] using hgBound
  have hJensen := AnalyticOnNhd.sum_divisor_le (c := c) (r := r) (R := R) (M := M) (f := g)
    (by simpa [abs_of_pos hr] using hr)
    (by simpa [abs_of_pos hr, abs_of_pos hRpos] using hR)
    hM hgAbs hgc0 hgBoundAbs
  have hzeroSet :
      {z : ℂ | z ∈ Metric.closedBall c r ∧ g z = 0} =
        {z : ℂ | z ∈ Metric.closedBall c r ∧ f z = 0} := by
    ext z
    simp [g, hfc]
  rw [← hzeroSet]
  have hcountFinal :
      Set.ncard {z : ℂ | z ∈ Metric.closedBall c r ∧ g z = 0} ≤
        Real.log (M / ‖g c‖) / Real.log (R / r) := by
    have hcount := ncard_zero_le_divisor g c r R hr hR hg hgc0
    have hcount' :
        Set.ncard {z : ℂ | z ∈ Metric.closedBall c r ∧ g z = 0} ≤
          ∑ᶠ z, (MeromorphicOn.divisor g (Metric.closedBall c |r|) z : ℝ) := by
      calc
        Set.ncard {z : ℂ | z ∈ Metric.closedBall c r ∧ g z = 0} ≤
            ∑ᶠ z, (MeromorphicOn.divisor g (Metric.closedBall c r) z : ℝ) := hcount
        _ = ∑ᶠ z, (MeromorphicOn.divisor g (Metric.closedBall c |r|) z : ℝ) := by
          apply finsum_congr
          intro z
          rw [abs_of_pos hr]
    let D' := MeromorphicOn.divisor g (Metric.closedBall c |r|)
    have hDfinite' := D'.finiteSupport (isCompact_closedBall c |r|)
    have hcount'' :
        (Set.ncard {z : ℂ | z ∈ Metric.closedBall c r ∧ g z = 0} : ℝ) ≤
          (∑ᶠ z, D' z : ℤ) := by
      calc
        _ ≤ ∑ᶠ z, (D' z : ℝ) := hcount'
        _ = (∑ᶠ z, D' z : ℤ) := (map_finsum (Int.castRingHom ℝ) hDfinite').symm
    exact hcount''.trans hJensen
  calc
    Set.ncard {z : ℂ | z ∈ Metric.closedBall c r ∧ g z = 0} ≤
        Real.log (M / ‖g c‖) / Real.log (R / r) := hcountFinal
    _ = (Real.log Smax - Real.log ‖f c‖) / Real.log (R / r) := by
      rw [hgc, norm_one, div_one]
      dsimp [M]
      rw [Real.log_div hSmaxPos.ne' hnormFc.ne']

end ArtinPrimitiveRoots.Ext.TypeIIInputs
