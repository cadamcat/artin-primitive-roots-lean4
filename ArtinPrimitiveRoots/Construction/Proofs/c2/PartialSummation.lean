import ArtinPrimitiveRoots.Construction.Defs
import ArtinPrimitiveRoots.Ext.TypeIIInputs
import Mathlib.NumberTheory.AbelSummation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace ArtinPrimitiveRoots.Construction.ProofsC2

open ArtinPrimitiveRoots.Ext.TypeIIInputs
open ArtinPrimitiveRoots.TypeII
open Finset MeasureTheory Filter
open scoped Topology

noncomputable def partialCoefficientSum (c : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n

noncomputable def progressionClassIndicator (q v n : ℕ) : ℝ :=
  if n.Prime ∧ (n : ZMod q) = (v : ZMod q) then 1 else 0

noncomputable def smoothProgressionFunction (x : ℝ) (c r : ℕ)
    (Ψ : ℝ → ℝ) (t : ℝ) : ℝ :=
  Ψ ((((c * r : ℕ) : ℝ) * t + 1) / x)

theorem smoothProgression_hasDerivAt
    (x : ℝ) (c r : ℕ) (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ ⊤ Ψ)
    (hx : x ≠ 0) (t : ℝ) :
    HasDerivAt (smoothProgressionFunction x c r Ψ)
      (deriv Ψ ((((c * r : ℕ) : ℝ) * t + 1) / x) *
        (((c * r : ℕ) : ℝ) / x)) t := by
  let cr : ℝ := ((c * r : ℕ) : ℝ)
  have hlin : HasDerivAt (fun s : ℝ => (cr * s + 1) / x) (cr / x) t := by
    convert (((hasDerivAt_id t).const_mul cr).add_const 1).div_const x using 1 <;>
      simp [cr] <;> ring
  have houter : HasDerivAt Ψ (deriv Ψ ((cr * t + 1) / x)) ((cr * t + 1) / x) :=
    (hΨ.differentiable (by simp) ((cr * t + 1) / x)).hasDerivAt
  have hcomp := houter.comp t hlin
  have hfun : smoothProgressionFunction x c r Ψ =
      fun s => Ψ ((cr * s + 1) / x) := by
    funext s
    simp [smoothProgressionFunction, cr]
  rw [hfun]
  change HasDerivAt (Ψ ∘ fun s => (cr * s + 1) / x)
    (deriv Ψ ((cr * t + 1) / x) * (cr / x)) t
  exact hcomp

theorem zmod_inv_eq_unit_inv {N : ℕ} {z : ZMod N} (hz : IsUnit z) :
    z⁻¹ = ((hz.unit⁻¹ : Units (ZMod N)) : ZMod N) := by
  have hv : (hz.unit : ZMod N) = z := hz.unit_spec
  have hi := congrArg (fun w : ZMod N => w⁻¹) hv
  rw [ZMod.inv_coe_unit] at hi
  exact hi.symm

theorem partialClassCount (q v : ℕ) (y : ℝ) :
    partialCoefficientSum (progressionClassIndicator q v) y =
      (((primesUpTo y).filter
        (fun n : ℕ => (n : ZMod q) = (v : ZMod q))).card : ℝ) := by
  classical
  unfold partialCoefficientSum progressionClassIndicator
  rw [Finset.sum_boole]
  have hfilter :
      (Finset.Icc 0 ⌊y⌋₊).filter
        (fun n : ℕ => n.Prime ∧ (n : ZMod q) = (v : ZMod q)) =
      (primesUpTo y).filter (fun n : ℕ => (n : ZMod q) = (v : ZMod q)) := by
    ext n
    simp [primesUpTo, and_assoc]
  exact_mod_cast congrArg Finset.card hfilter

theorem sum_filter_eq_sum_indicator
    (S T : Finset ℕ) (P Q : ℕ → Prop) (f : ℕ → ℝ)
    [DecidablePred P] [DecidablePred Q]
    (hTS : T ⊆ S)
    (hSupport : ∀ n ∈ S, n ∉ T → f n = 0)
    (hPQ : ∀ n ∈ S, f n ≠ 0 → (P n ↔ Q n)) :
    (∑ n ∈ S.filter P, f n) = ∑ n ∈ T.filter Q, f n := by
  classical
  rw [Finset.sum_filter]
  calc
    (∑ n ∈ S, if P n then f n else 0) =
        ∑ n ∈ S, if n ∈ T ∧ Q n then f n else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hfn : f n = 0
      · simp [hfn]
      · have hnt : n ∈ T := by
          by_contra hnt
          exact hfn (hSupport n hn hnt)
        have hiff := hPQ n hn hfn
        by_cases hp : P n
        · have hq : Q n := hiff.mp hp
          simp [hp, hnt, hq]
        · have hq : ¬ Q n := fun hq => hp (hiff.mpr hq)
          simp [hp, hnt, hq]
    _ = ∑ n ∈ S, if n ∈ T ∧ Q n then f n else 0 := rfl
    _ = ∑ n ∈ T, if n ∈ T ∧ Q n then f n else 0 := by
      symm
      apply Finset.sum_subset hTS
      intro n hnS hnT
      simp [hnT]
    _ = ∑ n ∈ T, if Q n then f n else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      simp [hn]
    _ = ∑ n ∈ T.filter Q, f n := by rw [Finset.sum_filter]

theorem progressionPrimeSum_eq_crt_sum
    (x : ℝ) (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ)
    (r ℓ q v : ℕ) (T : Finset ℕ)
    (hT : T ⊆ Finset.range (⌊2 * x⌋₊ + 1))
    (hSupport : ∀ n : ℕ, smoothProgressionFunction x c r Ψ (n : ℝ) ≠ 0 → n ∈ T)
    (hCut : ∀ n : ℕ, smoothProgressionFunction x c r Ψ (n : ℝ) ≠ 0 →
      Real.rpow x (9 / 10 : ℝ) < (n : ℝ))
    (hClass : ∀ n : ℕ,
      ((((c * r * n + 1 : ℕ) : ℤ) ≡ u [ZMOD M] ∧ ℓ ∣ c * r * n + 1) ↔
        (n : ZMod q) = (v : ZMod q))) :
    progressionPrimeSum x M c u Ψ r ℓ =
      ∑ n ∈ T,
        smoothProgressionFunction x c r Ψ (n : ℝ) * progressionClassIndicator q v n := by
  classical
  let S := Finset.range (⌊2 * x⌋₊ + 1)
  let P : ℕ → Prop := fun n =>
    n.Prime ∧ Real.rpow x (9 / 10 : ℝ) < (n : ℝ) ∧
      (((c * r * n + 1 : ℕ) : ℤ) ≡ u [ZMOD M] ∧ ℓ ∣ c * r * n + 1)
  let Q : ℕ → Prop := fun n => n.Prime ∧ (n : ZMod q) = (v : ZMod q)
  let f : ℕ → ℝ := fun n => smoothProgressionFunction x c r Ψ (n : ℝ)
  letI : DecidablePred P := fun n => by dsimp [P]; infer_instance
  letI : DecidablePred Q := fun n => by dsimp [Q]; infer_instance
  have hPQ (n : ℕ) (_hn : n ∈ S) (hfn : f n ≠ 0) : P n ↔ Q n := by
    have hcut := hCut n (by simpa [f] using hfn)
    have hclass := hClass n
    constructor
    · rintro ⟨hp, ⟨_, hpd⟩⟩
      exact ⟨hp, hclass.mp hpd⟩
    · rintro ⟨hp, hres⟩
      exact ⟨hp, hcut, hclass.mpr hres⟩
  have hfinite := sum_filter_eq_sum_indicator S T P Q f hT
    (by
      intro n hn hnot
      by_contra hfn
      exact hnot (hSupport n (by simpa [f] using hfn)))
    hPQ
  have hleft : progressionPrimeSum x M c u Ψ r ℓ = ∑ n ∈ S.filter P, f n := by
    have hS :
        (Finset.range (⌊2 * x⌋₊ + 1)).filter
            (fun n : ℕ => n.Prime ∧ Real.rpow x (9 / 10 : ℝ) < (n : ℝ) ∧
              (((c * r * n + 1 : ℕ) : ℤ) ≡ u [ZMOD M] ∧ ℓ ∣ c * r * n + 1)) =
          S.filter P := by
      ext n
      simp [S, P]
    unfold progressionPrimeSum
    rw [hS]
    apply Finset.sum_congr rfl
    intro n hn
    simp [f, smoothProgressionFunction, Nat.cast_mul, Nat.cast_add, mul_assoc]
  calc
    _ = _ := hleft
    _ = ∑ n ∈ T.filter Q, f n := hfinite
    _ = _ := by
      simp [Finset.sum_filter, Q, f, progressionClassIndicator, mul_comm]

/-- The smooth prime-class sum is unchanged when restricted to its support interval. -/
theorem sum_range_eq_sum_Ioc_of_support
    (x a b : ℝ) (f : ℝ → ℝ) (g : ℕ → ℝ)
    (hab : a ≤ b) (hfloor : ⌊b⌋₊ ≤ ⌊2 * x⌋₊)
    (hsupport : ∀ n : ℕ, f (n : ℝ) ≠ 0 →
      n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊) :
    (∑ n ∈ Finset.range (⌊2 * x⌋₊ + 1), f (n : ℝ) * g n) =
      ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f (n : ℝ) * g n := by
  classical
  let S := Finset.range (⌊2 * x⌋₊ + 1)
  let T := Finset.Ioc ⌊a⌋₊ ⌊b⌋₊
  have hTS : T ⊆ S := by
    intro n hn
    have hnB := (Finset.mem_Ioc.mp hn).2
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (le_trans hnB hfloor))
  calc
    (∑ n ∈ S, f (n : ℝ) * g n) = ∑ n ∈ T, f (n : ℝ) * g n := by
      symm
      apply Finset.sum_subset hTS
      intro n hnS hnT
      have hnzero : f (n : ℝ) = 0 := by
        by_contra hne
        exact hnT (hsupport n hne)
      simp [hnzero]
    _ = _ := rfl

theorem smoothProgression_integral_eq_main
    (x : ℝ) (c r : ℕ) (Ψ : ℝ → ℝ)
    (hx : 0 < x) (hcr : 0 < ((c * r : ℕ) : ℝ)) :
    (∫ t in (x - 1) / ((c * r : ℕ) : ℝ)..(2 * x - 1) / ((c * r : ℕ) : ℝ),
      smoothProgressionFunction x c r Ψ t / Real.log t) =
      smoothedMainTerm x c r Ψ := by
  let cr : ℝ := ((c * r : ℕ) : ℝ)
  let lam : ℝ := cr / x
  let delta : ℝ := 1 / x
  let a : ℝ := (x - 1) / cr
  let b : ℝ := (2 * x - 1) / cr
  let g : ℝ → ℝ := fun y => Ψ y / Real.log ((x * y - 1) / cr)
  have hlam : lam ≠ 0 := div_ne_zero hcr.ne' hx.ne'
  have harg₁ (t : ℝ) : (cr * t + 1) / x = lam * t + delta := by
    dsimp [lam, delta]
    ring
  have harg₂ (t : ℝ) :
      (x * (lam * t + delta) - 1) / cr = t := by
    calc
      (x * (lam * t + delta) - 1) / cr = (cr * t) / cr := by
        dsimp [lam, delta]
        field_simp [hx.ne', hcr.ne']
        ring
      _ = t := by exact mul_div_cancel_left₀ t hcr.ne'
  have hfun (t : ℝ) :
      smoothProgressionFunction x c r Ψ t / Real.log t = g (lam * t + delta) := by
    dsimp [smoothProgressionFunction, g, cr]
    rw [harg₁, harg₂]
  have ha : lam * a + delta = 1 := by
    dsimp [lam, a, delta, cr]
    field_simp [hx.ne', hcr.ne']
    ring
  have hb : lam * b + delta = 2 := by
    dsimp [lam, b, delta, cr]
    field_simp [hx.ne', hcr.ne']
    ring
  have hcoef : lam⁻¹ = x / cr := by
    dsimp [lam]
    field_simp [hx.ne', hcr.ne']
  calc
    _ = ∫ t in a..b, g (lam * t + delta) := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact hfun t
    _ = lam⁻¹ * (∫ y in (1 : ℝ)..2, g y) := by
      rw [intervalIntegral.integral_comp_mul_add g hlam delta, ha, hb]
      simp [smul_eq_mul]
    _ = smoothedMainTerm x c r Ψ := by
      rw [hcoef, smoothedMainTerm]

theorem smoothProgression_support_bounds
    (x cr cutoff a b : ℝ) (Ψ : ℝ → ℝ) (n : ℕ)
    (hx : 0 < x) (hcr : 0 < cr) (ha0 : 0 ≤ a) (hcut : cutoff ≤ a)
    (ha : a = (x - 1) / cr) (hb : b = (2 * x - 1) / cr)
    (hΨsupp : Function.support Ψ ⊆ Set.Ioo 1 2)
    (hn : Ψ ((cr * (n : ℝ) + 1) / x) ≠ 0) :
    cutoff < (n : ℝ) ∧ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ := by
  have hy : (cr * (n : ℝ) + 1) / x ∈ Set.Ioo 1 2 :=
    hΨsupp (Function.mem_support.mpr hn)
  have hlow : a < (n : ℝ) := by
    rw [ha]
    apply (div_lt_iff₀ hcr).2
    have h := (lt_div_iff₀ hx).1 hy.1
    linarith
  have hupp : (n : ℝ) < b := by
    rw [hb]
    apply (lt_div_iff₀ hcr).2
    have h := (div_lt_iff₀ hx).1 hy.2
    linarith
  constructor
  · exact lt_of_le_of_lt hcut hlow
  · exact Finset.mem_Ioc.mpr ⟨(Nat.floor_lt ha0).2 hlow, Nat.le_floor hupp.le⟩

/-- Abel summation against a differentiable cumulative main term. -/
theorem smoothCountError_of_endpointControl
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (c : ℕ → ℝ) (α E : ℝ) (Li f : ℝ → ℝ)
    (hf : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hf_int : IntegrableOn (deriv f) (Set.Icc a b))
    (hli : ∀ t ∈ Set.Icc a b, HasDerivAt Li (1 / Real.log t) t)
    (hli_int : IntervalIntegrable (fun t => 1 / Real.log t) volume a b)
    (hfli_int : IntervalIntegrable (fun t => deriv f t * Li t) volume a b)
    (hflog_int : IntervalIntegrable (fun t => f t / Real.log t) volume a b)
    (hcount : ∀ t ∈ Set.Icc a b,
      |partialCoefficientSum c t - α * Li t| ≤ E)
    (hfa : f a = 0) (hfb : f b = 0) :
    |(∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f n * c n) -
        α * (∫ t in a..b, f t / Real.log t)| ≤
      E * (∫ t in a..b, |deriv f t|) := by
  let P : ℝ → ℝ := partialCoefficientSum c
  have hP_int : IntervalIntegrable (fun t => deriv f t * P t) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact integrableOn_mul_sum_Icc c ha hf_int
  have habel := sum_mul_eq_sub_sub_integral_mul c ha hab hf hf_int
  have habel' : (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f n * c n) =
      -(∫ t in a..b, deriv f t * P t) := by
    dsimp [P, partialCoefficientSum] at habel ⊢
    rw [hfa, hfb, zero_mul, zero_mul] at habel
    rw [← intervalIntegral.integral_of_le hab] at habel
    linarith
  have hparts := intervalIntegral.integral_deriv_mul_eq_sub
    (fun t ht => (hf t (by simpa [Set.uIcc_of_le hab] using ht)).hasDerivAt)
    (fun t ht => hli t (by simpa [Set.uIcc_of_le hab] using ht))
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hf_int)
    hli_int
  have hparts' :
      (∫ t in a..b, deriv f t * Li t) + (∫ t in a..b, f t / Real.log t) =
        f b * Li b - f a * Li a := by
    rw [← intervalIntegral.integral_add hfli_int hflog_int]
    simpa [div_eq_mul_inv, mul_comm] using hparts
  have hmain : (∫ t in a..b, f t / Real.log t) =
      -(∫ t in a..b, deriv f t * Li t) := by
    rw [hfa, hfb] at hparts'
    linarith
  have hlin :
      (∫ t in a..b, deriv f t * (α * Li t - P t)) =
        α * (∫ t in a..b, deriv f t * Li t) -
          (∫ t in a..b, deriv f t * P t) := by
    have hpoint (t : ℝ) : deriv f t * (α * Li t - P t) =
        α * (deriv f t * Li t) - deriv f t * P t := by ring
    rw [show (fun t => deriv f t * (α * Li t - P t)) =
        fun t => α * (deriv f t * Li t) - deriv f t * P t from funext hpoint]
    rw [intervalIntegral.integral_sub (hfli_int.const_mul α) hP_int]
    rw [intervalIntegral.integral_const_mul]
  have hidentity :
      (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f n * c n) -
          α * (∫ t in a..b, f t / Real.log t) =
        ∫ t in a..b, deriv f t * (α * Li t - P t) := by
    rw [habel', hmain, hlin]
    ring
  have herr_int : IntervalIntegrable
      (fun t => deriv f t * (α * Li t - P t)) volume a b := by
    have hsub := (hfli_int.const_mul α).sub hP_int
    exact hsub.congr (by
      intro t ht
      ring)
  have hderiv_abs : IntervalIntegrable (fun t => |deriv f t|) volume a b :=
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hf_int).abs
  have hbound_int : IntervalIntegrable (fun t => |deriv f t| * E) volume a b :=
    hderiv_abs.mul_const E
  calc
    _ = |∫ t in a..b, deriv f t * (α * Li t - P t)| := by rw [hidentity]
    _ ≤ ∫ t in a..b, |deriv f t * (α * Li t - P t)| :=
      intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ t in a..b, |deriv f t| * E := by
      apply intervalIntegral.integral_mono_on hab herr_int.abs hbound_int
      intro t ht
      rw [abs_mul]
      have ht' := hcount t ht
      have hrev : |α * Li t - P t| ≤ E := by
        simpa [abs_sub_comm] using ht'
      exact mul_le_mul_of_nonneg_left hrev (abs_nonneg _)
    _ = E * (∫ t in a..b, |deriv f t|) := by
      rw [intervalIntegral.integral_mul_const, mul_comm]

/-- Finite-family Abel summation keeps a pointwise aggregate endpoint error inside the
integral. This is the form needed when the available progression theorem sums errors over all
moduli at each endpoint, rather than bounding a maximum error over endpoints for each modulus. -/
theorem smoothFamilyError_of_aggregateEndpointControl
    {ι : Type*} (s : Finset ι)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (c : ι → ℕ → ℝ) (α : ι → ℝ) (E Li f : ℝ → ℝ)
    (hf : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hf_int : IntegrableOn (deriv f) (Set.Icc a b))
    (hli : ∀ t ∈ Set.Icc a b, HasDerivAt Li (1 / Real.log t) t)
    (hli_int : IntervalIntegrable (fun t => 1 / Real.log t) volume a b)
    (hflog_int : IntervalIntegrable (fun t => f t / Real.log t) volume a b)
    (hP_int : ∀ i ∈ s,
      IntervalIntegrable (fun t => deriv f t * partialCoefficientSum (c i) t) volume a b)
    (hE_int : IntervalIntegrable (fun t => |deriv f t| * E t) volume a b)
    (hcount : ∀ t ∈ Set.Icc a b,
      (∑ i ∈ s, |partialCoefficientSum (c i) t - α i * Li t|) ≤ E t)
    (hfa : f a = 0) (hfb : f b = 0) :
    (∑ i ∈ s,
      |(∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f n * c i n) -
        α i * (∫ t in a..b, f t / Real.log t)|) ≤
      ∫ t in a..b, |deriv f t| * E t := by
  classical
  have hLi_cont : ContinuousOn Li (Set.Icc a b) := by
    intro t ht
    exact (hli t ht).continuousAt.continuousWithinAt
  have hderivLi_int :
      IntervalIntegrable (fun t => deriv f t * Li t) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact hf_int.mul_continuousOn hLi_cont isCompact_Icc
  have hP_int' (i : ι) (hi : i ∈ s) :
      IntervalIntegrable (fun t => deriv f t * partialCoefficientSum (c i) t) volume a b :=
    hP_int i hi
  have hidentity (i : ι) (hi : i ∈ s) :
      (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f n * c i n) -
          α i * (∫ t in a..b, f t / Real.log t) =
        ∫ t in a..b, deriv f t *
          (α i * Li t - partialCoefficientSum (c i) t) := by
    let P : ℝ → ℝ := partialCoefficientSum (c i)
    have habel := sum_mul_eq_sub_sub_integral_mul (c i) ha hab hf hf_int
    have habel' :
        (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f n * c i n) =
          -(∫ t in a..b, deriv f t * P t) := by
      dsimp [P, partialCoefficientSum] at habel ⊢
      rw [hfa, hfb, zero_mul, zero_mul] at habel
      rw [← intervalIntegral.integral_of_le hab] at habel
      linarith
    have hparts := intervalIntegral.integral_deriv_mul_eq_sub
      (fun t ht => (hf t (by simpa [Set.uIcc_of_le hab] using ht)).hasDerivAt)
      (fun t ht => hli t (by simpa [Set.uIcc_of_le hab] using ht))
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hf_int)
      hli_int
    have hparts' :
        (∫ t in a..b, deriv f t * Li t) +
          (∫ t in a..b, f t / Real.log t) = f b * Li b - f a * Li a := by
      rw [← intervalIntegral.integral_add hderivLi_int hflog_int]
      simpa [div_eq_mul_inv, mul_comm] using hparts
    have hmain :
        (∫ t in a..b, f t / Real.log t) =
          -(∫ t in a..b, deriv f t * Li t) := by
      rw [hfa, hfb] at hparts'
      linarith
    have hlin :
        (∫ t in a..b, deriv f t * (α i * Li t - P t)) =
          α i * (∫ t in a..b, deriv f t * Li t) -
            (∫ t in a..b, deriv f t * P t) := by
      have hpoint (t : ℝ) :
          deriv f t * (α i * Li t - P t) =
            α i * (deriv f t * Li t) - deriv f t * P t := by ring
      rw [show (fun t => deriv f t * (α i * Li t - P t)) =
          fun t => α i * (deriv f t * Li t) - deriv f t * P t from funext hpoint]
      rw [intervalIntegral.integral_sub (hderivLi_int.const_mul (α i))
        (hP_int' i hi)]
      rw [intervalIntegral.integral_const_mul]
    calc
      _ = -(∫ t in a..b, deriv f t * P t) -
          α i * (∫ t in a..b, f t / Real.log t) := by rw [habel']
      _ = α i * (∫ t in a..b, deriv f t * Li t) -
          (∫ t in a..b, deriv f t * P t) := by rw [hmain]; ring
      _ = _ := by rw [← hlin]
  have herror_int (i : ι) (hi : i ∈ s) :
      IntervalIntegrable
        (fun t => deriv f t * (α i * Li t - partialCoefficientSum (c i) t))
        volume a b := by
    have hsub := (hderivLi_int.const_mul (α i)).sub (hP_int' i hi)
    exact hsub.congr (by intro t ht; ring)
  have hterm_int (i : ι) (hi : i ∈ s) :
      IntervalIntegrable
        (fun t => |deriv f t| *
          |α i * Li t - partialCoefficientSum (c i) t|) volume a b := by
    exact (herror_int i hi).abs.congr (by intro t ht; simp only [abs_mul])
  have hsum_int :
      IntervalIntegrable
        (fun t => ∑ i ∈ s, |deriv f t| *
          |α i * Li t - partialCoefficientSum (c i) t|) volume a b := by
    have hsum_fn :
        (∑ i ∈ s, fun t => |deriv f t| *
          |α i * Li t - partialCoefficientSum (c i) t|) =
          fun t => ∑ i ∈ s, |deriv f t| *
            |α i * Li t - partialCoefficientSum (c i) t| :=
      Finset.sum_fn s (fun i t => |deriv f t| *
        |α i * Li t - partialCoefficientSum (c i) t|)
    exact (IntervalIntegrable.sum s hterm_int).congr (by
      intro t ht
      exact congrFun hsum_fn t)
  have hsum_bound (t : ℝ) (ht : t ∈ Set.Icc a b) :
      (∑ i ∈ s, |deriv f t| *
        |α i * Li t - partialCoefficientSum (c i) t|) ≤ |deriv f t| * E t := by
    calc
      _ = |deriv f t| *
          (∑ i ∈ s, |α i * Li t - partialCoefficientSum (c i) t|) := by
            rw [Finset.mul_sum]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        convert hcount t ht using 1
        apply Finset.sum_congr rfl
        intro i hi
        rw [abs_sub_comm]
  calc
    _ ≤ ∑ i ∈ s,
        ∫ t in a..b, |deriv f t| *
          |α i * Li t - partialCoefficientSum (c i) t| := by
      apply Finset.sum_le_sum
      intro i hi
      rw [hidentity i hi]
      calc
        |∫ t in a..b, deriv f t *
            (α i * Li t - partialCoefficientSum (c i) t)| ≤
          ∫ t in a..b, |deriv f t *
            (α i * Li t - partialCoefficientSum (c i) t)| :=
              intervalIntegral.abs_integral_le_integral_abs hab
        _ = _ := by
          apply intervalIntegral.integral_congr
          intro t ht
          change |deriv f t *
            (α i * Li t - partialCoefficientSum (c i) t)| = _
          rw [abs_mul]
    _ = ∫ t in a..b,
        ∑ i ∈ s, |deriv f t| *
          |α i * Li t - partialCoefficientSum (c i) t| := by
      symm
      exact intervalIntegral.integral_finsetSum hterm_int
    _ ≤ ∫ t in a..b, |deriv f t| * E t :=
      intervalIntegral.integral_mono_on hab hsum_int hE_int hsum_bound

/-- Any reduced residue class is bounded by the maximum progression error used by the BV input. -/
theorem progressionError_class_bound (y : ℝ) (q v : ℕ)
    (hv : v < q) (hcop : Nat.Coprime v q) :
    |(((primesUpTo y).filter
        (fun p : ℕ => ((p : ℕ) : ZMod q) = ((v : ℕ) : ZMod q))).card : ℝ) -
      logarithmicIntegral y / (Nat.totient q : ℝ)| ≤ primeProgressionError y q := by
  unfold primeProgressionError
  apply (Finset.le_fold_max _).2
  right
  refine ⟨v, Finset.mem_filter.mpr ?_, ?_⟩
  · exact ⟨Finset.mem_range.mpr hv, hcop⟩
  · rfl

theorem progressionError_nonneg (y : ℝ) (q : ℕ) :
    0 ≤ primeProgressionError y q := by
  unfold primeProgressionError
  exact (Finset.le_fold_max (0 : ℝ)).2 (Or.inl le_rfl)

/-- Distinct moduli of the form `N * ℓ` inherit the aggregate endpoint bound from BV. -/
theorem sum_progression_class_errors_le_bv
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (q v : ι → ℕ) (qMax : ℕ) (y : ℝ)
    (hqInj : Set.InjOn q s)
    (hq : ∀ i ∈ s, q i ≤ qMax)
    (hv : ∀ i ∈ s, v i < q i)
    (hcop : ∀ i ∈ s, Nat.Coprime (v i) (q i)) :
    (∑ i ∈ s,
      |(((primesUpTo y).filter
          (fun p : ℕ => ((p : ℕ) : ZMod (q i)) = ((v i : ℕ) : ZMod (q i)))).card : ℝ) -
        logarithmicIntegral y / (Nat.totient (q i) : ℝ)|) ≤
      ∑ q ∈ Finset.range (qMax + 1), primeProgressionError y q := by
  classical
  have hterm (i : ι) (hi : i ∈ s) :
      |(((primesUpTo y).filter
          (fun p : ℕ => ((p : ℕ) : ZMod (q i)) = ((v i : ℕ) : ZMod (q i)))).card : ℝ) -
        logarithmicIntegral y / (Nat.totient (q i) : ℝ)| ≤
        primeProgressionError y (q i) :=
    progressionError_class_bound y (q i) (v i) (hv i hi) (hcop i hi)
  have himage : s.image q ⊆ Finset.range (qMax + 1) := by
    apply Finset.image_subset_iff.mpr
    intro i hi
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hq i hi))
  calc
    _ ≤ ∑ i ∈ s, primeProgressionError y (q i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hterm i hi
    _ = ∑ q ∈ s.image q, primeProgressionError y q := by
      symm
      exact Finset.sum_image hqInj
    _ ≤ ∑ q ∈ Finset.range (qMax + 1), primeProgressionError y q :=
      Finset.sum_le_sum_of_subset_of_nonneg himage
        (fun q _ _ => progressionError_nonneg y q)

/-- A prime dividing both the progression modulus and the sieve modulus prevents any term. -/
theorem progressionPrimeSum_vanish_of_not_coprime
    (x : ℝ) (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (r ℓ : ℕ)
    (hu : Int.gcd u M = 1)
    (hbad : ¬ Nat.Coprime ℓ (M * r)) :
    progressionPrimeSum x M c u Ψ r ℓ = 0 := by
  classical
  unfold progressionPrimeSum
  have hgcd : Nat.gcd ℓ (M * r) ≠ 1 := by
    intro h
    exact hbad ((Nat.coprime_iff_gcd_eq_one).2 h)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hgcd
  have hpe : p ∣ ℓ := Nat.dvd_trans hpd (Nat.gcd_dvd_left _ _)
  have hpMr : p ∣ M * r := Nat.dvd_trans hpd (Nat.gcd_dvd_right _ _)
  have hfilter :
      (Finset.range (⌊2 * x⌋₊ + 1)).filter (fun Q : ℕ =>
        Q.Prime ∧ Real.rpow x (9 / 10 : ℝ) < (Q : ℝ) ∧
          (((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M]) ∧ ℓ ∣ c * r * Q + 1) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro Q _ hQ
    rcases hQ with ⟨_, _, hprog, hdiv⟩
    have hpn : p ∣ c * r * Q + 1 := Nat.dvd_trans hpe hdiv
    rcases hp.dvd_mul.mp hpMr with hpM | hpr
    · have hpMZ : (p : ℤ) ∣ (M : ℤ) := by exact_mod_cast hpM
      have hpnZ : (p : ℤ) ∣ (c * r * Q + 1 : ℕ) := by exact_mod_cast hpn
      have hdiff : (M : ℤ) ∣ u - (c * r * Q + 1 : ℕ) := hprog.dvd
      have hpu : (p : ℤ) ∣ u := by
        have hpdiff : (p : ℤ) ∣ u - (c * r * Q + 1 : ℕ) := dvd_trans hpMZ hdiff
        have hpadd := Int.dvd_add hpdiff hpnZ
        simpa using hpadd
      have hcop : IsCoprime u (M : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr hu
      rcases hcop with ⟨a, b, hab⟩
      have hp1 : (p : ℤ) ∣ 1 := by
        rw [← hab]
        exact Int.dvd_add (dvd_mul_of_dvd_right hpu a) (dvd_mul_of_dvd_right hpMZ b)
      have hpone : p = 1 := Nat.dvd_one.mp (by exact_mod_cast hp1)
      exact hp.ne_one hpone
    · have hpcr : p ∣ c * r * Q := by
        rw [show c * r * Q = (c * Q) * r by ring]
        exact dvd_mul_of_dvd_right hpr (c * Q)
      have hp1 : p ∣ 1 := by
        have := Nat.dvd_sub hpn hpcr
        simpa using this
      exact hp.ne_one (Nat.dvd_one.mp hp1)
  rw [hfilter, Finset.sum_empty]

theorem logarithmicIntegral_hasDerivAt {t : ℝ} (ht : 2 < t) :
    HasDerivAt logarithmicIntegral (1 / Real.log t) t := by
  change HasDerivAt (fun u : ℝ => ∫ y in (2 : ℝ)..u, 1 / Real.log y)
    (1 / Real.log t) t
  let g : ℝ → ℝ := fun y => 1 / Real.log y
  have hlog_cont : ContinuousOn Real.log (Set.Ioi (1 : ℝ)) := by
    apply Real.continuousOn_log.mono
    intro y hy
    change y ≠ 0
    exact ne_of_gt (lt_trans zero_lt_one (Set.mem_Ioi.mp hy))
  have hg_cont : ContinuousOn g (Set.Ioi (1 : ℝ)) := by
    dsimp [g]
    apply continuousOn_const.div hlog_cont
    intro y hy
    exact ne_of_gt (Real.log_pos hy)
  have hg_int : IntervalIntegrable g volume 2 t := by
    apply ContinuousOn.intervalIntegrable_of_Icc (le_of_lt ht)
    apply hg_cont.mono
    intro y hy
    exact Set.mem_Ioi.mpr (lt_of_lt_of_le (by norm_num) hy.1)
  have hg_meas : StronglyMeasurableAtFilter g (𝓝 t) volume := by
    exact (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hg_cont) t
      (Set.mem_Ioi.mpr (by linarith))
  have hg_at : ContinuousAt g t := by
    dsimp [g]
    apply continuousAt_const.div (Real.continuousAt_log (ne_of_gt (by linarith : 0 < t)))
    exact ne_of_gt (Real.log_pos (by linarith : 1 < t))
  have h := intervalIntegral.integral_hasDerivAt_right hg_int hg_meas hg_at
  simpa [g, one_div] using h

/-- For large `x`, every marked prime exceeds a fixed modulus, uniformly over valid bands. -/
theorem exists_markedPrimes_gt (M K : ℕ) (a : Fin K → ℝ)
    (ha : ValidBands K a) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ p ∈ markedPrimes x K a, (M : ℝ) < (p : ℝ) := by
  have hlim : Filter.Tendsto
      (fun x : ℝ => Real.exp (Real.rpow (Real.log x) (1 / 10 : ℝ)))
      Filter.atTop Filter.atTop := by
    exact Real.tendsto_exp_atTop.comp <|
      (tendsto_rpow_atTop (by norm_num : 0 < (1 / 10 : ℝ))).comp
        Real.tendsto_log_atTop
  have hev : ∀ᶠ x : ℝ in atTop,
      (M : ℝ) < Real.exp (Real.rpow (Real.log x) (1 / 10 : ℝ)) :=
    hlim.eventually_gt_atTop (M : ℝ)
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.1 hev
  refine ⟨max X (Real.exp 1), ?_⟩
  intro x hx p hp
  have hxX : X ≤ x := le_trans (le_max_left _ _) hx
  have hxExp : (M : ℝ) < Real.exp (Real.rpow (Real.log x) (1 / 10 : ℝ)) := hX x hxX
  have hxLog : 1 ≤ Real.log x := by
    have hxpos : 0 < Real.exp 1 := Real.exp_pos 1
    have hlog := Real.log_le_log hxpos (le_trans (le_max_right _ _) hx)
    simpa using hlog
  obtain ⟨i, _, hpband⟩ := Finset.mem_biUnion.mp hp
  rcases Finset.mem_filter.mp hpband with ⟨_, ⟨_, hpLower, _⟩⟩
  have hai : (1 / 10 : ℝ) < a i := (ha.2.1 i).1
  have hpow : Real.rpow (Real.log x) (1 / 10 : ℝ) ≤
      Real.rpow (Real.log x) (a i) :=
    Real.rpow_le_rpow_of_exponent_le hxLog hai.le
  have hpLarge : Real.exp (Real.rpow (Real.log x) (1 / 10 : ℝ)) ≤ (p : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hpow) hpLower
  exact lt_of_lt_of_le hxExp hpLarge

/-- An integer supported on marked primes is coprime to any fixed modulus once all marks exceed it. -/
theorem groupInteger_coprime_modulus (x : ℝ) (M K r : ℕ) (a : Fin K → ℝ)
    (hM : 0 < M) (hmark : ∀ p ∈ markedPrimes x K a, (M : ℝ) < (p : ℝ))
    (hr : IsGroupInteger x K a r) : Nat.Coprime r M := by
  apply Nat.coprime_of_dvd
  intro p hp hpr hpM
  have hlarge := hmark p (hr p hp hpr)
  have hple : p ≤ M := Nat.le_of_dvd hM hpM
  exact (not_lt_of_ge (show (p : ℝ) ≤ (M : ℝ) by exact_mod_cast hple)) hlarge

theorem groupInteger_pos_of_marks_gt_two (x : ℝ) (K r : ℕ) (a : Fin K → ℝ)
    (hmark : ∀ p ∈ markedPrimes x K a, (2 : ℝ) < (p : ℝ))
    (hr : IsGroupInteger x K a r) : 0 < r := by
  have hcop := groupInteger_coprime_modulus x 2 K r a (by norm_num) hmark hr
  by_contra hn
  have hr0 : r = 0 := Nat.eq_zero_of_not_pos hn
  subst r
  norm_num [Nat.Coprime] at hcop

theorem int_gcd_to_nat_coprime {z : ℤ} {N : ℕ}
    (h : Int.gcd z (N : ℤ) = 1) : Nat.Coprime z.natAbs N := by
  simpa [Nat.Coprime, Int.gcd_def] using h

theorem int_gcd_one_zmod_isUnit {z : ℤ} {N : ℕ}
    (h : Int.gcd z (N : ℤ) = 1) : IsUnit (z : ZMod N) := by
  have hcop : IsCoprime z (N : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr h
  rcases hcop with ⟨a, b, hab⟩
  apply isUnit_iff_exists_inv.mpr
  refine ⟨(a : ZMod N), ?_⟩
  have hcast := congrArg (fun w : ℤ => (w : ZMod N)) hab
  simpa [mul_comm] using hcast

theorem exists_real_rpow_ge {δ B : ℝ} (hδ : 0 < δ) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → B ≤ Real.rpow x δ := by
  have hev : ∀ᶠ x : ℝ in atTop, B ≤ Real.rpow x δ :=
    (tendsto_rpow_atTop hδ).eventually_ge_atTop B
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1 hev
  exact ⟨x₀, fun x hx => hx₀ x hx⟩

theorem nat_product_le_rpow_of_growth
    (N ell : ℕ) (x ε β θ δ : ℝ)
    (hx : 1 ≤ x) (hθ : 0 < θ)
    (hell : (ell : ℝ) ≤ Real.rpow x β)
    (hδ : δ = (1 - ε) * θ - β)
    (hGrowth : (N : ℝ) * Real.rpow 8 θ ≤ Real.rpow x δ) :
    ((N * ell : ℕ) : ℝ) ≤ Real.rpow (Real.rpow x (1 - ε) / 8) θ := by
  have h8 : 0 < Real.rpow (8 : ℝ) θ := Real.rpow_pos_of_pos (by norm_num) θ
  have hN : (N : ℝ) ≤ Real.rpow x δ / Real.rpow 8 θ :=
    (le_div_iff₀ h8).2 (by simpa [mul_comm] using hGrowth)
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hxnonneg : 0 ≤ x := le_trans (by norm_num) hx
  have hxβ : 0 ≤ Real.rpow x β := Real.rpow_nonneg hxnonneg β
  calc
    ((N * ell : ℕ) : ℝ) = (N : ℝ) * (ell : ℝ) := by norm_num
    _ ≤ (N : ℝ) * Real.rpow x β := mul_le_mul_of_nonneg_left hell (Nat.cast_nonneg _)
    _ ≤ (Real.rpow x δ / Real.rpow 8 θ) * Real.rpow x β :=
      mul_le_mul_of_nonneg_right hN hxβ
    _ = Real.rpow x (β + δ) / Real.rpow 8 θ := by
      change (x ^ δ / 8 ^ θ) * x ^ β = x ^ (β + δ) / 8 ^ θ
      rw [Real.rpow_add hxpos β δ]
      ring
    _ = Real.rpow x ((1 - ε) * θ) / Real.rpow 8 θ := by
      change x ^ (β + δ) / 8 ^ θ = x ^ ((1 - ε) * θ) / 8 ^ θ
      rw [show β + δ = (1 - ε) * θ by linarith [hδ]]
    _ = Real.rpow (Real.rpow x (1 - ε) / 8) θ := by
      change x ^ ((1 - ε) * θ) / 8 ^ θ = (x ^ (1 - ε) / 8) ^ θ
      have hdiv := Real.div_rpow (Real.rpow_nonneg hxnonneg (1 - ε))
        (by norm_num : (0 : ℝ) ≤ 8) θ
      calc
        _ = (x ^ (1 - ε)) ^ θ / 8 ^ θ := by rw [Real.rpow_mul hxnonneg]
        _ = _ := hdiv.symm

theorem real_interval_lower_cutoff
    (x cr ε : ℝ) (hx : 2 ≤ x) (heps : ε < 1 / 100)
    (hcr : 0 < cr) (hcrUpper : cr ≤ 4 * Real.rpow x ε)
    (hpow : 8 ≤ Real.rpow x (9 / 100 : ℝ)) :
    Real.rpow x (9 / 10 : ℝ) ≤ (x - 1) / cr := by
  have hxpos : 0 < x := by linarith
  have hxnonneg : 0 ≤ x := le_of_lt hxpos
  have hdelta : (9 / 100 : ℝ) ≤ 1 / 10 - ε := by linarith
  have hpow' : 8 ≤ Real.rpow x (1 / 10 - ε) :=
    le_trans hpow (Real.rpow_le_rpow_of_exponent_le (by linarith) hdelta)
  have hFactor : 1 ≤ Real.rpow x (1 / 10 - ε) / 8 :=
    (one_le_div (by norm_num : (0 : ℝ) < 8)).2 hpow'
  have hsplit : Real.rpow x (1 - ε) / 8 =
      Real.rpow x (9 / 10 : ℝ) * (Real.rpow x (1 / 10 - ε) / 8) := by
    have hexp : (9 / 10 : ℝ) + (1 / 10 - ε) = 1 - ε := by ring
    change x ^ (1 - ε) / 8 = x ^ (9 / 10 : ℝ) * (x ^ (1 / 10 - ε) / 8)
    rw [← hexp, Real.rpow_add hxpos]
    ring
  have hpower : Real.rpow x (9 / 10 : ℝ) ≤ Real.rpow x (1 - ε) / 8 := by
    rw [hsplit]
    exact le_mul_of_one_le_right (Real.rpow_nonneg hxnonneg _) hFactor
  have hden : 0 < Real.rpow x ε := Real.rpow_pos_of_pos hxpos ε
  have hscale : x / (8 * Real.rpow x ε) = Real.rpow x (1 - ε) / 8 := by
    calc
      x / (8 * Real.rpow x ε) = (x / Real.rpow x ε) / 8 := by
        field_simp [hden.ne'] <;> ring
    _ = (Real.rpow x (1 : ℝ) / Real.rpow x ε) / 8 := by
      change (x / Real.rpow x ε) / 8 =
        (Real.rpow x (1 : ℝ) / Real.rpow x ε) / 8
      have hpowone : Real.rpow x (1 : ℝ) = x := Real.rpow_one x
      rw [hpowone]
    _ = Real.rpow x (1 - ε) / 8 := by
      change (Real.rpow x (1 : ℝ) / Real.rpow x ε) / 8 =
        Real.rpow x (1 - ε) / 8
      exact congrArg (fun y : ℝ => y / 8)
        (Real.rpow_sub hxpos (1 : ℝ) ε).symm
  have hdenUpper : 2 * cr ≤ 8 * Real.rpow x ε := by nlinarith [hcrUpper]
  have hfirst : x / (8 * Real.rpow x ε) ≤ x / (2 * cr) :=
    div_le_div_of_nonneg_left hxnonneg (by positivity) hdenUpper
  have hxhalf : x / 2 ≤ x - 1 := by linarith
  have hsecond : x / (2 * cr) ≤ (x - 1) / cr := by
    rw [← div_div]
    exact (div_le_div_iff_of_pos_right hcr).2 hxhalf
  calc
    Real.rpow x (9 / 10 : ℝ) ≤ Real.rpow x (1 - ε) / 8 := hpower
    _ = x / (8 * Real.rpow x ε) := hscale.symm
    _ ≤ x / (2 * cr) := hfirst
    _ ≤ (x - 1) / cr := hsecond

theorem real_interval_lower_growth
    (x cr ε : ℝ) (hx : 2 ≤ x) (hcr : 0 < cr)
    (hcrUpper : cr ≤ 4 * Real.rpow x ε) :
    Real.rpow x (1 - ε) / 8 ≤ (x - 1) / cr := by
  have hxpos : 0 < x := by linarith
  have hxnonneg : 0 ≤ x := le_of_lt hxpos
  have hden : 0 < Real.rpow x ε := Real.rpow_pos_of_pos hxpos ε
  have hscale : x / (8 * Real.rpow x ε) = Real.rpow x (1 - ε) / 8 := by
    calc
      x / (8 * Real.rpow x ε) = (x / Real.rpow x ε) / 8 := by
        field_simp [hden.ne'] <;> ring
      _ = (Real.rpow x (1 : ℝ) / Real.rpow x ε) / 8 := by
        change (x / Real.rpow x ε) / 8 =
          (Real.rpow x (1 : ℝ) / Real.rpow x ε) / 8
        have hpowone : Real.rpow x (1 : ℝ) = x := Real.rpow_one x
        rw [hpowone]
      _ = Real.rpow x (1 - ε) / 8 := by
        change (Real.rpow x (1 : ℝ) / Real.rpow x ε) / 8 =
          Real.rpow x (1 - ε) / 8
        exact congrArg (fun y : ℝ => y / 8)
          (Real.rpow_sub hxpos (1 : ℝ) ε).symm
  have hdenUpper : 2 * cr ≤ 8 * Real.rpow x ε := by nlinarith [hcrUpper]
  have hfirst : x / (8 * Real.rpow x ε) ≤ x / (2 * cr) :=
    div_le_div_of_nonneg_left hxnonneg (by positivity) hdenUpper
  have hxhalf : x / 2 ≤ x - 1 := by linarith
  have hsecond : x / (2 * cr) ≤ (x - 1) / cr := by
    rw [← div_div]
    exact (div_le_div_iff_of_pos_right hcr).2 hxhalf
  calc
    Real.rpow x (1 - ε) / 8 = x / (8 * Real.rpow x ε) := hscale.symm
    _ ≤ x / (2 * cr) := hfirst
    _ ≤ (x - 1) / cr := hsecond

/-- The CRT representative packages the two reduced progression conditions into one modulus. -/
theorem nat_crt_residue_spec (N ℓ a b Q : ℕ) (hcop : Nat.Coprime N ℓ) :
    (Q ≡ (Nat.chineseRemainder hcop a b : ℕ) [MOD N * ℓ]) ↔
      Q ≡ a [MOD N] ∧ Q ≡ b [MOD ℓ] := by
  constructor
  · intro h
    have hcrt := (Nat.chineseRemainder hcop a b).prop
    exact ⟨(h.of_mul_right ℓ).trans hcrt.1,
      (h.of_mul_left N).trans hcrt.2⟩
  · rintro ⟨hN, hℓ⟩
    exact Nat.chineseRemainder_modEq_unique hcop hN hℓ

/-- A CRT residue is reduced when each of its two local residues is reduced. -/
theorem nat_crt_residue_coprime (N ℓ a b : ℕ) (hcop : Nat.Coprime N ℓ)
    (ha : Nat.Coprime a N) (hb : Nat.Coprime b ℓ) :
    Nat.Coprime (Nat.chineseRemainder hcop a b : ℕ) (N * ℓ) := by
  apply Nat.coprime_of_dvd
  intro p hp hpv hpq
  rcases hp.dvd_mul.mp hpq with hpN | hpℓ
  · have hmod := (Nat.chineseRemainder hcop a b).prop.1
    have hpa : p ∣ a := (hmod.dvd_iff hpN).mp hpv
    have hone : p ∣ 1 := by
      rw [← ha.gcd_eq_one]
      exact Nat.dvd_gcd hpa hpN
    exact hp.not_dvd_one hone
  · have hmod := (Nat.chineseRemainder hcop a b).prop.2
    have hpb : p ∣ b := (hmod.dvd_iff hpℓ).mp hpv
    have hone : p ∣ 1 := by
      rw [← hb.gcd_eq_one]
      exact Nat.dvd_gcd hpb hpℓ
    exact hp.not_dvd_one hone

/-! The next reciprocal-totient estimate adapts the elementary divisor-count argument in
`OAI/NumberTheory/PrimeGaps/CharacterErrors.lean`; that module's compiled artifact is not in the
shared library, so the small argument is kept locally. -/

def divisorMultiplicity (k n : ℕ) : ℕ := (ArithmeticFunction.zeta ^ k) n

theorem divisorMultiplicity_one (k : ℕ) : divisorMultiplicity k 1 = 1 := by
  exact (ArithmeticFunction.isMultiplicative_zeta.pow).1

theorem divisorMultiplicity_succ (k n : ℕ) :
    divisorMultiplicity (k + 1) n = ∑ d ∈ n.divisors, divisorMultiplicity k d := by
  simp only [divisorMultiplicity, pow_succ, ArithmeticFunction.mul_zeta_apply]

theorem divisorMultiplicity_two (q : ℕ) : divisorMultiplicity 2 q = q.divisors.card := by
  rw [show 2 = 1 + 1 by rfl, divisorMultiplicity_succ]
  calc
    _ = ∑ d ∈ q.divisors, 1 := by
      apply Finset.sum_congr rfl
      intro d hd
      simp [divisorMultiplicity, ArithmeticFunction.zeta_apply_ne
        (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1
          (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2)).ne']
    _ = _ := by simp

theorem reciprocal_divisor_sum_le (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, (∑ d ∈ q.divisors, f d) / (q : ℝ)) ≤
      (∑ d ∈ Finset.Icc 1 Q, f d / (d : ℝ)) * (harmonic Q : ℝ) := by
  classical
  let s := (Finset.Icc 1 Q).sigma fun q => q.divisors
  let t := (Finset.Icc 1 Q) ×ˢ (Finset.Icc 1 Q)
  let e : (a : ℕ) × ℕ → ℕ × ℕ := fun x => (x.2, x.1 / x.2)
  have he_mem : ∀ x ∈ s, e x ∈ t := by
    rintro ⟨q, d⟩ hx
    obtain ⟨hq, hd⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hq1, hqQ⟩ := Finset.mem_Icc.mp hq
    obtain ⟨hdq, hq0⟩ := Nat.mem_divisors.mp hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdq hq1
    have hdle : d ≤ q := Nat.le_of_dvd hq1 hdq
    have hdivpos : 0 < q / d := Nat.div_pos hdle hd0
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hd0, hdle.trans hqQ⟩,
      Finset.mem_Icc.mpr ⟨hdivpos, (Nat.div_le_self q d).trans hqQ⟩⟩
  have he_inj : Set.InjOn e s := by
    rintro ⟨q, d⟩ hx ⟨q', d'⟩ hy he
    obtain ⟨hq, hd⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hq', hd'⟩ := Finset.mem_sigma.mp hy
    have hed : d = d' := congrArg Prod.fst he
    have heq : q / d = q' / d' := congrArg Prod.snd he
    have hdq : d ∣ q := (Nat.mem_divisors.mp hd).1
    have hdq' : d' ∣ q' := (Nat.mem_divisors.mp hd').1
    have hqq : q = q' := by
      rw [← Nat.div_mul_cancel hdq, ← Nat.div_mul_cancel hdq', heq, hed]
    subst d'
    subst q'
    rfl
  have hsum : (∑ q ∈ Finset.Icc 1 Q, (∑ d ∈ q.divisors, f d) / (q : ℝ)) =
      ∑ x ∈ s, f (e x).1 / (e x).1 / (e x).2 := by
    dsimp only [s]
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d hd
    have hdq := (Nat.mem_divisors.mp hd).1
    dsimp only [e]
    rw [div_div, ← Nat.cast_mul, Nat.mul_div_cancel' hdq]
  rw [hsum]
  calc
    _ = ∑ x ∈ s.image e, f x.1 / (x.1 : ℝ) / (x.2 : ℝ) := by
      rw [Finset.sum_image he_inj]
    _ ≤ ∑ x ∈ t, f x.1 / (x.1 : ℝ) / (x.2 : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr he_mem)
        (fun x _ _ => div_nonneg (div_nonneg (hf _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
    _ = _ := by
      simp only [t, Finset.sum_product, div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum,
        harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      rw [Finset.sum_comm]

theorem sum_divisorMultiplicity_reciprocal_le (k Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, (divisorMultiplicity k q : ℝ) / (q : ℝ)) ≤
      (harmonic Q : ℝ) ^ k := by
  induction k with
  | zero =>
    by_cases hQ : Q = 0
    · subst Q
      simp
    · have hQ1 : 1 ≤ Q := Nat.one_le_iff_ne_zero.mpr hQ
      simp [divisorMultiplicity, ArithmeticFunction.one_apply, ite_div, hQ1]
  | succ k ih =>
    have h := reciprocal_divisor_sum_le (fun n => (divisorMultiplicity k n : ℝ))
      (fun n => Nat.cast_nonneg _) Q
    simp only [divisorMultiplicity_succ, Nat.cast_sum] at ⊢
    apply h.trans
    rw [pow_succ]
    exact mul_le_mul_of_nonneg_right ih (by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      exact Finset.sum_nonneg fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))

theorem nat_le_card_divisors_mul_totient (q : ℕ) : q ≤ q.divisors.card * q.totient := by
  calc
    q = ∑ d ∈ q.divisors, d.totient := (Nat.sum_totient q).symm
    _ ≤ ∑ _d ∈ q.divisors, q.totient := by
      apply Finset.sum_le_sum
      intro d hd
      exact Nat.le_of_dvd
        (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2))
        (Nat.totient_dvd_of_dvd (Nat.mem_divisors.mp hd).1)
    _ = _ := by simp

theorem sum_totient_reciprocal_le (Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, (1 : ℝ) / (q.totient : ℝ)) ≤ (harmonic Q : ℝ) ^ 2 := by
  apply le_trans (Finset.sum_le_sum (g := fun q =>
      (divisorMultiplicity 2 q : ℝ) / (q : ℝ)) ?_)
    (sum_divisorMultiplicity_reciprocal_le 2 Q)
  intro q hq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
  have hphi : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Finset.mem_Icc.mp hq).1
  rw [divisorMultiplicity_two, div_le_div_iff₀ hphi hq0, one_mul]
  exact_mod_cast nat_le_card_divisors_mul_totient q

theorem localSieveDensity_sum_le (M r : ℕ) (D : ℝ) :
    (∑ ℓ ∈ oddSquarefreeUpTo D, localSieveDensity M r ℓ) ≤
      (harmonic ⌊D⌋₊ : ℝ) ^ 2 := by
  have hsubset : oddSquarefreeUpTo D ⊆ Finset.Icc 1 ⌊D⌋₊ := by
    intro ℓ hℓ
    simp only [oddSquarefreeUpTo, Finset.mem_filter, Finset.mem_range] at hℓ
    rcases hℓ with ⟨hℓlt, hℓodd, _⟩
    have hℓ0 : ℓ ≠ 0 := by
      intro hz
      subst ℓ
      simp at hℓodd
    exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hℓ0, Nat.lt_succ_iff.mp hℓlt⟩
  have hterm (ℓ : ℕ) (hℓ : ℓ ∈ oddSquarefreeUpTo D) :
      localSieveDensity M r ℓ ≤ (1 : ℝ) / (Nat.totient ℓ : ℝ) := by
    have hℓpos : 0 < ℓ := Nat.pos_of_ne_zero (by
      intro hz
      subst ℓ
      have hodd := (Finset.mem_filter.mp hℓ).2.1
      simp at hodd)
    have hφ : 0 < Nat.totient ℓ := Nat.totient_pos.mpr hℓpos
    unfold localSieveDensity
    split_ifs
    · rfl
    · exact div_nonneg (by norm_num) (by positivity)
  calc
    _ ≤ ∑ ℓ ∈ oddSquarefreeUpTo D, (1 : ℝ) / (Nat.totient ℓ : ℝ) := by
      apply Finset.sum_le_sum
      intro ℓ hℓ
      exact hterm ℓ hℓ
    _ ≤ ∑ ℓ ∈ Finset.Icc 1 ⌊D⌋₊, (1 : ℝ) / (Nat.totient ℓ : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro ℓ hℓ _
      exact div_nonneg (by norm_num) (Nat.cast_nonneg _)
    _ ≤ _ := sum_totient_reciprocal_le ⌊D⌋₊

end ArtinPrimitiveRoots.Construction.ProofsC2

namespace ArtinPrimitiveRoots.Construction.ProofsC2

/-- A prime `Q` satisfying the two local congruences lies in one reduced class modulo `Nℓ`. -/
theorem progressionClass_crt_forward
    (M c N r ℓ Q : ℕ) (u z : ℤ)
    (hMN : c * N = M) (hc : 0 < c) (hN : 0 < N) (hℓ : 0 < ℓ)
    (hz : (c : ℤ) * z = u - 1)
    (hrN : Nat.Coprime r N) (hcrℓ : Nat.Coprime (c * r) ℓ)
    (hNℓ : Nat.Coprime N ℓ)
    (hprog : ((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M])
    (hdiv : ℓ ∣ c * r * Q + 1) :
    Q ≡ Nat.chineseRemainder hNℓ
      ((r : ZMod N)⁻¹ * (z : ZMod N)).val
      (-(((c * r : ℕ) : ZMod ℓ)⁻¹)).val [MOD N * ℓ] := by
  let vN : ℕ := ((r : ZMod N)⁻¹ * (z : ZMod N)).val
  let vℓ : ℕ := (-(((c * r : ℕ) : ZMod ℓ)⁻¹)).val
  have hN0 : N ≠ 0 := Nat.ne_of_gt hN
  have hℓ0 : ℓ ≠ 0 := Nat.ne_of_gt hℓ
  letI : NeZero N := ⟨hN0⟩
  letI : NeZero ℓ := ⟨hℓ0⟩
  have hu : u = (c : ℤ) * z + 1 := by linarith
  have hshift :
      (c : ℤ) * (r : ℤ) * (Q : ℤ) + 1 ≡ (c : ℤ) * z + 1 [ZMOD M] := by
    simpa [Nat.cast_mul, Nat.cast_add, hu, mul_assoc] using hprog
  have hmul :
      (c : ℤ) * (r : ℤ) * (Q : ℤ) ≡ (c : ℤ) * z [ZMOD M] :=
    Int.ModEq.add_right_cancel' 1 hshift
  have hMcast : (M : ℤ) = (c : ℤ) * (N : ℤ) := by exact_mod_cast hMN.symm
  rw [hMcast] at hmul
  have hmul' :
      (c : ℤ) * ((r : ℤ) * (Q : ℤ)) ≡ (c : ℤ) * z
          [ZMOD (c : ℤ) * (N : ℤ)] := by
    simpa [mul_assoc] using hmul
  have hsmall : (r : ℤ) * (Q : ℤ) ≡ z [ZMOD (N : ℤ)] := by
    have hc0 : (c : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hc)
    exact Int.ModEq.mul_left_cancel' (c := (c : ℤ)) hc0 hmul'
  have hsmallZ : (r : ZMod N) * (Q : ZMod N) = (z : ZMod N) := by
    simpa [Int.cast_mul] using
      (ZMod.intCast_eq_intCast_iff ((r : ℤ) * (Q : ℤ)) z N).2 hsmall
  have hprodN : (r : ZMod N) * (Q : ZMod N) = (z : ZMod N) := by
    exact hsmallZ
  have hrUnit : IsUnit (r : ZMod N) := (ZMod.isUnit_iff_coprime r N).2 hrN
  have hUnitInv : (r : ZMod N)⁻¹ = ((hrUnit.unit⁻¹ : Units (ZMod N)) : ZMod N) :=
    zmod_inv_eq_unit_inv hrUnit
  have hInvMul : (r : ZMod N)⁻¹ * (r : ZMod N) = 1 := by
    rw [hUnitInv]
    exact hrUnit.val_inv_mul
  have hQeqN : (Q : ZMod N) = (r : ZMod N)⁻¹ * (z : ZMod N) := by
    calc
      (Q : ZMod N) = 1 * (Q : ZMod N) := by simp
      _ = ((r : ZMod N)⁻¹ * (r : ZMod N)) * (Q : ZMod N) := by
        rw [hInvMul]
      _ = (r : ZMod N)⁻¹ * (z : ZMod N) := by rw [mul_assoc, hprodN]
  have hVNCast : (vN : ZMod N) = (r : ZMod N)⁻¹ * (z : ZMod N) := by
    simp [vN]
  have hQmodN : Q ≡ vN [MOD N] :=
    (ZMod.natCast_eq_natCast_iff Q vN N).1 (hQeqN.trans hVNCast.symm)
  have hzero : ((c * r * Q + 1 : ℕ) : ZMod ℓ) = 0 :=
    (ZMod.natCast_eq_zero_iff (c * r * Q + 1) ℓ).2 hdiv
  have hprodℓ :
      ((c * r : ℕ) : ZMod ℓ) * (Q : ZMod ℓ) = -1 := by
    have hsum : ((c * r : ℕ) : ZMod ℓ) * (Q : ZMod ℓ) + 1 = 0 := by
      simpa [Nat.cast_mul, Nat.cast_add, mul_assoc] using hzero
    exact (add_eq_zero_iff_eq_neg).mp hsum
  have hcrUnit : IsUnit ((c * r : ℕ) : ZMod ℓ) :=
    (ZMod.isUnit_iff_coprime (c * r) ℓ).2 hcrℓ
  have hcrUnitInv : ((c * r : ℕ) : ZMod ℓ)⁻¹ =
      ((hcrUnit.unit⁻¹ : Units (ZMod ℓ)) : ZMod ℓ) := zmod_inv_eq_unit_inv hcrUnit
  have hcrInvMul : ((c * r : ℕ) : ZMod ℓ)⁻¹ * ((c * r : ℕ) : ZMod ℓ) = 1 := by
    rw [hcrUnitInv]
    exact hcrUnit.val_inv_mul
  have hQeqℓ : (Q : ZMod ℓ) = -(((c * r : ℕ) : ZMod ℓ)⁻¹) := by
    calc
      (Q : ZMod ℓ) = 1 * (Q : ZMod ℓ) := by simp
      _ = ((((c * r : ℕ) : ZMod ℓ)⁻¹ * ((c * r : ℕ) : ZMod ℓ)) *
          (Q : ZMod ℓ)) := by
        rw [hcrInvMul]
      _ = ((c * r : ℕ) : ZMod ℓ)⁻¹ *
          (((c * r : ℕ) : ZMod ℓ) * (Q : ZMod ℓ)) := by ring
      _ = ((c * r : ℕ) : ZMod ℓ)⁻¹ * (-1) := by rw [hprodℓ]
      _ = -(((c * r : ℕ) : ZMod ℓ)⁻¹) := by ring
  have hVℓCast : (vℓ : ZMod ℓ) = -(((c * r : ℕ) : ZMod ℓ)⁻¹) := by
    simp [vℓ]
  have hQmodℓ : Q ≡ vℓ [MOD ℓ] :=
    (ZMod.natCast_eq_natCast_iff Q vℓ ℓ).1 (hQeqℓ.trans hVℓCast.symm)
  exact (nat_crt_residue_spec N ℓ vN vℓ Q hNℓ).2 ⟨hQmodN, hQmodℓ⟩

end ArtinPrimitiveRoots.Construction.ProofsC2

namespace ArtinPrimitiveRoots.Construction.ProofsC2

theorem progressionClass_crt_reverse
    (M c N r ℓ Q : ℕ) (u z : ℤ)
    (hMN : c * N = M) (hN : 0 < N) (hℓ : 0 < ℓ)
    (hz : (c : ℤ) * z = u - 1)
    (hrN : Nat.Coprime r N) (hcrℓ : Nat.Coprime (c * r) ℓ)
    (hNℓ : Nat.Coprime N ℓ)
    (hclass : Q ≡ Nat.chineseRemainder hNℓ
      ((r : ZMod N)⁻¹ * (z : ZMod N)).val
      (-(((c * r : ℕ) : ZMod ℓ)⁻¹)).val [MOD N * ℓ]) :
    (((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M]) ∧ ℓ ∣ c * r * Q + 1 := by
  let vN : ℕ := ((r : ZMod N)⁻¹ * (z : ZMod N)).val
  let vℓ : ℕ := (-(((c * r : ℕ) : ZMod ℓ)⁻¹)).val
  have hN0 : N ≠ 0 := Nat.ne_of_gt hN
  have hℓ0 : ℓ ≠ 0 := Nat.ne_of_gt hℓ
  letI : NeZero N := ⟨hN0⟩
  letI : NeZero ℓ := ⟨hℓ0⟩
  have hCRT := (nat_crt_residue_spec N ℓ vN vℓ Q hNℓ).1 hclass
  rcases hCRT with ⟨hQmodN, hQmodℓ⟩
  have hrUnit : IsUnit (r : ZMod N) := (ZMod.isUnit_iff_coprime r N).2 hrN
  have hUnitInv : (r : ZMod N)⁻¹ = ((hrUnit.unit⁻¹ : Units (ZMod N)) : ZMod N) :=
    zmod_inv_eq_unit_inv hrUnit
  have hMulInv : (r : ZMod N) * (r : ZMod N)⁻¹ = 1 := by
    rw [hUnitInv]
    exact hrUnit.mul_val_inv
  have hQeqN : (Q : ZMod N) = (r : ZMod N)⁻¹ * (z : ZMod N) := by
    have hh := (ZMod.natCast_eq_natCast_iff Q vN N).2 hQmodN
    simpa [vN] using hh
  have hprodN : (r : ZMod N) * (Q : ZMod N) = (z : ZMod N) := by
    calc
      (r : ZMod N) * (Q : ZMod N) =
          (r : ZMod N) * ((r : ZMod N)⁻¹ * (z : ZMod N)) := by rw [hQeqN]
      _ = (z : ZMod N) := by
        rw [← mul_assoc, hMulInv, one_mul]
  have hsmall : (r : ℤ) * (Q : ℤ) ≡ z [ZMOD (N : ℤ)] := by
    apply (ZMod.intCast_eq_intCast_iff ((r : ℤ) * (Q : ℤ)) z N).1
    simpa [Int.cast_mul] using hprodN
  have hmul := Int.ModEq.mul_left' (c := (c : ℤ)) hsmall
  have hMcast : (M : ℤ) = (c : ℤ) * (N : ℤ) := by exact_mod_cast hMN.symm
  rw [← hMcast] at hmul
  have hu : u = (c : ℤ) * z + 1 := by linarith
  have hprog : ((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M] := by
    simpa [Nat.cast_mul, Nat.cast_add, mul_assoc, hu] using hmul.add_right 1
  have hcrUnit : IsUnit ((c * r : ℕ) : ZMod ℓ) :=
    (ZMod.isUnit_iff_coprime (c * r) ℓ).2 hcrℓ
  have hcrUnitInv : ((c * r : ℕ) : ZMod ℓ)⁻¹ =
      ((hcrUnit.unit⁻¹ : Units (ZMod ℓ)) : ZMod ℓ) := zmod_inv_eq_unit_inv hcrUnit
  have hcrMulInv : ((c * r : ℕ) : ZMod ℓ) * ((c * r : ℕ) : ZMod ℓ)⁻¹ = 1 := by
    rw [hcrUnitInv]
    exact hcrUnit.mul_val_inv
  have hQeqℓ : (Q : ZMod ℓ) = -(((c * r : ℕ) : ZMod ℓ)⁻¹) := by
    have hh := (ZMod.natCast_eq_natCast_iff Q vℓ ℓ).2 hQmodℓ
    simpa [vℓ] using hh
  have hzero : ((c * r * Q + 1 : ℕ) : ZMod ℓ) = 0 := by
    calc
      ((c * r * Q + 1 : ℕ) : ZMod ℓ) =
          ((c * r : ℕ) : ZMod ℓ) * (Q : ZMod ℓ) + 1 := by
            simp [Nat.cast_mul, Nat.cast_add, mul_assoc]
      _ = ((c * r : ℕ) : ZMod ℓ) *
          (-(((c * r : ℕ) : ZMod ℓ)⁻¹)) + 1 := by rw [hQeqℓ]
      _ = 0 := by rw [mul_neg, hcrMulInv]; ring
  have hdiv : ℓ ∣ c * r * Q + 1 :=
    (ZMod.natCast_eq_zero_iff (c * r * Q + 1) ℓ).1 hzero
  exact ⟨hprog, hdiv⟩

/-- A good sieve modulus gives one reduced CRT class modulo `N * ℓ`. -/
theorem progressionClass_data
    (M c N r ℓ : ℕ) (u z : ℤ)
    (hMN : c * N = M) (hc : 0 < c) (hN : 0 < N) (hℓ : 0 < ℓ)
    (hz : (c : ℤ) * z = u - 1)
    (hrN : Nat.Coprime r N) (hZgcd : Int.gcd z (N : ℤ) = 1)
    (hGood : Nat.Coprime ℓ (M * r)) :
    ∃ v : ℕ, v < N * ℓ ∧ Nat.Coprime v (N * ℓ) ∧
      ∀ Q : ℕ,
        ((((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M] ∧ ℓ ∣ c * r * Q + 1) ↔
          Q ≡ v [MOD N * ℓ]) := by
  have hNdivM : N ∣ M := by
    refine ⟨c, ?_⟩
    exact hMN.symm.trans (Nat.mul_comm c N)
  have hEllM : Nat.Coprime ℓ M :=
    hGood.coprime_dvd_right (dvd_mul_right M r)
  have hEllN : Nat.Coprime ℓ N := hEllM.coprime_dvd_right hNdivM
  have hEllR : Nat.Coprime ℓ r :=
    hGood.coprime_dvd_right (show r ∣ M * r from ⟨M, by ring⟩)
  have hCrDivMr : c * r ∣ M * r := by
    refine ⟨N, ?_⟩
    rw [← hMN]
    ring
  have hEllCr : Nat.Coprime ℓ (c * r) := hGood.coprime_dvd_right hCrDivMr
  have hNℓ : Nat.Coprime N ℓ := hEllN.symm
  have hcrℓ : Nat.Coprime (c * r) ℓ := hEllCr.symm
  have hN0 : N ≠ 0 := Nat.ne_of_gt hN
  have hℓ0 : ℓ ≠ 0 := Nat.ne_of_gt hℓ
  letI : NeZero N := ⟨hN0⟩
  letI : NeZero ℓ := ⟨hℓ0⟩
  let vN : ℕ := ((r : ZMod N)⁻¹ * (z : ZMod N)).val
  let vℓ : ℕ := (-(((c * r : ℕ) : ZMod ℓ)⁻¹)).val
  let v : ℕ := Nat.chineseRemainder hNℓ vN vℓ
  have hrUnit : IsUnit (r : ZMod N) := (ZMod.isUnit_iff_coprime r N).2 hrN
  have hzUnit : IsUnit (z : ZMod N) := int_gcd_one_zmod_isUnit hZgcd
  have hrInvUnit : IsUnit ((r : ZMod N)⁻¹) := by
    rw [zmod_inv_eq_unit_inv hrUnit]
    exact (hrUnit.unit⁻¹).isUnit
  have hvNUnit : IsUnit (vN : ZMod N) := by
    dsimp [vN]
    rw [ZMod.natCast_zmod_val]
    exact IsUnit.mul hrInvUnit hzUnit
  have hcrUnit : IsUnit ((c * r : ℕ) : ZMod ℓ) :=
    (ZMod.isUnit_iff_coprime (c * r) ℓ).2 hcrℓ
  have hcrInvUnit : IsUnit (((c * r : ℕ) : ZMod ℓ)⁻¹) := by
    rw [zmod_inv_eq_unit_inv hcrUnit]
    exact (hcrUnit.unit⁻¹).isUnit
  have hvℓUnit : IsUnit (vℓ : ZMod ℓ) := by
    dsimp [vℓ]
    rw [ZMod.natCast_zmod_val]
    exact hcrInvUnit.neg
  have hvNCop : Nat.Coprime vN N := (ZMod.isUnit_iff_coprime vN N).1 hvNUnit
  have hvℓCop : Nat.Coprime vℓ ℓ := (ZMod.isUnit_iff_coprime vℓ ℓ).1 hvℓUnit
  have hvCop : Nat.Coprime v (N * ℓ) := by
    dsimp [v]
    exact nat_crt_residue_coprime N ℓ vN vℓ hNℓ hvNCop hvℓCop
  have hvLt : v < N * ℓ := by
    dsimp [v]
    simpa using Nat.chineseRemainder_lt_mul hNℓ vN vℓ hN0 hℓ0
  refine ⟨v, hvLt, hvCop, ?_⟩
  intro Q
  constructor
  · intro h
    simpa [v, vN, vℓ] using
      progressionClass_crt_forward M c N r ℓ Q u z hMN hc hN hℓ hz hrN hcrℓ hNℓ
        h.1 h.2
  · intro h
    have h' := progressionClass_crt_reverse M c N r ℓ Q u z hMN hN hℓ hz
      hrN hcrℓ hNℓ (by simpa [v, vN, vℓ] using h)
    exact h'

end ArtinPrimitiveRoots.Construction.ProofsC2

namespace ArtinPrimitiveRoots.Construction.ProofsC2

theorem progression_modulus_coprime_of_divisibility
    (M c r ℓ Q : ℕ) (u : ℤ)
    (hu : Int.gcd u M = 1)
    (hprog : ((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M])
    (hdiv : ℓ ∣ c * r * Q + 1)
    (hbad : ¬ Nat.Coprime ℓ (M * r)) : False := by
  obtain ⟨p, hp, hpℓ, hpMr⟩ := Nat.Prime.not_coprime_iff_dvd.mp hbad
  rcases (Nat.Prime.dvd_mul hp).1 hpMr with hpM | hpr
  · have hpMInt : (p : ℤ) ∣ (M : ℤ) := by exact_mod_cast hpM
    have hprogP := Int.ModEq.of_dvd hpMInt hprog
    have hpD : p ∣ c * r * Q + 1 := hpℓ.trans hdiv
    have hpUInt : (p : ℤ) ∣ u := (hprogP.dvd_iff).mp (by exact_mod_cast hpD)
    have hpOne : (p : ℤ) ∣ 1 := by
      have hpgcd : (p : ℤ) ∣ Int.gcd u (M : ℤ) := dvd_gcd hpUInt hpMInt
      rw [hu] at hpgcd
      exact hpgcd
    exact hp.not_dvd_one (by exact_mod_cast hpOne)
  · have hpTerm : p ∣ c * r * Q := by
      have htmp : p ∣ r * (c * Q) := dvd_mul_of_dvd_left hpr (c * Q)
      simpa [mul_assoc, mul_left_comm, mul_comm] using htmp
    have hpD : p ∣ c * r * Q + 1 := hpℓ.trans hdiv
    have hpOneInt : (p : ℤ) ∣ 1 := by
      have hpTermInt : (p : ℤ) ∣ (c * r * Q : ℤ) := by exact_mod_cast hpTerm
      have hpDInt : (p : ℤ) ∣ (c * r * Q + 1 : ℤ) := by exact_mod_cast hpD
      have hsub := Int.dvd_sub hpDInt hpTermInt
      simpa using hsub
    have hpOne : p ∣ 1 := by exact_mod_cast hpOneInt
    exact hp.not_dvd_one hpOne

end ArtinPrimitiveRoots.Construction.ProofsC2
