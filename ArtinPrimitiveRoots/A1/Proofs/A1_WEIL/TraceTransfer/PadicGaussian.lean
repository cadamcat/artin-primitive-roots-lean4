import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.RationalData
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.RationalOddGauss
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.LatticeGaussian
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# One-dimensional `p`-adic Gaussians

For a character `θ` of `ℚ_[p]` with kernel `ℤ_[p]` and the standard values on `ℤ[1/p]`, the
integral of `θ (c * y ^ 2)` over a large ball is a positive real multiple of the explicit
rational phase `rationalPrimePhase p c`. The proof averages over a small ball (the lead's
`large_subgroup_phase_integrals_eq`), shrinks to an explicit ball, and evaluates the resulting
finite coset sum with the rational Gauss sums.
-/

set_option autoImplicit false

open MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.weil_trace_opus

open ArtinPrimitiveRoots.Proofs.a1_weil_sol

variable {p : ℕ} [Fact p.Prime]

local instance padicMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
local instance padicBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩

/-- The closed ball `{x | ‖x‖ ≤ p ^ s}` of `ℚ_[p]` as an additive subgroup. -/
def padicBall (p : ℕ) [Fact p.Prime] (s : ℤ) : AddSubgroup ℚ_[p] where
  carrier := {x | ‖x‖ ≤ (p : ℝ) ^ s}
  add_mem' := by
    intro x y hx hy
    exact (Padic.nonarchimedean x y).trans (max_le hx hy)
  zero_mem' := by
    change ‖(0 : ℚ_[p])‖ ≤ (p : ℝ) ^ s
    rw [norm_zero]
    positivity
  neg_mem' := by
    intro x hx
    change ‖-x‖ ≤ (p : ℝ) ^ s
    rw [norm_neg]
    exact hx

theorem mem_padicBall {s : ℤ} {x : ℚ_[p]} : x ∈ padicBall p s ↔ ‖x‖ ≤ (p : ℝ) ^ s :=
  Iff.rfl

theorem padic_one_lt : (1 : ℝ) < p := by
  exact_mod_cast (Fact.out : p.Prime).one_lt

theorem padic_zpow_pos (s : ℤ) : (0 : ℝ) < (p : ℝ) ^ s :=
  zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) s

theorem padicBall_coe (s : ℤ) :
    (padicBall p s : Set ℚ_[p]) = Metric.closedBall 0 ((p : ℝ) ^ s) := by
  ext x
  simp only [SetLike.mem_coe, mem_padicBall, Metric.mem_closedBall, dist_zero_right]

theorem padicBall_isCompact (s : ℤ) : IsCompact (padicBall p s : Set ℚ_[p]) := by
  rw [padicBall_coe]
  exact isCompact_closedBall 0 _

theorem padicBall_isOpen (s : ℤ) : IsOpen (padicBall p s : Set ℚ_[p]) := by
  apply AddSubgroup.isOpen_of_mem_nhds (padicBall p s) (g := 0)
  rw [padicBall_coe]
  exact Filter.mem_of_superset (Metric.ball_mem_nhds 0 (padic_zpow_pos s))
    Metric.ball_subset_closedBall

theorem padicBall_mono {s t : ℤ} (h : s ≤ t) : padicBall p s ≤ padicBall p t := by
  intro x hx
  exact hx.trans (zpow_le_zpow_right₀ padic_one_lt.le h)

/-- Every compact set lies in all sufficiently large balls. -/
theorem exists_padicBall_superset {S : Set ℚ_[p]} (hS : IsCompact S) :
    ∃ s0 : ℤ, ∀ s, s0 ≤ s → S ⊆ padicBall p s := by
  obtain ⟨R, hR⟩ := hS.isBounded.subset_closedBall 0
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt R (padic_one_lt (p := p))
  refine ⟨n, fun s hs x hx => ?_⟩
  have hx' := hR hx
  rw [Metric.mem_closedBall, dist_zero_right] at hx'
  rw [SetLike.mem_coe, mem_padicBall]
  calc ‖x‖ ≤ R := hx'
    _ ≤ (p : ℝ) ^ n := hn.le
    _ = (p : ℝ) ^ (n : ℤ) := (zpow_natCast _ _).symm
    _ ≤ (p : ℝ) ^ s := zpow_le_zpow_right₀ padic_one_lt.le hs

/-- A character trivial exactly on `ℤ_[p]` is continuous. -/
theorem padicChar_continuous (θ : AddChar ℚ_[p] ℂ) (hθ : ∀ x, θ x = 1 ↔ ‖x‖ ≤ 1) :
    Continuous θ := by
  rw [continuous_iff_continuousAt]
  intro x
  apply continuousAt_of_locally_lipschitz zero_lt_one 0
  intro y hy
  have hyx : ‖y - x‖ ≤ 1 := by
    rw [← dist_eq_norm]
    exact hy.le
  have h1 : θ (y - x) = 1 := (hθ _).mpr hyx
  have hy' : θ y = θ x := by
    calc θ y = θ ((y - x) + x) := by rw [sub_add_cancel]
      _ = θ (y - x) * θ x := AddChar.map_add_eq_mul θ _ _
      _ = θ x := by rw [h1, one_mul]
  rw [hy', dist_self, zero_mul]

/-- A character trivial exactly on `ℤ_[p]` takes values of modulus one. -/
theorem padicChar_norm (θ : AddChar ℚ_[p] ℂ) (hθ : ∀ x, θ x = 1 ↔ ‖x‖ ≤ 1) (x : ℚ_[p]) :
    ‖θ x‖ = 1 := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ‖x‖ (padic_one_lt (p := p))
  have hpow : θ x ^ (p ^ n) = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, hθ, nsmul_eq_mul, norm_mul, Nat.cast_pow,
      Padic.norm_p_pow]
    rw [zpow_neg, zpow_natCast]
    rw [inv_mul_le_iff₀ (pow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) n), mul_one]
    exact hn.le
  have hnorm : ‖θ x‖ ^ (p ^ n) = 1 := by rw [← norm_pow, hpow, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _)
    (pow_ne_zero n (Fact.out : p.Prime).ne_zero)).mp hnorm

theorem padicChar_quadratic_shift (θ : AddChar ℚ_[p] ℂ) (c x y : ℚ_[p]) :
    θ (c * (y + x) ^ 2) = θ (c * x ^ 2) * θ (2 * c * x * y) * θ (c * y ^ 2) := by
  rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 1
  ring

theorem padicBall_measure_pos_finite (μ : Measure ℚ_[p]) [μ.IsAddHaarMeasure] (s : ℤ) :
    0 < (μ (padicBall p s : Set ℚ_[p])).toReal := by
  apply ENNReal.toReal_pos
  · exact ((padicBall_isOpen s).measure_pos μ ⟨0, (padicBall p s).zero_mem⟩).ne'
  · exact ((padicBall_isCompact s).measure_lt_top).ne

/-- Shrink the domain of a `p`-adic Gaussian to any ball containing the annihilator of a small
ball on which the quadratic phase is trivial. -/
theorem padic_gaussian_ball_eq (θ : AddChar ℚ_[p] ℂ) (hθ : ∀ x, θ x = 1 ↔ ‖x‖ ≤ 1)
    (μ : Measure ℚ_[p]) [μ.IsAddHaarMeasure] (c : ℚ_[p]) (m b s : ℤ)
    (hK : ∀ y ∈ padicBall p m, θ (c * y ^ 2) = 1)
    (hC : ∀ x, (∀ y ∈ padicBall p m, θ (2 * c * x * y) = 1) → x ∈ padicBall p b)
    (hmb : m ≤ b) (hbs : b ≤ s) :
    ∫ y in (padicBall p s : Set ℚ_[p]), θ (c * y ^ 2) ∂μ =
      ∫ y in (padicBall p b : Set ℚ_[p]), θ (c * y ^ 2) ∂μ := by
  have hcont := padicChar_continuous θ hθ
  let χ : ℚ_[p] → AddChar ℚ_[p] ℂ := fun x =>
    θ.compAddMonoidHom (AddMonoidHom.mulLeft (2 * c * x))
  have hχ (x y : ℚ_[p]) : χ x y = θ (2 * c * x * y) := rfl
  refine large_subgroup_phase_integrals_eq μ (padicBall p s) (padicBall p b) (padicBall p m)
    (padicBall_isCompact s) (padicBall_isCompact b) (padicBall_isCompact m)
    (padicBall_measure_pos_finite μ m).ne' (padicBall_mono (hmb.trans hbs))
    (padicBall_mono hmb) (fun y => θ (c * y ^ 2))
    (hcont.comp (continuous_const.mul (continuous_id.pow 2)))
    (fun y => (padicChar_norm θ hθ _).le) χ ?_ ?_ ?_ ?_
  · intro x y hy
    rw [hχ, padicChar_quadratic_shift, hK y hy, mul_one]
  · have : {x : ℚ_[p] | ∀ y ∈ padicBall p m, χ x y = 1} =
        ⋂ y ∈ (padicBall p m : Set ℚ_[p]), {x | θ (2 * c * x * y) = 1} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, SetLike.mem_coe, hχ]
    rw [this]
    apply IsClosed.measurableSet
    apply isClosed_biInter
    intro y _
    exact isClosed_eq (hcont.comp ((continuous_const.mul continuous_id).mul continuous_const))
      continuous_const
  · intro x hx
    exact padicBall_mono hbs (hC x fun y hy => hx y hy)
  · intro x hx
    exact hC x fun y hy => hx y hy

/-- On a ball of radius `p ^ (m + t)`, a function constant on cosets of the radius-`p ^ m` ball
integrates to the corresponding finite coset sum. -/
theorem padic_coset_integral (μ : Measure ℚ_[p]) [μ.IsAddHaarMeasure] (f : ℚ_[p] → ℂ)
    (hf : Continuous f) (m : ℤ) (t : ℕ)
    (hconst : ∀ x ∈ padicBall p (m + t), ∀ y ∈ padicBall p m, f (x + y) = f x) :
    ∫ x in (padicBall p (m + t) : Set ℚ_[p]), f x ∂μ =
      ((μ (padicBall p m : Set ℚ_[p])).toReal : ℂ) *
        ∑ j ∈ Finset.range (p ^ t), f ((j : ℚ_[p]) * (p : ℚ_[p]) ^ (-(m + t))) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  let r : ℕ → ℚ_[p] := fun j => (j : ℚ_[p]) * (p : ℚ_[p]) ^ (-(m + t))
  let S : ℕ → Set ℚ_[p] := fun j => (fun x => x + -r j) ⁻¹' (padicBall p m : Set ℚ_[p])
  have hnorm_r (j : ℕ) : ‖r j‖ ≤ (p : ℝ) ^ (m + t) := by
    simp only [r, norm_mul, Padic.norm_p_zpow, neg_neg]
    calc ‖(j : ℚ_[p])‖ * (p : ℝ) ^ (m + t) ≤ 1 * (p : ℝ) ^ (m + t) := by
          apply mul_le_mul_of_nonneg_right _ (padic_zpow_pos _).le
          exact_mod_cast Padic.norm_int_le_one (j : ℤ)
      _ = (p : ℝ) ^ (m + t) := one_mul _
  have hr (j : ℕ) : r j ∈ padicBall p (m + t) := hnorm_r j
  have hmt : m ≤ m + t := by omega
  have hSsub (j : ℕ) : S j ⊆ padicBall p (m + t) := by
    intro x hx
    have hx' : x + -r j ∈ padicBall p (m + t) := padicBall_mono hmt hx
    have := (padicBall p (m + t)).add_mem hx' (hr j)
    simpa only [neg_add_cancel_right, SetLike.mem_coe] using this
  have hScover : (padicBall p (m + t) : Set ℚ_[p]) = ⋃ j ∈ Finset.range (p ^ t), S j := by
    apply Set.Subset.antisymm
    · intro x hx
      have hx' : ‖x * (p : ℚ_[p]) ^ (m + t)‖ ≤ 1 := by
        rw [norm_mul, Padic.norm_p_zpow]
        calc ‖x‖ * (p : ℝ) ^ (-(m + t)) ≤ (p : ℝ) ^ (m + t) * (p : ℝ) ^ (-(m + t)) :=
              mul_le_mul_of_nonneg_right hx (padic_zpow_pos _).le
          _ = 1 := by
            rw [← zpow_add₀ (by exact_mod_cast (Fact.out : p.Prime).ne_zero), add_neg_cancel,
              zpow_zero]
      let z : ℤ_[p] := ⟨x * (p : ℚ_[p]) ^ (m + t), hx'⟩
      have hspec := PadicInt.appr_spec t z
      obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hspec
      refine Set.mem_biUnion (x := z.appr t) (Finset.mem_range.mpr (PadicInt.appr_lt z t)) ?_
      change ‖x + -r (z.appr t)‖ ≤ (p : ℝ) ^ m
      have hzq : (x * (p : ℚ_[p]) ^ (m + t)) - (z.appr t : ℚ_[p]) =
          (w : ℚ_[p]) * (p : ℚ_[p]) ^ t := by
        have := congrArg (fun q : ℤ_[p] => (q : ℚ_[p])) hw
        simp only [PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast, PadicInt.coe_sub] at this
        rw [← this]
      have hx_eq : x + -r (z.appr t) =
          ((x * (p : ℚ_[p]) ^ (m + t)) - (z.appr t : ℚ_[p])) * (p : ℚ_[p]) ^ (-(m + t)) := by
        simp only [r]
        rw [sub_mul, mul_assoc, ← zpow_add₀ hp0, add_neg_cancel, zpow_zero, mul_one]
        ring
      rw [hx_eq, hzq, norm_mul, norm_mul, Padic.norm_p_pow, Padic.norm_p_zpow, neg_neg]
      calc ‖(w : ℚ_[p])‖ * (p : ℝ) ^ (-(t : ℤ)) * (p : ℝ) ^ (m + t)
          ≤ 1 * (p : ℝ) ^ (-(t : ℤ)) * (p : ℝ) ^ (m + t) := by
            apply mul_le_mul_of_nonneg_right _ (padic_zpow_pos _).le
            exact mul_le_mul_of_nonneg_right (PadicInt.norm_le_one w) (padic_zpow_pos _).le
        _ = (p : ℝ) ^ m := by
            rw [one_mul, ← zpow_add₀ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)]
            congr 1
            ring
    · intro x hx
      obtain ⟨j, _, hxj⟩ := Set.mem_iUnion₂.mp hx
      exact hSsub j hxj
  have hSmeas (j : ℕ) : MeasurableSet (S j) :=
    (padicBall_isCompact m).measurableSet.preimage (measurable_id.add_const _)
  have hSdisj : (↑(Finset.range (p ^ t)) : Set ℕ).Pairwise (Function.onFun Disjoint S) := by
    intro i hi j hj hij
    rw [Function.onFun, Set.disjoint_left]
    intro x hxi hxj
    apply hij
    have hdiff : r j + -r i ∈ padicBall p m := by
      have := (padicBall p m).sub_mem hxi hxj
      have heq : x + -r i - (x + -r j) = r j + -r i := by ring
      rwa [heq] at this
    have hdiff' : ‖(((j : ℤ) - (i : ℤ) : ℤ) : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(t : ℤ)) := by
      have hrr : r j + -r i = (((j : ℤ) - (i : ℤ) : ℤ) : ℚ_[p]) * (p : ℚ_[p]) ^ (-(m + t)) := by
        simp only [r]
        push_cast
        ring
      have h1 := hdiff
      rw [mem_padicBall, hrr, norm_mul, Padic.norm_p_zpow, neg_neg] at h1
      have hpos := padic_zpow_pos (p := p) (m + t)
      rw [← le_div_iff₀ hpos, ← zpow_sub₀ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)] at h1
      convert h1 using 2
      ring
    rw [Padic.norm_int_le_pow_iff_dvd] at hdiff'
    have hi' : i < p ^ t := Finset.mem_range.mp hi
    have hj' : j < p ^ t := Finset.mem_range.mp hj
    have hz := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdiff' (by
      rw [Int.natAbs_pow, Int.natAbs_natCast]
      omega)
    omega
  have hSint (j : ℕ) : IntegrableOn f (S j) μ := by
    have hcomp : IsCompact (S j) := by
      have : S j = (fun y => y + r j) '' (padicBall p m : Set ℚ_[p]) := by
        ext x
        simp only [S, Set.mem_preimage, Set.mem_image]
        constructor
        · intro hx
          exact ⟨x + -r j, hx, by ring⟩
        · rintro ⟨y, hy, rfl⟩
          simpa only [add_neg_cancel_right] using hy
      rw [this]
      exact (padicBall_isCompact m).image (continuous_id.add continuous_const)
    exact hf.continuousOn.integrableOn_compact hcomp
  rw [hScover, integral_biUnion_finset _ (fun j _ => hSmeas j) hSdisj (fun j _ => hSint j),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hval : ∀ x ∈ S j, f x = f (r j) := by
    intro x hx
    have := hconst (r j) (hr j) (x + -r j) hx
    rwa [show r j + (x + -r j) = x by ring] at this
  rw [setIntegral_congr_fun (hSmeas j) hval, setIntegral_const]
  have hmeasS : μ (S j) = μ (padicBall p m : Set ℚ_[p]) :=
    measure_preimage_add_right μ (-r j) _
  rw [measureReal_def, hmeasS, Complex.real_smul, mul_comm]

theorem padic_p_ne_zero : (p : ℚ_[p]) ≠ 0 := by
  exact_mod_cast (Fact.out : p.Prime).ne_zero

theorem padic_real_p_ne_zero : (p : ℝ) ≠ 0 := by
  exact_mod_cast (Fact.out : p.Prime).ne_zero

theorem pz_mul (a b : ℤ) : (p : ℝ) ^ a * (p : ℝ) ^ b = (p : ℝ) ^ (a + b) :=
  (zpow_add₀ padic_real_p_ne_zero a b).symm

theorem pz_le {a b : ℤ} (h : a ≤ b) : (p : ℝ) ^ a ≤ (p : ℝ) ^ b :=
  zpow_le_zpow_right₀ padic_one_lt.le h

theorem pz_le_one {a : ℤ} (h : a ≤ 0) : (p : ℝ) ^ a ≤ 1 := by
  simpa only [zpow_zero] using pz_le (p := p) h

/-- Approximate an integral `p`-adic number by a natural number modulo `p ^ t`. -/
theorem exists_nat_approx (z : ℚ_[p]) (hz : ‖z‖ ≤ 1) (t : ℕ) :
    ∃ j : ℕ, j < p ^ t ∧ ‖z - j‖ ≤ (p : ℝ) ^ (-(t : ℤ)) := by
  let z' : ℤ_[p] := ⟨z, hz⟩
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp (PadicInt.appr_spec t z')
  refine ⟨z'.appr t, PadicInt.appr_lt z' t, ?_⟩
  have h := congrArg (fun q : ℤ_[p] => (q : ℚ_[p])) hw
  simp only [PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast, PadicInt.coe_sub] at h
  change ‖z - ((z'.appr t : ℕ) : ℚ_[p])‖ ≤ _
  have h' : z - ((z'.appr t : ℕ) : ℚ_[p]) = (w : ℚ_[p]) * (p : ℚ_[p]) ^ t := by
    rw [h]
  rw [h', norm_mul, Padic.norm_p_pow]
  calc ‖(w : ℚ_[p])‖ * (p : ℝ) ^ (-(t : ℤ)) ≤ 1 * (p : ℝ) ^ (-(t : ℤ)) :=
        mul_le_mul_of_nonneg_right (PadicInt.norm_le_one w) (padic_zpow_pos _).le
    _ = _ := one_mul _

theorem rational_unit_decomp (c : ℚˣ) :
    ((c : ℚ) : ℚ_[p]) =
      (p : ℚ_[p]) ^ padicValRat p (c : ℚ) * ((rationalUnitPart p c : ℚ) : ℚ_[p]) := by
  have hp : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpk : (p : ℚ) ^ padicValRat p (c : ℚ) ≠ 0 := zpow_ne_zero _ hp
  have hq : (c : ℚ) = (p : ℚ) ^ padicValRat p (c : ℚ) * rationalUnitPart p c := by
    unfold rationalUnitPart
    field_simp
  conv_lhs => rw [hq]
  push_cast
  rfl

theorem rational_unit_norm (c : ℚˣ) : ‖((rationalUnitPart p c : ℚ) : ℚ_[p])‖ = 1 := by
  have hp : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hc : (c : ℚ) ≠ 0 := c.ne_zero
  have hpk : (p : ℚ) ^ padicValRat p (c : ℚ) ≠ 0 := zpow_ne_zero _ hp
  have hu : rationalUnitPart p c ≠ 0 := by
    unfold rationalUnitPart
    exact div_ne_zero hc hpk
  have hval : padicValRat p (rationalUnitPart p c) = 0 := by
    unfold rationalUnitPart
    rw [padicValRat.div hc hpk, padicValRat.zpow, padicValRat.self (Fact.out : p.Prime).one_lt,
      mul_one, sub_self]
  rw [Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero hu, hval, neg_zero, zpow_zero]
  norm_num

/-- Arithmetic consequences of an integer approximation of a rational `p`-adic unit. -/
theorem unit_approx_congr (u : ℚ) (hu : ‖(u : ℚ_[p])‖ = 1) (N : ℤ)
    (hN : ‖(u : ℚ_[p]) - N‖ ≤ (p : ℝ) ^ (-3 : ℤ)) :
    (p : ℤ) ^ 3 ∣ u.num - N * u.den ∧ ¬ (p : ℤ) ∣ u.den ∧ ¬ (p : ℤ) ∣ N := by
  have hlt : ‖(u : ℚ_[p]) - N‖ < 1 :=
    hN.trans_lt (zpow_lt_one_of_neg₀ padic_one_lt (by norm_num))
  have hNnorm : ‖(N : ℚ_[p])‖ = 1 := by
    rw [← hu]
    exact (Padic.norm_eq_of_norm_sub_lt_left (by rw [hu]; exact hlt)).symm
  have hdiv3 : (p : ℤ) ^ 3 ∣ u.num - N * u.den := by
    rw [← Padic.norm_int_le_pow_iff_dvd]
    have heq : (((u.num - N * u.den : ℤ)) : ℚ_[p]) = ((u : ℚ_[p]) - N) * (u.den : ℚ_[p]) := by
      have h1 : ((u.num : ℚ) : ℚ_[p]) = (u : ℚ_[p]) * (u.den : ℚ_[p]) := by
        rw [← Rat.mul_den_eq_num u]
        push_cast
        rfl
      push_cast
      rw [show ((u.num : ℤ) : ℚ_[p]) = ((u.num : ℚ) : ℚ_[p]) by push_cast; rfl, h1]
      ring
    rw [heq, norm_mul]
    calc ‖(u : ℚ_[p]) - N‖ * ‖(u.den : ℚ_[p])‖ ≤ (p : ℝ) ^ (-3 : ℤ) * 1 := by
          apply mul_le_mul hN _ (norm_nonneg _) (padic_zpow_pos _).le
          exact_mod_cast Padic.norm_int_le_one (u.den : ℤ)
      _ = (p : ℝ) ^ (-((3 : ℕ) : ℤ)) := by rw [mul_one]; rfl
  refine ⟨hdiv3, ?_, ?_⟩
  · intro hden
    have hnum : (p : ℤ) ∣ u.num := by
      have h1 : (p : ℤ) ∣ u.num - N * u.den := (dvd_pow_self _ (by norm_num)).trans hdiv3
      have h2 : (p : ℤ) ∣ N * u.den := dvd_mul_of_dvd_right hden N
      have := dvd_add h1 h2
      simpa only [sub_add_cancel] using this
    have hnum' : p ∣ u.num.natAbs := Int.ofNat_dvd_left.mp hnum
    have hden' : p ∣ u.den := by exact_mod_cast hden
    have := Nat.dvd_gcd hnum' hden'
    rw [u.reduced] at this
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp this)
  · intro hNp
    have := Padic.norm_intCast_lt_one_iff.mpr hNp
    rw [hNnorm] at this
    exact lt_irrefl _ this

/-- The Gaussian over a large ball equals the explicit finite coset sum. -/
theorem padic_gaussian_coset_sum (θ : AddChar ℚ_[p] ℂ) (hθ : ∀ x, θ x = 1 ↔ ‖x‖ ≤ 1)
    (hform : ∀ (a : ℤ) (n : ℕ), θ ((a : ℚ_[p]) / (p : ℚ_[p]) ^ n) =
      Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / (p : ℂ) ^ n))
    (μ : Measure ℚ_[p]) [μ.IsAddHaarMeasure] (c u : ℚ_[p]) (N k m : ℤ) (δ ε t e : ℕ)
    (hc : c = (p : ℚ_[p]) ^ k * u) (hu : ‖u‖ = 1) (hN : ‖u - N‖ ≤ (p : ℝ) ^ (-3 : ℤ))
    (hk : k = 2 * m + δ) (hδ : δ ≤ 1) (h2 : ‖(2 : ℚ_[p])‖ = (p : ℝ) ^ (-(ε : ℤ)))
    (ht : t = δ + ε) (he : (e : ℤ) = 2 * t - δ) (he3 : e ≤ 3) (s : ℤ) (hs : m + t ≤ s) :
    ∫ y in (padicBall p s : Set ℚ_[p]), θ (c * y ^ 2) ∂μ =
      ((μ (padicBall p m : Set ℚ_[p])).toReal : ℂ) *
        ∑ j ∈ Finset.range (p ^ t),
          Complex.exp (2 * Real.pi * Complex.I * ((N * (j : ℤ) ^ 2 : ℤ) : ℂ) / (p : ℂ) ^ e) := by
  have hcn : ‖c‖ = (p : ℝ) ^ (-k) := by rw [hc, norm_mul, Padic.norm_p_zpow, hu, mul_one]
  have hsq {y : ℚ_[p]} {a : ℤ} (hy : ‖y‖ ≤ (p : ℝ) ^ a) : ‖y ^ 2‖ ≤ (p : ℝ) ^ (2 * a) := by
    rw [norm_pow, show 2 * a = a + a by ring, ← pz_mul, sq]
    exact mul_le_mul hy hy (norm_nonneg _) (padic_zpow_pos _).le
  have hK : ∀ y ∈ padicBall p m, θ (c * y ^ 2) = 1 := by
    intro y hy
    rw [hθ, norm_mul, hcn]
    calc (p : ℝ) ^ (-k) * ‖y ^ 2‖ ≤ (p : ℝ) ^ (-k) * (p : ℝ) ^ (2 * m) :=
          mul_le_mul_of_nonneg_left (hsq hy) (padic_zpow_pos _).le
      _ ≤ 1 := by rw [pz_mul]; exact pz_le_one (by omega)
  have hC : ∀ x, (∀ y ∈ padicBall p m, θ (2 * c * x * y) = 1) → x ∈ padicBall p (m + t) := by
    intro x hx
    have hy : (p : ℚ_[p]) ^ (-m) ∈ padicBall p m := by
      rw [mem_padicBall, Padic.norm_p_zpow, neg_neg]
    have h := (hθ _).mp (hx _ hy)
    rw [norm_mul, norm_mul, norm_mul, h2, hcn, Padic.norm_p_zpow, neg_neg] at h
    rw [mem_padicBall]
    have hexp : (p : ℝ) ^ (-(ε : ℤ)) * (p : ℝ) ^ (-k) * ‖x‖ * (p : ℝ) ^ m =
        ‖x‖ * (p : ℝ) ^ (-(m + t)) := by
      rw [show ‖x‖ * (p : ℝ) ^ (-(m + t)) =
          ‖x‖ * ((p : ℝ) ^ (-(ε : ℤ)) * (p : ℝ) ^ (-k) * (p : ℝ) ^ m) by
        rw [pz_mul, pz_mul]; congr 2; omega]
      ring
    rw [hexp] at h
    have hpos := padic_zpow_pos (p := p) (-(m + t))
    calc ‖x‖ = ‖x‖ * (p : ℝ) ^ (-(m + t)) * (p : ℝ) ^ (m + t) := by
          rw [mul_assoc, pz_mul, neg_add_cancel, zpow_zero, mul_one]
      _ ≤ 1 * (p : ℝ) ^ (m + t) := mul_le_mul_of_nonneg_right h (padic_zpow_pos _).le
      _ = (p : ℝ) ^ (m + t) := one_mul _
  rw [padic_gaussian_ball_eq θ hθ μ c m (m + t) s hK hC (by omega) hs]
  have hconst : ∀ x ∈ padicBall p (m + t), ∀ y ∈ padicBall p m,
      θ (c * (x + y) ^ 2) = θ (c * x ^ 2) := by
    intro x hx y hy
    rw [add_comm x y, padicChar_quadratic_shift, hK y hy, mul_one]
    have h1 : θ (2 * c * x * y) = 1 := by
      rw [hθ, norm_mul, norm_mul, norm_mul, h2, hcn]
      calc (p : ℝ) ^ (-(ε : ℤ)) * (p : ℝ) ^ (-k) * ‖x‖ * ‖y‖
          ≤ (p : ℝ) ^ (-(ε : ℤ)) * (p : ℝ) ^ (-k) * (p : ℝ) ^ (m + t) * (p : ℝ) ^ m := by
            apply mul_le_mul _ hy (norm_nonneg _) (by positivity)
            exact mul_le_mul_of_nonneg_left hx (by positivity)
        _ ≤ 1 := by
            rw [pz_mul, pz_mul, pz_mul]
            exact pz_le_one (by omega)
    rw [h1, mul_one]
  have hcont := padicChar_continuous θ hθ
  rw [padic_coset_integral μ (fun y => θ (c * y ^ 2))
    (hcont.comp (continuous_const.mul (continuous_id.pow 2))) m t hconst]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have hval : c * ((j : ℚ_[p]) * (p : ℚ_[p]) ^ (-(m + t))) ^ 2 =
      ((N * (j : ℤ) ^ 2 : ℤ) : ℚ_[p]) / (p : ℚ_[p]) ^ e +
        (u - N) * (j : ℚ_[p]) ^ 2 * (p : ℚ_[p]) ^ (-(e : ℤ)) := by
    have hpe : (p : ℚ_[p]) ^ k * ((p : ℚ_[p]) ^ (-(m + t))) ^ 2 = (p : ℚ_[p]) ^ (-(e : ℤ)) := by
      rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ padic_p_ne_zero]
      congr 1
      push_cast
      omega
    rw [hc, div_eq_mul_inv, show ((p : ℚ_[p]) ^ e)⁻¹ = (p : ℚ_[p]) ^ (-(e : ℤ)) by
      rw [zpow_neg, zpow_natCast]]
    calc (p : ℚ_[p]) ^ k * u * ((j : ℚ_[p]) * (p : ℚ_[p]) ^ (-(m + t))) ^ 2 =
        u * (j : ℚ_[p]) ^ 2 * ((p : ℚ_[p]) ^ k * ((p : ℚ_[p]) ^ (-(m + t))) ^ 2) := by ring
      _ = _ := by rw [hpe]; push_cast; ring
  change θ (c * ((j : ℚ_[p]) * (p : ℚ_[p]) ^ (-(m + t))) ^ 2) = _
  rw [hval, AddChar.map_add_eq_mul, hform]
  have hsmall : θ ((u - N) * (j : ℚ_[p]) ^ 2 * (p : ℚ_[p]) ^ (-(e : ℤ))) = 1 := by
    rw [hθ, norm_mul, norm_mul, Padic.norm_p_zpow, neg_neg, norm_pow]
    have hj : ‖(j : ℚ_[p])‖ ≤ 1 := by exact_mod_cast Padic.norm_int_le_one (j : ℤ)
    calc ‖u - N‖ * ‖(j : ℚ_[p])‖ ^ 2 * (p : ℝ) ^ (e : ℤ) ≤ (p : ℝ) ^ (-3 : ℤ) * 1 * (p : ℝ) ^ (e : ℤ) := by
          apply mul_le_mul_of_nonneg_right _ (padic_zpow_pos _).le
          apply mul_le_mul hN _ (by positivity) (padic_zpow_pos _).le
          exact pow_le_one₀ (norm_nonneg _) hj
      _ ≤ 1 := by rw [mul_one, pz_mul]; exact pz_le_one (by omega)
  rw [hsmall, mul_one]

theorem dyadic_even_sum (N : ℤ) (r8 : ℕ) (q : ℤ) (hN : N = r8 + 8 * q) :
    ∑ j ∈ Finset.range 2,
        Complex.exp (2 * Real.pi * Complex.I * ((N * (j : ℤ) ^ 2 : ℤ) : ℂ) / (2 : ℂ) ^ 2) =
      1 + Complex.I ^ r8 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  push_cast
  have h0 : Complex.exp (2 * Real.pi * Complex.I * (N * 0) / 2 ^ 2) = 1 := by
    simp
  have h1 : Complex.exp (2 * Real.pi * Complex.I * (N * 1) / 2 ^ 2) = Complex.I ^ r8 := by
    rw [hN]
    push_cast
    have : 2 * (Real.pi : ℂ) * Complex.I * ((r8 + 8 * q) * 1) / 2 ^ 2 =
        (r8 : ℂ) * ((Real.pi : ℂ) / 2 * Complex.I) + ((2 * q : ℤ) : ℂ) *
          (2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [this, Complex.exp_add, Complex.exp_nat_mul, Complex.exp_pi_div_two_mul_I,
      Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [h0, h1]

theorem dyadic_odd_sum (N : ℤ) (r8 : ℕ) (q : ℤ) (hN : N = r8 + 8 * q) (hodd : Odd N) :
    ∑ j ∈ Finset.range 4,
        Complex.exp (2 * Real.pi * Complex.I * ((N * (j : ℤ) ^ 2 : ℤ) : ℂ) / (2 : ℂ) ^ 3) =
      2 * Complex.exp (Real.pi * Complex.I * (r8 : ℂ) / 4) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  push_cast
  set E := Complex.exp (Real.pi * Complex.I * (r8 : ℂ) / 4) with hE
  have h1 : Complex.exp (2 * Real.pi * Complex.I * (N * 1) / 2 ^ 3) = E := by
    rw [hN]
    push_cast
    have : 2 * (Real.pi : ℂ) * Complex.I * ((r8 + 8 * q) * 1) / 2 ^ 3 =
        (Real.pi * Complex.I * (r8 : ℂ) / 4) + (q : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have h2 : Complex.exp (2 * Real.pi * Complex.I * (N * 4) / 2 ^ 3) = -1 := by
    have : 2 * (Real.pi : ℂ) * Complex.I * (N * 4) / 2 ^ 3 =
        (N : ℂ) * ((Real.pi : ℂ) * Complex.I) := by ring
    rw [this, Complex.exp_int_mul, Complex.exp_pi_mul_I, Odd.neg_one_zpow hodd]
  have h3 : Complex.exp (2 * Real.pi * Complex.I * (N * 9) / 2 ^ 3) = E := by
    have : 2 * (Real.pi : ℂ) * Complex.I * (N * 9) / 2 ^ 3 =
        2 * Real.pi * Complex.I * (N * 1) / 2 ^ 3 + (N : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      ring
    rw [this, Complex.exp_add, h1, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have h0 : Complex.exp (2 * Real.pi * Complex.I * (N * 0) / 2 ^ 3) = 1 := by simp
  rw [h0, h1, h2, h3]
  ring

theorem dyadic_residue_congr (c : ℚˣ) (N : ℤ)
    (h3 : (2 : ℤ) ^ 3 ∣ (rationalUnitPart 2 c).num - N * (rationalUnitPart 2 c).den)
    (hden : ¬ (2 : ℤ) ∣ (rationalUnitPart 2 c).den) :
    ∃ q : ℤ, N = (rationalDyadicResidue c : ℤ) + 8 * q := by
  set u := rationalUnitPart 2 c with hu
  have hcop : Nat.Coprime u.den 8 := by
    have h2 : Nat.Coprime u.den 2 := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
      intro h
      exact hden (by exact_mod_cast h)
    simpa using Nat.Coprime.pow_right 3 h2
  have hinv : (u.den : ZMod 8) * (u.den : ZMod 8)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one u.den hcop
  have hnum : (u.num : ZMod 8) = (N : ZMod 8) * (u.den : ZMod 8) := by
    have h := (ZMod.intCast_eq_intCast_iff_dvd_sub (N * u.den) u.num 8).mpr
      (by norm_num at h3 ⊢; exact h3)
    push_cast at h
    exact h.symm
  have hres : ((rationalDyadicResidue c : ℕ) : ZMod 8) = (N : ZMod 8) := by
    unfold rationalDyadicResidue
    simp only []
    rw [← hu, ZMod.natCast_zmod_val, hnum, mul_assoc, hinv, mul_one]
  have hdvd : (8 : ℤ) ∣ N - (rationalDyadicResidue c : ℤ) := by
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub ((rationalDyadicResidue c : ℕ) : ℤ) N 8).mp
      (by push_cast; exact hres)
    exact_mod_cast this
  obtain ⟨q, hq⟩ := hdvd
  exact ⟨q, by omega⟩

theorem odd_prime_coset_sum (hp2 : p ≠ 2) (N : ℤ) (hN : ¬ (p : ℤ) ∣ N) :
    ∑ j ∈ Finset.range (p ^ 1),
        Complex.exp (2 * Real.pi * Complex.I * ((N * (j : ℤ) ^ 2 : ℤ) : ℂ) / (p : ℂ) ^ 1) =
      (quadraticChar (ZMod p) (N : ZMod p) : ℂ) *
        (if p % 4 = 1 then 1 else Complex.I) * (Real.sqrt (p : ℝ) : ℂ) := by
  have hN0 : (N : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hN
  have hg := rational_odd_gauss_sum p hp2 (Units.mk0 (N : ZMod p) hN0)
  rw [Units.val_mk0] at hg
  rw [← hg, pow_one, pow_one]
  refine Finset.sum_bij' (fun (j : ℕ) _ => ((j : ℕ) : ZMod p)) (fun (x : ZMod p) _ => x.val)
    ?_ ?_ ?_ ?_ ?_
  · intro j _
    exact Finset.mem_univ _
  · intro x _
    exact Finset.mem_range.mpr (ZMod.val_lt x)
  · intro j hj
    exact ZMod.val_cast_of_lt (Finset.mem_range.mp hj)
  · intro x _
    exact ZMod.natCast_zmod_val x
  · intro j _
    have := ZMod.stdAddChar_coe (N := p) (N * (j : ℤ) ^ 2)
    push_cast at this ⊢
    rw [this]

theorem odd_prime_jacobi (u : ℚ) (N : ℤ) (h3 : (p : ℤ) ^ 3 ∣ u.num - N * u.den)
    (hden : ¬ (p : ℤ) ∣ u.den) :
    quadraticChar (ZMod p) (N : ZMod p) = jacobiSym (u.num * u.den) p := by
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  change quadraticChar (ZMod p) (N : ZMod p) = quadraticChar (ZMod p) ((u.num * u.den : ℤ) : ZMod p)
  have hnum : (u.num : ZMod p) = (N : ZMod p) * (u.den : ZMod p) := by
    have h1 : (p : ℤ) ∣ u.num - N * u.den := (dvd_pow_self _ (by norm_num)).trans h3
    have h := (ZMod.intCast_eq_intCast_iff_dvd_sub (N * u.den) u.num p).mpr h1
    push_cast at h
    exact h.symm
  have hden0 : (u.den : ZMod p) ≠ 0 := by
    intro h
    apply hden
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (u.den : ℤ) p).mp (by exact_mod_cast h)
    exact this
  push_cast
  rw [hnum, mul_assoc, ← sq, map_mul, quadraticChar_sq_one' hden0, mul_one]

/-- The stabilized one-dimensional `p`-adic Gaussian is a positive multiple of the explicit
rational phase. -/
theorem padic_gaussian_phase (q : Nat.Primes) [Fact (q : ℕ).Prime] (θ : AddChar ℚ_[q] ℂ)
    (hθ : ∀ x, θ x = 1 ↔ ‖x‖ ≤ 1)
    (hform : ∀ (a : ℤ) (n : ℕ), θ ((a : ℚ_[q]) / ((q : ℕ) : ℚ_[q]) ^ n) =
      Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / ((q : ℕ) : ℂ) ^ n))
    (μ : Measure ℚ_[q]) [μ.IsAddHaarMeasure] (c : ℚˣ) :
    ∃ s0 : ℤ, ∀ s, s0 ≤ s → ∃ r : ℝ, 0 < r ∧
      ∫ y in (padicBall q s : Set ℚ_[q]), θ (((c : ℚ) : ℚ_[q]) * y ^ 2) ∂μ =
        r * rationalPrimePhase q c := by
  obtain ⟨m, hm⟩ := Int.even_or_odd' (padicValRat q (c : ℚ))
  obtain ⟨Nn, -, hNn⟩ := exists_nat_approx (p := q)
    ((rationalUnitPart q c : ℚ) : ℚ_[q]) (rational_unit_norm c).le 3
  have hN : ‖((rationalUnitPart q c : ℚ) : ℚ_[q]) - (((Nn : ℤ)) : ℚ_[q])‖ ≤
      ((q : ℕ) : ℝ) ^ (-3 : ℤ) := by
    simpa only [Int.cast_natCast, Nat.cast_ofNat] using hNn
  obtain ⟨h3, hden, hNp⟩ := unit_approx_congr _ (rational_unit_norm c) (Nn : ℤ) hN
  have hKpos := padicBall_measure_pos_finite (p := q) μ m
  set K := (μ (padicBall q m : Set ℚ_[q])).toReal with hKdef
  by_cases hp2 : (q : ℕ) = 2
  · have h2 : ‖(2 : ℚ_[q])‖ = ((q : ℕ) : ℝ) ^ (-((1 : ℕ) : ℤ)) := by
      have : (2 : ℚ_[q]) = ((q : ℕ) : ℚ_[q]) := by exact_mod_cast hp2.symm
      rw [this, Padic.norm_p, Nat.cast_one, zpow_neg_one]
    have hu2 : rationalUnitPart q c = rationalUnitPart 2 c := by rw [hp2]
    have hq2 : ((q : ℕ) : ℤ) = 2 := by exact_mod_cast hp2
    have h3' := h3
    have hden' := hden
    rw [hu2, hq2] at h3'
    rw [hu2, hq2] at hden'
    obtain ⟨qq, hqq⟩ := dyadic_residue_congr c (Nn : ℤ) h3' hden'
    rcases hm with hk | hk
    · refine ⟨m + 1, fun s hs => ⟨K * Real.sqrt 2, by positivity, ?_⟩⟩
      rw [padic_gaussian_coset_sum θ hθ hform μ _ _ (Nn : ℤ) _ m 0 1 1 2
        (rational_unit_decomp c) (rational_unit_norm c) hN (by rw [hk]; push_cast; ring)
        (by norm_num) h2 rfl (by norm_num) (by norm_num) s (by push_cast; omega)]
      have hsum : ∑ j ∈ Finset.range ((q : ℕ) ^ 1),
          Complex.exp (2 * Real.pi * Complex.I * (((Nn : ℤ) * (j : ℤ) ^ 2 : ℤ) : ℂ) /
            ((q : ℕ) : ℂ) ^ 2) = 1 + Complex.I ^ rationalDyadicResidue c := by
        have := dyadic_even_sum (Nn : ℤ) (rationalDyadicResidue c) qq hqq
        rw [hp2]
        simpa using this
      rw [hsum]
      unfold rationalPrimePhase
      simp only []
      rw [if_pos hp2, if_pos (show Even (padicValRat (q : ℕ) (c : ℚ)) by rw [hk]; exact even_two_mul m)]
      have hs2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
        exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
      rw [← hKdef]
      push_cast
      field_simp
    · refine ⟨m + 2, fun s hs => ⟨K * 2, by positivity, ?_⟩⟩
      rw [padic_gaussian_coset_sum θ hθ hform μ _ _ (Nn : ℤ) _ m 1 1 2 3
        (rational_unit_decomp c) (rational_unit_norm c) hN (by rw [hk]; push_cast; ring)
        (by norm_num) h2 rfl (by norm_num) (by norm_num) s (by push_cast; omega)]
      have hodd : Odd (Nn : ℤ) := by
        apply Int.not_even_iff_odd.mp
        rw [even_iff_two_dvd]
        intro h
        exact hNp (by rw [hq2]; exact h)
      have hsum : ∑ j ∈ Finset.range ((q : ℕ) ^ 2),
          Complex.exp (2 * Real.pi * Complex.I * (((Nn : ℤ) * (j : ℤ) ^ 2 : ℤ) : ℂ) /
            ((q : ℕ) : ℂ) ^ 3) =
            2 * Complex.exp (Real.pi * Complex.I * (rationalDyadicResidue c : ℂ) / 4) := by
        have := dyadic_odd_sum (Nn : ℤ) (rationalDyadicResidue c) qq hqq hodd
        rw [hp2]
        simpa using this
      rw [hsum]
      unfold rationalPrimePhase
      simp only []
      rw [if_pos hp2, if_neg (show ¬ Even (padicValRat (q : ℕ) (c : ℚ)) by
        rw [hk]; exact Int.not_even_iff_odd.mpr (odd_two_mul_add_one m))]
      rw [← hKdef]
      push_cast
      ring
  · have h2 : ‖(2 : ℚ_[q])‖ = ((q : ℕ) : ℝ) ^ (-((0 : ℕ) : ℤ)) := by
      have : ‖((2 : ℕ) : ℚ_[q])‖ = 1 := by
        rw [Padic.norm_natCast_eq_one_iff]
        exact (Nat.coprime_primes q.2 Nat.prime_two).mpr hp2
      simpa using this
    rcases hm with hk | hk
    · refine ⟨m, fun s hs => ⟨K, hKpos, ?_⟩⟩
      rw [padic_gaussian_coset_sum θ hθ hform μ _ _ (Nn : ℤ) _ m 0 0 0 0
        (rational_unit_decomp c) (rational_unit_norm c) hN (by rw [hk]; push_cast; ring)
        (by norm_num) h2 rfl (by norm_num) (by norm_num) s (by push_cast; omega)]
      unfold rationalPrimePhase
      simp only []
      rw [if_neg hp2, if_pos (show Even (padicValRat (q : ℕ) (c : ℚ)) by rw [hk]; exact even_two_mul m)]
      rw [← hKdef]
      simp
    · have hqpos : (0 : ℝ) < ((q : ℕ) : ℝ) := by exact_mod_cast q.2.pos
      refine ⟨m + 1, fun s hs => ⟨K * Real.sqrt ((q : ℕ) : ℝ),
        mul_pos hKpos (Real.sqrt_pos.mpr hqpos), ?_⟩⟩
      rw [padic_gaussian_coset_sum θ hθ hform μ _ _ (Nn : ℤ) _ m 1 0 1 1
        (rational_unit_decomp c) (rational_unit_norm c) hN (by rw [hk]; push_cast; ring)
        (by norm_num) h2 rfl (by norm_num) (by norm_num) s (by push_cast; omega)]
      rw [odd_prime_coset_sum hp2 (Nn : ℤ) (fun h => hNp (by exact_mod_cast h)),
        odd_prime_jacobi _ (Nn : ℤ) h3 hden]
      unfold rationalPrimePhase
      simp only []
      rw [if_neg hp2, if_neg (show ¬ Even (padicValRat (q : ℕ) (c : ℚ)) by
        rw [hk]; exact Int.not_even_iff_odd.mpr (odd_two_mul_add_one m))]
      rw [← hKdef]
      push_cast
      ring

end ArtinPrimitiveRoots.Proofs.weil_trace_opus
