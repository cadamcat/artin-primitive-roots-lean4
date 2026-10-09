import ArtinPrimitiveRoots.Ext.TypeIIInputs

/-! A first-derivative estimate for logarithmic phases on a natural interval. -/

namespace ArtinPrimitiveRoots.Proofs.pp_phase_p

open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.Ext.TypeIIInputs
open NormedSpace

private lemma log_step_lower {x : ℝ} (hx : 0 < x) :
    1 / (x + 1) ≤ Real.log (x + 1) - Real.log x := by
  have hx1 : 0 < x + 1 := by positivity
  rw [← Real.log_div hx1.ne' hx.ne']
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hx1 hx)
  convert h using 1 <;> field_simp <;> ring

private lemma log_step_upper {x : ℝ} (hx : 0 < x) :
    Real.log (x + 1) - Real.log x ≤ 1 / x := by
  have hx1 : 0 < x + 1 := by positivity
  rw [← Real.log_div hx1.ne' hx.ne']
  have h := Real.log_le_sub_one_of_pos (div_pos hx1 hx)
  convert h using 1 <;> field_simp <;> ring

private lemma log_step_antitone {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    Real.log (y + 1) - Real.log y ≤ Real.log (x + 1) - Real.log x := by
  have hy : 0 < y := hx.trans_le hxy
  rw [← Real.log_div (by positivity : x + 1 ≠ 0) hx.ne',
    ← Real.log_div (by positivity : y + 1 ≠ 0) hy.ne']
  apply Real.log_le_log (by positivity)
  apply (div_le_div_iff₀ hy hx).mpr
  nlinarith

private lemma additiveCharacter_nat_add (n : ℕ) (t : ℝ) :
    additiveCharacter ((n : ℝ) + t) = additiveCharacter t := by
  unfold additiveCharacter
  have hn : Complex.exp ((n : ℂ) * (2 * Real.pi * Complex.I)) = 1 := by
    convert Complex.exp_int_mul_two_pi_mul_I (n : ℤ) using 1 <;> push_cast <;> ring
  push_cast
  rw [show Complex.I * (2 * Real.pi * ((n : ℂ) + t)) =
      (n : ℂ) * (2 * Real.pi * Complex.I) + Complex.I * (2 * Real.pi * t) by ring,
    Complex.exp_add, hn, one_mul]

private lemma additiveCharacter_log_neg (z x : ℝ) :
    additiveCharacter (-z / (2 * Real.pi) * Real.log x) =
      Complex.exp (-Complex.I * z * (Real.log x : ℂ)) := by
  unfold additiveCharacter
  congr 1
  push_cast
  field_simp
  <;> ring

theorem logPhase_first_derivative_interval {U θ Z : ℝ}
    (hU : 1 ≤ U) (hZ : 0 < Z) (hZU : Z ≤ U)
    (L R : ℕ) (hL : U ≤ (L : ℝ) + θ)
    (hR : (R : ℝ) + θ ≤ 2 * U) :
    ‖∑ n ∈ Finset.Icc L R,
        Complex.exp (Complex.I * Z * (Real.log ((n : ℝ) + θ : ℝ) : ℂ))‖ ≤
      32 * Real.pi * U / Z := by
  let N := R + 1 - L
  let f : ℕ → ℝ := fun i => (i : ℝ) - Z / (2 * Real.pi) *
    Real.log (((L + i : ℕ) : ℝ) + θ)
  let β : ℝ := Z / (16 * Real.pi * U)
  have hU0 : 0 < U := by linarith
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβle : β ≤ 1 / 2 := by
    dsimp [β]
    have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 16 * Real.pi * U)]
    calc
      Z ≤ U := hZU
      _ ≤ 8 * Real.pi * U := by nlinarith [Real.pi_gt_three, hU0]
      _ = 1 / 2 * (16 * Real.pi * U) := by ring
  have hstep (i : ℕ) (hi : i < N) :
      β ≤ f (i + 1) - f i ∧ f (i + 1) - f i ≤ 1 - β := by
    have hidx : L + i ≤ R := by
      dsimp [N] at hi
      omega
    have hLnat : L ≤ L + i := Nat.le_add_right L i
    have hLreal : (L : ℝ) ≤ ((L + i : ℕ) : ℝ) := by exact_mod_cast hLnat
    have hu : U ≤ ((L + i : ℕ) : ℝ) + θ := by
      exact hL.trans (by nlinarith [hLreal])
    have hidxR : ((L + i : ℕ) : ℝ) ≤ (R : ℝ) := by exact_mod_cast hidx
    have huR : ((L + i : ℕ) : ℝ) + θ ≤ 2 * U := by
      have htmp : ((L + i : ℕ) : ℝ) + θ ≤ (R : ℝ) + θ := by
        linarith [hidxR]
      exact htmp.trans hR
    have hu0 : 0 < ((L + i : ℕ) : ℝ) + θ := by linarith
    have hu1 : ((L + i : ℕ) : ℝ) + θ + 1 ≤ 3 * U := by linarith [hU]
    have hloglo := log_step_lower hu0
    have hloghi := log_step_upper hu0
    have hdeltaLo : Z / (2 * Real.pi) *
        (Real.log ((((L + i : ℕ) : ℝ) + θ) + 1) -
          Real.log (((L + i : ℕ) : ℝ) + θ)) ≥ β := by
      let c := Z / (2 * Real.pi)
      have hc : 0 ≤ c := by dsimp [c]; positivity
      have hmul := mul_le_mul_of_nonneg_left hloglo hc
      have hden : 1 / ((((L + i : ℕ) : ℝ) + θ) + 1) ≥ 1 / (3 * U) := by
        exact one_div_le_one_div_of_le (by positivity) hu1
      have hmulden := mul_le_mul_of_nonneg_left hden hc
      have hsmall : Z / (16 * Real.pi * U) ≤ Z / (6 * Real.pi * U) := by
        have hdenom : 6 * Real.pi * U ≤ 16 * Real.pi * U := by
          nlinarith [Real.pi_gt_three, hU0]
        have hinv : 1 / (16 * Real.pi * U) ≤ 1 / (6 * Real.pi * U) :=
          one_div_le_one_div_of_le (by positivity) hdenom
        calc
          Z / (16 * Real.pi * U) = Z * (1 / (16 * Real.pi * U)) := by ring
          _ ≤ Z * (1 / (6 * Real.pi * U)) :=
            mul_le_mul_of_nonneg_left hinv hZ.le
          _ = Z / (6 * Real.pi * U) := by ring
      dsimp [β, c]
      calc
        Z / (16 * Real.pi * U) ≤ Z / (6 * Real.pi * U) := hsmall
        _ = (Z / (2 * Real.pi)) * (1 / (3 * U)) := by ring
        _ ≤ (Z / (2 * Real.pi)) *
              (1 / ((((L + i : ℕ) : ℝ) + θ) + 1)) := hmulden
        _ ≤ (Z / (2 * Real.pi)) *
              (Real.log ((((L + i : ℕ) : ℝ) + θ) + 1) -
                Real.log (((L + i : ℕ) : ℝ) + θ)) := hmul
    have hdeltaHi : Z / (2 * Real.pi) *
        (Real.log ((((L + i : ℕ) : ℝ) + θ) + 1) -
          Real.log (((L + i : ℕ) : ℝ) + θ)) ≤ 1 / 2 := by
      let c := Z / (2 * Real.pi)
      have hc : 0 ≤ c := by dsimp [c]; positivity
      have huinv : 1 / (((L + i : ℕ) : ℝ) + θ) ≤ 1 / U :=
        one_div_le_one_div_of_le (by positivity) hu
      have hh := mul_le_mul_of_nonneg_left hloghi hc
      have hmulInv := mul_le_mul_of_nonneg_left huinv hc
      have hz : Z / (2 * Real.pi * U) ≤ 1 / 2 := by
        apply (div_le_iff₀ (by positivity)).2
        have hpiU : U ≤ Real.pi * U := by
          have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
          simpa using mul_le_mul_of_nonneg_right hpi hU0.le
        nlinarith [hZU, hpiU]
      calc
        _ ≤ (Z / (2 * Real.pi)) * (1 / (((L + i : ℕ) : ℝ) + θ)) := hh
        _ ≤ (Z / (2 * Real.pi)) * (1 / U) := hmulInv
        _ = Z / (2 * Real.pi * U) := by ring
        _ ≤ 1 / 2 := hz
    have hinc : f (i + 1) - f i = 1 - Z / (2 * Real.pi) *
        (Real.log ((((L + i : ℕ) : ℝ) + θ) + 1) -
          Real.log (((L + i : ℕ) : ℝ) + θ)) := by
      dsimp [f]
      push_cast
      ring
    rw [hinc]
    constructor
    · dsimp [β]
      have hβle : β ≤ 1 / 2 := hβle
      linarith
    · linarith [hdeltaLo]
  have hmono : MonotoneOn (fun i : ℕ => f (i + 1) - f i) (Set.Icc 0 N) := by
    intro i hi j hj hij
    have hLreal : (L : ℝ) ≤ ((L + i : ℕ) : ℝ) := by
      exact_mod_cast (Nat.le_add_right L i)
    have hu_i_le : U ≤ ((L + i : ℕ) : ℝ) + θ := by
      exact hL.trans (by nlinarith [hLreal])
    have hu_i : 0 < ((L + i : ℕ) : ℝ) + θ := hU0.trans_le hu_i_le
    have hxy : ((L + i : ℕ) : ℝ) + θ ≤ ((L + j : ℕ) : ℝ) + θ := by
      have hij' : L + i ≤ L + j := Nat.add_le_add_left hij L
      have hijReal : ((L + i : ℕ) : ℝ) ≤ ((L + j : ℕ) : ℝ) := by
        exact_mod_cast hij'
      nlinarith
    have hlog := log_step_antitone hu_i hxy
    have hi_inc : f (i + 1) - f i = 1 - Z / (2 * Real.pi) *
        (Real.log ((((L + i : ℕ) : ℝ) + θ) + 1) -
          Real.log (((L + i : ℕ) : ℝ) + θ)) := by
      dsimp [f]
      push_cast
      ring
    have hj_inc : f (j + 1) - f j = 1 - Z / (2 * Real.pi) *
        (Real.log ((((L + j : ℕ) : ℝ) + θ) + 1) -
          Real.log (((L + j : ℕ) : ℝ) + θ)) := by
      dsimp [f]
      push_cast
      ring
    change f (i + 1) - f i ≤ f (j + 1) - f j
    rw [hi_inc, hj_inc]
    have hcoef : 0 ≤ Z / (2 * Real.pi) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hlog hcoef
    linarith
  have htest := derivative_test f N β hβ
    (fun i hi => (hstep i hi).1) (fun i hi => (hstep i hi).2) hmono
  have hsum :
      (∑ n ∈ Finset.Icc L R,
        additiveCharacter (-Z / (2 * Real.pi) * Real.log ((n : ℝ) + θ))) =
      ∑ i ∈ Finset.range N, additiveCharacter (f i) := by
    have hset : Finset.Icc L R = Finset.Ico L (R + 1) := by
      ext n
      simp
    rw [hset, Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    have harg : f i = (i : ℝ) +
        (-Z / (2 * Real.pi) * Real.log (((L + i : ℕ) : ℝ) + θ)) := by
      dsimp [f]
      ring
    rw [harg, additiveCharacter_nat_add]
  have hphase (n : ℕ) :
      additiveCharacter (-Z / (2 * Real.pi) * Real.log ((n : ℝ) + θ)) =
        star (Complex.exp (Complex.I * Z * (Real.log ((n : ℝ) + θ) : ℂ))) := by
    rw [additiveCharacter_log_neg]
    simp only [Complex.star_def]
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  have hnorm :
      ‖∑ n ∈ Finset.Icc L R,
        Complex.exp (Complex.I * Z * (Real.log ((n : ℝ) + θ) : ℂ))‖ =
      ‖∑ n ∈ Finset.Icc L R,
        additiveCharacter (-Z / (2 * Real.pi) * Real.log ((n : ℝ) + θ))‖ := by
    have hsumstar :
        (∑ n ∈ Finset.Icc L R,
          additiveCharacter (-Z / (2 * Real.pi) * Real.log ((n : ℝ) + θ))) =
        star (∑ n ∈ Finset.Icc L R,
          Complex.exp (Complex.I * Z * (Real.log ((n : ℝ) + θ) : ℂ))) := by
      calc
        _ = ∑ n ∈ Finset.Icc L R,
            star (Complex.exp (Complex.I * Z * (Real.log ((n : ℝ) + θ) : ℂ))) := by
              apply Finset.sum_congr rfl
              intro n hn
              exact hphase n
        _ = _ := by simp only [star_sum]
    rw [hsumstar, norm_star]
  rw [hnorm, hsum]
  have hbound := htest
  dsimp [β] at hbound
  have hpos : 0 < Z := hZ
  calc
    _ ≤ 2 / β := hbound
    _ = 32 * Real.pi * U / Z := by
      dsimp [β]
      field_simp
      <;> ring

end ArtinPrimitiveRoots.Proofs.pp_phase_p
