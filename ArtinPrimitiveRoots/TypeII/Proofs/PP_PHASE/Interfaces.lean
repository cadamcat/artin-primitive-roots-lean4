import ArtinPrimitiveRoots.TypeII.PP.Defs
import ArtinPrimitiveRoots.TypeII.Proofs.PP_PHASE.LogPhaseLow
import ArtinPrimitiveRoots.TypeII.Proofs.PP_PHASE.PhaseReindex
import ArtinPrimitiveRoots.TypeII.Proofs.PP_PHASE.TorusMoment

/-! Exact interfaces for the PP-PHASE decomposition. -/

namespace ArtinPrimitiveRoots.Proofs.pp_phase_p

open MeasureTheory
open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.TypeII.PP
open scoped ComplexConjugate ENNReal

def phaseMeanValueInput : Prop :=
  ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
    ∀ k : ℕ, 2 ≤ k →
      ∃ s : ℕ, k ≤ s ∧ (s : ℝ) ≤ C₁ * (k : ℝ) ^ 4 ∧
        ∀ M : ℕ, 1 ≤ M →
          (vinogradovCount s k M : ℝ) ≤
            Real.exp (C₁ * Real.rpow (k : ℝ) C₂) *
              Real.rpow (M : ℝ)
                (2 * (s : ℝ) - ((k : ℝ) * ((k : ℝ) + 1)) / 2 + 1 / 100 : ℝ)

noncomputable def phaseCoefficient (v θ : ℝ) (b j : ℕ) : ℝ :=
  (-1 : ℝ) ^ j * v /
    (2 * Real.pi * ((j + 1 : ℕ) : ℝ) * ((b : ℝ) + θ) ^ (j + 1))

noncomputable def phasePolynomialSum (v θ : ℝ) (b k M : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 M,
    additiveCharacter
      (∑ j : Fin k, phaseCoefficient v θ b j.val * (h : ℝ) ^ (j.val + 1))

private theorem phase_exp_I_mul_lipschitz (x y : ℝ) :
    ‖Complex.exp (Complex.I * x) - Complex.exp (Complex.I * y)‖ ≤ |x - y| := by
  have hfactor : Complex.exp (Complex.I * x) - Complex.exp (Complex.I * y) =
      Complex.exp (Complex.I * y) * (Complex.exp (Complex.I * (x - y)) - 1) := by
    rw [show Complex.I * x = Complex.I * y + Complex.I * (x - y) by ring,
      Complex.exp_add]
    ring
  have hyNorm : ‖Complex.exp (Complex.I * y)‖ = 1 := by
    simp [Complex.norm_exp, Complex.mul_re]
  calc
    ‖Complex.exp (Complex.I * x) - Complex.exp (Complex.I * y)‖ =
        ‖Complex.exp (Complex.I * y) *
          (Complex.exp (Complex.I * (x - y)) - 1)‖ := by rw [hfactor]
    _ = ‖Complex.exp (Complex.I * y)‖ *
          ‖Complex.exp (Complex.I * (x - y)) - 1‖ := by rw [norm_mul]
    _ = ‖Complex.exp (Complex.I * (x - y)) - 1‖ := by rw [hyNorm, one_mul]
    _ ≤ |x - y| := by
      have harg : Complex.I * ((x : ℂ) - (y : ℂ)) =
          Complex.I * ((x - y : ℝ) : ℂ) := by
        push_cast
        ring
      have h := @Real.norm_exp_I_mul_ofReal_sub_one_le (x - y)
      rw [harg]
      simpa only [Real.norm_eq_abs] using h

private theorem phase_sum_Icc_shift_reindex (f : ℕ → ℂ) (l u t : ℕ) :
    (∑ b ∈ Finset.Icc l u, f (b + t)) =
      ∑ b ∈ Finset.Icc (l + t) (u + t), f b := by
  classical
  have hinj : Set.InjOn (fun b : ℕ => b + t) (Finset.Icc l u : Set ℕ) := by
    intro b hb c hc h
    exact Nat.add_right_cancel h
  calc
    _ = ∑ b ∈ (Finset.Icc l u).image (fun b : ℕ => b + t), f b := by
      symm
      exact Finset.sum_image hinj
    _ = ∑ b ∈ Finset.Icc (l + t) (u + t), f b := by simp

private theorem phase_sum_Icc_shift_step {l u : ℕ} (hlu : l ≤ u)
    (f : ℕ → ℂ) (t : ℕ) :
    (∑ b ∈ Finset.Icc l u, f (b + t)) -
        ∑ b ∈ Finset.Icc l u, f (b + t + 1) =
      f (l + t) - f (u + t + 1) := by
  have h₀ := phase_sum_Icc_shift_reindex f l u t
  have h₁ := phase_sum_Icc_shift_reindex f l u (t + 1)
  have h₁' :
      (∑ b ∈ Finset.Icc l u, f (b + t + 1)) =
        ∑ b ∈ Finset.Icc (l + t + 1) (u + t + 1), f b := by
    simpa [Nat.add_assoc] using h₁
  rw [h₀, h₁']
  have hab : l + t ≤ u + t := Nat.add_le_add_right hlu t
  have hleft : Finset.Icc (l + t) (u + t) =
      insert (l + t) (Finset.Ioc (l + t) (u + t)) := by
    rw [← Finset.insert_Icc_add_one_left_eq_Icc hab,
      Finset.Icc_add_one_left_eq_Ioc]
  have hright : Finset.Icc (l + t + 1) (u + t + 1) =
      insert (u + t + 1) (Finset.Ioc (l + t) (u + t)) := by
    rw [Finset.Icc_add_one_left_eq_Ioc]
    exact (Finset.insert_Ioc_right_eq_Ioc_add_one hab).symm
  rw [hleft, hright, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
  ring

private theorem phase_sum_Icc_shift_error (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ = 1) (l u h : ℕ) :
    ‖(∑ b ∈ Finset.Icc l u, f b) -
      ∑ b ∈ Finset.Icc l u, f (b + h)‖ ≤ 2 * h := by
  by_cases hlu : l ≤ u
  · induction h with
    | zero => simp
    | succ h ih =>
      have hstep :
          ‖(∑ b ∈ Finset.Icc l u, f (b + h)) -
            ∑ b ∈ Finset.Icc l u, f (b + h + 1)‖ ≤ 2 := by
        rw [phase_sum_Icc_shift_step hlu]
        calc
          ‖f (l + h) - f (u + h + 1)‖ ≤
              ‖f (l + h)‖ + ‖f (u + h + 1)‖ := norm_sub_le _ _
          _ = 2 := by rw [hf, hf]; norm_num
      calc
        ‖(∑ b ∈ Finset.Icc l u, f b) -
            ∑ b ∈ Finset.Icc l u, f (b + (h + 1))‖ =
            ‖((∑ b ∈ Finset.Icc l u, f b) -
                ∑ b ∈ Finset.Icc l u, f (b + h)) +
              ((∑ b ∈ Finset.Icc l u, f (b + h)) -
                ∑ b ∈ Finset.Icc l u, f (b + h + 1))‖ := by
          congr 1
          simp only [Nat.add_assoc]
          ring
        _ ≤ ‖(∑ b ∈ Finset.Icc l u, f b) -
              ∑ b ∈ Finset.Icc l u, f (b + h)‖ +
            ‖(∑ b ∈ Finset.Icc l u, f (b + h)) -
              ∑ b ∈ Finset.Icc l u, f (b + h + 1)‖ := norm_add_le _ _
        _ ≤ 2 * ((h + 1 : ℕ) : ℝ) := by
          have htmp := add_le_add ih hstep
          have hcast : ((h + 1 : ℕ) : ℝ) = (h : ℝ) + 1 := by norm_cast
          nlinarith [htmp, hcast]
  · have hempty : Finset.Icc l u = ∅ := Finset.Icc_eq_empty_of_lt (lt_of_not_ge hlu)
    simp [hempty]

private theorem phase_shift_average_boundary (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ = 1) (l u M : ℕ) (hM : 1 ≤ M) :
    ‖∑ b ∈ Finset.Icc l u, f b‖ ≤
      (1 / (M : ℝ)) *
        ‖∑ h ∈ Finset.Icc 1 M, ∑ b ∈ Finset.Icc l u, f (b + h)‖ +
        2 * M := by
  classical
  let J : Finset ℕ := Finset.Icc 1 M
  let S₀ : ℂ := ∑ b ∈ Finset.Icc l u, f b
  let G : ℂ := ∑ h ∈ J, ∑ b ∈ Finset.Icc l u, f (b + h)
  let E : ℂ := ∑ h ∈ J,
    (S₀ - ∑ b ∈ Finset.Icc l u, f (b + h))
  have hJcard : J.card = M := by
    dsimp [J]
    simp
  have hconst : (∑ h ∈ J, S₀) = (M : ℂ) * S₀ := by
    simp [hJcard]
  have hdecomp : (M : ℂ) * S₀ = G + E := by
    calc
      (M : ℂ) * S₀ = ∑ h ∈ J, S₀ := hconst.symm
      _ = ∑ h ∈ J,
          ((∑ b ∈ Finset.Icc l u, f (b + h)) +
            (S₀ - ∑ b ∈ Finset.Icc l u, f (b + h))) := by
        apply Finset.sum_congr rfl
        intro h hh
        dsimp [S₀]
        ring
      _ = G + E := by
        dsimp [G, E]
        rw [Finset.sum_add_distrib]
  have hE : ‖E‖ ≤ 2 * (M : ℝ) ^ 2 := by
    dsimp [E]
    calc
      _ ≤ ∑ h ∈ J,
          ‖S₀ - ∑ b ∈ Finset.Icc l u, f (b + h)‖ := norm_sum_le _ _
      _ ≤ ∑ _h ∈ J, 2 * (M : ℝ) := by
        apply Finset.sum_le_sum
        intro h hh
        have hhM : h ≤ M := (Finset.mem_Icc.mp hh).2
        have hshift := phase_sum_Icc_shift_error f hf l u h
        calc
          ‖S₀ - ∑ b ∈ Finset.Icc l u, f (b + h)‖ ≤ 2 * (h : ℝ) := by
            simpa [S₀] using hshift
          _ ≤ 2 * (M : ℝ) := by gcongr
      _ = (J.card : ℝ) * (2 * (M : ℝ)) := by simp
      _ = 2 * (M : ℝ) ^ 2 := by rw [hJcard]; ring
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hM)
  have hnormM : ‖(M : ℂ) * S₀‖ = (M : ℝ) * ‖S₀‖ := by
    rw [norm_mul]
    simp
  have hlarge : (M : ℝ) * ‖S₀‖ ≤ ‖G‖ + 2 * (M : ℝ) ^ 2 := by
    calc
      (M : ℝ) * ‖S₀‖ = ‖(M : ℂ) * S₀‖ := hnormM.symm
      _ = ‖G + E‖ := by rw [hdecomp]
      _ ≤ ‖G‖ + ‖E‖ := norm_add_le _ _
      _ ≤ ‖G‖ + 2 * (M : ℝ) ^ 2 := by nlinarith [hE]
  have hdiv := div_le_div_of_nonneg_right hlarge hMpos.le
  calc
    ‖S₀‖ = ((M : ℝ) * ‖S₀‖) / (M : ℝ) := by field_simp [ne_of_gt hMpos]
    _ ≤ (‖G‖ + 2 * (M : ℝ) ^ 2) / (M : ℝ) := hdiv
    _ = (1 / (M : ℝ)) *
          ‖∑ h ∈ Finset.Icc 1 M, ∑ b ∈ Finset.Icc l u, f (b + h)‖ +
          2 * M := by
        dsimp [G]
        field_simp [ne_of_gt hMpos]
        <;> ring

private theorem phase_log_taylor_remainder {z : ℝ} (hz : |z| < 1) (k : ℕ) :
    |Real.log (1 + z) -
      (∑ i ∈ Finset.range k, (-1 : ℝ) ^ i * z ^ (i + 1) / (i + 1))| ≤
      |z| ^ (k + 1) / (1 - |z|) := by
  have hneg : |-z| < 1 := by simpa using hz
  have hraw := Real.abs_log_sub_add_sum_range_le (x := -z) hneg k
  have hterm (i : ℕ) :
      (-z) ^ (i + 1) / (i + 1) =
        -((-1 : ℝ) ^ i * z ^ (i + 1) / (i + 1)) := by
    rw [neg_pow, pow_succ]
    push_cast
    ring
  have hsum :
      (∑ i ∈ Finset.range k, (-z) ^ (i + 1) / (i + 1)) =
        -(∑ i ∈ Finset.range k, (-1 : ℝ) ^ i * z ^ (i + 1) / (i + 1)) := by
    calc
      _ = ∑ i ∈ Finset.range k, -((-1 : ℝ) ^ i * z ^ (i + 1) / (i + 1)) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hterm i
      _ = _ := by rw [Finset.sum_neg_distrib]
  simpa [hsum, abs_neg, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hraw

private theorem phase_rpow_threequarters_le_half {H : ℝ} (hH : 16 ≤ H) :
    Real.rpow H (3 / 4) ≤ H / 2 := by
  have hHpos : 0 < H := by linarith
  have hpowEq : (Real.rpow H (3 / 4 : ℝ)) ^ 4 = H ^ 3 := by
    calc
      (Real.rpow H (3 / 4 : ℝ)) ^ 4 = Real.rpow H ((3 / 4 : ℝ) * 4) :=
        (Real.rpow_mul_natCast hHpos.le (3 / 4 : ℝ) 4).symm
      _ = H ^ 3 := by norm_num
  have hmul : 16 * H ^ 3 ≤ H ^ 4 := by
    calc
      16 * H ^ 3 ≤ H * H ^ 3 := mul_le_mul_of_nonneg_right hH (pow_nonneg hHpos.le 3)
      _ = H ^ 4 := by rw [pow_succ]; ring
  have hpowBound : H ^ 3 ≤ (H / 2) ^ 4 := by
    rw [div_pow]
    norm_num
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 16)]
    simpa [mul_comm] using hmul
  exact le_of_pow_le_pow_left₀ (by norm_num : 4 ≠ 0) (by positivity)
    (hpowEq ▸ hpowBound)

private theorem phase_log_taylor_error {H y θ v : ℝ} {b h k M : ℕ}
    (hH : 16 ≤ H) (hy : 4 / 5 ≤ y) (hv : |v| ≤ Real.rpow H y)
    (hk : 4 * y + 8 ≤ k) (hMupper : (M : ℝ) ≤ Real.rpow H (3 / 4))
    (hh : h ≤ M)
    (hinterval : H ≤ (b : ℝ) + θ ∧ (b : ℝ) + θ ≤ 2 * H) :
    |v * (Real.log ((b : ℝ) + θ + h) - Real.log ((b : ℝ) + θ)) -
      2 * Real.pi * (∑ j : Fin k,
        phaseCoefficient v θ b j.val * (h : ℝ) ^ (j.val + 1))| ≤
      2 * Real.rpow H (-9 / 4) := by
  let d : ℝ := (b : ℝ) + θ
  let z : ℝ := (h : ℝ) / d
  let P : ℝ :=
    ∑ j : Fin k, (-1 : ℝ) ^ j.val * z ^ (j.val + 1) / (j.val + 1 : ℝ)
  have hHpos : 0 < H := by linarith
  have hHone : 1 ≤ H := by linarith
  have hdpos : 0 < d := lt_of_lt_of_le (by linarith) hinterval.1
  have hA : Real.rpow H (3 / 4 : ℝ) ≤ H / 2 := phase_rpow_threequarters_le_half hH
  have hAdivHalf : Real.rpow H (3 / 4 : ℝ) / H ≤ 1 / 2 := by
    apply (div_le_iff₀ hHpos).2
    nlinarith [hA]
  have hMcast : (h : ℝ) ≤ (M : ℝ) := by exact_mod_cast hh
  have hzNonneg : 0 ≤ z := by dsimp [z]; positivity
  have hratioA : z ≤ Real.rpow H (3 / 4 : ℝ) / H := by
    dsimp [z, d]
    calc
      (h : ℝ) / ((b : ℝ) + θ) ≤ (M : ℝ) / ((b : ℝ) + θ) := by
        gcongr
      _ ≤ Real.rpow H (3 / 4 : ℝ) / ((b : ℝ) + θ) := by gcongr
      _ ≤ Real.rpow H (3 / 4 : ℝ) / H :=
        div_le_div_of_nonneg_left (Real.rpow_nonneg hHpos.le _) hHpos hinterval.1
  have hzHalf : z ≤ 1 / 2 := by
    exact hratioA.trans hAdivHalf
  have hzLt : |z| < 1 := by
    rw [abs_of_nonneg hzNonneg]
    linarith [hzHalf]
  have hAdiv : Real.rpow H (3 / 4 : ℝ) / H = Real.rpow H (-1 / 4 : ℝ) := by
    calc
      Real.rpow H (3 / 4 : ℝ) / H =
          Real.rpow H (3 / 4 : ℝ) / Real.rpow H 1 := by simp
      _ = Real.rpow H ((3 / 4 : ℝ) - 1) := (Real.rpow_sub hHpos _ _).symm
      _ = Real.rpow H (-1 / 4 : ℝ) := by congr 1 <;> norm_num
  have hratio : z ≤ Real.rpow H (-1 / 4 : ℝ) := hAdiv ▸ hratioA
  have hzPow : z ^ (k + 1) ≤ (Real.rpow H (-1 / 4 : ℝ)) ^ (k + 1) :=
    pow_le_pow_left₀ hzNonneg hratio (k + 1)
  have hexp : y + (-1 / 4 : ℝ) * ((k + 1 : ℕ) : ℝ) ≤ -9 / 4 := by
    push_cast
    nlinarith [hk]
  have hTaylorPower : Real.rpow H y * z ^ (k + 1) ≤ Real.rpow H (-9 / 4 : ℝ) := by
    have hmulExp : (Real.rpow H (-1 / 4 : ℝ)) ^ (k + 1) =
        Real.rpow H ((-1 / 4 : ℝ) * ((k + 1 : ℕ) : ℝ)) :=
      (Real.rpow_mul_natCast hHpos.le (-1 / 4 : ℝ) (k + 1)).symm
    calc
      Real.rpow H y * z ^ (k + 1) ≤
      Real.rpow H y * (Real.rpow H (-1 / 4 : ℝ)) ^ (k + 1) :=
        mul_le_mul_of_nonneg_left hzPow (Real.rpow_nonneg hHpos.le _)
      _ = Real.rpow H (y + (-1 / 4 : ℝ) * ((k + 1 : ℕ) : ℝ)) := by
        rw [hmulExp]
        exact (Real.rpow_add hHpos y _).symm
      _ ≤ Real.rpow H (-9 / 4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hHone hexp
  have hfac : d + (h : ℝ) = d * (1 + z) := by
    dsimp [z]
    field_simp [ne_of_gt hdpos]
  have h1pos : 0 < 1 + z := by linarith [hzNonneg]
  have hlogs : Real.log (d + (h : ℝ)) - Real.log d = Real.log (1 + z) := by
    rw [hfac, Real.log_mul (ne_of_gt hdpos) (ne_of_gt h1pos)]
    ring
  have hpoly : 2 * Real.pi *
      (∑ j : Fin k, phaseCoefficient v θ b j.val * (h : ℝ) ^ (j.val + 1)) = v * P := by
    have hcoeff (j : Fin k) :
        phaseCoefficient v θ b j.val =
          (-1 : ℝ) ^ j.val * v /
            (2 * Real.pi * ((j.val + 1 : ℕ) : ℝ) * d ^ (j.val + 1)) := by
      simp [phaseCoefficient, d]
    have hhEq : (h : ℝ) = d * z := by
      dsimp [z]
      field_simp [ne_of_gt hdpos]
    calc
      _ = ∑ j : Fin k,
          2 * Real.pi * (phaseCoefficient v θ b j.val * (h : ℝ) ^ (j.val + 1)) :=
        Finset.mul_sum _ _ _
      _ = ∑ j : Fin k,
          v * ((-1 : ℝ) ^ j.val * z ^ (j.val + 1) /
            ((j.val + 1 : ℕ) : ℝ)) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hcoeff j, hhEq]
        field_simp [Real.pi_ne_zero, ne_of_gt hdpos,
          ne_of_gt (show 0 < ((j.val + 1 : ℕ) : ℝ) by positivity),
          ne_of_gt (pow_pos hdpos (j.val + 1))]
        <;> ring
      _ = v * P := by
        dsimp [P]
        rw [← Finset.mul_sum]
        simp only [Nat.cast_add, Nat.cast_one]
  have hPRange : P =
      ∑ i ∈ Finset.range k, (-1 : ℝ) ^ i * z ^ (i + 1) / (i + 1 : ℝ) := by
    dsimp [P]
    simpa only [Nat.cast_add, Nat.cast_one] using
      (Fin.sum_univ_eq_sum_range
        (fun i : ℕ => (-1 : ℝ) ^ i * z ^ (i + 1) / (i + 1 : ℝ)) k)
  have hseries := phase_log_taylor_remainder hzLt k
  have hseriesFin : |Real.log (1 + z) - P| ≤ z ^ (k + 1) / (1 - z) := by
    rw [← hPRange] at hseries
    simpa [abs_of_nonneg hzNonneg] using hseries
  have hden : 0 < 1 - z := by linarith [hzHalf]
  have hrecip : 1 / (1 - z) ≤ 2 := by
    rw [div_le_iff₀ hden]
    nlinarith [hzHalf]
  have hangle :
      v * (Real.log ((b : ℝ) + θ + h) - Real.log ((b : ℝ) + θ)) -
        2 * Real.pi * (∑ j : Fin k,
          phaseCoefficient v θ b j.val * (h : ℝ) ^ (j.val + 1)) =
      v * (Real.log (1 + z) - P) := by
    rw [hlogs, hpoly]
    ring
  have hmain : |v| * |Real.log (1 + z) - P| ≤
      2 * Real.rpow H (-9 / 4) := by
    calc
      |v| * |Real.log (1 + z) - P| ≤
          Real.rpow H y * (z ^ (k + 1) / (1 - z)) :=
        mul_le_mul hv hseriesFin (abs_nonneg _) (Real.rpow_nonneg hHpos.le _)
      _ = Real.rpow H y * z ^ (k + 1) * (1 / (1 - z)) := by ring
      _ ≤ Real.rpow H y * z ^ (k + 1) * 2 :=
        mul_le_mul_of_nonneg_left hrecip
          (mul_nonneg (Real.rpow_nonneg hHpos.le _) (pow_nonneg hzNonneg _))
      _ = 2 * (Real.rpow H y * z ^ (k + 1)) := by ring
      _ ≤ 2 * Real.rpow H (-9 / 4) := by
        exact mul_le_mul_of_nonneg_left hTaylorPower (by norm_num)
  rw [hangle, abs_mul]
  exact hmain

/-- Shift averaging and the Taylor remainder on a dyadic natural interval. -/
theorem phase_shift_average {H y θ v : ℝ} {l u k M : ℕ}
    (hH : 16 ≤ H) (hy : 4 / 5 ≤ y)
    (hv : |v| ≤ Real.rpow H y) (hk : 4 * y + 8 ≤ k)
    (hM : 1 ≤ M) (hMupper : (M : ℝ) ≤ Real.rpow H (3 / 4))
    (hcard : ((Finset.Icc l u).card : ℝ) ≤ 2 * H)
    (hinterval : ∀ b ∈ Finset.Icc l u,
      H ≤ (b : ℝ) + θ ∧ (b : ℝ) + θ ≤ 2 * H) :
    ‖∑ b ∈ Finset.Icc l u,
        Complex.exp (Complex.I * v * Real.log ((b : ℝ) + θ))‖ ≤
      (1 / (M : ℝ)) *
        ∑ b ∈ Finset.Icc l u, ‖phasePolynomialSum v θ b k M‖ +
        4 * M + 8 / H := by
  classical
  let f : ℕ → ℂ := fun n =>
    Complex.exp (Complex.I * (v * Real.log ((n : ℝ) + θ)))
  let base (b : ℕ) : ℂ :=
    Complex.exp (Complex.I * (v * Real.log ((b : ℝ) + θ)))
  let J : Finset ℕ := Finset.Icc 1 M
  let G : ℂ := ∑ h ∈ J, ∑ b ∈ Finset.Icc l u, f (b + h)
  let T : ℂ := ∑ b ∈ Finset.Icc l u,
    base b * phasePolynomialSum v θ b k M
  let δ : ℝ := 2 * Real.rpow H (-9 / 4)
  have hHpos : 0 < H := by linarith
  have hHone : 1 ≤ H := by linarith
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hM)
  have hJcard : J.card = M := by
    dsimp [J]
    simp
  have hf (n : ℕ) : ‖f n‖ = 1 := by
    simp [f, Complex.norm_exp, Complex.mul_re]
  have hOrig :
      (∑ b ∈ Finset.Icc l u,
        Complex.exp (Complex.I * v * Real.log ((b : ℝ) + θ))) =
      ∑ b ∈ Finset.Icc l u, f b := by
    apply Finset.sum_congr rfl
    intro b hb
    dsimp [f]
    congr 1
    ring
  have hShift :
      ‖∑ b ∈ Finset.Icc l u,
          Complex.exp (Complex.I * v * Real.log ((b : ℝ) + θ))‖ ≤
        (1 / (M : ℝ)) * ‖G‖ + 2 * (M : ℝ) := by
    rw [hOrig]
    simpa [G, J] using phase_shift_average_boundary f hf l u M hM
  have hbaseNorm (b : ℕ) : ‖base b‖ = 1 := by
    simp [base, Complex.norm_exp, Complex.mul_re]
  have hApprox (b h : ℕ) (hb : b ∈ Finset.Icc l u) (hh : h ∈ J) :
      ‖f (b + h) - base b * additiveCharacter
        (∑ j : Fin k, phaseCoefficient v θ b j.val * (h : ℝ) ^ (j.val + 1))‖ ≤ δ := by
    have hTaylor := phase_log_taylor_error hH hy hv hk hMupper
      (Finset.mem_Icc.mp (by simpa [J] using hh)).2 (hinterval b hb)
    let d : ℝ := (b : ℝ) + θ
    let P : ℝ :=
      ∑ j : Fin k, phaseCoefficient v θ b j.val * (h : ℝ) ^ (j.val + 1)
    have hfirst : f (b + h) =
        Complex.exp (Complex.I * (v * Real.log (d + (h : ℝ)))) := by
      dsimp [f, d]
      congr 1
      congr 1
      push_cast
      ring
    have hfactor : base b * additiveCharacter P =
        Complex.exp (Complex.I * (v * Real.log d + 2 * Real.pi * P)) := by
      dsimp [base]
      unfold additiveCharacter
      rw [← Complex.exp_add]
      congr 1
      ring
    have hAngle := phase_exp_I_mul_lipschitz
      (v * Real.log (d + (h : ℝ))) (v * Real.log d + 2 * Real.pi * P)
    have hAngle' :
        ‖Complex.exp (Complex.I * ((v : ℂ) * (Real.log (d + (h : ℝ)) : ℂ))) -
          Complex.exp (Complex.I * ((v : ℂ) * (Real.log d : ℂ) +
            (2 * Real.pi * P : ℂ)))‖ ≤
          |v * Real.log (d + (h : ℝ)) - (v * Real.log d + 2 * Real.pi * P)| := by
      simpa [Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_natCast] using hAngle
    have hrem :
        |v * (Real.log (d + (h : ℝ)) - Real.log d) - 2 * Real.pi * P| ≤ δ := by
      simpa [P, d, δ] using hTaylor
    calc
      _ = ‖Complex.exp (Complex.I * (v * Real.log (d + (h : ℝ)))) -
            Complex.exp (Complex.I * (v * Real.log d + 2 * Real.pi * P))‖ := by
          rw [hfirst, hfactor]
      _ ≤ |v * Real.log (d + (h : ℝ)) -
            (v * Real.log d + 2 * Real.pi * P)| := hAngle'
      _ = |v * (Real.log (d + (h : ℝ)) - Real.log d) - 2 * Real.pi * P| := by
        congr 1
        ring
      _ ≤ δ := hrem
  have hTaylorB (b : ℕ) (hb : b ∈ Finset.Icc l u) :
      ‖(∑ h ∈ J, f (b + h)) -
          base b * phasePolynomialSum v θ b k M‖ ≤ (M : ℝ) * δ := by
    have hsum :
        (∑ h ∈ J, f (b + h)) -
            base b * phasePolynomialSum v θ b k M =
          ∑ h ∈ J, (f (b + h) - base b * additiveCharacter
            (∑ j : Fin k, phaseCoefficient v θ b j.val * (h : ℝ) ^ (j.val + 1))) := by
      dsimp [J, phasePolynomialSum]
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    rw [hsum]
    calc
      _ ≤ ∑ h ∈ J, ‖f (b + h) - base b * additiveCharacter
          (∑ j : Fin k, phaseCoefficient v θ b j.val * (h : ℝ) ^ (j.val + 1))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _h ∈ J, δ := Finset.sum_le_sum fun h hh => hApprox b h hb hh
      _ = (M : ℝ) * δ := by simp [J, hJcard]
  have hGswap : G = ∑ b ∈ Finset.Icc l u, ∑ h ∈ J, f (b + h) := by
    dsimp [G]
    rw [Finset.sum_comm]
  have hGminusT : G - T =
      ∑ b ∈ Finset.Icc l u,
        ((∑ h ∈ J, f (b + h)) - base b * phasePolynomialSum v θ b k M) := by
    dsimp [T]
    rw [hGswap, Finset.sum_sub_distrib]
  have hpowMul : H * Real.rpow H (-9 / 4) = Real.rpow H (-5 / 4) := by
    calc
      H * Real.rpow H (-9 / 4) = Real.rpow H 1 * Real.rpow H (-9 / 4) := by simp
      _ = Real.rpow H (1 + (-9 / 4 : ℝ)) := (Real.rpow_add hHpos 1 _).symm
      _ = Real.rpow H (-5 / 4) := by congr 1 <;> norm_num
  have hGdiff : ‖G - T‖ ≤ 4 * (M : ℝ) * Real.rpow H (-5 / 4) := by
    rw [hGminusT]
    calc
      _ ≤ ∑ b ∈ Finset.Icc l u,
          ‖(∑ h ∈ J, f (b + h)) - base b * phasePolynomialSum v θ b k M‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _b ∈ Finset.Icc l u, (M : ℝ) * δ :=
        Finset.sum_le_sum fun b hb => hTaylorB b hb
      _ = (Finset.Icc l u).card * ((M : ℝ) * δ) := by simp
      _ ≤ (2 * H) * ((M : ℝ) * δ) := by
        have hMnonneg : 0 ≤ (M : ℝ) := Nat.cast_nonneg _
        have hδnonneg : 0 ≤ δ := by dsimp [δ]; positivity
        exact mul_le_mul_of_nonneg_right hcard (mul_nonneg hMnonneg hδnonneg)
      _ = 4 * (M : ℝ) * Real.rpow H (-5 / 4) := by
        dsimp [δ]
        calc
          (2 * H) * ((M : ℝ) * (2 * Real.rpow H (-9 / 4))) =
              4 * (M : ℝ) * (H * Real.rpow H (-9 / 4)) := by ring
          _ = 4 * (M : ℝ) * Real.rpow H (-5 / 4) :=
            congrArg (fun q : ℝ => 4 * (M : ℝ) * q) hpowMul
  have hTnorm : ‖T‖ ≤
      ∑ b ∈ Finset.Icc l u, ‖phasePolynomialSum v θ b k M‖ := by
    dsimp [T]
    calc
      _ ≤ ∑ b ∈ Finset.Icc l u, ‖base b * phasePolynomialSum v θ b k M‖ :=
        norm_sum_le _ _
      _ = ∑ b ∈ Finset.Icc l u, ‖phasePolynomialSum v θ b k M‖ := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [norm_mul, hbaseNorm, one_mul]
  have hGnorm : ‖G‖ ≤
      (∑ b ∈ Finset.Icc l u, ‖phasePolynomialSum v θ b k M‖) +
        4 * (M : ℝ) * Real.rpow H (-5 / 4) := by
    calc
      ‖G‖ = ‖T + (G - T)‖ := by congr 1 <;> ring
      _ ≤ ‖T‖ + ‖G - T‖ := norm_add_le _ _
      _ ≤ _ := add_le_add hTnorm hGdiff
  have hboundary := phase_shift_average_boundary f hf l u M hM
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hM)
  have hErrorAbsorb : 4 * Real.rpow H (-5 / 4) ≤ 8 / H := by
    have hExpMono : Real.rpow H (-5 / 4 : ℝ) ≤ Real.rpow H (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hHone (by norm_num)
    have hInv : Real.rpow H (-1 : ℝ) = 1 / H := by
      calc
        Real.rpow H (-1 : ℝ) = H⁻¹ := Real.rpow_neg_one H
        _ = 1 / H := by simp
    rw [hInv] at hExpMono
    calc
      4 * Real.rpow H (-5 / 4 : ℝ) ≤ 4 * (1 / H) :=
        mul_le_mul_of_nonneg_left hExpMono (by norm_num)
      _ = 4 / H := by ring
      _ ≤ 8 / H := div_le_div_of_nonneg_right (by norm_num) hHpos.le
  calc
    _ ≤ (1 / (M : ℝ)) * ‖G‖ + 2 * (M : ℝ) := by
      rw [hOrig]
      simpa [G, J] using hboundary
    _ ≤ (1 / (M : ℝ)) *
          (∑ b ∈ Finset.Icc l u, ‖phasePolynomialSum v θ b k M‖) +
        (1 / (M : ℝ)) *
          (4 * (M : ℝ) * Real.rpow H (-5 / 4)) + 2 * (M : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hGnorm (by positivity : 0 ≤ 1 / (M : ℝ))
      nlinarith [hmul]
    _ ≤ (1 / (M : ℝ)) *
          (∑ b ∈ Finset.Icc l u, ‖phasePolynomialSum v θ b k M‖) +
        8 / H + 4 * (M : ℝ) := by
      have hcancel :
          (1 / (M : ℝ)) * (4 * (M : ℝ) * Real.rpow H (-5 / 4)) =
            4 * Real.rpow H (-5 / 4) := by
        field_simp [ne_of_gt hMpos]
      rw [hcancel]
      nlinarith [hErrorAbsorb, hMpos]
    _ = (1 / (M : ℝ)) *
          (∑ b ∈ Finset.Icc l u, ‖phasePolynomialSum v θ b k M‖) +
        4 * M + 8 / H := by ring

abbrev PhaseBoxIndex (k M : ℕ) := ∀ j : Fin k, Fin (M ^ (j.val + 1))

noncomputable def phaseAlphaVector (H y θ : ℝ) (b : ℕ) (k : ℕ) : Fin k → ℝ :=
  fun j => phaseCoefficient (Real.rpow H y) θ b j.val

def phaseInBox {k M : ℕ} (r : PhaseBoxIndex k M) (α : Fin k → ℝ) : Prop :=
  ∀ j : Fin k,
    ((r j).val : ℝ) / (M : ℝ) ^ (j.val + 1) ≤ Int.fract (α j) ∧
      Int.fract (α j) < ((r j).val + 1 : ℝ) / (M : ℝ) ^ (j.val + 1)

noncomputable def phaseBoxMembers {H y θ : ℝ} {k M : ℕ} (B : Finset ℕ)
    (r : PhaseBoxIndex k M) : Finset ℕ := by
  classical
  exact B.filter fun b => phaseInBox r (phaseAlphaVector H y θ b k)

private theorem phase_natInterval_card_le (T : Finset ℕ) (lo hi W : ℝ)
    (hW : 0 ≤ W) (hwidth : hi - lo ≤ W)
    (hT : ∀ n ∈ T, lo ≤ (n : ℝ) ∧ (n : ℝ) ≤ hi) :
    T.card ≤ ⌈W⌉₊ + 2 := by
  let I : Finset ℤ := Finset.Icc ⌈lo⌉ ⌊hi⌋
  have hmap : Set.MapsTo (fun n : ℕ => (n : ℤ)) (T : Set ℕ) (I : Set ℤ) := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨Int.ceil_le.mpr (by simpa using (hT n hn).1),
      Int.le_floor.mpr (by simpa using (hT n hn).2)⟩
  have hinj : (T : Set ℕ).InjOn (fun n : ℕ => (n : ℤ)) := by
    intro n hn m hm h
    exact Int.ofNat_inj.mp h
  have hcard : T.card ≤ I.card := Finset.card_le_card_of_injOn _ hmap hinj
  have hdiffR : ((⌊hi⌋ + 1 - ⌈lo⌉ : ℤ) : ℝ) ≤ ((⌈W⌉₊ + 2 : ℕ) : ℝ) := by
    have hfloor := Int.floor_le hi
    have hceil := Int.le_ceil lo
    have hceilW := Nat.le_ceil W
    push_cast
    linarith
  have hdiffZ : (⌊hi⌋ + 1 - ⌈lo⌉ : ℤ) ≤ ((⌈W⌉₊ + 2 : ℕ) : ℤ) := by
    exact_mod_cast hdiffR
  have hI : I.card ≤ ⌈W⌉₊ + 2 := by
    simpa only [I, Int.card_Icc] using Int.toNat_le.mpr hdiffZ
  exact hcard.trans hI

private theorem phase_fract_diff_of_small (x y : ℝ)
    (hx : |x| < 1 / 4) (hy : |y| < 1 / 4)
    (hfrac : |Int.fract x - Int.fract y| < 1 / 2) :
    |x - y| = |Int.fract x - Int.fract y| := by
  have hxy : |x - y| < 1 / 2 := by
    calc
      |x - y| ≤ |x| + |y| := by
        rw [sub_eq_add_neg]
        simpa only [abs_neg] using abs_add_le x (-y)
      _ < 1 / 2 := by nlinarith
  have hxid : (⌊x⌋ : ℝ) + Int.fract x = x := Int.floor_add_fract x
  have hyid : (⌊y⌋ : ℝ) + Int.fract y = y := Int.floor_add_fract y
  have hfloor : ((⌊x⌋ - ⌊y⌋ : ℤ) : ℝ) =
      x - y - (Int.fract x - Int.fract y) := by
    push_cast
    linarith
  have hsmall : |((⌊x⌋ - ⌊y⌋ : ℤ) : ℝ)| < 1 := by
    rw [hfloor]
    calc
      |x - y - (Int.fract x - Int.fract y)| ≤
          |x - y| + |Int.fract x - Int.fract y| := by
            rw [sub_eq_add_neg]
            simpa only [abs_neg] using
              abs_add_le (x - y) (-(Int.fract x - Int.fract y))
      _ < 1 := by nlinarith
  have hzero : ⌊x⌋ - ⌊y⌋ = 0 := by
    apply Int.abs_lt_one_iff.mp
    exact_mod_cast hsmall
  have hEq : x - y = Int.fract x - Int.fract y := by
    have hcast : ((⌊x⌋ - ⌊y⌋ : ℤ) : ℝ) = 0 := by simp [hzero]
    nlinarith [hfloor, hcast]
  rw [hEq]

private theorem phaseCoefficient_abs_le_inv_H {H y θ : ℝ} {b j : ℕ}
    (hH : 16 ≤ H) (hyj : y ≤ (j : ℝ))
    (hd : H ≤ (b : ℝ) + θ) :
    |phaseCoefficient (Real.rpow H y) θ b j| ≤ 1 / H := by
  have hHpos : 0 < H := by linarith
  have hdpos : 0 < (b : ℝ) + θ := lt_of_lt_of_le (by linarith) hd
  have hHone : 1 ≤ H := by linarith
  have hyPow : H ^ y ≤ H ^ j := by
    rw [← Real.rpow_natCast H j]
    exact Real.rpow_le_rpow_of_exponent_le hHone (by exact_mod_cast hyj)
  have hdPow : H ^ (j + 1) ≤ ((b : ℝ) + θ) ^ (j + 1) :=
    pow_le_pow_left₀ hHpos.le hd (j + 1)
  have hfactor : 1 ≤ 2 * Real.pi * ((j + 1 : ℕ) : ℝ) := by
    have hj : 1 ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le j))
    nlinarith [Real.pi_gt_three]
  have hden : H ^ j * H ≤
      2 * Real.pi * ((j + 1 : ℕ) : ℝ) * ((b : ℝ) + θ) ^ (j + 1) := by
    have hdpow : H ^ j * H ≤ ((b : ℝ) + θ) ^ (j + 1) := by
      simpa only [pow_succ] using hdPow
    calc
      H ^ j * H ≤ 1 * ((b : ℝ) + θ) ^ (j + 1) := by simpa using hdpow
      _ ≤ 2 * Real.pi * ((j + 1 : ℕ) : ℝ) * ((b : ℝ) + θ) ^ (j + 1) :=
        mul_le_mul_of_nonneg_right hfactor (pow_nonneg hdpos.le _)
  have hdenpos : 0 < 2 * Real.pi * ((j + 1 : ℕ) : ℝ) * ((b : ℝ) + θ) ^ (j + 1) := by
    positivity
  have habs : |phaseCoefficient (Real.rpow H y) θ b j| =
      Real.rpow H y /
        (2 * Real.pi * ((j + 1 : ℕ) : ℝ) * ((b : ℝ) + θ) ^ (j + 1)) := by
    rw [phaseCoefficient, abs_div, abs_of_pos hdenpos, abs_mul, abs_pow]
    simp [abs_of_nonneg (Real.rpow_nonneg hHpos.le _)]
  rw [habs, div_le_div_iff₀ hdenpos hHpos]
  exact (mul_le_mul_of_nonneg_right hyPow hHpos.le).trans (by simpa using hden)

private theorem phase_reciprocal_difference_lower {H d₁ d₂ : ℝ} {p : ℕ}
    (hH : 0 < H) (hd₁ : H ≤ d₁) (hd₂ : d₂ ≤ 2 * H)
    (hd₁₂ : d₁ ≤ d₂) (hp : 1 ≤ p) :
    1 / d₁ ^ p - 1 / d₂ ^ p ≥ (d₂ - d₁) / (2 * H) ^ (p + 1) := by
  have hd₂pos : 0 < d₂ := lt_of_lt_of_le hH (le_trans hd₁ hd₁₂)
  have h2Hpos : 0 < 2 * H := by positivity
  have hd₁le : d₁ ≤ 2 * H := hd₁₂.trans hd₂
  have hpowD : d₁ ^ p ≤ (2 * H) ^ p := pow_le_pow_left₀ (by linarith) hd₁le p
  have hrecip : 1 / (2 * H) ^ p ≤ 1 / d₁ ^ p :=
    one_div_le_one_div_of_le (pow_pos (lt_of_lt_of_le hH hd₁) p) hpowD
  have hratioPos : 0 < d₁ / d₂ := div_pos (lt_of_lt_of_le hH hd₁) hd₂pos
  have hratioLe : d₁ / d₂ ≤ 1 := (div_le_one₀ hd₂pos).2 hd₁₂
  have hpowRatio : (d₁ / d₂) ^ p ≤ d₁ / d₂ :=
    pow_le_of_le_one hratioPos.le hratioLe (by omega)
  have hratioDelta : (d₂ - d₁) / (2 * H) ≤ 1 - d₁ / d₂ := by
    have hrecipD : 1 / (2 * H) ≤ 1 / d₂ :=
      one_div_le_one_div_of_le hd₂pos hd₂
    calc
      (d₂ - d₁) / (2 * H) = (d₂ - d₁) * (1 / (2 * H)) := by ring
      _ ≤ (d₂ - d₁) * (1 / d₂) :=
        mul_le_mul_of_nonneg_left hrecipD (sub_nonneg.mpr hd₁₂)
      _ = 1 - d₁ / d₂ := by
        field_simp [ne_of_gt hd₂pos]
  have hratioPow : (d₂ - d₁) / (2 * H) ≤ 1 - (d₁ / d₂) ^ p := by
    linarith [hratioDelta, hpowRatio]
  have hidentity : 1 / d₁ ^ p - 1 / d₂ ^ p =
      (1 / d₁ ^ p) * (1 - (d₁ / d₂) ^ p) := by
    rw [div_pow]
    field_simp [ne_of_gt (pow_pos (lt_of_lt_of_le hH hd₁) p),
      ne_of_gt (pow_pos hd₂pos p)]
  have hdelta : 0 ≤ (d₂ - d₁) / (2 * H) :=
    div_nonneg (sub_nonneg.mpr hd₁₂) h2Hpos.le
  have hupper : 0 ≤ 1 / d₁ ^ p :=
    div_nonneg (by positivity) (pow_nonneg (le_of_lt (lt_of_lt_of_le hH hd₁)) _)
  calc
    1 / d₁ ^ p - 1 / d₂ ^ p =
        (1 / d₁ ^ p) * (1 - (d₁ / d₂) ^ p) := hidentity
    _ ≥ (1 / (2 * H) ^ p) * ((d₂ - d₁) / (2 * H)) :=
      mul_le_mul hrecip hratioPow hdelta hupper
    _ = (d₂ - d₁) / (2 * H) ^ (p + 1) := by
      rw [pow_succ]
      field_simp [ne_of_gt h2Hpos]

private theorem phase_box_pair_distance {H y θ : ℝ} {k M : ℕ}
    (B : Finset ℕ) (r : PhaseBoxIndex k M)
    (hH : 16 ≤ H) (hy : 4 / 5 ≤ y) (hklo : 4 * y + 8 ≤ k)
    (hM : 0 < M) (hMlo : Real.rpow H (3 / 4) / 2 ≤ (M : ℝ))
    (hB : ∀ n ∈ B, H ≤ (n : ℝ) + θ ∧ (n : ℝ) + θ ≤ 2 * H)
    (j : ℕ) (hj : j < k) (hyj : y ≤ (j : ℝ))
    {b c : ℕ} (hbc : b ≤ c)
    (hb : b ∈ phaseBoxMembers (H := H) (y := y) (θ := θ) B r)
    (hc : c ∈ phaseBoxMembers (H := H) (y := y) (θ := θ) B r) :
    (c : ℝ) - b ≤
      (2 * Real.pi * ((j + 1 : ℕ) : ℝ) *
        (2 * H) ^ (j + 2)) /
        (Real.rpow H y * (M : ℝ) ^ (j + 1)) := by
  classical
  let p : ℕ := j + 1
  let jFin : Fin k := ⟨j, hj⟩
  let d₁ : ℝ := (b : ℝ) + θ
  let d₂ : ℝ := (c : ℝ) + θ
  let coeff (n : ℕ) : ℝ := phaseCoefficient (Real.rpow H y) θ n j
  let A : ℝ := Real.rpow H y / (2 * Real.pi * (p : ℝ))
  let g (n : ℕ) : ℝ := A * (1 / (((n : ℝ) + θ) ^ p))
  have hp : 1 ≤ p := by dsimp [p]; omega
  have hpCast : (p : ℝ) = ((j + 1 : ℕ) : ℝ) := by rfl
  have hHpos : 0 < H := by linarith
  have hHone : 1 ≤ H := by linarith
  have hyNonneg : 0 ≤ y := by linarith
  have hfloor : ((Nat.floor y : ℕ) : ℝ) ≤ y := Nat.floor_le hyNonneg
  have hyj' : y ≤ (j : ℝ) := hyj
  have hMreal : 0 < (M : ℝ) := by exact_mod_cast hM
  have hMtwo : 2 ≤ (M : ℝ) := by
    have hsqrt : 4 ≤ Real.sqrt H :=
      (Real.le_sqrt (by norm_num) (by linarith [hH])).2 (by nlinarith [hH])
    have hhalf : 4 ≤ Real.rpow H (1 / 2 : ℝ) := by
      simpa [Real.sqrt_eq_rpow] using hsqrt
    have hthreequarters : Real.rpow H (1 / 2 : ℝ) ≤ Real.rpow H (3 / 4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hHone (by norm_num)
    nlinarith [hMlo, hhalf.trans hthreequarters]
  have hMone : 1 ≤ (M : ℝ) := by linarith
  have hMp : 2 ≤ (M : ℝ) ^ p := by
    have hpow : (M : ℝ) ≤ (M : ℝ) ^ p :=
      le_self_pow₀ hMone (by omega : p ≠ 0)
    exact hMtwo.trans hpow
  have hcellwidth : 1 / (M : ℝ) ^ p ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) hMp
  have hmemB : b ∈ B := (Finset.mem_filter.mp hb).1
  have hmemC : c ∈ B := (Finset.mem_filter.mp hc).1
  have hB₁ := hB b hmemB
  have hB₂ := hB c hmemC
  have hd₁ : H ≤ d₁ := by exact hB₁.1
  have hd₁hi : d₁ ≤ 2 * H := hB₁.2
  have hd₂ : H ≤ d₂ := hB₂.1
  have hd₂hi : d₂ ≤ 2 * H := hB₂.2
  have hd₁₂ : d₁ ≤ d₂ := by
    dsimp [d₁, d₂]
    exact add_le_add (by exact_mod_cast hbc : (b : ℝ) ≤ c) le_rfl
  have hcoeffAbs (n : ℕ) (hn : n ∈ B) :
      |coeff n| ≤ 1 / H := by
    have hnB := hB n hn
    exact phaseCoefficient_abs_le_inv_H hH hyj hnB.1
  have hsmall₁ : |coeff b| < 1 / 4 := by
    have h16 : 1 / H ≤ 1 / 16 := one_div_le_one_div_of_le (by norm_num) hH
    have h := hcoeffAbs b hmemB
    nlinarith
  have hsmall₂ : |coeff c| < 1 / 4 := by
    have h16 : 1 / H ≤ 1 / 16 := one_div_le_one_div_of_le (by norm_num) hH
    have h := hcoeffAbs c hmemC
    nlinarith
  have hbox₁ : phaseInBox r (phaseAlphaVector H y θ b k) :=
    (Finset.mem_filter.mp hb).2
  have hbox₂ : phaseInBox r (phaseAlphaVector H y θ c k) :=
    (Finset.mem_filter.mp hc).2
  have hcoord₁ := hbox₁ jFin
  have hcoord₂ := hbox₂ jFin
  have hcoord₁' :
      ((r jFin).val : ℝ) / (M : ℝ) ^ p ≤ Int.fract (coeff b) ∧
        Int.fract (coeff b) < (((r jFin).val + 1 : ℕ) : ℝ) / (M : ℝ) ^ p := by
    simpa [p, coeff, phaseAlphaVector, jFin] using hcoord₁
  have hcoord₂' :
      ((r jFin).val : ℝ) / (M : ℝ) ^ p ≤ Int.fract (coeff c) ∧
        Int.fract (coeff c) < (((r jFin).val + 1 : ℕ) : ℝ) / (M : ℝ) ^ p := by
    simpa [p, coeff, phaseAlphaVector, jFin] using hcoord₂
  have hcell :
      ((r jFin).val : ℝ) / (M : ℝ) ^ p + 1 / (M : ℝ) ^ p =
        (((r jFin).val + 1 : ℕ) : ℝ) / (M : ℝ) ^ p := by
    have hden : (M : ℝ) ^ p ≠ 0 := ne_of_gt (pow_pos hMreal p)
    field_simp [hden]
    norm_num [Nat.cast_add]
  have hfrac : |Int.fract (coeff b) - Int.fract (coeff c)| < 1 / (M : ℝ) ^ p := by
    rw [abs_lt]
    constructor <;> linarith [hcoord₁'.1, hcoord₁'.2, hcoord₂'.1, hcoord₂'.2, hcell]
  have hcoeffDiff : |coeff b - coeff c| < 1 / (M : ℝ) ^ p := by
    rw [phase_fract_diff_of_small (coeff b) (coeff c) hsmall₁ hsmall₂]
    · exact hfrac
    · exact lt_of_lt_of_le hfrac hcellwidth
  have hrepr (n : ℕ) (hn : n ∈ B) : coeff n = (-1 : ℝ) ^ j * g n := by
    have hdn : 0 < (n : ℝ) + θ := lt_of_lt_of_le (by linarith) (hB n hn).1
    have hpc : 0 < (p : ℝ) := by exact_mod_cast hp
    dsimp [coeff, g, A, p]
    simp only [phaseCoefficient]
    rw [pow_succ]
    field_simp [ne_of_gt hdn, Real.pi_ne_zero, ne_of_gt hpc]
    <;> ring
  have hApos : 0 < A := by
    dsimp [A]
    positivity
  have hd₁pos : 0 < d₁ := lt_of_lt_of_le (by linarith) hd₁
  have hd₂pos : 0 < d₂ := lt_of_lt_of_le (by linarith) hd₂
  have hpow : d₁ ^ p ≤ d₂ ^ p :=
    pow_le_pow_left₀ hd₁pos.le hd₁₂ p
  have hrecip : 1 / d₂ ^ p ≤ 1 / d₁ ^ p :=
    one_div_le_one_div_of_le (pow_pos hd₁pos p) hpow
  have hgmono : g c ≤ g b := by
    dsimp [g, d₁, d₂] at *
    exact mul_le_mul_of_nonneg_left hrecip hApos.le
  have hsignAbs : |(-1 : ℝ) ^ j| = 1 := by simp
  have hcoeffDiffEq : |coeff b - coeff c| = g b - g c := by
    rw [hrepr b hmemB, hrepr c hmemC, ← mul_sub, abs_mul, hsignAbs,
      abs_of_nonneg (sub_nonneg.mpr hgmono), one_mul]
  have hrecipLower := phase_reciprocal_difference_lower hHpos hd₁ hd₂hi hd₁₂ hp
  have hglower : g b - g c ≥
      ((c : ℝ) - b) *
        (Real.rpow H y /
          (2 * Real.pi * (p : ℝ) * (2 * H) ^ (p + 1))) := by
    dsimp [g, A, d₁, d₂]
    calc
      (Real.rpow H y / (2 * Real.pi * (p : ℝ))) *
            (1 / ((b : ℝ) + θ) ^ p) -
          (Real.rpow H y / (2 * Real.pi * (p : ℝ))) *
            (1 / ((c : ℝ) + θ) ^ p) =
          (Real.rpow H y / (2 * Real.pi * (p : ℝ))) *
            (1 / ((b : ℝ) + θ) ^ p - 1 / ((c : ℝ) + θ) ^ p) := by ring
      _ ≥ (Real.rpow H y / (2 * Real.pi * (p : ℝ))) *
            ((d₂ - d₁) / (2 * H) ^ (p + 1)) :=
          mul_le_mul_of_nonneg_left hrecipLower (div_nonneg (Real.rpow_nonneg hHpos.le _) (by positivity))
      _ = ((c : ℝ) - b) *
            (Real.rpow H y /
              (2 * Real.pi * (p : ℝ) * (2 * H) ^ (p + 1))) := by
          dsimp [d₁, d₂]
          field_simp [ne_of_gt hHpos, Real.pi_ne_zero,
            ne_of_gt (show 0 < (p : ℝ) by exact_mod_cast hp),
            ne_of_gt (pow_pos (lt_of_lt_of_le hHpos hd₁) p),
            ne_of_gt (pow_pos (by positivity : 0 < 2 * H) (p + 1))]
          <;> ring
  have hpCastPos : 0 < (p : ℝ) := by exact_mod_cast hp
  have h2Hpos : 0 < 2 * H := by positivity
  have hfactor : 0 <
      Real.rpow H y /
        (2 * Real.pi * (p : ℝ) * (2 * H) ^ (p + 1)) := by
    apply div_pos (Real.rpow_pos_of_pos hHpos y)
    positivity
  have hgapMul :
      ((c : ℝ) - b) *
          (Real.rpow H y /
            (2 * Real.pi * (p : ℝ) * (2 * H) ^ (p + 1))) < 1 / (M : ℝ) ^ p := by
    exact lt_of_le_of_lt hglower (by rw [← hcoeffDiffEq]; exact hcoeffDiff)
  have hgap : (c : ℝ) - b <
      (2 * Real.pi * (p : ℝ) * (2 * H) ^ (p + 1)) /
        (Real.rpow H y * (M : ℝ) ^ p) := by
    have hlt := (lt_div_iff₀ hfactor).2 hgapMul
    have heq :
        (1 / (M : ℝ) ^ p) /
            (Real.rpow H y /
              (2 * Real.pi * (p : ℝ) * (2 * H) ^ (p + 1))) =
          (2 * Real.pi * (p : ℝ) * (2 * H) ^ (p + 1)) /
            (Real.rpow H y * (M : ℝ) ^ p) := by
      field_simp [ne_of_gt hMreal, ne_of_gt hHpos,
        ne_of_gt (pow_pos hMreal p), ne_of_gt (Real.rpow_pos_of_pos hHpos y)]
      <;> ring
    rw [heq] at hlt
    exact hlt
  exact hgap.le

private theorem phase_box_radius_le {H y : ℝ} {k M p : ℕ}
    (hH : 16 ≤ H) (hM : 0 < M)
    (hMlo : Real.rpow H (3 / 4) / 2 ≤ (M : ℝ))
    (hp : 1 ≤ p) (hpk : p ≤ k)
    (hpexp : (p : ℝ) / 4 + 1 / 4 ≤ y) :
    (2 * Real.pi * (p : ℝ) * (2 * H) ^ (p + 1)) /
        (Real.rpow H y * (M : ℝ) ^ p) ≤
      Real.exp (8 * (k : ℝ)) * Real.rpow H (3 / 4) := by
  have hHpos : 0 < H := by linarith
  have hHone : 1 ≤ H := by linarith
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast hM
  let A : ℝ := Real.rpow H (3 / 4)
  let R : ℝ :=
    (2 * Real.pi * (p : ℝ) * (2 * H) ^ (p + 1)) /
      (Real.rpow H y * (M : ℝ) ^ p)
  let R₀ : ℝ :=
    (2 * Real.pi * (p : ℝ) * (2 * H) ^ (p + 1)) /
      (Real.rpow H y * (A / 2) ^ p)
  let C : ℝ := 2 * Real.pi * (p : ℝ) * (2 : ℝ) ^ (2 * p + 1)
  have hAnonneg : 0 ≤ A := Real.rpow_nonneg hHpos.le _
  have hApos : 0 < A := Real.rpow_pos_of_pos hHpos _
  have hMpow : (A / 2) ^ p ≤ (M : ℝ) ^ p := by
    have hbase : A / 2 ≤ (M : ℝ) := hMlo
    exact pow_le_pow_left₀ (div_nonneg hAnonneg (by norm_num)) hbase p
  have hden :
      Real.rpow H y * (A / 2) ^ p ≤ Real.rpow H y * (M : ℝ) ^ p :=
    mul_le_mul_of_nonneg_left hMpow (Real.rpow_nonneg hHpos.le _)
  have hRle : R ≤ R₀ := by
    dsimp [R, R₀]
    have hnum : 0 ≤ 2 * Real.pi * (p : ℝ) * (2 * H) ^ (p + 1) := by positivity
    have hsmall : 0 < Real.rpow H y * (A / 2) ^ p :=
      mul_pos (Real.rpow_pos_of_pos hHpos y) (pow_pos (div_pos hApos (by norm_num)) p)
    exact div_le_div_of_nonneg_left hnum hsmall hden
  have hExp : ((p + 1 : ℕ) : ℝ) ≤
      y + (3 / 4 : ℝ) * (p : ℝ) + 3 / 4 := by
    push_cast
    nlinarith [hpexp]
  have hRpowRight : Real.rpow H (y + (3 / 4 : ℝ) * (p : ℝ) + 3 / 4) =
      Real.rpow H y * A ^ p * A := by
    dsimp [A]
    rw [Real.rpow_add hHpos, Real.rpow_add hHpos,
      ← Real.rpow_mul_natCast hHpos.le]
  have hcore : H ^ (p + 1) ≤ Real.rpow H y * A ^ p * A := by
    calc
      H ^ (p + 1) = Real.rpow H ((p + 1 : ℕ) : ℝ) :=
        (Real.rpow_natCast H (p + 1)).symm
      _ ≤ Real.rpow H (y + (3 / 4 : ℝ) * (p : ℝ) + 3 / 4) :=
        Real.rpow_le_rpow_of_exponent_le hHone hExp
      _ = Real.rpow H y * A ^ p * A := hRpowRight
  have hcoreDen : 0 < Real.rpow H y * A ^ p :=
    mul_pos (Real.rpow_pos_of_pos hHpos y) (pow_pos hApos p)
  have hcoreRatio : H ^ (p + 1) /
      (Real.rpow H y * A ^ p) ≤ A := by
    apply (div_le_iff₀ hcoreDen).2
    calc
      H ^ (p + 1) ≤ Real.rpow H y * A ^ p * A := hcore
      _ = A * (Real.rpow H y * A ^ p) := by ring
  have hR₀eq : R₀ = C * (H ^ (p + 1) / (Real.rpow H y * A ^ p)) := by
    dsimp [R₀, C, A]
    rw [mul_pow, div_pow]
    have htwo : (2 : ℝ) ^ (p + 1) * 2 ^ p = 2 ^ (2 * p + 1) := by
      rw [← pow_add]
      congr 1
      omega
    field_simp [ne_of_gt hHpos, ne_of_gt hMpos,
      ne_of_gt (Real.rpow_pos_of_pos hHpos y),
      ne_of_gt (Real.rpow_pos_of_pos hHpos (3 / 4 : ℝ))]
    rw [htwo]
    <;> ring
  have hCnonneg : 0 ≤ C := by positivity
  have hR₀bound : R₀ ≤ C * A := by
    rw [hR₀eq]
    exact mul_le_mul_of_nonneg_left hcoreRatio hCnonneg
  have hexp1 : 2 ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    norm_num at this ⊢
    exact this
  have hexp3 : 8 ≤ Real.exp 3 := by
    have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hexp1 3
    norm_num at hpow
    have hEq : (Real.exp 1) ^ 3 = Real.exp 3 := by
      norm_num [← Real.exp_add]
    simpa [hEq] using hpow
  have hpi : 2 * Real.pi ≤ Real.exp 3 := by
    have h := Real.pi_lt_four
    linarith [hexp3]
  have hpExp : (p : ℝ) ≤ Real.exp (p : ℝ) := by
    have h := Real.add_one_le_exp (p : ℝ)
    linarith
  have htwoExp : (2 : ℝ) ^ (2 * p + 1) ≤ Real.exp ((2 * p + 1 : ℕ) : ℝ) := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hexp1 (2 * p + 1)
    simpa only [Real.exp_one_pow] using h
  have hCexp : C ≤ Real.exp (8 * (k : ℝ)) := by
    dsimp [C]
    have hpR : (p : ℝ) ≤ k := by exact_mod_cast hpk
    have hponeR : 1 ≤ (p : ℝ) := by exact_mod_cast hp
    calc
      2 * Real.pi * (p : ℝ) * (2 : ℝ) ^ (2 * p + 1) ≤
          Real.exp 3 * Real.exp (p : ℝ) *
            Real.exp ((2 * p + 1 : ℕ) : ℝ) := by
        gcongr
      _ = Real.exp (3 + (p : ℝ) + ((2 * p + 1 : ℕ) : ℝ)) := by
        rw [← Real.exp_add, ← Real.exp_add]
      _ ≤ Real.exp (8 * (k : ℝ)) := by
        apply Real.exp_le_exp.mpr
        push_cast
        nlinarith [hpR, hponeR]
  calc
    R = R := rfl
    _ ≤ R₀ := hRle
    _ ≤ C * A := hR₀bound
    _ ≤ Real.exp (8 * (k : ℝ)) * Real.rpow H (3 / 4 : ℝ) := by
      dsimp [A]
      exact mul_le_mul_of_nonneg_right hCexp (Real.rpow_nonneg hHpos.le _)

/-- Every coefficient box contains few quotient indices. -/
theorem phase_box_occupancy {H y θ : ℝ} {k M : ℕ} (B : Finset ℕ)
    (hH : 16 ≤ H) (hy : 4 / 5 ≤ y)
    (hklo : 4 * y + 8 ≤ k) (hkhi : (k : ℝ) ≤ 4 * y + 9)
    (hM : 0 < M)
    (hMlo : Real.rpow H (3 / 4) / 2 ≤ (M : ℝ))
    (hMhi : (M : ℝ) ≤ Real.rpow H (3 / 4))
    (hB : ∀ b ∈ B, H ≤ (b : ℝ) + θ ∧ (b : ℝ) + θ ≤ 2 * H)
    (r : PhaseBoxIndex k M) :
    ((phaseBoxMembers (H := H) (y := y) (θ := θ) B r).card : ℝ) ≤
      Real.exp (10 * k) * Real.rpow H (4 / 5) := by
  classical
  let S : Finset ℕ := phaseBoxMembers (H := H) (y := y) (θ := θ) B r
  change (S.card : ℝ) ≤ Real.exp (10 * (k : ℝ)) * Real.rpow H (4 / 5 : ℝ)
  by_cases hS : S = ∅
  · simp [hS]
    positivity
  · have hSn : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
    obtain ⟨b₀, hb₀⟩ := hSn
    have hyNonneg : 0 ≤ y := by linarith
    have hfloor : ((Nat.floor y : ℕ) : ℝ) ≤ y := Nat.floor_le hyNonneg
    let j : ℕ := Nat.floor y + 1
    let p : ℕ := j + 1
    have hjR : (j : ℝ) ≤ y + 1 := by
      dsimp [j]
      push_cast
      linarith
    have hyj : y ≤ (j : ℝ) := by
      have hlt : y < (j : ℝ) := by
        dsimp [j]
        exact_mod_cast (Nat.lt_floor_add_one y)
      exact hlt.le
    have hkR : y + 1 < (k : ℝ) := by nlinarith [hklo, hy]
    have hjltR : (j : ℝ) < k := lt_of_le_of_lt hjR hkR
    have hj : j < k := by exact_mod_cast hjltR
    have hpR : (p : ℝ) ≤ y + 2 := by
      dsimp [p, j]
      push_cast
      linarith
    have hpkR : (p : ℝ) ≤ k := by nlinarith [hklo, hy, hpR]
    have hpk : p ≤ k := by exact_mod_cast hpkR
    have hp : 1 ≤ p := by dsimp [p]; omega
    have hpexp : (p : ℝ) / 4 + 1 / 4 ≤ y := by
      by_cases hylt : y < 1
      · have hfloor0 : Nat.floor y = 0 := Nat.floor_eq_zero.mpr hylt
        simp [j, p, hfloor0]
        nlinarith [hy]
      · have hyge : 1 ≤ y := le_of_not_gt hylt
        nlinarith [hpR, hyge]
    have hRadius := phase_box_radius_le hH hM hMlo hp hpk hpexp
    let R : ℝ :=
      (2 * Real.pi * (p : ℝ) * (2 * H) ^ (p + 1)) /
        (Real.rpow H y * (M : ℝ) ^ p)
    have hRbound : R ≤ Real.exp (8 * (k : ℝ)) * Real.rpow H (3 / 4 : ℝ) := by
      simpa [R] using hRadius
    have hRpos : 0 < R := by
      dsimp [R]
      positivity
    have hdist : ∀ b ∈ S, |(b : ℝ) - (b₀ : ℝ)| ≤ R := by
      intro b hb
      rcases le_total b b₀ with hbb₀ | hb₀b
      · have hpdist := phase_box_pair_distance B r hH hy hklo hM hMlo hB
          j hj hyj hbb₀ hb hb₀
        have hpdist' : (b₀ : ℝ) - b ≤ R := by
          simpa [R, p] using hpdist
        have hcast : (b : ℝ) ≤ (b₀ : ℝ) := by exact_mod_cast hbb₀
        simpa [abs_of_nonpos (sub_nonpos.mpr hcast)] using hpdist'
      · have hpdist := phase_box_pair_distance B r hH hy hklo hM hMlo hB
          j hj hyj hb₀b hb₀ hb
        have hpdist' : (b : ℝ) - b₀ ≤ R := by
          simpa [R, p] using hpdist
        have hcast : (b₀ : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb₀b
        have habs : |(b : ℝ) - (b₀ : ℝ)| = (b : ℝ) - b₀ :=
          abs_of_nonneg (sub_nonneg.mpr hcast)
        rw [habs]
        exact hpdist'
    have hcardNat : S.card ≤ ⌈2 * R⌉₊ + 2 := by
      apply phase_natInterval_card_le S ((b₀ : ℝ) - R) ((b₀ : ℝ) + R) (2 * R)
      · linarith [hRpos]
      · linarith
      · intro b hb
        have hd := hdist b hb
        have hd' := abs_le.mp hd
        constructor <;> linarith [hd'.1, hd'.2]
    have hcardR : (S.card : ℝ) ≤ (⌈2 * R⌉₊ : ℝ) + 2 := by exact_mod_cast hcardNat
    have hceil : (⌈2 * R⌉₊ : ℝ) < 2 * R + 1 := Nat.ceil_lt_add_one (by positivity)
    have hcardBound : (S.card : ℝ) ≤ 2 * R + 3 := by linarith [hcardR, hceil]
    let X : ℝ := Real.exp (8 * (k : ℝ))
    let Y : ℝ := Real.exp (2 * (k : ℝ))
    let Z : ℝ := Real.rpow H (4 / 5 : ℝ)
    have hkone : 1 ≤ (k : ℝ) := by
      exact le_trans (by exact_mod_cast hp) hpkR
    have hX : 3 ≤ X := by
      dsimp [X]
      have h := Real.add_one_le_exp (8 * (k : ℝ))
      nlinarith [hkone]
    have hY : 3 ≤ Y := by
      dsimp [Y]
      have h := Real.add_one_le_exp (2 * (k : ℝ))
      nlinarith [hkone]
    have hZ : 1 ≤ Z := by
      dsimp [Z]
      have h := Real.rpow_le_rpow_of_exponent_le (x := H) (by linarith [hH])
        (by norm_num : (0 : ℝ) ≤ (4 / 5 : ℝ))
      simpa using h
    have hPow : Real.rpow H (3 / 4 : ℝ) ≤ Z := by
      dsimp [Z]
      exact Real.rpow_le_rpow_of_exponent_le (x := H) (by linarith [hH]) (by norm_num)
    have hXB : 3 ≤ X * Z := by
      calc
        3 ≤ 3 * Z := by nlinarith [hZ]
        _ ≤ X * Z := mul_le_mul_of_nonneg_right hX (by positivity)
    have hYsub : 1 ≤ Y - 2 := by linarith [hY]
    have hprod : 3 ≤ X * Z * (Y - 2) := by
      calc
        3 ≤ X * Z := hXB
        _ ≤ X * Z * (Y - 2) :=
          by
            have hmul := mul_le_mul_of_nonneg_left hYsub
              (mul_nonneg (by positivity : 0 ≤ X) (by positivity : 0 ≤ Z))
            simpa only [mul_one] using hmul
    have hdom : 2 * X * Z + 3 ≤ X * Y * Z := by
      have heq : X * Y * Z = 2 * X * Z + X * Z * (Y - 2) := by ring
      rw [heq]
      linarith [hprod]
    have hRZ : R ≤ X * Z := by
      calc
        R ≤ Real.exp (8 * (k : ℝ)) * Real.rpow H (3 / 4 : ℝ) := hRbound
        _ ≤ X * Z := by
          dsimp [X, Z]
          exact mul_le_mul_of_nonneg_left hPow (Real.exp_nonneg _)
    calc
      (S.card : ℝ) ≤ 2 * R + 3 := hcardBound
      _ ≤ 2 * X * Z + 3 := by nlinarith [hRZ]
      _ ≤ X * Y * Z := hdom
      _ = Real.exp (10 * (k : ℝ)) * Real.rpow H (4 / 5 : ℝ) := by
        dsimp [X, Y, Z]
        rw [← Real.exp_add]
        congr 2
        ring

noncomputable def phaseWeylSum (k M : ℕ) (a : Fin k → ℝ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 M,
    additiveCharacter (∑ j : Fin k, a j * (h : ℝ) ^ (j.val + 1))

/-- Exact weighted torus moment for the Vinogradov mean-value count. -/
theorem phase_torus_moment {s k M : ℕ} {D : ℝ} (hD : 0 ≤ D)
    (c : ℕ → ℂ) (hc : ∀ h ∈ Finset.Icc 1 M, ‖c h‖ ≤ D) :
      ∫ a : Fin k → ℝ,
        Set.indicator {a | ∀ j, 0 ≤ a j ∧ a j ≤ 1}
          (fun a => ‖∑ h ∈ Finset.Icc 1 M,
            c h * additiveCharacter
              (∑ j : Fin k, a j * (h : ℝ) ^ (j.val + 1))‖ ^ (2 * s)) a ≤
        D ^ (2 * s) * (vinogradovCount s k M : ℝ) := by
  classical
  let cube : Set (Fin k → ℝ) := Set.univ.pi (fun _ => Set.Icc (0 : ℝ) 1)
  have hcubeEq : {a : Fin k → ℝ | ∀ j, 0 ≤ a j ∧ a j ≤ 1} = cube := by
    ext a
    simp [cube, Set.mem_pi, Pi.le_def, forall_and]
  have hcubeMeas :
      MeasurableSet {a : Fin k → ℝ | ∀ j, 0 ≤ a j ∧ a j ≤ 1} := by
    rw [hcubeEq]
    exact MeasurableSet.univ_pi fun _ => measurableSet_Icc
  let G := phaseMomentSolutions s k M
  let coeff (uv : (Fin s → ℕ) × (Fin s → ℕ)) :=
    phaseTupleWeight c uv.1 * conj (phaseTupleWeight c uv.2)
  let realMoment : ℝ :=
    ∫ a in cube,
      ‖phaseWeightedWeylSum (M := M) c a‖ ^ (2 * s)
        ∂(volume : Measure (Fin k → ℝ))
  have hMoment := phaseWeightedWeylSum_moment_integral (s := s) (k := k)
    (M := M) c
  have hCast :
      ∫ a in cube,
          (‖phaseWeightedWeylSum (M := M) c a‖ ^ (2 * s) : ℂ)
            ∂(volume : Measure (Fin k → ℝ)) =
        (realMoment : ℂ) := by
    dsimp [realMoment]
    simpa only [Complex.ofReal_pow] using
      (integral_complex_ofReal
        (μ := (volume : Measure (Fin k → ℝ)).restrict cube)
        (f := fun a : Fin k → ℝ =>
          ‖phaseWeightedWeylSum (M := M) c a‖ ^ (2 * s)))
  have hreal :
      realMoment = (∑ uv ∈ G, coeff uv).re := by
    calc
      _ = (realMoment : ℂ).re := by simp
      _ = (∫ a in cube,
          (‖phaseWeightedWeylSum (M := M) c a‖ ^ (2 * s) : ℂ)
            ∂(volume : Measure (Fin k → ℝ))).re := by rw [← hCast]
      _ = (∑ uv ∈ G, coeff uv).re := by
        exact congrArg Complex.re (by simpa [cube, G, coeff] using hMoment)
  have hcoef (uv : (Fin s → ℕ) × (Fin s → ℕ)) (huv : uv ∈ G) :
      ‖coeff uv‖ ≤ D ^ (2 * s) := by
    have huv' := (Finset.mem_filter.mp huv).1
    rcases Finset.mem_product.mp huv' with ⟨hu, hv⟩
    have hwu := phaseTupleWeight_norm_le hD c hc uv.1 hu
    have hwv := phaseTupleWeight_norm_le hD c hc uv.2 hv
    calc
      ‖coeff uv‖ = ‖phaseTupleWeight c uv.1‖ *
          ‖phaseTupleWeight c uv.2‖ := by simp [coeff, norm_mul]
      _ ≤ D ^ s * D ^ s :=
        mul_le_mul hwu hwv (norm_nonneg _) (pow_nonneg hD _)
      _ = D ^ (2 * s) := by
        calc
          _ = D ^ (s + s) := (pow_add D s s).symm
          _ = D ^ (2 * s) := by congr 1 <;> omega
  have hcard := phaseMomentSolutions_card_le_vinogradovCount s k M
  have hsumNorm :
      ‖∑ uv ∈ G, coeff uv‖ ≤ ∑ uv ∈ G, ‖coeff uv‖ :=
    norm_sum_le _ _
  have hsumBound :
      (∑ uv ∈ G, ‖coeff uv‖) ≤ (G.card : ℝ) * D ^ (2 * s) := by
    calc
      _ ≤ ∑ _uv ∈ G, D ^ (2 * s) :=
        Finset.sum_le_sum fun uv huv => hcoef uv huv
      _ = (G.card : ℝ) * D ^ (2 * s) := by simp
  have hfinal :
      realMoment ≤
        D ^ (2 * s) * (vinogradovCount s k M : ℝ) := by
    calc
      _ = (∑ uv ∈ G, coeff uv).re := hreal
      _ ≤ ‖∑ uv ∈ G, coeff uv‖ := Complex.re_le_norm _
      _ ≤ ∑ uv ∈ G, ‖coeff uv‖ := hsumNorm
      _ ≤ (G.card : ℝ) * D ^ (2 * s) := hsumBound
      _ ≤ (vinogradovCount s k M : ℝ) * D ^ (2 * s) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (pow_nonneg hD _)
      _ = D ^ (2 * s) * (vinogradovCount s k M : ℝ) := by ring
  rw [integral_indicator hcubeMeas, hcubeEq]
  change (∫ a in cube,
      ‖phaseWeightedWeylSum (M := M) c a‖ ^ (2 * s)
        ∂(volume : Measure (Fin k → ℝ))) ≤ _
  simpa [realMoment] using hfinal

def phaseClosedBox {k M : ℕ} (r : PhaseBoxIndex k M) : Set (Fin k → ℝ) :=
  {a | ∀ j : Fin k,
    ((r j).val : ℝ) / (M : ℝ) ^ (j.val + 1) ≤ a j ∧
      a j ≤ ((r j).val + 1 : ℝ) / (M : ℝ) ^ (j.val + 1)}

noncomputable def phaseBoxExponent (k : ℕ) : ℕ :=
  ∑ j : Fin k, (j.val + 1)

private def phaseBoxUnitCube (k : ℕ) : Set (Fin k → ℝ) :=
  {x | ∀ j, 0 ≤ x j ∧ x j ≤ 1}

private noncomputable def phaseBoxPoint {k M : ℕ} (r : PhaseBoxIndex k M)
    (x : Fin k → ℝ) : Fin k → ℝ :=
  fun j => (((r j).val : ℝ) + x j) / (M : ℝ) ^ (j.val + 1)

private noncomputable def phaseBoxRescaledSum {k M : ℕ}
    (r : PhaseBoxIndex k M) (x : Fin k → ℝ) : ℂ :=
  phaseWeylSum k M (phaseBoxPoint r x)

private noncomputable def phaseBoxMixedWeylSum {k M : ℕ}
    (r : PhaseBoxIndex k M) (e : Finset (Fin k)) (x : Fin k → ℝ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 M,
    (∏ j ∈ e, (2 * Real.pi * Complex.I) *
      (((((h : ℝ) / (M : ℝ)) ^ (j.val + 1)) : ℝ) : ℂ)) *
      additiveCharacter (∑ j : Fin k,
        phaseBoxPoint r x j * (h : ℝ) ^ (j.val + 1))

private theorem phase_box_rescaled_mem {k M : ℕ}
    (r : PhaseBoxIndex k M) (a : Fin k → ℝ) (hM : 0 < M) :
    a ∈ phaseClosedBox r ↔
      ∀ j : Fin k,
        0 ≤ (M : ℝ) ^ (j.val + 1) * a j - (r j).val ∧
          (M : ℝ) ^ (j.val + 1) * a j - (r j).val ≤ 1 := by
  constructor
  · intro ha j
    rcases ha j with ⟨hlo, hhi⟩
    have hd : 0 < (M : ℝ) ^ (j.val + 1) := by positivity
    rw [div_le_iff₀ hd] at hlo
    rw [le_div_iff₀ hd] at hhi
    constructor <;> nlinarith
  · intro ha j
    have hd : 0 < (M : ℝ) ^ (j.val + 1) := by positivity
    constructor
    · apply (div_le_iff₀ hd).2
      have hj := (ha j).1
      nlinarith
    · apply (le_div_iff₀ hd).2
      have hj := (ha j).2
      nlinarith

private theorem phase_box_rescaled_eq {k M : ℕ}
    (r : PhaseBoxIndex k M) (a : Fin k → ℝ) (hM : 0 < M)
    (ha : a ∈ phaseClosedBox r) :
    phaseWeylSum k M a = phaseBoxRescaledSum r
      (fun j => (M : ℝ) ^ (j.val + 1) * a j - (r j).val) := by
  unfold phaseBoxRescaledSum
  congr 1
  funext j
  simp only [phaseBoxPoint]
  have hd : (M : ℝ) ^ (j.val + 1) ≠ 0 := by positivity
  field_simp
  <;> ring

private theorem phase_box_mixed_derivative {k M : ℕ}
    (r : PhaseBoxIndex k M) (e : Finset (Fin k)) (j : Fin k)
    (hM : 0 < M) (hje : j ∉ e) (x : Fin k → ℝ) :
    HasDerivAt
      (fun t => phaseBoxMixedWeylSum r e (Function.update x j t))
      (phaseBoxMixedWeylSum r (insert j e) x) (x j) := by
  classical
  unfold phaseBoxMixedWeylSum
  apply HasDerivAt.fun_sum
  intro h hh
  let p : ℕ := j.val + 1
  let d : ℝ := (M : ℝ) ^ p
  let w : ℝ := (h : ℝ) ^ p
  have hd : d ≠ 0 := by
    dsimp [d]
    positivity
  have hratio : (1 / d) * w = (((h : ℝ) / (M : ℝ)) ^ p) := by
    dsimp [d, w]
    rw [div_pow]
    field_simp
  have hcoords (i : Fin k) :
      HasDerivAt
        (fun t => phaseBoxPoint r (Function.update x j t) i *
          (h : ℝ) ^ (i.val + 1))
        (if i = j then (1 / d) * w else 0) (x j) := by
    by_cases hij : i = j
    · subst i
      have hlin : HasDerivAt
          (fun t : ℝ => (((r j).val : ℝ) + t) / d * w)
          ((1 / d) * w) (x j) := by
        have h₀ := ((hasDerivAt_id (x j)).add_const ((r j).val : ℝ)).div_const d
        have h₁ := h₀.mul_const w
        convert h₁ using 1
        · funext t
          simp [d, w, add_comm]
      simpa [phaseBoxPoint, Function.update_self, d, w, add_comm] using hlin
    · have hconst : HasDerivAt
          (fun _ : ℝ => phaseBoxPoint r x i * (h : ℝ) ^ (i.val + 1))
          0 (x j) := hasDerivAt_const _ _
      simpa [phaseBoxPoint, Function.update_of_ne hij, hij] using hconst
  have hangle : HasDerivAt
      (fun t => ∑ i : Fin k,
        phaseBoxPoint r (Function.update x j t) i * (h : ℝ) ^ (i.val + 1))
      (((h : ℝ) / (M : ℝ)) ^ p) (x j) := by
    have hsum := HasDerivAt.fun_sum (fun i (_hi : i ∈ (Finset.univ : Finset (Fin k))) =>
      hcoords i)
    convert hsum using 1
    simpa [Finset.sum_ite_eq, hratio.symm]
  let angle : ℝ → ℝ := fun t =>
    ∑ i : Fin k,
      phaseBoxPoint r (Function.update x j t) i * (h : ℝ) ^ (i.val + 1)
  let coeff : Fin k → ℂ := fun i =>
    (2 * Real.pi * Complex.I) *
      (((((h : ℝ) / (M : ℝ)) ^ (i.val + 1)) : ℝ) : ℂ)
  have hcast := hangle.ofReal_comp
  have hcomplex : HasDerivAt
      (fun t : ℝ => Complex.I *
        ((2 * Real.pi * angle t : ℝ) : ℂ))
      (Complex.I * ((2 * Real.pi : ℂ) *
        (((h : ℝ) / (M : ℝ)) ^ p : ℝ) : ℂ)) (x j) := by
    convert (hcast.const_mul (2 * Real.pi : ℂ)).const_mul Complex.I using 1
    · funext t
      simp [angle, Complex.ofReal_mul]
  have hchar : HasDerivAt
      (fun t => additiveCharacter (angle t))
      (coeff j * additiveCharacter (angle (x j))) (x j) := by
    have hcexp := hcomplex.cexp
    convert hcexp using 1
    · funext t
      simp [additiveCharacter, angle, Complex.ofReal_mul]
    · simp [coeff, additiveCharacter, angle, Complex.ofReal_mul]
      ring
  have hterm := HasDerivAt.const_mul (∏ i ∈ e, coeff i) hchar
  simpa [coeff, angle, Finset.prod_insert, hje, mul_assoc, mul_left_comm,
    mul_comm] using hterm

private theorem phase_box_interval_sobolev {f f' : ℝ → ℂ}
    (hf : ContDiff ℝ 1 f)
    (hderiv : ∀ t, HasDerivAt f (f' t) t)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ‖f x‖ₑ ≤
      (∫⁻ y in Set.Icc (0 : ℝ) 1, ‖f y‖ₑ) +
        (∫⁻ y in Set.Icc (0 : ℝ) 1, ‖f' y‖ₑ) := by
  classical
  let μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)
  let aBound : ENNReal := ∫⁻ y, ‖f' y‖ₑ ∂μ
  have hderiv_eq (t : ℝ) : deriv f t = f' t := (hderiv t).deriv
  have hFTC (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
      ‖f x - f y‖ₑ ≤ aBound := by
    rcases le_total x y with hxy | hyx
    · have hcont : ContDiffOn ℝ 1 f (Set.Icc x y) :=
        hf.contDiffOn.mono (Set.Icc_subset_Icc hx.1 hy.2)
      calc
        ‖f x - f y‖ₑ = ‖f y - f x‖ₑ := by
          rw [show f x - f y = -(f y - f x) by abel, enorm_neg]
        _ ≤ ∫⁻ t in Set.Icc x y, ‖deriv f t‖ₑ :=
          enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hcont hxy
        _ ≤ ∫⁻ t in Set.Icc (0 : ℝ) 1, ‖deriv f t‖ₑ :=
          lintegral_mono_set (Set.Icc_subset_Icc hx.1 hy.2)
        _ = aBound := by
          apply lintegral_congr_ae
          filter_upwards with t
          simp [aBound, hderiv_eq]
    · have hyx' : y ≤ x := hyx
      have hcont : ContDiffOn ℝ 1 f (Set.Icc y x) :=
        hf.contDiffOn.mono (Set.Icc_subset_Icc hy.1 hx.2)
      calc
        ‖f x - f y‖ₑ ≤ ∫⁻ t in Set.Icc y x, ‖deriv f t‖ₑ :=
          enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hcont hyx'
        _ ≤ ∫⁻ t in Set.Icc (0 : ℝ) 1, ‖deriv f t‖ₑ :=
          lintegral_mono_set (Set.Icc_subset_Icc hy.1 hx.2)
        _ = aBound := by
          apply lintegral_congr_ae
          filter_upwards with t
          simp [aBound, hderiv_eq]
  have hpoint (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
      ‖f x‖ₑ ≤ ‖f y‖ₑ + aBound := by
    calc
      ‖f x‖ₑ = ‖f y + (f x - f y)‖ₑ := by congr 1 <;> ring
      _ ≤ ‖f y‖ₑ + ‖f x - f y‖ₑ := enorm_add_le _ _
      _ ≤ ‖f y‖ₑ + aBound := by
        calc
          _ = ‖f y‖ₑ + ‖f x - f y‖ₑ := by ac_rfl
          _ ≤ ‖f y‖ₑ + aBound := add_le_add_right (hFTC y hy) _
  have hmono :
      (∫⁻ y, ‖f x‖ₑ ∂μ) ≤ ∫⁻ y, (‖f y‖ₑ + aBound) ∂μ := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with y hy
    exact hpoint y hy
  have hmeas : Measurable (fun y : ℝ => ‖f y‖ₑ) :=
    hf.continuous.measurable.enorm
  have hleft : (∫⁻ y, ‖f x‖ₑ ∂μ) = ‖f x‖ₑ := by
    rw [lintegral_const]
    simp [μ, Real.volume_Icc]
  have hright :
      (∫⁻ y, (‖f y‖ₑ + aBound) ∂μ) = (∫⁻ y, ‖f y‖ₑ ∂μ) + aBound := by
    rw [lintegral_add_left hmeas, lintegral_const]
    simp [μ, Real.volume_Icc, mul_comm]
  simpa [aBound, μ] using hleft.symm.le.trans (hmono.trans_eq hright)

private theorem phase_box_mixed_line_contDiff (k M : ℕ)
    (r : PhaseBoxIndex k M) (e : Finset (Fin k)) (j : Fin k)
    (x : Fin k → ℝ) :
    ContDiff ℝ 1 (fun t => phaseBoxMixedWeylSum r e (Function.update x j t)) := by
  classical
  have hpoint (i : Fin k) :
      ContDiff ℝ 1 (fun t => phaseBoxPoint r (Function.update x j t) i) := by
    simp only [phaseBoxPoint, Function.update_apply]
    split_ifs <;> fun_prop
  have hangle (h : ℕ) :
      ContDiff ℝ 1 (fun t =>
        ∑ i : Fin k, phaseBoxPoint r (Function.update x j t) i *
          (h : ℝ) ^ (i.val + 1)) := by
    apply ContDiff.sum
    intro i hi
    exact (hpoint i).mul contDiff_const
  have hangleC (h : ℕ) :
      ContDiff ℝ 1 (fun t =>
        ((∑ i : Fin k, phaseBoxPoint r (Function.update x j t) i *
          (h : ℝ) ^ (i.val + 1) : ℝ) : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp (hangle h)
  have hterm (h : ℕ) :
      ContDiff ℝ 1 (fun t =>
        (∏ i ∈ e, (2 * Real.pi * Complex.I) *
          (((((h : ℝ) / (M : ℝ)) ^ (i.val + 1)) : ℝ) : ℂ)) *
        additiveCharacter (∑ i : Fin k,
          phaseBoxPoint r (Function.update x j t) i * (h : ℝ) ^ (i.val + 1))) := by
    unfold additiveCharacter
    exact contDiff_const.mul <| Complex.contDiff_exp.comp <| by
      simpa only [Complex.ofRealCLM_apply, Complex.ofReal_mul] using
        (contDiff_const.mul (contDiff_const.mul (hangleC h)))
  unfold phaseBoxMixedWeylSum
  change ContDiff ℝ 1 (fun t =>
    ∑ h ∈ Finset.Icc 1 M,
      (∏ i ∈ e, (2 * Real.pi * Complex.I) *
        (((((h : ℝ) / (M : ℝ)) ^ (i.val + 1)) : ℝ) : ℂ)) *
      additiveCharacter (∑ i : Fin k,
        phaseBoxPoint r (Function.update x j t) i * (h : ℝ) ^ (i.val + 1)))
  apply ContDiff.sum
  intro h hh
  exact hterm h

private theorem phase_box_line_sobolev (k M : ℕ) (hM : 0 < M)
    (r : PhaseBoxIndex k M) (e : Finset (Fin k)) (j : Fin k)
    (hje : j ∉ e) (x : Fin k → ℝ)
    (hxj : x j ∈ Set.Icc (0 : ℝ) 1) :
    ‖phaseBoxMixedWeylSum r e x‖ ≤
      (∫ t in Set.Icc (0 : ℝ) 1,
        ‖phaseBoxMixedWeylSum r e (Function.update x j t)‖) +
      (∫ t in Set.Icc (0 : ℝ) 1,
        ‖phaseBoxMixedWeylSum r (insert j e) (Function.update x j t)‖) := by
  let f : ℝ → ℂ := fun t =>
    phaseBoxMixedWeylSum r e (Function.update x j t)
  let f' : ℝ → ℂ := fun t =>
    phaseBoxMixedWeylSum r (insert j e) (Function.update x j t)
  have hf : ContDiff ℝ 1 f := by
    exact phase_box_mixed_line_contDiff k M r e j x
  have hf' : Continuous f' := by
    exact (phase_box_mixed_line_contDiff k M r (insert j e) j x).continuous
  have hderiv : ∀ t, HasDerivAt f (f' t) t := by
    intro t
    have h := phase_box_mixed_derivative r e j hM hje (Function.update x j t)
    simpa [f, f', Function.update_idem] using h
  have h := phase_box_interval_sobolev hf hderiv hxj
  have hfi : Integrable f (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    exact hf.continuous.continuousOn.integrableOn_compact isCompact_Icc
  have hfi' : Integrable f' (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    exact hf'.continuousOn.integrableOn_compact isCompact_Icc
  have hnormf :
      ENNReal.ofReal (∫ t in Set.Icc (0 : ℝ) 1, ‖f t‖) =
        ∫⁻ t in Set.Icc (0 : ℝ) 1, ‖f t‖ₑ := by
    simpa using (MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm hfi)
  have hnormf' :
      ENNReal.ofReal (∫ t in Set.Icc (0 : ℝ) 1, ‖f' t‖) =
        ∫⁻ t in Set.Icc (0 : ℝ) 1, ‖f' t‖ₑ := by
    simpa using (MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm hfi')
  have hA : 0 ≤ ∫ t in Set.Icc (0 : ℝ) 1, ‖f t‖ :=
    setIntegral_nonneg measurableSet_Icc fun _ _ => norm_nonneg _
  have hB : 0 ≤ ∫ t in Set.Icc (0 : ℝ) 1, ‖f' t‖ :=
    setIntegral_nonneg measurableSet_Icc fun _ _ => norm_nonneg _
  rw [show ‖f (x j)‖ₑ = ENNReal.ofReal ‖f (x j)‖ by simp,
    ← hnormf, ← hnormf'] at h
  rw [← ENNReal.ofReal_add hA hB] at h
  have hAB : 0 ≤ (∫ t in Set.Icc (0 : ℝ) 1, ‖f t‖) +
      ∫ t in Set.Icc (0 : ℝ) 1, ‖f' t‖ := add_nonneg hA hB
  have hreal := (ENNReal.ofReal_le_ofReal_iff hAB).mp h
  simpa [f, f'] using hreal

private theorem phase_box_mixed_continuous (k M : ℕ)
    (r : PhaseBoxIndex k M) (e : Finset (Fin k)) :
    Continuous (phaseBoxMixedWeylSum r e) := by
  unfold phaseBoxMixedWeylSum phaseBoxPoint additiveCharacter
  fun_prop

private theorem phase_box_line_sobolev_enorm (k M : ℕ) (hM : 0 < M)
    (r : PhaseBoxIndex k M) (e : Finset (Fin k)) (j : Fin k)
    (hje : j ∉ e) (x : Fin k → ℝ)
    (hxj : x j ∈ Set.Icc (0 : ℝ) 1) :
    ‖phaseBoxMixedWeylSum r e x‖ₑ ≤
      (∫⁻ t in Set.Icc (0 : ℝ) 1,
        ‖phaseBoxMixedWeylSum r e (Function.update x j t)‖ₑ) +
      (∫⁻ t in Set.Icc (0 : ℝ) 1,
        ‖phaseBoxMixedWeylSum r (insert j e) (Function.update x j t)‖ₑ) := by
  let f : ℝ → ℂ := fun t =>
    phaseBoxMixedWeylSum r e (Function.update x j t)
  let f' : ℝ → ℂ := fun t =>
    phaseBoxMixedWeylSum r (insert j e) (Function.update x j t)
  have hf : ContDiff ℝ 1 f := phase_box_mixed_line_contDiff k M r e j x
  have hderiv : ∀ t, HasDerivAt f (f' t) t := by
    intro t
    have h := phase_box_mixed_derivative r e j hM hje (Function.update x j t)
    simpa [f, f', Function.update_idem] using h
  have h := phase_box_interval_sobolev hf hderiv hxj
  simpa [f, f', Function.update_self] using h

private theorem phase_box_sobolev_aux (k M : ℕ) (hM : 0 < M)
    (r : PhaseBoxIndex k M) (s e : Finset (Fin k))
    (hdisj : Disjoint e s) (x : Fin k → ℝ)
    (hx : ∀ j ∈ s, x j ∈ Set.Icc (0 : ℝ) 1) :
    ‖phaseBoxMixedWeylSum r e x‖ₑ ≤
      ∑ d ∈ s.powerset,
        (∫⋯∫⁻_s, (fun y : Fin k → ℝ =>
          ‖phaseBoxMixedWeylSum r (e ∪ d) y‖ₑ)
          ∂(fun _ : Fin k => volume.restrict (Set.Icc (0 : ℝ) 1))) x := by
  classical
  let μ : Fin k → Measure ℝ := fun _ => volume.restrict (Set.Icc (0 : ℝ) 1)
  have hmeas (d : Finset (Fin k)) : Measurable fun y : Fin k → ℝ =>
      ‖phaseBoxMixedWeylSum r d y‖ₑ := by
    exact (phase_box_mixed_continuous k M r d).measurable.enorm
  induction s using Finset.induction_on generalizing e x with
  | empty =>
      simp
  | @insert j s hj ih =>
      have hjE : j ∉ e := by
        intro hje
        exact (Finset.disjoint_left.mp hdisj) hje (Finset.mem_insert_self j s)
      have hdisjTail : Disjoint e s := by
        apply Finset.disjoint_left.mpr
        intro z hze hzS
        exact (Finset.disjoint_left.mp hdisj) hze (Finset.mem_insert_of_mem hzS)
      have hdisjInsert : Disjoint (insert j e) s := by
        apply Finset.disjoint_left.mpr
        intro z hze hzS
        rcases Finset.mem_insert.mp hze with rfl | hze
        · exact hj hzS
        · exact (Finset.disjoint_left.mp hdisj) hze (Finset.mem_insert_of_mem hzS)
      have hxj : x j ∈ Set.Icc (0 : ℝ) 1 := hx j (Finset.mem_insert_self j s)
      have hline := phase_box_line_sobolev_enorm k M hM r e j hjE x hxj
      have hxTail (t : ℝ) : ∀ i ∈ s, Function.update x j t i ∈ Set.Icc (0 : ℝ) 1 := by
        intro i hi
        have hne : i ≠ j := by
          intro hij'
          subst i
          exact hj hi
        simpa [Function.update_of_ne hne] using hx i (Finset.mem_insert_of_mem hi)
      have hIntLeft :
          (∫⁻ t, ‖phaseBoxMixedWeylSum r e (Function.update x j t)‖ₑ
            ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) ≤
          ∑ d ∈ s.powerset,
            (∫⋯∫⁻_insert j s, (fun y : Fin k → ℝ =>
              ‖phaseBoxMixedWeylSum r (e ∪ d) y‖ₑ)
              ∂(fun _ : Fin k => volume.restrict (Set.Icc (0 : ℝ) 1))) x := by
        calc
          _ ≤ ∫⁻ t, ∑ d ∈ s.powerset,
                (∫⋯∫⁻_s, (fun y : Fin k → ℝ =>
                  ‖phaseBoxMixedWeylSum r (e ∪ d) y‖ₑ)
                  ∂(fun _ : Fin k => volume.restrict (Set.Icc (0 : ℝ) 1)))
                  (Function.update x j t)
                ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) := by
            apply lintegral_mono
            intro t
            exact ih e hdisjTail (Function.update x j t) (hxTail t)
          _ = ∑ d ∈ s.powerset,
                ∫⁻ t,
                  (∫⋯∫⁻_s, (fun y : Fin k → ℝ =>
                    ‖phaseBoxMixedWeylSum r (e ∪ d) y‖ₑ)
                    ∂(fun _ : Fin k => volume.restrict (Set.Icc (0 : ℝ) 1)))
                    (Function.update x j t)
                  ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) := by
            rw [MeasureTheory.lintegral_finsetSum
              (μ := volume.restrict (Set.Icc (0 : ℝ) 1))]
            · intro d hd
              exact ((hmeas (e ∪ d)).lmarginal μ).comp (by fun_prop)
          _ = _ := by
            apply Finset.sum_congr rfl
            intro d hd
            exact (MeasureTheory.lmarginal_insert
              (μ := fun _ : Fin k => volume.restrict (Set.Icc (0 : ℝ) 1))
              (f := fun y : Fin k → ℝ =>
                ‖phaseBoxMixedWeylSum r (e ∪ d) y‖ₑ)
              ((hmeas (e ∪ d))) hj x).symm
      have hIntRight :
          (∫⁻ t, ‖phaseBoxMixedWeylSum r (insert j e) (Function.update x j t)‖ₑ
            ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) ≤
          ∑ d ∈ s.powerset,
            (∫⋯∫⁻_insert j s, (fun y : Fin k → ℝ =>
              ‖phaseBoxMixedWeylSum r (insert j e ∪ d) y‖ₑ)
              ∂(fun _ : Fin k => volume.restrict (Set.Icc (0 : ℝ) 1))) x := by
        calc
          _ ≤ ∫⁻ t, ∑ d ∈ s.powerset,
                (∫⋯∫⁻_s, (fun y : Fin k → ℝ =>
                  ‖phaseBoxMixedWeylSum r (insert j e ∪ d) y‖ₑ)
                  ∂(fun _ : Fin k => volume.restrict (Set.Icc (0 : ℝ) 1)))
                  (Function.update x j t)
                ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) := by
            apply lintegral_mono
            intro t
            exact ih (insert j e) hdisjInsert (Function.update x j t) (hxTail t)
          _ = ∑ d ∈ s.powerset,
                ∫⁻ t,
                  (∫⋯∫⁻_s, (fun y : Fin k → ℝ =>
                    ‖phaseBoxMixedWeylSum r (insert j e ∪ d) y‖ₑ)
                    ∂(fun _ : Fin k => volume.restrict (Set.Icc (0 : ℝ) 1)))
                    (Function.update x j t)
                  ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) := by
            rw [MeasureTheory.lintegral_finsetSum
              (μ := volume.restrict (Set.Icc (0 : ℝ) 1))]
            · intro d hd
              exact ((hmeas (insert j e ∪ d)).lmarginal μ).comp (by fun_prop)
          _ = _ := by
            apply Finset.sum_congr rfl
            intro d hd
            exact (MeasureTheory.lmarginal_insert
              (μ := fun _ : Fin k => volume.restrict (Set.Icc (0 : ℝ) 1))
              (f := fun y : Fin k → ℝ =>
                ‖phaseBoxMixedWeylSum r (insert j e ∪ d) y‖ₑ)
              ((hmeas (insert j e ∪ d))) hj x).symm
      have hPdisj : Disjoint s.powerset (s.powerset.image (insert j)) := by
        apply Finset.disjoint_left.mpr
        intro d hd hdm
        rcases Finset.mem_image.mp hdm with ⟨d', hd', hEq⟩
        have hjd : j ∉ d := Finset.notMem_of_mem_powerset_of_notMem hd hj
        have hjmem : j ∈ d := by rw [← hEq]; simp
        exact hjd hjmem
      have hPInj : Set.InjOn (insert j) (s.powerset : Set (Finset (Fin k))) := by
        intro d hd d' hd' hEq
        apply Finset.ext
        intro z
        by_cases hz : z = j
        · subst z
          have hjd : j ∉ d := Finset.notMem_of_mem_powerset_of_notMem hd hj
          have hjd' : j ∉ d' := Finset.notMem_of_mem_powerset_of_notMem hd' hj
          simp [hjd, hjd']
        · have hmem := congrArg (fun u : Finset (Fin k) => z ∈ u) hEq
          simpa [hz] using hmem
      have hsum :
          (∑ d ∈ s.powerset,
            (∫⋯∫⁻_insert j s, (fun y : Fin k → ℝ =>
              ‖phaseBoxMixedWeylSum r (e ∪ d) y‖ₑ)
              ∂(fun _ : Fin k => volume.restrict (Set.Icc (0 : ℝ) 1))) x) +
          ∑ d ∈ s.powerset,
            (∫⋯∫⁻_insert j s, (fun y : Fin k → ℝ =>
              ‖phaseBoxMixedWeylSum r (insert j e ∪ d) y‖ₑ)
              ∂(fun _ : Fin k => volume.restrict (Set.Icc (0 : ℝ) 1))) x =
          ∑ d ∈ (insert j s).powerset,
            (∫⋯∫⁻_insert j s, (fun y : Fin k → ℝ =>
              ‖phaseBoxMixedWeylSum r (e ∪ d) y‖ₑ)
              ∂(fun _ : Fin k => volume.restrict (Set.Icc (0 : ℝ) 1))) x := by
        rw [Finset.powerset_insert, Finset.sum_union hPdisj, Finset.sum_image hPInj]
        conv_rhs => rw [← Finset.sum_add_distrib]
        conv_lhs => rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro d hd
        congr 2
        ext z
        simp [Finset.mem_union, Finset.mem_insert, or_assoc, or_left_comm, or_comm]
      calc
        _ ≤ (∫⁻ t, ‖phaseBoxMixedWeylSum r e (Function.update x j t)‖ₑ
              ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) +
            ∫⁻ t, ‖phaseBoxMixedWeylSum r (insert j e) (Function.update x j t)‖ₑ
              ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) := by simpa using hline
        _ ≤ _ := add_le_add hIntLeft hIntRight
        _ = _ := hsum

private theorem phase_box_sobolev (k M : ℕ) (hM : 0 < M)
    (r : PhaseBoxIndex k M) (x : Fin k → ℝ)
    (hx : x ∈ phaseBoxUnitCube k) :
    ‖phaseBoxMixedWeylSum r ∅ x‖ ≤
      ∑ e : Finset (Fin k),
        ∫ y in phaseBoxUnitCube k, ‖phaseBoxMixedWeylSum r e y‖ := by
  classical
  let μ : Fin k → Measure ℝ := fun _ => volume.restrict (Set.Icc (0 : ℝ) 1)
  have hcubeEq : phaseBoxUnitCube k =
      Set.univ.pi (fun _ : Fin k => Set.Icc (0 : ℝ) 1) := by
    ext y
    simp [phaseBoxUnitCube, Set.mem_pi, Pi.le_def, forall_and]
  have hcubeMeas : MeasurableSet (phaseBoxUnitCube k) := by
    rw [hcubeEq]
    exact MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hcubeCompact : IsCompact (phaseBoxUnitCube k) := by
    rw [hcubeEq]
    exact isCompact_univ_pi fun _ => isCompact_Icc
  have hx' : ∀ j ∈ (Finset.univ : Finset (Fin k)),
      x j ∈ Set.Icc (0 : ℝ) 1 := by
    intro j hj
    exact hx j
  have hlin := phase_box_sobolev_aux k M hM r Finset.univ ∅ (by simp) x hx'
  have hpow : (Finset.univ : Finset (Fin k)).powerset =
      (Finset.univ : Finset (Finset (Fin k))) := by
    ext e
    simp
  have hlinPi :
      ‖phaseBoxMixedWeylSum r ∅ x‖ₑ ≤
        ∑ d ∈ (Finset.univ : Finset (Fin k)).powerset,
          ∫⁻ y, ‖phaseBoxMixedWeylSum r d y‖ₑ ∂Measure.pi μ := by
    calc
      _ ≤ ∑ d ∈ (Finset.univ : Finset (Fin k)).powerset,
          (∫⋯∫⁻_Finset.univ, (fun y : Fin k → ℝ =>
            ‖phaseBoxMixedWeylSum r d y‖ₑ) ∂μ) x := by
        simpa [Finset.union_empty] using hlin
      _ = _ := by
        apply Finset.sum_congr rfl
        intro d hd
        exact (MeasureTheory.lintegral_eq_lmarginal_univ
          (μ := μ) (f := fun y : Fin k → ℝ =>
            ‖phaseBoxMixedWeylSum r d y‖ₑ) x).symm
  have hlin :
      ‖phaseBoxMixedWeylSum r ∅ x‖ₑ ≤
        ∑ e : Finset (Fin k),
          ∫⁻ y, ‖phaseBoxMixedWeylSum r e y‖ₑ ∂Measure.pi μ := by
    simpa only [hpow] using hlinPi
  have hchange (e : Finset (Fin k)) :
      (∫⁻ y in phaseBoxUnitCube k,
        ‖phaseBoxMixedWeylSum r e y‖ₑ) =
      ∫⁻ y, ‖phaseBoxMixedWeylSum r e y‖ₑ ∂Measure.pi μ := by
    rw [hcubeEq, volume_pi, Measure.restrict_pi_pi]
  have hlinCube :
      ‖phaseBoxMixedWeylSum r ∅ x‖ₑ ≤
        ∑ e : Finset (Fin k),
          ∫⁻ y in phaseBoxUnitCube k,
            ‖phaseBoxMixedWeylSum r e y‖ₑ := by
    calc
      _ ≤ ∑ e : Finset (Fin k),
          ∫⁻ y, ‖phaseBoxMixedWeylSum r e y‖ₑ ∂Measure.pi μ := by
        simpa using hlin
      _ = _ := by
        apply Finset.sum_congr rfl
        intro e he
        exact (hchange e).symm
  have hnormIntegral (e : Finset (Fin k)) :
      ENNReal.ofReal
          (∫ y in phaseBoxUnitCube k, ‖phaseBoxMixedWeylSum r e y‖) =
        ∫⁻ y in phaseBoxUnitCube k,
          ‖phaseBoxMixedWeylSum r e y‖ₑ := by
    have hfi : Integrable (phaseBoxMixedWeylSum r e)
        (volume.restrict (phaseBoxUnitCube k)) :=
      (phase_box_mixed_continuous k M r e).continuousOn.integrableOn_compact hcubeCompact
    simpa using MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm hfi
  have hnonneg (e : Finset (Fin k)) :
      0 ≤ ∫ y in phaseBoxUnitCube k, ‖phaseBoxMixedWeylSum r e y‖ :=
    setIntegral_nonneg hcubeMeas fun y hy => norm_nonneg _
  have hsum :
      ENNReal.ofReal
          (∑ e : Finset (Fin k),
            ∫ y in phaseBoxUnitCube k, ‖phaseBoxMixedWeylSum r e y‖) =
        ∑ e : Finset (Fin k),
          ENNReal.ofReal
            (∫ y in phaseBoxUnitCube k, ‖phaseBoxMixedWeylSum r e y‖) := by
    simpa using ENNReal.ofReal_sum_of_nonneg
      (s := Finset.univ)
      (f := fun e => ∫ y in phaseBoxUnitCube k,
        ‖phaseBoxMixedWeylSum r e y‖)
      (fun e he => hnonneg e)
  simp_rw [← hnormIntegral] at hlinCube
  rw [← hsum] at hlinCube
  rw [show ‖phaseBoxMixedWeylSum r ∅ x‖ₑ =
      ENNReal.ofReal ‖phaseBoxMixedWeylSum r ∅ x‖ by simp] at hlinCube
  have hsumNonneg : 0 ≤ ∑ e : Finset (Fin k),
      ∫ y in phaseBoxUnitCube k, ‖phaseBoxMixedWeylSum r e y‖ :=
    Finset.sum_nonneg fun e _ => hnonneg e
  exact (ENNReal.ofReal_le_ofReal_iff hsumNonneg).mp hlinCube

private noncomputable def phase_box_affineHomeomorph (a b : ℝ) (ha : a ≠ 0) : ℝ ≃ₜ ℝ where
  toFun x := (b + x) / a
  invFun y := a * y - b
  left_inv x := by
    dsimp
    field_simp [ha]
    ring
  right_inv y := by
    dsimp
    field_simp [ha]
    ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private theorem phase_box_affine_map_ioc {a b : ℝ} (ha : 0 < a) :
    Measure.map (phase_box_affineHomeomorph a b ha.ne')
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) =
      ENNReal.ofReal a • volume.restrict (Set.Ioc (b / a) ((b + 1) / a)) := by
  let e := phase_box_affineHomeomorph a b ha.ne'
  have himage : e '' Set.Ioc (0 : ℝ) 1 = Set.Ioc (b / a) ((b + 1) / a) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Set.mem_Ioc] at hx ⊢
      constructor
      · apply (div_lt_div_iff_of_pos_right ha).2
        linarith
      · apply (div_le_div_iff_of_pos_right ha).2
        linarith
    · intro hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      rw [Set.mem_Ioc]
      constructor
      · have h := (div_lt_iff₀ ha).mp hy.1
        dsimp [e, phase_box_affineHomeomorph]
        linarith
      · have h := (le_div_iff₀ ha).mp hy.2
        dsimp [e, phase_box_affineHomeomorph]
        linarith
  have hpre : e ⁻¹' Set.Ioc (b / a) ((b + 1) / a) = Set.Ioc (0 : ℝ) 1 := by
    rw [← himage]
    exact Set.preimage_image_eq _ e.injective
  have hscale : Measure.map (fun x : ℝ => a⁻¹ * x) volume =
      ENNReal.ofReal a • volume := by
    rw [show (fun x : ℝ => a⁻¹ * x) = (a⁻¹ * ·) by rfl,
      Real.map_volume_mul_left (inv_ne_zero ha.ne')]
    simp [abs_of_pos ha]
  have hvol : Measure.map e volume = ENNReal.ofReal a • volume := by
    have hfun : (e : ℝ → ℝ) =
        (fun y : ℝ => y + b / a) ∘ (fun x : ℝ => a⁻¹ * x) := by
      funext x
      dsimp [e, phase_box_affineHomeomorph]
      field_simp [ha.ne']
      ring
    rw [hfun, ← Measure.map_map (μ := volume) (by fun_prop) (by fun_prop)]
    rw [hscale, Measure.map_smul, map_add_right_eq_self]
    fun_prop
  calc
    _ = (volume.restrict (e ⁻¹' Set.Ioc (b / a) ((b + 1) / a))).map e := by
      rw [hpre]
    _ = (volume.map e).restrict (Set.Ioc (b / a) ((b + 1) / a)) :=
      e.measurableEmbedding.restrict_map volume _ |>.symm
    _ = (ENNReal.ofReal a • volume).restrict (Set.Ioc (b / a) ((b + 1) / a)) := by
      rw [hvol]
    _ = ENNReal.ofReal a •
        volume.restrict (Set.Ioc (b / a) ((b + 1) / a)) := by
      rw [Measure.restrict_smul]

private def phaseBoxIoc {k M : ℕ} (r : PhaseBoxIndex k M) : Set (Fin k → ℝ) :=
  Set.univ.pi (fun j : Fin k =>
    Set.Ioc (((r j).val : ℝ) / (M : ℝ) ^ (j.val + 1))
      ((((r j).val + 1 : ℕ) : ℝ) / (M : ℝ) ^ (j.val + 1)))

private def phaseBoxUnitIoc (k : ℕ) : Set (Fin k → ℝ) :=
  Set.univ.pi (fun _ : Fin k => Set.Ioc (0 : ℝ) 1)

private theorem phase_box_pi_smul {k : ℕ} (μ : Fin k → Measure ℝ)
    (c : Fin k → ℝ≥0∞) [∀ j, SigmaFinite (μ j)]
    (hfinite : ∀ j, IsFiniteMeasure (c j • μ j)) :
    Measure.pi (fun j => c j • μ j) = (∏ j, c j) • Measure.pi μ := by
  classical
  haveI (j : Fin k) : SigmaFinite (c j • μ j) := (hfinite j).toSigmaFinite
  apply Measure.pi_eq
  intro s hs
  simp only [Measure.smul_apply, smul_eq_mul, Measure.pi_pi]
  rw [← Finset.prod_mul_distrib]

private theorem phase_box_map_cube (k M : ℕ) (hM : 0 < M)
    (r : PhaseBoxIndex k M) :
    Measure.map (fun x : Fin k → ℝ => phaseBoxPoint r x)
        (Measure.pi (fun _ : Fin k => volume.restrict (Set.Ioc (0 : ℝ) 1))) =
      ENNReal.ofReal ((M : ℝ) ^ phaseBoxExponent k) •
        Measure.pi (fun j : Fin k => volume.restrict
          (Set.Ioc (((r j).val : ℝ) / (M : ℝ) ^ (j.val + 1))
            ((((r j).val + 1 : ℕ) : ℝ) / (M : ℝ) ^ (j.val + 1)))) := by
  classical
  let m (j : Fin k) : ℝ := (M : ℝ) ^ (j.val + 1)
  let b (j : Fin k) : ℝ := (r j).val
  let μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  have hm (j : Fin k) : 0 < m j := by
    dsimp [m]
    positivity
  have hcoord (j : Fin k) :
      Measure.map (fun x : ℝ => (b j + x) / m j) μ =
        ENNReal.ofReal (m j) • volume.restrict (Set.Ioc (b j / m j) ((b j + 1) / m j)) := by
    simpa [μ, phase_box_affineHomeomorph] using phase_box_affine_map_ioc (hm j)
  have hpi := Measure.pi_map_pi
    (μ := fun _ : Fin k => μ)
    (f := fun j x => (b j + x) / m j)
    (fun j => (by fun_prop : AEMeasurable (fun x : ℝ => (b j + x) / m j) μ))
  have hscale : ∏ j : Fin k, ENNReal.ofReal (m j) =
      ENNReal.ofReal ((M : ℝ) ^ phaseBoxExponent k) := by
    calc
      _ = ENNReal.ofReal (∏ j : Fin k, m j) := by
        symm
        exact ENNReal.ofReal_prod_of_nonneg (fun j _ => (le_of_lt (hm j)))
      _ = ENNReal.ofReal ((M : ℝ) ^ phaseBoxExponent k) := by
        congr 1
        simp only [m, phaseBoxExponent]
        rw [← Finset.prod_pow_eq_pow_sum]
  have hfinite (j : Fin k) : IsFiniteMeasure
      (ENNReal.ofReal (m j) • volume.restrict
        (Set.Ioc (b j / m j) ((b j + 1) / m j))) := by
    exact Measure.smul_finite
      (volume.restrict (Set.Ioc (b j / m j) ((b j + 1) / m j)))
      ENNReal.ofReal_ne_top
  calc
    _ = Measure.pi (fun j : Fin k =>
          ENNReal.ofReal (m j) • volume.restrict
            (Set.Ioc (b j / m j) ((b j + 1) / m j))) := by
      rw [show (fun x : Fin k → ℝ => phaseBoxPoint r x) =
        (fun x j => (b j + x j) / m j) by
          funext x
          funext j
          simp [phaseBoxPoint, b, m]]
      rw [hpi]
      simp_rw [hcoord]
    _ = (∏ j : Fin k, ENNReal.ofReal (m j)) •
          Measure.pi (fun j : Fin k => volume.restrict
            (Set.Ioc (b j / m j) ((b j + 1) / m j))) :=
      phase_box_pi_smul _ _ hfinite
    _ = _ := by
      rw [hscale]
      simp [b, m]

private theorem phase_box_ioc_disjoint {k M : ℕ} (hM : 0 < M) :
    ∀ r s : PhaseBoxIndex k M, r ≠ s → Disjoint (phaseBoxIoc r) (phaseBoxIoc s) := by
  classical
  intro r s hrs
  rw [Set.disjoint_left]
  intro x hxr hxs
  simp only [phaseBoxIoc, Set.mem_pi, Set.mem_univ, true_implies] at hxr hxs
  have hcoord : ∃ j : Fin k, r j ≠ s j := by
    by_contra h
    push_neg at h
    apply hrs
    funext j
    exact h j
  obtain ⟨j, hj⟩ := hcoord
  have hd : 0 < (M : ℝ) ^ (j.val + 1) := by positivity
  rcases lt_or_gt_of_ne hj with hlt | hgt
  · have hltval : (r j).val < (s j).val := hlt
    have hend : (((r j).val + 1 : ℕ) : ℝ) ≤ (s j).val := by
      exact_mod_cast Nat.succ_le_of_lt hltval
    have hinterval :
        (((r j).val + 1 : ℕ) : ℝ) / (M : ℝ) ^ (j.val + 1) ≤
          ((s j).val : ℝ) / (M : ℝ) ^ (j.val + 1) :=
      (div_le_div_iff_of_pos_right hd).2 hend
    have h₁ := (Set.mem_Ioc.mp (hxr j)).2
    have h₂ := (Set.mem_Ioc.mp (hxs j)).1
    linarith
  · have hltval : (s j).val < (r j).val := hgt
    have hend : (((s j).val + 1 : ℕ) : ℝ) ≤ (r j).val := by
      exact_mod_cast Nat.succ_le_of_lt hltval
    have hinterval :
        (((s j).val + 1 : ℕ) : ℝ) / (M : ℝ) ^ (j.val + 1) ≤
          ((r j).val : ℝ) / (M : ℝ) ^ (j.val + 1) :=
      (div_le_div_iff_of_pos_right hd).2 hend
    have h₁ := (Set.mem_Ioc.mp (hxs j)).2
    have h₂ := (Set.mem_Ioc.mp (hxr j)).1
    linarith

private theorem phase_box_ioc_cover {k M : ℕ} (hM : 0 < M) :
    Set.iUnion (fun r : PhaseBoxIndex k M => phaseBoxIoc (k := k) (M := M) r) =
      phaseBoxUnitIoc k := by
  classical
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨r, hr⟩
    simp only [phaseBoxIoc, Set.mem_pi, Set.mem_univ, true_implies] at hr
    simp only [phaseBoxUnitIoc, Set.mem_pi, Set.mem_univ, true_implies]
    intro j
    have hj := Set.mem_Ioc.mp (hr j)
    have hd : 0 < (M : ℝ) ^ (j.val + 1) := by positivity
    have hrle : (((r j).val + 1 : ℕ) : ℝ) ≤ (M : ℝ) ^ (j.val + 1) := by
      have hfin := (r j).isLt
      exact_mod_cast Nat.succ_le_of_lt hfin
    constructor
    · have hnonneg : 0 ≤ ((r j).val : ℝ) / (M : ℝ) ^ (j.val + 1) := by positivity
      linarith
    · have hdiv : (((r j).val + 1 : ℕ) : ℝ) / (M : ℝ) ^ (j.val + 1) ≤ 1 :=
        (div_le_one₀ hd).2 hrle
      exact hj.2.trans hdiv
  · intro hx
    simp only [phaseBoxUnitIoc, Set.mem_pi, Set.mem_univ, true_implies] at hx
    have hcoord (j : Fin k) :
        ∃ q : Fin (M ^ (j.val + 1)),
          x j ∈ Set.Ioc (((q.val : ℕ) : ℝ) / (M : ℝ) ^ (j.val + 1))
            ((((q.val + 1 : ℕ) : ℝ) / (M : ℝ) ^ (j.val + 1))) := by
      let n : ℕ := M ^ (j.val + 1)
      let z : ℝ := (n : ℝ) * x j
      have hn : 0 < n := by dsimp [n]; exact Nat.pow_pos hM
      have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
      have hncast : (n : ℝ) = (M : ℝ) ^ (j.val + 1) := by simp [n]
      have hxj := Set.mem_Ioc.mp (hx j)
      have hzpos : 0 < z := by dsimp [z]; exact mul_pos hnreal hxj.1
      have hzle : z ≤ (n : ℝ) := by
        dsimp [z]
        calc
          (n : ℝ) * x j ≤ (n : ℝ) * 1 := mul_le_mul_of_nonneg_left hxj.2 hnreal.le
          _ = (n : ℝ) := by ring
      have hceilpos : 1 ≤ Nat.ceil z := Nat.ceil_pos.mpr hzpos
      have hceille : Nat.ceil z ≤ n := Nat.ceil_le.mpr hzle
      let q : Fin n := ⟨Nat.ceil z - 1, by omega⟩
      refine ⟨q, ?_⟩
      rw [Set.mem_Ioc]
      constructor
      · have hceillt : (Nat.ceil z : ℝ) < z + 1 := Nat.ceil_lt_add_one (le_of_lt hzpos)
        have hcast : ((Nat.ceil z - 1 : ℕ) : ℝ) = (Nat.ceil z : ℝ) - 1 := by
          simpa using (Nat.cast_sub hceilpos : (↑(Nat.ceil z - 1) : ℝ) = ↑(Nat.ceil z) - ↑(1 : ℕ))
        rw [hcast]
        rw [← hncast]
        change ((Nat.ceil z : ℝ) - 1) / (n : ℝ) < x j
        apply (div_lt_iff₀ hnreal).2
        dsimp [z]
        nlinarith
      · have hsucc : q.val + 1 = Nat.ceil z := Nat.sub_add_cancel hceilpos
        rw [hsucc]
        rw [← hncast]
        change x j ≤ (Nat.ceil z : ℝ) / (n : ℝ)
        apply (le_div_iff₀ hnreal).2
        simpa [z, mul_comm] using (Nat.le_ceil z)
    choose q hq using hcoord
    refine ⟨q, ?_⟩
    simp only [phaseBoxIoc, Set.mem_pi, Set.mem_univ, true_implies]
    intro j
    simpa using hq j

private theorem phase_box_mixed_coefficient_norm_le {k M : ℕ}
    (hM : 1 ≤ M) (e : Finset (Fin k)) {h : ℕ}
    (hh : h ∈ Finset.Icc 1 M) :
    ‖∏ j ∈ e, (2 * Real.pi * Complex.I) *
      (((((h : ℝ) / (M : ℝ)) ^ (j.val + 1)) : ℝ) : ℂ)‖ ≤
        (2 * Real.pi : ℝ) ^ k := by
  classical
  have hMreal : 0 < (M : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hM)
  have hratio : 0 ≤ (h : ℝ) / (M : ℝ) ∧ (h : ℝ) / (M : ℝ) ≤ 1 := by
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) hMreal.le
    · exact (div_le_one₀ hMreal).2 (by exact_mod_cast (Finset.mem_Icc.mp hh).2)
  have hfactor (j : Fin k) :
    ‖(2 * Real.pi * Complex.I) *
      (((((h : ℝ) / (M : ℝ)) ^ (j.val + 1)) : ℝ) : ℂ)‖ ≤
          2 * Real.pi := by
    rw [norm_mul]
    have hconst : ‖(2 * Real.pi : ℂ) * Complex.I‖ = 2 * Real.pi := by
      rw [norm_mul, Complex.norm_I, mul_one, norm_mul]
      have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [htwo, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have hpow : ((h : ℝ) / (M : ℝ)) ^ (j.val + 1) ≤ 1 :=
      pow_le_one₀ hratio.1 hratio.2
    have hnorm : ‖((((h : ℝ) / (M : ℝ)) ^ (j.val + 1) : ℝ) : ℂ)‖ =
        ((h : ℝ) / (M : ℝ)) ^ (j.val + 1) := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg hratio.1 _)]
    rw [hconst, hnorm]
    calc
      2 * Real.pi * ((h : ℝ) / (M : ℝ)) ^ (j.val + 1) ≤
          2 * Real.pi * 1 :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = 2 * Real.pi := by ring
  have hprod :
      ‖∏ j ∈ e, (2 * Real.pi * Complex.I) *
        (((((h : ℝ) / (M : ℝ)) ^ (j.val + 1)) : ℝ) : ℂ)‖ ≤
        ∏ j ∈ e, (2 * Real.pi : ℝ) := by
    rw [norm_prod]
    apply Finset.prod_le_prod₀
    · intro j hj
      positivity
    · intro j hj
      exact hfactor j
  have hcard : e.card ≤ k := by simpa [Fintype.card_fin] using (Finset.card_le_univ e)
  have hpi : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  calc
    _ ≤ (2 * Real.pi) ^ e.card := by simpa using hprod
    _ ≤ (2 * Real.pi) ^ k := pow_le_pow_right₀ hpi hcard

private theorem phase_box_summed_mixed_moment (s k M : ℕ) (hM : 0 < M)
    (e : Finset (Fin k)) :
    ∑ r : PhaseBoxIndex k M,
      ∫ x in phaseBoxUnitCube k,
        ‖phaseBoxMixedWeylSum r e x‖ ^ (2 * s) ≤
      (M : ℝ) ^ phaseBoxExponent k *
        (2 * Real.pi : ℝ) ^ (2 * s * k) * (vinogradovCount s k M : ℝ) := by
  classical
  let coeff : ℕ → ℂ := fun h =>
    ∏ j ∈ e, (2 * Real.pi * Complex.I) *
      (((((h : ℝ) / (M : ℝ)) ^ (j.val + 1)) : ℝ) : ℂ)
  let F : (Fin k → ℝ) → ℝ := fun a =>
    ‖phaseWeightedWeylSum (M := M) coeff a‖ ^ (2 * s)
  have hM1 : 1 ≤ M := by omega
  have hcoeff (h : ℕ) (hh : h ∈ Finset.Icc 1 M) :
      ‖coeff h‖ ≤ (2 * Real.pi : ℝ) ^ k := by
    simpa [coeff] using phase_box_mixed_coefficient_norm_le hM1 e hh
  have hFcont : Continuous F := by
    dsimp [F, phaseWeightedWeylSum, additiveCharacter]
    fun_prop
  have hcubeEq : phaseBoxUnitCube k =
      Set.univ.pi (fun _ : Fin k => Set.Icc (0 : ℝ) 1) := by
    ext a
    simp [phaseBoxUnitCube, Pi.le_def, forall_and]
  have hcubeMeas : MeasurableSet (phaseBoxUnitCube k) := by
    rw [hcubeEq]
    exact MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hcubeCompact : IsCompact (phaseBoxUnitCube k) := by
    rw [hcubeEq]
    exact isCompact_univ_pi fun _ => isCompact_Icc
  have hcubeIcc : Set.Icc (fun _ : Fin k => (0 : ℝ)) (fun _ => (1 : ℝ)) =
      phaseBoxUnitCube k := by
    ext x
    simp [phaseBoxUnitCube, Set.mem_Icc, Pi.le_def, forall_and]
  have hcubeAe : phaseBoxUnitIoc k =ᵐ[volume] phaseBoxUnitCube k := by
    simpa [phaseBoxUnitIoc, volume_pi, hcubeIcc] using
      (Measure.univ_pi_Ioc_ae_eq_Icc
        (μ := fun _ : Fin k => (volume : Measure ℝ))
        (f := fun _ : Fin k => (0 : ℝ)) (g := fun _ => (1 : ℝ)))
  have hmuCube : volume.restrict (phaseBoxUnitIoc k) =
      volume.restrict (phaseBoxUnitCube k) :=
    Measure.restrict_congr_set hcubeAe
  have hsource : volume.restrict (phaseBoxUnitIoc k) =
      Measure.pi (fun _ : Fin k => volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    rw [phaseBoxUnitIoc, volume_pi, Measure.restrict_pi_pi]
  have hclosedMoment :
      ∫ a in phaseBoxUnitCube k, F a ≤
        ((2 * Real.pi : ℝ) ^ k) ^ (2 * s) * (vinogradovCount s k M : ℝ) := by
    let cubeSet : Set (Fin k → ℝ) := {a | ∀ j, 0 ≤ a j ∧ a j ≤ 1}
    have hcubeSetEq : cubeSet = phaseBoxUnitCube k := by
      ext a
      simp [cubeSet, phaseBoxUnitCube, Pi.le_def, forall_and]
    have hcubeSetMeas : MeasurableSet cubeSet := by
      rw [hcubeSetEq, hcubeEq]
      exact MeasurableSet.univ_pi fun _ => measurableSet_Icc
    have htorus := phase_torus_moment (s := s) (k := k) (M := M)
      (D := (2 * Real.pi : ℝ) ^ k) (by positivity) coeff hcoeff
    rw [integral_indicator hcubeSetMeas, hcubeSetEq] at htorus
    simpa [F, phaseWeightedWeylSum] using htorus
  have hFintClosed : Integrable F (volume.restrict (phaseBoxUnitCube k)) :=
    hFcont.continuousOn.integrableOn_compact hcubeCompact
  have hFintOpen : Integrable F (volume.restrict (phaseBoxUnitIoc k)) := by
    rw [hmuCube]
    exact hFintClosed
  let boxMeasure (r : PhaseBoxIndex k M) : Measure (Fin k → ℝ) :=
    volume.restrict (phaseBoxIoc r)
  have hboxMeas (r : PhaseBoxIndex k M) : MeasurableSet (phaseBoxIoc r) := by
    rw [phaseBoxIoc]
    exact MeasurableSet.univ_pi fun _ => measurableSet_Ioc
  have hdisjoint : Pairwise (fun r s : PhaseBoxIndex k M =>
      Disjoint (phaseBoxIoc r) (phaseBoxIoc s)) := by
    intro r s hrs
    exact phase_box_ioc_disjoint hM r s hrs
  have hsumMeasure : Measure.sum boxMeasure =
      volume.restrict (phaseBoxUnitIoc k) := by
    rw [← Measure.restrict_iUnion hdisjoint hboxMeas]
    rw [phase_box_ioc_cover hM]
  have hFintSum : Integrable F (Measure.sum boxMeasure) := by
    rw [hsumMeasure]
    exact hFintOpen
  have htarget (r : PhaseBoxIndex k M) :
      Measure.pi (fun j : Fin k => volume.restrict
        (Set.Ioc (((r j).val : ℝ) / (M : ℝ) ^ (j.val + 1))
          ((((r j).val + 1 : ℕ) : ℝ) / (M : ℝ) ^ (j.val + 1)))) =
      volume.restrict (phaseBoxIoc r) := by
    rw [phaseBoxIoc, volume_pi, Measure.restrict_pi_pi]
  have hboxMap (r : PhaseBoxIndex k M) :
      Measure.map (fun x : Fin k → ℝ => phaseBoxPoint r x)
        (Measure.pi (fun _ : Fin k => volume.restrict (Set.Ioc (0 : ℝ) 1))) =
      ENNReal.ofReal ((M : ℝ) ^ phaseBoxExponent k) • boxMeasure r := by
    rw [phase_box_map_cube k M hM r, htarget]
  have hboxComp (r : PhaseBoxIndex k M) :
      (∫ x, F (phaseBoxPoint r x) ∂(Measure.pi
          (fun _ : Fin k => volume.restrict (Set.Ioc (0 : ℝ) 1)))) =
        ((M : ℝ) ^ phaseBoxExponent k) *
          (∫ x, F x ∂boxMeasure r) := by
    have hmap := MeasureTheory.integral_map
      (by
        have hcontinuous : Continuous (fun x : Fin k → ℝ => phaseBoxPoint r x) := by
          unfold phaseBoxPoint
          fun_prop
        exact hcontinuous.measurable.aemeasurable
          (μ := Measure.pi (fun _ : Fin k => volume.restrict (Set.Ioc (0 : ℝ) 1))))
      (hFcont.aestronglyMeasurable)
    have hpow : 0 ≤ (M : ℝ) ^ phaseBoxExponent k := by positivity
    calc
      _ = ∫ x, F x ∂Measure.map (fun x : Fin k → ℝ => phaseBoxPoint r x)
          (Measure.pi (fun _ : Fin k => volume.restrict (Set.Ioc (0 : ℝ) 1))) := hmap.symm
      _ = ∫ x, F x ∂(ENNReal.ofReal ((M : ℝ) ^ phaseBoxExponent k) • boxMeasure r) := by
        rw [hboxMap]
      _ = ((M : ℝ) ^ phaseBoxExponent k) * (∫ x, F x ∂boxMeasure r) := by
        rw [MeasureTheory.integral_smul_measure, ENNReal.toReal_ofReal hpow, smul_eq_mul]
  have hboxInt (r : PhaseBoxIndex k M) :
      (∫ x in phaseBoxUnitCube k,
        ‖phaseBoxMixedWeylSum r e x‖ ^ (2 * s)) =
      ((M : ℝ) ^ phaseBoxExponent k) * (∫ x, F x ∂boxMeasure r) := by
    calc
      _ = ∫ x in phaseBoxUnitIoc k,
          ‖phaseBoxMixedWeylSum r e x‖ ^ (2 * s) :=
        setIntegral_congr_set hcubeAe.symm
      _ = ∫ x, F (phaseBoxPoint r x) ∂(Measure.pi
          (fun _ : Fin k => volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
        rw [hsource]
        simp [F, coeff, phaseBoxMixedWeylSum, phaseWeightedWeylSum]
      _ = _ := hboxComp r
  have hsumInt :
      ∑ r : PhaseBoxIndex k M, ∫ x, F x ∂boxMeasure r =
        ∫ x, F x ∂(volume.restrict (phaseBoxUnitIoc k)) := by
    calc
      _ = ∫ x, F x ∂Measure.sum boxMeasure := by
        calc
          _ = ∑' r, ∫ x, F x ∂boxMeasure r := by simp
          _ = ∫ x, F x ∂Measure.sum boxMeasure := (integral_sum_measure hFintSum).symm
      _ = _ := by rw [hsumMeasure]
  calc
    _ = ((M : ℝ) ^ phaseBoxExponent k) *
        (∑ r : PhaseBoxIndex k M, ∫ x, F x ∂boxMeasure r) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      exact hboxInt r
    _ = ((M : ℝ) ^ phaseBoxExponent k) *
        (∫ x in phaseBoxUnitCube k, F x) := by
      rw [hsumInt, hmuCube]
    _ ≤ ((M : ℝ) ^ phaseBoxExponent k) *
        (((2 * Real.pi : ℝ) ^ k) ^ (2 * s) * (vinogradovCount s k M : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hclosedMoment (by positivity)
    _ = (M : ℝ) ^ phaseBoxExponent k *
        (2 * Real.pi : ℝ) ^ (2 * s * k) * (vinogradovCount s k M : ℝ) := by
      rw [← pow_mul]
      rw [Nat.mul_comm k (2 * s)]
      ring

/-
The former single-box moment and supremum contracts were false: summing them
individually loses a factor `M^K`. The aggregate contract above is the one
needed to prove `phase_box_suprema`.
-/

/-- Sum of the suprema over all closed coefficient boxes. -/
theorem phase_box_suprema (s k M : ℕ) (hM : 0 < M) :
    ∑ r : PhaseBoxIndex k M,
      (sSup {z : ℝ | ∃ a : Fin k → ℝ, a ∈ phaseClosedBox r ∧
        z = ‖phaseWeylSum k M a‖}) ^ (2 * s) ≤
      (4 * Real.pi : ℝ) ^ (2 * s * k) *
        (M : ℝ) ^ phaseBoxExponent k * (vinogradovCount s k M : ℝ) := by
  classical
  let cube : Set (Fin k → ℝ) := phaseBoxUnitCube k
  have hcubeEq : cube = Set.univ.pi (fun _ : Fin k => Set.Icc (0 : ℝ) 1) := by
    ext x
    simp [cube, phaseBoxUnitCube, Set.mem_pi, Pi.le_def, forall_and]
  have hcubeCompact : IsCompact cube := by
    rw [hcubeEq]
    exact isCompact_univ_pi fun _ => isCompact_Icc
  have hcubeMeas : MeasurableSet cube := by
    rw [hcubeEq]
    exact MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hcubeVol : volume cube = 1 := by
    rw [hcubeEq, volume_pi, Measure.pi_pi]
    simp
  let μ : Measure (Fin k → ℝ) := volume.restrict cube
  have hμprob : IsProbabilityMeasure μ := by
    rw [isProbabilityMeasure_iff]
    simp [μ, hcubeVol]
  letI : IsProbabilityMeasure μ := hμprob
  let n : ℕ := 2 * s
  have hindexCard : Fintype.card (PhaseBoxIndex k M) = M ^ phaseBoxExponent k := by
    simp [PhaseBoxIndex, phaseBoxExponent, Fintype.card_pi]
    rw [← Finset.prod_pow_eq_pow_sum]
  have hsubsetCard : Fintype.card (Finset (Fin k)) = 2 ^ k := by
    simp [Fintype.card_finset]
  by_cases hs : 0 < s
  · have hn : 1 ≤ n := by dsimp [n]; omega
    let boxIntegral (r : PhaseBoxIndex k M) (e : Finset (Fin k)) : ℝ :=
      ∫ x in cube, ‖phaseBoxMixedWeylSum r e x‖
    have hboxIntegralNonneg (r : PhaseBoxIndex k M) (e : Finset (Fin k)) :
        0 ≤ boxIntegral r e := by
      dsimp [boxIntegral]
      exact setIntegral_nonneg hcubeMeas fun x hx => norm_nonneg _
    have hboxIntegralPow (r : PhaseBoxIndex k M) (e : Finset (Fin k)) :
        (boxIntegral r e) ^ n ≤
          ∫ x in cube, ‖phaseBoxMixedWeylSum r e x‖ ^ n := by
      dsimp [boxIntegral]
      have hfcont : Continuous (fun x : Fin k → ℝ =>
          ‖phaseBoxMixedWeylSum r e x‖) := by
        exact (phase_box_mixed_continuous k M r e).norm
      have hfi : Integrable (fun x : Fin k → ℝ =>
          ‖phaseBoxMixedWeylSum r e x‖) μ := by
        exact (hfcont.continuousOn.integrableOn_compact hcubeCompact).integrable
      have hfiPow : Integrable (fun x : Fin k → ℝ =>
          ‖phaseBoxMixedWeylSum r e x‖ ^ n) μ := by
        exact ((hfcont.pow n).continuousOn.integrableOn_compact hcubeCompact).integrable
      have hnonneg : ∀ x : Fin k → ℝ,
          0 ≤ ‖phaseBoxMixedWeylSum r e x‖ := fun _ => norm_nonneg _
      have hJensen := (convexOn_pow n).map_integral_le
        ((continuous_id.pow n).continuousOn) isClosed_Ici
        (ae_of_all μ fun x => hnonneg x) hfi
        (by
          convert hfiPow using 1 <;> rfl)
      simpa [μ, cube, Function.comp_apply] using hJensen
    have hboxCompact (r : PhaseBoxIndex k M) : IsCompact (phaseClosedBox r) := by
      have hboxEq : phaseClosedBox r = Set.univ.pi (fun j : Fin k =>
          Set.Icc (((r j).val : ℝ) / (M : ℝ) ^ (j.val + 1))
            ((((r j).val + 1 : ℕ) : ℝ) / (M : ℝ) ^ (j.val + 1))) := by
        ext a
        simp [phaseClosedBox, Set.mem_pi, Set.mem_Icc, Pi.le_def, forall_and]
      rw [hboxEq]
      exact isCompact_univ_pi fun j => isCompact_Icc
    have hboxNonempty (r : PhaseBoxIndex k M) : (phaseClosedBox r).Nonempty := by
      refine ⟨fun j => ((r j).val : ℝ) / (M : ℝ) ^ (j.val + 1), ?_⟩
      intro j
      have hd : 0 < (M : ℝ) ^ (j.val + 1) := by positivity
      constructor
      · exact le_rfl
      · apply (div_le_div_iff_of_pos_right hd).2
        norm_num
    have hvalueSet (r : PhaseBoxIndex k M) :
        {z : ℝ | ∃ a : Fin k → ℝ, a ∈ phaseClosedBox r ∧
          z = ‖phaseWeylSum k M a‖} =
          (fun a : Fin k → ℝ => ‖phaseWeylSum k M a‖) '' phaseClosedBox r := by
      ext z
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨a, ha, rfl⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨a, ha, rfl⟩
    have hsup (r : PhaseBoxIndex k M) :
        ∃ a ∈ phaseClosedBox r,
          sSup {z : ℝ | ∃ a : Fin k → ℝ, a ∈ phaseClosedBox r ∧
            z = ‖phaseWeylSum k M a‖} = ‖phaseWeylSum k M a‖ := by
      rw [hvalueSet]
      exact (hboxCompact r).exists_sSup_image_eq (hboxNonempty r) (by
        have hc : Continuous (fun a : Fin k → ℝ => ‖phaseWeylSum k M a‖) := by
          dsimp [phaseWeylSum, additiveCharacter]
          fun_prop
        exact hc.continuousOn)
    have hboxSobolev (r : PhaseBoxIndex k M) :
        (sSup {z : ℝ | ∃ a : Fin k → ℝ, a ∈ phaseClosedBox r ∧
          z = ‖phaseWeylSum k M a‖}) ^ n ≤
          (Fintype.card (Finset (Fin k)) : ℝ) ^ (n - 1) *
            ∑ e : Finset (Fin k), (boxIntegral r e) ^ n := by
      obtain ⟨a, ha, hsupEq⟩ := hsup r
      let x : Fin k → ℝ := fun j =>
        (M : ℝ) ^ (j.val + 1) * a j - (r j).val
      have hx : x ∈ phaseBoxUnitCube k := by
        rw [phase_box_rescaled_mem r a hM] at ha
        simpa [x, phaseBoxUnitCube] using ha
      have hsob := phase_box_sobolev k M hM r x hx
      have hbase : ‖phaseWeylSum k M a‖ ≤
          ∑ e : Finset (Fin k), boxIntegral r e := by
        rw [phase_box_rescaled_eq r a hM ha]
        simpa [x, boxIntegral, phaseBoxRescaledSum, phaseBoxMixedWeylSum,
          phaseWeylSum] using hsob
      have hsumNonneg : 0 ≤ ∑ e : Finset (Fin k), boxIntegral r e :=
        Finset.sum_nonneg fun e _ => hboxIntegralNonneg r e
      have hpowBase :
          (sSup {z : ℝ | ∃ a : Fin k → ℝ, a ∈ phaseClosedBox r ∧
            z = ‖phaseWeylSum k M a‖}) ^ n ≤
            (∑ e : Finset (Fin k), boxIntegral r e) ^ n := by
        rw [hsupEq]
        exact pow_le_pow_left₀ (norm_nonneg _) hbase n
      have hsumPow := pow_sum_le_card_mul_sum_pow
        (s := (Finset.univ : Finset (Finset (Fin k))))
        (f := boxIntegral r)
        (fun e he => hboxIntegralNonneg r e) (n - 1)
      have hnsub : (n - 1) + 1 = n := by omega
      rw [hnsub] at hsumPow
      exact hpowBase.trans (by simpa [n] using hsumPow)
    have haggregate (e : Finset (Fin k)) :
        ∑ r : PhaseBoxIndex k M, (boxIntegral r e) ^ n ≤
          (M : ℝ) ^ phaseBoxExponent k *
            (2 * Real.pi : ℝ) ^ (n * k) * (vinogradovCount s k M : ℝ) := by
      calc
        _ ≤ ∑ r : PhaseBoxIndex k M,
            ∫ x in cube, ‖phaseBoxMixedWeylSum r e x‖ ^ n :=
          Finset.sum_le_sum fun r _ => hboxIntegralPow r e
        _ = ∑ r : PhaseBoxIndex k M,
            ∫ x in phaseBoxUnitCube k,
              ‖phaseBoxMixedWeylSum r e x‖ ^ (2 * s) := by
          simp [cube, n]
        _ ≤ _ := by
          simpa [n] using phase_box_summed_mixed_moment s k M hM e
    have hsumAggregate :
        ∑ r : PhaseBoxIndex k M,
          ∑ e : Finset (Fin k), (boxIntegral r e) ^ n ≤
          (Fintype.card (Finset (Fin k)) : ℝ) *
            ((M : ℝ) ^ phaseBoxExponent k *
              (2 * Real.pi : ℝ) ^ (n * k) * (vinogradovCount s k M : ℝ)) := by
      rw [Finset.sum_comm]
      calc
        _ ≤ ∑ e : Finset (Fin k),
            (M : ℝ) ^ phaseBoxExponent k *
              (2 * Real.pi : ℝ) ^ (n * k) * (vinogradovCount s k M : ℝ) :=
          Finset.sum_le_sum fun e _ => haggregate e
        _ = _ := by simp
    calc
      _ ≤ ∑ r : PhaseBoxIndex k M,
            (Fintype.card (Finset (Fin k)) : ℝ) ^ (n - 1) *
              ∑ e : Finset (Fin k), (boxIntegral r e) ^ n :=
        Finset.sum_le_sum fun r _ => hboxSobolev r
      _ = (Fintype.card (Finset (Fin k)) : ℝ) ^ (n - 1) *
          ∑ r : PhaseBoxIndex k M,
            ∑ e : Finset (Fin k), (boxIntegral r e) ^ n := by
        rw [Finset.mul_sum]
      _ ≤ (Fintype.card (Finset (Fin k)) : ℝ) ^ (n - 1) *
          ((Fintype.card (Finset (Fin k)) : ℝ) *
            ((M : ℝ) ^ phaseBoxExponent k *
              (2 * Real.pi : ℝ) ^ (n * k) * (vinogradovCount s k M : ℝ))) :=
        mul_le_mul_of_nonneg_left hsumAggregate (by positivity)
      _ = (4 * Real.pi : ℝ) ^ (n * k) *
          (M : ℝ) ^ phaseBoxExponent k * (vinogradovCount s k M : ℝ) := by
        have hconst :
            (2 : ℝ) ^ (k * (n - 1)) * (2 : ℝ) ^ k *
                (2 * Real.pi : ℝ) ^ (n * k) =
              (4 * Real.pi : ℝ) ^ (n * k) := by
          calc
            _ = (2 : ℝ) ^ (k * (n - 1) + k) *
                (2 * Real.pi : ℝ) ^ (n * k) := by rw [← pow_add]
            _ = (2 : ℝ) ^ (n * k) *
                (2 * Real.pi : ℝ) ^ (n * k) := by
              rw [show k * (n - 1) + k = n * k by
                calc
                  k * (n - 1) + k = k * ((n - 1) + 1) := by rw [Nat.mul_add, Nat.mul_one]
                  _ = k * n := by rw [Nat.sub_add_cancel hn]
                  _ = n * k := Nat.mul_comm _ _]
            _ = ((2 : ℝ) * (2 * Real.pi : ℝ)) ^ (n * k) :=
              (mul_pow _ _ _).symm
            _ = _ := by congr 1 <;> ring
        have hpowCard :
            ((Fintype.card (Finset (Fin k)) : ℝ) ^ (n - 1)) *
                (Fintype.card (Finset (Fin k)) : ℝ) =
              (2 : ℝ) ^ (k * (n - 1)) * (2 : ℝ) ^ k := by
          rw [hsubsetCard]
          simp [← pow_mul]
        calc
          _ = (((Fintype.card (Finset (Fin k)) : ℝ) ^ (n - 1) *
                (Fintype.card (Finset (Fin k)) : ℝ)) *
              (2 * Real.pi : ℝ) ^ (n * k)) *
              ((M : ℝ) ^ phaseBoxExponent k * (vinogradovCount s k M : ℝ)) := by ring
          _ = ((2 : ℝ) ^ (k * (n - 1)) * (2 : ℝ) ^ k *
                (2 * Real.pi : ℝ) ^ (n * k)) *
              ((M : ℝ) ^ phaseBoxExponent k * (vinogradovCount s k M : ℝ)) := by
            rw [hpowCard]
          _ = _ := by rw [hconst]; ring
  · have hs0 : s = 0 := Nat.eq_zero_of_not_pos hs
    subst s
    have hcount : vinogradovCount 0 k M = 1 := by
      simp [vinogradovCount, boundedTuples]
    simpa [n, hcount, hindexCard]

/-- The common target window restricted to a given frequency regime. -/
def phaseWindowBound (freq : ℝ → ℝ → Prop) (C C₀ x₀ : ℝ) : Prop :=
  ∀ x : ℝ, x₀ ≤ x →
    let L := Real.log x
    let T := Real.log L
    ∀ N' : ℝ, Real.exp (L / T ^ 2) ≤ N' → N' ≤ 2 * Real.rpow x 5 →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.rpow L C →
        ∀ a : ZMod q, ∀ v : ℝ,
          Real.exp (L / (2 * T ^ 2)) ≤ |v| → |v| ≤ 4 * Real.rpow x 3 →
            freq (N' / (q : ℝ)) v →
              ∀ N₁ N₂ : ℝ, N' ≤ N₁ → N₂ ≤ 2 * N' →
                ‖residuePhaseSum N' q a v
                    {n : ℕ | N₁ ≤ (n : ℝ) ∧ (n : ℝ) ≤ N₂}‖ ≤
                  C₀ * (N' / q) * Real.exp (-L / Real.rpow T 11)

def phaseLogPhaseStatement : Prop :=
  ∃ C₃ : ℝ, 0 < C₃ ∧
    ∀ C : ℝ, 0 < C →
      ∃ C₀ x₀ : ℝ, 0 < C₀ ∧ 2 < x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          let L := Real.log x
          let T := Real.log L
          ∀ N' : ℝ, Real.exp (L / T ^ 2) ≤ N' → N' ≤ 2 * Real.rpow x 5 →
            ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.rpow L C →
              ∀ a : ZMod q, ∀ v : ℝ,
                Real.exp (L / (2 * T ^ 2)) ≤ |v| → |v| ≤ 4 * Real.rpow x 3 →
                  ∀ N₁ N₂ : ℝ, N' ≤ N₁ → N₂ ≤ 2 * N' →
                    ‖residuePhaseSum N' q a v
                        {n : ℕ | N₁ ≤ (n : ℝ) ∧ (n : ℝ) ≤ N₂}‖ ≤
                      C₀ * (N' / q) * Real.exp (-L / Real.rpow T C₃)

/-- Combine the easy and growing-degree frequency ranges. -/
theorem phase_from_regimes (hMV : phaseMeanValueInput)
    (hLow : ∀ C : ℝ, 0 < C →
      ∃ C₀ x₀ : ℝ, 0 < C₀ ∧ 2 < x₀ ∧
        phaseWindowBound (fun H v => |v| < Real.rpow H (4 / 5)) C C₀ x₀)
    (hHigh : phaseMeanValueInput → ∀ C : ℝ, 0 < C →
      ∃ C₀ x₀ : ℝ, 0 < C₀ ∧ 2 < x₀ ∧
        phaseWindowBound (fun H v => Real.rpow H (4 / 5) ≤ |v|) C C₀ x₀) :
    phaseLogPhaseStatement := by
  classical
  unfold phaseLogPhaseStatement
  refine ⟨11, by norm_num, ?_⟩
  intro C hC
  obtain ⟨C₀L, x₀L, hC₀L, hx₀L, hLowC⟩ := hLow C hC
  obtain ⟨C₀H, x₀H, hC₀H, hx₀H, hHighC⟩ := hHigh hMV C hC
  refine ⟨max C₀L C₀H, max x₀L x₀H, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le hC₀L (le_max_left _ _)
  · exact lt_of_lt_of_le hx₀L (le_max_left _ _)
  · intro x hx
    dsimp only
    intro N' hNlo hNhi q hq hqC a v hvlo hvhi N₁ N₂ hN₁ hN₂
    have hxL : x₀L ≤ x := (le_max_left _ _).trans hx
    have hxH : x₀H ≤ x := (le_max_right _ _).trans hx
    let H := N' / (q : ℝ)
    by_cases hfreq : Real.rpow H (4 / 5) ≤ |v|
    · have hest := hHighC x hxH N' hNlo hNhi q hq hqC a v hvlo hvhi
        (by simpa [H] using hfreq) N₁ N₂ hN₁ hN₂
      have hqR : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
      have hNpos : 0 < N' := lt_of_lt_of_le (Real.exp_pos _) hNlo
      have hfac : 0 ≤ (N' / (q : ℝ)) * Real.exp
          (-Real.log x / Real.rpow (Real.log (Real.log x)) 11) :=
        mul_nonneg (div_nonneg hNpos.le hqR.le) (Real.exp_pos _).le
      calc
        _ ≤ C₀H * (N' / (q : ℝ)) * Real.exp
              (-Real.log x / Real.rpow (Real.log (Real.log x)) 11) := hest
        _ = C₀H * ((N' / (q : ℝ)) * Real.exp
              (-Real.log x / Real.rpow (Real.log (Real.log x)) 11)) := by ring
        _ ≤ max C₀L C₀H * ((N' / (q : ℝ)) * Real.exp
              (-Real.log x / Real.rpow (Real.log (Real.log x)) 11)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hfac
        _ = max C₀L C₀H * (N' / q) * Real.exp
              (-Real.log x / Real.rpow (Real.log (Real.log x)) 11) := by ring
    · have hfreq' : |v| < Real.rpow H (4 / 5) := lt_of_not_ge hfreq
      have hest := hLowC x hxL N' hNlo hNhi q hq hqC a v hvlo hvhi
        (by simpa [H] using hfreq') N₁ N₂ hN₁ hN₂
      have hqR : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
      have hNpos : 0 < N' := lt_of_lt_of_le (Real.exp_pos _) hNlo
      have hfac : 0 ≤ (N' / (q : ℝ)) * Real.exp
          (-Real.log x / Real.rpow (Real.log (Real.log x)) 11) :=
        mul_nonneg (div_nonneg hNpos.le hqR.le) (Real.exp_pos _).le
      calc
        _ ≤ C₀L * (N' / (q : ℝ)) * Real.exp
              (-Real.log x / Real.rpow (Real.log (Real.log x)) 11) := hest
        _ = C₀L * ((N' / (q : ℝ)) * Real.exp
              (-Real.log x / Real.rpow (Real.log (Real.log x)) 11)) := by ring
        _ ≤ max C₀L C₀H * ((N' / (q : ℝ)) * Real.exp
              (-Real.log x / Real.rpow (Real.log (Real.log x)) 11)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hfac
        _ = max C₀L C₀H * (N' / q) * Real.exp
              (-Real.log x / Real.rpow (Real.log (Real.log x)) 11) := by ring

/-- Low frequencies use the first-derivative estimate and quotient reindexing. -/
theorem phase_low_regime_bound :
    ∀ C : ℝ, 0 < C →
      ∃ C₀ x₀ : ℝ, 0 < C₀ ∧ 2 < x₀ ∧
        phaseWindowBound (fun H v => |v| < Real.rpow H (4 / 5)) C C₀ x₀ := by
  sorry

private theorem phase_boxExponent_eq_half (k : ℕ) :
    (phaseBoxExponent k : ℝ) = (k : ℝ) * ((k : ℝ) + 1) / 2 := by
  induction k with
  | zero => simp [phaseBoxExponent]
  | succ k ih =>
      have hstep : phaseBoxExponent (k + 1) = phaseBoxExponent k + (k + 1) := by
        simp [phaseBoxExponent, Fin.sum_univ_castSucc]
      rw [hstep]
      push_cast
      rw [ih]
      ring

private theorem phase_high_box_cover {H y θ : ℝ} {k M : ℕ}
    (B : Finset ℕ) (hM : 0 < M) :
    ∀ b ∈ B, ∃ r : PhaseBoxIndex k M,
      b ∈ phaseBoxMembers (H := H) (y := y) (θ := θ) B r := by
  classical
  intro b hb
  let r : PhaseBoxIndex k M := fun j =>
    ⟨Nat.floor ((M : ℝ) ^ (j.val + 1) *
        Int.fract (phaseAlphaVector H y θ b k j)), by
      have hMpos : 0 < (M : ℝ) := by exact_mod_cast hM
      have ht : 0 < (M : ℝ) ^ (j.val + 1) := by positivity
      have hfrac0 : 0 ≤ Int.fract (phaseAlphaVector H y θ b k j) :=
        Int.fract_nonneg _
      have hfrac1 : Int.fract (phaseAlphaVector H y θ b k j) < 1 :=
        Int.fract_lt_one _
      have hx0 : 0 ≤ (M : ℝ) ^ (j.val + 1) *
          Int.fract (phaseAlphaVector H y θ b k j) :=
        mul_nonneg (le_of_lt ht) hfrac0
      have hxlt : (M : ℝ) ^ (j.val + 1) *
          Int.fract (phaseAlphaVector H y θ b k j) <
          (M : ℝ) ^ (j.val + 1) := by
        calc
          _ < (M : ℝ) ^ (j.val + 1) * 1 := mul_lt_mul_of_pos_left hfrac1 ht
          _ = _ := by ring
      have hfloor := Nat.floor_le hx0
      exact_mod_cast lt_of_le_of_lt hfloor hxlt⟩
  refine ⟨r, ?_⟩
  change b ∈ B.filter (fun n => phaseInBox r (phaseAlphaVector H y θ n k))
  rw [Finset.mem_filter]
  refine ⟨hb, ?_⟩
  intro j
  dsimp [r]
  let t : ℝ := (M : ℝ) ^ (j.val + 1)
  let x : ℝ := t * Int.fract (phaseAlphaVector H y θ b k j)
  have ht : 0 < t := by dsimp [t]; positivity
  have hx0 : 0 ≤ x := by
    dsimp [x]
    exact mul_nonneg (le_of_lt ht) (Int.fract_nonneg _)
  have hfloor : (Nat.floor x : ℝ) ≤ x := Nat.floor_le hx0
  have hceil : x < (Nat.floor x : ℝ) + 1 := Nat.lt_floor_add_one x
  constructor
  · apply (div_le_iff₀ ht).2
    simpa [x, t, mul_comm] using hfloor
  · apply (lt_div_iff₀ ht).2
    simpa [x, t, mul_comm] using hceil

private theorem phase_high_box_value_le_sup {k M : ℕ}
    (r : PhaseBoxIndex k M) (a : Fin k → ℝ) (hM : 0 < M)
    (ha : a ∈ phaseClosedBox r) :
    ‖phaseWeylSum k M a‖ ≤
      sSup {z : ℝ | ∃ a : Fin k → ℝ, a ∈ phaseClosedBox r ∧
        z = ‖phaseWeylSum k M a‖} := by
  sorry

private theorem phase_high_translate_box_sup {H y θ V : ℝ} {k M : ℕ}
    (r : PhaseBoxIndex k M) (b : ℕ) (hM : 0 < M)
    (hV : V = Real.rpow H y)
    (hb : phaseInBox r (phaseAlphaVector H y θ b k)) :
    ‖phasePolynomialSum V θ b k M‖ ≤
      sSup {z : ℝ | ∃ a : Fin k → ℝ, a ∈ phaseClosedBox r ∧
        z = ‖phaseWeylSum k M a‖} := by
  sorry

private theorem phase_high_polynomial_interval_bound
    {H y θ V : ℝ} {l u k M s : ℕ} {C₁ C₂ : ℝ}
    (hH : 16 ≤ H) (hy : 4 / 5 ≤ y) (hV : V = Real.rpow H y)
    (hklo : 4 * y + 8 ≤ k) (hkhi : (k : ℝ) ≤ 4 * y + 9)
    (hM : 0 < M)
    (hMlo : Real.rpow H (3 / 4) / 2 ≤ (M : ℝ))
    (hMhi : (M : ℝ) ≤ Real.rpow H (3 / 4))
    (hcard : ((Finset.Icc l u).card : ℝ) ≤ 2 * H)
    (hinterval : ∀ b ∈ Finset.Icc l u,
      H ≤ (b : ℝ) + θ ∧ (b : ℝ) + θ ≤ 2 * H)
    (hks : k ≤ s)
    (hcount : (vinogradovCount s k M : ℝ) ≤
      Real.exp (C₁ * Real.rpow (k : ℝ) C₂) *
        Real.rpow (M : ℝ)
          (2 * (s : ℝ) - (phaseBoxExponent k : ℝ) + 1 / 100 : ℝ)) :
    (1 / (M : ℝ)) *
      ∑ b ∈ Finset.Icc l u, ‖phasePolynomialSum V θ b k M‖ ≤
      2 * H * Real.exp
        ((10 * (k : ℝ) + 2 * (s : ℝ) * (k : ℝ) * Real.log (4 * Real.pi) +
          C₁ * Real.rpow (k : ℝ) C₂ - (1 / 5) * Real.log H +
          (1 / 100) * Real.log (M : ℝ)) / (2 * (s : ℝ))) := by
  classical
  let B : Finset ℕ := Finset.Icc l u
  let p : ℕ := 2 * s
  let pR : ℝ := (p : ℝ)
  let K : ℝ := (phaseBoxExponent k : ℝ)
  let occ : ℝ := Real.exp (10 * (k : ℝ)) * Real.rpow H (4 / 5 : ℝ)
  let boxSup (r : PhaseBoxIndex k M) : ℝ :=
    sSup {z : ℝ | ∃ a : Fin k → ℝ, a ∈ phaseClosedBox r ∧
      z = ‖phaseWeylSum k M a‖}
  have hHpos : 0 < H := by linarith
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast hM
  have hk2 : 2 ≤ k := by
    have hkR : (2 : ℝ) ≤ (k : ℝ) := by nlinarith [hklo, hy]
    exact_mod_cast hkR
  have hp1 : 1 ≤ p := by dsimp [p]; omega
  have hpR : pR = 2 * (s : ℝ) := by dsimp [pR, p]; norm_cast
  have hK : K = (k : ℝ) * ((k : ℝ) + 1) / 2 := by
    simpa [K] using phase_boxExponent_eq_half k
  have hboxPowNonneg (r : PhaseBoxIndex k M) : 0 ≤ boxSup r ^ p := by
    have hpEven : p = s * 2 := by dsimp [p]; omega
    rw [hpEven, pow_mul]
    exact sq_nonneg (boxSup r ^ s)
  have hcoverMoment :
      ∑ b ∈ B, ‖phasePolynomialSum V θ b k M‖ ^ p ≤
        occ * ∑ r : PhaseBoxIndex k M, boxSup r ^ p := by
    calc
      _ ≤ ∑ b ∈ B, ∑ r : PhaseBoxIndex k M,
            if b ∈ phaseBoxMembers (H := H) (y := y) (θ := θ) B r then
              boxSup r ^ p else 0 := by
        apply Finset.sum_le_sum
        intro b hb
        obtain ⟨r, hr⟩ := phase_high_box_cover B hM b hb
        have hrMem : phaseInBox r (phaseAlphaVector H y θ b k) := by
          change b ∈ B.filter (fun n => phaseInBox r (phaseAlphaVector H y θ n k)) at hr
          exact (Finset.mem_filter.mp hr).2
        have htranslate := phase_high_translate_box_sup r b hM hV hrMem
        have hsingle : boxSup r ^ p ≤
            ∑ r' : PhaseBoxIndex k M,
              if b ∈ phaseBoxMembers (H := H) (y := y) (θ := θ) B r' then
                boxSup r' ^ p else 0 := by
          calc
            _ = if b ∈ phaseBoxMembers (H := H) (y := y) (θ := θ) B r then
                  boxSup r ^ p else 0 := by simp [hr]
            _ ≤ _ := Finset.single_le_sum
              (f := fun r' : PhaseBoxIndex k M =>
                if b ∈ phaseBoxMembers (H := H) (y := y) (θ := θ) B r' then
                  boxSup r' ^ p else 0)
              (fun r' _ => by
                by_cases hmem : b ∈ phaseBoxMembers (H := H) (y := y) (θ := θ) B r'
                · simp [hmem, hboxPowNonneg]
                · simp [hmem])
              (Finset.mem_univ r)
        have hpow := pow_le_pow_left₀ (norm_nonneg _) htranslate p
        exact hpow.trans (by simpa [hr] using hsingle)
      _ = ∑ r : PhaseBoxIndex k M,
            ∑ b ∈ B,
              if b ∈ phaseBoxMembers (H := H) (y := y) (θ := θ) B r then
                boxSup r ^ p else 0 := by rw [Finset.sum_comm]
      _ = ∑ r : PhaseBoxIndex k M,
            ((phaseBoxMembers (H := H) (y := y) (θ := θ) B r).card : ℝ) *
              boxSup r ^ p := by
        apply Finset.sum_congr rfl
        intro r hr
        have hsub : phaseBoxMembers (H := H) (y := y) (θ := θ) B r ⊆ B := by
          intro b hb
          change b ∈ B.filter (fun n => phaseInBox r (phaseAlphaVector H y θ n k)) at hb
          exact (Finset.mem_filter.mp hb).1
        have hfilter : B.filter
            (fun b => b ∈ phaseBoxMembers (H := H) (y := y) (θ := θ) B r) =
              phaseBoxMembers (H := H) (y := y) (θ := θ) B r := by
          ext b
          constructor
          · intro hb
            exact (Finset.mem_filter.mp hb).2
          · intro hb
            exact Finset.mem_filter.mpr ⟨hsub hb, hb⟩
        rw [← Finset.sum_filter, hfilter]
        simp
      _ ≤ ∑ r : PhaseBoxIndex k M, occ * boxSup r ^ p := by
        apply Finset.sum_le_sum
        intro r hr
        have hocc := phase_box_occupancy B hH hy hklo hkhi hM hMlo hMhi
          (fun b hb => hinterval b (by simpa [B] using hb)) r
        exact mul_le_mul_of_nonneg_right hocc (hboxPowNonneg r)
      _ = occ * ∑ r : PhaseBoxIndex k M, boxSup r ^ p := by
        rw [← Finset.mul_sum]
  have hsupMoment :
      ∑ r : PhaseBoxIndex k M, boxSup r ^ p ≤
        (4 * Real.pi : ℝ) ^ (2 * s * k) *
          (M : ℝ) ^ phaseBoxExponent k * (vinogradovCount s k M : ℝ) := by
    simpa [boxSup, p] using phase_box_suprema s k M hM
  have hsumPow :
      (∑ b ∈ B, ‖phasePolynomialSum V θ b k M‖) ^ p ≤
        (B.card : ℝ) ^ (p - 1) *
          ∑ b ∈ B, ‖phasePolynomialSum V θ b k M‖ ^ p := by
    have h := pow_sum_le_card_mul_sum_pow
      (s := B) (f := fun b => ‖phasePolynomialSum V θ b k M‖)
      (fun b hb => norm_nonneg _) (p - 1)
    have hpSub : (p - 1) + 1 = p := by omega
    rw [hpSub] at h
    exact h
  have hcardPow : (B.card : ℝ) ^ (p - 1) ≤ (2 * H) ^ (p - 1) :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by simpa [B] using hcard) _
  have hsumNonneg :
      0 ≤ ∑ b ∈ B, ‖phasePolynomialSum V θ b k M‖ ^ p :=
    Finset.sum_nonneg fun b hb => pow_nonneg (norm_nonneg _) _
  have hbaseMoment :
      (∑ b ∈ B, ‖phasePolynomialSum V θ b k M‖) ^ p ≤
        (2 * H) ^ (p - 1) *
          (occ * ((4 * Real.pi : ℝ) ^ (2 * s * k) *
            (M : ℝ) ^ phaseBoxExponent k * (vinogradovCount s k M : ℝ))) := by
    calc
      _ ≤ (B.card : ℝ) ^ (p - 1) *
          ∑ b ∈ B, ‖phasePolynomialSum V θ b k M‖ ^ p := hsumPow
      _ ≤ (2 * H) ^ (p - 1) *
          (occ * ∑ r : PhaseBoxIndex k M, boxSup r ^ p) := by
        exact mul_le_mul hcardPow hcoverMoment hsumNonneg (by positivity)
      _ ≤ (2 * H) ^ (p - 1) *
          (occ * ((4 * Real.pi : ℝ) ^ (2 * s * k) *
            (M : ℝ) ^ phaseBoxExponent k * (vinogradovCount s k M : ℝ))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsupMoment (by dsimp [occ]; positivity))
          (by positivity)
  have hscaledMoment :
      ((1 / (M : ℝ)) *
        ∑ b ∈ B, ‖phasePolynomialSum V θ b k M‖) ^ p ≤
          (1 / (M : ℝ)) ^ p *
            ((2 * H) ^ (p - 1) *
              (occ * ((4 * Real.pi : ℝ) ^ (2 * s * k) *
                (M : ℝ) ^ phaseBoxExponent k * (vinogradovCount s k M : ℝ)))) := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hbaseMoment (by positivity)
  have hcountScaled :
      ((1 / (M : ℝ)) *
        ∑ b ∈ B, ‖phasePolynomialSum V θ b k M‖) ^ p ≤
          (1 / (M : ℝ)) ^ p *
            ((2 * H) ^ (p - 1) *
              (occ * ((4 * Real.pi : ℝ) ^ (2 * s * k) *
                (M : ℝ) ^ phaseBoxExponent k *
                (Real.exp (C₁ * Real.rpow (k : ℝ) C₂) *
                  Real.rpow (M : ℝ)
                    (2 * (s : ℝ) - (phaseBoxExponent k : ℝ) + 1 / 100))))) := by
    calc
      _ ≤ (1 / (M : ℝ)) ^ p *
          ((2 * H) ^ (p - 1) *
            (occ * ((4 * Real.pi : ℝ) ^ (2 * s * k) *
              (M : ℝ) ^ phaseBoxExponent k * (vinogradovCount s k M : ℝ)))) :=
        hscaledMoment
      _ = ((1 / (M : ℝ)) ^ p * (2 * H) ^ (p - 1) * occ *
          (4 * Real.pi : ℝ) ^ (2 * s * k)) *
          ((M : ℝ) ^ phaseBoxExponent k * (vinogradovCount s k M : ℝ)) := by ring
      _ ≤ ((1 / (M : ℝ)) ^ p * (2 * H) ^ (p - 1) * occ *
          (4 * Real.pi : ℝ) ^ (2 * s * k)) *
          ((M : ℝ) ^ phaseBoxExponent k *
            (Real.exp (C₁ * Real.rpow (k : ℝ) C₂) *
              Real.rpow (M : ℝ)
                (2 * (s : ℝ) - (phaseBoxExponent k : ℝ) + 1 / 100))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hcount (by positivity))
          (by dsimp [occ]; positivity)
      _ = _ := by ring
  have hMprod :
      (1 / (M : ℝ)) ^ p * (M : ℝ) ^ phaseBoxExponent k *
        Real.rpow (M : ℝ)
          (2 * (s : ℝ) - (phaseBoxExponent k : ℝ) + 1 / 100) =
        Real.rpow (M : ℝ) (1 / 100 : ℝ) := by
    have hInvPow : (1 / (M : ℝ)) ^ p =
        Real.exp (-(pR) * Real.log (M : ℝ)) := by
      rw [← Real.rpow_natCast (1 / (M : ℝ)) p,
        Real.rpow_def_of_pos (by positivity) pR,
        Real.log_div (by norm_num) hMpos.ne']
      simp only [Real.log_one, zero_sub]
      congr 1
      ring
    have hKpow : (M : ℝ) ^ phaseBoxExponent k =
        Real.exp (K * Real.log (M : ℝ)) := by
      rw [← Real.rpow_natCast (M : ℝ) (phaseBoxExponent k),
        Real.rpow_def_of_pos hMpos (phaseBoxExponent k : ℝ)]
      congr 1
      dsimp [K]
      ring
    have hTail : Real.rpow (M : ℝ)
          (2 * (s : ℝ) - (phaseBoxExponent k : ℝ) + 1 / 100) =
        Real.exp ((pR - K + 1 / 100) * Real.log (M : ℝ)) := by
      calc
        _ = Real.exp (Real.log (M : ℝ) *
            (2 * (s : ℝ) - (phaseBoxExponent k : ℝ) + 1 / 100)) :=
          Real.rpow_def_of_pos hMpos _
        _ = _ := by
          congr 1
          rw [hpR]
          dsimp [K]
          ring
    have hHundred : Real.rpow (M : ℝ) (1 / 100 : ℝ) =
        Real.exp ((1 / 100 : ℝ) * Real.log (M : ℝ)) := by
      calc
        _ = Real.exp (Real.log (M : ℝ) * (1 / 100 : ℝ)) :=
          Real.rpow_def_of_pos hMpos _
        _ = _ := by congr 1 <;> ring
    rw [hInvPow, hKpow, hTail, hHundred]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp [K]
    ring
  have hPcast : (p : ℝ) = 2 * (s : ℝ) := by dsimp [p]; norm_cast
  have hPiExp : (4 * Real.pi : ℝ) ^ (2 * s * k) =
      Real.exp ((p : ℝ) * (k : ℝ) * Real.log (4 * Real.pi)) := by
    rw [← Real.rpow_natCast (4 * Real.pi : ℝ) (2 * s * k),
      Real.rpow_def_of_pos (by positivity) ((2 * s * k : ℕ) : ℝ)]
    congr 1
    push_cast
    rw [hPcast]
    ring
  have hMfrac : Real.rpow (M : ℝ) (1 / 100 : ℝ) =
      Real.exp ((1 / 100 : ℝ) * Real.log (M : ℝ)) := by
    calc
      _ = Real.exp (Real.log (M : ℝ) * (1 / 100 : ℝ)) :=
        Real.rpow_def_of_pos hMpos _
      _ = _ := by congr 1 <;> ring
  have hCoreExp :
      Real.exp (10 * (k : ℝ)) *
        (4 * Real.pi : ℝ) ^ (2 * s * k) *
        Real.exp (C₁ * Real.rpow (k : ℝ) C₂) *
        Real.rpow (M : ℝ) (1 / 100 : ℝ) =
      Real.exp (10 * (k : ℝ) + (p : ℝ) * (k : ℝ) * Real.log (4 * Real.pi) +
        C₁ * Real.rpow (k : ℝ) C₂ + (1 / 100) * Real.log (M : ℝ)) := by
    rw [hPiExp, hMfrac]
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  have hHratio :
      Real.rpow H (4 / 5 : ℝ) ≤
        2 * H * Real.exp (-(1 / 5) * Real.log H) := by
    have hExpSub : Real.exp (Real.log H) *
        Real.exp (-(1 / 5) * Real.log H) =
        Real.exp ((4 / 5 : ℝ) * Real.log H) := by
      calc
        _ = Real.exp (Real.log H + (-(1 / 5) * Real.log H)) := by
          exact (Real.exp_add _ _).symm
        _ = _ := by congr 1 <;> ring
    calc
      Real.rpow H (4 / 5 : ℝ) =
          Real.exp (Real.log H * (4 / 5 : ℝ)) :=
        Real.rpow_def_of_pos hHpos _
      _ = Real.exp ((4 / 5 : ℝ) * Real.log H) := by congr 1 <;> ring
      _ ≤ 2 * Real.exp ((4 / 5 : ℝ) * Real.log H) := by
        nlinarith [Real.exp_pos ((4 / 5 : ℝ) * Real.log H)]
      _ = 2 * Real.exp (Real.log H) *
          Real.exp (-(1 / 5) * Real.log H) := by
        calc
          _ = 2 * (Real.exp (Real.log H) *
              Real.exp (-(1 / 5) * Real.log H)) :=
            congrArg (fun z : ℝ => 2 * z) hExpSub.symm
          _ = _ := by ring
      _ = 2 * H * Real.exp (-(1 / 5) * Real.log H) := by
        rw [Real.exp_log hHpos]
  have hHfactor :
      (2 * H) ^ (p - 1) * Real.rpow H (4 / 5 : ℝ) ≤
        (2 * H) ^ p * Real.exp (-(1 / 5) * Real.log H) := by
    have hpSub : p = (p - 1) + 1 := by omega
    rw [hpSub, pow_succ]
    calc
      (2 * H) ^ (p - 1) * Real.rpow H (4 / 5 : ℝ) ≤
          (2 * H) ^ (p - 1) *
            (2 * H * Real.exp (-(1 / 5) * Real.log H)) :=
        mul_le_mul_of_nonneg_left hHratio (by positivity)
      _ = (2 * H) ^ (p - 1) * (2 * H) *
          Real.exp (-(1 / 5) * Real.log H) := by ring
  have hcore :
      ((1 / (M : ℝ)) *
        ∑ b ∈ B, ‖phasePolynomialSum V θ b k M‖) ^ p ≤
        (2 * H) ^ p * Real.exp
          (10 * (k : ℝ) + (p : ℝ) * (k : ℝ) * Real.log (4 * Real.pi) +
            C₁ * Real.rpow (k : ℝ) C₂ - (1 / 5) * Real.log H +
            (1 / 100) * Real.log (M : ℝ)) := by
    calc
      _ ≤ (1 / (M : ℝ)) ^ p *
          ((2 * H) ^ (p - 1) *
            (occ * ((4 * Real.pi : ℝ) ^ (2 * s * k) *
              (M : ℝ) ^ phaseBoxExponent k *
              (Real.exp (C₁ * Real.rpow (k : ℝ) C₂) *
                Real.rpow (M : ℝ)
                  (2 * (s : ℝ) - (phaseBoxExponent k : ℝ) + 1 / 100))))) :=
        hcountScaled
      _ = ((2 * H) ^ (p - 1) * Real.rpow H (4 / 5 : ℝ)) *
          (Real.exp (10 * (k : ℝ)) *
            (4 * Real.pi : ℝ) ^ (2 * s * k) *
            Real.exp (C₁ * Real.rpow (k : ℝ) C₂) *
            ((1 / (M : ℝ)) ^ p * (M : ℝ) ^ phaseBoxExponent k *
              Real.rpow (M : ℝ)
                (2 * (s : ℝ) - (phaseBoxExponent k : ℝ) + 1 / 100))) := by
          dsimp [occ]
          ring
      _ = ((2 * H) ^ (p - 1) * Real.rpow H (4 / 5 : ℝ)) *
          (Real.exp (10 * (k : ℝ)) *
            (4 * Real.pi : ℝ) ^ (2 * s * k) *
            Real.exp (C₁ * Real.rpow (k : ℝ) C₂) *
            Real.rpow (M : ℝ) (1 / 100 : ℝ)) := by rw [hMprod]
      _ = ((2 * H) ^ (p - 1) * Real.rpow H (4 / 5 : ℝ)) *
          Real.exp (10 * (k : ℝ) + (p : ℝ) * (k : ℝ) *
            Real.log (4 * Real.pi) + C₁ * Real.rpow (k : ℝ) C₂ +
            (1 / 100) * Real.log (M : ℝ)) := by rw [hCoreExp]
      _ ≤ ((2 * H) ^ p * Real.exp (-(1 / 5) * Real.log H)) *
          Real.exp (10 * (k : ℝ) + (p : ℝ) * (k : ℝ) *
            Real.log (4 * Real.pi) + C₁ * Real.rpow (k : ℝ) C₂ +
            (1 / 100) * Real.log (M : ℝ)) :=
        mul_le_mul_of_nonneg_right hHfactor (Real.exp_pos _).le
      _ = (2 * H) ^ p *
          Real.exp (-(1 / 5) * Real.log H +
            (10 * (k : ℝ) + (p : ℝ) * (k : ℝ) * Real.log (4 * Real.pi) +
              C₁ * Real.rpow (k : ℝ) C₂ +
              (1 / 100) * Real.log (M : ℝ))) := by
        calc
          _ = (2 * H) ^ p *
              (Real.exp (-(1 / 5) * Real.log H) *
                Real.exp (10 * (k : ℝ) + (p : ℝ) * (k : ℝ) *
                  Real.log (4 * Real.pi) + C₁ * Real.rpow (k : ℝ) C₂ +
                  (1 / 100) * Real.log (M : ℝ))) := by ring
          _ = _ := congrArg (fun z : ℝ => (2 * H) ^ p * z)
            (Real.exp_add (-(1 / 5) * Real.log H)
              (10 * (k : ℝ) + (p : ℝ) * (k : ℝ) * Real.log (4 * Real.pi) +
                C₁ * Real.rpow (k : ℝ) C₂ + (1 / 100) * Real.log (M : ℝ))).symm
      _ = _ := by congr 1 <;> ring
  have hBnonneg :
      0 ≤ 2 * H * Real.exp
        ((10 * (k : ℝ) + 2 * (s : ℝ) * (k : ℝ) * Real.log (4 * Real.pi) +
          C₁ * Real.rpow (k : ℝ) C₂ - (1 / 5) * Real.log H +
          (1 / 100) * Real.log (M : ℝ)) / (2 * (s : ℝ))) := by
    positivity
  have hBpow :
      (2 * H * Real.exp
        ((10 * (k : ℝ) + 2 * (s : ℝ) * (k : ℝ) * Real.log (4 * Real.pi) +
          C₁ * Real.rpow (k : ℝ) C₂ - (1 / 5) * Real.log H +
          (1 / 100) * Real.log (M : ℝ)) / (2 * (s : ℝ)))) ^ p =
        (2 * H) ^ p * Real.exp
          (10 * (k : ℝ) + (p : ℝ) * (k : ℝ) * Real.log (4 * Real.pi) +
            C₁ * Real.rpow (k : ℝ) C₂ - (1 / 5) * Real.log H +
            (1 / 100) * Real.log (M : ℝ)) := by
    rw [mul_pow, ← Real.rpow_natCast (Real.exp
      ((10 * (k : ℝ) + 2 * (s : ℝ) * (k : ℝ) * Real.log (4 * Real.pi) +
        C₁ * Real.rpow (k : ℝ) C₂ - (1 / 5) * Real.log H +
        (1 / 100) * Real.log (M : ℝ)) / (2 * (s : ℝ)))) p,
      Real.rpow_def_of_pos (Real.exp_pos _) (p : ℝ)]
    rw [Real.log_exp]
    congr 1
    rw [hPcast]
    have hspos : 0 < s := by omega
    field_simp [ne_of_gt (show 0 < (s : ℝ) by exact_mod_cast hspos)]
  have hppos : 0 < p := lt_of_lt_of_le (by norm_num) hp1
  exact le_of_pow_le_pow_left₀ (Nat.ne_of_gt hppos) hBnonneg
    (hcore.trans_eq hBpow.symm)

/-- High frequencies use the Taylor polynomial and Vinogradov mean value. -/
theorem phase_high_regime_bound (hMV : phaseMeanValueInput) :
    ∀ C : ℝ, 0 < C →
      ∃ C₀ x₀ : ℝ, 0 < C₀ ∧ 2 < x₀ ∧
        phaseWindowBound (fun H v => Real.rpow H (4 / 5) ≤ |v|) C C₀ x₀ := by
  sorry

end ArtinPrimitiveRoots.Proofs.pp_phase_p
