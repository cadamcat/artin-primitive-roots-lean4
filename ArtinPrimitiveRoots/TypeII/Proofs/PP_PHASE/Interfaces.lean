import ArtinPrimitiveRoots.TypeII.PP.Defs
import ArtinPrimitiveRoots.TypeII.Proofs.PP_PHASE.LogPhaseLow
import ArtinPrimitiveRoots.TypeII.Proofs.PP_PHASE.PhaseReindex
import ArtinPrimitiveRoots.TypeII.Proofs.PP_PHASE.TorusMoment

/-! Exact interfaces for the PP-PHASE decomposition. -/

namespace ArtinPrimitiveRoots.Proofs.pp_phase_p

open MeasureTheory
open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.TypeII.PP
open scoped ComplexConjugate

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
  sorry

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

/-- Sum of the suprema over all closed coefficient boxes. -/
theorem phase_box_suprema (s k M : ℕ) (hM : 0 < M) :
    ∑ r : PhaseBoxIndex k M,
      (sSup {z : ℝ | ∃ a : Fin k → ℝ, a ∈ phaseClosedBox r ∧
        z = ‖phaseWeylSum k M a‖}) ^ (2 * s) ≤
      (4 * Real.pi : ℝ) ^ (2 * s * k) *
        (M : ℝ) ^ phaseBoxExponent k * (vinogradovCount s k M : ℝ) := by
  sorry

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

/-- High frequencies use the Taylor polynomial and Vinogradov mean value. -/
theorem phase_high_regime_bound (hMV : phaseMeanValueInput) :
    ∀ C : ℝ, 0 < C →
      ∃ C₀ x₀ : ℝ, 0 < C₀ ∧ 2 < x₀ ∧
        phaseWindowBound (fun H v => Real.rpow H (4 / 5) ≤ |v|) C C₀ x₀ := by
  sorry

end ArtinPrimitiveRoots.Proofs.pp_phase_p
