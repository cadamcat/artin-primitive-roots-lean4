import ArtinPrimitiveRoots.TypeII.PD.Defs

namespace ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0

open MeasureTheory intervalIntegral Filter
open scoped Topology

noncomputable def phase (t y : ℝ) : ℂ :=
  Complex.exp (Complex.I * t * Real.log y)

noncomputable def phaseAntiderivative (t y : ℝ) : ℂ :=
  (y : ℂ) * phase t y / (1 + Complex.I * t)

lemma phase_norm_one (t y : ℝ) : ‖phase t y‖ = 1 := by
  simp [phase, Complex.norm_exp]

lemma phase_integral_trivial (t l r : ℝ) (hlr : l ≤ r) :
    ‖∫ y in l..r, phase t y‖ ≤ r - l := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := l) (b := r) (C := (1 : ℝ)) (f := phase t) (by
        intro y hy
        rw [phase_norm_one])
  simpa [abs_of_nonneg (sub_nonneg.mpr hlr)] using h

lemma phase_hasDerivAt (t y : ℝ) (hy : y ≠ 0) :
    HasDerivAt (phase t) (phase t y * (Complex.I * t / y)) y := by
  have hlog : HasDerivAt (fun x : ℝ => (Real.log x : ℂ)) ((y : ℂ)⁻¹) y := by
    convert (Real.hasDerivAt_log hy).ofReal_comp using 1 <;> simp [div_eq_mul_inv]
  have harg : HasDerivAt (fun x : ℝ => Complex.I * t * (Real.log x : ℂ))
      (Complex.I * t * (y : ℂ)⁻¹) y := by
    convert hlog.const_mul (Complex.I * t) using 1 <;> simp [mul_comm]
  have hexp := (Complex.hasDerivAt_exp (Complex.I * t * (Real.log y : ℂ))).comp y harg
  have hfun : phase t = Complex.exp ∘ (fun x : ℝ => Complex.I * (t * (Real.log x : ℂ))) := by
    funext x
    simp only [phase, Function.comp_apply]
    congr 1
    ring
  rw [hfun]
  convert hexp using 1 <;> simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] <;> ring

lemma phaseAntiderivative_hasDerivAt (t y : ℝ) (hy : y ≠ 0) :
    HasDerivAt (phaseAntiderivative t) (phase t y) y := by
  have hreal : HasDerivAt (fun z : ℝ => (z : ℂ)) 1 y := by
    simpa using (hasDerivAt_id y).ofReal_comp
  have hphase := phase_hasDerivAt t y hy
  have hprodRaw := hreal.mul hphase
  have hcancel : (y : ℂ) * (Complex.I * t / y) = Complex.I * t := by
    field_simp [Complex.ofReal_ne_zero.mpr hy]
  have hprodEq : 1 * phase t y + (y : ℂ) * (phase t y * (Complex.I * t / y)) =
      phase t y * (1 + Complex.I * t) := by
    calc
      1 * phase t y + (y : ℂ) * (phase t y * (Complex.I * t / y)) =
          phase t y + phase t y * ((y : ℂ) * (Complex.I * t / y)) := by ring
      _ = phase t y + phase t y * (Complex.I * t) := by rw [hcancel]
      _ = phase t y * (1 + Complex.I * t) := by ring
  have hprod : HasDerivAt (fun z : ℝ => (z : ℂ) * phase t z)
      (phase t y * (1 + Complex.I * t)) y := by
    convert hprodRaw using 1
    exact hprodEq.symm
  have hden : (1 + Complex.I * t : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hdiv := hprod.div_const (1 + Complex.I * t)
  convert hdiv using 1
  · funext z
    rfl
  · field_simp [hden]

lemma phase_continuousOn_Ici_aux (t N : ℝ) (hN : 0 < N) :
    ContinuousOn (phase t) (Set.Ici N) := by
  have hlog : ContinuousOn Real.log (Set.Ici N) :=
    ContinuousOn.mono Real.continuousOn_log (by
      intro y hy
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt (lt_of_lt_of_le hN hy))
  have hlogC : ContinuousOn (fun y : ℝ => (Real.log y : ℂ)) (Set.Ici N) :=
    Complex.continuous_ofReal.comp_continuousOn hlog
  have harg : ContinuousOn (fun y : ℝ => Complex.I * t * (Real.log y : ℂ)) (Set.Ici N) :=
    continuousOn_const.mul hlogC
  have hExp : ContinuousOn
      (fun y : ℝ => Complex.exp (Complex.I * t * (Real.log y : ℂ))) (Set.Ici N) :=
    (Complex.contDiff_exp (𝕜 := ℝ) (n := ⊤)).continuous.comp_continuousOn harg
  change ContinuousOn
    (fun y : ℝ => Complex.exp (Complex.I * t * (Real.log y : ℂ))) (Set.Ici N)
  exact hExp

lemma phase_integral_bound (t N l r : ℝ) (hN : 0 < N) (hl : N ≤ l)
    (hlr : l ≤ r) (hr : r ≤ 2 * N) (ht : 1 ≤ |t|) :
    ‖∫ y in l..r, phase t y‖ ≤ 4 * N / |t| := by
  let den : ℂ := 1 + Complex.I * t
  have hdenSq : ‖den‖ ^ 2 = 1 + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [den, Complex.normSq]
    ring
  have hdenLower : |t| ≤ ‖den‖ := by
    have hnorm : 0 ≤ ‖den‖ := norm_nonneg _
    have habsSq : |t| ^ 2 = t ^ 2 := sq_abs t
    nlinarith [hdenSq, habsSq, sq_nonneg (‖den‖ - |t|)]
  have hphaseCont := phase_continuousOn_Ici_aux t N hN
  have hphaseInt : IntervalIntegrable (phase t) MeasureTheory.volume l r := by
    apply (hphaseCont.mono ?_).intervalIntegrable
    intro y hy
    have hy' : y ∈ Set.Icc l r := by
      simpa [Set.uIcc_of_le hlr] using hy
    exact le_trans hl hy'.1
  have hderivEq : ∀ y ∈ Set.Icc l r,
      deriv (phaseAntiderivative t) y = phase t y := by
    intro y hy
    have hypos : 0 < y := lt_of_lt_of_le hN (le_trans hl hy.1)
    exact (phaseAntiderivative_hasDerivAt t y hypos.ne').deriv
  have hdiff : ∀ y ∈ Set.uIcc l r,
      DifferentiableAt ℝ (phaseAntiderivative t) y := by
    intro y hy
    have hy' : y ∈ Set.Icc l r := by simpa [Set.uIcc_of_le hlr] using hy
    have hypos : 0 < y := lt_of_lt_of_le hN (le_trans hl hy'.1)
    exact (phaseAntiderivative_hasDerivAt t y hypos.ne').differentiableAt
  have hderivInt : IntervalIntegrable (deriv (phaseAntiderivative t))
      MeasureTheory.volume l r := by
    apply hphaseInt.congr
    intro y hy
    have hy' : y ∈ Set.Ioc l r := by
      simpa [Set.uIoc_of_le hlr] using hy
    exact (hderivEq y ⟨hy'.1.le, hy'.2⟩).symm
  have hFTC : ∫ y in l..r, deriv (phaseAntiderivative t) y =
      phaseAntiderivative t r - phaseAntiderivative t l :=
    intervalIntegral.integral_deriv_eq_sub hdiff hderivInt
  have hreplace : ∫ y in l..r, deriv (phaseAntiderivative t) y =
      ∫ y in l..r, phase t y := by
    apply intervalIntegral.integral_congr
    intro y hy
    have hy' : y ∈ Set.Icc l r := by simpa [Set.uIcc_of_le hlr] using hy
    exact hderivEq y hy'
  have hnormPhase (y : ℝ) (hy : 0 < y) : ‖phase t y‖ = 1 := by
    simp [phase, Complex.norm_exp]
  have hAntiNorm (y : ℝ) (hy : 0 < y) :
      ‖phaseAntiderivative t y‖ = y / ‖den‖ := by
    simp [phaseAntiderivative, den, hnormPhase y hy, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hy]
  have hTpos : 0 < |t| := lt_of_lt_of_le zero_lt_one ht
  have hInv : 1 / ‖den‖ ≤ 1 / |t| := one_div_le_one_div_of_le hTpos hdenLower
  have hsum : r + l ≤ 4 * N := by linarith
  calc
    ‖∫ y in l..r, phase t y‖ =
        ‖phaseAntiderivative t r - phaseAntiderivative t l‖ := by
      rw [← hreplace, hFTC]
    _ ≤ ‖phaseAntiderivative t r‖ + ‖phaseAntiderivative t l‖ := norm_sub_le _ _
    _ = r / ‖den‖ + l / ‖den‖ := by
      rw [hAntiNorm r (by linarith), hAntiNorm l (by linarith)]
    _ = (r + l) * ‖den‖⁻¹ := by ring
    _ ≤ (4 * N) * ‖den‖⁻¹ := mul_le_mul_of_nonneg_right hsum (inv_nonneg.mpr (norm_nonneg _))
    _ ≤ (4 * N) * |t|⁻¹ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [one_div] using hInv
    _ = 4 * N / |t| := by ring

lemma phase_lipschitz (t N : ℝ) (hN : 0 < N) :
    ∀ y z : ℝ, N ≤ y → N ≤ z →
      ‖phase t y - phase t z‖ ≤ (|t| / N) * |y - z| := by
  intro y z hy hz
  have hs : Convex ℝ (Set.Ici N) := convex_Ici (𝕜 := ℝ) N
  apply hs.norm_image_sub_le_of_norm_deriv_le (f := phase t)
  · intro w hw
    exact (phase_hasDerivAt t w (ne_of_gt (lt_of_lt_of_le hN hw))).differentiableAt
  · intro w hw
    have hwpos : 0 < w := lt_of_lt_of_le hN hw
    have hd := phase_hasDerivAt t w hwpos.ne'
    rw [hd.deriv]
    have hexp : ‖phase t w‖ = 1 := by
      simp [phase, Complex.norm_exp]
    calc
      ‖phase t w * (Complex.I * t / w)‖ =
          ‖phase t w‖ * ‖Complex.I * t / w‖ := norm_mul _ _
      _ = |t| / w := by
        rw [hexp]
        simp [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hwpos]
      _ ≤ |t| / N := div_le_div_of_nonneg_left (abs_nonneg t) hN hw
  · exact hz
  · exact hy

lemma phase_continuousOn_Ici (t N : ℝ) (hN : 0 < N) :
    ContinuousOn (phase t) (Set.Ici N) := by
  have hlog : ContinuousOn Real.log (Set.Ici N) :=
    ContinuousOn.mono Real.continuousOn_log (by
      intro y hy
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt (lt_of_lt_of_le hN hy))
  have hlogC : ContinuousOn (fun y : ℝ => (Real.log y : ℂ)) (Set.Ici N) :=
    Complex.continuous_ofReal.comp_continuousOn hlog
  have harg : ContinuousOn (fun y : ℝ => Complex.I * t * (Real.log y : ℂ)) (Set.Ici N) :=
    continuousOn_const.mul hlogC
  have hExp : ContinuousOn
      (fun y : ℝ => Complex.exp (Complex.I * t * (Real.log y : ℂ))) (Set.Ici N) :=
    (Complex.contDiff_exp (𝕜 := ℝ) (n := ⊤)).continuous.comp_continuousOn harg
  change ContinuousOn
    (fun y : ℝ => Complex.exp (Complex.I * t * (Real.log y : ℂ))) (Set.Ici N)
  exact hExp

lemma phase_cell_integral_error (t N a q : ℝ) (hN : 0 < N) (ha : N ≤ a)
    (hq : 0 < q) :
    ‖q * phase t a - ∫ y in a..a + q, phase t y‖ ≤ (|t| / N) * q ^ 2 := by
  have hcont := phase_continuousOn_Ici t N hN
  have hcell : ContinuousOn (phase t) (Set.Icc a (a + q)) :=
    ContinuousOn.mono hcont (by
      intro y hy
      exact le_trans ha hy.1)
  have hInt : IntervalIntegrable (phase t) MeasureTheory.volume a (a + q) :=
    hcell.intervalIntegrable_of_Icc (by linarith)
  have hconst : IntervalIntegrable (fun _ : ℝ => phase t a) MeasureTheory.volume a (a + q) :=
    intervalIntegrable_const
  have heq : q * phase t a - ∫ y in a..a + q, phase t y =
      ∫ y in a..a + q, (phase t a - phase t y) := by
    calc
      q * phase t a - ∫ y in a..a + q, phase t y =
          (∫ y in a..a + q, phase t a) - ∫ y in a..a + q, phase t y := by
        congr 1
        simp [intervalIntegral.integral_const, smul_eq_mul]
      _ = ∫ y in a..a + q, (phase t a - phase t y) := by
        rw [← intervalIntegral.integral_sub hconst hInt]
  calc
    _ = ‖∫ y in a..a + q, (phase t a - phase t y)‖ := by rw [heq]
    _ ≤ ((|t| / N) * q) * |q| := by
      calc
        _ ≤ ((|t| / N) * q) * |(a + q) - a| :=
          intervalIntegral.norm_integral_le_of_norm_le_const
            (a := a) (b := a + q) (C := (|t| / N) * q) (by
          intro y hy
          have hyIoc : y ∈ Set.Ioc a (a + q) := by
            simpa [Set.uIoc_of_le (le_add_of_nonneg_right hq.le)] using hy
          have hy' : y ∈ Set.Icc a (a + q) := ⟨hyIoc.1.le, hyIoc.2⟩
          have hay : a ≤ y := hy'.1
          calc
            ‖phase t a - phase t y‖ ≤ (|t| / N) * |a - y| := by
              apply phase_lipschitz t N hN a y ha (le_trans ha hay)
            _ ≤ (|t| / N) * q := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              rw [abs_of_nonpos (sub_nonpos.mpr hay)]
              nlinarith [hy'.2])
        _ = ((|t| / N) * q) * |q| := by congr 1 <;> ring
    _ = (|t| / N) * q ^ 2 := by rw [abs_of_pos hq]; ring

lemma phase_lattice_sum_integral_bound (t N a q : ℝ) (m : ℕ)
    (hN : 0 < N) (ha : N ≤ a) (hq : 0 < q) (hqN : q ≤ N)
    (hlen : q * ((m + 1 : ℕ) : ℝ) ≤ 2 * N) :
    ‖(∑ k ∈ Finset.range (m + 1), phase t (a + q * (k : ℝ))) -
        (1 / q) * ∫ y in a..a + q * ((m + 1 : ℕ) : ℝ), phase t y‖ ≤ 2 * |t| := by
  let x : ℕ → ℝ := fun k => a + q * (k : ℝ)
  let e : ℕ → ℂ := fun k =>
    (q : ℂ) * phase t (x k) - ∫ y in x k..x (k + 1), phase t y
  have hcont := phase_continuousOn_Ici t N hN
  have hxN (k : ℕ) : N ≤ x k := by
    dsimp [x]
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    nlinarith [mul_nonneg hq.le hk]
  have hxle (k : ℕ) : x k ≤ x (k + 1) := by
    dsimp [x]
    push_cast
    nlinarith [hq.le]
  have hcell (k : ℕ) : IntervalIntegrable (phase t) MeasureTheory.volume (x k) (x (k + 1)) := by
    have hsub : Set.uIcc (x k) (x (k + 1)) ⊆ Set.Ici N := by
      intro y hy
      have hy' : y ∈ Set.Icc (x k) (x (k + 1)) := by
        simpa [Set.uIcc_of_le (hxle k)] using hy
      exact le_trans (hxN k) hy'.1
    exact (hcont.mono hsub).intervalIntegrable
  have hsumInt :
      (∑ k ∈ Finset.range (m + 1), ∫ y in x k..x (k + 1), phase t y) =
        ∫ y in a..a + q * ((m + 1 : ℕ) : ℝ), phase t y := by
    simpa [x] using
      (intervalIntegral.sum_integral_adjacent_intervals
        (f := phase t) (μ := MeasureTheory.volume)
        (a := x) (n := m + 1) (fun k _ => hcell k))
  have hsumId :
      (∑ k ∈ Finset.range (m + 1), e k) =
        (q : ℂ) * (∑ k ∈ Finset.range (m + 1), phase t (x k)) -
          ∫ y in a..a + q * ((m + 1 : ℕ) : ℝ), phase t y := by
    simp only [e, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, hsumInt]
  have herr : ‖∑ k ∈ Finset.range (m + 1), e k‖ ≤
      ((m + 1 : ℕ) : ℝ) * ((|t| / N) * q ^ 2) := by
    calc
      _ ≤ ∑ k ∈ Finset.range (m + 1), ‖e k‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range (m + 1), ((|t| / N) * q ^ 2) := by
        apply Finset.sum_le_sum
        intro k hk
        have hnext : x (k + 1) = x k + q := by
          dsimp [x]
          push_cast
          ring
        have hloc := phase_cell_integral_error t N (x k) q hN (hxN k) hq
        dsimp [e]
        rw [hnext]
        exact hloc
      _ = ((m + 1 : ℕ) : ℝ) * ((|t| / N) * q ^ 2) := by simp
  have hqC : (q : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hq)
  have hform :
      (∑ k ∈ Finset.range (m + 1), phase t (x k)) -
          (1 / (q : ℂ)) * (∫ y in a..a + q * ((m + 1 : ℕ) : ℝ), phase t y) =
        (q : ℂ)⁻¹ * ((q : ℂ) * (∑ k ∈ Finset.range (m + 1), phase t (x k)) -
          ∫ y in a..a + q * ((m + 1 : ℕ) : ℝ), phase t y) := by
    field_simp [hqC]
  calc
    _ = ‖(q : ℂ)⁻¹ * (∑ k ∈ Finset.range (m + 1), e k)‖ := by
      rw [hsumId, ← hform]
    _ = q⁻¹ * ‖∑ k ∈ Finset.range (m + 1), e k‖ := by
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq]
    _ ≤ q⁻¹ * (((m + 1 : ℕ) : ℝ) * ((|t| / N) * q ^ 2)) :=
      mul_le_mul_of_nonneg_left herr (by positivity)
    _ ≤ 2 * |t| := by
      have hdiv : q * ((m + 1 : ℕ) : ℝ) / N ≤ 2 := by
        apply (div_le_iff₀ hN).2
        exact hlen
      have hqpos : 0 < q := hq
      calc
        q⁻¹ * (((m + 1 : ℕ) : ℝ) * ((|t| / N) * q ^ 2)) =
            (q * ((m + 1 : ℕ) : ℝ) / N) * |t| := by
          field_simp [ne_of_gt hqpos, ne_of_gt hN]
        _ ≤ 2 * |t| := mul_le_mul_of_nonneg_right hdiv (abs_nonneg t)

lemma phase_residue_sum_eq_lattice (t l r : ℝ) (q : ℕ) (a : ZMod q)
    (n₀ m : ℕ) (hq : 0 < q) (hn₀ : (n₀ : ZMod q) = a)
    (hl : l ≤ (n₀ : ℝ)) (hfirst : (n₀ : ℝ) < l + q)
    (hlast : (n₀ : ℝ) + (q : ℝ) * (m : ℝ) ≤ r)
    (hnext : r < (n₀ : ℝ) + (q : ℝ) * ((m + 1 : ℕ) : ℝ)) :
    (∑ n ∈ (Finset.range (⌊r⌋₊ + 1)).filter (fun (n : ℕ) =>
      l ≤ (n : ℝ) ∧ (n : ℝ) ≤ r ∧ (n : ZMod q) = a), phase t (n : ℝ)) =
      ∑ k ∈ Finset.range (m + 1), phase t ((n₀ + q * k : ℕ) : ℝ) := by
  classical
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  let S : Finset ℕ := (Finset.range (⌊r⌋₊ + 1)).filter fun n =>
    l ≤ (n : ℝ) ∧ (n : ℝ) ≤ r ∧ (n : ZMod q) = a
  let T : Finset ℕ := Finset.range (m + 1)
  change (∑ n ∈ S, phase t (n : ℝ)) = ∑ k ∈ T, phase t ((n₀ + q * k : ℕ) : ℝ)
  apply Finset.sum_bij'
    (fun n _ => (n - n₀) / q)
    (fun k _ => n₀ + q * k)
  · intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnrange, hprop⟩
    rcases hprop with ⟨hnl, hnr, hnres⟩
    have hcast : (n : ZMod q) = (n₀ : ZMod q) := hnres.trans hn₀.symm
    have hmod : n % q = n₀ % q := (ZMod.natCast_eq_natCast_iff' n n₀ q).mp hcast
    have hme : n₀ ≡ n [MOD q] := by simpa [Nat.ModEq] using hmod.symm
    have hn₀le : n₀ ≤ n := by
      by_contra hnot
      have hlt : n < n₀ := by omega
      have hnat : n + q ≤ n₀ := Nat.ModEq.add_le_of_lt hme.symm hlt
      have hreal : (n : ℝ) + (q : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast hnat
      linarith [hnl, hfirst, hreal]
    have hdiv : q ∣ n - n₀ := (Nat.modEq_iff_dvd' hn₀le).mp hme
    have hfac : n₀ + q * ((n - n₀) / q) = n := by
      calc
        n₀ + q * ((n - n₀) / q) = n₀ + (n - n₀) := by rw [Nat.mul_div_cancel' hdiv]
        _ = n := Nat.add_sub_of_le hn₀le
    have hfacR : (n : ℝ) = (n₀ : ℝ) + (q : ℝ) * (((n - n₀) / q : ℕ) : ℝ) := by
      exact_mod_cast hfac.symm
    have hk : (n - n₀) / q ≤ m := by
      by_contra hnot
      have hmle : m + 1 ≤ (n - n₀) / q := by omega
      have hmleR : ((m + 1 : ℕ) : ℝ) ≤ (((n - n₀) / q : ℕ) : ℝ) := by exact_mod_cast hmle
      have hqmono := mul_le_mul_of_nonneg_left hmleR (by positivity : 0 ≤ (q : ℝ))
      linarith [hnext, hnr, hfacR]
    exact Finset.mem_range.mpr (by omega)
  · intro k hk
    have hk' : k ≤ m := by have := Finset.mem_range.mp hk; omega
    have hkR : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hk'
    have hqk : (q : ℝ) * (k : ℝ) ≤ (q : ℝ) * (m : ℝ) :=
      mul_le_mul_of_nonneg_left hkR (by positivity)
    have hcast : ((n₀ + q * k : ℕ) : ℝ) = (n₀ : ℝ) + (q : ℝ) * (k : ℝ) := by norm_cast
    have hnr : ((n₀ + q * k : ℕ) : ℝ) ≤ r := by
      rw [hcast]
      linarith [hlast]
    have hnrange : n₀ + q * k ∈ Finset.range (⌊r⌋₊ + 1) := by
      apply Finset.mem_range.mpr
      apply Nat.lt_succ_of_le
      exact Nat.le_floor (by exact_mod_cast hnr)
    have hnl : l ≤ ((n₀ + q * k : ℕ) : ℝ) := by
      rw [hcast]
      exact le_trans hl (le_add_of_nonneg_right
        (mul_nonneg (by exact_mod_cast hq.le) (Nat.cast_nonneg k)))
    have hnres : ((n₀ + q * k : ℕ) : ZMod q) = a := by
      simpa [Nat.cast_add, Nat.cast_mul] using hn₀
    exact Finset.mem_filter.mpr ⟨hnrange, ⟨hnl, hnr, hnres⟩⟩
  · intro n hn
    rcases Finset.mem_filter.mp hn with ⟨_, hprop⟩
    rcases hprop with ⟨hnl, _, hnres⟩
    have hn₀le : n₀ ≤ n := by
      have hcast : (n : ZMod q) = (n₀ : ZMod q) := hnres.trans hn₀.symm
      have hmod : n % q = n₀ % q := (ZMod.natCast_eq_natCast_iff' n n₀ q).mp hcast
      have hme : n₀ ≡ n [MOD q] := by simpa [Nat.ModEq] using hmod.symm
      by_contra hnot
      have hlt : n < n₀ := by omega
      have hnat : n + q ≤ n₀ := Nat.ModEq.add_le_of_lt hme.symm hlt
      have hreal : (n : ℝ) + (q : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast hnat
      linarith [hnl, hfirst, hreal]
    have hdiv : q ∣ n - n₀ := by
      have hcast : (n : ZMod q) = (n₀ : ZMod q) := hnres.trans hn₀.symm
      have hmod : n % q = n₀ % q := (ZMod.natCast_eq_natCast_iff' n n₀ q).mp hcast
      exact (Nat.modEq_iff_dvd' hn₀le).mp (by simpa [Nat.ModEq] using hmod.symm)
    calc
      n₀ + q * ((n - n₀) / q) = n₀ + (n - n₀) := by rw [Nat.mul_div_cancel' hdiv]
      _ = n := Nat.add_sub_of_le hn₀le
  · intro k hk
    simp only [Nat.add_sub_cancel_left, Nat.mul_div_cancel_left k hq]
  · intro n hn
    rcases Finset.mem_filter.mp hn with ⟨_, hprop⟩
    rcases hprop with ⟨hnl, _, hnres⟩
    have hn₀le : n₀ ≤ n := by
      have hcast : (n : ZMod q) = (n₀ : ZMod q) := hnres.trans hn₀.symm
      have hmod : n % q = n₀ % q := (ZMod.natCast_eq_natCast_iff' n n₀ q).mp hcast
      have hme : n₀ ≡ n [MOD q] := by simpa [Nat.ModEq] using hmod.symm
      by_contra hnot
      have hlt : n < n₀ := by omega
      have hnat : n + q ≤ n₀ := Nat.ModEq.add_le_of_lt hme.symm hlt
      have hreal : (n : ℝ) + (q : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast hnat
      linarith [hnl, hfirst, hreal]
    have hdiv : q ∣ n - n₀ := by
      have hcast : (n : ZMod q) = (n₀ : ZMod q) := hnres.trans hn₀.symm
      have hmod : n % q = n₀ % q := (ZMod.natCast_eq_natCast_iff' n n₀ q).mp hcast
      exact (Nat.modEq_iff_dvd' hn₀le).mp (by simpa [Nat.ModEq] using hmod.symm)
    have hfac : n₀ + q * ((n - n₀) / q) = n := by
      calc
        n₀ + q * ((n - n₀) / q) = n₀ + (n - n₀) := by rw [Nat.mul_div_cancel' hdiv]
        _ = n := Nat.add_sub_of_le hn₀le
    simp [hfac]

lemma exists_phase_residue_start (q : ℕ) (a : ZMod q) (l : ℝ)
    (hl : 0 < l) (hq : 0 < q) :
    ∃ n₀ : ℕ, (n₀ : ZMod q) = a ∧ l ≤ (n₀ : ℝ) ∧ (n₀ : ℝ) < l + q := by
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  let m₀ : ℕ := ⌊l / (q : ℝ)⌋₊
  let b : ℕ := q * m₀ + a.val
  let n₀ : ℕ := if (b : ℝ) < l then b + q else b
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hm₀lo : (m₀ : ℝ) ≤ l / (q : ℝ) := Nat.floor_le (by positivity)
  have hm₀hi : l / (q : ℝ) < (m₀ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hqlo : (q : ℝ) * (m₀ : ℝ) ≤ l := by
    calc
      (q : ℝ) * (m₀ : ℝ) ≤ (q : ℝ) * (l / (q : ℝ)) :=
        mul_le_mul_of_nonneg_left hm₀lo hqR.le
      _ = l := by field_simp [ne_of_gt hqR]
  have hqhi : l < (q : ℝ) * ((m₀ + 1 : ℕ) : ℝ) := by
    calc
      l < ((m₀ : ℝ) + 1) * (q : ℝ) := (div_lt_iff₀ hqR).mp hm₀hi
      _ = (q : ℝ) * ((m₀ + 1 : ℕ) : ℝ) := by push_cast; ring
  have hbcast : (b : ℝ) = (q : ℝ) * (m₀ : ℝ) + (a.val : ℝ) := by
    dsimp [b]
    push_cast
    ring
  have haval : (a.val : ℝ) < (q : ℝ) := by exact_mod_cast a.val_lt
  have hblo : (q : ℝ) * (m₀ : ℝ) ≤ (b : ℝ) := by
    rw [hbcast]
    exact le_add_of_nonneg_right (by positivity)
  have hbhi : (b : ℝ) < (q : ℝ) * (m₀ : ℝ) + q := by
    rw [hbcast]
    linarith
  have hbResidue : (b : ZMod q) = a := by
    dsimp [b]
    simp [Nat.cast_add, Nat.cast_mul]
  refine ⟨n₀, ?_, ?_, ?_⟩
  · dsimp [n₀]
    split_ifs <;> simp [hbResidue]
  · by_cases hb : (b : ℝ) < l
    · dsimp [n₀]
      rw [if_pos hb, Nat.cast_add]
      have hqstep : (q : ℝ) * ((m₀ + 1 : ℕ) : ℝ) ≤ (b : ℝ) + q := by
        rw [hbcast, Nat.cast_add]
        push_cast
        have hvalnonneg : (0 : ℝ) ≤ (a.val : ℝ) := Nat.cast_nonneg _
        nlinarith [hvalnonneg]
      linarith [hqhi, hqstep]
    · dsimp [n₀]
      rw [if_neg hb]
      exact le_of_not_gt hb
  · by_cases hb : (b : ℝ) < l
    · dsimp [n₀]
      rw [if_pos hb, Nat.cast_add]
      linarith
    · dsimp [n₀]
      rw [if_neg hb]
      have hupper : (b : ℝ) < l + q := by
        rw [hbcast]
        nlinarith [hqlo, hbhi]
      exact hupper

lemma phase_residue_interval_bounds (t N l r : ℝ) (q : ℕ) (a : ZMod q)
    (hN : 0 < N) (hlower : N ≤ l) (hlr : l ≤ r) (hr : r ≤ 2 * N)
    (hq : 0 < q) (hqN : (q : ℝ) ≤ N) (ht : 1 ≤ |t|) :
    ‖(∑ n ∈ (Finset.range (⌊r⌋₊ + 1)).filter (fun (n : ℕ) =>
        l ≤ (n : ℝ) ∧ (n : ℝ) ≤ r ∧ (n : ZMod q) = a), phase t (n : ℝ)) -
        (1 / (q : ℂ)) * ∫ y in l..r, phase t y‖ ≤ 4 * (1 + |t|) ∧
      ‖∫ y in l..r, phase t y‖ ≤ 4 * N / |t| ∧
      ((q : ℝ) / N) *
        ‖∑ n ∈ (Finset.range (⌊r⌋₊ + 1)).filter (fun (n : ℕ) =>
          l ≤ (n : ℝ) ∧ (n : ℝ) ≤ r ∧ (n : ZMod q) = a), phase t (n : ℝ)‖ ≤
        4 / |t| + 4 * ((q : ℝ) / N) * (1 + |t|) := by
  classical
  let S : Finset ℕ := (Finset.range (⌊r⌋₊ + 1)).filter fun n =>
    l ≤ (n : ℝ) ∧ (n : ℝ) ≤ r ∧ (n : ZMod q) = a
  let z : ℂ := 1 / (q : ℂ)
  let I : ℂ := ∫ y in l..r, phase t y
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hI : ‖I‖ ≤ 4 * N / |t| := by
    exact phase_integral_bound t N l r hN hlower hlr hr ht
  have hcoef : ‖z‖ = 1 / (q : ℝ) := by
    dsimp [z]
    rw [norm_div, norm_one, Complex.norm_natCast]
  have hscaled (w : ℂ) : ‖z * w‖ = (1 / (q : ℝ)) * ‖w‖ := by
    rw [norm_mul, hcoef]
  have herr : ‖(∑ n ∈ S, phase t (n : ℝ)) - z * I‖ ≤ 2 * |t| + 2 := by
    by_cases hshort : r - l < (q : ℝ)
    · have hcard : S.card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro n hn m hm
        by_contra hne
        rcases Finset.mem_filter.mp hn with ⟨_, ⟨hnl, hnr, hnres⟩⟩
        rcases Finset.mem_filter.mp hm with ⟨_, ⟨hml, hmr, hmres⟩⟩
        have hcast : (n : ZMod q) = (m : ZMod q) := hnres.trans hmres.symm
        have hmod : n % q = m % q := (ZMod.natCast_eq_natCast_iff' n m q).mp hcast
        have hme : n ≡ m [MOD q] := by simpa [Nat.ModEq] using hmod
        rcases lt_or_gt_of_ne hne with hnm | hmn
        · have hgap := Nat.ModEq.add_le_of_lt hme hnm
          have hgapR : (n : ℝ) + (q : ℝ) ≤ (m : ℝ) := by exact_mod_cast hgap
          have hqle : (q : ℝ) ≤ r - l := by linarith
          exact (not_lt_of_ge hqle) hshort
        · have hgap := Nat.ModEq.add_le_of_lt hme.symm hmn
          have hgapR : (m : ℝ) + (q : ℝ) ≤ (n : ℝ) := by exact_mod_cast hgap
          have hqle : (q : ℝ) ≤ r - l := by linarith
          exact (not_lt_of_ge hqle) hshort
      have hsum : ‖∑ n ∈ S, phase t (n : ℝ)‖ ≤ 1 := by
        calc
          _ ≤ ∑ n ∈ S, ‖phase t (n : ℝ)‖ := norm_sum_le _ _
          _ = S.card := by simp [phase_norm_one]
          _ ≤ 1 := by exact_mod_cast hcard
      have hIntTriv : ‖I‖ ≤ r - l := by
        dsimp [I]
        exact phase_integral_trivial t l r hlr
      calc
        _ ≤ ‖∑ n ∈ S, phase t (n : ℝ)‖ + ‖z * I‖ := norm_sub_le _ _
        _ ≤ 1 + (1 / (q : ℝ)) * (r - l) := by
          rw [hscaled]
          exact add_le_add hsum (mul_le_mul_of_nonneg_left hIntTriv (by positivity))
        _ ≤ 2 := by
          have hdiv : (1 / (q : ℝ)) * (r - l) < 1 := by
            calc
              (1 / (q : ℝ)) * (r - l) = (r - l) / (q : ℝ) := by ring
              _ < 1 := (div_lt_one hqR).2 hshort
          linarith
        _ ≤ 2 * |t| + 2 := by nlinarith [abs_nonneg t]
    · have hlong : (q : ℝ) ≤ r - l := le_of_not_gt hshort
      obtain ⟨n₀, hn₀res, hn₀l, hn₀next⟩ :=
        exists_phase_residue_start q a l (lt_of_lt_of_le hN hlower) hq
      have hn₀r : (n₀ : ℝ) ≤ r := by linarith
      have hn₀N : N ≤ (n₀ : ℝ) := le_trans hlower hn₀l
      let m : ℕ := ⌊(r - (n₀ : ℝ)) / (q : ℝ)⌋₊
      have hmlo : (m : ℝ) ≤ (r - (n₀ : ℝ)) / (q : ℝ) := by
        dsimp [m]
        exact Nat.floor_le (by positivity)
      have hlast : (n₀ : ℝ) + (q : ℝ) * (m : ℝ) ≤ r := by
        have hmul := mul_le_mul_of_nonneg_left hmlo hqR.le
        have hcancel : (q : ℝ) * ((r - (n₀ : ℝ)) / (q : ℝ)) =
            r - (n₀ : ℝ) := by field_simp [ne_of_gt hqR]
        dsimp [m] at hmul ⊢
        rw [hcancel] at hmul
        linarith
      have hmhi : (r - (n₀ : ℝ)) / (q : ℝ) < (m : ℝ) + 1 := by
        dsimp [m]
        exact Nat.lt_floor_add_one _
      have hnext : r < (n₀ : ℝ) + (q : ℝ) * ((m + 1 : ℕ) : ℝ) := by
        have hmul : r - (n₀ : ℝ) <
            (q : ℝ) * ((m + 1 : ℕ) : ℝ) := by
          calc
            r - (n₀ : ℝ) < ((m : ℝ) + 1) * (q : ℝ) :=
              (div_lt_iff₀ hqR).mp hmhi
            _ = (q : ℝ) * ((m + 1 : ℕ) : ℝ) := by push_cast; ring
        linarith
      have hlen : (q : ℝ) * ((m + 1 : ℕ) : ℝ) ≤ 2 * N := by
        have hqm : (q : ℝ) * (m : ℝ) ≤ r - (n₀ : ℝ) := by linarith [hlast]
        have hwidth : r - l ≤ N := by linarith
        have hstep : (q : ℝ) * ((m + 1 : ℕ) : ℝ) = (q : ℝ) * (m : ℝ) + q := by
          push_cast
          ring
        rw [hstep]
        nlinarith [hqm, hwidth, hqN, hn₀l]
      have hsumEq :
          (∑ n ∈ S, phase t (n : ℝ)) =
            ∑ k ∈ Finset.range (m + 1), phase t ((n₀ + q * k : ℕ) : ℝ) := by
        simpa [S] using
          (phase_residue_sum_eq_lattice t l r q a n₀ m hq hn₀res hn₀l hn₀next hlast hnext)
      have hcastSum :
          (∑ k ∈ Finset.range (m + 1), phase t ((n₀ + q * k : ℕ) : ℝ)) =
            ∑ k ∈ Finset.range (m + 1), phase t ((n₀ : ℝ) + (q : ℝ) * (k : ℝ)) := by
        apply Finset.sum_congr rfl
        intro k hk
        congr 1
        push_cast
        ring
      let u : ℝ := (n₀ : ℝ) + (q : ℝ) * ((m + 1 : ℕ) : ℝ)
      let J : ℂ := ∫ y in (n₀ : ℝ)..u, phase t y
      have hlat :
          ‖(∑ k ∈ Finset.range (m + 1), phase t ((n₀ : ℝ) + (q : ℝ) * (k : ℝ))) -
              (1 / (q : ℂ)) * J‖ ≤ 2 * |t| := by
        dsimp [J, u]
        exact phase_lattice_sum_integral_bound t N (n₀ : ℝ) (q : ℝ) m hN hn₀N hqR hqN hlen
      have hcont := phase_continuousOn_Ici_aux t N hN
      have hseg (v w : ℝ) (hv : N ≤ v) (hvw : v ≤ w) :
          IntervalIntegrable (phase t) MeasureTheory.volume v w := by
        apply (hcont.mono ?_).intervalIntegrable
        intro y hy
        have hy' : y ∈ Set.Icc v w := by simpa [Set.uIcc_of_le hvw] using hy
        exact le_trans hv hy'.1
      have hu : r ≤ u := by
        dsimp [u]
        linarith [hnext]
      have hAdj1 := intervalIntegral.integral_add_adjacent_intervals
        (hseg l (n₀ : ℝ) hlower hn₀l) (hseg (n₀ : ℝ) r hn₀N hn₀r)
      have hAdj2 := intervalIntegral.integral_add_adjacent_intervals
        (hseg (n₀ : ℝ) r hn₀N hn₀r) (hseg r u (by linarith [hlower]) hu)
      have hEndpointId :
          (∫ y in l..r, phase t y) - J =
            (∫ y in l..(n₀ : ℝ), phase t y) - ∫ y in r..u, phase t y := by
        dsimp [J]
        calc
          (∫ y in l..r, phase t y) - ∫ y in (n₀ : ℝ)..u, phase t y =
              ((∫ y in l..(n₀ : ℝ), phase t y) + ∫ y in (n₀ : ℝ)..r, phase t y) -
                ((∫ y in (n₀ : ℝ)..r, phase t y) + ∫ y in r..u, phase t y) := by
            rw [← hAdj1, ← hAdj2]
          _ = _ := by ring
      have hEndgap : u - r ≤ q := by
        dsimp [u]
        have hqm : (q : ℝ) * (m : ℝ) ≤ r - (n₀ : ℝ) := by linarith [hlast]
        have hstep : (q : ℝ) * ((m + 1 : ℕ) : ℝ) = (q : ℝ) * (m : ℝ) + q := by
          push_cast
          ring
        rw [hstep]
        linarith
      have hEndInt : ‖(∫ y in l..r, phase t y) - J‖ ≤ 2 * (q : ℝ) := by
        rw [hEndpointId]
        calc
          _ ≤ ‖∫ y in l..(n₀ : ℝ), phase t y‖ + ‖∫ y in r..u, phase t y‖ := norm_sub_le _ _
          _ ≤ ((n₀ : ℝ) - l) + (u - r) := by
            exact add_le_add (phase_integral_trivial t l (n₀ : ℝ) hn₀l)
              (phase_integral_trivial t r u hu)
          _ ≤ 2 * (q : ℝ) := by linarith [hn₀next, hEndgap]
      have hScaleEnd : ‖z * J - z * I‖ ≤ 2 := by
        have hdiffInt : ‖J - I‖ ≤ 2 * (q : ℝ) := by
          dsimp [J, I]
          simpa only [norm_sub_rev] using hEndInt
        calc
          _ = ‖z * (J - I)‖ := by congr 1 <;> ring
          _ = (1 / (q : ℝ)) * ‖J - I‖ := hscaled (J - I)
          _ ≤ (1 / (q : ℝ)) * (2 * (q : ℝ)) :=
            mul_le_mul_of_nonneg_left hdiffInt (by positivity)
          _ = 2 := by field_simp [ne_of_gt hqR]
      have hlongerr : ‖(∑ n ∈ S, phase t (n : ℝ)) - z * I‖ ≤
          2 * |t| + 2 := by
        have hlat' : ‖(∑ n ∈ S, phase t (n : ℝ)) - z * J‖ ≤ 2 * |t| := by
          rw [hsumEq, hcastSum]
          exact hlat
        have hdecomp :
            (∑ n ∈ S, phase t (n : ℝ)) - z * I =
              ((∑ n ∈ S, phase t (n : ℝ)) - z * J) + (z * J - z * I) := by ring
        rw [hdecomp]
        calc
          _ ≤ ‖(∑ n ∈ S, phase t (n : ℝ)) - z * J‖ + ‖z * J - z * I‖ := norm_add_le _ _
          _ ≤ 2 * |t| + 2 := add_le_add hlat' hScaleEnd
      exact hlongerr
  have herrFinal : ‖(∑ n ∈ S, phase t (n : ℝ)) - z * I‖ ≤ 4 * (1 + |t|) := by
    exact herr.trans (by nlinarith [abs_nonneg t])
  have hmain : ‖z * I‖ = (1 / (q : ℝ)) * ‖I‖ := hscaled I
  have hsumNorm : ‖∑ n ∈ S, phase t (n : ℝ)‖ ≤ ‖z * I‖ + 4 * (1 + |t|) := by
    have hrepr : (∑ n ∈ S, phase t (n : ℝ)) =
        ((∑ n ∈ S, phase t (n : ℝ)) - z * I) + z * I := by ring
    rw [hrepr]
    calc
      _ ≤ ‖(∑ n ∈ S, phase t (n : ℝ)) - z * I‖ + ‖z * I‖ := norm_add_le _ _
      _ ≤ 4 * (1 + |t|) + ‖z * I‖ := by nlinarith [herrFinal]
      _ = ‖z * I‖ + 4 * (1 + |t|) := by ring
  constructor
  · simpa [S, I, z] using herrFinal
  constructor
  · exact hI
  · have hmainScaled : ((q : ℝ) / N) * ‖z * I‖ ≤ 4 / |t| := by
      rw [hmain]
      calc
        ((q : ℝ) / N) * ((1 / (q : ℝ)) * ‖I‖) ≤
            ((q : ℝ) / N) * ((1 / (q : ℝ)) * (4 * N / |t|)) := by
          apply mul_le_mul_of_nonneg_left
          · exact mul_le_mul_of_nonneg_left hI (by positivity)
          · exact div_nonneg hqR.le hN.le
        _ = 4 / |t| := by field_simp [ne_of_gt hqR, ne_of_gt hN, ne_of_gt (lt_of_lt_of_le zero_lt_one ht)]
    calc
      ((q : ℝ) / N) * ‖∑ n ∈ S, phase t (n : ℝ)‖ ≤
          ((q : ℝ) / N) * (‖z * I‖ + 4 * (1 + |t|)) :=
        mul_le_mul_of_nonneg_left hsumNorm (div_nonneg hqR.le hN.le)
      _ = ((q : ℝ) / N) * ‖z * I‖ + ((q : ℝ) / N) * (4 * (1 + |t|)) := by ring
      _ ≤ 4 / |t| + 4 * ((q : ℝ) / N) * (1 + |t|) := by
        calc
          _ ≤ 4 / |t| + ((q : ℝ) / N) * (4 * (1 + |t|)) :=
            add_le_add hmainScaled le_rfl
          _ = 4 / |t| + 4 * ((q : ℝ) / N) * (1 + |t|) := by ring

lemma eventually_log_rpow_le_rpow (C ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, Real.rpow (Real.log x) C ≤ Real.rpow x ε := by
  have hratio : Tendsto
      (fun x : ℝ => Real.rpow (Real.log x) C * Real.exp (-ε * Real.log x))
      atTop (𝓝 0) := by
    have h := (_root_.tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero C ε hε).comp
      Real.tendsto_log_atTop
    convert h using 1
    funext x
    rfl
  filter_upwards [(tendsto_order.1 hratio).2 1 zero_lt_one,
    Ici_mem_atTop (2 : ℝ)] with x hsmall hx
  have hx2 : 2 ≤ x := by simpa using hx
  have hxpos : 0 < x := by linarith
  have hLpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hExpNeg : Real.exp (-ε * Real.log x) = (Real.exp (ε * Real.log x))⁻¹ := by
    have harg : -ε * Real.log x = -(ε * Real.log x) := by ring
    rw [harg, Real.exp_neg]
  have hquot : Real.rpow (Real.log x) C / Real.exp (ε * Real.log x) < 1 := by
    calc
      _ = Real.rpow (Real.log x) C * Real.exp (-ε * Real.log x) := by
        calc
          _ = Real.rpow (Real.log x) C * (Real.exp (ε * Real.log x))⁻¹ := by rw [div_eq_mul_inv]
          _ = Real.rpow (Real.log x) C * Real.exp (-ε * Real.log x) := by rw [hExpNeg.symm]
      _ < 1 := hsmall
  have hpow : Real.rpow (Real.log x) C < Real.exp (ε * Real.log x) :=
    (div_lt_one (Real.exp_pos _)).mp hquot
  have hRpowEq : Real.rpow x ε = Real.exp (Real.log x * ε) :=
    Real.rpow_def_of_pos hxpos ε
  calc
    Real.rpow (Real.log x) C ≤ Real.exp (ε * Real.log x) := hpow.le
    _ = Real.rpow x ε := by rw [hRpowEq]; congr 1 <;> ring

lemma eventually_moderate_cutoff_le (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop,
      Real.exp (Real.log x / Real.log (Real.log x) ^ 2) ≤ Real.rpow x (δ / 8) := by
  let g : ℝ → ℝ := fun x => Real.log (Real.log x)
  have hg : Tendsto g atTop atTop := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hinv : Tendsto (fun x => (g x)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hg
  have hsmall : ∀ᶠ x : ℝ in atTop, (g x)⁻¹ < Real.sqrt (δ / 8) :=
    (tendsto_order.1 hinv).2 _ (Real.sqrt_pos.2 (by positivity))
  filter_upwards [hsmall, Real.tendsto_log_atTop.eventually_gt_atTop 1,
    Ici_mem_atTop (2 : ℝ)] with x hsmall hL hx
  have hx2 : 2 ≤ x := by simpa using hx
  have hxpos : 0 < x := by linarith
  have hLpos : 0 < Real.log x := by linarith
  have hgpos : 0 < g x := Real.log_pos (by linarith)
  have hinvNonneg : 0 ≤ (g x)⁻¹ := inv_nonneg.mpr hgpos.le
  have hsmallSq : (g x)⁻¹ ^ 2 ≤ δ / 8 := by
    calc
      (g x)⁻¹ ^ 2 = (g x)⁻¹ * (g x)⁻¹ := by rw [pow_two]
      _ ≤ Real.sqrt (δ / 8) * Real.sqrt (δ / 8) :=
        calc
          _ ≤ Real.sqrt (δ / 8) * (g x)⁻¹ :=
            mul_le_mul_of_nonneg_right hsmall.le hinvNonneg
          _ ≤ Real.sqrt (δ / 8) * Real.sqrt (δ / 8) :=
            mul_le_mul_of_nonneg_left hsmall.le (Real.sqrt_nonneg _)
      _ = δ / 8 := Real.mul_self_sqrt (by positivity)
  have hrecip : (g x ^ 2)⁻¹ = (g x)⁻¹ ^ 2 := by
    field_simp [ne_of_gt hgpos]
  have hrecipBound : (g x ^ 2)⁻¹ ≤ δ / 8 := by
    rw [hrecip]
    exact hsmallSq
  have hexpBound : Real.log x / g x ^ 2 ≤ (δ / 8) * Real.log x := by
    calc
      Real.log x / g x ^ 2 = Real.log x * (g x ^ 2)⁻¹ := by ring
      _ ≤ Real.log x * (δ / 8) :=
        mul_le_mul_of_nonneg_left hrecipBound hLpos.le
      _ = (δ / 8) * Real.log x := by ring
  have hT : Real.exp (Real.log x / g x ^ 2) ≤ Real.exp ((δ / 8) * Real.log x) :=
    Real.exp_le_exp.mpr hexpBound
  have hpow : Real.exp ((δ / 8) * Real.log x) = Real.rpow x (δ / 8) := by
    calc
      Real.exp ((δ / 8) * Real.log x) = Real.exp (Real.log x * (δ / 8)) := by congr 1 <;> ring
      _ = Real.rpow x (δ / 8) := (Real.rpow_def_of_pos hxpos (δ / 8)).symm
  simpa [g] using hT.trans_eq hpow

lemma exists_moderate_absorption (δ C : ℝ) (hδ : 0 < δ) (hC : 0 < C) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      Real.rpow (Real.log x) C *
        (1 + Real.exp (Real.log x / Real.log (Real.log x) ^ 2)) ≤
          Real.rpow x (δ / 2) := by
  have hpoly := eventually_log_rpow_le_rpow C (δ / 4) (by positivity)
  have hcut := eventually_moderate_cutoff_le δ hδ
  have hbase : ∀ᶠ x : ℝ in atTop, 2 ≤ Real.rpow x (δ / 8) :=
    (_root_.tendsto_rpow_atTop (by positivity : 0 < δ / 8)).eventually_ge_atTop 2
  have hall : ∀ᶠ x : ℝ in atTop,
      2 ≤ x ∧ Real.rpow (Real.log x) C ≤ Real.rpow x (δ / 4) ∧
        Real.exp (Real.log x / Real.log (Real.log x) ^ 2) ≤ Real.rpow x (δ / 8) ∧
          2 ≤ Real.rpow x (δ / 8) := by
    filter_upwards [Ici_mem_atTop (2 : ℝ), hpoly, hcut, hbase] with x hx hpolyx hcutx hbasex
    exact ⟨hx, hpolyx, hcutx, hbasex⟩
  obtain ⟨x₁, hx₁⟩ := (eventually_atTop.1 hall)
  refine ⟨max x₁ 2, le_max_right _ _, ?_⟩
  intro x hx
  have hxx₁ : x₁ ≤ x := (le_max_left x₁ 2).trans hx
  have hallx := hx₁ x hxx₁
  rcases hallx with ⟨hx2, hpolyx, hcutx, hbasex⟩
  have hxpos : 0 < x := by linarith
  have hhalf : δ / 4 + δ / 4 = δ / 2 := by ring
  have hsumPow : (Real.rpow x (δ / 8)) ^ 2 = Real.rpow x (δ / 4) := by
    have hexp := (Real.rpow_mul_natCast (le_of_lt hxpos) (δ / 8) 2).symm
    calc
      (Real.rpow x (δ / 8)) ^ 2 = Real.rpow x ((δ / 8) * 2) := hexp
      _ = Real.rpow x (δ / 4) := by congr 1 <;> ring
  have hOnePlus : 1 + Real.exp (Real.log x / Real.log (Real.log x) ^ 2) ≤
      Real.rpow x (δ / 4) := by
    calc
      _ ≤ 1 + Real.rpow x (δ / 8) := by linarith [hcutx]
      _ ≤ 2 * Real.rpow x (δ / 8) := by nlinarith [hbasex]
      _ ≤ (Real.rpow x (δ / 8)) ^ 2 := by nlinarith [hbasex]
      _ = Real.rpow x (δ / 4) := hsumPow
  calc
    _ ≤ Real.rpow x (δ / 4) * (1 + Real.exp (Real.log x / Real.log (Real.log x) ^ 2)) :=
      mul_le_mul_of_nonneg_right hpolyx (by positivity)
    _ ≤ Real.rpow x (δ / 4) * Real.rpow x (δ / 4) :=
      mul_le_mul_of_nonneg_left hOnePlus (Real.rpow_nonneg hxpos.le (δ / 4))
    _ = Real.rpow x (δ / 2) := by
      calc
        _ = Real.rpow x (δ / 4 + δ / 4) :=
          (Real.rpow_add hxpos (δ / 4) (δ / 4)).symm
        _ = Real.rpow x (δ / 2) := by rw [hhalf]

end ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0
