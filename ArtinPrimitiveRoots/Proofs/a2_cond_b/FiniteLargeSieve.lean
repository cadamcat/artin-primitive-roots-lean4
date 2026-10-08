import OAI.NumberTheory.PrimeGaps.AdditiveSieve

set_option autoImplicit false
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_cond_b

open OAI.LargePrimeGaps
open scoped ComplexConjugate

private theorem conductorCentered_abs_le_translate {x : ℝ} (hx : |x| ≤ 1 / 2)
    (m : ℤ) : |x| ≤ |x + (m : ℝ)| := by
  by_cases hm0 : m = 0
  · simp [hm0]
  by_cases hmpos : 0 < m
  · have hm : 1 ≤ m := by omega
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hxlo : -(1 / 2 : ℝ) ≤ x := (abs_le.mp hx).1
    have hsum : 1 / 2 ≤ x + (m : ℝ) := by linarith
    rw [abs_of_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1 / 2) hsum)]
    exact le_trans hx hsum
  · have hmneg : m < 0 := by omega
    have hm : m ≤ -1 := by omega
    have hmR : (m : ℝ) ≤ -1 := by exact_mod_cast hm
    have hxhi : x ≤ 1 / 2 := (abs_le.mp hx).2
    have hsum : x + (m : ℝ) ≤ -(1 / 2 : ℝ) := by linarith
    have hsum0 : x + (m : ℝ) ≤ 0 := le_trans hsum (by norm_num)
    rw [abs_of_nonpos hsum0]
    calc
      |x| ≤ 1 / 2 := hx
      _ ≤ -(x + (m : ℝ)) := by linarith

theorem conductorAngle_modInteger_lower {x y θ δ : ℝ}
    (hθ : |θ| ≤ 1 / 2) (hsep : δ ≤ |θ|)
    (hexp : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((x - y : ℝ) : ℂ)) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (θ : ℂ)))
    (m : ℤ) : δ ≤ |x - y - (m : ℝ)| := by
  let c : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  have hc : c ≠ 0 := by
    dsimp [c]
    apply mul_ne_zero
    · exact mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
    · exact Complex.I_ne_zero
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
  have hscaled : c * ((x - y : ℝ) : ℂ) =
      c * (θ : ℂ) + c * (n : ℂ) := by
    dsimp [c]
    convert hn using 1 <;> ring
  have hcancel : ((x - y : ℝ) : ℂ) = (θ : ℂ) + (n : ℂ) := by
    apply (mul_left_cancel₀ hc)
    calc
      c * ((x - y : ℝ) : ℂ) = c * (θ : ℂ) + c * (n : ℂ) := hscaled
      _ = c * ((θ : ℂ) + (n : ℂ)) := by ring
  have hreal : x - y = θ + (n : ℝ) := by exact_mod_cast hcancel
  have htranslate : |x - y - (m : ℝ)| = |θ + ((n - m : ℤ) : ℝ)| := by
    rw [hreal]
    congr 1
    push_cast
    ring
  rw [htranslate]
  exact hsep.trans (conductorCentered_abs_le_translate hθ (n - m))

def conductorShellWeight (N : ℕ) (δ : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then ((N + 1 : ℕ) : ℝ) ^ 2 else
    min (((N + 1 : ℕ) : ℝ) ^ 2) (1 / ((k : ℝ) ^ 2 * δ ^ 2))

theorem conductorShellWeight_nonneg (N : ℕ) (δ : ℝ) (k : ℕ) :
    0 ≤ conductorShellWeight N δ k := by
  by_cases hk : k = 0
  · simp [conductorShellWeight, hk]
    positivity
  · rw [conductorShellWeight, if_neg hk]
    rcases le_total (((N + 1 : ℕ) : ℝ) ^ 2)
        (1 / ((k : ℝ) ^ 2 * δ ^ 2)) with h | h
    · rw [min_eq_left h]
      positivity
    · rw [min_eq_right h]
      positivity

theorem conductorShellWeight_sum_le (N K : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (∑ k ∈ Finset.Icc 0 K, conductorShellWeight N δ k) ≤
      2 * ((N + 1 : ℕ) : ℝ) * (((N + 1 : ℕ) : ℝ) + δ⁻¹) := by
  let a : ℝ := (N + 1 : ℕ)
  let u : ℝ := (a * δ)⁻¹
  let R : ℕ := Nat.ceil u
  have ha : 0 < a := by dsimp [a]; positivity
  have hu : 0 < u := by dsimp [u]; positivity
  have hRlo : u ≤ (R : ℝ) := by exact Nat.le_ceil u
  have hRhi : (R : ℝ) < u + 1 := Nat.ceil_lt_add_one hu.le
  have hRpos : 0 < R := by
    by_contra h
    have hR0 : R = 0 := Nat.eq_zero_of_not_pos h
    rw [hR0, Nat.cast_zero] at hRlo
    exact (not_le_of_gt hu) hRlo
  have hterm (k : ℕ) (hk : k ≤ R) : conductorShellWeight N δ k ≤ a ^ 2 := by
    by_cases hk0 : k = 0
    · simp [conductorShellWeight, a, hk0]
    · simp [conductorShellWeight, a, hk0, min_le_left]
  have hlowSet : (Finset.Icc 0 K).filter (fun k => k ≤ R) ⊆ Finset.Icc 0 R := by
    intro k hk
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, (Finset.mem_filter.mp hk).2⟩
  have hlow :
      (∑ k ∈ (Finset.Icc 0 K).filter (fun k => k ≤ R), conductorShellWeight N δ k) ≤
        ((R + 1 : ℕ) : ℝ) * a ^ 2 := by
    calc
      _ ≤ ∑ k ∈ (Finset.Icc 0 K).filter (fun k => k ≤ R), a ^ 2 :=
        Finset.sum_le_sum (fun k hk => hterm k (Finset.mem_filter.mp hk).2)
      _ ≤ ∑ k ∈ Finset.Icc 0 R, a ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hlowSet
        intro k hk₁ hk₂
        positivity
      _ = ((R + 1 : ℕ) : ℝ) * a ^ 2 := by simp
  have hhighSet (hRK : R ≤ K) :
      (Finset.Icc 0 K).filter (fun k => ¬ k ≤ R) ⊆ Finset.Ioc R K := by
    intro k hk
    have hmem := (Finset.mem_filter.mp hk).1
    have hgt := (Finset.mem_filter.mp hk).2
    exact Finset.mem_Ioc.mpr ⟨Nat.lt_of_not_ge hgt, (Finset.mem_Icc.mp hmem).2⟩
  have hhigh (hRK : R ≤ K) :
      (∑ k ∈ (Finset.Icc 0 K).filter (fun k => ¬ k ≤ R), conductorShellWeight N δ k) ≤
        a * δ⁻¹ := by
    have hsub := hhighSet hRK
    calc
      _ ≤ ∑ k ∈ (Finset.Icc 0 K).filter (fun k => ¬ k ≤ R),
          1 / ((k : ℝ) ^ 2 * δ ^ 2) := by
        apply Finset.sum_le_sum
        intro k hk
        have hne : k ≠ 0 := by
          have hk' := Finset.mem_filter.mp hk
          have hki := Finset.mem_Icc.mp hk'.1
          omega
        simp [conductorShellWeight, hne]
      _ ≤ ∑ k ∈ Finset.Ioc R K, 1 / ((k : ℝ) ^ 2 * δ ^ 2) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro k hk₁ hk₂
        positivity
      _ = (δ ^ 2)⁻¹ * ∑ k ∈ Finset.Ioc R K, ((k : ℝ) ^ 2)⁻¹ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        field_simp
      _ ≤ (δ ^ 2)⁻¹ * ((R : ℝ)⁻¹ - (K : ℝ)⁻¹) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact sum_Ioc_inv_sq_le_sub (α := ℝ) (by omega) hRK
      _ ≤ (δ ^ 2)⁻¹ * (R : ℝ)⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hKpos : 0 < (K : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le hRpos hRK)
        have : 0 ≤ (K : ℝ)⁻¹ := inv_nonneg.mpr (le_of_lt hKpos)
        linarith
      _ ≤ a * δ⁻¹ := by
        have hRinv : (R : ℝ)⁻¹ ≤ u⁻¹ := by
          simpa [one_div] using one_div_le_one_div_of_le hu hRlo
        have huinv : u⁻¹ = a * δ := by dsimp [u]; field_simp
        rw [huinv] at hRinv
        have hmul := mul_le_mul_of_nonneg_left hRinv (by positivity : 0 ≤ (δ ^ 2)⁻¹)
        have hmul' : (δ ^ 2)⁻¹ * (R : ℝ)⁻¹ ≤ a * δ⁻¹ := by
          calc
            _ ≤ (δ ^ 2)⁻¹ * (a * δ) := hmul
            _ = a * δ⁻¹ := by field_simp
        exact hmul'
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.Icc 0 K) (fun k => k ≤ R) (fun k => conductorShellWeight N δ k)
  have hsum :
      (∑ k ∈ Finset.Icc 0 K, conductorShellWeight N δ k) ≤
        ((R + 1 : ℕ) : ℝ) * a ^ 2 + a * δ⁻¹ := by
    rw [← hsplit]
    by_cases hRK : R ≤ K
    · exact add_le_add hlow (hhigh hRK)
    · have hempty : (Finset.Icc 0 K).filter (fun k => ¬ k ≤ R) = ∅ := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty]
        constructor
        · rintro ⟨⟨_, hkK⟩, hknot⟩
          exact False.elim (hknot (hkK.trans (le_of_lt (lt_of_not_ge hRK))))
        · intro h
          exact False.elim h
      rw [hempty, Finset.sum_empty, add_zero]
      exact le_trans hlow (le_add_of_nonneg_right
        (mul_nonneg (le_of_lt ha) (inv_nonneg.mpr hδ.le)))
  have hRplus : ((R + 1 : ℕ) : ℝ) ≤ u + 2 := by
    calc
      ((R + 1 : ℕ) : ℝ) = (R : ℝ) + 1 := by norm_cast
      _ ≤ u + 2 := by linarith [hRhi.le]
  have hfinal :
      ((R + 1 : ℕ) : ℝ) * a ^ 2 + a * δ⁻¹ ≤
        2 * a * (a + δ⁻¹) := by
    dsimp [u] at hRplus
    have h1 := mul_le_mul_of_nonneg_right hRplus (sq_nonneg a)
    have h2 : (a * δ)⁻¹ * a ^ 2 = a * δ⁻¹ := by field_simp
    calc
      _ ≤ ((a * δ)⁻¹ + 2) * a ^ 2 + a * δ⁻¹ := by
        linarith [h1]
      _ = 2 * a * (a + δ⁻¹) := by rw [add_mul, h2]; ring
  exact hsum.trans hfinal

def conductorShellCode (D : ℕ) (x : ℝ) (hx : |x| ≤ 1 / 2) : Bool × Fin (D + 1) :=
  let t := |x| * (2 * (D : ℝ))
  ⟨decide (0 ≤ x), ⟨⌊t⌋₊, Nat.lt_succ_of_le (Nat.floor_le_of_le (by
    have hD : 0 ≤ (D : ℝ) := Nat.cast_nonneg _
    dsimp [t]
    nlinarith [hx]) )⟩⟩

theorem conductorShellCode_abs_diff_lt (D : ℕ) (hD : 0 < D)
    {x y : ℝ} (hx : |x| ≤ 1 / 2) (hy : |y| ≤ 1 / 2)
    (hcode : conductorShellCode D x hx = conductorShellCode D y hy) :
    |x - y| < 1 / (D : ℝ) := by
  have hsign : decide (0 ≤ x) = decide (0 ≤ y) := congrArg Prod.fst hcode
  have hsign' : (0 ≤ x) ↔ (0 ≤ y) := by simpa using hsign
  have hfloor :
      ⌊|x| * (2 * (D : ℝ))⌋₊ = ⌊|y| * (2 * (D : ℝ))⌋₊ := by
    exact congrArg (fun z : Bool × Fin (D + 1) => z.2.val) hcode
  have hxlo : (⌊|x| * (2 * (D : ℝ))⌋₊ : ℝ) ≤ |x| * (2 * (D : ℝ)) :=
    Nat.floor_le (by positivity)
  have hxhi : |x| * (2 * (D : ℝ)) <
      (⌊|x| * (2 * (D : ℝ))⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hylo : (⌊|y| * (2 * (D : ℝ))⌋₊ : ℝ) ≤ |y| * (2 * (D : ℝ)) :=
    Nat.floor_le (by positivity)
  have hyhi : |y| * (2 * (D : ℝ)) <
      (⌊|y| * (2 * (D : ℝ))⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  rw [← hfloor] at hylo hyhi
  have hmulabs :
      |(|x| - |y|) * (2 * (D : ℝ))| < 1 := by
    rw [abs_lt]
    constructor <;> nlinarith
  have hscale : |(|x| - |y|)| < 1 / (2 * (D : ℝ)) := by
    have hpos : 0 < 2 * (D : ℝ) := by positivity
    rw [abs_mul, abs_of_pos hpos] at hmulabs
    exact (lt_div_iff₀ hpos).2 (by nlinarith)
  by_cases hxn : 0 ≤ x
  · have hyn : 0 ≤ y := hsign'.mp hxn
    have habs : |x - y| = |(|x| - |y|)| := by simp [abs_of_nonneg hxn, abs_of_nonneg hyn]
    rw [habs]
    have hpos : 0 < (D : ℝ) := by exact_mod_cast hD
    have hden : (D : ℝ) < 2 * (D : ℝ) := by linarith
    exact lt_trans hscale (one_div_lt_one_div_of_lt hpos hden)
  · have hxneg : x < 0 := lt_of_not_ge hxn
    have hynn : ¬ 0 ≤ y := fun hy => hxn (hsign'.mpr hy)
    have hyn : y < 0 := lt_of_not_ge hynn
    have habs : |x - y| = |(|x| - |y|)| := by
      rw [abs_of_neg hxneg, abs_of_neg hyn]
      rw [abs_sub_comm]
      congr 1
      ring
    rw [habs]
    have hpos : 0 < (D : ℝ) := by exact_mod_cast hD
    have hden : (D : ℝ) < 2 * (D : ℝ) := by linarith
    exact lt_trans hscale (one_div_lt_one_div_of_lt hpos hden)

def conductorPairKernel (L : ℕ) (x : ℝ) : ℂ :=
  bvExp ((L : ℝ) * x) *
    (∑ u ∈ Finset.range (L + 1), bvExp ((u : ℝ) * x)) *
    (∑ v ∈ Finset.range (3 * L + 1), bvExp (-((v : ℝ) * x)))

set_option maxHeartbeats 500000 in
theorem conductorPairKernel_norm_le_shell (L D : ℕ) (hD : 0 < D)
    (x : ℝ) (hx : |x| ≤ 1 / 2) :
    ‖conductorPairKernel L x‖ ≤
      3 * conductorShellWeight L (1 / (2 * (D : ℝ)))
        (conductorShellCode D x hx).2.val := by
  classical
  let k := (conductorShellCode D x hx).2.val
  let M : ℝ := ((L + 1 : ℕ) : ℝ)
  change ‖conductorPairKernel L x‖ ≤
    3 * conductorShellWeight L (1 / (2 * (D : ℝ))) k
  have hM : 0 < M := by dsimp [M]; positivity
  have hkdef : k = ⌊|x| * (2 * (D : ℝ))⌋₊ := rfl
  have hA : ‖∑ u ∈ Finset.range (L + 1), bvExp ((u : ℝ) * x)‖ ≤ M := by
    calc
      _ ≤ ∑ u ∈ Finset.range (L + 1), ‖bvExp ((u : ℝ) * x)‖ := norm_sum_le _ _
      _ = M := by simp [M]
  have hB : ‖∑ v ∈ Finset.range (3 * L + 1), bvExp (-((v : ℝ) * x))‖ ≤ 3 * M := by
    calc
      _ ≤ ∑ v ∈ Finset.range (3 * L + 1), ‖bvExp (-((v : ℝ) * x))‖ := norm_sum_le _ _
      _ = (3 * L + 1 : ℕ) := by simp
      _ ≤ 3 * M := by
        dsimp [M]
        exact_mod_cast (by omega : 3 * L + 1 ≤ 3 * (L + 1))
  have htrivial : ‖conductorPairKernel L x‖ ≤ 3 * M ^ 2 := by
    rw [conductorPairKernel, norm_mul, norm_mul, norm_bvExp, one_mul]
    calc
      _ ≤ M * (3 * M) := mul_le_mul hA hB (by positivity) (by positivity)
      _ = 3 * M ^ 2 := by ring
  by_cases hk0 : k = 0
  · simpa [conductorShellWeight, hk0, M] using htrivial
  · have hfloor : (k : ℝ) ≤ |x| * (2 * (D : ℝ)) := by
      rw [hkdef]
      exact Nat.floor_le (by positivity)
    have hxne : x ≠ 0 := by
      intro hzero
      subst x
      simp [hkdef] at hk0
    have hAdecay := exponential_sum_bound (L + 1) hx hxne
    have hBdecay := exponential_sum_bound (3 * L + 1) (x := -x) (by simpa using hx)
      (by simpa using hxne)
    have hBdecay' :
        ‖∑ v ∈ Finset.range (3 * L + 1), bvExp (-((v : ℝ) * x))‖ ≤
          1 / (2 * |x|) := by
      simpa [mul_neg] using hBdecay
    have hdecay : ‖conductorPairKernel L x‖ ≤ 1 / (4 * |x| ^ 2) := by
      rw [conductorPairKernel, norm_mul, norm_mul, norm_bvExp, one_mul]
      calc
        _ ≤ (1 / (2 * |x|)) * (1 / (2 * |x|)) := by
          exact mul_le_mul hAdecay hBdecay' (by positivity) (by positivity)
        _ = 1 / (4 * |x| ^ 2) := by ring
    have hDpos : 0 < (D : ℝ) := by exact_mod_cast hD
    have hkpos : 0 < (k : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hk0)
    have hxlower : (k : ℝ) / (2 * (D : ℝ)) ≤ |x| := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have htail : 1 / (4 * |x| ^ 2) ≤
        1 / ((k : ℝ) ^ 2 * (1 / (2 * (D : ℝ))) ^ 2) := by
      have hposx : 0 < |x| := lt_of_lt_of_le (div_pos hkpos (by positivity)) hxlower
      have hposk : 0 < (k : ℝ) / (2 * (D : ℝ)) := div_pos hkpos (by positivity)
      have hsq : ((k : ℝ) / (2 * (D : ℝ))) ^ 2 ≤ |x| ^ 2 :=
        pow_le_pow_left₀ (by positivity) hxlower 2
      calc
        _ ≤ 1 / (4 * ((k : ℝ) / (2 * (D : ℝ))) ^ 2) := by
          gcongr
        _ ≤ 1 / ((k : ℝ) / (2 * (D : ℝ))) ^ 2 := by
          apply one_div_le_one_div_of_le (by positivity)
          nlinarith [sq_nonneg ((k : ℝ) / (2 * (D : ℝ)))]
        _ = 1 / ((k : ℝ) ^ 2 * (1 / (2 * (D : ℝ))) ^ 2) := by
          have heq : ((k : ℝ) / (2 * (D : ℝ))) ^ 2 =
              (k : ℝ) ^ 2 * (1 / (2 * (D : ℝ))) ^ 2 := by ring
          rw [heq]
    simp only [conductorShellWeight, if_neg hk0]
    dsimp [M] at htrivial ⊢
    by_cases hmin :
      ((L + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / ((k : ℝ) ^ 2 * (1 / (2 * (D : ℝ))) ^ 2)
    · rw [min_eq_left hmin]
      exact htrivial
    · have hmin' :
        1 / ((k : ℝ) ^ 2 * (1 / (2 * (D : ℝ))) ^ 2) ≤ ((L + 1 : ℕ) : ℝ) ^ 2 :=
        le_of_lt (lt_of_not_ge hmin)
      rw [min_eq_right hmin']
      have htail0 :
          0 ≤ 1 / ((k : ℝ) ^ 2 * (1 / (2 * (D : ℝ))) ^ 2) := by positivity
      exact (hdecay.trans htail).trans (by nlinarith [htail0])

theorem conductorVectorBinCode_injective {α I : Type*} [Fintype I] [DecidableEq I]
    (s : Finset α) (θ : α → I → ℝ) (D : ℕ) (hD : 0 < D) (row : α)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ∃ k : I, ∀ m : ℤ,
      1 / (D : ℝ) ≤ |θ a k - θ b k - (m : ℝ)|) :
    Set.InjOn (fun a k => conductorShellCode D
      (bvCentered (θ a k - θ row k)) (abs_bvCentered_le _)) s := by
  intro a ha b hb hcode
  by_contra hab
  obtain ⟨k, hk⟩ := hsep a ha b hb hab
  have hsmall := conductorShellCode_abs_diff_lt D hD
    (abs_bvCentered_le _) (abs_bvCentered_le _) (congrFun hcode k)
  let m : ℤ := ⌊θ a k - θ row k + 1 / 2⌋ -
    ⌊θ b k - θ row k + 1 / 2⌋
  have hcenter :
      bvCentered (θ a k - θ row k) - bvCentered (θ b k - θ row k) =
        θ a k - θ b k - (m : ℝ) := by
    dsimp [bvCentered, m]
    push_cast
    ring
  have hlarge := hk m
  rw [← hcenter] at hlarge
  exact (not_lt_of_ge hlarge) hsmall

theorem conductorShellCode_weight_sum_le (N D : ℕ) (hD : 0 < D) :
    (∑ c : Bool × Fin (D + 1), conductorShellWeight N
      (1 / (2 * (D : ℝ))) c.2.val) ≤
        4 * ((N + 1 : ℕ) : ℝ) * (((N + 1 : ℕ) : ℝ) + 2 * D) := by
  let δ : ℝ := 1 / (2 * (D : ℝ))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsum := conductorShellWeight_sum_le N D hδ
  have hcoord :
      (∑ c : Bool × Fin (D + 1), conductorShellWeight N δ c.2.val) =
        2 * (∑ k ∈ Finset.Icc 0 D, conductorShellWeight N δ k) := by
    classical
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, Bool.false_eq_true, Bool.true_eq_false,
      Finset.sum_const_zero, add_comm]
    rw [Fin.sum_univ_eq_sum_range, Nat.range_succ_eq_Icc_zero]
    ring
  calc
    _ = (∑ c : Bool × Fin (D + 1), conductorShellWeight N δ c.2.val) := by
      simp [δ]
    _ = 2 * (∑ k ∈ Finset.Icc 0 D, conductorShellWeight N δ k) := hcoord
    _ ≤ 2 * (2 * ((N + 1 : ℕ) : ℝ) * (((N + 1 : ℕ) : ℝ) + δ⁻¹)) := by
      exact mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = 4 * ((N + 1 : ℕ) : ℝ) * (((N + 1 : ℕ) : ℝ) + 2 * D) := by
      dsimp [δ]
      have hDpos : (D : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
      field_simp [hDpos]
      norm_num

theorem conductorBinGrid_product_sum_le {I : Type*} [Fintype I] [DecidableEq I]
    (N D : ℕ) (hD : 0 < D) :
    (∑ c : I → (Bool × Fin (D + 1)),
      ∏ i : I, conductorShellWeight N (1 / (2 * (D : ℝ))) (c i).2.val) ≤
        (4 * ((N + 1 : ℕ) : ℝ) * (((N + 1 : ℕ) : ℝ) + 2 * D)) ^ Fintype.card I := by
  classical
  let f : Bool × Fin (D + 1) → ℝ := fun c =>
    conductorShellWeight N (1 / (2 * (D : ℝ))) c.2.val
  let B : ℝ := 4 * ((N + 1 : ℕ) : ℝ) * (((N + 1 : ℕ) : ℝ) + 2 * D)
  have hcoord : ∀ i : I, (∑ c : Bool × Fin (D + 1), f c) ≤ B := by
    intro i
    exact conductorShellCode_weight_sum_le N D hD
  have hfactor :
      (∑ c : I → (Bool × Fin (D + 1)), ∏ i : I, f (c i)) =
        ∏ i : I, ∑ c : Bool × Fin (D + 1), f c := by
    simpa [f] using
      (Finset.sum_prod_piFinset (ι := I) (s := Finset.univ)
        (g := fun _ c => f c))
  have hprod :
      (∏ i : I, ∑ c : Bool × Fin (D + 1), f c) ≤ ∏ i : I, B := by
    apply Finset.prod_le_prod₀
    · intro i hi
      apply Finset.sum_nonneg
      intro c hc
      dsimp [f, conductorShellWeight]
      split_ifs <;> positivity
    · intro i hi
      exact hcoord i
  rw [hfactor]
  calc
    _ ≤ ∏ i : I, B := hprod
    _ = B ^ Fintype.card I := by simp [B]

set_option maxHeartbeats 500000 in
theorem conductorPackedShell_sum_le {α I : Type*} [Fintype I] [DecidableEq I]
    (s : Finset α) (θ : α → I → ℝ) (N D : ℕ) (hD : 0 < D) (row : α)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ∃ k : I, ∀ m : ℤ,
      1 / (D : ℝ) ≤ |θ a k - θ b k - (m : ℝ)|) :
    (∑ a ∈ s, ∏ k : I, conductorShellWeight N (1 / (2 * (D : ℝ)))
      (conductorShellCode D (bvCentered (θ a k - θ row k))
        (abs_bvCentered_le _)).2.val) ≤
      (4 * ((N + 1 : ℕ) : ℝ) * (((N + 1 : ℕ) : ℝ) + 2 * D)) ^ Fintype.card I := by
  classical
  let code : α → I → Bool × Fin (D + 1) := fun a k =>
    conductorShellCode D (bvCentered (θ a k - θ row k)) (abs_bvCentered_le _)
  let weight : (I → Bool × Fin (D + 1)) → ℝ := fun c =>
    ∏ k : I, conductorShellWeight N (1 / (2 * (D : ℝ))) (c k).2.val
  have hcode : Set.InjOn code s := conductorVectorBinCode_injective s θ D hD row hsep
  have himage : (∑ a ∈ s, weight (code a)) =
      ∑ c ∈ s.image code, weight c := by
    symm
    exact Finset.sum_image hcode
  have hsub : s.image code ⊆ Finset.univ := Finset.subset_univ _
  calc
    _ = ∑ a ∈ s, weight (code a) := by simp [weight, code]
    _ = ∑ c ∈ s.image code, weight c := himage
    _ ≤ ∑ c : I → Bool × Fin (D + 1), weight c := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro c hc₁ hc₂
      apply Finset.prod_nonneg
      intro k hk
      exact conductorShellWeight_nonneg N _ _
    _ ≤ (4 * ((N + 1 : ℕ) : ℝ) * (((N + 1 : ℕ) : ℝ) + 2 * D)) ^ Fintype.card I := by
      change (∑ c : I → Bool × Fin (D + 1),
        ∏ k : I, conductorShellWeight N (1 / (2 * (D : ℝ))) (c k).2.val) ≤ _
      exact conductorBinGrid_product_sum_le (I := I) N D hD

set_option maxHeartbeats 500000 in
theorem conductorProductKernel_row_sum_le {α I : Type*} [Fintype I] [DecidableEq I]
    (s : Finset α) (θ : α → I → ℝ) (L D : ℕ) (hD : 0 < D) (row : α)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ∃ k : I, ∀ m : ℤ,
      1 / (D : ℝ) ≤ |θ a k - θ b k - (m : ℝ)|) :
    (∑ a ∈ s, ∏ k : I,
      ‖conductorPairKernel L (bvCentered (θ a k - θ row k))‖) ≤
        (12 * ((L + 1 : ℕ) : ℝ) *
          (((L + 1 : ℕ) : ℝ) + 2 * D)) ^ Fintype.card I := by
  classical
  let code : α → I → Bool × Fin (D + 1) := fun a k =>
    conductorShellCode D (bvCentered (θ a k - θ row k)) (abs_bvCentered_le _)
  let weight : α → ℝ := fun a =>
    ∏ k : I, conductorShellWeight L (1 / (2 * (D : ℝ))) (code a k).2.val
  let B : ℝ := 4 * ((L + 1 : ℕ) : ℝ) *
    (((L + 1 : ℕ) : ℝ) + 2 * D)
  have hcode : Set.InjOn code s := conductorVectorBinCode_injective s θ D hD row hsep
  have hpack := conductorPackedShell_sum_le s θ L D hD row hsep
  have hpoint : ∀ a ∈ s,
      (∏ k : I, ‖conductorPairKernel L (bvCentered (θ a k - θ row k))‖) ≤
        (3 : ℝ) ^ Fintype.card I * weight a := by
    intro a ha
    calc
      _ ≤ ∏ k : I,
          3 * conductorShellWeight L (1 / (2 * (D : ℝ))) (code a k).2.val := by
        apply Finset.prod_le_prod₀
        · intro k hk
          positivity
        · intro k hk
          simpa [code] using conductorPairKernel_norm_le_shell L D hD
            (bvCentered (θ a k - θ row k)) (abs_bvCentered_le _)
      _ = (3 : ℝ) ^ Fintype.card I * weight a := by
        simp [weight, Finset.prod_mul_distrib]
  calc
    _ ≤ ∑ a ∈ s, ((3 : ℝ) ^ Fintype.card I * weight a) :=
      Finset.sum_le_sum (fun a ha => hpoint a ha)
    _ ≤ (3 : ℝ) ^ Fintype.card I * B ^ Fintype.card I := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hpack (by positivity)
    _ = (12 * ((L + 1 : ℕ) : ℝ) *
          (((L + 1 : ℕ) : ℝ) + 2 * D)) ^ Fintype.card I := by
      dsimp [B]
      rw [← mul_pow]
      ring_nf

theorem conductorPi_sum_prod {I A R : Type*} [Fintype I] [DecidableEq I]
    [Fintype A] [CommSemiring R] (g : I → A → R) :
    (∑ x : I → A, ∏ i : I, g i (x i)) =
      ∏ i : I, ∑ a : A, g i a := by
  classical
  simpa using
    (Finset.sum_prod_piFinset (ι := I) (s := (Finset.univ : Finset A)) (g := g))

theorem conductorPiPair_sum_prod {I A B R : Type*} [Fintype I] [DecidableEq I]
    [Fintype A] [Fintype B] [CommSemiring R] (g : I → A → B → R) :
    (∑ x : I → A, ∑ y : I → B, ∏ i : I, g i (x i) (y i)) =
      ∏ i : I, ∑ a : A, ∑ b : B, g i a b := by
  classical
  calc
    _ = ∑ x : I → A, ∏ i : I, ∑ y : B, g i (x i) y := by
      apply Finset.sum_congr rfl
      intro x hx
      exact conductorPi_sum_prod (fun i y => g i (x i) y)
    _ = ∏ i : I, ∑ a : A, ∑ b : B, g i a b := by
      exact conductorPi_sum_prod (fun i a => ∑ b : B, g i a b)

theorem conductorPairKernel_Fin_sum (L : ℕ) (x : ℝ) :
    (∑ u : Fin (L + 1), ∑ v : Fin (3 * L + 1),
      bvExp (((L : ℝ) + (u.val : ℝ) - (v.val : ℝ)) * x)) =
      conductorPairKernel L x := by
  calc
    _ = ∑ u : Fin (L + 1), ∑ v : Fin (3 * L + 1),
        bvExp ((L : ℝ) * x + ((u.val : ℝ) * x + -((v.val : ℝ) * x))) := by
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      congr 1
      ring
    _ = ∑ u : Fin (L + 1), ∑ v : Fin (3 * L + 1),
        (bvExp ((L : ℝ) * x) * bvExp ((u.val : ℝ) * x)) *
          bvExp (-((v.val : ℝ) * x)) := by
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      rw [bvExp_add, bvExp_add]
      ring
    _ = ∑ u : Fin (L + 1),
        (bvExp ((L : ℝ) * x) * bvExp ((u.val : ℝ) * x)) *
          (∑ v : Fin (3 * L + 1), bvExp (-((v.val : ℝ) * x))) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [← Finset.mul_sum]
    _ = bvExp ((L : ℝ) * x) *
        (∑ u : Fin (L + 1), bvExp ((u.val : ℝ) * x)) *
        (∑ v : Fin (3 * L + 1), bvExp (-((v.val : ℝ) * x))) := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ = conductorPairKernel L x := by
      rw [conductorPairKernel, ← Fin.sum_univ_eq_sum_range,
        ← Fin.sum_univ_eq_sum_range]

private theorem conductorBvExp_nat_mul_sub_int (n : ℕ) (x : ℝ) (m : ℤ) :
    bvExp ((n : ℝ) * (x - (m : ℝ))) = bvExp ((n : ℝ) * x) := by
  have h := bvExp_sub_int ((n : ℝ) * x) ((n : ℤ) * m)
  have h' : bvExp ((n : ℝ) * x - (n : ℝ) * (m : ℝ)) =
      bvExp ((n : ℝ) * x) := by
    simpa only [Int.cast_mul, Int.cast_natCast] using h
  rw [show (n : ℝ) * (x - (m : ℝ)) =
    (n : ℝ) * x - (n : ℝ) * (m : ℝ) by ring]
  exact h'

private theorem conductorBvExp_neg_nat_mul_sub_int (n : ℕ) (x : ℝ) (m : ℤ) :
    bvExp (-((n : ℝ) * (x - (m : ℝ)))) = bvExp (-((n : ℝ) * x)) := by
  have h := bvExp_sub_int (-((n : ℝ) * x)) (-(n : ℤ) * m)
  have h' : bvExp (-((n : ℝ) * x) - (-(n : ℝ) * (m : ℝ))) =
      bvExp (-((n : ℝ) * x)) := by
    simpa only [Int.cast_mul, Int.cast_neg, Int.cast_natCast] using h
  rw [show -((n : ℝ) * (x - (m : ℝ))) =
    -((n : ℝ) * x) - (-(n : ℝ) * (m : ℝ)) by ring]
  exact h'

theorem conductorPairKernel_sub_int (L : ℕ) (x : ℝ) (m : ℤ) :
    conductorPairKernel L (x - (m : ℝ)) = conductorPairKernel L x := by
  simp only [conductorPairKernel, conductorBvExp_nat_mul_sub_int,
    conductorBvExp_neg_nat_mul_sub_int]

theorem conductorPairKernel_centered (L : ℕ) (x : ℝ) :
    conductorPairKernel L (bvCentered x) = conductorPairKernel L x := by
  dsimp [bvCentered]
  exact conductorPairKernel_sub_int L x ⌊x + 1 / 2⌋

abbrev ConductorPairIndex (I : Type*) (L : ℕ) :=
  (I → Fin (L + 1)) × (I → Fin (3 * L + 1))

noncomputable def conductorPairFrequencyVector {α I : Type*} [Fintype I] [DecidableEq I]
    (L : ℕ) (θ : α → I → ℝ) (a : α) :
    EuclideanSpace ℂ (ConductorPairIndex I L) :=
  WithLp.toLp 2 (fun p : ConductorPairIndex I L =>
    ∏ i : I, bvExp
      (((L : ℝ) + (p.1 i).val - (p.2 i).val) * θ a i))

set_option maxHeartbeats 500000 in
theorem inner_conductorPairFrequencyVector {α I : Type*} [Fintype I] [DecidableEq I]
    (L : ℕ) (θ : α → I → ℝ) (a b : α) :
    inner ℂ (conductorPairFrequencyVector L θ a)
      (conductorPairFrequencyVector L θ b) =
        ∏ i : I, conductorPairKernel L (θ b i - θ a i) := by
  classical
  let pphase := fun (c : ConductorPairIndex I L) (j : α) =>
    ∏ i : I, bvExp (((L : ℝ) + (c.1 i).val - (c.2 i).val) * θ j i)
  have hpoint (c : ConductorPairIndex I L) :
      conj (pphase c a) * pphase c b =
        ∏ i : I, bvExp
          (((L : ℝ) + (c.1 i).val - (c.2 i).val) * (θ b i - θ a i)) := by
    simp only [pphase, map_prod, conj_bvExp]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [← bvExp_add]
    congr 1
    ring
  have hinner :
      inner ℂ (conductorPairFrequencyVector L θ a)
          (conductorPairFrequencyVector L θ b) =
        ∑ c : ConductorPairIndex I L, ∏ i : I,
          bvExp (((L : ℝ) + (c.1 i).val - (c.2 i).val) * (θ b i - θ a i)) := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conductorPairFrequencyVector]
    apply Finset.sum_congr rfl
    intro c hc
    simpa only [pphase, mul_comm] using hpoint c
  rw [hinner, Fintype.sum_prod_type]
  let g : I → Fin (L + 1) → Fin (3 * L + 1) → ℂ := fun i u v =>
    bvExp (((L : ℝ) + (u.val : ℝ) - (v.val : ℝ)) * (θ b i - θ a i))
  have hfactor :
      (∑ u : I → Fin (L + 1), ∑ v : I → Fin (3 * L + 1),
        ∏ i : I, g i (u i) (v i)) =
          ∏ i : I, ∑ u : Fin (L + 1), ∑ v : Fin (3 * L + 1), g i u v := by
    exact conductorPiPair_sum_prod g
  rw [hfactor]
  simp_rw [g, conductorPairKernel_Fin_sum]

set_option maxHeartbeats 500000 in
theorem conductorPairFrequencyVector_row_bound {α I : Type*} [Fintype I]
    [DecidableEq I] (s : Finset α) (θ : α → I → ℝ) (L D : ℕ) (hD : 0 < D)
    (row : α) (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ∃ k : I, ∀ m : ℤ,
      1 / (D : ℝ) ≤ |θ a k - θ b k - (m : ℝ)|) :
    (∑ b ∈ s, ‖inner ℂ (conductorPairFrequencyVector L θ row)
      (conductorPairFrequencyVector L θ b)‖) ≤
      (12 * ((L + 1 : ℕ) : ℝ) *
        (((L + 1 : ℕ) : ℝ) + 2 * D)) ^ Fintype.card I := by
  have hformula (b : α) :
      inner ℂ (conductorPairFrequencyVector L θ row)
          (conductorPairFrequencyVector L θ b) =
        ∏ k : I, conductorPairKernel L (θ b k - θ row k) :=
    inner_conductorPairFrequencyVector L θ row b
  simp_rw [hformula]
  calc
    _ = ∑ b ∈ s, ∏ k : I,
        ‖conductorPairKernel L (θ b k - θ row k)‖ := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [norm_prod]
    _ = ∑ b ∈ s, ∏ k : I,
        ‖conductorPairKernel L (bvCentered (θ b k - θ row k))‖ := by
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.prod_congr rfl
      intro k hk
      rw [conductorPairKernel_centered]
    _ ≤ (12 * ((L + 1 : ℕ) : ℝ) *
        (((L + 1 : ℕ) : ℝ) + 2 * D)) ^ Fintype.card I :=
      conductorProductKernel_row_sum_le s θ L D hD row hsep

set_option maxHeartbeats 500000 in
theorem conductorPairFrequencyVector_gram {α I : Type*} [Fintype I]
    [DecidableEq I] (s : Finset α) (θ : α → I → ℝ) (L D : ℕ) (hD : 0 < D)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ∃ k : I, ∀ m : ℤ,
      1 / (D : ℝ) ≤ |θ a k - θ b k - (m : ℝ)|) :
    ∀ z : EuclideanSpace ℂ (ConductorPairIndex I L),
      (∑ a ∈ s, ‖inner ℂ (conductorPairFrequencyVector L θ a) z‖ ^ 2) ≤
        (12 * ((L + 1 : ℕ) : ℝ) *
          (((L + 1 : ℕ) : ℝ) + 2 * D)) ^ Fintype.card I * ‖z‖ ^ 2 := by
  intro z
  apply OAI.LargePrimeGaps.gram_large_sieve s (conductorPairFrequencyVector L θ)
  · positivity
  · intro a ha
    exact conductorPairFrequencyVector_row_bound s θ L D hD a hsep

def conductorPairDifference {I : Type*} (L : ℕ)
    (p : ConductorPairIndex I L) : I → ℤ :=
  fun i => (L : ℤ) + (p.1 i).val - (p.2 i).val

def conductorPairVCoord (L : ℕ) (x : ℤ) (u : Fin (L + 1))
    (hx : |x| ≤ (L : ℤ)) : Fin (3 * L + 1) :=
  let z : ℤ := (L : ℤ) + (u.val : ℤ) - x
  ⟨z.toNat, Nat.lt_succ_of_le (by
    have hz0 : 0 ≤ z := by
      dsimp [z]
      have hhi : x ≤ (L : ℤ) := (abs_le.mp hx).2
      have hu0 : 0 ≤ (u.val : ℤ) := by exact_mod_cast Nat.zero_le u.val
      nlinarith
    have hzu : z ≤ (3 * L : ℤ) := by
      dsimp [z]
      have hlo : -(L : ℤ) ≤ x := (abs_le.mp hx).1
      have hu : (u.val : ℤ) ≤ (L : ℤ) := by
        exact_mod_cast (Nat.le_of_lt_succ u.isLt)
      nlinarith
    have hcast := Int.toNat_of_nonneg hz0
    have hnat : (z.toNat : ℤ) ≤ 3 * L := by
      rw [hcast]
      exact hzu
    exact_mod_cast hnat)⟩

theorem conductorPairVCoord_intCast (L : ℕ) (x : ℤ) (u : Fin (L + 1))
    (hx : |x| ≤ (L : ℤ)) :
    ((conductorPairVCoord L x u hx).val : ℤ) =
      (L : ℤ) + (u.val : ℤ) - x := by
  dsimp [conductorPairVCoord]
  have hz0 : 0 ≤ (L : ℤ) + (u.val : ℤ) - x := by
    have hhi : x ≤ (L : ℤ) := (abs_le.mp hx).2
    have hu0 : 0 ≤ (u.val : ℤ) := by exact_mod_cast Nat.zero_le u.val
    nlinarith
  rw [Int.toNat_of_nonneg hz0]

noncomputable def conductorPairFiberEquiv {I : Type*} [Fintype I] [DecidableEq I]
    (L : ℕ) (x : I → ℤ) (hx : ∀ i, |x i| ≤ (L : ℤ)) :
    {p : ConductorPairIndex I L // conductorPairDifference L p = x} ≃
      (I → Fin (L + 1)) where
  toFun p := p.1.1
  invFun u :=
    ⟨(u, fun i => conductorPairVCoord L (x i) (u i) (hx i)), by
      funext i
      simp [conductorPairDifference, conductorPairVCoord_intCast]⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext i
      apply Fin.ext
      have hp := congrFun p.2 i
      dsimp [conductorPairDifference] at hp
      have hv := conductorPairVCoord_intCast L (x i) (p.1.1 i) (hx i)
      have hp' :
          ((p.1.2 i).val : ℤ) =
            (L : ℤ) + (p.1.1 i).val - x i := by omega
      have hcast :
          ((conductorPairVCoord L (x i) (p.1.1 i) (hx i)).val : ℤ) =
            ((p.1.2 i).val : ℤ) := by rw [hv, hp']
      exact_mod_cast hcast
  right_inv u := rfl

theorem conductorPairFiber_card {I : Type*} [Fintype I] [DecidableEq I]
    (L : ℕ) (x : I → ℤ) (hx : ∀ i, |x i| ≤ (L : ℤ)) :
    Fintype.card {p : ConductorPairIndex I L // conductorPairDifference L p = x} =
      (L + 1) ^ Fintype.card I := by
  classical
  rw [Fintype.card_congr (conductorPairFiberEquiv L x hx)]
  simp

def conductorPairLiftMap {β I : Type*} (L : ℕ) (x : β → I → ℤ)
    (hx : ∀ a i, |x a i| ≤ (L : ℤ)) (a : β × (I → Fin (L + 1))) :
    ConductorPairIndex I L :=
  (a.2, fun i => conductorPairVCoord L (x a.1 i) (a.2 i) (hx a.1 i))

theorem conductorPairLiftMap_difference {β I : Type*} [DecidableEq I]
    (L : ℕ) (x : β → I → ℤ) (hx : ∀ a i, |x a i| ≤ (L : ℤ))
    (a : β × (I → Fin (L + 1))) :
    conductorPairDifference L (conductorPairLiftMap L x hx a) = x a.1 := by
  funext i
  simp [conductorPairDifference, conductorPairLiftMap,
    conductorPairVCoord_intCast]

theorem conductorPairLiftMap_injective {β I : Type*} [Fintype I] [DecidableEq I]
    (L : ℕ) (x : β → I → ℤ) (hx : ∀ a i, |x a i| ≤ (L : ℤ))
    (hinj : Function.Injective x) :
    Function.Injective (conductorPairLiftMap L x hx) := by
  intro a b hab
  have hdiff := congrArg (conductorPairDifference L) hab
  rw [conductorPairLiftMap_difference, conductorPairLiftMap_difference] at hdiff
  have hfirst : a.1 = b.1 := hinj hdiff
  have hsecond : a.2 = b.2 := congrArg Prod.fst hab
  exact Prod.ext hfirst hsecond

noncomputable def conductorPairLiftCoord {β I : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq β] (L : ℕ) (t : Finset β) (x : β → I → ℤ)
    (hx : ∀ a i, |x a i| ≤ (L : ℤ)) (b : β → ℂ) (M : ℝ)
    (p : ConductorPairIndex I L) : ℂ :=
  ∑ q ∈ t.product Finset.univ,
    if conductorPairLiftMap L x hx q = p then b q.1 / M else 0

noncomputable def conductorPairLiftVector {β I : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq β] (L : ℕ) (t : Finset β) (x : β → I → ℤ)
    (hx : ∀ a i, |x a i| ≤ (L : ℤ)) (b : β → ℂ) (M : ℝ) :
    EuclideanSpace ℂ (ConductorPairIndex I L) :=
  WithLp.toLp 2 (conductorPairLiftCoord L t x hx b M)

theorem conductorPairLiftCoord_on_map {β I : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq β] (L : ℕ) (t : Finset β) (x : β → I → ℤ)
    (hx : ∀ a i, |x a i| ≤ (L : ℤ)) (hinj : Function.Injective x)
    (b : β → ℂ) (M : ℝ) (q : β × (I → Fin (L + 1)))
    (hq : q ∈ t.product Finset.univ) :
    conductorPairLiftCoord L t x hx b M (conductorPairLiftMap L x hx q) =
      b q.1 / M := by
  classical
  unfold conductorPairLiftCoord
  rw [Finset.sum_eq_single q]
  · simp
  · intro q' hq' hne
    have hmaps : conductorPairLiftMap L x hx q' ≠
        conductorPairLiftMap L x hx q := fun he => hne (conductorPairLiftMap_injective L x hx hinj he)
    simp [hmaps]
  · intro hnot
    exact (hnot hq).elim

theorem conductorPairLiftCoord_eq_zero_of_not_mem_image {β I : Type*}
    [Fintype I] [DecidableEq I] [DecidableEq β] (L : ℕ) (t : Finset β)
    (x : β → I → ℤ) (hx : ∀ a i, |x a i| ≤ (L : ℤ)) (b : β → ℂ) (M : ℝ)
    (p : ConductorPairIndex I L) (hp : p ∉ (t.product Finset.univ).image
      (conductorPairLiftMap L x hx)) :
    conductorPairLiftCoord L t x hx b M p = 0 := by
  classical
  unfold conductorPairLiftCoord
  apply Finset.sum_eq_zero
  intro q hq
  have hne : conductorPairLiftMap L x hx q ≠ p := by
    intro he
    exact hp (Finset.mem_image.mpr ⟨q, hq, he⟩)
  simp [hne]

set_option maxHeartbeats 500000 in
theorem conductorPairLiftVector_norm_sq_le {β I : Type*} [Fintype I]
    [DecidableEq I] [DecidableEq β] (L : ℕ) (t : Finset β)
    (x : β → I → ℤ) (hx : ∀ a i, |x a i| ≤ (L : ℤ))
    (hinj : Function.Injective x) (b : β → ℂ) :
    ‖conductorPairLiftVector L t x hx b
        (((L + 1 : ℕ) : ℝ) ^ Fintype.card I)‖ ^ 2 ≤
      (((L + 1 : ℕ) : ℝ) ^ Fintype.card I)⁻¹ *
        ∑ a ∈ t, ‖b a‖ ^ 2 := by
  classical
  let M : ℝ := ((L + 1 : ℕ) : ℝ) ^ Fintype.card I
  let source : Finset (β × (I → Fin (L + 1))) := t.product Finset.univ
  let φ : β × (I → Fin (L + 1)) → ConductorPairIndex I L :=
    conductorPairLiftMap L x hx
  let c (q : β × (I → Fin (L + 1))) : ℂ := b q.1 / M
  let zf : ConductorPairIndex I L → ℂ := conductorPairLiftCoord L t x hx b M
  have hφ : Function.Injective φ := conductorPairLiftMap_injective L x hx hinj
  have hzval (q : β × (I → Fin (L + 1))) (hq : q ∈ source) :
      zf (φ q) = c q := by
    exact conductorPairLiftCoord_on_map L t x hx hinj b M q hq
  have hzzero (p : ConductorPairIndex I L) (hp : p ∉ source.image φ) :
      zf p = 0 := by
    exact conductorPairLiftCoord_eq_zero_of_not_mem_image L t x hx b M p hp
  have hnorm :
      ‖conductorPairLiftVector L t x hx b M‖ ^ 2 =
        ∑ p : ConductorPairIndex I L, ‖zf p‖ ^ 2 := by
    simp [conductorPairLiftVector, EuclideanSpace.norm_sq_eq, zf]
  have hsum :
      (∑ p : ConductorPairIndex I L, ‖zf p‖ ^ 2) =
        ∑ p ∈ source.image φ, ‖zf p‖ ^ 2 := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro p hp hpnot
    rw [hzzero p hpnot]
    simp
  have himage :
      (∑ p ∈ source.image φ, ‖zf p‖ ^ 2) =
        ∑ q ∈ source, ‖zf (φ q)‖ ^ 2 := by
    exact Finset.sum_image hφ.injOn
  have hsource :
      (∑ q ∈ source, ‖c q‖ ^ 2) =
        M⁻¹ * ∑ a ∈ t, ‖b a‖ ^ 2 := by
    have hMpos : 0 < M := by dsimp [M]; positivity
    have hnormdiv (a : β) : ‖b a / M‖ ^ 2 = ‖b a‖ ^ 2 / M ^ 2 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hMpos]
      ring
    dsimp [source, c]
    rw [Finset.sum_product]
    simp_rw [hnormdiv]
    have hcard : (Fintype.card (I → Fin (L + 1)) : ℝ) = M := by
      simp [M, Fintype.card_fun]
    have hsumconst (a : β) :
        (∑ u : I → Fin (L + 1), ‖b a‖ ^ 2 / M ^ 2) =
          M * (‖b a‖ ^ 2 / M ^ 2) := by
      calc
        _ = (Fintype.card (I → Fin (L + 1)) : ℝ) * (‖b a‖ ^ 2 / M ^ 2) := by simp
        _ = _ := by rw [hcard]
    calc
      _ = ∑ a ∈ t, M * (‖b a‖ ^ 2 / M ^ 2) := by
        apply Finset.sum_congr rfl
        intro a ha
        exact hsumconst a
      _ = ∑ a ∈ t, M⁻¹ * ‖b a‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro a ha
        have hMne : M ≠ 0 := ne_of_gt hMpos
        field_simp [hMne]
      _ = M⁻¹ * ∑ a ∈ t, ‖b a‖ ^ 2 := by rw [Finset.mul_sum]
  rw [hnorm, hsum, himage]
  calc
    _ = ∑ q ∈ source, ‖c q‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [hzval q hq]
    _ = M⁻¹ * ∑ a ∈ t, ‖b a‖ ^ 2 := hsource
    _ ≤ _ := by
      change M⁻¹ * ∑ a ∈ t, ‖b a‖ ^ 2 ≤
        M⁻¹ * ∑ a ∈ t, ‖b a‖ ^ 2
      exact le_rfl

set_option maxHeartbeats 500000 in
theorem conductorPairLiftVector_inner_eq {α β I : Type*} [Fintype I]
    [DecidableEq I] [DecidableEq β] (L : ℕ) (t : Finset β)
    (x : β → I → ℤ) (hx : ∀ a i, |x a i| ≤ (L : ℤ))
    (hinj : Function.Injective x) (b : β → ℂ) (θ : α → I → ℝ) (a : α) :
    inner ℂ (conductorPairFrequencyVector L (fun a i => -θ a i) a)
      (conductorPairLiftVector L t x hx b
        (((L + 1 : ℕ) : ℝ) ^ Fintype.card I)) =
      ∑ j ∈ t, b j * ∏ i : I, bvExp ((x j i : ℝ) * θ a i) := by
  classical
  let M : ℝ := ((L + 1 : ℕ) : ℝ) ^ Fintype.card I
  let source : Finset (β × (I → Fin (L + 1))) := t.product Finset.univ
  let φ : β × (I → Fin (L + 1)) → ConductorPairIndex I L :=
    conductorPairLiftMap L x hx
  let c : β × (I → Fin (L + 1)) → ℂ := fun q => b q.1 / M
  let zf : ConductorPairIndex I L → ℂ := conductorPairLiftCoord L t x hx b M
  have hφ : Function.Injective φ := conductorPairLiftMap_injective L x hx hinj
  have hzval (q : β × (I → Fin (L + 1))) (hq : q ∈ source) :
      zf (φ q) = c q :=
    conductorPairLiftCoord_on_map L t x hx hinj b M q hq
  have hzzero (p : ConductorPairIndex I L) (hp : p ∉ source.image φ) :
      zf p = 0 :=
    conductorPairLiftCoord_eq_zero_of_not_mem_image L t x hx b M p hp
  have hphase (q : β × (I → Fin (L + 1))) :
      conj (conductorPairFrequencyVector L (fun a i => -θ a i) a (φ q)) =
        ∏ i : I, bvExp ((x q.1 i : ℝ) * θ a i) := by
    simp only [conductorPairFrequencyVector, conductorPairLiftMap,
      WithLp.ofLp_toLp, map_prod, conj_bvExp]
    dsimp [φ, conductorPairLiftMap]
    apply Finset.prod_congr rfl
    intro i hi
    have hdi :
        (L : ℤ) + (q.2 i).val -
          (conductorPairVCoord L (x q.1 i) (q.2 i) (hx q.1 i)).val =
            x q.1 i := by
      simpa [conductorPairDifference, conductorPairLiftMap] using
        congrFun (conductorPairLiftMap_difference L x hx q) i
    have hcoord :
        (L : ℝ) + (q.2 i).val -
            (conductorPairVCoord L (x q.1 i) (q.2 i) (hx q.1 i)).val =
          (x q.1 i : ℝ) := by
      exact_mod_cast hdi
    rw [hcoord]
    congr 1
    ring
  have hinner :
      inner ℂ (conductorPairFrequencyVector L (fun a i => -θ a i) a)
        (conductorPairLiftVector L t x hx b M) =
          ∑ p : ConductorPairIndex I L,
            zf p * conj (conductorPairFrequencyVector L (fun a i => -θ a i) a p) := by
    simp [conductorPairLiftVector, conductorPairFrequencyVector, zf,
      PiLp.inner_apply, RCLike.inner_apply, WithLp.ofLp_toLp]
  have hinner' :
      inner ℂ (conductorPairFrequencyVector L (fun a i => -θ a i) a)
        (conductorPairLiftVector L t x hx b M) =
          ∑ p : ConductorPairIndex I L,
            conj (conductorPairFrequencyVector L (fun a i => -θ a i) a p) * zf p := by
    calc
      _ = ∑ p : ConductorPairIndex I L,
          zf p * conj (conductorPairFrequencyVector L (fun a i => -θ a i) a p) := hinner
      _ = _ := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [mul_comm]
  have hrestrict :
      (∑ p : ConductorPairIndex I L,
        conj (conductorPairFrequencyVector L (fun a i => -θ a i) a p) * zf p) =
        ∑ p ∈ source.image φ,
          conj (conductorPairFrequencyVector L (fun a i => -θ a i) a p) * zf p := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro p hp hpnot
    rw [hzzero p hpnot]
    simp
  have himage :
      (∑ p ∈ source.image φ,
        conj (conductorPairFrequencyVector L (fun a i => -θ a i) a p) * zf p) =
        ∑ q ∈ source,
          conj (conductorPairFrequencyVector L (fun a i => -θ a i) a (φ q)) *
            zf (φ q) := by
    exact Finset.sum_image hφ.injOn
  have hsource :
      (∑ q ∈ source,
        conj (conductorPairFrequencyVector L (fun a i => -θ a i) a (φ q)) *
          zf (φ q)) =
        ∑ j ∈ t, b j * ∏ i : I, bvExp ((x j i : ℝ) * θ a i) := by
    dsimp [source]
    rw [Finset.sum_product]
    simp_rw [hphase]
    have hcard : (Fintype.card (I → Fin (L + 1)) : ℂ) = (M : ℂ) := by
      exact_mod_cast (show (Fintype.card (I → Fin (L + 1)) : ℝ) = M by
        simp [M, Fintype.card_fun])
    have hpowC : ((L + 1 : ℕ) : ℂ) ^ Fintype.card I = (M : ℂ) := by
      simpa [Fintype.card_fun, Nat.cast_pow] using hcard
    calc
      _ = ∑ j ∈ t, ∑ u : I → Fin (L + 1),
          (∏ i : I, bvExp ((x j i : ℝ) * θ a i)) * (b j / M) := by
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro u hu
        have hmem : (j, u) ∈ t.product Finset.univ := Finset.mem_product.mpr ⟨hj, Finset.mem_univ _⟩
        rw [hzval (j, u) hmem]
      _ = ∑ j ∈ t, b j * ∏ i : I, bvExp ((x j i : ℝ) * θ a i) := by
        apply Finset.sum_congr rfl
        intro j hj
        simp only [Finset.sum_const]
        simp only [nsmul_eq_mul]
        rw [Finset.card_univ, hcard]
        have hMne : M ≠ 0 := by dsimp [M]; positivity
        field_simp [hMne]
  calc
    _ = ∑ p : ConductorPairIndex I L,
        conj (conductorPairFrequencyVector L (fun a i => -θ a i) a p) * zf p := hinner'
    _ = ∑ p ∈ source.image φ,
        conj (conductorPairFrequencyVector L (fun a i => -θ a i) a p) * zf p := hrestrict
    _ = ∑ q ∈ source,
        conj (conductorPairFrequencyVector L (fun a i => -θ a i) a (φ q)) *
          zf (φ q) := himage
    _ = ∑ j ∈ t, b j * ∏ i : I, bvExp ((x j i : ℝ) * θ a i) := hsource

set_option maxHeartbeats 500000 in
theorem conductorFiniteDimLargeSieve {α β I : Type*} [Fintype I]
    [DecidableEq I] [DecidableEq β] (s : Finset α) (θ : α → I → ℝ)
    (L D : ℕ) (hD : 0 < D)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ∃ k : I, ∀ m : ℤ,
      1 / (D : ℝ) ≤ |θ a k - θ b k - (m : ℝ)|)
    (t : Finset β) (x : β → I → ℤ)
    (hx : ∀ a i, |x a i| ≤ (L : ℤ)) (hinj : Function.Injective x)
    (b : β → ℂ) :
    (∑ a ∈ s, ‖∑ j ∈ t, b j * ∏ i : I,
      bvExp ((x j i : ℝ) * θ a i)‖ ^ 2) ≤
        (12 * (((L + 1 : ℕ) : ℝ) + 2 * D)) ^ Fintype.card I *
          ∑ j ∈ t, ‖b j‖ ^ 2 := by
  classical
  let θneg : α → I → ℝ := fun a i => -θ a i
  let M : ℝ := ((L + 1 : ℕ) : ℝ) ^ Fintype.card I
  let z := conductorPairLiftVector L t x hx b M
  have hsepneg : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ∃ k : I, ∀ m : ℤ,
      1 / (D : ℝ) ≤ |θneg a k - θneg b k - (m : ℝ)| := by
    intro a ha a' ha' haa'
    obtain ⟨k, hk⟩ := hsep a ha a' ha' haa'
    refine ⟨k, fun m => ?_⟩
    have h := hk (-m)
    have heq : θneg a k - θneg a' k - (m : ℝ) =
        -(θ a k - θ a' k - ((-m : ℤ) : ℝ)) := by
      dsimp [θneg]
      push_cast
      ring
    rw [heq, abs_neg]
    exact h
  have hgram := conductorPairFrequencyVector_gram s θneg L D hD hsepneg z
  have hlift := conductorPairLiftVector_norm_sq_le L t x hx hinj b
  have hMpos : 0 < M := by dsimp [M]; positivity
  have hsame (a : α) :
      ‖∑ j ∈ t, b j * ∏ i : I, bvExp ((x j i : ℝ) * θ a i)‖ =
        ‖inner ℂ (conductorPairFrequencyVector L θneg a) z‖ := by
    rw [conductorPairLiftVector_inner_eq L t x hx hinj b θ a]
  calc
    _ = ∑ a ∈ s, ‖inner ℂ (conductorPairFrequencyVector L θneg a) z‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [hsame]
    _ ≤ (12 * ((L + 1 : ℕ) : ℝ) *
          (((L + 1 : ℕ) : ℝ) + 2 * D)) ^ Fintype.card I * ‖z‖ ^ 2 := hgram
    _ ≤ (12 * ((L + 1 : ℕ) : ℝ) *
          (((L + 1 : ℕ) : ℝ) + 2 * D)) ^ Fintype.card I *
          (M⁻¹ * ∑ j ∈ t, ‖b j‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left hlift
      positivity
    _ = (12 * (((L + 1 : ℕ) : ℝ) + 2 * D)) ^ Fintype.card I *
          ∑ j ∈ t, ‖b j‖ ^ 2 := by
      let A : ℝ := ((L + 1 : ℕ) : ℝ)
      have hA : 0 < A := by dsimp [A]; positivity
      have hApow : A ^ Fintype.card I ≠ 0 := pow_ne_zero _ hA.ne'
      change (12 * A * (A + 2 * D)) ^ Fintype.card I *
          ((A ^ Fintype.card I)⁻¹ * ∑ j ∈ t, ‖b j‖ ^ 2) =
        (12 * (A + 2 * D)) ^ Fintype.card I * ∑ j ∈ t, ‖b j‖ ^ 2
      rw [mul_pow, mul_pow]
      field_simp [hApow]
      rw [← mul_pow]
      ring

theorem conductorGeometricSum_norm_sq_le (N : ℕ) (x : ℝ) :
    ‖∑ n ∈ Finset.range (N + 1), bvExp ((n : ℝ) * x)‖ ^ 2 ≤
      ((N + 1 : ℕ) : ℝ) ^ 2 := by
  have hsum : ‖∑ n ∈ Finset.range (N + 1), bvExp ((n : ℝ) * x)‖ ≤ N + 1 := by
    calc
      _ ≤ ∑ n ∈ Finset.range (N + 1), ‖bvExp ((n : ℝ) * x)‖ := norm_sum_le _ _
      _ = N + 1 := by simp
  have hsum' : ‖∑ n ∈ Finset.range (N + 1), bvExp ((n : ℝ) * x)‖ ≤
      ((N + 1 : ℕ) : ℝ) := by exact_mod_cast hsum
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hsum'

theorem conductorGeometricSum_norm_sq_le_of_centered_ne_zero (N : ℕ) (x : ℝ)
    (hx : bvCentered x ≠ 0) :
    ‖∑ n ∈ Finset.range (N + 1), bvExp ((n : ℝ) * x)‖ ^ 2 ≤
      1 / (4 * |bvCentered x| ^ 2) := by
  have hsum := exponential_sum_bound (N + 1) (abs_bvCentered_le x) hx
  rw [exponential_sum_centered] at hsum
  have hden : 0 ≤ 1 / (2 * |bvCentered x|) := by positivity
  calc
    _ ≤ (1 / (2 * |bvCentered x|)) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hden).2 hsum
    _ = 1 / (4 * |bvCentered x| ^ 2) := by ring

end ArtinPrimitiveRoots.Proofs.a2_cond_b
