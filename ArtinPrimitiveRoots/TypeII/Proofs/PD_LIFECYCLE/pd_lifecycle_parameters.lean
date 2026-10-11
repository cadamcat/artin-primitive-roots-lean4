import ArtinPrimitiveRoots.TypeII.Proofs.PD_LIFECYCLE.Defs

set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical Filter
open ArtinPrimitiveRoots.TypeII
noncomputable section

private theorem pdLifeBPrime_half_of_large_x {K : ℕ} (F : PDFix K) (hF : F.Valid) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → ∀ p ∈ markedPrimes x K F.a,
      (1 / 2 : ℝ) ≤ memoryBPrime x F.q_d p := by
  rcases hF with ⟨hBands, hqd, hqdlt, _, _, _⟩
  have hy : Filter.Tendsto (fun x : ℝ => Real.rpow (Real.log x) (1 / 10 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop
  have hratio : Filter.Tendsto
      (fun x : ℝ => Real.exp (Real.rpow (Real.log x) (1 / 10 : ℝ)) /
        (Real.rpow (Real.log x) (1 / 10 : ℝ)) ^ (5 : ℝ)) atTop atTop :=
    (tendsto_exp_div_rpow_atTop 5).comp hy
  obtain ⟨xE, hxE⟩ := Filter.eventually_atTop.1
    ((Filter.tendsto_atTop.1 hratio) (3 : ℝ))
  obtain ⟨xY, hxY⟩ := Filter.eventually_atTop.1
    ((Filter.tendsto_atTop.1 hy) (2 : ℝ))
  let x₀ := max 2 (max xE (max xY (Real.exp 1)))
  have h₂ : 2 ≤ x₀ := by dsimp [x₀]; exact le_max_left _ _
  refine ⟨x₀, h₂, ?_⟩
  intro x hx p hp
  have hxE₀ : xE ≤ x₀ := by
    dsimp [x₀]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hxY₀ : xY ≤ x₀ := by
    dsimp [x₀]
    exact le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))
  have hexp₀ : Real.exp 1 ≤ x₀ := by
    dsimp [x₀]
    exact le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))
  have hxE' : xE ≤ x := hxE₀.trans hx
  have hxY' : xY ≤ x := hxY₀.trans hx
  have hexp' : Real.exp 1 ≤ x := hexp₀.trans hx
  have hL : 1 ≤ Real.log x := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hexp'
  let y := Real.rpow (Real.log x) (1 / 10 : ℝ)
  have hyx : 2 ≤ y := by simpa [y] using hxY x hxY'
  have hrx : 3 ≤ Real.exp y / y ^ (5 : ℝ) := by simpa [y] using hxE x hxE'
  rcases Finset.mem_biUnion.mp hp with ⟨i, _, hpi⟩
  have hband := (Finset.mem_filter.mp hpi).2.2.1
  have hai : (1 / 10 : ℝ) < F.a i := hBands.2.1 i |>.1
  have hlow : y ≤ Real.rpow (Real.log x) (F.a i) :=
    Real.rpow_le_rpow_of_exponent_le hL hai.le
  have hpLower : Real.exp y ≤ (p : ℝ) :=
    (Real.exp_le_exp.mpr hlow).trans hband
  have hypos : 0 < y := lt_of_lt_of_le (by norm_num) hyx
  have hy5pos : 0 < y ^ (5 : ℝ) := Real.rpow_pos_of_pos hypos _
  have hExpLower : 3 * y ^ (5 : ℝ) ≤ Real.exp y :=
    (le_div_iff₀ hy5pos).mp hrx
  have hy5ge : (32 : ℝ) ≤ y ^ (5 : ℝ) := by
    calc
      32 = (2 : ℝ) ^ (5 : ℕ) := by norm_num
      _ ≤ y ^ (5 : ℕ) := by gcongr
      _ = y ^ (5 : ℝ) := (Real.rpow_natCast y 5).symm
  have hN : (pathLength x : ℝ) < y ^ (5 : ℝ) + 2 := by
    have hceil :
        (⌈Real.rpow (Real.log x) (1 / 2 : ℝ) / 2⌉₊ : ℝ) <
          Real.rpow (Real.log x) (1 / 2 : ℝ) / 2 + 1 :=
      Nat.ceil_lt_add_one (div_nonneg (Real.rpow_nonneg (by linarith [hL]) _) (by norm_num))
    have hceil2 :
        (2 : ℝ) * (⌈Real.rpow (Real.log x) (1 / 2 : ℝ) / 2⌉₊ : ℝ) <
          Real.rpow (Real.log x) (1 / 2 : ℝ) + 2 := by
      have hmul := mul_lt_mul_of_pos_left hceil (by norm_num : (0 : ℝ) < 2)
      nlinarith
    have hpath : (pathLength x : ℝ) < Real.rpow (Real.log x) (1 / 2 : ℝ) + 2 := by
      dsimp [pathLength, momentR]
      push_cast
      exact hceil2
    have hy5 : y ^ (5 : ℝ) = Real.rpow (Real.log x) (1 / 2 : ℝ) := by
      dsimp [y]
      rw [← Real.rpow_mul (by linarith [hL]) (1 / 10 : ℝ) (5 : ℝ)]
      norm_num
    simpa [hy5] using hpath
  have hpDouble : 2 * ((pathLength x + 1 : ℕ) : ℝ) < (p : ℝ) := by
    have hp3 : 3 * y ^ (5 : ℝ) ≤ (p : ℝ) := le_trans hExpLower hpLower
    have hNatCast : ((pathLength x + 1 : ℕ) : ℝ) = (pathLength x : ℝ) + 1 := by simp
    have hNplus : ((pathLength x + 1 : ℕ) : ℝ) < y ^ (5 : ℝ) + 3 := by
      rw [hNatCast]
      linarith [hN]
    have hpGap : 2 * (y ^ (5 : ℝ) + 3) ≤ 3 * y ^ (5 : ℝ) := by nlinarith [hy5ge]
    calc
      _ < 2 * (y ^ (5 : ℝ) + 3) := by nlinarith [hNplus]
      _ ≤ 3 * y ^ (5 : ℝ) := hpGap
      _ ≤ (p : ℝ) := hp3
  have heta (j : ℕ) : memoryEta x F.q_d j ≤ 1 := by
    simp only [memoryEta, memoryQ]
    split_ifs <;> linarith [Real.sqrt_nonneg F.q_d]
  have hsum :
      (∑ j ∈ Finset.range (pathLength x + 1), memoryEta x F.q_d j) ≤
        ((pathLength x + 1 : ℕ) : ℝ) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (pathLength x + 1), (1 : ℝ) :=
        Finset.sum_le_sum fun j _ => heta j
      _ = ((pathLength x + 1 : ℕ) : ℝ) := by simp
  have hpplus : 0 < (p : ℝ) + 1 := by positivity
  have hratio' : ((pathLength x + 1 : ℕ) : ℝ) / ((p : ℝ) + 1) < 1 / 2 := by
    apply (div_lt_iff₀ hpplus).2
    nlinarith [hpDouble]
  have hquot :
      (∑ j ∈ Finset.range (pathLength x + 1), memoryEta x F.q_d j) /
          ((p : ℝ) + 1) < 1 / 2 := by
    calc
      _ ≤ ((pathLength x + 1 : ℕ) : ℝ) / ((p : ℝ) + 1) :=
        div_le_div_of_nonneg_right hsum hpplus.le
      _ < 1 / 2 := hratio'
  unfold memoryBPrime
  rw [← Finset.sum_div]
  linarith

private theorem pdLifeBandMass_bounds {K : ℕ} (F : PDFix K) (hF : F.Valid) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → ∀ i : Fin K,
      0 < bandMass x (F.a i) ∧ bandMass x (F.a i) ≤ 2 * Real.log 2 := by
  classical
  let x_i : Fin K → ℝ := fun i =>
    Classical.choose (band_mass (F.a i)
      (lt_trans (by norm_num : (0 : ℝ) < 1 / 10) (hF.1.2.1 i).1)
      (lt_trans (hF.1.2.1 i).2 (by norm_num))
      (Real.log 2) (Real.log_pos (by norm_num)))
  have hx_i : ∀ i : Fin K,
      2 ≤ x_i i ∧ ∀ x : ℝ, x_i i ≤ x →
        |bandMass x (F.a i) - Real.log 2| ≤ Real.log 2 ∧
          0 < bandMass x (F.a i) := by
    intro i
    exact Classical.choose_spec (band_mass (F.a i)
      (lt_trans (by norm_num : (0 : ℝ) < 1 / 10) (hF.1.2.1 i).1)
      (lt_trans (hF.1.2.1 i).2 (by norm_num))
      (Real.log 2) (Real.log_pos (by norm_num)))
  let x₀ : ℝ := 2 + ∑ i : Fin K, x_i i
  have hx₀ : 2 ≤ x₀ := by
    dsimp [x₀]
    have hsum : 0 ≤ ∑ i : Fin K, x_i i :=
      Finset.sum_nonneg fun i hi => by linarith [(hx_i i).1]
    linarith
  refine ⟨x₀, hx₀, ?_⟩
  intro x hx i
  have hsingle : x_i i ≤ ∑ j : Fin K, x_i j :=
    Finset.single_le_sum (s := Finset.univ) (f := x_i)
      (fun j hj => by linarith [(hx_i j).1]) (Finset.mem_univ i)
  have hxi : x_i i ≤ x₀ := by dsimp [x₀]; linarith
  have hmass := (hx_i i).2 x (le_trans hxi hx)
  constructor
  · exact hmass.2
  · have hupper := (abs_le.mp hmass.1).2
    linarith

/-- Positive, bounded band masses, disjoint bands, and b-prime denominators at large x.
Uses band_mass and
large-x separation of ValidBands; feeds all lifespan normalization and bounds. -/
theorem pd_lifecycle_parameters (K : ℕ) (F : PDFix K) (hF : F.Valid) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      (∀ i : Fin K, 0 < bandMass x (F.a i) ∧ bandMass x (F.a i) ≤ 2 * Real.log 2) ∧
      (∀ i i' : Fin K, i ≠ i' → Disjoint (primeBand x (F.a i)) (primeBand x (F.a i'))) ∧
      (∀ p ∈ markedPrimes x K F.a, (1 / 2 : ℝ) ≤ memoryBPrime x F.q_d p) := by
  obtain ⟨xV, hxV, hMass⟩ := pdLifeBandMass_bounds F hF
  obtain ⟨xB, hxB, hB⟩ := pdLifeBPrime_half_of_large_x F hF
  obtain ⟨xSep, hxSep, hSep⟩ := pd1c_eventual_bands_separated K F.a hF.1
  let x₀ := max xV (max xB xSep)
  have hx₀ : 2 ≤ x₀ := by
    dsimp [x₀]
    exact le_trans hxV (le_max_left _ _)
  refine ⟨x₀, hx₀, ?_⟩
  intro x hx
  have hxV' : xV ≤ x := (le_max_left xV (max xB xSep)).trans hx
  have hxB' : xB ≤ x :=
    (le_max_left xB xSep).trans ((le_max_right xV (max xB xSep)).trans hx)
  have hxSep' : xSep ≤ x :=
    (le_max_right xB xSep).trans ((le_max_right xV (max xB xSep)).trans hx)
  refine ⟨hMass x hxV', ?_, hB x hxB'⟩
  intro i i' hii'
  exact (hSep x hxSep').1 i i' hii'

end
end ArtinPrimitiveRoots.TypeII.PD
