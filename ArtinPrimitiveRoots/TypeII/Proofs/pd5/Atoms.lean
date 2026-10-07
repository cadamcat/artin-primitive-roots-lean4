import ArtinPrimitiveRoots.TypeII.PD.Memory

set_option autoImplicit false
set_option linter.unusedVariables false

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical
open Filter
open ArtinPrimitiveRoots.TypeII

noncomputable section

theorem pd5_bandMass_lower_eventually {K : ℕ} (a : Fin K → ℝ)
    (ha : ValidBands K a) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → ∀ i : Fin K,
      Real.log 2 / 2 ≤ bandMass x (a i) := by
  classical
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK : 0 < K := ha.1
  have hindex : (Finset.univ : Finset (Fin K)).Nonempty := by
    rw [Finset.univ_nonempty_iff]
    exact ⟨⟨0, by omega⟩⟩
  have hmass : ∀ i : Fin K, ∃ x₀ : ℝ, 2 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x → Real.log 2 / 2 ≤ bandMass x (a i) := by
    intro i
    have hai := ha.2.1 i
    obtain ⟨x₀, hx₀, hbound⟩ :=
      band_mass (a i) (by linarith [hai.1]) (by linarith [hai.2])
        (Real.log 2 / 2) (by positivity)
    refine ⟨x₀, hx₀, ?_⟩
    intro x hx
    have habs := (hbound x hx).1
    have := abs_le.mp habs
    linarith
  choose t ht using hmass
  let T := Finset.univ.sup' hindex t
  refine ⟨max 2 T, le_max_left _ _, ?_⟩
  intro x hx i
  have hti : t i ≤ T := by
    dsimp [T]
    exact Finset.le_sup' t (Finset.mem_univ i)
  have hTx : T ≤ max 2 T := le_max_right _ _
  exact (ht i).2 x (hti.trans (hTx.trans hx))

theorem pd5_memoryEta_bounds {x q_d : ℝ} (hqd0 : 0 < q_d) (hqd1 : q_d < 1)
    (j : ℕ) : 0 ≤ memoryEta x q_d j ∧ memoryEta x q_d j ≤ 1 := by
  unfold memoryEta memoryQ
  split_ifs
  · have hsqrt0 : 0 ≤ Real.sqrt q_d := Real.sqrt_nonneg _
    have hsqrt2 : (Real.sqrt q_d) ^ 2 = q_d := Real.sq_sqrt (le_of_lt hqd0)
    constructor <;> nlinarith
  · constructor <;> linarith

theorem pd5_memoryBPrime_lower {x q_d : ℝ} (hqd0 : 0 < q_d) (hqd1 : q_d < 1)
    (p : ℕ) :
    memoryBPrime x q_d p ≥ 1 - ((pathLength x + 1 : ℕ) : ℝ) / ((p : ℝ) + 1) := by
  have hp : 0 < (p : ℝ) + 1 := by positivity
  have hsum :
      (∑ j ∈ Finset.range (pathLength x + 1),
          memoryEta x q_d j / ((p : ℝ) + 1)) ≤
        ((pathLength x + 1 : ℕ) : ℝ) / ((p : ℝ) + 1) := by
    calc
      (∑ j ∈ Finset.range (pathLength x + 1),
          memoryEta x q_d j / ((p : ℝ) + 1)) ≤
          ∑ j ∈ Finset.range (pathLength x + 1), (1 : ℝ) / ((p : ℝ) + 1) := by
            apply Finset.sum_le_sum
            intro j hj
            exact div_le_div_of_nonneg_right
              (pd5_memoryEta_bounds hqd0 hqd1 j).2 hp.le
      _ = ((pathLength x + 1 : ℕ) : ℝ) / ((p : ℝ) + 1) := by
        simp [div_eq_mul_inv]
  unfold memoryBPrime
  linarith

theorem pd5_memoryNu_bound_of_path_small {x q_d : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (hqd0 : 0 < q_d) (hqd1 : q_d < 1) (i : Fin K) (p : ℕ)
    (hmass : 0 < bandMass x (a i))
    (hpath : ((pathLength x + 1 : ℕ) : ℝ) ≤ ((p : ℝ) + 1) / 2) :
    memoryNu x K a q_d i p ≤ 2 / (bandMass x (a i) * ((p : ℝ) + 1)) := by
  have hp : 0 < (p : ℝ) + 1 := by positivity
  have hprime : memoryBPrime x q_d p ≥ 1 / 2 := by
    have := pd5_memoryBPrime_lower (x := x) hqd0 hqd1 p
    have hfrac : ((pathLength x + 1 : ℕ) : ℝ) / ((p : ℝ) + 1) ≤ 1 / 2 := by
      rw [div_le_iff₀ hp]
      nlinarith
    linarith
  have hbprime : 0 < memoryBPrime x q_d p := by linarith
  have hM : 0 < bandMass x (a i) * ((p : ℝ) + 1) := mul_pos hmass hp
  have hD : 0 < bandMass x (a i) * ((p : ℝ) + 1) * memoryBPrime x q_d p :=
    mul_pos hM hbprime
  rw [memoryNu]
  apply (div_le_div_iff₀ hD hM).2
  norm_num
  nlinarith [hprime, hM]

private theorem pd5_pathLength_linear_bound {x : ℝ} (hL : 1 ≤ Real.log x) :
    ((pathLength x + 1 : ℕ) : ℝ) ≤ 4 * Real.log x := by
  have hpow : Real.rpow (Real.log x) (1 / 2 : ℝ) ≤ Real.log x := by
    calc
      Real.rpow (Real.log x) (1 / 2 : ℝ) ≤ Real.rpow (Real.log x) 1 :=
        Real.rpow_le_rpow_of_exponent_le (x := Real.log x) hL (by norm_num)
      _ = Real.log x := Real.rpow_one _
  have hceil : (momentR x : ℝ) <
      Real.rpow (Real.log x) (1 / 2 : ℝ) / 2 + 1 := by
    unfold momentR
    exact Nat.ceil_lt_add_one
      (div_nonneg (Real.rpow_nonneg (by linarith [hL]) _) (by norm_num))
  have hpath :
      ((pathLength x + 1 : ℕ) : ℝ) = 2 * (momentR x : ℝ) + 1 := by
    simp [pathLength]
  rw [hpath]
  nlinarith

theorem pd5_pathLength_exponential_small :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      ((pathLength x + 1 : ℕ) : ℝ) ≤
        Real.exp (Real.rpow (Real.log x) (1 / 10 : ℝ)) / 2 := by
  have hu : Tendsto (fun x : ℝ => Real.rpow x (1 / 10 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hratio : Tendsto
      (fun x : ℝ =>
        Real.exp (Real.rpow (Real.log x) (1 / 10 : ℝ)) /
          (Real.rpow (Real.log x) (1 / 10 : ℝ)) ^ (10 : ℕ)) atTop atTop :=
    (Real.tendsto_exp_div_pow_atTop 10).comp (hu.comp Real.tendsto_log_atTop)
  have hlog := (Filter.tendsto_atTop.1 Real.tendsto_log_atTop) 1
  have hlarge := (Filter.tendsto_atTop.1 hratio) 8
  have hP : ∀ᶠ x : ℝ in atTop,
      2 ≤ x ∧ ((pathLength x + 1 : ℕ) : ℝ) ≤
        Real.exp (Real.rpow (Real.log x) (1 / 10 : ℝ)) / 2 := by
    filter_upwards [eventually_ge_atTop (2 : ℝ), hlog, hlarge] with x hx2 hxL hxratio
    have hLpos : 0 < Real.log x := by linarith
    have hpow :
        (Real.rpow (Real.log x) (1 / 10 : ℝ)) ^ (10 : ℕ) = Real.log x := by
      calc
        (Real.rpow (Real.log x) (1 / 10 : ℝ)) ^ (10 : ℕ) =
            Real.rpow (Real.rpow (Real.log x) (1 / 10 : ℝ)) (10 : ℝ) :=
          (Real.rpow_natCast _ _).symm
        _ = Real.rpow (Real.log x) ((1 / 10 : ℝ) * 10) :=
          (Real.rpow_mul (le_of_lt hLpos) _ _).symm
        _ = Real.log x := by norm_num [Real.rpow_one]
    rw [hpow] at hxratio
    have hbig : 8 * Real.log x ≤
        Real.exp (Real.rpow (Real.log x) (1 / 10 : ℝ)) :=
      (le_div_iff₀ hLpos).mp hxratio
    refine ⟨hx2, ?_⟩
    have hsmall := pd5_pathLength_linear_bound hxL
    nlinarith
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1 hP
  refine ⟨x₀, (hx₀ x₀ le_rfl).1, ?_⟩
  intro x hx
  exact (hx₀ x hx).2

theorem pd5_memoryNu_exponential_atom_bound {K : ℕ} (a : Fin K → ℝ)
    (ha : ValidBands K a) {q_d : ℝ} (hqd0 : 0 < q_d) (hqd1 : q_d < 1) :
    ∃ C x₀ : ℝ, 0 < C ∧ 2 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x → ∀ i : Fin K, ∀ p : ℕ,
        p ∈ primeBand x (a i) →
          memoryNu x K a q_d i p ≤
            C * Real.exp (-(Real.rpow (Real.log x) (1 / 10 : ℝ))) := by
  obtain ⟨xB, hxB, hBandMass⟩ := pd5_bandMass_lower_eventually a ha
  obtain ⟨xP, hxP, hPath⟩ := pd5_pathLength_exponential_small
  let x₀ := max xB (max xP (Real.exp 1))
  have hx₀ : 2 ≤ x₀ := by
    dsimp [x₀]
    exact le_trans hxB (le_max_left _ _)
  have hxB₀ : xB ≤ x₀ := le_max_left _ _
  have hxP₀ : xP ≤ x₀ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hexp₀ : Real.exp 1 ≤ x₀ := le_trans (le_max_right _ _) (le_max_right _ _)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨4 / Real.log 2, x₀, by positivity, hx₀, ?_⟩
  intro x hx i p hp
  have hxB' := hBandMass x (hxB₀.trans hx) i
  have hxPath := hPath x (hxP₀.trans hx)
  have hL : 1 ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 1) (hexp₀.trans hx)
    simpa using this
  have hBandLower :
      Real.exp (Real.rpow (Real.log x) (1 / 10 : ℝ)) ≤ (p : ℝ) := by
    have hpLower := (Finset.mem_filter.mp hp).2.2.1
    have hrpow : Real.rpow (Real.log x) (1 / 10 : ℝ) ≤
        Real.rpow (Real.log x) (a i) := by
      apply Real.rpow_le_rpow_of_exponent_le hL
      linarith [(ha.2.1 i).1]
    exact (Real.exp_le_exp.mpr hrpow).trans hpLower
  have hpathSmall :
      ((pathLength x + 1 : ℕ) : ℝ) ≤ ((p : ℝ) + 1) / 2 := by
    nlinarith [hxPath]
  have hmass : 0 < bandMass x (a i) := by
    have := hBandMass x (hxB₀.trans hx) i
    exact lt_of_lt_of_le (by positivity) this
  have hNu := pd5_memoryNu_bound_of_path_small hqd0 hqd1 i p hmass hpathSmall
  have hM : 0 < bandMass x (a i) * ((p : ℝ) + 1) :=
    mul_pos hmass (by positivity)
  have hu : 0 < Real.rpow (Real.log x) (1 / 10 : ℝ) :=
    Real.rpow_pos_of_pos (by linarith) _
  have hfactor :
      (Real.log 2 / 2) * Real.exp (Real.rpow (Real.log x) (1 / 10 : ℝ)) ≤
        bandMass x (a i) * ((p : ℝ) + 1) := by
    apply mul_le_mul hxB' (by linarith [hBandLower]) (by positivity) (by positivity)
  have hdiv :
      2 / (bandMass x (a i) * ((p : ℝ) + 1)) ≤
        4 / (Real.log 2 * Real.exp (Real.rpow (Real.log x) (1 / 10 : ℝ))) := by
    apply (div_le_div_iff₀ hM (mul_pos hlog2 (Real.exp_pos _))).2
    nlinarith [hfactor]
  have hrewrite :
      4 / (Real.log 2 * Real.exp (Real.rpow (Real.log x) (1 / 10 : ℝ))) =
        (4 / Real.log 2) *
          Real.exp (-(Real.rpow (Real.log x) (1 / 10 : ℝ))) := by
    rw [Real.exp_neg]
    field_simp [ne_of_gt hlog2, ne_of_gt (Real.exp_pos (Real.rpow (Real.log x) (1 / 10 : ℝ)))]
  calc
    memoryNu x K a q_d i p ≤ 2 / (bandMass x (a i) * ((p : ℝ) + 1)) := hNu
    _ ≤ 4 / (Real.log 2 * Real.exp (Real.rpow (Real.log x) (1 / 10 : ℝ))) := hdiv
    _ = (4 / Real.log 2) *
        Real.exp (-(Real.rpow (Real.log x) (1 / 10 : ℝ))) := hrewrite

theorem pd5_memoryNu_mass_le_two {x q_d : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (hqd0 : 0 < q_d) (hqd1 : q_d < 1) (i : Fin K)
    (hmass : 0 < bandMass x (a i))
    (hpath : ∀ p ∈ primeBand x (a i),
      ((pathLength x + 1 : ℕ) : ℝ) ≤ ((p : ℝ) + 1) / 2) :
    (∑ p ∈ primeBand x (a i), memoryNu x K a q_d i p) ≤ 2 := by
  have hpoint :
      (∑ p ∈ primeBand x (a i), memoryNu x K a q_d i p) ≤
        ∑ p ∈ primeBand x (a i),
          2 / (bandMass x (a i) * ((p : ℝ) + 1)) := by
    apply Finset.sum_le_sum
    intro p hp
    exact pd5_memoryNu_bound_of_path_small hqd0 hqd1 i p hmass (hpath p hp)
  have hdenoms :
      (∑ p ∈ primeBand x (a i),
          2 / (bandMass x (a i) * ((p : ℝ) + 1))) ≤
        ∑ p ∈ primeBand x (a i), 2 / (bandMass x (a i) * (p : ℝ)) := by
    apply Finset.sum_le_sum
    intro p hp
    have hprime : p.Prime := (Finset.mem_filter.mp hp).2.1
    have hp0 : 0 < (p : ℝ) := by exact_mod_cast hprime.pos
    have hM0 : 0 < bandMass x (a i) := hmass
    apply (div_le_div_iff₀
      (mul_pos hM0 (by positivity : 0 < (p : ℝ) + 1))
      (mul_pos hM0 hp0)).2
    nlinarith
  have hsum :
      (∑ p ∈ primeBand x (a i),
          2 / (bandMass x (a i) * (p : ℝ))) = 2 := by
    have hMsum : 0 < (∑ p ∈ primeBand x (a i), 1 / (p : ℝ)) := by
      simpa [bandMass] using hmass
    have heq :
        (∑ p ∈ primeBand x (a i),
            2 / (bandMass x (a i) * (p : ℝ))) =
          (2 / bandMass x (a i)) *
            (∑ p ∈ primeBand x (a i), 1 / (p : ℝ)) := by
      calc
        _ = ∑ p ∈ primeBand x (a i),
              (2 / bandMass x (a i)) * (1 / (p : ℝ)) := by
                apply Finset.sum_congr rfl
                intro p hp
                have hprime : p.Prime := (Finset.mem_filter.mp hp).2.1
                have hp0 : (p : ℝ) ≠ 0 := by
                  exact_mod_cast hprime.ne_zero
                field_simp [ne_of_gt hmass, hp0]
                ring
        _ = _ := by rw [← Finset.mul_sum]
    rw [heq]
    simp only [bandMass]
    field_simp [ne_of_gt hMsum]
    ring
  linarith [hpoint, hdenoms, hsum]

end

end ArtinPrimitiveRoots.TypeII.PD
