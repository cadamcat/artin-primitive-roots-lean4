import ArtinPrimitiveRoots.Ext.TypeIIInputs

namespace ArtinPrimitiveRoots.Proofs.c_bins_sol

open Filter
open scoped Topology
open ArtinPrimitiveRoots.TypeII

/-- The reciprocal mass of a prime bin with its strictly excluded lower endpoint. -/
theorem reciprocal_prime_bin (γ γ' : ℝ) (hγ : 0 < γ) (hγγ' : γ < γ') :
    ∀ ρ : ℝ, 0 < ρ → ∃ x₀ : ℝ, 2 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        |(∑ n ∈ (primesUpTo (Real.rpow x γ')).filter
              (fun n : ℕ => Real.rpow x γ < (n : ℝ)),
            1 / ((n : ℝ) - 1)) - Real.log (γ' / γ)| ≤ ρ := by
  classical
  intro ρ hρ
  have hγ' : 0 < γ' := hγ.trans hγγ'
  obtain ⟨y₀, hy₀, hMertens⟩ :=
    ArtinPrimitiveRoots.Ext.TypeIIInputs.mertens.1 (ρ / 4) (by positivity)
  have hlarge : ∀ᶠ x : ℝ in atTop,
      max y₀ (max 4 (4 / ρ)) ≤ Real.rpow x γ :=
    (tendsto_rpow_atTop hγ).eventually (eventually_ge_atTop _)
  have hfinal : ∀ᶠ x : ℝ in atTop,
      |(∑ n ∈ (primesUpTo (Real.rpow x γ')).filter
            (fun n : ℕ => Real.rpow x γ < (n : ℝ)),
          1 / ((n : ℝ) - 1)) - Real.log (γ' / γ)| ≤ ρ := by
    filter_upwards [eventually_ge_atTop (2 : ℝ), hlarge] with x hx hxlarge
    let A := Real.rpow x γ
    let B := Real.rpow x γ'
    let Bin := (primesUpTo B).filter (fun n : ℕ => A < (n : ℝ))
    have hxpos : 0 < x := by linarith
    have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
    have hApos : 0 < A := Real.rpow_pos_of_pos hxpos γ
    have hBpos : 0 < B := Real.rpow_pos_of_pos hxpos γ'
    have hAB : A ≤ B := Real.rpow_le_rpow_of_exponent_le (by linarith) hγγ'.le
    have hyA : y₀ ≤ A := (le_max_left _ _).trans hxlarge
    have hA4 : 4 ≤ A := (le_max_left _ _).trans ((le_max_right _ _).trans hxlarge)
    have hAsmall : 4 / ρ ≤ A :=
      (le_max_right _ _).trans ((le_max_right _ _).trans hxlarge)
    have hmem (y : ℝ) (hy : 0 ≤ y) (n : ℕ) :
        n ∈ primesUpTo y ↔ n.Prime ∧ (n : ℝ) ≤ y := by
      simp only [primesUpTo, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff,
        Nat.le_floor_iff hy]
      exact and_comm
    have hlow : (primesUpTo B).filter (fun n : ℕ => ¬ A < (n : ℝ)) =
        primesUpTo A := by
      ext n
      simp only [Finset.mem_filter, hmem B hBpos.le, hmem A hApos.le, not_lt]
      constructor
      · rintro ⟨⟨hp, _⟩, hn⟩
        exact ⟨hp, hn⟩
      · rintro ⟨hp, hn⟩
        exact ⟨⟨hp, hn.trans hAB⟩, hn⟩
    have hbinSum : (∑ n ∈ Bin, 1 / (n : ℝ)) =
        (∑ n ∈ primesUpTo B, 1 / (n : ℝ)) -
          ∑ n ∈ primesUpTo A, 1 / (n : ℝ) := by
      have h := Finset.sum_filter_add_sum_filter_not (primesUpTo B)
        (fun n : ℕ => A < (n : ℝ)) (fun n : ℕ => 1 / (n : ℝ))
      rw [hlow] at h
      exact eq_sub_iff_add_eq.mpr h
    have hlogdiff : Real.log (Real.log B) - Real.log (Real.log A) =
        Real.log (γ' / γ) := by
      dsimp [A, B]
      rw [Real.log_rpow hxpos, Real.log_rpow hxpos,
        Real.log_mul hγ'.ne' hlogx.ne', Real.log_mul hγ.ne' hlogx.ne',
        Real.log_div hγ'.ne' hγ.ne']
      ring
    have hprimeErr : |(∑ n ∈ Bin, 1 / (n : ℝ)) - Real.log (γ' / γ)| ≤ ρ / 2 := by
      have hMA := abs_le.mp (hMertens A hyA)
      have hMB := abs_le.mp (hMertens B (hyA.trans hAB))
      rw [hbinSum, abs_le]
      constructor <;> linarith only [hMA.1, hMA.2, hMB.1, hMB.2, hlogdiff]
    let N := ⌊A⌋₊
    let U := ⌊B⌋₊
    have hNU : N ≤ U := Nat.floor_mono hAB
    have hN2 : 2 ≤ N := (Nat.le_floor_iff hApos.le).mpr (by norm_num; linarith)
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hUpos : 0 < (U : ℝ) := by exact_mod_cast (show 0 < U by omega)
    have hcorrNonneg (n : ℕ) (hn : 2 ≤ n) :
        0 ≤ 1 / ((n : ℝ) - 1) - 1 / (n : ℝ) := by
      have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
      exact sub_nonneg.mpr (one_div_le_one_div_of_le (by linarith) (by linarith))
    have hsub : Bin ⊆ Finset.Ico (N + 1) (U + 1) := by
      intro n hn
      obtain ⟨hnB, hnA⟩ := Finset.mem_filter.mp hn
      have hnU : n < U + 1 :=
        Finset.mem_range.mp (Finset.mem_filter.mp hnB).1
      have hNn : N < n := (Nat.floor_lt hApos.le).mpr hnA
      exact Finset.mem_Ico.mpr ⟨by omega, hnU⟩
    have htel : (∑ n ∈ Finset.Ico (N + 1) (U + 1),
        (1 / ((n : ℝ) - 1) - 1 / (n : ℝ))) = 1 / (N : ℝ) - 1 / (U : ℝ) := by
      have h := Finset.sum_Ico_sub (fun n : ℕ => -(1 / ((n : ℝ) - 1)))
        (Nat.add_le_add_right hNU 1)
      simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, neg_sub_neg] using h
    have hCorrection : 0 ≤ (∑ n ∈ Bin, (1 / ((n : ℝ) - 1) - 1 / (n : ℝ))) ∧
        (∑ n ∈ Bin, (1 / ((n : ℝ) - 1) - 1 / (n : ℝ))) ≤ ρ / 2 := by
      have hle : (∑ n ∈ Bin, (1 / ((n : ℝ) - 1) - 1 / (n : ℝ))) ≤
          ∑ n ∈ Finset.Ico (N + 1) (U + 1),
            (1 / ((n : ℝ) - 1) - 1 / (n : ℝ)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro n hn _
        exact hcorrNonneg n (by have := (Finset.mem_Ico.mp hn).1; omega)
      have hNhalf : A / 2 ≤ (N : ℝ) := by
        have hf : A < (N : ℝ) + 1 := Nat.lt_floor_add_one A
        linarith only [hf, hA4]
      have hInv : 1 / (N : ℝ) ≤ 2 / A := by
        calc
          1 / (N : ℝ) ≤ 1 / (A / 2) :=
            one_div_le_one_div_of_le (by positivity) hNhalf
          _ = 2 / A := by rw [div_div_eq_mul_div, one_mul]
      have hsmall : 2 / A ≤ ρ / 2 := by
        have h := (div_le_iff₀ hρ).mp hAsmall
        apply (div_le_iff₀ hApos).mpr
        nlinarith only [h]
      constructor
      · apply Finset.sum_nonneg
        intro n hn
        exact hcorrNonneg n (by have := (Finset.mem_Ico.mp (hsub hn)).1; omega)
      · calc
          _ ≤ 1 / (N : ℝ) - 1 / (U : ℝ) := hle.trans_eq htel
          _ ≤ 1 / (N : ℝ) := sub_le_self _ (by positivity)
          _ ≤ 2 / A := hInv
          _ ≤ ρ / 2 := hsmall
    have hreplace : (∑ n ∈ Bin, 1 / ((n : ℝ) - 1)) =
        (∑ n ∈ Bin, 1 / (n : ℝ)) +
          ∑ n ∈ Bin, (1 / ((n : ℝ) - 1) - 1 / (n : ℝ)) := by
      rw [Finset.sum_sub_distrib]
      ring
    change |(∑ n ∈ Bin, 1 / ((n : ℝ) - 1)) - Real.log (γ' / γ)| ≤ ρ
    rw [hreplace, abs_le]
    have hprimeBounds := abs_le.mp hprimeErr
    constructor <;>
      linarith only [hprimeBounds.1, hprimeBounds.2, hCorrection.1, hCorrection.2]
  obtain ⟨X, hX⟩ := eventually_atTop.mp hfinal
  refine ⟨max 2 X, le_max_left _ _, ?_⟩
  intro x hx
  exact hX x ((le_max_right _ _).trans hx)

end ArtinPrimitiveRoots.Proofs.c_bins_sol
