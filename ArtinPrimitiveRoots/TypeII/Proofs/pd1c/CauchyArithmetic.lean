import ArtinPrimitiveRoots.TypeII.PD.Defs

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical ArtinPrimitiveRoots.TypeII

lemma pd1c_dyadicScale_log_bounds {x : ℝ} {K : ℕ} {Y : ℝ}
    (hY : Y ∈ dyadicScales x K) :
    (1 / 20 : ℝ) * Real.rpow (Real.log x) (1 / 10 : ℝ) ≤ Real.log Y ∧
      Real.log Y ≤ ((K + 1 : ℕ) : ℝ) * Real.rpow (Real.log x) (1 / 5 : ℝ) := by
  simp only [dyadicScales, Finset.mem_filter] at hY
  exact hY.2

lemma pd1c_cauchy_arithmetic
    {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {ta tb : Fin K → ℕ}
    (hta : IsMarkedPrimeTuple x K a ta) (htb : IsMarkedPrimeTuple x K a tb)
    (hc : Nat.Coprime (tupleProduct ta) (tupleProduct tb))
    {m n r s : ℕ} (hmn : 1 ≤ m * n) (hrs : 1 ≤ r * s) :
    ((∃ h : ℕ, m * n - 1 = tupleProduct ta * h ∧
        r * s - 1 = tupleProduct tb * h) ↔
      ((tupleProduct tb : ℕ) : ℤ) * (m : ℤ) * (n : ℤ) -
        ((tupleProduct ta : ℕ) : ℤ) * (r : ℤ) * (s : ℤ) =
          (tupleProduct tb : ℤ) - (tupleProduct ta : ℤ)) := by
  let aa := tupleProduct ta
  let bb := tupleProduct tb
  have haa : 0 < aa := by
    dsimp [aa, tupleProduct]
    apply Finset.prod_pos
    intro i hi
    have hp : (ta i).Prime := by
      have hmem : ta i ∈ primeBand x (a i) := hta i
      change ta i ∈ (Finset.range
        (⌊Real.exp (2 * Real.rpow (Real.log x) (a i))⌋₊ + 1)).filter
        (fun p : ℕ => p.Prime ∧ Real.exp (Real.rpow (Real.log x) (a i)) ≤ (p : ℝ) ∧
          (p : ℝ) ≤ Real.exp (2 * Real.rpow (Real.log x) (a i))) at hmem
      exact (Finset.mem_filter.mp hmem).2.1
    exact hp.pos
  have hbb : 0 < bb := by
    dsimp [bb, tupleProduct]
    apply Finset.prod_pos
    intro i hi
    have hp : (tb i).Prime := by
      have hmem : tb i ∈ primeBand x (a i) := htb i
      change tb i ∈ (Finset.range
        (⌊Real.exp (2 * Real.rpow (Real.log x) (a i))⌋₊ + 1)).filter
        (fun p : ℕ => p.Prime ∧ Real.exp (Real.rpow (Real.log x) (a i)) ≤ (p : ℝ) ∧
          (p : ℝ) ≤ Real.exp (2 * Real.rpow (Real.log x) (a i))) at hmem
      exact (Finset.mem_filter.mp hmem).2.1
    exact hp.pos
  have hmnCast : ((m * n - 1 : ℕ) : ℤ) = (m : ℤ) * (n : ℤ) - 1 := by
    rw [Nat.cast_sub hmn]
    push_cast
    norm_num
  have hrsCast : ((r * s - 1 : ℕ) : ℤ) = (r : ℤ) * (s : ℤ) - 1 := by
    rw [Nat.cast_sub hrs]
    push_cast
    norm_num
  constructor
  · rintro ⟨h, hm, hr⟩
    have hmI : (m : ℤ) * (n : ℤ) - 1 = (aa : ℤ) * (h : ℤ) := by
      rw [← hmnCast]
      exact_mod_cast hm
    have hrI : (r : ℤ) * (s : ℤ) - 1 = (bb : ℤ) * (h : ℤ) := by
      rw [← hrsCast]
      exact_mod_cast hr
    change (bb : ℤ) * (m : ℤ) * (n : ℤ) -
      (aa : ℤ) * (r : ℤ) * (s : ℤ) = (bb : ℤ) - (aa : ℤ)
    nlinarith [hmI, hrI]
  · intro hEq
    have hEq' : (bb : ℤ) * ((m * n - 1 : ℕ) : ℤ) =
        (aa : ℤ) * ((r * s - 1 : ℕ) : ℤ) := by
      rw [hmnCast, hrsCast]
      change (bb : ℤ) * (m : ℤ) * (n : ℤ) -
        (aa : ℤ) * (r : ℤ) * (s : ℤ) = (bb : ℤ) - (aa : ℤ) at hEq
      nlinarith [hEq]
    have hNat : bb * (m * n - 1) = aa * (r * s - 1) := by
      exact_mod_cast hEq'
    have hAdiv : aa ∣ m * n - 1 := by
      apply (hc.dvd_mul_left).mp
      exact ⟨r * s - 1, hNat⟩
    have hBdiv : bb ∣ r * s - 1 := by
      apply (hc.symm.dvd_mul_left).mp
      exact ⟨m * n - 1, hNat.symm⟩
    obtain ⟨u, hu⟩ := hAdiv
    obtain ⟨v, hv⟩ := hBdiv
    have huv : bb * u = bb * v := by
      nlinarith [hNat, hu, hv]
    have huv' : u = v := Nat.mul_left_cancel hbb huv
    refine ⟨u, hu, ?_⟩
    simpa [huv'] using hv

end ArtinPrimitiveRoots.TypeII.PD
