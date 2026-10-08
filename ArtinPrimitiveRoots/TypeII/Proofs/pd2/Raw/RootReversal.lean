import ArtinPrimitiveRoots.TypeII.Proofs.pd2.Raw.RootGraph

namespace ArtinPrimitiveRoots.TypeII.PD
set_option maxHeartbeats 1000000

lemma pd2a_root_completion_strict (u v : ℕ) (hu : 2 ≤ u) (hv : 2 ≤ v) (c d : ℤ)
    (hdet : (u : ℤ) * d - (v : ℤ) * c = 1) (hc₀ : 0 ≤ c) (hcu : c < u) :
    0 < c ∧ 0 < d ∧ d < v := by
  have huZ : (2 : ℤ) ≤ u := by exact_mod_cast hu
  have hvZ : (2 : ℤ) ≤ v := by exact_mod_cast hv
  have hc1 : c ≤ (u : ℤ) - 1 := by omega
  have hd0 : 0 < d := by nlinarith
  have hdv : d < v := by
    have hmul := mul_le_mul_of_nonneg_left hc1 (show (0 : ℤ) ≤ v by omega)
    nlinarith
  have hcpos : 0 < c := by
    by_contra hn
    have hzero : c = 0 := by omega
    rw [hzero, mul_zero, sub_zero] at hdet
    have hdiv : (u : ℤ) ∣ 1 := ⟨d, hdet.symm⟩
    have huOne : u ∣ 1 := by exact_mod_cast hdiv
    have heq := Nat.dvd_one.mp huOne
    omega
  exact ⟨hcpos, hd0, hdv⟩

lemma pd2a_root_reversal_identity (u v : ℕ) (hu : 0 < u) (hv : 0 < v) (c d : ℤ)
    (hdet : (u : ℤ) * d - (v : ℤ) * c = 1) :
    (d : ℝ) / v - (c : ℝ) / u = 1 / ((u : ℝ) * v) := by
  have huR : (u : ℝ) ≠ 0 := by exact_mod_cast hu.ne'
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
  have hdetR : (u : ℝ) * (d : ℝ) - (v : ℝ) * (c : ℝ) = 1 := by exact_mod_cast hdet
  field_simp
  nlinarith only [hdetR]

lemma pd2a_root_reversal_shift (u v : ℕ) (U V : ℝ) (hU : 0 < U) (hV : 0 < V)
    (hu : U ≤ (u : ℝ)) (hv : V ≤ (v : ℝ)) (c d : ℤ)
    (hdet : (u : ℤ) * d - (v : ℤ) * c = 1) :
    0 < (d : ℝ) / v - (c : ℝ) / u ∧ (d : ℝ) / v - (c : ℝ) / u ≤ 1 / (U * V) := by
  have huR : 0 < (u : ℝ) := hU.trans_le hu
  have hvR : 0 < (v : ℝ) := hV.trans_le hv
  have huN : 0 < u := by exact_mod_cast huR
  have hvN : 0 < v := by exact_mod_cast hvR
  rw [pd2a_root_reversal_identity u v huN hvN c d hdet]
  exact ⟨by positivity, one_div_le_one_div_of_le (mul_pos hU hV)
    (mul_le_mul hu hv hV.le huR.le)⟩

end ArtinPrimitiveRoots.TypeII.PD
