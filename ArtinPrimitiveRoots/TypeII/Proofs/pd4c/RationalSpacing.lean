import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.Circle

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD

noncomputable section

/-- A reduced rational approximation separates distinct phases in a half-denominator block. -/
theorem rational_block_spacing (c : ℤ) (d : ℕ) (hd : 2 ≤ d)
    (hcop : Int.gcd c (d : ℤ) = 1) (θ : ℝ)
    (happrox : |θ - (c : ℝ) / (d : ℝ)| ≤ 1 / (d : ℝ)^2)
    (n m : ℤ) (hne : n ≠ m)
    (hblock : |((n - m : ℤ) : ℝ)| ≤ (d : ℝ)/2) :
    1 / (2*(d : ℝ)) ≤ circleDistance (((n - m : ℤ) : ℝ)*θ) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hdne : (d : ℝ) ≠ 0 := hdpos.ne'
  have hnm : n - m ≠ 0 := sub_ne_zero.mpr hne
  have hnum (k : ℤ) : (n - m) * c - k * (d : ℤ) ≠ 0 := by
    intro hz
    have hprod : (n - m) * c = k * (d : ℤ) := sub_eq_zero.mp hz
    have hdiv : (d : ℤ) ∣ n - m := by
      refine ⟨k * Int.gcdA c (d : ℤ) + (n - m) * Int.gcdB c (d : ℤ), ?_⟩
      calc
        n - m = (n - m) * (c * Int.gcdA c (d : ℤ) +
            (d : ℤ) * Int.gcdB c (d : ℤ)) := by
          rw [← Int.gcd_eq_gcd_ab c (d : ℤ), hcop]
          simp
        _ = ((n - m) * c) * Int.gcdA c (d : ℤ) +
            (d : ℤ) * ((n - m) * Int.gcdB c (d : ℤ)) := by ring
        _ = _ := by rw [hprod]; ring
    obtain ⟨t, ht⟩ := hdiv
    have htne : t ≠ 0 := by
      intro ht0
      exact hnm (by simpa only [ht0, mul_zero] using ht)
    have htone : (1 : ℤ) ≤ |t| := by
      have h := abs_pos.mpr htne
      omega
    have htoneR : (1 : ℝ) ≤ |(t : ℝ)| := by exact_mod_cast htone
    have htR : ((n - m : ℤ) : ℝ) = (d : ℝ) * (t : ℝ) := by exact_mod_cast ht
    have hlarge : (d : ℝ) ≤ |((n - m : ℤ) : ℝ)| := by
      rw [htR, abs_mul, abs_of_pos hdpos]
      exact le_mul_of_one_le_right hdpos.le htoneR
    linarith
  have hdist (k : ℤ) :
      1 / (d : ℝ) ≤ |((n - m : ℤ) : ℝ) * (c : ℝ) / (d : ℝ) - (k : ℝ)| := by
    let e := (n - m) * c - k * (d : ℤ)
    have heone : (1 : ℤ) ≤ |e| := by
      have h := abs_pos.mpr (hnum k)
      change 0 < |e| at h
      omega
    have heoneR : (1 : ℝ) ≤ |(e : ℝ)| := by exact_mod_cast heone
    have heR : (e : ℝ) = ((n - m : ℤ) : ℝ) * (c : ℝ) - (k : ℝ) * (d : ℝ) := by
      dsimp only [e]
      push_cast <;> rfl
    calc
      _ ≤ |(e : ℝ)| / (d : ℝ) := div_le_div_of_nonneg_right heoneR hdpos.le
      _ = _ := by
        have heq : (e : ℝ) / (d : ℝ) =
            ((n - m : ℤ) : ℝ) * (c : ℝ) / (d : ℝ) - (k : ℝ) := by
          rw [heR]
          field_simp [hdne] <;> ring
        rw [← heq, abs_div, abs_of_pos hdpos]
  have hrat : 1 / (d : ℝ) ≤
      circleDistance (((n - m : ℤ) : ℝ) * (c : ℝ) / (d : ℝ)) := by
    rw [pd4c_circleDistance_eq_round]
    exact hdist _
  have herr : |((n - m : ℤ) : ℝ) * θ -
      ((n - m : ℤ) : ℝ) * (c : ℝ) / (d : ℝ)| ≤ 1 / (2 * (d : ℝ)) := by
    calc
      _ = |((n - m : ℤ) : ℝ)| * |θ - (c : ℝ) / (d : ℝ)| := by
        rw [← abs_mul]
        congr 1
        ring
      _ ≤ ((d : ℝ) / 2) * (1 / (d : ℝ)^2) :=
        mul_le_mul hblock happrox (abs_nonneg _) (by positivity)
      _ = _ := by field_simp [hdne] <;> ring
  have htri := pd4c_circleDistance_lipschitz
    (((n - m : ℤ) : ℝ) * (c : ℝ) / (d : ℝ)) (((n - m : ℤ) : ℝ) * θ)
  rw [abs_sub_comm] at htri
  have hhalf : 1 / (d : ℝ) = 2 * (1 / (2 * (d : ℝ))) := by field_simp [hdne]
  linarith

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
