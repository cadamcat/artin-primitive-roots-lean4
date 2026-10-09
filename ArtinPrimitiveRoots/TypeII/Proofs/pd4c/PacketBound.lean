import Mathlib

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

noncomputable section

/-- The exact half-denominator block count admits a symmetric real envelope. -/
theorem half_denominator_packet_bound (d M N : ℕ) (hd : 2 ≤ d)
    (S : ℝ) (hS : 1 ≤ S) :
    (((M/(d/2)+1 : ℕ) : ℝ)*((N : ℝ)+32*(d : ℝ)*S)) ≤
    96*((M : ℝ)*(N : ℝ)/(d : ℝ)+((M : ℝ)+(N : ℝ))*S+(d : ℝ)*S) := by
  let q := d/2
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hq : d ≤ 3*q := by dsimp only [q]; omega
  have hfloor : (M/q)*q ≤ M := Nat.div_mul_le_self M q
  have hprod : (M/q)*d ≤ 3*M := by
    calc
      _ ≤ (M/q)*(3*q) := Nat.mul_le_mul_left _ hq
      _ = 3*((M/q)*q) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hfloor
  have hprodR : ((M/q : ℕ) : ℝ)*(d : ℝ) ≤ 3*(M : ℝ) := by exact_mod_cast hprod
  have hcount : ((M/q+1 : ℕ) : ℝ) ≤ 3*(M : ℝ)/(d : ℝ)+1 := by
    calc
      _ ≤ (3*(M : ℝ)+(d : ℝ))/(d : ℝ) := by
        apply (le_div_iff₀ hdpos).mpr
        push_cast
        nlinarith only [hprodR]
      _ = _ := by field_simp [hdpos.ne'] <;> ring
  have hS0 : 0 ≤ S := le_trans (by norm_num) hS
  have hN : (N : ℝ) ≤ (N : ℝ)*S :=
    le_mul_of_one_le_right (by positivity) hS
  have hMN0 : 0 ≤ (M : ℝ)*(N : ℝ)/(d : ℝ) := by positivity
  have hNS0 : 0 ≤ (N : ℝ)*S := by positivity
  have hDS0 : 0 ≤ (d : ℝ)*S := by positivity
  have hexpand : (3*(M : ℝ)/(d : ℝ)+1)*((N : ℝ)+32*(d : ℝ)*S) =
      3*(M : ℝ)*(N : ℝ)/(d : ℝ)+(N : ℝ)+96*(M : ℝ)*S+32*(d : ℝ)*S := by
    field_simp [hdpos.ne'] <;> ring
  calc
    _ ≤ (3*(M : ℝ)/(d : ℝ)+1)*((N : ℝ)+32*(d : ℝ)*S) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = _ := hexpand
    _ ≤ _ := by
      apply sub_nonneg.mp
      have hdiff : 0 ≤ (N : ℝ)*S-(N : ℝ) := sub_nonneg.mpr hN
      calc
        0 ≤ 93*((M : ℝ)*(N : ℝ)/(d : ℝ))+95*((N : ℝ)*S)+
            ((N : ℝ)*S-(N : ℝ))+64*((d : ℝ)*S) := by positivity
        _ = _ := by ring

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
