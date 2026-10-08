import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.ErrorDecay

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace ArtinPrimitiveRoots.TypeII.PD

/-- The polynomial pad loss and the noncoprime comparison loss are smaller than every log power. -/
theorem padError_logPowerDecay (A Er Em Cr Cm Cn E : ℝ)
    (hCr : 0 < Cr) (hCm : 0 < Cm) (hCn : 0 ≤ Cn) (hE : 0 < E) :
    ∃ CA L₀ : ℝ, 0 < CA ∧ 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
      ∀ X Y : ℝ, 0 < X → 0 < Y →
        (E * Real.rpow L (2 / 100 : ℝ) * Real.exp (-Real.rpow L (1 / 10 : ℝ))) *
            (Cr * X * Y * Real.rpow L Er + Cm * X * Y * Real.rpow L Em) +
          Cn * X * Y * Real.rpow L Em * Real.exp (-Real.rpow L (1 / 10 : ℝ)) ≤
            CA * X * Y * Real.rpow L (-A) := by
  let B := max (Er + 2 / 100) (Em + 2 / 100)
  let CA := E * (Cr + Cm) + Cn
  have hCA : 0 < CA := by dsimp [CA]; positivity
  obtain ⟨L₀, hL₀, hdecay⟩ := modelError_logPowerDecay A B 1 (1 / 10 : ℝ) (by norm_num) (by norm_num)
  refine ⟨CA, L₀, hCA, hL₀, ?_⟩
  intro L hL X Y hX hY
  have hLone : 1 ≤ L := hL₀.trans hL
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hLone
  have hEr : (2 / 100 : ℝ) + Er ≤ B := by dsimp [B]; linarith [le_max_left (Er + 2 / 100) (Em + 2 / 100)]
  have hEm : (2 / 100 : ℝ) + Em ≤ B := by dsimp [B]; linarith [le_max_right (Er + 2 / 100) (Em + 2 / 100)]
  have hEm' : Em ≤ B := by linarith
  have hraw : Real.rpow L (2 / 100 : ℝ) * Real.rpow L Er ≤ Real.rpow L B := by
    calc
      _ = Real.rpow L ((2 / 100 : ℝ) + Er) := (Real.rpow_add hLpos _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hLone hEr
  have hcomp : Real.rpow L (2 / 100 : ℝ) * Real.rpow L Em ≤ Real.rpow L B := by
    calc
      _ = Real.rpow L ((2 / 100 : ℝ) + Em) := (Real.rpow_add hLpos _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hLone hEm
  have hcoll : Real.rpow L Em ≤ Real.rpow L B := Real.rpow_le_rpow_of_exponent_le hLone hEm'
  let g := Real.exp (-Real.rpow L (1 / 10 : ℝ))
  have hrg : (Real.rpow L (2 / 100 : ℝ) * Real.rpow L Er) * g ≤ Real.rpow L B * g := mul_le_mul_of_nonneg_right hraw (Real.exp_pos _).le
  have hcg : (Real.rpow L (2 / 100 : ℝ) * Real.rpow L Em) * g ≤ Real.rpow L B * g := mul_le_mul_of_nonneg_right hcomp (Real.exp_pos _).le
  have hng : Real.rpow L Em * g ≤ Real.rpow L B * g := mul_le_mul_of_nonneg_right hcoll (Real.exp_pos _).le
  have hfirst := mul_le_mul_of_nonneg_left hrg (by positivity : 0 ≤ E * Cr * X * Y)
  have hsecond := mul_le_mul_of_nonneg_left hcg (by positivity : 0 ≤ E * Cm * X * Y)
  have hthird := mul_le_mul_of_nonneg_left hng (by positivity : 0 ≤ Cn * X * Y)
  have hbound : (E * Real.rpow L (2 / 100 : ℝ) * g) *
      (Cr * X * Y * Real.rpow L Er + Cm * X * Y * Real.rpow L Em) +
      Cn * X * Y * Real.rpow L Em * g ≤ CA * X * Y * (Real.rpow L B * g) := by
    have hs := add_le_add (add_le_add hfirst hsecond) hthird
    dsimp only [CA, g]
    convert hs using 1 <;> ring
  apply hbound.trans
  have hd := hdecay L hL
  have hd' : Real.rpow L B * g ≤ Real.rpow L (-A) := by simpa only [neg_one_mul] using hd
  exact mul_le_mul_of_nonneg_left hd' (by positivity)

end ArtinPrimitiveRoots.TypeII.PD
