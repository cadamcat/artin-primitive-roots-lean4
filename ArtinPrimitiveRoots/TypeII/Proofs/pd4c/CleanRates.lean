import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

/-- Combine the minor-rectangle rate and collision error at one exponential scale. -/
theorem clean_minor_collision_rate_le (L A C : ℝ) (hL : 1 ≤ L) (hC : 0 ≤ C) :
    C*(Real.rpow L ((1/5 : ℝ)-A)+
      Real.rpow L (1/5 : ℝ)*Real.exp (-(1/200 : ℝ)*Real.rpow L (1/10 : ℝ)))+
      (1+(Real.rpow L A)^3)*Real.exp (-Real.rpow L (1/10 : ℝ)) ≤
    (C+2)*(Real.rpow L ((1/5 : ℝ)-A)+
      Real.rpow L (max (1/5 : ℝ) (3*A))*
        Real.exp (-(1/200 : ℝ)*Real.rpow L (1/10 : ℝ))) := by
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  let P := max (1/5 : ℝ) (3*A)
  let E := Real.exp (-(1/200 : ℝ)*Real.rpow L (1/10 : ℝ))
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hP0 : 0 ≤ P := (by norm_num : (0 : ℝ) ≤ 1/5).trans (le_max_left _ _)
  have hOne : 1 ≤ Real.rpow L P := Real.one_le_rpow hL hP0
  have hMinor : Real.rpow L (1/5 : ℝ) ≤ Real.rpow L P :=
    Real.rpow_le_rpow_of_exponent_le hL (le_max_left _ _)
  have hCube : (Real.rpow L A)^3 = Real.rpow L (3*A) := by
    calc
      _ = Real.rpow (Real.rpow L A) (3 : ℝ) := (Real.rpow_natCast _ 3).symm
      _ = Real.rpow L (A*3) := (Real.rpow_mul hLpos.le _ _).symm
      _ = _ := by congr 1; ring
  have hCubeBound : (Real.rpow L A)^3 ≤ Real.rpow L P := by
    rw [hCube]
    exact Real.rpow_le_rpow_of_exponent_le hL (le_max_right _ _)
  have hMemory : 1+(Real.rpow L A)^3 ≤ 2*Real.rpow L P := by
    linarith only [hOne, hCubeBound]
  have ht : 0 ≤ Real.rpow L (1/10 : ℝ) := Real.rpow_nonneg hLpos.le _
  have hExp : Real.exp (-Real.rpow L (1/10 : ℝ)) ≤ E := by
    apply Real.exp_le_exp.mpr
    nlinarith only [ht]
  have hCollision : (1+(Real.rpow L A)^3)*Real.exp (-Real.rpow L (1/10 : ℝ)) ≤
      (2*Real.rpow L P)*E := by
    exact mul_le_mul hMemory hExp (Real.exp_pos _).le (by positivity)
  have hMinorRate : Real.rpow L (1/5 : ℝ)*E ≤ Real.rpow L P*E :=
    mul_le_mul_of_nonneg_right hMinor hE
  have hX : 0 ≤ Real.rpow L ((1/5 : ℝ)-A) := Real.rpow_nonneg hLpos.le _
  change C*(Real.rpow L ((1/5 : ℝ)-A)+Real.rpow L (1/5 : ℝ)*E)+
    (1+(Real.rpow L A)^3)*Real.exp (-Real.rpow L (1/10 : ℝ)) ≤
    (C+2)*(Real.rpow L ((1/5 : ℝ)-A)+Real.rpow L P*E)
  calc
    _ ≤ C*(Real.rpow L ((1/5 : ℝ)-A)+Real.rpow L P*E)+(2*Real.rpow L P)*E :=
      add_le_add (mul_le_mul_of_nonneg_left (add_le_add (le_refl _) hMinorRate) hC)
        hCollision
    _ ≤ _ := by nlinarith only [hX]

end ArtinPrimitiveRoots.Proofs.pd4d_sol
