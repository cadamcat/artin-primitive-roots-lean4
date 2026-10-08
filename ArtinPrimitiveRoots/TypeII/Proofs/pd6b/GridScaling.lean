import ArtinPrimitiveRoots.TypeII.PD.Physical

set_option autoImplicit false
namespace ArtinPrimitiveRoots.TypeII.PD

theorem gridMesh_cube_exp (x ε : ℝ) (hx : 0 < x) :
    (Real.rpow x (-ε)) ^ 3 = Real.exp (-3 * ε * Real.log x) := by
  have hp : Real.rpow x (-ε) = Real.exp (Real.log x * (-ε)) := Real.rpow_def_of_pos hx _
  rw [hp, ← Real.exp_nat_mul]
  congr 1
  norm_num
  ring

theorem gridBoundary_scale_exp (x ε v : ℝ) (hx : 0 < x) :
    (3 * (Real.exp v * Real.rpow x (2 * ε))) * (Real.rpow x (-ε)) ^ 3 =
      3 * Real.exp (v - ε * Real.log x) := by
  have hp : Real.rpow x (2 * ε) = Real.exp (Real.log x * (2 * ε)) := Real.rpow_def_of_pos hx _
  rw [gridMesh_cube_exp x ε hx, hp]
  calc
    _ = 3 * Real.exp (v + Real.log x * (2 * ε) + (-3 * ε * Real.log x)) := by
      simp only [Real.exp_add]
      ring
    _ = _ := by congr 2 <;> ring

theorem gridResidue_scale_exp (x ε c Cr U V : ℝ) (hx : 0 < x) :
    (475 / (Real.rpow x (-ε)) ^ 3) * (Cr * U * V * Real.rpow x (-c)) =
      475 * Cr * U * V * Real.exp (-(c - 3 * ε) * Real.log x) := by
  have hp : Real.rpow x (-c) = Real.exp (Real.log x * (-c)) := Real.rpow_def_of_pos hx _
  rw [gridMesh_cube_exp x ε hx, hp, div_eq_mul_inv, ← Real.exp_neg]
  calc
    _ = 475 * Cr * U * V * Real.exp (-(-3 * ε * Real.log x) + Real.log x * (-c)) := by
      rw [Real.exp_add]
      ring
    _ = _ := by congr 2 <;> ring

end ArtinPrimitiveRoots.TypeII.PD
