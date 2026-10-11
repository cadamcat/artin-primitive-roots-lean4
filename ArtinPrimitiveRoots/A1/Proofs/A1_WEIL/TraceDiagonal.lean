import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.RationalData
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.RingTheory.Trace.Basic

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Diagonalize the genuine nondegenerate rational trace form.
Uses: traceForm_nondegenerate; equivalent_weightedSumSquares_units_of_nondegenerate. -/
theorem quadratic_trace_diagonal_exists (a : Fˣ) : Nonempty (QuadraticTraceDiagonal a) := by
  let m : F →ₗ[ℚ] F := LinearMap.mul ℚ F (a : F)
  let B : LinearMap.BilinForm ℚ F := (Algebra.traceForm ℚ F).compLeft m
  have htrace : (Algebra.traceForm ℚ F).SeparatingLeft :=
    (traceForm_nondegenerate ℚ F).1
  have hB : B.SeparatingLeft := by
    intro x hx
    have hx' : m x = 0 := htrace (m x) (by
      intro y
      simpa [B, LinearMap.BilinForm.compLeft_apply] using hx y)
    change (a : F) * x = 0 at hx'
    exact (mul_eq_zero.mp hx').resolve_left (Units.ne_zero a)
  have hsym : B.IsSymm := by
    refine ⟨fun x y => ?_⟩
    simp only [B, LinearMap.BilinForm.compLeft_apply, m, Algebra.traceForm_apply]
    congr 1
    change (a : F) * x * y = (a : F) * y * x
    ring
  let Q : QuadraticForm ℚ F := B.toQuadraticMap
  have hQval (x : F) : Q x = Algebra.trace ℚ F ((a : F) * x ^ 2) := by
    simp only [Q, LinearMap.BilinMap.toQuadraticMap_apply, B,
      LinearMap.BilinForm.compLeft_apply, m, Algebra.traceForm_apply]
    congr 1
    change (a : F) * x * x = (a : F) * x ^ 2
    ring
  have hQassoc : QuadraticMap.associated (R := ℚ) Q = B := by
    simpa [Q] using QuadraticMap.associated_left_inverse ℚ hsym.1
  have hQ : (QuadraticMap.associated (R := ℚ) Q).SeparatingLeft := by
    rw [hQassoc]
    exact hB
  obtain ⟨w, hequiv⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate' hQ
  obtain ⟨e⟩ := hequiv
  let n := Module.finrank ℚ F
  let b : Module.Basis (Fin n) ℚ F := (Pi.basisFun ℚ (Fin n)).map e.symm
  have hb (x : F) : b.repr x = e x := by
    ext i
    change (e.toLinearEquiv x) i = (e.toLinearEquiv x) i
    rfl
  refine ⟨⟨b, w, ?_⟩⟩
  intro x
  calc
    Algebra.trace ℚ F ((a : F) * x ^ 2) = Q x := (hQval x).symm
    _ = QuadraticMap.weightedSumSquares ℚ w (e x) := (e.map_app x).symm
    _ = ∑ i, (w i : ℚ) * (b.repr x i) ^ 2 := by
      rw [QuadraticMap.weightedSumSquares_apply]
      rw [hb x]
      simp [Units.smul_def, pow_two]

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
