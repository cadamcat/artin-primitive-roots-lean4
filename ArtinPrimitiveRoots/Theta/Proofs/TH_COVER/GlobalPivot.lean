import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

set_option autoImplicit false
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.th_cover_sol

variable {K E : Type} [Field K] [Field E]

/-- The nonzero second-row entry used by the rational Kubota section. -/
def secondRow (g : GL (Fin 2) K) : K :=
  if (g : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 then
    (g : Matrix (Fin 2) (Fin 2) K) 1 0
  else (g : Matrix (Fin 2) (Fin 2) K) 1 1

theorem secondRow_ne_zero (g : GL (Fin 2) K) : secondRow g ≠ 0 := by
  unfold secondRow
  split_ifs with h
  · exact h
  · intro h11
    have h10 : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by simpa using h
    apply g.det_ne_zero
    rw [Matrix.det_fin_two]
    simp [h10, h11]

def secondRowUnit (g : GL (Fin 2) K) : Kˣ :=
  Units.mk0 (secondRow g) (secondRow_ne_zero g)

theorem map_secondRowUnit (f : K →+* E) (g : GL (Fin 2) K) :
    Units.map f.toMonoidHom (secondRowUnit g) =
      secondRowUnit (Matrix.GeneralLinearGroup.map f g) := by
  apply Units.ext
  change f (secondRow g) = secondRow (Matrix.GeneralLinearGroup.map f g)
  unfold secondRow
  simp only [Matrix.GeneralLinearGroup.map_apply]
  by_cases h : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  · simp [h]
  · have hf : f ((g : Matrix (Fin 2) (Fin 2) K) 1 0) ≠ 0 := by
      intro hz
      apply h
      exact f.injective (hz.trans f.map_zero.symm)
    simp [h, hf]

end ArtinPrimitiveRoots.Proofs.th_cover_sol
