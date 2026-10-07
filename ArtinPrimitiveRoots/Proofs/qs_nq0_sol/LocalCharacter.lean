import ArtinPrimitiveRoots.Proofs.qs_nq0_sol.Generators
import ArtinPrimitiveRoots.A1.Characters

/-!
# Local quadratic characters for the narrow family

Read the cubed Hilbert symbol through the fixed complex embedding. The
algebraic local character is quadratic because the Hilbert value is a sixth
root of unity. Continuity and global descent are subsequent steps.

The remaining intermediate statements, in this module's context, are:
```
theorem qs_nq0_quadratic_local_continuous (D : FieldData K) (H : HilbertData K)
    (v : FinPlace K) (a : (v.adicCompletion K)ˣ) :
    Continuous (qsNQQuadraticLocal D H v a)

theorem qs_nq0_quadratic_character_exists (D : FieldData K) (H : HilbertData K)
    (a : Kˣ) :
    ∃ χ : HeckeChar K, χ ^ 2 = 1 ∧
      (∀ (w : InfinitePlace K) (u : w.Completionˣ), χ.locInf w u = 1) ∧
      (∀ v : FinPlace K, χ.loc v = qsNQQuadraticLocal D H v (toLoc v a))
```
-/

set_option autoImplicit false

open scoped NumberField
open ArtinPrimitiveRoots.A1

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]

/-- The cubed Hilbert character at one finite place, read through `D.σ0`. -/
def qsNQQuadraticLocal (D : FieldData K) (H : HilbertData K)
    (v : FinPlace K) (a : (v.adicCompletion K)ˣ) :
    (v.adicCompletion K)ˣ →* ℂˣ :=
  (powMonoidHom 3 : ℂˣ →* ℂˣ).comp
    ((Units.map D.σ0.toMonoidHom).comp
      ((rootsOfUnity 6 K).subtype.comp
        (MonoidHom.mk' (fun u => H.hilb v a u) (fun u u' => H.mul_right v a u u'))))

/-- Cubing a sextic Hilbert character gives a character whose square is trivial. -/
theorem qs_nq0_quadratic_local_square (D : FieldData K) (H : HilbertData K)
    (v : FinPlace K) (a : (v.adicCompletion K)ˣ) :
    qsNQQuadraticLocal D H v a ^ 2 = 1 := by
  apply MonoidHom.ext
  intro u
  change (Units.map D.σ0.toMonoidHom (H.hilb v a u : Kˣ) ^ 3) ^ 2 = 1
  have h6 : (H.hilb v a u : Kˣ) ^ 6 = 1 :=
    (mem_rootsOfUnity 6 _).mp (H.hilb v a u).property
  rw [← pow_mul]
  change Units.map D.σ0.toMonoidHom (H.hilb v a u : Kˣ) ^ 6 = 1
  rw [← map_pow, h6, map_one]

end ArtinPrimitiveRoots.A2
