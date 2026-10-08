import ArtinPrimitiveRoots.Proofs.qs_nq0_sol.EqualClass

/-!
# Local algebra for product conductors

Cubed Hilbert symbols preserve multiplication and division in their first
argument. These identities compare products of canonical local characters
with the characters of products and quotients of their generators.
-/

set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain ArtinPrimitiveRoots.A1

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]

/-- The local quadratic character preserves multiplication and division of its parameter. -/
theorem qs_nq0_quadratic_local_mul_div
    (D : FieldData K) (H : HilbertData K) (v : FinPlace K)
    (a b : (v.adicCompletion K)ˣ) :
    qsNQQuadraticLocal D H v (a * b) =
      qsNQQuadraticLocal D H v a * qsNQQuadraticLocal D H v b ∧
    qsNQQuadraticLocal D H v (a / b) =
      qsNQQuadraticLocal D H v a / qsNQQuadraticLocal D H v b := by
  let g : rootsOfUnity 6 K →* ℂˣ :=
    (powMonoidHom 3 : ℂˣ →* ℂˣ).comp
      ((Units.map D.σ0.toMonoidHom).comp (rootsOfUnity 6 K).subtype)
  let f : (v.adicCompletion K)ˣ →* ((v.adicCompletion K)ˣ →* ℂˣ) :=
    MonoidHom.mk' (fun x => qsNQQuadraticLocal D H v x) (fun x y => by
      apply MonoidHom.ext
      intro u
      change g (H.hilb v (x * y) u) = g (H.hilb v x u) * g (H.hilb v y u)
      rw [H.mul_left, map_mul])
  refine ⟨f.map_mul a b, ?_⟩
  change f (a / b) = f a / f b
  exact map_div f a b

end ArtinPrimitiveRoots.A2
