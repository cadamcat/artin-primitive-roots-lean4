import ArtinPrimitiveRoots.Hecke.Defs

/-!
# The congruence subgroup of global units

The unit subgroup used by the ray-theta construction is closed under products and inverses:
finite-place conditions are preimages of the higher-unit subgroups, and selected real-place
positivity is preserved by products and inversion.
-/

set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain
open ClassFieldTheory

noncomputable section

namespace ArtinPrimitiveRoots.Hecke

variable {K : Type*} [Field K] [NumberField K]

theorem rayClassModulus_infinitePart_eq_empty [IsTotallyComplex K]
    (m : RayClassModulus K) : m.infinitePart = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  exact (InfinitePlace.not_isReal_iff_isComplex.mpr
    (IsTotallyComplex.isComplex v.1)) v.2

/-- Units satisfying the finite and real congruences of a ray modulus. -/
def rayCongruentUnits (m : RayClassModulus K) : Subgroup Kˣ where
  carrier := {x | IsRayCongruent m x}
  one_mem' := by
    constructor
    · intro v hv
      simp [finitePlaceUnitEmbedding, rayLocalHigherUnitGroup]
    · intro v hv
      simp [InfinitePlace.embedding_of_isReal]
  mul_mem' := by
    intro x y hx hy
    constructor
    · intro v hv
      simpa [finitePlaceUnitEmbedding] using
        (rayLocalHigherUnitGroup v (m.finitePart v)).mul_mem (hx.1 v hv) (hy.1 v hv)
    · intro v hv
      simpa [map_mul] using mul_pos (hx.2 v hv) (hy.2 v hv)
  inv_mem' := by
    intro x hx
    constructor
    · intro v hv
      simpa [finitePlaceUnitEmbedding] using
        (rayLocalHigherUnitGroup v (m.finitePart v)).inv_mem (hx.1 v hv)
    · intro v hv
      simpa [map_inv] using inv_pos.mpr (hx.2 v hv)

@[simp] theorem mem_rayCongruentUnits {m : RayClassModulus K} (x : Kˣ) :
    x ∈ rayCongruentUnits m ↔ IsRayCongruent m x := Iff.rfl

/-- The subgroup of integral units satisfying the ray congruence, the unit lattice subobject used
by the ray theta construction. -/
def rayCongruentIntegralUnits (m : RayClassModulus K) : Subgroup (𝓞 K)ˣ :=
  Subgroup.comap
    (Units.map (algebraMap (𝓞 K) K).toMonoidHom)
    (rayCongruentUnits m)

@[simp] theorem mem_rayCongruentIntegralUnits {m : RayClassModulus K} (u : (𝓞 K)ˣ) :
    u ∈ rayCongruentIntegralUnits m ↔
      IsRayCongruent m (Units.map (algebraMap (𝓞 K) K).toMonoidHom u) := Iff.rfl

end ArtinPrimitiveRoots.Hecke

end
