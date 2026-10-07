import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-!
# Dirichlet's S-unit theorem

For a finite set of finite places of a number field, the S-unit group is finitely generated,
its torsion subgroup is the roots of unity, and its rank is the unit rank plus the number of
places in S.
-/

noncomputable section

namespace ArtinPrimitiveRoots.Arith

open NumberField

variable (K : Type*) [Field K] [NumberField K]
variable (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))

/-- The torsion subgroup of the S-unit group is the group of roots of unity of `K`.

The equivalence is the one induced by viewing roots of unity as units of `𝓞 K` and then as
S-units. -/
theorem sUnit_torsion :
    Nonempty (CommGroup.torsion
      (Set.unit (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) => v ∈ S) K) ≃*
      NumberField.Units.torsion K) := by
  sorry

/-- The S-unit group of a number field is finitely generated. -/
theorem sUnit_fg : Monoid.FG
    (Set.unit (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) => v ∈ S) K) := by
  sorry

/-- The torsion-free rank of the S-unit group is the unit rank plus the number of finite places
in `S`. -/
theorem sUnit_rank :
    Module.finrank ℤ (Additive ((Set.unit
      (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) => v ∈ S) K) ⧸
      CommGroup.torsion (Set.unit
        (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) => v ∈ S) K))) =
      NumberField.Units.rank K + S.card := by
  sorry

end ArtinPrimitiveRoots.Arith

end
