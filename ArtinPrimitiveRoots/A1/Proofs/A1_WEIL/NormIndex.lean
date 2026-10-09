import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.NormResidue
import Mathlib.GroupTheory.Index

set_option autoImplicit false

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

/-- The local norm-subgroup index is the degree of a finite abelian Galois extension.
Guide: PROOFS.md:474–475, norm-coset route. Uses the already built actual Artin map;
the unavailable MathlibInterface umbrella module is not imported. -/
theorem local_norm_index_eq_finrank (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsAbelianGalois K L] :
    (LocalFieldTheory.localNormSubgroup K L).index = Module.finrank K L := by
  rw [← LocalClassFieldTheory.abelianLocalArtinMonoidHom_ker K L, Subgroup.index_eq_card]
  exact (Nat.card_congr
    (QuotientGroup.quotientKerEquivOfSurjective
      (LocalClassFieldTheory.abelianLocalArtinMonoidHom K L)
      (LocalClassFieldTheory.abelianLocalArtinMonoidHom_surjective K L)).toEquiv).trans
    (IsGalois.card_aut_eq_finrank K L)

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
