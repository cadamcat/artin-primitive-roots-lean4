import ArtinPrimitiveRoots.Theta.Proofs.TH_CLASSICAL.Helpers
import ArtinPrimitiveRoots.Theta.Proofs.«TH-GOOD-SUBGROUP».ProjectedCongruence
import ArtinPrimitiveRoots.Theta.Proofs.«TH-GOOD-SUBGROUP».FiniteRational
import ArtinPrimitiveRoots.Theta.Proofs.«TH-GOOD-SUBGROUP».LevelHom
import ArtinPrimitiveRoots.Theta.Proofs.«TH-GOOD-SUBGROUP».Multiplier

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical MatrixGroups
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Finite-level lifting followed by the kernel of the central multiplier and a free congruence
subgroup. The resulting group is only required to have finite index. -/
theorem th_good_finite_level (P : CoverPackage D S H A)
    (T0 : Finset (FinPlace F)) (hT0 : S.Sf ⊆ T0) (m : FinPlace F → ℕ)
    (hm : ∀ v ∈ T0, (P.loc v).m0 ≤ m v) (j : P.RP) :
    ∃ Γ : Subgroup (SL(2, 𝓞 F)), Γ.FiniteIndex ∧ Spec.FreeAction F Γ ∧
      ∀ γ ∈ Γ, ∃ k : P.RP, th_classical_finiteLevel P T0 hT0 m k ∧
        th_classical_finiteEq P
          (P.ratRP (Matrix.SpecialLinearGroup.toGL (Spec.toSLF F γ)) * j) (j * k) := by
  classical
  obtain ⟨Γ0, hΓ0, σ, hklevel, hproj⟩ := th_good_level_hom P T0 hT0 m hm j
  obtain ⟨χ, hχ⟩ := th_good_multiplier_hom P j Γ0 σ (fun γ w => (hklevel γ).1 w) hproj
  let Γ1 : Subgroup (SL(2, 𝓞 F)) := χ.ker.map Γ0.subtype
  have hker : χ.ker.FiniteIndex := inferInstance
  have hΓ1 : Γ1.FiniteIndex := by
    apply Subgroup.finiteIndex_iff.mpr
    change (χ.ker.map Γ0.subtype).index ≠ 0
    rw [Subgroup.index_map_subtype]
    exact mul_ne_zero hker.index_ne_zero hΓ0.index_ne_zero
  obtain ⟨N, hN, hfree⟩ := Spec.exists_free_congr F
  have hΓN : (Spec.congrSubgroup F N).FiniteIndex := by
    letI : Finite (𝓞 F ⧸ N) := Ring.HasFiniteQuotients.finiteQuotient hN
    letI : Fintype (𝓞 F ⧸ N) := Fintype.ofFinite _
    letI : Fintype (SL(2, 𝓞 F ⧸ N)) := Fintype.ofFinite _
    dsimp [Spec.congrSubgroup]
    infer_instance
  let Γ : Subgroup (SL(2, 𝓞 F)) := Γ1 ⊓ Spec.congrSubgroup F N
  letI : Γ1.FiniteIndex := hΓ1
  letI : (Spec.congrSubgroup F N).FiniteIndex := hΓN
  have hΓ : Γ.FiniteIndex := inferInstance
  refine ⟨Γ, hΓ, ?_, ?_⟩
  · intro γ hγ z hfix
    exact hfree γ hγ.2 z hfix
  · intro γ hγ
    obtain ⟨δ, hδ, hδγ⟩ := Subgroup.mem_map.mp hγ.1
    have hδχ : χ δ = 1 := hδ
    refine ⟨σ δ, hklevel δ, ?_⟩
    rw [← hδγ]
    exact hχ δ hδχ

end ArtinPrimitiveRoots.A1.Theta
