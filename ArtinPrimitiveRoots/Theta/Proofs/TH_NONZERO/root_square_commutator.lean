import ArtinPrimitiveRoots.Theta.TorusInd

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical commutatorElement
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {H : HilbertData F} {v : FinPlace F}

/-- The commutator of two root-word square-torus lifts lies in the root-generated
subgroup. Their unknown central phases cancel, leaving the torus pairing. -/
theorem root_square_commutator (L : FinLocalCover D H v)
    (t u : (v.adicCompletion F)ˣ)
    (ht : ∃ h ∈ Subgroup.closure (Set.range L.n ∪ Set.range L.nbar),
      ∃ ζ, h = L.z ζ * L.a (t ^ 2))
    (hu : ∃ h ∈ Subgroup.closure (Set.range L.n ∪ Set.range L.nbar),
      ∃ ζ, h = L.z ζ * L.a (u ^ 2)) :
    L.z (torusPairing D H v (t ^ 2) (u ^ 2)) ∈
      Subgroup.closure (Set.range L.n ∪ Set.range L.nbar) := by
  let R := Subgroup.closure (Set.range L.n ∪ Set.range L.nbar)
  obtain ⟨h, hh, ζ, heq⟩ := ht
  obtain ⟨k, hk, ξ, keq⟩ := hu
  have hz (η : rootsOfUnity 3 ℂ) (g : L.L) : Commute (L.z η) g := L.z_central η g
  have hphase : ⁅h, k⁆ = ⁅L.a (t ^ 2), L.a (u ^ 2)⁆ := by
    rw [heq, keq, commutatorElement_mul_left_eq_conj_mul,
      (hz ζ (L.z ξ * L.a (u ^ 2))).commutator_eq, mul_one,
      commutatorElement_mul_right_eq_mul_conj,
      (hz ξ (L.a (t ^ 2))).symm.commutator_eq, one_mul,
      (hz ξ ⁅L.a (t ^ 2), L.a (u ^ 2)⁆).eq, mul_inv_cancel_right,
      (hz ζ ⁅L.a (t ^ 2), L.a (u ^ 2)⁆).eq, mul_inv_cancel_right]
  have hmem : ⁅h, k⁆ ∈ R :=
    R.mul_mem (R.mul_mem (R.mul_mem hh hk) (R.inv_mem hh)) (R.inv_mem hk)
  rw [hphase, commutatorElement_def, torus_commutator] at hmem
  exact hmem
end ArtinPrimitiveRoots.A1.Theta
