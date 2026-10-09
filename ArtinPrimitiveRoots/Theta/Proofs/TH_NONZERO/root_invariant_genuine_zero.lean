import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.square_pairing_nontrivial
import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.root_square_lift
import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.root_square_commutator

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {H : HilbertData F} {CE : ℕ} {condη : Ideal (𝓞 F)}
  {S : SData F CE condη} {A : AddCharData F} {P : CoverPackage D S H A}

/-- A genuine function invariant under both local root groups vanishes. Invariance
extends to their algebraic generated subgroup, which contains a nontrivial center
element by the square-torus root word. No continuity of the function is needed. -/
theorem root_invariant_genuine_zero (v : FinPlace F) (_hv : v ∉ S.Sf)
    (f : P.tc.G → ℂ)
    (hgenuine : ∀ ζ g, f (P.tc.z ζ * g) = ((ζ : ℂˣ) : ℂ) * f g)
    (hn : ∀ t g, f (P.emb v ((P.loc v).n t) * g) = f g)
    (hnbar : ∀ t g, f (P.emb v ((P.loc v).nbar t) * g) = f g) :
    ∀ g, f g = 0 := by
  have hinv : ∀ h ∈ Subgroup.closure
      (Set.range (P.loc v).n ∪ Set.range (P.loc v).nbar),
      ∀ g, f (P.emb v h * g) = f g := by
    intro h hh
    induction hh using Subgroup.closure_induction with
    | mem h hh =>
        rcases hh with ⟨t, rfl⟩ | ⟨t, rfl⟩
        · exact hn t
        · exact hnbar t
    | one =>
        intro g
        simp only [map_one, one_mul]
    | mul h k _ _ ih ik =>
        intro g
        rw [map_mul, mul_assoc, ih, ik]
    | inv h _ ih =>
        intro g
        simpa only [map_inv, mul_inv_cancel_left] using
          (ih (P.emb v h⁻¹ * g)).symm
  obtain ⟨t, u, hζ⟩ := square_pairing_nontrivial D H v
  let ζ := torusPairing D H v (t ^ 2) (u ^ 2)
  have hmem : (P.loc v).z ζ ∈ Subgroup.closure
      (Set.range (P.loc v).n ∪ Set.range (P.loc v).nbar) :=
    root_square_commutator (P.loc v) t u
      (root_square_lift (P.loc v) t) (root_square_lift (P.loc v) u)
  have hζc : ((ζ : ℂˣ) : ℂ) ≠ 1 := by
    intro heq
    apply hζ
    apply Subtype.ext
    apply Units.ext
    simpa only [OneMemClass.coe_one, Units.val_one] using heq
  intro g
  have hz : (((ζ : ℂˣ) : ℂ) - 1) * f g = 0 := by
    rw [sub_mul, one_mul, ← hgenuine, ← P.emb_z v ζ, hinv _ hmem g, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hζc)

end ArtinPrimitiveRoots.A1.Theta
