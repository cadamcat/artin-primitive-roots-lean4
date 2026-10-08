import ArtinPrimitiveRoots.A1.ThetaInterface
import ArtinPrimitiveRoots.Theta.Cover
import ArtinPrimitiveRoots.Theta.TorusInd

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.th_jacquet_p

open ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {H : HilbertData F} {v : FinPlace F}

theorem section_add_smul (L : FinLocalCover D H v) (T : TorusRep D H v) (s c : ℂ)
    (f g : L.L → T.V) (hf : IsSection L T s f) (hg : IsSection L T s g) :
    IsSection L T s (f + c • g) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y h
    simp only [Pi.add_apply, Pi.smul_apply, hf.1, hg.1, map_add, map_smul,
      smul_add, smul_smul]
    module
  · intro ζ h
    simp only [Pi.add_apply, Pi.smul_apply, hf.2.1, hg.2.1,
      smul_add, smul_smul]
    module
  · obtain ⟨m₁, hm₁, hK₁⟩ := hf.2.2
    obtain ⟨m₂, hm₂, hK₂⟩ := hg.2.2
    let m := max m₁ m₂
    have hm : L.m0 ≤ m := le_trans hm₁ (le_max_left _ _)
    refine ⟨m, hm, ?_⟩
    intro h k hk
    have hk₁ : k ∈ L.Kc m₁ := L.Kc_anti m₁ m hm₁ (le_max_left _ _) hk
    have hk₂ : k ∈ L.Kc m₂ := L.Kc_anti m₂ m hm₂ (le_max_right _ _) hk
    simp only [Pi.add_apply, Pi.smul_apply, hK₁ h k hk₁, hK₂ h k hk₂]

end ArtinPrimitiveRoots.Proofs.th_jacquet_p
