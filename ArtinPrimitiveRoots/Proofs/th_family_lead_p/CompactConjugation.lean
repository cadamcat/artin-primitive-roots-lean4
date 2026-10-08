import ArtinPrimitiveRoots.Proofs.th_family_lead_p.RestrictedProduct
import Mathlib.Topology.Compactness.Compact

set_option autoImplicit false

open Topology Set

namespace ArtinPrimitiveRoots.A1.Theta

theorem compact_conjugation_neighborhood {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {C V : Set G} (hC : IsCompact C) (hV : IsOpen V)
    (h1 : (1 : G) ∈ V) :
    ∃ U : Set G, IsOpen U ∧ (1 : G) ∈ U ∧
      ∀ a ∈ U, ∀ g ∈ C, g⁻¹ * a * g ∈ V := by
  let f : G × G → G := fun p => p.1⁻¹ * p.2 * p.1
  have hf : Continuous f := by fun_prop
  let W : Set (G × G) := f ⁻¹' V
  have hW : IsOpen W := hV.preimage hf
  have hprod : C ×ˢ ({1} : Set G) ⊆ W := by
    rintro ⟨g, a⟩ ⟨hg, ha⟩
    have ha' : a = 1 := by simpa using ha
    subst a
    simpa [W, f] using h1
  obtain ⟨U₁, U₂, hU₁, hU₂, hCU₁, h1U₂, hUprod⟩ :=
    generalized_tube_lemma hC isCompact_singleton hW hprod
  refine ⟨U₂, hU₂, h1U₂ (by simp), ?_⟩
  intro a ha g hg
  have hp : (g, a) ∈ U₁ ×ˢ U₂ := ⟨hCU₁ hg, ha⟩
  have hp' : (g, a) ∈ f ⁻¹' V := hUprod hp
  simpa [f] using hp'

end ArtinPrimitiveRoots.A1.Theta
