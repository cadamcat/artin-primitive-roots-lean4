import ArtinPrimitiveRoots.Theta.Cover
import Mathlib.Topology.Maps.Proper.Basic

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

/-- The finite local cover has compact preimages of compact projective sets. -/
theorem local_cover_compact_preimage
    {D : FieldData F} {H : HilbertData F} {v : FinPlace F}
    (L : FinLocalCover D H v)
    (K : Set (PGL2 (v.adicCompletion F))) (hK : IsCompact K) :
    IsCompact (L.pr ⁻¹' K) := by
  have hz (ζ : rootsOfUnity 3 ℂ) : L.pr (L.z ζ) = 1 := by
    change L.z ζ ∈ L.pr.ker
    rw [L.pr_ker]
    exact ⟨ζ, rfl⟩
  have hrel {g c : L.L} (h : L.pr g = L.pr c) :
      ∃ ζ : rootsOfUnity 3 ℂ, g = L.z ζ * c := by
    have hk : g * c⁻¹ ∈ L.pr.ker := by
      change L.pr (g * c⁻¹) = 1
      simp only [map_mul, map_inv, h, mul_inv_cancel]
    rw [L.pr_ker] at hk
    obtain ⟨ζ, hζ⟩ := hk
    exact ⟨ζ, by simp only [hζ, inv_mul_cancel_right]⟩
  have hclosed : IsClosedMap L.pr := by
    intro C hC
    apply ((Topology.isQuotientMap_iff_isClosed.mp
      (L.pr_open.isQuotientMap L.pr_cont L.pr_surj)).2 (L.pr '' C)).mpr
    have hsat : L.pr ⁻¹' (L.pr '' C) =
        ⋃ ζ : rootsOfUnity 3 ℂ, (fun g : L.L => L.z ζ * g) '' C := by
      ext g
      constructor
      · rintro ⟨c, hc, hcg⟩
        obtain ⟨ζ, hζ⟩ := hrel hcg.symm
        exact Set.mem_iUnion.mpr ⟨ζ, c, hc, hζ.symm⟩
      · intro hg
        obtain ⟨ζ, c, hc, rfl⟩ := Set.mem_iUnion.mp hg
        exact ⟨c, hc, by simp only [map_mul, hz, one_mul]⟩
    rw [hsat]
    exact isClosed_iUnion_of_finite fun ζ =>
      (Homeomorph.mulLeft (L.z ζ)).isClosedMap C hC
  have hfibers (y : PGL2 (v.adicCompletion F)) :
      IsCompact (L.pr ⁻¹' {y}) := by
    obtain ⟨a, ha⟩ := L.pr_surj y
    apply Set.Finite.isCompact
    apply (Set.finite_range fun ζ : rootsOfUnity 3 ℂ => L.z ζ * a).subset
    intro g hg
    obtain ⟨ζ, hζ⟩ := hrel ((Set.mem_singleton_iff.mp hg).trans ha.symm)
    exact ⟨ζ, hζ.symm⟩
  exact (isProperMap_iff_isClosedMap_and_compact_fibers.mpr
    ⟨L.pr_cont, hclosed, hfibers⟩).isCompact_preimage hK

end ArtinPrimitiveRoots.A1.Theta
