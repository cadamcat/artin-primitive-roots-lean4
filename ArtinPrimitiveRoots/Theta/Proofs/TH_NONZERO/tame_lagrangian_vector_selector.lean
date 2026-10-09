import ArtinPrimitiveRoots.Theta.Eis

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- At a tame place, the spherical basis vector already annihilates every
translate outside the Lagrangian subgroup. -/
theorem tame_lagrangian_vector_selector {P : CoverPackage D S H A}
    (G : GlobalDatum P) (v : FinPlace F) (hv : v ∉ S.Sf)
    (y : (v.adicCompletion F)ˣ) (hy : y ∉ G.Alag v) :
    G.lam v ((G.T v).σa y ((G.B v hv).e 0)) = 0 := by
  obtain ⟨j, u, hu, hyu⟩ := (Classical.choice (exists_tameLocalGeometry v)).decomposition y
  have hj : (j : ZMod 3) ≠ 0 := by
    intro hj
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd j 3).mp hj
    apply hy
    apply (G.alag_tame v hv y).mpr
    exact ⟨k, u, hu, by simpa [hk] using hyu⟩
  rw [hyu, (G.B v hv).act j u hu 0]
  simp [G.lam_tame v hv, hj]

end ArtinPrimitiveRoots.A1.Theta
