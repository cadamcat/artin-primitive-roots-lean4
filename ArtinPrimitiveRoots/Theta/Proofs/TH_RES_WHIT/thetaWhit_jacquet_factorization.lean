import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_WHIT.Defs

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}
variable {P : CoverPackage D S H A} {G : GlobalDatum P}
  {μ : ∀ v : FinPlace F, LocHaar v}

/-- A multilinear form on local section spaces, psi-equivariant separately in every
coordinate, factors through the local Jacquet maps. Apply whittaker_twoCell to each partial
functional and descend successively through each Jacquet kernel; complements extend to V.
Guide: sol-thin-thglobal/PROOFS.md:1007–1019.
Uses: whittaker_twoCell, jacquet_linear, whittaker_extend (if extending partial functionals).
Feeds: thetaWhit_multilinear after thetaWhit_section_multilinear. -/
theorem thetaWhit_jacquet_factorization
    (W : MultilinearMap ℂ
      (fun v : S.Sf => sectionSpace (P.loc v.1) (G.T v.1) (1 / 6)) ℂ)
    (hW : ∀ (v : S.Sf) (f : ∀ w : S.Sf, sectionSpace (P.loc w.1) (G.T w.1) (1 / 6))
      (t : v.1.adicCompletion F),
      W (Function.update f v (sectionRtr (P.loc v.1) (G.T v.1) (1 / 6)
        ((P.loc v.1).n (Multiplicative.ofAdd t)) (f v))) = A.ψ v.1 t * W f) :
    ∃ Λ : MultilinearMap ℂ (fun v : S.Sf => (G.T v.1).V) ℂ,
      ∀ f : ∀ v : S.Sf, sectionSpace (P.loc v.1) (G.T v.1) (1 / 6),
        W f = Λ (fun v => jacquet (P.loc v.1) A (μ v.1) (f v)) := by
  sorry

end ArtinPrimitiveRoots.A1.Theta
