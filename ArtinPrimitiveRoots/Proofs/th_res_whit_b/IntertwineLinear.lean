import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_WHIT.Defs

set_option autoImplicit false

open NumberField IsDedekindDomain
open MeasureTheory
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- The intertwining integral is linear on the section subspace in its convergence region. -/
def intertwineSectionLinear {v : FinPlace F} (L : FinLocalCover D H v)
    (T : TorusRep D H v) (μ : LocHaar v) (s : ℂ) (hs : 0 < s.re) :
    sectionSpace L T s →ₗ[ℂ] (L.L → T.V) where
  toFun f := intertwine L μ f.1
  map_add' f g := by
    funext x
    change (∫ y, (f.1 (L.w * L.n (Multiplicative.ofAdd y) * x) +
        g.1 (L.w * L.n (Multiplicative.ofAdd y) * x)) ∂μ.μ) = _
    have hf := (intertwine_isSection L T μ s hs f.1 f.2).1 x
    have hg := (intertwine_isSection L T μ s hs g.1 g.2).1 x
    exact integral_add hf hg
  map_smul' c f := by
    funext x
    change (∫ y, c • f.1 (L.w * L.n (Multiplicative.ofAdd y) * x) ∂μ.μ) = _
    exact integral_smul c _

end ArtinPrimitiveRoots.A1.Theta
