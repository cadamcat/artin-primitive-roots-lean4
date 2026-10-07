import Mathlib.LinearAlgebra.Basis.Basic
import ArtinPrimitiveRoots.Theta.Res

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1
open Module

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- The coordinate along `e₀` of a tame basis. -/
def tameCoord0 {D : FieldData F} {H : HilbertData F} {v : FinPlace F} {T : TorusRep D H v}
    (B : TameTorusBasis T) : T.V →ₗ[ℂ] ℂ :=
  (Basis.mk B.linIndep B.spans.ge).coord 0

/-- **def:Wv**: the normalized exterior spherical Whittaker function on `G` (`0` off `Gloc v`):
`Wv(emb k) = c₀(𝒥(π(k) f°'))`, `c₀` the `e₀`-coordinate of the Weyl basis (`c₀(u) = 1`). -/
def WvAll (P : CoverPackage D S H A) (G : GlobalDatum P) (μ : ∀ v : FinPlace F, LocHaar v)
    (v : FinPlace F) (h : P.tc.G) : ℂ :=
  if hv : v ∉ S.Sf then
    if hh : ∃ k, P.emb v k = h then
      tameCoord0 (G.B v hv).weyl
        (jacquet (P.loc v) A (μ v) (rtr hh.choose (sphWeyl P G v hv (1 / 6))))
    else 0
  else 0

/-- Exterior local argument after inserting the rational diagonal and optional Weyl element.
The supplied local factor occurs only on the original finite set `T`. -/
def thetaWhit_localArgument (P : CoverPackage D S H A) (ν : Fˣ) (ε : Bool)
    (T : Finset (FinPlace F)) (g : FinPlace F → P.tc.G) (v : FinPlace F) : P.tc.G :=
  P.tc.a v (toLoc v ν) * (if ε then P.tc.w v else 1) * (if v ∈ T then g v else 1)

end ArtinPrimitiveRoots.A1.Theta
