import ArtinPrimitiveRoots.Theta.LocalWhit

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {H : HilbertData F} {v : FinPlace F}

/-- A normalized spherical Jacquet factor is one after a compact translation and a
torus action fixed by the coordinate functional. -/
theorem whit_good_local_factor (L : FinLocalCover D H v) (τ : TameSplitting L)
    (T : TorusRep D H v) (B : TameTorusBasis T) (A : AddCharData F) (μ : LocHaar v)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal) (hd : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal)
    (s : ℂ) (f : L.L → T.V) (hf : IsSection L T s f) (h1 : f 1 = B.e 0)
    (hK : ∀ g, ∀ k ∈ τ.Kmax, f (g * k) = f g)
    (lam : T.V →ₗ[ℂ] ℂ) (hlam : ∀ j : ZMod 3, lam (B.e j) = if j = 0 then 1 else 0)
    (u : (v.adicCompletion F)ˣ) (hfixed : ∀ z, lam (T.σa u z) = lam z)
    (k : L.L) (hk : k ∈ τ.Kmax) :
    lam (T.σa u (jacquet L A μ (rtr k f))) = 1 := by
  rw [hfixed]
  have hrtr : rtr k f = f := by
    funext g
    exact hK g k hk
  rw [hrtr]
  have hrtrOne : rtr (1 : L.L) f = f := by
    funext g
    exact congrArg f (mul_one g)
  have htwo : (2 : ZMod 3) ≠ 0 := by decide
  have hJ := congrArg lam (jacquet_spherical L τ T B A μ hv hd s f hf h1 hK 0)
  simpa [L.a_one, hrtrOne, map_add, map_smul, hlam, htwo] using hJ

/-- A rational unit fails to be a local integral unit at only finitely many places. -/
theorem whit_rational_nonunit_finite (δ : Fˣ) :
    Set.Finite {v : FinPlace F | ¬ IsLocUnit v (toLoc v δ)} := by
  refine ((HeightOneSpectrum.Support.finite (𝓞 F) (δ : F)).union
    (HeightOneSpectrum.Support.finite (𝓞 F) ((δ⁻¹ : Fˣ) : F))).subset ?_
  intro v hv
  by_contra hnot
  have hval : v.valuation F (δ : F) ≤ 1 := by
    apply le_of_not_gt
    intro hgt
    exact hnot (Or.inl hgt)
  have hinv : v.valuation F ((δ⁻¹ : Fˣ) : F) ≤ 1 := by
    apply le_of_not_gt
    intro hgt
    exact hnot (Or.inr hgt)
  apply hv
  constructor
  · change ((δ : F) : v.adicCompletion F) ∈ v.adicCompletionIntegers F
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hval
  · change (((δ⁻¹ : Fˣ) : F) : v.adicCompletion F) ∈ v.adicCompletionIntegers F
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hinv

end ArtinPrimitiveRoots.A1.Theta
