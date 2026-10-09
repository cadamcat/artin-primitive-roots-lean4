import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.rat_intertwined_scalar_nonzero_iff_mem_delta

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Normalized local selectors leave one nonzero term in the rational torus sum. -/
theorem normalized_intertwined_torus_sum_ne_zero {P : CoverPackage D S H A}
    (G : GlobalDatum P) (μ : ∀ v : FinPlace F, LocHaar v) (Fam : AnalyticFamily P G μ)
    (hT : Fam.T0 = S.Sf)
    (h1 : ∀ v ∈ S.Sf,
      G.lam v (intertwine (P.loc v) (μ v) ((Fam.sec (1 / 6)).f v) 1) = 1)
    (hzero : ∀ v ∈ S.Sf, ∀ y : (v.adicCompletion F)ˣ, y ∉ G.Alag v →
      G.lam v ((G.T v).σa y
        (intertwine (P.loc v) (μ v) ((Fam.sec (1 / 6)).f v) 1)) = 0) :
    (∑' δ : Fˣ ⧸ G.Δ,
      fourierRawM μ Fam.sec (1 / 6) (P.tc.rat (diagGL (Quotient.out δ)))) ≠ 0 := by
  let a : Fˣ ⧸ G.Δ → ℂ := fun δ =>
    fourierRawM μ Fam.sec (1 / 6) (P.tc.rat (diagGL (Quotient.out δ)))
  have hterm (δ : Fˣ ⧸ G.Δ) : a δ ≠ 0 ↔ δ = 1 := by
    dsimp only [a]
    rw [rat_intertwined_scalar_nonzero_iff_mem_delta G μ Fam hT h1 hzero,
      ← QuotientGroup.eq_one_iff]
    have hout : ((Quotient.out δ : Fˣ) : Fˣ ⧸ G.Δ) = δ := Quotient.out_eq δ
    rw [hout]
  change (∑' δ, a δ) ≠ 0
  rw [tsum_eq_single (1 : Fˣ ⧸ G.Δ) (fun δ hδ => by
    by_contra hn
    exact hδ ((hterm δ).mp hn))]
  exact (hterm 1).mpr rfl

end ArtinPrimitiveRoots.A1.Theta
