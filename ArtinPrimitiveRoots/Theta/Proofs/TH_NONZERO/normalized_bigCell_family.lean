import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.lagrangian_vector_selector
import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.bigCell_normalized_intertwine
import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.zero_seed_analyticFamily
import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.replace_at_S_bigCell

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Big-cell sections realize normalized separating vectors at all exceptional places. -/
theorem normalized_bigCell_family (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) :
    ∃ Fam : AnalyticFamily P G μ, Fam.T0 = S.Sf ∧
      (∀ v ∈ S.Sf, ∃ φ : v.adicCompletion F → (G.T v).V,
        IsLocallyConstant φ ∧ HasCompactSupport φ ∧
          ∀ s, (Fam.sec s).f v = bigCell (P.loc v) (G.T v) s φ) ∧
      (∀ v ∈ S.Sf,
        G.lam v (intertwine (P.loc v) (μ v) ((Fam.sec (1 / 6)).f v) 1) = 1) ∧
      (∀ v ∈ S.Sf, ∀ y : (v.adicCompletion F)ˣ, y ∉ G.Alag v →
        G.lam v ((G.T v).σa y
          (intertwine (P.loc v) (μ v) ((Fam.sec (1 / 6)).f v) 1)) = 0) := by
  classical
  choose x hx hzero using fun v : S.Sf => lagrangian_vector_selector G v.1
  choose φ hφ hcφ hM using fun v : S.Sf =>
    bigCell_normalized_intertwine (P.loc v.1) (G.T v.1) (μ v.1) (x v)
  obtain ⟨Seed, hSeed, _⟩ := zero_seed_analyticFamily P G μ
  obtain ⟨Fam, hT, hf⟩ := replace_at_S_bigCell P G μ Seed hSeed φ hφ hcφ
  refine ⟨Fam, hT, ?_, ?_, ?_⟩
  · intro v hv
    exact ⟨φ ⟨v, hv⟩, hφ ⟨v, hv⟩, hcφ ⟨v, hv⟩, hf ⟨v, hv⟩⟩
  · intro v hv
    rw [hf ⟨v, hv⟩ (1 / 6), hM ⟨v, hv⟩ (1 / 6)]
    exact hx ⟨v, hv⟩
  · intro v hv y hy
    rw [hf ⟨v, hv⟩ (1 / 6), hM ⟨v, hv⟩ (1 / 6)]
    exact hzero ⟨v, hv⟩ y hy

end ArtinPrimitiveRoots.A1.Theta
