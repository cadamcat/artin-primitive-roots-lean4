import ArtinPrimitiveRoots.Theta.Proofs.TH_FACTOR.Defs
import ArtinPrimitiveRoots.Proofs.th_factor_b.Analytic

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Realize the global coefficient with one exterior argument as a Whittaker functional
on the translated Weyl spherical vector. Its scaling absorbs `cv v (1/6)`.
Uses frozen `theta_exterior_whittaker`, `theta_linear_translate`,
`intertwine_rtr`, `intertwine_spherical`, and continuation uniqueness;
feeds `thetaWhit_factor_step`. The original family has exterior level exactly S. -/
theorem thetaWhit_factor_functional {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam : AnalyticFamily P G μ)
    (hT : Fam.T0 = S.Sf) (C : ContinuedEis Fam) (v : FinPlace F) (hv : v ∉ S.Sf)
    (X : P.tc.G) (hX : ∀ k : (P.loc v).L, X * P.emb v k = P.emb v k * X) :
    ∃ Λ : ((P.loc v).L → (G.T v).V) →ₗ[ℂ] ℂ,
      IsWhittakerOn (P.loc v) A (thetaSpace (P.loc v) (G.T v) (μ v)) Λ ∧
      ∀ k : (P.loc v).L, thetaWhit C (X * P.emb v k) =
        Λ (rtr k (sphWeyl P G v hv (1 / 6))) := by
  obtain ⟨Λ, hΛ, hΛapply⟩ := theta_exterior_whittaker Fam v hv X hX
  have hvFam : v ∉ Fam.T0 := by rw [hT]; exact hv
  have hv6 : (6 : 𝓞 F) ∉ v.asIdeal := fun h => hv (S.over6 v h)
  have hvsec (s : ℂ) : v ∉ (Fam.sec s).T0 := by
    rw [Fam.T0_eq s]
    exact hvFam
  have hsrc : IsSection (P.loc v) (G.T v) (1 / 6) ((Fam.sec (1 / 6)).f v) :=
    (Fam.sec (1 / 6)).f_sec v
  have hsrc1 : (Fam.sec (1 / 6)).f v 1 = (G.B v hv).e 0 :=
    ((Fam.sec (1 / 6)).f_sph v (hvsec (1 / 6))).1
  have hsrcK : ∀ g k, k ∈ (P.tame v hv).Kmax →
      (Fam.sec (1 / 6)).f v (g * k) = (Fam.sec (1 / 6)).f v g := by
    intro g k hk
    exact (Fam.sec (1 / 6)).f_sph v (hvsec (1 / 6)) |>.2 g k hk
  have hsph := sphWeyl_data (P := P) (G := G) v hv (1 / 6)
  have hM0 : intertwine (P.loc v) (μ v) ((Fam.sec (1 / 6)).f v) =
      cv v (1 / 6) • sphWeyl P G v hv (1 / 6) :=
    intertwine_spherical (P.loc v) (P.tame v hv) (G.T v) (G.B v hv) (μ v) hv6
      (1 / 6) (by norm_num) ((Fam.sec (1 / 6)).f v) hsrc hsrc1 hsrcK
      (sphWeyl P G v hv (1 / 6)) hsph.1 hsph.2.1 hsph.2.2
  let Λ' : ((P.loc v).L → (G.T v).V) →ₗ[ℂ] ℂ := cv v (1 / 6) • Λ
  refine ⟨Λ', ?_, ?_⟩
  · intro f hf t
    dsimp [Λ']
    rw [hΛ f hf t]
    ring
  · intro k
    let TF := translateExteriorFamily Fam hT v hv k
    let Ck : ContinuedEis TF := Classical.choice (exists_continuedEis TF)
    have hTF : TF.T0 = insert v Fam.T0 := by rfl
    have hOff : ∀ s w, w ≠ v → (TF.sec s).f w = (Fam.sec s).f w := by
      intro s w hw
      simpa [TF, translateExteriorFamily, translateLocalAt, hw]
    have hAt : ∀ s, (TF.sec s).f v = rtr k ((Fam.sec s).f v) := by
      intro s
      simpa [TF, translateExteriorFamily]
    have hExt := hΛapply TF Ck hTF hOff
    have hTrans := thetaWhit_translateExteriorFamily Fam hT v hv k C Ck X
    have hMk : intertwine (P.loc v) (μ v) ((TF.sec (1 / 6)).f v) =
        cv v (1 / 6) • rtr k (sphWeyl P G v hv (1 / 6)) := by
      rw [hAt]
      rw [intertwine_rtr]
      rw [hM0]
      funext y
      simp [rtr]
    calc
      thetaWhit C (X * P.emb v k) = thetaWhit Ck X := hTrans.symm
      _ = Λ (intertwine (P.loc v) (μ v) ((TF.sec (1 / 6)).f v)) := hExt
      _ = Λ (cv v (1 / 6) • rtr k (sphWeyl P G v hv (1 / 6))) :=
        congrArg Λ hMk
      _ = cv v (1 / 6) * Λ (rtr k (sphWeyl P G v hv (1 / 6))) := by
        rw [map_smul]
        simp only [smul_eq_mul]
      _ = Λ' (rtr k (sphWeyl P G v hv (1 / 6))) := by
        simp [Λ', smul_eq_mul]

end ArtinPrimitiveRoots.A1.Theta
