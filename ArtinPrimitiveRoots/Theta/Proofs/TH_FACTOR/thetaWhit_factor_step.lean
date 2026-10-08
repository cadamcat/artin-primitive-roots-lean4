import ArtinPrimitiveRoots.Theta.Proofs.TH_FACTOR.thetaWhit_factor_functional
import ArtinPrimitiveRoots.Theta.Proofs.TH_FACTOR.thetaWhit_local_normalizer

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- One-place factorization, valid even when the coefficient at X vanishes.
Uses `thetaWhit_factor_functional`, `thetaWhit_local_normalizer`, and frozen
`whittaker_theta_dim_le_one`/`thetaSpace_le`; feeds `thetaWhit_factor_iteration`. -/
theorem thetaWhit_factor_step {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam : AnalyticFamily P G μ)
    (hT : Fam.T0 = S.Sf) (C : ContinuedEis Fam) (v : FinPlace F) (hv : v ∉ S.Sf)
    (X : P.tc.G) (hX : ∀ k : (P.loc v).L, X * P.emb v k = P.emb v k * X)
    (k : (P.loc v).L) :
    thetaWhit C (X * P.emb v k) = thetaWhit C X * WvAll P G μ v (P.emb v k) := by
  obtain ⟨Λ, hΛ, hΛapply⟩ :=
    thetaWhit_factor_functional Fam hT C v hv X hX
  obtain ⟨hsph, α, hα, hαsph, hαrtr⟩ :=
    thetaWhit_local_normalizer P G μ v hv
  have hv6 : (6 : 𝓞 F) ∉ v.asIdeal := fun h => hv (S.over6 v h)
  have hd : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal :=
    fun h => hv (S.different_mem v h)
  have hstable := thetaSpace_le (P.loc v) (G.T v) (μ v)
  have hrtr : rtr k (sphWeyl P G v hv (1 / 6)) ∈
      thetaSpace (P.loc v) (G.T v) (μ v) :=
    hstable.2 (sphWeyl P G v hv (1 / 6)) hsph k
  have hdim := whittaker_theta_dim_le_one (P.loc v) (G.T v) (G.B v hv) A (μ v)
    hv6 hd Λ α hΛ hα
  have hmul := hdim (sphWeyl P G v hv (1 / 6)) hsph
    (rtr k (sphWeyl P G v hv (1 / 6))) hrtr
  have hfactor : Λ (rtr k (sphWeyl P G v hv (1 / 6))) =
      Λ (sphWeyl P G v hv (1 / 6)) * WvAll P G μ v (P.emb v k) := by
    calc
      Λ (rtr k (sphWeyl P G v hv (1 / 6))) =
          Λ (rtr k (sphWeyl P G v hv (1 / 6))) *
            α (sphWeyl P G v hv (1 / 6)) := by rw [hαsph]; simp
      _ = Λ (sphWeyl P G v hv (1 / 6)) *
            α (rtr k (sphWeyl P G v hv (1 / 6))) := by
        calc
          _ = α (sphWeyl P G v hv (1 / 6)) *
                Λ (rtr k (sphWeyl P G v hv (1 / 6))) := mul_comm _ _
          _ = α (rtr k (sphWeyl P G v hv (1 / 6))) *
                Λ (sphWeyl P G v hv (1 / 6)) := hmul
          _ = _ := mul_comm _ _
      _ = Λ (sphWeyl P G v hv (1 / 6)) * WvAll P G μ v (P.emb v k) := by
        rw [hαrtr]
  have hrtr_one : rtr (1 : (P.loc v).L) (sphWeyl P G v hv (1 / 6)) =
      sphWeyl P G v hv (1 / 6) := by
    funext y
    simp [rtr]
  have hbase : thetaWhit C X = Λ (sphWeyl P G v hv (1 / 6)) := by
    calc
      thetaWhit C X = thetaWhit C (X * P.emb v (1 : (P.loc v).L)) := by simp
      _ = Λ (rtr (1 : (P.loc v).L) (sphWeyl P G v hv (1 / 6))) := hΛapply 1
      _ = Λ (sphWeyl P G v hv (1 / 6)) := by rw [hrtr_one]
  calc
    thetaWhit C (X * P.emb v k) = Λ (rtr k (sphWeyl P G v hv (1 / 6))) :=
      hΛapply k
    _ = Λ (sphWeyl P G v hv (1 / 6)) * WvAll P G μ v (P.emb v k) := hfactor
    _ = thetaWhit C X * WvAll P G μ v (P.emb v k) := by rw [← hbase]

end ArtinPrimitiveRoots.A1.Theta
