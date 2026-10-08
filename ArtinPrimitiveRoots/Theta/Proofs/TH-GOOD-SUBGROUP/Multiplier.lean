import ArtinPrimitiveRoots.Theta.Proofs.TH_CLASSICAL.Helpers
import ArtinPrimitiveRoots.Theta.Proofs.«TH-GOOD-SUBGROUP».FiniteRational

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical MatrixGroups
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- The difference between the finite rational splitting and a level splitting is a cubic
character. Its kernel removes the residual phase from the finite components. -/
theorem th_good_multiplier_hom (P : CoverPackage D S H A) (j : P.RP)
    (Γ0 : Subgroup (SL(2, 𝓞 F))) (σ : Γ0 →* P.RP)
    (hσ : ∀ γ w, P.compC w (σ γ) = 1)
    (hproj : ∀ (γ : Γ0) (v : FinPlace F), (P.loc v).pr (P.compF v
      (P.ratRP (Matrix.SpecialLinearGroup.toGL (Spec.toSLF F (γ : SL(2, 𝓞 F)))) * j)) =
        (P.loc v).pr (P.compF v (j * σ γ))) :
    ∃ χ : Γ0 →* rootsOfUnity 3 ℂ, ∀ γ, χ γ = 1 →
      th_classical_finiteEq P
        (P.ratRP (Matrix.SpecialLinearGroup.toGL (Spec.toSLF F (γ : SL(2, 𝓞 F)))) * j)
        (j * σ γ) := by
  classical
  obtain ⟨ρ, hρ⟩ := th_good_finite_rational_hom P
  let g : Γ0 →* GL (Fin 2) F :=
    Matrix.SpecialLinearGroup.toGL.comp ((Spec.toSLF F).comp Γ0.subtype)
  have hg (γ : Γ0) : g γ =
      Matrix.SpecialLinearGroup.toGL (Spec.toSLF F (γ : SL(2, 𝓞 F))) := rfl
  choose r hrq hrC hrF using fun γ : Γ0 => hρ (g γ)
  let τ : Γ0 →* P.tc.G :=
    (MulAut.conj ((P.q j)⁻¹)).toMonoidHom.comp (ρ.comp g)
  have hτ (γ : Γ0) : τ γ = (P.q j)⁻¹ * ρ (g γ) * P.q j := by
    change (P.q j)⁻¹ * ρ (g γ) * ((P.q j)⁻¹)⁻¹ = _
    rw [inv_inv]
  let d (γ : Γ0) : P.RP := j⁻¹ * r γ * j * (σ γ)⁻¹
  have hdF (γ : Γ0) (v : FinPlace F) : (P.loc v).pr (P.compF v (d γ)) = 1 := by
    have he : (P.loc v).pr (P.compF v (r γ)) * (P.loc v).pr (P.compF v j) =
        (P.loc v).pr (P.compF v j) * (P.loc v).pr (P.compF v (σ γ)) := by
      simpa only [map_mul, hrF, hg] using hproj γ v
    calc
      (P.loc v).pr (P.compF v (d γ)) =
          ((P.loc v).pr (P.compF v j))⁻¹ *
            ((P.loc v).pr (P.compF v (r γ)) * (P.loc v).pr (P.compF v j)) *
              ((P.loc v).pr (P.compF v (σ γ)))⁻¹ := by
        simp only [d, map_mul, map_inv, mul_assoc]
      _ = ((P.loc v).pr (P.compF v j))⁻¹ *
            ((P.loc v).pr (P.compF v j) * (P.loc v).pr (P.compF v (σ γ))) *
              ((P.loc v).pr (P.compF v (σ γ)))⁻¹ := by rw [he]
      _ = 1 := by simp only [inv_mul_cancel_left, mul_inv_cancel]
  have hdC (γ : Γ0) (w : InfinitePlace F) : P.compC w (d γ) = 1 := by
    simp only [d, map_mul, map_inv, hrC, hσ, mul_one, inv_one, inv_mul_cancel]
  have hphase : ∀ γ : Γ0, ∃ ξ : rootsOfUnity 3 ℂ, P.q (d γ) = P.tc.z ξ :=
    fun γ => (th_classical_central_kernel P (d γ) (hdF γ) (hdC γ)).exists
  choose ξ hξ using hphase
  have hdq (γ : Γ0) : P.q (d γ) = τ γ * (P.q (σ γ))⁻¹ := by
    rw [hτ]
    simp only [d, map_mul, map_inv, hrq]
  have hfac (γ : Γ0) : τ γ = P.tc.z (ξ γ) * P.q (σ γ) := by
    have he : τ γ * (P.q (σ γ))⁻¹ = P.tc.z (ξ γ) := (hdq γ).symm.trans (hξ γ)
    calc
      τ γ = (τ γ * (P.q (σ γ))⁻¹) * P.q (σ γ) := by
        simp only [mul_assoc, inv_mul_cancel, mul_one]
      _ = P.tc.z (ξ γ) * P.q (σ γ) := congrArg (fun a => a * P.q (σ γ)) he
  have hOne : ξ 1 = 1 := by
    apply P.tc.z_inj
    simpa only [map_one, mul_one] using (hfac (1 : Γ0)).symm
  have hMul (γ δ : Γ0) : ξ (γ * δ) = ξ γ * ξ δ := by
    have he : P.tc.z (ξ (γ * δ)) * P.q (σ (γ * δ)) =
        (P.tc.z (ξ γ) * P.tc.z (ξ δ)) * P.q (σ (γ * δ)) := by
      calc
        P.tc.z (ξ (γ * δ)) * P.q (σ (γ * δ)) = τ (γ * δ) := (hfac _).symm
        _ = τ γ * τ δ := map_mul _ _ _
        _ = (P.tc.z (ξ γ) * P.q (σ γ)) * (P.tc.z (ξ δ) * P.q (σ δ)) := by
          rw [hfac γ, hfac δ]
        _ = P.tc.z (ξ γ) * (P.q (σ γ) * P.tc.z (ξ δ)) * P.q (σ δ) := by
          simp only [mul_assoc]
        _ = P.tc.z (ξ γ) * (P.tc.z (ξ δ) * P.q (σ γ)) * P.q (σ δ) := by
          rw [← P.tc.z_central (ξ δ) (P.q (σ γ))]
        _ = (P.tc.z (ξ γ) * P.tc.z (ξ δ)) * P.q (σ (γ * δ)) := by
          simp only [map_mul, mul_assoc]
    apply P.tc.z_inj
    exact (mul_right_cancel he).trans (map_mul P.tc.z (ξ γ) (ξ δ)).symm
  let χ : Γ0 →* rootsOfUnity 3 ℂ :=
    { toFun := ξ
      map_one' := hOne
      map_mul' := hMul }
  refine ⟨χ, ?_⟩
  intro γ hγ
  change ξ γ = 1 at hγ
  have hτker : τ γ = P.q (σ γ) := by
    simpa only [hγ, map_one, one_mul] using hfac γ
  have he := congrArg (fun a => P.q j * a) hτker
  simp only [hτ, mul_assoc, mul_inv_cancel_left] at he
  have hq : P.q (r γ * j) = P.q (j * σ γ) := by
    simpa only [map_mul, hrq] using he
  obtain ⟨ζ, hζfin, hζprod, hζF, _⟩ := (P.q_eq (r γ * j) (j * σ γ)).mp hq
  refine ⟨ζ, hζfin, hζprod, ?_⟩
  intro v
  simpa only [map_mul, hrF, hg] using hζF v

end ArtinPrimitiveRoots.A1.Theta
