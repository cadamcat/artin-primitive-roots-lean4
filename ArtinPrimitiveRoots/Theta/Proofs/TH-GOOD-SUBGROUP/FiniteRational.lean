import ArtinPrimitiveRoots.Theta.Cover

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical MatrixGroups
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- The finite part of the rational splitting is a hom after quotienting by the global phases. -/
theorem th_good_finite_rational_hom (P : CoverPackage D S H A) :
    ∃ ρ : GL (Fin 2) F →* P.tc.G, ∀ γ : GL (Fin 2) F,
      ∃ r : P.RP, P.q r = ρ γ ∧ (∀ w, P.compC w r = 1) ∧
        ∀ v, P.compF v r = P.compF v (P.ratRP γ) := by
  classical
  have hres : Set.Finite {v : FinPlace F | ∃ hv : v ∉ S.Sf,
      (1 : (P.loc v).L) ∉ (P.tame v hv).Kmax} := by
    apply Set.finite_empty.subset
    intro v hv
    obtain ⟨hvS, hbad⟩ := hv
    exact (hbad (P.tame v hvS).Kmax.one_mem).elim
  choose a haF haC using fun γ : GL (Fin 2) F => P.comp_surj (fun _ => 1)
    (fun w => QuotientGroup.mk (Matrix.GeneralLinearGroup.map w.embedding γ)) hres
  have haOne : a 1 = 1 := by
    apply P.comp_ext
    · intro v
      simp only [haF, map_one]
    · intro w
      simp only [haC, map_one, QuotientGroup.mk_one]
  have haMul (γ δ : GL (Fin 2) F) : a (γ * δ) = a γ * a δ := by
    apply P.comp_ext
    · intro v
      simp only [haF, map_mul, mul_one]
    · intro w
      simp only [haC, map_mul, QuotientGroup.mk_mul]
  let arch : GL (Fin 2) F →* P.RP :=
    { toFun := a
      map_one' := haOne
      map_mul' := haMul }
  have harchF (γ : GL (Fin 2) F) (v : FinPlace F) : P.compF v (arch γ) = 1 := haF γ v
  have harchC (γ : GL (Fin 2) F) (w : InfinitePlace F) :
      P.compC w (arch γ) = P.compC w (P.ratRP γ) :=
    (haC γ w).trans (P.compC_ratRP w γ).symm
  let fin (γ : GL (Fin 2) F) : P.RP := P.ratRP γ * (arch γ)⁻¹
  have hfinF (γ : GL (Fin 2) F) (v : FinPlace F) :
      P.compF v (fin γ) = P.compF v (P.ratRP γ) := by
    simp only [fin, map_mul, map_inv, harchF, inv_one, mul_one]
  have hfinC (γ : GL (Fin 2) F) (w : InfinitePlace F) : P.compC w (fin γ) = 1 := by
    simp only [fin, map_mul, map_inv, harchC, mul_inv_cancel]
  have hcomm (γ δ : GL (Fin 2) F) : fin γ * arch δ = arch δ * fin γ := by
    apply P.comp_ext
    · intro v
      simp only [map_mul, harchF, mul_one, one_mul]
    · intro w
      simp only [map_mul, hfinC, mul_one, one_mul]
  have hfac (γ : GL (Fin 2) F) : fin γ * arch γ = P.ratRP γ := by
    simp only [fin, mul_assoc, inv_mul_cancel, mul_one]
  have hfacq (γ : GL (Fin 2) F) : P.q (fin γ) * P.q (arch γ) = P.tc.rat γ := by
    rw [← map_mul, hfac, P.q_ratRP]
  have hOne : P.q (fin 1) = 1 := by
    simpa only [map_one, mul_one] using hfacq (1 : GL (Fin 2) F)
  have hMul (γ δ : GL (Fin 2) F) : P.q (fin (γ * δ)) = P.q (fin γ) * P.q (fin δ) := by
    have hc : P.q (arch γ) * P.q (fin δ) = P.q (fin δ) * P.q (arch γ) := by
      simpa only [map_mul] using (congrArg P.q (hcomm δ γ)).symm
    have he : P.q (fin (γ * δ)) * P.q (arch (γ * δ)) =
        (P.q (fin γ) * P.q (fin δ)) * P.q (arch (γ * δ)) := by
      calc
        P.q (fin (γ * δ)) * P.q (arch (γ * δ)) = P.tc.rat (γ * δ) := hfacq _
        _ = P.tc.rat γ * P.tc.rat δ := map_mul _ _ _
        _ = (P.q (fin γ) * P.q (arch γ)) * (P.q (fin δ) * P.q (arch δ)) := by
          rw [hfacq γ, hfacq δ]
        _ = (P.q (fin γ) * P.q (fin δ)) * P.q (arch (γ * δ)) := by
          simp only [map_mul]
          calc
            (P.q (fin γ) * P.q (arch γ)) * (P.q (fin δ) * P.q (arch δ)) =
                P.q (fin γ) * (P.q (arch γ) * P.q (fin δ)) * P.q (arch δ) := by
              simp only [mul_assoc]
            _ = P.q (fin γ) * (P.q (fin δ) * P.q (arch γ)) * P.q (arch δ) := by rw [hc]
            _ = (P.q (fin γ) * P.q (fin δ)) * (P.q (arch γ) * P.q (arch δ)) := by
              simp only [mul_assoc]
    exact mul_right_cancel he
  let ρ : GL (Fin 2) F →* P.tc.G :=
    { toFun := fun γ => P.q (fin γ)
      map_one' := hOne
      map_mul' := hMul }
  exact ⟨ρ, fun γ => ⟨fin γ, rfl, hfinC γ, hfinF γ⟩⟩

end ArtinPrimitiveRoots.A1.Theta
