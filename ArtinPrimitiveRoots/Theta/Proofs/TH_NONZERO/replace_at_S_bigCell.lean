import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_WHIT.analyticFamily_bigCell_rtr

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Replace every exceptional finite section by prescribed compactly supported big-cell data. -/
theorem replace_at_S_bigCell (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) (Fam : AnalyticFamily P G μ)
    (hT : Fam.T0 = S.Sf)
    (φ : ∀ v : S.Sf, v.1.adicCompletion F → (G.T v.1).V)
    (hφ : ∀ v, IsLocallyConstant (φ v)) (hcφ : ∀ v, HasCompactSupport (φ v)) :
    ∃ Fam' : AnalyticFamily P G μ, Fam'.T0 = S.Sf ∧
      ∀ v : S.Sf, ∀ s : ℂ,
        (Fam'.sec s).f v.1 = bigCell (P.loc v.1) (G.T v.1) s (φ v) := by
  have hmany (U : Finset S.Sf) :
      ∃ Fam' : AnalyticFamily P G μ, Fam'.T0 = S.Sf ∧
        ∀ v ∈ U, ∀ s : ℂ,
          (Fam'.sec s).f v.1 = bigCell (P.loc v.1) (G.T v.1) s (φ v) := by
    induction U using Finset.induction_on with
    | empty =>
        refine ⟨Fam, hT, ?_⟩
        intro v hv
        simp at hv
    | @insert a U ha ih =>
        obtain ⟨FamU, hU, hfixed⟩ := ih
        obtain ⟨Fam', hExt, hnew⟩ :=
          analyticFamily_bigCell_rtr FamU a.1 (φ a) (hφ a) (hcφ a) 1
        refine ⟨Fam', ?_, ?_⟩
        · rw [hExt.1, hU, Finset.insert_eq_of_mem a.property]
        · intro v hv s
          rcases Finset.mem_insert.mp hv with rfl | hv
          · funext g
            have hval := congrFun (hnew s) g
            change (Fam'.sec s).f v.1 g =
              bigCell (P.loc v.1) (G.T v.1) s (φ v) (g * 1) at hval
            simpa only [mul_one] using hval
          · have hne : v.1 ≠ a.1 := by
              intro heq
              have hva : v = a := Subtype.ext heq
              subst v
              exact ha hv
            rw [hExt.2 s v.1 hne]
            exact hfixed v hv s
  obtain ⟨Fam', hT', hfixed⟩ := hmany Finset.univ
  exact ⟨Fam', hT', fun v => hfixed v (Finset.mem_univ v)⟩

end ArtinPrimitiveRoots.A1.Theta
