import ArtinPrimitiveRoots.A2.Interface

set_option autoImplicit false
set_option maxHeartbeats 800000

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_rffwd_sol
open ArtinPrimitiveRoots.A1 ArtinPrimitiveRoots.A2

theorem rfSCharacter_generator_class {F : Type} [Field F] [NumberField F]
    {CE : ℕ} {condη : Ideal (𝓞 F)}
    (D : FieldData F) (S : SData F CE condη) (H : HilbertData F)
    (Bd : BData S H) (ϑ : HeckeChar F)
    (houtside : ∀ v : FinPlace F, v ∉ S.Sf → ϑ.UnramifiedAt v)
    (ε ε' : S.US) (hclass : unitSixClass S ε = unitSixClass S ε')
    (J : Ideal (𝓞 F)) (hJ : S.IsExterior J) (a : Fˣ)
    (ha : S.IsGen (a : F) J ∧ Bd.Allowed a) :
    rfSCharacter D S H ϑ ε (S.diagU a) =
      ϑ.idealValue J * chiIdealPow D J ((ε' : Fˣ) : F) 1 := by
  classical
  let y : S.FSˣ := S.diagU a
  have hmem : ε / ε' ∈ Gamma S :=
    (QuotientGroup.eq_iff_div_mem).mp (by simpa [unitSixClass] using hclass)
  obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hmem
  have hu' : u ^ 6 = ε / ε' := by
    simpa [sixthPowerOnUS] using hu
  have heps : ε = ε' * u ^ 6 := by
    calc
      ε = ε' * (ε / ε') := (mul_div_cancel ε' ε).symm
      _ = ε' * u ^ 6 := by rw [← hu']
  have hmulHS (x z : S.FSˣ) :
      S.HS H (x * z) y = S.HS H x y * S.HS H z y := by
    unfold SData.HS
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro v hv
    exact H.mul_left v.1 (S.compU v x) (S.compU v z) (S.compU v y)
  have hsixHS (x : S.FSˣ) : S.HS H (x ^ 6) y = 1 := by
    unfold SData.HS
    apply Finset.prod_eq_one
    intro v hv
    exact H.sixth_power v.1 (S.compU v (x ^ 6)) (S.compU v y)
      ⟨S.compU v x, by simp [SData.compU]⟩
  have hdiag : S.diagU ((ε' * u ^ 6 : S.US) : Fˣ) =
      S.diagU (ε' : Fˣ) * (S.diagU (u : Fˣ)) ^ 6 := by
    change S.diagU ((ε' : Fˣ) * (u : Fˣ) ^ 6) =
      S.diagU (ε' : Fˣ) * (S.diagU (u : Fˣ)) ^ 6
    rw [map_mul, map_pow]
  have hhs : S.HS H (S.diagU ε) y = S.HS H (S.diagU ε') y := by
    rw [heps, hdiag, hmulHS, hsixHS, mul_one]
  unfold rfSCharacter lambdaEpsilon
  rw [hhs]
  have hLS := rf_heckeChar_idealValue_eq_LS_of_gen D S ϑ houtside J a ha.1
  rw [hLS]
  have hsymbol := unit_symbol D S H Bd J hJ a ε' ha ε'.property
  rw [← hsymbol]

end ArtinPrimitiveRoots.Proofs.a2_rffwd_sol
