import ArtinPrimitiveRoots.A2.Interface

set_option autoImplicit false
set_option maxHeartbeats 800000

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_rffwd_sol
open ArtinPrimitiveRoots.A1 ArtinPrimitiveRoots.A2

theorem generator_orbit_injective {F : Type} [Field F] [NumberField F]
    {CE : ℕ} {condη : Ideal (𝓞 F)}
    (D : FieldData F) (S : SData F CE condη) (H : HilbertData F)
    (Bd : BData S H) (bc : BalancedChoices D S H Bd) :
    Function.Injective (fun p : S.ExtIdeal × Gamma S =>
      (p.2.1 : Fˣ) * bc.gen p.1) := by
  classical
  have hSameIdeal (x : F) (I J : Ideal (𝓞 F))
      (hI : S.IsGen x I) (hJ : S.IsGen x J) : I = J := by
    have hI0 : I ≠ 0 := by simpa [Ideal.zero_eq_bot] using hI.1.1
    have hJ0 : J ≠ 0 := by simpa [Ideal.zero_eq_bot] using hJ.1.1
    have hcounts : ∀ v : FinPlace F,
        FractionalIdeal.count F v (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
          FractionalIdeal.count F v (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
      intro v
      by_cases hv : v ∈ S.Sf
      · have hnotI : ¬ v.asIdeal ∣ I := by
          intro hdiv
          exact hI.1.2 v hv (Ideal.dvd_iff_le.mp hdiv)
        have hnotJ : ¬ v.asIdeal ∣ J := by
          intro hdiv
          exact hJ.1.2 v hv (Ideal.dvd_iff_le.mp hdiv)
        have hcountI : (Associates.mk v.asIdeal).count (Associates.mk I).factors = 0 := by
          by_contra hn
          exact hnotI ((Associates.count_ne_zero_iff_dvd hI0 v.irreducible).mp hn)
        have hcountJ : (Associates.mk v.asIdeal).count (Associates.mk J).factors = 0 := by
          by_contra hn
          exact hnotJ ((Associates.count_ne_zero_iff_dvd hJ0 v.irreducible).mp hn)
        rw [FractionalIdeal.count_coe F v hI0, FractionalIdeal.count_coe F v hJ0,
          hcountI, hcountJ]
      · exact (hI.2.2 v hv).symm.trans (hJ.2.2 v hv)
    let gI : ClassFieldTheory.NumberFieldFractionalIdealGroup F :=
      Units.mk0 (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
        (FractionalIdeal.coeIdeal_ne_zero.mpr hI0)
    let gJ : ClassFieldTheory.NumberFieldFractionalIdealGroup F :=
      Units.mk0 (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
        (FractionalIdeal.coeIdeal_ne_zero.mpr hJ0)
    have hg : gI = gJ := by
      apply ClassFieldTheory.NumberFieldFractionalIdealGroup.ext_count
      intro v
      change FractionalIdeal.count F v
          (gI : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
        FractionalIdeal.count F v (gJ : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
      simpa [gI, gJ] using hcounts v
    have hfrac : (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
        (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
      have hval := congrArg
        (fun g : ClassFieldTheory.NumberFieldFractionalIdealGroup F =>
          (g : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)) hg
      simpa [gI, gJ] using hval
    exact FractionalIdeal.coeIdeal_injective hfrac
  intro p q hpq
  have hp := ArtinPrimitiveRoots.Proofs.A1Generators.isGen_mul_sUnit S p.2.1
    (bc.gen p.1) (bc.gen_spec p.1).1
  have hq := ArtinPrimitiveRoots.Proofs.A1Generators.isGen_mul_sUnit S q.2.1
    (bc.gen q.1) (bc.gen_spec q.1).1
  change (p.2.1 : Fˣ) * bc.gen p.1 = (q.2.1 : Fˣ) * bc.gen q.1 at hpq
  rw [hpq] at hp
  have hIdeal : p.1 = q.1 :=
    Subtype.ext (hSameIdeal _ p.1.1 q.1.1 hp hq)
  have hGamma : p.2 = q.2 := by
    apply Subtype.ext
    apply Subtype.ext
    exact mul_right_cancel (by simpa only [hIdeal] using hpq)
  exact Prod.ext hIdeal hGamma

end ArtinPrimitiveRoots.Proofs.a2_rffwd_sol
