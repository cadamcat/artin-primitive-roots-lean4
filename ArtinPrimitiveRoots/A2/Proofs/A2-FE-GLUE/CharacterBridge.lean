import ArtinPrimitiveRoots.A2.ZeroFree.Results
import ArtinPrimitiveRoots.A2.Proofs.QS_ANALYTIC.RNDict

/-!
# A2-FE-GLUE: primitive idelic character to HK ray character
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ClassFieldTheory
open scoped NumberField Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.A2FreqP

variable {F : Type} [Field F] [NumberField F]

private theorem heckeChar_inv_apply (ω : ArtinPrimitiveRoots.A1.HeckeChar F)
    (x : IdeleClassGroup (𝓞 F) F) : (ω⁻¹) x = (ω x)⁻¹ := by
  rfl

theorem exists_primitive_ray_bridge [IsTotallyComplex F]
    (ω : ArtinPrimitiveRoots.A1.HeckeChar F) (hfin : IsOfFinOrder ω) (hnon : ω ≠ 1)
    (f : Ideal (𝓞 F)) (hf : ArtinPrimitiveRoots.A2.IsPrimitiveConductor ω f) :
    ∃ m : RayClassModulus F, ∃ ψ : RayClassGroup m →* ℂˣ,
      ArtinPrimitiveRoots.Hecke.modulusNorm m = Ideal.absNorm f ∧
      ψ ≠ 1 ∧ ArtinPrimitiveRoots.Hecke.HKPrimitive ψ ∧
      (∀ s : ℂ, 1 < s.re → ArtinPrimitiveRoots.A2.heckeLSeries ω s =
        ArtinPrimitiveRoots.Hecke.LSeriesRay ψ s) ∧
      (∀ s : ℂ, 1 < s.re → ArtinPrimitiveRoots.A2.heckeLSeries (ω⁻¹) s =
        ArtinPrimitiveRoots.Hecke.LSeriesRay (ψ⁻¹) s) := by
  classical
  obtain ⟨m, ψ, hm, -, hval⟩ :=
    ArtinPrimitiveRoots.Dictionary.exists_rayClass_of_heckeChar ω hfin f hf.1 hf.2.1
  have hcop : ∀ v : ArtinPrimitiveRoots.A1.FinPlace F,
      v ∉ m.finitePart.support → ArtinPrimitiveRoots.Hecke.IsCoprimeTo m v.asIdeal := by
    intro v hv
    refine ⟨v.ne_bot, ?_⟩
    intro w hw
    have hwv : w ≠ v := fun h => hv (h ▸ hw)
    simpa [ArtinPrimitiveRoots.Hecke.idealUnit] using
      FractionalIdeal.count_maximal_coprime F w (Ne.symm hwv)
  have hunr : ∀ v : ArtinPrimitiveRoots.A1.FinPlace F,
      v ∉ m.finitePart.support → ω.UnramifiedAt v := by
    intro v hv
    refine ArtinPrimitiveRoots.A2.qsa_unramifiedAt_of_conductorDvd ω f hf.2.1 v ?_
    rw [← hm, ArtinPrimitiveRoots.Dictionary.idealExp_modulusIdeal]
    exact Finsupp.notMem_support_iff.mp hv
  have hnonRay : ψ ≠ 1 := by
    intro hψ
    have hun1 (v : ArtinPrimitiveRoots.A1.FinPlace F) :
        (1 : ArtinPrimitiveRoots.A1.HeckeChar F).UnramifiedAt v := by
      intro u hu huinv
      rfl
    apply hnon
    refine ArtinPrimitiveRoots.Dictionary.heckeChar_eq_of_primeValue ω 1
      m.finitePart.support ?_
    intro v hv
    have hprime : ω.primeValue v = 1 := by
      rw [← hval v hv, hψ]
      simp [ArtinPrimitiveRoots.Hecke.charValue, hcop v hv]
    have hprime' : ω.primeValue v =
        (1 : ArtinPrimitiveRoots.A1.HeckeChar F).primeValue v := by
      rw [hprime]
      simp [ArtinPrimitiveRoots.A1.HeckeChar.primeValue, hun1 v,
        ArtinPrimitiveRoots.A1.HeckeChar.loc]
    exact ⟨hunr v hv, hun1 v, hprime'⟩
  have hprim := ArtinPrimitiveRoots.A2.qsa_hkPrimitive_of_primitiveConductor
    ω f hf ψ hm hval
  have hseries : ∀ s : ℂ, 1 < s.re →
      ArtinPrimitiveRoots.A2.heckeLSeries ω s = ArtinPrimitiveRoots.Hecke.LSeriesRay ψ s := by
    intro s hs
    refine ArtinPrimitiveRoots.A2.qsa_heckeLSeries_eq_LSeriesRay ω ψ ?_ hs
    intro I hI
    by_cases hcopI : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m I
    · exact ArtinPrimitiveRoots.Dictionary.idealValue_eq_charValue ψ ω
        (fun v hv => ⟨hunr v hv, (hval v hv).symm⟩) I hcopI
    · rw [ArtinPrimitiveRoots.Hecke.charValue, dif_neg hcopI]
      have hex : ∃ v ∈ m.finitePart.support, v.asIdeal ∣ I := by
        by_contra hnot
        push_neg at hnot
        apply hcopI
        refine ⟨hI, ?_⟩
        intro v hv
        simp only [ArtinPrimitiveRoots.Hecke.idealUnit, Units.val_mk0]
        rw [FractionalIdeal.count_coe F v hI]
        have hcount :=
          (Associates.count_ne_zero_iff_dvd hI v.irreducible).not.mpr (hnot v hv)
        push_neg at hcount
        exact_mod_cast hcount
      obtain ⟨v, hv, hvI⟩ := hex
      have hvf : v.asIdeal ∣ f := by
        rw [← hm]
        unfold ArtinPrimitiveRoots.Dictionary.modulusIdeal
        have hpos : m.finitePart v ≠ 0 := Finsupp.mem_support_iff.mp hv
        exact (dvd_pow_self v.asIdeal hpos).trans
          (Finset.dvd_prod_of_mem (fun w => w.asIdeal ^ m.finitePart w) hv)
      exact ArtinPrimitiveRoots.A2.qs_idealValue_eq_zero_of_conductor_M0
        ω f hf v.asIdeal I v.isPrime v.ne_bot hvf hI hvI
  have hfinInv : IsOfFinOrder (ω⁻¹) := IsOfFinOrder.inv hfin
  have hcondInv : (ω⁻¹).ConductorDvd f := by
    intro v u hu huinv hv
    have hloc : (ω⁻¹).loc v u = (ω.loc v u)⁻¹ := by
      simp only [ArtinPrimitiveRoots.A1.HeckeChar.loc, MonoidHom.comp_apply]
      exact heckeChar_inv_apply ω _
    rw [hloc, hf.2.1 v u hu huinv hv]
    simp
  have hprimInv : ArtinPrimitiveRoots.A2.IsPrimitiveConductor (ω⁻¹) f := by
    refine ⟨hf.1, hcondInv, ?_⟩
    intro g hg hcg
    apply hf.2.2 g hg
    intro v u hu huinv hv
    have hloc : (ω⁻¹).loc v u = (ω.loc v u)⁻¹ := by
      simp only [ArtinPrimitiveRoots.A1.HeckeChar.loc, MonoidHom.comp_apply]
      exact heckeChar_inv_apply ω _
    have h := hcg v u hu huinv hv
    rw [hloc] at h
    exact inv_eq_one.mp h
  have hunrInv : ∀ v : ArtinPrimitiveRoots.A1.FinPlace F,
      v ∉ m.finitePart.support → (ω⁻¹).UnramifiedAt v := by
    intro v hv
    intro u hu huinv
    have h := hunr v hv u hu huinv
    have hloc : (ω⁻¹).loc v u = (ω.loc v u)⁻¹ := by
      simp only [ArtinPrimitiveRoots.A1.HeckeChar.loc, MonoidHom.comp_apply]
      exact heckeChar_inv_apply ω _
    rw [hloc, h]
    simp
  have hvalInv : ∀ v : ArtinPrimitiveRoots.A1.FinPlace F,
      v ∉ m.finitePart.support →
        ArtinPrimitiveRoots.Hecke.charValue (ψ⁻¹) v.asIdeal = (ω⁻¹).primeValue v := by
    intro v hv
    have hcharInv : ArtinPrimitiveRoots.Hecke.charValue (ψ⁻¹) v.asIdeal =
        (ArtinPrimitiveRoots.Hecke.charValue ψ v.asIdeal)⁻¹ := by
      simp [ArtinPrimitiveRoots.Hecke.charValue, hcop v hv]
    have hprimeInv : (ω⁻¹).primeValue v = (ω.primeValue v)⁻¹ := by
      simp only [ArtinPrimitiveRoots.A1.HeckeChar.primeValue,
        if_pos (hunrInv v hv), if_pos (hunr v hv)]
      have hloc : (ω⁻¹).loc v
          (ArtinPrimitiveRoots.A1.toLoc v
            (Units.mk0 (ArtinPrimitiveRoots.A1.unif v)
              (ArtinPrimitiveRoots.A1.unif_ne_zero v))) =
          (ω.loc v (ArtinPrimitiveRoots.A1.toLoc v
            (Units.mk0 (ArtinPrimitiveRoots.A1.unif v)
              (ArtinPrimitiveRoots.A1.unif_ne_zero v))) : ℂˣ)⁻¹ := by
        simp only [ArtinPrimitiveRoots.A1.HeckeChar.loc, MonoidHom.comp_apply]
        exact heckeChar_inv_apply ω _
      rw [hloc]
      simp
    calc
      ArtinPrimitiveRoots.Hecke.charValue (ψ⁻¹) v.asIdeal =
          (ArtinPrimitiveRoots.Hecke.charValue ψ v.asIdeal)⁻¹ := hcharInv
      _ = (ω.primeValue v)⁻¹ := by rw [hval v hv]
      _ = (ω⁻¹).primeValue v := hprimeInv.symm
  have hseriesInv : ∀ s : ℂ, 1 < s.re →
      ArtinPrimitiveRoots.A2.heckeLSeries (ω⁻¹) s =
        ArtinPrimitiveRoots.Hecke.LSeriesRay (ψ⁻¹) s := by
    intro s hs
    refine ArtinPrimitiveRoots.A2.qsa_heckeLSeries_eq_LSeriesRay (ω⁻¹) (ψ⁻¹) ?_ hs
    intro I hI
    by_cases hcopI : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m I
    · exact ArtinPrimitiveRoots.Dictionary.idealValue_eq_charValue (ψ⁻¹) (ω⁻¹)
        (fun v hv => ⟨hunrInv v hv, (hvalInv v hv).symm⟩) I hcopI
    · rw [ArtinPrimitiveRoots.Hecke.charValue, dif_neg hcopI]
      have hex : ∃ v ∈ m.finitePart.support, v.asIdeal ∣ I := by
        by_contra hnot
        push_neg at hnot
        apply hcopI
        refine ⟨hI, ?_⟩
        intro v hv
        simp only [ArtinPrimitiveRoots.Hecke.idealUnit, Units.val_mk0]
        rw [FractionalIdeal.count_coe F v hI]
        have hcount :=
          (Associates.count_ne_zero_iff_dvd hI v.irreducible).not.mpr (hnot v hv)
        push_neg at hcount
        exact_mod_cast hcount
      obtain ⟨v, hv, hvI⟩ := hex
      have hvf : v.asIdeal ∣ f := by
        rw [← hm]
        unfold ArtinPrimitiveRoots.Dictionary.modulusIdeal
        have hpos : m.finitePart v ≠ 0 := Finsupp.mem_support_iff.mp hv
        exact (dvd_pow_self v.asIdeal hpos).trans
          (Finset.dvd_prod_of_mem (fun w => w.asIdeal ^ m.finitePart w) hv)
      exact ArtinPrimitiveRoots.A2.qs_idealValue_eq_zero_of_conductor_M0
        (ω⁻¹) f hprimInv v.asIdeal I v.isPrime v.ne_bot hvf hI hvI
  refine ⟨m, ψ, ?_, hnonRay, hprim, hseries, hseriesInv⟩
  rw [ArtinPrimitiveRoots.Dictionary.modulusNorm_eq_absNorm, hm]

end ArtinPrimitiveRoots.Proofs.A2FreqP
