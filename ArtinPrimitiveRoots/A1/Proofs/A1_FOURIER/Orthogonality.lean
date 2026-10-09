import ArtinPrimitiveRoots.A1.Proofs.A1_FOURIER.EBasic

/-!
# A1-FOURIER part `a1_fourier_orthogonality` (IMPL)

Orthogonality of the characters `x ↦ e(x ν)`, `ν ∈ R`, on a fundamental domain of volume one.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Orthogonality: `∫_K e(x ν) dμ = [ν = 0]` for `ν ∈ R`.

Proof hint: for `ν = 0` the integrand is `1` and `μ K = 1`. For `ν ≠ 0`, `S.diag ν` is a unit of
`F_S` (every component of a nonzero element is nonzero); with `z` from `a1_fourier_e_basic`
put `y = z * (S.diag ν)⁻¹`, so `e(y ν) ≠ 1`. The integrand `h x = e(x ν)` is `R`-periodic by
`hself` and additivity; `K + y` is another fundamental domain, and
`IsAddFundamentalDomain.setIntegral_eq` plus translation invariance of `μ` give
`∫_K h = ∫_K h(x + y) = e(y ν) ∫_K h`, so `∫_K h = 0`. Integrability: `‖h‖ = 1`, `μ K = 1`.
Uses: `a1_fourier_e_basic`. Used by: `a1_fourier_poisson_abstract`. -/
theorem a1_fourier_orthogonality (S : SData F CE condη) (A : AddCharData F)
    {mS : MeasurableSpace S.FS} [BorelSpace S.FS]
    (μ : Measure S.FS) [μ.IsAddHaarMeasure]
    (K : Set S.FS) (hKm : MeasurableSet K)
    (hK : ∀ x : S.FS, ∃! p : S.R × S.FS, p.2 ∈ K ∧ x = S.diag (p.1 : F) + p.2)
    (hKμ : μ K = 1)
    (hself : ∀ r s : S.R, S.e A (S.diag (r : F) * S.diag (s : F)) = 1)
    (ν : S.R) :
    ∫ x in K, S.e A (x * S.diag (ν : F)) ∂μ = if (ν : F) = 0 then 1 else 0 := by
  classical
  obtain ⟨_, hnorm, hadd, ⟨z, hz⟩⟩ := a1_fourier_e_basic S A
  have he0 : S.e A 0 = 1 := by
    have h00 : S.e A 0 = S.e A 0 * S.e A 0 := by
      have h := hadd 0 0
      simpa using h
    have hne : S.e A 0 ≠ 0 := by
      intro h0
      have hnorm0 := hnorm 0
      rw [h0, norm_zero] at hnorm0
      norm_num at hnorm0
    have h1 : S.e A 0 * 1 = S.e A 0 * S.e A 0 := by rw [mul_one]; exact h00
    have h12 : (1 : ℂ) = S.e A 0 := mul_left_cancel₀ hne h1
    exact h12.symm
  by_cases hν0 : (ν : F) = 0
  · have hdiag0 : S.diag (ν : F) = 0 := by rw [hν0, map_zero]
    have hh1 : ∀ x : S.FS, S.e A (x * S.diag (ν : F)) = 1 := by
      intro x
      rw [hdiag0, mul_zero, he0]
    have hI1 : ∫ x in K, S.e A (x * S.diag (ν : F)) ∂μ = 1 := by
      simp_rw [hh1]
      have hreal : μ.real K = 1 := by
        have h1 : μ.real K = (μ K).toReal := rfl
        rw [h1, hKμ, ENNReal.toReal_one]
      rw [setIntegral_const, hreal, one_smul]
    rw [if_pos hν0]
    exact hI1
  · -- ν ≠ 0: build y with e(y ν) ≠ 1
    have hfin_ne : ∀ v : S.Sf, (S.diag (ν : F)).1 v ≠ 0 := by
      intro v
      have h1 : (S.diag (ν : F)).1 v = algebraMap F (v.1.adicCompletion F) (ν : F) := rfl
      rw [h1]
      intro h0
      apply hν0
      have hinj : Function.Injective (algebraMap F (v.1.adicCompletion F)) :=
        RingHom.injective (algebraMap F (v.1.adicCompletion F))
      have h2 : algebraMap F (v.1.adicCompletion F) (ν : F) =
          algebraMap F (v.1.adicCompletion F) 0 := by simpa using h0
      have h3 := hinj h2
      simpa using h3
    have harch_ne : ∀ w : InfinitePlace F, (S.diag (ν : F)).2 w ≠ 0 := by
      intro w
      have h1 : (S.diag (ν : F)).2 w = w.embedding (ν : F) := rfl
      rw [h1]
      intro h0
      apply hν0
      have hinj : Function.Injective (w.embedding) := RingHom.injective w.embedding
      have h2 : w.embedding (ν : F) = w.embedding 0 := by simpa using h0
      have h3 := hinj h2
      simpa using h3
    have hmul1 : S.diag (ν : F) *
        ((fun v => ((S.diag (ν : F)).1 v)⁻¹,
          fun w => ((S.diag (ν : F)).2 w)⁻¹) : S.FS) = 1 := by
      apply Prod.ext
      · funext v
        exact mul_inv_cancel₀ (hfin_ne v)
      · funext w
        exact mul_inv_cancel₀ (harch_ne w)
    have hmul2 : ((fun v => ((S.diag (ν : F)).1 v)⁻¹,
          fun w => ((S.diag (ν : F)).2 w)⁻¹) : S.FS) * S.diag (ν : F) = 1 := by
      rw [mul_comm, hmul1]
    set y : S.FS := z *
      ((fun v => ((S.diag (ν : F)).1 v)⁻¹,
        fun w => ((S.diag (ν : F)).2 w)⁻¹) : S.FS) with hy_def
    have hy : y * S.diag (ν : F) = z := by
      rw [hy_def]
      calc (z * ((fun v => ((S.diag (ν : F)).1 v)⁻¹,
            fun w => ((S.diag (ν : F)).2 w)⁻¹) : S.FS)) * S.diag (ν : F)
          = z * ((((fun v => ((S.diag (ν : F)).1 v)⁻¹,
            fun w => ((S.diag (ν : F)).2 w)⁻¹) : S.FS)) * S.diag (ν : F)) := by ring
        _ = z * 1 := by rw [hmul2]
        _ = z := mul_one _
    have hc : S.e A (y * S.diag (ν : F)) ≠ 1 := by rw [hy]; exact hz
    have hperV : ∀ (g : S.R) (x : S.FS),
        S.e A ((S.diag (g : F) + x) * S.diag (ν : F)) =
          S.e A (x * S.diag (ν : F)) := by
      intro g x
      have h1 : (S.diag (g : F) + x) * S.diag (ν : F) =
          x * S.diag (ν : F) + S.diag (g : F) * S.diag (ν : F) := by ring
      rw [h1, hadd, hself g ν, mul_one]
    have hshift : ∀ x : S.FS, S.e A ((y + x) * S.diag (ν : F)) =
        S.e A (y * S.diag (ν : F)) * S.e A (x * S.diag (ν : F)) := by
      intro x
      have h1 : (y + x) * S.diag (ν : F) =
          y * S.diag (ν : F) + x * S.diag (ν : F) := by ring
      rw [h1, hadd]
    -- fundamental domain infrastructure
    letI : AddAction S.R S.FS :=
      { vadd := fun r x => S.diag (r : F) + x
        add_vadd := by
          intro r s x
          change S.diag ((r + s : S.R) : F) + x =
            S.diag (r : F) + (S.diag (s : F) + x)
          simp only [Subalgebra.coe_add, map_add]
          abel
        zero_vadd := by
          intro x
          change S.diag (0 : F) + x = x
          simp }
    letI : MeasurableConstVAdd S.R S.FS := ⟨fun r => by
      change Measurable (fun x : S.FS => S.diag (r : F) + x)
      fun_prop⟩
    letI : VAddInvariantMeasure S.R S.FS μ := ⟨by
      intro r T hT
      change μ ((fun x : S.FS => S.diag (r : F) + x) ⁻¹' T) = μ T
      have hmap : Measure.map (fun x : S.FS => S.diag (r : F) + x) μ = μ :=
        MeasureTheory.map_add_left_eq_self μ (S.diag (r : F))
      have h1 : μ ((fun x : S.FS => S.diag (r : F) + x) ⁻¹' T) =
          Measure.map (fun x : S.FS => S.diag (r : F) + x) μ T := by
        rw [Measure.map_apply (by fun_prop : Measurable (fun x : S.FS => S.diag (r : F) + x)) hT]
      rw [h1, hmap]⟩
    letI : Countable F := by
      letI : Countable ℚ := inferInstance
      exact Finsupp.Countable.of_moduleFinite (R := ℚ) (M := F)
    letI : Countable S.R := inferInstance
    have hKfd : MeasureTheory.IsAddFundamentalDomain S.R K μ := by
      apply MeasureTheory.IsAddFundamentalDomain.mk' hKm.nullMeasurableSet
      intro x
      obtain ⟨p, hp, huniq⟩ := hK x
      rcases p with ⟨r, k⟩
      rcases hp with ⟨hk, hrep⟩
      refine ⟨-r, ?_, ?_⟩
      · change S.diag ((-r : S.R) : F) + x ∈ K
        rw [hrep]
        simpa [map_neg] using hk
      · intro g hg
        have hrep' : x = S.diag ((-g : S.R) : F) + (g +ᵥ x) := by
          change x = S.diag ((-g : S.R) : F) + (S.diag (g : F) + x)
          simp [map_neg]
        have hpair :
            ((-g : S.R), g +ᵥ x).2 ∈ K ∧
              x = S.diag (((-g : S.R), g +ᵥ x).1 : F) + ((-g : S.R), g +ᵥ x).2 := by
          exact ⟨hg, hrep'⟩
        have heq := huniq (-g, g +ᵥ x) hpair
        have hfirst : -g = r := congrArg Prod.fst heq
        simpa using congrArg (fun a : S.R => -a) hfirst
    have hfQMP : Measure.QuasiMeasurePreserving (⇑(Equiv.addLeft y).symm) μ μ := by
      have hmp : MeasurePreserving (fun x : S.FS => -y + x) μ μ :=
        measurePreserving_add_left μ (-y)
      have heq : (⇑(Equiv.addLeft y).symm : S.FS → S.FS) =
          (fun x : S.FS => -y + x) := rfl
      rw [heq]
      exact hmp.quasiMeasurePreserving
    have hef : ∀ g : S.R, Function.Semiconj ⇑(Equiv.addLeft y)
        (fun x : S.FS => (Equiv.refl S.R) g +ᵥ x) (fun x : S.FS => g +ᵥ x) := by
      intro g x
      show y + (S.diag (((Equiv.refl S.R) g : S.R) : F) + x) =
        S.diag (g : F) + (y + x)
      simp only [Equiv.refl_apply]
      abel
    have hKy : MeasureTheory.IsAddFundamentalDomain S.R (⇑(Equiv.addLeft y) '' K) μ :=
      hKfd.image_of_equiv (Equiv.addLeft y) hfQMP (Equiv.refl S.R) hef
    have hperV' : ∀ (g : S.R) (x : S.FS),
        (fun x : S.FS => S.e A (x * S.diag (ν : F))) (g +ᵥ x) =
          (fun x : S.FS => S.e A (x * S.diag (ν : F))) x := by
      intro g x
      show S.e A ((S.diag (g : F) + x) * S.diag (ν : F)) = _
      exact hperV g x
    have hIeq1 : (∫ x in K, S.e A (x * S.diag (ν : F)) ∂μ) =
        ∫ x in ⇑(Equiv.addLeft y) '' K, S.e A (x * S.diag (ν : F)) ∂μ :=
      hKfd.setIntegral_eq hKy hperV'
    have hmp : MeasurePreserving (fun x : S.FS => y + x) μ μ :=
      measurePreserving_add_left μ y
    have hembed : MeasurableEmbedding (fun x : S.FS => y + x) :=
      (MeasurableEquiv.addLeft y).measurableEmbedding
    have htrans : (∫ x in ⇑(Equiv.addLeft y) '' K, S.e A (x * S.diag (ν : F)) ∂μ) =
        ∫ x in K, S.e A ((y + x) * S.diag (ν : F)) ∂μ := by
      have h1 := hmp.setIntegral_image_emb hembed
        (fun x : S.FS => S.e A (x * S.diag (ν : F))) K
      simpa using h1
    have hfactor : (∫ x in K, S.e A ((y + x) * S.diag (ν : F)) ∂μ) =
        S.e A (y * S.diag (ν : F)) * ∫ x in K, S.e A (x * S.diag (ν : F)) ∂μ := by
      simp_rw [hshift]
      rw [integral_const_mul]
    have hIeq : (∫ x in K, S.e A (x * S.diag (ν : F)) ∂μ) =
        S.e A (y * S.diag (ν : F)) * ∫ x in K, S.e A (x * S.diag (ν : F)) ∂μ := by
      calc (∫ x in K, S.e A (x * S.diag (ν : F)) ∂μ)
          = ∫ x in ⇑(Equiv.addLeft y) '' K, S.e A (x * S.diag (ν : F)) ∂μ := hIeq1
        _ = ∫ x in K, S.e A ((y + x) * S.diag (ν : F)) ∂μ := htrans
        _ = _ := hfactor
    have hI0 : (∫ x in K, S.e A (x * S.diag (ν : F)) ∂μ) = 0 := by
      have hcc : (1 : ℂ) - S.e A (y * S.diag (ν : F)) ≠ 0 :=
        sub_ne_zero.mpr (Ne.symm hc)
      have h0 : ((1 : ℂ) - S.e A (y * S.diag (ν : F))) *
          (∫ x in K, S.e A (x * S.diag (ν : F)) ∂μ) = 0 := by
        calc ((1 : ℂ) - S.e A (y * S.diag (ν : F))) *
              (∫ x in K, S.e A (x * S.diag (ν : F)) ∂μ)
            = (∫ x in K, S.e A (x * S.diag (ν : F)) ∂μ) -
              S.e A (y * S.diag (ν : F)) * ∫ x in K, S.e A (x * S.diag (ν : F)) ∂μ := by ring
          _ = 0 := by rw [← hIeq, sub_self]
      exact (mul_eq_zero.mp h0).resolve_left hcc
    rw [if_neg hν0]
    exact hI0

end ArtinPrimitiveRoots.A1
