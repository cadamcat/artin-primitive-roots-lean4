import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_WHIT.FullJacquet

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

/-- Changing a nonzero local Fourier frequency is right translation by its torus lift. -/
theorem whit_local_fourier_dilation {D : FieldData F} {H : HilbertData F}
    {v : FinPlace F} (L : FinLocalCover D H v) (T : TorusRep D H v)
    (A : AddCharData F) (μ : LocHaar v) {s : ℂ} (hs : 0 < s.re)
    (f : L.L → T.V) (hf : IsSection L T s f)
    (b : (v.adicCompletion F)ˣ) (g : L.L) :
    Integrable (fun u => A.ψ v (-((b : v.adicCompletion F) * u)) •
      f (L.w * L.n (Multiplicative.ofAdd u) * g)) μ.μ ∧
      (∫ u, A.ψ v (-((b : v.adicCompletion F) * u)) •
        f (L.w * L.n (Multiplicative.ofAdd u) * g) ∂μ.μ) =
        ((absFin v b : ℂ) ^ (s - (1 : ℂ) / 2)) •
          T.σa b (jacquet L A μ (rtr (L.a b * g) f)) := by
  classical
  let K := v.adicCompletion F
  let base : K → T.V := fun u => f (L.w * L.n (Multiplicative.ofAdd u) * g)
  let kernel : K → T.V := fun u => A.ψ v (-((b : K) * u)) • base u
  have hbase : Integrable base μ.μ :=
    (intertwine_isSection L T μ s hs f hf).1 g
  have hopen : IsOpen (v.adicCompletionIntegers F : Set K) :=
    Valued.isOpen_valuationSubring K
  have hpsi : IsLocallyConstant (A.ψ v) := by
    apply (IsLocallyConstant.iff_exists_open _).2
    intro t
    refine ⟨{y : K | y - t ∈ v.adicCompletionIntegers F},
      hopen.preimage (continuous_id.sub continuous_const), ?_, ?_⟩
    · change t - t ∈ v.adicCompletionIntegers F
      rw [sub_self]
      exact (v.adicCompletionIntegers F).zero_mem
    · intro y hy
      have hi := A.integral v (y - t) hy
      simpa only [sub_add_cancel, hi, one_mul] using
        (A.ψ v).map_add_eq_mul (y - t) t
  have hphase : Continuous (fun u : K => A.ψ v (-((b : K) * u))) :=
    hpsi.continuous.comp (continuous_neg.comp (continuous_const.mul continuous_id))
  have hnorm (u : K) : ‖kernel u‖ = ‖base u‖ := by
    simp only [kernel, norm_smul, whit_psi_norm, one_mul]
  have hstrong : AEStronglyMeasurable kernel μ.μ :=
    hphase.aestronglyMeasurable.smul hbase.aestronglyMeasurable
  have hint : Integrable kernel μ.μ :=
    Integrable.mono hbase hstrong (ae_of_all _ fun u => (hnorm u).le)
  let σ : T.V →L[ℂ] T.V := (T.σa b⁻¹).toContinuousLinearMap
  let C : ℂ := (absFin v (b⁻¹ : Kˣ) : ℂ) ^ ((1 : ℂ) / 2 + s)
  let q : ℝ := absFin v b
  have hqpos : 0 < q := absFin_pos b.ne_zero
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hqpos.ne'
  have hinv : absFin v (b⁻¹ : Kˣ) = q⁻¹ := by
    simp only [q, absFin_eq_norm, Units.val_inv_eq_inv_val, norm_inv]
  have hwa : L.w * L.a b = L.a b⁻¹ * L.w := by
    calc
      _ = (L.w * L.a b * L.w⁻¹) * L.w := by group
      _ = _ := by rw [L.lift_wa]
  have hgroup (u : K) :
      L.w * L.n (Multiplicative.ofAdd u) * (L.a b * g) =
        L.a b⁻¹ * (L.w * L.n (Multiplicative.ofAdd (u * (b⁻¹ : Kˣ))) * g) := by
    calc
      _ = L.w * (L.n (Multiplicative.ofAdd u) * L.a b) * g := by group
      _ = L.w * (L.a b * L.n (Multiplicative.ofAdd (u * (b⁻¹ : Kˣ)))) * g := by
        rw [L.lift_na]
      _ = (L.w * L.a b) * (L.n (Multiplicative.ofAdd (u * (b⁻¹ : Kˣ))) * g) := by group
      _ = _ := by rw [hwa]; group
  have hsection (u : K) :
      f (L.a b⁻¹ * (L.w * L.n (Multiplicative.ofAdd u) * g)) =
        C • T.σa b⁻¹ (base u) := by
    simpa [C, base] using hf.1 0 b⁻¹ (L.w * L.n (Multiplicative.ofAdd u) * g)
  have hunit (u : K) : (b : K) * (u * (b⁻¹ : Kˣ)) = u := by
    calc
      _ = u * ((b : K) * (b⁻¹ : Kˣ)) := by ring
      _ = u := by simp
  have hpoint (u : K) :
      A.ψ v (-u) • f (L.w * L.n (Multiplicative.ofAdd u) * (L.a b * g)) =
        C • σ (kernel (u * (b⁻¹ : Kˣ))) := by
    rw [hgroup, hsection]
    simp [kernel, σ, hunit, smul_smul, mul_comm]
  have hscaled :
      (∫ u, σ (kernel (u * (b⁻¹ : Kˣ))) ∂μ.μ) =
        (q : ℂ) • σ (∫ u, kernel u ∂μ.μ) := by
    calc
      _ = ∫ u, σ (kernel ((b⁻¹ : Kˣ) * u)) ∂μ.μ := by
        apply integral_congr_ae
        filter_upwards [] with u
        rw [mul_comm u]
      _ = (absFin v (b⁻¹ : Kˣ))⁻¹ • ∫ u, σ (kernel u) ∂μ.μ :=
        LocHaar.integral_comp_mul μ b⁻¹ (fun u => σ (kernel u))
      _ = q • σ (∫ u, kernel u ∂μ.μ) := by
        rw [hinv, inv_inv, ContinuousLinearMap.integral_comp_comm σ hint]
      _ = (q : ℂ) • σ (∫ u, kernel u ∂μ.μ) := by
        symm
        exact IsScalarTower.algebraMap_smul (R := ℝ) (A := ℂ) (M := T.V) q _
  have hbasePow : C = (q : ℂ) ^ (-((1 : ℂ) / 2 + s)) := by
    dsimp only [C]
    rw [hinv, Complex.ofReal_inv,
      Complex.inv_cpow_ofReal_nonneg hqpos.le ((1 : ℂ) / 2 + s), ← Complex.cpow_neg]
  have hcoef : C * (q : ℂ) = (q : ℂ) ^ ((1 : ℂ) / 2 - s) := by
    calc
      _ = (q : ℂ) ^ (-((1 : ℂ) / 2 + s)) * (q : ℂ) ^ (1 : ℂ) := by
        rw [hbasePow, Complex.cpow_one]
      _ = (q : ℂ) ^ (-((1 : ℂ) / 2 + s) + 1) :=
        (Complex.cpow_add _ _ hqC).symm
      _ = _ := by congr 1; ring
  have hfull := (whit_local_jacquet_integral L T A μ hs
    (rtr (L.a b * g) f) (hf.rtr (L.a b * g))).2
  change jacquet L A μ (rtr (L.a b * g) f) =
    ∫ u, A.ψ v (-u) • f (L.w * L.n (Multiplicative.ofAdd u) * (L.a b * g)) ∂μ.μ at hfull
  have hW : jacquet L A μ (rtr (L.a b * g) f) =
      (q : ℂ) ^ ((1 : ℂ) / 2 - s) • σ (∫ u, kernel u ∂μ.μ) := by
    calc
      _ = ∫ u, A.ψ v (-u) •
          f (L.w * L.n (Multiplicative.ofAdd u) * (L.a b * g)) ∂μ.μ := hfull
      _ = ∫ u, C • σ (kernel (u * (b⁻¹ : Kˣ))) ∂μ.μ := by
        apply integral_congr_ae
        exact ae_of_all _ hpoint
      _ = C • ∫ u, σ (kernel (u * (b⁻¹ : Kˣ))) ∂μ.μ := integral_smul _ _
      _ = (C * (q : ℂ)) • σ (∫ u, kernel u ∂μ.μ) := by rw [hscaled, smul_smul]
      _ = _ := by rw [hcoef]
  have hone : H.hilb v b 1 = 1 := by
    have hleft : H.hilb v 1 b = 1 := H.sixth_power v 1 b ⟨1, by simp⟩
    simpa only [hleft, mul_one] using H.skew v b 1
  have hmul : H.hilb v b b * H.hilb v b b⁻¹ = 1 := by
    have h := H.mul_right v b b b⁻¹
    rw [mul_inv_cancel, hone] at h
    exact h.symm
  have hrel : H.hilb v b b⁻¹ = (H.hilb v b b)⁻¹ := by
    apply mul_left_cancel (a := H.hilb v b b)
    rw [hmul, mul_inv_cancel]
  have hsquare : (H.hilb v b b⁻¹) ^ 2 = 1 := by
    have hself : (H.hilb v b b) ^ 2 = 1 := by simpa only [pow_two] using H.skew v b b
    rw [hrel, inv_pow, hself, inv_one]
  have hcoeff : muThree D (H.hilb v b b⁻¹) = 1 := by
    apply rootsOfUnity.coe_injective
    change D.σ0 ((((H.hilb v b b⁻¹ ^ 2 : rootsOfUnity 6 F) : Fˣ) : F)) = 1
    rw [hsquare]
    simp
  have hsigma (z : T.V) : T.σa b (T.σa b⁻¹ z) = z := by
    have h := congrArg (fun ρ : T.V →ₗ[ℂ] T.V => ρ z) (T.σa_mul b b⁻¹)
    simpa [hcoeff, T.σa_one] using h
  have hsigW : T.σa b (jacquet L A μ (rtr (L.a b * g) f)) =
      (q : ℂ) ^ ((1 : ℂ) / 2 - s) • (∫ u, kernel u ∂μ.μ) := by
    have h := congrArg (T.σa b) hW
    simpa only [map_smul, σ, LinearMap.coe_toContinuousLinearMap', hsigma] using h
  refine ⟨hint, ?_⟩
  change (∫ u, kernel u ∂μ.μ) =
    (q : ℂ) ^ (s - (1 : ℂ) / 2) • T.σa b (jacquet L A μ (rtr (L.a b * g) f))
  rw [hsigW, smul_smul, ← Complex.cpow_add _ _ hqC]
  have hexp : (s - (1 : ℂ) / 2) + ((1 : ℂ) / 2 - s) = 0 := by ring
  rw [hexp, Complex.cpow_zero, one_smul]

end ArtinPrimitiveRoots.A1.Theta
