import ArtinPrimitiveRoots.Theta.Proofs.TH_FACTOR.thetaWhit_argument_decomposition

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- A global element that fixes every scalar section fixes the residue Whittaker coefficient.
Uses frozen `eisenstein_automorphic`, `theta_fourierCoeff`, and the defining
Laurent and adapted-lattice conditions; feeds `thetaWhit_factor_iteration`. -/
theorem thetaWhit_tail_invariance {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam : AnalyticFamily P G μ)
    (C : ContinuedEis Fam) (k : P.tc.G)
    (hfix : ∀ s h, scalarOf P G (Fam.sec s).f (Fam.sec s).fC (h * k) =
      scalarOf P G (Fam.sec s).f (Fam.sec s).fC h) :
    ∀ X : P.tc.G, thetaWhit C (X * k) = thetaWhit C X := by
  classical
  intro X
  let Adapted : P.tc.G → Prop := fun X =>
    ∃ (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (Pd : Set (InfinitePlace F → ℂ)),
      𝔞 ≠ 0 ∧
      (∀ s, ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
        scalarOf P G (Fam.sec s).f (Fam.sec s).fC
          (h * (X⁻¹ * nFin P ξ * X)) = scalarOf P G (Fam.sec s).f (Fam.sec s).fC h) ∧
      IsAddFundamentalDomain ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom)
        Pd volume ∧ Bornology.IsBounded Pd ∧
      ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), psiInf 1 (infEmbA ξ) = 1
  have hfixInv : ∀ s h, scalarOf P G (Fam.sec s).f (Fam.sec s).fC (h * k⁻¹) =
      scalarOf P G (Fam.sec s).f (Fam.sec s).fC h := by
    intro s h
    have hh := (hfix s (h * k⁻¹)).symm
    simpa [mul_assoc] using hh
  have hAdaptMove {X t : P.tc.G}
      (hfixT : ∀ s h, scalarOf P G (Fam.sec s).f (Fam.sec s).fC (h * t) =
        scalarOf P G (Fam.sec s).f (Fam.sec s).fC h)
      (hX : Adapted X) : Adapted (X * t) := by
    rcases hX with ⟨𝔞, Pd, h𝔞, hfixX, hPd, hb, hψ⟩
    have hfixTInv : ∀ s h, scalarOf P G (Fam.sec s).f (Fam.sec s).fC (h * t⁻¹) =
        scalarOf P G (Fam.sec s).f (Fam.sec s).fC h := by
      intro s h
      have hh := (hfixT s (h * t⁻¹)).symm
      simpa [mul_assoc] using hh
    refine ⟨𝔞, Pd, h𝔞, ?_, hPd, hb, hψ⟩
    intro s ξ hξ h
    let N := X⁻¹ * nFin P ξ * X
    have hconj : (X * t)⁻¹ * nFin P ξ * (X * t) = t⁻¹ * N * t := by
      simp [N, mul_assoc]
    calc
      scalarOf P G (Fam.sec s).f (Fam.sec s).fC
          (h * ((X * t)⁻¹ * nFin P ξ * (X * t))) =
        scalarOf P G (Fam.sec s).f (Fam.sec s).fC ((h * t⁻¹ * N) * t) := by
          rw [hconj]
          simp [mul_assoc]
      _ = scalarOf P G (Fam.sec s).f (Fam.sec s).fC (h * t⁻¹ * N) := hfixT s (h * t⁻¹ * N)
      _ = scalarOf P G (Fam.sec s).f (Fam.sec s).fC (h * t⁻¹) := hfixX s ξ hξ (h * t⁻¹)
      _ = scalarOf P G (Fam.sec s).f (Fam.sec s).fC h := hfixTInv s h
  have hAdaptEquiv : Adapted X ↔ Adapted (X * k) := by
    constructor
    · exact hAdaptMove hfix
    · intro hXk
      have h := hAdaptMove (X := X * k) (t := k⁻¹) hfixInv hXk
      simpa [mul_assoc] using h
  have hθ := theta_right_of_scalar_fix Fam C k hfix
  have htorus (Pd : Set (InfinitePlace F → ℂ)) :
      torusCoeff P C.theta (X * k) Pd 1 = torusCoeff P C.theta X Pd 1 := by
    unfold torusCoeff
    congr 1
    apply integral_congr_ae
    filter_upwards with x
    calc
      C.theta (nInf P x * (X * k)) * psiInf (-1) x =
          C.theta ((nInf P x * X) * k) * psiInf (-1) x := by
            congr 1 <;> group
      _ = C.theta (nInf P x * X) * psiInf (-1) x := by rw [hθ (nInf P x * X)]
  by_cases hX : Adapted X
  · rcases hX with ⟨𝔞, Pd, h𝔞, hfixX, hPd, hb, hψ⟩
    have hfixXk : ∀ s, ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
        scalarOf P G (Fam.sec s).f (Fam.sec s).fC
          (h * ((X * k)⁻¹ * nFin P ξ * (X * k))) =
        scalarOf P G (Fam.sec s).f (Fam.sec s).fC h := by
      intro s ξ hξ h
      let N := X⁻¹ * nFin P ξ * X
      have hconj : (X * k)⁻¹ * nFin P ξ * (X * k) = k⁻¹ * N * k := by
        simp [N, mul_assoc]
      calc
        scalarOf P G (Fam.sec s).f (Fam.sec s).fC
            (h * ((X * k)⁻¹ * nFin P ξ * (X * k))) =
          scalarOf P G (Fam.sec s).f (Fam.sec s).fC ((h * k⁻¹ * N) * k) := by
            rw [hconj]
            simp [mul_assoc]
        _ = scalarOf P G (Fam.sec s).f (Fam.sec s).fC (h * k⁻¹ * N) := hfix s (h * k⁻¹ * N)
        _ = scalarOf P G (Fam.sec s).f (Fam.sec s).fC (h * k⁻¹) := hfixX s ξ hξ (h * k⁻¹)
        _ = scalarOf P G (Fam.sec s).f (Fam.sec s).fC h := hfixInv s h
    have hdiag1 : diagGL (1 : Fˣ) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [diagGL]
    have hfourierX := theta_fourierCoeff Fam C X 𝔞 h𝔞 hfixX Pd hPd hb 1 hψ
    have hfourierXk := theta_fourierCoeff Fam C (X * k) 𝔞 h𝔞 hfixXk Pd hPd hb 1 hψ
    have hθX : torusCoeff P C.theta X Pd 1 = thetaWhit C X := by
      simpa [hdiag1] using hfourierX
    have hθXk : torusCoeff P C.theta (X * k) Pd 1 = thetaWhit C (X * k) := by
      simpa [hdiag1] using hfourierXk
    calc
      thetaWhit C (X * k) = torusCoeff P C.theta (X * k) Pd 1 := hθXk.symm
      _ = torusCoeff P C.theta X Pd 1 := htorus Pd
      _ = thetaWhit C X := hθX
  · have hXk : ¬ Adapted (X * k) := by
      intro hXk
      exact hX (hAdaptEquiv.mpr hXk)
    have hRawX : ¬ (∃ (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
        (Pd : Set (InfinitePlace F → ℂ)), 𝔞 ≠ 0 ∧
        (∀ s, ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
          scalarOf P G (Fam.sec s).f (Fam.sec s).fC
            (h * (X⁻¹ * nFin P ξ * X)) = scalarOf P G (Fam.sec s).f (Fam.sec s).fC h) ∧
        IsAddFundamentalDomain ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom)
          Pd volume ∧ Bornology.IsBounded Pd ∧
        ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), psiInf 1 (infEmbA ξ) = 1) := by
      simpa only [Adapted] using hX
    have hRawXk : ¬ (∃ (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
        (Pd : Set (InfinitePlace F → ℂ)), 𝔞 ≠ 0 ∧
        (∀ s, ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
          scalarOf P G (Fam.sec s).f (Fam.sec s).fC
            (h * ((X * k)⁻¹ * nFin P ξ * (X * k))) = scalarOf P G (Fam.sec s).f (Fam.sec s).fC h) ∧
        IsAddFundamentalDomain ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom)
          Pd volume ∧ Bornology.IsBounded Pd ∧
        ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), psiInf 1 (infEmbA ξ) = 1) := by
      simpa only [Adapted] using hXk
    have hθX : thetaWhit C X = 0 := by
      unfold thetaWhit
      simp only [dif_neg hRawX]
    have hθXk : thetaWhit C (X * k) = 0 := by
      unfold thetaWhit
      simp only [dif_neg hRawXk]
    rw [hθXk, hθX]

end ArtinPrimitiveRoots.A1.Theta
