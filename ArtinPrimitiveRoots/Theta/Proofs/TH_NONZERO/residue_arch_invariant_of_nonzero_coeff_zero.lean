import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.residue_ideal_period
import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.idealTorus_constant_of_nonzero_fourier_zero
import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.idealTraceFrequency_ne_zero
import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.idealTraceFrequency_period
import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_FOURIER.theta_adapted_domain_exists

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Vanishing of the nonzero adapted Fourier coefficients makes the residue
constant along every left archimedean upper-root orbit. -/
theorem residue_arch_invariant_of_nonzero_coeff_zero
    {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam : AnalyticFamily P G μ)
    (C : ContinuedEis Fam) (hFam : FourierFamilyHyp μ Fam.sec Fam.T0)
    (hcoeff : ∀ (g : P.tc.G)
      (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
      (Pd : Set (InfinitePlace F → ℂ)) (ν : Fˣ),
      FourierAdaptedDomain Fam.sec g 𝔞 Pd (ν : F) →
        torusCoeff P C.theta g Pd (ν : F) = 0) :
    ∀ (x : InfinitePlace F → ℂ) (g : P.tc.G),
      C.theta (nInf P x * g) = C.theta g := by
  let : IsTotallyComplex F := D.isTotallyComplex
  intro x g
  obtain ⟨𝔞, Pd, hdom, _⟩ := theta_adapted_domain_exists hFam g
  let I := Units.mk0 𝔞 hdom.1
  let := Fintype.ofFinite (Module.Free.ChooseBasisIndex ℤ I)
  have hnzero : nInf P 0 = 1 := by
    change P.tc.nS 1 = 1
    exact P.tc.nS.map_one
  let f : C(InfinitePlace F → ℂ, ℂ) :=
    ⟨fun y => C.theta (nInf P y * g), by
      have h := (C.jointRoots g).continuous.comp
        (continuous_id.prodMk (continuous_const (y := (0 : InfinitePlace F → ℂ))))
      simpa only [Function.comp_def, id_eq, hnzero, mul_one] using h⟩
  have hper : ∀ ξ ∈ (I : Set F), ∀ y, f (y + infEmbA ξ) = f y := by
    exact residue_ideal_period Fam C g 𝔞 hdom.2.1
  have hgroup :
      (𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom =
        (Submodule.span ℤ (Set.range (idealArchBasis F I))).toAddSubgroup := by
    ext y
    change (∃ ξ ∈ (I : Set F), (fun w : InfinitePlace F => w.embedding ξ) = y) ↔
      y ∈ Submodule.span ℤ (Set.range (idealArchBasis F I))
    exact (mem_span_idealArchBasis F I).symm
  have hPd : IsAddFundamentalDomain
      (Submodule.span ℤ (Set.range (idealArchBasis F I))).toAddSubgroup Pd volume := by
    rw [← hgroup]
    exact hdom.2.2.1
  have hzero : ∀ n : Module.Free.ChooseBasisIndex ℤ I → ℤ, n ≠ 0 →
      ((volume Pd).toReal : ℂ)⁻¹ *
        (∫ y in Pd, f y * psiInf (-(idealTraceFrequency F I n)) y) = 0 := by
    intro n hn
    let ν := Units.mk0 (idealTraceFrequency F I n) (idealTraceFrequency_ne_zero F I hn)
    have hνdom : FourierAdaptedDomain Fam.sec g 𝔞 Pd (ν : F) := by
      refine ⟨hdom.1, hdom.2.1, hdom.2.2.1, hdom.2.2.2.1, ?_⟩
      intro ξ hξ
      exact idealTraceFrequency_period F I n hξ
    simpa only [torusCoeff, Complex.ofReal_inv, f, ContinuousMap.coe_mk,
      ν, Units.val_mk0] using hcoeff g 𝔞 Pd ν hνdom
  have hx := idealTorus_constant_of_nonzero_fourier_zero F I f hper Pd hPd hzero x
  simpa only [f, ContinuousMap.coe_mk, hnzero, one_mul] using hx

end ArtinPrimitiveRoots.A1.Theta
