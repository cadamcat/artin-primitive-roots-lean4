import ArtinPrimitiveRoots.Theta.Proofs.«TH-RDERIV».ResidueActions

set_option autoImplicit false

open NumberField IsDedekindDomain Module MeasureTheory Filter Topology
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.thsol_torusf

open ArtinPrimitiveRoots.A1 ArtinPrimitiveRoots.A1.Theta

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

private theorem ratUpper_nInf_commute (P : CoverPackage D S H A)
    (η : F) (x : InfinitePlace F → ℂ) :
    P.tc.rat (upperGL η) * nInf P x = nInf P x * P.tc.rat (upperGL η) := by
  classical
  obtain ⟨y, hy, hF, hC⟩ := P.nS_components ((0, x) : S.FS)
  have hFy (v : FinPlace F) : P.compF v y = 1 := by
    rw [hF v]
    by_cases hv : v ∈ S.Sf <;> simp [hv]
  have hmap (w : InfinitePlace F) :
      Matrix.GeneralLinearGroup.map w.embedding (upperGL η) =
        upperM ℂ (w.embedding η) := by
    ext i j <;> fin_cases i <;> fin_cases j <;> simp [upperGL, upperM]
  have hupper (a b : ℂ) : upperM ℂ a * upperM ℂ b = upperM ℂ b * upperM ℂ a := by
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [upperM, Matrix.mul_apply, add_comm]
  have hRP : P.ratRP (upperGL η) * y = y * P.ratRP (upperGL η) := by
    apply P.comp_ext
    · intro v
      simp only [map_mul, hFy, mul_one, one_mul]
    · intro w
      simp only [map_mul, P.compC_ratRP, hmap, hC]
      change QuotientGroup.mk (upperM ℂ (w.embedding η)) * QuotientGroup.mk (upperM ℂ (x w)) =
        QuotientGroup.mk (upperM ℂ (x w)) * QuotientGroup.mk (upperM ℂ (w.embedding η))
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hupper]
  have h := congrArg P.q hRP
  simpa only [map_mul, P.q_ratRP, hy, nInf] using h

private theorem ratUpper_nFin_commute (P : CoverPackage D S H A) (η ξ : F) :
    P.tc.rat (upperGL η) * nFin P ξ = nFin P ξ * P.tc.rat (upperGL η) := by
  have hmat : upperGL η * upperGL ξ = upperGL ξ * upperGL η := by
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [upperGL, Matrix.mul_apply, add_comm]
  have hrat : P.tc.rat (upperGL η) * P.tc.rat (upperGL ξ) =
      P.tc.rat (upperGL ξ) * P.tc.rat (upperGL η) := by
    rw [← map_mul, hmat, map_mul]
  unfold nFin
  rw [← mul_assoc, hrat, mul_assoc,
    ratUpper_nInf_commute P η (-(infEmbA ξ)), ← mul_assoc]

theorem thetaWhit_ratUpper {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam : AnalyticFamily P G μ)
    (C : ContinuedEis Fam) (η : F) (h : P.tc.G) :
    thetaWhit C (P.tc.rat (upperGL η) * h) = thetaWhit C h := by
  classical
  obtain ⟨𝔞, Pd, hPd, _⟩ := theta_adapted_domain_exists Fam.fourierHyp h
  rcases hPd with ⟨hne, hfix, hfund, hb, hψ⟩
  let r := P.tc.rat (upperGL η)
  have hconj (ξ : F) : (r * h)⁻¹ * nFin P ξ * (r * h) =
      h⁻¹ * nFin P ξ * h := by
    have hc : r * nFin P ξ = nFin P ξ * r := ratUpper_nFin_commute P η ξ
    have hcancel : r⁻¹ * nFin P ξ * r = nFin P ξ := by
      rw [mul_assoc, ← hc]
      simp
    calc
      (r * h)⁻¹ * nFin P ξ * (r * h) = h⁻¹ * (r⁻¹ * nFin P ξ * r) * h := by
        simp only [mul_inv_rev, mul_assoc]
      _ = h⁻¹ * nFin P ξ * h := by rw [hcancel]
  have hfix' : FourierIdealFix Fam.sec (r * h) 𝔞 := by
    intro s ξ hξ k
    rw [hconj]
    exact hfix s ξ hξ k
  have hdiag : diagGL (1 : Fˣ) = 1 := by
    ext i j <;> fin_cases i <;> fin_cases j <;> simp [diagGL]
  have hcoeff (g : P.tc.G) (hf : FourierIdealFix Fam.sec g 𝔞) :
      torusCoeff P C.theta g Pd 1 = thetaWhit C g := by
    simpa only [Units.val_one, hdiag, map_one, one_mul] using
      theta_fourierCoeff Fam C g 𝔞 hne hf Pd hfund hb (1 : Fˣ) hψ
  have hAut := (theta_residue_actions Fam C).1
  have hcurve : (fun x => C.theta (nInf P x * (r * h))) =
      (fun x => C.theta (nInf P x * h)) := by
    funext x
    rw [← mul_assoc, ← ratUpper_nInf_commute P η x, mul_assoc]
    exact hAut (upperGL η) (nInf P x * h)
  have hcoeffEq : torusCoeff P C.theta (r * h) Pd 1 = torusCoeff P C.theta h Pd 1 := by
    unfold torusCoeff
    rw [show (fun x => C.theta (nInf P x * (r * h)) * psiInf (-1) x) =
        (fun x => C.theta (nInf P x * h) * psiInf (-1) x) from by
      funext x
      rw [congrFun hcurve x]]
  exact (hcoeff (r * h) hfix').symm.trans (hcoeffEq.trans (hcoeff h hfix))

end ArtinPrimitiveRoots.Proofs.thsol_torusf
