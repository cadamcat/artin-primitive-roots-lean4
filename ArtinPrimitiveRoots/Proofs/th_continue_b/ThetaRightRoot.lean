import ArtinPrimitiveRoots.Proofs.th_continue_b.ThetaRoots

set_option autoImplicit false
set_option maxHeartbeats 30000
set_option maxRecDepth 128
open NumberField IsDedekindDomain
open scoped Classical ContDiff
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

theorem continuedEis_theta_rightRoot
    {P : CoverPackage D S H A} {G : GlobalDatum P}
    {I : ContinuedEisInput P G} {C : ContinuedEisComponents I}
    (R : ContinuedEisReconstruction C) (g : P.tc.G) (w : InfinitePlace F) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ℂ => R.theta (g * P.tc.nS
        (Multiplicative.ofAdd ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z)))) := by
  classical
  have hZero : nInf P (0 : InfinitePlace F → ℂ) = 1 := by
    change P.tc.nS 1 = 1
    exact P.tc.nS.map_one
  have hSlice : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ℂ => ((0 : InfinitePlace F → ℂ),
        (Pi.single w z : InfinitePlace F → ℂ))) := by
    have hSingle : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : ℂ => (Pi.single w z : InfinitePlace F → ℂ)) :=
      contDiff_single (𝕜 := ℝ) (fun _ : InfinitePlace F => ℂ) _ w
    have hConst : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun _ : ℂ => (0 : InfinitePlace F → ℂ)) := contDiff_const
    exact hConst.prodMk hSingle
  have h := (continuedEis_theta_jointRoots R g).comp hSlice
  change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun z : ℂ => R.theta (nInf P 0 * g * nInf P (Pi.single w z))) at h
  rw [hZero, one_mul] at h
  exact h

end ArtinPrimitiveRoots.A1.Theta
