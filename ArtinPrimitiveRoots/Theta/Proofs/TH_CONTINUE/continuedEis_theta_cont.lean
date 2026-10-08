import ArtinPrimitiveRoots.Theta.Proofs.TH_CONTINUE.Defs
import ArtinPrimitiveRoots.Proofs.th_continue_b.ThetaRightRoot
import ArtinPrimitiveRoots.Proofs.th_continue_b.TorusContinuous

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Continuity on all translated S-torus orbits and smoothness on joint left/right
archimedean root orbits. Obtain finite local constancy from the common level, and compose
the finite residue sums with smooth archimedean coordinate charts. Single-place right-root
smoothness is included in the exact form required by the frozen consumer.
Guide: `runs/lanes/sol-thin-thglobal/PROOFS.md:824–832`.
Uses component reconstruction, common finite level and `Spec.ContinuedEisenstein.res_smooth`.
Consumed by frozen `exists_continuedEis`; no `hRP` hypothesis.
Amended (`runs/lanes/theta-iface-opus/AMENDMENT.md`): the first conjunct is continuity in the
torus parameter of every iterated right root derivative, not only of the residue itself. -/
theorem continuedEis_theta_cont {P : CoverPackage D S H A} {G : GlobalDatum P}
    {I : ContinuedEisInput P G} {C : ContinuedEisComponents I}
    (R : ContinuedEisReconstruction C) :
    (∀ (g h : P.tc.G) (n : ℕ), Continuous fun y : S.FSˣ =>
      iteratedFDeriv ℝ n
        (fun x : InfinitePlace F → ℂ => R.theta (g * P.tc.aS y * h * nInf P x)) 0) ∧
    (∀ (g : P.tc.G) (w : InfinitePlace F),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : ℂ => R.theta (g * P.tc.nS
          (Multiplicative.ofAdd ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z))))) ∧
    JointRootSmooth P R.theta := by
  exact ⟨continuedEis_theta_torus_cont R,
    continuedEis_theta_rightRoot R, continuedEis_theta_jointRoots R⟩

end ArtinPrimitiveRoots.A1.Theta
