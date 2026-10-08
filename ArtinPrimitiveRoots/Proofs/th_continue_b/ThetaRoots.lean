import ArtinPrimitiveRoots.Proofs.th_continue_b.ThetaCont

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

theorem continuedEis_theta_jointRoots
    {P : CoverPackage D S H A} {G : GlobalDatum P}
    {I : ContinuedEisInput P G} {C : ContinuedEisComponents I}
    (R : ContinuedEisReconstruction C) : JointRootSmooth P R.theta := by
  classical
  intro g
  obtain ⟨j, p, hpSmooth, hpPos, hthetaEq⟩ :=
    continuedEis_theta_jointRoots_chart R g
  have hComp : ContDiffOn ℝ ∞
      (fun z : ArtinPrimitiveRoots.A1.Spec.Coord F =>
        C.componentTheta j (ArtinPrimitiveRoots.A1.Spec.ptX F z))
      (ArtinPrimitiveRoots.A1.Spec.posSet F) :=
    continuedEis_componentTheta_contDiffOn C j
  have hCompose := hComp.comp_contDiff hpSmooth hpPos
  have hEq : (fun q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ) =>
      R.theta (nInf P q.1 * g * nInf P q.2)) =
      (fun q => C.componentTheta j (ArtinPrimitiveRoots.A1.Spec.ptX F (p q))) := by
    funext q
    exact hthetaEq q
  rw [hEq]
  exact hCompose

end ArtinPrimitiveRoots.A1.Theta
