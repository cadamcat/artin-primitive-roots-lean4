import ArtinPrimitiveRoots.Proofs.th_continue_b.TorusRatioChart
import ArtinPrimitiveRoots.Proofs.th_continue_b.TorusRootReduction

set_option autoImplicit false
set_option maxHeartbeats 30000
set_option maxRecDepth 128
open NumberField IsDedekindDomain
open scoped Classical Topology ContDiff
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

theorem continuedEis_theta_torus_cont
    {P : CoverPackage D S H A} {G : GlobalDatum P}
    {I : ContinuedEisInput P G} {C : ContinuedEisComponents I}
    (R : ContinuedEisReconstruction C) (g h : P.tc.G) :
    Continuous fun y : S.FSˣ => R.theta (g * P.tc.aS y * h) := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro y0
  obtain ⟨j, p, hpCont, hpPos, hChart⟩ :=
    continuedEis_theta_torus_ratio_chart R (g * P.tc.aS y0) h y0
  have hComp : ContinuousOn
      (fun z : ArtinPrimitiveRoots.A1.Spec.Coord F =>
        C.componentTheta j (ArtinPrimitiveRoots.A1.Spec.ptX F z))
      (ArtinPrimitiveRoots.A1.Spec.posSet F) :=
    (continuedEis_componentTheta_contDiffOn C j).continuousOn
  have hModel : ContinuousAt
      (fun y => C.componentTheta j (ArtinPrimitiveRoots.A1.Spec.ptX F (p y))) y0 := by
    apply (continuousWithinAt_univ _ _).mp
    exact (hComp (p y0) (hpPos y0)).comp
      (f := p) hpCont.continuousWithinAt (fun y _ => hpPos y)
  have hEq : (fun y => R.theta (g * P.tc.aS y * h)) =ᶠ[𝓝 y0]
      (fun y => C.componentTheta j (ArtinPrimitiveRoots.A1.Spec.ptX F (p y))) := by
    filter_upwards [continuedEis_theta_torus_local_reduction R g h y0] with y hy
    exact hy.trans (hChart y)
  exact hModel.congr hEq.symm

end ArtinPrimitiveRoots.A1.Theta
