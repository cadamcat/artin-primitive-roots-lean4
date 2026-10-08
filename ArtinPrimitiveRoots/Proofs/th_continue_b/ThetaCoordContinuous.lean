import ArtinPrimitiveRoots.Proofs.th_continue_b.ThetaBasics

set_option autoImplicit false
set_option maxHeartbeats 30000
set_option maxRecDepth 128
open scoped MatrixGroups
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

theorem continuedEis_baseCoord_continuousAt
    {X : Type*} [TopologicalSpace X] (M : X → SL(2, ℂ)) (x : X)
    (hM : ∀ i j, ContinuousAt (fun q => M q i j) x) :
    ContinuousAt (fun q => continuedEis_baseCoord (M q)) x := by
  have hden : ContinuousAt (fun q => continuedEis_baseDen (M q)) x :=
    (Complex.continuous_normSq.continuousAt.comp (hM 1 0)).add
      (Complex.continuous_normSq.continuousAt.comp (hM 1 1))
  have hnum : ContinuousAt (fun q => continuedEis_baseNum (M q)) x :=
    ((hM 0 0).mul (Complex.continuous_conj.continuousAt.comp (hM 1 0))).add
      ((hM 0 1).mul (Complex.continuous_conj.continuousAt.comp (hM 1 1)))
  have hdenC : ContinuousAt (fun q => (continuedEis_baseDen (M q) : ℂ)) x :=
    Complex.ofRealCLM.continuous.continuousAt.comp hden
  have hne : continuedEis_baseDen (M x) ≠ 0 :=
    (continuedEis_baseDen_pos (M x)).ne'
  exact (hnum.div hdenC (Complex.ofReal_ne_zero.mpr hne)).prodMk (hden.inv₀ hne)

end ArtinPrimitiveRoots.A1.Theta
