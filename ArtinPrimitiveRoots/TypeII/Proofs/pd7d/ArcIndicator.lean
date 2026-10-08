import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.ArcGeometry
import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.MajorArcPhase

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical MeasureTheory
open ArtinPrimitiveRoots.TypeII
set_option autoImplicit false

lemma pd7d_majorArc_measurable (x Y A₀ : ℝ) :
    MeasurableSet {theta : ℝ | majorArc x Y A₀ theta} := by
  unfold majorArc
  simp only [Set.setOf_exists, Set.setOf_and]
  measurability

lemma pd7d_major_arc_phase_integrable (x Y A₀ : ℝ) (d : ℤ) :
    IntegrableOn (fun theta : ℝ => if majorArc x Y A₀ theta then
      additiveCharacter (theta * (d : ℝ)) else 0) (Set.Icc (0 : ℝ) 1) := by
  have hcont : Continuous (fun theta : ℝ => additiveCharacter (theta * (d : ℝ))) := by
    unfold additiveCharacter
    fun_prop
  have hi := (hcont.integrableOn_Icc : IntegrableOn
    (fun theta : ℝ => additiveCharacter (theta * (d : ℝ))) (Set.Icc (0 : ℝ) 1))
  have hind := hi.indicator (pd7d_majorArc_measurable x Y A₀)
  have hEq : (fun theta : ℝ => if majorArc x Y A₀ theta then
      additiveCharacter (theta * (d : ℝ)) else 0) =
      ({theta : ℝ | majorArc x Y A₀ theta}.indicator
        (fun theta => additiveCharacter (theta * (d : ℝ)))) := by
    funext theta
    rfl
  rw [hEq]
  exact hind

end ArtinPrimitiveRoots.TypeII.PD
