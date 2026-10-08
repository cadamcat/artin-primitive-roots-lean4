import ArtinPrimitiveRoots.Theta.Eis
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

set_option autoImplicit false
open NumberField IsDedekindDomain Filter
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]

/-- A uniform ball around one consists of sixth powers in a finite completion. -/
theorem local_sixth_power_threshold (v : FinPlace F) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ u : (v.adicCompletion F)ˣ,
      ‖(u : v.adicCompletion F) - 1‖ < ε →
      ∃ t : (v.adicCompletion F)ˣ, t ^ 6 = u := by
  let K := v.adicCompletion F
  letI : NontriviallyNormedField K := Valued.toNontriviallyNormedField K (WithZero (Multiplicative ℤ))
  have h6 : (6 : K) ≠ 0 := by
    intro h
    have hF : (6 : F) = 0 := (algebraMap F K).injective
      (by simpa using h)
    norm_num at hF
  have hd : HasStrictDerivAt (fun t : K => t ^ 6) (6 : K) (1 : K) := by
    simpa using hasStrictDerivAt_pow 6 (1 : K)
  have hs : Set.range (fun t : K => t ^ 6) ∈ 𝓝 (1 : K) := by
    have hm : Set.range (fun t : K => t ^ 6) ∈
        Filter.map (fun t : K => t ^ 6) (𝓝 (1 : K)) := by
      apply Filter.mem_map.mpr
      exact Filter.Eventually.of_forall (fun t => ⟨t, rfl⟩)
    rw [hd.map_nhds_eq h6] at hm
    simpa only [one_pow] using hm
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨ε, hε, fun u hu => ?_⟩
  obtain ⟨t, ht⟩ := hball (by simpa only [Metric.mem_ball, dist_eq_norm] using hu)
  have ht0 : t ≠ 0 := by
    intro h
    apply u.ne_zero
    simpa [h] using ht.symm
  refine ⟨Units.mk0 t ht0, ?_⟩
  apply Units.ext
  simpa only [Units.val_pow_eq_pow_val, Units.val_mk0] using ht

end ArtinPrimitiveRoots.A1.Theta
