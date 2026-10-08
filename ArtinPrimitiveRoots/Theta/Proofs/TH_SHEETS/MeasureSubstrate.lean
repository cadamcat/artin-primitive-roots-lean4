import ArtinPrimitiveRoots.Theta.Shared
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion
import Mathlib.Topology.Algebra.Valued.LocallyCompact

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory
open scoped Classical Topology

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.thsol_sheets

open ArtinPrimitiveRoots.A1 ArtinPrimitiveRoots.A1.Theta

variable {F : Type} [Field F] [NumberField F]

/-- Local measure facts needed before using product Fubini for sheets. -/
theorem local_measure_substrate (μ : ∀ v : FinPlace F, LocHaar v) :
    (∀ v : FinPlace F,
      Measurable (absFin v) ∧
      (∀ x : v.adicCompletion F, x ≠ 0 → 0 < absFin v x) ∧
      NullSingletonClass (μ v).μ ∧ SigmaFinite (μ v).μ ∧
      SigmaFinite ((μ v).μ.withDensity fun x => ENNReal.ofReal (absFin v x)⁻¹)) ∧
    NullSingletonClass (volume.withDensity fun z : ℂ => ENNReal.ofReal (Complex.normSq z)⁻¹) ∧
    SigmaFinite (volume.withDensity fun z : ℂ => ENNReal.ofReal (Complex.normSq z)⁻¹) := by
  constructor
  · intro v
    let K := v.adicCompletion F
    let O := v.adicCompletionIntegers F
    let _ : Finite (IsLocalRing.ResidueField O) :=
      Finite.of_equiv _ (v.residueFieldEquivAdicCompletionIntegers (K := F)).toEquiv
    let _ : ProperSpace K :=
      (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
        (K := K) (Γ₀ := WithZero (Multiplicative ℤ))).mpr
        ⟨inferInstance, inferInstanceAs (IsDiscreteValuationRing O),
          inferInstanceAs (Finite (IsLocalRing.ResidueField O))⟩
    let _ : NontriviallyNormedField K :=
      Valued.toNontriviallyNormedField K (WithZero (Multiplicative ℤ))
    have habs (x : K) : absFin v x = ‖x‖ := by
      unfold absFin
      rw [dif_pos (HeightOneSpectrum.absNorm_ne_zero v)]
      exact (FinitePlace.norm_def v x).symm
    have hpos (x : K) (hx : x ≠ 0) : 0 < absFin v x := by
      rw [habs]
      exact norm_pos_iff.mpr hx
    have hnull : NullSingletonClass (μ v).μ := inferInstance
    have hfinite : SigmaFinite (μ v).μ := inferInstance
    refine ⟨?_, hpos, hnull, hfinite, ?_⟩
    · change Measurable (fun x : K => absFin v x)
      simpa only [habs] using (continuous_norm.measurable : Measurable (fun x : K => ‖x‖))
    · infer_instance
  · constructor
    · infer_instance
    · infer_instance

end ArtinPrimitiveRoots.Proofs.thsol_sheets
