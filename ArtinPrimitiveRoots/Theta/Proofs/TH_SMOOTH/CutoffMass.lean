import ArtinPrimitiveRoots.Theta.Proofs.TH_SMOOTH.FiniteHaar

set_option autoImplicit false
noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open ArtinPrimitiveRoots.A1

namespace ArtinPrimitiveRoots.Proofs.thsol_smooth

variable {F : Type} [Field F] [NumberField F]

/-- On an open compact cutoff of local units, multiplicative and additive product Haar
measures agree, and the cutoff has positive finite mass. -/
theorem finite_unit_cutoff_mass {CE : ℕ} {condη : Ideal (𝓞 F)} (S : SData F CE condη)
    (μ : ∀ v : FinPlace F, ArtinPrimitiveRoots.A1.Theta.LocHaar v)
    (U : Set (∀ v : S.Sf, v.1.adicCompletion F)) (hUo : IsOpen U) (hUc : IsCompact U)
    (hU1 : (1 : ∀ v : S.Sf, v.1.adicCompletion F) ∈ U)
    (hUunit : ∀ y ∈ U, ∀ v : S.Sf, Valued.v (y v) = 1) :
    (Measure.pi (fun v : S.Sf => (μ v.1).μ.withDensity
      (fun y => ENNReal.ofReal ((absFin v.1 y)⁻¹)))).restrict U =
      (Measure.pi (fun v : S.Sf => (μ v.1).μ)).restrict U ∧
    0 < (Measure.pi (fun v : S.Sf => (μ v.1).μ.withDensity
      (fun y => ENNReal.ofReal ((absFin v.1 y)⁻¹))) U).toReal ∧
    Measure.pi (fun v : S.Sf => (μ v.1).μ.withDensity
      (fun y => ENNReal.ofReal ((absFin v.1 y)⁻¹))) U < ⊤ := by
  classical
  let ν (v : S.Sf) : Measure (v.1.adicCompletion F) :=
    (μ v.1).μ.withDensity (fun y => ENNReal.ofReal ((absFin v.1 y)⁻¹))
  let O (v : S.Sf) : Set (v.1.adicCompletion F) := {y | Valued.v y = 1}
  have : ∀ v : S.Sf, SigmaFinite (μ v.1).μ :=
    fun v => locHaar_sigmaFinite v.1 (μ v.1)
  have : ∀ v : S.Sf, SigmaFinite (ν v) := fun v => by
    dsimp [ν]
    infer_instance
  have hO (v : S.Sf) : MeasurableSet (O v) := by
    simpa only [Valuation.restrict_eq_one_iff] using
      (Valued.isClosed_sphere (v.1.adicCompletion F) 1).measurableSet
  have hlocal (v : S.Sf) : (ν v).restrict (O v) = (μ v.1).μ.restrict (O v) := by
    rw [restrict_withDensity (hO v)]
    calc
      ((μ v.1).μ.restrict (O v)).withDensity
          (fun y => ENNReal.ofReal ((absFin v.1 y)⁻¹)) =
          ((μ v.1).μ.restrict (O v)).withDensity 1 := by
        apply withDensity_congr_ae
        filter_upwards [ae_restrict_mem (hO v)] with y hy
        change Valued.v y = 1 at hy
        rw [absFin, dif_pos (HeightOneSpectrum.absNorm_ne_zero v.1), hy, map_one]
        simp
      _ = (μ v.1).μ.restrict (O v) := withDensity_one
  have hUP : U ⊆ Set.univ.pi O := by
    intro y hy v _
    exact hUunit y hy v
  have hproduct : (Measure.pi ν).restrict (Set.univ.pi O) =
      (Measure.pi (fun v : S.Sf => (μ v.1).μ)).restrict (Set.univ.pi O) := by
    rw [Measure.restrict_pi_pi, Measure.restrict_pi_pi]
    congr 1
    funext v
    exact hlocal v
  have hrestrict : (Measure.pi ν).restrict U =
      (Measure.pi (fun v : S.Sf => (μ v.1).μ)).restrict U := by
    rw [← Measure.restrict_restrict_of_subset hUP, hproduct,
      Measure.restrict_restrict_of_subset hUP]
  have hmass : Measure.pi ν U = Measure.pi (fun v : S.Sf => (μ v.1).μ) U := by
    rw [← Measure.restrict_apply_self (Measure.pi ν) U, hrestrict,
      Measure.restrict_apply_self]
  refine ⟨hrestrict, ?_⟩
  change 0 < (Measure.pi ν U).toReal ∧ Measure.pi ν U < ⊤
  rw [hmass]
  have hpos := hUo.measure_pos (Measure.pi (fun v : S.Sf => (μ v.1).μ)) ⟨1, hU1⟩
  have hfin := hUc.measure_lt_top (μ := Measure.pi (fun v : S.Sf => (μ v.1).μ))
  exact ⟨ENNReal.toReal_pos hpos.ne' hfin.ne, hfin⟩

end ArtinPrimitiveRoots.Proofs.thsol_smooth
