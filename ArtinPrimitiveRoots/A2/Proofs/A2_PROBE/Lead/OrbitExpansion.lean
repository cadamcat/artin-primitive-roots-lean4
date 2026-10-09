import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE.Lead.OrbitEquiv
import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE.Lead.PeriodicPoisson
import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE.Lead.OrbitAbs
import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE.Lead.OrbitSheet
import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE.Lead.Contracts
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
open ArtinPrimitiveRoots A1 A2
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a2_probe_sol
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}
variable (R : ReflectionSetup D S H Bd A ϑ bc μ v0) (sd : S.SelfDualMeasure A)
variable (W : ProbeWeights (S := S)) (η : HeckeChar F) (U : FrequencyData S D η)

/-- The original rows have one finite support set over the entire fundamental set. -/
private theorem lead_probe_rows_uniform (X Y : ℝ) (hY : 0 < Y) :
    {sm : S.ExtIdeal × S.R |
      W.W1 (qI sm.1.1 / Y) ≠ 0 ∧
      ∃ t : S.FSˣ, (t : S.FS) ∈ omegaAt R 1 ∧
        W.W0 (S.diag (sm.2 : F) *
          ((t * R.sheets.ellU (qI sm.1.1 * X))⁻¹ : S.FSˣ).val) ≠ 0}.Finite := by
  classical
  have hdiagFinite (K : Set S.FS) (hK : IsCompact K) :
      (K ∩ S.diagR).Finite := by
    let Hring : Subring S.FS := (S.diag.comp S.R.val.toRingHom).range
    let H : AddSubgroup S.FS := Hring.toAddSubgroup
    have hH : (H : Set S.FS) = S.diagR := by
      change Set.range (fun x : S.R => S.diag (x : F)) = _
      rfl
    have hdiscrete : IsDiscrete (H : Set S.FS) := by
      simpa only [hH] using (S.diagR_discrete_cocompact D).1
    have hclosed : IsClosed (H : Set S.FS) := H.isClosed_of_isDiscrete hdiscrete
    have hcompact : IsCompact (K ∩ (H : Set S.FS)) := hK.inter_right hclosed
    have hdiscrete' : IsDiscrete (K ∩ (H : Set S.FS)) :=
      hdiscrete.mono Set.inter_subset_right
    have hfinite := hcompact.finite hdiscrete'
    simpa only [hH] using hfinite
  have hrows (s : S.ExtIdeal) :
      {m : S.R | ∃ t : S.FSˣ, (t : S.FS) ∈ omegaAt R 1 ∧
        W.W0 (S.diag (m : F) *
          ((t * R.sheets.ellU (qI s.1 * X))⁻¹ : S.FSˣ).val) ≠ 0}.Finite := by
    classical
    obtain ⟨K, hK, hOmega⟩ := R.sheets.omega_bounded
    let a0 : S.FSˣ := R.sheets.ellU 1
    let a1 : S.FSˣ := R.sheets.ellU (qI s.1 * X)
    let Kunit : Set S.FS := (fun x : S.FS => (a0 : S.FS) * x * (a1 : S.FS)) '' K
    have hWcompact : IsCompact (tsupport W.W0) := W.W0_compact
    have hKunit : IsCompact Kunit := by
      change IsCompact ((fun x : S.FS => (a0 : S.FS) * x * (a1 : S.FS)) '' K)
      exact hK.image ((continuous_const.mul continuous_id).mul continuous_const)
    let Ktotal : Set S.FS :=
      (fun p : S.FS × S.FS => p.1 * p.2) '' (tsupport W.W0 ×ˢ Kunit)
    have hKtotal : IsCompact Ktotal := by
      change IsCompact ((fun p : S.FS × S.FS => p.1 * p.2) ''
        (tsupport W.W0 ×ˢ Kunit))
      exact (hWcompact.prod hKunit).image (continuous_fst.mul continuous_snd)
    have hfinite := hdiagFinite Ktotal hKtotal
    have hdiag : Function.Injective (fun m : S.R => S.diag (m : F)) := by
      intro m n hmn
      apply Subtype.ext
      apply v0.embedding.injective
      change (S.diag (m : F)).2 v0 = (S.diag (n : F)).2 v0
      exact congrArg (fun y : S.FS => y.2 v0) hmn
    apply Set.Finite.of_injOn (f := fun m : S.R => S.diag (m : F))
      (s := {m : S.R | ∃ t : S.FSˣ, (t : S.FS) ∈ omegaAt R 1 ∧
        W.W0 (S.diag (m : F) * ((t * a1)⁻¹ : S.FSˣ).val) ≠ 0})
      (t := Ktotal ∩ S.diagR) ?_ ?_ hfinite
    · intro m hm
      obtain ⟨t, ht, hW⟩ := hm
      let y : S.FS :=
        S.diag (m : F) * ((t * a1)⁻¹ : S.FSˣ).val
      have hy : y ∈ tsupport W.W0 := by
        apply subset_closure
        exact Function.mem_support.mpr hW
      rcases ht with ⟨x, hx, htx⟩
      have hta : (t : S.FS) * (a1 : S.FS) ∈ Kunit := by
        refine ⟨x, hOmega hx, ?_⟩
        dsimp [Kunit]
        rw [htx]
      constructor
      · refine ⟨(y, (t : S.FS) * (a1 : S.FS)), ⟨hy, hta⟩, ?_⟩
        dsimp [y]
        simp [mul_assoc]
      · exact ⟨m, rfl⟩
    · intro m hm n hn hmn
      exact hdiag hmn
  have houter : (Function.support (fun s : S.ExtIdeal => W.W1 (qI s.1 / Y))).Finite := by
    have hcompact : IsCompact (tsupport W.W1) := W.W1_compact
    obtain ⟨B, hB⟩ :=
      (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hcompact.isBounded
    let cutoff : ℝ := Y * max B 1
    have hcutoff : 0 ≤ cutoff := by
      dsimp [cutoff]
      positivity
    have hfinite := a2_bridge_COUNT_finite S cutoff hcutoff
    apply hfinite.1.subset
    intro I hI
    have hts : qI I.1 / Y ∈ tsupport W.W1 := by
      apply subset_closure
      exact Function.mem_support.mpr hI
    have hball := hB hts
    have hdist : dist (qI I.1 / Y) 0 ≤ B := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hball
    have hfrac : qI I.1 / Y ≤ max B 1 := by
      calc
        qI I.1 / Y ≤ |qI I.1 / Y| := le_abs_self _
        _ = dist (qI I.1 / Y) 0 := by
          simpa only [sub_zero] using (Real.dist_eq (qI I.1 / Y) 0).symm
        _ ≤ B := hdist
        _ ≤ max B 1 := le_max_left _ _
    have hq : qI I.1 ≤ cutoff := by
      dsimp [cutoff]
      calc
        qI I.1 ≤ max B 1 * Y := (div_le_iff₀ hY).mp hfrac
        _ = Y * max B 1 := by ring
    simpa [qI, idealNorm] using hq
  have hfinite :
      (⋃ s ∈ Function.support (fun s : S.ExtIdeal => W.W1 (qI s.1 / Y)),
        (Prod.mk s) '' {m : S.R | ∃ t : S.FSˣ, (t : S.FS) ∈ omegaAt R 1 ∧
          W.W0 (S.diag (m : F) *
            ((t * R.sheets.ellU (qI s.1 * X))⁻¹ : S.FSˣ).val) ≠ 0}).Finite :=
    houter.biUnion fun s hs => (hrows s).image (Prod.mk s)
  apply hfinite.subset
  rintro ⟨s, m⟩ ⟨hs, hm⟩
  exact Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr
    ⟨Function.mem_support.mpr hs, ⟨m, hm, rfl⟩⟩⟩

/-- LEAD: integrate the expanded Bm rows using the independent worker parts. -/
theorem orbit_expansion
    (hspec : LeadWeightSpec R sd W) (hcoset : LeadCosetContract sd W)
    (hfinite : LeadFiniteContract R) (hsheets : LeadSheetsContract R sd W)
    (hclass : LeadClassContract (bc := bc) η U)
    (hratio : LeadRatioContract (S := S)) :
    LeadExpansionContract R sd W η U := by
  sorry

end ArtinPrimitiveRoots.Proofs.a2_probe_sol
