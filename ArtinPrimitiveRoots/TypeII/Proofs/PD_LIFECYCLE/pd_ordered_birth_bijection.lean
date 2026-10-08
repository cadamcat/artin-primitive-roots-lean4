import ArtinPrimitiveRoots.Proofs.pd_life_b.BoundarySupport
import ArtinPrimitiveRoots.Proofs.pd_life_b.BirthCombinatorics
import ArtinPrimitiveRoots.Proofs.pd_life_b.HistoryPaths
import ArtinPrimitiveRoots.Proofs.pd_life_b.OrderedContinuation
import ArtinPrimitiveRoots.Proofs.pd_life_b.GhostSubsetSum
import ArtinPrimitiveRoots.Proofs.pd_life_b.IndexTransport
import ArtinPrimitiveRoots.Proofs.pd_life_b.MemoryIndexTransport
import ArtinPrimitiveRoots.TypeII.Proofs.PD_LIFECYCLE.Defs
import ArtinPrimitiveRoots.TypeII.Proofs.PD_LIFECYCLE.pd_lifecycle_parameters
import ArtinPrimitiveRoots.TypeII.Proofs.PD_LIFECYCLE.pd_ordered_distinct_batch_sum

set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical Filter
open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.Proofs.pd_life_b
noncomputable section

/-- Ordered distinct histories are the finite lifespan sum with the same memory cutoff.
Batch orderings cancel each local ghost factorial; unique old indices give no factorial.
Active symmetrizations and raw-minus-comparison choices give the signed pathCoefficient
before any norm is taken. The normalization is nonzero at this threshold.
Guide runs/lanes/sol-thin-pdmem/PROOFS.md:386–433,447–449,454–473. Uses finite distinct
history support, projective-line transport and ordered_distinct_batch_sum; feeds
history_path_value and pd_truncation_choice_majorant. Defs records literal raw charges;
pd_history_scalar_charge is applied by consumers, not assumed by this bijection. -/
theorem pd_ordered_birth_bijection (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid → ∀ ρ : ℝ, IsMemoryRho F.q_d ρ →
      ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
        pdActiveNormalization F S ≠ 0 ∧
        ∀ w : ArchRoot, w.InRegion S → ∀ γ : EnvPath S.x K,
          IsEnvPathAdmissible F S γ → ∀ B : Option ℕ,
            memHistory F S ρ w B (some γ) distinctWeight =
                pathCoefficient F S γ * (pathArch F S w γ : ℂ) *
                ((pdActiveNormalization F S)⁻¹ * pdRawHistorySum F S ρ γ B : ℝ) := by
  intro K F hF ρ hρ
  obtain ⟨x₀, hx₀, hParams⟩ := pd_lifecycle_parameters K F hF
  refine ⟨x₀, hx₀, ?_⟩
  intro S hS hx
  have hParamsAt := hParams S.x hx
  have hMass := hParamsAt.1
  have hPhys : physicalMeasure S.x K F.a ≠ 0 := by
    unfold physicalMeasure
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact ne_of_gt (Real.rpow_pos_of_pos (hMass i).1 _)
  have hInvMass : (∏ i : Fin K, (bandMass S.x (F.a i))⁻¹) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact inv_ne_zero (ne_of_gt (hMass i).1)
  have hNorm : pdActiveNormalization F S ≠ 0 := by
    unfold pdActiveNormalization
    exact mul_ne_zero hPhys (pow_ne_zero _ hInvMass)
  refine ⟨hNorm, ?_⟩
  intro w hw γ hγ B
  rw [pd_life_b_memHistory_initialLog_sum F S ρ w B (some γ) distinctWeight]
  let j0 : Fin (pathLength S.x + 1) := ⟨0, by omega⟩
  let y0 : EnvPoint S.x K := γ j0
  let s0 : MemPoint S.x K := Prod.mk y0.1 (Prod.mk y0.2 (fun _ => []))
  let σ0 : LogPoint S.x K := (s0, initialLog s0)
  let I := (pd_life_b_initialLogSupport_finite F S).toFinset
  have hEnv0 : EnvValid F S y0 := hγ.1 j0
  have hInitialNodup := pd_life_b_initialLog_values_nodup F.a s0 hEnv0.2 hParamsAt.2.1
  have hInitialDistinct : distinctWeight σ0.2 = 1 := by
    simp [distinctWeight, σ0, hInitialNodup]
  have hMemValid0 : MemValid F S s0 := by
    rcases hEnv0 with ⟨hgcd, hLists⟩
    refine ⟨hgcd, ?_, ?_⟩
    · intro i j
      exact (hLists.1 i j).2
    · intro i e he
      simp [s0] at he
  have hν0 (i : Fin K) (j : Fin (slotCount S.x)) :
      0 < memoryNu S.x K F.a F.q_d i (y0.2 i j) := by
    rcases hEnv0.2.1 i j with ⟨hp, hband⟩
    have hmark : y0.2 i j ∈ markedPrimes S.x K F.a :=
      Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hband⟩
    have hbp := hParamsAt.2.2 (y0.2 i j) hmark
    have hp1 : (0 : ℝ) < (y0.2 i j : ℝ) + 1 := by positivity
    unfold memoryNu
    apply one_div_pos.mpr
    exact mul_pos (mul_pos (hMass i).1 hp1) (by linarith)
  have hMeasure0 : memMeasure F S s0 ≠ 0 := by
    unfold memMeasure
    rw [if_pos hMemValid0]
    apply mul_ne_zero
    · apply Finset.prod_ne_zero_iff.mpr
      intro i hi
      apply Finset.prod_ne_zero_iff.mpr
      intro j hj
      exact ne_of_gt (hν0 i j)
    · simp [s0]
  have hMeasureFormula : memMeasure F S s0 =
      ∏ i : Fin K, ∏ j : Fin (slotCount S.x),
        memoryNu S.x K F.a F.q_d i (y0.2 i j) := by
    unfold memMeasure
    rw [if_pos hMemValid0]
    simp [s0]
  have hBoundary0 : logBoundaryIn σ0 = 1 := by
    simp [σ0, s0, y0, j0, logBoundaryIn, memBoundary, hγ.2.1]
  have hCoeff0 :
      (memMeasure F S s0 : ℂ) * star (logBoundaryIn σ0) ≠ 0 := by
    rw [hBoundary0]
    simp only [star_one, mul_one]
    exact_mod_cast hMeasure0
  have hμσ0 : memMeasure F S σ0.1 ≠ 0 := by simpa [σ0] using hMeasure0
  have hbσ0 : logBoundaryIn σ0 ≠ 0 := by rw [hBoundary0]; norm_num
  have hσ0 : σ0 ∈ I := by
    simp [I, Set.Finite.mem_toFinset, hμσ0, hbσ0]
  have hZeroHistory (σL : LogPoint S.x K) (hσL : σL ∈ I)
      (hne : σL ≠ σ0) :
      logHistoryFn F S ρ w B (some γ) distinctWeight (pathLength S.x) σL = 0 := by
    have hCoeff :
        (memMeasure F S σL.1 : ℂ) * star (logBoundaryIn σL) ≠ 0 := by
      simpa [I, Set.Finite.mem_toFinset] using hσL
    have hμ : memMeasure F S σL.1 ≠ 0 := by
      intro hzero
      apply hCoeff
      simp [hzero]
    have hb : logBoundaryIn σL ≠ 0 := by
      intro hzero
      apply hCoeff
      simp [hzero]
    have hlog : σL.2 = initialLog σL.1 := by
      by_contra hn
      apply hb
      simp [logBoundaryIn, hn]
    have hboundary : σL.1.1 = (1, 0) ∧ (∀ i, σL.1.2.2 i = []) := by
      by_contra hn
      apply hb
      simp [logBoundaryIn, hlog, memBoundary, hn]
    have hOff : (σL.1.1, σL.1.2.1) ≠
        γ ⟨pathLength S.x - pathLength S.x,
          Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ := by
      intro hEq
      have hIndex :
          (⟨pathLength S.x - pathLength S.x,
            Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ : Fin (pathLength S.x + 1)) = j0 := by
        apply Fin.ext
        simp [j0]
      have hEq0 : (σL.1.1, σL.1.2.1) = y0 := by
        simpa [y0, j0, hIndex] using hEq
      have hState : σL.1 = s0 := by
        have hPoint := Prod.ext_iff.mp hEq0
        have hpos : σL.1.1 = y0.1 := hPoint.1
        have hlists : σL.1.2.1 = y0.2 := hPoint.2
        have hmemory : σL.1.2.2 = fun _ => [] := funext hboundary.2
        exact Prod.ext hpos (Prod.ext hlists hmemory)
      have hLog : σL.2 = initialLog s0 := by
        simpa [hState] using hlog
      have hSigma : σL = σ0 := by
        apply Prod.ext hState
        simpa [σ0] using hLog
      exact hne hSigma
    exact pd_life_b_logHistoryFn_zero_off_path_visit F S ρ w B γ distinctWeight
      (pathLength S.x) le_rfl σL hOff
  have hSumSingle :
      (∑ σL ∈ I,
        ((memMeasure F S σL.1 : ℂ) * star (logBoundaryIn σL)) *
          logHistoryFn F S ρ w B (some γ) distinctWeight (pathLength S.x) σL) =
        ((memMeasure F S σ0.1 : ℂ) * star (logBoundaryIn σ0)) *
          logHistoryFn F S ρ w B (some γ) distinctWeight (pathLength S.x) σ0 := by
    rw [Finset.sum_eq_single σ0]
    · intro σL hσL hne
      simp [hZeroHistory σL hσL hne]
    · intro hnot
      exact (hnot hσ0).elim
  rw [hSumSingle]
  simp only [hBoundary0, star_one, mul_one]
  rw [hMeasureFormula]
  sorry

end
end ArtinPrimitiveRoots.TypeII.PD
