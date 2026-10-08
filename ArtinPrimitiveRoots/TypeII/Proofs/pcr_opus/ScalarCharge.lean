import ArtinPrimitiveRoots.TypeII.Proofs.PD_LIFECYCLE.pd_active_run_count

/-! Exact per-prime scalar charge of a lifespan (guide
`runs/lanes/sol-thin-pdmem/PROOFS.md:434–449`): the rho factors cancel, and the raw charge
is the signed lifespan charge times one band inverse per active run. -/

set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
open ArtinPrimitiveRoots.TypeII
noncomputable section

theorem pcr_rawSurvival_eq {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (hρ : ρ ≠ 0)
    (γ : EnvPath S.x K) (p : ℕ) (lam : Fin (p + 1)) (j : Fin (pathLength S.x + 1)) :
    pdRawSurvival F S ρ γ p lam j = pdLifeSurvival F S γ p lam j := by
  unfold pdRawSurvival pdLifeSurvival memoryEta
  split_ifs
  · have h : ρ * (memoryQ S.x F.q_d j.val / ρ ^ 2) * ρ = memoryQ S.x F.q_d j.val := by
      field_simp
    rw [h]
    ring
  · ring

theorem pcr_activeRuns_pos {K : ℕ} (S : PDScale) (γ : EnvPath S.x K) (p : ℕ)
    (hA : (pdLifeActive S γ p).Nonempty) : 1 ≤ pdActiveRuns S γ p := by
  unfold pdActiveRuns
  apply Finset.card_pos.mpr
  refine ⟨(pdLifeActive S γ p).min' hA, ?_⟩
  have hmem := Finset.min'_mem _ hA
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, (Finset.mem_filter.mp hmem).2, ?_⟩
  rintro ⟨k, hk, hact⟩
  have hkA : k ∈ pdLifeActive S γ p := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hact⟩
  have hle := Finset.min'_le _ k hkA
  have hlt : k < (pdLifeActive S γ p).min' hA := by
    rw [Fin.lt_def]
    omega
  exact absurd hle (not_le.mpr hlt)

theorem pcr_activeRuns_zero {K : ℕ} (S : PDScale) (γ : EnvPath S.x K) (p : ℕ)
    (hA : ¬ (pdLifeActive S γ p).Nonempty) : pdActiveRuns S γ p = 0 := by
  unfold pdActiveRuns
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_of_forall_notMem
  intro j hj
  apply hA
  exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2.1⟩⟩

/-- Per prime: the raw lifespan charge is `V⁻¹^(active runs)` times the signed charge. -/
theorem pcr_prime_charge {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (hρ : ρ ≠ 0)
    (γ : EnvPath S.x K) (i : Fin K) (p : ℕ) (hV : bandMass S.x (F.a i) ≠ 0)
    (life : PrimeLife S γ p) :
    pdRawPrimeLifeCharge F S ρ γ i p life =
      ((bandMass S.x (F.a i))⁻¹) ^ (pdActiveRuns S γ p) * primeLifeCharge F S γ p life := by
  have hν : memoryNu S.x K F.a F.q_d i p =
      (bandMass S.x (F.a i))⁻¹ * (((p : ℝ) + 1) * memoryBPrime S.x F.q_d p)⁻¹ := by
    unfold memoryNu
    rw [one_div, mul_assoc, mul_inv]
  have hsurv := pcr_rawSurvival_eq F S ρ hρ γ p
  have hVV : bandMass S.x (F.a i) * (bandMass S.x (F.a i))⁻¹ = 1 := mul_inv_cancel₀ hV
  have hρρ (e : ℝ) : e / ρ * ρ = e := div_mul_cancel₀ e hρ
  unfold pdRawPrimeLifeCharge primeLifeCharge
  simp only [hsurv]
  by_cases hA : (pdLifeActive S γ p).Nonempty
  · have hr := pcr_activeRuns_pos S γ p hA
    rw [dif_pos hA, dif_pos hA]
    obtain ⟨n, hn⟩ : ∃ n, pdActiveRuns S γ p = n + 1 :=
      ⟨pdActiveRuns S γ p - 1, by omega⟩
    rw [hn, Nat.add_sub_cancel, hν]
    rcases life with ⟨⟨_ | a, _ | c⟩, hl⟩
    · dsimp only
      ring
    · dsimp only
      rw [hρρ]
      ring
    · dsimp only
      rw [hρρ]
      linear_combination (-memoryEta S.x F.q_d a.val *
        (((p : ℝ) + 1) * memoryBPrime S.x F.q_d p)⁻¹ * (bandMass S.x (F.a i))⁻¹ ^ (n + 1) *
        (∏ j ∈ Finset.univ.filter (fun j => a < j ∧ j < (pdLifeActive S γ p).min' hA),
          pdLifeSurvival F S γ p (projLine p (γ ((pdLifeActive S γ p).min' hA)).1) j) *
        (∏ j ∈ Finset.univ.filter (fun j => (pdLifeActive S γ p).min' hA < j ∧
            j < (pdLifeActive S γ p).max' hA ∧ j ∉ pdLifeActive S γ p),
          pdLifeSurvival F S γ p (projLine p (γ ((pdLifeActive S γ p).min' hA)).1) j)) * hVV
    · dsimp only
      rw [hρρ, hρρ]
      linear_combination (-memoryEta S.x F.q_d a.val *
        (((p : ℝ) + 1) * memoryBPrime S.x F.q_d p)⁻¹ * (bandMass S.x (F.a i))⁻¹ ^ (n + 1) *
        (∏ j ∈ Finset.univ.filter (fun j => a < j ∧ j < (pdLifeActive S γ p).min' hA),
          pdLifeSurvival F S γ p (projLine p (γ ((pdLifeActive S γ p).min' hA)).1) j) *
        (∏ j ∈ Finset.univ.filter (fun j => (pdLifeActive S γ p).min' hA < j ∧
            j < (pdLifeActive S γ p).max' hA ∧ j ∉ pdLifeActive S γ p),
          pdLifeSurvival F S γ p (projLine p (γ ((pdLifeActive S γ p).min' hA)).1) j) *
        (-memoryEta S.x F.q_d c.val *
          ∏ j ∈ Finset.univ.filter (fun j => (pdLifeActive S γ p).max' hA < j ∧ j < c),
            pdLifeSurvival F S γ p (projLine p (γ ((pdLifeActive S γ p).min' hA)).1) j)) * hVV
  · rw [dif_neg hA, dif_neg hA, pcr_activeRuns_zero S γ p hA, pow_zero, one_mul]
    rcases life with ⟨⟨_ | a, _ | c⟩, hl⟩
    · rfl
    · rfl
    · rfl
    · dsimp only
      rw [hρρ, hρρ, hν]
      linear_combination (memoryEta S.x F.q_d a.val * memoryEta S.x F.q_d c.val *
        (((p : ℝ) + 1) * memoryBPrime S.x F.q_d p)⁻¹ *
        ∏ j ∈ Finset.univ.filter (fun j => a < j ∧ j < c),
          pdLifeSurvival F S γ p (projLine p (γ a).1) j) * hVV

/-- The scalar charge of a whole assignment from the run count. -/
theorem pcr_scalar_charge_of_runs {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (hρ : ρ ≠ 0)
    (γ : EnvPath S.x K) (H : PDLifeAssignment F S γ)
    (hV : ∀ i, 0 < bandMass S.x (F.a i))
    (hR : ∀ i : Fin K, (∑ p : primeBand S.x (F.a i), pdActiveRuns S γ p.1) =
      slotCount S.x + pathLength S.x) :
    pdRawAssignmentCharge F S ρ γ H =
      pdActiveNormalization F S * pdLifeAssignmentCharge F S γ H := by
  unfold pdRawAssignmentCharge pdActiveNormalization pdLifeAssignmentCharge physicalMeasure
  calc
    (∏ i : Fin K, ∏ p : primeBand S.x (F.a i), pdRawPrimeLifeCharge F S ρ γ i p.1 (H i p)) =
        ∏ i : Fin K, (((bandMass S.x (F.a i))⁻¹) ^ (slotCount S.x + pathLength S.x) *
          ∏ p : primeBand S.x (F.a i), primeLifeCharge F S γ p.1 (H i p)) := by
      apply Finset.prod_congr rfl
      intro i _
      have h1 : (∏ p : primeBand S.x (F.a i), pdRawPrimeLifeCharge F S ρ γ i p.1 (H i p)) =
          ∏ p : primeBand S.x (F.a i), (((bandMass S.x (F.a i))⁻¹) ^ (pdActiveRuns S γ p.1) *
            primeLifeCharge F S γ p.1 (H i p)) := by
        apply Finset.prod_congr rfl
        intro p _
        exact pcr_prime_charge F S ρ hρ γ i p.1 (hV i).ne' (H i p)
      rw [h1, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hR i]
    _ = (∏ i : Fin K, ((bandMass S.x (F.a i))⁻¹) ^ (slotCount S.x + pathLength S.x)) *
          ∏ i : Fin K, ∏ p : primeBand S.x (F.a i), primeLifeCharge F S γ p.1 (H i p) :=
      Finset.prod_mul_distrib
    _ = _ := by
      congr 1
      rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      rw [Real.rpow_eq_pow, Real.rpow_neg (hV i).le, Real.rpow_natCast, pow_add, inv_pow]

end
end ArtinPrimitiveRoots.TypeII.PD
