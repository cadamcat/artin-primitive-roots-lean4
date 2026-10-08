import ArtinPrimitiveRoots.TypeII.Proofs.PD_LIFECYCLE.pd_active_run_count

set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
open ArtinPrimitiveRoots.TypeII
noncomputable section

private def pdLifeMemoryListSet {x : ℝ} {K : ℕ} (p : PrimeLists x K) (i : Fin K) :
    Finset ℕ := Finset.univ.image (p i)

private lemma pdLifeMemory_sum_subtype {α β : Type*} [AddCommMonoid β]
    (T : Finset α) (f : α → β) :
    (∑ x : {x // x ∈ T}, f x.1) = ∑ x ∈ T, f x := by
  classical
  have hAttach : T.attach = (Finset.univ : Finset {x // x ∈ T}) := by
    ext x
    simp
  rw [← hAttach]
  exact Finset.sum_attach (s := T) (f := f)

private lemma pdLifeMemoryListSet_card {K : ℕ} (F : PDFix K) (S : PDScale)
    (γ : EnvPath S.x K) (hγ : ∀ j, EnvValid F S (γ j)) (i : Fin K)
    (j : Fin (pathLength S.x + 1)) :
    (pdLifeMemoryListSet (γ j).2 i).card = slotCount S.x := by
  classical
  have hinj : Function.Injective ((γ j).2 i) := by
    intro k k' h
    by_contra hne
    exact (hγ j).2.2 i k k' hne h
  unfold pdLifeMemoryListSet
  rw [Finset.card_image_of_injective _ hinj]
  simp

private lemma pdLifeMemoryListSet_subset_band {K : ℕ} (F : PDFix K)
    (S : PDScale) (γ : EnvPath S.x K) (hγ : ∀ j, EnvValid F S (γ j))
    (i : Fin K) (j : Fin (pathLength S.x + 1)) :
    pdLifeMemoryListSet (γ j).2 i ⊆ primeBand S.x (F.a i) := by
  intro p hp
  rcases Finset.mem_image.mp hp with ⟨k, hk, hkp⟩
  rw [← hkp]
  exact (hγ j).2.1 i k |>.2

private lemma pdLifeMemoryActive_iff_listSet {K : ℕ} (F : PDFix K)
    (S : PDScale) (γ : EnvPath S.x K) (hγ : ∀ j, EnvValid F S (γ j))
    (hBands : ∀ i i' : Fin K, i ≠ i' →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a i')))
    (i : Fin K) {p : ℕ} (hp : p ∈ primeBand S.x (F.a i))
    (j : Fin (pathLength S.x + 1)) :
    IsActiveAt γ p j ↔ p ∈ pdLifeMemoryListSet (γ j).2 i := by
  classical
  constructor
  · rintro ⟨i', k, hpk⟩
    have hp' : p ∈ primeBand S.x (F.a i') := by
      rw [← hpk]
      exact (hγ j).2.1 i' k |>.2
    have hii : i' = i := by
      by_contra hne
      have hne' : i ≠ i' := by
        intro h
        exact hne h.symm
      exact (Finset.disjoint_left.mp (hBands i i' hne')) hp hp'
    subst i'
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hpk⟩
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨k, hk, hpk⟩
    exact ⟨i, k, hpk⟩

private lemma pdLifeMemoryRuns_pos {K : ℕ} (S : PDScale)
    (γ : EnvPath S.x K) (p : ℕ) (hactive : ∃ j, IsActiveAt γ p j) :
    1 ≤ pdActiveRuns S γ p := by
  classical
  let A : Finset (Fin (pathLength S.x + 1)) :=
    Finset.univ.filter (IsActiveAt γ p)
  have hA : A.Nonempty := by
    rcases hactive with ⟨j, hj⟩
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  let j₀ := A.min' hA
  have hj₀A : j₀ ∈ A := Finset.min'_mem A hA
  have hstart : IsActiveAt γ p j₀ ∧
      ¬ ∃ k : Fin (pathLength S.x + 1), k.val + 1 = j₀.val ∧ IsActiveAt γ p k := by
    refine ⟨(Finset.mem_filter.mp hj₀A).2, ?_⟩
    rintro ⟨k, hk, hactiveK⟩
    have hkA : k ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hactiveK⟩
    have hmin := Finset.min'_le A k hkA
    have hval : j₀.val ≤ k.val := Fin.le_iff_val_le_val.mp hmin
    omega
  unfold pdActiveRuns
  apply Nat.succ_le_iff.mpr
  exact Finset.card_pos.mpr ⟨j₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hstart⟩⟩

/-- A lifespan assignment has at most KN pending non-ghost primes at every tested state.
Guide runs/lanes/sol-thin-pdmem/PROOFS.md:454–467. Uses pd_active_run_count;
feeds pd_truncation_choice_majorant. In each group the union of active primes has cardinal
at most M+N; remove the M current active primes and add at most the ghost-birth count. -/
theorem pd_life_memory_bound (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid →
      ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
          ∀ γ : EnvPath S.x K, IsEnvPathAdmissible F S γ → pathCoefficient F S γ ≠ 0 →
            ∀ H : PDLifeAssignment F S γ,
              pdLifeMaxMemory F S γ H ≤ K * pathLength S.x + pdLifeGhostBirths F S γ H := by
  classical
  intro K F hF
  obtain ⟨xP, hxP, hParameters⟩ := pd_lifecycle_parameters K F hF
  obtain ⟨xR, hxR, hRunCount⟩ := pd_active_run_count δ c₁ c₂ hδ hc₁ K F hF
  let x₀ := max xP xR
  have hx₀ : 2 ≤ x₀ := by
    dsimp [x₀]
    exact le_trans hxP (le_max_left _ _)
  refine ⟨x₀, hx₀, ?_⟩
  intro S hS hx γ hAdmissible hCoefficient H
  have hxP' : xP ≤ S.x := (le_max_left xP xR).trans hx
  have hxR' : xR ≤ S.x := (le_max_right xP xR).trans hx
  have hAtX := hParameters S.x hxP'
  have hBands : ∀ i i' : Fin K, i ≠ i' →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a i')) := hAtX.2.1
  have hValidAt : ∀ j : Fin (pathLength S.x + 1), EnvValid F S (γ j) := hAdmissible.1
  have hRunAt := hRunCount S hS hxR' γ hAdmissible hCoefficient
  let Visit := Fin (pathLength S.x + 1)
  have hGroupBound (i : Fin K) (afterGhost : Bool) (j : Visit) :
      (∑ p : primeBand S.x (F.a i),
        if pdLifePending S γ p.1 (H i p) afterGhost j then 1 else 0) ≤
        pathLength S.x +
          ∑ p : primeBand S.x (F.a i),
            if (H i p).1.1.isSome then 1 else 0 := by
    let B : Finset ℕ := primeBand S.x (F.a i)
    let U : Finset ℕ := B.filter fun p => ∃ k : Visit, IsActiveAt γ p k
    let C : Finset ℕ := B.filter (fun p => IsActiveAt γ p j)
    have hBsub : U ⊆ B := Finset.filter_subset _ _
    have hRunFin :
        (∑ p ∈ B, pdActiveRuns S γ p) = slotCount S.x + pathLength S.x := by
      rw [← pdLifeMemory_sum_subtype B (fun p => pdActiveRuns S γ p)]
      simpa [B] using hRunAt i
    have hUcard : U.card ≤ slotCount S.x + pathLength S.x := by
      calc
        U.card = ∑ p ∈ B, if p ∈ U then 1 else 0 := Finset.card_eq_sum_ite hBsub
        _ ≤ ∑ p ∈ B, pdActiveRuns S γ p := by
          apply Finset.sum_le_sum
          intro p hp
          by_cases hu : p ∈ U
          · have hpos := pdLifeMemoryRuns_pos S γ p (Finset.mem_filter.mp hu).2
            simpa [hu] using hpos
          · simp [hu]
        _ = slotCount S.x + pathLength S.x := hRunFin
    have hActiveIff (p : ℕ) (hp : p ∈ B) (k : Visit) :
        IsActiveAt γ p k ↔ p ∈ pdLifeMemoryListSet (γ k).2 i :=
      pdLifeMemoryActive_iff_listSet F S γ hValidAt hBands i hp k
    have hCeq (k : Visit) :
        B.filter (fun p => IsActiveAt γ p k) = pdLifeMemoryListSet (γ k).2 i := by
      ext p
      constructor
      · intro hp
        exact (hActiveIff p (Finset.mem_filter.mp hp).1 k).mp (Finset.mem_filter.mp hp).2
      · intro hp
        have hpB := pdLifeMemoryListSet_subset_band F S γ hValidAt i k hp
        exact Finset.mem_filter.mpr ⟨hpB, (hActiveIff p hpB k).mpr hp⟩
    have hCcard : C.card = slotCount S.x := by
      change (B.filter (fun p => IsActiveAt γ p j)).card = _
      rw [hCeq j]
      exact pdLifeMemoryListSet_card F S γ hValidAt i j
    have hCsubU : C ⊆ U := by
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpB, hpactive⟩
      exact Finset.mem_filter.mpr ⟨hpB, ⟨j, hpactive⟩⟩
    have hDiffSub : U \ C ⊆ B := by
      intro p hp
      exact hBsub (Finset.mem_sdiff.mp hp).1
    have hDiffCard : (U \ C).card ≤ pathLength S.x := by
      rw [Finset.card_sdiff_of_subset hCsubU]
      omega
    have hNowMem (p : ℕ) (hp : p ∈ B) : p ∈ C ↔ IsActiveAt γ p j := by
      simp [C, hp]
    have hPendingInactive (p : {p // p ∈ B})
        (hpending : pdLifePending S γ p.1 (H i p) afterGhost j) :
        ¬ IsActiveAt γ p.1 j := by
      by_cases hA : (pdLifeActive S γ p.1).Nonempty
      · have hpending' := hpending
        simp [pdLifePending, hA] at hpending'
        exact hpending'.1
      · intro hactive
        exact hA ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hactive⟩⟩
    have hPointwise (p : {p // p ∈ B}) :
        (if pdLifePending S γ p.1 (H i p) afterGhost j then 1 else 0) ≤
          (if p.1 ∈ U ∧ ¬ IsActiveAt γ p.1 j then 1 else 0) +
            (if (H i p).1.1.isSome then 1 else 0) := by
      by_cases hpending : pdLifePending S γ p.1 (H i p) afterGhost j
      · by_cases hghost : (H i p).1.1.isSome
        · simp [hpending, hghost]
        · have hActiveEver : ∃ k : Visit, IsActiveAt γ p.1 k := by
            by_contra hnone
            have hAempty : ¬ (pdLifeActive S γ p.1).Nonempty := by
              intro hA
              rcases hA with ⟨k, hk⟩
              exact hnone ⟨k, (Finset.mem_filter.mp hk).2⟩
            have hImpossible :
                ¬ pdLifePending S γ p.1 (H i p) afterGhost j := by
              have hBirthNone : (H i p).1.1 = none := by
                cases hb : (H i p).1.1 with
                | none => rfl
                | some a => exact (hghost (by simp [hb])).elim
              have hLife : (H i p).1 = (none, (H i p).1.2) :=
                Prod.ext hBirthNone rfl
              unfold pdLifePending
              rw [dif_neg hAempty]
              rw [hLife]
              simp
            exact hImpossible hpending
          have hU : p.1 ∈ U :=
            Finset.mem_filter.mpr ⟨p.property, hActiveEver⟩
          have hInactive := hPendingInactive p hpending
          simp [hpending, hghost, hU, hInactive]
      · simp [hpending]
    have hInactiveSum :
        (∑ p : primeBand S.x (F.a i),
          if p.1 ∈ U ∧ ¬ IsActiveAt γ p.1 j then 1 else 0) = (U \ C).card := by
      calc
        _ = ∑ p : primeBand S.x (F.a i),
              if p.1 ∈ U \ C then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro p hp
            have hpC : p.1 ∈ C ↔ IsActiveAt γ p.1 j := hNowMem p.1 p.property
            by_cases hu : p.1 ∈ U <;> by_cases ha : IsActiveAt γ p.1 j <;>
              simp [hu, ha, hpC, Finset.mem_sdiff]
        _ = ∑ p ∈ B, if p ∈ U \ C then 1 else 0 :=
              pdLifeMemory_sum_subtype B (fun p => if p ∈ U \ C then 1 else 0)
        _ = (U \ C).card := (Finset.card_eq_sum_ite hDiffSub).symm
    have hGroupPointwise :
        (∑ p : primeBand S.x (F.a i),
          if pdLifePending S γ p.1 (H i p) afterGhost j then 1 else 0) ≤
          (U \ C).card +
            ∑ p : primeBand S.x (F.a i), if (H i p).1.1.isSome then 1 else 0 := by
      calc
        _ ≤ ∑ p : primeBand S.x (F.a i),
              ((if p.1 ∈ U ∧ ¬ IsActiveAt γ p.1 j then 1 else 0) +
                (if (H i p).1.1.isSome then 1 else 0)) := by
            apply Finset.sum_le_sum
            intro p hp
            exact hPointwise p
        _ = (∑ p : primeBand S.x (F.a i),
              if p.1 ∈ U ∧ ¬ IsActiveAt γ p.1 j then 1 else 0) +
              ∑ p : primeBand S.x (F.a i), if (H i p).1.1.isSome then 1 else 0 :=
            Finset.sum_add_distrib
        _ = _ := by rw [hInactiveSum]
    calc
      _ ≤ (U \ C).card +
            ∑ p : primeBand S.x (F.a i), if (H i p).1.1.isSome then 1 else 0 :=
        hGroupPointwise
      _ ≤ pathLength S.x +
            ∑ p : primeBand S.x (F.a i), if (H i p).1.1.isSome then 1 else 0 :=
        Nat.add_le_add_right hDiffCard _
  have hMemorySizeBound (afterGhost : Bool) (j : Visit) :
      pdLifeMemorySize F S γ H afterGhost j ≤
        K * pathLength S.x + pdLifeGhostBirths F S γ H := by
    unfold pdLifeMemorySize
    calc
      _ ≤ ∑ i : Fin K,
            (pathLength S.x +
              ∑ p : primeBand S.x (F.a i), if (H i p).1.1.isSome then 1 else 0) := by
        apply Finset.sum_le_sum
        intro i hi
        exact hGroupBound i afterGhost j
      _ = K * pathLength S.x + pdLifeGhostBirths F S γ H := by
        simp [pdLifeGhostBirths, Finset.sum_add_distrib]
  unfold pdLifeMaxMemory
  apply Finset.sup_le
  intro j hj
  exact max_le (hMemorySizeBound false j) (hMemorySizeBound true j)

end
end ArtinPrimitiveRoots.TypeII.PD
