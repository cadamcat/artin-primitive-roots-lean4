import ArtinPrimitiveRoots.TypeII.Proofs.PD_LIFECYCLE.Defs

set_option autoImplicit false
set_option linter.unusedVariables false

namespace ArtinPrimitiveRoots.Proofs.pd_life_b
open ArtinPrimitiveRoots.TypeII.PD
open Classical
open ArtinPrimitiveRoots.TypeII
noncomputable section

/-- A primitive integer vector remains nonzero modulo a prime in at least one coordinate. -/
private theorem pd_life_b_zmod_coords_not_both_zero (p : ℕ) (hp : p.Prime)
    (z : ℤ × ℤ) (hz : Int.gcd z.1 z.2 = 1) :
    (z.1 : ZMod p) ≠ 0 ∨ (z.2 : ZMod p) ≠ 0 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  by_contra h
  push_neg at h
  have hdiv1 : (p : ℤ) ∣ z.1 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h.1
  have hdiv2 : (p : ℤ) ∣ z.2 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h.2
  have hg : (p : ℤ) ∣ Int.gcd z.1 z.2 := dvd_gcd hdiv1 hdiv2
  have hzCast : ((Int.gcd z.1 z.2 : ℕ) : ℤ) = 1 := by exact_mod_cast hz
  have hdiv : (p : ℤ) ∣ 1 := hzCast ▸ hg
  have hdivNat : p ∣ 1 := by exact_mod_cast hdiv
  exact hp.not_dvd_one hdivNat

/-- Primitive integer vectors with determinant divisible by p determine the same
projective line over `ZMod p`. -/
theorem pd_life_b_projLine_eq_of_det_dvd (p : ℕ) (hp : p.Prime) (z z' : ℤ × ℤ)
    (hz : Int.gcd z.1 z.2 = 1) (hz' : Int.gcd z'.1 z'.2 = 1)
    (hdet : (p : ℤ) ∣ det2 z z') : projLine p z = projLine p z' := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have hdetmod :
      (z.1 : ZMod p) * (z'.2 : ZMod p) -
        (z.2 : ZMod p) * (z'.1 : ZMod p) = 0 := by
    rcases hdet with ⟨n, hn⟩
    have hcast := congrArg (fun t : ℤ => (t : ZMod p)) hn
    simpa [det2] using hcast
  have hdetEq :
      (z.1 : ZMod p) * (z'.2 : ZMod p) =
        (z.2 : ZMod p) * (z'.1 : ZMod p) := sub_eq_zero.mp hdetmod
  by_cases hz2 : (z.2 : ZMod p) = 0
  · have hz1ne : (z.1 : ZMod p) ≠ 0 := by
      rcases pd_life_b_zmod_coords_not_both_zero p hp z hz with h1 | h2
      · exact h1
      · exact (h2 hz2).elim
    have hz'2 : (z'.2 : ZMod p) = 0 := by
      have hprod : (z.1 : ZMod p) * (z'.2 : ZMod p) = 0 := by
        simpa [hz2] using hdetmod
      rcases mul_eq_zero.mp hprod with h1 | h2
      · exact (hz1ne h1).elim
      · exact h2
    simp [projLine, hz2, hz'2]
  · have hz2ne : (z.2 : ZMod p) ≠ 0 := hz2
    have hz'2ne : (z'.2 : ZMod p) ≠ 0 := by
      intro hzero
      have hprod : (z.2 : ZMod p) * (z'.1 : ZMod p) = 0 := by
        have h := hdetEq
        rw [hzero] at h
        simpa using h.symm
      rcases mul_eq_zero.mp hprod with h2 | h1
      · exact (hz2ne h2).elim
      · have hcoords := pd_life_b_zmod_coords_not_both_zero p hp z' hz'
        rcases hcoords with hleft | hright
        · exact (hleft h1).elim
        · exact (hright hzero).elim
    have hratio :
        (z.1 : ZMod p) * (z.2 : ZMod p)⁻¹ =
          (z'.1 : ZMod p) * (z'.2 : ZMod p)⁻¹ := by
      calc
        (z.1 : ZMod p) * (z.2 : ZMod p)⁻¹ =
            ((z.1 : ZMod p) * (z'.2 : ZMod p)) *
              ((z.2 : ZMod p) * (z'.2 : ZMod p))⁻¹ := by
                field_simp [hz2ne, hz'2ne] <;> ring
        _ = ((z.2 : ZMod p) * (z'.1 : ZMod p)) *
              ((z.2 : ZMod p) * (z'.2 : ZMod p))⁻¹ := by rw [hdetEq]
        _ = (z'.1 : ZMod p) * (z'.2 : ZMod p)⁻¹ := by
                field_simp [hz2ne, hz'2ne] <;> ring
    simp [projLine, hz2, hz'2ne, hratio]

/-- Slot sharing and the pad condition transport an active prime's line across an edge. -/
theorem pd_life_b_projLine_eq_of_transition_active {K : ℕ} (F : PDFix K)
    (S : PDScale) (z z' : ℤ × ℤ) (p q : PrimeLists S.x K)
    (hpv : ValidPrimeLists S.x K F.a p) (hqv : ValidPrimeLists S.x K F.a q)
    (hz : Int.gcd z.1 z.2 = 1) (hz' : Int.gcd z'.1 z'.2 = 1)
    (hslot : IsSlotTransition p q)
    (hpad : IsPadAdmissible S.d₀ (sharedProduct p) (det2 z z'))
    (r : ℕ) (hr : ∃ i j, p i j = r) (hr' : ∃ i j, q i j = r) :
    projLine r z = projLine r z' := by
  classical
  rcases hr with ⟨i, j, hsource⟩
  rcases hr' with ⟨i', j', htarget⟩
  have hrprime : r.Prime := by
    rw [← hsource]
    exact (hpv.1 i j).1
  have hj'lt : j'.val < momentJ S.x := by
    by_contra hn
    have hj'le : j'.val ≤ momentJ S.x := by
      have hlt := j'.isLt
      dsimp [slotCount] at hlt
      omega
    have hj'ge : momentJ S.x ≤ j'.val := Nat.le_of_not_gt hn
    have hj'val : j'.val = momentJ S.x := by omega
    have hj'eq : j' = lastSlot S.x := by
      apply Fin.ext
      simpa [lastSlot] using hj'val
    have hqLast : q i' (lastSlot S.x) = r := by simpa [hj'eq] using htarget
    have heq : q i' (lastSlot S.x) = p i j := hqLast.trans hsource.symm
    exact (hslot.2 i' i j) heq
  have hcopy : q i' j' = p i' j' := hslot.1 i' j' hj'lt
  have hshared : p i' j' = r := hcopy.symm.trans htarget
  have hdivNat : r ∣ sharedProduct p := by
    have hfactor : (if j'.val < momentJ S.x then p i' j' else 1) = r := by
      simp [hj'lt, hshared]
    have hinner : r ∣ ∏ j : Fin (slotCount S.x),
        if j.val < momentJ S.x then p i' j else 1 := by
      rw [← hfactor]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_univ j')
    have houter :
        (∏ j : Fin (slotCount S.x),
          if j.val < momentJ S.x then p i' j else 1) ∣ sharedProduct p :=
      Finset.dvd_prod_of_mem _ (Finset.mem_univ i')
    exact hinner.trans houter
  have hdivInt : (r : ℤ) ∣ (sharedProduct p : ℤ) := by exact_mod_cast hdivNat
  have hdet : (r : ℤ) ∣ det2 z z' := hdivInt.trans hpad.2.2
  exact pd_life_b_projLine_eq_of_det_dvd r hrprime z z' hz hz' hdet

/-- Valid active lists in separated bands give pairwise distinct initial birth values. -/
theorem pd_life_b_initialLog_values_nodup {x : ℝ} {K : ℕ} (a : Fin K → ℝ)
    (s : MemPoint x K) (hLists : ValidPrimeLists x K a s.2.1)
    (hBands : ∀ i i' : Fin K, i ≠ i' →
      Disjoint (primeBand x (a i)) (primeBand x (a i'))) :
    ((initialLog s).map Prod.snd).Nodup := by
  classical
  have hflat :
      ((List.finRange K).flatMap fun i =>
        (List.finRange (slotCount x)).map fun j => s.2.1 i j).Nodup := by
    rw [List.nodup_flatMap]
    constructor
    · intro i hi
      apply (List.nodup_map_iff_inj_on (List.nodup_finRange _)).2
      intro j hj j' hj' heq
      by_contra hne
      exact (hLists.2 i j j' hne) heq
    · apply List.pairwise_iff_getElem.mpr
      intro i i' hi hi' hij
      apply List.disjoint_left.mpr
      intro p hp hp'
      rcases List.mem_map.mp hp with ⟨j, hj, hjEq⟩
      rcases List.mem_map.mp hp' with ⟨j', hj', hj'Eq⟩
      let g := (List.finRange K)[i]
      let g' := (List.finRange K)[i']
      have hEq : s.2.1 g j = s.2.1 g' j' := hjEq.trans hj'Eq.symm
      have hGroupNe : g ≠ g' := by
        intro heq
        have hidx : i = i' := by simpa [g, g'] using congrArg Fin.val heq
        omega
      have hdisj := hBands g g' hGroupNe
      have hLeft : s.2.1 g j ∈ primeBand x (a g) := (hLists.1 g j).2
      have hRight : s.2.1 g j ∈ primeBand x (a g') := by
        rw [hEq]
        exact (hLists.1 g' j').2
      have hnot : s.2.1 g j ∉ primeBand x (a g') :=
        (Finset.disjoint_left.mp hdisj) hLeft
      exact hnot hRight
  simpa [initialLog, List.map_flatMap, List.map_map, Function.comp_def] using hflat

private theorem pd_life_b_validPrimeLists_permute {x : ℝ} {K : ℕ}
    {a : Fin K → ℝ} (σ : Fin K → Equiv.Perm (Fin (slotCount x)))
    (p : PrimeLists x K) (hp : ValidPrimeLists x K a p) :
    ValidPrimeLists x K a (permuteLists σ p) := by
  rcases hp with ⟨hband, hdistinct⟩
  constructor
  · intro i j
    simpa [permuteLists] using hband i (σ i j)
  · intro i j j' hne
    apply hdistinct i (σ i j) (σ i j')
    intro heq
    exact hne ((σ i).injective heq)

/-- A nonzero slot kernel forces every prime shared by its endpoint lists to retain
the same projective line. -/
private theorem pd_life_b_projLine_eq_of_slotKernel_nezero {K : ℕ} (F : PDFix K)
    (S : PDScale) (z z' : ℤ × ℤ) (p q : PrimeLists S.x K)
    (hpv : ValidPrimeLists S.x K F.a p) (hqv : ValidPrimeLists S.x K F.a q)
    (hz : Int.gcd z.1 z.2 = 1) (hz' : Int.gcd z'.1 z'.2 = 1)
    (hkernel : slotKernel F S p q (det2 z z') ≠ 0)
    (r : ℕ) (hr : ∃ i j, p i j = r) (hr' : ∃ i j, q i j = r) :
    projLine r z = projLine r z' := by
  have hcondition :
      IsSlotTransition p q ∧ IsPadAdmissible S.d₀ (sharedProduct p) (det2 z z') := by
    by_contra h
    apply hkernel
    simp [slotKernel, h]
  exact pd_life_b_projLine_eq_of_transition_active F S z z' p q hpv hqv hz hz'
    hcondition.1 hcondition.2 r hr hr'

/-- Along every edge, a prime active at both visits has the same line whenever the
signed path coefficient is nonzero. -/
theorem pd_life_b_adjacent_active_line_eq_of_pathCoefficient_nezero {K : ℕ}
    (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (hAdm : IsEnvPathAdmissible F S γ) (hcoef : pathCoefficient F S γ ≠ 0)
    (j : Fin (pathLength S.x)) (p : ℕ)
    (hsource : IsActiveAt γ p j.castSucc) (htarget : IsActiveAt γ p j.succ) :
    projLine p (γ j.castSucc).1 = projLine p (γ j.succ).1 := by
  classical
  have hKernelProduct :
      (∏ e : Fin (pathLength S.x),
        symKernel F S (decide (e.val % 2 = 0)) (γ e.castSucc) (γ e.succ)) ≠ 0 := by
    intro hzero
    apply hcoef
    simp [pathCoefficient, hzero]
  have hSym :
      symKernel F S (decide (j.val % 2 = 0)) (γ j.castSucc) (γ j.succ) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hKernelProduct) j (Finset.mem_univ _)
  have hsum :
      (∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
        ∑ σ' : Fin K → Equiv.Perm (Fin (slotCount S.x)),
          if decide (j.val % 2 = 0) then
            slotKernel F S (permuteLists σ (γ j.castSucc).2)
              (permuteLists σ' (γ j.succ).2)
              (det2 (γ j.castSucc).1 (γ j.succ).1)
          else star (slotKernel F S (permuteLists σ' (γ j.succ).2)
              (permuteLists σ (γ j.castSucc).2)
              (det2 (γ j.succ).1 (γ j.castSucc).1))) ≠ 0 := by
    have hs := hSym
    unfold symKernel at hs
    exact (mul_ne_zero_iff.mp hs).2
  obtain ⟨σ, hσ, hInner⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  obtain ⟨σ', hσ', hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hInner
  have hEnvSource : EnvValid F S (γ j.castSucc) := hAdm.1 j.castSucc
  have hEnvTarget : EnvValid F S (γ j.succ) := hAdm.1 j.succ
  by_cases heven : j.val % 2 = 0
  · have hkernel :
        slotKernel F S (permuteLists σ (γ j.castSucc).2)
          (permuteLists σ' (γ j.succ).2)
          (det2 (γ j.castSucc).1 (γ j.succ).1) ≠ 0 := by
      simpa [heven] using hterm
    have hsource' : ∃ i k, (permuteLists σ (γ j.castSucc).2) i k = p := by
      rcases hsource with ⟨i, k, hk⟩
      refine ⟨i, (σ i)⁻¹ k, ?_⟩
      simp [permuteLists, hk]
    have htarget' : ∃ i k, (permuteLists σ' (γ j.succ).2) i k = p := by
      rcases htarget with ⟨i, k, hk⟩
      refine ⟨i, (σ' i)⁻¹ k, ?_⟩
      simp [permuteLists, hk]
    exact pd_life_b_projLine_eq_of_slotKernel_nezero F S
      (γ j.castSucc).1 (γ j.succ).1
      (permuteLists σ (γ j.castSucc).2) (permuteLists σ' (γ j.succ).2)
      (pd_life_b_validPrimeLists_permute σ (γ j.castSucc).2 hEnvSource.2)
      (pd_life_b_validPrimeLists_permute σ' (γ j.succ).2 hEnvTarget.2)
      hEnvSource.1 hEnvTarget.1 hkernel p hsource' htarget'
  · have hkernel :
        slotKernel F S (permuteLists σ' (γ j.succ).2)
          (permuteLists σ (γ j.castSucc).2)
          (det2 (γ j.succ).1 (γ j.castSucc).1) ≠ 0 := by
      have hstar : star
          (slotKernel F S (permuteLists σ' (γ j.succ).2)
            (permuteLists σ (γ j.castSucc).2)
            (det2 (γ j.succ).1 (γ j.castSucc).1)) ≠ 0 := by
        simpa [heven] using hterm
      intro hz
      exact hstar (by simp [hz])
    have htarget' : ∃ i k, (permuteLists σ' (γ j.succ).2) i k = p := by
      rcases htarget with ⟨i, k, hk⟩
      refine ⟨i, (σ' i)⁻¹ k, ?_⟩
      simp [permuteLists, hk]
    have hsource' : ∃ i k, (permuteLists σ (γ j.castSucc).2) i k = p := by
      rcases hsource with ⟨i, k, hk⟩
      refine ⟨i, (σ i)⁻¹ k, ?_⟩
      simp [permuteLists, hk]
    have hrev := pd_life_b_projLine_eq_of_slotKernel_nezero F S
      (γ j.succ).1 (γ j.castSucc).1
      (permuteLists σ' (γ j.succ).2) (permuteLists σ (γ j.castSucc).2)
      (pd_life_b_validPrimeLists_permute σ' (γ j.succ).2 hEnvTarget.2)
      (pd_life_b_validPrimeLists_permute σ (γ j.castSucc).2 hEnvSource.2)
      hEnvTarget.1 hEnvSource.1 hkernel p htarget' hsource'
    exact hrev.symm

/-- For a never-active prime with a ghost-only lifespan, the pending-memory interval is
half-open on each side of the ghost operation. -/
theorem pd_life_b_pending_ghostOnly {K : ℕ} (S : PDScale) (γ : EnvPath S.x K)
    (p : ℕ) (life : PrimeLife S γ p)
    (hA : ¬ (pdLifeActive S γ p).Nonempty) (a c : Fin (pathLength S.x + 1))
    (hLife : life.1 = (some a, some c)) (j : Fin (pathLength S.x + 1)) :
    (pdLifePending S γ p life true j ↔ a ≤ j ∧ j < c) ∧
      (pdLifePending S γ p life false j ↔ a < j ∧ j ≤ c) := by
  simp [pdLifePending, hA, hLife]

/-- At a prefix ghost endpoint of an active prime, the pending interval begins at that
visit after the ghost and strictly after it before the ghost. -/
theorem pd_life_b_pending_prefix_active {K : ℕ} (S : PDScale) (γ : EnvPath S.x K)
    (p : ℕ) (life : PrimeLife S γ p) (hA : (pdLifeActive S γ p).Nonempty)
    (a j : Fin (pathLength S.x + 1)) (hBirth : life.1.1 = some a)
    (hj : j < (pdLifeActive S γ p).min' hA) (hInactive : ¬ IsActiveAt γ p j) :
    (pdLifePending S γ p life true j ↔ a ≤ j) ∧
      (pdLifePending S γ p life false j ↔ a < j) := by
  simp [pdLifePending, hA, hBirth, hj, hInactive]

/-- At a suffix ghost endpoint of an active prime, the pending interval ends after the
ghost at that visit and before the ghost strictly earlier. -/
theorem pd_life_b_pending_suffix_active {K : ℕ} (S : PDScale) (γ : EnvPath S.x K)
    (p : ℕ) (life : PrimeLife S γ p) (hA : (pdLifeActive S γ p).Nonempty)
    (c j : Fin (pathLength S.x + 1)) (hDelete : life.1.2 = some c)
    (hωj : (pdLifeActive S γ p).max' hA < j) (hInactive : ¬ IsActiveAt γ p j) :
    (pdLifePending S γ p life true j ↔ j < c) ∧
      (pdLifePending S γ p life false j ↔ j ≤ c) := by
  have hAll : ∀ y ∈ pdLifeActive S γ p, y < j := by
    intro y hy
    have hle : y ≤ (pdLifeActive S γ p).max' hA := by
      simpa using Finset.le_max' (pdLifeActive S γ p) y hy
    exact hle.trans_lt hωj
  have hnotAll : ¬ ∀ y ∈ pdLifeActive S γ p, j < y := by
    intro hall
    have hmax := hall _ (Finset.max'_mem _ hA)
    omega
  simp [pdLifePending, hA, hDelete, hnotAll, hInactive]
  exact ⟨Or.inl hAll, Or.inl hAll⟩

/-- An active visit never carries a pending particle for the same prime. -/
theorem pd_life_b_not_pending_at_active_visit {K : ℕ} (S : PDScale)
    (γ : EnvPath S.x K) (p : ℕ) (life : PrimeLife S γ p)
    (j : Fin (pathLength S.x + 1)) (hactive : IsActiveAt γ p j) :
    ¬ pdLifePending S γ p life true j ∧ ¬ pdLifePending S γ p life false j := by
  have hA : (pdLifeActive S γ p).Nonempty := by
    refine ⟨j, ?_⟩
    simp [pdLifeActive, hactive]
  simp [pdLifePending, hA, hactive]

/-- Between the first and last active visits, an inactive prime is pending on both sides
of the ghost operation. -/
theorem pd_life_b_pending_in_active_span {K : ℕ} (S : PDScale) (γ : EnvPath S.x K)
    (p : ℕ) (life : PrimeLife S γ p) (hA : (pdLifeActive S γ p).Nonempty)
    (j : Fin (pathLength S.x + 1))
    (hα : (pdLifeActive S γ p).min' hA ≤ j)
    (hω : j ≤ (pdLifeActive S γ p).max' hA)
    (hInactive : ¬ IsActiveAt γ p j) :
    pdLifePending S γ p life true j ∧ pdLifePending S γ p life false j := by
  have hnotPrefix : ¬ ∀ y ∈ pdLifeActive S γ p, j < y := by
    intro hall
    have hlt := hall _ (Finset.min'_mem _ hA)
    omega
  have hnotSuffix : ¬ ∀ y ∈ pdLifeActive S γ p, y < j := by
    intro hall
    have hlt := hall _ (Finset.max'_mem _ hA)
    omega
  simp [pdLifePending, hA, hnotPrefix, hnotSuffix, hInactive]

/-- At an active-prime prefix ghost endpoint, pending memory is created exactly at that
visit. -/
theorem pd_life_b_pending_prefix_birth_event {K : ℕ} (S : PDScale)
    (γ : EnvPath S.x K) (p : ℕ) (life : PrimeLife S γ p)
    (hA : (pdLifeActive S γ p).Nonempty) (a j : Fin (pathLength S.x + 1))
    (hBirth : life.1.1 = some a) (hj : j < (pdLifeActive S γ p).min' hA)
    (hInactive : ¬ IsActiveAt γ p j) :
    (pdLifePending S γ p life true j ∧ ¬ pdLifePending S γ p life false j) ↔ a = j := by
  have hPending := pd_life_b_pending_prefix_active S γ p life hA a j hBirth hj hInactive
  constructor
  · rintro ⟨ha, hb⟩
    have hle : a ≤ j := hPending.1.mp ha
    have hnot : ¬ a < j := by
      intro hlt
      exact hb (hPending.2.mpr hlt)
    apply Fin.ext
    omega
  · intro hEq
    subst j
    constructor
    · exact hPending.1.mpr le_rfl
    · intro hbefore
      exact (not_lt_of_ge le_rfl) (hPending.2.mp hbefore)

/-- At an active-prime suffix ghost endpoint, pending memory is deleted exactly at that
visit. -/
theorem pd_life_b_pending_suffix_delete_event {K : ℕ} (S : PDScale)
    (γ : EnvPath S.x K) (p : ℕ) (life : PrimeLife S γ p)
    (hA : (pdLifeActive S γ p).Nonempty) (c j : Fin (pathLength S.x + 1))
    (hDelete : life.1.2 = some c) (hωj : (pdLifeActive S γ p).max' hA < j)
    (hInactive : ¬ IsActiveAt γ p j) :
    (pdLifePending S γ p life false j ∧ ¬ pdLifePending S γ p life true j) ↔ j = c := by
  have hPending := pd_life_b_pending_suffix_active S γ p life hA c j hDelete hωj hInactive
  constructor
  · rintro ⟨hb, ha⟩
    have hle : j ≤ c := hPending.2.mp hb
    have hnot : ¬ j < c := by
      intro hlt
      exact ha (hPending.1.mpr hlt)
    apply Fin.ext
    omega
  · intro hEq
    subst j
    constructor
    · exact hPending.2.mpr le_rfl
    · intro hafter
      exact (not_lt_of_ge le_rfl) (hPending.1.mp hafter)

/-- For a ghost-only prime, pending memory is created and deleted at its two endpoints. -/
theorem pd_life_b_pending_ghostOnly_events {K : ℕ} (S : PDScale)
    (γ : EnvPath S.x K) (p : ℕ) (life : PrimeLife S γ p)
    (hA : ¬ (pdLifeActive S γ p).Nonempty) (a c j : Fin (pathLength S.x + 1))
    (hLife : life.1 = (some a, some c)) (hac : a < c) :
    ((pdLifePending S γ p life true j ∧ ¬ pdLifePending S γ p life false j) ↔ a = j) ∧
      ((pdLifePending S γ p life false j ∧ ¬ pdLifePending S γ p life true j) ↔ j = c) := by
  have hPending := pd_life_b_pending_ghostOnly S γ p life hA a c hLife j
  constructor
  · constructor
    · rintro ⟨hafter, hnot⟩
      rcases hPending.1.mp hafter with ⟨hale, hjc⟩
      have hnotlt : ¬ a < j := by
        intro hlt
        exact hnot (hPending.2.mpr ⟨hlt, hjc.le⟩)
      apply Fin.ext
      omega
    · intro hEq
      subst j
      constructor
      · exact hPending.1.mpr ⟨le_rfl, hac⟩
      · intro hbefore
        exact (not_lt_of_ge le_rfl) (hPending.2.mp hbefore).1
  · constructor
    · rintro ⟨hbefore, hnot⟩
      rcases hPending.2.mp hbefore with ⟨haj, hjle⟩
      have hnotlt : ¬ j < c := by
        intro hlt
        exact hnot (hPending.1.mpr ⟨haj.le, hlt⟩)
      apply Fin.ext
      omega
    · intro hEq
      subst j
      constructor
      · exact hPending.2.mpr ⟨hac, le_rfl⟩
      · intro hafter
        exact (not_lt_of_ge le_rfl) (hPending.1.mp hafter).2

end
end ArtinPrimitiveRoots.Proofs.pd_life_b
