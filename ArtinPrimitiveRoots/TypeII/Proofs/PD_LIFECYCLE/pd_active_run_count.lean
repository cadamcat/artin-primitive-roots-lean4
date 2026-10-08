import ArtinPrimitiveRoots.TypeII.Proofs.PD_LIFECYCLE.pd_lifecycle_parameters

set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical Filter
open ArtinPrimitiveRoots.TypeII
noncomputable section

private def pdLifeListSet {x : ℝ} {K : ℕ} (p : PrimeLists x K) (i : Fin K) :
    Finset ℕ := Finset.univ.image (p i)

private def pdLifeRunStart {x : ℝ} {K : ℕ} (γ : EnvPath x K) (p : ℕ)
    (j : Fin (pathLength x + 1)) : Prop :=
  IsActiveAt γ p j ∧ ¬ ∃ k : Fin (pathLength x + 1),
    k.val + 1 = j.val ∧ IsActiveAt γ p k

private lemma pdLife_sum_subtype {α β : Type*} [AddCommMonoid β]
    (T : Finset α) (f : α → β) :
    (∑ x : {x // x ∈ T}, f x.1) = ∑ x ∈ T, f x := by
  classical
  have hAttach : T.attach = (Finset.univ : Finset {x // x ∈ T}) := by
    ext x
    simp
  rw [← hAttach]
  exact Finset.sum_attach (s := T) (f := f)

private lemma pdLifeListSet_card {x : ℝ} {K : ℕ} (F : PDFix K) (S : PDScale)
    (γ : EnvPath S.x K) (hγ : ∀ j, EnvValid F S (γ j)) (i : Fin K)
    (j : Fin (pathLength S.x + 1)) :
    (pdLifeListSet (γ j).2 i).card = slotCount S.x := by
  classical
  have hinj : Function.Injective ((γ j).2 i) := by
    intro k k' h
    by_contra hne
    exact (hγ j).2.2 i k k' hne h
  unfold pdLifeListSet
  rw [Finset.card_image_of_injective _ hinj]
  simp

private lemma pdLifeListSet_subset_band {x : ℝ} {K : ℕ} (F : PDFix K)
    (S : PDScale) (γ : EnvPath S.x K) (hγ : ∀ j, EnvValid F S (γ j))
    (i : Fin K) (j : Fin (pathLength S.x + 1)) :
    pdLifeListSet (γ j).2 i ⊆ primeBand S.x (F.a i) := by
  intro p hp
  rcases Finset.mem_image.mp hp with ⟨k, hk, hkp⟩
  rw [← hkp]
  exact (hγ j).2.1 i k |>.2

private lemma pdLifeListSet_permute {x : ℝ} {K : ℕ} (p : PrimeLists x K)
    (σ : Fin K → Equiv.Perm (Fin (slotCount x))) (i : Fin K) :
    pdLifeListSet (permuteLists σ p) i = pdLifeListSet p i := by
  classical
  ext r
  simp only [pdLifeListSet, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨σ i j, hj⟩
  · rintro ⟨j, hj⟩
    exact ⟨(σ i).symm j, by simpa [permuteLists] using hj⟩

private lemma pdLifeActive_iff_listSet {x : ℝ} {K : ℕ} (F : PDFix K)
    (S : PDScale) (γ : EnvPath S.x K) (hγ : ∀ j, EnvValid F S (γ j))
    (hBands : ∀ i i' : Fin K, i ≠ i' →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a i')))
    (i : Fin K) {p : ℕ} (hp : p ∈ primeBand S.x (F.a i))
    (j : Fin (pathLength S.x + 1)) :
    IsActiveAt γ p j ↔ p ∈ pdLifeListSet (γ j).2 i := by
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

private lemma pdLifeListSet_sdiff_eq_singleton {x : ℝ} {K : ℕ}
    (p q : PrimeLists x K) (hslot : IsSlotTransition p q) (i : Fin K) :
    pdLifeListSet q i \ pdLifeListSet p i = {q i (lastSlot x)} := by
  classical
  have hnewMem : q i (lastSlot x) ∈ pdLifeListSet q i :=
    Finset.mem_image.mpr ⟨lastSlot x, Finset.mem_univ _, rfl⟩
  have hnewNot : q i (lastSlot x) ∉ pdLifeListSet p i := by
    intro hp
    rcases Finset.mem_image.mp hp with ⟨j, hj, hjp⟩
    exact (hslot.2 i i j) (by simpa using hjp.symm)
  ext r
  constructor
  · intro hr
    rcases Finset.mem_sdiff.mp hr with ⟨hrq, hrp⟩
    rcases Finset.mem_image.mp hrq with ⟨j, hj, hjq⟩
    by_cases hlast : j = lastSlot x
    · simpa [hlast] using hjq.symm
    · have hval : j.val ≠ momentJ x := by
        intro hval
        apply hlast
        apply Fin.ext
        simpa [lastSlot] using hval
      have hjlt : j.val < momentJ x := by
        have hjbound := j.isLt
        dsimp [slotCount] at hjbound
        omega
      have hcopy := hslot.1 i j hjlt
      exact (False.elim (hrp (Finset.mem_image.mpr
        ⟨j, Finset.mem_univ _, hcopy.symm.trans hjq⟩)))
  · intro hr
    have hr' : r = q i (lastSlot x) := Finset.mem_singleton.mp hr
    subst r
    exact Finset.mem_sdiff.mpr ⟨hnewMem, hnewNot⟩

private lemma pdLifeListSet_sdiff_card_of_permuted_transition {x : ℝ} {K : ℕ}
    (p q : PrimeLists x K)
    (σ σ' : Fin K → Equiv.Perm (Fin (slotCount x)))
    (hslot : IsSlotTransition (permuteLists σ p) (permuteLists σ' q))
    (i : Fin K) :
    (pdLifeListSet q i \ pdLifeListSet p i).card = 1 := by
  have hP := pdLifeListSet_permute p σ i
  have hQ := pdLifeListSet_permute q σ' i
  rw [← hQ, ← hP, pdLifeListSet_sdiff_eq_singleton _ _ hslot i]
  simp

private lemma pdLifeSlotKernel_nonzero_transition {K : ℕ}
    (F : PDFix K) (S : PDScale) (p q : PrimeLists S.x K) (dt : ℤ)
    (hslot : slotKernel F S p q dt ≠ 0) : IsSlotTransition p q := by
  by_contra hbad
  have hzero : slotKernel F S p q dt = 0 := by
    simp [slotKernel, hbad]
  exact hslot hzero

private lemma pdLifeSymKernel_nonzero_term {K : ℕ} (F : PDFix K) (S : PDScale)
    (forward : Bool) (s s' : EnvPoint S.x K)
    (hsym : symKernel F S forward s s' ≠ 0) :
    ∃ σ σ' : Fin K → Equiv.Perm (Fin (slotCount S.x)),
      (if forward then
        slotKernel F S (permuteLists σ s.2) (permuteLists σ' s'.2) (det2 s.1 s'.1)
      else
        star (slotKernel F S (permuteLists σ' s'.2) (permuteLists σ s.2)
          (det2 s'.1 s.1))) ≠ 0 := by
  classical
  let A (σ σ' : Fin K → Equiv.Perm (Fin (slotCount S.x))) : ℂ :=
    if forward then
      slotKernel F S (permuteLists σ s.2) (permuteLists σ' s'.2) (det2 s.1 s'.1)
    else
      star (slotKernel F S (permuteLists σ' s'.2) (permuteLists σ s.2)
        (det2 s'.1 s.1))
  have hsum :
      (∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
        ∑ σ' : Fin K → Equiv.Perm (Fin (slotCount S.x)), A σ σ') ≠ 0 := by
    have hmul : ((permCount S.x K : ℂ))⁻¹ ^ 2 *
        (∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
          ∑ σ' : Fin K → Equiv.Perm (Fin (slotCount S.x)), A σ σ') ≠ 0 := by
      simpa [symKernel, A] using hsym
    exact (mul_ne_zero_iff.mp hmul).2
  obtain ⟨σ, hσ, hinner⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  obtain ⟨σ', hσ', hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hinner
  exact ⟨σ, σ', by simpa [A] using hterm⟩

private lemma pdLifeEdge_sdiff_card {K : ℕ} (F : PDFix K) (S : PDScale)
    (γ : EnvPath S.x K) (hγ : IsEnvPathAdmissible F S γ)
    (hcoef : pathCoefficient F S γ ≠ 0) (e : Fin (pathLength S.x)) (i : Fin K) :
    (pdLifeListSet (γ e.succ).2 i \ pdLifeListSet (γ e.castSucc).2 i).card = 1 := by
  classical
  have hprod :
      (∏ j : Fin (pathLength S.x),
        symKernel F S (decide (j.val % 2 = 0)) (γ j.castSucc) (γ j.succ)) ≠ 0 := by
    have hmul := hcoef
    unfold pathCoefficient at hmul
    exact (mul_ne_zero_iff.mp hmul).2
  have hsym :
      symKernel F S (decide (e.val % 2 = 0)) (γ e.castSucc) (γ e.succ) ≠ 0 := by
    intro hzero
    apply hprod
    rw [Finset.prod_eq_zero (Finset.mem_univ e) hzero]
  obtain ⟨σ, σ', hterm⟩ := pdLifeSymKernel_nonzero_term F S
    (decide (e.val % 2 = 0)) (γ e.castSucc) (γ e.succ) hsym
  cases hfwd : decide (e.val % 2 = 0) with
  | true =>
      have hslot : slotKernel F S (permuteLists σ (γ e.castSucc).2)
          (permuteLists σ' (γ e.succ).2)
          (det2 (γ e.castSucc).1 (γ e.succ).1) ≠ 0 := by
        simpa [hfwd] using hterm
      exact pdLifeListSet_sdiff_card_of_permuted_transition _ _ σ σ'
        (pdLifeSlotKernel_nonzero_transition F S _ _
          (det2 (γ e.castSucc).1 (γ e.succ).1) hslot) i
  | false =>
      have hslot : slotKernel F S (permuteLists σ' (γ e.succ).2)
          (permuteLists σ (γ e.castSucc).2)
          (det2 (γ e.succ).1 (γ e.castSucc).1) ≠ 0 := by
        have hstar := by simpa [hfwd] using hterm
        simpa using hstar
      have hreverse := pdLifeListSet_sdiff_card_of_permuted_transition _ _ σ' σ
        (pdLifeSlotKernel_nonzero_transition F S _ _
          (det2 (γ e.succ).1 (γ e.castSucc).1) hslot) i
      have hsource := pdLifeListSet_card (x := S.x) F S γ
        (fun j => hγ.1 j) i e.castSucc
      have htarget := pdLifeListSet_card (x := S.x) F S γ
        (fun j => hγ.1 j) i e.succ
      have hformula₁ := Finset.card_sdiff_add_card_inter
        (pdLifeListSet (γ e.succ).2 i) (pdLifeListSet (γ e.castSucc).2 i)
      have hformula₂ := Finset.card_sdiff_add_card_inter
        (pdLifeListSet (γ e.castSucc).2 i) (pdLifeListSet (γ e.succ).2 i)
      rw [Finset.inter_comm] at hformula₂
      omega

/-- On a nonzero path each group has M initial runs and exactly one new run per edge.
Guide runs/lanes/sol-thin-pdmem/PROOFS.md:434–449. Uses the support of symKernel,
IsSlotTransition and disjoint bands; feeds pd_history_scalar_charge and the active count
in pd_doubled_lifespan_bound. Odd edges give the same undirected set transition. -/
theorem pd_active_run_count (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid →
      ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
        ∀ γ : EnvPath S.x K, IsEnvPathAdmissible F S γ → pathCoefficient F S γ ≠ 0 →
          ∀ i : Fin K, (∑ p : primeBand S.x (F.a i), pdActiveRuns S γ p.1) =
            slotCount S.x + pathLength S.x := by
  classical
  intro K F hF
  obtain ⟨x₀, hx₀, hParameters⟩ := pd_lifecycle_parameters K F hF
  refine ⟨x₀, hx₀, ?_⟩
  intro S hS hx γ hAdmissible hCoefficient i
  let B : Finset ℕ := primeBand S.x (F.a i)
  let Visit := Fin (pathLength S.x + 1)
  have hBands : ∀ i i' : Fin K, i ≠ i' →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a i')) :=
    (hParameters S.x hx).2.1
  have hValidLists : ∀ j : Visit, ValidPrimeLists S.x K F.a (γ j).2 :=
    fun j => (hAdmissible.1 j).2
  have hStartExpand :
      (∑ p : B, pdActiveRuns S γ p.1) =
        ∑ j : Visit, ∑ p : B,
          if pdLifeRunStart γ p.1 j then 1 else 0 := by
    calc
      _ = ∑ p : B, ∑ j : Visit,
            if pdLifeRunStart γ p.1 j then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro p hp
        unfold pdActiveRuns
        let T : Finset Visit := Finset.univ.filter
          (fun j => IsActiveAt γ p.1 j ∧
            ¬ ∃ k : Visit, k.val + 1 = j.val ∧ IsActiveAt γ p.1 k)
        change T.card = _
        calc
          _ = ∑ j ∈ (Finset.univ : Finset Visit), if j ∈ T then 1 else 0 :=
            Finset.card_eq_sum_ite (Finset.subset_univ T)
          _ = ∑ j : Visit,
                if pdLifeRunStart γ p.1 j then 1 else 0 := by
              apply Finset.sum_congr rfl
              intro j hj
              simp [T, pdLifeRunStart] <;> rfl
      _ = ∑ j : Visit, ∑ p : B,
            if pdLifeRunStart γ p.1 j then 1 else 0 := Finset.sum_comm
  have hStartCount (j : Visit) :
      (∑ p : B, if pdLifeRunStart γ p.1 j then 1 else 0) =
        if j.val = 0 then slotCount S.x else 1 := by
    by_cases hj0 : j.val = 0
    · have hNoPrev (p : ℕ) :
          ¬ ∃ k : Visit, k.val + 1 = j.val ∧ IsActiveAt γ p k := by
        rintro ⟨k, hk, _⟩
        omega
      have hStartIff (p : ℕ) (hp : p ∈ B) :
          pdLifeRunStart γ p j ↔ p ∈ pdLifeListSet (γ j).2 i := by
        have hActive := pdLifeActive_iff_listSet (x := S.x) F S γ hAdmissible.1 hBands
          i hp j
        change (IsActiveAt γ p j ∧
          ¬ ∃ k : Visit, k.val + 1 = j.val ∧ IsActiveAt γ p k) ↔ _
        constructor
        · rintro ⟨hcurrent, _⟩
          exact hActive.mp hcurrent
        · intro hmem
          refine ⟨hActive.mpr hmem, ?_⟩
          rintro ⟨k, hk, hprevious⟩
          exact hNoPrev p ⟨k, hk, hprevious⟩
      have hSubset : pdLifeListSet (γ j).2 i ⊆ B := by
        exact pdLifeListSet_subset_band (x := S.x) F S γ hAdmissible.1 i j
      calc
        _ = ∑ p : B, if (p.1 ∈ pdLifeListSet (γ j).2 i) then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro p hp
          simp [hStartIff p.1 p.property]
        _ = ∑ p ∈ B, if p ∈ pdLifeListSet (γ j).2 i then 1 else 0 :=
          pdLife_sum_subtype B (fun p => if p ∈ pdLifeListSet (γ j).2 i then 1 else 0)
        _ = (pdLifeListSet (γ j).2 i).card :=
          (Finset.card_eq_sum_ite hSubset).symm
        _ = slotCount S.x :=
          pdLifeListSet_card (x := S.x) F S γ hAdmissible.1 i j
      simp [hj0]
    · let jPrev : Visit := ⟨j.val - 1, by have := j.isLt; omega⟩
      have hjge : 1 ≤ j.val := by omega
      have hPred (p : ℕ) :
          (∃ k : Visit, k.val + 1 = j.val ∧ IsActiveAt γ p k) ↔
            IsActiveAt γ p jPrev := by
        constructor
        · rintro ⟨k, hk, hactive⟩
          have hval : k.val = jPrev.val := by dsimp [jPrev]; omega
          have heq : k = jPrev := Fin.ext hval
          simpa [heq] using hactive
        · intro hactive
          have hsucc : jPrev.val + 1 = j.val := by
            dsimp [jPrev]
            exact Nat.sub_add_cancel hjge
          exact ⟨jPrev, hsucc, hactive⟩
      have hStartIff (p : ℕ) (hp : p ∈ B) :
          pdLifeRunStart γ p j ↔
            p ∈ pdLifeListSet (γ j).2 i \ pdLifeListSet (γ jPrev).2 i := by
        change (IsActiveAt γ p j ∧
          ¬ ∃ k : Visit, k.val + 1 = j.val ∧ IsActiveAt γ p k) ↔ _
        constructor
        · rintro ⟨hcurrent, hnoPrev⟩
          have hprev : ¬ IsActiveAt γ p jPrev := by
            intro hprev
            exact hnoPrev ((hPred p).mpr hprev)
          exact Finset.mem_sdiff.mpr ⟨
            (pdLifeActive_iff_listSet (x := S.x) F S γ hAdmissible.1 hBands i hp j).mp hcurrent,
            fun hmem => hprev ((pdLifeActive_iff_listSet (x := S.x) F S γ hAdmissible.1 hBands i hp jPrev).mpr hmem)⟩
        · intro hmem
          have hmem' := Finset.mem_sdiff.mp hmem
          have hcurrent :=
            (pdLifeActive_iff_listSet (x := S.x) F S γ hAdmissible.1 hBands i hp j).mpr hmem'.1
          have hprev : ¬ IsActiveAt γ p jPrev := by
            intro hprev
            exact hmem'.2 ((pdLifeActive_iff_listSet (x := S.x) F S γ hAdmissible.1 hBands i hp jPrev).mp hprev)
          refine ⟨hcurrent, ?_⟩
          rintro ⟨k, hk, hactive⟩
          exact hprev ((hPred p).mp ⟨k, hk, hactive⟩)
      have hSubset :
          (pdLifeListSet (γ j).2 i \ pdLifeListSet (γ jPrev).2 i) ⊆ B := by
        intro p hp
        exact pdLifeListSet_subset_band (x := S.x) F S γ hAdmissible.1 i j
          (Finset.mem_sdiff.mp hp).1
      let e : Fin (pathLength S.x) := ⟨j.val - 1, by have := j.isLt; omega⟩
      have heSucc : e.succ = j := by
        apply Fin.ext
        dsimp [e]
        exact Nat.sub_add_cancel hjge
      have heCast : e.castSucc = jPrev := by
        apply Fin.ext
        rfl
      have hEdge := pdLifeEdge_sdiff_card F S γ hAdmissible hCoefficient e i
      have hEdge' :
          (pdLifeListSet (γ j).2 i \ pdLifeListSet (γ jPrev).2 i).card = 1 := by
        simpa [heSucc, heCast] using hEdge
      calc
        _ = ∑ p : B,
              if p.1 ∈ pdLifeListSet (γ j).2 i \ pdLifeListSet (γ jPrev).2 i
              then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro p hp
          simp [hStartIff p.1 p.property]
        _ = ∑ p ∈ B,
              if p ∈ pdLifeListSet (γ j).2 i \ pdLifeListSet (γ jPrev).2 i
              then 1 else 0 := pdLife_sum_subtype B
                (fun p => if p ∈ pdLifeListSet (γ j).2 i \ pdLifeListSet (γ jPrev).2 i
                  then 1 else 0)
        _ = (pdLifeListSet (γ j).2 i \ pdLifeListSet (γ jPrev).2 i).card :=
          (Finset.card_eq_sum_ite hSubset).symm
        _ = 1 := hEdge'
      simp [hj0]
  calc
    _ = ∑ j : Visit, if j.val = 0 then slotCount S.x else 1 := by
        rw [hStartExpand]
        apply Finset.sum_congr rfl
        intro j hj
        exact hStartCount j
    _ = slotCount S.x + pathLength S.x := by
      rw [Fin.sum_univ_succ]
      simp

end
end ArtinPrimitiveRoots.TypeII.PD
