import ArtinPrimitiveRoots.Proofs.pd_life_b.GuidedGhostOut
import ArtinPrimitiveRoots.Proofs.pd_life_b.GuidedEdgeGeo

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_birth_opus

open Classical
open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
open ArtinPrimitiveRoots.Proofs.pd_life_b

noncomputable section

/-- Hits of a life-state memory list, counted by band primes. -/
theorem hitCount_life {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (H : PDLifeAssignment F S γ) (i : Fin K) (b : Bool) (jP jz : Fin (pathLength S.x + 1))
    (l : List Particle) (hnd : (l.map Prod.fst).Nodup)
    (hmem : ∀ q : Particle, q ∈ l ↔ ∃ hp : q.1 ∈ primeBand S.x (F.a i),
      pdLifePending S γ q.1 (H i ⟨q.1, hp⟩) b jP ∧
        q.2 = (lifeLine S γ q.1 (H i ⟨q.1, hp⟩).1).val) :
    hitCount l (γ jz).1 =
      (Finset.univ.filter fun p : primeBand S.x (F.a i) =>
        pdLifePending S γ p.1 (H i p) b jP ∧ lifeHit S γ p.1 (H i p).1 jz).card := by
  unfold hitCount hitIndices
  refine card_filter_get_eq (s := primeBand S.x (F.a i)) _ hnd
    (fun q => particleHits q (γ jz).1) _ (dR := _) (dC := _) ?_ ?_
  · intro r hr
    obtain ⟨hp, hpend, hanc⟩ := (hmem _).mp (List.get_mem _ _)
    refine ⟨hp, hpend, ?_⟩
    unfold particleHits at hr
    unfold lifeHit
    apply Fin.ext
    rw [← hr, hanc]
  · intro p hp
    obtain ⟨hpend, hhit⟩ := hp
    have hin : ((p.1, (lifeLine S γ p.1 (H i p).1).val) : Particle) ∈ l :=
      (hmem _).mpr ⟨p.2, hpend, rfl⟩
    obtain ⟨r, hr⟩ := List.mem_iff_get.mp hin
    refine ⟨r, by rw [hr], ?_⟩
    unfold particleHits
    rw [hr]
    exact congrArg Fin.val hhit.symm

theorem not_pending_of_active {K : ℕ} (S : PDScale) (γ : EnvPath S.x K) (p : ℕ)
    (e : PrimeLife S γ p) (b : Bool) (j : Fin (pathLength S.x + 1))
    (hj : IsActiveAt γ p j) : ¬ pdLifePending S γ p e b j := by
  have hA : (pdLifeActive S γ p).Nonempty := ⟨j, by simp [pdLifeActive, hj]⟩
  simp only [pdLifePending, hA, ↓reduceDIte]
  exact fun h => h.1 hj

theorem lifeLine_of_active {K : ℕ} (S : PDScale) (γ : EnvPath S.x K) (p : ℕ)
    (e : PrimeLife S γ p) (j : Fin (pathLength S.x + 1))
    (hj : IsActiveAt γ p j) : lifeLine S γ p e.1 = projLine p (γ j).1 := by
  have hA : (pdLifeActive S γ p).Nonempty := ⟨j, by simp [pdLifeActive, hj]⟩
  simp only [lifeLine, hA, ↓reduceDIte]
  exact ((life_active_facts S γ p e hA).2.2.2 j hj).symm

/-- Across an edge, a prime inactive at both ends keeps its pending status. -/
theorem pending_edge_iff {K : ℕ} (S : PDScale) (γ : EnvPath S.x K) (p : ℕ)
    (e : PrimeLife S γ p) (j : Fin (pathLength S.x))
    (hj : ¬ IsActiveAt γ p j.castSucc) (hj1 : ¬ IsActiveAt γ p j.succ) :
    pdLifePending S γ p e false j.succ ↔ pdLifePending S γ p e true j.castSucc := by
  by_cases hA : (pdLifeActive S γ p).Nonempty
  · obtain ⟨-, hB, hC, -⟩ := life_active_facts S γ p e hA
    have hαact : IsActiveAt γ p ((pdLifeActive S γ p).min' hA) :=
      (Finset.mem_filter.mp (Finset.min'_mem _ hA)).2
    have hωact : IsActiveAt γ p ((pdLifeActive S γ p).max' hA) :=
      (Finset.mem_filter.mp (Finset.max'_mem _ hA)).2
    have hα1 : ((pdLifeActive S γ p).min' hA).val ≠ j.val + 1 := by
      intro h; apply hj1
      have : (pdLifeActive S γ p).min' hA = j.succ := Fin.ext (by simp [h])
      rwa [← this]
    have hω0 : ((pdLifeActive S γ p).max' hA).val ≠ j.val := by
      intro h; apply hj
      have : (pdLifeActive S γ p).max' hA = j.castSucc := Fin.ext (by simp [h])
      rwa [← this]
    have hαω := Finset.min'_le_max' _ hA
    simp only [pdLifePending, hA, ↓reduceDIte, hj, hj1, not_false_eq_true, true_and]
    rcases e with ⟨⟨_ | a, _ | c⟩, he⟩ <;>
      split_ifs <;>
      simp only [Fin.lt_def, Fin.le_def, Fin.ext_iff, Fin.val_succ, Fin.coe_castSucc, not_lt,
        Bool.false_eq_true, ↓reduceIte, true_and, false_and, true_iff, false_iff, and_true,
        and_false, or_false, false_or, iff_true, iff_false, not_false_eq_true,
        Option.some.injEq, reduceCtorEq, imp_false, forall_eq'] at * <;>
      (first | omega | simp)
  · simp only [pdLifePending, hA, ↓reduceDIte]
    rcases life_inactive_facts S γ p e hA with h | ⟨a, c, h, hac, -⟩
    · simp [h]
    · simp only [h, Bool.false_eq_true, ↓reduceIte]
      simp only [Fin.lt_def, Fin.le_def, Fin.val_succ, Fin.coe_castSucc]
      omega

/-- A prime pending after the ghost of visit `j` is logged by then. -/
theorem logged_of_pending_true {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (H : PDLifeAssignment F S γ) (i : Fin K) (p : primeBand S.x (F.a i))
    (j : Fin (pathLength S.x + 1)) (h : pdLifePending S γ p.1 (H i p) true j) :
    lifeBornBefore F S γ H p.1 j ∨ ∃ i', lifeBornAt F S γ H i' p.1 j := by
  by_cases hA : (pdLifeActive S γ p.1).Nonempty
  · have hαact : IsActiveAt γ p.1 ((pdLifeActive S γ p.1).min' hA) :=
      (Finset.mem_filter.mp (Finset.min'_mem _ hA)).2
    simp only [pdLifePending, hA, ↓reduceDIte] at h
    obtain ⟨-, h⟩ := h
    by_cases h1 : j < (pdLifeActive S γ p.1).min' hA
    · rw [if_pos h1] at h
      cases ha : (H i p).1.1 with
      | none => rw [ha] at h; exact h.elim
      | some a =>
        rw [ha] at h
        simp only [↓reduceIte] at h
        rcases lt_or_eq_of_le h with h | h
        · exact Or.inl (Or.inr ⟨i, a, h, p.2, ha⟩)
        · subst h; exact Or.inr ⟨i, p.2, ha⟩
    · exact Or.inl (Or.inl ⟨_, not_lt.mp h1, hαact⟩)
  · simp only [pdLifePending, hA, ↓reduceDIte] at h
    rcases life_inactive_facts S γ p.1 (H i p) hA with he | ⟨a, c, he, -, -⟩
    · rw [he] at h; exact h.elim
    · rw [he] at h
      simp only [↓reduceIte] at h
      have ha : (H i p).1.1 = some a := by rw [he]
      rcases lt_or_eq_of_le h.1 with h' | h'
      · exact Or.inl (Or.inr ⟨i, a, h', p.2, ha⟩)
      · subst h'; exact Or.inr ⟨i, p.2, ha⟩

/-- An entering prime that is already logged is pending after the previous ghost. -/
theorem pending_of_entering_logged {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (H : PDLifeAssignment F S γ)
    (hBands : ∀ i i' : Fin K, i ≠ i' →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a i')))
    (i : Fin K) (p : primeBand S.x (F.a i)) (j : Fin (pathLength S.x))
    (h1 : IsActiveAt γ p.1 j.succ) (h0 : ¬ IsActiveAt γ p.1 j.castSucc)
    (hlog : lifeBornBefore F S γ H p.1 j.castSucc ∨
      ∃ i', lifeBornAt F S γ H i' p.1 j.castSucc) :
    pdLifePending S γ p.1 (H i p) true j.castSucc := by
  have hA : (pdLifeActive S γ p.1).Nonempty := ⟨j.succ, by simp [pdLifeActive, h1]⟩
  obtain ⟨hAJ, hB, -, -⟩ := life_active_facts S γ p.1 (H i p) hA
  have hα := (hAJ _ h1).1
  have hbirth : ∀ i' a, lifeBornAt F S γ H i' p.1 a → (H i p).1.1 = some a := by
    rintro i' a ⟨hp', hb⟩
    by_cases hii : i' = i
    · subst hii; exact hb
    · exact absurd p.2 (Finset.disjoint_left.mp (hBands i' i hii) hp')
  simp only [pdLifePending, hA, ↓reduceDIte, h0, not_false_eq_true, true_and]
  by_cases hlt : j.castSucc < (pdLifeActive S γ p.1).min' hA
  · rw [if_pos hlt]
    rcases hlog with (⟨j', hj', hact⟩ | ⟨i', a, ha, hb⟩) | ⟨i', hb⟩
    · exact absurd (lt_of_le_of_lt hj' hlt) (not_lt.mpr (hAJ _ hact).1)
    · rw [hbirth i' a hb]; simp only [↓reduceIte]; exact le_of_lt ha
    · rw [hbirth i' _ hb]; simp
  · rw [if_neg hlt]
    have hle : j.castSucc ≤ (pdLifeActive S γ p.1).max' hA := by
      have := (hAJ _ h1).2
      simp only [Fin.le_def, Fin.val_succ, Fin.coe_castSucc] at this ⊢
      omega
    rw [if_neg (not_lt.mpr hle)]
    trivial

end

end ArtinPrimitiveRoots.Proofs.pd_birth_opus
