import ArtinPrimitiveRoots.Proofs.pd_life_b.GuidedLocalCharge
import ArtinPrimitiveRoots.Proofs.pd_life_b.MemoryPrimeHits

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_birth_opus

open Classical
open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
open ArtinPrimitiveRoots.Proofs.pd_life_b

noncomputable section

/-- The ghost choice prescribed by the fixed lifespan assignment. -/
def guidedGhostChoice {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (H : PDLifeAssignment F S γ) (j : Fin (pathLength S.x + 1))
    (σ : LogPoint S.x K) : GhostTraceChoice F S σ :=
  (fun i => Finset.univ.filter (fun r =>
      lifeDeletedAt F S γ H i ((σ.1.2.2 i).get r).1 j),
   fun i => ⟨(primeBand S.x (F.a i)).filter (fun p => lifeBornAt F S γ H i p j),
     Finset.mem_powerset.mpr (Finset.filter_subset _ _)⟩)

theorem ghostGuided_iff {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (H : PDLifeAssignment F S γ) (j : Fin (pathLength S.x + 1))
    (σ : LogPoint S.x K) (g : GhostTraceChoice F S σ) :
    GhostGuided F S γ H j σ g ↔ g = guidedGhostChoice F S γ H j σ := by
  constructor
  · intro h
    apply Prod.ext
    · exact funext fun i => (h i).1
    · exact funext fun i => Subtype.ext (h i).2
  · rintro rfl
    intro i
    exact ⟨rfl, rfl⟩

/-- A valid deletion endpoint is a pending hit before the ghost. -/
theorem life_delete_pending_hit {K : ℕ} (S : PDScale) (γ : EnvPath S.x K)
    (p : ℕ) (e : PrimeLife S γ p) (j : Fin (pathLength S.x + 1))
    (hd : e.1.2 = some j) :
    pdLifePending S γ p e false j ∧ lifeHit S γ p e.1 j := by
  have hv : pdLifeEndpointValid S γ p e.1 := (Finset.mem_filter.mp e.2).2
  by_cases hA : (pdLifeActive S γ p).Nonempty
  · have hdel : (pdLifeActive S γ p).max' hA < j ∧
        projLine p (γ j).1 = projLine p (γ ((pdLifeActive S γ p).min' hA)).1 := by
      simp only [pdLifeEndpointValid, hA, ↓reduceDIte, hd] at hv
      exact hv.2.2
    have hi : ¬ IsActiveAt γ p j := by
      intro hj
      have hm : j ∈ pdLifeActive S γ p := by simp [pdLifeActive, hj]
      have hle := Finset.le_max' (pdLifeActive S γ p) j hm
      exact (not_lt_of_ge hle) hdel.1
    constructor
    · exact (pd_life_b_pending_suffix_active S γ p e hA j j hd hdel.1 hi).2.mpr le_rfl
    · simpa [lifeHit, lifeLine, hA] using hdel.2
  · cases ha : e.1.1 with
    | none =>
      have he : e.1 = (none, some j) := Prod.ext ha hd
      simp [pdLifeEndpointValid, hA, he] at hv
    | some a =>
      have he : e.1 = (some a, some j) := Prod.ext ha hd
      have hac : a < j ∧ projLine p (γ j).1 = projLine p (γ a).1 := by
        simpa [pdLifeEndpointValid, hA, he] using hv
      constructor
      · simp [pdLifePending, hA, he, hac.1]
      · simpa [lifeHit, lifeLine, hA, ha] using hac.2

/-- Counting memory indices by their primes: a Nodup-by-prime memory list is in bijection with
the band primes it carries. -/
theorem card_filter_get_eq {s : Finset ℕ} (l : List Particle) (hnd : (l.map Prod.fst).Nodup)
    (R : Particle → Prop) (C : s → Prop)
    {dR : DecidablePred fun r : Fin l.length => R (l.get r)} {dC : DecidablePred C}
    (h1 : ∀ r : Fin l.length, R (l.get r) → ∃ hp : (l.get r).1 ∈ s, C ⟨_, hp⟩)
    (h2 : ∀ p : s, C p → ∃ r : Fin l.length, (l.get r).1 = p.1 ∧ R (l.get r)) :
    (Finset.univ.filter fun r : Fin l.length => R (l.get r)).card =
      (Finset.univ.filter C).card := by
  apply Finset.card_bij (fun r hr => (⟨(l.get r).1,
      (h1 r (Finset.mem_filter.mp hr).2).1⟩ : s))
  · intro r hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (h1 r (Finset.mem_filter.mp hr).2).2⟩
  · intro r hr r' hr' h
    have h' : (l.map Prod.fst).get ⟨r.val, by simp⟩ =
        (l.map Prod.fst).get ⟨r'.val, by simp⟩ := by
      simpa using congrArg Subtype.val h
    exact Fin.ext (by simpa using (hnd.get_inj_iff).mp h')
  · intro p hp
    obtain ⟨r, hr, hR⟩ := h2 p (Finset.mem_filter.mp hp).2
    exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hR⟩, Subtype.ext hr⟩

theorem prod_ite_one_pow {α : Type*} [Fintype α] (c : α → Prop) [DecidablePred c]
    (X : ℝ) :
    (∏ a : α, if c a then X else 1) = X ^ (Finset.univ.filter c).card := by
  rw [← Finset.prod_filter, Finset.prod_const]

/-- The local ghost factors of one group, collected into powers. -/
theorem ghost_group_prod {α : Type*} [Fintype α] (P Q B : α → Prop)
    {dP : DecidablePred P} {dQ : DecidablePred Q} {dB : DecidablePred B}
    (X Y Z : ℝ) (ν : α → ℝ) :
    (∏ a, (if P a then (if Q a then X else Y) else 1) * (if B a then Z * ν a else 1)) =
      X ^ (Finset.univ.filter fun a => P a ∧ Q a).card *
        Y ^ ((Finset.univ.filter P).card - (Finset.univ.filter fun a => P a ∧ Q a).card) *
        Z ^ (Finset.univ.filter B).card * ∏ a ∈ Finset.univ.filter B, ν a := by
  have hsplit : ∀ a, (if P a then (if Q a then X else Y) else 1) * (if B a then Z * ν a else 1) =
      ((if P a ∧ Q a then X else 1) * (if P a ∧ ¬ Q a then Y else 1)) *
        ((if B a then Z else 1) * (if B a then ν a else 1)) := by
    intro a
    by_cases hP : P a <;> by_cases hQ : Q a <;> by_cases hB : B a <;> simp [hP, hQ, hB]
  rw [Finset.prod_congr rfl (fun a _ => hsplit a), Finset.prod_mul_distrib,
    Finset.prod_mul_distrib, Finset.prod_mul_distrib, prod_ite_one_pow, prod_ite_one_pow,
    prod_ite_one_pow, ← Finset.prod_filter]
  have h1 := Finset.card_filter_add_card_filter_not (s := Finset.univ.filter P) Q
  rw [Finset.filter_filter, Finset.filter_filter] at h1
  rw [← h1, Nat.add_sub_cancel_left]
  ring

/-- The guided ghost charge is the product of the local ghost factors. -/
theorem guided_ghost_charge {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ)
    (γ : EnvPath S.x K) (H : PDLifeAssignment F S γ)
    (j : Fin (pathLength S.x + 1)) (σ : LogPoint S.x K)
    (hσ : IsLifeState F S γ H j σ) :
    ghostTraceCharge F S ρ j.val σ (guidedGhostChoice F S γ H j σ) =
      ((∏ i : Fin K, ∏ p : primeBand S.x (F.a i),
        lifeGhostLocal F S ρ γ i p.1 (H i p) j : ℝ) : ℂ) := by
  obtain ⟨hpos, hnd, hmem, -, -⟩ := hσ
  have hz : σ.1.1 = (γ j).1 := congrArg Prod.fst hpos
  -- per-group counts
  have hHit (i : Fin K) :
      hitCount (σ.1.2.2 i) σ.1.1 =
        (Finset.univ.filter fun p : primeBand S.x (F.a i) =>
          pdLifePending S γ p.1 (H i p) false j ∧ lifeHit S γ p.1 (H i p).1 j).card := by
    unfold hitCount hitIndices
    refine card_filter_get_eq (s := primeBand S.x (F.a i)) _ (hnd i)
      (fun q => particleHits q σ.1.1) _ (dR := _) (dC := _) ?_ ?_
    · intro r hr
      obtain ⟨hp, hpend, hanc⟩ := (hmem i _).mp (List.get_mem _ _)
      refine ⟨hp, hpend, ?_⟩
      unfold particleHits at hr
      unfold lifeHit
      apply Fin.ext
      rw [← hz, ← hr, hanc]
    · intro p hp
      obtain ⟨hpend, hhit⟩ := hp
      have hin : ((p.1, (lifeLine S γ p.1 (H i p).1).val) : Particle) ∈ σ.1.2.2 i :=
        (hmem i _).mpr ⟨p.2, hpend, rfl⟩
      obtain ⟨r, hr⟩ := List.mem_iff_get.mp hin
      refine ⟨r, by rw [hr], ?_⟩
      unfold particleHits
      rw [hr, hz]
      exact congrArg Fin.val hhit.symm
  have hDel (i : Fin K) :
      ((guidedGhostChoice F S γ H j σ).1 i).card =
        (Finset.univ.filter fun p : primeBand S.x (F.a i) =>
          (pdLifePending S γ p.1 (H i p) false j ∧ lifeHit S γ p.1 (H i p).1 j) ∧
            (H i p).1.2 = some j).card := by
    unfold guidedGhostChoice
    refine card_filter_get_eq (s := primeBand S.x (F.a i)) _ (hnd i)
      (fun q => lifeDeletedAt F S γ H i q.1 j) _ (dR := _) (dC := _) ?_ ?_
    · intro r hr
      obtain ⟨hp, hd⟩ := hr
      exact ⟨hp, life_delete_pending_hit S γ _ _ j hd, hd⟩
    · intro p hp
      obtain ⟨⟨hpend, -⟩, hd⟩ := hp
      have hin : ((p.1, (lifeLine S γ p.1 (H i p).1).val) : Particle) ∈ σ.1.2.2 i :=
        (hmem i _).mpr ⟨p.2, hpend, rfl⟩
      obtain ⟨r, hr⟩ := List.mem_iff_get.mp hin
      exact ⟨r, by rw [hr], by rw [hr]; exact ⟨p.2, hd⟩⟩
  have hGuard : ∀ i, (guidedGhostChoice F S γ H j σ).1 i ⊆
      hitIndices (σ.1.2.2 i) σ.1.1 := by
    intro i r hr
    have hr' : lifeDeletedAt F S γ H i ((σ.1.2.2 i).get r).1 j :=
      (Finset.mem_filter.mp hr).2
    obtain ⟨hp, hd⟩ := hr'
    obtain ⟨-, hhit⟩ := life_delete_pending_hit S γ _ _ j hd
    obtain ⟨_, _, hanc⟩ := (hmem i _).mp (List.get_mem _ r)
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    unfold particleHits
    rw [hanc, hz]
    exact congrArg Fin.val hhit.symm
  have hBcard (i : Fin K) : (Finset.univ.filter fun p : primeBand S.x (F.a i) =>
        (H i p).1.1 = some j).card =
      ((guidedGhostChoice F S γ H j σ).2 i).1.card := by
    show _ = ((primeBand S.x (F.a i)).filter (fun p => lifeBornAt F S γ H i p j)).card
    rw [← Finset.card_map (Function.Embedding.subtype _)]
    congr 1
    ext p
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.subtype_apply, lifeBornAt]
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.2, q.2, hq⟩
    · rintro ⟨hp, hp', hq⟩
      exact ⟨⟨p, hp⟩, hq, rfl⟩
  have hNu (i : Fin K) : (∏ p ∈ Finset.univ.filter fun p : primeBand S.x (F.a i) =>
        (H i p).1.1 = some j, memoryNu S.x K F.a F.q_d i p.1) =
      ∏ p ∈ ((guidedGhostChoice F S γ H j σ).2 i).1, memoryNu S.x K F.a F.q_d i p := by
    show _ = ∏ p ∈ (primeBand S.x (F.a i)).filter (fun p => lifeBornAt F S γ H i p j),
      memoryNu S.x K F.a F.q_d i p
    rw [Finset.prod_filter, Finset.prod_filter,
      ← Finset.prod_coe_sort (primeBand S.x (F.a i))]
    apply Finset.prod_congr rfl
    intro p _
    have : ((H i p).1.1 = some j) ↔ lifeBornAt F S γ H i p.1 j :=
      ⟨fun h => ⟨p.2, h⟩, fun ⟨_, h⟩ => h⟩
    simp only [this]
  unfold ghostTraceCharge
  rw [if_pos hGuard]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  simp only [lifeGhostLocal]
  rw [ghost_group_prod, hHit i, hDel i, hBcard i, hNu i]

end

end ArtinPrimitiveRoots.Proofs.pd_birth_opus
