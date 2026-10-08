import ArtinPrimitiveRoots.Proofs.pd_life_b.GuidedDefs
import ArtinPrimitiveRoots.Proofs.pd_life_b.BirthCombinatorics

set_option autoImplicit false

/-! R1 of the `pd-birth-opus` route: the literal raw charge of one prime lifespan is the
product of its initial, ghost, and edge local factors. -/

namespace ArtinPrimitiveRoots.Proofs.pd_birth_opus

open Classical
open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
open ArtinPrimitiveRoots.Proofs.pd_life_b

noncomputable section

/-- Target-hit factor of one prime at a visit (contributed by the incoming edge). -/
def lifeInF {K : ℕ} (S : PDScale) (ρ : ℝ) (γ : EnvPath S.x K) (p : ℕ)
    (e : PrimeLife S γ p) (j : Fin (pathLength S.x + 1)) : ℝ :=
  if pdLifePending S γ p e false j ∧ lifeHit S γ p e.1 j then ρ else 1

/-- Source-hit factor of one prime at a visit (contributed by the outgoing edge). -/
def lifeOutF {K : ℕ} (S : PDScale) (ρ : ℝ) (γ : EnvPath S.x K) (p : ℕ)
    (e : PrimeLife S γ p) (j : Fin (pathLength S.x + 1)) : ℝ :=
  if pdLifePending S γ p e true j ∧ lifeHit S γ p e.1 j then ρ else 1

/-- The visit preceding a nonzero visit. -/
def prevVisit {x : ℝ} (j : Fin (pathLength x + 1)) : Fin (pathLength x + 1) :=
  ⟨j.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩

/-- Entry factor of one prime at a visit (contributed by the incoming edge). -/
def lifeEntF {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K) (i : Fin K) (p : ℕ)
    (e : PrimeLife S γ p) (j : Fin (pathLength S.x + 1)) : ℝ :=
  if j.val = 0 then 1 else
    if IsActiveAt γ p j ∧ ¬ IsActiveAt γ p (prevVisit j) then
      (if pdLifePending S γ p e true (prevVisit j) then (bandMass S.x (F.a i))⁻¹
        else memoryNu S.x K F.a F.q_d i p)
    else 1

/-- All factors attached to one visit. -/
def lifeVisitLocal {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (γ : EnvPath S.x K)
    (i : Fin K) (p : ℕ) (e : PrimeLife S γ p) (j : Fin (pathLength S.x + 1)) : ℝ :=
  (if j.val = 0 then lifeInitLocal F S γ i p else 1) * lifeGhostLocal F S ρ γ i p e j *
    lifeOutF S ρ γ p e j * lifeEntF F S γ i p e j * lifeInF S ρ γ p e j

private lemma mem_active {K : ℕ} (S : PDScale) (γ : EnvPath S.x K) (p : ℕ)
    (j : Fin (pathLength S.x + 1)) : j ∈ pdLifeActive S γ p ↔ IsActiveAt γ p j := by
  simp [pdLifeActive]

private lemma pending_false_of_not {K : ℕ} (S : PDScale) (γ : EnvPath S.x K) (p : ℕ)
    (e : PrimeLife S γ p) (b : Bool) (j : Fin (pathLength S.x + 1))
    (hA : (pdLifeActive S γ p).Nonempty) (hα : j < (pdLifeActive S γ p).min' hA)
    (hnone : e.1.1 = none) : ¬ pdLifePending S γ p e b j := by
  intro h
  unfold pdLifePending at h
  dsimp only at h
  rw [dif_pos hA, if_pos hα, hnone] at h
  exact h.2

private lemma pending_suffix_none {K : ℕ} (S : PDScale) (γ : EnvPath S.x K) (p : ℕ)
    (e : PrimeLife S γ p) (b : Bool) (j : Fin (pathLength S.x + 1))
    (hA : (pdLifeActive S γ p).Nonempty) (hω : (pdLifeActive S γ p).max' hA < j)
    (hnone : e.1.2 = none) : ¬ pdLifePending S γ p e b j := by
  intro h
  have hαω : (pdLifeActive S γ p).min' hA ≤ (pdLifeActive S γ p).max' hA :=
    Finset.min'_le _ _ (Finset.max'_mem _ hA)
  have hnα : ¬ j < (pdLifeActive S γ p).min' hA := by
    intro hj; exact absurd (lt_trans (lt_of_le_of_lt hαω hω) hj) (lt_irrefl _)
  unfold pdLifePending at h
  dsimp only at h
  rw [dif_pos hA, if_neg hnα, if_pos hω, hnone] at h
  exact h.2

private lemma pending_inactive_none {K : ℕ} (S : PDScale) (γ : EnvPath S.x K) (p : ℕ)
    (e : PrimeLife S γ p) (b : Bool) (j : Fin (pathLength S.x + 1))
    (hA : ¬ (pdLifeActive S γ p).Nonempty) (hnone : e.1.1 = none) :
    ¬ pdLifePending S γ p e b j := by
  intro h
  unfold pdLifePending at h
  dsimp only at h
  rw [dif_neg hA] at h
  obtain ⟨⟨oa, oc⟩, he⟩ := e
  simp only at hnone
  subst hnone
  exact h

theorem pending_true_last {K : ℕ} (S : PDScale) (γ : EnvPath S.x K) (p : ℕ)
    (e : PrimeLife S γ p) : ¬ pdLifePending S γ p e true (Fin.last (pathLength S.x)) := by
  intro h
  by_cases hA : (pdLifeActive S γ p).Nonempty
  · by_cases hact : IsActiveAt γ p (Fin.last (pathLength S.x))
    · exact (pd_life_b_not_pending_at_active_visit S γ p e _ hact).1 h
    · have hωle : (pdLifeActive S γ p).max' hA ≤ Fin.last (pathLength S.x) := Fin.le_last _
      have hωne : (pdLifeActive S γ p).max' hA ≠ Fin.last (pathLength S.x) := by
        intro heq
        apply hact
        rw [← mem_active, ← heq]
        exact Finset.max'_mem _ hA
      have hω : (pdLifeActive S γ p).max' hA < Fin.last (pathLength S.x) :=
        lt_of_le_of_ne hωle hωne
      cases hc : e.1.2 with
      | none => exact pending_suffix_none S γ p e true _ hA hω hc h
      | some c =>
          have := (pd_life_b_pending_suffix_active S γ p e hA c _ hc hω hact).1.mp h
          exact absurd (Fin.le_last c) (not_le.mpr this)
  · cases ha : e.1.1 with
    | none => exact pending_inactive_none S γ p e true _ hA ha h
    | some a =>
        cases hc : e.1.2 with
        | none =>
            unfold pdLifePending at h
            dsimp only at h
            rw [dif_neg hA] at h
            obtain ⟨⟨oa, oc⟩, he⟩ := e
            simp only at ha hc
            subst ha hc
            exact h
        | some c =>
            have hlife : e.1 = (some a, some c) := Prod.ext ha hc
            have := (pd_life_b_pending_ghostOnly S γ p e hA a c hlife _).1.mp h
            exact absurd (Fin.le_last c) (not_le.mpr this.2)

private lemma pending_false_zero {K : ℕ} (S : PDScale) (γ : EnvPath S.x K) (p : ℕ)
    (e : PrimeLife S γ p) : ¬ pdLifePending S γ p e false 0 := by
  intro h
  by_cases hA : (pdLifeActive S γ p).Nonempty
  · by_cases hact : IsActiveAt γ p 0
    · exact (pd_life_b_not_pending_at_active_visit S γ p e _ hact).2 h
    · have hαne : (pdLifeActive S γ p).min' hA ≠ 0 := by
        intro heq
        apply hact
        rw [← mem_active, ← heq]
        exact Finset.min'_mem _ hA
      have hα : (0 : Fin (pathLength S.x + 1)) < (pdLifeActive S γ p).min' hA :=
        lt_of_le_of_ne (Fin.zero_le _) (Ne.symm hαne)
      cases ha : e.1.1 with
      | none => exact pending_false_of_not S γ p e false _ hA hα ha h
      | some a =>
          have := (pd_life_b_pending_prefix_active S γ p e hA a 0 ha hα hact).2.mp h
          exact absurd (Fin.zero_le a) (not_le.mpr this)
  · cases ha : e.1.1 with
    | none => exact pending_inactive_none S γ p e false _ hA ha h
    | some a =>
        cases hc : e.1.2 with
        | none =>
            unfold pdLifePending at h
            dsimp only at h
            rw [dif_neg hA] at h
            obtain ⟨⟨oa, oc⟩, he⟩ := e
            simp only at ha hc
            subst ha hc
            exact h
        | some c =>
            have hlife : e.1 = (some a, some c) := Prod.ext ha hc
            have := (pd_life_b_pending_ghostOnly S γ p e hA a c hlife _).2.mp h
            exact absurd (Fin.zero_le a) (not_le.mpr this.1)

/-- Regroup the edge factors by visit. -/
theorem lifeLocal_regroup {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ)
    (γ : EnvPath S.x K) (i : Fin K) (p : ℕ) (e : PrimeLife S γ p) :
    lifeInitLocal F S γ i p * (∏ j, lifeGhostLocal F S ρ γ i p e j) *
        ∏ j : Fin (pathLength S.x), lifeEdgeLocal F S ρ γ i p e j =
      ∏ j, lifeVisitLocal F S ρ γ i p e j := by
  have hOut : ∏ j : Fin (pathLength S.x),
      (if pdLifePending S γ p e true j.castSucc ∧ lifeHit S γ p e.1 j.castSucc then ρ else 1) =
      ∏ j, lifeOutF S ρ γ p e j := by
    rw [Fin.prod_univ_castSucc (f := lifeOutF S ρ γ p e)]
    have hlast : lifeOutF S ρ γ p e (Fin.last (pathLength S.x)) = 1 := by
      unfold lifeOutF
      rw [if_neg (fun h => pending_true_last S γ p e h.1)]
    rw [hlast, mul_one]
    rfl
  have hIn : ∏ j : Fin (pathLength S.x),
      (if pdLifePending S γ p e false j.succ ∧ lifeHit S γ p e.1 j.succ then ρ else 1) =
      ∏ j, lifeInF S ρ γ p e j := by
    rw [Fin.prod_univ_succ (f := lifeInF S ρ γ p e)]
    have hzero : lifeInF S ρ γ p e 0 = 1 := by
      unfold lifeInF
      rw [if_neg (fun h => pending_false_zero S γ p e h.1)]
    rw [hzero, one_mul]
    rfl
  have hEnt : ∏ j : Fin (pathLength S.x),
      (if IsActiveAt γ p j.succ ∧ ¬ IsActiveAt γ p j.castSucc then
        (if pdLifePending S γ p e true j.castSucc then (bandMass S.x (F.a i))⁻¹
          else memoryNu S.x K F.a F.q_d i p)
      else 1) = ∏ j, lifeEntF F S γ i p e j := by
    rw [Fin.prod_univ_succ (f := lifeEntF F S γ i p e)]
    have hzero : lifeEntF F S γ i p e 0 = 1 := by
      have h0 : (0 : Fin (pathLength S.x + 1)).val = 0 := by simp
      unfold lifeEntF
      rw [if_pos h0]
    rw [hzero, one_mul]
    apply Finset.prod_congr rfl
    intro j _
    have hprev : prevVisit j.succ = j.castSucc := by
      apply Fin.ext
      simp [prevVisit]
    have hne : (j.succ : Fin (pathLength S.x + 1)).val ≠ 0 := by simp
    unfold lifeEntF
    rw [if_neg hne, hprev]
  have hInit : (∏ j : Fin (pathLength S.x + 1),
      (if j.val = 0 then lifeInitLocal F S γ i p else 1)) = lifeInitLocal F S γ i p := by
    rw [Fin.prod_univ_succ]
    simp
  unfold lifeVisitLocal lifeEdgeLocal
  simp only [Finset.prod_mul_distrib]
  rw [hOut, hIn, hEnt, hInit]
  ring

/-- Start of a maximal active run (the predicate counted by `pdActiveRuns`). -/
def runStart {x : ℝ} {K : ℕ} (γ : EnvPath x K) (p : ℕ) (j : Fin (pathLength x + 1)) : Prop :=
  IsActiveAt γ p j ∧ ¬ ∃ k : Fin (pathLength x + 1), k.val + 1 = j.val ∧ IsActiveAt γ p k

private lemma runStart_iff {x : ℝ} {K : ℕ} (γ : EnvPath x K) (p : ℕ)
    (j : Fin (pathLength x + 1)) :
    runStart γ p j ↔ IsActiveAt γ p j ∧ (j.val = 0 ∨ ¬ IsActiveAt γ p (prevVisit j)) := by
  unfold runStart
  constructor
  · rintro ⟨hj, hk⟩
    refine ⟨hj, ?_⟩
    by_cases h0 : j.val = 0
    · exact Or.inl h0
    · right
      intro hprev
      exact hk ⟨prevVisit j, by simp [prevVisit]; omega, hprev⟩
  · rintro ⟨hj, h⟩
    refine ⟨hj, ?_⟩
    rintro ⟨k, hk, hact⟩
    rcases h with h0 | hprev
    · omega
    · have : k = prevVisit j := by
        apply Fin.ext
        simp [prevVisit]
        omega
      exact hprev (this ▸ hact)

private lemma runs_card {K : ℕ} (S : PDScale) (γ : EnvPath S.x K) (p : ℕ) :
    pdActiveRuns S γ p = (Finset.univ.filter (runStart γ p)).card := by
  unfold pdActiveRuns
  congr 1
  ext j
  simp [runStart]

private lemma runs_pow {K : ℕ} (S : PDScale) (γ : EnvPath S.x K) (p : ℕ) (X : ℝ) :
    X ^ pdActiveRuns S γ p = ∏ j, (if runStart γ p j then X else 1) := by
  rw [← Finset.prod_filter, Finset.prod_const, runs_card]

private lemma runs_first {K : ℕ} (S : PDScale) (γ : EnvPath S.x K) (p : ℕ)
    (hA : (pdLifeActive S γ p).Nonempty) (X Y : ℝ) :
    X * Y ^ (pdActiveRuns S γ p - 1) =
      ∏ j, (if runStart γ p j then
        (if j = (pdLifeActive S γ p).min' hA then X else Y) else 1) := by
  rw [← Finset.prod_filter]
  have hmem : (pdLifeActive S γ p).min' hA ∈ Finset.univ.filter (runStart γ p) := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, (mem_active S γ p _).mp (Finset.min'_mem _ hA), ?_⟩
    rintro ⟨k, hk, hact⟩
    have hle := Finset.min'_le _ k ((mem_active S γ p k).mpr hact)
    have hle' : ((pdLifeActive S γ p).min' hA).val ≤ k.val := hle
    omega
  rw [← Finset.mul_prod_erase _ _ hmem, if_pos rfl]
  congr 1
  rw [Finset.prod_congr rfl (fun j hj => if_neg (Finset.ne_of_mem_erase hj)),
    Finset.prod_const, Finset.card_erase_of_mem hmem, runs_card]

private lemma valid_active {K : ℕ} (S : PDScale) (γ : EnvPath S.x K) (p : ℕ)
    (e : PrimeLife S γ p) (hA : (pdLifeActive S γ p).Nonempty) :
    (∀ j ∈ pdLifeActive S γ p,
        projLine p (γ j).1 = projLine p (γ ((pdLifeActive S γ p).min' hA)).1) ∧
      (∀ a, e.1.1 = some a → a < (pdLifeActive S γ p).min' hA ∧
        projLine p (γ a).1 = projLine p (γ ((pdLifeActive S γ p).min' hA)).1) ∧
      (∀ c, e.1.2 = some c → (pdLifeActive S γ p).max' hA < c ∧
        projLine p (γ c).1 = projLine p (γ ((pdLifeActive S γ p).min' hA)).1) := by
  have h := (Finset.mem_filter.mp e.2).2
  unfold pdLifeEndpointValid at h
  dsimp only at h
  rw [dif_pos hA] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, ?_, ?_⟩
  · intro a ha
    rw [ha] at h2
    exact h2
  · intro c hc
    rw [hc] at h3
    exact h3

private lemma valid_inactive {K : ℕ} (S : PDScale) (γ : EnvPath S.x K) (p : ℕ)
    (e : PrimeLife S γ p) (hA : ¬ (pdLifeActive S γ p).Nonempty) :
    e.1 = (none, none) ∨ ∃ a c, e.1 = (some a, some c) ∧ a < c ∧
      projLine p (γ c).1 = projLine p (γ a).1 := by
  obtain ⟨⟨oa, oc⟩, he⟩ := e
  have h := (Finset.mem_filter.mp he).2
  unfold pdLifeEndpointValid at h
  dsimp only at h
  rw [dif_neg hA] at h
  rcases oa with _ | a <;> rcases oc with _ | c
  · exact Or.inl rfl
  · exact h.elim
  · exact h.elim
  · exact Or.inr ⟨a, c, rfl, h⟩

/-- Visit factor of the active-lifespan charge. -/
private def activeW {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (γ : EnvPath S.x K)
    (i : Fin K) (p : ℕ) (oa oc : Option (Fin (pathLength S.x + 1)))
    (α ω : Fin (pathLength S.x + 1)) (lam : Fin (p + 1))
    (j : Fin (pathLength S.x + 1)) : ℝ :=
  (if oa = some j then
      -memoryEta S.x F.q_d j.val * bandMass S.x (F.a i) / ρ * ρ *
        memoryNu S.x K F.a F.q_d i p
    else 1) *
  (if runStart γ p j then
      (if oa = none ∧ j = α then memoryNu S.x K F.a F.q_d i p
        else (bandMass S.x (F.a i))⁻¹)
    else 1) *
  (if (∃ a, oa = some a ∧ a < j) ∧ j < α then pdRawSurvival F S ρ γ p lam j else 1) *
  (if α < j ∧ j < ω ∧ j ∉ pdLifeActive S γ p then pdRawSurvival F S ρ γ p lam j else 1) *
  (if oc = some j then -memoryEta S.x F.q_d j.val / ρ * ρ else 1) *
  (if ω < j ∧ ∃ c, oc = some c ∧ j < c then pdRawSurvival F S ρ γ p lam j else 1)

private lemma rawCharge_active_eq_W {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ)
    (γ : EnvPath S.x K) (i : Fin K) (p : ℕ) (e : PrimeLife S γ p)
    (hA : (pdLifeActive S γ p).Nonempty) :
    pdRawPrimeLifeCharge F S ρ γ i p e =
      ∏ j, activeW F S ρ γ i p e.1.1 e.1.2 ((pdLifeActive S γ p).min' hA)
        ((pdLifeActive S γ p).max' hA) (projLine p (γ ((pdLifeActive S γ p).min' hA)).1) j := by
  unfold pdRawPrimeLifeCharge activeW
  dsimp only
  rw [dif_pos hA]
  simp only [Finset.prod_mul_distrib]
  obtain ⟨⟨oa, oc⟩, he⟩ := e
  dsimp only
  rcases oa with _ | a <;> rcases oc with _ | c <;>
    simp only [reduceCtorEq, Option.some.injEq, eq_self_iff_true, false_and, and_false,
      true_and, exists_false,
      exists_eq_left', eq_self_iff_true, ↓reduceIte, reduceIte, Finset.prod_const_one, Finset.prod_ite_eq,
      Finset.mem_univ, Finset.prod_filter, one_mul, mul_one]
  all_goals first | rw [runs_first S γ p hA] | rw [runs_pow S γ p]
  all_goals ring

private lemma entry_eq {K : ℕ} (F : PDFix K) (S : PDScale)
    (γ : EnvPath S.x K) (i : Fin K) (p : ℕ) (e : PrimeLife S γ p)
    (hA : (pdLifeActive S γ p).Nonempty) (j : Fin (pathLength S.x + 1)) :
    (if j.val = 0 then lifeInitLocal F S γ i p else 1) * lifeEntF F S γ i p e j =
      (if runStart γ p j then
        (if e.1.1 = none ∧ j = (pdLifeActive S γ p).min' hA then memoryNu S.x K F.a F.q_d i p
          else (bandMass S.x (F.a i))⁻¹)
      else 1) := by
  have hval := valid_active S γ p e hA
  have hαmem := Finset.min'_mem _ hA
  by_cases h0 : j.val = 0
  · have hj0 : j = 0 := Fin.ext h0
    subst hj0
    have hent : lifeEntF F S γ i p e 0 = 1 := by
      unfold lifeEntF
      rw [if_pos h0]
    rw [if_pos h0, hent, mul_one]
    unfold lifeInitLocal
    by_cases hact : IsActiveAt γ p 0
    · have hrun : runStart γ p 0 := (runStart_iff γ p 0).mpr ⟨hact, Or.inl h0⟩
      have hα0 : (pdLifeActive S γ p).min' hA = 0 := by
        apply le_antisymm _ (Fin.zero_le _)
        exact Finset.min'_le _ _ ((mem_active S γ p 0).mpr hact)
      have hnone : e.1.1 = none := by
        cases ha : e.1.1 with
        | none => rfl
        | some a =>
            have := (hval.2.1 a ha).1
            rw [hα0] at this
            exact absurd this (not_lt.mpr (Fin.zero_le a))
      rw [if_pos hact, if_pos hrun, if_pos ⟨hnone, hα0.symm⟩]
    · have hrun : ¬ runStart γ p 0 := fun h => hact ((runStart_iff γ p 0).mp h).1
      rw [if_neg hact, if_neg hrun]
  · rw [if_neg h0, one_mul]
    unfold lifeEntF
    rw [if_neg h0]
    by_cases hstart : IsActiveAt γ p j ∧ ¬ IsActiveAt γ p (prevVisit j)
    · have hrun : runStart γ p j := (runStart_iff γ p j).mpr ⟨hstart.1, Or.inr hstart.2⟩
      rw [if_pos hstart, if_pos hrun]
      have hprevlt : prevVisit j < j := by
        rw [Fin.lt_iff_val_lt_val]; show j.val - 1 < j.val; omega
      have hαj : (pdLifeActive S γ p).min' hA ≤ j :=
        Finset.min'_le _ _ ((mem_active S γ p j).mpr hstart.1)
      by_cases hjα : j = (pdLifeActive S γ p).min' hA
      · have hpα : prevVisit j < (pdLifeActive S γ p).min' hA := hjα ▸ hprevlt
        cases ha : e.1.1 with
        | none =>
            rw [if_neg (pending_false_of_not S γ p e true _ hA hpα ha), if_pos ⟨rfl, hjα⟩]
        | some a =>
            have haα := (hval.2.1 a ha).1
            have hle : a ≤ prevVisit j := by
              rw [Fin.le_iff_val_le_val]
              rw [← hjα, Fin.lt_iff_val_lt_val] at haα
              show a.val ≤ j.val - 1
              omega
            have hpend := (pd_life_b_pending_prefix_active S γ p e hA a _ ha hpα hstart.2).1.mpr hle
            have hne : ¬ ((some a : Option (Fin (pathLength S.x + 1))) = none ∧
                j = (pdLifeActive S γ p).min' hA) := fun h => by cases h.1
            rw [if_pos hpend, if_neg hne]
      · have hαp : (pdLifeActive S γ p).min' hA ≤ prevVisit j := by
          have hlt : (pdLifeActive S γ p).min' hA < j := lt_of_le_of_ne hαj (Ne.symm hjα)
          rw [Fin.le_iff_val_le_val]
          rw [Fin.lt_iff_val_lt_val] at hlt
          show ((pdLifeActive S γ p).min' hA).val ≤ j.val - 1
          omega
        have hpω : prevVisit j ≤ (pdLifeActive S γ p).max' hA :=
          le_trans hprevlt.le (Finset.le_max' _ _ ((mem_active S γ p j).mpr hstart.1))
        have hpend := (pd_life_b_pending_in_active_span S γ p e hA _ hαp hpω hstart.2).1
        have hne : ¬ (e.1.1 = none ∧ j = (pdLifeActive S γ p).min' hA) := fun h => hjα h.2
        rw [if_pos hpend, if_neg hne]
    · have hrun : ¬ runStart γ p j := by
        intro h
        rcases (runStart_iff γ p j).mp h with ⟨hact, h0' | hprev⟩
        · exact h0 h0'
        · exact hstart ⟨hact, hprev⟩
      rw [if_neg hstart, if_neg hrun]

private lemma rest_eq_active {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ)
    (γ : EnvPath S.x K) (i : Fin K) (p : ℕ) (e : PrimeLife S γ p)
    (hA : (pdLifeActive S γ p).Nonempty) (α ω : Fin (pathLength S.x + 1))
    (hαdef : (pdLifeActive S γ p).min' hA = α) (hωdef : (pdLifeActive S γ p).max' hA = ω)
    (j : Fin (pathLength S.x + 1)) :
    lifeGhostLocal F S ρ γ i p e j * lifeOutF S ρ γ p e j * lifeInF S ρ γ p e j =
      (if e.1.1 = some j then
          -memoryEta S.x F.q_d j.val * bandMass S.x (F.a i) / ρ * ρ *
            memoryNu S.x K F.a F.q_d i p
        else 1) *
      (if (∃ a, e.1.1 = some a ∧ a < j) ∧ j < α then
          pdRawSurvival F S ρ γ p (projLine p (γ α).1) j else 1) *
      (if α < j ∧ j < ω ∧ j ∉ pdLifeActive S γ p then
          pdRawSurvival F S ρ γ p (projLine p (γ α).1) j else 1) *
      (if e.1.2 = some j then -memoryEta S.x F.q_d j.val / ρ * ρ else 1) *
      (if ω < j ∧ ∃ c, e.1.2 = some c ∧ j < c then
          pdRawSurvival F S ρ γ p (projLine p (γ α).1) j else 1) := by
  have hval := valid_active S γ p e hA
  rw [hαdef, hωdef] at hval
  have hline : lifeLine S γ p e.1 = projLine p (γ α).1 := by
    unfold lifeLine
    rw [dif_pos hA, hαdef]
  have hαω : α ≤ ω := by
    rw [← hαdef, ← hωdef]
    exact Finset.min'_le _ _ (Finset.max'_mem _ hA)
  have hαmem : α ∈ pdLifeActive S γ p := hαdef ▸ Finset.min'_mem _ hA
  have hωmem : ω ∈ pdLifeActive S γ p := hωdef ▸ Finset.max'_mem _ hA
  unfold lifeGhostLocal lifeOutF lifeInF lifeHit pdRawSurvival
  rw [hline]
  by_cases hact : IsActiveAt γ p j
  · obtain ⟨hPA, hPB⟩ := pd_life_b_not_pending_at_active_visit S γ p e j hact
    have hmem : j ∈ pdLifeActive S γ p := (mem_active S γ p j).mpr hact
    have hαj : α ≤ j := hαdef ▸ Finset.min'_le _ _ hmem
    have hjω : j ≤ ω := hωdef ▸ Finset.le_max' _ _ hmem
    have hoa : ¬ e.1.1 = some j := fun h => absurd (hval.2.1 j h).1 (not_lt.mpr hαj)
    have hoc : ¬ e.1.2 = some j := fun h => absurd (hval.2.2 j h).1 (not_lt.mpr hjω)
    have hpre : ¬ ((∃ a, e.1.1 = some a ∧ a < j) ∧ j < α) :=
      fun h => absurd h.2 (not_lt.mpr hαj)
    have hgap : ¬ (α < j ∧ j < ω ∧ j ∉ pdLifeActive S γ p) := fun h => h.2.2 hmem
    have hsuf : ¬ (ω < j ∧ ∃ c, e.1.2 = some c ∧ j < c) :=
      fun h => absurd h.1 (not_lt.mpr hjω)
    simp only [hPA, hPB, hoa, hoc, hpre, hgap, hsuf, false_and, eq_self_iff_true, ↓reduceIte, reduceIte, mul_one]
  · rcases lt_or_ge j α with hjα | hαj
    · have hjα' : j < (pdLifeActive S γ p).min' hA := hαdef ▸ hjα
      have hoc : ¬ e.1.2 = some j := fun h =>
        absurd (lt_trans (lt_of_le_of_lt hαω (hval.2.2 j h).1) hjα) (lt_irrefl _)
      have hgap : ¬ (α < j ∧ j < ω ∧ j ∉ pdLifeActive S γ p) :=
        fun h => absurd (lt_trans h.1 hjα) (lt_irrefl _)
      have hsuf : ¬ (ω < j ∧ ∃ c, e.1.2 = some c ∧ j < c) :=
        fun h => absurd (lt_trans (lt_of_le_of_lt hαω h.1) hjα) (lt_irrefl _)
      cases hoa : e.1.1 with
      | none =>
          have hPA := pending_false_of_not S γ p e true j hA hjα' hoa
          have hPB := pending_false_of_not S γ p e false j hA hjα' hoa
          have hbr : ¬ ((none : Option (Fin (pathLength S.x + 1))) = some j) := by simp
          have hpre : ¬ ((∃ a, (none : Option (Fin (pathLength S.x + 1))) = some a ∧ a < j) ∧
              j < α) := by simp
          simp only [hPA, hPB, hoc, hgap, hsuf, hbr, hpre, false_and, eq_self_iff_true, ↓reduceIte, reduceIte, mul_one]
      | some a =>
          have hpend := pd_life_b_pending_prefix_active S γ p e hA a j hoa hjα' hact
          have hlinea : projLine p (γ a).1 = projLine p (γ α).1 := (hval.2.1 a hoa).2
          rcases lt_trichotomy j a with hja | hja | hja
          · have hPA : ¬ pdLifePending S γ p e true j :=
              fun h => absurd (hpend.1.mp h) (not_le.mpr hja)
            have hPB : ¬ pdLifePending S γ p e false j :=
              fun h => absurd (hpend.2.mp h) (not_lt.mpr hja.le)
            have hbr : ¬ (some a = some j) := fun h => by
              cases h; exact absurd hja (lt_irrefl _)
            have hpre : ¬ ((∃ a', some a = some a' ∧ a' < j) ∧ j < α) := by
              rintro ⟨⟨a', ha', ha'j⟩, -⟩
              cases ha'
              exact absurd (lt_trans ha'j hja) (lt_irrefl _)
            simp only [hPA, hPB, hbr, hoc, hgap, hsuf, hpre, false_and, eq_self_iff_true, ↓reduceIte, reduceIte, mul_one]
          · have hPA : pdLifePending S γ p e true j := hpend.1.mpr (le_of_eq hja.symm)
            have hPB : ¬ pdLifePending S γ p e false j :=
              fun h => absurd (hpend.2.mp h) (not_lt.mpr (le_of_eq hja))
            have hbr : some a = some j := by rw [hja]
            have hpre : ¬ ((∃ a', some a = some a' ∧ a' < j) ∧ j < α) := by
              rintro ⟨⟨a', ha', ha'j⟩, -⟩
              cases ha'
              rw [hja] at ha'j
              exact absurd ha'j (lt_irrefl _)
            have hhit : projLine p (γ j).1 = projLine p (γ α).1 := hja ▸ hlinea
            simp only [hPA, hPB, eq_true hbr, hoc, hgap, hsuf, hpre, eq_true hhit, false_and, and_self,
              eq_self_iff_true, ↓reduceIte, reduceIte, mul_one, one_mul]
            ring
          · have hPA : pdLifePending S γ p e true j := hpend.1.mpr hja.le
            have hPB : pdLifePending S γ p e false j := hpend.2.mpr hja
            have hbr : ¬ (some a = some j) := fun h => by
              cases h; exact absurd hja (lt_irrefl _)
            have hpre : (∃ a', some a = some a' ∧ a' < j) ∧ j < α := ⟨⟨a, rfl, hja⟩, hjα⟩
            simp only [hPA, hPB, hbr, hoc, hgap, hsuf, hpre, true_and, and_self, false_and,
              eq_self_iff_true, ↓reduceIte, reduceIte, mul_one, one_mul]
            split_ifs <;> first | ring1 | contradiction
    · rcases le_or_gt j ω with hjω | hωj
      · have hjne : j ∉ pdLifeActive S γ p := fun h => hact ((mem_active S γ p j).mp h)
        have hαj' : α < j := lt_of_le_of_ne hαj (fun h => hjne (h ▸ hαmem))
        have hjω' : j < ω := lt_of_le_of_ne hjω (fun h => hjne (h.symm ▸ hωmem))
        obtain ⟨hPA, hPB⟩ := pd_life_b_pending_in_active_span S γ p e hA j
          (hαdef ▸ hαj) (hωdef ▸ hjω) hact
        have hoa : ¬ e.1.1 = some j := fun h =>
          absurd (lt_trans (hval.2.1 j h).1 hαj') (lt_irrefl _)
        have hoc : ¬ e.1.2 = some j := fun h =>
          absurd (lt_trans (hval.2.2 j h).1 hjω') (lt_irrefl _)
        have hpre : ¬ ((∃ a, e.1.1 = some a ∧ a < j) ∧ j < α) :=
          fun h => absurd h.2 (not_lt.mpr hαj)
        have hgap : (α < j ∧ j < ω ∧ j ∉ pdLifeActive S γ p) := ⟨hαj', hjω', hjne⟩
        have hsuf : ¬ (ω < j ∧ ∃ c, e.1.2 = some c ∧ j < c) :=
          fun h => absurd h.1 (not_lt.mpr hjω)
        simp only [hPA, hPB, hoa, hoc, hpre, hgap, hsuf, true_and, and_self, false_and,
          eq_self_iff_true, ↓reduceIte, reduceIte, mul_one, one_mul]
        split_ifs <;> first | ring1 | contradiction
      · have hoa : ¬ e.1.1 = some j := fun h =>
          absurd (lt_trans (lt_of_lt_of_le (hval.2.1 j h).1 hαω) hωj) (lt_irrefl _)
        have hpre : ¬ ((∃ a, e.1.1 = some a ∧ a < j) ∧ j < α) :=
          fun h => absurd h.2 (not_lt.mpr hαj)
        have hgap : ¬ (α < j ∧ j < ω ∧ j ∉ pdLifeActive S γ p) :=
          fun h => absurd (lt_trans h.2.1 hωj) (lt_irrefl _)
        have hωj' : (pdLifeActive S γ p).max' hA < j := hωdef ▸ hωj
        cases hoc : e.1.2 with
        | none =>
            have hPA := pending_suffix_none S γ p e true j hA hωj' hoc
            have hPB := pending_suffix_none S γ p e false j hA hωj' hoc
            have hcp : ¬ ((none : Option (Fin (pathLength S.x + 1))) = some j) := by simp
            have hsuf : ¬ (ω < j ∧ ∃ c, (none : Option (Fin (pathLength S.x + 1))) = some c ∧
                j < c) := by simp
            simp only [hPA, hPB, hoa, hpre, hgap, hcp, hsuf, false_and, eq_self_iff_true, ↓reduceIte, reduceIte, mul_one]
        | some c =>
            have hpend := pd_life_b_pending_suffix_active S γ p e hA c j hoc hωj' hact
            have hlinec : projLine p (γ c).1 = projLine p (γ α).1 := (hval.2.2 c hoc).2
            rcases lt_trichotomy j c with hjc | hjc | hjc
            · have hPA : pdLifePending S γ p e true j := hpend.1.mpr hjc
              have hPB : pdLifePending S γ p e false j := hpend.2.mpr hjc.le
              have hcp : ¬ (some c = some j) := fun h => by
                cases h; exact absurd hjc (lt_irrefl _)
              have hsuf : ω < j ∧ ∃ c', some c = some c' ∧ j < c' := ⟨hωj, c, rfl, hjc⟩
              simp only [hPA, hPB, hoa, hpre, hgap, hcp, hsuf, true_and, and_self,
                false_and, eq_self_iff_true, ↓reduceIte, reduceIte, mul_one, one_mul]
              split_ifs <;> first | ring1 | contradiction
            · have hPA : ¬ pdLifePending S γ p e true j :=
                fun h => absurd (hpend.1.mp h) (not_lt.mpr (le_of_eq hjc.symm))
              have hPB : pdLifePending S γ p e false j := hpend.2.mpr (le_of_eq hjc)
              have hcp : some c = some j := by rw [hjc]
              have hsuf : ¬ (ω < j ∧ ∃ c', some c = some c' ∧ j < c') := by
                rintro ⟨-, c', hc', hjc'⟩
                cases hc'
                rw [hjc] at hjc'
                exact absurd hjc' (lt_irrefl _)
              have hhit : projLine p (γ j).1 = projLine p (γ α).1 := hjc ▸ hlinec
              simp only [hPA, hPB, hoa, hpre, hgap, eq_true hcp, hsuf, eq_true hhit, false_and, and_self,
                eq_self_iff_true, ↓reduceIte, reduceIte, mul_one, one_mul]
            · have hPA : ¬ pdLifePending S γ p e true j :=
                fun h => absurd (hpend.1.mp h) (not_lt.mpr hjc.le)
              have hPB : ¬ pdLifePending S γ p e false j :=
                fun h => absurd (hpend.2.mp h) (not_le.mpr hjc)
              have hcp : ¬ (some c = some j) := fun h => by
                cases h; exact absurd hjc (lt_irrefl _)
              have hsuf : ¬ (ω < j ∧ ∃ c', some c = some c' ∧ j < c') := by
                rintro ⟨-, c', hc', hjc'⟩
                cases hc'
                exact absurd (lt_trans hjc hjc') (lt_irrefl _)
              simp only [hPA, hPB, hoa, hpre, hgap, hcp, hsuf, false_and, eq_self_iff_true, ↓reduceIte, reduceIte, mul_one]

private lemma visit_active_eq_W {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ)
    (γ : EnvPath S.x K) (i : Fin K) (p : ℕ) (e : PrimeLife S γ p)
    (hA : (pdLifeActive S γ p).Nonempty) (j : Fin (pathLength S.x + 1)) :
    lifeVisitLocal F S ρ γ i p e j =
      activeW F S ρ γ i p e.1.1 e.1.2 ((pdLifeActive S γ p).min' hA)
        ((pdLifeActive S γ p).max' hA) (projLine p (γ ((pdLifeActive S γ p).min' hA)).1) j := by
  have h1 := entry_eq F S γ i p e hA j
  have h2 := rest_eq_active F S ρ γ i p e hA _ _ rfl rfl j
  calc lifeVisitLocal F S ρ γ i p e j =
      ((if j.val = 0 then lifeInitLocal F S γ i p else 1) * lifeEntF F S γ i p e j) *
        (lifeGhostLocal F S ρ γ i p e j * lifeOutF S ρ γ p e j * lifeInF S ρ γ p e j) := by
        unfold lifeVisitLocal; ring
    _ = _ := by
        rw [h1, h2]
        unfold activeW
        ring

private lemma visit_inactive_none {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ)
    (γ : EnvPath S.x K) (i : Fin K) (p : ℕ) (e : PrimeLife S γ p)
    (hA : ¬ (pdLifeActive S γ p).Nonempty) (hnone : e.1.1 = none)
    (j : Fin (pathLength S.x + 1)) : lifeVisitLocal F S ρ γ i p e j = 1 := by
  have hnact : ∀ k, ¬ IsActiveAt γ p k := fun k h => hA ⟨k, (mem_active S γ p k).mpr h⟩
  have hPA := pending_inactive_none S γ p e true j hA hnone
  have hPB := pending_inactive_none S γ p e false j hA hnone
  have hbr : ¬ e.1.1 = some j := by rw [hnone]; simp
  have hinit : lifeInitLocal F S γ i p = 1 := by
    unfold lifeInitLocal; rw [if_neg (hnact 0)]
  have hent : lifeEntF F S γ i p e j = 1 := by
    unfold lifeEntF
    by_cases h0 : j.val = 0
    · rw [if_pos h0]
    · rw [if_neg h0, if_neg (fun h => hnact j h.1)]
  unfold lifeVisitLocal lifeGhostLocal lifeOutF lifeInF
  rw [hent, hinit]
  simp only [hPA, hPB, hbr, false_and, eq_self_iff_true, ↓reduceIte, reduceIte, mul_one, ite_self]

private lemma visit_inactive_some {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ)
    (γ : EnvPath S.x K) (i : Fin K) (p : ℕ) (e : PrimeLife S γ p)
    (hA : ¬ (pdLifeActive S γ p).Nonempty) (a c : Fin (pathLength S.x + 1))
    (hlife : e.1 = (some a, some c)) (hac : a < c)
    (hline : projLine p (γ c).1 = projLine p (γ a).1)
    (j : Fin (pathLength S.x + 1)) :
    lifeVisitLocal F S ρ γ i p e j =
      (if j = a then -memoryEta S.x F.q_d j.val * bandMass S.x (F.a i) / ρ * ρ *
          memoryNu S.x K F.a F.q_d i p else 1) *
      (if j = c then -memoryEta S.x F.q_d j.val / ρ * ρ else 1) *
      (if a < j ∧ j < c then pdRawSurvival F S ρ γ p (projLine p (γ a).1) j else 1) := by
  have hnact : ∀ k, ¬ IsActiveAt γ p k := fun k h => hA ⟨k, (mem_active S γ p k).mpr h⟩
  have hoa : e.1.1 = some a := by rw [hlife]
  have hoc : e.1.2 = some c := by rw [hlife]
  have hpend := pd_life_b_pending_ghostOnly S γ p e hA a c hlife j
  have hll : lifeLine S γ p e.1 = projLine p (γ a).1 := by
    unfold lifeLine
    rw [dif_neg hA, hoa]
  have hinit : (if j.val = 0 then lifeInitLocal F S γ i p else 1) = 1 := by
    unfold lifeInitLocal; rw [if_neg (hnact 0), ite_self]
  have hent : lifeEntF F S γ i p e j = 1 := by
    unfold lifeEntF
    by_cases h0 : j.val = 0
    · rw [if_pos h0]
    · rw [if_neg h0, if_neg (fun h => hnact j h.1)]
  unfold lifeVisitLocal lifeGhostLocal lifeOutF lifeInF lifeHit pdRawSurvival
  rw [hent, hinit, hll]
  rcases lt_trichotomy j a with hja | hja | hja
  · have hPA : ¬ pdLifePending S γ p e true j := fun h => absurd (hpend.1.mp h).1 (not_le.mpr hja)
    have hPB : ¬ pdLifePending S γ p e false j :=
      fun h => absurd (hpend.2.mp h).1 (not_lt.mpr hja.le)
    have hbr : ¬ e.1.1 = some j := by
      rw [hoa]; intro h; cases h; exact absurd hja (lt_irrefl _)
    have hja' : ¬ j = a := ne_of_lt hja
    have hjc : ¬ j = c := ne_of_lt (lt_trans hja hac)
    have hmid : ¬ (a < j ∧ j < c) := fun h => absurd (lt_trans h.1 hja) (lt_irrefl _)
    simp only [hPA, hPB, hbr, hja', hjc, hmid, false_and, eq_self_iff_true, ↓reduceIte, reduceIte, mul_one]
  · have hPA : pdLifePending S γ p e true j := hpend.1.mpr ⟨le_of_eq hja.symm, hja ▸ hac⟩
    have hPB : ¬ pdLifePending S γ p e false j :=
      fun h => absurd (hpend.2.mp h).1 (not_lt.mpr (le_of_eq hja))
    have hbr : e.1.1 = some j := by rw [hoa, hja]
    have hcj : ¬ e.1.2 = some j := by
      rw [hoc]; intro h; cases h; exact absurd (hja ▸ hac) (lt_irrefl _)
    have hjc : ¬ j = c := fun h => absurd (h ▸ hja ▸ hac) (lt_irrefl _)
    have hmid : ¬ (a < j ∧ j < c) := fun h => absurd (hja ▸ h.1) (lt_irrefl _)
    have hhit : projLine p (γ j).1 = projLine p (γ a).1 := by rw [hja]
    simp only [hPA, hPB, eq_true hbr, hcj, eq_true hja, hjc, hmid, eq_true hhit, false_and, and_self,
      eq_self_iff_true, ↓reduceIte, reduceIte, mul_one, one_mul]
    ring
  · rcases lt_trichotomy j c with hjc | hjc | hjc
    · have hPA : pdLifePending S γ p e true j := hpend.1.mpr ⟨hja.le, hjc⟩
      have hPB : pdLifePending S γ p e false j := hpend.2.mpr ⟨hja, hjc.le⟩
      have hbr : ¬ e.1.1 = some j := by
        rw [hoa]; intro h; cases h; exact absurd hja (lt_irrefl _)
      have hcj : ¬ e.1.2 = some j := by
        rw [hoc]; intro h; cases h; exact absurd hjc (lt_irrefl _)
      have hja' : ¬ j = a := ne_of_gt hja
      have hjc' : ¬ j = c := ne_of_lt hjc
      have hmid : a < j ∧ j < c := ⟨hja, hjc⟩
      simp only [hPA, hPB, hbr, hcj, hja', hjc', hmid, true_and, and_self,
        eq_self_iff_true, ↓reduceIte, reduceIte, mul_one, one_mul]
      split_ifs <;> first | ring1 | contradiction
    · have hPA : ¬ pdLifePending S γ p e true j :=
        fun h => absurd (hpend.1.mp h).2 (not_lt.mpr (le_of_eq hjc.symm))
      have hPB : pdLifePending S γ p e false j := hpend.2.mpr ⟨hja, le_of_eq hjc⟩
      have hbr : ¬ e.1.1 = some j := by
        rw [hoa]; intro h; cases h; exact absurd hja (lt_irrefl _)
      have hcj : e.1.2 = some j := by rw [hoc, hjc]
      have hja' : ¬ j = a := ne_of_gt hja
      have hmid : ¬ (a < j ∧ j < c) := fun h => absurd (hjc ▸ h.2) (lt_irrefl _)
      have hhit : projLine p (γ j).1 = projLine p (γ a).1 := by rw [hjc]; exact hline
      simp only [hPA, hPB, hbr, eq_true hcj, hja', eq_true hjc, hmid, eq_true hhit, false_and, and_self,
        eq_self_iff_true, ↓reduceIte, reduceIte, mul_one, one_mul]
    · have hPA : ¬ pdLifePending S γ p e true j :=
        fun h => absurd (hpend.1.mp h).2 (not_lt.mpr hjc.le)
      have hPB : ¬ pdLifePending S γ p e false j :=
        fun h => absurd (hpend.2.mp h).2 (not_le.mpr hjc)
      have hbr : ¬ e.1.1 = some j := by
        rw [hoa]; intro h; cases h; exact absurd hja (lt_irrefl _)
      have hcj : ¬ e.1.2 = some j := by
        rw [hoc]; intro h; cases h; exact absurd hjc (lt_irrefl _)
      have hja' : ¬ j = a := ne_of_gt hja
      have hjc' : ¬ j = c := ne_of_gt hjc
      have hmid : ¬ (a < j ∧ j < c) := fun h => absurd (lt_trans h.2 hjc) (lt_irrefl _)
      simp only [hPA, hPB, hbr, hcj, hja', hjc', hmid, false_and, eq_self_iff_true, ↓reduceIte, reduceIte, mul_one]

/-- R1: the literal raw charge of a prime lifespan is the product of its local factors. -/
theorem rawPrimeLifeCharge_eq_local {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ)
    (γ : EnvPath S.x K) (i : Fin K) (p : ℕ) (e : PrimeLife S γ p) :
    pdRawPrimeLifeCharge F S ρ γ i p e =
      lifeInitLocal F S γ i p * (∏ j, lifeGhostLocal F S ρ γ i p e j) *
        ∏ j : Fin (pathLength S.x), lifeEdgeLocal F S ρ γ i p e j := by
  rw [lifeLocal_regroup]
  by_cases hA : (pdLifeActive S γ p).Nonempty
  · rw [rawCharge_active_eq_W F S ρ γ i p e hA]
    exact Finset.prod_congr rfl (fun j _ => (visit_active_eq_W F S ρ γ i p e hA j).symm)
  · rcases valid_inactive S γ p e hA with h | ⟨a, c, h, hac, hline⟩
    · have hnone : e.1.1 = none := by rw [h]
      rw [Finset.prod_eq_one (fun j _ => visit_inactive_none F S ρ γ i p e hA hnone j)]
      unfold pdRawPrimeLifeCharge
      dsimp only
      rw [dif_neg hA, h]
    · rw [Finset.prod_congr rfl (fun j _ => visit_inactive_some F S ρ γ i p e hA a c h hac hline j)]
      unfold pdRawPrimeLifeCharge
      dsimp only
      rw [dif_neg hA, h]
      dsimp only
      simp only [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, ↓reduceIte, reduceIte,
        Finset.prod_filter]

end

end ArtinPrimitiveRoots.Proofs.pd_birth_opus
