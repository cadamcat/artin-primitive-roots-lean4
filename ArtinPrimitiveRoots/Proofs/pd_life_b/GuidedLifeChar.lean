import ArtinPrimitiveRoots.Proofs.pd_life_b.GuidedExist

set_option autoImplicit false

/-! Characterizations and constructors of lifespans. -/

namespace ArtinPrimitiveRoots.Proofs.pd_birth_opus

open Classical
open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
open ArtinPrimitiveRoots.Proofs.pd_life_b

noncomputable section

theorem pend_active_iff {K : ℕ} (S : PDScale) (γ : EnvPath S.x K) (p : ℕ)
    (e : PrimeLife S γ p) (hA : (pdLifeActive S γ p).Nonempty)
    (m : Fin (pathLength S.x + 1)) :
    pdLifePending S γ p e false m ↔ ¬ IsActiveAt γ p m ∧
      ((∃ a, e.1.1 = some a ∧ a < m) ∨ (pdLifeActive S γ p).min' hA < m) ∧
      ((∃ c, e.1.2 = some c ∧ m ≤ c) ∨ m < (pdLifeActive S γ p).max' hA) := by
  obtain ⟨-, hB, hC, -⟩ := life_active_facts S γ p e hA
  have hαact : IsActiveAt γ p ((pdLifeActive S γ p).min' hA) :=
    (Finset.mem_filter.mp (Finset.min'_mem _ hA)).2
  have hωact : IsActiveAt γ p ((pdLifeActive S γ p).max' hA) :=
    (Finset.mem_filter.mp (Finset.max'_mem _ hA)).2
  have hαω := Finset.min'_le_max' _ hA
  simp only [pdLifePending, hA, ↓reduceDIte]
  by_cases hm : IsActiveAt γ p m
  · simp [hm]
  have hαm : (pdLifeActive S γ p).min' hA ≠ m := fun h => hm (h ▸ hαact)
  have hωm : (pdLifeActive S γ p).max' hA ≠ m := fun h => hm (h ▸ hωact)
  simp only [hm, not_false_eq_true, true_and]
  clear hαact hωact
  generalize (pdLifeActive S γ p).min' hA = α at *
  generalize (pdLifeActive S γ p).max' hA = ω at *
  rcases e with ⟨⟨_ | a, _ | c⟩, he⟩
  · have := fun a (h : (none : Option (Fin (pathLength S.x + 1))) = some a) => hB a h
    split_ifs with h1 h2 <;> simp only [Fin.lt_def, Fin.le_def, Fin.ext_iff] at * <;>
      simp <;> omega
  · have hc := hC c rfl
    split_ifs with h1 h2 <;> simp only [Fin.lt_def, Fin.le_def, Fin.ext_iff] at * <;>
      simp <;> omega
  · have ha := (hB a rfl).1
    split_ifs with h1 h2 <;> simp only [Fin.lt_def, Fin.le_def, Fin.ext_iff] at * <;>
      simp <;> omega
  · have ha := (hB a rfl).1
    have hc := hC c rfl
    split_ifs with h1 h2 <;> simp only [Fin.lt_def, Fin.le_def, Fin.ext_iff] at * <;>
      simp <;> omega

theorem pend_inactive_iff {K : ℕ} (S : PDScale) (γ : EnvPath S.x K) (p : ℕ)
    (e : PrimeLife S γ p) (hA : ¬ (pdLifeActive S γ p).Nonempty)
    (m : Fin (pathLength S.x + 1)) :
    pdLifePending S γ p e false m ↔
      ∃ a c, e.1 = (some a, some c) ∧ a < m ∧ m ≤ c := by
  simp only [pdLifePending, hA, ↓reduceDIte]
  rcases life_inactive_facts S γ p e hA with h | ⟨a, c, h, -, -⟩
  · simp [h]
  · rw [h]; simp

theorem mem_active_iff {K : ℕ} (S : PDScale) (γ : EnvPath S.x K) (p : ℕ)
    (m : Fin (pathLength S.x + 1)) : m ∈ pdLifeActive S γ p ↔ IsActiveAt γ p m := by
  simp [pdLifeActive]

/-- Constructor: an active-type lifespan. -/
theorem mkLife_active {K : ℕ} (S : PDScale) (γ : EnvPath S.x K) (p : ℕ)
    (hA : (pdLifeActive S γ p).Nonempty)
    (hlines : ∀ m m', IsActiveAt γ p m → IsActiveAt γ p m' →
      projLine p (γ m).1 = projLine p (γ m').1)
    (b d : Option (Fin (pathLength S.x + 1)))
    (hb : ∀ a, b = some a → (∀ m, IsActiveAt γ p m → a < m) ∧
      ∃ m, IsActiveAt γ p m ∧ projLine p (γ a).1 = projLine p (γ m).1)
    (hd : ∀ c, d = some c → (∀ m, IsActiveAt γ p m → m < c) ∧
      ∃ m, IsActiveAt γ p m ∧ projLine p (γ c).1 = projLine p (γ m).1) :
    (b, d) ∈ pdLifeEndpoints S γ p := by
  have hαact : IsActiveAt γ p ((pdLifeActive S γ p).min' hA) :=
    (Finset.mem_filter.mp (Finset.min'_mem _ hA)).2
  have hωact : IsActiveAt γ p ((pdLifeActive S γ p).max' hA) :=
    (Finset.mem_filter.mp (Finset.max'_mem _ hA)).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  simp only [pdLifeEndpointValid, hA, ↓reduceDIte]
  refine ⟨fun m hm => hlines m _ ((mem_active_iff S γ p m).mp hm) hαact, ?_, ?_⟩
  · cases b with
    | none => trivial
    | some a =>
      obtain ⟨h1, m, hm, hl⟩ := hb a rfl
      exact ⟨h1 _ hαact, hl.trans (hlines m _ hm hαact)⟩
  · cases d with
    | none => trivial
    | some c =>
      obtain ⟨h1, m, hm, hl⟩ := hd c rfl
      exact ⟨h1 _ hωact, hl.trans (hlines m _ hm hαact)⟩

theorem mkLife_inactive_none {K : ℕ} (S : PDScale) (γ : EnvPath S.x K) (p : ℕ)
    (hA : ¬ (pdLifeActive S γ p).Nonempty) :
    ((none, none) : Option (Fin (pathLength S.x + 1)) × Option (Fin (pathLength S.x + 1))) ∈
      pdLifeEndpoints S γ p := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  simp only [pdLifeEndpointValid, hA, ↓reduceDIte]

theorem mkLife_inactive_some {K : ℕ} (S : PDScale) (γ : EnvPath S.x K) (p : ℕ)
    (hA : ¬ (pdLifeActive S γ p).Nonempty) (a c : Fin (pathLength S.x + 1)) (hac : a < c)
    (hl : projLine p (γ c).1 = projLine p (γ a).1) :
    ((some a, some c) : Option (Fin (pathLength S.x + 1)) × Option (Fin (pathLength S.x + 1))) ∈
      pdLifeEndpoints S γ p := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  simp only [pdLifeEndpointValid, hA, ↓reduceDIte]
  exact ⟨hac, hl⟩

/-- Line consistency of the active visits, from any valid lifespan. -/
theorem active_lines_of_life {K : ℕ} (S : PDScale) (γ : EnvPath S.x K) (p : ℕ)
    (e : PrimeLife S γ p) (m m' : Fin (pathLength S.x + 1))
    (hm : IsActiveAt γ p m) (hm' : IsActiveAt γ p m') :
    projLine p (γ m).1 = projLine p (γ m').1 := by
  have hA : (pdLifeActive S γ p).Nonempty := ⟨m, (mem_active_iff S γ p m).mpr hm⟩
  have h := (life_active_facts S γ p e hA).2.2.2
  rw [h m hm, h m' hm']

theorem lifeLine_active {K : ℕ} (S : PDScale) (γ : EnvPath S.x K) (p : ℕ)
    (e : Option (Fin (pathLength S.x + 1)) × Option (Fin (pathLength S.x + 1)))
    (hA : (pdLifeActive S γ p).Nonempty) :
    lifeLine S γ p e = projLine p (γ ((pdLifeActive S γ p).min' hA)).1 := by
  simp only [lifeLine, hA, ↓reduceDIte]

theorem lifeLine_inactive {K : ℕ} (S : PDScale) (γ : EnvPath S.x K) (p : ℕ)
    (a : Fin (pathLength S.x + 1)) (d : Option (Fin (pathLength S.x + 1)))
    (hA : ¬ (pdLifeActive S γ p).Nonempty) :
    lifeLine S γ p (some a, d) = projLine p (γ a).1 := by
  simp only [lifeLine, hA, ↓reduceDIte]

end

end ArtinPrimitiveRoots.Proofs.pd_birth_opus
