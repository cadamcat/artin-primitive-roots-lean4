import ArtinPrimitiveRoots.TypeII.Proofs.pd5b.PDHigh.BatchSupport
import ArtinPrimitiveRoots.TypeII.Proofs.pd5b.PDHigh.DeletionSupport
import ArtinPrimitiveRoots.TypeII.Proofs.pd5b.PDHigh.pd5_edge_position_mass_le
import ArtinPrimitiveRoots.TypeII.Proofs.pd5b.PDHigh.pd5_scale_facts

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
open ArtinPrimitiveRoots.TypeII
noncomputable section

private theorem triangular_coordinate_bound (P : Finset ℕ) (ν : ℕ → ℝ)
    (pick : ℕ) (Δ : ℝ) (hΔ : 0 ≤ Δ) (ha : ∀ p ∈ P, ν p ≤ Δ) :
    (∑ p : P, if (p : ℕ) = pick then ν p else 0) ≤ Δ := by
  by_cases hp : pick ∈ P
  · let p₀ : P := ⟨pick, hp⟩
    rw [Finset.sum_eq_single p₀]
    · simpa [p₀] using ha pick hp
    · intro p _ hne
      have hv : (p : ℕ) ≠ pick := fun he => hne (Subtype.ext he)
      simp [hv]
    · simp
  · have hz : (∑ p : P, if (p : ℕ) = pick then ν p else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro p _
      have hv : (p : ℕ) ≠ pick := fun he => hp (he ▸ p.property)
      simp [hv]
    rw [hz]
    exact hΔ

/-- Prefix-dependent prescribed coordinates cost one atom each. A prescription reads only
strictly earlier coordinates, including earlier coordinates of the same batch.
Guide `runs/lanes/sol-thin-pd5/PROOFS.md:207–243`; uses finite sum decomposition only;
feeds pd5_positive_choice_rows. LEAD. -/
theorem pd5_triangular_birth_sum_le (n : ℕ) (P : Fin n → Finset ℕ)
    (ν : Fin n → ℕ → ℝ) (R : Finset (Fin n)) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (pick : (k : Fin n) → (Fin k.val → ℕ) → ℕ)
    (hν : ∀ k p, p ∈ P k → 0 ≤ ν k p)
    (hatom : ∀ k ∈ R, ∀ p ∈ P k, ν k p ≤ Δ) :
    (∑ b : (k : Fin n) → {p : ℕ // p ∈ P k},
      if ∀ k ∈ R, (b k : ℕ) = pick k
        (fun j => (b ⟨j.val, lt_trans j.isLt k.isLt⟩ : ℕ))
      then ∏ k : Fin n, ν k (b k) else 0) ≤
      ∏ k : Fin n, if k ∈ R then Δ else ∑ p ∈ P k, ν k p := by
  induction n generalizing Δ with
  | zero => simp
  | succ n ih =>
    let R₀ : Finset (Fin n) := Finset.univ.filter fun k => k.castSucc ∈ R
    let P₀ : Fin n → Finset ℕ := fun k => P k.castSucc
    let ν₀ : Fin n → ℕ → ℝ := fun k => ν k.castSucc
    let pick₀ : (k : Fin n) → (Fin k.val → ℕ) → ℕ := fun k => pick k.castSucc
    let good₀ (b : (k : Fin n) → P₀ k) : Prop :=
      ∀ k ∈ R₀, (b k : ℕ) = pick₀ k
        (fun j => (b ⟨j.val, lt_trans j.isLt k.isLt⟩ : ℕ))
    let wt₀ (b : (k : Fin n) → P₀ k) : ℝ :=
      if good₀ b then ∏ k : Fin n, ν₀ k (b k) else 0
    let c : ℝ := if Fin.last n ∈ R then Δ else ∑ p ∈ P (Fin.last n), ν (Fin.last n) p
    have hc : 0 ≤ c := by
      dsimp [c]
      split_ifs
      · exact hΔ
      · exact Finset.sum_nonneg fun p hp => hν _ p hp
    have hw₀ (b : (k : Fin n) → P₀ k) : 0 ≤ wt₀ b := by
      dsimp [wt₀]
      split_ifs
      · exact Finset.prod_nonneg fun k _ => hν _ _ (b k).property
      · exact le_rfl
    let wt (b : (k : Fin (n + 1)) → P k) : ℝ :=
      if ∀ k ∈ R, (b k : ℕ) = pick k
        (fun j => (b ⟨j.val, lt_trans j.isLt k.isLt⟩ : ℕ))
      then ∏ k : Fin (n + 1), ν k (b k) else 0
    have hvalue (b : (k : Fin n) → P₀ k) (p : P (Fin.last n)) :
        (fun k => ((Fin.snoc (α := fun k => P k) b p) k : ℕ)) =
          Fin.snoc (α := fun _ => ℕ) (fun k => (b k : ℕ)) (p : ℕ) := by
      funext k
      refine Fin.lastCases ?_ (fun k => ?_) k <;> simp
    have hgood (b : (k : Fin n) → P₀ k) (p : P (Fin.last n)) :
        (∀ k ∈ R, ((Fin.snoc (α := fun k => P k) b p) k : ℕ) = pick k
          (fun j => ((Fin.snoc (α := fun k => P k) b p) ⟨j.val, lt_trans j.isLt k.isLt⟩ : ℕ))) ↔
          good₀ b ∧ (Fin.last n ∈ R →
            (p : ℕ) = pick (Fin.last n) (fun j => (b j : ℕ))) := by
      have hv (k : Fin (n + 1)) := congrFun (hvalue b p) k
      simp_rw [hv]
      constructor
      · intro h
        constructor
        · intro k hk
          have he := h k.castSucc (Finset.mem_filter.mp hk).2
          simp only [Fin.snoc_castSucc] at he
          calc
            (b k : ℕ) = pick k.castSucc
                (fun j => Fin.snoc (α := fun _ => ℕ) (fun k => (b k : ℕ)) (p : ℕ)
                  ⟨j.val, lt_trans j.isLt k.castSucc.isLt⟩) := he
            _ = pick₀ k (fun j => (b ⟨j.val, lt_trans j.isLt k.isLt⟩ : ℕ)) := by
              apply congrArg (pick k.castSucc)
              funext j
              exact Fin.snoc_castSucc (α := fun _ => ℕ) (p : ℕ) (fun k => (b k : ℕ))
                ⟨j.val, lt_trans j.isLt k.isLt⟩
        · intro hk
          have he := h (Fin.last n) hk
          simp only [Fin.snoc_last] at he
          calc
            (p : ℕ) = pick (Fin.last n)
                (fun j => Fin.snoc (α := fun _ => ℕ) (fun k => (b k : ℕ)) (p : ℕ)
                  ⟨j.val, lt_trans j.isLt (Fin.last n).isLt⟩) := he
            _ = pick (Fin.last n) (fun j => (b j : ℕ)) := by
              apply congrArg (pick (Fin.last n))
              funext j
              exact Fin.snoc_castSucc (α := fun _ => ℕ) (p : ℕ) (fun k => (b k : ℕ)) j
      · rintro ⟨h₀, hl⟩ k hk
        by_cases hkl : k = Fin.last n
        · subst k
          simp only [Fin.snoc_last]
          calc
            (p : ℕ) = pick (Fin.last n) (fun j => (b j : ℕ)) := hl hk
            _ = pick (Fin.last n)
                (fun j => Fin.snoc (α := fun _ => ℕ) (fun k => (b k : ℕ)) (p : ℕ)
                  ⟨j.val, lt_trans j.isLt (Fin.last n).isLt⟩) := by
              apply congrArg (pick (Fin.last n))
              funext j
              exact (Fin.snoc_castSucc (α := fun _ => ℕ) (p : ℕ) (fun k => (b k : ℕ)) j).symm
        · obtain ⟨k₀, rfl⟩ := Fin.exists_castSucc_eq.mpr hkl
          simp only [Fin.snoc_castSucc]
          have hk₀ : k₀ ∈ R₀ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
          calc
            (b k₀ : ℕ) = pick₀ k₀
                (fun j => (b ⟨j.val, lt_trans j.isLt k₀.isLt⟩ : ℕ)) := h₀ k₀ hk₀
            _ = pick k₀.castSucc
                (fun j => Fin.snoc (α := fun _ => ℕ) (fun k => (b k : ℕ)) (p : ℕ)
                  ⟨j.val, lt_trans j.isLt k₀.castSucc.isLt⟩) := by
              apply congrArg (pick k₀.castSucc)
              funext j
              exact (Fin.snoc_castSucc (α := fun _ => ℕ) (p : ℕ) (fun k => (b k : ℕ))
                ⟨j.val, lt_trans j.isLt k₀.isLt⟩).symm
    have hsplit (b : (k : Fin n) → P₀ k) (p : P (Fin.last n)) :
        wt ((Fin.snoc (α := fun k => P k) b p)) = wt₀ b *
          (if Fin.last n ∈ R then
            if (p : ℕ) = pick (Fin.last n) (fun j => (b j : ℕ))
            then ν (Fin.last n) p else 0
          else ν (Fin.last n) p) := by
      dsimp [wt, wt₀]
      rw [ite_cond_congr (propext (hgood b p))]
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      by_cases hb : good₀ b <;> by_cases hl : Fin.last n ∈ R <;>
        by_cases hp : (p : ℕ) = pick (Fin.last n) (fun j => (b j : ℕ)) <;>
        simp [hb, hl, hp, ν₀]
    have hlocal (b : (k : Fin n) → P₀ k) :
        (∑ p : P (Fin.last n), wt ((Fin.snoc (α := fun k => P k) b p))) ≤ wt₀ b * c := by
      simp_rw [hsplit]
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (hw₀ b)
      by_cases hl : Fin.last n ∈ R
      · simp only [hl, if_true, c]
        exact triangular_coordinate_bound (P (Fin.last n)) (ν (Fin.last n))
          (pick (Fin.last n) (fun j => (b j : ℕ))) Δ hΔ (hatom _ hl)
      · simp only [hl, if_false, c]
        rw [Finset.sum_coe_sort]
    have hih := ih P₀ ν₀ R₀ Δ hΔ pick₀
      (fun k p hp => hν k.castSucc p hp)
      (fun k hk p hp => hatom k.castSucc (Finset.mem_filter.mp hk).2 p hp)
    calc
      _ = ∑ p : P (Fin.last n), ∑ b : (k : Fin n) → P₀ k, wt ((Fin.snoc (α := fun k => P k) b p)) := by
        rw [← (Fin.snocEquiv (fun k => P k)).sum_comp wt, Fintype.sum_prod_type]
        rfl
      _ = ∑ b : (k : Fin n) → P₀ k, ∑ p : P (Fin.last n), wt ((Fin.snoc (α := fun k => P k) b p)) :=
        Finset.sum_comm
      _ ≤ ∑ b : (k : Fin n) → P₀ k, wt₀ b * c :=
        Finset.sum_le_sum fun b _ => hlocal b
      _ = (∑ b : (k : Fin n) → P₀ k, wt₀ b) * c := by rw [Finset.sum_mul]
      _ ≤ (∏ k : Fin n, if k ∈ R₀ then Δ else ∑ p ∈ P₀ k, ν₀ k p) * c :=
        mul_le_mul_of_nonneg_right hih hc
      _ = _ := by
        rw [Fin.prod_univ_castSucc]
        simp [R₀, P₀, ν₀, c]

/-- Uniform finite positive-choice rows with performed flags and chronological prescriptions.
Guide `runs/lanes/sol-thin-pd5/PROOFS.md:151–327`; uses pd5_scale_facts,
pd5_triangular_birth_sum_le, the deletion binomial sum and uniform geometric target count;
feeds pd5_fixed_system_abs_estimate and frozen history_rank_high. LEAD. -/
theorem pd5_positive_choice_rows (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁)
    (K : ℕ) (F : PDFix K) (hF : F.Valid) (ρ : ℝ) (hρ : IsMemoryRho F.q_d ρ) :
    PD5PositiveRowsAvailable δ c₁ c₂ F ρ := by
  sorry

end
end ArtinPrimitiveRoots.TypeII.PD
