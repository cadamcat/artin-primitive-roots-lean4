import ArtinPrimitiveRoots.TypeII.Proofs.«PD-HIGH».BatchSupport
import ArtinPrimitiveRoots.TypeII.Proofs.«PD-HIGH».DeletionSupport
import ArtinPrimitiveRoots.TypeII.Proofs.«PD-HIGH».pd5_edge_position_mass_le
import ArtinPrimitiveRoots.TypeII.Proofs.«PD-HIGH».pd5_scale_facts
import ArtinPrimitiveRoots.TypeII.Proofs.pcr_opus.GhostRow
import ArtinPrimitiveRoots.TypeII.Proofs.pcr_opus.EdgeRow

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
  obtain ⟨x₁, hx₁, hscale⟩ := pd5_scale_facts K F hF
  obtain ⟨Cgeom, x₂, hCgeom, hx₂, hgeom⟩ := pd5_edge_position_mass_le δ c₁ c₂ hδ hc₁ K F hF
  have hρ0 : 0 < ρ := hρ.1
  have hρ1 : ρ < 1 := hρ.2.1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set v : ℝ := max 2 (2 / (ρ * (1 - Real.sqrt F.q_d / ρ ^ 2))) with hvdef
  have hv2 : 2 ≤ v := le_max_left _ _
  have hvlarge : 2 / (ρ * (1 - Real.sqrt F.q_d / ρ ^ 2)) ≤ v := le_max_right _ _
  have hv0 : 0 < v := by linarith
  set aAtom : ℝ := 4 / Real.log 2 with haAtom
  set Vinv : ℝ := 2 / Real.log 2 with hVinvdef
  set cbar : ℝ := v * (2 * Real.log 2) / ρ with hcbar
  set Cghost : ℝ := Real.exp (2 * (K : ℝ) * cbar) with hCghost
  set Cedge : ℝ := Cgeom * ((1 + v) * (Vinv + 2)) ^ K with hCedge
  have hVinv0 : 0 ≤ Vinv := (div_pos (by norm_num) hlog2).le
  refine ⟨v, Cghost, Cedge, 1, aAtom, max x₁ x₂, by linarith, Real.exp_pos _, ?_, le_rfl,
    div_pos (by norm_num) hlog2, le_trans hx₁ (le_max_left _ _), ?_⟩
  · rw [hCedge]
    apply mul_pos hCgeom
    apply pow_pos
    apply mul_pos (by linarith)
    linarith
  intro S hS hxS w hw B Δ s hs
  obtain ⟨hL1, -, -, -, -, -, -, hband⟩ := hscale S (le_trans (le_max_left _ _) hxS)
  have hsB : memSize s ≤ B := hs.2.1
  have hV : ∀ i, 0 < bandMass S.x (F.a i) := fun i =>
    lt_of_lt_of_le (by linarith) (hband i).1
  have hVinv : ∀ i, (bandMass S.x (F.a i))⁻¹ ≤ Vinv := by
    intro i
    have hlow := (hband i).1
    have hhalf : 0 < Real.log 2 / 2 := by linarith
    calc
      (bandMass S.x (F.a i))⁻¹ ≤ (Real.log 2 / 2)⁻¹ := (inv_le_inv₀ (hV i) hhalf).mpr hlow
      _ = Vinv := by rw [hVinvdef, inv_div]
  have hν : ∀ i p, p ∈ primeBand S.x (F.a i) → 0 ≤ memoryNu S.x K F.a F.q_d i p :=
    fun i p hp => ((hband i).2.2.2 p hp).1
  have hmass : ∀ i, (∑ p ∈ primeBand S.x (F.a i), memoryNu S.x K F.a F.q_d i p) ≤ 2 :=
    fun i => (hband i).2.2.1
  have hatom : ∀ i p, p ∈ primeBand S.x (F.a i) → memoryNu S.x K F.a F.q_d i p ≤ Δ :=
    fun i p hp => ((hband i).2.2.2 p hp).2
  have hΔ : 0 ≤ Δ := mul_nonneg (div_pos (by norm_num) hlog2).le (Real.exp_pos _).le
  constructor
  · intro j hj U R hRU hU pick pastLog
    have hη := pd5_memoryEta_bounds (x := S.x) hF.2.1 hF.2.2.1 j
    have hq : 0 ≤ memoryQ S.x F.q_d j := by
      unfold memoryQ
      split_ifs
      · exact Real.sqrt_nonneg _
      · exact hF.2.1.le
    have hdel := pcr_ghost_delete_total_le_one F S hF ρ hρ v hv0 hvlarge j s
    let c : Fin K → ℝ := fun i => v * memoryEta S.x F.q_d j * bandMass S.x (F.a i) / ρ
    have hc : ∀ i, 0 ≤ c i := fun i =>
      div_nonneg (mul_nonneg (mul_nonneg hv0.le hη.1) (hV i).le) hρ0.le
    have hcb : ∀ i, c i ≤ cbar := by
      intro i
      have h1 : memoryEta S.x F.q_d j * bandMass S.x (F.a i) ≤ 2 * Real.log 2 := by
        calc
          memoryEta S.x F.q_d j * bandMass S.x (F.a i) ≤ 1 * bandMass S.x (F.a i) :=
            mul_le_mul_of_nonneg_right hη.2 (hV i).le
          _ ≤ 2 * Real.log 2 := by linarith [(hband i).2.1]
      have h2 : v * memoryEta S.x F.q_d j * bandMass S.x (F.a i) ≤ v * (2 * Real.log 2) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left h1 hv0.le
      exact div_le_div_of_nonneg_right h2 hρ0.le
    have hcreate : (∑ l : Fin K → Fin (B + 1),
        (∏ i, pcr_ghostCreateFactor F S ρ v j (fun i => (l i).val) i) *
          (2 : ℝ) ^ (∑ i, (l i).val)) ≤ Cghost := by
      refine le_trans (le_of_eq ?_) (pcr_ghost_create_total_le_exp K B c cbar hc hcb)
      apply Finset.sum_congr rfl
      intro l _
      rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
      rfl
    have h := pcr_ghost_prescribed_row F S ρ v hρ0 hv0 j B s hsB U R hRU pick pastLog Δ Cghost
      hΔ (Real.exp_pos _).le hη.1 hq (fun i => (hV i).le) hν hmass hatom hdel hcreate
    simpa only [one_mul] using h
  · intro j hj U R hRU hU pick pastLog Z hZ
    have hG : 0 ≤ Cgeom * Real.rpow S.L (3 * F.A₀) :=
      mul_nonneg hCgeom.le (Real.rpow_nonneg (by linarith) _)
    have h := pcr_edge_prescribed_row F S ρ w j B Z s hsB U R hRU hU pick pastLog v Δ Vinv
      (Cgeom * Real.rpow S.L (3 * F.A₀)) hρ0 hρ1.le (by linarith) hΔ hVinv0 hG hV hVinv hν
      hmass hatom
      (fun p q hd hb forward => hgeom S hS (le_trans (le_max_right _ _) hxS) w hw s.1
        hs.1.1 hb p q hd forward Z)
    refine h.trans (le_of_eq ?_)
    rw [hCedge]
    push_cast
    rw [mul_pow]
    ring

end
end ArtinPrimitiveRoots.TypeII.PD
