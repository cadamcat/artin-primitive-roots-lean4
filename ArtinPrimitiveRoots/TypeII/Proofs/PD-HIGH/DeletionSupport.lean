import ArtinPrimitiveRoots.TypeII.Proofs.pd5b.PDHigh.Defs

set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
open ArtinPrimitiveRoots.TypeII
noncomputable section

/-! Indexed deletion bounds exposed from the proved MemoryResults helper bodies.
Guide `runs/lanes/sol-thin-pd5/PROOFS.md:164–185`. These feed positive ghost choice rows;
subsets count coordinates rather than distinct particle values. -/

theorem pd5_sum_powerset_binomial {α : Type*} [DecidableEq α]
    (H : Finset α) (a b : ℝ) :
    (∑ D ∈ H.powerset, a ^ D.card * b ^ (H.card - D.card)) = (a + b) ^ H.card := by
  classical
  calc
    _ = ∑ D ∈ H.powerset,
          (∏ _i ∈ D, a) * ∏ _i ∈ H \ D, b := by
          apply Finset.sum_congr rfl
          intro D hD
          have hsubset : D ⊆ H := Finset.mem_powerset.mp hD
          simp [Finset.prod_const, Finset.card_sdiff_of_subset hsubset]
    _ = ∏ i ∈ H, (a + b) := by
          symm
          exact Finset.prod_add (fun _ => a) (fun _ => b) H
    _ = (a + b) ^ H.card := by simp [Finset.prod_const]


theorem pd5_ghost_parenthesis_le_one {K : ℕ} (F : PDFix K) (hF : F.Valid)
    (ρ : ℝ) (hρ : IsMemoryRho F.q_d ρ) (v : ℝ)
    (hv : 2 / (ρ * (1 - Real.sqrt F.q_d / ρ ^ 2)) ≤ v) {x : ℝ} (j : ℕ) :
    memoryQ x F.q_d j / ρ ^ 2 + memoryEta x F.q_d j / (ρ * v) ≤ 1 := by
  rcases hF with ⟨_, hqd, hqdlt, _, _, _⟩
  rcases hρ with ⟨hρpos, hρlt, hroot⟩
  have hsquare : (Real.sqrt F.q_d) ^ 2 = F.q_d := Real.sq_sqrt hqd.le
  have hrootnonneg : 0 ≤ Real.sqrt F.q_d := Real.sqrt_nonneg _
  have hrootleOne : Real.sqrt F.q_d ≤ 1 := by
    by_contra h
    have hgt : 1 < Real.sqrt F.q_d := lt_of_not_ge h
    nlinarith [sq_nonneg (Real.sqrt F.q_d - 1), hsquare]
  have hrootle : F.q_d ≤ Real.sqrt F.q_d := by
    calc
      F.q_d = Real.sqrt F.q_d * Real.sqrt F.q_d := by nlinarith [hsquare]
      _ ≤ Real.sqrt F.q_d * 1 :=
        mul_le_mul_of_nonneg_left hrootleOne hrootnonneg
      _ = Real.sqrt F.q_d := by ring
  have hqjpos : 0 < memoryQ x F.q_d j := by
    unfold memoryQ
    split_ifs <;> positivity
  have hqj : memoryQ x F.q_d j ≤ Real.sqrt F.q_d := by
    unfold memoryQ
    split_ifs <;> linarith [hrootle]
  let g : ℝ := 1 - Real.sqrt F.q_d / ρ ^ 2
  have hg : 0 < g := by
    dsimp [g]
    apply sub_pos.mpr
    exact (div_lt_one (by positivity)).2 hroot
  have hdenρv : 0 < ρ * v := by
    have hvpos : 0 < 2 / (ρ * g) := div_pos (by norm_num) (mul_pos hρpos hg)
    exact mul_pos hρpos (lt_of_lt_of_le (div_pos (by norm_num) (mul_pos hρpos hg)) hv)
  have hlarge : 2 ≤ ρ * g * v := by
    have := (div_le_iff₀ (mul_pos hρpos hg)).mp hv
    nlinarith
  have hfrac : 1 / (ρ * v) ≤ g / 2 := by
    rw [div_le_iff₀ hdenρv]
    nlinarith [hlarge]
  have hqdiv : memoryQ x F.q_d j / ρ ^ 2 ≤ 1 - g := by
    calc
      _ ≤ Real.sqrt F.q_d / ρ ^ 2 :=
        div_le_div_of_nonneg_right hqj (sq_nonneg ρ)
      _ = 1 - g := by dsimp [g]; ring
  have heta : memoryEta x F.q_d j ≤ 1 := by
    unfold memoryEta
    linarith [hqjpos]
  have hetadiv : memoryEta x F.q_d j / (ρ * v) ≤ g / 2 := by
    calc
      _ ≤ 1 / (ρ * v) := div_le_div_of_nonneg_right heta hdenρv.le
      _ ≤ g / 2 := hfrac
  linarith


theorem pd5_ghost_deletion_subset_sum_le_one {α : Type*} [DecidableEq α]
    (H : Finset α) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    (∑ D ∈ H.powerset, a ^ D.card * b ^ (H.card - D.card)) ≤ 1 := by
  rw [pd5_sum_powerset_binomial]
  exact pow_le_one₀ (add_nonneg ha hb) hab

theorem pd5_ghost_group_deletions_le_one {K : ℕ} (F : PDFix K) (hF : F.Valid)
    (ρ : ℝ) (hρ : IsMemoryRho F.q_d ρ) (v : ℝ) (hv0 : 0 < v)
    (hv : 2 / (ρ * (1 - Real.sqrt F.q_d / ρ ^ 2)) ≤ v)
    {x : ℝ} (j : ℕ) (l : List Particle) (z : ℤ × ℤ) :
    (∑ D ∈ (hitIndices l z).powerset,
      (memoryEta x F.q_d j / (ρ * v)) ^ D.card *
        (memoryQ x F.q_d j / ρ ^ 2) ^ ((hitIndices l z).card - D.card)) ≤ 1 := by
  have hqd : 0 < F.q_d := hF.2.1
  have hqdlt : F.q_d < 1 := hF.2.2.1
  have hρpos := hρ.1
  have hρlt := hρ.2.1
  have hroot := hρ.2.2
  have hη : 0 ≤ memoryEta x F.q_d j := by
    have hqj : memoryQ x F.q_d j < 1 := by
      have hρsq : ρ ^ 2 < 1 := by nlinarith [hρpos, hρlt]
      have hrootltone : Real.sqrt F.q_d < 1 := lt_trans hroot hρsq
      unfold memoryQ
      split_ifs <;> assumption
    unfold memoryEta
    linarith
  have hqnonneg : 0 ≤ memoryQ x F.q_d j := by
    unfold memoryQ
    split_ifs
    · exact Real.sqrt_nonneg _
    · exact hF.2.1.le
  have ha : 0 ≤ memoryEta x F.q_d j / (ρ * v) :=
    div_nonneg hη (mul_nonneg hρpos.le hv0.le)
  have hb : 0 ≤ memoryQ x F.q_d j / ρ ^ 2 :=
    div_nonneg hqnonneg (sq_nonneg ρ)
  have hab : memoryEta x F.q_d j / (ρ * v) +
      memoryQ x F.q_d j / ρ ^ 2 ≤ 1 := by
    have h := pd5_ghost_parenthesis_le_one F hF ρ hρ v hv (x := x) j
    linarith
  exact pd5_ghost_deletion_subset_sum_le_one (hitIndices l z)
    (memoryEta x F.q_d j / (ρ * v)) (memoryQ x F.q_d j / ρ ^ 2) ha hb hab

/-- The finite all-subsets sum vanishes off the hitting-coordinate powerset. -/
theorem pd5_ghost_indexed_deletions_le_one {K : ℕ} (F : PDFix K) (hF : F.Valid)
    (ρ : ℝ) (hρ : IsMemoryRho F.q_d ρ) (v : ℝ) (hv0 : 0 < v)
    (hv : 2 / (ρ * (1 - Real.sqrt F.q_d / ρ ^ 2)) ≤ v)
    {x : ℝ} (j : ℕ) (l : List Particle) (z : ℤ × ℤ) :
    (∑ D : Finset (Fin l.length), if D ⊆ hitIndices l z then
      (memoryEta x F.q_d j / (ρ * v)) ^ D.card *
        (memoryQ x F.q_d j / ρ ^ 2) ^ ((hitIndices l z).card - D.card) else 0) ≤ 1 := by
  rw [← Finset.sum_filter]
  have he : (Finset.univ.filter fun D : Finset (Fin l.length) => D ⊆ hitIndices l z) =
      (hitIndices l z).powerset := by
    ext D
    simp
  rw [he]
  exact pd5_ghost_group_deletions_le_one F hF ρ hρ v hv0 hv j l z

end
end ArtinPrimitiveRoots.TypeII.PD
