import ArtinPrimitiveRoots.Construction.Proofs.c4.BlockApply
import ArtinPrimitiveRoots.Construction.Proofs.c4.RoughPairResidues

namespace ArtinPrimitiveRoots.Construction.Proofs.C4

open Classical
open Filter
open scoped Topology
open ArtinPrimitiveRoots.TypeII

theorem pairSieveG_eulerFactor {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) (W : ℝ) :
    (if (p : ℝ) ≤ W then
      1 - pairSieveG W p =
        (1 - 1 / (p : ℝ)) ^ 3 * (1 - 1 / ((p : ℝ) - 1) ^ 2)
    else
      1 - pairSieveG W p =
        (1 - 1 / (p : ℝ)) * (1 + 1 / ((p : ℝ) * ((p : ℝ) - 1)))) := by
  have hpcast : (2 : ℝ) < (p : ℝ) := by exact_mod_cast hp2
  have hpne : (p : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hpminusne : (p : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
  have hcastSub : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ p)]
    simp
  have hcastSub₂ : ((2 * p - 1 : ℕ) : ℝ) = 2 * (p : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * p)]
    push_cast
    simp
  by_cases hW : (p : ℝ) ≤ W
  · simp only [if_pos hW]
    unfold pairSieveG pairSieveRho
    rw [if_pos hW]
    push_cast
    rw [hcastSub, hcastSub₂]
    field_simp [hpne, hpminusne]
    <;> ring_nf
  · simp only [if_neg hW]
    unfold pairSieveG pairSieveRho
    rw [if_neg hW]
    push_cast
    rw [hcastSub]
    field_simp [hpne, hpminusne]
    <;> ring_nf

noncomputable def pairSieveBaseline (W : ℝ) (p : ℕ) : ℝ :=
  if (p : ℝ) ≤ W then (1 - 1 / (p : ℝ)) ^ 3 else 1 - 1 / (p : ℝ)

noncomputable def pairSieveCorrection (W : ℝ) (p : ℕ) : ℝ :=
  if (p : ℝ) ≤ W then 1 else 1 + 1 / ((p : ℝ) * ((p : ℝ) - 1))

theorem pairSieveBaseline_inv_le_exp {p : ℕ} (hp5 : 5 ≤ p) (W : ℝ) :
    0 < pairSieveBaseline W p ∧
      (pairSieveBaseline W p)⁻¹ ≤ Real.exp (6 / (p : ℝ)) := by
  have hpcast : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp5
  have hpPos : 0 < (p : ℝ) := by linarith
  have hpmPos : 0 < (p : ℝ) - 1 := by linarith
  have hpne : (p : ℝ) ≠ 0 := ne_of_gt hpPos
  have hpmne : (p : ℝ) - 1 ≠ 0 := ne_of_gt hpmPos
  have hbaseEq : 1 - 1 / (p : ℝ) = ((p : ℝ) - 1) / (p : ℝ) := by
    field_simp [hpne]
    <;> ring
  have hright : 1 + 6 / (p : ℝ) = ((p : ℝ) + 6) / (p : ℝ) := by
    field_simp [hpne]
    <;> ring
  have hpoly : (p : ℝ) ^ 4 ≤ ((p : ℝ) + 6) * ((p : ℝ) - 1) ^ 3 := by
    have hlin : 0 ≤ 3 * (p : ℝ) - 15 := by linarith
    have h1 : 0 ≤ (p : ℝ) ^ 2 * (3 * (p : ℝ) - 15) :=
      mul_nonneg (sq_nonneg _) hlin
    have h2 : 0 ≤ 17 * (p : ℝ) - 6 := by nlinarith
    have hid : ((p : ℝ) + 6) * ((p : ℝ) - 1) ^ 3 - (p : ℝ) ^ 4 =
        (p : ℝ) ^ 2 * (3 * (p : ℝ) - 15) + (17 * (p : ℝ) - 6) := by ring
    nlinarith
  have hlowRat : ((1 - 1 / (p : ℝ)) ^ 3)⁻¹ ≤ 1 + 6 / (p : ℝ) := by
    rw [hbaseEq, hright]
    have hinv : ((((p : ℝ) - 1) / (p : ℝ)) ^ 3)⁻¹ =
        (p : ℝ) ^ 3 / ((p : ℝ) - 1) ^ 3 := by
      field_simp [hpne, hpmne]
      <;> ring
    rw [hinv]
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < ((p : ℝ) - 1) ^ 3) hpPos).2
    nlinarith [hpoly]
  have hhighRat : (1 - 1 / (p : ℝ))⁻¹ ≤ 1 + 6 / (p : ℝ) := by
    rw [hbaseEq, hright]
    have hinv : (((p : ℝ) - 1) / (p : ℝ))⁻¹ =
        (p : ℝ) / ((p : ℝ) - 1) := by
      field_simp [hpne, hpmne]
      <;> ring
    rw [hinv]
    apply (div_le_div_iff₀ hpmPos hpPos).2
    nlinarith [hpcast]
  have hexp : 1 + 6 / (p : ℝ) ≤ Real.exp (6 / (p : ℝ)) := by
    simpa [add_comm] using Real.add_one_le_exp (6 / (p : ℝ))
  have hbasePos : 0 < 1 - 1 / (p : ℝ) := by
    have hlt : 1 / (p : ℝ) < 1 := (div_lt_one hpPos).2 (by linarith)
    linarith
  by_cases hW : (p : ℝ) ≤ W
  · rw [pairSieveBaseline, if_pos hW]
    exact ⟨pow_pos hbasePos 3,
      hlowRat.trans hexp⟩
  · rw [pairSieveBaseline, if_neg hW]
    exact ⟨hbasePos, hhighRat.trans hexp⟩

theorem pairSieveMissingFactor_bound (All R : Finset ℕ) (W : ℝ)
    (hW : 2 ≤ W) (hR : ∀ p ∈ R, 5 ≤ p)
    (hrecip : ∑ p ∈ R, 1 / (p : ℝ) ≤ 1) :
    0 < ∏ p ∈ insert 2 R, pairSieveBaseline W p ∧
      (∏ p ∈ insert 2 R, pairSieveBaseline W p)⁻¹ ≤ 8 * Real.exp 6 := by
  have htwoW : (2 : ℝ) ≤ W := hW
  have hbase2 : pairSieveBaseline W 2 = 1 / 8 := by
    simp [pairSieveBaseline, htwoW]
    norm_num
  have hbaseRpos : ∀ p ∈ R, 0 < pairSieveBaseline W p := by
    intro p hp
    exact (pairSieveBaseline_inv_le_exp (hR p hp) W).1
  have h2not : 2 ∉ R := by
    intro hmem
    have h := hR 2 hmem
    omega
  have hprodRpos : 0 < ∏ p ∈ R, pairSieveBaseline W p :=
    Finset.prod_pos fun p hp => hbaseRpos p hp
  have hpos : 0 < ∏ p ∈ insert 2 R, pairSieveBaseline W p := by
    rw [Finset.prod_insert h2not, hbase2]
    positivity
  have hprodRInv :
      ∏ p ∈ R, (pairSieveBaseline W p)⁻¹ ≤ Real.exp 6 := by
    have hpoint : ∀ p ∈ R,
        0 ≤ (pairSieveBaseline W p)⁻¹ ∧
          (pairSieveBaseline W p)⁻¹ ≤ Real.exp (6 / (p : ℝ)) := by
      intro p hp
      have h := pairSieveBaseline_inv_le_exp (hR p hp) W
      exact ⟨(inv_nonneg.mpr h.1.le), h.2⟩
    have hprodExp :
        (∏ p ∈ R, (pairSieveBaseline W p)⁻¹) ≤
          ∏ p ∈ R, Real.exp (6 / (p : ℝ)) := by
      apply Finset.prod_le_prod₀
      · exact fun p hp => (hpoint p hp).1
      · exact fun p hp => (hpoint p hp).2
    have hsumExp : (∑ p ∈ R, 6 / (p : ℝ)) =
        6 * (∑ p ∈ R, 1 / (p : ℝ)) := by
      calc
        _ = ∑ p ∈ R, 6 * (1 / (p : ℝ)) := by
          apply Finset.sum_congr rfl
          intro p hp
          ring
        _ = _ := by rw [Finset.mul_sum]
    have hExpEq :
        (∏ p ∈ R, Real.exp (6 / (p : ℝ))) =
          Real.exp (6 * (∑ p ∈ R, 1 / (p : ℝ))) := by
      rw [← Real.exp_sum, hsumExp]
    calc
      _ ≤ ∏ p ∈ R, Real.exp (6 / (p : ℝ)) := hprodExp
      _ = Real.exp (6 * (∑ p ∈ R, 1 / (p : ℝ))) := hExpEq
      _ ≤ Real.exp 6 := by
        apply Real.exp_le_exp.mpr
        have hmul := mul_le_mul_of_nonneg_left hrecip (by norm_num : (0 : ℝ) ≤ 6)
        simpa using hmul
  constructor
  · exact hpos
  · rw [Finset.prod_insert h2not, hbase2]
    have hprodInv : (∏ p ∈ R, pairSieveBaseline W p)⁻¹ =
        ∏ p ∈ R, (pairSieveBaseline W p)⁻¹ := by rw [Finset.prod_inv_distrib]
    calc
      (1 / 8 * ∏ p ∈ R, pairSieveBaseline W p)⁻¹ =
          8 * (∏ p ∈ R, pairSieveBaseline W p)⁻¹ := by
        field_simp [ne_of_gt hprodRpos]
        <;> ring
      _ = 8 * ∏ p ∈ R, (pairSieveBaseline W p)⁻¹ := by rw [hprodInv]
      _ ≤ 8 * Real.exp 6 :=
        mul_le_mul_of_nonneg_left hprodRInv (by norm_num)

theorem pairSieveBaselineProduct_eq (W z : ℝ) (hW : 2 ≤ W) (hWz : W ≤ z) :
    ∏ p ∈ ArtinPrimitiveRoots.TypeII.primesUpTo z, pairSieveBaseline W p =
      ArtinPrimitiveRoots.TypeII.roughSieveProduct W ^ 2 *
        ArtinPrimitiveRoots.TypeII.roughSieveProduct z := by
  classical
  have hWnonneg : 0 ≤ W := by linarith
  have hZnonneg : 0 ≤ z := le_trans hWnonneg hWz
  have hmem (y : ℝ) (hy : 0 ≤ y) (p : ℕ) :
      p ∈ ArtinPrimitiveRoots.TypeII.primesUpTo y ↔ p.Prime ∧ (p : ℝ) ≤ y := by
    simp only [ArtinPrimitiveRoots.TypeII.primesUpTo, Finset.mem_filter,
      Finset.mem_range, Nat.lt_succ_iff, Nat.le_floor_iff hy]
    exact and_comm
  let All := ArtinPrimitiveRoots.TypeII.primesUpTo z
  let low := All.filter (fun p : ℕ => (p : ℝ) ≤ W)
  let high := All.filter (fun p : ℕ => W < (p : ℝ))
  have hlow : low = ArtinPrimitiveRoots.TypeII.primesUpTo W := by
    ext p
    simp only [low, All, Finset.mem_filter, hmem z hZnonneg p,
      hmem W hWnonneg p]
    constructor
    · rintro ⟨⟨hp, hpz⟩, hpW⟩
      exact ⟨hp, hpW⟩
    · rintro ⟨hp, hpW⟩
      exact ⟨⟨hp, hpW.trans hWz⟩, hpW⟩
  have hsplit :
      (∏ p ∈ All, (1 - 1 / (p : ℝ))) =
        (∏ p ∈ low, (1 - 1 / (p : ℝ))) *
          ∏ p ∈ high, (1 - 1 / (p : ℝ)) := by
    simpa [low, high] using
      (Finset.prod_filter_mul_prod_filter_not All
        (fun p : ℕ => (p : ℝ) ≤ W) (fun p => 1 - 1 / (p : ℝ))).symm
  have hbaseSplit :
      (∏ p ∈ All, pairSieveBaseline W p) =
        (∏ p ∈ low, (1 - 1 / (p : ℝ)) ^ 3) *
          ∏ p ∈ high, (1 - 1 / (p : ℝ)) := by
    have hlowFactor : ∀ p ∈ low,
        pairSieveBaseline W p = (1 - 1 / (p : ℝ)) ^ 3 := by
      intro p hp
      rw [pairSieveBaseline, if_pos (Finset.mem_filter.mp hp).2]
    have hhighFactor : ∀ p ∈ high,
        pairSieveBaseline W p = 1 - 1 / (p : ℝ) := by
      intro p hp
      rw [pairSieveBaseline, if_neg (by simpa using (Finset.mem_filter.mp hp).2)]
    calc
      _ = (∏ p ∈ low, pairSieveBaseline W p) *
            ∏ p ∈ high, pairSieveBaseline W p := by
          simpa [low, high] using
            (Finset.prod_filter_mul_prod_filter_not All
              (fun p : ℕ => (p : ℝ) ≤ W) (fun p => pairSieveBaseline W p)).symm
      _ = _ := by
        congr 1
        · apply Finset.prod_congr rfl
          intro p hp
          exact hlowFactor p hp
        · apply Finset.prod_congr rfl
          intro p hp
          exact hhighFactor p hp
  have hlowPow : (∏ p ∈ low, (1 - 1 / (p : ℝ)) ^ 3) =
      (∏ p ∈ ArtinPrimitiveRoots.TypeII.primesUpTo W, (1 - 1 / (p : ℝ))) ^ 3 := by
    rw [← hlow, Finset.prod_pow]
  have hVsplit :
      ArtinPrimitiveRoots.TypeII.roughSieveProduct z =
        ArtinPrimitiveRoots.TypeII.roughSieveProduct W *
          ∏ p ∈ high, (1 - 1 / (p : ℝ)) := by
    unfold ArtinPrimitiveRoots.TypeII.roughSieveProduct
    change (∏ p ∈ All, (1 - 1 / (p : ℝ))) =
      (∏ p ∈ ArtinPrimitiveRoots.TypeII.primesUpTo W, (1 - 1 / (p : ℝ))) *
        ∏ p ∈ high, (1 - 1 / (p : ℝ))
    rw [hsplit, hlow]
  rw [hbaseSplit, hlowPow]
  rw [hVsplit]
  unfold ArtinPrimitiveRoots.TypeII.roughSieveProduct
  ring

theorem pairSieveG_factor_le {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) (W : ℝ) :
    0 ≤ 1 - pairSieveG W p ∧
      1 - pairSieveG W p ≤ pairSieveBaseline W p * pairSieveCorrection W p := by
  have hpcast : (2 : ℝ) < (p : ℝ) := by exact_mod_cast hp2
  have hfactor := pairSieveG_eulerFactor hp hp2 W
  by_cases hW : (p : ℝ) ≤ W
  · simp only [if_pos hW] at hfactor
    constructor
    · rw [hfactor]
      have hden : 1 < ((p : ℝ) - 1) ^ 2 := by nlinarith
      have hinv : 0 < 1 - 1 / ((p : ℝ) - 1) ^ 2 := by
        have hlt : 1 / ((p : ℝ) - 1) ^ 2 < 1 := (div_lt_one (by positivity)).2 hden
        linarith
      have hbase : 0 < (1 - 1 / (p : ℝ)) ^ 3 := by
        have hpInvLt : 1 / (p : ℝ) < 1 := (div_lt_one (by linarith)).2 (by linarith)
        exact pow_pos (by linarith) _
      exact mul_nonneg hbase.le hinv.le
    · rw [hfactor]
      dsimp [pairSieveBaseline, pairSieveCorrection]
      rw [if_pos hW, if_pos hW]
      have hfactorNonneg : 0 ≤ (1 - 1 / (p : ℝ)) ^ 3 := by
        have hpInvLt : 1 / (p : ℝ) < 1 := (div_lt_one (by linarith)).2 (by linarith)
        exact (pow_pos (by linarith) _).le
      have hfactorLe : 1 - 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 := by
        have hnonneg : 0 ≤ 1 / ((p : ℝ) - 1) ^ 2 := by positivity
        linarith
      calc
        (1 - 1 / (p : ℝ)) ^ 3 * (1 - 1 / ((p : ℝ) - 1) ^ 2) ≤
            (1 - 1 / (p : ℝ)) ^ 3 * 1 :=
          mul_le_mul_of_nonneg_left hfactorLe hfactorNonneg
        _ = (1 - 1 / (p : ℝ)) ^ 3 * 1 := rfl
  · simp only [if_neg hW] at hfactor
    constructor
    · rw [hfactor]
      have hpminus : 1 < (p : ℝ) := by linarith
      have hden : 0 < (p : ℝ) * ((p : ℝ) - 1) := mul_pos (by linarith) (by linarith)
      have hfrac : 0 < (p : ℝ) - 1 := by linarith
      have hpfrac : 0 < 1 - 1 / (p : ℝ) := by
        have hlt : 1 / (p : ℝ) < 1 := (div_lt_one (by linarith)).2 (by linarith)
        linarith
      have hcor : 0 < 1 + 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by positivity
      positivity
    · rw [hfactor]
      dsimp [pairSieveBaseline, pairSieveCorrection]
      rw [if_neg hW, if_neg hW]

theorem pairSieveG_prod_le_of_missing_bound (P All : Finset ℕ) (W C D : ℝ)
    (g : ℕ → ℝ) (hP : P ⊆ All)
    (hfactor : ∀ p ∈ P, 0 ≤ 1 - g p ∧
      1 - g p ≤ pairSieveBaseline W p * pairSieveCorrection W p)
    (hbase : ∀ p ∈ All, 0 ≤ pairSieveBaseline W p)
    (hcorr : ∀ p ∈ P, 0 ≤ pairSieveCorrection W p)
    (hmissPos : 0 < ∏ p ∈ All \ P, pairSieveBaseline W p)
    (hmissInv : (∏ p ∈ All \ P, pairSieveBaseline W p)⁻¹ ≤ C)
    (hcorrBound : ∏ p ∈ P, pairSieveCorrection W p ≤ D)
    (hC : 0 ≤ C) (hD : 0 ≤ D) :
    ∏ p ∈ P, (1 - g p) ≤ C * D * ∏ p ∈ All, pairSieveBaseline W p := by
  classical
  let missing := All \ P
  have hdisj : Disjoint P missing := by
    rw [Finset.disjoint_left]
    intro p hpP hpMiss
    exact (Finset.mem_sdiff.mp hpMiss).2 hpP
  have hUnion : P ∪ missing = All := by
    ext p
    simp only [Finset.mem_union]
    dsimp [missing]
    simp only [Finset.mem_sdiff]
    constructor
    · intro hp
      rcases hp with hpP | ⟨hpAll, _⟩
      · exact hP hpP
      · exact hpAll
    · intro hpAll
      by_cases hpP : p ∈ P
      · exact Or.inl hpP
      · exact Or.inr ⟨hpAll, hpP⟩
  have hAllProduct :
      (∏ p ∈ All, pairSieveBaseline W p) =
        (∏ p ∈ P, pairSieveBaseline W p) *
          ∏ p ∈ missing, pairSieveBaseline W p := by
    rw [← hUnion, Finset.prod_union hdisj]
  have hPbaseNonneg : 0 ≤ ∏ p ∈ P, pairSieveBaseline W p := by
    apply Finset.prod_nonneg
    intro p hp
    exact hbase p (hP hp)
  have hAllbaseNonneg : 0 ≤ ∏ p ∈ All, pairSieveBaseline W p := by
    apply Finset.prod_nonneg
    exact hbase
  have hPbaseBound :
      ∏ p ∈ P, pairSieveBaseline W p ≤
        C * ∏ p ∈ All, pairSieveBaseline W p := by
    have hEq :
      ∏ p ∈ P, pairSieveBaseline W p =
          (∏ p ∈ All, pairSieveBaseline W p) *
            (∏ p ∈ missing, pairSieveBaseline W p)⁻¹ := by
      rw [hAllProduct]
      have hmissPos' : 0 < ∏ p ∈ missing, pairSieveBaseline W p := by
        simpa [missing] using hmissPos
      field_simp [ne_of_gt hmissPos']
      <;> ring
    rw [hEq]
    calc
      _ ≤ (∏ p ∈ All, pairSieveBaseline W p) * C :=
        mul_le_mul_of_nonneg_left hmissInv hAllbaseNonneg
      _ = C * ∏ p ∈ All, pairSieveBaseline W p := by ring
  have hPcorNonneg : 0 ≤ ∏ p ∈ P, pairSieveCorrection W p := by
    apply Finset.prod_nonneg
    exact hcorr
  have hPfactor :
      ∏ p ∈ P, (1 - g p) ≤
        ∏ p ∈ P, (pairSieveBaseline W p * pairSieveCorrection W p) := by
    apply Finset.prod_le_prod₀
    · exact fun p hp => (hfactor p hp).1
    · exact fun p hp => hfactor p hp |>.2
  calc
    _ ≤ ∏ p ∈ P, (pairSieveBaseline W p * pairSieveCorrection W p) := hPfactor
    _ = (∏ p ∈ P, pairSieveBaseline W p) *
          ∏ p ∈ P, pairSieveCorrection W p := by rw [Finset.prod_mul_distrib]
    _ ≤ (C * ∏ p ∈ All, pairSieveBaseline W p) * D :=
      mul_le_mul hPbaseBound hcorrBound hPcorNonneg (mul_nonneg hC hAllbaseNonneg)
    _ = C * D * ∏ p ∈ All, pairSieveBaseline W p := by ring
theorem pairCorrectionProduct_le_half (S : Finset ℕ)
    (hS : ∀ p ∈ S, 3 ≤ p) :
    ∏ p ∈ S, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 1))) ≤ Real.exp (1 / 2) := by
  classical
  let N : ℕ := max 3 (S.sup id)
  have hN : 3 ≤ N := by dsimp [N]; exact le_max_left _ _
  have htel : ∀ n : ℕ, 2 ≤ n →
      (∑ p ∈ Finset.Icc 3 n, (1 / ((p : ℝ) - 1) - 1 / (p : ℝ))) =
        1 / 2 - 1 / (n : ℝ) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      rw [ih]
      have hcast : (((n + 1 : ℕ) : ℝ) - 1) = (n : ℝ) := by push_cast; ring
      rw [hcast]
      have hnne : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
      have hnsne : (n : ℝ) + 1 ≠ 0 := by positivity
      field_simp [hnne, hnsne]
      <;> ring
  have hsubset : S ⊆ Finset.Icc 3 N := by
    intro p hp
    refine Finset.mem_Icc.mpr ⟨hS p hp, ?_⟩
    have hpN : p ≤ S.sup id := Finset.le_sup (f := id) hp
    exact hpN.trans (le_max_right _ _)
  have hsum :
      (∑ p ∈ S, 1 / ((p : ℝ) * ((p : ℝ) - 1))) ≤ 1 / 2 := by
    have hEq : (∑ p ∈ S, 1 / ((p : ℝ) * ((p : ℝ) - 1))) =
        ∑ p ∈ S, (1 / ((p : ℝ) - 1) - 1 / (p : ℝ)) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hpcast : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hS p hp
      have hpne : (p : ℝ) ≠ 0 := ne_of_gt (by linarith)
      have hpmne : (p : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
      field_simp [hpne, hpmne]
      <;> ring
    rw [hEq]
    have hsumle := Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (by
        intro p hp hpnot
        have hpcast : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hp).1
        have hpne : (p : ℝ) ≠ 0 := ne_of_gt (by linarith)
        have hpmne : (p : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
        have hle : 1 / (p : ℝ) ≤ 1 / ((p : ℝ) - 1) := by
          apply (div_le_div_iff₀ (by linarith : (0 : ℝ) < (p : ℝ))
            (by linarith : (0 : ℝ) < (p : ℝ) - 1)).2
          nlinarith
        exact sub_nonneg.mpr hle)
    have htelN := htel N (by omega)
    have hNcast : 0 ≤ 1 / (N : ℝ) := by positivity
    calc
      _ ≤ ∑ p ∈ Finset.Icc 3 N,
          (1 / ((p : ℝ) - 1) - 1 / (p : ℝ)) := hsumle
      _ = 1 / 2 - 1 / (N : ℝ) := htelN
      _ ≤ 1 / 2 := by linarith
  calc
    _ ≤ ∏ p ∈ S,
        Real.exp (1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
          apply Finset.prod_le_prod₀
          · intro p hp
            have hpcast : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hS p hp
            have hpden : 0 < (p : ℝ) * ((p : ℝ) - 1) :=
              mul_pos (by linarith) (by linarith)
            positivity
          · intro p hp
            simpa [add_comm] using
              (Real.add_one_le_exp (1 / ((p : ℝ) * ((p : ℝ) - 1))))
    _ = Real.exp (∑ p ∈ S,
          1 / ((p : ℝ) * ((p : ℝ) - 1))) := by rw [← Real.exp_sum]
    _ ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr hsum
theorem pairSieveG_product_le (W z : ℝ) (r : ℕ)
    (hW : 2 ≤ W) (hWz : W ≤ z)
    (hRprimeSize : ∀ p ∈
        (ArtinPrimitiveRoots.TypeII.primesUpTo z).filter (fun p : ℕ => p ∣ r),
        5 ≤ p)
    (hRrecip : ∑ p ∈ (ArtinPrimitiveRoots.TypeII.primesUpTo z).filter
        (fun p : ℕ => p ∣ r), 1 / (p : ℝ) ≤ 1) :
    ∏ p ∈ (ArtinPrimitiveRoots.TypeII.primesUpTo z).filter
        (fun p : ℕ => 2 < p ∧ ¬ p ∣ r), (1 - pairSieveG W p) ≤
      8 * Real.exp (6 + 1 / 2) *
        ArtinPrimitiveRoots.TypeII.roughSieveProduct W ^ 2 *
          ArtinPrimitiveRoots.TypeII.roughSieveProduct z := by
  classical
  let All := ArtinPrimitiveRoots.TypeII.primesUpTo z
  let R := All.filter (fun p : ℕ => p ∣ r)
  let P := All.filter (fun p : ℕ => 2 < p ∧ ¬ p ∣ r)
  have hWnonneg : 0 ≤ W := by linarith
  have hZnonneg : 0 ≤ z := le_trans hWnonneg hWz
  have hmem (y : ℝ) (hy : 0 ≤ y) (p : ℕ) :
      p ∈ ArtinPrimitiveRoots.TypeII.primesUpTo y ↔ p.Prime ∧ (p : ℝ) ≤ y := by
    simp only [ArtinPrimitiveRoots.TypeII.primesUpTo, Finset.mem_filter,
      Finset.mem_range, Nat.lt_succ_iff, Nat.le_floor_iff hy]
    exact and_comm
  have h2All : 2 ∈ All := by
    dsimp [All]
    apply (hmem z hZnonneg 2).2
    exact ⟨Nat.prime_two, by exact_mod_cast (show (2 : ℝ) ≤ z by linarith)⟩
  have h2notR : 2 ∉ R := by
    intro h
    have hsize := hRprimeSize 2 h
    omega
  have hMissing : All \ P = insert 2 R := by
    ext p
    simp only [Finset.mem_sdiff, Finset.mem_insert]
    constructor
    · rintro ⟨hpAll, hpnot⟩
      by_cases hp2 : p = 2
      · exact Or.inl hp2
      · right
        have hpPrime : p.Prime := (hmem z hZnonneg p).mp (by simpa [All] using hpAll) |>.1
        have hpTwo : 2 < p := by
          have hpLower := hpPrime.two_le
          omega
        have hpdiv : p ∣ r := by
          by_contra hn
          apply hpnot
          change p ∈ All.filter (fun q : ℕ => 2 < q ∧ ¬ q ∣ r)
          exact Finset.mem_filter.mpr ⟨hpAll, ⟨hpTwo, hn⟩⟩
        change p ∈ All.filter (fun q : ℕ => q ∣ r)
        exact Finset.mem_filter.mpr ⟨hpAll, hpdiv⟩
    · rintro (hp2 | hpR)
      · subst p
        refine ⟨h2All, ?_⟩
        intro hpP
        change 2 ∈ All.filter (fun q : ℕ => 2 < q ∧ ¬ q ∣ r) at hpP
        have hpCond := (Finset.mem_filter.mp hpP).2
        omega
      · change p ∈ All.filter (fun q : ℕ => q ∣ r) at hpR
        have hpR' := Finset.mem_filter.mp hpR
        refine ⟨hpR'.1, ?_⟩
        intro hpP
        change p ∈ All.filter (fun q : ℕ => 2 < q ∧ ¬ q ∣ r) at hpP
        have hpCond := (Finset.mem_filter.mp hpP).2
        exact hpCond.2 hpR'.2
  have hmiss := pairSieveMissingFactor_bound All R W hW hRprimeSize
    (by simpa [All, R] using hRrecip)
  have hfactor : ∀ p ∈ P, 0 ≤ 1 - pairSieveG W p ∧
      1 - pairSieveG W p ≤ pairSieveBaseline W p * pairSieveCorrection W p := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpAll, ⟨hp2, _⟩⟩
    have hpprime : p.Prime := (hmem z hZnonneg p).mp hpAll |>.1
    exact pairSieveG_factor_le hpprime hp2 W
  have hbase : ∀ p ∈ All, 0 ≤ pairSieveBaseline W p := by
    intro p hp
    have hpprime : p.Prime := (hmem z hZnonneg p).mp hp |>.1
    have hpLower : 2 ≤ p := hpprime.two_le
    have hpcast : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpLower
    by_cases hpW : (p : ℝ) ≤ W
    · rw [pairSieveBaseline, if_pos hpW]
      have hfrac : 0 ≤ 1 - 1 / (p : ℝ) := by
        have hle : 1 / (p : ℝ) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
        linarith
      positivity
    · rw [pairSieveBaseline, if_neg hpW]
      have hpW' : (2 : ℝ) ≤ (p : ℝ) := hpcast
      have hfrac : 0 ≤ 1 - 1 / (p : ℝ) := by
        have hlt : 1 / (p : ℝ) < 1 := (div_lt_one (by linarith)).2 (by linarith)
        linarith
      exact hfrac
  have hcorr : ∀ p ∈ P, 0 ≤ pairSieveCorrection W p := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨_, ⟨hp2, _⟩⟩
    by_cases hpW : (p : ℝ) ≤ W
    · simp [pairSieveCorrection, hpW]
    · rw [pairSieveCorrection, if_neg hpW]
      have hden : 0 < (p : ℝ) * ((p : ℝ) - 1) := by
        have hpR : 2 < (p : ℝ) := by exact_mod_cast hp2
        exact mul_pos (by linarith) (by linarith)
      positivity
  have hcorrLe : ∏ p ∈ P, pairSieveCorrection W p ≤
      ∏ p ∈ P, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
    apply Finset.prod_le_prod₀
    · exact hcorr
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨_, ⟨hp2, _⟩⟩
      by_cases hpW : (p : ℝ) ≤ W
      · rw [pairSieveCorrection, if_pos hpW]
        have hpR : 2 < (p : ℝ) := by exact_mod_cast hp2
        have hden : 0 < (p : ℝ) * ((p : ℝ) - 1) :=
          mul_pos (by linarith) (by linarith)
        exact le_add_of_nonneg_right
          (div_nonneg (by norm_num) (le_of_lt hden))
      · rw [pairSieveCorrection, if_neg hpW]
  have hcorrBound : ∏ p ∈ P, pairSieveCorrection W p ≤ Real.exp (1 / 2) :=
    hcorrLe.trans (pairCorrectionProduct_le_half P (by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨_, ⟨hp2, _⟩⟩
    omega))
  have hmissPos : 0 < ∏ p ∈ All \ P, pairSieveBaseline W p := by
    rw [hMissing]
    exact hmiss.1
  have hmissInv : (∏ p ∈ All \ P, pairSieveBaseline W p)⁻¹ ≤ 8 * Real.exp 6 := by
    rw [hMissing]
    exact hmiss.2
  have hprod := pairSieveG_prod_le_of_missing_bound P All W
    (8 * Real.exp 6) (Real.exp (1 / 2)) (pairSieveG W)
    (by intro p hp; exact (Finset.mem_filter.mp hp).1)
    hfactor hbase hcorr hmissPos hmissInv hcorrBound (by positivity) (by positivity)
  have hbaseProduct := pairSieveBaselineProduct_eq W z hW hWz
  rw [hbaseProduct] at hprod
  have hexp : Real.exp 6 * Real.exp (1 / 2) = Real.exp (6 + 1 / 2) := by
    rw [← Real.exp_add]
  calc
    _ ≤ (8 * Real.exp 6) * Real.exp (1 / 2) *
        (ArtinPrimitiveRoots.TypeII.roughSieveProduct W ^ 2 *
          ArtinPrimitiveRoots.TypeII.roughSieveProduct z) := hprod
    _ = 8 * (Real.exp 6 * Real.exp (1 / 2)) *
          (ArtinPrimitiveRoots.TypeII.roughSieveProduct W ^ 2 *
            ArtinPrimitiveRoots.TypeII.roughSieveProduct z) := by ring
    _ = 8 * Real.exp (6 + 1 / 2) *
          (ArtinPrimitiveRoots.TypeII.roughSieveProduct W ^ 2 *
            ArtinPrimitiveRoots.TypeII.roughSieveProduct z) := by rw [hexp]
    _ = 8 * Real.exp (6 + 1 / 2) *
          ArtinPrimitiveRoots.TypeII.roughSieveProduct W ^ 2 *
            ArtinPrimitiveRoots.TypeII.roughSieveProduct z := by ring

theorem pairRpow_mul {x : ℝ} (hx : 0 < x) (a b : ℝ) :
    Real.rpow x a * Real.rpow x b = Real.rpow x (a + b) := by
  have hdef (t : ℝ) : Real.rpow x t = Real.exp (t * Real.log x) := by
    simpa [mul_comm] using Real.rpow_def_of_pos hx t
  rw [hdef a, hdef b, hdef (a + b), ← Real.exp_add]
  congr 1
  ring

theorem pairSieveLatticeErrors_scaled {k : ℕ} (P : Finset ℕ) (W H₁ H₂ x Y : ℝ)
    (hk : 0 < k) (hprime : ∀ p ∈ P, p.Prime)
    (hcopBase : ∀ p ∈ P, Nat.Coprime k p)
    (hH₁ : 2 ≤ H₁) (hH₂ : 2 ≤ H₂) (hY : 1 ≤ Y)
    (hx : 1 ≤ x)
    (hHsum : H₁ + H₂ ≤ 4 * Real.rpow x (54 / 100 : ℝ))
    (hkScale : (k : ℝ) ≤ 4 * Real.rpow x (11 / 100 : ℝ))
    (hYScale : Y ≤ Real.rpow x (2 / 100 : ℝ)) :
    Finset.sum (P.powerset.filter
        (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ Y))
      (fun D => pairSieveLatticeError P D W H₁ H₂ hk hprime hcopBase) ≤
      64 * Real.rpow x (54 / 100 : ℝ) * Real.rpow x (11 / 100 : ℝ) *
          (Real.rpow x (2 / 100 : ℝ)) ^ 2 +
        128 * (Real.rpow x (11 / 100 : ℝ)) ^ 2 *
          (Real.rpow x (2 / 100 : ℝ)) ^ 3 := by
  have hmain := pairSieveLatticeErrors_sum_le P W H₁ H₂ Y hk hprime hcopBase
    hH₁ hH₂ hY
  have hxnonneg : 0 ≤ x := le_trans (by norm_num) hx
  have hA : 0 ≤ Real.rpow x (54 / 100 : ℝ) := Real.rpow_nonneg hxnonneg _
  have hB : 0 ≤ Real.rpow x (11 / 100 : ℝ) := Real.rpow_nonneg hxnonneg _
  have hC : 0 ≤ Real.rpow x (2 / 100 : ℝ) := Real.rpow_nonneg hxnonneg _
  have hkNonneg : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  have hYnonneg : 0 ≤ Y := le_trans (by norm_num) hY
  have hxpos : 0 < x := by linarith
  have hC2 : (Real.rpow x (2 / 100 : ℝ)) ^ 2 =
      Real.rpow x (4 / 100 : ℝ) := by
    rw [pow_two]
    calc
      _ = Real.rpow x ((2 / 100 : ℝ) + (2 / 100 : ℝ)) :=
        pairRpow_mul hxpos (2 / 100 : ℝ) (2 / 100 : ℝ)
      _ = Real.rpow x (4 / 100 : ℝ) := by congr 1 <;> norm_num
  have hYsq : Y ^ 2 ≤ (Real.rpow x (2 / 100 : ℝ)) ^ 2 := by
    have h₁ := mul_le_mul_of_nonneg_right hYScale hYnonneg
    have h₂ := mul_le_mul_of_nonneg_left hYScale hC
    nlinarith
  have hYcube : Y ^ 3 ≤ (Real.rpow x (2 / 100 : ℝ)) ^ 3 := by
    have h₁ := mul_le_mul_of_nonneg_right hYsq hYnonneg
    have h₂ := mul_le_mul_of_nonneg_left hYScale (sq_nonneg (Real.rpow x (2 / 100 : ℝ)))
    nlinarith
  calc
    _ ≤ 4 * (H₁ + H₂) * (k : ℝ) * Y ^ 2 +
          8 * (k : ℝ) ^ 2 * Y ^ 3 :=
        hmain
    _ ≤ 4 * (4 * Real.rpow x (54 / 100 : ℝ)) *
          (4 * Real.rpow x (11 / 100 : ℝ)) *
            (Real.rpow x (2 / 100 : ℝ)) ^ 2 +
        8 * (4 * Real.rpow x (11 / 100 : ℝ)) ^ 2 *
          (Real.rpow x (2 / 100 : ℝ)) ^ 3 := by
      gcongr
    _ = 64 * Real.rpow x (54 / 100 : ℝ) * Real.rpow x (11 / 100 : ℝ) *
          (Real.rpow x (2 / 100 : ℝ)) ^ 2 +
        128 * (Real.rpow x (11 / 100 : ℝ)) ^ 2 *
          (Real.rpow x (2 / 100 : ℝ)) ^ 3 := by ring

theorem eventually_power_error_absorbed (C E : ℝ) (hC : 0 < C) (hE : 0 < E) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      C * Real.rpow x (69 / 100 : ℝ) ≤
        E * Real.rpow x (89 / 100 : ℝ) / Real.log x ^ 10 := by
  have hdecay : Tendsto
      (fun L : ℝ => Real.rpow L (10 : ℝ) * Real.exp (-(1 / 5 : ℝ) * L))
      atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (10 : ℝ) (1 / 5 : ℝ) (by norm_num)
  have hsmall : ∀ᶠ x : ℝ in atTop,
      Real.rpow (Real.log x) (10 : ℝ) *
        Real.exp (-(1 / 5 : ℝ) * Real.log x) < E / C := by
    have hdecayX := hdecay.comp Real.tendsto_log_atTop
    exact hdecayX.eventually (Iio_mem_nhds (div_pos hE hC))
  have hlarge : ∀ᶠ x : ℝ in atTop, 2 ≤ x := eventually_ge_atTop 2
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.mp (hsmall.and hlarge)
  let x₀ := max x₁ 2
  refine ⟨x₀, le_max_right _ _, ?_⟩
  intro x hx
  have hx1 : x₁ ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : 2 ≤ x := le_trans (le_max_right _ _) hx
  have hsmallX := (hx₁ x hx1).1
  have hxpos : 0 < x := by linarith
  have hLpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hxpowpos : 0 < Real.rpow x (89 / 100 : ℝ) := Real.rpow_pos_of_pos hxpos _
  have hpowExp : Real.rpow x (69 / 100 : ℝ) =
      Real.rpow x (89 / 100 : ℝ) * Real.exp (-(1 / 5 : ℝ) * Real.log x) := by
    calc
      Real.rpow x (69 / 100 : ℝ) =
          Real.rpow x ((89 / 100 : ℝ) + (-1 / 5 : ℝ)) := by congr 1 <;> norm_num
      _ = Real.rpow x (89 / 100 : ℝ) * Real.rpow x (-1 / 5 : ℝ) :=
        (pairRpow_mul hxpos (89 / 100 : ℝ) (-1 / 5 : ℝ)).symm
      _ = Real.rpow x (89 / 100 : ℝ) *
          Real.exp (-(1 / 5 : ℝ) * Real.log x) := by
            have hneg : Real.rpow x (-1 / 5 : ℝ) =
                Real.exp (Real.log x * (-1 / 5 : ℝ)) := by
              simpa using Real.rpow_def_of_pos hxpos (-1 / 5 : ℝ)
            rw [hneg]
            congr 1
            ring
  have hlogPow : Real.rpow (Real.log x) (10 : ℝ) = Real.log x ^ 10 := by
    exact Real.rpow_natCast (Real.log x) 10
  have hsmall' : Real.log x ^ 10 *
      Real.exp (-(1 / 5 : ℝ) * Real.log x) < E / C := by
    simpa [hlogPow] using hsmallX
  apply (le_div_iff₀ (by positivity : 0 < Real.log x ^ 10)).2
  have hstrict :
      C * Real.rpow x (69 / 100 : ℝ) * Real.log x ^ 10 <
        E * Real.rpow x (89 / 100 : ℝ) := calc
    C * Real.rpow x (69 / 100 : ℝ) * Real.log x ^ 10 =
        (C * Real.rpow x (89 / 100 : ℝ)) *
          (Real.log x ^ 10 * Real.exp (-(1 / 5 : ℝ) * Real.log x)) := by
            rw [hpowExp]
            ring
    _ < (C * Real.rpow x (89 / 100 : ℝ)) * (E / C) :=
      mul_lt_mul_of_pos_left hsmall' (mul_pos hC hxpowpos)
    _ = E * Real.rpow x (89 / 100 : ℝ) := by field_simp [ne_of_gt hC]
  exact le_of_lt hstrict

noncomputable def pairSieveBasePairs (H₁ H₂ : ℝ) (k : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((dyadicIntegers H₁).product (dyadicIntegers H₂)).filter fun mn : ℕ × ℕ =>
    (mn.1 : ZMod k) * (mn.2 : ZMod k) = 1

noncomputable def pairSieveSurvivors (H₁ H₂ : ℝ) (k : ℕ) (P : Finset ℕ)
    (W : ℝ) : Finset (ℕ × ℕ) := by
  classical
  exact (pairSieveBasePairs H₁ H₂ k).filter fun mn : ℕ × ℕ =>
    ∀ p ∈ P, ¬ localBadProductPredicate W p ((mn.1 : ZMod p), (mn.2 : ZMod p))

theorem pairSieveBlock_upper {k : ℕ} (P : Finset ℕ) (W H₁ H₂ z η C₀ : ℝ)
    (hk : 0 < k) (hprime : ∀ p ∈ P, p.Prime) (hcopBase : ∀ p ∈ P, Nat.Coprime k p)
    (hz : 2 ≤ z) (hPz : ∀ p ∈ P, (p : ℝ) ≤ z)
    (hH₁ : 2 ≤ H₁) (hH₂ : 2 ≤ H₂)
    (hη : 0 < η) (hC₀ : 0 < C₀)
    (hgbounds : ∀ p ∈ P, 0 ≤ pairSieveG W p ∧ pairSieveG W p ≤ 1 - η)
    (hblock : ∀ v : ℝ, 1 < v →
      ∑ p ∈ P.filter (fun p : ℕ => v < (p : ℝ) ∧ (p : ℝ) ≤ v ^ 2),
        pairSieveG W p ≤ C₀) :
    ∃ K : ℝ, 0 < K ∧
      (pairSieveSurvivors H₁ H₂ k P W).card ≤
        K * ((H₁ * H₂ * (Nat.totient k : ℝ) / (k : ℝ) ^ 2) *
          ∏ p ∈ P, (1 - pairSieveG W p)) +
        K * ∑ D ∈ P.powerset.filter
          (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ z ^ 10),
            pairSieveLatticeError P D W H₁ H₂ hk hprime hcopBase := by
  classical
  let A := pairSieveBasePairs H₁ H₂ k
  let bad : ℕ → ℕ × ℕ → Prop := fun p mn =>
    localBadProductPredicate W p ((mn.1 : ZMod p), (mn.2 : ZMod p))
  let X' : ℝ := H₁ * H₂ * (Nat.totient k : ℝ) / (k : ℝ) ^ 2
  have hX' : 0 ≤ X' := by dsimp [X']; positivity
  have hwt : ∀ mn ∈ A, (0 : ℝ) ≤ (1 : ℝ) := by intro; norm_num
  have hErr : ∀ D ∈ P.powerset.filter
      (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ z ^ 10),
      |(∑ mn ∈ A with ∀ p ∈ D, bad p mn, (1 : ℝ)) -
          X' * ∏ p ∈ D, pairSieveG W p| ≤
        pairSieveLatticeError P D W H₁ H₂ hk hprime hcopBase := by
    intro D hD
    have hDP : D ⊆ P := Finset.mem_powerset.mp (Finset.mem_filter.mp hD).1
    have hprimeD : ∀ p ∈ D, p.Prime := fun p hp => hprime p (hDP hp)
    have hcopD : ∀ p ∈ D, Nat.Coprime k p := fun p hp => hcopBase p (hDP hp)
    have hpos := pairSieveModuli_positive D hk hprimeD
    let q := ∏ i : PairSieveIndex D, pairSieveModulus k D i
    letI : NeZero q := ⟨Nat.ne_of_gt hpos.2⟩
    letI : ∀ i : PairSieveIndex D, NeZero (pairSieveModulus k D i) :=
      fun i => ⟨Nat.ne_of_gt (hpos.1 i)⟩
    have hfilter : A.filter (fun mn : ℕ × ℕ => ∀ p ∈ D, bad p mn) =
        pairSieveIntersectionPairs H₁ H₂ k D W := by
      ext mn
      simp [A, bad, pairSieveBasePairs, pairSieveIntersectionPairs,
        Finset.mem_filter, Finset.mem_product, and_assoc]
    have hsum : (∑ mn ∈ A with ∀ p ∈ D, bad p mn, (1 : ℝ)) =
        (pairSieveIntersectionPairs H₁ H₂ k D W).card := by
      rw [Finset.sum_filter]
      simp [hfilter]
    have hcount :
        (pairSieveIntersectionPairs H₁ H₂ k D W).card =
          dyadicPairResidueClassCount H₁ H₂ q
            (pairSieveResidues D W hprimeD hcopD) := by
      simpa [q, pairSieveIntersectionPairs] using
        pairSieveIntersection_card_eq D W H₁ H₂ hprimeD hcopD
    have hmain := pairSieveMainTerm_eq D W H₁ H₂ hk hprimeD hcopD
    have hlat : pairSieveLatticeError P D W H₁ H₂ hk hprime hcopBase =
        |(pairSieveIntersectionPairs H₁ H₂ k D W).card -
          X' * ∏ p ∈ D, pairSieveG W p| := by
      rw [pairSieveLatticeError]
      simp only [hDP, ↓reduceDIte]
      dsimp [q] at hcount hmain ⊢
      rw [hcount]
      rw [hmain]
    rw [hsum, hlat]
  obtain ⟨K, hK, hbound⟩ := blockSieve_upper_of_error_bound
    A (fun _ : ℕ × ℕ => (1 : ℝ)) P bad X' z η C₀ (fun p => pairSieveG W p)
      (fun D => pairSieveLatticeError P D W H₁ H₂ hk hprime hcopBase)
      hwt hz (by intro p hp; exact ⟨hprime p hp, hPz p hp⟩) hX' hη hC₀
      hgbounds hblock hErr
  refine ⟨K, hK, ?_⟩
  have hsurvivors :
      (∑ mn ∈ A with ∀ p ∈ P, ¬ bad p mn, (1 : ℝ)) =
        (pairSieveSurvivors H₁ H₂ k P W).card := by
    rw [Finset.sum_filter]
    have hset : A.filter (fun mn : ℕ × ℕ => ∀ p ∈ P, ¬ bad p mn) =
        pairSieveSurvivors H₁ H₂ k P W := by
      ext mn
      simp [A, bad, pairSieveSurvivors, pairSieveBasePairs]
    simp [hset]
  simpa [hsurvivors, A, bad, X'] using hbound

end ArtinPrimitiveRoots.Construction.Proofs.C4
