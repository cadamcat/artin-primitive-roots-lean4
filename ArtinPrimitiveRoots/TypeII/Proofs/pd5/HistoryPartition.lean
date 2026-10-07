import ArtinPrimitiveRoots.TypeII.PD.Memory
import ArtinPrimitiveRoots.TypeII.Proofs.pd5.Partition

set_option autoImplicit false
set_option linter.unusedVariables false

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical

noncomputable section

def pd5_constraintWeightSum {K : ℕ} (A : Finset (BirthAddress K))
    (log : BirthLog K) : ℂ :=
  ∑ C ∈ constraintSystems A, (constraintCoeff C : ℂ) * constraintWeight C log

theorem pd5_envBox_finite {S : PDScale} {w : ArchRoot}
    (hU : 0 < S.U) (hV : 0 < S.V) (hu : 0 < w.u) (hv : 0 < w.v)
    (hr0 : 0 ≤ w.r) (hr1 : w.r ≤ 1) :
    {z : ℤ × ℤ | envBox S w z}.Finite := by
  classical
  let B₂ : ℝ := 2 * w.u * S.V + 16 * w.v * S.U
  let B₁ : ℝ := 16 * S.U / w.u + B₂
  have hB₂ : 0 ≤ B₂ := by positivity
  have hB₁ : 0 ≤ B₁ := by positivity
  let T₂ : ℕ := ⌈B₂⌉₊
  let T₁ : ℕ := ⌈B₁⌉₊
  have hceil₂ : B₂ ≤ (T₂ : ℝ) := by
    dsimp [T₂]
    exact Nat.le_ceil B₂
  have hceil₁ : B₁ ≤ (T₁ : ℝ) := by
    dsimp [T₁]
    exact Nat.le_ceil B₁
  have hsub : {z : ℤ × ℤ | envBox S w z} ⊆
      Set.Icc (-(T₁ : ℤ)) (T₁ : ℤ) ×ˢ Set.Icc (-(T₂ : ℤ)) (T₂ : ℤ) := by
    intro z hz
    rcases hz with ⟨hbox₁, hbox₂, hbox₃, hbox₄⟩
    have hτlo : S.U / w.u ≤ w.tau z :=
      (div_le_iff₀ hu).2 (by simpa [mul_comm] using hbox₁)
    have hτhi : w.tau z ≤ 16 * S.U / w.u :=
      (le_div_iff₀ hu).2 (by simpa [mul_comm] using hbox₂)
    have hτpos : 0 < w.tau z := lt_of_lt_of_le (div_pos hU hu) hτlo
    have hlowDiv : S.V - w.v * w.tau z ≤ (z.2 : ℝ) / w.u := by linarith
    have hlow := (le_div_iff₀ hu).1 hlowDiv
    have hscale := mul_le_mul_of_nonneg_left hbox₂ hv.le
    have hz₂lo : w.u * S.V - 16 * w.v * S.U ≤ (z.2 : ℝ) := by
      nlinarith [hlow, hscale]
    have hhighMul := mul_le_mul_of_nonneg_left hbox₄ hu.le
    have hdiv : w.u * ((z.2 : ℝ) / w.u) = (z.2 : ℝ) := by
      field_simp [ne_of_gt hu]
    have hprodNonneg : 0 ≤ w.u * (w.v * w.tau z) :=
      mul_nonneg hu.le (mul_nonneg hv.le hτpos.le)
    have hz₂hi : (z.2 : ℝ) ≤ 2 * w.u * S.V := by
      nlinarith [hhighMul, hdiv, hprodNonneg]
    have hz₂abs : |(z.2 : ℝ)| ≤ B₂ := by
      rw [abs_le]
      constructor <;> dsimp [B₂] <;> linarith
    have hrabs : |w.r| ≤ 1 := by
      rw [abs_le]
      exact ⟨by linarith, hr1⟩
    have hrz : |w.r * (z.2 : ℝ)| ≤ |(z.2 : ℝ)| := by
      calc
        |w.r * (z.2 : ℝ)| = |w.r| * |(z.2 : ℝ)| := abs_mul _ _
        _ ≤ 1 * |(z.2 : ℝ)| := mul_le_mul_of_nonneg_right hrabs (abs_nonneg _)
        _ = |(z.2 : ℝ)| := one_mul _
    have hz₁eq : (z.1 : ℝ) = w.tau z - w.r * (z.2 : ℝ) := by
      dsimp [ArchRoot.tau]
      ring
    have hz₁abs : |(z.1 : ℝ)| ≤ B₁ := by
      calc
        |(z.1 : ℝ)| = |w.tau z - w.r * (z.2 : ℝ)| := by rw [hz₁eq]
        _ ≤ |w.tau z| + |w.r * (z.2 : ℝ)| := by
          calc
            |w.tau z - w.r * (z.2 : ℝ)| = |w.tau z + -(w.r * (z.2 : ℝ))| := by congr 1 <;> ring
            _ ≤ |w.tau z| + |-(w.r * (z.2 : ℝ))| := abs_add_le _ _
            _ = |w.tau z| + |w.r * (z.2 : ℝ)| := by simp
        _ ≤ 16 * S.U / w.u + B₂ := by
          rw [abs_of_pos hτpos]
          exact add_le_add hτhi (hrz.trans hz₂abs)
        _ = B₁ := by rfl
    have hz₁le : |(z.1 : ℝ)| ≤ (T₁ : ℝ) := hz₁abs.trans hceil₁
    have hz₂le : |(z.2 : ℝ)| ≤ (T₂ : ℝ) := hz₂abs.trans hceil₂
    have hz₁bounds := abs_le.mp hz₁le
    have hz₂bounds := abs_le.mp hz₂le
    refine ⟨?_, ?_⟩
    · constructor
      · exact_mod_cast hz₁bounds.1
      · exact_mod_cast hz₁bounds.2
    · constructor
      · exact_mod_cast hz₂bounds.1
      · exact_mod_cast hz₂bounds.2
  exact (Set.Finite.prod (Set.finite_Icc _ _) (Set.finite_Icc _ _)).subset hsub

theorem pd5_envBox_finite_of_valid {K : ℕ} {δ c₁ c₂ : ℝ}
    {S : PDScale} {w : ArchRoot} (hS : S.Valid K δ c₁ c₂) (hw : w.InRegion S) :
    {z : ℤ × ℤ | envBox S w z}.Finite := by
  classical
  rcases hS with ⟨hx, hHm, hHn, _, _, hY, hd₀⟩
  rcases Finset.mem_filter.mp hY with ⟨hYimage, _⟩
  rcases Finset.mem_image.mp hYimage with ⟨k, hk, hYeq⟩
  have hYpos : 0 < S.Y := by rw [← hYeq]; positivity
  rcases Finset.mem_image.mp hd₀ with ⟨k₀, hk₀, hd₀eq⟩
  have hd₀pos : 0 < (S.d₀ : ℝ) := by
    rw [← hd₀eq]
    exact_mod_cast (Nat.pow_pos (by norm_num : 0 < 2))
  have hxpos : 0 < S.x := by linarith
  have hHmpos : 0 < S.Hm :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hxpos _) hHm
  have hHnpos : 0 < S.Hn :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hxpos _) hHn
  have hU : 0 < S.U := by
    rw [PDScale.U, PDScale.H]
    exact mul_pos (mul_pos hd₀pos hYpos) hHmpos
  have hV : 0 < S.V := by
    rw [PDScale.V]
    exact hHnpos
  rcases hw with ⟨hu, _, hv, _, hr0, hr1⟩
  exact pd5_envBox_finite hU hV (lt_of_lt_of_le hU hu) (lt_of_lt_of_le hV hv) hr0 hr1

theorem pd5_scale_counting_bounds {S : PDScale} (hL : 1 ≤ S.L) :
    (S.M : ℝ) ≤ 2 * Real.rpow S.L (1 / 100 : ℝ) ∧
    (S.N : ℝ) ≤ Real.rpow S.L (1 / 2 : ℝ) + 2 ∧
    Real.rpow S.L (1 / 2 : ℝ) ≤ S.N ∧
    (memoryCutoff S : ℝ) ≤ 2 * S.L ^ 2 := by
  have hLpos : 0 < S.L := lt_of_lt_of_le (by norm_num) hL
  have hLnonneg : 0 ≤ S.L := le_trans (by norm_num) hL
  have hslotPow : 1 ≤ Real.rpow S.L (1 / 100 : ℝ) := by
    calc
      1 = Real.rpow S.L 0 := by simp
      _ ≤ Real.rpow S.L (1 / 100 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have hfloor : (momentJ S.x : ℝ) ≤ Real.rpow S.L (1 / 100 : ℝ) := by
    dsimp [momentJ, PDScale.L]
    exact Nat.floor_le (Real.rpow_nonneg hLnonneg _)
  have hM : (S.M : ℝ) ≤ Real.rpow S.L (1 / 100 : ℝ) + 1 := by
    simp only [PDScale.M, slotCount, Nat.cast_add, Nat.cast_one]
    exact add_le_add hfloor le_rfl
  have hceil : (momentR S.x : ℝ) <
      Real.rpow S.L (1 / 2 : ℝ) / 2 + 1 := by
    dsimp [momentR, PDScale.L]
    exact Nat.ceil_lt_add_one
      (div_nonneg (Real.rpow_nonneg hLnonneg _) (by norm_num))
  have hNupper : (S.N : ℝ) ≤ Real.rpow S.L (1 / 2 : ℝ) + 2 := by
    have hpath : (S.N : ℝ) = 2 * (momentR S.x : ℝ) := by
      simp [PDScale.N, pathLength]
    rw [hpath]
    nlinarith
  have hceilLower : Real.rpow S.L (1 / 2 : ℝ) / 2 ≤ momentR S.x := by
    dsimp [momentR, PDScale.L]
    exact Nat.le_ceil _
  have hNlower : Real.rpow S.L (1 / 2 : ℝ) ≤ S.N := by
    have hpath : (S.N : ℝ) = 2 * (momentR S.x : ℝ) := by
      simp [PDScale.N, pathLength]
    rw [hpath]
    nlinarith
  have hBceil : (memoryCutoff S : ℝ) <
      Real.rpow S.L 2 + 1 := by
    dsimp [memoryCutoff]
    exact Nat.ceil_lt_add_one (Real.rpow_nonneg hLnonneg _)
  have hpow2 : Real.rpow S.L 2 = S.L ^ 2 := by
    rw [← Real.rpow_natCast]
    norm_num
  refine ⟨?_, hNupper, hNlower, ?_⟩
  · nlinarith
  · rw [hpow2] at hBceil
    nlinarith [hL]

theorem pd5_birthAddresses_card_le {x : ℝ} (K B : ℕ) :
    (birthAddresses x K B).card ≤
      K * slotCount x + K * pathLength x + K * (pathLength x + 1) * B := by
  classical
  let I : Finset (BirthAddress K) :=
    (Finset.univ ×ˢ Finset.range (slotCount x)).image fun p =>
      BirthAddress.initial p.1 p.2
  let E : Finset (BirthAddress K) :=
    (Finset.range (pathLength x) ×ˢ Finset.univ).image fun p =>
      BirthAddress.edge p.1 p.2
  let G : Finset (BirthAddress K) :=
    (Finset.range (pathLength x + 1) ×ˢ (Finset.univ ×ˢ Finset.range B)).image fun p =>
      BirthAddress.ghost p.1 p.2.1 p.2.2
  have hI : I.card ≤ K * slotCount x := by
    dsimp [I]
    calc
      _ ≤ (Finset.univ ×ˢ Finset.range (slotCount x)).card := Finset.card_image_le
      _ = K * slotCount x := by simp
  have hE : E.card ≤ K * pathLength x := by
    dsimp [E]
    calc
      _ ≤ (Finset.range (pathLength x) ×ˢ Finset.univ).card := Finset.card_image_le
      _ = K * pathLength x := by simp [Nat.mul_comm]
  have hG : G.card ≤ K * (pathLength x + 1) * B := by
    dsimp [G]
    calc
      _ ≤ (Finset.range (pathLength x + 1) ×ˢ
          (Finset.univ ×ˢ Finset.range B)).card := Finset.card_image_le
      _ = K * (pathLength x + 1) * B := by
        simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  change ((I ∪ E) ∪ G).card ≤ _
  calc
    ((I ∪ E) ∪ G).card ≤ (I ∪ E).card + G.card := Finset.card_union_le _ _
    _ ≤ I.card + E.card + G.card := by
      have hIE := Finset.card_union_le I E
      omega
    _ ≤ K * slotCount x + K * pathLength x + K * (pathLength x + 1) * B := by
      omega

noncomputable def pd5_edgeChoiceMass {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (i : Fin K) : ℝ :=
  edgeNewMemory.match_1 F S s i (fun _ => ℝ) (c i).2
    (fun _ => (bandMass S.x (F.a i))⁻¹)
    (fun p => memoryNu S.x K F.a F.q_d i p)

theorem pd5_logEdgePiece_finite {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (step : ℕ) (raw : Bool) (St Pr : Finset (Fin K))
    (f : LogPoint S.x K → ℂ) (σL : LogPoint S.x K)
    (hbox : {z : ℤ × ℤ | envBox S w z}.Finite) :
    logEdgePiece F S ρ w step raw St Pr f σL =
      ∑ c : (i : Fin K) → EdgeChoice S.x F.a (σL.1.2.2 i) i,
        ∑ z' ∈ hbox.toFinset,
          if edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧
              EdgeAdmissible F S w σL.1 c z' then
            have mem' := edgeNewMemory F S σL.1 c
            ((ρ ^ (∑ i : Fin K, hitCount (σL.1.2.2 i) σL.1.1) *
                (∏ i : Fin K, pd5_edgeChoiceMass F S σL.1 c i) *
                ρ ^ (∑ i : Fin K, hitCount (mem' i) z') : ℝ) : ℂ) *
              edgeMultiplier F S (decide (step % 2 = 0)) raw σL.1.2.1
                (edgeTargetLists F S σL.1 c) σL.1.1 z' *
              f ((z', edgeTargetLists F S σL.1 c, mem'),
                σL.2 ++ edgeBirths F S step σL.1 c)
          else 0 := by
  classical
  unfold logEdgePiece
  refine Finset.sum_congr rfl ?_
  intro c hc
  refine (tsum_eq_sum (L := SummationFilter.unconditional (ℤ × ℤ))
    (s := hbox.toFinset) ?_).trans ?_
  · intro z hz
    by_cases hcond : edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧
        EdgeAdmissible F S w σL.1 c z
    · simp only [if_pos hcond]
      rcases hcond.2.2 with ⟨_, _, _, _, _, _, _, hzBox, _, _⟩
      exact (hz (hbox.mem_toFinset.mpr hzBox)).elim
    · simp [hcond]
  · apply Finset.sum_congr rfl
    intro z hz
    by_cases hcond : edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧
        EdgeAdmissible F S w σL.1 c z
    · simp only [if_pos hcond]
      simp [pd5_edgeChoiceMass]
    · simp only [if_neg hcond]

theorem pd5_logEdgePiece_finsetSum {K : ℕ} {ι : Type*} [DecidableEq ι]
    (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot) (step : ℕ)
    (raw : Bool) (St Pr : Finset (Fin K)) (T : Finset ι) (a : ι → ℂ)
    (g : ι → LogPoint S.x K → ℂ) (σL : LogPoint S.x K)
    (hbox : {z : ℤ × ℤ | envBox S w z}.Finite) :
    logEdgePiece F S ρ w step raw St Pr (fun τL => ∑ i ∈ T, a i * g i τL) σL =
      ∑ i ∈ T, a i * logEdgePiece F S ρ w step raw St Pr (g i) σL := by
  classical
  rw [pd5_logEdgePiece_finite F S ρ w step raw St Pr
    (fun τL => ∑ i ∈ T, a i * g i τL) σL hbox]
  calc
    (∑ c : (i : Fin K) → EdgeChoice S.x F.a (σL.1.2.2 i) i,
      ∑ z' ∈ hbox.toFinset,
        if edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧
            EdgeAdmissible F S w σL.1 c z' then
          have mem' := edgeNewMemory F S σL.1 c
          ((ρ ^ (∑ i : Fin K, hitCount (σL.1.2.2 i) σL.1.1) *
              (∏ i : Fin K, pd5_edgeChoiceMass F S σL.1 c i) *
              ρ ^ (∑ i : Fin K, hitCount (mem' i) z') : ℝ) : ℂ) *
            edgeMultiplier F S (decide (step % 2 = 0)) raw σL.1.2.1
              (edgeTargetLists F S σL.1 c) σL.1.1 z' *
            (∑ i ∈ T, a i * g i ((z', edgeTargetLists F S σL.1 c, mem'),
              σL.2 ++ edgeBirths F S step σL.1 c))
        else 0) =
      ∑ c : (i : Fin K) → EdgeChoice S.x F.a (σL.1.2.2 i) i,
        ∑ z' ∈ hbox.toFinset, ∑ i ∈ T,
          a i * (if edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧
            EdgeAdmissible F S w σL.1 c z' then
            have mem' := edgeNewMemory F S σL.1 c
            ((ρ ^ (∑ i : Fin K, hitCount (σL.1.2.2 i) σL.1.1) *
                (∏ i : Fin K, pd5_edgeChoiceMass F S σL.1 c i) *
                ρ ^ (∑ i : Fin K, hitCount (mem' i) z') : ℝ) : ℂ) *
              edgeMultiplier F S (decide (step % 2 = 0)) raw σL.1.2.1
                (edgeTargetLists F S σL.1 c) σL.1.1 z' *
              g i ((z', edgeTargetLists F S σL.1 c, mem'),
                σL.2 ++ edgeBirths F S step σL.1 c)
          else 0) := by
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hcond : edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧
          EdgeAdmissible F S w σL.1 c z
      · simp only [if_pos hcond]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      · simp [hcond]
    _ = ∑ c : (j : Fin K) → EdgeChoice S.x F.a (σL.1.2.2 j) j,
          ∑ i ∈ T, ∑ z' ∈ hbox.toFinset,
            a i * (if edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧
                EdgeAdmissible F S w σL.1 c z' then
              have mem' := edgeNewMemory F S σL.1 c
              ((ρ ^ (∑ j : Fin K, hitCount (σL.1.2.2 j) σL.1.1) *
                  (∏ j : Fin K, pd5_edgeChoiceMass F S σL.1 c j) *
                  ρ ^ (∑ j : Fin K, hitCount (mem' j) z') : ℝ) : ℂ) *
                edgeMultiplier F S (decide (step % 2 = 0)) raw σL.1.2.1
                  (edgeTargetLists F S σL.1 c) σL.1.1 z' *
                g i ((z', edgeTargetLists F S σL.1 c, mem'),
                  σL.2 ++ edgeBirths F S step σL.1 c)
            else 0) := by
          apply Finset.sum_congr rfl
          intro c hc
          rw [Finset.sum_comm]
    _ = ∑ i ∈ T,
          ∑ c : (j : Fin K) → EdgeChoice S.x F.a (σL.1.2.2 j) j,
            ∑ z' ∈ hbox.toFinset,
              a i * (if edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧
                  EdgeAdmissible F S w σL.1 c z' then
                have mem' := edgeNewMemory F S σL.1 c
                ((ρ ^ (∑ j : Fin K, hitCount (σL.1.2.2 j) σL.1.1) *
                    (∏ j : Fin K, pd5_edgeChoiceMass F S σL.1 c j) *
                    ρ ^ (∑ j : Fin K, hitCount (mem' j) z') : ℝ) : ℂ) *
                  edgeMultiplier F S (decide (step % 2 = 0)) raw σL.1.2.1
                    (edgeTargetLists F S σL.1 c) σL.1.1 z' *
                  g i ((z', edgeTargetLists F S σL.1 c, mem'),
                    σL.2 ++ edgeBirths F S step σL.1 c)
              else 0) := by
          rw [Finset.sum_comm]
    _ = ∑ i ∈ T, a i *
          ∑ c : (j : Fin K) → EdgeChoice S.x F.a (σL.1.2.2 j) j,
            ∑ z' ∈ hbox.toFinset,
              (if edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧
                  EdgeAdmissible F S w σL.1 c z' then
                have mem' := edgeNewMemory F S σL.1 c
                ((ρ ^ (∑ j : Fin K, hitCount (σL.1.2.2 j) σL.1.1) *
                    (∏ j : Fin K, pd5_edgeChoiceMass F S σL.1 c j) *
                    ρ ^ (∑ j : Fin K, hitCount (mem' j) z') : ℝ) : ℂ) *
                  edgeMultiplier F S (decide (step % 2 = 0)) raw σL.1.2.1
                    (edgeTargetLists F S σL.1 c) σL.1.1 z' *
                  g i ((z', edgeTargetLists F S σL.1 c, mem'),
                    σL.2 ++ edgeBirths F S step σL.1 c)
              else 0) := by
          apply Finset.sum_congr rfl
          intro i hi
          simp_rw [← Finset.mul_sum]
    _ = ∑ i ∈ T, a i * logEdgePiece F S ρ w step raw St Pr (g i) σL := by
          congr 1
          funext i
          rw [pd5_logEdgePiece_finite F S ρ w step raw St Pr
            (g i) σL hbox]

theorem pd5_logSym_finsetSum {K : ℕ} {ι : Type*} [DecidableEq ι]
    (F : PDFix K) (S : PDScale) (T : Finset ι) (a : ι → ℂ)
    (g : ι → LogPoint S.x K → ℂ) (σL : LogPoint S.x K) :
    logSym F S (fun τL => ∑ i ∈ T, a i * g i τL) σL =
      ∑ i ∈ T, a i * logSym F S (g i) σL := by
  classical
  unfold logSym
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.mul_sum]
  ring

theorem pd5_logEdgeFullInner_finsetSum {K : ℕ} {ι : Type*} [DecidableEq ι]
    (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot) (step : ℕ)
    (T : Finset ι) (a : ι → ℂ) (g : ι → LogPoint S.x K → ℂ)
    (σL : LogPoint S.x K) (hbox : {z : ℤ × ℤ | envBox S w z}.Finite) :
    (∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
      (logEdgePiece F S ρ w step true St Pr
          (logSym F S (fun τL => ∑ i ∈ T, a i * g i τL)) σL -
        logEdgePiece F S ρ w step false St Pr
          (logSym F S (fun τL => ∑ i ∈ T, a i * g i τL)) σL)) =
      ∑ i ∈ T, a i *
        ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
          (logEdgePiece F S ρ w step true St Pr (logSym F S (g i)) σL -
            logEdgePiece F S ρ w step false St Pr (logSym F S (g i)) σL) := by
  classical
  have hSym : logSym F S (fun τL => ∑ i ∈ T, a i * g i τL) =
      fun τL => ∑ i ∈ T, a i * logSym F S (g i) τL := by
    funext τL
    exact pd5_logSym_finsetSum F S T a g τL
  rw [hSym]
  have hRaw (St Pr : Finset (Fin K)) :
      logEdgePiece F S ρ w step true St Pr
          (fun τL => ∑ i ∈ T, a i * logSym F S (g i) τL) σL =
        ∑ i ∈ T, a i * logEdgePiece F S ρ w step true St Pr
          (logSym F S (g i)) σL := by
    exact pd5_logEdgePiece_finsetSum F S ρ w step true St Pr T a
      (fun i τL => logSym F S (g i) τL) σL hbox
  have hCmp (St Pr : Finset (Fin K)) :
      logEdgePiece F S ρ w step false St Pr
          (fun τL => ∑ i ∈ T, a i * logSym F S (g i) τL) σL =
        ∑ i ∈ T, a i * logEdgePiece F S ρ w step false St Pr
          (logSym F S (g i)) σL := by
    exact pd5_logEdgePiece_finsetSum F S ρ w step false St Pr T a
      (fun i τL => logSym F S (g i) τL) σL hbox
  calc
    _ = ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
          ∑ i ∈ T, a i *
            (logEdgePiece F S ρ w step true St Pr (logSym F S (g i)) σL -
              logEdgePiece F S ρ w step false St Pr (logSym F S (g i)) σL) := by
          apply Finset.sum_congr rfl
          intro St hSt
          apply Finset.sum_congr rfl
          intro Pr hPr
          rw [hRaw, hCmp, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = ∑ St : Finset (Fin K), ∑ i ∈ T, ∑ Pr : Finset (Fin K),
          a i *
            (logEdgePiece F S ρ w step true St Pr (logSym F S (g i)) σL -
              logEdgePiece F S ρ w step false St Pr (logSym F S (g i)) σL) := by
          apply Finset.sum_congr rfl
          intro St hSt
          rw [Finset.sum_comm]
    _ = ∑ i ∈ T, ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
          a i *
            (logEdgePiece F S ρ w step true St Pr (logSym F S (g i)) σL -
              logEdgePiece F S ρ w step false St Pr (logSym F S (g i)) σL) := by
          rw [Finset.sum_comm]
    _ = ∑ i ∈ T, a i *
          ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
            (logEdgePiece F S ρ w step true St Pr (logSym F S (g i)) σL -
              logEdgePiece F S ρ w step false St Pr (logSym F S (g i)) σL) := by
          apply Finset.sum_congr rfl
          intro i hi
          simp_rw [← Finset.mul_sum]

theorem pd5_logEdge_full_finsetSum {K : ℕ} {ι : Type*} [DecidableEq ι]
    (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot) (step : ℕ)
    (T : Finset ι) (a : ι → ℂ) (g : ι → LogPoint S.x K → ℂ)
    (hbox : {z : ℤ × ℤ | envBox S w z}.Finite) (σL : LogPoint S.x K) :
    logEdge F S ρ w EdgeKind.full step (fun τL => ∑ i ∈ T, a i * g i τL) σL =
      ∑ i ∈ T, a i * logEdge F S ρ w EdgeKind.full step (g i) σL := by
  classical
  have hInner :
      (fun τL => ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
        (logEdgePiece F S ρ w step true St Pr
            (logSym F S (fun ξL => ∑ i ∈ T, a i * g i ξL)) τL -
          logEdgePiece F S ρ w step false St Pr
            (logSym F S (fun ξL => ∑ i ∈ T, a i * g i ξL)) τL)) =
      (fun τL => ∑ i ∈ T, a i *
        ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
          (logEdgePiece F S ρ w step true St Pr (logSym F S (g i)) τL -
            logEdgePiece F S ρ w step false St Pr (logSym F S (g i)) τL)) := by
    funext τL
    exact pd5_logEdgeFullInner_finsetSum F S ρ w step T a g τL hbox
  simp only [logEdge, EdgeKind.full]
  rw [hInner]
  exact pd5_logSym_finsetSum F S T a
    (fun i τL => ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
      (logEdgePiece F S ρ w step true St Pr (logSym F S (g i)) τL -
        logEdgePiece F S ρ w step false St Pr (logSym F S (g i)) τL)) σL

theorem pd5_logEdge_full_finsetSumFun {K : ℕ} {ι : Type*} [DecidableEq ι]
    (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot) (step : ℕ)
    (T : Finset ι) (a : ι → ℂ) (g : ι → LogPoint S.x K → ℂ)
    (hbox : {z : ℤ × ℤ | envBox S w z}.Finite) :
    logEdge F S ρ w EdgeKind.full step (fun τL => ∑ i ∈ T, a i * g i τL) =
      fun σL => ∑ i ∈ T, a i * logEdge F S ρ w EdgeKind.full step (g i) σL := by
  funext σL
  exact pd5_logEdge_full_finsetSum F S ρ w step T a g hbox σL

def pd5_prefixAddress {K : ℕ} (B edgeBound ghostBound : ℕ) :
    BirthAddress K → Prop
  | .initial _ _ => True
  | .edge step _ => step < edgeBound
  | .ghost step _ k => step < ghostBound ∧ k < B

def pd5_logPrefixGood {K : ℕ} (x : ℝ) (B edgeBound ghostBound : ℕ)
    (log : BirthLog K) : Prop :=
  (log.map Prod.fst).Nodup ∧
    ∀ e ∈ log, pd5_prefixAddress B edgeBound ghostBound e.1 ∧
      e.1 ∈ birthAddresses x K B

noncomputable def pd5_boundedLengths (K B : ℕ) : Finset (Fin K → ℕ) :=
  (Finset.univ : Finset (Fin K → Fin (B + 1))).image fun l i => (l i).val

theorem pd5_mem_boundedLengths {K B : ℕ} {l : Fin K → ℕ} :
    l ∈ pd5_boundedLengths K B ↔ ∀ i, l i ≤ B := by
  classical
  simp only [pd5_boundedLengths, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨f, rfl⟩ i
    exact Nat.le_of_lt_succ (f i).isLt
  · intro h
    refine ⟨fun i => ⟨l i, Nat.lt_succ_of_le (h i)⟩, rfl⟩

theorem pd5_prefixAddress_mono {K : ℕ} {B e₁ g₁ e₂ g₂ : ℕ}
    (he : e₁ ≤ e₂) (hg : g₁ ≤ g₂) {a : BirthAddress K}
    (ha : pd5_prefixAddress B e₁ g₁ a) : pd5_prefixAddress B e₂ g₂ a := by
  cases a with
  | initial i j => trivial
  | edge step i => exact lt_of_lt_of_le ha he
  | ghost step i k => exact ⟨lt_of_lt_of_le ha.1 hg, ha.2⟩

theorem pd5_logPrefixGood_append {K : ℕ} {x : ℝ} {B e₁ g₁ e₂ g₂ : ℕ}
    {L₁ L₂ : BirthLog K}
    (hL : pd5_logPrefixGood x B e₁ g₁ L₁)
    (hN₂ : (L₂.map Prod.fst).Nodup)
    (hAddr₂ : ∀ e ∈ L₂, pd5_prefixAddress B e₂ g₂ e.1 ∧
      e.1 ∈ birthAddresses x K B)
    (hDisjoint : ∀ a ∈ L₁.map Prod.fst, ∀ b ∈ L₂.map Prod.fst, a ≠ b)
    (he : e₁ ≤ e₂) (hg : g₁ ≤ g₂) :
    pd5_logPrefixGood x B e₂ g₂ (L₁ ++ L₂) := by
  constructor
  · rw [List.map_append]
    apply hL.1.append hN₂
    apply List.disjoint_left.mpr
    intro a ha hb
    exact (hDisjoint a ha a hb) rfl
  · intro e heMem
    rcases List.mem_append.mp heMem with heMem | heMem
    · rcases hL.2 e heMem with ⟨hpre, hA⟩
      exact ⟨pd5_prefixAddress_mono he hg hpre, hA⟩
    · exact hAddr₂ e heMem

theorem pd5_initialLog_addresses_nodup {x : ℝ} {K : ℕ} (s : MemPoint x K) :
    ((initialLog s).map Prod.fst).Nodup := by
  classical
  simp only [initialLog, List.map_flatMap, List.map_map, Function.comp_def]
  change ((List.finRange K).flatMap fun i =>
    (List.finRange (slotCount x)).map fun j => BirthAddress.initial i j.val).Nodup
  rw [List.nodup_flatMap]
  constructor
  · intro i hi
    apply (List.nodup_finRange _).map
    intro j j' h
    injection h with _ hval
    exact Fin.ext hval
  · apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    apply List.disjoint_left.mpr
    intro a ha hb
    rcases List.mem_map.mp ha with ⟨k, hk, hka⟩
    rcases List.mem_map.mp hb with ⟨k', hk', hk'a⟩
    have haddr := hka.trans hk'a.symm
    injection haddr with hgroup hslot
    have hgroups : (List.finRange K)[i] = (List.finRange K)[j] := hgroup
    have hij' : i = j := by
      simpa using congrArg Fin.val hgroups
    omega

theorem pd5_initialLog_address_mem {x : ℝ} {K B : ℕ} (s : MemPoint x K)
    (e : BirthAddress K × ℕ) (he : e ∈ initialLog s) :
    e.1 ∈ birthAddresses x K B := by
  classical
  unfold initialLog at he
  rcases List.mem_flatMap.mp he with ⟨i, hi, he⟩
  rcases List.mem_map.mp he with ⟨j, hj, rfl⟩
  have hj' : j.val ∈ Finset.range (slotCount x) := Finset.mem_range.mpr j.isLt
  unfold birthAddresses
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr
    ⟨(i, j.val), Finset.mem_product.mpr ⟨Finset.mem_univ _, hj'⟩, rfl⟩

theorem pd5_initialLog_prefixGood {x : ℝ} {K B : ℕ} (s : MemPoint x K) :
    pd5_logPrefixGood x B 0 0 (initialLog s) := by
  refine ⟨pd5_initialLog_addresses_nodup s, ?_⟩
  intro e he
  constructor
  · unfold initialLog at he
    rcases List.mem_flatMap.mp he with ⟨i, hi, he⟩
    rcases List.mem_map.mp he with ⟨j, hj, heq⟩
    have haddr : e.1 = BirthAddress.initial i j.val := (congrArg Prod.fst heq).symm
    rw [haddr]
    simp [pd5_prefixAddress]
  · exact pd5_initialLog_address_mem s e he

def pd5_ghostAddressList {K : ℕ} (j : ℕ) (l : Fin K → ℕ) : List (BirthAddress K) :=
  (List.finRange K).flatMap fun i =>
    List.ofFn fun k : Fin (l i) => BirthAddress.ghost j i k.val

def pd5_ghostBirthLog {K : ℕ} (j : ℕ) (l : Fin K → ℕ)
    (p : (i : Fin K) → Fin (l i) → ℕ) : BirthLog K :=
  (List.finRange K).flatMap fun i =>
    List.ofFn fun k : Fin (l i) => (BirthAddress.ghost j i k.val, p i k)

theorem pd5_ghostBirthLog_map_fst {K : ℕ} (j : ℕ) (l : Fin K → ℕ)
    (p : (i : Fin K) → Fin (l i) → ℕ) :
    (pd5_ghostBirthLog j l p).map Prod.fst = pd5_ghostAddressList j l := by
  simp [pd5_ghostBirthLog, pd5_ghostAddressList, List.map_flatMap,
    List.map_map, Function.comp_def]

theorem pd5_ghostAddressList_nodup {K : ℕ} (j : ℕ) (l : Fin K → ℕ) :
    (pd5_ghostAddressList j l).Nodup := by
  classical
  unfold pd5_ghostAddressList
  rw [List.nodup_flatMap]
  constructor
  · intro i hi
    apply List.nodup_ofFn.mpr
    intro k k' h
    have hk : k.val = k'.val := by
      injection h
    exact Fin.ext hk
  · apply List.pairwise_iff_getElem.mpr
    intro i i' hi hi' hii'
    have hne : (List.finRange K)[i] ≠ (List.finRange K)[i'] := by
      intro hEq
      have hval : i = i' := by
        simpa [List.getElem_finRange] using congrArg Fin.val hEq
      omega
    apply List.disjoint_left.mpr
    intro a ha ha'
    rcases List.mem_ofFn.mp ha with ⟨k, hk⟩
    rcases List.mem_ofFn.mp ha' with ⟨k', hk'⟩
    have haddr : BirthAddress.ghost j (List.finRange K)[i] k.val =
        BirthAddress.ghost j (List.finRange K)[i'] k'.val := hk.trans hk'.symm
    injection haddr with hstep hgroup hkval
    exact hne hgroup

theorem pd5_ghostAddressList_prefix {K : ℕ} {B n : ℕ} (l : Fin K → ℕ)
    (hl : ∀ i, l i ≤ B) {a : BirthAddress K}
    (ha : a ∈ pd5_ghostAddressList n l) :
    pd5_prefixAddress B n (n + 1) a := by
  rcases List.mem_flatMap.mp ha with ⟨i, hi, ha⟩
  rcases List.mem_ofFn.mp ha with ⟨k, hk⟩
  rw [← hk]
  simp [pd5_prefixAddress]
  exact lt_of_lt_of_le k.isLt (hl i)

theorem pd5_logPrefixGood_disjoint_ghost {K : ℕ} {x : ℝ} {B n : ℕ}
    {L : BirthLog K} (hL : pd5_logPrefixGood x B n n L)
    {l : Fin K → ℕ} :
    ∀ a ∈ L.map Prod.fst, ∀ b ∈ pd5_ghostAddressList n l, a ≠ b := by
  intro a ha b hb hab
  rcases List.mem_map.mp ha with ⟨e, he, heEq⟩
  have hpre := (hL.2 e he).1
  rcases List.mem_flatMap.mp hb with ⟨i, hi, hb⟩
  rcases List.mem_ofFn.mp hb with ⟨k, hk⟩
  have hEq : e.1 = BirthAddress.ghost n i k.val := by
    calc
      e.1 = a := heEq
      _ = b := hab
      _ = BirthAddress.ghost n i k.val := hk.symm
  cases haAddr : e.1 with
  | initial gi slot => simp [haAddr] at hEq
  | edge step gi => simp [haAddr] at hEq
  | ghost step gi index =>
      have hEq' : BirthAddress.ghost step gi index = BirthAddress.ghost n i k.val := by
        simpa [haAddr] using hEq
      have hstep : step = n := by injection hEq' with hstep hgrp hindex
      simp [pd5_prefixAddress, haAddr] at hpre
      omega

theorem pd5_edgeBirths_prefix {K B : ℕ} (F : PDFix K)
    (S : PDScale) (step : ℕ) (s : MemPoint S.x K)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i)
    (hstep : step < pathLength S.x) {a : BirthAddress K}
    (ha : a ∈ (edgeBirths F S step s c).map Prod.fst) :
    pd5_prefixAddress B (step + 1) (step + 1) a := by
  classical
  unfold edgeBirths at ha
  simp only [List.map_flatMap, List.map_map, Function.comp_def,
    List.map_nil, List.map_cons, Prod.fst] at ha
  rcases List.mem_flatMap.mp ha with ⟨i, hi, ha⟩
  cases h : (c i).2 with
  | inl k => simp [h] at ha
  | inr p =>
    have haEq : a = BirthAddress.edge step i := by simpa [h] using ha
    rw [haEq]
    simp [pd5_prefixAddress]

theorem pd5_logPrefixGood_disjoint_edge {K : ℕ} {x : ℝ} {B n : ℕ}
    {L : BirthLog K} (hL : pd5_logPrefixGood x B n (n + 1) L)
    {F : PDFix K} {S : PDScale} (step : ℕ) (s : MemPoint S.x K)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i)
    {a : BirthAddress K} (ha : a ∈ L.map Prod.fst)
    {b : BirthAddress K} (hb : b ∈ (edgeBirths F S step s c).map Prod.fst)
    (hstep : step = n) : a ≠ b := by
  classical
  rcases List.mem_map.mp ha with ⟨e, he, rfl⟩
  unfold edgeBirths at hb
  simp only [List.map_flatMap, List.map_map, Function.comp_def,
    List.map_nil, List.map_cons, Prod.fst] at hb
  rcases List.mem_flatMap.mp hb with ⟨i, hi, hb⟩
  cases h : (c i).2 with
  | inl k => simp [h] at hb
  | inr p =>
    have hbEq : b = BirthAddress.edge step i := by simpa [h] using hb
    intro heq
    have hEq : e.1 = BirthAddress.edge step i := heq.trans hbEq
    rcases hL.2 e he with ⟨hpre, hA⟩
    cases hAddr : e.1 with
    | initial gi slot => simp [hAddr] at hEq
    | edge oldStep gi =>
        have hold : oldStep < n := by simpa [pd5_prefixAddress, hAddr] using hpre
        have hEq' : BirthAddress.edge oldStep gi = BirthAddress.edge step i :=
          hAddr.symm.trans hEq
        have hnew : oldStep = step := by injection hEq' with hstep' hgroup
        omega
    | ghost oldStep gi k => simp [hAddr] at hEq

theorem pd5_ghostAddressList_mem_birthAddresses {x : ℝ} {K B : ℕ}
    {j : ℕ} {l : Fin K → ℕ} (hj : j ≤ pathLength x)
    (hl : ∀ i, l i ≤ B) {a : BirthAddress K}
    (ha : a ∈ pd5_ghostAddressList j l) : a ∈ birthAddresses x K B := by
  classical
  rcases List.mem_flatMap.mp ha with ⟨i, hi, ha⟩
  rcases List.mem_ofFn.mp ha with ⟨k, hk⟩
  rw [← hk]
  unfold birthAddresses
  apply Finset.mem_union_right
  apply Finset.mem_image.mpr
  refine ⟨(j, (i, k.val)), Finset.mem_product.mpr ⟨?_, Finset.mem_product.mpr ⟨?_, ?_⟩⟩, rfl⟩
  · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
  · exact Finset.mem_univ _
  · exact Finset.mem_range.mpr (lt_of_lt_of_le k.isLt (hl i))

theorem pd5_edgeBirths_addresses_nodup {K : ℕ} (F : PDFix K)
    (S : PDScale) (step : ℕ) (s : MemPoint S.x K)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) :
    ((edgeBirths F S step s c).map Prod.fst).Nodup := by
  classical
  unfold edgeBirths
  simp only [List.map_flatMap, List.map_map, Function.comp_def,
    List.map_nil, List.map_cons, Prod.fst]
  rw [List.nodup_flatMap]
  constructor
  · intro i hi
    cases h : (c i).2 with
    | inl k => simp [h]
    | inr p => simp [h]
  · apply List.pairwise_iff_getElem.mpr
    intro i i' hi hi' hii'
    apply List.disjoint_left.mpr
    intro a ha ha'
    cases h : (c (List.finRange K)[i]).2 with
    | inl k => simp [h] at ha
    | inr p =>
      cases h' : (c (List.finRange K)[i']).2 with
      | inl k => simp [h'] at ha'
      | inr p' =>
        have haEq : a = BirthAddress.edge step (List.finRange K)[i] := by
          simpa [h] using ha
        have ha'Eq : a = BirthAddress.edge step (List.finRange K)[i'] := by
          simpa [h'] using ha'
        have haddr : BirthAddress.edge step (List.finRange K)[i] =
            BirthAddress.edge step (List.finRange K)[i'] := haEq.symm.trans ha'Eq
        injection haddr with hstep hgroup
        have hval : i = i' := by
          simpa [List.getElem_finRange] using congrArg Fin.val hgroup
        omega

theorem pd5_edgeBirths_address_mem {K B : ℕ} (F : PDFix K)
    (S : PDScale) (step : ℕ) (s : MemPoint S.x K)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i)
    (hstep : step < pathLength S.x) {a : BirthAddress K}
    (ha : a ∈ (edgeBirths F S step s c).map Prod.fst) :
    a ∈ birthAddresses S.x K B := by
  classical
  unfold edgeBirths at ha
  simp only [List.map_flatMap, List.map_map, Function.comp_def,
    List.map_nil, List.map_cons, Prod.fst] at ha
  rcases List.mem_flatMap.mp ha with ⟨i, hi, ha⟩
  cases h : (c i).2 with
  | inl k => simp [h] at ha
  | inr p =>
    have haEq : a = BirthAddress.edge step i := by simpa [h] using ha
    rw [haEq]
    unfold birthAddresses
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr
      ⟨(step, i), Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr hstep, Finset.mem_univ _⟩, rfl⟩

theorem pd5_logPrefixGood_append_ghostBatch {K : ℕ} {x : ℝ} {B n : ℕ}
    {L : BirthLog K} (hL : pd5_logPrefixGood x B n n L)
    (hn : n ≤ pathLength x) (l : Fin K → ℕ)
    (hl : ∀ i, l i ≤ B) (p : (i : Fin K) → Fin (l i) → ℕ) :
    pd5_logPrefixGood x B n (n + 1) (L ++ pd5_ghostBirthLog n l p) := by
  have hN₂ : (pd5_ghostBirthLog n l p).map Prod.fst |>.Nodup := by
    rw [pd5_ghostBirthLog_map_fst]
    exact pd5_ghostAddressList_nodup n l
  have hAddr₂ : ∀ e ∈ pd5_ghostBirthLog n l p,
      pd5_prefixAddress B n (n + 1) e.1 ∧ e.1 ∈ birthAddresses x K B := by
    intro e he
    have heAddr : e.1 ∈ (pd5_ghostBirthLog n l p).map Prod.fst :=
      List.mem_map.mpr ⟨e, he, rfl⟩
    rw [pd5_ghostBirthLog_map_fst] at heAddr
    exact ⟨pd5_ghostAddressList_prefix l hl heAddr,
      pd5_ghostAddressList_mem_birthAddresses hn hl heAddr⟩
  have hDisjoint : ∀ a ∈ L.map Prod.fst,
      ∀ b ∈ (pd5_ghostBirthLog n l p).map Prod.fst, a ≠ b := by
    intro a ha b hb
    rw [pd5_ghostBirthLog_map_fst] at hb
    exact pd5_logPrefixGood_disjoint_ghost hL a ha b hb
  exact pd5_logPrefixGood_append hL hN₂ hAddr₂ hDisjoint le_rfl (Nat.le_succ n)

theorem pd5_ghost_length_le_memSize {x : ℝ} {K : ℕ} (s : MemPoint x K)
    (D : (i : Fin K) → Finset (Fin (s.2.2 i).length)) (l : Fin K → ℕ)
    (new : (i : Fin K) → Fin (l i) → ℕ) (i : Fin K) :
    l i ≤ memSize (s.1, s.2.1, fun j =>
      removeIndices (s.2.2 j) (D j) ++ List.ofFn fun k => anchorAt (new j k) s.1) := by
  classical
  let m : Fin K → ℕ := fun j =>
    (removeIndices (s.2.2 j) (D j) ++ List.ofFn fun k => anchorAt (new j k) s.1).length
  have hlen : l i ≤ m i := by
    dsimp [m]
    simp [List.length_append]
  have hsum : m i ≤ ∑ j : Fin K, m j := by
    exact Finset.single_le_sum (fun j hj => Nat.zero_le _) (Finset.mem_univ i)
  have hmem : memSize (s.1, s.2.1, fun j =>
      removeIndices (s.2.2 j) (D j) ++ List.ofFn fun k => anchorAt (new j k) s.1) =
      ∑ j : Fin K, m j := by
    simp [memSize, m]
  rw [hmem]
  exact hlen.trans hsum

noncomputable def pd5_ghostOutput {K : ℕ} (F : PDFix K) (S : PDScale)
    (sL : LogPoint S.x K)
    (D : (i : Fin K) → Finset (Fin (sL.1.2.2 i).length))
    (l : Fin K → ℕ) (new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i))
    (j : ℕ) : LogPoint S.x K :=
  ((sL.1.1, sL.1.2.1,
      fun i => removeIndices (sL.1.2.2 i) (D i) ++
        List.ofFn fun k => anchorAt (new i k) sL.1.1),
    sL.2 ++ (List.finRange K).flatMap fun i =>
      List.ofFn fun k : Fin (l i) => (BirthAddress.ghost j i k.val, (new i k : ℕ)))

noncomputable def pd5_ghostWeight {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (j : ℕ) (sL : LogPoint S.x K)
    (D : (i : Fin K) → Finset (Fin (sL.1.2.2 i).length)) (l : Fin K → ℕ)
    (new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i)) : ℂ :=
  ((∏ i : Fin K, ghostGroupCoeff F S ρ j i
      (hitCount (sL.1.2.2 i) sL.1.1) (D i).card (l i)
      (List.ofFn fun k => (new i k : ℕ)) : ℝ) : ℂ)

noncomputable def pd5_ghostLengthTerm {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (j : ℕ) (sL : LogPoint S.x K)
    (D : (i : Fin K) → Finset (Fin (sL.1.2.2 i).length))
    (l : Fin K → ℕ) (f : LogPoint S.x K → ℂ) : ℂ :=
  ∑ new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i),
    if ∀ i, D i ⊆ hitIndices (sL.1.2.2 i) sL.1.1 then
      pd5_ghostWeight F S ρ j sL D l new * f (pd5_ghostOutput F S sL D l new j)
    else 0

theorem pd5_ghostLengthTerm_zero_of_unbounded {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (j B : ℕ) (sL : LogPoint S.x K)
    (D : (i : Fin K) → Finset (Fin (sL.1.2.2 i).length))
    (l : Fin K → ℕ) (f : LogPoint S.x K → ℂ)
    (hl : l ∉ pd5_boundedLengths K B) :
    pd5_ghostLengthTerm F S ρ j sL D l (logTrunc (some B) f) = 0 := by
  classical
  have hbound : ¬ ∀ i, l i ≤ B := by
    intro h
    exact hl ((pd5_mem_boundedLengths).2 h)
  push_neg at hbound
  obtain ⟨i, hi⟩ := hbound
  have hgt : B < l i := by omega
  unfold pd5_ghostLengthTerm
  apply Finset.sum_eq_zero
  intro new hnew
  by_cases hdel : ∀ i, D i ⊆ hitIndices (sL.1.2.2 i) sL.1.1
  · simp only [if_pos hdel]
    let t : MemPoint S.x K :=
      (sL.1.1, sL.1.2.1, fun i => removeIndices (sL.1.2.2 i) (D i) ++
        List.ofFn fun k => anchorAt (new i k) sL.1.1)
    have hlen := pd5_ghost_length_le_memSize sL.1 D l (fun i k => (new i k : ℕ)) i
    have ht : B < memSize t := by
      exact lt_of_lt_of_le hgt (by simpa [t] using hlen)
    have hnot : ¬ memSize (pd5_ghostOutput F S sL D l new j).1 ≤ B := by
      simpa [pd5_ghostOutput, t] using (not_le_of_gt ht)
    simp [logTrunc, hnot]
  · simp [hdel]

theorem pd5_ghostLength_tsum_restrict {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (j B : ℕ) (sL : LogPoint S.x K)
    (D : (i : Fin K) → Finset (Fin (sL.1.2.2 i).length))
    (f : LogPoint S.x K → ℂ) :
    (∑' l : Fin K → ℕ,
      pd5_ghostLengthTerm F S ρ j sL D l (logTrunc (some B) f)) =
    ∑ l ∈ pd5_boundedLengths K B,
      pd5_ghostLengthTerm F S ρ j sL D l (logTrunc (some B) f) := by
  apply tsum_eq_sum
  intro l hl
  exact pd5_ghostLengthTerm_zero_of_unbounded F S ρ j B sL D l f hl

theorem pd5_ghostLengthTerm_finsetSum {K : ℕ} {ι : Type*} [DecidableEq ι]
    (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (j : ℕ) (sL : LogPoint S.x K)
    (D : (i : Fin K) → Finset (Fin (sL.1.2.2 i).length)) (l : Fin K → ℕ)
    (T : Finset ι) (c : ι → ℂ) (f : ι → LogPoint S.x K → ℂ) :
    pd5_ghostLengthTerm F S ρ j sL D l (fun σL => ∑ i ∈ T, c i * f i σL) =
      ∑ i ∈ T, c i * pd5_ghostLengthTerm F S ρ j sL D l (f i) := by
  classical
  unfold pd5_ghostLengthTerm
  by_cases hdel : ∀ i, D i ⊆ hitIndices (sL.1.2.2 i) sL.1.1
  · simp only [if_pos hdel]
    let newTy := (i : Fin K) → Fin (l i) → primeBand S.x (F.a i)
    let weight : newTy → ℂ := pd5_ghostWeight F S ρ j sL D l
    let output : newTy → LogPoint S.x K := fun new => pd5_ghostOutput F S sL D l new j
    change (∑ new : newTy, weight new * (∑ i ∈ T, c i * f i (output new))) =
      ∑ i ∈ T, c i * ∑ new : newTy, weight new * f i (output new)
    calc
      _ = ∑ new : newTy, ∑ i ∈ T, c i * (weight new * f i (output new)) := by
        apply Finset.sum_congr rfl
        intro new hnew
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = ∑ i ∈ T, ∑ new : newTy, c i * (weight new * f i (output new)) := by
        rw [Finset.sum_comm]
      _ = ∑ i ∈ T, c i * ∑ new : newTy, weight new * f i (output new) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← Finset.mul_sum]
  · simp [hdel]

theorem pd5_logGhost_truncated_finite {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (j B : ℕ) (f : LogPoint S.x K → ℂ) (sL : LogPoint S.x K) :
    logGhost F S ρ j (logTrunc (some B) f) sL =
      ∑ D : (i : Fin K) → Finset (Fin (sL.1.2.2 i).length),
        ∑ l ∈ pd5_boundedLengths K B,
          pd5_ghostLengthTerm F S ρ j sL D l (logTrunc (some B) f) := by
  classical
  unfold logGhost
  apply Finset.sum_congr rfl
  intro D hD
  exact pd5_ghostLength_tsum_restrict F S ρ j B sL D f

theorem pd5_logTrunc_finsetSum {x : ℝ} {K : ℕ} {ι : Type*} [DecidableEq ι]
    (B : Option ℕ) (T : Finset ι) (c : ι → ℂ)
    (f : ι → LogPoint x K → ℂ) :
    logTrunc B (fun σL => ∑ i ∈ T, c i * f i σL) =
      fun σL => ∑ i ∈ T, c i * logTrunc B (f i) σL := by
  funext σL
  cases B with
  | none => simp [logTrunc]
  | some b =>
      by_cases h : memSize σL.1 ≤ b <;> simp [logTrunc, h]

set_option maxHeartbeats 800000 in
theorem pd5_logGhost_finsetSum {K : ℕ} {ι : Type*} [DecidableEq ι]
    (F : PDFix K) (S : PDScale) (ρ : ℝ) (j B : ℕ) (T : Finset ι)
    (c : ι → ℂ) (f : ι → LogPoint S.x K → ℂ) (sL : LogPoint S.x K) :
    logGhost F S ρ j
        (logTrunc (some B) (fun σL => ∑ i ∈ T, c i * f i σL)) sL =
      ∑ i ∈ T, c i * logGhost F S ρ j (logTrunc (some B) (f i)) sL := by
  classical
  simp_rw [pd5_logGhost_truncated_finite, pd5_logTrunc_finsetSum]
  calc
    (∑ D : (i : Fin K) → Finset (Fin (sL.1.2.2 i).length),
        ∑ l ∈ pd5_boundedLengths K B,
          pd5_ghostLengthTerm F S ρ j sL D l
            (fun σL => ∑ i ∈ T, c i * logTrunc (some B) (f i) σL)) =
      ∑ D : (i : Fin K) → Finset (Fin (sL.1.2.2 i).length),
        ∑ l ∈ pd5_boundedLengths K B, ∑ i ∈ T,
          c i * pd5_ghostLengthTerm F S ρ j sL D l (logTrunc (some B) (f i)) := by
            apply Finset.sum_congr rfl
            intro D hD
            apply Finset.sum_congr rfl
            intro l hl
            exact pd5_ghostLengthTerm_finsetSum F S ρ j sL D l T c
              (fun i σL => logTrunc (some B) (f i) σL)
    _ = ∑ D : (i : Fin K) → Finset (Fin (sL.1.2.2 i).length),
          ∑ i ∈ T, ∑ l ∈ pd5_boundedLengths K B,
            c i * pd5_ghostLengthTerm F S ρ j sL D l (logTrunc (some B) (f i)) := by
          apply Finset.sum_congr rfl
          intro D hD
          rw [Finset.sum_comm]
    _ = ∑ D : (i : Fin K) → Finset (Fin (sL.1.2.2 i).length),
          ∑ i ∈ T, c i * ∑ l ∈ pd5_boundedLengths K B,
            pd5_ghostLengthTerm F S ρ j sL D l (logTrunc (some B) (f i)) := by
          apply Finset.sum_congr rfl
          intro D hD
          apply Finset.sum_congr rfl
          intro i hi
          rw [← Finset.mul_sum]
    _ = ∑ i ∈ T, ∑ D : (i : Fin K) → Finset (Fin (sL.1.2.2 i).length),
          c i * ∑ l ∈ pd5_boundedLengths K B,
            pd5_ghostLengthTerm F S ρ j sL D l (logTrunc (some B) (f i)) := by
          rw [Finset.sum_comm]
    _ = ∑ i ∈ T, c i *
          ∑ D : (i : Fin K) → Finset (Fin (sL.1.2.2 i).length),
            ∑ l ∈ pd5_boundedLengths K B,
              pd5_ghostLengthTerm F S ρ j sL D l (logTrunc (some B) (f i)) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [← Finset.mul_sum]

theorem pd5_logGhost_finsetSumFun {K : ℕ} {ι : Type*} [DecidableEq ι]
    (F : PDFix K) (S : PDScale) (ρ : ℝ) (j B : ℕ) (T : Finset ι)
    (c : ι → ℂ) (f : ι → LogPoint S.x K → ℂ) :
    logGhost F S ρ j (logTrunc (some B) (fun σL => ∑ i ∈ T, c i * f i σL)) =
      fun sL => ∑ i ∈ T, c i * logGhost F S ρ j (logTrunc (some B) (f i)) sL := by
  funext sL
  exact pd5_logGhost_finsetSum F S ρ j B T c f sL

theorem pd5_logBoundaryOut_finsetSumFun (x : ℝ) {K : ℕ} {ι : Type*} [DecidableEq ι]
    (T : Finset ι) (c : ι → ℂ) (W : ι → BirthLog K → ℂ) :
    logBoundaryOut (x := x) (fun log => ∑ i ∈ T, c i * W i log) =
      fun σL : LogPoint x K => ∑ i ∈ T, c i * logBoundaryOut (x := x) (W i) σL := by
  funext σL
  unfold logBoundaryOut
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem pd5_logPathRestrict_none {K : ℕ} {x : ℝ} (j : ℕ)
    (f : LogPoint x K → ℂ) : logPathRestrict none j f = f := rfl

set_option maxHeartbeats 800000 in
theorem pd5_logHistoryFn_finsetSum {K : ℕ} {ι : Type*} [DecidableEq ι]
    (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot) (B : ℕ)
    (T : Finset ι) (c : ι → ℂ) (W : ι → BirthLog K → ℂ)
    (hbox : {z : ℤ × ℤ | envBox S w z}.Finite) :
    ∀ k, k ≤ pathLength S.x →
      logHistoryFn F S ρ w (some B) none
          (fun log => ∑ i ∈ T, c i * W i log) k =
        fun σL => ∑ i ∈ T, c i * logHistoryFn F S ρ w (some B) none (W i) k σL := by
  classical
  intro k
  induction k with
  | zero =>
      intro hk
      funext σL
      simp only [logHistoryFn, pd5_logPathRestrict_none]
      rw [pd5_logBoundaryOut_finsetSumFun S.x T c W]
      rw [pd5_logGhost_finsetSumFun F S ρ (pathLength S.x) B T c
        (fun i => logBoundaryOut (W i))]
      rw [pd5_logTrunc_finsetSum]

  | succ k ih =>
      intro hk
      have hprev := ih (by omega : k ≤ pathLength S.x)
      funext σL
      simp only [logHistoryFn, pd5_logPathRestrict_none]
      rw [hprev]
      rw [pd5_logTrunc_finsetSum]
      let j : ℕ := pathLength S.x - (k + 1)
      have hj : j < pathLength S.x := by
        dsimp [j]
        omega
      rw [pd5_logEdge_full_finsetSumFun F S ρ w j T c
        (fun i τL => logTrunc (some B)
          (logHistoryFn F S ρ w (some B) none (W i) k) τL) hbox]
      rw [pd5_logGhost_finsetSumFun F S ρ j B T c
        (fun i τL => logEdge F S ρ w EdgeKind.full j
            (logTrunc (some B)
              (logHistoryFn F S ρ w (some B) none (W i) k)) τL)]
      rw [pd5_logTrunc_finsetSum]

theorem pd5_logBoundaryIn_weight_support_finite {K : ℕ} (F : PDFix K)
    (S : PDScale) :
    {σL : LogPoint S.x K |
      (memMeasure F S σL.1 : ℂ) * star (logBoundaryIn σL) ≠ 0}.Finite := by
  classical
  let Active : Type :=
    (i : Fin K) → Fin (slotCount S.x) →
      {p : ℕ // p ∈ primeBand S.x (F.a i)}
  letI : Fintype Active := inferInstance
  let stateOf : Active → MemPoint S.x K := fun l =>
    ((1, 0), (fun i j => (l i j : ℕ)), fun _ => [])
  let boundaryLogs : Finset (LogPoint S.x K) :=
    (Finset.univ : Finset Active).image fun l =>
      (stateOf l, initialLog (stateOf l))
  apply (boundaryLogs.finite_toSet).subset
  intro σL hσL
  rcases σL with ⟨s, L⟩
  have hmeasure : memMeasure F S s ≠ 0 := by
    intro hm
    apply hσL
    simp [hm]
  have hinput : logBoundaryIn (s, L) ≠ 0 := by
    intro hin
    apply hσL
    simp [hin]
  have hlog : L = initialLog s := by
    unfold logBoundaryIn at hinput
    by_cases h : L = initialLog s
    · exact h
    · simp [h] at hinput
  have hboundary : memBoundary s ≠ 0 := by
    simpa [logBoundaryIn, hlog] using hinput
  have hsBoundary : s.1 = (1, 0) ∧ ∀ i, s.2.2 i = [] := by
    unfold memBoundary at hboundary
    by_cases h : s.1 = (1, 0) ∧ ∀ i, s.2.2 i = []
    · exact h
    · simp [h] at hboundary
  have hsValid : MemValid F S s := by
    unfold memMeasure at hmeasure
    by_cases h : MemValid F S s
    · exact h
    · simp [h] at hmeasure
  let l : Active := fun i j => ⟨s.2.1 i j, hsValid.2.1 i j⟩
  have hs : s = stateOf l := by
    apply Prod.ext
    · exact hsBoundary.1
    · apply Prod.ext
      · funext i j
        rfl
      · funext i
        exact hsBoundary.2 i
  have hL : L = initialLog (stateOf l) := by
    rw [← hs]
    exact hlog
  apply Finset.mem_coe.mpr
  unfold boundaryLogs
  exact Finset.mem_image.mpr ⟨l, Finset.mem_univ _, Prod.ext hs.symm hL.symm⟩

theorem pd5_logInner_finsetSum {K : ℕ} {ι : Type*} [DecidableEq ι]
    (F : PDFix K) (S : PDScale) (T : Finset ι) (c : ι → ℂ)
    (g : ι → LogPoint S.x K → ℂ) :
    logInner F S logBoundaryIn (fun σL => ∑ i ∈ T, c i * g i σL) =
      ∑ i ∈ T, c i * logInner F S logBoundaryIn (g i) := by
  classical
  unfold logInner
  let weight : LogPoint S.x K → ℂ := fun σL =>
    (memMeasure F S σL.1 : ℂ) * star (logBoundaryIn σL)
  let support := (pd5_logBoundaryIn_weight_support_finite F S).toFinset
  have hzero (σL : LogPoint S.x K) (hσL : σL ∉ support) : weight σL = 0 := by
    by_contra hw
    apply hσL
    change σL ∈ (pd5_logBoundaryIn_weight_support_finite F S).toFinset
    exact (pd5_logBoundaryIn_weight_support_finite F S).mem_toFinset.mpr
      (by simpa [weight] using hw)
  have hzeroSum : ∀ σL, σL ∉ support →
      weight σL * (∑ i ∈ T, c i * g i σL) = 0 := by
    intro σL hσL
    simp [hzero σL hσL]
  have hzeroEach (i : ι) : ∀ σL, σL ∉ support →
      weight σL * g i σL = 0 := by
    intro σL hσL
    simp [hzero σL hσL]
  calc
    (∑' σL : LogPoint S.x K, weight σL * (∑ i ∈ T, c i * g i σL)) =
        ∑ σL ∈ support, weight σL * (∑ i ∈ T, c i * g i σL) :=
      tsum_eq_sum (L := SummationFilter.unconditional (LogPoint S.x K))
        (s := support) hzeroSum
    _ = ∑ i ∈ T, c i * ∑ σL ∈ support, weight σL * g i σL := by
      calc
        _ = ∑ σL ∈ support, ∑ i ∈ T, c i * (weight σL * g i σL) := by
          apply Finset.sum_congr rfl
          intro σL hσL
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = ∑ i ∈ T, ∑ σL ∈ support, c i * (weight σL * g i σL) := by
          rw [Finset.sum_comm]
        _ = ∑ i ∈ T, c i * ∑ σL ∈ support, weight σL * g i σL := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [← Finset.mul_sum]
    _ = ∑ i ∈ T, c i * ∑' σL : LogPoint S.x K, weight σL * g i σL := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← tsum_eq_sum (L := SummationFilter.unconditional (LogPoint S.x K))
        (s := support) (hzeroEach i)]

theorem pd5_memHistory_finsetSum {K : ℕ} {ι : Type*} [DecidableEq ι]
    (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot) (B : ℕ)
    (T : Finset ι) (c : ι → ℂ) (W : ι → BirthLog K → ℂ)
    (hbox : {z : ℤ × ℤ | envBox S w z}.Finite) :
    memHistory F S ρ w (some B) none (fun log => ∑ i ∈ T, c i * W i log) =
      ∑ i ∈ T, c i * memHistory F S ρ w (some B) none (W i) := by
  unfold memHistory
  rw [pd5_logHistoryFn_finsetSum F S ρ w B T c W hbox
    (pathLength S.x) le_rfl]
  exact pd5_logInner_finsetSum F S T c
    (fun i σL => logHistoryFn F S ρ w (some B) none (W i) (pathLength S.x) σL)

theorem pd5_logGhost_boundaryOut_congr {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (B n : ℕ) (s : MemPoint S.x K) (L : BirthLog K)
    (hL : pd5_logPrefixGood S.x B n n L) (hn : n ≤ pathLength S.x)
    (W₁ W₂ : BirthLog K → ℂ)
    (hW : ∀ log, (log.map Prod.fst).Nodup →
      (∀ e ∈ log, e.1 ∈ birthAddresses S.x K B) → W₁ log = W₂ log) :
    logGhost F S ρ n (logTrunc (some B) (logBoundaryOut W₁)) (s, L) =
      logGhost F S ρ n (logTrunc (some B) (logBoundaryOut W₂)) (s, L) := by
  classical
  unfold logGhost
  apply Finset.sum_congr rfl
  intro D hD
  apply tsum_congr
  intro l
  apply Finset.sum_congr rfl
  intro new hnew
  by_cases hdelete : ∀ i, D i ⊆ hitIndices (s.2.2 i) s.1
  · simp only [if_pos hdelete]
    let t : MemPoint S.x K :=
      (s.1, s.2.1, fun i => removeIndices (s.2.2 i) (D i) ++
        List.ofFn fun k => anchorAt (new i k) s.1)
    let G : BirthLog K := pd5_ghostBirthLog n l (fun i k => (new i k : ℕ))
    by_cases hsize : memSize t ≤ B
    · have hlength' : ∀ i, l i ≤ B := by
        intro i
        exact (pd5_ghost_length_le_memSize s D l (fun i k => (new i k : ℕ)) i).trans hsize
      have hgood : pd5_logPrefixGood S.x B n (n + 1) (L ++ G) := by
        simpa [G, pd5_ghostBirthLog] using
          (pd5_logPrefixGood_append_ghostBatch hL hn l hlength'
            (fun i k => (new i k : ℕ)))
      have hweight : W₁ (L ++ G) = W₂ (L ++ G) :=
        hW (L ++ G) hgood.1 (fun e he => (hgood.2 e he).2)
      have hinner :
          logTrunc (some B) (logBoundaryOut W₁) (t, L ++ G) =
            logTrunc (some B) (logBoundaryOut W₂) (t, L ++ G) := by
        simp [logTrunc, hsize, logBoundaryOut, hweight]
      have htarget :
          logTrunc (some B) (logBoundaryOut W₁)
              ((s.1, s.2.1, fun i => removeIndices (s.2.2 i) (D i) ++
                List.ofFn fun k => anchorAt (new i k) s.1),
                L ++ (List.finRange K).flatMap fun i =>
                  List.ofFn fun k : Fin (l i) => (BirthAddress.ghost n i k.val, (new i k : ℕ))) =
            logTrunc (some B) (logBoundaryOut W₂)
              ((s.1, s.2.1, fun i => removeIndices (s.2.2 i) (D i) ++
                List.ofFn fun k => anchorAt (new i k) s.1),
                L ++ (List.finRange K).flatMap fun i =>
                  List.ofFn fun k : Fin (l i) => (BirthAddress.ghost n i k.val, (new i k : ℕ))) := by
        simpa [t, G, pd5_ghostBirthLog] using hinner
      rw [htarget]
    · have hzero₁ :
          logTrunc (some B) (logBoundaryOut W₁)
              ((s.1, s.2.1, fun i => removeIndices (s.2.2 i) (D i) ++
                List.ofFn fun k => anchorAt (new i k) s.1),
                L ++ (List.finRange K).flatMap fun i =>
                  List.ofFn fun k : Fin (l i) => (BirthAddress.ghost n i k.val, (new i k : ℕ))) = 0 := by
        simp [logTrunc, t, hsize]
      have hzero₂ :
          logTrunc (some B) (logBoundaryOut W₂)
              ((s.1, s.2.1, fun i => removeIndices (s.2.2 i) (D i) ++
                List.ofFn fun k => anchorAt (new i k) s.1),
                L ++ (List.finRange K).flatMap fun i =>
                  List.ofFn fun k : Fin (l i) => (BirthAddress.ghost n i k.val, (new i k : ℕ))) = 0 := by
        simp [logTrunc, t, hsize]
      rw [hzero₁, hzero₂]
  · simp [hdelete]

theorem pd5_logGhost_prefix_congr {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (n B : ℕ) (s : MemPoint S.x K) (L : BirthLog K)
    (hL : pd5_logPrefixGood S.x B n n L) (hn : n ≤ pathLength S.x)
    (f₁ f₂ : LogPoint S.x K → ℂ)
    (hf : ∀ σL, pd5_logPrefixGood S.x B n (n + 1) σL.2 →
      f₁ σL = f₂ σL) :
    logGhost F S ρ n (logTrunc (some B) f₁) (s, L) =
      logGhost F S ρ n (logTrunc (some B) f₂) (s, L) := by
  classical
  unfold logGhost
  apply Finset.sum_congr rfl
  intro D hD
  apply tsum_congr
  intro l
  apply Finset.sum_congr rfl
  intro new hnew
  by_cases hdelete : ∀ i, D i ⊆ hitIndices (s.2.2 i) s.1
  · simp only [if_pos hdelete]
    let t : MemPoint S.x K :=
      (s.1, s.2.1, fun i => removeIndices (s.2.2 i) (D i) ++
        List.ofFn fun k => anchorAt (new i k) s.1)
    let G : BirthLog K := pd5_ghostBirthLog n l (fun i k => (new i k : ℕ))
    by_cases hsize : memSize t ≤ B
    · have hlength : ∀ i, l i ≤ B := by
        intro i
        exact (pd5_ghost_length_le_memSize s D l (fun i k => (new i k : ℕ)) i).trans hsize
      have hgood : pd5_logPrefixGood S.x B n (n + 1) (L ++ G) := by
        simpa [G, pd5_ghostBirthLog] using
          (pd5_logPrefixGood_append_ghostBatch hL hn l hlength
            (fun i k => (new i k : ℕ)))
      have hfun : f₁ (t, L ++ G) = f₂ (t, L ++ G) :=
        hf (t, L ++ G) hgood
      have hinner :
          logTrunc (some B) f₁ (t, L ++ G) = logTrunc (some B) f₂ (t, L ++ G) := by
        simp [logTrunc, hsize, hfun]
      have htarget :
          logTrunc (some B) f₁
              ((s.1, s.2.1, fun i => removeIndices (s.2.2 i) (D i) ++
                List.ofFn fun k => anchorAt (new i k) s.1),
                L ++ (List.finRange K).flatMap fun i =>
                  List.ofFn fun k : Fin (l i) => (BirthAddress.ghost n i k.val, (new i k : ℕ))) =
            logTrunc (some B) f₂
              ((s.1, s.2.1, fun i => removeIndices (s.2.2 i) (D i) ++
                List.ofFn fun k => anchorAt (new i k) s.1),
                L ++ (List.finRange K).flatMap fun i =>
                  List.ofFn fun k : Fin (l i) => (BirthAddress.ghost n i k.val, (new i k : ℕ))) := by
        simpa [t, G, pd5_ghostBirthLog] using hinner
      rw [htarget]
    · have hzero₁ :
          logTrunc (some B) f₁
              ((s.1, s.2.1, fun i => removeIndices (s.2.2 i) (D i) ++
                List.ofFn fun k => anchorAt (new i k) s.1),
                L ++ (List.finRange K).flatMap fun i =>
                  List.ofFn fun k : Fin (l i) => (BirthAddress.ghost n i k.val, (new i k : ℕ))) = 0 := by
        simp [logTrunc, t, hsize]
      have hzero₂ :
          logTrunc (some B) f₂
              ((s.1, s.2.1, fun i => removeIndices (s.2.2 i) (D i) ++
                List.ofFn fun k => anchorAt (new i k) s.1),
                L ++ (List.finRange K).flatMap fun i =>
                  List.ofFn fun k : Fin (l i) => (BirthAddress.ghost n i k.val, (new i k : ℕ))) = 0 := by
        simp [logTrunc, t, hsize]
      rw [hzero₁, hzero₂]
  · simp [hdelete]

theorem pd5_logPrefixGood_append_edge {K : ℕ} {x : ℝ} {B n : ℕ}
    {L : BirthLog K} (hL : pd5_logPrefixGood x B n (n + 1) L)
    (F : PDFix K) (S : PDScale) (s : MemPoint S.x K)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i)
    (hxn : S.x = x) (hstep : n < pathLength x) :
    pd5_logPrefixGood x B (n + 1) (n + 1) (L ++ edgeBirths F S n s c) := by
  have hN₂ : (edgeBirths F S n s c).map Prod.fst |>.Nodup :=
    pd5_edgeBirths_addresses_nodup F S n s c
  have hAddr₂ : ∀ e ∈ edgeBirths F S n s c,
      pd5_prefixAddress B (n + 1) (n + 1) e.1 ∧ e.1 ∈ birthAddresses x K B := by
    intro e he
    have heAddr : e.1 ∈ (edgeBirths F S n s c).map Prod.fst :=
      List.mem_map.mpr ⟨e, he, rfl⟩
    have hprefix := pd5_edgeBirths_prefix (B := B) F S n s c
      (by simpa [hxn] using hstep) heAddr
    have hmem := pd5_edgeBirths_address_mem (B := B) F S n s c
      (by simpa [hxn] using hstep) heAddr
    rw [hxn] at hmem
    simpa using And.intro hprefix hmem
  have hDisjoint : ∀ a ∈ L.map Prod.fst,
      ∀ b ∈ (edgeBirths F S n s c).map Prod.fst, a ≠ b := by
    intro a ha b hb
    exact pd5_logPrefixGood_disjoint_edge hL n s c ha hb rfl
  exact pd5_logPrefixGood_append hL hN₂ hAddr₂ hDisjoint (Nat.le_succ n) le_rfl

theorem pd5_logHistoryFn_zero_congr {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (B : ℕ) (W₁ W₂ : BirthLog K → ℂ)
    (hW : ∀ log, (log.map Prod.fst).Nodup →
      (∀ e ∈ log, e.1 ∈ birthAddresses S.x K B) → W₁ log = W₂ log)
    {s : MemPoint S.x K} {L : BirthLog K}
    (hL : pd5_logPrefixGood S.x B (pathLength S.x) (pathLength S.x) L) :
    logHistoryFn F S ρ w (some B) none W₁ 0 (s, L) =
      logHistoryFn F S ρ w (some B) none W₂ 0 (s, L) := by
  classical
  simp only [logHistoryFn, logPathRestrict]
  by_cases hB : memSize s ≤ B
  · simp only [logTrunc, hB, dite_true]
    exact pd5_logGhost_boundaryOut_congr F S ρ B (pathLength S.x) s L hL le_rfl W₁ W₂ hW
  · simp [logTrunc, hB]

theorem pd5_logSym_prefix_congr {K : ℕ} (F : PDFix K) (S : PDScale)
    {B e g : ℕ} {f₁ f₂ : LogPoint S.x K → ℂ}
    (hf : ∀ σL, pd5_logPrefixGood S.x B e g σL.2 → f₁ σL = f₂ σL)
    (σL : LogPoint S.x K) (hL : pd5_logPrefixGood S.x B e g σL.2) :
    logSym F S f₁ σL = logSym F S f₂ σL := by
  classical
  unfold logSym
  apply congrArg (fun z : ℂ => ((permCount S.x K : ℂ)⁻¹) * z)
  apply Finset.sum_congr rfl
  intro σ hσ
  exact hf ((σL.1.1, permuteLists σ σL.1.2.1, σL.1.2.2), σL.2) hL

theorem pd5_logEdgePiece_prefix_congr {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (step n B : ℕ) (raw : Bool)
    (St Pr : Finset (Fin K)) (f₁ f₂ : LogPoint S.x K → ℂ)
    (hf : ∀ σL, pd5_logPrefixGood S.x B (n + 1) (n + 1) σL.2 →
      f₁ σL = f₂ σL)
    (hstepEq : step = n) (hstep : step < pathLength S.x)
    {s : MemPoint S.x K} {L : BirthLog K}
    (hL : pd5_logPrefixGood S.x B n (n + 1) L) :
    logEdgePiece F S ρ w step raw St Pr f₁ (s, L) =
      logEdgePiece F S ρ w step raw St Pr f₂ (s, L) := by
  classical
  unfold logEdgePiece
  apply Finset.sum_congr rfl
  intro c hc
  apply tsum_congr
  intro z'
  let target : MemPoint S.x K :=
    (z', edgeTargetLists F S s c, edgeNewMemory F S s c)
  let targetLog : BirthLog K := L ++ edgeBirths F S step s c
  by_cases hcond : edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧
      EdgeAdmissible F S w s c z'
  · simp only [if_pos hcond]
    have htargetGood0 := pd5_logPrefixGood_append_edge hL F S s c rfl
      (by simpa [hstepEq] using hstep)
    have htargetGood : pd5_logPrefixGood S.x B (n + 1) (n + 1) (L ++ edgeBirths F S step s c) := by
      simpa [hstepEq] using htargetGood0
    have htargetLogGood : pd5_logPrefixGood S.x B (n + 1) (n + 1) (target, targetLog).2 := by
      simpa [targetLog] using htargetGood
    have hfun : f₁ (target, targetLog) = f₂ (target, targetLog) :=
      hf (target, targetLog) htargetLogGood
    rw [hfun]
  · simp [hcond]

theorem pd5_logEdge_prefix_congr {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (step n B : ℕ)
    (f₁ f₂ : LogPoint S.x K → ℂ)
    (hf : ∀ σL, pd5_logPrefixGood S.x B (n + 1) (n + 1) σL.2 →
      f₁ σL = f₂ σL)
    (hstepEq : step = n) (hstep : step < pathLength S.x)
    (σL : LogPoint S.x K) (hL : pd5_logPrefixGood S.x B n (n + 1) σL.2) :
    logEdge F S ρ w EdgeKind.full step f₁ σL =
      logEdge F S ρ w EdgeKind.full step f₂ σL := by
  classical
  have hSym (τL : LogPoint S.x K)
      (hτ : pd5_logPrefixGood S.x B (n + 1) (n + 1) τL.2) :
      logSym F S f₁ τL = logSym F S f₂ τL :=
    pd5_logSym_prefix_congr (F := F) (S := S) (B := B) (e := n + 1) (g := n + 1)
      hf τL hτ
  unfold logEdge
  refine pd5_logSym_prefix_congr (F := F) (S := S) (B := B) (e := n) (g := n + 1)
    ?_ σL hL
  · intro τL hτ
    simp only [EdgeKind.full]
    apply Finset.sum_congr rfl
    intro St hSt
    apply Finset.sum_congr rfl
    intro Pr hPr
    have hraw := pd5_logEdgePiece_prefix_congr F S ρ w step n B true St Pr
      (logSym F S f₁) (logSym F S f₂) hSym hstepEq hstep
      (s := τL.1) (L := τL.2) hτ
    have hcmp := pd5_logEdgePiece_prefix_congr F S ρ w step n B false St Pr
      (logSym F S f₁) (logSym F S f₂) hSym hstepEq hstep
      (s := τL.1) (L := τL.2) hτ
    rw [hraw, hcmp]

theorem pd5_logHistoryFn_prefix_congr {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (B : ℕ) (W₁ W₂ : BirthLog K → ℂ)
    (hW : ∀ log, (log.map Prod.fst).Nodup →
      (∀ e ∈ log, e.1 ∈ birthAddresses S.x K B) → W₁ log = W₂ log) :
    ∀ k, k ≤ pathLength S.x → ∀ s : MemPoint S.x K, ∀ L : BirthLog K,
      pd5_logPrefixGood S.x B (pathLength S.x - k) (pathLength S.x - k) L →
      logHistoryFn F S ρ w (some B) none W₁ k (s, L) =
        logHistoryFn F S ρ w (some B) none W₂ k (s, L) := by
  classical
  intro k
  induction k with
  | zero =>
      intro hk s L hL
      exact pd5_logHistoryFn_zero_congr F S ρ w B W₁ W₂ hW hL
  | succ k ih =>
      intro hk s L hL
      let n : ℕ := pathLength S.x - (k + 1)
      have hkn : k ≤ pathLength S.x := Nat.le_trans (Nat.le_succ _) hk
      have hnstep : n < pathLength S.x := by
        dsimp [n]
        omega
      have hnlog : pd5_logPrefixGood S.x B n n L := by
        simpa [n] using hL
      have hnext : pathLength S.x - k = n + 1 := by
        dsimp [n]
        omega
      simp only [logHistoryFn, logPathRestrict]
      change logTrunc (some B)
          (logGhost F S ρ n
            (logTrunc (some B)
              (logEdge F S ρ w EdgeKind.full n
                (logTrunc (some B) (logHistoryFn F S ρ w (some B) none W₁ k))))) (s, L) =
        logTrunc (some B)
          (logGhost F S ρ n
            (logTrunc (some B)
              (logEdge F S ρ w EdgeKind.full n
                (logTrunc (some B) (logHistoryFn F S ρ w (some B) none W₂ k))))) (s, L)
      by_cases hsrc : memSize s ≤ B
      · simp only [logTrunc, hsrc, dite_true]
        let cont₁ : LogPoint S.x K → ℂ := fun τL =>
          logEdge F S ρ w EdgeKind.full n
            (logTrunc (some B) (logHistoryFn F S ρ w (some B) none W₁ k)) τL
        let cont₂ : LogPoint S.x K → ℂ := fun τL =>
          logEdge F S ρ w EdgeKind.full n
            (logTrunc (some B) (logHistoryFn F S ρ w (some B) none W₂ k)) τL
        apply pd5_logGhost_prefix_congr F S ρ n B s L hnlog
          (Nat.le_of_lt hnstep) cont₁ cont₂
        intro τL hτ
        apply pd5_logEdge_prefix_congr F S ρ w n n B
          (logTrunc (some B) (logHistoryFn F S ρ w (some B) none W₁ k))
          (logTrunc (some B) (logHistoryFn F S ρ w (some B) none W₂ k))
          ?_ rfl hnstep τL hτ
        intro ξL hξ
        by_cases hξsize : memSize ξL.1 ≤ B
        · have hξprefix :
              pd5_logPrefixGood S.x B (pathLength S.x - k)
                (pathLength S.x - k) ξL.2 := by
            simpa [hnext] using hξ
          have hrec := ih hkn ξL.1 ξL.2 hξprefix
          simp [logTrunc, hξsize, hrec]
        · simp [logTrunc, hξsize]
        
      · simp [logTrunc, hsrc]

theorem pd5_birthPartition_weight_agree {K : ℕ} (A : Finset (BirthAddress K))
    {log : BirthLog K} (hN : (log.map Prod.fst).Nodup)
    (hA : ∀ e ∈ log, e.1 ∈ A) :
    distinctWeight log = pd5_constraintWeightSum A log := by
  simpa [pd5_constraintWeightSum] using birth_partition_from_labels A log hN hA

theorem pd5_memHistory_partition_identity {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (B : ℕ) (A : Finset (BirthAddress K))
    (hA : birthAddresses S.x K B ⊆ A) :
    memHistory F S ρ w (some B) none distinctWeight =
      memHistory F S ρ w (some B) none (pd5_constraintWeightSum A) := by
  classical
  unfold memHistory logInner
  apply tsum_congr
  intro σL
  by_cases hlog : σL.2 = initialLog σL.1
  · cases σL with
    | mk s log =>
      have hlog' : log = initialLog s := hlog
      subst log
      have hInit := pd5_initialLog_prefixGood (B := B) s
      have hHist := pd5_logHistoryFn_prefix_congr F S ρ w B distinctWeight
        (pd5_constraintWeightSum A) (by
          intro log hN hAddr
          exact pd5_birthPartition_weight_agree A hN (fun e he => hA (hAddr e he)))
        (pathLength S.x) le_rfl s (initialLog s) (by simpa using hInit)
      rw [hHist]
  · simp [logBoundaryIn, hlog]

theorem pd5_memHistory_partition_sum {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (B : ℕ) (A : Finset (BirthAddress K))
    (hA : birthAddresses S.x K B ⊆ A)
    (hbox : {z : ℤ × ℤ | envBox S w z}.Finite) :
    memHistory F S ρ w (some B) none distinctWeight =
      ∑ C ∈ constraintSystems A,
        (constraintCoeff C : ℂ) * memHistory F S ρ w (some B) none (constraintWeight C) := by
  rw [pd5_memHistory_partition_identity F S ρ w B A hA]
  change memHistory F S ρ w (some B) none
      (fun log => ∑ C ∈ constraintSystems A,
        (constraintCoeff C : ℂ) * constraintWeight C log) = _
  exact pd5_memHistory_finsetSum F S ρ w B (constraintSystems A)
    (fun C => (constraintCoeff C : ℂ)) constraintWeight hbox

end

end ArtinPrimitiveRoots.TypeII.PD
