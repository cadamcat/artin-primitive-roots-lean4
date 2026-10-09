import ArtinPrimitiveRoots.TypeII.MarkedTransfer

/-! Uniform output constants for the marked coefficient transfer over families with a common
upper bound on their starting thresholds and a common long-cancellation witness. -/

namespace ArtinPrimitiveRoots.Proofs.c_typeii_sol

open Classical
open ArtinPrimitiveRoots.TypeII

/-- Common long-cancellation constants, with all thresholds at least the common starting point. -/
structure LongCancellationWitness (δ C c₁ c₂ T : ℝ) where
  constant : ℝ → ℝ → ℝ → ℝ
  threshold : ℝ → ℝ → ℝ → ℝ
  positive : ∀ A₀ B A, 0 < A₀ → 0 < B → 0 < A → 0 < constant A₀ B A
  threshold_ge_base : ∀ A₀ B A, 0 < A₀ → 0 < B → 0 < A → T ≤ threshold A₀ B A

/-- The long-cancellation assertion with a specified witness, rather than with constants chosen
separately for each coefficient family. -/
def HasLongCancellationWith {δ C c₁ c₂ T : ℝ}
    (family : CoefficientFamily δ C c₁ c₂)
    (W : LongCancellationWitness δ C c₁ c₂ T) : Prop :=
  ∀ A₀ B A, 0 < A₀ → 0 < B → 0 < A →
    ∀ x : ℝ, W.threshold A₀ B A ≤ x →
      ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.rpow (Real.log x) A₀ →
        ∀ χ : DirichletCharacter ℂ k, ∀ t : ℝ,
          |t| ≤ 2 * (family.Hm x * family.Hn x) * Real.rpow (Real.log x) B →
            ‖∑ m ∈ familyTerms family x,
              family.alpha x m * χ (m : ZMod k) *
                Complex.exp (Complex.I * t * Real.log (m : ℝ))‖ /
                family.Hm x ≤ W.constant A₀ B A * Real.rpow (Real.log x) (-A)

private noncomputable def spliceIndices (xs : ℕ → ℝ) (y : ℝ) : Finset ℕ :=
  (Finset.range (⌊y⌋₊ + 1)).filter fun n => xs n = y

private noncomputable def spliceFamily {δ C c₁ c₂ : ℝ}
    (T : ℝ) (hT : 2 ≤ T)
    (base : CoefficientFamily δ C c₁ c₂) (hbase : base.xMin ≤ T)
    (families : ℕ → CoefficientFamily δ C c₁ c₂)
    (hmins : ∀ n, (families n).xMin ≤ T) (xs : ℕ → ℝ) :
    CoefficientFamily δ C c₁ c₂ := by
  classical
  refine {
    xMin := T
    xMin_ge_two := hT
    Hm := fun y => if h : (spliceIndices xs y).Nonempty then
      (families ((spliceIndices xs y).max' h)).Hm y else base.Hm y
    Hn := fun y => if h : (spliceIndices xs y).Nonempty then
      (families ((spliceIndices xs y).max' h)).Hn y else base.Hn y
    interval := fun y => if h : (spliceIndices xs y).Nonempty then
      (families ((spliceIndices xs y).max' h)).interval y else ∅
    alpha := fun y m => if h : (spliceIndices xs y).Nonempty then
      (families ((spliceIndices xs y).max' h)).alpha y m else 0
    interval_property := ?_
    scales := ?_
    interval_bounds := ?_
    rough_support := ?_
    coefficient_bound := ?_ }
  · intro y
    by_cases h : (spliceIndices xs y).Nonempty
    · simpa only [dif_pos h] using
        (families ((spliceIndices xs y).max' h)).interval_property y
    · intro m n k hm hn hmin hmax
      simp only [dif_neg h, Set.mem_empty_iff_false] at hm
  · intro y hy
    by_cases h : (spliceIndices xs y).Nonempty
    · simpa only [dif_pos h] using
        (families ((spliceIndices xs y).max' h)).scales y ((hmins _).trans hy)
    · simpa only [dif_neg h] using base.scales y (hbase.trans hy)
  · intro y hy m hm
    by_cases h : (spliceIndices xs y).Nonempty
    · have hm' : m ∈ (families ((spliceIndices xs y).max' h)).interval y := by
        simpa only [dif_pos h] using hm
      simpa only [dif_pos h] using
        (families ((spliceIndices xs y).max' h)).interval_bounds y ((hmins _).trans hy) m hm'
    · simp only [dif_neg h, Set.mem_empty_iff_false] at hm
  · intro y hy m hm
    by_cases h : (spliceIndices xs y).Nonempty
    · have hm' : (families ((spliceIndices xs y).max' h)).alpha y m ≠ 0 := by
        simpa only [dif_pos h] using hm
      simpa only [dif_pos h] using
        (families ((spliceIndices xs y).max' h)).rough_support y ((hmins _).trans hy) m hm'
    · simp only [dif_neg h] at hm
      exact (hm rfl).elim
  · intro y hy m hm
    by_cases h : (spliceIndices xs y).Nonempty
    · have hm' : m ∈ (families ((spliceIndices xs y).max' h)).interval y := by
        simpa only [dif_pos h] using hm
      simpa only [dif_pos h] using
        (families ((spliceIndices xs y).max' h)).coefficient_bound y ((hmins _).trans hy) m hm'
    · simp only [dif_neg h, Set.mem_empty_iff_false] at hm

private theorem spliceFamily_longCancellationWith
    {δ C c₁ c₂ T : ℝ} (W : LongCancellationWitness δ C c₁ c₂ T)
    (hT : 2 ≤ T)
    (base : CoefficientFamily δ C c₁ c₂) (hbase : base.xMin ≤ T)
    (families : ℕ → CoefficientFamily δ C c₁ c₂)
    (hmins : ∀ n, (families n).xMin ≤ T) (xs : ℕ → ℝ)
    (hfamilies : ∀ n, HasLongCancellationWith (families n) W) :
    HasLongCancellationWith (spliceFamily T hT base hbase families hmins xs) W := by
  classical
  intro A₀ B A hA₀ hB hA x hx k hk hkbound χ t ht
  let indices := spliceIndices xs x
  by_cases hactive : indices.Nonempty
  · let j := indices.max' hactive
    have hHm : (spliceFamily T hT base hbase families hmins xs).Hm x = (families j).Hm x := by
      simp [spliceFamily, indices, hactive, j]
    have hHn : (spliceFamily T hT base hbase families hmins xs).Hn x = (families j).Hn x := by
      simp [spliceFamily, indices, hactive, j]
    have ht' : |t| ≤ 2 * ((families j).Hm x * (families j).Hn x) *
        Real.rpow (Real.log x) B := by simpa [hHm, hHn] using ht
    have hsource := hfamilies j A₀ B A hA₀ hB hA x hx k hk hkbound χ t ht'
    simpa [familyTerms, spliceFamily, indices, hactive, j] using hsource
  · have hinterval : (spliceFamily T hT base hbase families hmins xs).interval x = ∅ := by
      simp [spliceFamily, indices, hactive]
    have halpha : (spliceFamily T hT base hbase families hmins xs).alpha x = fun _ => 0 := by
      funext m
      simp [spliceFamily, indices, hactive]
    have hsum : (∑ m ∈ familyTerms (spliceFamily T hT base hbase families hmins xs) x,
      (spliceFamily T hT base hbase families hmins xs).alpha x m * χ (m : ZMod k) *
        Complex.exp (Complex.I * t * Real.log (m : ℝ))) = 0 := by
      simp [familyTerms, hinterval, halpha]
    rw [hsum]
    have hxT : T ≤ x :=
      le_trans (W.threshold_ge_base A₀ B A hA₀ hB hA) hx
    have hx2 : 2 ≤ x := hT.trans hxT
    have hhm : 0 < (spliceFamily T hT base hbase families hmins xs).Hm x :=
      lt_of_lt_of_le (Real.rpow_pos_of_pos (by linarith [hx2]) δ)
        ((spliceFamily T hT base hbase families hmins xs).scales x hxT).1
    have hright : 0 ≤ W.constant A₀ B A * Real.rpow (Real.log x) (-A) :=
      mul_nonneg (W.positive A₀ B A hA₀ hB hA).le
        (Real.rpow_pos_of_pos
          (Real.log_pos (lt_of_lt_of_le (by norm_num) hx2)) _).le
    simpa only [norm_zero, zero_div] using hright

private structure TransferCounterexample {δ C c₁ c₂ T : ℝ}
    (W : LongCancellationWitness δ C c₁ c₂ T) (K : ℕ) (a : Fin K → ℝ)
    (q_d Dstar : ℝ) (n : ℕ) where
  family : CoefficientFamily δ C c₁ c₂
  family_min : family.xMin ≤ T
  family_long : HasLongCancellationWith family W
  x : ℝ
  x_lower : max T (n : ℝ) ≤ x
  beta : ℕ → ℂ
  beta_support : ∀ m, beta m ≠ 0 → m ∈ dyadicIntegers (family.Hn x) ∧
    roughAbove m (roughCutoff x)
  beta_bound : ∀ m ∈ dyadicIntegers (family.Hn x), ‖beta m‖ ≤ Real.rpow (Real.log x) C
  F : ℕ → ℂ
  F_invariant : IsMarkedInvariant x K a F
  violation : ((n + 1 : ℕ) : ℝ) * (family.Hm x * family.Hn x) *
      Real.rpow (Real.log x) (-Dstar) <
    ‖markedBilinearSum x K a q_d F (family.Hm x) (family.Hn x)
      (family.interval x) (family.alpha x) beta‖

/-- Transfer output constants are uniform over families with starting thresholds at most `T`
and a common long-cancellation witness. The same `K₀` works for every `T` and witness.
A diagonal family splices counterexamples and reuses valid source scales elsewhere. -/
theorem marked_coefficient_transfer_uniform
    (δ C Dstar q_d c₁ c₂ : ℝ)
    (hδ : 0 < δ) (hC : 0 < C) (hD : 0 < Dstar)
    (hqd₀ : 0 < q_d) (hqd₁ : q_d < 1)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₁₂ : c₁ ≤ c₂) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ a : Fin K → ℝ, ValidBands K a →
      ∀ T : ℝ, 2 ≤ T → ∀ W : LongCancellationWitness δ C c₁ c₂ T,
        ∃ C' x₀ : ℝ, 0 < C' ∧ T ≤ x₀ ∧
          ∀ family : CoefficientFamily δ C c₁ c₂,
            family.xMin ≤ T → HasLongCancellationWith family W →
            ∀ x : ℝ, x₀ ≤ x →
              ∀ beta : ℕ → ℂ,
                (∀ n, beta n ≠ 0 → n ∈ dyadicIntegers (family.Hn x) ∧
                  roughAbove n (roughCutoff x)) →
                (∀ n ∈ dyadicIntegers (family.Hn x),
                  ‖beta n‖ ≤ Real.rpow (Real.log x) C) →
                ∀ F : ℕ → ℂ, IsMarkedInvariant x K a F →
                  ‖markedBilinearSum x K a q_d F (family.Hm x) (family.Hn x)
                    (family.interval x) (family.alpha x) beta‖ ≤
                      C' * (family.Hm x * family.Hn x) *
                        Real.rpow (Real.log x) (-Dstar) := by
  obtain ⟨K₀, hTransfer⟩ :=
    ArtinPrimitiveRoots.TypeII.marked_coefficient_transfer δ C Dstar q_d c₁ c₂
      hδ hC hD hqd₀ hqd₁ hc₁ hc₂ hc₁₂
  refine ⟨K₀, ?_⟩
  intro K hK a ha T hT W
  by_contra hNoBound
  have hBad (n : ℕ) : Nonempty
      (TransferCounterexample W K a q_d Dstar n) := by
    have hexists : ∃ family : CoefficientFamily δ C c₁ c₂,
        family.xMin ≤ T ∧ HasLongCancellationWith family W ∧
        ∃ x : ℝ, max T (n : ℝ) ≤ x ∧
          ∃ beta : ℕ → ℂ,
            (∀ m, beta m ≠ 0 → m ∈ dyadicIntegers (family.Hn x) ∧
              roughAbove m (roughCutoff x)) ∧
            (∀ m ∈ dyadicIntegers (family.Hn x),
              ‖beta m‖ ≤ Real.rpow (Real.log x) C) ∧
            ∃ F : ℕ → ℂ, IsMarkedInvariant x K a F ∧
              ((n + 1 : ℕ) : ℝ) * (family.Hm x * family.Hn x) *
                Real.rpow (Real.log x) (-Dstar) <
              ‖markedBilinearSum x K a q_d F (family.Hm x) (family.Hn x)
                (family.interval x) (family.alpha x) beta‖ := by
      by_contra hnone
      apply hNoBound
      refine ⟨((n + 1 : ℕ) : ℝ), max T (n : ℝ), by positivity,
        le_max_left T (n : ℝ), ?_⟩
      intro family hmin hlong x hx beta hbeta₀ hbeta₁ F hF
      by_contra hle
      apply hnone
      exact ⟨family, hmin, hlong, x, hx, beta, hbeta₀, hbeta₁, F, hF,
        lt_of_not_ge hle⟩
    rcases hexists with ⟨family, hmin, hlong, x, hx, beta, hbeta₀, hbeta₁, F, hF, hlarge⟩
    exact ⟨⟨family, hmin, hlong, x, hx, beta, hbeta₀, hbeta₁, F, hF, hlarge⟩⟩
  let bad : (n : ℕ) → TransferCounterexample W K a q_d Dstar n := fun n =>
    Classical.choice (hBad n)
  let xs : ℕ → ℝ := fun n => (bad n).x
  let fs : ℕ → CoefficientFamily δ C c₁ c₂ := fun n => (bad n).family
  let combined : CoefficientFamily δ C c₁ c₂ :=
    spliceFamily T hT (fs 0) (bad 0).family_min fs (fun n => (bad n).family_min) xs
  have hcombinedLong : HasLongCancellationWith combined W := by
    apply spliceFamily_longCancellationWith W hT (fs 0) (bad 0).family_min fs
      (fun n => (bad n).family_min) xs
    · intro n
      exact (bad n).family_long
  obtain ⟨Ctransfer, xtransfer, hCtransfer, hxtransfer, hbound⟩ :=
    hTransfer K hK combined (by
      intro A₀ B A hA₀ hB hA
      exact ⟨W.constant A₀ B A, W.threshold A₀ B A,
        W.positive A₀ B A hA₀ hB hA,
        hT.trans (W.threshold_ge_base A₀ B A hA₀ hB hA),
        W.threshold_ge_base A₀ B A hA₀ hB hA,
        hcombinedLong A₀ B A hA₀ hB hA⟩) a ha
  obtain ⟨n, hnlarge⟩ : ∃ n : ℕ, Ctransfer < (n : ℝ) ∧ xtransfer ≤ (n : ℝ) := by
    obtain ⟨n, hn⟩ := exists_nat_gt (max Ctransfer xtransfer)
    exact ⟨n, lt_of_le_of_lt (le_max_left _ _) hn,
      (lt_of_le_of_lt (le_max_right _ _) hn).le⟩
  let y := (bad n).x
  have hy : xtransfer ≤ y := le_trans hnlarge.2 <| by
    exact (le_trans (le_max_right T (n : ℝ)) (bad n).x_lower)
  let active := spliceIndices xs y
  have hactive : active.Nonempty := by
    refine ⟨n, Finset.mem_filter.mpr ⟨?_, rfl⟩⟩
    apply Finset.mem_range.mpr
    have hnle : (n : ℝ) ≤ y := le_trans (le_max_right T (n : ℝ)) (bad n).x_lower
    exact Nat.lt_succ_of_le (Nat.le_floor hnle)
  let j := active.max' hactive
  have hjmem : j ∈ active := Finset.max'_mem active hactive
  have hjx : xs j = y := (Finset.mem_filter.mp hjmem).2
  have hjlarge : Ctransfer < ((j + 1 : ℕ) : ℝ) := by
    have hnj : n ≤ j := Finset.le_max' active n (Finset.mem_filter.mpr ⟨by
      apply Finset.mem_range.mpr
      have hnle : (n : ℝ) ≤ y := le_trans (le_max_right T (n : ℝ)) (bad n).x_lower
      exact Nat.lt_succ_of_le (Nat.le_floor hnle), rfl⟩)
    have hsucc : ((n + 1 : ℕ) : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.add_le_add_right hnj 1)
    have hltSucc : (n : ℝ) < ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.lt_succ_self n)
    exact lt_of_lt_of_le (lt_trans hnlarge.1 hltSucc) hsucc
  have hbadx : (bad j).x = y := by simpa [xs] using hjx
  have hHmEq : combined.Hm y = (bad j).family.Hm y := by
    simp [combined, spliceFamily, active, hactive, j, fs]
  have hHnEq : combined.Hn y = (bad j).family.Hn y := by
    simp [combined, spliceFamily, active, hactive, j, fs]
  have hscale : 0 < (combined.Hm y * combined.Hn y) *
      Real.rpow (Real.log y) (-Dstar) := by
    have hyT : T ≤ y := le_trans (le_max_left T (n : ℝ)) (bad n).x_lower
    have hy2 : 2 ≤ y := hT.trans hyT
    have hsc := combined.scales y hyT
    have hHmpos : 0 < combined.Hm y :=
      lt_of_lt_of_le (Real.rpow_pos_of_pos (by linarith) δ) hsc.1
    have hHnpos : 0 < combined.Hn y :=
      lt_of_lt_of_le (Real.rpow_pos_of_pos (by linarith) δ) hsc.2.1
    exact mul_pos (mul_pos hHmpos hHnpos)
      (Real.rpow_pos_of_pos (Real.log_pos (by linarith)) _)
  have hbSupport : ∀ m, (bad j).beta m ≠ 0 →
      m ∈ dyadicIntegers (combined.Hn y) ∧ roughAbove m (roughCutoff y) := by
    intro m hm
    have h := (bad j).beta_support m hm
    simpa [hbadx, hHnEq] using h
  have hbBound : ∀ m ∈ dyadicIntegers (combined.Hn y),
      ‖(bad j).beta m‖ ≤ Real.rpow (Real.log y) C := by
    intro m hm
    have hm' : m ∈ dyadicIntegers ((bad j).family.Hn (bad j).x) := by
      simpa only [hbadx, hHnEq] using hm
    simpa [hbadx] using (bad j).beta_bound m hm'
  have htransfer := hbound y hy (bad j).beta hbSupport
    hbBound (bad j).F (by simpa only [hbadx] using (bad j).F_invariant)
  have htransfer' :
      ‖markedBilinearSum y K a q_d (bad j).F (combined.Hm y) (combined.Hn y)
        (combined.interval y) (combined.alpha y) (bad j).beta‖ ≤
        Ctransfer * (combined.Hm y * combined.Hn y) *
          Real.rpow (Real.log y) (-Dstar) := by
    exact htransfer
  have hbad := (bad j).violation
  rw [hbadx] at hbad
  have hnormEq :
      markedBilinearSum y K a q_d (bad j).F (combined.Hm y) (combined.Hn y)
        (combined.interval y) (combined.alpha y) (bad j).beta =
      markedBilinearSum y K a q_d (bad j).F
        ((bad j).family.Hm y) ((bad j).family.Hn y)
        ((bad j).family.interval y) ((bad j).family.alpha y) (bad j).beta := by
    rw [hHmEq, hHnEq]
    have hIeq : combined.interval y = (bad j).family.interval y := by
      simp [combined, spliceFamily, active, hactive, j, fs]
    have hαeq : combined.alpha y = (bad j).family.alpha y := by
      funext m
      simp [combined, spliceFamily, active, hactive, j, fs]
    rw [hIeq, hαeq]
  have htransfer'' :
      ‖markedBilinearSum y K a q_d (bad j).F
          ((bad j).family.Hm y) ((bad j).family.Hn y)
          ((bad j).family.interval y) ((bad j).family.alpha y) (bad j).beta‖ ≤
        Ctransfer * ((bad j).family.Hm y * (bad j).family.Hn y) *
          Real.rpow (Real.log y) (-Dstar) := by
    rw [hnormEq, hHmEq, hHnEq] at htransfer'
    exact htransfer'
  have hviol' : ((j + 1 : ℕ) : ℝ) *
      ((bad j).family.Hm y * (bad j).family.Hn y) *
      Real.rpow (Real.log y) (-Dstar) <
        ‖markedBilinearSum y K a q_d (bad j).F
          ((bad j).family.Hm y) ((bad j).family.Hn y)
          ((bad j).family.interval y) ((bad j).family.alpha y) (bad j).beta‖ := by
    simpa [hbadx] using hbad
  have hscale' : 0 < ((bad j).family.Hm y * (bad j).family.Hn y) *
      Real.rpow (Real.log y) (-Dstar) := by
    simpa only [hHmEq, hHnEq] using hscale
  have hcompare : Ctransfer * ((bad j).family.Hm y * (bad j).family.Hn y) *
      Real.rpow (Real.log y) (-Dstar) <
      ((j + 1 : ℕ) : ℝ) * ((bad j).family.Hm y * (bad j).family.Hn y) *
        Real.rpow (Real.log y) (-Dstar) := by
    simpa only [mul_assoc] using mul_lt_mul_of_pos_right hjlarge hscale'
  exact (not_lt_of_ge htransfer'') (hcompare.trans hviol')

end ArtinPrimitiveRoots.Proofs.c_typeii_sol
