import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.Circle
import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.CauchyArithmetic

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical MeasureTheory ArtinPrimitiveRoots.TypeII Filter

set_option maxHeartbeats 1000000

private theorem pd1c_logPower_expDecay (A B c : ℝ) (hc : 0 < c) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
      Real.rpow L B * Real.exp (-c * Real.rpow L (1 / 10 : ℝ)) ≤
        Real.rpow L (-A) := by
  have hpowTendsto : Tendsto (fun L : ℝ => Real.rpow L (1 / 10 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (y := (1 / 10 : ℝ)) (by norm_num)
  have hcomp :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (10 * (A + B)) c hc).comp hpowTendsto
  have heq : (fun L : ℝ =>
      Real.rpow (Real.rpow L (1 / 10 : ℝ)) (10 * (A + B)) *
        Real.exp (-c * Real.rpow L (1 / 10 : ℝ))) =ᶠ[atTop]
      (fun L : ℝ => Real.rpow L (A + B) *
        Real.exp (-c * Real.rpow L (1 / 10 : ℝ))) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    have hpower : Real.rpow (Real.rpow L (1 / 10 : ℝ)) (10 * (A + B)) =
        Real.rpow L (A + B) := by
      have hlogpow : Real.log (Real.rpow L (1 / 10 : ℝ)) =
          (1 / 10 : ℝ) * Real.log L := by
        change Real.log (L ^ (1 / 10 : ℝ)) = _
        exact Real.log_rpow hL _
      calc
        Real.rpow (Real.rpow L (1 / 10 : ℝ)) (10 * (A + B)) =
            Real.exp (Real.log (Real.rpow L (1 / 10 : ℝ)) * (10 * (A + B))) :=
              Real.rpow_def_of_pos (Real.rpow_pos_of_pos hL _) _
        _ = Real.exp (Real.log L * (A + B)) := by
          rw [hlogpow]
          congr 1
          ring
        _ = Real.rpow L (A + B) := (Real.rpow_def_of_pos hL _).symm
    rw [hpower]
  have hlim : Tendsto (fun L : ℝ =>
      Real.rpow L (A + B) * Real.exp (-c * Real.rpow L (1 / 10 : ℝ))) atTop (nhds 0) :=
    hcomp.congr' heq
  have hevent : ∀ᶠ L : ℝ in atTop,
      Real.rpow L (A + B) * Real.exp (-c * Real.rpow L (1 / 10 : ℝ)) < 1 :=
    hlim.eventually (Iio_mem_nhds (by norm_num))
  rcases eventually_atTop.mp hevent with ⟨L₁, hL₁⟩
  refine ⟨max 1 L₁, le_max_left _ _, ?_⟩
  intro L hL
  have hL₀ : L₁ ≤ L := le_trans (le_max_right _ _) hL
  have hLone : 1 ≤ L := le_trans (le_max_left _ _) hL
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hLone
  have hsmall := (hL₁ L hL₀).le
  have hpow : Real.rpow L (-A) * Real.rpow L (A + B) = Real.rpow L B := by
    calc
      Real.rpow L (-A) * Real.rpow L (A + B) = Real.rpow L (-A + (A + B)) :=
        (Real.rpow_add hLpos _ _).symm
      _ = Real.rpow L B := by congr 1 <;> ring
  calc
    Real.rpow L B * Real.exp (-c * Real.rpow L (1 / 10 : ℝ)) =
        Real.rpow L (-A) *
          (Real.rpow L (A + B) * Real.exp (-c * Real.rpow L (1 / 10 : ℝ))) := by
            rw [← hpow]
            ring
    _ ≤ Real.rpow L (-A) * 1 := mul_le_mul_of_nonneg_left hsmall
      (Real.rpow_nonneg (le_of_lt hLpos) _)
    _ = Real.rpow L (-A) := by ring

noncomputable def pd1c_goodOneIndexSet (Y : ℝ) : Finset ℕ :=
  (Finset.range (⌊Real.rpow Y (1 / 5 : ℝ)⌋₊ + 1)).filter fun l => 1 ≤ l

noncomputable def pd1c_goodOnePairIndex (K : ℕ) (x Y : ℝ) :=
  (Fin K → Fin (slotCount x)) × {l : ℕ // l ∈ pd1c_goodOneIndexSet Y}

noncomputable def pd1c_goodOnePairFinset (K : ℕ) (x Y : ℝ) :
    Finset (pd1c_goodOnePairIndex K x Y) :=
  (Finset.univ : Finset (Fin K → Fin (slotCount x))).product
    (pd1c_goodOneIndexSet Y).attach

noncomputable def pd1c_freshOptions (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (I : Finset (Fin K)) (i : Fin K) : Finset ℕ :=
  if i ∈ I then {1} else primeBand x (a i)

noncomputable def pd1c_freshChoiceSet (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (I : Finset (Fin K)) : Finset (Fin K → ℕ) :=
  Fintype.piFinset (pd1c_freshOptions x K a I)

lemma pd1c_freshChoice_iff_mem (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (I : Finset (Fin K)) (fresh : Fin K → ℕ) :
    IsFreshChoice x a I fresh ↔ fresh ∈ pd1c_freshChoiceSet x K a I := by
  classical
  rw [IsFreshChoice, pd1c_freshChoiceSet, Fintype.mem_piFinset]
  constructor
  · intro h i
    by_cases hi : i ∈ I
    · simp [pd1c_freshOptions, hi, h.1 i hi]
    · simp [pd1c_freshOptions, hi, h.2 i hi]
  · intro h
    constructor
    · intro i hi
      have hmem := h i
      simpa [pd1c_freshOptions, hi] using hmem
    · intro i hi
      have hmem := h i
      simpa [pd1c_freshOptions, hi] using hmem

lemma pd1c_freshWeighted_tsum_eq_sum (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (I : Finset (Fin K)) (bad : (Fin K → ℕ) → Prop) :
    (∑' fresh : Fin K → ℕ,
      if IsFreshChoice x a I fresh ∧ bad fresh then freshChoiceWeight x a I fresh else 0) =
      ∑ fresh ∈ pd1c_freshChoiceSet x K a I,
        if bad fresh then freshChoiceWeight x a I fresh else 0 := by
  classical
  let F := pd1c_freshChoiceSet x K a I
  rw [tsum_eq_sum (s := F)]
  · apply Finset.sum_congr rfl
    intro fresh hfresh
    have hchoice : IsFreshChoice x a I fresh :=
      (pd1c_freshChoice_iff_mem x K a I fresh).2 hfresh
    simp [hchoice]
  · intro fresh hfresh
    have hnotChoice : ¬ IsFreshChoice x a I fresh := by
      intro hchoice
      exact hfresh ((pd1c_freshChoice_iff_mem x K a I fresh).1 hchoice)
    simp [hnotChoice]

lemma pd1c_freshChoiceWeight_sum (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (I : Finset (Fin K)) (hMass : ∀ i, 0 < bandMass x (a i)) :
    (∑ fresh ∈ pd1c_freshChoiceSet x K a I,
      freshChoiceWeight x a I fresh) = 1 := by
  classical
  let t := pd1c_freshOptions x K a I
  let w (i : Fin K) (q : ℕ) : ℝ :=
    if i ∉ I then 1 / (bandMass x (a i) * (q : ℝ)) else 1
  have hchoice (fresh : Fin K → ℕ) (hfresh : fresh ∈ Fintype.piFinset t) :
      IsFreshChoice x a I fresh := by
    have hmem := Fintype.mem_piFinset.mp hfresh
    constructor
    · intro i hi
      simpa [t, pd1c_freshOptions, hi] using hmem i
    · intro i hi
      simpa [t, pd1c_freshOptions, hi] using hmem i
  have hweight (fresh : Fin K → ℕ) (hfresh : fresh ∈ Fintype.piFinset t) :
      freshChoiceWeight x a I fresh = ∏ i : Fin K, w i (fresh i) := by
    have hc := hchoice fresh hfresh
    simp [freshChoiceWeight, w, hc]
  have hsumEq :
      (∑ fresh ∈ Fintype.piFinset t, ∏ i : Fin K, w i (fresh i)) =
        ∏ i : Fin K, ∑ q ∈ t i, w i q :=
    (Finset.prod_univ_sum t w).symm
  have hcoord : ∀ i : Fin K, ∑ q ∈ t i, w i q = 1 := by
    intro i
    by_cases hi : i ∈ I
    · simp [t, w, pd1c_freshOptions, hi]
    · have hV := hMass i
      have hterm : ∀ q ∈ primeBand x (a i),
          1 / (bandMass x (a i) * (q : ℝ)) =
            (bandMass x (a i))⁻¹ * (1 / (q : ℝ)) := by
        intro q hq
        have hqmem : q ∈ primeBand x (a i) := hq
        change q ∈ (Finset.range
          (⌊Real.exp (2 * Real.rpow (Real.log x) (a i))⌋₊ + 1)).filter
            (fun q : ℕ => q.Prime ∧ Real.exp (Real.rpow (Real.log x) (a i)) ≤ (q : ℝ) ∧
              (q : ℝ) ≤ Real.exp (2 * Real.rpow (Real.log x) (a i))) at hqmem
        have hqPrime : q.Prime := (Finset.mem_filter.mp hqmem).2.1
        have hqpos : 0 < (q : ℝ) := by exact_mod_cast hqPrime.pos
        field_simp
      calc
        (∑ q ∈ t i, w i q) =
            ∑ q ∈ primeBand x (a i),
              (bandMass x (a i))⁻¹ * (1 / (q : ℝ)) := by
                simp [t, w, pd1c_freshOptions, hi]
                exact Finset.sum_congr rfl fun q hq => by
                  simpa [one_div, mul_comm, mul_left_comm, mul_assoc] using hterm q hq
        _ = (bandMass x (a i))⁻¹ * bandMass x (a i) := by
              rw [← Finset.mul_sum]
              rfl
        _ = 1 := by field_simp [ne_of_gt hV]
  have hsumWeight :
      (∑ fresh ∈ pd1c_freshChoiceSet x K a I,
        freshChoiceWeight x a I fresh) =
        ∑ fresh ∈ Fintype.piFinset t, ∏ i : Fin K, w i (fresh i) := by
    apply Finset.sum_congr rfl
    intro fresh hfresh
    exact hweight fresh hfresh
  rw [hsumWeight, hsumEq]
  simp [hcoord]

lemma pd1c_freshChoiceWeight_nonneg (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (I : Finset (Fin K)) (fresh : Fin K → ℕ)
    (hMass : ∀ i, 0 < bandMass x (a i)) (hFresh : IsFreshChoice x a I fresh) :
    0 ≤ freshChoiceWeight x a I fresh := by
  simp only [freshChoiceWeight, hFresh, ↓reduceIte]
  apply Finset.prod_nonneg
  intro i hi
  by_cases hnot : i ∉ I
  · have hband := hFresh.2 i hnot
    have hmem : fresh i ∈ primeBand x (a i) := hband
    change fresh i ∈ (Finset.range
      (⌊Real.exp (2 * Real.rpow (Real.log x) (a i))⌋₊ + 1)).filter
        (fun q : ℕ => q.Prime ∧ Real.exp (Real.rpow (Real.log x) (a i)) ≤ (q : ℝ) ∧
          (q : ℝ) ≤ Real.exp (2 * Real.rpow (Real.log x) (a i))) at hmem
    have hprime : (fresh i).Prime := (Finset.mem_filter.mp hmem).2.1
    have hp : 0 < (fresh i : ℝ) := by exact_mod_cast hprime.pos
    have hden : 0 < bandMass x (a i) * (fresh i : ℝ) := mul_pos (hMass i) hp
    positivity
  · simp [hnot]

abbrev pd1c_trialCodeType (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (I : Finset (Fin K)) (iStar : Fin K) :=
  (Fin K → Fin (slotCount x)) ×
    ((i : {i : Fin K // i ∈ I.erase iStar}) →
      {z : ℕ // z ∈ primeBand x (a i)})

noncomputable def pd1c_trialCodeZ {x : ℝ} (K : ℕ) (a : Fin K → ℝ)
    (I : Finset (Fin K)) (iStar : Fin K)
    (code : pd1c_trialCodeType x K a I iStar) (i : Fin K) : ℕ :=
  if hi : i ∈ I.erase iStar then (code.2 ⟨i, hi⟩).val else 1

noncomputable def pd1c_trialCodeValue (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (p : PrimeLists x K) (I : Finset (Fin K)) (iStar : Fin K)
    (fresh : Fin K → ℕ) (code : pd1c_trialCodeType x K a I iStar) : ℕ :=
  omissionProduct p code.1 *
    (∏ i : Fin K, if i ∈ I ∧ i ≠ iStar then
      pd1c_trialCodeZ K a I iStar code i else 1) *
    (∏ i : Fin K, if i ∉ I then fresh i else 1)

noncomputable def pd1c_trialCodeFinset (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (I : Finset (Fin K)) (iStar : Fin K) :
    Finset (pd1c_trialCodeType x K a I iStar) := by
  classical
  letI : Fintype {i : Fin K // i ∈ I.erase iStar} :=
    Fintype.ofFinset (I.erase iStar) (by intro i; rfl)
  exact (Finset.univ : Finset (Fin K → Fin (slotCount x))).product
    (Fintype.piFinset fun i : {i : Fin K // i ∈ I.erase iStar} =>
      (primeBand x (a i)).attach)

lemma pd1c_goodnessTrialValue_finiteCode {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (p : PrimeLists x K) (d₀ : ℝ) (I : Finset (Fin K)) (iStar : Fin K)
    (fresh : Fin K → ℕ) (n : ℕ)
    (hn : IsGoodnessTrialValue a p d₀ I iStar fresh n) :
    ∃ code : pd1c_trialCodeType x K a I iStar,
      code ∈ pd1c_trialCodeFinset x K a I iStar ∧
        n = pd1c_trialCodeValue x K a p I iStar fresh code := by
  classical
  rcases hn with ⟨omitted, z, hn, hd₀lo, hd₀hi, hz⟩
  letI : Fintype {i : Fin K // i ∈ I.erase iStar} :=
    Fintype.ofFinset (I.erase iStar) (by intro i; rfl)
  let code : pd1c_trialCodeType x K a I iStar :=
    (omitted, fun i => ⟨z i.1,
      hz i.1 ⟨(Finset.mem_erase.mp i.2).2, (Finset.mem_erase.mp i.2).1⟩⟩)
  have hProd :
      (∏ i : Fin K, if i ∈ I ∧ i ≠ iStar then z i else 1) =
        (∏ i : Fin K, if i ∈ I ∧ i ≠ iStar then
          pd1c_trialCodeZ K a I iStar code i else 1) := by
    apply Finset.prod_congr rfl
    intro i hi
    by_cases h : i ∈ I ∧ i ≠ iStar
    · have hiErase : i ∈ I.erase iStar := Finset.mem_erase.mpr ⟨h.2, h.1⟩
      simp [h, pd1c_trialCodeZ, code, hiErase]
    · simp [h]
  have hCodeMem : code ∈ pd1c_trialCodeFinset x K a I iStar := by
    dsimp [code, pd1c_trialCodeType, pd1c_trialCodeFinset]
    rw [Finset.mem_product]
    constructor
    · exact Finset.mem_univ _
    · apply Fintype.mem_piFinset.mpr
      intro i
      exact Finset.mem_attach _ _
  refine ⟨code, hCodeMem, ?_⟩
  rw [hn]
  simp only [pd1c_trialCodeValue, code]
  rw [hProd]

lemma pd1c_trialCodeFinset_card (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (I : Finset (Fin K)) (iStar : Fin K) :
    (pd1c_trialCodeFinset x K a I iStar).card =
      (slotCount x) ^ K *
        ∏ i : {i : Fin K // i ∈ I.erase iStar}, (primeBand x (a i)).card := by
  classical
  letI : Fintype {i : Fin K // i ∈ I.erase iStar} :=
    Fintype.ofFinset (I.erase iStar) (by intro i; rfl)
  calc
    (pd1c_trialCodeFinset x K a I iStar).card =
        (Finset.univ : Finset (Fin K → Fin (slotCount x))).card *
          (Fintype.piFinset
            (fun i : {i : Fin K // i ∈ I.erase iStar} =>
              (primeBand x (a i)).attach)).card := by
            simp [pd1c_trialCodeFinset, pd1c_trialCodeType, Finset.card_product]
    _ = (slotCount x) ^ K *
        ∏ i : {i : Fin K // i ∈ I.erase iStar}, (primeBand x (a i)).card := by
          simp [Fintype.card_fun, Fintype.card_piFinset]

lemma pd1c_goodOnePairFinset_card_bound (K : ℕ) (x Y : ℝ)
    (hT : 1 ≤ Real.rpow Y (1 / 5 : ℝ)) :
    ((pd1c_goodOnePairFinset K x Y).card : ℝ) ≤
      (slotCount x : ℝ) ^ K * (2 * Real.rpow Y (1 / 5 : ℝ)) := by
  let T := Real.rpow Y (1 / 5 : ℝ)
  have hTnonneg : 0 ≤ T := le_trans (by norm_num) hT
  have hLcard : (pd1c_goodOneIndexSet Y).card ≤ ⌊T⌋₊ + 1 := by
    unfold pd1c_goodOneIndexSet
    calc
      _ ≤ (Finset.range (⌊Real.rpow Y (1 / 5 : ℝ)⌋₊ + 1)).card :=
        Finset.card_filter_le _ _
      _ = ⌊T⌋₊ + 1 := by simp [T]
  have hLreal : ((pd1c_goodOneIndexSet Y).card : ℝ) ≤ 2 * T := by
    have hfloor : (⌊T⌋₊ : ℝ) ≤ T := Nat.floor_le hTnonneg
    have hcardCast : ((pd1c_goodOneIndexSet Y).card : ℝ) ≤ (⌊T⌋₊ : ℝ) + 1 := by
      exact_mod_cast hLcard
    calc
      ((pd1c_goodOneIndexSet Y).card : ℝ) ≤ (⌊T⌋₊ : ℝ) + 1 := hcardCast
      _ ≤ T + 1 := by linarith [hfloor]
      _ ≤ 2 * T := by linarith
  have hpairCard :
      (pd1c_goodOnePairFinset K x Y).card =
        (slotCount x) ^ K * (pd1c_goodOneIndexSet Y).card := by
    simp [pd1c_goodOnePairFinset, pd1c_goodOnePairIndex, Fintype.card_fun]
  have hLnonneg : 0 ≤ ((pd1c_goodOneIndexSet Y).card : ℝ) := Nat.cast_nonneg _
  calc
    ((pd1c_goodOnePairFinset K x Y).card : ℝ) =
        (slotCount x : ℝ) ^ K * (pd1c_goodOneIndexSet Y).card := by
          rw [hpairCard, Nat.cast_mul, Nat.cast_pow]
    _ ≤ (slotCount x : ℝ) ^ K * (2 * T) :=
          mul_le_mul_of_nonneg_left hLreal (by positivity)
    _ = (slotCount x : ℝ) ^ K * (2 * Real.rpow Y (1 / 5 : ℝ)) := by rfl

lemma pd1c_finite_distinct_frequency_badset_measure {α : Type*} [Fintype α]
    (value : α → ℕ) (e : ℝ) (he : 0 ≤ e) :
    volume {r : ℝ | r ∈ Set.Icc 0 1 ∧
      ∃ a b, value a ≠ value b ∧
        circleDistance (((value a : ℝ) - (value b : ℝ)) * r) ≤ e} ≤
      ENNReal.ofReal ((Fintype.card α * Fintype.card α : ℕ) • (4 * e)) := by
  classical
  let diff (a b : α) : ℤ := (value a : ℤ) - (value b : ℤ)
  let E (a b : α) : Set ℝ :=
    if value a = value b then ∅ else
      {r : ℝ | r ∈ Set.Icc 0 1 ∧
        circleDistance (((value a : ℝ) - (value b : ℝ)) * r) ≤ e}
  have hsub :
      {r : ℝ | r ∈ Set.Icc 0 1 ∧
        ∃ a b, value a ≠ value b ∧
          circleDistance (((value a : ℝ) - (value b : ℝ)) * r) ≤ e} ⊆
        ⋃ pair : α × α, E pair.1 pair.2 := by
    intro r hr
    rcases hr with ⟨hrange, a, b, hab, hdist⟩
    refine Set.mem_iUnion.2 ⟨(a, b), ?_⟩
    simp only [E, hab, ↓reduceIte]
    exact ⟨hrange, hdist⟩
  calc
    volume {r : ℝ | r ∈ Set.Icc 0 1 ∧
        ∃ a b, value a ≠ value b ∧
          circleDistance (((value a : ℝ) - (value b : ℝ)) * r) ≤ e} ≤
        volume (⋃ pair : α × α, E pair.1 pair.2) := measure_mono hsub
    _ ≤ ∑ pair : α × α, volume (E pair.1 pair.2) :=
          MeasureTheory.measure_iUnion_fintype_le volume _
    _ ≤ ∑ pair : α × α, ENNReal.ofReal (4 * e) := by
          apply Finset.sum_le_sum
          intro pair hpair
          by_cases hEq : value pair.1 = value pair.2
          · simp [E, hEq, he]
          · have hdiff : ((value pair.1 : ℤ) - (value pair.2 : ℤ)) ≠ 0 := by
              intro hzero
              have hcast : (value pair.1 : ℤ) = (value pair.2 : ℤ) := sub_eq_zero.mp hzero
              exact hEq (by exact_mod_cast hcast)
            have hbound := pd1c_circle_small_set_measure
              (diff pair.1 pair.2) hdiff e he
            have hfreq : (diff pair.1 pair.2 : ℝ) =
                (value pair.1 : ℝ) - (value pair.2 : ℝ) := by
              simp [diff, Int.cast_sub]
            simpa [E, hEq, hfreq] using hbound
    _ = ENNReal.ofReal ((Fintype.card α * Fintype.card α : ℕ) • (4 * e)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
            ← ENNReal.ofReal_nsmul]

lemma pd1c_goodnessTrialPair_badset_measure_le (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (p : PrimeLists x K) (d₀ : ℝ) (I : Finset (Fin K)) (iStar : Fin K)
    (fresh : Fin K → ℕ) (e : ℝ) (he : 0 ≤ e) :
    volume {r : ℝ | r ∈ Set.Icc 0 1 ∧ ∃ n₁ n₂,
      IsGoodnessTrialValue a p d₀ I iStar fresh n₁ ∧
      IsGoodnessTrialValue a p d₀ I iStar fresh n₂ ∧ n₁ ≠ n₂ ∧
      circleDistance (((n₁ : ℝ) - n₂) * r) ≤ e} ≤
      ENNReal.ofReal
        ((pd1c_trialCodeFinset x K a I iStar).card ^ 2 • (4 * e)) := by
  classical
  let F := pd1c_trialCodeFinset x K a I iStar
  let α := {code : pd1c_trialCodeType x K a I iStar // code ∈ F}
  let value (code : α) : ℕ := pd1c_trialCodeValue x K a p I iStar fresh code.1
  letI : Fintype α := Fintype.ofFinset F (by intro code; rfl)
  have hCard : Fintype.card α = F.card := by simp [α, F]
  have hsub :
      {r : ℝ | r ∈ Set.Icc 0 1 ∧ ∃ n₁ n₂,
        IsGoodnessTrialValue a p d₀ I iStar fresh n₁ ∧
        IsGoodnessTrialValue a p d₀ I iStar fresh n₂ ∧ n₁ ≠ n₂ ∧
        circleDistance (((n₁ : ℝ) - n₂) * r) ≤ e} ⊆
        {r : ℝ | r ∈ Set.Icc 0 1 ∧ ∃ c₁ c₂ : α,
          value c₁ ≠ value c₂ ∧
            circleDistance (((value c₁ : ℝ) - (value c₂ : ℝ)) * r) ≤ e} := by
    intro r hr
    rcases hr with ⟨hrange, n₁, n₂, hn₁, hn₂, hneq, hdist⟩
    obtain ⟨code₁, hmem₁, hval₁⟩ :=
      pd1c_goodnessTrialValue_finiteCode p d₀ I iStar fresh n₁ hn₁
    obtain ⟨code₂, hmem₂, hval₂⟩ :=
      pd1c_goodnessTrialValue_finiteCode p d₀ I iStar fresh n₂ hn₂
    let c₁ : α := ⟨code₁, hmem₁⟩
    let c₂ : α := ⟨code₂, hmem₂⟩
    have hvneq : value c₁ ≠ value c₂ := by
      intro hv
      apply hneq
      dsimp [c₁, c₂, value] at hv
      rw [hval₁, hval₂, hv]
    have hvalReal₁ : (n₁ : ℝ) = (value c₁ : ℝ) := by exact_mod_cast hval₁
    have hvalReal₂ : (n₂ : ℝ) = (value c₂ : ℝ) := by exact_mod_cast hval₂
    have hdist' :
        circleDistance (((value c₁ : ℝ) - (value c₂ : ℝ)) * r) ≤ e := by
      simpa [hvalReal₁, hvalReal₂] using hdist
    exact ⟨hrange, c₁, c₂, hvneq, hdist'⟩
  calc
    volume {r : ℝ | r ∈ Set.Icc 0 1 ∧ ∃ n₁ n₂,
        IsGoodnessTrialValue a p d₀ I iStar fresh n₁ ∧
        IsGoodnessTrialValue a p d₀ I iStar fresh n₂ ∧ n₁ ≠ n₂ ∧
        circleDistance (((n₁ : ℝ) - n₂) * r) ≤ e} ≤
        volume {r : ℝ | r ∈ Set.Icc 0 1 ∧ ∃ c₁ c₂ : α,
          value c₁ ≠ value c₂ ∧
            circleDistance (((value c₁ : ℝ) - (value c₂ : ℝ)) * r) ≤ e} := measure_mono hsub
    _ ≤ ENNReal.ofReal ((Fintype.card α * Fintype.card α : ℕ) • (4 * e)) :=
      pd1c_finite_distinct_frequency_badset_measure value e he
    _ = ENNReal.ofReal (F.card ^ 2 • (4 * e)) := by rw [hCard, pow_two]

lemma pd1c_goodnessTrialPair_badset_measurable (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (p : PrimeLists x K) (d₀ : ℝ) (I : Finset (Fin K)) (iStar : Fin K)
    (fresh : Fin K → ℕ) (e : ℝ) :
    MeasurableSet {r : ℝ | r ∈ Set.Icc 0 1 ∧ ∃ n₁ n₂,
      IsGoodnessTrialValue a p d₀ I iStar fresh n₁ ∧
      IsGoodnessTrialValue a p d₀ I iStar fresh n₂ ∧ n₁ ≠ n₂ ∧
      circleDistance (((n₁ : ℝ) - n₂) * r) ≤ e} := by
  have hEq :
      {r : ℝ | r ∈ Set.Icc 0 1 ∧ ∃ n₁ n₂,
        IsGoodnessTrialValue a p d₀ I iStar fresh n₁ ∧
        IsGoodnessTrialValue a p d₀ I iStar fresh n₂ ∧ n₁ ≠ n₂ ∧
        circleDistance (((n₁ : ℝ) - n₂) * r) ≤ e} =
      ⋃ n₁ : ℕ, ⋃ n₂ : ℕ,
        if IsGoodnessTrialValue a p d₀ I iStar fresh n₁ ∧
            IsGoodnessTrialValue a p d₀ I iStar fresh n₂ ∧ n₁ ≠ n₂ then
          {r : ℝ | r ∈ Set.Icc 0 1 ∧ circleDistance (((n₁ : ℝ) - n₂) * r) ≤ e}
        else ∅ := by
    ext r
    constructor
    · rintro ⟨hr, n₁, n₂, hn₁, hn₂, hne, hdist⟩
      refine Set.mem_iUnion.2 ⟨n₁, Set.mem_iUnion.2 ⟨n₂, ?_⟩⟩
      rw [if_pos (show IsGoodnessTrialValue a p d₀ I iStar fresh n₁ ∧
          IsGoodnessTrialValue a p d₀ I iStar fresh n₂ ∧ n₁ ≠ n₂ from ⟨hn₁, hn₂, hne⟩)]
      exact ⟨hr, hdist⟩
    · intro hr
      rcases Set.mem_iUnion.mp hr with ⟨n₁, hr⟩
      rcases Set.mem_iUnion.mp hr with ⟨n₂, hr⟩
      by_cases hc : IsGoodnessTrialValue a p d₀ I iStar fresh n₁ ∧
          IsGoodnessTrialValue a p d₀ I iStar fresh n₂ ∧ n₁ ≠ n₂
      · rw [if_pos hc] at hr
        rcases hr with ⟨hrange, hdist⟩
        exact ⟨hrange, n₁, n₂, hc.1, hc.2.1, hc.2.2, hdist⟩
      · simp [hc] at hr
  rw [hEq]
  apply MeasurableSet.iUnion
  intro n₁
  apply MeasurableSet.iUnion
  intro n₂
  by_cases hH : IsGoodnessTrialValue a p d₀ I iStar fresh n₁ ∧
      IsGoodnessTrialValue a p d₀ I iStar fresh n₂ ∧ n₁ ≠ n₂
  · rw [if_pos hH]
    exact measurableSet_Icc.inter
      (pd1c_circleDistance_realSublevel_measurable ((n₁ : ℝ) - n₂) e)
  · rw [if_neg hH]
    exact MeasurableSet.empty

def pd1c_goodnessTrialPair_collisionSet (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (p : PrimeLists x K) (d₀ : ℝ) (I : Finset (Fin K)) (iStar : Fin K)
    (fresh : Fin K → ℕ) (e : ℝ) : Set ℝ :=
  {r : ℝ | ∃ n₁ n₂, IsGoodnessTrialValue a p d₀ I iStar fresh n₁ ∧
    IsGoodnessTrialValue a p d₀ I iStar fresh n₂ ∧ n₁ ≠ n₂ ∧
    circleDistance (((n₁ : ℝ) - n₂) * r) ≤ e}

lemma pd1c_goodnessTrialPair_collisionSet_measurable (x : ℝ) (K : ℕ)
    (a : Fin K → ℝ) (p : PrimeLists x K) (d₀ : ℝ) (I : Finset (Fin K))
    (iStar : Fin K) (fresh : Fin K → ℕ) (e : ℝ) :
    MeasurableSet (pd1c_goodnessTrialPair_collisionSet x K a p d₀ I iStar fresh e) := by
  have hEq : pd1c_goodnessTrialPair_collisionSet x K a p d₀ I iStar fresh e =
      ⋃ n₁ : ℕ, ⋃ n₂ : ℕ,
        if IsGoodnessTrialValue a p d₀ I iStar fresh n₁ ∧
            IsGoodnessTrialValue a p d₀ I iStar fresh n₂ ∧ n₁ ≠ n₂ then
          {r : ℝ | circleDistance (((n₁ : ℝ) - n₂) * r) ≤ e}
        else ∅ := by
    ext r
    constructor
    · rintro ⟨n₁, n₂, hn₁, hn₂, hne, hdist⟩
      refine Set.mem_iUnion.2 ⟨n₁, Set.mem_iUnion.2 ⟨n₂, ?_⟩⟩
      rw [if_pos ⟨hn₁, hn₂, hne⟩]
      exact hdist
    · intro hr
      rcases Set.mem_iUnion.mp hr with ⟨n₁, hr⟩
      rcases Set.mem_iUnion.mp hr with ⟨n₂, hr⟩
      by_cases hc : IsGoodnessTrialValue a p d₀ I iStar fresh n₁ ∧
          IsGoodnessTrialValue a p d₀ I iStar fresh n₂ ∧ n₁ ≠ n₂
      · rw [if_pos hc] at hr
        exact ⟨n₁, n₂, hc.1, hc.2.1, hc.2.2, hr⟩
      · simp [hc] at hr
  rw [hEq]
  apply MeasurableSet.iUnion
  intro n₁
  apply MeasurableSet.iUnion
  intro n₂
  by_cases hc : IsGoodnessTrialValue a p d₀ I iStar fresh n₁ ∧
      IsGoodnessTrialValue a p d₀ I iStar fresh n₂ ∧ n₁ ≠ n₂
  · rw [if_pos hc]
    exact pd1c_circleDistance_realSublevel_measurable ((n₁ : ℝ) - n₂) e
  · rw [if_neg hc]
    exact MeasurableSet.empty

noncomputable def pd1c_goodTestTwoBadWeight (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (p : PrimeLists x K) (d₀ : ℝ) (I : Finset (Fin K)) (iStar : Fin K)
    (e : ℝ) (r : ℝ) : ℝ :=
  ∑ fresh ∈ pd1c_freshChoiceSet x K a I,
    (pd1c_goodnessTrialPair_collisionSet x K a p d₀ I iStar fresh e).indicator
      (fun _ => freshChoiceWeight x a I fresh) r

lemma pd1c_goodTestTwoBadWeight_eq_tsum (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (p : PrimeLists x K) (d₀ : ℝ) (I : Finset (Fin K)) (iStar : Fin K)
    (e r : ℝ) :
    pd1c_goodTestTwoBadWeight x K a p d₀ I iStar e r =
      ∑' fresh : Fin K → ℕ,
        if IsFreshChoice x a I fresh ∧
            ∃ n₁ n₂, IsGoodnessTrialValue a p d₀ I iStar fresh n₁ ∧
              IsGoodnessTrialValue a p d₀ I iStar fresh n₂ ∧ n₁ ≠ n₂ ∧
              circleDistance (((n₁ : ℝ) - n₂) * r) ≤ e
        then freshChoiceWeight x a I fresh else 0 := by
  classical
  simp only [pd1c_goodTestTwoBadWeight, pd1c_goodnessTrialPair_collisionSet,
    Set.indicator]
  simpa using (pd1c_freshWeighted_tsum_eq_sum x K a I
    (fun fresh => ∃ n₁ n₂,
      IsGoodnessTrialValue a p d₀ I iStar fresh n₁ ∧
      IsGoodnessTrialValue a p d₀ I iStar fresh n₂ ∧ n₁ ≠ n₂ ∧
      circleDistance (((n₁ : ℝ) - n₂) * r) ≤ e)).symm

lemma pd1c_goodTestTwoBadWeight_measurable (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (p : PrimeLists x K) (d₀ : ℝ) (I : Finset (Fin K)) (iStar : Fin K)
    (e : ℝ) : Measurable (pd1c_goodTestTwoBadWeight x K a p d₀ I iStar e) := by
  classical
  unfold pd1c_goodTestTwoBadWeight
  apply Finset.measurable_sum
  intro fresh hfresh
  exact measurable_const.indicator
    (pd1c_goodnessTrialPair_collisionSet_measurable x K a p d₀ I iStar fresh e)

lemma pd1c_goodTestTwoBadWeight_intervalIntegrable (x : ℝ) (K : ℕ)
    (a : Fin K → ℝ) (p : PrimeLists x K) (d₀ : ℝ) (I : Finset (Fin K))
    (iStar : Fin K) (e : ℝ) :
    IntervalIntegrable (pd1c_goodTestTwoBadWeight x K a p d₀ I iStar e) volume 0 1 := by
  classical
  unfold pd1c_goodTestTwoBadWeight
  let F := pd1c_freshChoiceSet x K a I
  let g (fresh : Fin K → ℕ) (r : ℝ) :=
    (pd1c_goodnessTrialPair_collisionSet x K a p d₀ I iStar fresh e).indicator
      (fun _ => freshChoiceWeight x a I fresh) r
  change IntervalIntegrable
    (fun r => ∑ fresh ∈ F, g fresh r) volume 0 1
  have hsumfun : (fun r => ∑ fresh ∈ F, g fresh r) = ∑ fresh ∈ F, g fresh := by
    funext r
    simp
  rw [hsumfun]
  refine IntervalIntegrable.sum F ?_
  intro fresh hfresh
  have hAm := pd1c_goodnessTrialPair_collisionSet_measurable
    x K a p d₀ I iStar fresh e
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [integrableOn_indicator_iff hAm]
  have hfinite : volume
      (pd1c_goodnessTrialPair_collisionSet x K a p d₀ I iStar fresh e ∩
        Set.Ioc (0 : ℝ) 1) ≠ ⊤ := by
    apply ne_of_lt
    calc
      volume (pd1c_goodnessTrialPair_collisionSet x K a p d₀ I iStar fresh e ∩
          Set.Ioc (0 : ℝ) 1) ≤ volume (Set.Icc 0 1) :=
        measure_mono (fun r hr => ⟨le_of_lt hr.2.1, hr.2.2⟩)
      _ = ENNReal.ofReal 1 := by simp [Real.volume_Icc]
      _ < ⊤ := ENNReal.ofReal_lt_top
  simpa [g] using (integrableOn_const hfinite :
    IntegrableOn (fun _ : ℝ => freshChoiceWeight x a I fresh)
      (pd1c_goodnessTrialPair_collisionSet x K a p d₀ I iStar fresh e ∩
        Set.Ioc (0 : ℝ) 1) volume)

lemma pd1c_goodTestTwo_inner_integral_bound (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (p : PrimeLists x K) (d₀ : ℝ) (I : Finset (Fin K)) (iStar : Fin K)
    (hMass : ∀ i, 0 < bandMass x (a i)) (e : ℝ) (he : 0 ≤ e) :
    (∫ r in (0 : ℝ)..1,
      ∑' fresh : Fin K → ℕ,
        if IsFreshChoice x a I fresh ∧
            ∃ n₁ n₂, IsGoodnessTrialValue a p d₀ I iStar fresh n₁ ∧
              IsGoodnessTrialValue a p d₀ I iStar fresh n₂ ∧ n₁ ≠ n₂ ∧
              circleDistance (((n₁ : ℝ) - n₂) * r) ≤ e
        then freshChoiceWeight x a I fresh else 0) ≤
      ((pd1c_trialCodeFinset x K a I iStar).card : ℝ) ^ 2 *
        (4 * e) := by
  classical
  let F := pd1c_freshChoiceSet x K a I
  let bad (fresh : Fin K → ℕ) (r : ℝ) : Prop :=
    ∃ n₁ n₂, IsGoodnessTrialValue a p d₀ I iStar fresh n₁ ∧
      IsGoodnessTrialValue a p d₀ I iStar fresh n₂ ∧ n₁ ≠ n₂ ∧
        circleDistance (((n₁ : ℝ) - n₂) * r) ≤ e
  let A (fresh : Fin K → ℕ) : Set ℝ := {r | r ∈ Set.Icc 0 1 ∧ bad fresh r}
  let w (fresh : Fin K → ℕ) : ℝ := freshChoiceWeight x a I fresh
  have hmassSum := pd1c_freshChoiceWeight_sum x K a I hMass
  have hpoint : ∀ r ∈ Set.Ioc (0 : ℝ) 1,
      (∑ fresh ∈ F, if bad fresh r then w fresh else 0) =
        ∑ fresh ∈ F, (A fresh).indicator (fun _ => w fresh) r := by
    intro r hr
    have hrIcc : r ∈ Set.Icc 0 1 := ⟨le_of_lt hr.1, hr.2⟩
    apply Finset.sum_congr rfl
    intro fresh hfresh
    by_cases hb : bad fresh r
    · have hA : r ∈ A fresh := ⟨hrIcc, hb⟩
      rw [if_pos hb, Set.indicator_of_mem hA]
    · have hA : r ∉ A fresh := by
        rintro ⟨_, hb'⟩
        exact hb hb'
      rw [if_neg hb, Set.indicator_of_notMem hA]
  have hsumToFinite : ∀ r,
      (∑' fresh : Fin K → ℕ,
        if IsFreshChoice x a I fresh ∧ bad fresh r then w fresh else 0) =
        ∑ fresh ∈ F, if bad fresh r then w fresh else 0 := by
    intro r
    simpa [F, w] using
      (pd1c_freshWeighted_tsum_eq_sum x K a I (fun fresh => bad fresh r))
  have hcongr :
      (∫ r in (0 : ℝ)..1,
        ∑' fresh : Fin K → ℕ,
          if IsFreshChoice x a I fresh ∧ bad fresh r then w fresh else 0) =
        ∫ r in (0 : ℝ)..1,
          ∑ fresh ∈ F, (A fresh).indicator (fun _ => w fresh) r := by
    apply intervalIntegral.integral_congr_ae'
    · exact Filter.Eventually.of_forall fun r hr => by
        rw [hsumToFinite r]
        exact hpoint r hr
    · exact Filter.Eventually.of_forall fun r hr => by
        have hr' : r ∈ Set.Ioc (1 : ℝ) 0 := hr
        simp only [Set.mem_Ioc] at hr'
        linarith
  have hInt : ∀ fresh ∈ F,
      IntervalIntegrable (fun r => (A fresh).indicator (fun _ => w fresh) r) volume 0 1 := by
    intro fresh hfresh
    have hAm : MeasurableSet (A fresh) := by
      simpa [A, bad] using
        (pd1c_goodnessTrialPair_badset_measurable x K a p d₀ I iStar fresh e)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    rw [integrableOn_indicator_iff hAm]
    have hfinite : volume (A fresh ∩ Set.Ioc 0 1) ≠ ⊤ := by
      apply ne_of_lt
      calc
        volume (A fresh ∩ Set.Ioc 0 1) ≤ volume (Set.Icc 0 1) :=
          measure_mono (fun r hr => (hr.1).1)
        _ = ENNReal.ofReal 1 := by simp [Real.volume_Icc]
        _ < ⊤ := ENNReal.ofReal_lt_top
    exact integrableOn_const hfinite
  have hsumIntegral :
      (∫ r in (0 : ℝ)..1, ∑ fresh ∈ F, (A fresh).indicator (fun _ => w fresh) r) =
        ∑ fresh ∈ F, ∫ r in (0 : ℝ)..1, (A fresh).indicator (fun _ => w fresh) r :=
    intervalIntegral.integral_finsetSum hInt
  have hterm : ∀ fresh ∈ F,
      (∫ r in (0 : ℝ)..1, (A fresh).indicator (fun _ => w fresh) r) ≤
        ((pd1c_trialCodeFinset x K a I iStar).card : ℝ) ^ 2 * (4 * e) * w fresh := by
    intro fresh hfresh
    have hChoice : IsFreshChoice x a I fresh :=
      (pd1c_freshChoice_iff_mem x K a I fresh).2 (by simpa [F] using hfresh)
    have hw : 0 ≤ w fresh := pd1c_freshChoiceWeight_nonneg x K a I fresh hMass hChoice
    have hAm : MeasurableSet (A fresh) := by
      simpa [A, bad] using
        (pd1c_goodnessTrialPair_badset_measurable x K a p d₀ I iStar fresh e)
    have hVol := pd1c_goodnessTrialPair_badset_measure_le x K a p d₀ I iStar fresh e he
    have hVolReal : volume.real (A fresh) ≤
        ((pd1c_trialCodeFinset x K a I iStar).card : ℝ) ^ 2 * (4 * e) := by
      calc
        volume.real (A fresh) = (volume (A fresh)).toReal := rfl
        _ ≤ (ENNReal.ofReal
            ((pd1c_trialCodeFinset x K a I iStar).card ^ 2 • (4 * e))).toReal :=
              ENNReal.toReal_mono ENNReal.ofReal_ne_top hVol
        _ = ((pd1c_trialCodeFinset x K a I iStar).card : ℝ) ^ 2 * (4 * e) := by
          have harg : 0 ≤
              ((pd1c_trialCodeFinset x K a I iStar).card ^ 2 : ℕ) • (4 * e) := by
            positivity
          rw [ENNReal.toReal_ofReal harg]
          calc
            _ = (((pd1c_trialCodeFinset x K a I iStar).card ^ 2 : ℕ) : ℝ) • (4 * e) :=
              (Nat.cast_smul_eq_nsmul ℝ _ _).symm
            _ = _ := by rw [smul_eq_mul, Nat.cast_pow]
    calc
      _ ≤ volume.real (A fresh) * w fresh :=
            pd1c_interval_indicator_weight_le_volume (A fresh)
              (fun _ hr => hr.1) hAm (w fresh) hw
      _ ≤ ((pd1c_trialCodeFinset x K a I iStar).card : ℝ) ^ 2 * (4 * e) * w fresh :=
            mul_le_mul_of_nonneg_right hVolReal hw
  have hfinal :
      (∫ r in (0 : ℝ)..1,
        ∑' fresh : Fin K → ℕ,
          if IsFreshChoice x a I fresh ∧ bad fresh r then w fresh else 0) ≤
        ((pd1c_trialCodeFinset x K a I iStar).card : ℝ) ^ 2 * (4 * e) := by
    calc
      _ = ∑ fresh ∈ F, ∫ r in (0 : ℝ)..1,
            (A fresh).indicator (fun _ => w fresh) r := by rw [hcongr, hsumIntegral]
      _ ≤ ∑ fresh ∈ F,
            ((pd1c_trialCodeFinset x K a I iStar).card : ℝ) ^ 2 * (4 * e) * w fresh :=
              Finset.sum_le_sum hterm
      _ = ((pd1c_trialCodeFinset x K a I iStar).card : ℝ) ^ 2 * (4 * e) *
            ∑ fresh ∈ F, w fresh := by rw [← Finset.mul_sum]
      _ = ((pd1c_trialCodeFinset x K a I iStar).card : ℝ) ^ 2 * (4 * e) := by
            rw [hmassSum]
            ring
  simpa [w, bad] using hfinal

lemma pd1c_goodTestTwoBadWeight_integral_bound (x : ℝ) (K : ℕ)
    (a : Fin K → ℝ) (p : PrimeLists x K) (d₀ : ℝ) (I : Finset (Fin K))
    (iStar : Fin K) (hMass : ∀ i, 0 < bandMass x (a i)) (e : ℝ) (he : 0 ≤ e) :
    (∫ r in (0 : ℝ)..1, pd1c_goodTestTwoBadWeight x K a p d₀ I iStar e r) ≤
      ((pd1c_trialCodeFinset x K a I iStar).card : ℝ) ^ 2 * (4 * e) := by
  classical
  have hfun : (fun r => pd1c_goodTestTwoBadWeight x K a p d₀ I iStar e r) =
      (fun r => ∑' fresh : Fin K → ℕ,
        if IsFreshChoice x a I fresh ∧
            ∃ n₁ n₂, IsGoodnessTrialValue a p d₀ I iStar fresh n₁ ∧
              IsGoodnessTrialValue a p d₀ I iStar fresh n₂ ∧ n₁ ≠ n₂ ∧
              circleDistance (((n₁ : ℝ) - n₂) * r) ≤ e
        then freshChoiceWeight x a I fresh else 0) := by
    funext r
    exact pd1c_goodTestTwoBadWeight_eq_tsum x K a p d₀ I iStar e r
  rw [hfun]
  exact pd1c_goodTestTwo_inner_integral_bound x K a p d₀ I iStar hMass e he

def pd1c_goodOneBadEvent (x Y d₀ : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (p : PrimeLists x K) (omitted : Fin K → Fin (slotCount x)) (l : ℕ) : Set ℝ :=
  if d₀ ≤ (omissionProduct p omitted : ℝ) ∧
      (omissionProduct p omitted : ℝ) < 2 * d₀ ∧ 1 ≤ l then
    {r : ℝ | r ∈ Set.Icc 0 1 ∧
      circleDistance ((l : ℝ) * (omissionProduct p omitted : ℝ) * r) ≤
        Real.rpow Y (-(7 / 10 : ℝ))}
  else ∅

lemma pd1c_goodOne_badset_eq (x Y d₀ : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (p : PrimeLists x K) (hY : 0 < Y) :
    {r : ℝ | r ∈ Set.Icc 0 1 ∧ ¬ goodTestOne x Y d₀ p r} =
      ⋃ idx : pd1c_goodOnePairIndex K x Y,
        pd1c_goodOneBadEvent x Y d₀ K a p idx.1 idx.2.1 := by
  ext r
  constructor
  · rintro ⟨hrange, hbad⟩
    have hbad' := hbad
    simp only [goodTestOne, not_forall, not_imp, not_lt] at hbad'
    rcases hbad' with ⟨omitted, hDlo, hDhi, l, hl, hL, hdist⟩
    have hTnonneg : 0 ≤ Real.rpow Y (1 / 5 : ℝ) :=
      Real.rpow_nonneg hY.le _
    have hlFloor : l ≤ ⌊Real.rpow Y (1 / 5 : ℝ)⌋₊ :=
      (Nat.le_floor_iff hTnonneg).2 hL
    have hls : l ∈ pd1c_goodOneIndexSet Y := by
      simp only [pd1c_goodOneIndexSet, Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_of_le hlFloor, hl⟩
    let idx : pd1c_goodOnePairIndex K x Y := (omitted, ⟨l, hls⟩)
    refine Set.mem_iUnion.2 ⟨idx, ?_⟩
    simp only [pd1c_goodOneBadEvent, idx, hDlo, hDhi, hl, ↓reduceIte]
    exact ⟨hrange, hdist⟩
  · intro hr
    rcases Set.mem_iUnion.mp hr with ⟨idx, hidx⟩
    have hbadEvent := hidx
    simp only [pd1c_goodOneBadEvent] at hbadEvent
    by_cases hvalid : d₀ ≤ (omissionProduct p idx.1 : ℝ) ∧
        (omissionProduct p idx.1 : ℝ) < 2 * d₀ ∧ 1 ≤ idx.2.1
    · simp only [hvalid, ↓reduceIte] at hbadEvent
      rcases hbadEvent with ⟨hrange, hdist⟩
      have hl : 1 ≤ idx.2.1 := hvalid.2.2
      have hlFloor : idx.2.1 ≤ ⌊Real.rpow Y (1 / 5 : ℝ)⌋₊ := by
        have hmem := idx.2.2
        simp only [pd1c_goodOneIndexSet, Finset.mem_filter, Finset.mem_range] at hmem
        exact Nat.le_of_lt_succ hmem.1
      have hL : (idx.2.1 : ℝ) ≤ Real.rpow Y (1 / 5 : ℝ) :=
        (Nat.le_floor_iff (Real.rpow_nonneg hY.le _)).1 hlFloor
      have hbad : ¬ goodTestOne x Y d₀ p r := by
        intro hgood
        have hstrict := hgood idx.1 hvalid.1 hvalid.2.1 idx.2.1 hl hL
        linarith
      exact ⟨hrange, hbad⟩
    · simp [hvalid] at hbadEvent

lemma pd1c_goodOne_badset_measurable (x Y d₀ : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (p : PrimeLists x K) (hY : 0 < Y) :
    MeasurableSet {r : ℝ | r ∈ Set.Icc 0 1 ∧ ¬ goodTestOne x Y d₀ p r} := by
  letI : Fintype {l : ℕ // l ∈ pd1c_goodOneIndexSet Y} :=
    Fintype.ofFinset (pd1c_goodOneIndexSet Y) (by intro l; rfl)
  letI : Fintype (pd1c_goodOnePairIndex K x Y) := by
    unfold pd1c_goodOnePairIndex
    infer_instance
  rw [pd1c_goodOne_badset_eq x Y d₀ K a p hY]
  apply MeasurableSet.iUnion
  intro idx
  unfold pd1c_goodOneBadEvent
  by_cases hvalid : d₀ ≤ (omissionProduct p idx.1 : ℝ) ∧
      (omissionProduct p idx.1 : ℝ) < 2 * d₀ ∧ 1 ≤ idx.2.1
  · simp only [if_pos hvalid]
    change MeasurableSet
      (Set.Icc 0 1 ∩ {r : ℝ | circleDistance
        ((idx.2.1 : ℝ) * (omissionProduct p idx.1 : ℝ) * r) ≤
          Real.rpow Y (-(7 / 10 : ℝ))})
    exact measurableSet_Icc.inter
      (pd1c_circleDistance_realSublevel_measurable
        ((idx.2.1 : ℝ) * (omissionProduct p idx.1 : ℝ))
        (Real.rpow Y (-(7 / 10 : ℝ))))
  · simp [hvalid]

lemma pd1c_omissionProduct_pos {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (p : PrimeLists x K) (hp : ValidPrimeLists x K a p)
    (omitted : Fin K → Fin (slotCount x)) : 0 < omissionProduct p omitted := by
  unfold omissionProduct
  apply Finset.prod_pos
  intro i hi
  apply Finset.prod_pos
  intro j hj
  split_ifs with h
  · exact (hp.1 i j).1.pos
  · norm_num

lemma pd1c_goodOneBadEvent_volume_le (x Y d₀ : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (p : PrimeLists x K) (hp : ValidPrimeLists x K a p)
    (omitted : Fin K → Fin (slotCount x)) (l : ℕ) (hl : 1 ≤ l) (hY : 0 < Y) :
    volume (pd1c_goodOneBadEvent x Y d₀ K a p omitted l) ≤
      ENNReal.ofReal (4 * Real.rpow Y (-(7 / 10 : ℝ))) := by
  have hDpos : 0 < omissionProduct p omitted := pd1c_omissionProduct_pos p hp omitted
  have hfreqpos : 0 < l * omissionProduct p omitted := Nat.mul_pos hl hDpos
  have hfreqne : Int.ofNat (l * omissionProduct p omitted) ≠ 0 := by
    simpa using (Nat.ne_of_gt hfreqpos)
  have he : 0 ≤ Real.rpow Y (-(7 / 10 : ℝ)) := Real.rpow_nonneg hY.le _
  by_cases hvalid : d₀ ≤ (omissionProduct p omitted : ℝ) ∧
      (omissionProduct p omitted : ℝ) < 2 * d₀ ∧ 1 ≤ l
  · have hfreq : ((Int.ofNat (l * omissionProduct p omitted) : ℤ) : ℝ) =
        (l : ℝ) * (omissionProduct p omitted : ℝ) := by
      simp [Nat.cast_mul]
    have hbound := pd1c_circle_small_set_measure (Int.ofNat (l * omissionProduct p omitted))
      hfreqne (Real.rpow Y (-(7 / 10 : ℝ))) he
    simpa [pd1c_goodOneBadEvent, hvalid, hfreq] using hbound
  · simp [pd1c_goodOneBadEvent, hvalid]

lemma pd1c_goodOne_badset_volume_le (x Y d₀ : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (p : PrimeLists x K) (hp : ValidPrimeLists x K a p) (hY : 0 < Y) :
    volume {r : ℝ | r ∈ Set.Icc 0 1 ∧ ¬ goodTestOne x Y d₀ p r} ≤
      ∑ idx ∈ pd1c_goodOnePairFinset K x Y,
        ENNReal.ofReal (4 * Real.rpow Y (-(7 / 10 : ℝ))) := by
  letI : Fintype {l : ℕ // l ∈ pd1c_goodOneIndexSet Y} :=
    Fintype.ofFinset (pd1c_goodOneIndexSet Y) (by intro l; rfl)
  letI : Fintype (pd1c_goodOnePairIndex K x Y) := by
    unfold pd1c_goodOnePairIndex
    infer_instance
  have hUniv : (Finset.univ : Finset (pd1c_goodOnePairIndex K x Y)) =
      pd1c_goodOnePairFinset K x Y := by
    ext idx
    rcases idx with ⟨omitted, l⟩
    constructor
    · intro _
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_attach _ _⟩
    · intro _
      exact Finset.mem_univ _
  rw [pd1c_goodOne_badset_eq x Y d₀ K a p hY]
  calc
    volume (⋃ idx : pd1c_goodOnePairIndex K x Y,
        pd1c_goodOneBadEvent x Y d₀ K a p idx.1 idx.2.1) ≤
      ∑ idx : pd1c_goodOnePairIndex K x Y,
        volume (pd1c_goodOneBadEvent x Y d₀ K a p idx.1 idx.2.1) :=
          MeasureTheory.measure_iUnion_fintype_le volume _
    _ = ∑ idx ∈ pd1c_goodOnePairFinset K x Y,
        volume (pd1c_goodOneBadEvent x Y d₀ K a p idx.1 idx.2.1) := by rw [← hUniv]
    _ ≤ ∑ idx ∈ pd1c_goodOnePairFinset K x Y,
        ENNReal.ofReal (4 * Real.rpow Y (-(7 / 10 : ℝ))) := by
          apply Finset.sum_le_sum
          intro idx hidx
          have hl : 1 ≤ idx.2.1 := by
            have hmem := idx.2.2
            simp only [pd1c_goodOneIndexSet, Finset.mem_filter] at hmem
            exact hmem.2
          exact pd1c_goodOneBadEvent_volume_le x Y d₀ K a p hp idx.1 idx.2.1 hl hY

lemma pd1c_goodTestOne_bad_integral_le (x Y d₀ : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (p : PrimeLists x K) (hp : ValidPrimeLists x K a p) (hY : 0 < Y) :
    (∫ r in (0 : ℝ)..1, if goodTestOne x Y d₀ p r then (0 : ℝ) else 1) ≤
      (∑ idx ∈ pd1c_goodOnePairFinset K x Y,
        ENNReal.ofReal (4 * Real.rpow Y (-(7 / 10 : ℝ)))).toReal := by
  let B : Set ℝ := {r | r ∈ Set.Icc 0 1 ∧ ¬ goodTestOne x Y d₀ p r}
  have hBmeas : MeasurableSet B := by
    simpa [B] using pd1c_goodOne_badset_measurable x Y d₀ K a p hY
  have hBsub : B ⊆ Set.Icc 0 1 := fun _ hr => hr.1
  have hcongr :
      (∫ r in (0 : ℝ)..1, if goodTestOne x Y d₀ p r then (0 : ℝ) else 1) =
        ∫ r in (0 : ℝ)..1, B.indicator (fun _ => (1 : ℝ)) r := by
    apply intervalIntegral.integral_congr_ae'
    · exact Filter.Eventually.of_forall fun r hr => by
        have hrIcc : r ∈ Set.Icc 0 1 := ⟨le_of_lt hr.1, hr.2⟩
        by_cases hg : goodTestOne x Y d₀ p r
        · have hrnot : r ∉ B := by
            intro h
            exact h.2 hg
          have hr0 : 0 ≤ r := hrIcc.1
          have hr1 : r ≤ 1 := hrIcc.2
          simp [Set.indicator, B, hg, hrnot, hr0, hr1]
        · have hrB : r ∈ B := ⟨hrIcc, hg⟩
          have hr0 : 0 ≤ r := hrIcc.1
          have hr1 : r ≤ 1 := hrIcc.2
          simp [Set.indicator, B, hg, hrB, hr0, hr1]
    · exact Filter.Eventually.of_forall fun r hr => by
        have : r ∈ Set.Ioc (1 : ℝ) 0 := hr
        norm_num [Set.mem_Ioc] at this
  have hvolume := pd1c_goodOne_badset_volume_le x Y d₀ K a p hp hY
  have hsumtop :
      (∑ idx ∈ pd1c_goodOnePairFinset K x Y,
        ENNReal.ofReal (4 * Real.rpow Y (-(7 / 10 : ℝ)))) ≠ ⊤ := by
    apply ENNReal.sum_ne_top.2
    intro idx hidx
    exact ENNReal.ofReal_ne_top
  calc
    (∫ r in (0 : ℝ)..1, if goodTestOne x Y d₀ p r then (0 : ℝ) else 1) =
        ∫ r in (0 : ℝ)..1, B.indicator (fun _ => (1 : ℝ)) r := hcongr
    _ ≤ volume.real B := pd1c_interval_indicator_le_volume B hBsub hBmeas
    _ = (volume B).toReal := rfl
    _ ≤ (∑ idx ∈ pd1c_goodOnePairFinset K x Y,
        ENNReal.ofReal (4 * Real.rpow Y (-(7 / 10 : ℝ)))).toReal :=
          ENNReal.toReal_mono hsumtop hvolume

lemma pd1c_goodTestOne_bad_integral_power_le (x Y d₀ : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (p : PrimeLists x K) (hp : ValidPrimeLists x K a p)
    (hY : 0 < Y) (hT : 1 ≤ Real.rpow Y (1 / 5 : ℝ)) :
    (∫ r in (0 : ℝ)..1, if goodTestOne x Y d₀ p r then (0 : ℝ) else 1) ≤
      8 * (slotCount x : ℝ) ^ K * Real.rpow Y (-(1 / 2 : ℝ)) := by
  let s := pd1c_goodOnePairFinset K x Y
  let e := Real.rpow Y (-(7 / 10 : ℝ))
  have he : 0 ≤ e := Real.rpow_nonneg hY.le _
  have hsumEq : (∑ idx ∈ s, ENNReal.ofReal (4 * e)) =
      ENNReal.ofReal ((s.card : ℕ) • (4 * e)) := by
    rw [Finset.sum_const, ← ENNReal.ofReal_nsmul]
  have hsumValue : (∑ idx ∈ s, ENNReal.ofReal (4 * e)).toReal =
      (s.card : ℝ) * (4 * e) := by
    have hnonneg : 0 ≤ (s.card : ℕ) • (4 * e) := by positivity
    rw [hsumEq, ENNReal.toReal_ofReal hnonneg]
    simp [Nat.cast_smul_eq_nsmul, smul_eq_mul]
  have hcount : (s.card : ℝ) ≤
      (slotCount x : ℝ) ^ K * (2 * Real.rpow Y (1 / 5 : ℝ)) := by
    simpa [s] using pd1c_goodOnePairFinset_card_bound K x Y hT
  have hTprod : Real.rpow Y (1 / 5 : ℝ) * e =
      Real.rpow Y (-(1 / 2 : ℝ)) := by
    dsimp [e]
    rw [← Real.rpow_add hY]
    congr 1
    norm_num
  calc
    (∫ r in (0 : ℝ)..1, if goodTestOne x Y d₀ p r then (0 : ℝ) else 1) ≤
        (∑ idx ∈ s, ENNReal.ofReal (4 * e)).toReal := by
          simpa [s, e] using pd1c_goodTestOne_bad_integral_le x Y d₀ K a p hp hY
    _ = (s.card : ℝ) * (4 * e) := hsumValue
    _ ≤ ((slotCount x : ℝ) ^ K * (2 * Real.rpow Y (1 / 5 : ℝ))) * (4 * e) :=
          mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = 8 * (slotCount x : ℝ) ^ K *
        (Real.rpow Y (1 / 5 : ℝ) * e) := by ring
    _ = 8 * (slotCount x : ℝ) ^ K * Real.rpow Y (-(1 / 2 : ℝ)) := by rw [hTprod]

lemma pd1c_goodTestOne_uniform_absorption (K : ℕ) (a : Fin K → ℝ) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        ∀ Y ∈ dyadicScales x K,
          ∀ d₀ : ℝ, ∀ p : PrimeLists x K, ValidPrimeLists x K a p →
            (∫ r in (0 : ℝ)..1,
              if goodTestOne x Y d₀ p r then (0 : ℝ) else 1) ≤
              Real.exp (-(1 / 80 : ℝ) * Real.rpow (Real.log x) (1 / 10 : ℝ)) := by
  let B : ℝ := ((K + 3 : ℕ) : ℝ) + (K : ℝ) / 100
  obtain ⟨L₀, hL₀, hdecay⟩ := pd1c_logPower_expDecay 0 B (1 / 80 : ℝ) (by norm_num)
  let Lstar := max 2 L₀
  let x₀ := max 2 (Real.exp Lstar)
  refine ⟨x₀, le_max_left _ _, ?_⟩
  intro x hx Y hY d₀ p hp
  let L := Real.log x
  have hxexp : Real.exp Lstar ≤ x := (le_max_right _ _).trans hx
  have hLstarx : Lstar ≤ L := by
    have hlog := Real.log_le_log (Real.exp_pos Lstar) hxexp
    simpa [L] using hlog
  have hL₀x : L₀ ≤ L := le_trans (le_max_right 2 L₀) hLstarx
  have hLone : 1 ≤ L := le_trans hL₀ hL₀x
  have hLtwo : 2 ≤ L := le_trans (le_max_left 2 L₀) hLstarx
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hLone
  have hLpowOne : 1 ≤ Real.rpow L (1 / 100 : ℝ) :=
    Real.one_le_rpow hLone (by norm_num)
  have hMfloor : (momentJ x : ℝ) ≤ Real.rpow L (1 / 100 : ℝ) := by
    dsimp [momentJ, L]
    exact Nat.floor_le (Real.rpow_nonneg hLpos.le _)
  have hM : (slotCount x : ℝ) ≤ 2 * Real.rpow L (1 / 100 : ℝ) := by
    simp only [slotCount, Nat.cast_add, Nat.cast_one]
    nlinarith
  have hMpow : (slotCount x : ℝ) ^ K ≤ (2 * Real.rpow L (1 / 100 : ℝ)) ^ K :=
    pow_le_pow_left₀ (by positivity) hM K
  have hLpowK : (Real.rpow L (1 / 100 : ℝ)) ^ K =
      Real.rpow L ((K : ℝ) / 100) := by
    calc
      (Real.rpow L (1 / 100 : ℝ)) ^ K =
          (Real.rpow L (1 / 100 : ℝ)) ^ (K : ℝ) :=
            (Real.rpow_natCast _ _).symm
      _ = Real.rpow L ((1 / 100 : ℝ) * (K : ℝ)) :=
            (Real.rpow_mul hLpos.le _ _).symm
      _ = Real.rpow L ((K : ℝ) / 100) := by congr 1 <;> ring
  have hMpow' : (slotCount x : ℝ) ^ K ≤
      (2 : ℝ) ^ K * Real.rpow L ((K : ℝ) / 100) := by
    calc
      _ ≤ (2 * Real.rpow L (1 / 100 : ℝ)) ^ K := hMpow
      _ = (2 : ℝ) ^ K * Real.rpow L ((K : ℝ) / 100) := by
        rw [mul_pow, hLpowK]
  have hconst : (8 : ℝ) * (2 : ℝ) ^ K ≤ L ^ (K + 3) := by
    calc
      (8 : ℝ) * (2 : ℝ) ^ K = (2 : ℝ) ^ K * (2 : ℝ) ^ 3 := by norm_num; ring
      _ = (2 : ℝ) ^ (K + 3) := (pow_add _ _ _).symm
      _ ≤ L ^ (K + 3) := pow_le_pow_left₀ (by norm_num) hLtwo _
  have hBpow : L ^ (K + 3) * Real.rpow L ((K : ℝ) / 100) = Real.rpow L B := by
    calc
      L ^ (K + 3) * Real.rpow L ((K : ℝ) / 100) =
          Real.rpow L ((K + 3 : ℕ) : ℝ) * Real.rpow L ((K : ℝ) / 100) := by
            exact congrArg (fun z : ℝ => z * Real.rpow L ((K : ℝ) / 100))
              (Real.rpow_natCast L (K + 3)).symm
      _ = Real.rpow L (((K + 3 : ℕ) : ℝ) + (K : ℝ) / 100) := by
            exact (Real.rpow_add hLpos ((K + 3 : ℕ) : ℝ) ((K : ℝ) / 100)).symm
      _ = Real.rpow L B := by simp [B]
  have hYbounds := pd1c_dyadicScale_log_bounds hY
  have hYpos : 0 < Y := by
    unfold dyadicScales at hY
    rcases Finset.mem_filter.mp hY with ⟨hImage, _⟩
    rcases Finset.mem_image.mp hImage with ⟨k, _, rfl⟩
    positivity
  have hlogYpos : 0 < Real.log Y := by
    have hpowpos : 0 < Real.rpow L (1 / 10 : ℝ) := Real.rpow_pos_of_pos hLpos _
    have hlowpos : 0 < (1 / 20 : ℝ) * Real.rpow L (1 / 10 : ℝ) := by positivity
    linarith [hYbounds.1]
  have hYgt1 : 1 < Y := (Real.log_pos_iff hYpos.le).mp hlogYpos
  have hYpowOne : 1 ≤ Real.rpow Y (1 / 5 : ℝ) :=
    Real.one_le_rpow hYgt1.le (by norm_num)
  have hYpow : Real.rpow Y (-(1 / 2 : ℝ)) ≤
      Real.exp (-(1 / 40 : ℝ) * Real.rpow L (1 / 10 : ℝ)) := by
    calc
      Real.rpow Y (-(1 / 2 : ℝ)) =
          Real.exp (Real.log Y * (-(1 / 2 : ℝ))) := Real.rpow_def_of_pos hYpos _
      _ ≤ Real.exp (-(1 / 40 : ℝ) * Real.rpow L (1 / 10 : ℝ)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [hYbounds.1]
  have htest := pd1c_goodTestOne_bad_integral_power_le x Y d₀ K a p hp hYpos hYpowOne
  have hmain : 8 * (slotCount x : ℝ) ^ K * Real.rpow Y (-(1 / 2 : ℝ)) ≤
      Real.rpow L B * Real.exp (-(1 / 40 : ℝ) * Real.rpow L (1 / 10 : ℝ)) := by
    calc
      _ ≤ 8 * (slotCount x : ℝ) ^ K *
          Real.exp (-(1 / 40 : ℝ) * Real.rpow L (1 / 10 : ℝ)) :=
            mul_le_mul_of_nonneg_left hYpow (by positivity)
      _ ≤ 8 * ((2 : ℝ) ^ K * Real.rpow L ((K : ℝ) / 100)) *
          Real.exp (-(1 / 40 : ℝ) * Real.rpow L (1 / 10 : ℝ)) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hMpow' (by norm_num)) (Real.exp_nonneg _)
      _ = (8 * (2 : ℝ) ^ K) * (Real.rpow L ((K : ℝ) / 100) *
          Real.exp (-(1 / 40 : ℝ) * Real.rpow L (1 / 10 : ℝ))) := by ring
      _ ≤ L ^ (K + 3) * (Real.rpow L ((K : ℝ) / 100) *
          Real.exp (-(1 / 40 : ℝ) * Real.rpow L (1 / 10 : ℝ))) := by
            apply mul_le_mul_of_nonneg_right hconst
            exact mul_nonneg (Real.rpow_nonneg hLpos.le _) (Real.exp_nonneg _)
      _ = L ^ (K + 3) * Real.rpow L ((K : ℝ) / 100) *
          Real.exp (-(1 / 40 : ℝ) * Real.rpow L (1 / 10 : ℝ)) := by ring
      _ = Real.rpow L B * Real.exp (-(1 / 40 : ℝ) * Real.rpow L (1 / 10 : ℝ)) := by
            rw [hBpow]
  have hhalf : Real.rpow L B *
      Real.exp (-(1 / 40 : ℝ) * Real.rpow L (1 / 10 : ℝ)) ≤
        Real.exp (-(1 / 80 : ℝ) * Real.rpow L (1 / 10 : ℝ)) := by
    have hAbsorb : Real.rpow L B *
        Real.exp (-(1 / 80 : ℝ) * Real.rpow L (1 / 10 : ℝ)) ≤ 1 := by
      convert hdecay L hL₀x using 1 <;> norm_num
    have hsplit : Real.exp (-(1 / 40 : ℝ) * Real.rpow L (1 / 10 : ℝ)) =
        Real.exp (-(1 / 80 : ℝ) * Real.rpow L (1 / 10 : ℝ)) *
          Real.exp (-(1 / 80 : ℝ) * Real.rpow L (1 / 10 : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ = (Real.rpow L B *
          Real.exp (-(1 / 80 : ℝ) * Real.rpow L (1 / 10 : ℝ))) *
            Real.exp (-(1 / 80 : ℝ) * Real.rpow L (1 / 10 : ℝ)) := by rw [hsplit]; ring
      _ ≤ 1 * Real.exp (-(1 / 80 : ℝ) * Real.rpow L (1 / 10 : ℝ)) :=
          mul_le_mul_of_nonneg_right hAbsorb (Real.exp_nonneg _)
      _ = _ := by ring
  exact htest.trans (hmain.trans hhalf)

lemma pd1c_bandMass_pos_of_validPrimeLists (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (p : PrimeLists x K) (hp : ValidPrimeLists x K a p) :
    ∀ i, 0 < bandMass x (a i) := by
  intro i
  have hslots : 0 < slotCount x := by
    dsimp [slotCount]
    omega
  let j : Fin (slotCount x) := ⟨0, hslots⟩
  have hlabel := hp.1 i j
  have hmem : p i j ∈ primeBand x (a i) := hlabel.2
  have hprime : (p i j).Prime := hlabel.1
  have hpositive : 0 < 1 / (p i j : ℝ) := by
    have hq : 0 < (p i j : ℝ) := by exact_mod_cast hprime.pos
    positivity
  have hsum : 1 / (p i j : ℝ) ≤ bandMass x (a i) := by
    unfold bandMass
    exact Finset.single_le_sum (f := fun q : ℕ => 1 / (q : ℝ))
      (fun q hq => by positivity) hmem
  exact lt_of_lt_of_le hpositive hsum

lemma pd1c_primeBand_card_bound (x a : ℝ) (hx : 2 ≤ x) :
    ((primeBand x a).card : ℝ) ≤ 2 * Real.exp (2 * Real.rpow (Real.log x) a) := by
  let U := Real.exp (2 * Real.rpow (Real.log x) a)
  have hU : 0 ≤ U := (Real.exp_pos _).le
  have hcard := Finset.card_filter_le
    (Finset.range (⌊Real.exp (2 * Real.rpow (Real.log x) a)⌋₊ + 1))
    (fun p : ℕ => p.Prime ∧ Real.exp (Real.rpow (Real.log x) a) ≤ (p : ℝ) ∧
      (p : ℝ) ≤ Real.exp (2 * Real.rpow (Real.log x) a))
  calc
    ((primeBand x a).card : ℝ) ≤
        ((Finset.range (⌊Real.exp (2 * Real.rpow (Real.log x) a)⌋₊ + 1)).card : ℝ) := by
          unfold primeBand
          exact_mod_cast hcard
    _ = (⌊U⌋₊ : ℝ) + 1 := by simp [U]
    _ ≤ U + 1 := by
      simpa [add_comm] using add_le_add_right (Nat.floor_le hU) 1
    _ ≤ 2 * U := by
      have hlog : 0 < Real.log x := Real.log_pos (by linarith)
      have hrpow : 0 ≤ Real.rpow (Real.log x) a := Real.rpow_nonneg hlog.le _
      have h1 : 1 ≤ U := Real.one_le_exp (by positivity)
      linarith

lemma pd1c_slotCount_bound (x : ℝ) (hL : 1 ≤ Real.log x) :
    (slotCount x : ℝ) ≤ 2 * Real.rpow (Real.log x) (1 / 100 : ℝ) := by
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (by norm_num) hL
  have hfloor : (momentJ x : ℝ) ≤ Real.rpow (Real.log x) (1 / 100 : ℝ) := by
    dsimp [momentJ]
    exact Nat.floor_le (Real.rpow_nonneg hLpos.le _)
  have hone : 1 ≤ Real.rpow (Real.log x) (1 / 100 : ℝ) :=
    Real.one_le_rpow hL (by norm_num)
  simp only [slotCount, Nat.cast_add, Nat.cast_one]
  nlinarith

lemma pd1c_lowerBandRpow_small (K : ℕ) (a : Fin K → ℝ)
    (ha : ValidBands K a) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L → ∀ i j : Fin K,
      i.val < j.val →
        Real.rpow L (a i) ≤ Real.rpow L (a j) / (64 * (K : ℝ)) := by
  have hEvent : ∀ᶠ L : ℝ in atTop, ∀ i j : Fin K, i.val < j.val →
      Real.rpow L (a i) ≤ Real.rpow L (a j) / (64 * (K : ℝ)) := by
    apply (eventually_all).2
    intro i
    apply (eventually_all).2
    intro j
    by_cases hij : i.val < j.val
    · have hratio : Tendsto (fun L : ℝ => Real.rpow L (a i - a j)) atTop (nhds 0) := by
        have hneg := tendsto_rpow_neg_atTop
          (sub_pos.mpr (ha.2.2 i j hij))
        simpa [sub_eq_add_neg] using hneg
      have hK : (0 : ℝ) < (K : ℝ) := by exact_mod_cast ha.1
      have htarget : 0 < 1 / (64 * (K : ℝ)) := by positivity
      have hsmall : ∀ᶠ L : ℝ in atTop,
          Real.rpow L (a i - a j) < 1 / (64 * (K : ℝ)) :=
        hratio.eventually (Iio_mem_nhds htarget)
      have hLpos : ∀ᶠ L : ℝ in atTop, 0 < L := eventually_gt_atTop 0
      filter_upwards [hsmall, hLpos] with L hs hL
      intro _
      have hpow : Real.rpow L (a i) =
          Real.rpow L (a j) * Real.rpow L (a i - a j) := by
        calc
          Real.rpow L (a i) = Real.rpow L (a j + (a i - a j)) := by congr 1 <;> ring
          _ = _ := Real.rpow_add hL _ _
      rw [hpow]
      calc
        _ ≤ Real.rpow L (a j) * (1 / (64 * (K : ℝ))) :=
            mul_le_mul_of_nonneg_left hs.le (Real.rpow_nonneg hL.le _)
        _ = _ := by ring
    · filter_upwards [] with L
      intro hij'
      exact (hij hij').elim
  rcases eventually_atTop.mp hEvent with ⟨L₁, hL₁⟩
  refine ⟨max 1 L₁, le_max_left _ _, ?_⟩
  intro L hL i j hij
  exact hL₁ L (le_trans (le_max_right _ _) hL) i j hij

lemma pd1c_trialCode_card_exp_bound (K : ℕ) (a : Fin K → ℝ)
    (ha : ValidBands K a) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ x : ℝ, L₀ ≤ Real.log x → 2 ≤ x →
      ∀ I : Finset (Fin K), ∀ iStar : Fin K,
        (∀ i, i ∈ I.erase iStar →
          Real.rpow (Real.log x) (a i) ≤
            Real.rpow (Real.log x) (a iStar) / (64 * (K : ℝ))) →
        400 * ((pd1c_trialCodeFinset x K a I iStar).card : ℝ) ^ 2 ≤
          Real.exp (Real.rpow (Real.log x) (a iStar) / 8) := by
  classical
  let C := (400 : ℝ) * (16 : ℝ) ^ K
  let B := (1 : ℝ) + 2 * (K : ℝ)
  obtain ⟨Ldec, hLdec, hdecay⟩ :=
    pd1c_logPower_expDecay 0 B (1 / 16 : ℝ) (by norm_num)
  let L₀ := max 1 (max Ldec C)
  refine ⟨L₀, le_max_left _ _, ?_⟩
  intro x hxL hx I iStar hGap
  let L := Real.log x
  let t := Real.rpow L (a iStar)
  let α := {i : Fin K // i ∈ I.erase iStar}
  letI : Fintype α := Fintype.ofFinset (I.erase iStar) (by intro i; rfl)
  have hL : 1 ≤ L := le_trans (le_max_left 1 (max Ldec C)) hxL
  have hLdecay : Ldec ≤ L := le_trans
    (le_max_left Ldec C) (le_trans (le_max_right 1 (max Ldec C)) hxL)
  have hLlarge : C ≤ L := le_trans
    (le_max_right Ldec C) (le_trans (le_max_right 1 (max Ldec C)) hxL)
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hK : 0 < (K : ℝ) := by exact_mod_cast ha.1
  have hB : 1 ≤ 2 * Real.exp (t / (32 * (K : ℝ))) := by
    have ht : 0 < t := Real.rpow_pos_of_pos hLpos _
    have : 0 ≤ t / (32 * (K : ℝ)) := by positivity
    have hexp : 1 ≤ Real.exp (t / (32 * (K : ℝ))) := Real.one_le_exp this
    linarith
  have hslot : (slotCount x : ℝ) ≤ 2 * L := by
    calc
      (slotCount x : ℝ) ≤ 2 * Real.rpow L (1 / 100 : ℝ) :=
        pd1c_slotCount_bound x hL
      _ ≤ 2 * L := by
        have hpow : Real.rpow L (1 / 100 : ℝ) ≤ L := by
          simpa [Real.rpow_one] using
            (Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (1 / 100 : ℝ) ≤ 1))
        exact mul_le_mul_of_nonneg_left hpow (by norm_num)
  have hcardCast :
      ((pd1c_trialCodeFinset x K a I iStar).card : ℝ) =
        (slotCount x : ℝ) ^ K *
          ∏ i : α, ((primeBand x (a i)).card : ℝ) := by
    rw [pd1c_trialCodeFinset_card]
    norm_cast
  have hBand : ∀ i : α, ((primeBand x (a i)).card : ℝ) ≤
      2 * Real.exp (t / (32 * (K : ℝ))) := by
    intro i
    have hsmall := hGap i.1 i.2
    have hexp : Real.exp (2 * Real.rpow L (a i)) ≤
        Real.exp (t / (32 * (K : ℝ))) := by
      apply Real.exp_le_exp.mpr
      calc
        2 * Real.rpow L (a i) ≤ 2 * (t / (64 * (K : ℝ))) :=
          mul_le_mul_of_nonneg_left hsmall (by norm_num)
        _ = t / (32 * (K : ℝ)) := by ring
    calc
      ((primeBand x (a i.1)).card : ℝ) ≤
          2 * Real.exp (2 * Real.rpow L (a i.1)) := by
            exact pd1c_primeBand_card_bound x (a i.1) hx
      _ ≤ 2 * Real.exp (t / (32 * (K : ℝ))) :=
        mul_le_mul_of_nonneg_left hexp (by norm_num)
  have hProd : ∏ i : α, ((primeBand x (a i)).card : ℝ) ≤
      (2 * Real.exp (t / (32 * (K : ℝ)))) ^ K := by
    have hCardα : Fintype.card α ≤ K := by
      have hEq : Fintype.card α = (I.erase iStar).card := by
        dsimp [α]
        exact Fintype.card_of_subtype (I.erase iStar) (by
          intro i
          simp [Finset.mem_erase, and_comm])
      rw [hEq]
      exact le_trans (Finset.card_le_card (Finset.subset_univ _)) (by simp)
    change ∏ i ∈ (Finset.univ : Finset α),
        ((primeBand x (a i)).card : ℝ) ≤ _
    calc
      _ ≤ ∏ i ∈ (Finset.univ : Finset α),
          2 * Real.exp (t / (32 * (K : ℝ))) := by
            apply Finset.prod_le_prod₀
            · intro i hi
              exact Nat.cast_nonneg _
            · intro i hi
              exact hBand i
      _ = (2 * Real.exp (t / (32 * (K : ℝ)))) ^ Fintype.card α := by simp
      _ ≤ (2 * Real.exp (t / (32 * (K : ℝ)))) ^ K :=
        pow_le_pow_right₀ hB hCardα
  have hCode : ((pd1c_trialCodeFinset x K a I iStar).card : ℝ) ≤
      (4 * L * Real.exp (t / (32 * (K : ℝ)))) ^ K := by
    rw [hcardCast]
    calc
      (slotCount x : ℝ) ^ K *
          ∏ i : α, ((primeBand x (a i)).card : ℝ) ≤
        (2 * L) ^ K * (2 * Real.exp (t / (32 * (K : ℝ)))) ^ K := by
          have hslotPow : (slotCount x : ℝ) ^ K ≤ (2 * L) ^ K :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) hslot K
          have hprodNonneg : 0 ≤
              ∏ i : α, ((primeBand x (a i)).card : ℝ) :=
            Finset.prod_nonneg fun i hi => Nat.cast_nonneg _
          have hslotNonneg : 0 ≤ (2 * L) ^ K :=
            pow_nonneg (by positivity) _
          calc
            _ ≤ (2 * L) ^ K *
                ∏ i : α, ((primeBand x (a i)).card : ℝ) :=
              mul_le_mul_of_nonneg_right hslotPow hprodNonneg
            _ ≤ _ := mul_le_mul_of_nonneg_left hProd hslotNonneg
      _ = (4 * L * Real.exp (t / (32 * (K : ℝ)))) ^ K := by
        rw [← mul_pow]
        congr 1
        ring
  have hCpos : 0 < C := by dsimp [C]; positivity
  have hpoly : C * Real.rpow L (2 * (K : ℝ)) ≤
      Real.exp (Real.rpow L (1 / 10 : ℝ) / 16) := by
    have hCsmall : C * Real.rpow L (2 * (K : ℝ)) *
        Real.exp (-(1 / 16 : ℝ) * Real.rpow L (1 / 10 : ℝ)) ≤ 1 := by
      have hdec := hdecay L hLdecay
      have hpow : Real.rpow L B =
          L * Real.rpow L (2 * (K : ℝ)) := by
        calc
          Real.rpow L B = Real.rpow L (1 + 2 * (K : ℝ)) := by rfl
          _ = Real.rpow L 1 * Real.rpow L (2 * (K : ℝ)) :=
            Real.rpow_add hLpos _ _
          _ = L * Real.rpow L (2 * (K : ℝ)) := by
            exact congrArg (fun z : ℝ => z * Real.rpow L (2 * (K : ℝ)))
              (Real.rpow_one L)
      rw [hpow] at hdec
      have hdec' : L * Real.rpow L (2 * (K : ℝ)) *
          Real.exp (-(1 / 16 : ℝ) * Real.rpow L (1 / 10 : ℝ)) ≤ 1 := by
        simpa using hdec
      have hmul : C * Real.rpow L (2 * (K : ℝ)) *
          Real.exp (-(1 / 16 : ℝ) * Real.rpow L (1 / 10 : ℝ)) ≤
        L * Real.rpow L (2 * (K : ℝ)) *
          Real.exp (-(1 / 16 : ℝ) * Real.rpow L (1 / 10 : ℝ)) := by
        calc
          _ ≤ (L * Real.rpow L (2 * (K : ℝ))) *
              Real.exp (-(1 / 16 : ℝ) * Real.rpow L (1 / 10 : ℝ)) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hLlarge (Real.rpow_nonneg hLpos.le _))
              (Real.exp_nonneg _)
          _ = _ := by ring
      calc
        _ ≤ L * Real.rpow L (2 * (K : ℝ)) *
            Real.exp (-(1 / 16 : ℝ) * Real.rpow L (1 / 10 : ℝ)) := hmul
        _ ≤ 1 := hdec'
    calc
      _ = (C * Real.rpow L (2 * (K : ℝ)) *
          Real.exp (-(1 / 16 : ℝ) * Real.rpow L (1 / 10 : ℝ))) *
            Real.exp (Real.rpow L (1 / 10 : ℝ) / 16) := by
          have hcancel : Real.exp (-(1 / 16 : ℝ) * Real.rpow L (1 / 10 : ℝ)) *
              Real.exp (Real.rpow L (1 / 10 : ℝ) / 16) = 1 := by
            rw [← Real.exp_add]
            rw [show -(1 / 16 : ℝ) * Real.rpow L (1 / 10 : ℝ) +
                Real.rpow L (1 / 10 : ℝ) / 16 = 0 by ring]
            simp
          have hprod := congrArg
            (fun z : ℝ => C * Real.rpow L (2 * (K : ℝ)) * z) hcancel
          calc
            _ = C * Real.rpow L (2 * (K : ℝ)) *
                (Real.exp (-(1 / 16 : ℝ) * Real.rpow L (1 / 10 : ℝ)) *
                  Real.exp (Real.rpow L (1 / 10 : ℝ) / 16)) := by
              calc
                _ = C * Real.rpow L (2 * (K : ℝ)) * 1 := by ring
                _ = _ := hprod.symm
            _ = _ := by ring
      _ ≤ 1 * Real.exp (Real.rpow L (1 / 10 : ℝ) / 16) :=
        mul_le_mul_of_nonneg_right hCsmall (Real.exp_nonneg _)
      _ = _ := by ring
  have hRpowNat : Real.rpow L (2 * (K : ℝ)) = L ^ (2 * K : ℕ) := by
    calc
      Real.rpow L (2 * (K : ℝ)) = Real.rpow L ((2 * K : ℕ) : ℝ) := by
        congr 1
        norm_cast
      _ = L ^ (2 * K : ℕ) := Real.rpow_natCast L (2 * K)
  have htexp : Real.rpow L (1 / 10 : ℝ) ≤ t := by
    dsimp [t]
    exact Real.rpow_le_rpow_of_exponent_le hL (ha.2.1 iStar).1.le
  have hCodeSq : 400 * ((pd1c_trialCodeFinset x K a I iStar).card : ℝ) ^ 2 ≤
      C * Real.rpow L (2 * (K : ℝ)) * Real.exp (t / 16) := by
    have hcodeNonneg : 0 ≤ (pd1c_trialCodeFinset x K a I iStar).card := Nat.cast_nonneg _
    calc
      _ ≤ 400 * ((4 * L * Real.exp (t / (32 * (K : ℝ)))) ^ K) ^ 2 := by
        apply mul_le_mul_of_nonneg_left
        · exact pow_le_pow_left₀ (Nat.cast_nonneg _) hCode 2
        · norm_num
      _ = C * Real.rpow L (2 * (K : ℝ)) * Real.exp (t / 16) := by
        dsimp [C]
        have hExp : (Real.exp (t / (32 * (K : ℝ)))) ^ (2 * K) =
            Real.exp (t / 16) := by
          have hKne : (K : ℝ) ≠ 0 := ne_of_gt hK
          calc
            _ = Real.exp ((2 * K : ℕ) * (t / (32 * (K : ℝ)))) :=
              (Real.exp_nat_mul (t / (32 * (K : ℝ))) (2 * K)).symm
            _ = Real.exp (t / 16) := by
              congr 1
              rw [Nat.cast_mul]
              field_simp [hKne]
              ring
        have hFour : (4 : ℝ) ^ (2 * K) = (16 : ℝ) ^ K := by
          calc
            (4 : ℝ) ^ (2 * K) = (4 : ℝ) ^ (K * 2) := by congr 1; omega
            _ = ((4 : ℝ) ^ 2) ^ K := by
              rw [← pow_mul]
              congr 1
              omega
            _ = (16 : ℝ) ^ K := by norm_num
        have hOuter : ((4 * L * Real.exp (t / (32 * (K : ℝ)))) ^ K) ^ 2 =
            (4 * L * Real.exp (t / (32 * (K : ℝ)))) ^ (2 * K) := by
          rw [← pow_mul]
          congr 1
          omega
        have hExpand : (4 * L * Real.exp (t / (32 * (K : ℝ)))) ^ (2 * K) =
            (4 : ℝ) ^ (2 * K) * L ^ (2 * K) *
              (Real.exp (t / (32 * (K : ℝ)))) ^ (2 * K) := by
          rw [show 4 * L * Real.exp (t / (32 * (K : ℝ))) =
            ((4 : ℝ) * L) * Real.exp (t / (32 * (K : ℝ))) by ring, mul_pow, mul_pow]
        calc
          _ = 400 * ((4 : ℝ) ^ (2 * K) * L ^ (2 * K) *
              (Real.exp (t / (32 * (K : ℝ)))) ^ (2 * K)) := by rw [hOuter, hExpand]
          _ = 400 * (16 : ℝ) ^ K * Real.rpow L (2 * (K : ℝ)) * Real.exp (t / 16) := by
            rw [hFour, hExp]
            rw [hRpowNat.symm]
            ring
          _ = _ := by rfl
  calc
    400 * ((pd1c_trialCodeFinset x K a I iStar).card : ℝ) ^ 2 ≤
        C * Real.rpow L (2 * (K : ℝ)) * Real.exp (t / 16) := hCodeSq
    _ ≤ Real.exp (Real.rpow L (1 / 10 : ℝ) / 16) * Real.exp (t / 16) := by
      apply mul_le_mul_of_nonneg_right
      · exact hpoly
      · exact Real.exp_nonneg _
    _ ≤ Real.exp (t / 8) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith

lemma pd1c_goodTestTwo_markov_bound (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (p : PrimeLists x K) (d₀ : ℝ) (I : Finset (Fin K)) (iStar : Fin K)
    (hx : 2 ≤ x)
    (hMass : ∀ i, 0 < bandMass x (a i))
    (hCard : 400 * ((pd1c_trialCodeFinset x K a I iStar).card : ℝ) ^ 2 ≤
      Real.exp (Real.rpow (Real.log x) (a iStar) / 8)) :
    (∫ r in (0 : ℝ)..1,
      if Real.exp (-(1 / 4 : ℝ) * Real.rpow (Real.log x) (a iStar)) <
        pd1c_goodTestTwoBadWeight x K a p d₀ I iStar
          (100 * Real.exp (-Real.rpow (Real.log x) (a iStar))) r
      then (1 : ℝ) else 0) ≤
        Real.exp (-(1 / 2 : ℝ) * Real.rpow (Real.log x) (a iStar)) := by
  classical
  let t := Real.rpow (Real.log x) (a iStar)
  let e := 100 * Real.exp (-t)
  let θ := Real.exp (-(1 / 4 : ℝ) * t)
  let f := pd1c_goodTestTwoBadWeight x K a p d₀ I iStar e
  have hf : Measurable f := by
    simpa [f] using pd1c_goodTestTwoBadWeight_measurable x K a p d₀ I iStar e
  have hfInt : IntervalIntegrable f volume 0 1 := by
    simpa [f] using pd1c_goodTestTwoBadWeight_intervalIntegrable x K a p d₀ I iStar e
  have hfNonneg : ∀ r, 0 ≤ f r := by
    intro r
    have hweight : ∀ fresh ∈ pd1c_freshChoiceSet x K a I,
        0 ≤ freshChoiceWeight x a I fresh := by
      intro fresh hfresh
      exact pd1c_freshChoiceWeight_nonneg x K a I fresh hMass
        ((pd1c_freshChoice_iff_mem x K a I fresh).2 hfresh)
    simp [f, pd1c_goodTestTwoBadWeight]
    apply Finset.sum_nonneg
    intro fresh hfresh
    by_cases hr : r ∈ pd1c_goodnessTrialPair_collisionSet x K a p d₀ I iStar fresh e
    · simp [hr]
      exact hweight fresh hfresh
    · simp [hr]
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hmoment := pd1c_goodTestTwoBadWeight_integral_bound
    x K a p d₀ I iStar hMass e he
  have hmark := pd1c_interval_markov_bad_integral f hf hfInt hfNonneg θ hθ
  have hratio : Real.exp (-t) / Real.exp (-(1 / 4 : ℝ) * t) =
      Real.exp (-(3 / 4 : ℝ) * t) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  have hmoment' : (∫ r in (0 : ℝ)..1, f r) / θ ≤
      Real.exp (-(1 / 2 : ℝ) * t) := by
    have hmoment'' : (∫ r in (0 : ℝ)..1, f r) / θ ≤
        (400 * ((pd1c_trialCodeFinset x K a I iStar).card : ℝ) ^ 2) *
          Real.exp (-(3 / 4 : ℝ) * t) := by
      calc
        _ ≤ (((pd1c_trialCodeFinset x K a I iStar).card : ℝ) ^ 2 * (4 * e)) / θ :=
          div_le_div_of_nonneg_right hmoment hθ.le
        _ = (400 * ((pd1c_trialCodeFinset x K a I iStar).card : ℝ) ^ 2) *
            Real.exp (-(3 / 4 : ℝ) * t) := by
          dsimp [e, θ]
          rw [show 4 * (100 * Real.exp (-t)) =
            400 * Real.exp (-t) by ring, hratio]
          ring
    calc
      _ ≤ Real.exp (t / 8) * Real.exp (-(3 / 4 : ℝ) * t) :=
        mul_le_mul_of_nonneg_right hmoment'' (Real.exp_nonneg _)
      _ = Real.exp (-(5 / 8 : ℝ) * t) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-(1 / 2 : ℝ) * t) := by
        apply Real.exp_le_exp.mpr
        have hL : 0 < Real.log x := Real.log_pos (by linarith)
        have ht : 0 ≤ t := Real.rpow_nonneg hL.le _
        nlinarith
  simpa [f, θ, t] using hmark.trans hmoment'

end ArtinPrimitiveRoots.TypeII.PD
