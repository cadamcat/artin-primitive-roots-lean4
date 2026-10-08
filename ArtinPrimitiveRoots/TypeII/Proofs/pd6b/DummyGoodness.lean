import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.PadProbability
import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.PadReindexing
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

open ArtinPrimitiveRoots.TypeII Classical Filter

noncomputable section

/-- Higher fixed bands provide auxiliary label lists without changing the root scales. -/
def higherPDFix {K : ℕ} (F : PDFix K) : PDFix K :=
  { F with a := fun i => (F.a i + (1 / 5 : ℝ)) / 2 }

theorem higherPDFix_valid {K : ℕ} (F : PDFix K) (hF : F.Valid) : (higherPDFix F).Valid := by
  refine ⟨⟨hF.1.1, ?_, ?_⟩, hF.2⟩
  · intro i
    dsimp [higherPDFix]
    constructor <;> linarith [(hF.1.2.1 i).1, (hF.1.2.1 i).2]
  · intro i j hij
    dsimp [higherPDFix]
    linarith [hF.1.2.2 i j hij]

/-- Enough primes in each band yield a valid ordered list of every required slot. -/
theorem validPrimeLists_of_card {x : ℝ} {K : ℕ} (a : Fin K → ℝ)
    (hcard : ∀ i : Fin K, slotCount x ≤ (primeBand x (a i)).card) :
    ∃ p : PrimeLists x K, ValidPrimeLists x K a p := by
  let idx (i : Fin K) (j : Fin (slotCount x)) : Fin (primeBand x (a i)).card :=
    ⟨j.val, lt_of_lt_of_le j.isLt (hcard i)⟩
  let p : PrimeLists x K := fun i j => (primeBand x (a i)).orderEmbOfFin rfl (idx i j)
  have hmem (i : Fin K) (j : Fin (slotCount x)) : p i j ∈ primeBand x (a i) :=
    (primeBand x (a i)).orderEmbOfFin_mem rfl (idx i j)
  refine ⟨p, ⟨fun i j => ⟨(Finset.mem_filter.mp (hmem i j)).2.1, hmem i j⟩, ?_⟩⟩
  intro i j j' hne heq
  have hidx : idx i j = idx i j' := (primeBand x (a i)).orderEmbOfFin rfl |>.injective heq
  have hval : j.val = j'.val := congrArg (fun z : Fin (primeBand x (a i)).card => z.val) hidx
  have hj : j = j' := Fin.ext hval
  exact hne hj

/-- The fixed exponent gaps separate auxiliary omission products from original pad products. -/
theorem higherBand_gap_eventually {K : ℕ} (F : PDFix K) (hF : F.Valid) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → 1 ≤ Real.log x ∧
      ∀ i : Fin K, 4 * Real.rpow (Real.log x) (F.a i) <
        Real.rpow (Real.log x) ((higherPDFix F).a i) := by
  have hevent : ∀ᶠ x : ℝ in atTop, ∀ i : Fin K,
      4 * Real.rpow (Real.log x) (F.a i) < Real.rpow (Real.log x) ((higherPDFix F).a i) := by
    rw [Filter.eventually_all]
    intro i
    have hgap : 0 < (higherPDFix F).a i - F.a i := by
      dsimp [higherPDFix]
      linarith [(hF.1.2.1 i).2]
    have ht : Tendsto (fun x : ℝ => Real.rpow (Real.log x) ((higherPDFix F).a i - F.a i))
        atTop atTop := (tendsto_rpow_atTop hgap).comp Real.tendsto_log_atTop
    filter_upwards [ht.eventually_gt_atTop 4, eventually_ge_atTop (2 : ℝ)] with x hx hx₂
    have hL : 0 < Real.log x := Real.log_pos (by linarith)
    have hpos : 0 < Real.rpow (Real.log x) (F.a i) := Real.rpow_pos_of_pos hL _
    have hprod : Real.rpow (Real.log x) ((higherPDFix F).a i) =
        Real.rpow (Real.log x) (F.a i) *
          Real.rpow (Real.log x) ((higherPDFix F).a i - F.a i) := by
      calc
        _ = Real.rpow (Real.log x) (F.a i + ((higherPDFix F).a i - F.a i)) := by congr 1 <;> ring
        _ = _ := Real.rpow_add hL _ _
    rw [hprod]
    simpa only [mul_comm] using mul_lt_mul_of_pos_left hx hpos
  have hboth : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x ∧
      ∀ i : Fin K, 4 * Real.rpow (Real.log x) (F.a i) <
        Real.rpow (Real.log x) ((higherPDFix F).a i) := by
    filter_upwards [hevent, Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hx hL
    exact ⟨hL, hx⟩
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.mp hboth
  exact ⟨max 2 x₁, le_max_left _ _, fun x hx => hx₁ x ((le_max_right _ _).trans hx)⟩

/-- Harmonic mass and the least possible prime bound control the band cardinality. -/
private theorem bandCard_lower (x a P c : ℝ) (hP : 0 < P) (hc : c ≤ bandMass x a)
    (hLower : ∀ p ∈ primeBand x a, P ≤ (p : ℝ)) :
    P * c ≤ ((primeBand x a).card : ℝ) := by
  have hmass : bandMass x a ≤ ((primeBand x a).card : ℝ) / P := by
    unfold bandMass
    calc
      _ ≤ ∑ p ∈ primeBand x a, P⁻¹ := by
        apply Finset.sum_le_sum
        intro p hp
        have hpPos : 0 < (p : ℝ) := hP.trans_le (hLower p hp)
        simpa only [one_div] using (inv_le_inv₀ hpPos hP).mpr (hLower p hp)
      _ = _ := by simp [div_eq_mul_inv]
  have h := (le_div_iff₀ hP).mp (hc.trans hmass)
  simpa only [mul_comm] using h

/-- Eventually every valid band contains all slots required by the moment parameter. -/
theorem validPrimeLists_exist_eventually {K : ℕ} (a : Fin K → ℝ) (ha : ValidBands K a) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → ∃ p : PrimeLists x K, ValidPrimeLists x K a p := by
  let c := Real.log 2 / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hMassEvent : ∀ᶠ x : ℝ in atTop, ∀ i : Fin K, c ≤ bandMass x (a i) := by
    rw [Filter.eventually_all]
    intro i
    have ha₀ : 0 < a i := (by norm_num : (0 : ℝ) < 1 / 10).trans (ha.2.1 i).1
    have ha₁ : a i < 1 := (ha.2.1 i).2.trans (by norm_num)
    obtain ⟨x₁, hx₁, hm⟩ := band_mass (a i) ha₀ ha₁ c hc
    filter_upwards [eventually_ge_atTop x₁] with x hx
    have habs := abs_le.mp (hm x hx).1
    dsimp [c] at *
    linarith
  have hT : Tendsto (fun x : ℝ => Real.rpow (Real.log x) (1 / 10 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop
  have hRatio : Tendsto (fun x : ℝ => Real.exp (Real.rpow (Real.log x) (1 / 10 : ℝ)) /
      Real.rpow (Real.log x) (1 / 10 : ℝ)) atTop atTop := by
    have hbase : Tendsto (fun T : ℝ => Real.exp T / T) atTop atTop := by
      simpa only [Real.rpow_one] using tendsto_exp_div_rpow_atTop (1 : ℝ)
    change Tendsto ((fun T : ℝ => Real.exp T / T) ∘
      (fun x : ℝ => Real.rpow (Real.log x) (1 / 10 : ℝ))) atTop atTop
    exact hbase.comp hT
  have hEvent : ∀ᶠ x : ℝ in atTop, (∀ i : Fin K, c ≤ bandMass x (a i)) ∧
      1 ≤ Real.log x ∧ 2 / c ≤ Real.exp (Real.rpow (Real.log x) (1 / 10 : ℝ)) /
        Real.rpow (Real.log x) (1 / 10 : ℝ) := by
    filter_upwards [hMassEvent, Real.tendsto_log_atTop.eventually_ge_atTop 1,
      hRatio.eventually_ge_atTop (2 / c)] with x hmass hlog hratio
    exact ⟨hmass, hlog, hratio⟩
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.mp hEvent
  refine ⟨max 2 x₁, le_max_left _ _, ?_⟩
  intro x hx
  obtain ⟨hmass, hlog, hratio⟩ := hx₁ x ((le_max_right _ _).trans hx)
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (by norm_num) hlog
  let T := Real.rpow (Real.log x) (1 / 10 : ℝ)
  have hTpos : 0 < T := Real.rpow_pos_of_pos hLpos _
  have hTone : 1 ≤ T := Real.one_le_rpow hlog (by norm_num)
  have hJ : (momentJ x : ℝ) ≤ T :=
    (Nat.floor_le (Real.rpow_nonneg hLpos.le (1 / 100 : ℝ))).trans
      (Real.rpow_le_rpow_of_exponent_le hlog (by norm_num))
  have hslots : (slotCount x : ℝ) ≤ 2 * T := by
    have heq : (slotCount x : ℝ) = (momentJ x : ℝ) + 1 := by simp [slotCount]
    rw [heq]
    linarith
  have hexp : 2 * T ≤ c * Real.exp T := by
    have h := mul_le_mul_of_nonneg_left ((le_div_iff₀ hTpos).mp hratio) hc.le
    have hcancel : c * (2 / c * T) = 2 * T := by field_simp [hc.ne']
    rwa [hcancel] at h
  apply validPrimeLists_of_card a
  intro i
  have hLower (p : ℕ) (hp : p ∈ primeBand x (a i)) : Real.exp T ≤ (p : ℝ) := by
    have hpow : T ≤ Real.rpow (Real.log x) (a i) :=
      Real.rpow_le_rpow_of_exponent_le hlog (ha.2.1 i).1.le
    exact (Real.exp_le_exp.mpr hpow).trans (Finset.mem_filter.mp hp).2.2.1
  have hcard := bandCard_lower x (a i) (Real.exp T) c (Real.exp_pos _) (hmass i) hLower
  have hslotsCard : (slotCount x : ℝ) ≤ ((primeBand x (a i)).card : ℝ) :=
    hslots.trans (hexp.trans (by simpa only [mul_comm] using hcard))
  exact_mod_cast hslotsCard


/-- Exactly J labels remain in each group after an arbitrary omission. -/
private theorem omission_scalar_sum {x : ℝ} (j₀ : Fin (slotCount x)) (c : ℝ) :
    (∑ j : Fin (slotCount x), if j ≠ j₀ then c else 0) = (momentJ x : ℝ) * c := by
  have hfilter : (Finset.univ : Finset (Fin (slotCount x))).filter (fun j => j ≠ j₀) =
      Finset.univ.erase j₀ := by ext j; simp [ne_comm]
  have hcard : ((Finset.univ : Finset (Fin (slotCount x))).erase j₀).card = momentJ x := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j₀), Finset.card_univ, Fintype.card_fin]
    simp only [slotCount, Nat.add_sub_cancel]
  rw [← Finset.sum_filter, hfilter]
  simp only [Finset.sum_const, nsmul_eq_mul, hcard]

/-- The logarithm of an omission product lies between its band endpoint sums. -/
theorem omissionProduct_log_bounds {x : ℝ} {K : ℕ} (a : Fin K → ℝ)
    (p : PrimeLists x K) (hp : ValidPrimeLists x K a p)
    (omitted : Fin K → Fin (slotCount x)) :
    (∑ i : Fin K, (momentJ x : ℝ) * Real.rpow (Real.log x) (a i)) ≤
        Real.log (omissionProduct p omitted : ℝ) ∧
      Real.log (omissionProduct p omitted : ℝ) ≤
        ∑ i : Fin K, (momentJ x : ℝ) * (2 * Real.rpow (Real.log x) (a i)) := by
  have hpos (i : Fin K) (j : Fin (slotCount x)) :
      0 < ((if j ≠ omitted i then p i j else 1 : ℕ) : ℝ) := by
    split_ifs
    · exact Nat.cast_pos.mpr (hp.1 i j).1.pos
    · norm_num
  have hLog : Real.log (omissionProduct p omitted : ℝ) =
      ∑ i : Fin K, ∑ j : Fin (slotCount x),
        Real.log ((if j ≠ omitted i then p i j else 1 : ℕ) : ℝ) := by
    unfold omissionProduct
    rw [Nat.cast_prod, Real.log_prod]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [Nat.cast_prod, Real.log_prod]
      intro j hj
      exact (hpos i j).ne'
    · intro i hi
      apply ne_of_gt
      rw [Nat.cast_prod]
      exact Finset.prod_pos (fun j hj => hpos i j)
  have hLow (i : Fin K) (j : Fin (slotCount x)) :
      (if j ≠ omitted i then Real.rpow (Real.log x) (a i) else 0) ≤
        Real.log ((if j ≠ omitted i then p i j else 1 : ℕ) : ℝ) := by
    by_cases hj : j ≠ omitted i
    · rw [if_pos hj, if_pos hj]
      have h := Real.log_le_log (Real.exp_pos _) (Finset.mem_filter.mp (hp.1 i j).2).2.2.1
      simpa only [Real.log_exp] using h
    · simp [hj]
  have hHi (i : Fin K) (j : Fin (slotCount x)) :
      Real.log ((if j ≠ omitted i then p i j else 1 : ℕ) : ℝ) ≤
        (if j ≠ omitted i then 2 * Real.rpow (Real.log x) (a i) else 0) := by
    by_cases hj : j ≠ omitted i
    · rw [if_pos hj, if_pos hj]
      have h := Real.log_le_log (Nat.cast_pos.mpr (hp.1 i j).1.pos)
        (Finset.mem_filter.mp (hp.1 i j).2).2.2.2
      simpa only [Real.log_exp] using h
    · simp [hj]
  rw [hLog]
  constructor
  · calc
      _ = ∑ i : Fin K, ∑ j : Fin (slotCount x),
          if j ≠ omitted i then Real.rpow (Real.log x) (a i) else 0 := by
        simp_rw [omission_scalar_sum]
      _ ≤ _ := Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hLow i j))
  · calc
      _ ≤ ∑ i : Fin K, ∑ j : Fin (slotCount x),
          if j ≠ omitted i then 2 * Real.rpow (Real.log x) (a i) else 0 :=
        Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hHi i j))
      _ = _ := by simp_rw [omission_scalar_sum]

/-- If no omission lies in a pad dyad, both goodness tests hold for every ratio. -/
theorem isGoodRatio_of_no_eligible_omission (x Y d₀ : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (p : PrimeLists x K)
    (houtside : ∀ omitted : Fin K → Fin (slotCount x),
      ¬ (d₀ ≤ (omissionProduct p omitted : ℝ) ∧ (omissionProduct p omitted : ℝ) < 2 * d₀)) :
    ∀ r : ℝ, IsGoodRatio x Y d₀ K a p r := by
  intro r
  constructor
  · intro omitted hlo hhi
    exact (houtside omitted ⟨hlo, hhi⟩).elim
  · intro I hI
    dsimp only
    have hTrial (fresh : Fin K → ℕ) (n : ℕ) :
        ¬ IsGoodnessTrialValue a p d₀ I (I.max' hI) fresh n := by
      rintro ⟨omitted, z, hEq, hlo, hhi, hz⟩
      exact houtside omitted ⟨hlo, hhi⟩
    have hsum :
        (∑' fresh : Fin K → ℕ,
          if IsFreshChoice x a I fresh ∧
              ∃ n₁ n₂, IsGoodnessTrialValue a p d₀ I (I.max' hI) fresh n₁ ∧
                IsGoodnessTrialValue a p d₀ I (I.max' hI) fresh n₂ ∧ n₁ ≠ n₂ ∧
                circleDistance (((n₁ : ℝ) - n₂) * r) ≤
                  100 * Real.exp (-Real.rpow (Real.log x) (a (I.max' hI)))
          then freshChoiceWeight x a I fresh else 0) = 0 := by
      simp [hTrial]
    rw [hsum]
    positivity


/-- Higher-band omission products miss the dyad of every original supported source pad. -/
theorem higherLists_good_of_sourcePad {x Y : ℝ} {K : ℕ}
    (F : PDFix K) (hF : F.Valid) (hL : 1 ≤ Real.log x)
    (hgap : ∀ i : Fin K, 4 * Real.rpow (Real.log x) (F.a i) <
      Real.rpow (Real.log x) ((higherPDFix F).a i))
    (p q : PrimeLists x K) (hp : ValidPrimeLists x K F.a p)
    (hq : ValidPrimeLists x K (higherPDFix F).a q)
    (d₀ : ℕ) (hd₀ : 0 < d₀) (hd : (d₀ : ℝ) ≤ (sharedProduct p : ℝ)) :
    ∀ r : ℝ, IsGoodRatio x Y (d₀ : ℝ) K (higherPDFix F).a q r := by
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (by norm_num) hL
  have hJ : 1 ≤ momentJ x := by
    change 1 ≤ ⌊Real.rpow (Real.log x) (1 / 100 : ℝ)⌋₊
    apply (Nat.le_floor_iff (Real.rpow_nonneg hLpos.le (1 / 100 : ℝ))).mpr
    simpa only [Nat.cast_one] using
      (Real.one_le_rpow hL (by norm_num : (0 : ℝ) ≤ (1 / 100 : ℝ)))
  have hJR : (1 : ℝ) ≤ momentJ x := by exact_mod_cast hJ
  have hJpos : 0 < (momentJ x : ℝ) := lt_of_lt_of_le (by norm_num) hJR
  let A := ∑ i : Fin K, (momentJ x : ℝ) * (2 * Real.rpow (Real.log x) (F.a i))
  let B := ∑ i : Fin K, (momentJ x : ℝ) * Real.rpow (Real.log x) ((higherPDFix F).a i)
  let i₀ : Fin K := ⟨0, hF.1.1⟩
  have hAlo : 2 ≤ A := by
    have hOne : 1 ≤ Real.rpow (Real.log x) (F.a i₀) :=
      Real.one_le_rpow hL ((by norm_num : (0 : ℝ) < 1 / 10).trans (hF.1.2.1 i₀).1).le
    have hmul := mul_le_mul hJR hOne (by norm_num : (0 : ℝ) ≤ 1) (by positivity)
    have hterm : 2 ≤ (momentJ x : ℝ) * (2 * Real.rpow (Real.log x) (F.a i₀)) := by nlinarith
    exact hterm.trans (Finset.single_le_sum
      (fun (i : Fin K) hi => mul_nonneg hJpos.le (mul_nonneg (by norm_num) (Real.rpow_nonneg hLpos.le _)))
      (Finset.mem_univ i₀))
  have hSum : 2 * A < B := by
    have hterm (i : Fin K) : 2 * ((momentJ x : ℝ) * (2 * Real.rpow (Real.log x) (F.a i))) <
        (momentJ x : ℝ) * Real.rpow (Real.log x) ((higherPDFix F).a i) := by
      have h := mul_lt_mul_of_pos_left (hgap i) hJpos
      nlinarith
    have h := Finset.sum_lt_sum (fun i hi => (hterm i).le)
      ⟨i₀, Finset.mem_univ i₀, hterm i₀⟩
    rw [← Finset.mul_sum] at h
    exact h
  have hOrig : Real.log (sharedProduct p : ℝ) ≤ A := by
    rw [sharedProduct_eq_omission_last]
    exact (omissionProduct_log_bounds F.a p hp (fun _ => lastSlot x)).2
  have hd₀R : 0 < (d₀ : ℝ) := by exact_mod_cast hd₀
  have hDpos : 0 < (sharedProduct p : ℝ) := hd₀R.trans_le hd
  have hLogd := (Real.log_le_log hd₀R hd).trans hOrig
  have hlog2le : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  apply isGoodRatio_of_no_eligible_omission
  intro omitted helig
  have hDummy := (omissionProduct_log_bounds (higherPDFix F).a q hq omitted).1
  have hOmPos : 0 < (omissionProduct q omitted : ℝ) := by
    apply Nat.cast_pos.mpr
    unfold omissionProduct
    apply Finset.prod_pos
    intro i hi
    apply Finset.prod_pos
    intro j hj
    split_ifs
    · exact (hq.1 i j).1.pos
    · norm_num
  have hLog : Real.log (2 * (d₀ : ℝ)) < Real.log (omissionProduct q omitted : ℝ) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hd₀R.ne']
    calc
      _ ≤ Real.log 2 + A := by linarith
      _ < 2 * A := by linarith
      _ < B := hSum
      _ ≤ _ := hDummy
  have hBig : 2 * (d₀ : ℝ) < (omissionProduct q omitted : ℝ) :=
    (Real.log_lt_log_iff (by positivity) hOmPos).mp hLog
  exact (not_lt_of_ge hBig.le) helig.2


end
end ArtinPrimitiveRoots.TypeII.PD
