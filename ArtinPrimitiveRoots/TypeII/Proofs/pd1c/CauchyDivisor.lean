import ArtinPrimitiveRoots.TypeII.Proofs.pd0.MomentArithmetic
import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.PositiveOperator
import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.BandGeometry

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical
open Proofs.pd0
set_option maxHeartbeats 1000000

lemma pd1c_progression_divisibility_card (H l d : ℕ) (hd : 0 < d) :
    ((Finset.range (H + 1)).filter fun h => d ∣ 1 + l * h).card ≤ H / d + 1 := by
  let s := (Finset.range (H + 1)).filter fun h => d ∣ 1 + l * h
  by_cases hs : s.Nonempty
  · obtain ⟨h₀, hh₀⟩ := hs
    have hd₀ : d ∣ 1 + l * h₀ := (Finset.mem_filter.mp hh₀).2
    have hcBase : Nat.Coprime (1 + l * h₀) l :=
      (Nat.coprime_add_mul_left_left 1 l h₀).mpr (Nat.coprime_one_left l)
    have hcop : Nat.Coprime d l := hcBase.of_dvd_left hd₀
    have hcopInt : Int.gcd (d : ℤ) (l : ℤ) = 1 := by
      rw [Int.gcd_natCast_natCast]
      exact hcop.gcd_eq_one
    have hResidue : ∀ a ∈ s, ∀ b ∈ s, a % d = b % d := by
      intro a ha b hb
      have hda : (d : ℤ) ∣ 1 + (l : ℤ) * (a : ℤ) := by exact_mod_cast (Finset.mem_filter.mp ha).2
      have hdb : (d : ℤ) ∣ 1 + (l : ℤ) * (b : ℤ) := by exact_mod_cast (Finset.mem_filter.mp hb).2
      have hdDiff : (d : ℤ) ∣ (l : ℤ) * ((a : ℤ) - (b : ℤ)) := by
        convert dvd_sub hda hdb using 1 <;> ring
      have hab : (d : ℤ) ∣ (a : ℤ) - (b : ℤ) :=
        Int.dvd_of_dvd_mul_left_of_gcd_one (by simpa [mul_comm] using hdDiff) hcopInt
      have hba : (d : ℤ) ∣ (b : ℤ) - (a : ℤ) := by simpa using dvd_neg.mpr hab
      have hZ : (a : ZMod d) = (b : ZMod d) := by
        simpa only [Int.cast_natCast] using (ZMod.intCast_eq_intCast_iff_dvd_sub (a : ℤ) (b : ℤ) d).mpr hba
      exact (ZMod.natCast_eq_natCast_iff' a b d).mp hZ
    letI : Fintype s := Fintype.ofFinset s (by intro h; rfl)
    let f : s → Fin (H / d + 1) := fun h =>
      ⟨h.1 / d, Nat.lt_succ_of_le (Nat.div_le_div_right
        (Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp h.2).1)))⟩
    have hf : Function.Injective f := by
      intro a b hab
      have hq : a.1 / d = b.1 / d := congrArg Fin.val hab
      have hm := hResidue a.1 a.2 b.1 b.2
      have ha := Nat.mod_add_div a.1 d
      have hb := Nat.mod_add_div b.1 d
      rw [hm, hq] at ha
      apply Subtype.ext
      exact ha.symm.trans hb
    have hc := Fintype.card_le_of_injective f hf
    simpa [s, Fintype.card_coe] using hc
  · have hzero : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    change s.card ≤ _
    rw [hzero, Finset.card_empty]
    exact Nat.zero_le _

lemma pd1c_four_factor_small_remainder (f : Fin 4 → ℕ) (n : ℕ)
    (hf : f ∈ factorTuples 4 n) (i : Fin 4) (hMax : ∀ j, f j ≤ f i) :
    let t := fun j : Fin 3 => f (i.succAbove j)
    0 < ∏ j, t j ∧ (∏ j, t j) ^ 4 ≤ n ^ 3 := by
  let t := fun j : Fin 3 => f (i.succAbove j)
  have hEntry : ∀ j, 0 < f j := by
    intro j
    have h := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hf).1 j
    exact Nat.succ_le_iff.mp (Finset.mem_filter.mp h).2
  have hProd : ∏ j : Fin 4, f j = n := (Finset.mem_filter.mp hf).2
  have hn : f i * (∏ j : Fin 3, t j) = n := by
    rw [← hProd, Fin.prod_univ_succAbove f i]
  have ht : 0 < ∏ j : Fin 3, t j := Finset.prod_pos fun j hj => hEntry _
  have hsmall : ∏ j : Fin 3, t j ≤ (f i) ^ 3 := by
    calc
      _ ≤ ∏ j : Fin 3, f i := Finset.prod_le_prod (fun j hj => hMax _)
      _ = _ := by simp
  refine ⟨ht, ?_⟩
  change (∏ j : Fin 3, t j) ^ 4 ≤ n ^ 3
  calc
    _ = (∏ j : Fin 3, t j) * (∏ j : Fin 3, t j) ^ 3 := by ring
    _ ≤ (f i) ^ 3 * (∏ j : Fin 3, t j) ^ 3 := Nat.mul_le_mul_right _ hsmall
    _ = (f i * (∏ j : Fin 3, t j)) ^ 3 := (mul_pow _ _ _).symm
    _ = n ^ 3 := by rw [hn]


lemma pd1c_factorTuple_entry_pos {r n : ℕ} {f : Fin r → ℕ} (hf : f ∈ factorTuples r n) :
    ∀ j, 0 < f j := by
  intro j
  have h := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hf).1 j
  exact Nat.succ_le_iff.mp (Finset.mem_filter.mp h).2

lemma pd1c_positive_triple_box_mem (t : Fin 3 → ℕ) (D : ℕ) (ht : ∀ j, 0 < t j)
    (hprod : ∏ j, t j ≤ D) : t ∈ positiveProductBox 3 D := by
  have hpos : 0 < ∏ j, t j := Finset.prod_pos fun j hj => ht j
  apply Finset.mem_filter.mpr
  refine ⟨Fintype.mem_piFinset.mpr ?_, hprod⟩
  intro j
  have hle : t j ≤ D :=
    (Nat.le_of_dvd hpos (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))).trans hprod
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hle), by have h := ht j; omega⟩

lemma pd1c_four_factor_remainder_box (f : Fin 4 → ℕ) (n : ℕ)
    (hf : f ∈ factorTuples 4 n) (i : Fin 4) (hMax : ∀ j, f j ≤ f i)
    (Z : ℝ) (hZ : 0 ≤ Z) (hnZ : (n : ℝ) ≤ Z) :
    (fun j : Fin 3 => f (i.succAbove j)) ∈
      positiveProductBox 3 (⌊Z ^ (3 / 4 : ℝ)⌋₊) := by
  let t := fun j : Fin 3 => f (i.succAbove j)
  let d := ∏ j : Fin 3, t j
  have hSmall := pd1c_four_factor_small_remainder f n hf i hMax
  have hNat : d ^ 4 ≤ n ^ 3 := hSmall.2
  have hReal : (d : ℝ) ^ 4 ≤ (n : ℝ) ^ 3 := by exact_mod_cast hNat
  have hUp : (n : ℝ) ^ 3 ≤ Z ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg _) hnZ 3
  have hRoot := pd1c_power_bound_to_rpow (d : ℝ) Z 1 (Nat.cast_nonneg _) hZ (by norm_num)
    4 (by norm_num) (by simpa using hReal.trans hUp)
  have hdZ : (d : ℝ) ≤ Z ^ (3 / 4 : ℝ) := by
    norm_num [Real.rpow_eq_pow] at hRoot
    exact hRoot
  have hdD : d ≤ ⌊Z ^ (3 / 4 : ℝ)⌋₊ := (Nat.le_floor_iff (Real.rpow_nonneg hZ _)).mpr hdZ
  exact pd1c_positive_triple_box_mem t _
    (fun j => pd1c_factorTuple_entry_pos hf _) hdD


noncomputable def pd1c_fourMaxIndex (f : Fin 4 → ℕ) : Fin 4 :=
  Classical.choose (Finset.exists_max_image Finset.univ f (by simp))

lemma pd1c_fourMaxIndex_spec (f : Fin 4 → ℕ) (j : Fin 4) : f j ≤ f (pd1c_fourMaxIndex f) :=
  (Classical.choose_spec (Finset.exists_max_image Finset.univ f (by simp))).2 j (Finset.mem_univ _)

lemma pd1c_four_tuple_determined (f g : Fin 4 → ℕ) (n : ℕ)
    (hf : f ∈ factorTuples 4 n) (hg : g ∈ factorTuples 4 n) (i : Fin 4)
    (hrest : (fun j : Fin 3 => f (i.succAbove j)) = (fun j : Fin 3 => g (i.succAbove j))) : f = g := by
  have hProdF : f i * (∏ j : Fin 3, f (i.succAbove j)) = n := by
    rw [← (Finset.mem_filter.mp hf).2, Fin.prod_univ_succAbove f i]
  have hProdG : g i * (∏ j : Fin 3, g (i.succAbove j)) = n := by
    rw [← (Finset.mem_filter.mp hg).2, Fin.prod_univ_succAbove g i]
  have hProdRest : (∏ j : Fin 3, f (i.succAbove j)) = ∏ j : Fin 3, g (i.succAbove j) :=
    congrArg (fun t : Fin 3 → ℕ => ∏ j, t j) hrest
  have hRestPos : 0 < ∏ j : Fin 3, f (i.succAbove j) :=
    Finset.prod_pos fun j hj => pd1c_factorTuple_entry_pos hf _
  have hMid : f i = g i := by
    apply Nat.mul_right_cancel hRestPos
    rw [hProdF, hProdRest, hProdG]
  funext j
  exact Fin.succAboveCases i hMid (fun k => congrFun hrest k) j

lemma pd1c_quad_progression_card_bound (H l : ℕ) (Z : ℝ) (hZ : 0 ≤ Z)
    (hBound : ∀ h : ℕ, h ≤ H → (1 + l * h : ℝ) ≤ Z) :
    let D := ⌊Z ^ (3 / 4 : ℝ)⌋₊
    (∑ h ∈ Finset.range (H + 1), ((factorTuples 4 (1 + l * h)).card : ℝ)) ≤
      4 * (((H : ℝ) + (D : ℝ)) *
        (∑ n ∈ positiveRange D, ((n : ℝ)⁻¹)) ^ 3) := by
  let D := ⌊Z ^ (3 / 4 : ℝ)⌋₊
  let dom := Σ h : (Finset.range (H + 1)), (factorTuples 4 (1 + l * h.1))
  let cod := Fin 4 × Σ t : (positiveProductBox 3 D),
    ((Finset.range (H + 1)).filter fun h => (∏ j : Fin 3, t.1 j) ∣ 1 + l * h)
  let enc : dom → cod := fun x => by
    let i := pd1c_fourMaxIndex x.2.1
    let t := fun j : Fin 3 => x.2.1 (i.succAbove j)
    have ht : t ∈ positiveProductBox 3 D :=
      pd1c_four_factor_remainder_box x.2.1 (1 + l * x.1.1) x.2.2 i
        (pd1c_fourMaxIndex_spec x.2.1) Z hZ
        (by exact_mod_cast hBound x.1.1 (Nat.le_of_lt_succ (Finset.mem_range.mp x.1.2)))
    have hprod : x.2.1 i * (∏ j : Fin 3, t j) = 1 + l * x.1.1 := by
      exact (Fin.prod_univ_succAbove x.2.1 i).symm.trans (Finset.mem_filter.mp x.2.2).2
    refine ⟨i, ⟨⟨t, ht⟩, ⟨x.1.1, Finset.mem_filter.mpr ⟨x.1.2, ?_⟩⟩⟩⟩
    exact ⟨x.2.1 i, by simpa [mul_comm] using hprod.symm⟩
  have henc : Function.Injective enc := by
    rintro ⟨⟨h, hh⟩, ⟨f, hf⟩⟩ ⟨⟨k, hk⟩, ⟨g, hg⟩⟩ heq
    have hhEq := congrArg (fun z : cod => z.2.2.1) heq
    change h = k at hhEq
    subst k
    have hi := congrArg (fun z : cod => z.1) heq
    change pd1c_fourMaxIndex f = pd1c_fourMaxIndex g at hi
    have ht := congrArg (fun z : cod => z.2.1.1) heq
    change (fun j : Fin 3 => f ((pd1c_fourMaxIndex f).succAbove j)) =
      (fun j : Fin 3 => g ((pd1c_fourMaxIndex g).succAbove j)) at ht
    rw [← hi] at ht
    have hfg := pd1c_four_tuple_determined f g (1 + l * h) hf hg (pd1c_fourMaxIndex f) ht
    subst g
    rfl
  have hDomCard : Fintype.card dom = ∑ h ∈ Finset.range (H + 1), (factorTuples 4 (1 + l * h)).card := by
    simp only [dom, Fintype.card_sigma, Fintype.card_coe]
    exact Finset.sum_coe_sort (Finset.range (H + 1))
      (fun h : ℕ => (factorTuples 4 (1 + l * h)).card)
  have hCodCard : Fintype.card cod = 4 *
      ∑ t ∈ positiveProductBox 3 D,
        ((Finset.range (H + 1)).filter fun h => (∏ j : Fin 3, t j) ∣ 1 + l * h).card := by
    simp only [cod, Fintype.card_prod, Fintype.card_fin, Fintype.card_sigma, Fintype.card_coe]
    apply congrArg (fun n : ℕ => 4 * n)
    exact Finset.sum_coe_sort (positiveProductBox 3 D)
      (fun t : Fin 3 → ℕ => ((Finset.range (H + 1)).filter fun h => (∏ j, t j) ∣ 1 + l * h).card)
  have hNat := Fintype.card_le_of_injective enc henc
  rw [hDomCard, hCodCard] at hNat
  have hReal : (∑ h ∈ Finset.range (H + 1), ((factorTuples 4 (1 + l * h)).card : ℝ)) ≤
      4 * ∑ t ∈ positiveProductBox 3 D,
        (((Finset.range (H + 1)).filter fun h => (∏ j : Fin 3, t j) ∣ 1 + l * h).card : ℝ) := by
    exact_mod_cast hNat
  have hRoots : ∀ t ∈ positiveProductBox 3 D,
      (((Finset.range (H + 1)).filter fun h => (∏ j : Fin 3, t j) ∣ 1 + l * h).card : ℝ) ≤
        (H : ℝ) / ((∏ j : Fin 3, t j : ℕ) : ℝ) + 1 := by
    intro t ht
    have htPos : ∀ j, 0 < t j := by
      intro j
      have h := Fintype.mem_piFinset.mp (Finset.mem_filter.mp ht).1 j
      exact Nat.succ_le_iff.mp (Finset.mem_filter.mp h).2
    have hd : 0 < ∏ j : Fin 3, t j := Finset.prod_pos fun j hj => htPos j
    have hdR : 0 < ((∏ j : Fin 3, t j : ℕ) : ℝ) := by exact_mod_cast hd
    have hc := pd1c_progression_divisibility_card H l (∏ j : Fin 3, t j) hd
    have hcR : (((Finset.range (H + 1)).filter fun h => (∏ j : Fin 3, t j) ∣ 1 + l * h).card : ℝ) ≤
        ((H / (∏ j : Fin 3, t j) : ℕ) : ℝ) + 1 := by exact_mod_cast hc
    have hDiv : ((H / (∏ j : Fin 3, t j) : ℕ) : ℝ) ≤ (H : ℝ) / ((∏ j : Fin 3, t j : ℕ) : ℝ) := by
      apply (le_div_iff₀ hdR).mpr
      exact_mod_cast Nat.div_mul_le_self H (∏ j : Fin 3, t j)
    exact hcR.trans (by linarith)
  have hInv (t : Fin 3 → ℕ) : ((∏ j : Fin 3, t j : ℕ) : ℝ)⁻¹ = ∏ j : Fin 3, (t j : ℝ)⁻¹ := by
    rw [Nat.cast_prod, Finset.prod_inv_distrib]
  calc
    _ ≤ 4 * ∑ t ∈ positiveProductBox 3 D,
        ((H : ℝ) / ((∏ j : Fin 3, t j : ℕ) : ℝ) + 1) :=
      hReal.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hRoots) (by norm_num))
    _ = 4 * ((H : ℝ) * (∑ t ∈ positiveProductBox 3 D, ∏ j : Fin 3, (t j : ℝ)⁻¹) +
        ((positiveProductBox 3 D).card : ℝ)) := by
      simp only [div_eq_mul_inv, hInv, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ 4 * ((H : ℝ) * (∑ n ∈ positiveRange D, (n : ℝ)⁻¹) ^ 3 +
        (D : ℝ) * (∑ n ∈ positiveRange D, (n : ℝ)⁻¹) ^ 3) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact add_le_add
        (mul_le_mul_of_nonneg_left (positiveProductBox_weight_sum_le 3 D) (Nat.cast_nonneg H))
        (positiveProductBox_card_le 3 D)
    _ = _ := by ring


lemma pd1c_tau_sq_progression_bound (X Y : ℝ) (hX : 1 ≤ X) (hY : 0 < Y)
    (hYsmall : Y ≤ X ^ (1 / 4 : ℝ)) (l : ℕ) (hl : (l : ℝ) ≤ 4 * Y) :
    let D := ⌊(17 * X) ^ (3 / 4 : ℝ)⌋₊
    (∑ h ∈ Finset.range (⌊4 * X / Y⌋₊ + 1), (tau (1 + l * h) : ℝ) ^ 2) ≤
      84 * (X / Y) * (1 + Real.log (D : ℝ)) ^ 3 := by
  let H := ⌊4 * X / Y⌋₊
  let D := ⌊(17 * X) ^ (3 / 4 : ℝ)⌋₊
  have hXpos : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hH : (H : ℝ) ≤ 4 * X / Y := Nat.floor_le (by positivity)
  have hBound : ∀ h : ℕ, h ≤ H → (1 + l * h : ℝ) ≤ 17 * X := by
    intro h hh
    have hhR : (h : ℝ) ≤ 4 * X / Y := (Nat.cast_le.mpr hh).trans hH
    have hmul := mul_le_mul hl hhR (Nat.cast_nonneg h) (show 0 ≤ 4 * Y by positivity)
    have hRight : (4 * Y) * (4 * X / Y) = 16 * X := by field_simp [hY.ne'] <;> ring
    rw [hRight] at hmul
    nlinarith
  have hQuad := pd1c_quad_progression_card_bound H l (17 * X) (by positivity) hBound
  have hTau : (∑ h ∈ Finset.range (H + 1), (tau (1 + l * h) : ℝ) ^ 2) ≤
      ∑ h ∈ Finset.range (H + 1), ((factorTuples 4 (1 + l * h)).card : ℝ) := by
    apply Finset.sum_le_sum
    intro h hh
    have h := tau_pow_le_factorTuples_card 2 (1 + l * h) (by omega)
    exact_mod_cast (by simpa using h)
  have h17 : (17 : ℝ) ^ (3 / 4 : ℝ) ≤ 17 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 17) (by norm_num : (3 / 4 : ℝ) ≤ 1)
  have hXrem : X ^ (3 / 4 : ℝ) ≤ X / Y := by
    apply (le_div_iff₀ hY).mpr
    calc
      _ ≤ X ^ (3 / 4 : ℝ) * X ^ (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left hYsmall (Real.rpow_nonneg hXpos.le _)
      _ = X := by
        rw [← Real.rpow_add hXpos]
        norm_num
  have hD : (D : ℝ) ≤ 17 * (X / Y) := by
    calc
      _ ≤ (17 * X) ^ (3 / 4 : ℝ) := Nat.floor_le (by positivity)
      _ = (17 : ℝ) ^ (3 / 4 : ℝ) * X ^ (3 / 4 : ℝ) := Real.mul_rpow (by norm_num) hXpos.le
      _ ≤ 17 * (X / Y) := mul_le_mul h17 hXrem (Real.rpow_nonneg hXpos.le _) (by norm_num)
  have hHarm : 0 ≤ ∑ n ∈ positiveRange D, (n : ℝ)⁻¹ := Finset.sum_nonneg fun n hn => by positivity
  have hHarmBound := harmonicRange_le_one_add_log D
  have hCpow : (∑ n ∈ positiveRange D, (n : ℝ)⁻¹) ^ 3 ≤ (1 + Real.log (D : ℝ)) ^ 3 :=
    pow_le_pow_left₀ hHarm hHarmBound 3
  have hHD : (H : ℝ) + (D : ℝ) ≤ 21 * (X / Y) := by
    calc
      _ ≤ 4 * X / Y + 17 * (X / Y) := add_le_add hH hD
      _ = _ := by ring
  calc
    _ ≤ 4 * (((H : ℝ) + (D : ℝ)) * (∑ n ∈ positiveRange D, (n : ℝ)⁻¹) ^ 3) := hTau.trans hQuad
    _ ≤ 4 * ((21 * (X / Y)) * (1 + Real.log (D : ℝ)) ^ 3) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact mul_le_mul hHD hCpow (pow_nonneg hHarm 3) (by positivity)
    _ = _ := by ring


lemma pd1c_progression_divisor_uniform (c₁ c₂ : ℝ) (K : ℕ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    ∃ CDiv x₀ : ℝ, 0 < CDiv ∧ 2 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x → ∀ X : ℝ, c₁ * x ≤ X → X ≤ c₂ * x →
        ∀ Y ∈ dyadicScales x K, ∀ l : ℕ, (l : ℝ) ≤ 4 * Y →
          (∑ h ∈ Finset.range (⌊4 * X / Y⌋₊ + 1), (tau (1 + l * h) : ℝ) ^ 2) ≤
            CDiv * (X / Y) * (Real.log x) ^ 3 := by
  obtain ⟨x₀, hx₀, hSmall⟩ := pd1c_dyadic_small_relative_to_X K c₁ hc₁
  let Clog := 2 + |Real.log (17 * c₂)|
  have hClog : 0 < Clog := by dsimp only [Clog]; positivity
  refine ⟨84 * Clog ^ 3, x₀, by positivity, hx₀, ?_⟩
  intro x hx X hXlo hXhi Y hY l hl
  obtain ⟨hL, hX, hYs⟩ := hSmall x hx X hXlo
  obtain ⟨hYpos, hYsmall⟩ := hYs Y hY
  have hXpos : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) (hx₀.trans hx)
  let D := ⌊(17 * X) ^ (3 / 4 : ℝ)⌋₊
  have hZ : 1 ≤ 17 * X := by linarith
  have hPowOne : 1 ≤ (17 * X) ^ (3 / 4 : ℝ) := Real.one_le_rpow hZ (by norm_num)
  have hDOne : 1 ≤ D := (Nat.le_floor_iff (Real.rpow_nonneg (by positivity) _)).mpr (by simpa using hPowOne)
  have hDpos : 0 < (D : ℝ) := by exact_mod_cast (by omega : 0 < D)
  have hDup : (D : ℝ) ≤ 17 * c₂ * x := by
    calc
      _ ≤ (17 * X) ^ (3 / 4 : ℝ) := Nat.floor_le (by positivity)
      _ ≤ 17 * X := by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hZ
          (by norm_num : (3 / 4 : ℝ) ≤ 1)
      _ ≤ 17 * c₂ * x := by nlinarith [hXhi]
  have hlog : Real.log (D : ℝ) ≤ Real.log (17 * c₂) + Real.log x := by
    have h := Real.log_le_log hDpos hDup
    rw [Real.log_mul (by positivity : 17 * c₂ ≠ 0) hxpos.ne'] at h
    exact h
  have hBoundLog : 1 + Real.log (D : ℝ) ≤ Clog * Real.log x := by
    have hmul := mul_le_mul_of_nonneg_left hL
      (show 0 ≤ 1 + |Real.log (17 * c₂)| by positivity)
    dsimp only [Clog]
    nlinarith [le_abs_self (Real.log (17 * c₂))]
  have hlogNonneg : 0 ≤ 1 + Real.log (D : ℝ) := by
    have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hDOne
    have h := Real.log_nonneg hDR
    linarith
  have hCube : (1 + Real.log (D : ℝ)) ^ 3 ≤ Clog ^ 3 * (Real.log x) ^ 3 := by
    have h := pow_le_pow_left₀ hlogNonneg hBoundLog 3
    simpa only [mul_pow] using h
  have hProg := pd1c_tau_sq_progression_bound X Y hX hYpos hYsmall l hl
  calc
    _ ≤ 84 * (X / Y) * (1 + Real.log (D : ℝ)) ^ 3 := hProg
    _ ≤ 84 * (X / Y) * (Clog ^ 3 * (Real.log x) ^ 3) :=
      mul_le_mul_of_nonneg_left hCube (by positivity)
    _ = _ := by ring

end ArtinPrimitiveRoots.TypeII.PD
