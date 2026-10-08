import ArtinPrimitiveRoots.Construction.Defs
import ArtinPrimitiveRoots.Construction.Proofs.c1.SupportHelpers
import ArtinPrimitiveRoots.Construction.Proofs.c2.PartialSummation
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Basic

namespace ArtinPrimitiveRoots.Construction.ProofsC2

open ArtinPrimitiveRoots.Construction
open ArtinPrimitiveRoots.TypeII
open Filter
open MeasureTheory
open scoped Topology

lemma markedPart_eq_self_of_groupInteger (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (r : ℕ) (hr0 : r ≠ 0) (hr : IsGroupInteger x K a r) :
    markedPart x K a r = r := by
  suffices h : ∀ n : ℕ, n ≠ 0 → IsGroupInteger x K a n → markedPart x K a n = n by
    exact h r hr0 hr
  intro n hn hgroup
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases h1 : n = 1
      · subst n
        simp [markedPart]
      · obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd h1
        let m : ℕ := n / p
        have hmul : p * m = n := by
          dsimp [m]
          exact Nat.mul_div_cancel' hpd
        have hm0 : m ≠ 0 := by
          intro hm
          rw [hm, Nat.mul_zero] at hmul
          exact hn hmul.symm
        have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
        have hm_lt : m < n := by
          calc
            m = 1 * m := by simp
            _ < p * m := Nat.mul_lt_mul_of_pos_right hp.one_lt hmpos
            _ = n := hmul
        have hgroupm : IsGroupInteger x K a m := by
          intro q hq hqm
          apply hgroup q hq
          rw [← hmul]
          simpa [Nat.mul_comm] using dvd_mul_of_dvd_right hqm p
        calc
          markedPart x K a n = markedPart x K a (p * m) := by rw [hmul]
          _ = p * markedPart x K a m :=
            markedPart_mul_of_mem (hgroup p hp hpd) hp hm0
          _ = p * m := by rw [ih m hm_lt hm0 hgroupm]
          _ = n := hmul

lemma markedPart_mul_of_no_marked_prime_dvd
    (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (m n : ℕ)
    (hm : m ≠ 0) (hn : n ≠ 0)
    (hfree : ∀ p, p ∈ markedPrimes x K a → p.Prime → ¬ p ∣ m) :
    markedPart x K a (m * n) = markedPart x K a n := by
  unfold markedPart
  apply Finset.prod_congr rfl
  intro p hp
  have hp' : p.Prime := prime_of_mem_markedPrimes hp
  letI : Fact p.Prime := ⟨hp'⟩
  rw [padicValNat.mul hm hn]
  rw [padicValNat.eq_zero_of_not_dvd (hfree p hp hp')]
  simp

lemma no_marked_prime_dvd_c_mul_large_prime
    (x : ℝ) (K c Q : ℕ) (a : Fin K → ℝ)
    (hc24 : c = 2 ∨ c = 4) (hQ : Q.Prime)
    (hxpos : 0 < x) (hL : (4 : ℝ) ^ 10 ≤ Real.log x)
    (ha : ValidBands K a) (hQlarge : Real.rpow x (9 / 10 : ℝ) < (Q : ℝ)) :
    ∀ p, p ∈ markedPrimes x K a → p.Prime → ¬ p ∣ c * Q := by
  intro p hpMem hp hdiv
  have hscale := markedPrime_scale_bounds hxpos hL ha hpMem
  rcases hp.dvd_mul.mp hdiv with hpc | hpQ
  · have hcpos : 0 < c := by rcases hc24 with h | h <;> omega
    have hpcNat : p ≤ c := Nat.le_of_dvd hcpos hpc
    have hpcReal : (p : ℝ) ≤ (c : ℝ) := by exact_mod_cast hpcNat
    have hc4 : c ≤ 4 := by rcases hc24 with h | h <;> omega
    have hc4Real : (c : ℝ) ≤ 4 := by exact_mod_cast hc4
    linarith
  · have hpEqQ : p = Q := (Nat.prime_dvd_prime_iff_eq hp hQ).mp hpQ
    have hpEqQReal : (p : ℝ) = (Q : ℝ) := by exact_mod_cast hpEqQ
    linarith

lemma markedPart_c_r_Q_eq_r
    (x : ℝ) (K c r Q : ℕ) (a : Fin K → ℝ)
    (hc24 : c = 2 ∨ c = 4) (hQ : Q.Prime)
    (hxpos : 0 < x) (hL : (4 : ℝ) ^ 10 ≤ Real.log x)
    (ha : ValidBands K a) (hQlarge : Real.rpow x (9 / 10 : ℝ) < (Q : ℝ))
    (hr0 : r ≠ 0) (hr : IsGroupInteger x K a r) :
    markedPart x K a (c * r * Q) = r := by
  have hcpos : 0 < c := by rcases hc24 with h | h <;> omega
  have hcr0 : c * Q ≠ 0 := Nat.ne_of_gt (Nat.mul_pos hcpos hQ.pos)
  have hfree := no_marked_prime_dvd_c_mul_large_prime x K c Q a hc24 hQ
    hxpos hL ha hQlarge
  calc
    markedPart x K a (c * r * Q) = markedPart x K a ((c * Q) * r) := by
      congr 1
      ring
    _ = markedPart x K a r :=
      markedPart_mul_of_no_marked_prime_dvd x K a (c * Q) r hcr0 hr0 hfree
    _ = r := markedPart_eq_self_of_groupInteger x K a r hr0 hr

lemma markedPrime_dvd_c_r_Q_iff
    (x : ℝ) (K c r Q p : ℕ) (a : Fin K → ℝ)
    (hc24 : c = 2 ∨ c = 4) (hQ : Q.Prime)
    (hxpos : 0 < x) (hL : (4 : ℝ) ^ 10 ≤ Real.log x)
    (ha : ValidBands K a) (hQlarge : Real.rpow x (9 / 10 : ℝ) < (Q : ℝ))
    (hpMem : p ∈ markedPrimes x K a) (hp : p.Prime) :
    (p ∣ c * r * Q ↔ p ∣ r) := by
  have hfree := no_marked_prime_dvd_c_mul_large_prime x K c Q a hc24 hQ
    hxpos hL ha hQlarge p hpMem hp
  constructor
  · intro hdiv
    have hdiv' : p ∣ (c * Q) * r := by
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hdiv
    rcases hp.dvd_mul.mp hdiv' with hbad | hgood
    · exact (hfree hbad).elim
    · exact hgood
  · intro hdiv
    have hmul := dvd_mul_of_dvd_left hdiv (c * Q)
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul

lemma exists_logPower_exp_small
    (C ε δ η : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hη : 0 < η) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      C * (Real.log x * Real.exp (-ε * Real.rpow (Real.log x) δ)) ≤ η := by
  let T : ℝ → ℝ := fun x => Real.rpow (Real.log x) δ
  have hT : Tendsto T atTop atTop := by
    exact (tendsto_rpow_atTop hδ).comp Real.tendsto_log_atTop
  have hlim : Tendsto (fun x : ℝ => Real.rpow x (1 / δ) * Real.exp (-ε * x))
      atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / δ) ε hε
  have hlim' : Tendsto (fun x : ℝ =>
      Real.rpow (T x) (1 / δ) * Real.exp (-ε * T x)) atTop (𝓝 0) := hlim.comp hT
  have hpow (x : ℝ) (hx : 0 < Real.log x) :
      Real.rpow (T x) (1 / δ) = Real.log x := by
    dsimp [T]
    rw [← Real.rpow_mul hx.le δ (1 / δ)]
    have hmul : δ * (1 / δ) = 1 := by field_simp [ne_of_gt hδ]
    rw [hmul, Real.rpow_one]
  have hEq : (fun x : ℝ => Real.rpow (T x) (1 / δ) * Real.exp (-ε * T x)) =ᶠ[atTop]
      (fun x : ℝ => Real.log x * Real.exp (-ε * Real.rpow (Real.log x) δ)) := by
    filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 0] with x hx
    rw [hpow x hx]
  have hlimLog : Tendsto (fun x : ℝ =>
      Real.log x * Real.exp (-ε * Real.rpow (Real.log x) δ)) atTop (𝓝 0) :=
    hlim'.congr' hEq
  have hlimScaled : Tendsto (fun x : ℝ => C *
      (Real.log x * Real.exp (-ε * Real.rpow (Real.log x) δ))) atTop (𝓝 0) :=
    by simpa using hlimLog.const_mul C
  have hev : ∀ᶠ x : ℝ in atTop,
      C * (Real.log x * Real.exp (-ε * Real.rpow (Real.log x) δ)) ∈ Set.Iio η :=
    hlimScaled.eventually (Iio_mem_nhds hη)
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨x₀, ?_⟩
  intro x hx
  exact (hx₀ x hx).le

lemma conWeight_c_r_Q_plus_one
    (x : ℝ) (M c : ℕ) (u : ℤ) (K : ℕ) (a : Fin K → ℝ)
    (Ψ : ℝ → ℝ) (r Q : ℕ)
    (hc24 : c = 2 ∨ c = 4) (hQ : Q.Prime)
    (hxpos : 0 < x) (hL : (4 : ℝ) ^ 10 ≤ Real.log x)
    (ha : ValidBands K a) (hQlarge : Real.rpow x (9 / 10 : ℝ) < (Q : ℝ))
    (hrpos : 0 < r) (hr : IsGroupInteger x K a r)
    (hprog : (((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M])) :
    conWeight x M c u K a Ψ (c * r * Q + 1) =
      Ψ (((c * r * Q + 1 : ℕ) : ℝ) / x) * markedWeight x K a (1 / 2 : ℝ) r := by
  let d : ℕ := c * r * Q + 1
  have hcpos : 0 < c := by rcases hc24 with h | h <;> omega
  have hQpos : 0 < Q := hQ.pos
  have hd1 : 1 < d := by
    dsimp [d]
    have hprod : 0 < c * r * Q := Nat.mul_pos (Nat.mul_pos hcpos hrpos) hQpos
    omega
  have hsub : d - 1 = c * r * Q := by
    dsimp [d]
  have hpart := markedPart_c_r_Q_eq_r x K c r Q a hc24 hQ hxpos hL ha hQlarge
    (Nat.ne_of_gt hrpos) hr
  have hpart' : markedPart x K a (d - 1) = r := by
    rw [hsub]
    exact hpart
  have hdiv : ∀ p, p ∈ markedPrimes x K a → p.Prime →
      (p ∣ d - 1 ↔ p ∣ r) := by
    intro p hpMem hp
    rw [hsub]
    exact markedPrime_dvd_c_r_Q_iff x K c r Q p a hc24 hQ hxpos hL ha
      hQlarge hpMem hp
  have hweight : markedWeight x K a (1 / 2 : ℝ) (d - 1) =
      markedWeight x K a (1 / 2 : ℝ) r := markedWeight_eq_of_prime_dvd_iff hdiv
  have hfactor : conFactor x c K a (d - 1) = 1 := by
    have hex : ∃ q : ℕ, q.Prime ∧ Real.rpow x (9 / 10 : ℝ) < (q : ℝ) ∧
        d - 1 = c * markedPart x K a (d - 1) * q :=
      ⟨Q, hQ, hQlarge, by rw [hpart']; exact hsub⟩
    unfold conFactor
    rw [if_pos hex]
  have hcond : 1 < d ∧ (d : ℤ) ≡ u [ZMOD M] := by
    constructor
    · exact hd1
    · simpa [d] using hprog
  unfold conWeight
  rw [if_pos hcond, hfactor, hweight]
  simp

end ArtinPrimitiveRoots.Construction.ProofsC2

namespace ArtinPrimitiveRoots.Proofs.C_BV

open ArtinPrimitiveRoots.Construction
open ArtinPrimitiveRoots.Construction.ProofsC2
open ArtinPrimitiveRoots.TypeII
open MeasureTheory
open Filter
open scoped Topology

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

lemma conTotalMass_eq_groupProgressionSum
    (x : ℝ) (M c : ℕ) (u : ℤ) (K : ℕ) (a : Fin K → ℝ)
    (Ψ : ℝ → ℝ) (hc24 : c = 2 ∨ c = 4)
    (hx2 : 2 ≤ x) (hxpos : 0 < x) (hL : (4 : ℝ) ^ 10 ≤ Real.log x)
    (ha : ValidBands K a) (hΨsupp : Function.support Ψ ⊆ Set.Ioo 1 2)
    (hSupport : ∀ d, conWeight x M c u K a Ψ d ≠ 0 →
      x < (d : ℝ) ∧ (d : ℝ) < 2 * x ∧
        ∃ r Q : ℕ, d - 1 = c * r * Q ∧ Q.Prime ∧
          Real.rpow x (9 / 10 : ℝ) < (Q : ℝ) ∧
          IsGroupInteger x K a r ∧
          (r : ℝ) ≤ Real.rpow x (11 / 100 : ℝ) ∧
          markedWeight x K a (1 / 2 : ℝ) (d - 1) =
            markedWeight x K a (1 / 2 : ℝ) r) :
    conTotalMass x M c u K a Ψ =
      ∑ r ∈ (Finset.range (⌊2 * x⌋₊ + 1)).filter
          (fun r => IsGroupInteger x K a r),
        markedWeight x K a (1 / 2 : ℝ) r * progressionPrimeSum x M c u Ψ r 1 := by
  classical
  let S : Finset ℕ := Finset.range (⌊2 * x⌋₊ + 1)
  let R : Finset ℕ := S.filter (fun r => IsGroupInteger x K a r)
  let pairWeight : ℕ × ℕ → ℝ := fun z =>
    Ψ (((c * z.1 * z.2 + 1 : ℕ) : ℝ) / x) *
      markedWeight x K a (1 / 2 : ℝ) z.1
  let pairGood : ℕ × ℕ → Prop := fun z =>
    z.2.Prime ∧ Real.rpow x (9 / 10 : ℝ) < (z.2 : ℝ) ∧
      (((c * z.1 * z.2 + 1 : ℕ) : ℤ) ≡ u [ZMOD M]) ∧
      (1 : ℕ) ∣ c * z.1 * z.2 + 1
  let Pbase : Finset (ℕ × ℕ) := R.product S
  let Pgood : Finset (ℕ × ℕ) := Pbase.filter pairGood
  let P : Finset (ℕ × ℕ) := Pgood.filter (fun z => pairWeight z ≠ 0)
  let D : Finset ℕ := S.filter (fun d => conWeight x M c u K a Ψ d ≠ 0)
  have hcpos : 0 < c := by rcases hc24 with h | h <;> omega
  have hMarks : ∀ p, p ∈ markedPrimes x K a → (2 : ℝ) < (p : ℝ) := by
    intro p hp
    have hscale := markedPrime_scale_bounds hxpos hL ha hp
    linarith
  have hpairWitness (d : {d // d ∈ D}) :
      ∃ z : ℕ × ℕ, z ∈ P ∧ d.1 = c * z.1 * z.2 + 1 ∧
        markedPart x K a (c * z.1 * z.2) = z.1 ∧
        conWeight x M c u K a Ψ d.1 = pairWeight z := by
    have hdNZ : conWeight x M c u K a Ψ d.1 ≠ 0 :=
      (Finset.mem_filter.mp d.2).2
    have hdS : d.1 ∈ S := (Finset.mem_filter.mp d.2).1
    rcases hSupport d.1 hdNZ with ⟨hdlo, hdhi, r, Q, hfac, hQ, hQlarge,
      hrGroup, hrBound, hweightEq⟩
    have hcond : 1 < d.1 ∧ (d.1 : ℤ) ≡ u [ZMOD M] := by
      by_cases h : 1 < d.1 ∧ (d.1 : ℤ) ≡ u [ZMOD M]
      · exact h
      · simp [conWeight, h] at hdNZ
    have hrpos : 0 < r :=
      groupInteger_pos_of_marks_gt_two x K r a hMarks hrGroup
    have hQpos : 0 < Q := hQ.pos
    have hdeq : d.1 = c * r * Q + 1 := by
      calc
        d.1 = (d.1 - 1) + 1 := (Nat.sub_add_cancel (by omega : 1 ≤ d.1)).symm
        _ = c * r * Q + 1 := by rw [hfac]
    have hprog : (((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M]) := by
      simpa [hdeq] using hcond.2
    have hterm : conWeight x M c u K a Ψ d.1 = pairWeight (r, Q) := by
      rw [hdeq]
      simpa [pairWeight] using
        (conWeight_c_r_Q_plus_one x M c u K a Ψ r Q hc24 hQ hxpos hL ha
          hQlarge hrpos hrGroup hprog)
    have hpart := markedPart_c_r_Q_eq_r x K c r Q a hc24 hQ hxpos hL ha
      hQlarge (Nat.ne_of_gt hrpos) hrGroup
    have hrleProd : r ≤ c * r * Q := by
      have hcr : r ≤ c * r := by
        simpa only [Nat.one_mul] using Nat.mul_le_mul_right r (Nat.one_le_of_lt hcpos)
      have hcrQ : c * r ≤ c * r * Q := by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left (c * r)
          (Nat.one_le_of_lt hQpos)
      exact hcr.trans hcrQ
    have hQleProd : Q ≤ c * r * Q := by
      have hcrpos : 0 < c * r := Nat.mul_pos hcpos hrpos
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right Q
        (Nat.one_le_of_lt hcrpos)
    have hrleD : r ≤ d.1 := by
      have hrleSub : r ≤ d.1 - 1 := by rw [hfac]; exact hrleProd
      exact le_trans hrleSub (Nat.sub_le _ _)
    have hQleD : Q ≤ d.1 := by
      have hQleSub : Q ≤ d.1 - 1 := by rw [hfac]; exact hQleProd
      exact le_trans hQleSub (Nat.sub_le _ _)
    have hrFloor : r ≤ ⌊2 * x⌋₊ := by
      apply Nat.le_floor
      exact (Nat.cast_le.mpr hrleD).trans hdhi.le
    have hQFloor : Q ≤ ⌊2 * x⌋₊ := by
      apply Nat.le_floor
      exact (Nat.cast_le.mpr hQleD).trans hdhi.le
    have hrMem : r ∈ R := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hrFloor), hrGroup⟩
    have hQMem : Q ∈ S := Finset.mem_range.mpr (Nat.lt_succ_of_le hQFloor)
    have hgood : pairGood (r, Q) := by
      exact ⟨hQ, hQlarge, hprog, Nat.one_dvd _⟩
    have htermNZ : pairWeight (r, Q) ≠ 0 := by
      rw [← hterm]
      exact hdNZ
    refine ⟨(r, Q), ?_, hdeq, hpart, hterm⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hrMem, hQMem⟩, hgood⟩, htermNZ⟩
  let pairOf : {d // d ∈ D} → ℕ × ℕ := fun d => Classical.choose (hpairWitness d)
  have hpairSpec (d : {d // d ∈ D}) := Classical.choose_spec (hpairWitness d)
  have hMassFilter : conTotalMass x M c u K a Ψ =
      ∑ d ∈ D, conWeight x M c u K a Ψ d := by
    unfold conTotalMass
    dsimp [D, S]
    symm
    apply Finset.sum_subset
      (Finset.filter_subset (fun d => conWeight x M c u K a Ψ d ≠ 0)
        (Finset.range (⌊2 * x⌋₊ + 1)))
    intro d hd hnot
    have hzero : conWeight x M c u K a Ψ d = 0 := by
      by_contra hne
      exact hnot (Finset.mem_filter.mpr ⟨hd, hne⟩)
    simp [hzero]
  have hBijection : (∑ d ∈ D, conWeight x M c u K a Ψ d) =
      ∑ z ∈ P, pairWeight z := by
    calc
      _ = ∑ d ∈ D.attach, conWeight x M c u K a Ψ d.1 := by
        simpa using (Finset.sum_attach D (conWeight x M c u K a Ψ)).symm
      _ = ∑ z ∈ P, pairWeight z := by
        apply Finset.sum_bij (fun d _ => pairOf d)
        · intro d hd
          exact (hpairSpec d).1
        · intro d hd d' hd' heq
          apply Subtype.ext
          calc
            d.1 = c * (pairOf d).1 * (pairOf d).2 + 1 := (hpairSpec d).2.1
            _ = c * (pairOf d').1 * (pairOf d').2 + 1 := by rw [heq]
            _ = d'.1 := ((hpairSpec d').2.1).symm
        · intro z hz
          rcases Finset.mem_filter.mp hz with ⟨hzGood, hzNZ⟩
          rcases Finset.mem_filter.mp hzGood with ⟨hzBase, hzPred⟩
          rcases Finset.mem_product.mp hzBase with ⟨hrMem, hQMem⟩
          have hrGroup : IsGroupInteger x K a z.1 :=
            (Finset.mem_filter.mp hrMem).2
          rcases hzPred with ⟨hQ, hQlarge, hprog, hOne⟩
          have hrpos : 0 < z.1 :=
            groupInteger_pos_of_marks_gt_two x K z.1 a hMarks hrGroup
          have hΨnz : Ψ (↑(c * z.1 * z.2 + 1 : ℕ) / x) ≠ 0 := by
            intro hzΨ
            apply hzNZ
            change Ψ (↑(c * z.1 * z.2 + 1 : ℕ) / x) *
              markedWeight x K a (1 / 2 : ℝ) z.1 = 0
            rw [hzΨ, zero_mul]
          have hargSupport :
              (↑(c * z.1 * z.2 + 1 : ℕ) : ℝ) / x ∈ Function.support Ψ := by
            simpa [Function.support] using hΨnz
          have harg := hΨsupp hargSupport
          have hdlo : x < (↑(c * z.1 * z.2 + 1 : ℕ) : ℝ) := by
            have hmul := (lt_div_iff₀ hxpos).mp harg.1
            simpa using hmul
          have hdhi : (↑(c * z.1 * z.2 + 1 : ℕ) : ℝ) < 2 * x := by
            apply (div_lt_iff₀ hxpos).mp
            exact harg.2
          let d : ℕ := c * z.1 * z.2 + 1
          have hd1 : 1 < d := by
            dsimp [d]
            have hprod : 0 < c * z.1 * z.2 := Nat.mul_pos
              (Nat.mul_pos hcpos hrpos) hQ.pos
            omega
          have hdFloor : d ≤ ⌊2 * x⌋₊ := by
            apply Nat.le_floor
            dsimp [d]
            exact hdhi.le
          have hdMemS : d ∈ S := by
            dsimp [S]
            exact Finset.mem_range.mpr (Nat.lt_succ_of_le hdFloor)
          have hweight := conWeight_c_r_Q_plus_one x M c u K a Ψ z.1 z.2
            hc24 hQ hxpos hL ha hQlarge hrpos hrGroup (by simpa [d] using hprog)
          have hdNZ : conWeight x M c u K a Ψ d ≠ 0 := by
            rw [hweight]
            exact hzNZ
          have hdMemD : d ∈ D := by
            exact Finset.mem_filter.mpr ⟨hdMemS, hdNZ⟩
          refine ⟨⟨d, hdMemD⟩, Finset.mem_attach D ⟨d, hdMemD⟩, ?_⟩
          apply Prod.ext
          · have hpart := markedPart_c_r_Q_eq_r x K c z.1 z.2 a hc24 hQ
              hxpos hL ha hQlarge (Nat.ne_of_gt hrpos) hrGroup
            have hspec := hpairSpec ⟨d, hdMemD⟩
            have hprodEq : c * (pairOf ⟨d, hdMemD⟩).1 * (pairOf ⟨d, hdMemD⟩).2 =
                c * z.1 * z.2 := by
              have heq : c * (pairOf ⟨d, hdMemD⟩).1 * (pairOf ⟨d, hdMemD⟩).2 + 1 =
                  c * z.1 * z.2 + 1 := by
                calc
                  _ = d := (hspec.2.1).symm
                  _ = _ := by dsimp [d]
              exact Nat.add_right_cancel heq
            have hmarkChosen := hspec.2.2.1
            have hmarkTarget : markedPart x K a (c * z.1 * z.2) = z.1 := hpart
            have hmarkEq := congrArg (markedPart x K a) hprodEq
            rw [hmarkChosen, hmarkTarget] at hmarkEq
            exact hmarkEq
          · have hspec := hpairSpec ⟨d, hdMemD⟩
            have hrEq : (pairOf ⟨d, hdMemD⟩).1 = z.1 := by
              have hpart := markedPart_c_r_Q_eq_r x K c z.1 z.2 a hc24 hQ
                hxpos hL ha hQlarge (Nat.ne_of_gt hrpos) hrGroup
              have hmarkChosen := hspec.2.2.1
              have hprodEq : c * (pairOf ⟨d, hdMemD⟩).1 * (pairOf ⟨d, hdMemD⟩).2 =
                  c * z.1 * z.2 := by
                have heq : c * (pairOf ⟨d, hdMemD⟩).1 * (pairOf ⟨d, hdMemD⟩).2 + 1 =
                    c * z.1 * z.2 + 1 := by
                  calc
                    _ = d := (hspec.2.1).symm
                    _ = _ := by dsimp [d]
                exact Nat.add_right_cancel heq
              have hmarkEq := congrArg (markedPart x K a) hprodEq
              rw [hmarkChosen, hpart] at hmarkEq
              exact hmarkEq
            have hcoef : 0 < c * z.1 := Nat.mul_pos hcpos hrpos
            have hprodEq : c * (pairOf ⟨d, hdMemD⟩).1 * (pairOf ⟨d, hdMemD⟩).2 =
                c * z.1 * z.2 := by
              have heq : c * (pairOf ⟨d, hdMemD⟩).1 * (pairOf ⟨d, hdMemD⟩).2 + 1 =
                  c * z.1 * z.2 + 1 := by
                calc
                  _ = d := (hspec.2.1).symm
                  _ = _ := by dsimp [d]
              exact Nat.add_right_cancel heq
            have hQEq : (pairOf ⟨d, hdMemD⟩).2 = z.2 := by
              apply Nat.mul_left_cancel hcoef
              simpa [hrEq, Nat.mul_assoc] using hprodEq
            exact hQEq
        · intro d hd
          exact (hpairSpec d).2.2.2
  have hMassPairs : conTotalMass x M c u K a Ψ = ∑ z ∈ P, pairWeight z :=
    hMassFilter.trans hBijection
  have hProgressionPairs :
      (∑ r ∈ R, markedWeight x K a (1 / 2 : ℝ) r *
          progressionPrimeSum x M c u Ψ r 1) = ∑ z ∈ P, pairWeight z := by
    let qset : ℕ → Finset ℕ := fun r => S.filter (fun Q : ℕ =>
      Q.Prime ∧ Real.rpow x (9 / 10 : ℝ) < (Q : ℝ) ∧
        (((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M]) ∧
        (1 : ℕ) ∣ c * r * Q + 1)
    have hprog (r : ℕ) : progressionPrimeSum x M c u Ψ r 1 =
        ∑ Q ∈ qset r,
          Ψ (((c * r * Q + 1 : ℕ) : ℝ) / x) := by
      unfold progressionPrimeSum
      rfl
    calc
      _ = ∑ r ∈ R, ∑ Q ∈ qset r,
          pairWeight (r, Q) := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [hprog r, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro Q hQ
        dsimp [pairWeight]
        ring
      _ = ∑ z ∈ Pgood, pairWeight z := by
        calc
          _ = ∑ r ∈ R, ∑ Q ∈ S,
                if pairGood (r, Q) then pairWeight (r, Q) else 0 := by
            apply Finset.sum_congr rfl
            intro r hr
            dsimp [qset]
            rw [Finset.sum_filter]
            rfl
          _ = ∑ z ∈ Pgood, pairWeight z := by
            simp [Pgood, Pbase, R, S, pairGood, pairWeight,
              Finset.sum_product, Finset.sum_filter]
      _ = ∑ z ∈ P, pairWeight z := by
        dsimp [P]
        symm
        have hsub : Pgood.filter (fun z => pairWeight z ≠ 0) ⊆ Pgood :=
          Finset.filter_subset (fun z => pairWeight z ≠ 0) Pgood
        apply Finset.sum_subset hsub
        intro z hz hnot
        have hzero : pairWeight z = 0 := by
          by_contra hne
          exact hnot (Finset.mem_filter.mpr ⟨hz, hne⟩)
        simp [hzero]
  exact hMassPairs.trans hProgressionPairs.symm

lemma smoothedMainTerm_integral_bounds
    (x : ℝ) (c r : ℕ) (Ψ : ℝ → ℝ)
    (hc24 : c = 2 ∨ c = 4)
    (hx2 : 2 ≤ x) (hcr : 0 < ((c * r : ℕ) : ℝ))
    (hcut : Real.rpow x (9 / 10 : ℝ) ≤ (x - 1) / ((c * r : ℕ) : ℝ))
    (hΨsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ)
    (hΨnonneg : ∀ y, 0 ≤ Ψ y)
    (hΨint : 0 < ∫ y in (1 : ℝ)..2, Ψ y) :
    (x / ((c * r : ℕ) : ℝ)) *
        ((∫ y in (1 : ℝ)..2, Ψ y) / Real.log x) ≤
      smoothedMainTerm x c r Ψ ∧
      smoothedMainTerm x c r Ψ ≤
        (x / ((c * r : ℕ) : ℝ)) *
          (2 * (∫ y in (1 : ℝ)..2, Ψ y) / Real.log x) := by
  have hxpos : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  let cr : ℝ := ((c * r : ℕ) : ℝ)
  let q : ℝ → ℝ := fun y => (x * y - 1) / cr
  have hcrpos : 0 < cr := by simpa [cr] using hcr
  have hcrcont : Continuous q := by
    dsimp [q]
    fun_prop
  have hqLower (y : ℝ) (hy : y ∈ Set.Icc (1 : ℝ) 2) :
      Real.rpow x (9 / 10 : ℝ) ≤ q y := by
    have hy1 : 1 ≤ y := hy.1
    have hxy : x - 1 ≤ x * y - 1 := by
      have := mul_le_mul_of_nonneg_left hy1 hxpos.le
      linarith
    have hdiv := div_le_div_of_nonneg_right hxy hcrpos.le
    exact le_trans (by simpa [q, cr] using hcut) (by simpa [q, cr] using hdiv)
  have hqUpper (y : ℝ) (hy : y ∈ Set.Icc (1 : ℝ) 2) : q y ≤ x := by
    have hy2 : y ≤ 2 := hy.2
    have hxy : x * y ≤ 2 * x := by
      calc
        x * y ≤ x * 2 := mul_le_mul_of_nonneg_left hy2 hxpos.le
        _ = 2 * x := by ring
    have hcr2 : 2 ≤ cr := by
      have hc2 : 2 ≤ c := by rcases hc24 with h | h <;> omega
      have hr1 : 1 ≤ r := by
        by_contra hr
        have hr0 : r = 0 := by omega
        subst r
        norm_num at hcr
      have hcCast : (2 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc2
      have hrCast : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
      dsimp [cr]
      rw [Nat.cast_mul]
      nlinarith [mul_le_mul_of_nonneg_right hcCast (show 0 ≤ (r : ℝ) by positivity)]
    have hmul : 2 * x ≤ cr * x := by nlinarith [hcr2, hxpos]
    apply (div_le_iff₀ hcrpos).2
    change x * y - 1 ≤ x * cr
    nlinarith
  have hlogLower (y : ℝ) (hy : y ∈ Set.Icc (1 : ℝ) 2) :
      (9 / 10 : ℝ) * Real.log x ≤ Real.log (q y) := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hxpos _) (hqLower y hy)
    rw [Real.log_rpow hxpos] at h
    exact h
  have hlogUpper (y : ℝ) (hy : y ∈ Set.Icc (1 : ℝ) 2) :
      Real.log (q y) ≤ Real.log x :=
    Real.log_le_log (lt_of_lt_of_le (Real.rpow_pos_of_pos hxpos _) (hqLower y hy))
      (hqUpper y hy)
  have hlogqpos (y : ℝ) (hy : y ∈ Set.Icc (1 : ℝ) 2) : 0 < Real.log (q y) := by
    have h := hlogLower y hy
    nlinarith
  have hΨcont : Continuous Ψ := hΨsmooth.continuous
  have hlogcont : ContinuousOn (fun y => Real.log (q y)) (Set.Icc (1 : ℝ) 2) := by
    apply Real.continuousOn_log.comp' hcrcont.continuousOn
    intro y hy
    change q y ≠ 0
    exact ne_of_gt (lt_of_lt_of_le (Real.rpow_pos_of_pos hxpos _) (hqLower y hy))
  have hquotCont : ContinuousOn (fun y => Ψ y / Real.log (q y))
      (Set.Icc (1 : ℝ) 2) := by
    apply hΨcont.continuousOn.div hlogcont
    intro y hy
    exact ne_of_gt (hlogqpos y hy)
  have hquotInt : IntervalIntegrable (fun y => Ψ y / Real.log (q y))
      volume 1 2 :=
    ContinuousOn.intervalIntegrable_of_Icc (by norm_num) hquotCont
  have hΨoverLCont : ContinuousOn (fun y => Ψ y / Real.log x)
      (Set.Icc (1 : ℝ) 2) := by
    exact hΨcont.continuousOn.div continuousOn_const (fun _ _ => hlogx.ne')
  have hΨoverLInt : IntervalIntegrable (fun y => Ψ y / Real.log x)
      volume 1 2 :=
    ContinuousOn.intervalIntegrable_of_Icc (by norm_num) hΨoverLCont
  have hTwoΨoverLCont : ContinuousOn (fun y => 2 * Ψ y / Real.log x)
      (Set.Icc (1 : ℝ) 2) := by
    exact (continuousOn_const.mul hΨcont.continuousOn).div continuousOn_const
      (fun _ _ => hlogx.ne')
  have hTwoΨoverLInt : IntervalIntegrable (fun y => 2 * Ψ y / Real.log x)
      volume 1 2 :=
    ContinuousOn.intervalIntegrable_of_Icc (by norm_num) hTwoΨoverLCont
  have hLowerInt : (∫ y in (1 : ℝ)..2, Ψ y / Real.log x) ≤
      ∫ y in (1 : ℝ)..2, Ψ y / Real.log (q y) := by
    apply intervalIntegral.integral_mono_on (by norm_num) hΨoverLInt hquotInt
    intro y hy
    have hden := hlogUpper y hy
    rw [div_le_div_iff₀ hlogx (hlogqpos y hy)]
    exact mul_le_mul_of_nonneg_left hden (hΨnonneg y)
  have hUpperInt : (∫ y in (1 : ℝ)..2, Ψ y / Real.log (q y)) ≤
      ∫ y in (1 : ℝ)..2, 2 * Ψ y / Real.log x := by
    apply intervalIntegral.integral_mono_on (by norm_num) hquotInt hTwoΨoverLInt
    intro y hy
    have hden := hlogLower y hy
    have hLle : Real.log x ≤ 2 * Real.log (q y) := by nlinarith [hden]
    rw [div_le_div_iff₀ (hlogqpos y hy) hlogx]
    have hmul := mul_le_mul_of_nonneg_left hLle (hΨnonneg y)
    nlinarith
  have hLowerConst : (∫ y in (1 : ℝ)..2, Ψ y / Real.log x) =
      (∫ y in (1 : ℝ)..2, Ψ y) / Real.log x := by
    rw [show (fun y => Ψ y / Real.log x) =
        fun y => (Real.log x)⁻¹ * Ψ y by
          funext y
          simp [div_eq_mul_inv, mul_comm]]
    rw [intervalIntegral.integral_const_mul]
    ring
  have hUpperConst : (∫ y in (1 : ℝ)..2, 2 * Ψ y / Real.log x) =
      2 * (∫ y in (1 : ℝ)..2, Ψ y) / Real.log x := by
    rw [show (fun y => 2 * Ψ y / Real.log x) =
        fun y => (2 / Real.log x) * Ψ y by
          funext y
          ring]
    rw [intervalIntegral.integral_const_mul]
    ring
  have hpref : 0 ≤ x / cr := div_nonneg hxpos.le hcrpos.le
  constructor
  · calc
      (x / cr) * ((∫ y in (1 : ℝ)..2, Ψ y) / Real.log x) ≤
          (x / cr) * (∫ y in (1 : ℝ)..2, Ψ y / Real.log (q y)) :=
        mul_le_mul_of_nonneg_left (by rw [← hLowerConst]; exact hLowerInt) hpref
      _ = smoothedMainTerm x c r Ψ := by
        simp [smoothedMainTerm, cr, q]
  · calc
      smoothedMainTerm x c r Ψ =
          (x / cr) * (∫ y in (1 : ℝ)..2, Ψ y / Real.log (q y)) := by
            simp [smoothedMainTerm, cr, q]
      _ ≤ (x / cr) * (∫ y in (1 : ℝ)..2, 2 * Ψ y / Real.log x) :=
        mul_le_mul_of_nonneg_left hUpperInt hpref
      _ = (x / cr) * (2 * (∫ y in (1 : ℝ)..2, Ψ y) / Real.log x) := by
        rw [hUpperConst]

lemma smoothedMainTerm_totient_bounds
    (x : ℝ) (M c r : ℕ) (Ψ : ℝ → ℝ)
    (hM : 0 < M) (hc24 : c = 2 ∨ c = 4) (hcM : c ∣ M)
    (hx2 : 2 ≤ x) (hr : 0 < r)
    (hcut : Real.rpow x (9 / 10 : ℝ) ≤ (x - 1) / ((c * r : ℕ) : ℝ))
    (hΨsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ)
    (hΨnonneg : ∀ y, 0 ≤ Ψ y)
    (hΨint : 0 < ∫ y in (1 : ℝ)..2, Ψ y) :
    (∫ y in (1 : ℝ)..2, Ψ y) / (8 * (M : ℝ)) *
        (x / ((r : ℝ) * Real.log x)) ≤
          smoothedMainTerm x c r Ψ / (Nat.totient (M / c) : ℝ) ∧
      smoothedMainTerm x c r Ψ / (Nat.totient (M / c) : ℝ) ≤
        2 * (∫ y in (1 : ℝ)..2, Ψ y) *
          (x / ((r : ℝ) * Real.log x)) := by
  have hcpos : 0 < c := by rcases hc24 with h | h <;> omega
  have hcrpos : 0 < ((c * r : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hcpos hr
  have hbasic := smoothedMainTerm_integral_bounds x c r Ψ hc24 hx2 hcrpos hcut
    hΨsmooth hΨnonneg hΨint
  have hNpos : 0 < M / c := Nat.div_pos (Nat.le_of_dvd hM hcM) hcpos
  have hφposNat : 0 < Nat.totient (M / c) := Nat.totient_pos.mpr hNpos
  have hφpos : 0 < (Nat.totient (M / c) : ℝ) := by exact_mod_cast hφposNat
  have hφone : 1 ≤ (Nat.totient (M / c) : ℝ) := by exact_mod_cast hφposNat
  have hMreal : 0 < (M : ℝ) := by exact_mod_cast hM
  have hφleM : (Nat.totient (M / c) : ℝ) ≤ (M : ℝ) := by
    have hφle : Nat.totient (M / c) ≤ M := (Nat.totient_le (M / c)).trans
      (Nat.div_le_self M c)
    exact_mod_cast hφle
  have hxpos : 0 < x := by linarith
  have hLpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hrreal : 0 < (r : ℝ) := by exact_mod_cast hr
  have hIpos : 0 < ∫ y in (1 : ℝ)..2, Ψ y := hΨint
  have hIxn : 0 < (∫ y in (1 : ℝ)..2, Ψ y) * x := mul_pos hIpos hxpos
  have hcrCast : ((c * r : ℕ) : ℝ) = (c : ℝ) * (r : ℝ) := by simp
  have hcLower : (2 : ℝ) ≤ (c : ℝ) := by
    rcases hc24 with h | h <;> norm_num [h]
  have hcUpper : (c : ℝ) ≤ 4 := by
    rcases hc24 with h | h <;> norm_num [h]
  have hdenRpos : 0 < (4 : ℝ) * (r : ℝ) := by positivity
  have hdenCrPos : 0 < ((c * r : ℕ) : ℝ) := hcrpos
  have hcrLe4r : ((c * r : ℕ) : ℝ) ≤ 4 * (r : ℝ) := by
    rw [hcrCast]
    exact mul_le_mul_of_nonneg_right hcUpper (Nat.cast_nonneg _)
  have hfactorLower : x / (4 * (r : ℝ)) ≤ x / ((c * r : ℕ) : ℝ) := by
    rw [div_le_div_iff₀ hdenRpos hdenCrPos]
    exact mul_le_mul_of_nonneg_left hcrLe4r hxpos.le
  have hILogPos : 0 ≤ (∫ y in (1 : ℝ)..2, Ψ y) / Real.log x :=
    div_nonneg hΨint.le hLpos.le
  have hrawLower :
      (∫ y in (1 : ℝ)..2, Ψ y) * x /
        (8 * (r : ℝ) * Real.log x) ≤ smoothedMainTerm x c r Ψ := by
    have hfac := mul_le_mul_of_nonneg_right hfactorLower hILogPos
    have hfacEq : (x / (4 * (r : ℝ))) *
        ((∫ y in (1 : ℝ)..2, Ψ y) / Real.log x) =
          (∫ y in (1 : ℝ)..2, Ψ y) * x /
            (4 * (r : ℝ) * Real.log x) := by
      field_simp [ne_of_gt hrreal, ne_of_gt hLpos]
    have hHalf : (∫ y in (1 : ℝ)..2, Ψ y) * x /
        (8 * (r : ℝ) * Real.log x) ≤
      (∫ y in (1 : ℝ)..2, Ψ y) * x /
            (4 * (r : ℝ) * Real.log x) := by
      apply div_le_div_of_nonneg_left hIxn.le (by positivity)
      nlinarith [hrreal, hLpos]
    calc
      _ ≤ (x / (4 * (r : ℝ))) *
          ((∫ y in (1 : ℝ)..2, Ψ y) / Real.log x) := by rw [hfacEq]; exact hHalf
      _ ≤ (x / ((c * r : ℕ) : ℝ)) *
          ((∫ y in (1 : ℝ)..2, Ψ y) / Real.log x) := hfac
      _ ≤ smoothedMainTerm x c r Ψ := hbasic.1
  have htargetLowerEq :
      (∫ y in (1 : ℝ)..2, Ψ y) / (8 * (M : ℝ)) *
        (x / ((r : ℝ) * Real.log x)) =
          ((∫ y in (1 : ℝ)..2, Ψ y) * x) /
            (8 * (M : ℝ) * (r : ℝ) * Real.log x) := by
    field_simp [ne_of_gt hMreal, ne_of_gt hrreal, ne_of_gt hLpos]
  have hrawDivEq :
      ((∫ y in (1 : ℝ)..2, Ψ y) * x /
        (8 * (r : ℝ) * Real.log x)) / (Nat.totient (M / c) : ℝ) =
          ((∫ y in (1 : ℝ)..2, Ψ y) * x) /
            (8 * (r : ℝ) * Real.log x * (Nat.totient (M / c) : ℝ)) := by
    field_simp [ne_of_gt hrreal, ne_of_gt hLpos, hφpos.ne']
  have hdenCmp : 8 * (r : ℝ) * Real.log x * (Nat.totient (M / c) : ℝ) ≤
      8 * (r : ℝ) * Real.log x * (M : ℝ) := by
    exact mul_le_mul_of_nonneg_left hφleM (by positivity)
  have hdenLeftPos : 0 < 8 * (r : ℝ) * Real.log x *
      (Nat.totient (M / c) : ℝ) := by positivity
  have htargetRawDiv :
      ((∫ y in (1 : ℝ)..2, Ψ y) * x) /
        (8 * (M : ℝ) * (r : ℝ) * Real.log x) ≤
      ((∫ y in (1 : ℝ)..2, Ψ y) * x /
        (8 * (r : ℝ) * Real.log x)) / (Nat.totient (M / c) : ℝ) := by
    rw [hrawDivEq]
    have hdenMPos : 0 < 8 * (r : ℝ) * Real.log x * (M : ℝ) := by positivity
    calc
      _ = ((∫ y in (1 : ℝ)..2, Ψ y) * x) /
          (8 * (r : ℝ) * Real.log x * (M : ℝ)) := by congr 1 <;> ring
      _ ≤ _ := div_le_div_of_nonneg_left hIxn.le hdenLeftPos hdenCmp
  have hsmoothedNonneg : 0 ≤ smoothedMainTerm x c r Ψ :=
    le_trans (by positivity : 0 ≤ (∫ y in (1 : ℝ)..2, Ψ y) * x /
      (8 * (r : ℝ) * Real.log x)) hrawLower
  have hmassLower :
      (∫ y in (1 : ℝ)..2, Ψ y) / (8 * (M : ℝ)) *
        (x / ((r : ℝ) * Real.log x)) ≤
          smoothedMainTerm x c r Ψ / (Nat.totient (M / c) : ℝ) := by
    rw [htargetLowerEq]
    calc
      _ ≤ ((∫ y in (1 : ℝ)..2, Ψ y) * x /
          (8 * (r : ℝ) * Real.log x)) / (Nat.totient (M / c) : ℝ) := htargetRawDiv
      _ ≤ smoothedMainTerm x c r Ψ / (Nat.totient (M / c) : ℝ) :=
        div_le_div_of_nonneg_right hrawLower hφpos.le
  have hcrGe2r : 2 * (r : ℝ) ≤ ((c * r : ℕ) : ℝ) := by
    rw [hcrCast]
    exact mul_le_mul_of_nonneg_right hcLower (Nat.cast_nonneg _)
  have hden2rpos : 0 < 2 * (r : ℝ) := by positivity
  have hfactorUpper : x / ((c * r : ℕ) : ℝ) ≤ x / (2 * (r : ℝ)) :=
    div_le_div_of_nonneg_left hxpos.le hden2rpos hcrGe2r
  have hILogTwoPos : 0 ≤ 2 * (∫ y in (1 : ℝ)..2, Ψ y) / Real.log x := by positivity
  have hrawUpper : smoothedMainTerm x c r Ψ ≤
      2 * (∫ y in (1 : ℝ)..2, Ψ y) * (x / ((r : ℝ) * Real.log x)) := by
    have hfac := mul_le_mul_of_nonneg_right hfactorUpper hILogTwoPos
    have hfacEq : (x / (2 * (r : ℝ))) *
        (2 * (∫ y in (1 : ℝ)..2, Ψ y) / Real.log x) =
          (∫ y in (1 : ℝ)..2, Ψ y) * x /
            ((r : ℝ) * Real.log x) := by
      field_simp [ne_of_gt hrreal, ne_of_gt hLpos]
    calc
      _ ≤ (x / (2 * (r : ℝ))) *
          (2 * (∫ y in (1 : ℝ)..2, Ψ y) / Real.log x) := by
            calc
              _ ≤ (x / ((c * r : ℕ) : ℝ)) *
                  (2 * (∫ y in (1 : ℝ)..2, Ψ y) / Real.log x) := hbasic.2
              _ ≤ _ := hfac
      _ = (∫ y in (1 : ℝ)..2, Ψ y) * x /
          ((r : ℝ) * Real.log x) := hfacEq
      _ ≤ 2 * (∫ y in (1 : ℝ)..2, Ψ y) *
          (x / ((r : ℝ) * Real.log x)) := by
            have hEq : (∫ y in (1 : ℝ)..2, Ψ y) * x /
                ((r : ℝ) * Real.log x) =
                  (∫ y in (1 : ℝ)..2, Ψ y) *
                    (x / ((r : ℝ) * Real.log x)) := by ring
            rw [hEq]
            have hnonneg : 0 ≤ (∫ y in (1 : ℝ)..2, Ψ y) *
                (x / ((r : ℝ) * Real.log x)) := by positivity
            nlinarith
  have hdivle : smoothedMainTerm x c r Ψ /
      (Nat.totient (M / c) : ℝ) ≤ smoothedMainTerm x c r Ψ := by
    rw [div_le_iff₀ hφpos]
    have hmul := mul_le_mul_of_nonneg_left hφone hsmoothedNonneg
    nlinarith
  constructor
  · exact hmassLower
  · exact hdivle.trans hrawUpper

end

end ArtinPrimitiveRoots.Proofs.C_BV
