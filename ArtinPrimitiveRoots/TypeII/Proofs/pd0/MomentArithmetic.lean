import ArtinPrimitiveRoots.TypeII.PD.Defs
import OAI.NumberTheory.PrimeGaps.DivisorSums

namespace ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0

open Classical Finset
open scoped BigOperators

def positiveRange (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun n => 1 ≤ n)

noncomputable def factorTuples (r n : ℕ) : Finset (Fin r → ℕ) :=
  (Fintype.piFinset (fun _ : Fin r => positiveRange n)).filter
    (fun f => (∏ i : Fin r, f i) = n)

lemma tau_zero : ArtinPrimitiveRoots.TypeII.PD.tau 0 = 1 := by
  simp [ArtinPrimitiveRoots.TypeII.PD.tau]

lemma tau_eq_divisors_card (n : ℕ) (hn : 0 < n) :
    ArtinPrimitiveRoots.TypeII.PD.tau n = n.divisors.card := by
  classical
  unfold ArtinPrimitiveRoots.TypeII.PD.tau
  congr 1
  ext d
  simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_divisors]
  constructor
  · rintro ⟨_, hdiv⟩
    exact ⟨hdiv, hn.ne'⟩
  · rintro ⟨hdiv, _⟩
    have hdn : d ≤ n := Nat.le_of_dvd hn hdiv
    exact ⟨by omega, hdiv⟩

noncomputable def subsetFinEquiv (k : ℕ) : Fin (2 ^ k) ≃ Finset (Fin k) := by
  simpa using (Fintype.equivFin (Finset (Fin k))).symm

def levelMask {k : ℕ} (d : Fin k → ℕ) (p j : ℕ) : Finset (Fin k) :=
  Finset.univ.filter (fun i => j < (d i).factorization p)

noncomputable def layerCount {k : ℕ} (n : ℕ) (d : Fin k → ℕ)
    (p : ℕ) (S : Finset (Fin k)) : ℕ :=
  ((Finset.range (n.factorization p)).filter (fun j => levelMask d p j = S)).card

lemma layerCount_sum (k : ℕ) (n : ℕ) (d : Fin k → ℕ) (p : ℕ) :
    (∑ S ∈ (Finset.univ : Finset (Finset (Fin k))), layerCount n d p S) =
      n.factorization p := by
  classical
  unfold layerCount
  rw [Finset.sum_card_fiberwise_eq_card_filter
    (s := Finset.range (n.factorization p))
    (t := (Finset.univ : Finset (Finset (Fin k))))
    (g := levelMask d p)]
  simp

lemma layerCount_mem_sum (k : ℕ) (n : ℕ) (d : Fin k → ℕ)
    (i : Fin k) (p : ℕ) (hfac : (d i).factorization p ≤ n.factorization p) :
    (∑ S ∈ (Finset.univ : Finset (Finset (Fin k))).filter (fun S => i ∈ S),
      layerCount n d p S) = (d i).factorization p := by
  classical
  unfold layerCount
  rw [Finset.sum_card_fiberwise_eq_card_filter
    (s := Finset.range (n.factorization p))
    (t := (Finset.univ : Finset (Finset (Fin k))).filter (fun S => i ∈ S))
    (g := levelMask d p)]
  have hfilter :
      (Finset.range (n.factorization p)).filter (fun j => levelMask d p j ∈
        (Finset.univ : Finset (Finset (Fin k))).filter (fun S => i ∈ S)) =
      Finset.range ((d i).factorization p) := by
    ext j
    simp [levelMask]
    omega
  rw [hfilter]
  simp

noncomputable def layerFactor {k : ℕ} (n : ℕ) (d : Fin k → ℕ)
    (S : Finset (Fin k)) : ℕ :=
  ∏ p ∈ n.primeFactors, p ^ layerCount n d p S

lemma layerFactor_pos {k : ℕ} (n : ℕ) (d : Fin k → ℕ) (S : Finset (Fin k)) :
    0 < layerFactor n d S := by
  unfold layerFactor
  apply Finset.prod_pos
  intro p hp
  exact pow_pos (Nat.prime_of_mem_primeFactors hp).pos _

lemma layerFactor_prod_eq {k : ℕ} (n : ℕ) (d : Fin k → ℕ) (hn : n ≠ 0) :
    (∏ S : Finset (Fin k), layerFactor n d S) = n := by
  classical
  calc
    (∏ S : Finset (Fin k), layerFactor n d S) =
        ∏ S : Finset (Fin k), ∏ p ∈ n.primeFactors, p ^ layerCount n d p S := rfl
    _ = ∏ p ∈ n.primeFactors, ∏ S : Finset (Fin k), p ^ layerCount n d p S := by
      rw [Finset.prod_comm]
    _ = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [Finset.prod_pow_eq_pow_sum, layerCount_sum]
    _ = n := (Nat.prod_primeFactors_pow_factorization hn).symm

noncomputable def layerCoordinate {k : ℕ} (n : ℕ) (d : Fin k → ℕ) (i : Fin k) : ℕ :=
  ∏ S ∈ (Finset.univ : Finset (Finset (Fin k))).filter (fun S => i ∈ S),
    layerFactor n d S

lemma layerCoordinate_eq {k : ℕ} (n : ℕ) (d : Fin k → ℕ) (i : Fin k)
    (hn : n ≠ 0) (hdiv : ∀ j, d j ∣ n) : layerCoordinate n d i = d i := by
  classical
  have hdi : d i ≠ 0 := ne_zero_of_dvd_ne_zero hn (hdiv i)
  have hfac (p : ℕ) : (d i).factorization p ≤ n.factorization p :=
    (Nat.factorization_le_iff_dvd hdi hn).mpr (hdiv i) p
  have hprimeSubset : (d i).primeFactors ⊆ n.primeFactors := by
    intro p hp
    rcases Nat.mem_primeFactors.mp hp with ⟨hpp, hpd, _⟩
    exact Nat.mem_primeFactors.mpr ⟨hpp, hpd.trans (hdiv i), hn⟩
  calc
    layerCoordinate n d i =
        ∏ p ∈ n.primeFactors,
          ∏ S ∈ (Finset.univ : Finset (Finset (Fin k))).filter (fun S => i ∈ S),
            p ^ layerCount n d p S := by
      unfold layerCoordinate layerFactor
      rw [Finset.prod_comm]
    _ = ∏ p ∈ n.primeFactors, p ^ (d i).factorization p := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [Finset.prod_pow_eq_pow_sum, layerCount_mem_sum k n d i p (hfac p)]
    _ = ∏ p ∈ (d i).primeFactors, p ^ (d i).factorization p := by
      symm
      apply Finset.prod_subset hprimeSubset
      intro p hp hnot
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hnotdvd : ¬ p ∣ d i := by
        intro hpd
        exact hnot (Nat.mem_primeFactors.mpr ⟨hpp, hpd, hdi⟩)
      rw [Nat.factorization_eq_zero_of_not_dvd hnotdvd]
      simp
    _ = d i := (Nat.prod_primeFactors_pow_factorization hdi).symm

noncomputable def layerEncoding {k : ℕ} (n : ℕ) (d : Fin k → ℕ) : Fin (2 ^ k) → ℕ :=
  fun j => layerFactor n d (subsetFinEquiv k j)

lemma layerEncoding_prod_eq {k : ℕ} (n : ℕ) (d : Fin k → ℕ) (hn : n ≠ 0) :
    (∏ j : Fin (2 ^ k), layerEncoding n d j) = n := by
  calc
    (∏ j : Fin (2 ^ k), layerEncoding n d j) =
        ∏ S : Finset (Fin k), layerFactor n d S := by
      exact Equiv.prod_comp (subsetFinEquiv k) (fun S => layerFactor n d S)
    _ = n := layerFactor_prod_eq n d hn

lemma layerEncoding_mem {k : ℕ} (n : ℕ) (d : Fin k → ℕ) (hn : 0 < n) :
    layerEncoding n d ∈ factorTuples (2 ^ k) n := by
  classical
  change layerEncoding n d ∈
    (Fintype.piFinset (fun _ : Fin (2 ^ k) => positiveRange n)).filter
      (fun f => (∏ j : Fin (2 ^ k), f j) = n)
  rw [Finset.mem_filter]
  constructor
  · apply Fintype.mem_piFinset.mpr
    intro j
    have hpos := layerFactor_pos n d (subsetFinEquiv k j)
    have hAll := layerFactor_prod_eq n d hn.ne'
    have hdivProd : layerFactor n d (subsetFinEquiv k j) ∣
        ∏ S ∈ (Finset.univ : Finset (Finset (Fin k))), layerFactor n d S :=
      Finset.dvd_prod_of_mem (layerFactor n d)
        (s := (Finset.univ : Finset (Finset (Fin k)))) (Finset.mem_univ _)
    have hprodAll :
        (∏ S : Finset (Fin k), layerFactor n d S) ∣ n := by
      rw [hAll]
    have hprod : (layerEncoding n d j) ∣ n := by
      change layerFactor n d (subsetFinEquiv k j) ∣ n
      exact dvd_trans hdivProd hprodAll
    have hle := Nat.le_of_dvd hn hprod
    have hrange : layerEncoding n d j < n + 1 := Nat.lt_succ_of_le hle
    have hge : 1 ≤ layerEncoding n d j := by
      exact Nat.succ_le_iff.mpr hpos
    change layerEncoding n d j ∈ positiveRange n
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hrange, hge⟩
  · exact layerEncoding_prod_eq n d hn.ne'

lemma tau_pow_le_factorTuples_card (k n : ℕ) (hn : 0 < n) :
    (ArtinPrimitiveRoots.TypeII.PD.tau n) ^ k ≤ (factorTuples (2 ^ k) n).card := by
  classical
  let D : Type := Fin k → {d : ℕ // d ∈ n.divisors}
  let enc : D → {f // f ∈ factorTuples (2 ^ k) n} := fun d =>
    ⟨layerEncoding n (fun i => (d i).val),
      layerEncoding_mem n (fun i => (d i).val) hn⟩
  have hinj : Function.Injective enc := by
    intro d e hde
    have hfun : layerEncoding n (fun i => (d i).val) =
        layerEncoding n (fun i => (e i).val) := congrArg Subtype.val hde
    apply funext
    intro i
    apply Subtype.ext
    have hdvd : ∀ j, (d j).val ∣ n := fun j => (Nat.mem_divisors.mp (d j).property).1
    have hevd : ∀ j, (e j).val ∣ n := fun j => (Nat.mem_divisors.mp (e j).property).1
    have hpoint : ∀ S : Finset (Fin k),
        layerFactor n (fun j => (d j).val) S = layerFactor n (fun j => (e j).val) S := by
      intro S
      have hj := congrFun hfun ((subsetFinEquiv k).symm S)
      simpa [layerEncoding] using hj
    have hcoord : layerCoordinate n (fun j => (d j).val) i =
        layerCoordinate n (fun j => (e j).val) i := by
      unfold layerCoordinate
      apply Finset.prod_congr rfl
      intro S hS
      exact hpoint S
    rw [layerCoordinate_eq n (fun j => (d j).val) i hn.ne' hdvd,
      layerCoordinate_eq n (fun j => (e j).val) i hn.ne' hevd] at hcoord
    exact hcoord
  have hcard := Fintype.card_le_of_injective enc hinj
  have hDcard : Fintype.card D = (ArtinPrimitiveRoots.TypeII.PD.tau n) ^ k := by
    simp [D, tau_eq_divisors_card n hn, Fintype.card_fun, Fintype.card_coe]
  have hOutCard : Fintype.card {f // f ∈ factorTuples (2 ^ k) n} =
      (factorTuples (2 ^ k) n).card := Fintype.card_coe _
  rw [hDcard, hOutCard] at hcard
  exact hcard

noncomputable def positiveProductBox (r N : ℕ) : Finset (Fin r → ℕ) :=
  (Fintype.piFinset (fun _ : Fin r => positiveRange N)).filter
    (fun f => (∏ i : Fin r, f i) ≤ N)

lemma factorTuples_eq_box_fiber (r N n : ℕ) (hnN : n ∈ positiveRange N) :
    factorTuples r n =
      (positiveProductBox r N).filter (fun f => (∏ i : Fin r, f i) = n) := by
  classical
  ext f
  constructor
  · intro hf
    obtain ⟨hpi, hprod⟩ := Finset.mem_filter.mp hf
    have hninfo := Finset.mem_filter.mp hnN
    have hnle : n ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hninfo.1)
    have hnpos : 0 < n := by omega
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ?_, hprod⟩
    constructor
    · apply Fintype.mem_piFinset.mpr
      intro i
      have hi := Fintype.mem_piFinset.mp hpi i
      obtain ⟨_, hi_pos⟩ := Finset.mem_filter.mp hi
      have hdiv : f i ∣ ∏ j : Fin r, f j :=
        Finset.dvd_prod_of_mem (fun j => f j) (Finset.mem_univ i)
      rw [hprod] at hdiv
      have hle := Nat.le_of_dvd hnpos hdiv
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), hi_pos⟩
    · rw [hprod]
      exact hnle
  · intro hf
    obtain ⟨hbox, hprod⟩ := Finset.mem_filter.mp hf
    change f ∈ (Fintype.piFinset (fun _ : Fin r => positiveRange N)).filter
      (fun f => (∏ i : Fin r, f i) ≤ N) at hbox
    obtain ⟨hpi, _hNprod⟩ := Finset.mem_filter.mp hbox
    have hninfo := Finset.mem_filter.mp hnN
    have hnpos : 0 < n := by omega
    apply Finset.mem_filter.mpr
    constructor
    · apply Fintype.mem_piFinset.mpr
      intro i
      have hi := Fintype.mem_piFinset.mp hpi i
      obtain ⟨_, hi_pos⟩ := Finset.mem_filter.mp hi
      have hdiv : f i ∣ ∏ j : Fin r, f j :=
        Finset.dvd_prod_of_mem (fun j => f j) (Finset.mem_univ i)
      rw [hprod] at hdiv
      have hle := Nat.le_of_dvd hnpos hdiv
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), hi_pos⟩
    · exact hprod

lemma factorTuples_card_sum_eq_box_card (r N : ℕ) :
    (∑ n ∈ positiveRange N, (factorTuples r n).card) =
      (positiveProductBox r N).card := by
  classical
  have hmap : ∀ f ∈ positiveProductBox r N,
      (∏ i : Fin r, f i) ∈ positiveRange N := by
    intro f hf
    obtain ⟨hpi, hprod_le⟩ := Finset.mem_filter.mp hf
    have hprod_pos : 0 < ∏ i : Fin r, f i := by
      apply Finset.prod_pos
      intro i _
      have hi := Fintype.mem_piFinset.mp hpi i
      exact Nat.succ_le_iff.mp (Finset.mem_filter.mp hi).2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hprod_le), Nat.succ_le_iff.mpr hprod_pos⟩
  calc
    _ = ∑ n ∈ positiveRange N,
        ((positiveProductBox r N).filter (fun f => (∏ i : Fin r, f i) = n)).card := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [← factorTuples_eq_box_fiber r N n hn]
    _ = ((positiveProductBox r N).filter
        (fun f => (∏ i : Fin r, f i) ∈ positiveRange N)).card :=
      Finset.sum_card_fiberwise_eq_card_filter
        (positiveProductBox r N) (positiveRange N) (fun f => ∏ i : Fin r, f i)
    _ = (positiveProductBox r N).card := by
      rw [Finset.filter_eq_self.mpr hmap]

lemma positiveProductBox_weight_sum_le (r N : ℕ) :
    (∑ f ∈ positiveProductBox r N, ∏ i : Fin r, ((f i : ℝ)⁻¹)) ≤
      (∑ n ∈ positiveRange N, ((n : ℝ)⁻¹)) ^ r := by
  classical
  calc
    _ ≤ ∑ f ∈ Fintype.piFinset (fun _ : Fin r => positiveRange N),
          ∏ i : Fin r, ((f i : ℝ)⁻¹) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro f hf
        exact (Finset.mem_filter.mp hf).1
      · intro f hf hnot
        positivity
    _ = (∑ n ∈ positiveRange N, ((n : ℝ)⁻¹)) ^ r := by
      calc
        _ = ∏ i : Fin r, ∑ n ∈ positiveRange N, ((n : ℝ)⁻¹) :=
          Finset.sum_prod_piFinset (positiveRange N) (fun _ n => (n : ℝ)⁻¹)
        _ = _ := by simp [Finset.prod_const]

lemma factorTuples_weight_sum_le (r N : ℕ) :
    (∑ n ∈ positiveRange N,
      ((factorTuples r n).card : ℝ) / (n : ℝ)) ≤
        (∑ n ∈ positiveRange N, ((n : ℝ)⁻¹)) ^ r := by
  classical
  have hmap : ∀ f ∈ positiveProductBox r N,
      (∏ i : Fin r, f i) ∈ positiveRange N := by
    intro f hf
    obtain ⟨hpi, hprod_le⟩ := Finset.mem_filter.mp hf
    have hprod_pos : 0 < ∏ i : Fin r, f i := by
      apply Finset.prod_pos
      intro i _
      have hi := Fintype.mem_piFinset.mp hpi i
      exact Nat.succ_le_iff.mp (Finset.mem_filter.mp hi).2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hprod_le), Nat.succ_le_iff.mpr hprod_pos⟩
  have hlocal (n : ℕ) (hnN : n ∈ positiveRange N) :
      ((factorTuples r n).card : ℝ) / (n : ℝ) =
        ∑ f ∈ (positiveProductBox r N).filter
          (fun f => (∏ i : Fin r, f i) = n),
          ∏ i : Fin r, ((f i : ℝ)⁻¹) := by
    have hweight (f : Fin r → ℕ) (hf : f ∈ factorTuples r n) :
        (∏ i : Fin r, ((f i : ℝ)⁻¹)) = (n : ℝ)⁻¹ := by
      have hprod := (Finset.mem_filter.mp hf).2
      calc
        _ = (∏ i : Fin r, (f i : ℝ))⁻¹ := by rw [Finset.prod_inv_distrib]
        _ = ((∏ i : Fin r, f i : ℕ) : ℝ)⁻¹ := by simp
        _ = (n : ℝ)⁻¹ := by rw [hprod]
    calc
      ((factorTuples r n).card : ℝ) / (n : ℝ) =
          ∑ f ∈ factorTuples r n, (n : ℝ)⁻¹ := by
        simp [div_eq_mul_inv, Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ = ∑ f ∈ factorTuples r n, ∏ i : Fin r, ((f i : ℝ)⁻¹) := by
        apply Finset.sum_congr rfl
        intro f hf
        exact (hweight f hf).symm
      _ = ∑ f ∈ (positiveProductBox r N).filter
            (fun f => (∏ i : Fin r, f i) = n),
            ∏ i : Fin r, ((f i : ℝ)⁻¹) := by
        exact congrArg (fun s : Finset (Fin r → ℕ) =>
          ∑ f ∈ s, ∏ i : Fin r, ((f i : ℝ)⁻¹))
            (factorTuples_eq_box_fiber r N n hnN)
  calc
    _ = ∑ n ∈ positiveRange N, ∑ f ∈ (positiveProductBox r N).filter
          (fun f => (∏ i : Fin r, f i) = n),
          ∏ i : Fin r, ((f i : ℝ)⁻¹) := by
      apply Finset.sum_congr rfl
      intro n hnN
      exact hlocal n hnN
    _ = ∑ f ∈ (positiveProductBox r N).filter
          (fun f => (∏ i : Fin r, f i) ∈ positiveRange N),
          ∏ i : Fin r, ((f i : ℝ)⁻¹) := by
      exact Finset.sum_fiberwise_eq_sum_filter
        (positiveProductBox r N) (positiveRange N)
        (fun f => ∏ i : Fin r, f i)
        (fun f => ∏ i : Fin r, ((f i : ℝ)⁻¹))
    _ = ∑ f ∈ positiveProductBox r N, ∏ i : Fin r, ((f i : ℝ)⁻¹) := by
      rw [Finset.filter_eq_self.mpr hmap]
    _ ≤ (∑ n ∈ positiveRange N, ((n : ℝ)⁻¹)) ^ r :=
      positiveProductBox_weight_sum_le r N

lemma positiveRange_eq_Icc (N : ℕ) : positiveRange N = Finset.Icc 1 N := by
  classical
  ext n
  simp [positiveRange, Finset.mem_Icc]
  omega

lemma harmonicRange_le_one_add_log (N : ℕ) :
    (∑ n ∈ positiveRange N, ((n : ℝ)⁻¹)) ≤ 1 + Real.log (N : ℝ) := by
  rw [positiveRange_eq_Icc]
  simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
    Rat.cast_natCast, one_div] using harmonic_le_one_add_log N

lemma range_succ_eq_insert_zero_positive (N : ℕ) :
    Finset.range (N + 1) = insert 0 (positiveRange N) := by
  classical
  ext n
  simp [positiveRange]
  omega

lemma positiveProductBox_card_le (r N : ℕ) :
    ((positiveProductBox r N).card : ℝ) ≤
      (N : ℝ) * (∑ n ∈ positiveRange N, ((n : ℝ)⁻¹)) ^ r := by
  classical
  have hterm (n : ℕ) (hn : n ∈ positiveRange N) :
      ((factorTuples r n).card : ℝ) ≤ (N : ℝ) *
        (((factorTuples r n).card : ℝ) / (n : ℝ)) := by
    have hninfo := Finset.mem_filter.mp hn
    have hnle : n ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hninfo.1)
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hratio : 1 ≤ (N : ℝ) / (n : ℝ) :=
      (le_div_iff₀ hnpos).2 (by
        have hnr : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnle
        simpa using hnr)
    have hcard : 0 ≤ ((factorTuples r n).card : ℝ) := by positivity
    calc
      _ = 1 * ((factorTuples r n).card : ℝ) := by ring
      _ ≤ ((N : ℝ) / (n : ℝ)) * ((factorTuples r n).card : ℝ) :=
        mul_le_mul_of_nonneg_right hratio hcard
      _ = _ := by ring
  calc
    ((positiveProductBox r N).card : ℝ) =
        ∑ n ∈ positiveRange N, ((factorTuples r n).card : ℝ) := by
      exact_mod_cast (factorTuples_card_sum_eq_box_card r N).symm
    _ ≤ ∑ n ∈ positiveRange N,
        (N : ℝ) * (((factorTuples r n).card : ℝ) / (n : ℝ)) :=
      Finset.sum_le_sum fun n hn => hterm n hn
    _ = (N : ℝ) * ∑ n ∈ positiveRange N,
        (((factorTuples r n).card : ℝ) / (n : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ (N : ℝ) * (∑ n ∈ positiveRange N, ((n : ℝ)⁻¹)) ^ r :=
      mul_le_mul_of_nonneg_left (factorTuples_weight_sum_le r N) (Nat.cast_nonneg _)

lemma tau_pow_div_succ_le_factorTuple_weight (k n : ℕ) (hn : 0 < n) :
    (ArtinPrimitiveRoots.TypeII.PD.tau n : ℝ) ^ k / ((n : ℝ) + 1) ≤
      ((factorTuples (2 ^ k) n).card : ℝ) / (n : ℝ) := by
  have hdivisor := tau_pow_le_factorTuples_card k n hn
  have hcast : (ArtinPrimitiveRoots.TypeII.PD.tau n : ℝ) ^ k ≤
      ((factorTuples (2 ^ k) n).card : ℝ) := by exact_mod_cast hdivisor
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcard : 0 ≤ ((factorTuples (2 ^ k) n).card : ℝ) := by positivity
  have hrecip : 1 / ((n : ℝ) + 1) ≤ 1 / (n : ℝ) :=
    one_div_le_one_div_of_le hnR (by linarith)
  calc
    _ ≤ ((factorTuples (2 ^ k) n).card : ℝ) / ((n : ℝ) + 1) :=
      div_le_div_of_nonneg_right hcast (by positivity)
    _ = ((factorTuples (2 ^ k) n).card : ℝ) * (1 / ((n : ℝ) + 1)) := by ring
    _ ≤ ((factorTuples (2 ^ k) n).card : ℝ) * (1 / (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hrecip hcard
    _ = ((factorTuples (2 ^ k) n).card : ℝ) / (n : ℝ) := by ring

lemma sum_tau_pow_le (k N : ℕ) :
    (∑ n ∈ Finset.range (N + 1),
      (ArtinPrimitiveRoots.TypeII.PD.tau n : ℝ) ^ k) ≤
        1 + (N : ℝ) * (∑ n ∈ positiveRange N, ((n : ℝ)⁻¹)) ^ (2 ^ k) := by
  classical
  have hpos :
      (∑ n ∈ positiveRange N, (ArtinPrimitiveRoots.TypeII.PD.tau n : ℝ) ^ k) ≤
        ((positiveProductBox (2 ^ k) N).card : ℝ) := by
    calc
      _ ≤ ∑ n ∈ positiveRange N, ((factorTuples (2 ^ k) n).card : ℝ) :=
        Finset.sum_le_sum fun n hn => by
          have hn0 : 0 < n := by
            have := Finset.mem_filter.mp hn
            omega
          exact_mod_cast tau_pow_le_factorTuples_card k n hn0
      _ = ((positiveProductBox (2 ^ k) N).card : ℝ) := by
        exact_mod_cast (factorTuples_card_sum_eq_box_card (2 ^ k) N)
  rw [range_succ_eq_insert_zero_positive N, Finset.sum_insert (by
    simp [positiveRange])]
  simp only [tau_zero, Nat.cast_one, one_pow]
  calc
    (1 : ℝ) +
        ∑ n ∈ positiveRange N,
          (ArtinPrimitiveRoots.TypeII.PD.tau n : ℝ) ^ k ≤
      1 + ((positiveProductBox (2 ^ k) N).card : ℝ) := by nlinarith [hpos]
    _ ≤ 1 + (N : ℝ) * (∑ n ∈ positiveRange N, ((n : ℝ)⁻¹)) ^ (2 ^ k) := by
      gcongr
      exact positiveProductBox_card_le (2 ^ k) N

lemma sum_tau_pow_div_succ_le (k N : ℕ) :
    (∑ n ∈ Finset.range (N + 1),
      (ArtinPrimitiveRoots.TypeII.PD.tau n : ℝ) ^ k / ((n : ℝ) + 1)) ≤
        1 + (∑ n ∈ positiveRange N, ((n : ℝ)⁻¹)) ^ (2 ^ k) := by
  classical
  have hpos :
      (∑ n ∈ positiveRange N,
        (ArtinPrimitiveRoots.TypeII.PD.tau n : ℝ) ^ k / ((n : ℝ) + 1)) ≤
          (∑ n ∈ positiveRange N,
            ((factorTuples (2 ^ k) n).card : ℝ) / (n : ℝ)) :=
    Finset.sum_le_sum fun n hn => by
      have hn0 : 0 < n := by
        have := Finset.mem_filter.mp hn
        omega
      exact tau_pow_div_succ_le_factorTuple_weight k n hn0
  rw [range_succ_eq_insert_zero_positive N, Finset.sum_insert (by
    simp [positiveRange])]
  simp only [tau_zero, Nat.cast_one, one_pow, Nat.cast_zero, zero_add, div_one]
  calc
    (1 : ℝ) +
        ∑ n ∈ positiveRange N,
          (ArtinPrimitiveRoots.TypeII.PD.tau n : ℝ) ^ k / ((n : ℝ) + 1) ≤
      1 + (∑ n ∈ positiveRange N,
        ((factorTuples (2 ^ k) n).card : ℝ) / (n : ℝ)) := by nlinarith [hpos]
    _ ≤ 1 + (∑ n ∈ positiveRange N, ((n : ℝ)⁻¹)) ^ (2 ^ k) := by
      nlinarith [factorTuples_weight_sum_le (2 ^ k) N]

end ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0
