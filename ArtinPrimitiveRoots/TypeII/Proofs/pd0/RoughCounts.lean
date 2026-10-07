import ArtinPrimitiveRoots.TypeII.Defs
import ArtinPrimitiveRoots.Ext.TypeIIInputs
import OAI.NumberTheory.Jacobsthal.Sieve.EulerProductRatio
import OAI.NumberTheory.Jacobsthal.Sieve.RealCoprimeResidueCount
import OAI.NumberTheory.PrimeGaps.DirichletGrowth

namespace ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0

open Classical Finset
open scoped BigOperators

private lemma crtResidue_class_iff (m d : ℕ) (b : ZMod m)
    (hm : 0 < m) (hd : 0 < d) (hcop : Nat.Coprime m d) (n : ℤ) :
    (n : ZMod (m * d)) =
        ((Nat.chineseRemainder hcop b.val 0).val : ZMod (m * d)) ↔
      (n : ZMod m) = b ∧ (d : ℤ) ∣ n := by
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  letI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  let c := (Nat.chineseRemainder hcop b.val 0).val
  have hc₁ : (c : ZMod m) = b := by
    have hmod : c ≡ b.val [MOD m] := (Nat.chineseRemainder hcop b.val 0).property.1
    calc
      (c : ZMod m) = (b.val : ZMod m) := (ZMod.natCast_eq_natCast_iff c b.val m).2 hmod
      _ = b := ZMod.natCast_zmod_val b
  have hc₂ : (c : ZMod d) = 0 := by
    have hmod : c ≡ 0 [MOD d] := (Nat.chineseRemainder hcop b.val 0).property.2
    exact (ZMod.natCast_eq_zero_iff c d).mpr (Nat.modEq_zero_iff_dvd.mp hmod)
  have hcopZ : (m : ℤ).natAbs.Coprime (d : ℤ).natAbs := by
    simpa using hcop
  constructor
  · intro hn
    have hn' : (n : ZMod (m * d)) = ((c : ℤ) : ZMod (m * d)) := by
      simpa only [Int.cast_natCast] using hn
    have hprodNat := (ZMod.intCast_eq_intCast_iff n (c : ℤ) (m * d)).1 hn'
    have hprod : n ≡ (c : ℤ) [ZMOD (m : ℤ) * (d : ℤ)] := by
      simpa only [Int.natCast_mul] using hprodNat
    have hpair := (Int.modEq_and_modEq_iff_modEq_mul hcopZ).2 hprod
    have hmcastInt : (n : ZMod m) = ((c : ℤ) : ZMod m) :=
      (ZMod.intCast_eq_intCast_iff n (c : ℤ) m).2 hpair.1
    have hdcastInt : (n : ZMod d) = ((c : ℤ) : ZMod d) :=
      (ZMod.intCast_eq_intCast_iff n (c : ℤ) d).2 hpair.2
    have hmcast : (n : ZMod m) = (c : ZMod m) := by
      simpa only [Int.cast_natCast] using hmcastInt
    have hdcast : (n : ZMod d) = (c : ZMod d) := by
      simpa only [Int.cast_natCast] using hdcastInt
    refine ⟨hmcast.trans hc₁, ?_⟩
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    rw [hdcast, hc₂]
  · rintro ⟨hmb, hdn⟩
    have hmcast : (n : ZMod m) = (c : ZMod m) := hmb.trans hc₁.symm
    have hdcast : (n : ZMod d) = (c : ZMod d) := by
      rw [hc₂, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact hdn
    have hmcast' : (n : ZMod m) = ((c : ℤ) : ZMod m) := by
      simpa only [Int.cast_natCast] using hmcast
    have hdcast' : (n : ZMod d) = ((c : ℤ) : ZMod d) := by
      simpa only [Int.cast_natCast] using hdcast
    have hpair : n ≡ (c : ℤ) [ZMOD (m : ℤ)] ∧
        n ≡ (c : ℤ) [ZMOD (d : ℤ)] :=
      ⟨(ZMod.intCast_eq_intCast_iff n (c : ℤ) m).1 hmcast',
       (ZMod.intCast_eq_intCast_iff n (c : ℤ) d).1 hdcast'⟩
    have hprod : n ≡ (c : ℤ) [ZMOD (m : ℤ) * (d : ℤ)] :=
      (Int.modEq_and_modEq_iff_modEq_mul hcopZ).1 hpair
    have hprodNat : n ≡ (c : ℤ) [ZMOD ((m * d : ℕ) : ℤ)] := by
      simpa only [Int.natCast_mul] using hprod
    have hn' : (n : ZMod (m * d)) = ((c : ℤ) : ZMod (m * d)) :=
      (ZMod.intCast_eq_intCast_iff n (c : ℤ) (m * d)).2 hprodNat
    simpa only [Int.cast_natCast] using hn'

private lemma roughAbove_iff_avoids_primesUpTo (n : ℕ) (W : ℝ) :
    ArtinPrimitiveRoots.TypeII.roughAbove n W ↔
      ∀ p ∈ ArtinPrimitiveRoots.TypeII.primesUpTo W, ¬ p ∣ n := by
  constructor
  · intro h p hp hpn
    have hp' : p ∈ (Finset.range (⌊W⌋₊ + 1)).filter Nat.Prime := by
      simpa [ArtinPrimitiveRoots.TypeII.primesUpTo] using hp
    obtain ⟨hpRange, hpPrime⟩ := Finset.mem_filter.mp hp'
    have hpLe : p ≤ ⌊W⌋₊ := by
      have hlt := Finset.mem_range.mp hpRange
      omega
    have hW : (p : ℝ) ≤ W := (Nat.le_floor_iff' hpPrime.ne_zero).mp hpLe
    exact (not_lt_of_ge hW) (h p hpPrime hpn)
  · intro h p hp hpn
    by_contra hnot
    have hpW : (p : ℝ) ≤ W := le_of_not_gt (show ¬ W < (p : ℝ) from hnot)
    have hW0 : 0 ≤ W := le_trans (show (0 : ℝ) ≤ p by positivity) hpW
    have hpFloor : p ≤ ⌊W⌋₊ := (Nat.le_floor_iff hW0).mpr hpW
    have hpmem : p ∈ ArtinPrimitiveRoots.TypeII.primesUpTo W := by
      unfold ArtinPrimitiveRoots.TypeII.primesUpTo
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_of_le hpFloor, hp⟩
    exact h p hpmem hpn

theorem nat_rough_residue_image (N m : ℕ) (b : ZMod m) (W l : ℝ)
    (hl : 0 ≤ l) :
    ((Finset.range N).filter (fun n : ℕ =>
      l ≤ (n : ℝ) ∧ ArtinPrimitiveRoots.TypeII.roughAbove n W ∧ (n : ZMod m) = b)).image
        (fun n : ℕ => (n : ℤ)) =
      (OAI.Erdos970.ErdosCoprimeResidueInterval.realCoprimeResidues
        1 m {b} l (N : ℝ)).filter
        (fun z : ℤ => ∀ p ∈ ArtinPrimitiveRoots.TypeII.primesUpTo W,
          ¬ (p : ℤ) ∣ z) := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨n, hn, hzn⟩ := Finset.mem_image.mp hz
    subst z
    obtain ⟨hnrange, hnlow, hrough, hres⟩ := Finset.mem_filter.mp hn
    have hAvoid := (roughAbove_iff_avoids_primesUpTo n W).mp hrough
    apply Finset.mem_filter.mpr
    constructor
    · rw [OAI.Erdos970.ErdosCoprimeResidueInterval.mem_realCoprimeResidues]
      refine ⟨hnlow, ?_, by simp, by simp [hres]⟩
      have hnlt : n < N := Finset.mem_range.mp hnrange
      exact_mod_cast hnlt
    · intro p hp
      have hpn := hAvoid p hp
      exact fun h => hpn ((Int.natCast_dvd_natCast).mp h)
  · intro hz
    have hz' := Finset.mem_filter.mp hz
    rw [OAI.Erdos970.ErdosCoprimeResidueInterval.mem_realCoprimeResidues] at hz'
    rcases hz' with ⟨⟨hzlow, hzupper, hcop, hzres⟩, hzavoid⟩
    have hzNonneg : 0 ≤ z := by exact_mod_cast hl.trans hzlow
    let n := z.toNat
    have hcast : (n : ℤ) = z := Int.toNat_of_nonneg hzNonneg
    have hnlt : n < N := by
      have hzupperInt : z < (N : ℤ) := by exact_mod_cast hzupper
      rw [← hcast] at hzupperInt
      have : (n : ℝ) < N := by exact_mod_cast hzupperInt
      exact_mod_cast this
    have hrough : ArtinPrimitiveRoots.TypeII.roughAbove n W := by
      apply (roughAbove_iff_avoids_primesUpTo n W).mpr
      intro p hp hpn
      apply hzavoid p hp
      rw [← hcast]
      exact (Int.natCast_dvd_natCast).mpr hpn
    apply Finset.mem_image.mpr
    refine ⟨n, Finset.mem_filter.mpr ?_, hcast⟩
    have hcastR : (n : ℝ) = (z : ℝ) := by exact_mod_cast hcast
    have hcastZMod : (n : ZMod m) = (z : ZMod m) := by
      have hh := congrArg (fun t : ℤ => (t : ZMod m)) hcast
      simpa only [Int.cast_natCast] using hh
    have hzres' : (z : ZMod m) = b := Finset.mem_singleton.mp hzres
    exact ⟨Finset.mem_range.mpr hnlt,
      hcastR ▸ hzlow, hrough, hcastZMod.trans hzres'⟩

private lemma eventually_const_mul_rpow_le_linear (α K ε : ℝ)
    (hα : α < 1) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in Filter.atTop, K * L ^ α ≤ ε * L := by
  have hpow : Filter.Tendsto (fun L : ℝ => L ^ (α - 1)) Filter.atTop (nhds 0) := by
    convert tendsto_rpow_neg_atTop (sub_pos.mpr hα) using 1 <;> congr 1 <;> ring
  have hsmall : ∀ᶠ L : ℝ in Filter.atTop, L ^ (α - 1) < ε / (K + 1) :=
    hpow.eventually (Iio_mem_nhds (by positivity))
  filter_upwards [hsmall, Filter.eventually_gt_atTop (0 : ℝ)] with L hsmall hL
  have hcoeff : K * L ^ (α - 1) ≤ ε := by
    calc
      K * L ^ (α - 1) ≤ K * (ε / (K + 1)) :=
        mul_le_mul_of_nonneg_left hsmall.le hK
      _ ≤ ε := by
        have hden : K + 1 ≠ 0 := by positivity
        field_simp
        nlinarith [hK, hε]
  have hpowEq : L ^ α = L ^ (α - 1) * L := by
    calc
      L ^ α = L ^ ((α - 1) + 1) := by congr 1 <;> ring_nf
      _ = L ^ (α - 1) * L ^ (1 : ℝ) := Real.rpow_add hL _ _
      _ = L ^ (α - 1) * L := by rw [Real.rpow_one]
  calc
    K * L ^ α = (K * L ^ (α - 1)) * L := by rw [hpowEq]; ring
    _ ≤ ε * L := mul_le_mul_of_nonneg_right hcoeff hL.le

private lemma eventually_log_le_rpow (α : ℝ) (hα : 0 < α) :
    ∀ᶠ L : ℝ in Filter.atTop, Real.log L ≤ L ^ α := by
  have hlittle := (isLittleO_log_rpow_atTop hα).bound one_pos
  filter_upwards [hlittle, Filter.eventually_ge_atTop (1 : ℝ)] with L hL hL1
  have hnorm : |Real.log L| ≤ |L ^ α| := by simpa using hL
  rw [abs_of_nonneg (Real.log_nonneg hL1),
    abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ L) α)] at hnorm
  exact hnorm

private lemma eventually_const_mul_log_le_rpow (α K : ℝ)
    (hα : 0 < α) (hK : 0 ≤ K) :
    ∀ᶠ L : ℝ in Filter.atTop, K * Real.log L ≤ L ^ α := by
  have hsmall := (isLittleO_log_rpow_atTop hα).bound
    (show 0 < 1 / (K + 1) by positivity)
  filter_upwards [hsmall, Filter.eventually_ge_atTop (1 : ℝ)] with L hsmall hL1
  have hnorm : |Real.log L| ≤ (1 / (K + 1)) * |L ^ α| := by
    simpa using hsmall
  rw [abs_of_nonneg (Real.log_nonneg hL1),
    abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ L) α)] at hnorm
  have hnorm' : Real.log L ≤ L ^ α / (K + 1) := by
    calc
      Real.log L ≤ (1 / (K + 1)) * L ^ α := hnorm
      _ = L ^ α / (K + 1) := by ring
  calc
    K * Real.log L ≤ K * (L ^ α / (K + 1)) :=
      mul_le_mul_of_nonneg_left hnorm' hK
    _ ≤ L ^ α := by
      have hY : 0 ≤ L ^ α := Real.rpow_nonneg (by linarith : 0 ≤ L) α
      have heq : K * (L ^ α / (K + 1)) = (K * L ^ α) / (K + 1) := by ring
      rw [heq]
      exact (div_le_iff₀ (by positivity : 0 < K + 1)).2 (by nlinarith [hK, hY])

noncomputable def sieveDepth (L : ℝ) : ℝ := 480024 + L ^ (7 / 10 : ℝ)

theorem exists_sieve_precision (δ a B : ℝ)
    (hδ : 0 < δ) (ha : 0 < a) (ha1 : a < 1) (hB : 0 ≤ B) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
      2 * Real.exp (-sieveDepth L / 96) ≤ L ^ (-B) ∧
      8 * Real.exp (480024 * L ^ (24 / 100 : ℝ) + L ^ (94 / 100 : ℝ) + L ^ a) * L ^ B ≤
        Real.exp (δ * L) ∧
      L ^ B ≤ Real.exp (L ^ a) := by
  have he0 := eventually_const_mul_rpow_le_linear (24 / 100 : ℝ)
    (Real.log 8 + 480024) (δ / 4) (by norm_num) (by positivity) (by positivity)
  have he1 := eventually_const_mul_rpow_le_linear (94 / 100 : ℝ)
    1 (δ / 4) (by norm_num) (by norm_num) (by positivity)
  have he2 := eventually_const_mul_rpow_le_linear a
    1 (δ / 4) ha1 (by norm_num) (by positivity)
  have he3 := eventually_const_mul_rpow_le_linear (1 / 10 : ℝ)
    B (δ / 4) (by norm_num) hB (by positivity)
  have hlog := eventually_log_le_rpow (1 / 10 : ℝ) (by norm_num)
  have hlogA := eventually_const_mul_log_le_rpow a B ha hB
  have hlogS := eventually_const_mul_log_le_rpow (7 / 10 : ℝ) (192 * B)
    (by norm_num) (by positivity)
  have hpowS : ∀ᶠ L : ℝ in Filter.atTop, 192 * Real.log 2 ≤ L ^ (7 / 10 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 10)).eventually_ge_atTop _
  have hAll : ∀ᶠ L : ℝ in Filter.atTop,
      1 ≤ L ∧
      (Real.log 8 + 480024) * L ^ (24 / 100 : ℝ) ≤ (δ / 4) * L ∧
      L ^ (94 / 100 : ℝ) ≤ (δ / 4) * L ∧
      L ^ a ≤ (δ / 4) * L ∧
      B * L ^ (1 / 10 : ℝ) ≤ (δ / 4) * L ∧
      Real.log L ≤ L ^ (1 / 10 : ℝ) ∧
      B * Real.log L ≤ L ^ a ∧
      192 * B * Real.log L ≤ L ^ (7 / 10 : ℝ) ∧
      192 * Real.log 2 ≤ L ^ (7 / 10 : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ), he0, he1, he2, he3,
      hlog, hlogA, hlogS, hpowS] with L hL h0 h1 h2 h3 hlog hlogA hlogS hpowS
    exact ⟨hL, h0, by simpa only [one_mul] using h1,
      by simpa only [one_mul] using h2, h3, hlog, hlogA, hlogS, hpowS⟩
  obtain ⟨L₁, hEventually⟩ := Filter.eventually_atTop.1 hAll
  refine ⟨max 2 L₁, by linarith [le_max_left 2 L₁], ?_⟩
  intro L hL
  have hlarge : L₁ ≤ L := le_trans (le_max_right _ _) hL
  obtain ⟨hL, he0, he1, he2, he3, hlog, hlogA, hlogS, hpowS⟩ := hEventually L hlarge
  have hLpos : 0 < L := by linarith
  have hL24 : 1 ≤ L ^ (24 / 100 : ℝ) := by
    calc
      1 = L ^ (0 : ℝ) := by simp
      _ ≤ L ^ (24 / 100 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have hlog2 : Real.log 2 ≤ L ^ (7 / 10 : ℝ) / 192 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 192)).2
    nlinarith [hpowS]
  have hlogSB : B * Real.log L ≤ L ^ (7 / 10 : ℝ) / 192 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 192)).2
    nlinarith [hlogS]
  have hdepth : L ^ (7 / 10 : ℝ) ≤ sieveDepth L := by
    simp [sieveDepth]
  have hdecay : Real.log 2 + B * Real.log L ≤ sieveDepth L / 96 := by
    nlinarith [hlog2, hlogSB, hdepth]
  have hdecayLog :
      Real.log (2 * Real.exp (-sieveDepth L / 96) * L ^ B) ≤ 0 := by
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity), Real.log_exp, Real.log_rpow hLpos]
    ring_nf
    linarith [hdecay]
  have hdecayPos : 0 < 2 * Real.exp (-sieveDepth L / 96) * L ^ B := by positivity
  have hdecayProd : 2 * Real.exp (-sieveDepth L / 96) * L ^ B ≤ 1 := by
    have h := Real.exp_le_exp.mpr hdecayLog
    rw [Real.exp_log hdecayPos] at h
    simpa using h
  have htailLog :
      Real.log (8 * Real.exp (480024 * L ^ (24 / 100 : ℝ) +
        L ^ (94 / 100 : ℝ) + L ^ a) * L ^ B) ≤ δ * L := by
    rw [Real.log_mul (by norm_num) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_rpow hLpos]
    have hlog8pos : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
    have hlog8bound : Real.log 8 ≤ Real.log 8 * L ^ (24 / 100 : ℝ) :=
      calc
        Real.log 8 = Real.log 8 * 1 := by ring
        _ ≤ Real.log 8 * L ^ (24 / 100 : ℝ) :=
          mul_le_mul_of_nonneg_left hL24 hlog8pos
    nlinarith [he0, he1, he2, he3, hlog, hlog8bound]
  have htailPos :
      0 < 8 * Real.exp (480024 * L ^ (24 / 100 : ℝ) +
        L ^ (94 / 100 : ℝ) + L ^ a) * L ^ B := by positivity
  have htail :
      8 * Real.exp (480024 * L ^ (24 / 100 : ℝ) +
        L ^ (94 / 100 : ℝ) + L ^ a) * L ^ B ≤ Real.exp (δ * L) := by
    have h := Real.exp_le_exp.mpr htailLog
    rw [Real.exp_log htailPos] at h
    exact h
  have hpower : L ^ B ≤ Real.exp (L ^ a) := by
    have heq : L ^ B = Real.exp (B * Real.log L) := by
      rw [Real.rpow_def_of_pos hLpos]
      congr 1
      ring
    rw [heq]
    exact Real.exp_le_exp.mpr hlogA
  have hfirst : 2 * Real.exp (-sieveDepth L / 96) ≤ L ^ (-B) := by
    have hpowpos : 0 < L ^ B := Real.rpow_pos_of_pos hLpos B
    have hdiv := (le_div_iff₀ hpowpos).2 hdecayProd
    simpa [Real.rpow_neg hLpos.le B] using hdiv
  exact ⟨hfirst, htail, hpower⟩

private theorem real_interval_residue_divisor_count (m d : ℕ) (b : ZMod m)
    (hm : 0 < m) (hd : 0 < d) (hcop : Nat.Coprime m d)
    (l u : ℝ) (hlu : l ≤ u) :
    |(((OAI.Erdos970.ErdosCoprimeResidueInterval.realCoprimeResidues 1 m {b} l u).filter
        (fun n : ℤ => (d : ℤ) ∣ n)).card : ℝ) - (u - l) / (m * d)| ≤ 2 := by
  let cN := (Nat.chineseRemainder hcop b.val 0).val
  let cr : ZMod (m * d) := (cN : ZMod (m * d))
  let A : Finset (ZMod (m * d)) := {cr}
  let C : Finset ℤ := OAI.Erdos970.ErdosCoprimeResidueInterval.realCoprimeResidues 1 m {b} l u
  let D : Finset ℤ :=
    OAI.Erdos970.ErdosCoprimeResidueInterval.realCoprimeResidues 1 (m * d) A l u
  have hsets : C.filter (fun n : ℤ => (d : ℤ) ∣ n) = D := by
    ext n
    simp only [C, D, A, Finset.mem_filter]
    rw [OAI.Erdos970.ErdosCoprimeResidueInterval.mem_realCoprimeResidues,
      OAI.Erdos970.ErdosCoprimeResidueInterval.mem_realCoprimeResidues]
    simp only [Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hnl, hnr, _, hmb⟩, hdiv⟩
      exact ⟨hnl, hnr, by simp, (crtResidue_class_iff m d b hm hd hcop n).2 ⟨hmb, hdiv⟩⟩
    · rintro ⟨hnl, hnr, _, hcrt⟩
      have hmbdiv := (crtResidue_class_iff m d b hm hd hcop n).1 hcrt
      exact ⟨⟨hnl, hnr, by simp, hmbdiv.1⟩, hmbdiv.2⟩
  have hcnt := OAI.Erdos970.ErdosCoprimeResidueInterval.real_coprime_residue_count
    1 (m * d) (by norm_num) (Nat.mul_pos hm hd) (by simp) A l u hlu
  have hAcard : (A.card : ℝ) = 1 := by simp [A]
  have hmain : (u - l) * ((Nat.totient 1 : ℝ) / (1 : ℝ)) *
      ((A.card : ℝ) / ((m * d : ℕ) : ℝ)) = (u - l) / (m * d) := by
    simp [hAcard]
    push_cast
    ring
  have hcnt' : |((D.card : ℝ) - (u - l) / (m * d))| ≤ 2 := by
    rw [← hmain]
    simpa [A, hAcard] using hcnt
  calc
    _ = |(D.card : ℝ) - (u - l) / (m * d)| := by rw [hsets]
    _ ≤ 2 := hcnt'

theorem rough_sieve_residue_class_bound (m : ℕ) (b : ZMod m)
    (P : Finset ℕ) (v s l u : ℝ)
    (hm : 0 < m) (hl : 0 ≤ l) (hlu : l ≤ u)
    (hv : 2 ≤ v) (hs : 480024 ≤ s)
    (hprime : ∀ p ∈ P, p.Prime) (hsize : ∀ p ∈ P, (p : ℝ) ≤ v)
    (hcop : ∀ p ∈ P, Nat.Coprime m p) :
    |(((OAI.Erdos970.ErdosCoprimeResidueInterval.realCoprimeResidues 1 m {b} l u).filter
        (fun n : ℤ => ∀ p ∈ P, ¬ (p : ℤ) ∣ n)).card : ℝ) -
        ((u - l) / (m : ℝ)) * ∏ p ∈ P, (1 - (p : ℝ)⁻¹)| ≤
      ((u - l) / (m : ℝ)) * (∏ p ∈ P, (1 - (p : ℝ)⁻¹)) *
          Real.exp (-s / 96) + 4 * v ^ s := by
  classical
  let C : Finset ℤ :=
    OAI.Erdos970.ErdosCoprimeResidueInterval.realCoprimeResidues 1 m {b} l u
  let hit : ℕ → ℤ → Prop := fun p n => (p : ℤ) ∣ n
  let weight : ℤ → ℝ := fun _ => 1
  let X : ℝ := (u - l) / (m : ℝ)
  let g : ℕ → ℝ := fun p => (p : ℝ)⁻¹
  let V : ℝ := ∏ p ∈ P, (1 - (p : ℝ)⁻¹)
  let R : Finset ℤ := C.filter fun n => ∀ p ∈ P, ¬ hit p n
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hX : 0 ≤ X := by
    dsimp [X]
    apply div_nonneg _ hmR.le
    linarith
  have hweight : ∀ n ∈ C, 0 ≤ weight n := by intro n hn; simp [weight]
  have hprimeR : ∀ p ∈ P, p.Prime := hprime
  have hsizeR : ∀ p ∈ P, (p : ℝ) ≤ v := hsize
  have hg0 : ∀ p ∈ P, 0 ≤ g p := by intro p hp; simp [g, inv_nonneg]
  have hdim : ∀ p ∈ P, g p ≤ 2 / p := by
    intro p hp
    dsimp [g]
    simpa only [one_div] using
      div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) (Nat.cast_nonneg p)
  have htwo : 2 ∈ P → g 2 ≤ 1 / 2 := by
    intro h2
    simp [g]
  have hfund := OAI.Erdos970.NumberTheoryLean.RealFundamentalSieve.fundamental_lemma
    C weight hweight hit v s P X g hv hs hX hprimeR hsizeR hg0 hdim htwo
  have hcount :
      (∑ n ∈ C, weight n * OAI.Erdos970.NumberTheoryLean.BonferroniBlocks.survives P
        (fun p => hit p n)) = (R.card : ℝ) := by
    calc
      _ = ∑ n ∈ C, if n ∈ R then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro n hn
        simp [R, weight, OAI.Erdos970.NumberTheoryLean.BonferroniBlocks.survives, hn]
      _ = R.card := by
        have hfilter : C.filter (fun n => n ∈ R) = R := by
          ext n
          simp [R]
        rw [Finset.sum_boole]
        exact_mod_cast congrArg Finset.card hfilter
  have hD : Squarefree (∏ p ∈ P, p) :=
    OAI.Erdos970.NumberTheoryLean.IntervalBoundingSieve.squarefree_primeSet_product P hprime
  have hcopD : Nat.Coprime m (∏ p ∈ P, p) := by
    rw [Nat.coprime_prod_right_iff]
    exact hcop
  have hrem (d : ℕ) (hd : d ∈ OAI.Erdos970.NumberTheoryLean.RealFundamentalSieve.levelDivisors P v s) :
      |OAI.Erdos970.NumberTheoryLean.FundamentalBlockEstimate.integerRemainder
        C weight hit X g d| ≤ 2 := by
    let D : ℕ := ∏ p ∈ P, p
    have hddiv : d ∣ D := by
      exact Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
    have hdSq : Squarefree d := hD.squarefree_of_dvd (by dsimp [D] at hddiv ⊢; exact hddiv)
    have hcopd : Nat.Coprime m d := Nat.Coprime.coprime_dvd_right hddiv hcopD
    have hdpos : 0 < d := Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1
    have hsub : d.primeFactors ⊆ P := by
      rw [← Nat.primeFactors_prod hprime]
      exact Nat.primeFactors_mono hddiv hD.ne_zero
    have hprod : (∏ p ∈ d.primeFactors, p) = d :=
      Nat.prod_primeFactors_of_squarefree hdSq
    have hprodReal : (∏ p ∈ d.primeFactors, (p : ℝ)) = (d : ℝ) := by
      rw [← Nat.cast_prod]
      exact_mod_cast hprod
    have hpred (n : ℤ) :
        (∀ p ∈ d.primeFactors, (p : ℤ) ∣ n) ↔ (d : ℤ) ∣ n := by
      simpa only [Int.natCast_dvd] using
        (OAI.Erdos970.NumberTheoryLean.SmallSieveFinite.squarefree_dvd_iff_primeFactors
          hdSq).symm
    have hmassPred (n : ℤ) :
        OAI.Erdos970.NumberTheoryLean.BonferroniBlocks.intersectionValue d.primeFactors
          (fun p => hit p n) = if (d : ℤ) ∣ n then 1 else 0 := by
      unfold OAI.Erdos970.NumberTheoryLean.BonferroniBlocks.intersectionValue
      dsimp [hit]
      by_cases hp : ∀ p ∈ d.primeFactors, (p : ℤ) ∣ n
      · have hd : (d : ℤ) ∣ n := (hpred n).mp hp
        rw [if_pos hp, if_pos hd]
      · have hd : ¬ (d : ℤ) ∣ n := fun h => hp ((hpred n).mpr h)
        rw [if_neg hp, if_neg hd]
    have hmass : OAI.Erdos970.NumberTheoryLean.BonferroniBlocks.intersectionMass
        C weight hit d.primeFactors =
          ((C.filter fun n => (d : ℤ) ∣ n).card : ℝ) := by
      unfold OAI.Erdos970.NumberTheoryLean.BonferroniBlocks.intersectionMass
      simp_rw [weight, one_mul, hmassPred]
      rw [Finset.sum_boole]
    have hcountD := real_interval_residue_divisor_count m d b hm hdpos hcopd l u hlu
    have hprodInv : (∏ p ∈ d.primeFactors, ((p : ℝ)⁻¹)) = (d : ℝ)⁻¹ := by
      calc
        _ = (∏ p ∈ d.primeFactors, (p : ℝ))⁻¹ := by rw [Finset.prod_inv_distrib]
        _ = (d : ℝ)⁻¹ := by rw [hprodReal]
    have hmodel : X * (∏ p ∈ d.primeFactors, g p) =
        (u - l) / ((m * d : ℕ) : ℝ) := by
      dsimp [X, g]
      rw [hprodInv]
      field_simp [ne_of_gt hmR, (show (0 : ℝ) < d by exact_mod_cast hdpos)]
      push_cast
      ring_nf
    unfold OAI.Erdos970.NumberTheoryLean.FundamentalBlockEstimate.integerRemainder
      OAI.Erdos970.NumberTheoryLean.BonferroniBlocks.intersectionRemainder
    rw [hmass, hmodel]
    simpa [C, Nat.cast_mul] using hcountD
  have hlevel :
      (∑ d ∈ OAI.Erdos970.NumberTheoryLean.RealFundamentalSieve.levelDivisors P v s,
        |OAI.Erdos970.NumberTheoryLean.FundamentalBlockEstimate.integerRemainder
          C weight hit X g d|) ≤ 4 * v ^ s := by
    calc
      _ ≤ ∑ _d ∈ OAI.Erdos970.NumberTheoryLean.RealFundamentalSieve.levelDivisors P v s,
          (2 : ℝ) := by
        apply Finset.sum_le_sum
        intro d hd
        exact hrem d hd
      _ = 2 * ((OAI.Erdos970.NumberTheoryLean.RealFundamentalSieve.levelDivisors P v s).card : ℝ) := by
        simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ 4 * v ^ s := by
        have hc := OAI.Erdos970.NumberTheoryLean.SmallSieveFinite.realLevelDivisors_card_le
          P v s (by linarith)
        calc
          _ ≤ 2 * (v ^ s) := mul_le_mul_of_nonneg_left hc (by norm_num)
          _ ≤ 4 * (v ^ s) := by
            have hvpow : 0 ≤ v ^ s := Real.rpow_nonneg (by linarith : 0 ≤ v) s
            nlinarith [hvpow]
  have hfund' : |(R.card : ℝ) - X * V| ≤ X * V * Real.exp (-s / 96) +
      ∑ d ∈ OAI.Erdos970.NumberTheoryLean.RealFundamentalSieve.levelDivisors P v s,
        |OAI.Erdos970.NumberTheoryLean.FundamentalBlockEstimate.integerRemainder
          C weight hit X g d| := by
    simpa [R, X, V, weight, hit, OAI.Erdos970.NumberTheoryLean.BonferroniBlocks.survives] using hfund
  have hFinal : |(R.card : ℝ) - X * V| ≤ X * V * Real.exp (-s / 96) + 4 * v ^ s := by
    calc
      _ ≤ X * V * Real.exp (-s / 96) +
          ∑ d ∈ OAI.Erdos970.NumberTheoryLean.RealFundamentalSieve.levelDivisors P v s,
            |OAI.Erdos970.NumberTheoryLean.FundamentalBlockEstimate.integerRemainder C weight hit X g d| := hfund'
      _ ≤ X * V * Real.exp (-s / 96) + 4 * v ^ s := by
        calc
          _ = (∑ d ∈ OAI.Erdos970.NumberTheoryLean.RealFundamentalSieve.levelDivisors P v s,
              |OAI.Erdos970.NumberTheoryLean.FundamentalBlockEstimate.integerRemainder
                C weight hit X g d|) + X * V * Real.exp (-s / 96) := by ring
          _ ≤ 4 * v ^ s + X * V * Real.exp (-s / 96) := by nlinarith [hlevel]
          _ = _ := by ring
  simpa [R, C, X, V] using hFinal

end ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0
