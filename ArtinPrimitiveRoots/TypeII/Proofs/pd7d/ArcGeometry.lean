import ArtinPrimitiveRoots.TypeII.PD.Defs

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical
set_option autoImplicit false

noncomputable def pd7dReducedPairs (M : ℝ) : Finset (ℕ × ℕ) :=
  ((Finset.range (⌊M⌋₊ + 1)).product (Finset.range (⌊M⌋₊ + 1))).filter
    (fun p => 1 ≤ p.2 ∧ p.1 < p.2 ∧ Nat.Coprime p.1 p.2)

lemma pd7dReducedPairs_mem (M : ℝ) (p : ℕ × ℕ) :
    p ∈ pd7dReducedPairs M ↔ p.1 ≤ ⌊M⌋₊ ∧ p.2 ≤ ⌊M⌋₊ ∧
      1 ≤ p.2 ∧ p.1 < p.2 ∧ Nat.Coprime p.1 p.2 := by
  constructor
  · intro hp
    obtain ⟨hpProd, hrest⟩ := Finset.mem_filter.mp hp
    obtain ⟨hh, hk⟩ := Finset.mem_product.mp hpProd
    exact ⟨Nat.lt_succ_iff.mp (Finset.mem_range.mp hh),
      Nat.lt_succ_iff.mp (Finset.mem_range.mp hk), hrest⟩
  · rintro ⟨hh, hk, hrest⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hh),
      Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk)⟩, hrest⟩

lemma pd7dReducedPairs_card_le (M : ℝ) (hM : 0 ≤ M) :
    ((pd7dReducedPairs M).card : ℝ) ≤ M ^ 2 := by
  let N := ⌊M⌋₊
  let S := pd7dReducedPairs M
  let T := (Finset.range N).product (Finset.range N)
  have hmap : Set.MapsTo (fun p : ℕ × ℕ => (p.1, p.2 - 1)) S T := by
    intro p hp
    obtain ⟨hp₁, hp₂, hk, hh, _⟩ := (pd7dReducedPairs_mem M p).1 hp
    apply Finset.mem_product.mpr
    constructor <;> apply Finset.mem_range.mpr <;> dsimp [N] <;> omega
  have hinj : (S : Set (ℕ × ℕ)).InjOn (fun p : ℕ × ℕ => (p.1, p.2 - 1)) := by
    intro p hp q hq heq
    have hk := ((pd7dReducedPairs_mem M p).1 hp).2.2.1
    have hk' := ((pd7dReducedPairs_mem M q).1 hq).2.2.1
    have hfst := congrArg Prod.fst heq
    have hsnd := congrArg Prod.snd heq
    refine Prod.ext (by simpa using hfst) ?_
    dsimp only at hsnd
    omega
  have hcard : S.card ≤ N ^ 2 := by
    have hh := Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => (p.1, p.2 - 1)) hmap hinj
    simpa [T, Finset.card_product, Finset.card_range, pow_two] using hh
  have hcardR : (S.card : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hcard
  have hN : (N : ℝ) ≤ M := Nat.floor_le hM
  exact hcardR.trans (pow_le_pow_left₀ (by positivity) hN 2)

lemma pd7d_reduced_fraction_unique (h k h' k' : ℕ)
    (hk : 0 < k) (hk' : 0 < k') (hcop : Nat.Coprime h k) (hcop' : Nat.Coprime h' k')
    (heq : h * k' = h' * k) : h = h' ∧ k = k' := by
  have hkk' : k ∣ k' := hcop.symm.dvd_of_dvd_mul_left (by
    rw [heq]
    exact dvd_mul_left _ _)
  have hk'k : k' ∣ k := hcop'.symm.dvd_of_dvd_mul_left (by
    rw [← heq]
    exact dvd_mul_left _ _)
  have hkeq : k = k' := Nat.dvd_antisymm hkk' hk'k
  refine ⟨?_, hkeq⟩
  rw [← hkeq] at heq
  exact Nat.eq_of_mul_eq_mul_right hk heq

lemma pd7d_reduced_fraction_distance (h k h' k' : ℕ)
    (hk : 0 < k) (hk' : 0 < k') (hh : h < k) (hh' : h' < k')
    (hcop : Nat.Coprime h k) (hcop' : Nat.Coprime h' k')
    (hne : (h, k) ≠ (h', k')) (z : ℤ) :
    1 / ((k : ℝ) * k') ≤ |(h : ℝ) / k - (h' : ℝ) / k' - (z : ℝ)| := by
  have hkp : 0 < (k : ℝ) := by exact_mod_cast hk
  have hk'p : 0 < (k' : ℝ) := by exact_mod_cast hk'
  have hden : 0 < (k : ℝ) * k' := mul_pos hkp hk'p
  let d : ℤ := (h : ℤ) * k' - (h' : ℤ) * k - z * k * k'
  have hscale : ((h : ℝ) / k - (h' : ℝ) / k' - (z : ℝ)) * ((k : ℝ) * k') = (d : ℝ) := by
    dsimp [d]
    push_cast
    field_simp
    <;> ring
  have hd : d ≠ 0 := by
    intro hd
    have hdelta : (h : ℝ) / k - (h' : ℝ) / k' - (z : ℝ) = 0 := by
      rw [hd, Int.cast_zero] at hscale
      exact (mul_eq_zero.mp hscale).resolve_right (ne_of_gt hden)
    have hr : 0 ≤ (h : ℝ) / k ∧ (h : ℝ) / k < 1 :=
      ⟨by positivity, (div_lt_one hkp).2 (by exact_mod_cast hh)⟩
    have hr' : 0 ≤ (h' : ℝ) / k' ∧ (h' : ℝ) / k' < 1 :=
      ⟨by positivity, (div_lt_one hk'p).2 (by exact_mod_cast hh')⟩
    have hzlo : (-1 : ℝ) < (z : ℝ) := by linarith [hr.1, hr.2, hr'.1, hr'.2]
    have hzhi : (z : ℝ) < 1 := by linarith [hr.1, hr.2, hr'.1, hr'.2]
    have hzloI : (-1 : ℤ) < z := by exact_mod_cast hzlo
    have hzhiI : z < (1 : ℤ) := by exact_mod_cast hzhi
    have hz : z = 0 := by omega
    rw [hz, Int.cast_zero] at hdelta
    have hcross : (h : ℝ) * k' = (h' : ℝ) * k := by
      field_simp [ne_of_gt hkp, ne_of_gt hk'p] at hdelta
      nlinarith
    have hcrossN : h * k' = h' * k := by exact_mod_cast hcross
    obtain ⟨hheq, hkeq⟩ := pd7d_reduced_fraction_unique h k h' k' hk hk' hcop hcop' hcrossN
    exact hne (Prod.ext hheq hkeq)
  have hdAbs : (1 : ℤ) ≤ |d| := by
    have hh : (0 : ℤ) < |d| := abs_pos.mpr hd
    omega
  have hdAbsR : (1 : ℝ) ≤ |(d : ℝ)| := by exact_mod_cast hdAbs
  have habs := congrArg abs hscale
  rw [abs_mul, abs_of_pos hden] at habs
  apply (div_le_iff₀ hden).2
  rw [habs]
  exact hdAbsR

lemma pd7d_reduced_pair_circle_separation (M : ℝ) (hM : 1 ≤ M)
    (p q : ℕ × ℕ) (hp : p ∈ pd7dReducedPairs M) (hq : q ∈ pd7dReducedPairs M)
    (hne : p ≠ q) (z : ℤ) :
    1 / M ^ 2 ≤ |(p.1 : ℝ) / p.2 - (q.1 : ℝ) / q.2 - (z : ℝ)| := by
  obtain ⟨_, hp₂, hpk, hph, hpcop⟩ := (pd7dReducedPairs_mem M p).1 hp
  obtain ⟨_, hq₂, hqk, hqh, hqcop⟩ := (pd7dReducedPairs_mem M q).1 hq
  have hpkPos : 0 < (p.2 : ℝ) := by exact_mod_cast hpk
  have hqkPos : 0 < (q.2 : ℝ) := by exact_mod_cast hqk
  have hpM : (p.2 : ℝ) ≤ M := (by exact_mod_cast hp₂ : (p.2 : ℝ) ≤ (⌊M⌋₊ : ℝ)) |>.trans (Nat.floor_le (by linarith))
  have hqM : (q.2 : ℝ) ≤ M := (by exact_mod_cast hq₂ : (q.2 : ℝ) ≤ (⌊M⌋₊ : ℝ)) |>.trans (Nat.floor_le (by linarith))
  have hprod : (p.2 : ℝ) * q.2 ≤ M ^ 2 := by
    have hh := mul_le_mul hpM hqM hqkPos.le (by linarith : 0 ≤ M)
    simpa [pow_two] using hh
  calc
    _ ≤ 1 / ((p.2 : ℝ) * q.2) := one_div_le_one_div_of_le (mul_pos hpkPos hqkPos) hprod
    _ ≤ _ := pd7d_reduced_fraction_distance p.1 p.2 q.1 q.2 hpk hqk hph hqh hpcop hqcop hne z

def pd7dPairArc (M Y : ℝ) (p : ℕ × ℕ) (theta : ℝ) : Prop :=
  ∃ z : ℤ, |theta - (p.1 : ℝ) / p.2 - (z : ℝ)| ≤ 2 * M / Y

lemma pd7d_pair_arcs_disjoint (M Y : ℝ) (hM : 1 ≤ M) (hY : 4 * M ^ 3 < Y)
    (p q : ℕ × ℕ) (hp : p ∈ pd7dReducedPairs M) (hq : q ∈ pd7dReducedPairs M)
    (hne : p ≠ q) : Disjoint {theta : ℝ | pd7dPairArc M Y p theta}
      {theta : ℝ | pd7dPairArc M Y q theta} := by
  have hMp : 0 < M := by linarith
  have hYp : 0 < Y := lt_trans (by positivity) hY
  have hsmall : 4 * M / Y < 1 / M ^ 2 := by
    apply (div_lt_div_iff₀ hYp (sq_pos_of_pos hMp)).2
    nlinarith
  apply Set.disjoint_left.mpr
  intro theta hpθ hqθ
  obtain ⟨z₀, hz₀⟩ := hpθ
  obtain ⟨z₁, hz₁⟩ := hqθ
  have hdiff : |(p.1 : ℝ) / p.2 - (q.1 : ℝ) / q.2 - ((z₁ - z₀ : ℤ) : ℝ)| ≤ 4 * M / Y := by
    calc
      _ = |(theta - (q.1 : ℝ) / q.2 - (z₁ : ℝ)) -
          (theta - (p.1 : ℝ) / p.2 - (z₀ : ℝ))| := by congr 1; push_cast; ring
      _ ≤ |theta - (q.1 : ℝ) / q.2 - (z₁ : ℝ)| +
          |theta - (p.1 : ℝ) / p.2 - (z₀ : ℝ)| := abs_sub _ _
      _ ≤ 2 * M / Y + 2 * M / Y := add_le_add hz₁ hz₀
      _ = _ := by ring
  have hsep := pd7d_reduced_pair_circle_separation M hM p q hp hq hne (z₁ - z₀)
  exact not_lt_of_ge (hsep.trans hdiff) hsmall

end ArtinPrimitiveRoots.TypeII.PD
