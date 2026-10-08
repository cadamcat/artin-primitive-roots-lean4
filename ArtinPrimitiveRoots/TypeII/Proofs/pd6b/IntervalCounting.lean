import ArtinPrimitiveRoots.TypeII.PD.Physical

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical

/-- A finite set of natural numbers in a real interval has at most its length plus two entries. -/
theorem natInterval_card_le (T : Finset ℕ) (lo hi W : ℝ) (hW : 0 ≤ W)
    (hwidth : hi - lo ≤ W) (hT : ∀ n ∈ T, lo ≤ (n : ℝ) ∧ (n : ℝ) ≤ hi) :
    T.card ≤ ⌈W⌉₊ + 2 := by
  let I : Finset ℤ := Finset.Icc ⌈lo⌉ ⌊hi⌋
  have hmap : Set.MapsTo (fun n : ℕ => (n : ℤ)) (T : Set ℕ) (I : Set ℤ) := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨Int.ceil_le.mpr (by simpa using (hT n hn).1),
      Int.le_floor.mpr (by simpa using (hT n hn).2)⟩
  have hinj : (T : Set ℕ).InjOn (fun n : ℕ => (n : ℤ)) := fun n hn m hm h => Int.ofNat_inj.mp h
  have hcard : T.card ≤ I.card := Finset.card_le_card_of_injOn _ hmap hinj
  have hceil := Int.le_ceil lo
  have hfloor := Int.floor_le hi
  have hWceil := Nat.le_ceil W
  have hdiff : ((⌊hi⌋ + 1 - ⌈lo⌉ : ℤ) : ℝ) ≤ ((⌈W⌉₊ + 2 : ℕ) : ℝ) := by
    push_cast
    linarith
  have hdiffZ : (⌊hi⌋ + 1 - ⌈lo⌉ : ℤ) ≤ ((⌈W⌉₊ + 2 : ℕ) : ℤ) := by exact_mod_cast hdiff
  have hI : I.card ≤ ⌈W⌉₊ + 2 := by
    simpa only [I, Int.card_Icc] using Int.toNat_le.mpr hdiffZ
  exact hcard.trans hI

/-- The narrow comparison relation has bounded row and column degrees. -/
theorem comparisonRelation_row_card_le (Z : Finset ℕ) (a b k : ℕ) (Y R : ℝ)
    (hY : 0 < Y) (hR : 0 ≤ R) (ha : Y ≤ (a : ℝ)) :
    (Z.filter fun l : ℕ => |(b : ℝ) * k - (a : ℝ) * l| ≤ R * Y).card ≤ ⌈2 * R⌉₊ + 2 := by
  have haPos : 0 < (a : ℝ) := hY.trans_le ha
  apply natInterval_card_le _ (((b : ℝ) * k - R * Y) / a)
    (((b : ℝ) * k + R * Y) / a) (2 * R) (by positivity)
  · have hfrac : 2 * R * Y / (a : ℝ) ≤ 2 * R := by
      apply (div_le_iff₀ haPos).mpr
      exact mul_le_mul_of_nonneg_left ha (by positivity)
    have heq : ((b : ℝ) * k + R * Y) / a - ((b : ℝ) * k - R * Y) / a =
        2 * R * Y / a := by ring
    rw [heq]
    exact hfrac
  · intro l hl
    have h := (Finset.mem_filter.mp hl).2
    constructor
    · apply (div_le_iff₀ haPos).mpr
      linarith [(abs_le.mp h).2]
    · apply (le_div_iff₀ haPos).mpr
      linarith [(abs_le.mp h).1]

end ArtinPrimitiveRoots.TypeII.PD
