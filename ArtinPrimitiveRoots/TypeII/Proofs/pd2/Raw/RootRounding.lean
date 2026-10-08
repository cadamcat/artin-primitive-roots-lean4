import ArtinPrimitiveRoots.TypeII.Proofs.pd2.Raw.RootDensityCount

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
set_option maxHeartbeats 1000000

noncomputable def pd2a_intervalStart (A : ℝ) : ℕ := ⌈A⌉₊
noncomputable def pd2a_intervalLength (A B : ℝ) : ℕ := ⌊B⌋₊ + 1 - ⌈A⌉₊

lemma pd2a_interval_ceil_le_floor_succ (A B : ℝ) (hA : 0 ≤ A) (hAB : A ≤ B) :
    ⌈A⌉₊ ≤ ⌊B⌋₊ + 1 := by
  apply Nat.ceil_le.mpr
  have hB := Nat.lt_floor_add_one B
  push_cast
  linarith

lemma pd2a_intervalLength_error (A B : ℝ) (hA : 0 ≤ A) (hAB : A ≤ B) :
    |(pd2a_intervalLength A B : ℝ) - (B - A)| ≤ 1 := by
  have hB : 0 ≤ B := hA.trans hAB
  have hCeilLo : A ≤ (⌈A⌉₊ : ℝ) := Nat.le_ceil A
  have hCeilHi : (⌈A⌉₊ : ℝ) < A + 1 := Nat.ceil_lt_add_one hA
  have hFloorLo : B < (⌊B⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one B
  have hFloorHi : (⌊B⌋₊ : ℝ) ≤ B := Nat.floor_le hB
  unfold pd2a_intervalLength
  rw [Nat.cast_sub (pd2a_interval_ceil_le_floor_succ A B hA hAB), Nat.cast_add, Nat.cast_one, abs_le]
  constructor <;> linarith

lemma pd2a_interval_indices (A B : ℝ) (hA : 0 ≤ A) (hAB : A ≤ B) (i : ℕ) :
    i ∈ Finset.range (pd2a_intervalLength A B) →
      A ≤ ((pd2a_intervalStart A + i : ℕ) : ℝ) ∧ ((pd2a_intervalStart A + i : ℕ) : ℝ) ≤ B := by
  intro hi
  have hFloorCeil := pd2a_interval_ceil_le_floor_succ A B hA hAB
  have hib : i < ⌊B⌋₊ + 1 - ⌈A⌉₊ := Finset.mem_range.mp hi
  have hnUpper : ⌈A⌉₊ + i ≤ ⌊B⌋₊ := by omega
  constructor
  · have hCeil := Nat.le_ceil A
    dsimp [pd2a_intervalStart]
    push_cast
    linarith [show (0 : ℝ) ≤ i from Nat.cast_nonneg i]
  · exact (Nat.le_floor_iff (hA.trans hAB)).mp hnUpper

lemma pd2a_interval_index_exists (A B : ℝ) (hA : 0 ≤ A) (hAB : A ≤ B) (n : ℕ)
    (hLo : A ≤ (n : ℝ)) (hHi : (n : ℝ) ≤ B) :
    ∃ i ∈ Finset.range (pd2a_intervalLength A B), n = pd2a_intervalStart A + i := by
  have hnLo : ⌈A⌉₊ ≤ n := Nat.ceil_le.mpr hLo
  have hnHi : n ≤ ⌊B⌋₊ := (Nat.le_floor_iff (hA.trans hAB)).mpr hHi
  refine ⟨n - ⌈A⌉₊, Finset.mem_range.mpr ?_, ?_⟩
  · dsimp [pd2a_intervalLength]
    omega
  · dsimp [pd2a_intervalStart]
    omega

noncomputable def pd2a_rootCStart (u : ℕ) (l : ℝ) : ℕ := ⌈l * u⌉₊
noncomputable def pd2a_rootCLength (u : ℕ) (l r : ℝ) : ℕ :=
  min ⌊r * u⌋₊ (u - 1) + 1 - ⌈l * u⌉₊

lemma pd2a_rootCLength_bounds (u : ℕ) (hu : 0 < u) (l r : ℝ)
    (hl : 0 ≤ l) (hlr : l ≤ r) (hr : r ≤ 1) :
    pd2a_rootCLength u l r ≤ u ∧
      |(pd2a_rootCLength u l r : ℝ) - (u : ℝ) * (r - l)| ≤ 2 := by
  have huR : 0 < (u : ℝ) := by exact_mod_cast hu
  have hA : 0 ≤ l * (u : ℝ) := mul_nonneg hl huR.le
  have hAB : l * (u : ℝ) ≤ r * u := mul_le_mul_of_nonneg_right hlr huR.le
  have hceil : ⌈l * (u : ℝ)⌉₊ ≤ ⌊r * u⌋₊ + 1 := pd2a_interval_ceil_le_floor_succ _ _ hA hAB
  have hceilU : ⌈l * (u : ℝ)⌉₊ ≤ u := Nat.ceil_le.mpr (by nlinarith)
  have hfloorU : ⌊r * (u : ℝ)⌋₊ ≤ u := by
    have hbound : r * (u : ℝ) ≤ (u : ℝ) := by nlinarith
    simpa only [Nat.floor_natCast] using Nat.floor_le_floor hbound
  have hbase := pd2a_intervalLength_error (l * u) (r * u) hA hAB
  have hnat : pd2a_rootCLength u l r ≤ u ∧
      pd2a_intervalLength (l * u) (r * u) - pd2a_rootCLength u l r ≤ 1 ∧
        pd2a_rootCLength u l r ≤ pd2a_intervalLength (l * u) (r * u) := by
    dsimp [pd2a_rootCLength, pd2a_intervalLength]
    omega
  refine ⟨hnat.1, ?_⟩
  have hdiff : (pd2a_intervalLength (l * u) (r * u) : ℝ) - (pd2a_rootCLength u l r : ℝ) ≤ 1 := by
    rw [← Nat.cast_sub hnat.2.2]
    exact_mod_cast hnat.2.1
  have hle : (pd2a_rootCLength u l r : ℝ) ≤ pd2a_intervalLength (l * u) (r * u) := by exact_mod_cast hnat.2.2
  rw [abs_le] at hbase ⊢
  constructor <;> nlinarith

lemma pd2a_root_c_indices (u c : ℕ) (hu : 0 < u) (l r : ℝ)
    (hl : 0 ≤ l) (hlr : l ≤ r) (hr : r ≤ 1) :
    (c < u ∧ l ≤ (c : ℝ) / u ∧ (c : ℝ) / u ≤ r) ↔
      ∃ i ∈ Finset.range (pd2a_rootCLength u l r), c = pd2a_rootCStart u l + i := by
  have huR : 0 < (u : ℝ) := by exact_mod_cast hu
  have hr0 : 0 ≤ r := hl.trans hlr
  constructor
  · rintro ⟨hcu, hcl, hcr⟩
    have hLo : ⌈l * (u : ℝ)⌉₊ ≤ c := Nat.ceil_le.mpr ((le_div_iff₀ huR).mp hcl)
    have hHi : c ≤ ⌊r * (u : ℝ)⌋₊ := (Nat.le_floor_iff (mul_nonneg hr0 huR.le)).mpr ((div_le_iff₀ huR).mp hcr)
    refine ⟨c - ⌈l * (u : ℝ)⌉₊, Finset.mem_range.mpr ?_, ?_⟩
    · dsimp [pd2a_rootCLength]
      omega
    · dsimp [pd2a_rootCStart]
      omega
  · rintro ⟨i, hi, rfl⟩
    have hi' := Finset.mem_range.mp hi
    have hNat : pd2a_rootCStart u l + i ≤ min ⌊r * (u : ℝ)⌋₊ (u - 1) := by
      dsimp [pd2a_rootCLength, pd2a_rootCStart] at hi' ⊢
      omega
    have hcu : pd2a_rootCStart u l + i < u := by
      have hle := hNat.trans (min_le_right _ _)
      omega
    have hLo : l * (u : ℝ) ≤ ((pd2a_rootCStart u l + i : ℕ) : ℝ) := by
      have hceil := Nat.le_ceil (l * (u : ℝ))
      dsimp [pd2a_rootCStart]
      push_cast
      linarith [show (0 : ℝ) ≤ i from Nat.cast_nonneg i]
    have hHi : ((pd2a_rootCStart u l + i : ℕ) : ℝ) ≤ r * u :=
      (Nat.le_floor_iff (mul_nonneg hr0 huR.le)).mp (hNat.trans (min_le_left _ _))
    exact ⟨hcu, (le_div_iff₀ huR).mpr hLo, (div_le_iff₀ huR).mpr hHi⟩

end ArtinPrimitiveRoots.TypeII.PD
