import ArtinPrimitiveRoots.TypeII.PD.RootReplacement

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical

noncomputable section

/-- Every neighboring vector has its sheared first coordinate in a fixed short interval. -/
theorem envBox_tau_bounds (S : PDScale) (w : ArchRoot) (z : ℤ × ℤ)
    (hU : 0 < S.U) (hw : w.InRegion S) (hz : envBox S w z) :
    (1 / 16 : ℝ) ≤ w.tau z ∧ w.tau z ≤ 16 := by
  have hwu : 0 < w.u := lt_of_lt_of_le hU hw.1
  constructor
  · calc
      (1 / 16 : ℝ) ≤ S.U / w.u := by
        apply (le_div_iff₀ hwu).2
        linarith [hw.2.1]
      _ ≤ w.tau z := (div_le_iff₀ hwu).2 (by simpa only [mul_comm] using hz.1)
  · calc
      w.tau z ≤ 16 * S.U / w.u := (le_div_iff₀ hwu).2 (by simpa only [mul_comm] using hz.2.1)
      _ ≤ 16 := by
        apply (div_le_iff₀ hwu).2
        linarith [hw.1]

/-- Integer first coordinates allowed by the fixed second coordinate and root ratio. -/
def neighborFirstCoordinates (z₂ : ℤ) (r : ℝ) : Finset ℤ :=
  Finset.Icc ⌈(1 / 16 : ℝ) - r * (z₂ : ℝ)⌉ ⌊16 - r * (z₂ : ℝ)⌋

theorem neighborFirstCoordinates_card_le (z₂ : ℤ) (r : ℝ) :
    (neighborFirstCoordinates z₂ r).card ≤ 17 := by
  have hceil := Int.le_ceil ((1 / 16 : ℝ) - r * (z₂ : ℝ))
  have hfloor := Int.floor_le (16 - r * (z₂ : ℝ))
  have hdiffR :
      ((⌊16 - r * (z₂ : ℝ)⌋ - ⌈(1 / 16 : ℝ) - r * (z₂ : ℝ)⌉ + 1 : ℤ) : ℝ) ≤ 17 := by
    push_cast
    linarith
  have hdiffZ :
      (⌊16 - r * (z₂ : ℝ)⌋ - ⌈(1 / 16 : ℝ) - r * (z₂ : ℝ)⌉ + 1 : ℤ) ≤ 17 := by
    exact_mod_cast hdiffR
  have hdiffZ' :
      (⌊16 - r * (z₂ : ℝ)⌋ + 1 - ⌈(1 / 16 : ℝ) - r * (z₂ : ℝ)⌉ : ℤ) ≤ 17 := by
    omega
  simpa only [neighborFirstCoordinates, Int.card_Icc] using (Int.toNat_le.mpr hdiffZ')

/-- For each determinant there are at most seventeen candidate first coordinates. -/
theorem envBox_fixed_second_card_le (S : PDScale) (w : ArchRoot) (z₂ : ℤ)
    (hU : 0 < S.U) (hw : w.InRegion S) (Z : Finset ℤ)
    (hZ : ∀ z₁ ∈ Z, envBox S w (z₁, z₂)) : Z.card ≤ 17 := by
  have hsub : Z ⊆ neighborFirstCoordinates z₂ w.r := by
    intro z₁ hz₁
    have ht := envBox_tau_bounds S w (z₁, z₂) hU hw (hZ z₁ hz₁)
    simp only [neighborFirstCoordinates, Finset.mem_Icc, Int.ceil_le, Int.le_floor]
    dsimp [ArchRoot.tau] at ht
    constructor <;> linarith [ht.1, ht.2]
  exact (Finset.card_le_card hsub).trans (neighborFirstCoordinates_card_le z₂ w.r)

/-- Raw targets have a fixed determinant and at most seventeen first coordinates. -/
theorem envBox_rawTargets_card_le (S : PDScale) (w : ArchRoot) (hU : 0 < S.U)
    (hw : w.InRegion S) (Z : Finset (ℤ × ℤ)) (d : ℤ) :
    (Z.filter fun z => z.2 = d ∧ envBox S w z).card ≤ 17 := by
  let T := Z.filter fun z => z.2 = d ∧ envBox S w z
  have hinj : (T : Set (ℤ × ℤ)).InjOn Prod.fst := by
    intro z hz v hv hfirst
    exact Prod.ext hfirst ((Finset.mem_filter.mp hz).2.1.trans (Finset.mem_filter.mp hv).2.1.symm)
  have hfirst (z₁ : ℤ) (hz₁ : z₁ ∈ T.image Prod.fst) : envBox S w (z₁, d) := by
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hz₁
    have hz' := (Finset.mem_filter.mp hz).2
    have hbox := hz'.2
    change envBox S w (z.1, z.2) at hbox
    rwa [hz'.1] at hbox
  have hcount := envBox_fixed_second_card_le S w d hU hw (T.image Prod.fst) hfirst
  rw [Finset.card_image_of_injOn hinj] at hcount
  exact hcount

/-- Comparison targets have one short interval of determinants and uniformly bounded fibers. -/
theorem envBox_comparisonTargets_card_le (S : PDScale) (w : ArchRoot) (hU : 0 < S.U)
    (hw : w.InRegion S) (Z : Finset (ℤ × ℤ)) (D : ℤ) (Y R : ℝ)
    (hY : 0 < Y) (hR : 0 ≤ R) :
    (((Z.filter fun z => (∃ t : ℤ, |(t : ℝ)| ≤ R * Y ∧ z.2 = D * t) ∧ envBox S w z).card) : ℝ) ≤
      17 * (2 * R * Y + 1) := by
  let T : Finset ℤ := Finset.Icc ⌈-(R * Y)⌉ ⌊R * Y⌋
  let C := Z.filter fun z => (∃ t : ℤ, |(t : ℝ)| ≤ R * Y ∧ z.2 = D * t) ∧ envBox S w z
  let fiber (t : ℤ) := Z.filter fun z => z.2 = D * t ∧ envBox S w z
  have hsub : C ⊆ T.biUnion fiber := by
    intro z hz
    have hz' : z ∈ Z ∧ (∃ t : ℤ, |(t : ℝ)| ≤ R * Y ∧ z.2 = D * t) ∧ envBox S w z := by
      simpa only [C, Finset.mem_filter] using hz
    obtain ⟨hzZ, ⟨t, ht, hdet⟩, hbox⟩ := hz'
    have htT : t ∈ T := Finset.mem_Icc.mpr
      ⟨Int.ceil_le.mpr (abs_le.mp ht).1, Int.le_floor.mpr (abs_le.mp ht).2⟩
    exact Finset.mem_biUnion.mpr ⟨t, htT, Finset.mem_filter.mpr ⟨hzZ, hdet, hbox⟩⟩
  have hNat : C.card ≤ T.card * 17 := by
    calc
      _ ≤ (T.biUnion fiber).card := Finset.card_le_card hsub
      _ ≤ ∑ t ∈ T, (fiber t).card := Finset.card_biUnion_le
      _ ≤ ∑ t ∈ T, 17 := Finset.sum_le_sum (fun t ht => envBox_rawTargets_card_le S w hU hw Z (D * t))
      _ = _ := by simp
  have hlr : ⌈-(R * Y)⌉ ≤ ⌊R * Y⌋ + 1 := by
    have hlow : ⌈-(R * Y)⌉ ≤ (0 : ℤ) := Int.ceil_le.mpr
      (by simpa only [Int.cast_zero] using neg_nonpos.mpr (mul_nonneg hR hY.le))
    have hhi : (0 : ℤ) ≤ ⌊R * Y⌋ := Int.le_floor.mpr
      (by simpa only [Int.cast_zero] using mul_nonneg hR hY.le)
    omega
  have hcardZ := Int.card_Icc_of_le (a := ⌈-(R * Y)⌉) (b := ⌊R * Y⌋) hlr
  have hcardR : (T.card : ℝ) = ((⌊R * Y⌋ + 1 - ⌈-(R * Y)⌉ : ℤ) : ℝ) := by exact_mod_cast hcardZ
  have hTcard : (T.card : ℝ) ≤ 2 * R * Y + 1 := by
    rw [hcardR]
    push_cast
    linarith [Int.floor_le (R * Y), Int.le_ceil (-(R * Y))]
  have hCount : (C.card : ℝ) ≤ (T.card : ℝ) * 17 := by exact_mod_cast hNat
  calc
    _ ≤ (T.card : ℝ) * 17 := hCount
    _ ≤ (2 * R * Y + 1) * 17 := mul_le_mul_of_nonneg_right hTcard (by norm_num)
    _ = _ := by ring


end
end ArtinPrimitiveRoots.TypeII.PD
