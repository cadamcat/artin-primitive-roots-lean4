import ArtinPrimitiveRoots.TypeII.PD.Physical

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical

/-- One independent prime choice for every shared pad slot. -/
abbrev PadChoice (x : ℝ) (K : ℕ) (a : Fin K → ℝ) :=
  (q : Fin K × Fin (momentJ x)) → {p : ℕ // p ∈ primeBand x (a q.1)}

noncomputable def padAddressPairs (x : ℝ) (K : ℕ) :
    Finset ((Fin K × Fin (momentJ x)) × (Fin K × Fin (momentJ x))) := by
  classical
  exact (Finset.univ).filter fun qq => qq.1.1 = qq.2.1 ∧ qq.1 ≠ qq.2

def PadChoiceGood {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (d : PadChoice x K a) (ta tb : Fin K → ℕ) : Prop :=
  (∀ q, (d q).val ≠ ta q.1 ∧ (d q).val ≠ tb q.1) ∧
    ∀ q q', q.1 = q'.1 → q ≠ q' → (d q).val ≠ (d q').val

noncomputable def padChoiceBadCount {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (d : PadChoice x K a) (ta tb : Fin K → ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin K × Fin (momentJ x))).filter
    (fun q => (d q).val = ta q.1)).card +
  ((Finset.univ : Finset (Fin K × Fin (momentJ x))).filter
    (fun q => (d q).val = tb q.1)).card +
  ((padAddressPairs x K).filter
    (fun qq => (d qq.1).val = (d qq.2).val)).card

noncomputable def padChoiceSet (x : ℝ) {K : ℕ} (a : Fin K → ℝ) :
    Finset (PadChoice x K a) :=
  Fintype.piFinset (fun q : Fin K × Fin (momentJ x) => Finset.univ)

noncomputable instance bandPrimeFintype {x : ℝ} {K : ℕ} (a : Fin K → ℝ) (i : Fin K) :
    Fintype {p : ℕ // p ∈ primeBand x (a i)} := by
  classical
  exact Fintype.ofFinset (primeBand x (a i)) (by intro p; rfl)

noncomputable instance padChoiceFintype (x : ℝ) (K : ℕ) (a : Fin K → ℝ) :
    Fintype (PadChoice x K a) := by
  classical
  infer_instance

/-- The product of the reciprocal-prime probability weights for a pad choice. -/
noncomputable def padAtomWeight (x : ℝ) {K : ℕ} (a : Fin K → ℝ)
    (q : Fin K × Fin (momentJ x))
    (p : {p : ℕ // p ∈ primeBand x (a q.1)}) : ℝ :=
  1 / (bandMass x (a q.1) * (p.val : ℝ))

noncomputable def padChoiceWeight (x : ℝ) {K : ℕ} (a : Fin K → ℝ)
    (d : PadChoice x K a) : ℝ :=
  ∏ q : Fin K × Fin (momentJ x), padAtomWeight x a q (d q)

/-- The product of the primes chosen in the shared pad slots. -/
noncomputable def padChoicePrimeProduct (x : ℝ) {K : ℕ} {a : Fin K → ℝ}
    (d : PadChoice x K a) : ℕ :=
  ∏ q : Fin K × Fin (momentJ x), (d q).val

/-- Band normalizers factor over the `J` shared slots in each group. -/
theorem padBandInverseProduct {x : ℝ} {K : ℕ} (a : Fin K → ℝ) :
    (∏ q : Fin K × Fin (momentJ x), (bandMass x (a q.1))⁻¹) =
      ∏ i : Fin K, (bandMass x (a i))⁻¹ ^ momentJ x := by
  classical
  simp [Fintype.prod_prod_type, Finset.prod_const, Fintype.card_fin]

/-- Pad weight separates into the band normalizers and the reciprocal shared-prime product. -/
theorem padChoiceWeight_factorization {x : ℝ} {K : ℕ} (a : Fin K → ℝ)
    (d : PadChoice x K a) :
    padChoiceWeight x a d =
      (∏ q : Fin K × Fin (momentJ x), (bandMass x (a q.1))⁻¹) *
        ((padChoicePrimeProduct x d : ℝ)⁻¹) := by
  classical
  calc
    padChoiceWeight x a d =
        ∏ q : Fin K × Fin (momentJ x),
          (bandMass x (a q.1))⁻¹ * ((d q).val : ℝ)⁻¹ := by
      unfold padChoiceWeight
      apply Finset.prod_congr rfl
      intro q hq
      simp [padAtomWeight, div_eq_mul_inv, mul_inv]
      ring
    _ = (∏ q : Fin K × Fin (momentJ x), (bandMass x (a q.1))⁻¹) *
        (∏ q : Fin K × Fin (momentJ x), ((d q).val : ℝ)⁻¹) := by
      rw [Finset.prod_mul_distrib]
    _ = (∏ q : Fin K × Fin (momentJ x), (bandMass x (a q.1))⁻¹) *
        ((∏ q : Fin K × Fin (momentJ x), (d q).val : ℝ)⁻¹) := by
      simp only [Finset.prod_inv_distrib]
    _ = (∏ q : Fin K × Fin (momentJ x), (bandMass x (a q.1))⁻¹) *
        ((padChoicePrimeProduct x d : ℝ)⁻¹) := by
      simp [padChoicePrimeProduct]

/-- Grouped form of `padChoiceWeight_factorization`, displaying one normalizer per pad slot. -/
theorem padChoiceWeight_group_factorization {x : ℝ} {K : ℕ} (a : Fin K → ℝ)
    (d : PadChoice x K a) :
    padChoiceWeight x a d =
      (∏ i : Fin K, (bandMass x (a i))⁻¹ ^ momentJ x) *
        ((padChoicePrimeProduct x d : ℝ)⁻¹) := by
  rw [padChoiceWeight_factorization, padBandInverseProduct]

/-- Two fresh endpoint normalizers combine with the pad weight into one `J+2` band power. -/
theorem padChoiceWeight_group_two_normalizers {x : ℝ} {K : ℕ} (a : Fin K → ℝ)
    (d : PadChoice x K a) :
    padChoiceWeight x a d *
        (∏ i : Fin K, (bandMass x (a i))⁻¹) ^ 2 =
      (padChoicePrimeProduct x d : ℝ)⁻¹ *
        ∏ i : Fin K, (bandMass x (a i))⁻¹ ^ (momentJ x + 2) := by
  classical
  let c : Fin K → ℝ := fun i => (bandMass x (a i))⁻¹
  have hFreshSq : (∏ i : Fin K, c i) ^ 2 = ∏ i : Fin K, c i ^ 2 := by
    simpa only [pow_two] using
      (Finset.prod_pow (Finset.univ : Finset (Fin K)) 2 c).symm
  have hBandPow : (∏ i : Fin K, c i ^ momentJ x) * (∏ i : Fin K, c i ^ 2) =
      ∏ i : Fin K, c i ^ (momentJ x + 2) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [pow_add]
  rw [padChoiceWeight_group_factorization, hFreshSq]
  dsimp [c]
  calc
    (∏ i : Fin K, (bandMass x (a i))⁻¹ ^ momentJ x) *
        (↑(padChoicePrimeProduct x d))⁻¹ *
        (∏ i : Fin K, (bandMass x (a i))⁻¹ ^ 2) =
      (↑(padChoicePrimeProduct x d))⁻¹ *
        ((∏ i : Fin K, (bandMass x (a i))⁻¹ ^ momentJ x) *
          (∏ i : Fin K, (bandMass x (a i))⁻¹ ^ 2)) := by ring
    _ = (↑(padChoicePrimeProduct x d))⁻¹ *
        ∏ i : Fin K, (bandMass x (a i))⁻¹ ^ (momentJ x + 2) := by
      rw [hBandPow]

noncomputable def padChoiceFixedLabelMass {x : ℝ} {K : ℕ} (a : Fin K → ℝ)
    (q : Fin K × Fin (momentJ x)) (t : ℕ) : ℝ :=
  ∑ d ∈ padChoiceSet x a, if (d q).val = t then padChoiceWeight x a d else 0

noncomputable def padChoicePairMass {x : ℝ} {K : ℕ} (a : Fin K → ℝ)
    (q q' : Fin K × Fin (momentJ x)) : ℝ :=
  ∑ d ∈ padChoiceSet x a,
    if (d q).val = (d q').val then padChoiceWeight x a d else 0

/-- A finite sum over all pad choices factors into its coordinate sums. -/
theorem padChoice_product_sum {x : ℝ} {K : ℕ} (a : Fin K → ℝ)
    (f : (q : Fin K × Fin (momentJ x)) →
      {p : ℕ // p ∈ primeBand x (a q.1)} → ℝ) :
    (∑ d ∈ Fintype.piFinset (fun q : Fin K × Fin (momentJ x) =>
      (Finset.univ : Finset {p : ℕ // p ∈ primeBand x (a q.1)})),
      ∏ q, f q (d q)) =
        ∏ q : Fin K × Fin (momentJ x),
          ∑ p : {p : ℕ // p ∈ primeBand x (a q.1)}, f q p := by
  classical
  exact (Finset.prod_univ_sum
    (fun q : Fin K × Fin (momentJ x) =>
      (Finset.univ : Finset {p : ℕ // p ∈ primeBand x (a q.1)})) f).symm

/-- Each coordinate is a probability distribution on its marked band. -/
theorem padAtomWeight_sum_eq_one {x : ℝ} {K : ℕ} (a : Fin K → ℝ)
    (hV : ∀ i, 0 < bandMass x (a i)) (q : Fin K × Fin (momentJ x)) :
    (∑ p : {p : ℕ // p ∈ primeBand x (a q.1)}, padAtomWeight x a q p) = 1 := by
  classical
  letI : Fintype {p : ℕ // p ∈ primeBand x (a q.1)} :=
    Fintype.ofFinset (primeBand x (a q.1)) (by intro p; rfl)
  let V := bandMass x (a q.1)
  have hV' : 0 < V := hV q.1
  have hsubtype :
      (∑ p : {p : ℕ // p ∈ primeBand x (a q.1)},
        1 / (V * (p.val : ℝ))) =
        ∑ p ∈ primeBand x (a q.1), 1 / (V * (p : ℝ)) := by
    simpa [V] using (Finset.sum_subtype (primeBand x (a q.1)) (fun _ => Iff.rfl)
      (fun p => 1 / (V * (p : ℝ)))).symm
  have hterms : ∀ p ∈ primeBand x (a q.1),
      1 / (V * (p : ℝ)) = V⁻¹ * (1 / (p : ℝ)) := by
    intro p hp
    have hpPrime := (Finset.mem_filter.mp hp).2.1
    have hpPos : 0 < (p : ℝ) := by exact_mod_cast hpPrime.pos
    field_simp [ne_of_gt hV', ne_of_gt hpPos]
  calc
    _ = ∑ p ∈ primeBand x (a q.1), 1 / (V * (p : ℝ)) := by
      simpa [padAtomWeight, V] using hsubtype
    _ = V⁻¹ * ∑ p ∈ primeBand x (a q.1), 1 / (p : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      exact hterms p hp
    _ = V⁻¹ * V := by simp [V, bandMass]
    _ = 1 := inv_mul_cancel₀ (ne_of_gt hV')

/-- Extend one coordinate's atom weights by zero outside its band. -/
noncomputable def padAtomNat (x : ℝ) {K : ℕ} (a : Fin K → ℝ)
    (q : Fin K × Fin (momentJ x)) (n : ℕ) : ℝ :=
  if hn : n ∈ primeBand x (a q.1) then
    padAtomWeight x a q ⟨n, hn⟩
  else 0

/-- Any finite restriction of a coordinate's extended atom weights has mass at most one. -/
theorem padAtomNat_sum_le_one {x : ℝ} {K : ℕ} (a : Fin K → ℝ)
    (hV : ∀ i, 0 < bandMass x (a i)) (q : Fin K × Fin (momentJ x)) (s : Finset ℕ) :
    (∑ n ∈ s, padAtomNat x a q n) ≤ 1 := by
  classical
  let B := primeBand x (a q.1)
  let T := s.filter (fun n => n ∈ B)
  have hsubset : T ⊆ B := by
    intro n hn
    exact (Finset.mem_filter.mp hn).2
  have hnonneg : ∀ n ∈ B, 0 ≤ padAtomNat x a q n := by
    intro n hn
    have hnPrime := (Finset.mem_filter.mp hn).2.1
    have hnPos : 0 < (n : ℝ) := by exact_mod_cast hnPrime.pos
    have hVpos : 0 < bandMass x (a q.1) := hV q.1
    simp [padAtomNat, B, hn]
    unfold padAtomWeight
    positivity
  have hfull : (∑ n ∈ B, padAtomNat x a q n) = 1 := by
    calc
      _ = ∑ p : {p : ℕ // p ∈ B}, padAtomNat x a q p.val := by
        symm
        exact (Finset.sum_subtype B (fun _ => Iff.rfl) (padAtomNat x a q)).symm
      _ = 1 := by
        simpa [padAtomNat, B] using padAtomWeight_sum_eq_one a hV q
  have hrestrict :
      (∑ n ∈ s, padAtomNat x a q n) = ∑ n ∈ T, padAtomNat x a q n := by
    dsimp [T]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases h : n ∈ B
    · simp [padAtomNat, B, h]
    · simp [padAtomNat, B, h]
  calc
    (∑ n ∈ s, padAtomNat x a q n) = ∑ n ∈ T, padAtomNat x a q n := hrestrict
    _ ≤ ∑ n ∈ B, padAtomNat x a q n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
        intro n hn _
        exact hnonneg n hn)
    _ = 1 := hfull

/-- The probability that one pad coordinate takes a prescribed prime is its atom weight. -/
theorem padChoiceWeight_coordinate_mass {x : ℝ} {K : ℕ} (a : Fin K → ℝ)
    (hV : ∀ i, 0 < bandMass x (a i)) (q : Fin K × Fin (momentJ x))
    (p : {p : ℕ // p ∈ primeBand x (a q.1)}) :
    (∑ d ∈ Fintype.piFinset (fun q' : Fin K × Fin (momentJ x) =>
      (Finset.univ : Finset {p' : ℕ // p' ∈ primeBand x (a q'.1)})),
      if d q = p then padChoiceWeight x a d else 0) = padAtomWeight x a q p := by
  classical
  let f : (q' : Fin K × Fin (momentJ x)) →
      {p' : ℕ // p' ∈ primeBand x (a q'.1)} → ℝ := fun q' p' =>
    if hq : q' = q then
      if p'.val = p.val then padAtomWeight x a q' p' else 0
    else padAtomWeight x a q' p'
  have hterm (d : PadChoice x K a) :
      (if d q = p then padChoiceWeight x a d else 0) = ∏ q', f q' (d q') := by
    by_cases hEq : d q = p
    · simp only [if_pos hEq]
      rw [padChoiceWeight]
      apply Finset.prod_congr rfl
      intro q' hq'
      by_cases hq : q' = q
      · subst q'
        simp [f, hEq]
      · simp [f, hq]
    · simp only [if_neg hEq]
      have hval : (d q).val ≠ p.val := by
        intro hval
        exact hEq (Subtype.ext hval)
      have hzero : f q (d q) = 0 := by simp [f, hval]
      rw [Finset.prod_eq_zero (Finset.mem_univ q) hzero]
  calc
    _ = ∑ d ∈ Fintype.piFinset (fun q' : Fin K × Fin (momentJ x) =>
          (Finset.univ : Finset {p' : ℕ // p' ∈ primeBand x (a q'.1)})),
          ∏ q', f q' (d q') := by
        apply Finset.sum_congr rfl
        intro d hd
        exact hterm d
    _ = ∏ q' : Fin K × Fin (momentJ x), ∑ p' : {p' : ℕ //
          p' ∈ primeBand x (a q'.1)}, f q' p' := padChoice_product_sum a f
    _ = padAtomWeight x a q p := by
      change (Finset.univ : Finset (Fin K × Fin (momentJ x))).prod
        (fun q' => ∑ p' : {p' : ℕ // p' ∈ primeBand x (a q'.1)}, f q' p') = _
      calc
        _ = ∑ p' : {p' : ℕ // p' ∈ primeBand x (a q.1)}, f q p' :=
          Finset.prod_eq_single_of_mem q (Finset.mem_univ q) (by
            intro q' hq' hne
            simp [f, hne, padAtomWeight_sum_eq_one a hV q'])
        _ = padAtomWeight x a q p := by simp [f]

/-- Two distinct pad coordinates have independent atom masses. -/
theorem padChoiceWeight_coordinate_mass_typed {x : ℝ} {K : ℕ} (a : Fin K → ℝ)
    (hV : ∀ i, 0 < bandMass x (a i)) (q : Fin K × Fin (momentJ x))
    (p : {p : ℕ // p ∈ primeBand x (a q.1)}) :
    (∑ d : PadChoice x K a,
      if d q = p then padChoiceWeight x a d else 0) = padAtomWeight x a q p := by
  simpa only [Fintype.piFinset_univ] using padChoiceWeight_coordinate_mass a hV q p

theorem padChoiceWeight_two_coordinate_mass {x : ℝ} {K : ℕ} (a : Fin K → ℝ)
    (hV : ∀ i, 0 < bandMass x (a i)) (q q' : Fin K × Fin (momentJ x))
    (hqq' : q ≠ q')
    (p : {p : ℕ // p ∈ primeBand x (a q.1)})
    (p' : {p : ℕ // p ∈ primeBand x (a q'.1)}) :
    (∑ d ∈ Fintype.piFinset (fun r : Fin K × Fin (momentJ x) =>
      (Finset.univ : Finset {z : ℕ // z ∈ primeBand x (a r.1)})),
      if d q = p ∧ d q' = p' then padChoiceWeight x a d else 0) =
        padAtomWeight x a q p * padAtomWeight x a q' p' := by
  classical
  have hq'q : q' ≠ q := Ne.symm hqq'
  let f : (r : Fin K × Fin (momentJ x)) →
      {z : ℕ // z ∈ primeBand x (a r.1)} → ℝ := fun r z =>
    if hr : r = q then
      if z.val = p.val then padAtomWeight x a r z else 0
    else if hr' : r = q' then
      if z.val = p'.val then padAtomWeight x a r z else 0
    else padAtomWeight x a r z
  have hterm (d : PadChoice x K a) :
      (if d q = p ∧ d q' = p' then padChoiceWeight x a d else 0) =
        ∏ r, f r (d r) := by
    by_cases h1 : d q = p
    · by_cases h2 : d q' = p'
      · have hEvent : d q = p ∧ d q' = p' := ⟨h1, h2⟩
        simp only [if_pos hEvent]
        rw [padChoiceWeight]
        apply Finset.prod_congr rfl
        intro r hr
        by_cases hrq : r = q
        · subst r
          simp [f, h1]
        · by_cases hrq' : r = q'
          · subst r
            simp [f, h2, hq'q]
          · simp [f, hrq, hrq']
      · have hnot : ¬(d q = p ∧ d q' = p') := by
          rintro ⟨_, hh⟩
          exact h2 hh
        simp only [if_neg hnot]
        have hval : (d q').val ≠ p'.val := by
          intro hv
          exact h2 (Subtype.ext hv)
        have hzero : f q' (d q') = 0 := by simp [f, hq'q, hval]
        rw [Finset.prod_eq_zero (Finset.mem_univ q') hzero]
    · have hnot : ¬(d q = p ∧ d q' = p') := by
        rintro ⟨hh, _⟩
        exact h1 hh
      simp only [if_neg hnot]
      have hval : (d q).val ≠ p.val := by
        intro hv
        exact h1 (Subtype.ext hv)
      have hzero : f q (d q) = 0 := by simp [f, hval]
      rw [Finset.prod_eq_zero (Finset.mem_univ q) hzero]
  let g : (r : Fin K × Fin (momentJ x)) → ℝ := fun r => ∑ z, f r z
  have hgq : g q = padAtomWeight x a q p := by simp [g, f]
  have hgq' : g q' = padAtomWeight x a q' p' := by simp [g, f, hq'q]
  have hq'mem : q' ∈ Finset.univ.erase q :=
    Finset.mem_erase.mpr ⟨hq'q, Finset.mem_univ _⟩
  have hrest : ∏ r ∈ (Finset.univ.erase q).erase q', g r = 1 := by
    apply Finset.prod_eq_one
    intro r hr
    have hrq' : r ≠ q' := (Finset.mem_erase.mp hr).1
    have hrmem : r ∈ Finset.univ.erase q := (Finset.mem_erase.mp hr).2
    have hrq : r ≠ q := (Finset.mem_erase.mp hrmem).1
    simp [g, f, hrq, hrq', padAtomWeight_sum_eq_one a hV r]
  have hprod : ∏ r, g r = g q * g q' := by
    calc
      (∏ r, g r) = (∏ r ∈ Finset.univ.erase q, g r) * g q :=
        (Finset.prod_erase_mul Finset.univ g (Finset.mem_univ q)).symm
      _ = ((∏ r ∈ (Finset.univ.erase q).erase q', g r) * g q') * g q := by
        rw [← Finset.prod_erase_mul (Finset.univ.erase q) g hq'mem]
      _ = g q * g q' := by rw [hrest]; ring
  calc
    _ = ∑ d ∈ Fintype.piFinset (fun r : Fin K × Fin (momentJ x) =>
          (Finset.univ : Finset {z : ℕ // z ∈ primeBand x (a r.1)})),
          ∏ r, f r (d r) := by
        apply Finset.sum_congr rfl
        intro d hd
        exact hterm d
    _ = ∏ r, ∑ z, f r z := padChoice_product_sum a f
    _ = padAtomWeight x a q p * padAtomWeight x a q' p' := by
      rw [hprod, hgq, hgq']

/-- A collision between two pad addresses can be split over their common prime value. -/
theorem padChoiceWeight_collision_mass_eq {x : ℝ} {K : ℕ} (a : Fin K → ℝ)
    (q q' : Fin K × Fin (momentJ x)) :
    (∑ d ∈ Fintype.piFinset (fun r : Fin K × Fin (momentJ x) =>
      (Finset.univ : Finset {z : ℕ // z ∈ primeBand x (a r.1)})),
      if (d q).val = (d q').val then padChoiceWeight x a d else 0) =
      ∑ p ∈ primeBand x (a q.1),
        ∑ d ∈ Fintype.piFinset (fun r : Fin K × Fin (momentJ x) =>
          (Finset.univ : Finset {z : ℕ // z ∈ primeBand x (a r.1)})),
          if (d q).val = p ∧ (d q').val = p then padChoiceWeight x a d else 0 := by
  classical
  have hdecomp (d : PadChoice x K a) :
      (if (d q).val = (d q').val then padChoiceWeight x a d else 0) =
        ∑ p ∈ primeBand x (a q.1),
          if (d q).val = p ∧ (d q').val = p then padChoiceWeight x a d else 0 := by
    by_cases heq : (d q).val = (d q').val
    · have hmem : (d q).val ∈ primeBand x (a q.1) := (d q).property
      have hsum :
          (∑ p ∈ primeBand x (a q.1),
            if (d q).val = p ∧ (d q').val = p then (1 : ℝ) else 0) = 1 := by
        rw [Finset.sum_eq_single (d q).val]
        · simp [heq]
        · intro p hp hne
          have hcond : ¬((d q).val = p ∧ (d q').val = p) := by
            intro h
            exact hne h.1.symm
          simp [hcond]
        · intro hnot
          exact False.elim (hnot hmem)
      calc
        _ = padChoiceWeight x a d := by simp [heq]
        _ = padChoiceWeight x a d * 1 := by ring
        _ = padChoiceWeight x a d *
              ∑ p ∈ primeBand x (a q.1),
                if (d q).val = p ∧ (d q').val = p then (1 : ℝ) else 0 := by rw [hsum]
        _ = ∑ p ∈ primeBand x (a q.1),
              padChoiceWeight x a d *
                (if (d q).val = p ∧ (d q').val = p then (1 : ℝ) else 0) := by
                rw [Finset.mul_sum]
        _ = ∑ p ∈ primeBand x (a q.1),
              if (d q).val = p ∧ (d q').val = p then padChoiceWeight x a d else 0 := by
                apply Finset.sum_congr rfl
                intro p hp
                split_ifs <;> simp [mul_comm]
    · simp only [if_neg heq]
      symm
      apply Finset.sum_eq_zero
      intro p hp
      by_cases h₁ : (d q).val = p
      · have h₂ : (d q').val ≠ p := by
          intro heq'
          exact heq (h₁.trans heq'.symm)
        simp [h₁, h₂]
      · simp [h₁]
  calc
    _ = ∑ d ∈ Fintype.piFinset (fun r : Fin K × Fin (momentJ x) =>
          (Finset.univ : Finset {z : ℕ // z ∈ primeBand x (a r.1)})),
          ∑ p ∈ primeBand x (a q.1),
            if (d q).val = p ∧ (d q').val = p then padChoiceWeight x a d else 0 := by
        apply Finset.sum_congr rfl
        intro d hd
        exact hdecomp d
    _ = ∑ p ∈ primeBand x (a q.1),
          ∑ d ∈ Fintype.piFinset (fun r : Fin K × Fin (momentJ x) =>
            (Finset.univ : Finset {z : ℕ // z ∈ primeBand x (a r.1)})),
            if (d q).val = p ∧ (d q').val = p then padChoiceWeight x a d else 0 := by
        rw [Finset.sum_comm]

/-- If every atom is at most `ε`, the mass where two distinct coordinates collide is at most `ε`. -/
theorem padChoiceWeight_collision_mass_le {x : ℝ} {K : ℕ} (a : Fin K → ℝ)
    (hV : ∀ i, 0 < bandMass x (a i)) (ε : ℝ) (hε : 0 ≤ ε)
    (hAtom : ∀ (q : Fin K × Fin (momentJ x))
      (p : {p : ℕ // p ∈ primeBand x (a q.1)}),
      padAtomWeight x a q p ≤ ε)
    (q q' : Fin K × Fin (momentJ x)) (hqq' : q ≠ q') :
    (∑ d ∈ Fintype.piFinset (fun r : Fin K × Fin (momentJ x) =>
      (Finset.univ : Finset {z : ℕ // z ∈ primeBand x (a r.1)})),
      if (d q).val = (d q').val then padChoiceWeight x a d else 0) ≤ ε := by
  classical
  rw [padChoiceWeight_collision_mass_eq a q q']
  have hInner (p : ℕ) (hp : p ∈ primeBand x (a q.1)) :
      (∑ d ∈ Fintype.piFinset (fun r : Fin K × Fin (momentJ x) =>
        (Finset.univ : Finset {z : ℕ // z ∈ primeBand x (a r.1)})),
        if (d q).val = p ∧ (d q').val = p then padChoiceWeight x a d else 0) ≤
          ε * padAtomNat x a q' p := by
    by_cases hq'p : p ∈ primeBand x (a q'.1)
    · let p₀ : {p : ℕ // p ∈ primeBand x (a q.1)} := ⟨p, hp⟩
      let p₁ : {p : ℕ // p ∈ primeBand x (a q'.1)} := ⟨p, hq'p⟩
      have hconvert :
          (∑ d ∈ Fintype.piFinset (fun r : Fin K × Fin (momentJ x) =>
            (Finset.univ : Finset {z : ℕ // z ∈ primeBand x (a r.1)})),
            if (d q).val = p ∧ (d q').val = p then padChoiceWeight x a d else 0) =
          (∑ d ∈ Fintype.piFinset (fun r : Fin K × Fin (momentJ x) =>
            (Finset.univ : Finset {z : ℕ // z ∈ primeBand x (a r.1)})),
            if d q = p₀ ∧ d q' = p₁ then padChoiceWeight x a d else 0) := by
        apply Finset.sum_congr rfl
        intro d hd
        by_cases h : ((d q).val = p ∧ (d q').val = p)
        · have h' : d q = p₀ ∧ d q' = p₁ := by
            exact ⟨Subtype.ext h.1, Subtype.ext h.2⟩
          simp [h, h', p₀, p₁]
        · have h' : ¬(d q = p₀ ∧ d q' = p₁) := by
            intro hpq
            exact h (⟨congrArg Subtype.val hpq.1, congrArg Subtype.val hpq.2⟩)
          simp [h, h', p₀, p₁]
      rw [hconvert, padChoiceWeight_two_coordinate_mass a hV q q' hqq' p₀ p₁]
      have hAtom₀ : padAtomWeight x a q p₀ ≤ ε := hAtom q p₀
      have hNonneg₁ : 0 ≤ padAtomWeight x a q' p₁ := by
        have hpPrime := (Finset.mem_filter.mp hq'p).2.1
        have hpPos : 0 < (p : ℝ) := by exact_mod_cast hpPrime.pos
        have hVpos := hV q'.1
        unfold padAtomWeight
        positivity
      calc
        padAtomWeight x a q p₀ * padAtomWeight x a q' p₁ ≤
            ε * padAtomWeight x a q' p₁ :=
              mul_le_mul_of_nonneg_right hAtom₀ hNonneg₁
        _ = ε * padAtomNat x a q' p := by simp [padAtomNat, hq'p, p₁]
    · have hzero :
          (∑ d ∈ Fintype.piFinset (fun r : Fin K × Fin (momentJ x) =>
            (Finset.univ : Finset {z : ℕ // z ∈ primeBand x (a r.1)})),
            if (d q).val = p ∧ (d q').val = p then padChoiceWeight x a d else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro d hd
        by_cases h₁ : (d q).val = p
        · by_cases h₂ : (d q').val = p
          · have hpIn : p ∈ primeBand x (a q'.1) := by
              rw [← h₂]
              exact (d q').property
            exact (hq'p hpIn).elim
          · simp [h₁, h₂]
        · simp [h₁]
      rw [hzero]
      simp [padAtomNat, hq'p]
  have htotal : (∑ p ∈ primeBand x (a q.1), padAtomNat x a q' p) ≤ 1 :=
    padAtomNat_sum_le_one a hV q' (primeBand x (a q.1))
  calc
    (∑ p ∈ primeBand x (a q.1),
        ∑ d ∈ Fintype.piFinset (fun r : Fin K × Fin (momentJ x) =>
          (Finset.univ : Finset {z : ℕ // z ∈ primeBand x (a r.1)})),
          if (d q).val = p ∧ (d q').val = p then padChoiceWeight x a d else 0) ≤
      ∑ p ∈ primeBand x (a q.1), ε * padAtomNat x a q' p :=
        Finset.sum_le_sum fun p hp => hInner p hp
    _ = ε * ∑ p ∈ primeBand x (a q.1), padAtomNat x a q' p := by rw [Finset.mul_sum]
    _ ≤ ε * 1 := mul_le_mul_of_nonneg_left htotal hε
    _ = ε := by ring

/-- Sum of the bad pad-choice mass is bounded by the individual fixed-label and
pair-collision masses. -/
theorem padChoiceWeight_collision_mass_le_typed {x : ℝ} {K : ℕ} (a : Fin K → ℝ)
    (hV : ∀ i, 0 < bandMass x (a i)) (ε : ℝ) (hε : 0 ≤ ε)
    (hAtom : ∀ (q : Fin K × Fin (momentJ x))
      (p : {p : ℕ // p ∈ primeBand x (a q.1)}), padAtomWeight x a q p ≤ ε)
    (q q' : Fin K × Fin (momentJ x)) (hqq' : q ≠ q') :
    (∑ d : PadChoice x K a,
      if (d q).val = (d q').val then padChoiceWeight x a d else 0) ≤ ε := by
  simpa only [Fintype.piFinset_univ] using
    padChoiceWeight_collision_mass_le a hV ε hε hAtom q q' hqq'

theorem padChoiceWeight_forbiddenMass_le {x : ℝ} {K : ℕ} (a : Fin K → ℝ)
    (ta tb : Fin K → ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hV : ∀ i, 0 < bandMass x (a i))
    (hFixedA : ∀ q : Fin K × Fin (momentJ x),
      padChoiceFixedLabelMass a q (ta q.1) ≤ ε)
    (hFixedB : ∀ q : Fin K × Fin (momentJ x),
      padChoiceFixedLabelMass a q (tb q.1) ≤ ε)
    (hPairs : ∀ q q' : Fin K × Fin (momentJ x), q.1 = q'.1 → q ≠ q' →
      padChoicePairMass a q q' ≤ ε) :
    (∑ d ∈ padChoiceSet x a,
      if PadChoiceGood d ta tb then 0 else padChoiceWeight x a d) ≤
        (((2 * Fintype.card (Fin K × Fin (momentJ x)) +
          (padAddressPairs x K).card : ℕ) : ℝ) * ε) := by
  classical
  let Addr := Fin K × Fin (momentJ x)
  let Pairs := padAddressPairs x K
  let badA (d : PadChoice x K a) :=
    (Finset.univ : Finset Addr).filter (fun q => (d q).val = ta q.1)
  let badB (d : PadChoice x K a) :=
    (Finset.univ : Finset Addr).filter (fun q => (d q).val = tb q.1)
  let badPair (d : PadChoice x K a) :=
    Pairs.filter (fun qq => (d qq.1).val = (d qq.2).val)
  have hcountCast (d : PadChoice x K a) :
      (padChoiceBadCount d ta tb : ℝ) =
        (∑ q : Addr, if (d q).val = ta q.1 then (1 : ℝ) else 0) +
        (∑ q : Addr, if (d q).val = tb q.1 then (1 : ℝ) else 0) +
        ∑ qq ∈ Pairs, if (d qq.1).val = (d qq.2).val then (1 : ℝ) else 0 := by
    unfold padChoiceBadCount
    rw [Nat.cast_add, Nat.cast_add, Finset.natCast_card_filter,
      Finset.natCast_card_filter, Finset.natCast_card_filter]
  have hzeroGood (d : PadChoice x K a) (hz : padChoiceBadCount d ta tb = 0) :
      PadChoiceGood d ta tb := by
    have hsum : (badA d).card + (badB d).card + (badPair d).card = 0 := by
      simpa [padChoiceBadCount, badA, badB, badPair, Pairs] using hz
    rcases Nat.add_eq_zero.mp hsum with ⟨hAB, hcardP⟩
    rcases Nat.add_eq_zero.mp hAB with ⟨hcardA, hcardB⟩
    have hEmptyA : badA d = ∅ := Finset.card_eq_zero.mp hcardA
    have hEmptyB : badB d = ∅ := Finset.card_eq_zero.mp hcardB
    have hEmptyP : badPair d = ∅ := Finset.card_eq_zero.mp hcardP
    constructor
    · intro q
      constructor
      · intro h
        have hm : q ∈ badA d := Finset.mem_filter.mpr ⟨Finset.mem_univ q, h⟩
        rw [hEmptyA] at hm
        simpa using hm
      · intro h
        have hm : q ∈ badB d := Finset.mem_filter.mpr ⟨Finset.mem_univ q, h⟩
        rw [hEmptyB] at hm
        simpa using hm
    · intro q q' hgroup hne h
      have hpair : (q, q') ∈ Pairs := by simp [Pairs, padAddressPairs, hgroup, hne]
      have hm : (q, q') ∈ badPair d := Finset.mem_filter.mpr ⟨hpair, h⟩
      rw [hEmptyP] at hm
      simpa using hm
  have hcountPos (d : PadChoice x K a) (hbad : ¬PadChoiceGood d ta tb) :
      1 ≤ padChoiceBadCount d ta tb := by
    by_contra hnot
    have hz : padChoiceBadCount d ta tb = 0 := by omega
    exact hbad (hzeroGood d hz)
  have hweightNonneg (d : PadChoice x K a) : 0 ≤ padChoiceWeight x a d := by
    unfold padChoiceWeight
    apply Finset.prod_nonneg
    intro q hq
    have hVpos : 0 < bandMass x (a q.1) := hV q.1
    have hpPrime := (Finset.mem_filter.mp (d q).property).2.1
    have hpPos : 0 < ((d q).val : ℝ) := by exact_mod_cast hpPrime.pos
    unfold padAtomWeight
    positivity
  have hTAExpectation :
      (∑ d ∈ padChoiceSet x a,
        (∑ q : Addr, if (d q).val = ta q.1 then (1 : ℝ) else 0) *
          padChoiceWeight x a d) =
        ∑ q : Addr, padChoiceFixedLabelMass a q (ta q.1) := by
    calc
      _ = ∑ d ∈ padChoiceSet x a, ∑ q : Addr,
            if (d q).val = ta q.1 then padChoiceWeight x a d else 0 := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro q hq
        by_cases h : (d q).val = ta q.1 <;> simp [h]
      _ = ∑ q : Addr, padChoiceFixedLabelMass a q (ta q.1) := by
        rw [Finset.sum_comm]
        rfl
  have hTBExpectation :
      (∑ d ∈ padChoiceSet x a,
        (∑ q : Addr, if (d q).val = tb q.1 then (1 : ℝ) else 0) *
          padChoiceWeight x a d) =
        ∑ q : Addr, padChoiceFixedLabelMass a q (tb q.1) := by
    calc
      _ = ∑ d ∈ padChoiceSet x a, ∑ q : Addr,
            if (d q).val = tb q.1 then padChoiceWeight x a d else 0 := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro q hq
        by_cases h : (d q).val = tb q.1 <;> simp [h]
      _ = ∑ q : Addr, padChoiceFixedLabelMass a q (tb q.1) := by
        rw [Finset.sum_comm]
        rfl
  have hPairExpectation :
      (∑ d ∈ padChoiceSet x a,
        (∑ qq ∈ Pairs,
          if (d qq.1).val = (d qq.2).val then (1 : ℝ) else 0) *
            padChoiceWeight x a d) =
        ∑ qq ∈ Pairs, padChoicePairMass a qq.1 qq.2 := by
    calc
      _ = ∑ d ∈ padChoiceSet x a, ∑ qq ∈ Pairs,
            if (d qq.1).val = (d qq.2).val then padChoiceWeight x a d else 0 := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro qq hqq
        by_cases h : (d qq.1).val = (d qq.2).val <;> simp [h]
      _ = ∑ qq ∈ Pairs, padChoicePairMass a qq.1 qq.2 := by
        rw [Finset.sum_comm]
        rfl
  have hExpectation :
      (∑ d ∈ padChoiceSet x a, (padChoiceBadCount d ta tb : ℝ) * padChoiceWeight x a d) =
        (∑ q : Addr, padChoiceFixedLabelMass a q (ta q.1)) +
        (∑ q : Addr, padChoiceFixedLabelMass a q (tb q.1)) +
          ∑ qq ∈ Pairs, padChoicePairMass a qq.1 qq.2 := by
    calc
      _ = ∑ d ∈ padChoiceSet x a,
            ((∑ q : Addr, if (d q).val = ta q.1 then (1 : ℝ) else 0) +
              (∑ q : Addr, if (d q).val = tb q.1 then (1 : ℝ) else 0) +
              ∑ qq ∈ Pairs,
                if (d qq.1).val = (d qq.2).val then (1 : ℝ) else 0) *
              padChoiceWeight x a d := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [hcountCast]
      _ = (∑ d ∈ padChoiceSet x a,
            (∑ q : Addr, if (d q).val = ta q.1 then (1 : ℝ) else 0) *
              padChoiceWeight x a d) +
          (∑ d ∈ padChoiceSet x a,
            (∑ q : Addr, if (d q).val = tb q.1 then (1 : ℝ) else 0) *
              padChoiceWeight x a d) +
          ∑ d ∈ padChoiceSet x a,
            (∑ qq ∈ Pairs,
              if (d qq.1).val = (d qq.2).val then (1 : ℝ) else 0) *
              padChoiceWeight x a d := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro d hd
        ring
      _ = _ := by rw [hTAExpectation, hTBExpectation, hPairExpectation]
  have hTA :
      (∑ q : Addr, padChoiceFixedLabelMass a q (ta q.1)) ≤
        (Fintype.card Addr : ℝ) * ε := by
    calc
      _ ≤ ∑ q : Addr, ε := Finset.sum_le_sum fun q hq => hFixedA q
      _ = (Fintype.card Addr : ℝ) * ε := by simp [mul_comm]
  have hTB :
      (∑ q : Addr, padChoiceFixedLabelMass a q (tb q.1)) ≤
        (Fintype.card Addr : ℝ) * ε := by
    calc
      _ ≤ ∑ q : Addr, ε := Finset.sum_le_sum fun q hq => hFixedB q
      _ = (Fintype.card Addr : ℝ) * ε := by simp [mul_comm]
  have hPairs :
      (∑ qq ∈ Pairs, padChoicePairMass a qq.1 qq.2) ≤ (Pairs.card : ℝ) * ε := by
    calc
      _ ≤ ∑ qq ∈ Pairs, ε := Finset.sum_le_sum fun qq hqq => hPairs qq.1 qq.2
        (Finset.mem_filter.mp hqq).2.1 ((Finset.mem_filter.mp hqq).2.2)
      _ = (Pairs.card : ℝ) * ε := by simp [mul_comm]
  calc
    (∑ d ∈ padChoiceSet x a,
      if PadChoiceGood d ta tb then 0 else padChoiceWeight x a d) ≤
        ∑ d ∈ padChoiceSet x a,
          (padChoiceBadCount d ta tb : ℝ) * padChoiceWeight x a d := by
      apply Finset.sum_le_sum
      intro d hd
      by_cases hgood : PadChoiceGood d ta tb
      · simp [hgood]
        exact mul_nonneg (Nat.cast_nonneg _) (hweightNonneg d)
      · have hc := hcountPos d hgood
        have hc' : (1 : ℝ) ≤ (padChoiceBadCount d ta tb : ℝ) := by exact_mod_cast hc
        simp only [if_neg hgood]
        calc
          padChoiceWeight x a d = 1 * padChoiceWeight x a d := by ring
          _ ≤ (padChoiceBadCount d ta tb : ℝ) * padChoiceWeight x a d :=
            mul_le_mul_of_nonneg_right hc' (hweightNonneg d)
    _ ≤ ((2 * Fintype.card Addr + Pairs.card : ℕ) : ℝ) * ε := by
      rw [hExpectation]
      calc
        _ ≤ (Fintype.card Addr : ℝ) * ε + (Fintype.card Addr : ℝ) * ε +
            (Pairs.card : ℝ) * ε :=
              add_le_add (add_le_add hTA hTB) hPairs
        _ = ((2 * Fintype.card Addr + Pairs.card : ℕ) : ℝ) * ε := by
              push_cast
              ring

/-- The independent harmonic pad weights have total mass one. -/
theorem padChoiceWeight_sum_eq_one {x : ℝ} {K : ℕ} (a : Fin K → ℝ)
    (hV : ∀ i, 0 < bandMass x (a i)) :
    (∑ d ∈ Fintype.piFinset (fun q : Fin K × Fin (momentJ x) =>
      (Finset.univ : Finset {p : ℕ // p ∈ primeBand x (a q.1)})),
      padChoiceWeight x a d) = 1 := by
  classical
  calc
    (∑ d ∈ Fintype.piFinset (fun q : Fin K × Fin (momentJ x) =>
      (Finset.univ : Finset {p : ℕ // p ∈ primeBand x (a q.1)})),
      padChoiceWeight x a d) =
      ∏ q : Fin K × Fin (momentJ x),
          ∑ p : {p : ℕ // p ∈ primeBand x (a q.1)}, padAtomWeight x a q p := by
      simpa only [padChoiceWeight] using padChoice_product_sum a (padAtomWeight x a)
    _ = ∏ q : Fin K × Fin (momentJ x), (1 : ℝ) := by
      apply Finset.prod_congr rfl
      intro q hq
      exact padAtomWeight_sum_eq_one a hV q
    _ = 1 := by simp

end ArtinPrimitiveRoots.TypeII.PD
