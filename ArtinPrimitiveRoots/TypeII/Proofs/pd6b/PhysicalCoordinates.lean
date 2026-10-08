import ArtinPrimitiveRoots.TypeII.PD.Physical

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical

noncomputable section

/-- Canonical determinant-one completion of a positive primitive natural vector. -/
theorem canonical_completion (u v : ℕ) (hu : 0 < u) (hcop : Nat.Coprime u v) :
    let c := (-Int.gcdB (u : ℤ) (v : ℤ)) % (u : ℤ)
    let d := Int.gcdA (u : ℤ) (v : ℤ) -
      (v : ℤ) * ((-Int.gcdB (u : ℤ) (v : ℤ)) / (u : ℤ))
    (u : ℤ) * d - (v : ℤ) * c = 1 ∧ 0 ≤ c ∧ c < (u : ℤ) := by
  have huZ : 0 < (u : ℤ) := by exact_mod_cast hu
  have hbezout := Int.gcd_eq_gcd_ab (u : ℤ) (v : ℤ)
  rw [Int.gcd_natCast_natCast, hcop.gcd_eq_one] at hbezout
  refine ⟨?_, Int.emod_nonneg _ huZ.ne', Int.emod_lt_of_pos _ huZ⟩
  rw [Int.emod_def]
  calc
    _ = (u : ℤ) * Int.gcdA (u : ℤ) (v : ℤ) +
        (v : ℤ) * Int.gcdB (u : ℤ) (v : ℤ) := by ring
    _ = 1 := hbezout.symm

theorem physicalState_eq_of_coordinates
    {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {H' Hm Hn : ℝ}
    (P Q : PhysicalState x K a H' Hm Hn)
    (hfirst : P.first = Q.first) (hsecond : P.second = Q.second)
    (hlabels : P.labels = Q.labels) : P = Q := by
  have hfirstPos : 0 < P.first := by
    have hrange := P.completion_range
    have hpos : (0 : ℤ) < (P.first : ℤ) := lt_of_le_of_lt hrange.1 hrange.2
    exact_mod_cast hpos
  have hcop : Int.gcd (P.first : ℤ) (P.second : ℤ) = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact P.primitive.gcd_eq_one
  have hfirstZ : (P.first : ℤ) = (Q.first : ℤ) := by exact_mod_cast hfirst
  have hsecondZ : (P.second : ℤ) = (Q.second : ℤ) := by exact_mod_cast hsecond
  have hdiv : (P.first : ℤ) ∣ (P.completionC - Q.completionC) * (P.second : ℤ) := by
    have hQdet : (P.first : ℤ) * Q.completionD -
        (P.second : ℤ) * Q.completionC = 1 := by
      simpa [hfirstZ.symm, hsecondZ.symm] using Q.det_one
    refine ⟨P.completionD - Q.completionD, ?_⟩
    calc
      (P.completionC - Q.completionC) * (P.second : ℤ) =
          (1 + (P.second : ℤ) * P.completionC) -
            (1 + (P.second : ℤ) * Q.completionC) := by ring
      _ = (((P.first : ℤ) * P.completionD - (P.second : ℤ) * P.completionC) +
            (P.second : ℤ) * P.completionC) -
          (((P.first : ℤ) * Q.completionD - (P.second : ℤ) * Q.completionC) +
            (P.second : ℤ) * Q.completionC) := by rw [P.det_one, hQdet]
      _ = (P.first : ℤ) * (P.completionD - Q.completionD) := by ring
  have hcdiv : (P.first : ℤ) ∣ P.completionC - Q.completionC :=
    Int.dvd_of_dvd_mul_left_of_gcd_one hdiv hcop
  have hQupper : Q.completionC < (P.first : ℤ) := by
    calc
      Q.completionC < (Q.first : ℤ) := Q.completion_range.2
      _ = (P.first : ℤ) := hfirstZ.symm
  have hcabs : |P.completionC - Q.completionC| < (P.first : ℤ) := by
    rw [abs_lt]
    constructor
    · have h := P.completion_range.1
      have h' := Q.completion_range.1
      omega
    · have h := P.completion_range.2
      have h' := Q.completion_range.1
      omega
  have hC : P.completionC = Q.completionC := by
    have hz := Int.eq_zero_of_abs_lt_dvd hcdiv hcabs
    exact sub_eq_zero.mp hz
  have hDmul : (P.first : ℤ) * P.completionD = (P.first : ℤ) * Q.completionD := by
    have hQdet : (P.first : ℤ) * Q.completionD -
        (P.second : ℤ) * Q.completionC = 1 := by
      simpa [hfirstZ.symm, hsecondZ.symm] using Q.det_one
    calc
      (P.first : ℤ) * P.completionD =
          ((P.first : ℤ) * P.completionD - (P.second : ℤ) * P.completionC) +
            (P.second : ℤ) * P.completionC := by ring
      _ = ((P.first : ℤ) * Q.completionD - (P.second : ℤ) * Q.completionC) +
            (P.second : ℤ) * Q.completionC := by rw [P.det_one, hQdet, hC]
      _ = (P.first : ℤ) * Q.completionD := by ring
  have hD : P.completionD = Q.completionD :=
    mul_left_cancel₀ (by exact_mod_cast (Nat.ne_of_gt hfirstPos)) hDmul
  cases P
  cases Q
  simp_all

/-- Positions and labels with exactly the fields needed to reconstruct a physical state. -/
abbrev PhysicalCoordinates (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (H Hm Hn : ℝ) :=
  {t : (ℕ × ℕ) × PrimeLists x K //
    Nat.Coprime t.1.1 t.1.2 ∧ 0 < t.1.1 ∧
    H * Hm ≤ (t.1.1 : ℝ) ∧ (t.1.1 : ℝ) ≤ 16 * H * Hm ∧
    Hn ≤ (t.1.2 : ℝ) ∧ (t.1.2 : ℝ) ≤ 2 * Hn ∧
    ValidPrimeLists x K a t.2 ∧ ∀ i j, t.2 i j ∣ t.1.1}

/-- Build the unique physical state from its primitive position and valid dividing labels. -/
def physicalStateFromCoordinates {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {H Hm Hn : ℝ}
    (t : PhysicalCoordinates x K a H Hm Hn) : PhysicalState x K a H Hm Hn where
  first := t.val.1.1
  second := t.val.1.2
  completionC := (-Int.gcdB (t.val.1.1 : ℤ) (t.val.1.2 : ℤ)) % (t.val.1.1 : ℤ)
  completionD := Int.gcdA (t.val.1.1 : ℤ) (t.val.1.2 : ℤ) -
    (t.val.1.2 : ℤ) * ((-Int.gcdB (t.val.1.1 : ℤ) (t.val.1.2 : ℤ)) / (t.val.1.1 : ℤ))
  labels := t.val.2
  primitive := t.property.1
  first_lower := t.property.2.2.1
  first_upper := t.property.2.2.2.1
  second_lower := t.property.2.2.2.2.1
  second_upper := t.property.2.2.2.2.2.1
  det_one := (canonical_completion t.val.1.1 t.val.1.2 t.property.2.1 t.property.1).1
  completion_range := (canonical_completion t.val.1.1 t.val.1.2 t.property.2.1 t.property.1).2
  label_prime := fun i j => (t.property.2.2.2.2.2.2.1.1 i j).1
  label_in_band := fun i j => (t.property.2.2.2.2.2.2.1.1 i j).2
  label_divides := t.property.2.2.2.2.2.2.2
  label_distinct := t.property.2.2.2.2.2.2.1.2

/-- Completions introduce no multiplicity in the physical counting sum. -/
def physicalStateCoordinatesEquiv (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (H Hm Hn : ℝ) :
    PhysicalState x K a H Hm Hn ≃ PhysicalCoordinates x K a H Hm Hn where
  toFun P := ⟨((P.first, P.second), P.labels),
    ⟨P.primitive, by
      have hpos : (0 : ℤ) < (P.first : ℤ) :=
        lt_of_le_of_lt P.completion_range.1 P.completion_range.2
      exact_mod_cast hpos,
      P.first_lower, P.first_upper, P.second_lower, P.second_upper,
      ⟨fun i j => ⟨P.label_prime i j, P.label_in_band i j⟩, P.label_distinct⟩,
      P.label_divides⟩⟩
  invFun := physicalStateFromCoordinates
  left_inv P := physicalState_eq_of_coordinates _ _ rfl rfl rfl
  right_inv t := Subtype.ext rfl

end
end ArtinPrimitiveRoots.TypeII.PD
