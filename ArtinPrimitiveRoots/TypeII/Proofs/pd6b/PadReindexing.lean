import ArtinPrimitiveRoots.TypeII.PD.Physical
import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.PadProbability

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

open ArtinPrimitiveRoots.TypeII
open Classical

noncomputable section

/-- Split a physical list into its copied slots and its one fresh slot. -/
theorem listProduct_eq_shared_mul_last {x : ℝ} {K : ℕ}
    (p : PrimeLists x K) :
    (∏ i : Fin K, ∏ j : Fin (slotCount x), p i j) =
      sharedProduct p * lastProduct p := by
  dsimp only [PrimeLists, slotCount] at p
  have hgroup (i : Fin K) :
      (∏ j : Fin (slotCount x), p i j) =
        (∏ j : Fin (slotCount x), if j.val < momentJ x then p i j else 1) *
          p i (lastSlot x) := by
    change (∏ j : Fin (momentJ x + 1), p i j) =
      (∏ j : Fin (momentJ x + 1), if j.val < momentJ x then p i j else 1) *
        p i (Fin.last (momentJ x))
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
    simp
  simp_rw [hgroup]
  exact Finset.prod_mul_distrib

/-- A list is uniquely specified by its shared slots and its last slot. -/
theorem lists_ext_shared_last {x : ℝ} {K : ℕ} {p q : PrimeLists x K}
    (hshared : ∀ i (j : Fin (momentJ x)), p i j.castSucc = q i j.castSucc)
    (hlast : ∀ i, p i (lastSlot x) = q i (lastSlot x)) : p = q := by
  dsimp only [PrimeLists, slotCount] at p q
  funext i j
  induction j using Fin.lastCases with
  | last => exact hlast i
  | cast j => exact hshared i j

/-- For a slot transition the copied products coincide. -/
theorem sharedProduct_eq_of_slotTransition {x : ℝ} {K : ℕ}
    {p q : PrimeLists x K} (h : IsSlotTransition p q) :
    sharedProduct p = sharedProduct q := by
  unfold sharedProduct
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro j hj
  split_ifs with hslot
  · exact (h.1 i j hslot).symm
  · rfl

/-- Cancel the selected pad dyad from the geometric scalar. -/
theorem padDyad_scalar_cancel (d D : ℕ) (hd : 0 < d) :
    (d : ℂ)⁻¹ * (((d : ℝ) / (D : ℝ) : ℝ) : ℂ) = (D : ℂ)⁻¹ := by
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  push_cast
  rw [div_eq_mul_inv]
  rw [← mul_assoc, inv_mul_cancel₀ hdC, one_mul]

/-- The endpoint coefficient order in the physical pairing is the Cauchy order. -/
theorem endpoint_coefficient_product (α β : ℕ → ℂ) (m n r s : ℕ) :
    (α m * star (β s)) * (star (α r) * β n) =
      α m * star (α r) * β n * star (β s) := by ring

/-- The determinant after inserting a common pad product. -/
theorem det2_pad_positions (D a b m n r s : ℕ) :
    det2 ((D * b * m : ℕ), (s : ℤ)) ((D * a * r : ℕ), (n : ℤ)) =
      (D : ℤ) * ((b : ℤ) * m * n - (a : ℤ) * r * s) := by
  simp only [det2, Nat.cast_mul]
  ring

/-- Its quotient is exact because the common pad product is positive. -/
theorem det2_pad_positions_div (D a b m n r s : ℕ) (hD : 0 < D) :
    det2 ((D * b * m : ℕ), (s : ℤ)) ((D * a * r : ℕ), (n : ℤ)) / (D : ℤ) =
      (b : ℤ) * m * n - (a : ℤ) * r * s := by
  rw [det2_pad_positions]
  exact Int.mul_ediv_cancel_left _ (by exact_mod_cast Nat.ne_of_gt hD)

/-- Rough numbers are coprime to numbers all of whose prime factors are small. -/
theorem rough_coprime_of_prime_bound {W : ℝ} {d n : ℕ}
    (hd : ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) ≤ W)
    (hn : roughAbove n W) : Nat.Coprime d n := by
  by_contra h
  obtain ⟨p, hp, hpd, hpn⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  exact not_lt_of_ge (hd p hp hpd) (hn p hp hpn)

/-- Disjoint selected products and rough coefficients exclude a zero determinant. -/
theorem pad_determinant_ne_zero {W : ℝ} {a b m n r s : ℕ}
    (hb : 1 < b) (hab : Nat.Coprime a b)
    (hsmall : ∀ p : ℕ, p.Prime → p ∣ b → (p : ℝ) ≤ W)
    (hr : roughAbove r W) (hs : roughAbove s W) :
    (b : ℤ) * m * n - (a : ℤ) * r * s ≠ 0 := by
  intro hzero
  have heq : b * m * n = a * r * s := by
    have h := sub_eq_zero.mp hzero
    exact_mod_cast h
  have hbdiv : b ∣ a * r * s := by
    rw [← heq]
    exact dvd_mul_of_dvd_left (dvd_mul_right b m) n
  have hbr : Nat.Coprime b r := rough_coprime_of_prime_bound hsmall hr
  have hbs : Nat.Coprime b s := rough_coprime_of_prime_bound hsmall hs
  have hcop : Nat.Coprime b (a * r * s) := (hab.symm.mul_right hbr).mul_right hbs
  have hbone : b = 1 := by
    have hg := hcop.gcd_eq_one
    rw [Nat.gcd_eq_left hbdiv] at hg
    exact hg
  omega

/-- A common prime in two coefficients would divide a short nonzero determinant. -/
theorem coprime_of_short_pad_determinant {W : ℝ} {a b m n r s : ℕ}
    (hs : roughAbove s W)
    (ht : (b : ℤ) * m * n - (a : ℤ) * r * s ≠ 0)
    (htsmall : |(((b : ℤ) * m * n - (a : ℤ) * r * s : ℤ) : ℝ)| ≤ W) :
    Nat.Coprime m s := by
  by_contra h
  obtain ⟨p, hp, hpm, hps⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  have hpmZ : (p : ℤ) ∣ (m : ℤ) := by exact_mod_cast hpm
  have hpsZ : (p : ℤ) ∣ (s : ℤ) := by exact_mod_cast hps
  have hpt : (p : ℤ) ∣ (b : ℤ) * m * n - (a : ℤ) * r * s :=
    dvd_sub (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hpmZ _) _)
      (dvd_mul_of_dvd_right hpsZ _)
  have hple : (p : ℤ) ≤ |(b : ℤ) * m * n - (a : ℤ) * r * s| :=
    Int.le_abs_of_dvd ht hpt
  have hpleR : (p : ℝ) ≤ |(((b : ℤ) * m * n - (a : ℤ) * r * s : ℤ) : ℝ)| := by
    exact_mod_cast hple
  exact not_lt_of_ge (hpleR.trans htsmall) (hs p hp hps)

/-- Both positions reconstructed from rough Cauchy coefficients are primitive. -/
theorem pad_positions_coprime {W : ℝ} {D a b m n r s : ℕ}
    (hDb : ∀ p : ℕ, p.Prime → p ∣ D * b → (p : ℝ) ≤ W)
    (hDa : ∀ p : ℕ, p.Prime → p ∣ D * a → (p : ℝ) ≤ W)
    (hn : roughAbove n W) (hs : roughAbove s W)
    (ht : (b : ℤ) * m * n - (a : ℤ) * r * s ≠ 0)
    (htsmall : |(((b : ℤ) * m * n - (a : ℤ) * r * s : ℤ) : ℝ)| ≤ W) :
    Nat.Coprime (D * b * m) s ∧ Nat.Coprime (D * a * r) n := by
  have hms : Nat.Coprime m s := coprime_of_short_pad_determinant hs ht htsmall
  have hrn : Nat.Coprime r n := by
    apply coprime_of_short_pad_determinant hn
      (a := b) (b := a) (m := r) (n := s) (r := m)
    · exact sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp ht))
    · simpa only [Int.cast_sub, abs_sub_comm] using htsmall
  exact ⟨(rough_coprime_of_prime_bound hDb hs).mul_left hms,
    (rough_coprime_of_prime_bound hDa hn).mul_left hrn⟩

/-- The raw determinant equation is the common-predecessor equation on positive products. -/
theorem raw_det_iff_common_predecessor (a b m n r s : ℕ)
    (ha : 0 < a) (hab : Nat.Coprime a b) (hmn : 1 ≤ m * n) (hrs : 1 ≤ r * s) :
    ((b : ℤ) * m * n - (a : ℤ) * r * s = (b : ℤ) - a) ↔
      ∃ h : ℕ, m * n - 1 = a * h ∧ r * s - 1 = b * h := by
  have hmnZ : ((m * n - 1 : ℕ) : ℤ) = (m : ℤ) * n - 1 := by
    rw [Nat.cast_sub hmn]
    push_cast
    rfl
  have hrsZ : ((r * s - 1 : ℕ) : ℤ) = (r : ℤ) * s - 1 := by
    rw [Nat.cast_sub hrs]
    push_cast
    rfl
  constructor
  · intro hdet
    have heq : b * (m * n - 1) = a * (r * s - 1) := by
      have heqZ : (b : ℤ) * ((m * n - 1 : ℕ) : ℤ) =
          (a : ℤ) * ((r * s - 1 : ℕ) : ℤ) := by
        rw [hmnZ, hrsZ]
        nlinarith [hdet]
      exact_mod_cast heqZ
    have hdiv : a ∣ m * n - 1 := hab.dvd_of_dvd_mul_left
      (by rw [heq]; exact dvd_mul_right a (r * s - 1))
    let h := (m * n - 1) / a
    have hmEq : m * n - 1 = a * h := (Nat.mul_div_cancel' hdiv).symm
    have hsEq : r * s - 1 = b * h := by
      have hmul : a * (r * s - 1) = a * (b * h) := by rw [← heq, hmEq]; ring
      exact Nat.eq_of_mul_eq_mul_left ha hmul
    exact ⟨h, hmEq, hsEq⟩
  · rintro ⟨h, hmEq, hsEq⟩
    have hmZ : (m : ℤ) * n - 1 = (a : ℤ) * h := by
      have hcast := congrArg (fun z : ℕ => (z : ℤ)) hmEq
      simpa only [hmnZ, Nat.cast_mul] using hcast
    have hsZ : (r : ℤ) * s - 1 = (b : ℤ) * h := by
      have hcast := congrArg (fun z : ℕ => (z : ℤ)) hsEq
      simpa only [hrsZ, Nat.cast_mul] using hcast
    nlinarith

/-- The fixed copied-slot product is the omission of each group's last slot. -/
theorem sharedProduct_eq_omission_last {x : ℝ} {K : ℕ} (p : PrimeLists x K) :
    sharedProduct p = omissionProduct p (fun _ => lastSlot x) := by
  have hiff (j : Fin (slotCount x)) : j.val < momentJ x ↔ j ≠ lastSlot x := by
    have hj : j.val < momentJ x + 1 := by simpa only [slotCount] using j.isLt
    constructor
    · intro h heq
      have hv := congrArg Fin.val heq
      simp only [lastSlot] at hv
      omega
    · intro hne
      by_contra hnot
      have hv : j.val = momentJ x := by omega
      have heq : j = lastSlot x := Fin.ext hv
      exact hne heq
  unfold sharedProduct omissionProduct
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro j hj
  by_cases h : j.val < momentJ x
  · have hne := (hiff j).mp h
    simp only [if_pos h, if_pos hne]
  · have heq : j = lastSlot x := by
      by_contra hne
      exact h ((hiff j).mpr hne)
    subst j
    simp [lastSlot]


end

end ArtinPrimitiveRoots.TypeII.PD
