import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.RationalSpacing
import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.SeparatedGeometric

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD

noncomputable section

/-- Grouping a range into half-denominator blocks bounds all its geometric rows. -/
theorem rational_geometric_range_bound (c : ℤ) (d M N : ℕ)
    (hd : 2 ≤ d) (hcop : Int.gcd c (d : ℤ) = 1)
    (θ : ℝ) (happrox : |θ - (c : ℝ)/(d : ℝ)| ≤ 1/(d : ℝ)^2)
    (m : ℤ) :
    (∑ i ∈ Finset.range M, ‖∑ n ∈ Finset.range N,
      additiveCharacter ((((i : ℤ)-m : ℤ) : ℝ)*θ*(n : ℝ))‖) ≤
    ((M/(d/2)+1 : ℕ) : ℝ) *
      ((N : ℝ)+32*(d : ℝ)*(1+Real.log (4*(d : ℝ)))) := by
  let q := d/2
  let φ (i : ℕ) : ℝ := (((i : ℤ)-m : ℤ) : ℝ)*θ
  let g (i : ℕ) : ℝ := ‖∑ n ∈ Finset.range N, additiveCharacter (φ i*(n : ℝ))‖
  let block (b : ℕ) := (Finset.range M).filter fun i => i/q=b
  let C : ℝ := (N : ℝ)+32*(d : ℝ)*(1+Real.log (4*(d : ℝ)))
  have hq : 0 < q := by dsimp only [q]; omega
  have hqd : (q : ℝ) ≤ (d : ℝ)/2 := by
    have h : 2*q ≤ d := by dsimp only [q]; omega
    have hR : 2*(q : ℝ) ≤ (d : ℝ) := by exact_mod_cast h
    linarith only [hR]
  have hsep (b : ℕ) (i : ℕ) (hi : i ∈ block b) (j : ℕ) (hj : j ∈ block b)
      (hne : i ≠ j) : 1/(2*(d : ℝ)) ≤ circleDistance (φ i-φ j) := by
    have hiq : i/q=b := (Finset.mem_filter.mp hi).2
    have hjq : j/q=b := (Finset.mem_filter.mp hj).2
    have hiR : (i : ℝ) = ((i%q : ℕ) : ℝ)+(q : ℝ)*(b : ℝ) := by
      have h := (Nat.mod_add_div i q).symm
      rw [hiq] at h
      exact_mod_cast h
    have hjR : (j : ℝ) = ((j%q : ℕ) : ℝ)+(q : ℝ)*(b : ℝ) := by
      have h := (Nat.mod_add_div j q).symm
      rw [hjq] at h
      exact_mod_cast h
    have hri : ((i%q : ℕ) : ℝ) < (q : ℝ) := by exact_mod_cast Nat.mod_lt i hq
    have hrj : ((j%q : ℕ) : ℝ) < (q : ℝ) := by exact_mod_cast Nat.mod_lt j hq
    have hri0 : (0 : ℝ) ≤ ((i%q : ℕ) : ℝ) := by positivity
    have hrj0 : (0 : ℝ) ≤ ((j%q : ℕ) : ℝ) := by positivity
    have hsmall : |(i : ℝ)-(j : ℝ)| ≤ (q : ℝ) := by
      apply abs_le.mpr
      constructor <;> linarith only [hiR, hjR, hri, hrj, hri0, hrj0]
    have hblock : |(((i : ℤ)-(j : ℤ) : ℤ) : ℝ)| ≤ (d : ℝ)/2 := by
      push_cast
      exact hsmall.trans hqd
    have hneZ : (i : ℤ) ≠ (j : ℤ) := by exact_mod_cast hne
    have heq : φ i-φ j = (((i : ℤ)-(j : ℤ) : ℤ) : ℝ)*θ := by
      dsimp only [φ]
      push_cast
      ring
    rw [heq]
    exact rational_block_spacing c d hd hcop θ happrox (i : ℤ) (j : ℤ) hneZ hblock
  have hblockSum (b : ℕ) : (∑ i ∈ block b, g i) ≤ C :=
    separated_geometric_row_bound (block b) φ d N hd (hsep b)
  have hreindex : (∑ i ∈ Finset.range M, g i) =
      ∑ b ∈ Finset.range (M/q+1), ∑ i ∈ block b, g i := by
    dsimp only [block]
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    have hiB : i/q ∈ Finset.range (M/q+1) := by
      apply Finset.mem_range.mpr
      have h : i/q ≤ M/q := Nat.div_le_div_right (Nat.le_of_lt (Finset.mem_range.mp hi))
      omega
    symm
    rw [Finset.sum_eq_single (i/q)]
    · simp only [ite_true]
    · intro b hb hne
      exact if_neg (Ne.symm hne)
    · intro hn
      exact False.elim (hn hiB)
  change (∑ i ∈ Finset.range M, g i) ≤ ((M/q+1 : ℕ) : ℝ)*C
  rw [hreindex]
  calc
    _ ≤ ∑ b ∈ Finset.range (M/q+1), C :=
      Finset.sum_le_sum fun b hb => hblockSum b
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
