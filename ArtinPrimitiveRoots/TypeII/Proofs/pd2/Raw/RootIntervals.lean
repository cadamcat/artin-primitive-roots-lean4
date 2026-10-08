import ArtinPrimitiveRoots.TypeII.Proofs.pd2.Raw.RootFourier

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical ArtinPrimitiveRoots.TypeII
set_option maxHeartbeats 1000000

lemma pd2a_root_character_nat_fraction (m t : ℕ) [NeZero m] :
    additiveCharacter ((t : ℝ) / m) = ZMod.stdAddChar (t : ZMod m) := by
  have hcast : (t : ZMod m) = ((t : ℤ) : ZMod m) := by norm_cast
  rw [hcast, ZMod.stdAddChar_coe]
  unfold additiveCharacter
  congr 1
  push_cast
  ring

lemma pd2a_root_interval_character_bound (m a N : ℕ) [NeZero m] (h : ZMod m) (hh : h ≠ 0) :
    ‖∑ n ∈ Finset.range N, ZMod.stdAddChar (h * ((a + n : ℕ) : ZMod m))‖ ≤
      2 * (m : ℝ) / (min h.val (m - h.val) : ℕ) := by
  have hm : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hv : h.val < m := ZMod.val_lt h
  have hvpos : 0 < h.val := by
    by_contra hn
    have hz : h.val = 0 := by omega
    have hcast := ZMod.natCast_zmod_val h
    rw [hz, Nat.cast_zero] at hcast
    exact hh hcast.symm
  let d := min h.val (m - h.val)
  let θ := (h.val : ℝ) / m
  let β := (d : ℝ) / m
  have hd : 0 < d := by dsimp [d]; omega
  have hβ : 0 < β := by dsimp [β]; positivity
  have hlow : β ≤ θ := by
    dsimp [β, θ]
    apply div_le_div_of_nonneg_right _ hm.le
    exact_mod_cast min_le_left h.val (m - h.val)
  have hhigh : θ ≤ 1 - β := by
    have hdle : (d : ℝ) ≤ (m : ℝ) - h.val := by
      have hmin := min_le_right h.val (m - h.val)
      have hn : (d : ℝ) ≤ ((m - h.val : ℕ) : ℝ) := by exact_mod_cast hmin
      rw [Nat.cast_sub hv.le] at hn
      exact hn
    dsimp [θ, β]
    apply (le_sub_iff_add_le).mpr
    rw [← add_div]
    apply (div_le_one hm).mpr
    linarith
  let f := fun n : ℕ => θ * ((a + n : ℕ) : ℝ)
  have hstep : ∀ n : ℕ, f (n + 1) - f n = θ := by
    intro n
    dsimp [f]
    push_cast
    ring
  have hbound := ArtinPrimitiveRoots.Ext.TypeIIInputs.derivative_test f N β hβ
    (fun n hn => by rw [hstep]; exact hlow) (fun n hn => by rw [hstep]; exact hhigh)
    (fun i hi j hj hij => by dsimp only; rw [hstep, hstep])
  have hsum : (∑ n ∈ Finset.range N, ZMod.stdAddChar (h * ((a + n : ℕ) : ZMod m))) =
      ∑ n ∈ Finset.range N, additiveCharacter (f n) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hchar := pd2a_root_character_nat_fraction m (h.val * (a + n))
    simp only [Nat.cast_mul, ZMod.natCast_zmod_val] at hchar
    rw [← hchar]
    congr 1
    dsimp [f, θ]
    push_cast
    ring
  rw [hsum]
  calc
    _ ≤ 2 / β := hbound
    _ = _ := by dsimp [β, d]; field_simp

end ArtinPrimitiveRoots.TypeII.PD
