import Mathlib.Analysis.Complex.Norm
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false
open scoped BigOperators
open Classical

noncomputable section
namespace ArtinPrimitiveRoots.Proofs.s7sol_zeros

/-- Dyadic multiplicity bounds give a convergent inverse-square weighted sum. -/
theorem inverse_square_of_dyadic_count {m : ℂ → ℕ} {A : ℝ}
    (hA : 0 ≤ A)
    (hfinite : ∀ R : ℝ, 0 < R → Function.HasFiniteSupport
      (fun z : ℂ => if ‖z‖ ≤ R then (m z : ℝ) else 0))
    (hcount : ∀ n : ℕ,
      (∑' z : ℂ, if ‖z‖ ≤ (2 : ℝ) ^ (n + 1) then (m z : ℝ) else 0) ≤
        A * ((n : ℝ) + 2) * (2 : ℝ) ^ (n + 1)) :
    Summable (fun z : ℂ => (m z : ℝ) * ‖z‖⁻¹ ^ 2) := by
  classical
  let f : ℂ → ℝ := fun z => (m z : ℝ) * ‖z‖⁻¹ ^ 2
  let inside : ℂ → ℝ := fun z => if ‖z‖ ≤ 1 then f z else 0
  let g : ℕ → ℂ → ℝ := fun n z =>
    if (2 : ℝ) ^ n ≤ ‖z‖ ∧ ‖z‖ < (2 : ℝ) ^ (n + 1) then f z else 0
  let D : ℕ → ℂ → ℝ := fun n z =>
    if ‖z‖ ≤ (2 : ℝ) ^ (n + 1) then (m z : ℝ) else 0
  have hf (z : ℂ) : 0 ≤ f z := by dsimp [f]; positivity
  have hg (n : ℕ) (z : ℂ) : 0 ≤ g n z := by
    dsimp [g]
    split_ifs <;> positivity
  have hD (n : ℕ) (z : ℂ) : 0 ≤ D n z := by
    dsimp [D]
    split_ifs <;> positivity
  have hinside : Function.HasFiniteSupport inside := by
    apply (hfinite 1 (by norm_num)).subset
    intro z hz
    change inside z ≠ 0 at hz
    change (if ‖z‖ ≤ 1 then (m z : ℝ) else 0) ≠ 0
    intro hzero
    apply hz
    by_cases hz1 : ‖z‖ ≤ 1
    · have hm : (m z : ℝ) = 0 := by simpa only [if_pos hz1] using hzero
      simp only [inside, if_pos hz1, f, hm, zero_mul]
    · simp only [inside, if_neg hz1]
  have hDfinite (n : ℕ) : Function.HasFiniteSupport (D n) :=
    hfinite _ (pow_pos (by norm_num) _)
  have hgfinite (n : ℕ) : Function.HasFiniteSupport (g n) := by
    apply (hDfinite n).subset
    intro z hz
    change g n z ≠ 0 at hz
    change D n z ≠ 0
    intro hzero
    apply hz
    by_cases hzn : (2 : ℝ) ^ n ≤ ‖z‖ ∧ ‖z‖ < (2 : ℝ) ^ (n + 1)
    · have hm : (m z : ℝ) = 0 := by simpa only [D, if_pos hzn.2.le] using hzero
      simp only [g, if_pos hzn, f, hm, zero_mul]
    · simp only [g, if_neg hzn]
  have hgSum (n : ℕ) : Summable (g n) := summable_of_hasFiniteSupport (hgfinite n)
  have hDSum (n : ℕ) : Summable (D n) := summable_of_hasFiniteSupport (hDfinite n)
  have hpoint (n : ℕ) (z : ℂ) :
      g n z ≤ D n z * ((2 : ℝ) ^ n)⁻¹ ^ 2 := by
    by_cases hzn : (2 : ℝ) ^ n ≤ ‖z‖ ∧ ‖z‖ < (2 : ℝ) ^ (n + 1)
    · have hi : ‖z‖⁻¹ ≤ ((2 : ℝ) ^ n)⁻¹ := inv_anti₀ (pow_pos (by norm_num) _) hzn.1
      have hh := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg z)) hi 2) (Nat.cast_nonneg (m z))
      simpa only [g, if_pos hzn, D, if_pos hzn.2.le, f] using hh
    · rw [show g n z = 0 by simp only [g, if_neg hzn]]
      exact mul_nonneg (hD n z) (sq_nonneg _)
  let b : ℕ → ℝ := fun n => 2 * A * ((n : ℝ) + 2) * (1 / 2 : ℝ) ^ n
  have hbound (n : ℕ) : (∑' z : ℂ, g n z) ≤ b n := by
    calc
      (∑' z : ℂ, g n z) ≤ ∑' z : ℂ, D n z * ((2 : ℝ) ^ n)⁻¹ ^ 2 :=
        (hgSum n).tsum_le_tsum (hpoint n) ((hDSum n).mul_right _)
      _ = (∑' z : ℂ, D n z) * ((2 : ℝ) ^ n)⁻¹ ^ 2 := (hDSum n).tsum_mul_right _
      _ ≤ (A * ((n : ℝ) + 2) * (2 : ℝ) ^ (n + 1)) * ((2 : ℝ) ^ n)⁻¹ ^ 2 :=
        mul_le_mul_of_nonneg_right (hcount n) (sq_nonneg _)
      _ = b n := by
        have hinv : (1 / 2 : ℝ) ^ n = ((2 : ℝ) ^ n)⁻¹ := by rw [one_div, inv_pow]
        dsimp [b]
        rw [hinv, pow_succ]
        field_simp [pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)]
        <;> ring
  have hgeom : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hpoly : Summable (fun n : ℕ => (n : ℝ) * (1 / 2 : ℝ) ^ n) := by
    simpa only [pow_one] using
      (summable_pow_mul_geometric_of_norm_lt_one 1 (r := (1 / 2 : ℝ)) (by norm_num))
  have hbSum : Summable b := by
    convert (hpoly.add (hgeom.mul_left 2)).mul_left (2 * A) using 1
    ext n
    dsimp [b]
    ring
  have houter : Summable (fun n : ℕ => ∑' z : ℂ, g n z) :=
    Summable.of_nonneg_of_le (fun n => tsum_nonneg (hg n)) hbound hbSum
  have hprod : Summable (fun p : ℕ × ℂ => g p.1 p.2) :=
    (summable_prod_of_nonneg (fun p : ℕ × ℂ => hg p.1 p.2)).mpr ⟨hgSum, houter⟩
  have hswap : Summable (fun p : ℂ × ℕ => g p.2 p.1) := hprod.prod_symm
  obtain ⟨hzSum, hmajorant⟩ :=
    (summable_prod_of_nonneg (fun p : ℂ × ℕ => hg p.2 p.1)).mp hswap
  apply Summable.of_nonneg_of_le hf _ ((summable_of_hasFiniteSupport hinside).add hmajorant)
  intro z
  by_cases hz : ‖z‖ ≤ 1
  · simpa only [inside, if_pos hz] using le_add_of_nonneg_right (tsum_nonneg (fun n => hg n z))
  · obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near (le_of_lt (lt_of_not_ge hz))
      (by norm_num : (1 : ℝ) < 2)
    have hzn : (2 : ℝ) ^ n ≤ ‖z‖ ∧ ‖z‖ < (2 : ℝ) ^ (n + 1) := ⟨hn1, hn2⟩
    have hle := (hzSum z).le_tsum n (fun j _ => hg j z)
    rw [show g n z = f z by simp only [g, if_pos hzn]] at hle
    simpa only [inside, if_neg hz, zero_add] using hle

end ArtinPrimitiveRoots.Proofs.s7sol_zeros
