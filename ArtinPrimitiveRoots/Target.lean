import ArtinPrimitiveRoots.Reduction

/-!
# The target

`S` and the statement are identical to `Challenge.lean` (with `S` copied verbatim from Formal
Conjectures' `ArtinPrimitiveRootsConjecture.S`); this module proves it.
-/

namespace ArtinPrimitiveRootsConjecture

/-- Let $S(a)$ be the set of primes such that $a$ is a primitive root modulo $p$. -/
abbrev S (a : ℤ) : Set ℕ :=
  {p : ℕ | p.Prime ∧ orderOf (a : ZMod p) = (p-1 : ℕ)}

/-- **Artin's primitive root conjecture, infinitude form.** Every integer `a` that is neither `-1`
nor a perfect square is a primitive root modulo infinitely many primes. -/
theorem artin_primitive_roots_infinite :
    ∀ a : ℤ, a ≠ -1 → ¬ IsSquare a → (S a).Infinite := by
  intro a ha hns
  classical
  obtain ⟨c, hc, X, hX, hmain⟩ := ArtinPrimitiveRoots.thm_main a ha hns
  intro hfinite
  have hbound := hfinite.bddAbove
  obtain ⟨N, hN⟩ := hbound
  let x : ℝ := max X ((N : ℝ) + 1)
  have hxX : X ≤ x := le_max_left _ _
  have hxN : (N : ℝ) < x := by
    dsimp [x]
    have hN' : (N : ℝ) < (N : ℝ) + 1 := by norm_num
    exact lt_of_lt_of_le hN' (le_max_right _ _)
  have hposx : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_trans hX hxX)
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hmainx := hmain x hxX
  have hpos : 0 < c * x / Real.log x ^ 2 := by positivity
  let P : Set ℕ := {p | p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) < 2 * x ∧ ¬ (p : ℤ) ∣ a ∧
          orderOf (a : ZMod p) = p - 1}
  have hcount : 0 < (P.ncard : ℝ) := lt_of_lt_of_le hpos hmainx
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * x)
  have hPfin : P.Finite := (Set.finite_Iio n).subset (by
    intro p hp
    change p < n
    exact_mod_cast lt_trans hp.2.2.1 hn)
  have hset : P.Nonempty := by
    apply (Set.ncard_pos hPfin).mp
    exact_mod_cast hcount
  rcases hset with ⟨p, hpPrime, hpx, hp2x, hpa, horder⟩
  have hpS : p ∈ S a := ⟨hpPrime, horder⟩
  have hple : p ≤ N := hN hpS
  have hreal : (p : ℝ) ≤ (N : ℝ) := by exact_mod_cast hple
  linarith

end ArtinPrimitiveRootsConjecture
