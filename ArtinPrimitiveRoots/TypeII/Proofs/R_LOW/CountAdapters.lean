import ArtinPrimitiveRoots.TypeII.Marked
import ArtinPrimitiveRoots.TypeII.PP.Defs

namespace ArtinPrimitiveRoots.Proofs.r_impl_muse

open Classical ArtinPrimitiveRoots.TypeII
open scoped BigOperators

theorem prime_interval_bound_of_closed (N B : ℝ) (q : ℕ)
    (χ : DirichletCharacter ℂ q) (I : Set ℕ)
    (hN : 0 ≤ N) (hB : 0 ≤ B) (hinterval : IsNatInterval I)
    (hI : I ⊆ {p : ℕ | N ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * N})
    (hclosed : ∀ a b : ℝ, N ≤ a → a ≤ b → b ≤ 2 * N →
      ‖∑ p ∈ (Finset.range (⌊b⌋₊ + 1)).filter
          (fun p : ℕ => p.Prime ∧ a ≤ (p : ℝ) ∧ (p : ℝ) ≤ b),
        χ (p : ZMod q)‖ ≤ B) :
    ‖PP.primePhaseSum N q χ 0 I‖ ≤ B := by
  let T : Finset ℕ := (Finset.range (⌊2 * N⌋₊ + 1)).filter (fun p => p ∈ I)
  have h2N : 0 ≤ 2 * N := by positivity
  have hT : ∀ p : ℕ, p ∈ T ↔ p ∈ I := by
    intro p
    simp only [T, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
    constructor
    · exact fun hp => hp.2
    · intro hp
      exact ⟨(Nat.le_floor_iff h2N).mpr (hI hp).2, hp⟩
  by_cases hTne : T.Nonempty
  · let a : ℕ := T.min' hTne
    let b : ℕ := T.max' hTne
    have haI : a ∈ I := (hT a).mp (T.min'_mem hTne)
    have hbI : b ∈ I := (hT b).mp (T.max'_mem hTne)
    have hab : a ≤ b := T.min'_le_max' hTne
    have hIcc : ∀ p : ℕ, p ∈ I ↔ a ≤ p ∧ p ≤ b := by
      intro p
      constructor
      · intro hp
        have hpT : p ∈ T := (hT p).mpr hp
        exact ⟨T.min'_le p hpT, T.le_max' p hpT⟩
      · intro hp
        apply hinterval haI hbI
        · simpa only [min_eq_left hab] using hp.1
        · simpa only [max_eq_right hab] using hp.2
    have hsets :
        (Finset.range (⌊2 * N⌋₊ + 1)).filter (fun p : ℕ =>
          p.Prime ∧ N ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * N ∧ p ∈ I) =
        (Finset.range (⌊(b : ℝ)⌋₊ + 1)).filter (fun p : ℕ =>
          p.Prime ∧ (a : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) ≤ (b : ℝ)) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff,
        Nat.floor_natCast, Nat.cast_le]
      constructor
      · rintro ⟨_hpFloor, hpPrime, _hpN, _hp2N, hpI⟩
        exact ⟨(hIcc p).mp hpI |>.2, hpPrime, (hIcc p).mp hpI⟩
      · rintro ⟨_hpB, hpPrime, hpA, hpB⟩
        have hpI : p ∈ I := (hIcc p).mpr ⟨hpA, hpB⟩
        exact ⟨(Nat.le_floor_iff h2N).mpr (hI hpI).2,
          hpPrime, (hI hpI).1, (hI hpI).2, hpI⟩
    simp only [PP.primePhaseSum, Complex.ofReal_zero, mul_zero, zero_mul,
      Complex.exp_zero, mul_one]
    rw [hsets]
    exact hclosed (a : ℝ) (b : ℝ) (hI haI).1 (by exact_mod_cast hab) (hI hbI).2
  · have hIempty : I = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact hTne ⟨p, (hT p).mpr hp⟩
    simpa [PP.primePhaseSum, hIempty] using hB

end ArtinPrimitiveRoots.Proofs.r_impl_muse
