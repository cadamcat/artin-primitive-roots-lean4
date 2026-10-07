import Mathlib
import ArtinPrimitiveRoots.Splitting.Counting

/-!
# A uniform bound for complete splitting (paper: Proposition `prop:splitting`)

Source: `01a-reduction.tex`, lines 50–63; proved in `07-splitting.tex` from Theorem
`thm:hecke-zero-free`. Frozen interface, consumed by `thm_main`.

The paper counts primes `p` that split completely in `K_q = ℚ(μ_q, a^{1/q})`. This interface uses
the elementary condition `q ∣ p - 1 ∧ a^{(p-1)/q} ≡ 1 (mod p)`, which by the splitting test
(`alg:splitting-test`) implies complete splitting in `K_q` (the condition already forces `p ∤ a q`),
so the statement below follows from the paper's.
-/

namespace ArtinPrimitiveRoots

/-- **Proposition `prop:splitting`**, elementary form. Fix an integer `a` with `|a| > 1` and put
`δ₀ = 10⁻⁶`. There are `C`, `q₀` and `X` such that for every real `x ≥ X` and every prime
`q ≥ q₀` with `q ≤ exp((log x)^0.3)`, the number of primes `p ∈ (x, 2x]` with `q ∣ p - 1` and
`a^{(p-1)/q} ≡ 1 (mod p)` is at most `C (x / (q (q - 1) log x) + x^{1-δ₀})`. -/
theorem prop_splitting (a : ℤ) (ha : 1 < |a|) :
    ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ, ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ, q.Prime → q₀ ≤ q →
      (q : ℝ) ≤ Real.exp (Real.log x ^ (3 / 10 : ℝ)) →
        (({p : ℕ | p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x ∧ q ∣ p - 1 ∧
            (a : ZMod p) ^ ((p - 1) / q) = 1} : Set ℕ).ncard : ℝ) ≤
          C * (x / ((q : ℝ) * ((q : ℝ) - 1) * Real.log x) + x ^ (1 - (1 / 1000000 : ℝ))) := by
  have ha0 : a ≠ 0 := by
    intro hz
    simp [hz] at ha
  obtain ⟨C, hC, q₀, hq₀, X, hX, hbound⟩ :=
    ArtinPrimitiveRoots.Splitting.sp_count_from_theta a ha
  refine ⟨C, hC, q₀, X, ?_⟩
  intro x hx q hq hq₀ hqexp
  letI : NeZero q := ⟨hq.ne_zero⟩
  have hPnotA : ∀ p : ℕ, p.Prime → q ∣ p - 1 →
      (a : ZMod p) ^ ((p - 1) / q) = 1 → ¬ (p : ℤ) ∣ a := by
    intro p hp hdiv hpow hpA
    letI : Fact p.Prime := ⟨hp⟩
    have hp2 : 2 ≤ p := hp.two_le
    have hpminus : 0 < p - 1 := by
      omega
    have hple : q ≤ p - 1 := Nat.le_of_dvd hpminus hdiv
    have hexp : 0 < (p - 1) / q := Nat.div_pos hple hq.pos
    have hbase : (a : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd a p).mpr hpA
    have hzero := hpow
    rw [hbase] at hzero
    simp [zero_pow (Nat.ne_of_gt hexp)] at hzero
  have hPnotQ : ∀ p : ℕ, p.Prime → q ∣ p - 1 → ¬ p ∣ q := by
    intro p hp hdiv hpq
    have hq2 : 2 ≤ q := hq.two_le
    have hpq' : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp hpq
    rw [hpq'] at hdiv
    have hqminus : 0 < q - 1 := by omega
    have hle : q ≤ q - 1 := Nat.le_of_dvd hqminus hdiv
    omega
  let P : Set ℕ := {p : ℕ | p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x ∧
    q ∣ p - 1 ∧ (a : ZMod p) ^ ((p - 1) / q) = 1}
  let Q : Set ℕ := {p : ℕ | p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x ∧
    ArtinPrimitiveRoots.Splitting.splitsCompletely
      (ArtinPrimitiveRoots.Splitting.kummerField a q) p}
  have hsubset : P ⊆ Q := by
    intro p hp
    rcases hp with ⟨hp, hpx, hp2x, hdiv, hpow⟩
    have hpA := hPnotA p hp hdiv hpow
    have hpq := hPnotQ p hp hdiv
    have hnotpaq : ¬ (p : ℤ) ∣ a * (q : ℤ) := by
      intro hpAQ
      letI : Fact p.Prime := ⟨hp⟩
      have hz : (a : ZMod p) * ((q : ℤ) : ZMod p) = 0 := by
        have hz' : ((a * (q : ℤ) : ℤ) : ZMod p) = 0 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd (a * (q : ℤ)) p).mpr hpAQ
        simpa only [Int.cast_mul] using hz'
      rcases mul_eq_zero.mp hz with haZ | hqZ
      · exact hpA ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp haZ)
      · have hqZ' : ((q : ℤ) : ZMod p) = 0 := hqZ
        have hpqZ : (p : ℤ) ∣ (q : ℤ) :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd (q : ℤ) p).mp hqZ'
        exact hpq (Int.natCast_dvd.mp hpqZ)
    have hsplit := ArtinPrimitiveRoots.Splitting.alg_splitting_test
      a ha0 p q hp hq hnotpaq hdiv hpow
    exact ⟨hp, hpx, hp2x, hsplit⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * x)
  have hQfinite : Q.Finite := (Set.finite_Iio N).subset (by
    intro p hp
    change p < N
    have hlt : (p : ℝ) < (N : ℝ) := lt_of_le_of_lt hp.2.2.1 hN
    exact_mod_cast hlt)
  have hcard : P.ncard ≤ Q.ncard := Set.ncard_le_ncard hsubset hQfinite
  have hcardR : (P.ncard : ℝ) ≤ (Q.ncard : ℝ) := by exact_mod_cast hcard
  have hQ := hbound x hx q hq hq₀ hqexp
  have hP : (P.ncard : ℝ) ≤
      C * (x / ((q : ℝ) * ((q : ℝ) - 1) * Real.log x) +
        x ^ (1 - ArtinPrimitiveRoots.HeckeBoundary.δ₀)) := hcardR.trans hQ
  have hδ : (1 - ArtinPrimitiveRoots.HeckeBoundary.δ₀ : ℝ) =
      1 - (1 / 1000000 : ℝ) := by
    norm_num [ArtinPrimitiveRoots.HeckeBoundary.δ₀]
  rw [hδ] at hP
  simpa [P] using hP

end ArtinPrimitiveRoots
