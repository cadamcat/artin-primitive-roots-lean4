import ArtinPrimitiveRoots.Proofs.qs_c_p.C3HighDiv

/-! Exact dyadic expansion of the original high-divisor pair sum. -/

set_option autoImplicit false

open scoped NumberField ComplexConjugate
open NumberField IsDedekindDomain ClassFieldTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.qs_c3_sol

open ArtinPrimitiveRoots.A2
open ArtinPrimitiveRoots.Proofs.qs_c_p

/-- One original high-divisor row/divisor shell, with its exact cutoff weight. -/
def origHighDivShellKernel {K : Type} [Field K] [NumberField K]
    {m : RayClassModulus K} {qS : Ideal (𝓞 K)}
    (F : QSFamily m qS) (q eq : Ideal (𝓞 K)) (κ Λ M : ℝ)
    (k l r : ℕ) : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ := fun c d =>
  ∑ ec ∈ (qsDivisors c).filter (fun ec =>
      (2 ^ l : ℝ) ≤ qsN ec ∧ qsN ec < 2 ^ (l + 1)),
    ∑ ed ∈ (qsDivisors d).filter (fun ed =>
      (2 ^ r : ℝ) ≤ qsN ed ∧ qsN ed < 2 ^ (r + 1)),
      (qsMu (ec * ed) : ℂ) *
        ∑ a ∈ (qsSqfUpTo κ q).filter (fun a =>
          (2 ^ k : ℝ) ≤ qsN a ∧ qsN a < 2 ^ (k + 1)),
          qsC3RowTwist F a * (F.character c).idealValue a *
            (F.character d).idealValue a *
            (if Λ * Real.sqrt (M / qsN a) < qsN eq * qsN (ec * ed) then
              ((Real.sqrt (M / qsN a) / (qsN eq * qsN (ec * ed)) : ℝ) : ℂ)
            else 0)

/-- The original high-divisor pair sum is a finite sum of the shells estimated
by orig_highdiv_shell_bound, with the fixed residue/Mellin coefficient outside. -/
theorem orig_highdiv_pair_shell_expand {K : Type} [Field K] [NumberField K]
    {m : RayClassModulus K} {qS : Ideal (𝓞 K)}
    (F : QSFamily m qS) (W : ℝ → ℝ)
    (hrf : ∀ g h, F.rayFactor g h = 1) (hqS : qS ≠ ⊥)
    (M κ Λ n : ℝ) (q : Ideal (𝓞 K)) (cols : Finset (Ideal (𝓞 K)))
    (z : Ideal (𝓞 K) → ℂ) (hblock : QSBlockCols m qS q n cols) :
    qsPairSum cols z (qsOrigKernel (qsInnerHighDiv K) F W M κ Λ q) =
      ((qsResidueOne K : ℂ) * mellin (fun y => (W (y ^ 2) : ℂ)) 1) *
        ∑ eq ∈ qsDivisors q, (qsMu eq : ℂ) *
          ∑ k ∈ Finset.range (Nat.log 2 ⌊κ⌋₊ + 1),
            ∑ l ∈ Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1),
              ∑ r ∈ Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1),
                qsPairSum cols z (origHighDivShellKernel F q eq κ Λ M k l r) := by
  classical
  rcases hblock with ⟨hq, hbad, hcol, hclass⟩
  let A : ℂ := (qsResidueOne K : ℂ) * mellin (fun y => (W (y ^ 2) : ℂ)) 1
  have hrowSize : ∀ a ∈ qsSqfUpTo κ q,
      1 ≤ Ideal.absNorm a ∧ Ideal.absNorm a ≤ ⌊κ⌋₊ := by
    intro a ha
    have ha0 := QSC2.ne_bot_of_QSAdm (qs_c3_orig_row_admissible hqS hbad κ ha).1
    exact ⟨Nat.one_le_iff_ne_zero.mpr
      (fun hz => ha0 (Ideal.absNorm_eq_zero_iff.mp hz)), qs_c3_sqfUpTo_norm_le_nat ha⟩
  have hker : ∀ c ∈ cols, ∀ d ∈ cols, IsCoprime c d →
      qsOrigKernel (qsInnerHighDiv K) F W M κ Λ q c d =
        A * ∑ eq ∈ qsDivisors q, (qsMu eq : ℂ) *
          ∑ k ∈ Finset.range (Nat.log 2 ⌊κ⌋₊ + 1),
            ∑ l ∈ Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1),
              ∑ r ∈ Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1),
                origHighDivShellKernel F q eq κ Λ M k l r c d := by
    intro c hc d hd hcd
    have hc' := hcol c hc
    have hd' := hcol d hd
    have hdivSize (x : Ideal (𝓞 K)) (hx : QSAdm m qS x) (hxn : qsN x ≤ 2 * n) :
        ∀ e ∈ qsDivisors x, 1 ≤ Ideal.absNorm e ∧ Ideal.absNorm e ≤ ⌊2 * n⌋₊ := by
      intro e he
      have hx0 := QSC2.ne_bot_of_QSAdm hx
      have he0 : e ≠ ⊥ := by
        intro hz
        subst e
        exact hx0 (bot_unique (Ideal.le_of_dvd ((QSC2.mem_qsDivisors hx0).mp he)))
      exact ⟨Nat.one_le_iff_ne_zero.mpr
        (fun hz => he0 (Ideal.absNorm_eq_zero_iff.mp hz)),
        Nat.le_floor ((qs_c3_divisor_norm_le_of_col hx he).trans hxn)⟩
    let H : Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ :=
      fun eq a ec ed => (qsPairChar F c d).idealValue a * (qsMu (ec * ed) : ℂ) *
        (if Λ * Real.sqrt (M / qsN a) < qsN eq * qsN (ec * ed) then
          ((Real.sqrt (M / qsN a) / (qsN eq * qsN (ec * ed)) : ℝ) : ℂ)
        else 0)
    have hbase : qsOrigKernel (qsInnerHighDiv K) F W M κ Λ q c d =
        A * ∑ eq ∈ qsDivisors q, (qsMu eq : ℂ) *
          ∑ a ∈ qsSqfUpTo κ q, ∑ ec ∈ qsDivisors c, ∑ ed ∈ qsDivisors d,
            H eq a ec ed := by
      rw [qs_c3_orig_highdiv_expand F W M κ Λ q c d hq hc'.1 hd'.1
        hc'.2.1.symm hd'.2.1.symm hcd]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro eq heq
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro ec hec
      apply Finset.sum_congr rfl
      intro ed hed
      dsimp only [A, H]
      by_cases hcut : Λ * Real.sqrt (M / qsN a) < qsN eq * qsN (ec * ed)
      <;> simp only [hcut, ite_true, ite_false, Complex.ofReal_div, Complex.ofReal_mul]
      <;> ring
    have hdyad (eq : Ideal (𝓞 K)) :
        (∑ a ∈ qsSqfUpTo κ q, ∑ ec ∈ qsDivisors c, ∑ ed ∈ qsDivisors d, H eq a ec ed) =
          ∑ k ∈ Finset.range (Nat.log 2 ⌊κ⌋₊ + 1),
            ∑ l ∈ Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1),
              ∑ r ∈ Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1),
                origHighDivShellKernel F q eq κ Λ M k l r c d := by
      rw [qs_c3_shell_sum₃ (qsSqfUpTo κ q) Ideal.absNorm ⌊κ⌋₊ hrowSize
        (qsDivisors c) Ideal.absNorm ⌊2 * n⌋₊ (hdivSize c hc'.1 hc'.2.2.2)
        (qsDivisors d) Ideal.absNorm ⌊2 * n⌋₊ (hdivSize d hd'.1 hd'.2.2.2) (H eq)]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      apply Finset.sum_congr rfl
      intro r hr
      unfold origHighDivShellKernel
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ec hec
      apply Finset.sum_congr rfl
      intro ed hed
      apply Finset.sum_congr rfl
      intro a ha
      have haAdm := (qs_c3_orig_row_admissible hqS hbad κ (Finset.mem_filter.mp ha).1).1
      dsimp only [H]
      rw [qs_c3_pairValue_row F hrf haAdm hc'.1 hd'.1 hcd]
      ring
    rw [hbase]
    congr 1
    apply Finset.sum_congr rfl
    intro eq heq
    congr 1
    exact hdyad eq
  have hPair : qsPairSum cols z (qsOrigKernel (qsInnerHighDiv K) F W M κ Λ q) =
      qsPairSum cols z (fun c d =>
        A * ∑ eq ∈ qsDivisors q, (qsMu eq : ℂ) *
          ∑ k ∈ Finset.range (Nat.log 2 ⌊κ⌋₊ + 1),
            ∑ l ∈ Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1),
              ∑ r ∈ Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1),
                origHighDivShellKernel F q eq κ Λ M k l r c d) := by
    unfold qsPairSum
    apply Finset.sum_congr rfl
    intro c hc
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hcd : IsCoprime c d
    · simp only [if_pos hcd]
      rw [hker c hc d hd hcd]
    · simp only [if_neg hcd]
  rw [hPair, qs_c2b_pairSum_const_mul cols z A]
  change A * _ = A * _
  congr 1
  rw [qs_c3_pairSum_sum]
  apply Finset.sum_congr rfl
  intro eq heq
  rw [qs_c2b_pairSum_const_mul cols z (qsMu eq : ℂ)]
  congr 1
  rw [qs_c3_pairSum_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [qs_c3_pairSum_sum]
  apply Finset.sum_congr rfl
  intro l hl
  exact qs_c3_pairSum_sum cols z
    (Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1))
    (fun r => origHighDivShellKernel F q eq κ Λ M k l r)

end ArtinPrimitiveRoots.Proofs.qs_c3_sol
