import ArtinPrimitiveRoots.Proofs.qs_c_p.C3DualHighDiv
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-CANCEL».C3.Trans

/-! Exact bad-row and dyadic expansion of the dual high-divisor remainder. -/

set_option autoImplicit false

open scoped NumberField ComplexConjugate
open NumberField IsDedekindDomain ClassFieldTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.qs_c3_sol

open ArtinPrimitiveRoots.A2
open ArtinPrimitiveRoots.Proofs.qs_c_p

/-- The exact condition selecting the good cofactor of an original dual row. -/
def dualRowWeight {K : Type} [Field K] [NumberField K]
    (m : RayClassModulus K) (qS : Ideal (𝓞 K)) (κ : ℝ)
    (a₂ a₁ : Ideal (𝓞 K)) : ℂ :=
  if a₂ * a₁ ∈ qsSqfUpTo κ ⊤ ∧ a₂ * a₁ ⊔ QSC3.badIdeal m qS = a₂ then 1 else 0

/-- One dual high-divisor shell, including its fixed column twists. -/
def dualHighDivShellKernel {K : Type} [Field K] [NumberField K]
    {m : RayClassModulus K} {qS : Ideal (𝓞 K)}
    (F : QSFamily m qS) (e a₂ : Ideal (𝓞 K)) (κ n Λ M : ℝ)
    (k l r : ℕ) : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ := fun c d =>
  (QSC3.twist F c e * QSC3.twist F c a₂) *
    (QSC3.twistInv F d e * QSC3.twistInv F d a₂) *
      ∑ ec ∈ (qsDivisors c).filter (fun ec =>
          (2 ^ l : ℝ) ≤ qsN ec ∧ qsN ec < 2 ^ (l + 1)),
        ∑ ed ∈ (qsDivisors d).filter (fun ed =>
          (2 ^ r : ℝ) ≤ qsN ed ∧ qsN ed < 2 ^ (r + 1)),
          (qsMu (ec * ed) : ℂ) *
            ∑ a₁ ∈ (qsUpTo m qS κ).filter (fun a₁ =>
                (2 ^ k : ℝ) ≤ qsN a₁ ∧ qsN a₁ < 2 ^ (k + 1)),
              dualRowWeight m qS κ a₂ a₁ * (F.character c).idealValue a₁ *
                (F.character d).idealValue a₁ *
                  dualHighDivWeight M n Λ (qsN e) (qsN a₂) (qsN a₁) (qsN (ec * ed))

/-- Exact expansion of the dual high-divisor pair sum into the checked shells. -/
theorem dual_highdiv_pair_shell_expand {K : Type} [Field K] [NumberField K]
    {m : RayClassModulus K} {qS : Ideal (𝓞 K)}
    (F : QSFamily m qS) (W : ℝ → ℝ)
    (hrf : ∀ g h, F.rayFactor g h = 1) (hqS : qS ≠ ⊥)
    (M κ Λ n : ℝ) (hM : 0 < M) (q : Ideal (𝓞 K))
    (cols : Finset (Ideal (𝓞 K))) (z : Ideal (𝓞 K) → ℂ)
    (hblock : QSBlockCols m qS q n cols) :
    qsPairSum cols z (qsDualKernel (qsInnerHighDiv K) F W M κ Λ n q) =
      ((qsResidueOne K : ℂ) * mellin (QSC3.F0 K W) 1) *
        ∑ e ∈ qsDivisors q, (qsMu e : ℂ) *
          ∑ a₂ ∈ qsDivisors (QSC3.badIdeal m qS),
            ∑ k ∈ Finset.range (Nat.log 2 ⌊κ⌋₊ + 1),
              ∑ l ∈ Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1),
                ∑ r ∈ Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1),
                  qsPairSum cols z (dualHighDivShellKernel F e a₂ κ n Λ M k l r) := by
  classical
  rcases hblock with ⟨hq, hbad, hcol, hclass⟩
  have hq0 : q ≠ ⊥ := hq.ne_zero
  let S := qsSqfUpTo (K := K) κ ⊤
  let R := QSC3.badIdeal m qS
  let R₀ : ℂ := (qsResidueOne K : ℂ) * mellin (QSC3.F0 K W) 1
  have hS : ∀ a ∈ S, a ≠ ⊥ ∧ Squarefree a ∧ qsN a ≤ κ := by
    intro a ha
    have ha' := Finset.mem_filter.mp ha
    exact ⟨ha'.2.1, ha'.2.2.1, ha'.2.2.2.2⟩
  have hrowSize : ∀ a ∈ qsUpTo m qS κ,
      1 ≤ Ideal.absNorm a ∧ Ideal.absNorm a ≤ ⌊κ⌋₊ := by
    intro a ha
    have ha' := QSC2.mem_qsUpTo.mp ha
    have ha0 := QSC2.ne_bot_of_QSAdm ha'.1
    exact ⟨Nat.one_le_iff_ne_zero.mpr
      (fun hz => ha0 (Ideal.absNorm_eq_zero_iff.mp hz)), Nat.le_floor ha'.2⟩
  have hcancel (E A x : ℝ) (hE : 0 < E) (hA : 0 < A) (hx : 0 < x) :
      M / (E * Real.sqrt x) * Real.sqrt (E * x / (M * A)) =
        Real.sqrt (M / (E * A)) := by
    have hsquare : (M / (E * Real.sqrt x) * Real.sqrt (E * x / (M * A))) ^ 2 =
        (Real.sqrt (M / (E * A))) ^ 2 := by
      simp only [mul_pow, div_pow]
      rw [Real.sq_sqrt hx.le, Real.sq_sqrt (by positivity : 0 ≤ E * x / (M * A)),
        Real.sq_sqrt (by positivity : 0 ≤ M / (E * A))]
      field_simp [hM.ne', hE.ne', hA.ne', hx.ne']
    apply le_antisymm
    · exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsquare.le
    · exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsquare.ge
  have hker : ∀ c ∈ cols, ∀ d ∈ cols, IsCoprime c d →
      qsDualKernel (qsInnerHighDiv K) F W M κ Λ n q c d =
        R₀ * ∑ e ∈ qsDivisors q, (qsMu e : ℂ) *
          ∑ a₂ ∈ qsDivisors R,
            ∑ k ∈ Finset.range (Nat.log 2 ⌊κ⌋₊ + 1),
              ∑ l ∈ Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1),
                ∑ r ∈ Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1),
                  dualHighDivShellKernel F e a₂ κ n Λ M k l r c d := by
    intro c hc d hd hcd
    have hc' := hcol c hc
    have hd' := hcol d hd
    have hc0 := QSC2.ne_bot_of_QSAdm hc'.1
    have hd0 := QSC2.ne_bot_of_QSAdm hd'.1
    have hx : 0 < qsN (c * d) := by
      rw [QSC2.qsN_mul]
      exact mul_pos (QSC2.qsN_pos hc0) (QSC2.qsN_pos hd0)
    obtain ⟨hψe, hψa⟩ := QSC3.pairChar_block F hrf hqS hbad hc'.1 hd'.1
      hc'.2.1 hd'.2.1 hcd (hclass c hc d hd)
    have hdivSize (x : Ideal (𝓞 K)) (hxA : QSAdm m qS x) (hxn : qsN x ≤ 2 * n) :
        ∀ e ∈ qsDivisors x, 1 ≤ Ideal.absNorm e ∧ Ideal.absNorm e ≤ ⌊2 * n⌋₊ := by
      intro e he
      have hx0 := QSC2.ne_bot_of_QSAdm hxA
      have he0 : e ≠ ⊥ := by
        intro hz
        subst e
        exact hx0 (bot_unique (Ideal.le_of_dvd ((QSC2.mem_qsDivisors hx0).mp he)))
      exact ⟨Nat.one_le_iff_ne_zero.mpr
        (fun hz => he0 (Ideal.absNorm_eq_zero_iff.mp hz)),
        Nat.le_floor ((qs_c3_divisor_norm_le_of_col hxA he).trans hxn)⟩
    let G : Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ :=
      fun e a ec ed => (qsPairChar F c d).idealValue a * (qsMu (ec * ed) : ℂ) *
        dualHighDivWeight M n Λ (qsN e) 1 (qsN a) (qsN (ec * ed))
    let H : Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) →
        Ideal (𝓞 K) → ℂ := fun e a₂ a₁ ec ed =>
      (qsMu (ec * ed) : ℂ) *
        (dualRowWeight m qS κ a₂ a₁ * (F.character c).idealValue a₁ *
          (F.character d).idealValue a₁ *
            dualHighDivWeight M n Λ (qsN e) (qsN a₂) (qsN a₁) (qsN (ec * ed)))
    have hraw : qsDualKernel (qsInnerHighDiv K) F W M κ Λ n q c d =
        R₀ * ∑ e ∈ qsDivisors q, (qsMu e : ℂ) *
          ((qsPairChar F c d).idealValue e *
            ∑ a ∈ S, ∑ ec ∈ qsDivisors c, ∑ ed ∈ qsDivisors d, G e a ec ed) := by
      unfold qsDualKernel
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      have he0 : e ≠ ⊥ := by
        intro hz
        subst e
        exact hq0 (bot_unique (Ideal.le_of_dvd ((QSC2.mem_qsDivisors hq0).mp he)))
      apply Finset.sum_congr rfl
      intro a ha
      have ha0 := (hS a ha).1
      unfold qsInnerHighDiv
      rw [QSC3.sum_divisors_mul hc0 hd0 hcd]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ec hec
      apply Finset.sum_congr rfl
      intro ed hed
      have hcanc := hcancel (qsN e) (qsN a) (qsN (c * d))
        (QSC2.qsN_pos he0) (QSC2.qsN_pos ha0) hx
      dsimp only [G, R₀, QSC3.F0, dualHighDivWeight]
      simp only [mul_one]
      by_cases hcut : 2 * Λ * Real.sqrt (qsN e * n ^ 2 / (M * qsN a)) < qsN (ec * ed)
      · simp only [hcut, ite_true]
        calc
          _ = ((qsResidueOne K : ℂ) * mellin (QSC3.F0 K W) 1) *
              (qsMu e : ℂ) * (qsPairChar F c d).idealValue e *
              (qsPairChar F c d).idealValue a * (qsMu (ec * ed) : ℂ) *
              ((M / (qsN e * Real.sqrt (qsN (c * d))) *
                Real.sqrt (qsN e * qsN (c * d) / (M * qsN a)) / qsN (ec * ed) : ℝ) : ℂ) := by
            push_cast
            ring
          _ = _ := by
            rw [hcanc]
            push_cast
            ring
      · simp only [hcut, ite_false, mul_zero]
    have hsplit (e : Ideal (𝓞 K)) (he : e ∈ qsDivisors q) :
        (qsPairChar F c d).idealValue e *
            (∑ a ∈ S, ∑ ec ∈ qsDivisors c, ∑ ed ∈ qsDivisors d, G e a ec ed) =
          ∑ a₂ ∈ qsDivisors R,
            (QSC3.twist F c e * QSC3.twist F c a₂) *
              (QSC3.twistInv F d e * QSC3.twistInv F d a₂) *
                ∑ a₁ ∈ qsUpTo m qS κ, ∑ ec ∈ qsDivisors c,
                  ∑ ed ∈ qsDivisors d, H e a₂ a₁ ec ed := by
      rw [QSC3.sum_rows_split hqS S κ hS]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a₂ ha₂
      have ha₂R : a₂ ∣ R :=
        (QSC2.mem_qsDivisors (QSC3.badIdeal_ne_bot hqS)).mp ha₂
      apply Finset.sum_congr rfl
      intro a₁ ha₁
      have ha₁A := (QSC2.mem_qsUpTo.mp ha₁).1
      by_cases hrow : a₂ * a₁ ∈ S ∧ a₂ * a₁ ⊔ R = a₂
      · have hrow' : a₂ * a₁ ∈ S ∧ a₂ * a₁ ⊔ QSC3.badIdeal m qS = a₂ := hrow
        rw [ite_eq_left hrow']
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ec hec
        apply Finset.sum_congr rfl
        intro ed hed
        dsimp only [G, H]
        rw [hψe e ((QSC2.mem_qsDivisors hq0).mp he), hψa a₂ a₁ ha₂R ha₁A,
          QSC2.qsN_mul]
        simp only [dualRowWeight, show a₂ * a₁ ∈ qsSqfUpTo κ ⊤ ∧
          a₂ * a₁ ⊔ QSC3.badIdeal m qS = a₂ from hrow, and_self, ite_true, one_mul]
        unfold dualHighDivWeight
        simp only [mul_one, mul_assoc]
        ring
      · have hrow' : ¬ (a₂ * a₁ ∈ S ∧ a₂ * a₁ ⊔ QSC3.badIdeal m qS = a₂) := hrow
        rw [ite_eq_right hrow', mul_zero]
        have hrow'' : ¬ (a₂ * a₁ ∈ qsSqfUpTo κ ⊤ ∧
          a₂ * a₁ ⊔ QSC3.badIdeal m qS = a₂) := hrow
        simp only [H, dualRowWeight, hrow'', ite_false, zero_mul, mul_zero,
          Finset.sum_const_zero]
    have hdyad (e a₂ : Ideal (𝓞 K)) :
        (QSC3.twist F c e * QSC3.twist F c a₂) *
            (QSC3.twistInv F d e * QSC3.twistInv F d a₂) *
              (∑ a₁ ∈ qsUpTo m qS κ, ∑ ec ∈ qsDivisors c,
                ∑ ed ∈ qsDivisors d, H e a₂ a₁ ec ed) =
          ∑ k ∈ Finset.range (Nat.log 2 ⌊κ⌋₊ + 1),
            ∑ l ∈ Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1),
              ∑ r ∈ Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1),
                dualHighDivShellKernel F e a₂ κ n Λ M k l r c d := by
      rw [qs_c3_shell_sum₃ (qsUpTo m qS κ) Ideal.absNorm ⌊κ⌋₊ hrowSize
        (qsDivisors c) Ideal.absNorm ⌊2 * n⌋₊ (hdivSize c hc'.1 hc'.2.2.2)
        (qsDivisors d) Ideal.absNorm ⌊2 * n⌋₊ (hdivSize d hd'.1 hd'.2.2.2) (H e a₂)]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      apply Finset.sum_congr rfl
      intro r hr
      unfold dualHighDivShellKernel
      simp only [Finset.mul_sum]
      rfl
    rw [hraw]
    congr 1
    apply Finset.sum_congr rfl
    intro e he
    congr 1
    rw [hsplit e he]
    apply Finset.sum_congr rfl
    intro a₂ ha₂
    exact hdyad e a₂
  have hPair : qsPairSum cols z (qsDualKernel (qsInnerHighDiv K) F W M κ Λ n q) =
      qsPairSum cols z (fun c d => R₀ *
        ∑ e ∈ qsDivisors q, (qsMu e : ℂ) *
          ∑ a₂ ∈ qsDivisors R,
            ∑ k ∈ Finset.range (Nat.log 2 ⌊κ⌋₊ + 1),
              ∑ l ∈ Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1),
                ∑ r ∈ Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1),
                  dualHighDivShellKernel F e a₂ κ n Λ M k l r c d) := by
    unfold qsPairSum
    apply Finset.sum_congr rfl
    intro c hc
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hcd : IsCoprime c d
    · simp only [hcd, ite_true]
      rw [hker c hc d hd hcd]
    · simp only [hcd, ite_false]
  rw [hPair, qs_c2b_pairSum_const_mul cols z R₀]
  change R₀ * _ = R₀ * _
  congr 1
  rw [qs_c3_pairSum_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [qs_c2b_pairSum_const_mul cols z (qsMu e : ℂ)]
  congr 1
  rw [qs_c3_pairSum_sum]
  apply Finset.sum_congr rfl
  intro a₂ ha₂
  rw [qs_c3_pairSum_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [qs_c3_pairSum_sum]
  apply Finset.sum_congr rfl
  intro l hl
  exact qs_c3_pairSum_sum cols z (Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1))
    (fun r => dualHighDivShellKernel F e a₂ κ n Λ M k l r)

end ArtinPrimitiveRoots.Proofs.qs_c3_sol
