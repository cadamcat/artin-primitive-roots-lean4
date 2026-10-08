import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-BOOT».B0.Level

/-!
# B0: the trivial norm bound, unrolling the descent, the optimized shape
-/

set_option autoImplicit false

open scoped NumberField ComplexConjugate
open NumberField IsDedekindDomain
open ClassFieldTheory

noncomputable section

namespace ArtinPrimitiveRoots.A2.QSB0

open QSC2 QSC3

variable {K : Type} [Field K] [NumberField K]
variable {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}

/-- `B₂(M, X, κ) ≤ #{N a ≤ 5M/2} · W_max · #{N c ≤ X}`. -/
theorem highNorm_trivial (F : QSFamily m qS) {W : ℝ → ℝ} (hW : IsCapWeight W) {Wm : ℝ}
    (hWm : ∀ x : ℝ, 0 ≤ x → W x ≤ Wm) {M X κ : ℝ} (hM : 0 < M) :
    qsHighNorm F W M X κ ≤ (rowSet K (5 / 2 * M)).card * (Wm * idealCount K X) := by
  have hWm0 : 0 ≤ Wm := le_trans (hW.2.1 0) (hWm 0 le_rfl)
  refine (qs_high_norm_energy_S0 F W hW M X κ hM).2 _ (by positivity) fun z => ?_
  have hcols : ∀ c ∈ qsUpTo m qS X, QSAdm m qS c := fun c hc => (mem_qsUpTo.mp hc).1
  refine (energy_trivial F hW hWm hM (κ := κ) (qsUpTo m qS X) hcols z).trans ?_
  have hcard : ((qsUpTo m qS X).card : ℝ) ≤ idealCount K X := by
    have : qsUpTo m qS X ⊆ (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊X⌋₊).toFinset := by
      intro c hc
      rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      exact Nat.le_floor (mem_qsUpTo.mp hc).2
    exact_mod_cast Finset.card_le_card this
  have hS : 0 ≤ ∑ c ∈ qsUpTo m qS X, ‖z c‖ ^ 2 := Finset.sum_nonneg fun c _ => sq_nonneg _
  calc ((rowSet K (5 / 2 * M)).card : ℝ) * (Wm * (((qsUpTo m qS X).card : ℝ) *
        ∑ c ∈ qsUpTo m qS X, ‖z c‖ ^ 2))
      = ((rowSet K (5 / 2 * M)).card : ℝ) * (Wm * ((qsUpTo m qS X).card : ℝ)) *
          ∑ c ∈ qsUpTo m qS X, ‖z c‖ ^ 2 := by ring
    _ ≤ ((rowSet K (5 / 2 * M)).card : ℝ) * (Wm * idealCount K X) *
          ∑ c ∈ qsUpTo m qS X, ‖z c‖ ^ 2 := by gcongr

/-- Unrolling `H(X_k) ≤ a + b H(X_{k+1})`. -/
theorem unroll {H : ℕ → ℝ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (r : ℕ)
    (hstep : ∀ k < r, H k ≤ a + b * H (k + 1)) :
    H 0 ≤ a * ∑ i ∈ Finset.range r, b ^ i + b ^ r * H r := by
  have key : ∀ k ≤ r, H 0 ≤ a * ∑ i ∈ Finset.range k, b ^ i + b ^ k * H k := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
        intro hk
        have h1 := ih (by omega)
        have h2 := hstep k (by omega)
        have hbk : 0 ≤ b ^ k := pow_nonneg hb k
        calc H 0 ≤ a * ∑ i ∈ Finset.range k, b ^ i + b ^ k * H k := h1
          _ ≤ a * ∑ i ∈ Finset.range k, b ^ i + b ^ k * (a + b * H (k + 1)) := by gcongr
          _ = a * ∑ i ∈ Finset.range (k + 1), b ^ i + b ^ (k + 1) * H (k + 1) := by
              rw [Finset.sum_range_succ]; ring
  exact key r le_rfl

theorem geom_le {b : ℝ} (hb : 0 ≤ b) (r : ℕ) :
    ∑ i ∈ Finset.range r, b ^ i ≤ r * (1 + b) ^ r := by
  calc ∑ i ∈ Finset.range r, b ^ i ≤ ∑ i ∈ Finset.range r, (1 + b) ^ r :=
        Finset.sum_le_sum fun i hi => by
          calc b ^ i ≤ (1 + b) ^ i := pow_le_pow_left₀ hb (by linarith) i
            _ ≤ (1 + b) ^ r := pow_le_pow_right₀ (by linarith) (Finset.mem_range.mp hi).le
    _ = r * (1 + b) ^ r := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The block shape at the optimized `κ = N²/M · P^η`, `n ≤ N`. -/
theorem shape_le {M N n η α : ℝ} (hM : 0 < M) (hN : 1 ≤ N) (hn0 : 0 ≤ n) (hnN : n ≤ N)
    (hη : 0 ≤ η) (hα1 : 1 < α) (hα2 : α ≤ 2) (hP : 1 ≤ M * N) :
    qsBlockShape M n (N ^ (2 : ℝ) / M * (M * N) ^ η) α ≤
      2 * (M * N) ^ (2 * η) * (M + N + N ^ (2 * α - 1) * M ^ (1 - α)) := by
  set P := M * N with hP'
  have hN0 : 0 < N := by linarith
  have hP0 : 0 < P := by linarith
  have hPη : 1 ≤ P ^ η := Real.one_le_rpow hP hη
  set κ := N ^ (2 : ℝ) / M * P ^ η with hκ
  have hκ0 : 0 < κ := by positivity
  unfold qsBlockShape
  -- √M κ^{α-1/2} = N^{2α-1} M^{1-α} P^{η(α-1/2)}
  have h1 : Real.sqrt M * κ ^ (α - 1/2) =
      N ^ (2 * α - 1) * M ^ (1 - α) * P ^ (η * (α - 1/2)) := by
    rw [hκ, Real.mul_rpow (by positivity) (by positivity), Real.div_rpow (by positivity) hM.le,
      ← Real.rpow_mul hN0.le, ← Real.rpow_mul hP0.le, Real.sqrt_eq_rpow]
    rw [show (2 : ℝ) * (α - 1/2) = 2 * α - 1 by ring]
    have : M ^ (1 / 2 : ℝ) / M ^ (α - 1/2) = M ^ (1 - α) := by
      rw [← Real.rpow_sub hM]; congr 1; ring
    rw [show M ^ (1 / 2 : ℝ) * (N ^ (2 * α - 1) / M ^ (α - 1 / 2) * P ^ (η * (α - 1 / 2))) =
      N ^ (2 * α - 1) * (M ^ (1 / 2 : ℝ) / M ^ (α - 1 / 2)) * P ^ (η * (α - 1 / 2)) by ring,
      this]
  -- n √(M/κ) ≤ M
  have h2 : n * Real.sqrt (M / κ) ≤ M := by
    have hMκ : M / κ = (M / N) ^ 2 / P ^ η := by
      rw [hκ, Real.rpow_two]; field_simp
    have hsq : Real.sqrt (M / κ) ≤ M / N := by
      rw [Real.sqrt_le_left (by positivity), hMκ]
      exact div_le_self (sq_nonneg _) hPη
    calc n * Real.sqrt (M / κ) ≤ N * (M / N) :=
          mul_le_mul hnN hsq (Real.sqrt_nonneg _) (by linarith)
      _ = M := by field_simp
  have h3 : P ^ (η * (α - 1/2)) ≤ P ^ (2 * η) :=
    Real.rpow_le_rpow_of_exponent_le hP (by nlinarith)
  have hP2 : 1 ≤ P ^ (2 * η) := Real.one_le_rpow hP (by linarith)
  have hT0 : 0 ≤ N ^ (2 * α - 1) * M ^ (1 - α) := by positivity
  rw [h1]
  have h4 : N ^ (2 * α - 1) * M ^ (1 - α) * P ^ (η * (α - 1/2)) ≤
      N ^ (2 * α - 1) * M ^ (1 - α) * P ^ (2 * η) := mul_le_mul_of_nonneg_left h3 hT0
  have h5 : M + n + N ^ (2 * α - 1) * M ^ (1 - α) * P ^ (2 * η) + M ≤
      2 * P ^ (2 * η) * (M + N + N ^ (2 * α - 1) * M ^ (1 - α)) := by
    nlinarith [mul_le_mul_of_nonneg_left hP2 hM.le, mul_le_mul_of_nonneg_left hP2 hN0.le,
      mul_le_mul_of_nonneg_left hP2 hT0]
  linarith

end ArtinPrimitiveRoots.A2.QSB0
