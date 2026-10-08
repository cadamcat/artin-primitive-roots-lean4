import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.Defs

set_option autoImplicit false
open NumberField IsDedekindDomain ClassFieldTheory
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Absorb any fixed logarithmic power into an arbitrarily small positive
loss, uniformly for N,U at least two. Guide: sol-thin-a2zf/PROOFS.md:737–740.
Uses elementary exponential domination; feeds conductor_sieve_assemble. -/
theorem conductor_log_power_absorb (k : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ N U : ℝ, 2 ≤ N → 2 ≤ U →
        (1 + Real.log N) ^ k ≤ C * Real.rpow (N * U) ε := by
  classical
  intro ε hε
  let δ : ℝ := ε / (k + 1 : ℝ)
  let A : ℝ := 1 + 1 / δ
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hA : 0 < A := by
    dsimp [A]
    positivity
  refine ⟨A ^ k, by positivity, ?_⟩
  intro N U hN hU
  have hNpos : 0 < N := by linarith
  have hUpos : 0 < U := by linarith
  have hNU : N ≤ N * U := by nlinarith
  have hNUpos : 0 < N * U := mul_pos hNpos hUpos
  have hlog : Real.log N ≤ Real.log (N * U) := Real.log_le_log hNpos hNU
  have hx0 : 0 ≤ Real.log (N * U) := by
    apply Real.log_nonneg
    nlinarith [mul_le_mul_of_nonneg_left hU (le_of_lt hNpos)]
  let x : ℝ := Real.log (N * U)
  have hx : 0 ≤ x := by simpa [x] using hx0
  have hδx : 0 ≤ δ * x := mul_nonneg hδ.le hx
  have hexp1 : 1 ≤ Real.exp (δ * x) := by
    have h := Real.add_one_le_exp (δ * x)
    linarith
  have hexpδx : δ * x ≤ Real.exp (δ * x) := by
    have h := Real.add_one_le_exp (δ * x)
    linarith
  have hxrewrite : x = (1 / δ) * (δ * x) := by
    field_simp [ne_of_gt hδ]
  have hmul := mul_le_mul_of_nonneg_left hexpδx
    (le_of_lt (show 0 < 1 / δ by positivity))
  have hlinear : 1 + x ≤ A * Real.exp (δ * x) := by
    calc
      1 + x = 1 + (1 / δ) * (δ * x) := congrArg (fun y : ℝ => 1 + y) hxrewrite
      _ ≤ Real.exp (δ * x) + (1 / δ) * Real.exp (δ * x) := add_le_add hexp1 hmul
      _ = A * Real.exp (δ * x) := by dsimp [A]; ring
  have hpow : (1 + x) ^ k ≤ (A * Real.exp (δ * x)) ^ k :=
    pow_le_pow_left₀ (by positivity) hlinear k
  have hpow' : (A * Real.exp (δ * x)) ^ k =
      A ^ k * Real.exp ((k : ℝ) * (δ * x)) := by
    rw [mul_pow, Real.exp_nat_mul]
  have hcoef : (k : ℝ) * δ ≤ ε := by
    calc
      (k : ℝ) * δ = ((k : ℝ) * ε) / ((k : ℝ) + 1) := by dsimp [δ]; ring
      _ ≤ ε := (div_le_iff₀ (by positivity : 0 < (k : ℝ) + 1)).2 (by nlinarith)
  have hexpArg : (k : ℝ) * (δ * x) ≤ ε * x := by
    calc
      (k : ℝ) * (δ * x) = ((k : ℝ) * δ) * x := by ring
      _ ≤ ε * x := mul_le_mul_of_nonneg_right hcoef hx
  have hexp : Real.exp ((k : ℝ) * (δ * x)) ≤ Real.exp (ε * x) :=
    Real.exp_le_exp.mpr hexpArg
  have hbase0 : 0 ≤ 1 + Real.log N := by
    have := Real.log_nonneg (by linarith : 1 ≤ N)
    linarith
  have hbasele : 1 + Real.log N ≤ 1 + x := by dsimp [x]; linarith
  have hbasepow : (1 + Real.log N) ^ k ≤ (1 + x) ^ k :=
    pow_le_pow_left₀ hbase0 hbasele k
  have hrpow : Real.rpow (N * U) ε = Real.exp (ε * x) := by
    change (N * U) ^ ε = Real.exp (ε * x)
    rw [Real.rpow_def_of_pos hNUpos ε]
    simp only [x]
    rw [mul_comm]
  calc
    (1 + Real.log N) ^ k ≤ (1 + x) ^ k := hbasepow
    _ ≤ (A * Real.exp (δ * x)) ^ k := hpow
    _ = A ^ k * Real.exp ((k : ℝ) * (δ * x)) := hpow'
    _ ≤ A ^ k * Real.exp (ε * x) := mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = A ^ k * Real.rpow (N * U) ε := by rw [hrpow]

end ArtinPrimitiveRoots.A2
