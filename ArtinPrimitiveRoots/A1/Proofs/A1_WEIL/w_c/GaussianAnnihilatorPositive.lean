import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.w_c.GaussianCutoff

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory
open scoped ENNReal

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol_w_c

open ArtinPrimitiveRoots.A1
open ArtinPrimitiveRoots.Proofs.a1_weil_sol

variable {F : Type} [Field F] [NumberField F]

local instance measurableAnnihilatorPositive (v : FinPlace F) : MeasurableSpace (v.adicCompletion F) := borel _
local instance borelAnnihilatorPositive (v : FinPlace F) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

theorem quadraticBallAnnihilator_measure_pos
    (A : AddCharData F) (v : FinPlace F) (μ : Measure (v.adicCompletion F))
    (hμ : Measure.IsAddHaarMeasure μ) (a : (v.adicCompletion F)ˣ) (N : ℕ) :
    0 < μ (quadraticBallAnnihilator A v N a) := by
  classical
  letI : Measure.IsAddHaarMeasure μ := hμ
  let B := localBall v N
  let D := quadraticBallAnnihilator A v N a
  have h2 : (2 : v.adicCompletion F) ≠ 0 := by norm_num
  have ha : (a : v.adicCompletion F) ≠ 0 := a.ne_zero
  have hv2 : Valued.v (2 : v.adicCompletion F) ≠ 0 := (Valued.v.ne_zero_iff).2 h2
  have hva : Valued.v (a : v.adicCompletion F) ≠ 0 := (Valued.v.ne_zero_iff).2 ha
  let δ : ℤ := WithZero.log (Valued.v (2 : v.adicCompletion F)) +
    WithZero.log (Valued.v (a : v.adicCompletion F)) + (N : ℤ)
  let k : ℤ := - max 0 δ
  have hkN : k ≤ (N : ℤ) := by
    dsimp [k]
    omega
  have hδk : δ + k ≤ 0 := by
    dsimp [k]
    omega
  let U := valuedBall v k
  have hUopen : IsOpen U := by dsimp [U]; exact valuedBall_isOpen v k
  have hUnonempty : U.Nonempty := ⟨0, by simp [U, valuedBall]⟩
  have hUsub : U ⊆ D := by
    intro t ht
    have htval : Valued.v t ≤ WithZero.exp k := by simpa [U, valuedBall] using ht
    have htB : t ∈ B := by
      change Valued.v t ≤ WithZero.exp (N : ℤ)
      exact htval.trans ((WithZero.exp_le_exp).2 hkN)
    have htriv : ∀ x ∈ B,
        A.ψ v (-2 * (a : v.adicCompletion F) * x * t) = 1 := by
      intro x hx
      by_cases hx0 : x = 0
      · simp [hx0]
      by_cases ht0 : t = 0
      · simp [ht0]
      have hvx : Valued.v x ≠ 0 := (Valued.v.ne_zero_iff).2 hx0
      have hvt : Valued.v t ≠ 0 := (Valued.v.ne_zero_iff).2 ht0
      have hlogx : WithZero.log (Valued.v x) ≤ (N : ℤ) :=
        (WithZero.log_le_iff_le_exp hvx).mpr (by simpa [B, localBall] using hx)
      have hlogt : WithZero.log (Valued.v t) ≤ k :=
        (WithZero.log_le_iff_le_exp hvt).mpr htval
      let w := -2 * (a : v.adicCompletion F) * x * t
      have hwne : w ≠ 0 := by
        dsimp [w]
        exact mul_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr h2) ha) hx0) ht0
      have hvw : Valued.v w = Valued.v (2 : v.adicCompletion F) *
          Valued.v (a : v.adicCompletion F) * Valued.v x * Valued.v t := by
        dsimp [w]
        simp [Valuation.map_neg, Valuation.map_mul]
      have hvwne : Valued.v w ≠ 0 := (Valued.v.ne_zero_iff).2 hwne
      have hlogw : WithZero.log (Valued.v w) ≤ 0 := by
        rw [hvw, WithZero.log_mul (mul_ne_zero (mul_ne_zero hv2 hva) hvx) hvt,
          WithZero.log_mul (mul_ne_zero hv2 hva) hvx,
          WithZero.log_mul hv2 hva]
        dsimp [δ] at hδk
        omega
      have hvwle : Valued.v w ≤ 1 := by
        have := (WithZero.log_le_iff_le_exp hvwne).mp hlogw
        simpa using this
      have hwint : w ∈ v.adicCompletionIntegers F := by
        rw [HeightOneSpectrum.mem_adicCompletionIntegers]
        exact hvwle
      exact A.integral v w hwint
    have hDmem : t ∈ D := by
      have htriv' : ∀ x ∈ B,
          A.ψ v (-(2 * (a : v.adicCompletion F) * x * t)) = 1 := by
        intro x hx
        convert htriv x hx using 1 <;> ring
      simpa [D, quadraticBallAnnihilator, Set.mem_iInter, Set.mem_inter_iff,
        Set.mem_ofPred_eq] using ⟨htB, htriv'⟩
    exact hDmem
  have hUpos : 0 < μ U := hUopen.measure_pos μ hUnonempty
  exact lt_of_lt_of_le hUpos (measure_mono hUsub)

end ArtinPrimitiveRoots.Proofs.a1_weil_sol_w_c
