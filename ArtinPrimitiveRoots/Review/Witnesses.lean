import ArtinPrimitiveRoots.Construction.Defs
import ArtinPrimitiveRoots.TypeII.Marked

/-!
Kernel-checked inhabitance witnesses for the Prop-valued predicates used in part B.
The smooth witness uses Mathlib's `ContDiffBump`; its support is a compact open interval
strictly inside `(1, 2)`.
-/

namespace ArtinPrimitiveRoots.Review

open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.Construction

theorem roughAbove_witness : ∃ n : ℕ, ∀ y : ℝ, roughAbove n y := by
  refine ⟨1, ?_⟩
  intro y p hp hdiv
  have hpone : p = 1 := Nat.dvd_one.mp hdiv
  subst p
  exact (Nat.not_prime_one hp).elim
example : ∃ n : ℕ, ∀ y : ℝ, roughAbove n y := roughAbove_witness

theorem validBands_witness : ∃ K : ℕ, ∃ a : Fin K → ℝ, ValidBands K a := by
  refine ⟨1, fun _ => (3 / 20 : ℝ), ?_⟩
  norm_num [ValidBands]
example : ∃ K : ℕ, ∃ a : Fin K → ℝ, ValidBands K a := validBands_witness

theorem markedInvariant_witness : ∃ x : ℝ, ∃ K : ℕ, ∃ a : Fin K → ℝ, ∃ F : ℕ → ℂ,
    IsMarkedInvariant x K a F := by
  refine ⟨2, 1, fun _ => (3 / 20 : ℝ), fun _ => 0, ?_⟩
  constructor
  · intro h
    simp
  · intro p h hp _
    simp
example : ∃ x : ℝ, ∃ K : ℕ, ∃ a : Fin K → ℝ, ∃ F : ℕ → ℂ,
    IsMarkedInvariant x K a F := markedInvariant_witness

theorem groupInteger_witness : ∃ x : ℝ, ∃ K : ℕ, ∃ a : Fin K → ℝ, ∃ r : ℕ,
    IsGroupInteger x K a r := by
  refine ⟨2, 1, fun _ => (3 / 20 : ℝ), 1, ?_⟩
  intro p hp hdiv
  have hpone : p = 1 := Nat.dvd_one.mp hdiv
  subst p
  exact (Nat.not_prime_one hp).elim
example : ∃ x : ℝ, ∃ K : ℕ, ∃ a : Fin K → ℝ, ∃ r : ℕ,
    IsGroupInteger x K a r := groupInteger_witness

noncomputable def witnessBump : ContDiffBump (3 / 2 : ℝ) :=
  ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

noncomputable def witnessTestFunction : ℝ → ℝ := witnessBump

theorem testFunction_witness : ∃ Ψ : ℝ → ℝ, IsTestFunction Ψ := by
  refine ⟨witnessTestFunction, ?_⟩
  have hbumpSmooth :
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) witnessTestFunction := by
    simpa [witnessTestFunction] using
      (witnessBump.contDiff :
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (witnessBump : ℝ → ℝ))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hbumpSmooth
  · intro y hy
    rw [show Function.support witnessTestFunction = Metric.ball (3 / 2 : ℝ) (1 / 4 : ℝ) by
      simpa [witnessTestFunction, witnessBump] using witnessBump.support_eq] at hy
    have hy' : |y - (3 / 2 : ℝ)| < 1 / 4 := by
      simpa [Metric.mem_ball, Real.dist_eq] using hy
    rcases abs_lt.mp hy' with ⟨hlo, hhi⟩
    constructor <;> nlinarith
  · intro y
    exact witnessBump.nonneg
  · intro y
    exact witnessBump.le_one
  · apply intervalIntegral.integral_pos
    · norm_num
    · exact hbumpSmooth.continuous.continuousOn
    · intro y hy
      exact witnessBump.nonneg
    · refine ⟨(3 / 2 : ℝ), by norm_num, ?_⟩
      have hcenter : (3 / 2 : ℝ) ∈ Metric.closedBall (3 / 2 : ℝ) witnessBump.rIn := by
        simp [Metric.mem_closedBall, witnessBump]
      rw [witnessTestFunction, witnessBump.one_of_mem_closedBall hcenter]
      norm_num
example : ∃ Ψ : ℝ → ℝ, IsTestFunction Ψ := testFunction_witness

noncomputable def zeroCancellationFamily : CoefficientFamily 0 1 1 1 where
  Hm := fun x => x
  Hn := fun _ => 1
  interval := fun _ => ∅
  alpha := fun _ _ => 0
  interval_property := by
    intro x m n k hm hn hmin hmax
    have hfalse : False := by simpa using hm
    exact hfalse.elim
  scales := by
    intro x hx
    have hx1 : (1 : ℝ) ≤ x := by linarith
    simpa [Real.rpow_zero] using
      (show (1 : ℝ) ≤ x ∧ 1 ≤ 1 ∧ x ≤ x ∧ x ≤ x from
        ⟨hx1, le_rfl, le_rfl, le_rfl⟩)
  interval_bounds := by simp
  rough_support := by simp
  coefficient_bound := by simp

theorem longCancellation_witness : ∃ family : CoefficientFamily 0 1 1 1,
    HasLongCoefficientCancellation family := by
  refine ⟨zeroCancellationFamily, ?_⟩
  intro A₀ B A hA₀ hB hA
  refine ⟨1, 2, by norm_num, by norm_num, ?_⟩
  intro x hx k hk hkL χ t ht
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  simp [familyTerms, zeroCancellationFamily]
  positivity
example : ∃ family : CoefficientFamily 0 1 1 1,
    HasLongCoefficientCancellation family := longCancellation_witness

#print axioms roughAbove_witness
#print axioms validBands_witness
#print axioms markedInvariant_witness
#print axioms groupInteger_witness
#print axioms testFunction_witness
#print axioms longCancellation_witness

end ArtinPrimitiveRoots.Review
