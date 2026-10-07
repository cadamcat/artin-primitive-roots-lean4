import ArtinPrimitiveRoots.Construction.Defs
import ArtinPrimitiveRoots.TypeII.PD.Determinant
import ArtinPrimitiveRoots.TypeII.PD.Physical
import ArtinPrimitiveRoots.TypeII.PD.Memory

/-!
Kernel-checked inhabitance witnesses for the Prop-valued predicates used in part B.
The smooth witness uses Mathlib's `ContDiffBump`; its support is a compact open interval
strictly inside `(1, 2)`.
-/

namespace ArtinPrimitiveRoots.Review.SolGateB

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
  refine ⟨1, 2, by norm_num, by norm_num, by norm_num [zeroCancellationFamily], ?_⟩
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


/-! Positive-delta witness: the earlier review's family used δ=0, outside the
transfer theorem's hypotheses. -/
noncomputable def positiveCancellationFamily : CoefficientFamily (1 / 4) 1 1 1 where
  Hm := fun x => x ^ (1 / 2 : ℝ)
  Hn := fun x => x ^ (1 / 2 : ℝ)
  interval := fun _ => ∅
  alpha := fun _ _ => 0
  interval_property := by simp [IsNatInterval]
  scales := by
    intro x hx
    have hx1 : (1 : ℝ) ≤ x := by linarith
    have hx0 : 0 < x := by linarith
    have hlo : x ^ (1 / 4 : ℝ) ≤ x ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    have hprod : x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by
      rw [← Real.rpow_add hx0]
      norm_num
    exact ⟨hlo, hlo, by simpa only [one_mul] using hprod.ge,
      by simpa only [one_mul] using hprod.le⟩
  interval_bounds := by simp
  rough_support := by simp
  coefficient_bound := by simp

/-- The asymptotic threshold makes the formerly empty endpoint parameter choice inhabited. -/
noncomputable def quarterCoefficientFamily :
    CoefficientFamily (1 / 4) 1 (1 / 4) (1 / 4) where
  xMin := Real.rpow 4 4
  xMin_ge_two := by norm_num [Real.rpow_natCast]
  Hm := fun x => Real.rpow x (1 / 4 : ℝ)
  Hn := fun x => Real.rpow x (3 / 4 : ℝ) / 4
  interval := fun _ => ∅
  alpha := fun _ _ => 0
  interval_property := by simp [IsNatInterval]
  scales := by
    intro x hx
    have hxMin : Real.rpow 4 4 ≤ x := hx
    have hx0 : 0 < x := lt_of_lt_of_le (by norm_num [Real.rpow_natCast]) hxMin
    have hAt : Real.rpow (Real.rpow 4 4) (1 / 4 : ℝ) = 4 := by
      simpa using (Real.rpow_rpow_inv (by norm_num : (0 : ℝ) ≤ 4)
        (by norm_num : (4 : ℝ) ≠ 0))
    have hquarter : (4 : ℝ) ≤ Real.rpow x (1 / 4 : ℝ) := by
      calc
        4 = Real.rpow (Real.rpow 4 4) (1 / 4 : ℝ) := hAt.symm
        _ ≤ Real.rpow x (1 / 4 : ℝ) :=
          Real.rpow_le_rpow
            (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4) 4).le
            hxMin (by norm_num)
    have hroot : (4 : ℝ) ≤ Real.rpow x (1 / 2 : ℝ) := by
      have hsquare : Real.rpow x (1 / 4 : ℝ) * Real.rpow x (1 / 4 : ℝ) =
          Real.rpow x (1 / 2 : ℝ) := by
        calc
          Real.rpow x (1 / 4 : ℝ) * Real.rpow x (1 / 4 : ℝ) =
              Real.rpow x (1 / 4 + 1 / 4 : ℝ) :=
            (Real.rpow_add hx0 (1 / 4 : ℝ) (1 / 4 : ℝ)).symm
          _ = Real.rpow x (1 / 2 : ℝ) := by
            rw [show (1 / 4 + 1 / 4 : ℝ) = 1 / 2 by norm_num]
      calc
        4 ≤ 16 := by norm_num
        _ ≤ Real.rpow x (1 / 4 : ℝ) * Real.rpow x (1 / 4 : ℝ) := by nlinarith [hquarter]
        _ = Real.rpow x (1 / 2 : ℝ) := hsquare
    have hmul : Real.rpow x (1 / 4 : ℝ) ≤ Real.rpow x (3 / 4 : ℝ) / 4 := by
      have hpow0 : 0 ≤ Real.rpow x (1 / 4 : ℝ) :=
        (Real.rpow_pos_of_pos hx0 _).le
      have hmul' := mul_le_mul_of_nonneg_left hroot hpow0
      calc
        Real.rpow x (1 / 4 : ℝ) ≤
            Real.rpow x (1 / 4 : ℝ) * Real.rpow x (1 / 2 : ℝ) / 4 := by
          nlinarith
        _ = Real.rpow x (1 / 4 + 1 / 2 : ℝ) / 4 := by
          exact congrArg (fun y : ℝ => y / 4)
            (Real.rpow_add hx0 (1 / 4 : ℝ) (1 / 2 : ℝ)).symm
        _ = Real.rpow x (3 / 4 : ℝ) / 4 := by
          rw [show (1 / 4 + 1 / 2 : ℝ) = 3 / 4 by norm_num]
    have hprod : Real.rpow x (1 / 4 : ℝ) *
        (Real.rpow x (3 / 4 : ℝ) / 4) = x / 4 := by
      calc
        Real.rpow x (1 / 4 : ℝ) * (Real.rpow x (3 / 4 : ℝ) / 4) =
            (Real.rpow x (1 / 4 : ℝ) * Real.rpow x (3 / 4 : ℝ)) / 4 := by ring
        _ = Real.rpow x (1 / 4 + 3 / 4 : ℝ) / 4 := by
          exact congrArg (fun y : ℝ => y / 4)
            (Real.rpow_add hx0 (1 / 4 : ℝ) (3 / 4 : ℝ)).symm
        _ = x / 4 := by
          have hexp : (1 / 4 + 3 / 4 : ℝ) = 1 := by norm_num
          have hone : Real.rpow x (1 : ℝ) = x := Real.rpow_one x
          rw [hexp, hone]
    exact ⟨le_rfl, hmul,
      by rw [hprod]; exact le_of_eq (by ring),
      by rw [hprod]; exact le_of_eq (by ring)⟩
  interval_bounds := by simp
  rough_support := by simp
  coefficient_bound := by simp

theorem quarterCoefficientFamily_inhabited :
    Nonempty (CoefficientFamily (1 / 4) 1 (1 / 4) (1 / 4)) :=
  ⟨quarterCoefficientFamily⟩

theorem positiveCancellation_witness : ∃ family : CoefficientFamily (1 / 4) 1 1 1,
    HasLongCoefficientCancellation family := by
  refine ⟨positiveCancellationFamily, ?_⟩
  intro A0 B A hA0 hB hA
  refine ⟨1, 2, by norm_num, by norm_num, by norm_num [positiveCancellationFamily], ?_⟩
  intro x hx k hk hkL chi t ht
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  simp [familyTerms, positiveCancellationFamily]
  positivity

open ArtinPrimitiveRoots.TypeII.PD

noncomputable def arcBump : ContDiffBump (0 : ℝ) :=
  ⟨4, 5, by norm_num, by norm_num⟩

theorem arcCutoff_witness : ∃ psi : ℝ → ℝ, IsArcCutoff psi := by
  refine ⟨arcBump, arcBump.contDiff, arcBump.hasCompactSupport, ?_⟩
  intro t ht
  apply arcBump.one_of_mem_closedBall
  simpa [arcBump, Metric.mem_closedBall, Real.dist_eq, abs_le] using ht

theorem memoryRho_witness : ∃ rho : ℝ, IsMemoryRho (1 / 4) rho := by
  refine ⟨3 / 4, ?_⟩
  norm_num [IsMemoryRho, Real.sqrt_eq_iff_mul_self_eq]

theorem secondCoefficient_witness (S : PDScale) (C : ℝ) (hx : 2 ≤ S.x) :
    ∃ beta : ℕ → ℂ, IsSecondCoefficient S C beta := by
  refine ⟨fun _ => 0, ?_⟩
  constructor
  · simp
  · intro n hn
    simp only [norm_zero]
    exact Real.rpow_nonneg (Real.log_nonneg (by linarith)) C

#print axioms positiveCancellation_witness
#print axioms quarterCoefficientFamily_inhabited
#print axioms arcCutoff_witness
#print axioms memoryRho_witness
#print axioms secondCoefficient_witness

/-- Any bounded supported family can retain arbitrary coefficients at one scale
and vanish afterward, hence satisfy the asymptotic cancellation hypothesis. -/
noncomputable def finiteSpikeFamily {δ C c₁ c₂ : ℝ}
    (f : CoefficientFamily δ C c₁ c₂) (xstar : ℝ) : CoefficientFamily δ C c₁ c₂ :=
  { f with
    alpha := fun x m => if x = xstar then f.alpha x m else 0
    rough_support := by
      intro x hx m hm
      by_cases he : x = xstar
      · exact f.rough_support x hx m (by simpa [he] using hm)
      · simp [he] at hm
    coefficient_bound := by
      intro x hx m hm
      by_cases he : x = xstar
      · simpa [he] using f.coefficient_bound x hx m hm
      · simp only [he, if_false, norm_zero]
        have hx1 : (1 : ℝ) ≤ x := by linarith [f.xMin_ge_two, hx]
        exact Real.rpow_nonneg (Real.log_nonneg hx1) C }

theorem finiteSpike_longCancellation {δ C c₁ c₂ : ℝ}
    (f : CoefficientFamily δ C c₁ c₂) (xstar : ℝ) :
    HasLongCoefficientCancellation (finiteSpikeFamily f xstar) := by
  intro A0 B A hA0 hB hA
  refine ⟨1, max f.xMin (xstar + 1), by norm_num,
    le_trans f.xMin_ge_two (le_max_left _ _), le_max_left _ _, ?_⟩
  intro x hx k hk hkL chi t ht
  have hx2 : 2 ≤ x := (le_trans f.xMin_ge_two (le_max_left _ _)).trans hx
  have hxs : xstar + 1 ≤ x := (le_max_right _ _).trans hx
  have he : x ≠ xstar := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  simp [finiteSpikeFamily, he]
  exact (Real.rpow_pos_of_pos hlog _).le

#print axioms finiteSpike_longCancellation

end ArtinPrimitiveRoots.Review.SolGateB

namespace ArtinPrimitiveRoots.Review.SolGateB

open ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD

/-- The unrestricted determinant equivalence fails at zero inputs. -/
theorem cauchy_zero_inputs :
    ¬ ((∃ h : ℕ, 0 * 0 - 1 = 2 * h ∧ 0 * 0 - 1 = 3 * h) ↔
      (3 : ℤ) * 0 * 0 - (2 : ℤ) * 0 * 0 = 3 - 2) := by
  norm_num

/-- Unequal marked products have the same zero-input obstruction. -/
theorem cauchy_zero_inputs_general (aa bb : ℕ) (hne : aa ≠ bb) :
    ¬ ((∃ h : ℕ, 0 * 0 - 1 = aa * h ∧ 0 * 0 - 1 = bb * h) ↔
      (bb : ℤ) * 0 * 0 - (aa : ℤ) * 0 * 0 = (bb : ℤ) - aa) := by
  intro h
  have hz := h.mp ⟨0, by simp, by simp⟩
  have he : (bb : ℤ) = aa := by simpa [sub_eq_zero] using hz.symm
  exact hne (by exact_mod_cast he.symm)

#print axioms cauchy_zero_inputs
#print axioms cauchy_zero_inputs_general

end ArtinPrimitiveRoots.Review.SolGateB
namespace ArtinPrimitiveRoots.Review.SolGateB

open ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD

theorem ghost_single_birth {K : ℕ} (F : PDFix K) (S : PDScale)
    (rho : ℝ) (j : ℕ) (i : Fin K) (p : ℕ) :
    ghostGroupCoeff F S rho j i 0 0 1 [p] =
      -memoryEta S.x F.q_d j * bandMass S.x (F.a i) / rho *
        memoryNu S.x K F.a F.q_d i p := by
  simp [ghostGroupCoeff]

/-- One additional ordered coordinate changes the factorial measure by this factor. -/
theorem factorial_measure_step (v w : ℝ) (n : ℕ) :
    v ^ n * w / ((n + 1).factorial : ℝ) =
      (v ^ n / (n.factorial : ℝ)) * w / (n + 1 : ℝ) := by
  rw [Nat.factorial_succ, Nat.cast_mul]
  push_cast
  field_simp

/-- The actual ghost creation coefficient gives an unbounded column factor. -/
theorem ghost_creation_column_ratio {K : ℕ} (F : PDFix K) (S : PDScale)
    (rho : ℝ) (j : ℕ) (i : Fin K) (p n : ℕ) (mu : ℝ)
    (hmu : 0 < mu) (hrho : 0 < rho)
    (heta : 0 ≤ memoryEta S.x F.q_d j)
    (hV : 0 < bandMass S.x (F.a i))
    (hnu : 0 < memoryNu S.x K F.a F.q_d i p) :
    mu * |ghostGroupCoeff F S rho j i 0 0 1 [p]| /
      (mu * memoryNu S.x K F.a F.q_d i p / (n + 1 : ℝ)) =
        (n + 1 : ℝ) * memoryEta S.x F.q_d j * bandMass S.x (F.a i) / rho := by
  rw [ghost_single_birth]
  rw [abs_mul, abs_div, abs_mul, abs_neg, abs_of_nonneg heta,
    abs_of_pos hV, abs_of_pos hrho, abs_of_pos hnu]
  field_simp

/-- Necessary norm condition on the single-birth submatrix, tested by a function
equal to one on its targets. `mass` is the sum of the fresh-prime weights. -/
theorem ordered_creation_norm_lower (n : ℕ) (mu a mass c : ℝ)
    (hmu : 0 < mu) (hmass : 0 < mass)
    (h : mu * (a * mass) ^ 2 ≤ c ^ 2 * (mu * mass / (n + 1 : ℝ))) :
    (n + 1 : ℝ) * a ^ 2 * mass ≤ c ^ 2 := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have h1 : (a * mass) ^ 2 ≤ c ^ 2 * mass / (n + 1 : ℝ) := by
    exact (mul_le_mul_iff_right₀ hmu).mp (by convert h using 1 <;> ring)
  have h2 := (le_div_iff₀ hn).mp h1
  exact (mul_le_mul_iff_right₀ hmass).mp (by nlinarith [h2])

/-- No constant controls ordered creation on all factorial-weighted sectors. -/
theorem ordered_creation_unbounded (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    ¬ ∃ c : ℝ, ∀ n : ℕ, (n + 1 : ℝ) * a ^ 2 * mass ≤ c ^ 2 := by
  rintro ⟨c, hc⟩
  have ham : 0 < a ^ 2 * mass := by positivity
  obtain ⟨n, hn⟩ := exists_nat_gt (c ^ 2 / (a ^ 2 * mass))
  have hn' := (div_lt_iff₀ ham).mp hn
  have hh := hc n
  nlinarith

#print axioms ghost_single_birth
#print axioms factorial_measure_step
#print axioms ghost_creation_column_ratio
#print axioms ordered_creation_norm_lower
#print axioms ordered_creation_unbounded

end ArtinPrimitiveRoots.Review.SolGateB

/-! A smooth, nonnegative, compactly supported dyadic partition. This witnesses
the combined cutoff hypothesis, rather than its clauses separately. -/

namespace ArtinPrimitiveRoots.Review.SolGateB

open ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD

noncomputable def dyadicEta (y : ℝ) : ℝ :=
  Real.smoothTransition (y - 1) - Real.smoothTransition (y / 2 - 1)

lemma dyadicEta_zero_low {y : ℝ} (hy : y ≤ 1) : dyadicEta y = 0 := by
  have h1 : y - 1 ≤ 0 := by linarith
  have h2 : y / 2 - 1 ≤ 0 := by linarith
  simp [dyadicEta, Real.smoothTransition.zero_of_nonpos h1,
    Real.smoothTransition.zero_of_nonpos h2]

lemma dyadicEta_zero_high {y : ℝ} (hy : 4 ≤ y) : dyadicEta y = 0 := by
  have h1 : 1 ≤ y - 1 := by linarith
  have h2 : 1 ≤ y / 2 - 1 := by linarith
  simp [dyadicEta, Real.smoothTransition.one_of_one_le h1,
    Real.smoothTransition.one_of_one_le h2]

lemma dyadicEta_nonneg (y : ℝ) : 0 ≤ dyadicEta y := by
  by_cases hy : y ≤ 1
  · simp [dyadicEta_zero_low hy]
  · apply sub_nonneg.mpr
    exact Real.smoothTransition.monotone (by linarith)

lemma dyadicEta_pair {z : ℝ} (hz1 : 1 ≤ z) (hz2 : z ≤ 2) :
    dyadicEta (2 * z) + dyadicEta z = 1 := by
  have h1 : 1 ≤ 2 * z - 1 := by linarith
  have h2 : z / 2 - 1 ≤ 0 := by linarith
  simp [dyadicEta, Real.smoothTransition.one_of_one_le h1,
    Real.smoothTransition.zero_of_nonpos h2]

theorem dyadicEta_partition : IsDyadicPartition dyadicEta := by
  classical
  intro y hy
  let k : ℤ := ⌊Real.log y / Real.log 2⌋
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hklo : (k : ℝ) * Real.log 2 ≤ Real.log y := by
    exact (le_div_iff₀ hlog2).mp (Int.floor_le _)
  have hkhi : Real.log y < ((k : ℝ) + 1) * Real.log 2 := by
    exact (div_lt_iff₀ hlog2).mp (Int.lt_floor_add_one _)
  have hk0 : (0 : ℝ) < 2 ^ k := zpow_pos (by norm_num) _
  have hkp0 : (0 : ℝ) < 2 ^ (k + 1) := zpow_pos (by norm_num) _
  have hkLower : (2 : ℝ) ^ k ≤ y := by
    apply (Real.log_le_log_iff hk0 hy).mp
    simpa [Real.log_zpow] using hklo
  have hkUpper : y < (2 : ℝ) ^ (k + 1) := by
    apply (Real.log_lt_log_iff hy hkp0).mp
    simpa [Real.log_zpow] using hkhi
  let z := y / (2 : ℝ) ^ k
  have hz1 : 1 ≤ z := (one_le_div hk0).mpr hkLower
  have hz2 : z < 2 := by
    apply (div_lt_iff₀ hk0).mpr
    simpa [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), mul_comm] using hkUpper
  have hprev : y / (2 : ℝ) ^ (k - 1) = 2 * z := by
    dsimp [z]
    rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
    simp only [zpow_one]
    field_simp
  have hsupport : ∀ j : ℤ, j ∉ ({k - 1, k} : Finset ℤ) →
      dyadicEta (y / (2 : ℝ) ^ j) = 0 := by
    intro j hj
    have hne : j ≠ k - 1 ∧ j ≠ k := by simpa using hj
    have hne1 := hne.1
    have hne2 := hne.2
    have hj0 : (0 : ℝ) < 2 ^ j := zpow_pos (by norm_num) _
    by_cases hjk : j < k - 1
    · apply dyadicEta_zero_high
      apply (le_div_iff₀ hj0).mpr
      have hjk2 : j + 2 ≤ k := by omega
      have hpow := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hjk2
      have h4 : (2 : ℝ) ^ (j + 2) = 4 * (2 : ℝ) ^ j := by
        rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        norm_num <;> ring
      rw [h4] at hpow
      exact hpow.trans hkLower
    · apply dyadicEta_zero_low
      apply (div_le_one hj0).mpr
      have hjk1 : k + 1 ≤ j := by omega
      have hpow := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hjk1
      exact hkUpper.le.trans hpow
  rw [tsum_eq_sum hsupport]
  have hkne : k - 1 ≠ k := by omega
  rw [Finset.sum_pair hkne, hprev]
  exact dyadicEta_pair hz1 hz2.le

theorem dyadicEta_valid : IsCauchyCutoff dyadicEta := by
  refine ⟨?_, ?_, dyadicEta_nonneg, dyadicEta_partition⟩
  · unfold dyadicEta
    apply ContDiff.sub
    · exact Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)
    · exact Real.smoothTransition.contDiff.comp
        ((contDiff_id.div_const 2).sub contDiff_const)
  · intro y hy
    have hne : dyadicEta y ≠ 0 := by simpa only [Function.mem_support] using hy
    constructor
    · by_contra! hlo
      exact hne (dyadicEta_zero_low hlo.le)
    · by_contra! hhi
      exact hne (dyadicEta_zero_high hhi.le)

theorem cauchyCutoff_witness : ∃ eta : ℝ → ℝ, IsCauchyCutoff eta :=
  ⟨dyadicEta, dyadicEta_valid⟩

noncomputable def pdArcBump : ContDiffBump (0 : ℝ) :=
  ⟨4, 5, by norm_num, by norm_num⟩

noncomputable def witnessPDFix : PDFix 1 :=
  ⟨fun _ => 3 / 20, 1 / 4, 1, dyadicEta, pdArcBump⟩

theorem witnessPDFix_valid : witnessPDFix.Valid := by
  refine ⟨?_, by norm_num [witnessPDFix], by norm_num [witnessPDFix],
    by norm_num [witnessPDFix], dyadicEta_valid, ?_⟩
  · norm_num [witnessPDFix, ValidBands]
  · refine ⟨pdArcBump.contDiff, pdArcBump.hasCompactSupport, ?_⟩
    intro t ht
    apply pdArcBump.one_of_mem_closedBall
    simpa [pdArcBump, Metric.mem_closedBall, Real.dist_eq, abs_le] using ht

example : ∃ F : PDFix 1, F.Valid := ⟨witnessPDFix, witnessPDFix_valid⟩

noncomputable def witnessPDScale : PDScale :=
  ⟨Real.exp 1, Real.exp 1, Real.exp 1, 2, 1⟩

theorem witnessPDScale_valid : witnessPDScale.Valid 1 (1 / 4) 1 4 := by
  have he2 := Real.exp_one_gt_two
  have he3 := Real.exp_one_lt_three
  have he0 : 0 < Real.exp 1 := Real.exp_pos _
  have he1 : 1 ≤ Real.exp 1 := by linarith
  have hp : Real.rpow (Real.exp 1) (1 / 4 : ℝ) ≤ Real.exp 1 := by
    simpa using Real.rpow_le_rpow_of_exponent_le he1 (by norm_num : (1 / 4 : ℝ) ≤ 1)
  dsimp [PDScale.Valid, witnessPDScale]
  refine ⟨he2.le, hp, hp, ?_, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · unfold dyadicScales
    simp only [Real.log_exp]
    have hpow (a : ℝ) : Real.rpow 1 a = 1 := by change (1 : ℝ) ^ a = 1; simp
    simp only [hpow]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨1, ?_, by norm_num⟩, ?_, ?_⟩
    · apply Finset.mem_range.mpr
      apply Nat.lt_succ_of_le
      apply (Nat.le_floor_iff (by positivity)).mpr
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hlog2le : Real.log 2 ≤ 1 := by
        have hg := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        norm_num at hg
        exact hg
      apply (le_div_iff₀ hlog2).mpr
      norm_num
      linarith
    · have hg := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at hg ⊢
      linarith
    · have hg := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at hg ⊢
      linarith
  · unfold padScales
    simp only [Real.log_exp]
    have hpow (a : ℝ) : Real.rpow 1 a = 1 := by change (1 : ℝ) ^ a = 1; simp
    simp only [hpow]
    apply Finset.mem_image.mpr
    exact ⟨0, by norm_num, by norm_num⟩

example : ∃ S : PDScale, S.Valid 1 (1 / 4) 1 4 :=
  ⟨witnessPDScale, witnessPDScale_valid⟩

theorem three_in_witness_band : 3 ∈ primeBand (Real.exp 1) (3 / 20) := by
  have he3 := Real.exp_one_lt_three
  have he2 := Real.exp_one_gt_two
  have he0 : 0 < Real.exp 1 := Real.exp_pos _
  have hexp2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  have h3 : (3 : ℝ) ≤ Real.exp 2 := by rw [hexp2]; nlinarith
  unfold primeBand
  simp only [Real.log_exp]
  have hpow (a : ℝ) : Real.rpow 1 a = 1 := by change (1 : ℝ) ^ a = 1; simp
  simp only [hpow, mul_one]
  apply Finset.mem_filter.mpr
  refine ⟨?_, by norm_num, he3.le, h3⟩
  apply Finset.mem_range.mpr
  exact Nat.lt_succ_of_le ((Nat.le_floor_iff (Real.exp_pos _).le).mpr h3)

theorem memValid_witness : ∃ s : MemPoint (Real.exp 1) 1,
    MemValid witnessPDFix witnessPDScale s := by
  refine ⟨((1, 0), (fun _ _ => 3), fun _ => []), ?_⟩
  refine ⟨by norm_num, ?_, by simp⟩
  intro i j
  exact three_in_witness_band

theorem five_in_witness_band : 5 ∈ primeBand (Real.exp 1) (3 / 20) := by
  have he3 := Real.exp_one_lt_three
  have he0 : 0 < Real.exp 1 := Real.exp_pos _
  have hexp2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  have h5 : (5 : ℝ) ≤ Real.exp 2 := by
    rw [hexp2]
    nlinarith [Real.exp_one_gt_d9, sq_nonneg (Real.exp 1 - 5 / 2)]
  unfold primeBand
  simp only [Real.log_exp, Real.rpow_eq_pow, Real.one_rpow, mul_one]
  apply Finset.mem_filter.mpr
  refine ⟨?_, by norm_num, by norm_num; linarith, h5⟩
  apply Finset.mem_range.mpr
  exact Nat.lt_succ_of_le ((Nat.le_floor_iff (Real.exp_pos _).le).mpr h5)

noncomputable def witnessPrimeLists : PrimeLists (Real.exp 1) 1 :=
  fun _ j => if j.val = 0 then 3 else 5

theorem witnessPrimeLists_valid :
    ValidPrimeLists (Real.exp 1) 1 (fun _ => 3 / 20) witnessPrimeLists := by
  have hslots : slotCount (Real.exp 1) = 2 := by
    norm_num [slotCount, momentJ, Real.rpow_eq_pow]
  constructor
  · intro i j
    by_cases hj : j.val = 0
    · simpa [witnessPrimeLists, hj] using
        (show Nat.Prime 3 ∧ 3 ∈ primeBand (Real.exp 1) (3 / 20) from
          ⟨by norm_num, three_in_witness_band⟩)
    · simpa [witnessPrimeLists, hj] using
        (show Nat.Prime 5 ∧ 5 ∈ primeBand (Real.exp 1) (3 / 20) from
          ⟨by norm_num, five_in_witness_band⟩)
  · intro i j j' hne
    have hj : j.val < 2 := by simpa [hslots] using j.isLt
    have hj' : j'.val < 2 := by simpa [hslots] using j'.isLt
    have hvals : j.val ≠ j'.val := fun h => hne (Fin.ext h)
    have hjv : j.val = 0 ∨ j.val = 1 := by omega
    have hjv' : j'.val = 0 ∨ j'.val = 1 := by omega
    rcases hjv with hjv | hjv <;> rcases hjv' with hjv' | hjv' <;>
      simp_all [witnessPrimeLists]

theorem physicalState_witness : Nonempty (PState witnessPDFix witnessPDScale) := by
  refine ⟨{
    first := 15
    second := 4
    completionC := 11
    completionD := 3
    labels := witnessPrimeLists
    primitive := by norm_num
    first_lower := ?_
    first_upper := ?_
    second_lower := ?_
    second_upper := ?_
    det_one := by norm_num
    completion_range := by norm_num
    label_prime := fun i j => (witnessPrimeLists_valid.1 i j).1
    label_in_band := fun i j => (witnessPrimeLists_valid.1 i j).2
    label_divides := ?_
    label_distinct := witnessPrimeLists_valid.2 }⟩
  · norm_num [PDScale.H, witnessPDScale]
    linarith [Real.exp_one_lt_three]
  · norm_num [PDScale.H, witnessPDScale]
    linarith [Real.exp_one_gt_two]
  · change Real.exp 1 ≤ 4
    linarith [Real.exp_one_lt_three]
  · change (4 : ℝ) ≤ 2 * Real.exp 1
    linarith [Real.exp_one_gt_two]
  · intro i j
    by_cases hj : j.val = 0 <;> norm_num [witnessPrimeLists, hj]

theorem envValid_witness : ∃ s : EnvPoint (Real.exp 1) 1,
    EnvValid witnessPDFix witnessPDScale s :=
  ⟨((1, 0), witnessPrimeLists), by norm_num, witnessPrimeLists_valid⟩

theorem markedTuple_witness : ∃ t : Fin 1 → ℕ,
    IsMarkedPrimeTuple (Real.exp 1) 1 (fun _ => 3 / 20) t :=
  ⟨fun _ => 3, fun _ => three_in_witness_band⟩

theorem freshChoice_witness (x : ℝ) {K : ℕ} (a : Fin K → ℝ) :
    ∃ fresh : Fin K → ℕ, IsFreshChoice x a Finset.univ fresh := by
  refine ⟨fun _ => 1, ?_⟩
  simp [IsFreshChoice]

#print axioms dyadicEta_partition
#print axioms cauchyCutoff_witness
#print axioms witnessPDFix_valid
#print axioms witnessPDScale_valid
#print axioms three_in_witness_band
#print axioms memValid_witness
#print axioms witnessPrimeLists_valid
#print axioms physicalState_witness
#print axioms envValid_witness
#print axioms markedTuple_witness
#print axioms freshChoice_witness

end ArtinPrimitiveRoots.Review.SolGateB
