import ArtinPrimitiveRoots.TypeII.Defs
import ArtinPrimitiveRoots.Ext.TypeIIInputs

/-! The abstract marked coefficient transfer from `08-type-ii.tex:99-251`. -/

namespace ArtinPrimitiveRoots.TypeII

open Classical
open Filter
open scoped Topology

private lemma mem_primesUpTo_iff {y : ℝ} (hy : 0 ≤ y) {p : ℕ} :
    p ∈ primesUpTo y ↔ p.Prime ∧ (p : ℝ) ≤ y := by
  simp only [primesUpTo, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff,
    Nat.le_floor_iff hy]
  exact and_comm

private lemma primeBand_eq_filter (x a : ℝ) :
    primeBand x a = (primesUpTo (Real.exp (2 * Real.rpow (Real.log x) a))).filter
      (fun (p : ℕ) => Real.exp (Real.rpow (Real.log x) a) ≤ (p : ℝ)) := by
  ext p
  have hB : 0 ≤ Real.exp (2 * Real.rpow (Real.log x) a) := (Real.exp_pos _).le
  simp only [primeBand, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff,
    Nat.le_floor_iff hB]
  rw [mem_primesUpTo_iff hB]
  tauto

private noncomputable def reciprocalPrimeSum (y : ℝ) : ℝ :=
  ∑ p ∈ primesUpTo y, 1 / (p : ℝ)

private noncomputable def reciprocalMassOn (s : Finset ℕ) : ℝ :=
  ∑ p ∈ s, 1 / (p : ℝ)

private noncomputable def endpointPrimes (A : ℝ) : Finset ℕ :=
  (primesUpTo A).filter (fun (p : ℕ) => A ≤ (p : ℝ))

private lemma bandMass_cut_identity {x a : ℝ} (hx : 2 ≤ x)
    (ha₀ : 0 < a) :
    bandMass x a =
      reciprocalPrimeSum (Real.exp (2 * Real.rpow (Real.log x) a)) -
        reciprocalPrimeSum (Real.exp (Real.rpow (Real.log x) a)) +
        reciprocalMassOn (endpointPrimes (Real.exp (Real.rpow (Real.log x) a))) := by
  let u := Real.rpow (Real.log x) a
  let A := Real.exp u
  let B := Real.exp (2 * u)
  have hx1 : 1 < x := by linarith
  have hu : 0 < u := Real.rpow_pos_of_pos (Real.log_pos hx1) a
  have hA0 : 0 ≤ A := (Real.exp_pos _).le
  have hB0 : 0 ≤ B := (Real.exp_pos _).le
  have hAB : A ≤ B := by
    change Real.exp u ≤ Real.exp (2 * u)
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hbelow : (primesUpTo B).filter (fun (p : ℕ) => ¬ A ≤ (p : ℝ)) =
      (primesUpTo A).filter (fun (p : ℕ) => (p : ℝ) < A) := by
    ext p
    simp only [Finset.mem_filter]
    rw [mem_primesUpTo_iff hB0, mem_primesUpTo_iff hA0]
    constructor
    · rintro ⟨⟨hp, hpB⟩, hpA⟩
      exact ⟨⟨hp, le_of_lt (not_le.mp hpA)⟩, not_le.mp hpA⟩
    · rintro ⟨⟨hp, hpA⟩, hpLt⟩
      exact ⟨⟨hp, hpA.trans hAB⟩, not_le.mpr hpLt⟩
  let highB : Finset ℕ := (primesUpTo B).filter (fun (p : ℕ) => A ≤ (p : ℝ))
  let lowB : Finset ℕ := (primesUpTo B).filter (fun (p : ℕ) => ¬ A ≤ (p : ℝ))
  let lowA : Finset ℕ := (primesUpTo A).filter (fun (p : ℕ) => (p : ℝ) < A)
  let highA : Finset ℕ := (primesUpTo A).filter (fun (p : ℕ) => ¬ (p : ℝ) < A)
  have hsplitB : reciprocalPrimeSum B = reciprocalMassOn highB + reciprocalMassOn lowB := by
    unfold reciprocalPrimeSum reciprocalMassOn
    simpa [highB, lowB] using
      (Finset.sum_filter_add_sum_filter_not (primesUpTo B)
        (fun (p : ℕ) => A ≤ (p : ℝ)) (fun (p : ℕ) => 1 / (p : ℝ))).symm
  have hsplitA : reciprocalPrimeSum A = reciprocalMassOn lowA + reciprocalMassOn highA := by
    unfold reciprocalPrimeSum reciprocalMassOn
    simpa [lowA, highA] using
      (Finset.sum_filter_add_sum_filter_not (primesUpTo A)
        (fun (p : ℕ) => (p : ℝ) < A) (fun (p : ℕ) => 1 / (p : ℝ))).symm
  have hbelowSum : reciprocalMassOn lowB = reciprocalMassOn lowA := by
    unfold reciprocalMassOn
    rw [show lowB = lowA by exact hbelow]
  have hhighA : highA = endpointPrimes A := by
    ext p
    simp [highA, endpointPrimes, not_lt]
  have hBand : bandMass x a = reciprocalMassOn highB := by
    rw [bandMass, primeBand_eq_filter]
    change reciprocalMassOn ((primesUpTo B).filter
      (fun (p : ℕ) => Real.exp (Real.rpow (Real.log x) a) ≤ (p : ℝ))) = _
    rfl
  have hmain : reciprocalMassOn highB =
      reciprocalPrimeSum B - reciprocalPrimeSum A + reciprocalMassOn (endpointPrimes A) := by
    rw [hsplitB, hsplitA, hbelowSum, hhighA]
    ring
  rw [hBand]
  simpa [u, A, B] using hmain

private lemma bandMass_endpoint_le {A : ℝ} (hA : 0 < A) :
    reciprocalMassOn (endpointPrimes A) ≤ 1 / A := by
  have hA0 : 0 ≤ A := hA.le
  let s : Finset ℕ := endpointPrimes A
  have hcard : s.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hp q hq
    have hp' := Finset.mem_filter.mp hp
    have hq' := Finset.mem_filter.mp hq
    have hpeq := (mem_primesUpTo_iff hA0).mp hp'.1
    have hqeq := (mem_primesUpTo_iff hA0).mp hq'.1
    have hpA : (p : ℝ) = A := le_antisymm hpeq.2 hp'.2
    have hqA : (q : ℝ) = A := le_antisymm hqeq.2 hq'.2
    exact Nat.cast_injective (hpA.trans hqA.symm)
  have hsummand : ∀ p ∈ s, 1 / (p : ℝ) ≤ 1 / A := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpeq := (mem_primesUpTo_iff hA0).mp hp'.1
    have hcast : (p : ℝ) = A := le_antisymm hpeq.2 hp'.2
    rw [hcast]
  calc
    _ = reciprocalMassOn s := rfl
    _ ≤ (s.card : ℝ) * (1 / A) := by
      unfold reciprocalMassOn
      simpa [nsmul_eq_mul] using (Finset.sum_le_card_nsmul s (fun p => 1 / (p : ℝ))
        (1 / A) hsummand)
    _ ≤ 1 / A := by
      have hcard' : (s.card : ℝ) ≤ 1 := by exact_mod_cast hcard
      calc
        (s.card : ℝ) * (1 / A) ≤ 1 * (1 / A) :=
          mul_le_mul_of_nonneg_right hcard' (by positivity)
        _ = 1 / A := by ring

/-- Convexity in the natural order, expressing that a set of natural numbers is an interval.
This is correction 2 from review lane `rev-b`. -/
def IsNatInterval (I : Set ℕ) : Prop :=
  ∀ ⦃m n k : ℕ⦄, m ∈ I → n ∈ I → min m n ≤ k → k ≤ max m n → k ∈ I

/-- `t2:band-mass`, 08-type-ii.tex:54-56 and 12-construction.tex:29-31. For each fixed
exponent `a∈(0,1)`, the reciprocal-prime mass of its band tends to `log 2`. -/
theorem band_mass (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) :
    ∀ ε : ℝ, 0 < ε → ∃ x₀ : ℝ, 2 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        |bandMass x a - Real.log 2| ≤ ε ∧ 0 < bandMass x a := by
  intro ε hε
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let η := min (ε / 4) (Real.log 2 / 8)
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hηε : η ≤ ε / 4 := min_le_left _ _
  have hηlog : η ≤ Real.log 2 / 8 := min_le_right _ _
  obtain ⟨y₀, hy₀, hmertens⟩ := ArtinPrimitiveRoots.Ext.TypeIIInputs.mertens.1 η hη
  have hpow : Tendsto (fun x : ℝ => Real.rpow (Real.log x) a) atTop atTop :=
    (tendsto_rpow_atTop ha₀).comp Real.tendsto_log_atTop
  have hexp : Tendsto (fun x : ℝ => Real.exp (Real.rpow (Real.log x) a)) atTop atTop :=
    Real.tendsto_exp_atTop.comp hpow
  have hinv : Tendsto (fun x : ℝ => (Real.exp (Real.rpow (Real.log x) a))⁻¹)
      atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hexp
  let η₀ := min (ε / 2) (Real.log 2 / 4)
  have hη₀ : 0 < η₀ := lt_min (by positivity) (by positivity)
  have hsmall : ∀ᶠ x : ℝ in atTop,
      (Real.exp (Real.rpow (Real.log x) a))⁻¹ < η₀ :=
    hinv.eventually (Iio_mem_nhds hη₀)
  have hlarge : ∀ᶠ x : ℝ in atTop, Real.log y₀ ≤ Real.rpow (Real.log x) a :=
    hpow.eventually (eventually_ge_atTop (Real.log y₀))
  have hfinal : ∀ᶠ x : ℝ in atTop,
      |bandMass x a - Real.log 2| ≤ ε ∧ 0 < bandMass x a := by
    filter_upwards [eventually_ge_atTop (2 : ℝ), hsmall, hlarge]
      with x hx₂ hxsmall hxlarge
    let v := Real.rpow (Real.log x) a
    let A := Real.exp v
    let B := Real.exp (2 * v)
    have hv : 0 < v := Real.rpow_pos_of_pos (Real.log_pos (by linarith)) a
    have hA : y₀ ≤ A := by
      dsimp [A, v]
      calc
        y₀ = Real.exp (Real.log y₀) := (Real.exp_log (by linarith)).symm
        _ ≤ Real.exp (Real.rpow (Real.log x) a) := Real.exp_le_exp.mpr hxlarge
    have hB : y₀ ≤ B := by
      have hAB : A ≤ B := by
        change Real.exp v ≤ Real.exp (2 * v)
        exact Real.exp_le_exp.mpr (by nlinarith [hv])
      exact hA.trans hAB
    have hApos : 0 < A := Real.exp_pos _
    have hBpos : 0 < B := Real.exp_pos _
    have hlogA : Real.log A = v := by simp [A, Real.log_exp]
    have hlogB : Real.log B = 2 * v := by simp [B, Real.log_exp]
    have hlogdiff : Real.log (Real.log B) - Real.log (Real.log A) = Real.log 2 := by
      rw [hlogA, hlogB, Real.log_mul (by norm_num) (ne_of_gt hv)]
      ring
    have hA_m := hmertens A hA
    have hB_m := hmertens B hB
    have hA_m' :
        |reciprocalPrimeSum A - Real.log (Real.log A) -
          ArtinPrimitiveRoots.Ext.TypeIIInputs.meisselMertensConstant| ≤ η := by
      simpa [reciprocalPrimeSum] using hA_m
    have hB_m' :
        |reciprocalPrimeSum B - Real.log (Real.log B) -
          ArtinPrimitiveRoots.Ext.TypeIIInputs.meisselMertensConstant| ≤ η := by
      simpa [reciprocalPrimeSum] using hB_m
    have hdiff :
        |(reciprocalPrimeSum B - reciprocalPrimeSum A) - Real.log 2| ≤ 2 * η := by
      have hb := abs_le.mp hB_m'
      have ha := abs_le.mp hA_m'
      rw [abs_le]
      constructor <;> linarith [hlogdiff]
    have hEndPos : 0 ≤ reciprocalMassOn (endpointPrimes A) := by
      unfold reciprocalMassOn
      apply Finset.sum_nonneg
      intro p hp
      exact one_div_nonneg.mpr (Nat.cast_nonneg p)
    have hId : bandMass x a =
        reciprocalPrimeSum B - reciprocalPrimeSum A + reciprocalMassOn (endpointPrimes A) := by
      simpa [A, B, v] using bandMass_cut_identity (x := x) (a := a) hx₂ ha₀
    have hInvA : A⁻¹ ≤ η₀ := by
      have hsmall' : A⁻¹ < η₀ := by simpa [A, v] using hxsmall
      exact hsmall'.le
    have hbandErr :
        |bandMass x a - (reciprocalPrimeSum B - reciprocalPrimeSum A)| ≤ η₀ := by
      have heq : bandMass x a - (reciprocalPrimeSum B - reciprocalPrimeSum A) =
          reciprocalMassOn (endpointPrimes A) := by linarith [hId]
      rw [heq, abs_of_nonneg hEndPos]
      exact (bandMass_endpoint_le hApos).trans (by simpa [one_div] using hInvA)
    have htotal : |bandMass x a - Real.log 2| ≤ η₀ + 2 * η := by
      calc
        |bandMass x a - Real.log 2| =
            |(bandMass x a - (reciprocalPrimeSum B - reciprocalPrimeSum A)) +
              ((reciprocalPrimeSum B - reciprocalPrimeSum A) - Real.log 2)| := by
                congr 1 <;> ring
        _ ≤ _ := abs_add_le _ _
        _ ≤ η₀ + 2 * η := add_le_add hbandErr hdiff
    have htotalε : η₀ + 2 * η ≤ ε := by
      dsimp [η₀]
      have hη₀ε : η₀ ≤ ε / 2 := min_le_left _ _
      linarith
    have htotalLog : η₀ + 2 * η ≤ Real.log 2 / 2 := by
      dsimp [η₀]
      have hη₀log : η₀ ≤ Real.log 2 / 4 := min_le_right _ _
      linarith
    have hmasspos : 0 < bandMass x a := by
      have hlow : Real.log 2 / 2 ≤ bandMass x a := by
        have h := abs_le.mp (htotal.trans htotalLog)
        linarith
      linarith
    exact ⟨htotal.trans htotalε, hmasspos⟩
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp hfinal
  refine ⟨max x₀ 2, le_max_right _ _, ?_⟩
  intro x hx
  exact hx₀ x (le_trans (le_max_left _ _) hx)

/-- A scale-varying family of first-variable coefficients, as in the hypothesis
`eq:type-ii-long-coefficient-interface`. Correction 2 from review lane `rev-b` records that the
first-variable set is an interval. The family-specific asymptotic threshold is the correction from
refutation lane `sol-gate-b`. -/
structure CoefficientFamily (δ C c₁ c₂ : ℝ) where
  /-- First scale at which the family is required to satisfy its asymptotic bounds. -/
  xMin : ℝ := 2
  xMin_ge_two : 2 ≤ xMin := by norm_num
  Hm : ℝ → ℝ
  Hn : ℝ → ℝ
  interval : ℝ → Set ℕ
  alpha : ℝ → ℕ → ℂ
  interval_property : ∀ x, IsNatInterval (interval x)
  scales : ∀ x, xMin ≤ x → Real.rpow x δ ≤ Hm x ∧ Real.rpow x δ ≤ Hn x ∧
    c₁ * x ≤ Hm x * Hn x ∧ Hm x * Hn x ≤ c₂ * x
  interval_bounds : ∀ x, xMin ≤ x → ∀ m ∈ interval x, Hm x ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * Hm x
  rough_support : ∀ x, xMin ≤ x → ∀ m, alpha x m ≠ 0 →
    m ∈ interval x ∧ roughAbove m (roughCutoff x)
  coefficient_bound : ∀ x, xMin ≤ x → ∀ m ∈ interval x,
    ‖alpha x m‖ ≤ Real.rpow (Real.log x) C

/-- Finite interpretation of the interval in a coefficient family. -/
noncomputable def familyTerms {δ C c₁ c₂ : ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (x : ℝ) : Finset ℕ :=
  (dyadicIntegers (family.Hm x)).filter (fun m => m ∈ family.interval x)

/-- The long Dirichlet-polynomial hypothesis on the first-variable coefficients. Its interval
domain is the one in correction 2 from review lane `rev-b`; its threshold is the asymptotic
correction from refutation lane `sol-gate-b`. -/
def HasLongCoefficientCancellation {δ C c₁ c₂ : ℝ}
    (family : CoefficientFamily δ C c₁ c₂) : Prop :=
  ∀ A₀ B A : ℝ, 0 < A₀ → 0 < B → 0 < A →
    ∃ C' x₀ : ℝ, 0 < C' ∧ 2 ≤ x₀ ∧ family.xMin ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.rpow (Real.log x) A₀ →
          ∀ χ : DirichletCharacter ℂ k, ∀ t : ℝ,
            |t| ≤ 2 * (family.Hm x * family.Hn x) * Real.rpow (Real.log x) B →
              ‖∑ m ∈ familyTerms family x,
                family.alpha x m * χ (m : ZMod k) *
                  Complex.exp (Complex.I * t * Real.log (m : ℝ))‖ /
                  family.Hm x ≤ C' * Real.rpow (Real.log x) (-A)

/-- The Type II bilinear form with marked weight.  All sums are over the explicitly bounded
dyadic ranges. -/
noncomputable def markedBilinearSum (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (q_d : ℝ)
    (F : ℕ → ℂ) (Hm Hn : ℝ) (I : Set ℕ) (alpha beta : ℕ → ℂ) : ℂ :=
  ∑ m ∈ (dyadicIntegers Hm).filter (fun m => m ∈ I),
    ∑ n ∈ dyadicIntegers Hn,
      alpha m * beta n * F (m * n - 1) *
        (markedWeight x K a q_d (m * n - 1) : ℂ)


end ArtinPrimitiveRoots.TypeII
