import ArtinPrimitiveRoots.TypeII.Marked
import ArtinPrimitiveRoots.TypeII.PD.Defs
import ArtinPrimitiveRoots.TypeII.PP.Results
import ArtinPrimitiveRoots.TypeII.Proofs.r2.CharacterConductor

/-! The rough-factor Type II estimate and its coefficient (`08-type-ii.tex:321-536`). -/

namespace ArtinPrimitiveRoots.TypeII.Rough

open Classical
open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII.PP

/-- `def:rough-density` — 08-type-ii.tex:253-270. Alias of the shared Buchstab rough density; the
body is exactly the existing `ArtinPrimitiveRoots.Sieve.roughDensity` definition. -/
noncomputable abbrev roughDensity := ArtinPrimitiveRoots.Sieve.roughDensity

/-- The coefficient in equation `eq:rough-type-ii-coefficient`. -/
noncomputable def roughCoefficient (x γ v : ℝ) (m : ℕ) : ℂ :=
  Complex.exp (Complex.I * v * Real.log (m : ℝ)) *
    (((if roughAbove m (Real.rpow x γ) then (1 : ℝ) else 0) -
        roughDensity γ (Real.log (m : ℝ) / Real.log x) /
          (Real.log x * roughSieveProduct (roughCutoff x)) *
            (if roughAbove m (roughCutoff x) then (1 : ℝ) else 0)) : ℂ)

/-- The prime-indicator coefficient `1_{P⁻(m)>x^γ}`. -/
noncomputable def roughIndicator (x γ : ℝ) (m : ℕ) : ℝ :=
  if roughAbove m (Real.rpow x γ) then 1 else 0

/-- The proxy coefficient `D_γ(log m/log x)/(log x V(W))` on `W`-rough integers. -/
noncomputable def roughProxy (x γ : ℝ) (m : ℕ) : ℝ :=
  roughDensity γ (Real.log (m : ℝ) / Real.log x) /
    (Real.log x * roughSieveProduct (roughCutoff x)) *
      if roughAbove m (roughCutoff x) then 1 else 0

/-- The finite ordered-prime convolution `T_γ(m)` from `eq:rough-convolution-square-error`. -/
noncomputable def roughConvolutionTerm (x γ M : ℝ) (j m : ℕ) : ℝ :=
  (1 / (j.factorial : ℝ)) *
    ∑ t ∈ boundedTuples j (⌊2 * M⌋₊ + 1),
      if (∀ i, (t i).Prime ∧ Real.rpow x γ < (t i : ℝ)) ∧
          (∏ i : Fin j, t i) = m then 1 else 0

noncomputable def roughConvolution (x γ wMax M : ℝ) (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 (⌊wMax / γ⌋₊), roughConvolutionTerm x γ M j m

/-- Prime set in a closed real interval, explicitly truncated at the upper endpoint. -/
noncomputable def primesInInterval (lo hi : ℝ) : Finset ℕ :=
  (Finset.range (⌊hi⌋₊ + 1)).filter fun p => p.Prime ∧ lo ≤ (p : ℝ) ∧ (p : ℝ) ≤ hi

/-- Product-measure integral over ordered `j`-tuples of primes in logarithmic coordinates. -/
noncomputable def roughTupleIntegral (x γ lo hi : ℝ) (j : ℕ) : ℝ :=
  (1 / (j.factorial : ℝ)) *
    ∫ t : Fin j → ℝ,
      if (∀ i, Real.rpow x γ < t i) ∧
          lo ≤ ∏ i : Fin j, t i ∧ (∏ i : Fin j, t i) ≤ hi then
        ∏ i : Fin j, 1 / Real.log (t i) else 0

/-- `prop:rough-type-ii` — `08-type-ii.tex:321-536`. Fix the parameters in the
paper. Uniformly over admissible dyads, intervals, real twists, rough second-variable coefficients,
and marked-invariant multipliers, the coefficient `roughCoefficient` has the Type II saving once
`K` is sufficiently large. -/
theorem rough_type_ii
    (γ wMin wMax δ C Dstar q_d c₁ c₂ : ℝ)
    (hγ : 0 < γ) (hγwMin : γ < wMin) (hwMinMax : wMin < wMax)
    (hwMax : wMax < 1)
    (hδ : 0 < δ) (hC : 0 < C) (hD : 0 < Dstar)
    (hqd₀ : 0 < q_d) (hqd₁ : q_d < 1) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K →
      ∀ a : Fin K → ℝ, ValidBands K a →
        ∃ C' x₀ : ℝ, 0 < C' ∧ 2 ≤ x₀ ∧
          ∀ x : ℝ, x₀ ≤ x →
            ∀ Hm Hn : ℝ,
              Real.rpow x δ ≤ Hm → Real.rpow x δ ≤ Hn →
              c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x →
              Real.log Hm / Real.log x ∈ Set.Icc wMin wMax →
              Real.log (2 * Hm) / Real.log x ∈ Set.Icc wMin wMax →
              ∀ I : Set ℕ, I ⊆ {m : ℕ | Hm ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * Hm} →
                ∀ v : ℝ, |v| ≤ Real.rpow (Real.log x) C →
                  ∀ beta : ℕ → ℂ,
                    (∀ n, beta n ≠ 0 → n ∈ dyadicIntegers Hn ∧
                      roughAbove n (roughCutoff x)) →
                    (∀ n ∈ dyadicIntegers Hn,
                      ‖beta n‖ ≤ Real.rpow (Real.log x) C) →
                    ∀ F : ℕ → ℂ, IsMarkedInvariant x K a F →
                      ‖∑ m ∈ (dyadicIntegers Hm).filter (fun m => m ∈ I),
                        ∑ n ∈ dyadicIntegers Hn,
                          roughCoefficient x γ v m * beta n * F (m * n - 1) *
                            (markedWeight x K a q_d (m * n - 1) : ℂ)‖ ≤
                        C' * (Hm * Hn) * Real.rpow (Real.log x) (-Dstar) := by
  sorry

theorem rough_factor_count_le (x γ wMax : ℝ) (m : ℕ)
    (hx : 1 < x) (hγ : 0 < γ) (hm : 2 ≤ m)
    (hrough : roughAbove m (Real.rpow x γ))
    (hmx : (m : ℝ) ≤ Real.rpow x wMax) :
    m.primeFactorsList.length ≤ ⌊wMax / γ⌋₊ := by
  classical
  let l := m.primeFactorsList
  have hlne : l ≠ [] := by
    intro h
    have hm01 : m = 0 ∨ m = 1 := by
      apply (Nat.primeFactorsList_eq_nil m).mp
      simpa [l] using h
    omega
  have hlpos : 0 < l.length := List.length_pos_of_ne_nil hlne
  have hleft : (∏ i : Fin l.length, Real.rpow x γ) =
      (Real.rpow x γ) ^ l.length := by simp
  have hprodReal : (∏ i : Fin l.length, (l.get i : ℝ)) = (m : ℝ) := by
    calc
      (∏ i : Fin l.length, (l.get i : ℝ)) =
          ((∏ i : Fin l.length, l.get i : ℕ) : ℝ) := by simp
      _ = (l.prod : ℝ) := by
        norm_cast
        rw [← List.prod_ofFn, List.ofFn_get]
      _ = (m : ℝ) := by
        have hnat : l.prod = m := by
          dsimp [l]
          exact Nat.prod_primeFactorsList (by omega)
        exact_mod_cast hnat
  have hprodLower :
      (∏ i : Fin l.length, Real.rpow x γ) <
        ∏ i : Fin l.length, (l.get i : ℝ) := by
    apply Finset.prod_lt_prod_of_nonempty₀
    · intro i hi
      exact Real.rpow_pos_of_pos (by linarith) γ
    · intro i hi
      have hmem : l.get i ∈ l := List.get_mem l i
      have hfactor : l.get i ∈ m.primeFactorsList := by exact hmem
      have hpair : (l.get i).Prime ∧ l.get i ∣ m :=
        (Nat.mem_primeFactorsList (by omega : m ≠ 0)).mp hfactor
      exact hrough (l.get i) hpair.1 hpair.2
    · exact ⟨⟨0, hlpos⟩, Finset.mem_univ _⟩
  have hpowLt : (Real.rpow x γ) ^ l.length < Real.rpow x wMax := by
    calc
      _ = ∏ i : Fin l.length, Real.rpow x γ := hleft.symm
      _ < (m : ℝ) := hprodLower.trans_eq hprodReal
      _ ≤ Real.rpow x wMax := hmx
  have hpowEq : Real.rpow x (γ * (l.length : ℝ)) =
      (Real.rpow x γ) ^ l.length := by
    calc
      Real.rpow x (γ * (l.length : ℝ)) =
          (Real.rpow x γ) ^ (l.length : ℝ) := Real.rpow_mul (by positivity) γ _
      _ = (Real.rpow x γ) ^ l.length := Real.rpow_natCast _ _
  have hExp : Real.rpow x (γ * (l.length : ℝ)) < Real.rpow x wMax := by
    rw [hpowEq]
    exact hpowLt
  have hγlen : γ * (l.length : ℝ) < wMax :=
    (Real.rpow_lt_rpow_left_iff hx).mp hExp
  have hlenReal : (l.length : ℝ) < wMax / γ :=
    (lt_div_iff₀ hγ).2 (by nlinarith)
  have hlenNat : l.length ≤ ⌊wMax / γ⌋₊ := Nat.le_floor hlenReal.le
  simpa [l] using hlenNat

theorem roughConvolutionTerm_eq_tupleFiber (x γ M : ℝ) (j m : ℕ)
    (hrough : roughAbove m (Real.rpow x γ)) :
    roughConvolutionTerm x γ M j m =
      (1 / (j.factorial : ℝ)) *
        (RoughProofs.primeTupleFiber j (⌊2 * M⌋₊ + 1) m).card := by
  classical
  let B := ⌊2 * M⌋₊ + 1
  let P : (Fin j → ℕ) → Prop := fun t =>
    ((∀ i, (t i).Prime ∧ Real.rpow x γ < (t i : ℝ)) ∧
      (∏ i : Fin j, t i) = m)
  let Q : (Fin j → ℕ) → Prop := fun t =>
    (∀ i, (t i).Prime) ∧ (∏ i : Fin j, t i) = m
  have hPQ (t : Fin j → ℕ) : P t ↔ Q t := by
    constructor
    · rintro ⟨hp, hprod⟩
      exact ⟨fun i => (hp i).1, hprod⟩
    · rintro ⟨hp, hprod⟩
      refine ⟨?_, hprod⟩
      intro i
      refine ⟨hp i, ?_⟩
      have hdiv : t i ∣ m := by
        calc
          t i ∣ ∏ k : Fin j, t k :=
            Finset.dvd_prod_of_mem (fun k => t k) (Finset.mem_univ i)
          _ = m := hprod
      exact hrough (t i) (hp i) hdiv
  have hfilter : (boundedTuples j B).filter P =
      RoughProofs.primeTupleFiber j B m := by
    ext t
    simp only [Finset.mem_filter, RoughProofs.primeTupleFiber]
    constructor
    · rintro ⟨hB, hP⟩
      exact ⟨hB, (hPQ t).mp hP⟩
    · rintro ⟨hB, hQ⟩
      exact ⟨hB, (hPQ t).mpr hQ⟩
  unfold roughConvolutionTerm
  change (1 / (j.factorial : ℝ)) *
      (∑ t ∈ boundedTuples j B, if P t then (1 : ℝ) else 0) = _
  calc
    _ = (1 / (j.factorial : ℝ)) *
        ∑ t ∈ (boundedTuples j B).filter P, (1 : ℝ) := by
          congr 1
          exact (Finset.sum_filter (s := boundedTuples j B) P
            (fun _ => (1 : ℝ))).symm
    _ = _ := by rw [hfilter]; simp [B]


theorem roughConvolutionTerm_nonneg (x γ M : ℝ) (j m : ℕ)
    (hrough : roughAbove m (Real.rpow x γ)) :
    0 ≤ roughConvolutionTerm x γ M j m := by
  rw [roughConvolutionTerm_eq_tupleFiber x γ M j m hrough]
  positivity

theorem roughConvolutionTerm_le_one (x γ M : ℝ) (j m : ℕ)
    (hrough : roughAbove m (Real.rpow x γ)) :
    roughConvolutionTerm x γ M j m ≤ 1 := by
  rw [roughConvolutionTerm_eq_tupleFiber x γ M j m hrough]
  let F := RoughProofs.primeTupleFiber j (⌊2 * M⌋₊ + 1) m
  have hcard := RoughProofs.primeTupleFiber_card_le_factorial j
    (⌊2 * M⌋₊ + 1) m
  have hcardReal : (F.card : ℝ) ≤ (j.factorial : ℝ) := by
    exact_mod_cast hcard
  have hfact : 0 < (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
  calc
    (1 / (j.factorial : ℝ)) * (F.card : ℝ) =
        (F.card : ℝ) / (j.factorial : ℝ) := by ring
    _ ≤ 1 := (div_le_one hfact).2 hcardReal

theorem roughConvolutionTerm_eq_one_of_squarefree (x γ M : ℝ) (j m : ℕ)
    (hrough : roughAbove m (Real.rpow x γ)) (hm2 : 2 ≤ m)
    (hmSq : Squarefree m) (hj : j = m.primeFactorsList.length)
    (hB : ∀ p ∈ m.primeFactorsList, p ≤ ⌊2 * M⌋₊ + 1) :
    roughConvolutionTerm x γ M j m = 1 := by
  rw [roughConvolutionTerm_eq_tupleFiber x γ M j m hrough]
  rw [RoughProofs.primeTupleFiber_card_eq_factorial_of_squarefree j
    (⌊2 * M⌋₊ + 1) m (by omega) hmSq hj hB]
  field_simp

theorem roughConvolution_eq_one_of_rough_squarefree
    (x γ wMax M : ℝ) (m : ℕ)
    (hx : 1 < x) (hγ : 0 < γ) (hm2 : 2 ≤ m)
    (hrough : roughAbove m (Real.rpow x γ))
    (hmUpper : (m : ℝ) ≤ 2 * M) (hScale : 2 * M ≤ Real.rpow x wMax)
    (hmSq : Squarefree m) :
    roughConvolution x γ wMax M m = 1 := by
  let j := m.primeFactorsList.length
  have hjLower : 1 ≤ j := by
    have hlist : m.primeFactorsList ≠ [] := by
      intro h
      have hm01 : m = 0 ∨ m = 1 := by
        apply (Nat.primeFactorsList_eq_nil m).mp
        exact h
      omega
    exact List.length_pos_of_ne_nil hlist
  have hjUpper : j ≤ ⌊wMax / γ⌋₊ :=
    rough_factor_count_le x γ wMax m hx hγ hm2 hrough (hmUpper.trans hScale)
  have hjMem : j ∈ Finset.Icc 1 (⌊wMax / γ⌋₊) :=
    Finset.mem_Icc.mpr ⟨hjLower, hjUpper⟩
  have hB : ∀ p ∈ m.primeFactorsList, p ≤ ⌊2 * M⌋₊ + 1 := by
    intro p hp
    have hpDvd : p ∣ m := Nat.dvd_of_mem_primeFactorsList hp
    have hpLe : p ≤ m := Nat.le_of_dvd (by omega) hpDvd
    have hmFloor : m ≤ ⌊2 * M⌋₊ := Nat.le_floor hmUpper
    exact hpLe.trans (hmFloor.trans (Nat.le_succ _))
  have hterm : roughConvolutionTerm x γ M j m = 1 :=
    roughConvolutionTerm_eq_one_of_squarefree x γ M j m hrough hm2 hmSq
      (by rfl) hB
  have hzero : ∀ q ∈ Finset.Icc 1 (⌊wMax / γ⌋₊), q ≠ j →
      roughConvolutionTerm x γ M q m = 0 := by
    intro q hq hqj
    rw [roughConvolutionTerm_eq_tupleFiber x γ M q m hrough]
    rw [RoughProofs.primeTupleFiber_eq_empty_of_factor_length_ne
      (by simpa [j] using hqj)]
    simp
  calc
    roughConvolution x γ wMax M m =
        ∑ q ∈ Finset.Icc 1 (⌊wMax / γ⌋₊), roughConvolutionTerm x γ M q m := rfl
    _ = roughConvolutionTerm x γ M j m :=
      Finset.sum_eq_single_of_mem j hjMem hzero
    _ = 1 := hterm


theorem roughConvolutionTerm_eq_zero_of_not_rough (x γ M : ℝ) (j m : ℕ)
    (hnot : ¬ roughAbove m (Real.rpow x γ)) :
    roughConvolutionTerm x γ M j m = 0 := by
  classical
  unfold roughConvolutionTerm
  have hsum :
      (∑ t ∈ boundedTuples j (⌊2 * M⌋₊ + 1),
        if ((∀ i, (t i).Prime ∧ Real.rpow x γ < (t i : ℝ)) ∧
            (∏ i : Fin j, t i) = m) then (1 : ℝ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    by_cases hpred :
        (∀ i, (t i).Prime ∧ Real.rpow x γ < (t i : ℝ)) ∧
          (∏ i : Fin j, t i) = m
    · rcases hpred with ⟨hcoords, hprod⟩
      have hwitness : ∃ p, p.Prime ∧ p ∣ m ∧ ¬ Real.rpow x γ < (p : ℝ) := by
        by_contra h
        apply hnot
        intro p hp hpdiv
        by_contra hpnot
        exact h ⟨p, hp, hpdiv, hpnot⟩
      rcases hwitness with ⟨p, hp, hpdiv, hpnot⟩
      have hpDivProd : p ∣ ∏ i : Fin j, t i := by simpa [hprod] using hpdiv
      rcases (Prime.dvd_finsetProd_iff (Nat.prime_iff.mp hp) (fun i => t i)).mp hpDivProd with
        ⟨i, _, hpi⟩
      have heq : p = t i :=
        (Nat.prime_dvd_prime_iff_eq hp (hcoords i).1).mp hpi
      exact False.elim (hpnot (by simpa [heq] using (hcoords i).2))
    · simp only [if_neg hpred]
  rw [hsum]
  simp

theorem roughConvolution_bounds_of_rough
    (x γ wMax M : ℝ) (m : ℕ)
    (hx : 1 < x) (hγ : 0 < γ) (hm2 : 2 ≤ m)
    (hrough : roughAbove m (Real.rpow x γ))
    (hmUpper : (m : ℝ) ≤ 2 * M) (hScale : 2 * M ≤ Real.rpow x wMax) :
    0 ≤ roughConvolution x γ wMax M m ∧ roughConvolution x γ wMax M m ≤ 1 := by
  let j := m.primeFactorsList.length
  have hjLower : 1 ≤ j := by
    have hlist : m.primeFactorsList ≠ [] := by
      intro h
      have hm01 : m = 0 ∨ m = 1 := by
        apply (Nat.primeFactorsList_eq_nil m).mp h
      omega
    exact List.length_pos_of_ne_nil hlist
  have hjUpper : j ≤ ⌊wMax / γ⌋₊ :=
    rough_factor_count_le x γ wMax m hx hγ hm2 hrough (hmUpper.trans hScale)
  have hjMem : j ∈ Finset.Icc 1 (⌊wMax / γ⌋₊) :=
    Finset.mem_Icc.mpr ⟨hjLower, hjUpper⟩
  have hzero : ∀ q ∈ Finset.Icc 1 (⌊wMax / γ⌋₊), q ≠ j →
      roughConvolutionTerm x γ M q m = 0 := by
    intro q hq hqj
    rw [roughConvolutionTerm_eq_tupleFiber x γ M q m hrough]
    rw [RoughProofs.primeTupleFiber_eq_empty_of_factor_length_ne
      (by simpa [j] using hqj)]
    simp
  have hsum : roughConvolution x γ wMax M m = roughConvolutionTerm x γ M j m := by
    unfold roughConvolution
    exact Finset.sum_eq_single_of_mem j hjMem hzero
  constructor
  · rw [hsum]
    exact roughConvolutionTerm_nonneg x γ M j m hrough
  · rw [hsum]
    exact roughConvolutionTerm_le_one x γ M j m hrough

theorem dyadic_multiples_card_le_floor (M : ℝ) (hM : 1 ≤ M) (p : ℕ)
    (hp : p.Prime) :
    ((dyadicIntegers M).filter (fun (m : ℕ) => p ^ 2 ∣ m)).card ≤
      ⌊2 * M / (p : ℝ) ^ 2⌋₊ := by
  classical
  let K := ⌊2 * M / (p : ℝ) ^ 2⌋₊
  let U := Finset.Ioc 0 K
  let f : ℕ → ℕ := fun n => p ^ 2 * n
  have hsubset :
      (dyadicIntegers M).filter (fun (m : ℕ) => p ^ 2 ∣ m) ⊆ U.image f := by
    intro m hm
    rcases Finset.mem_filter.mp hm with ⟨hmD, hdiv⟩
    change m ∈ (Finset.range (⌊2 * M⌋₊ + 1) : Finset ℕ).filter
      (fun (n : ℕ) => M ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * M) at hmD
    rcases Finset.mem_filter.mp hmD with ⟨_, ⟨hmLower, hmUpper⟩⟩
    rcases hdiv with ⟨n, hn⟩
    have hnpos : 0 < n := by
      by_contra hn0
      have : n = 0 := Nat.eq_zero_of_not_pos hn0
      simp [this] at hn
      have hmpos : 0 < m := by
        have hmcast : (1 : ℝ) ≤ (m : ℝ) := le_trans hM hmLower
        exact_mod_cast hmcast
      omega
    have hnBound : n ≤ K := by
      apply Nat.le_floor
      have hpPos : 0 < (p : ℝ) := by exact_mod_cast hp.pos
      have hden : 0 < (p : ℝ) ^ 2 := by positivity
      have hcastEq : (m : ℝ) = (p : ℝ) ^ 2 * (n : ℝ) := by
        rw [hn]
        push_cast
        ring
      apply (le_div_iff₀ hden).2
      nlinarith [hcastEq]
    refine Finset.mem_image.mpr ⟨n, ?_, ?_⟩
    · exact Finset.mem_Ioc.mpr ⟨hnpos, hnBound⟩
    · dsimp [f]
      exact hn.symm
  calc
    ((dyadicIntegers M).filter (fun m => p ^ 2 ∣ m)).card ≤ (U.image f).card :=
      Finset.card_le_card hsubset
    _ ≤ U.card := Finset.card_image_le
    _ = K := by simp [U]

theorem roughBadDyadic_card_le_square_count (x γ M : ℝ) (hM : 1 ≤ M) :
    let Y := Real.rpow x γ
    let Bad := (dyadicIntegers M).filter
      (fun m => roughAbove m Y ∧ ¬ Squarefree m)
    Bad.card ≤
      (∑ p ∈ (primesUpTo (Real.sqrt (2 * M))).filter (fun (p : ℕ) => Y < (p : ℝ)),
        ⌊2 * M / (p : ℝ) ^ 2⌋₊) := by
  classical
  let Y := Real.rpow x γ
  let P : Finset ℕ := (primesUpTo (Real.sqrt (2 * M))).filter
    (fun (p : ℕ) => Y < (p : ℝ))
  let Bad : Finset ℕ := (dyadicIntegers M).filter
    (fun (m : ℕ) => roughAbove m Y ∧ ¬ Squarefree m)
  change Bad.card ≤ ∑ p ∈ P, ⌊2 * M / (p : ℝ) ^ 2⌋₊
  have hsumBad : Bad.card ≤
      ∑ m ∈ Bad, ∑ p ∈ P, if p ^ 2 ∣ m then 1 else 0 := by
    calc
      Bad.card = ∑ m ∈ Bad, 1 := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro m hm
        have hmBad := (Finset.mem_filter.mp hm).2
        rcases hmBad with ⟨hmrough, hmnotSq⟩
        obtain ⟨p, hp, hpdiv⟩ : ∃ p, p.Prime ∧ p * p ∣ m := by
          by_contra h
          apply hmnotSq
          apply Nat.squarefree_iff_prime_squarefree.mpr
          intro p hp hdiv
          exact h ⟨p, hp, hdiv⟩
        have hmDy := (Finset.mem_filter.mp hm).1
        change m ∈ (Finset.range (⌊2 * M⌋₊ + 1) : Finset ℕ).filter
          (fun (n : ℕ) => M ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * M) at hmDy
        rcases Finset.mem_filter.mp hmDy with ⟨_, ⟨hmLower, hmUpper⟩⟩
        have hmpos : 0 < m := by
          have hmcast : (1 : ℝ) ≤ (m : ℝ) := le_trans hM hmLower
          exact_mod_cast hmcast
        have hpSqNat : p * p ≤ m := Nat.le_of_dvd hmpos hpdiv
        have hpSqReal : (p : ℝ) ^ 2 ≤ 2 * M := by
          have hcast : ((p * p : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hpSqNat
          rw [Nat.cast_mul] at hcast
          nlinarith
        have hpSqrt : (p : ℝ) ≤ Real.sqrt (2 * M) := Real.le_sqrt_of_sq_le hpSqReal
        have hpFloor : p ≤ ⌊Real.sqrt (2 * M)⌋₊ := Nat.le_floor hpSqrt
        have hpPrimeSet : p ∈ primesUpTo (Real.sqrt (2 * M)) := by
          unfold primesUpTo
          refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hp⟩
          omega
        have hpDvd : p ∣ m := dvd_trans (dvd_mul_right p p) hpdiv
        have hpY : Y < (p : ℝ) := hmrough p hp hpDvd
        have hpP : p ∈ P := Finset.mem_filter.mpr ⟨hpPrimeSet, hpY⟩
        have hcount : 1 ≤ (P.filter (fun q => q ^ 2 ∣ m)).card := by
          apply Nat.succ_le_of_lt
          exact Finset.card_pos.mpr ⟨p, Finset.mem_filter.mpr
            ⟨hpP, by simpa [pow_two] using hpdiv⟩⟩
        have hcountsum :
            (∑ q ∈ P, if q ^ 2 ∣ m then 1 else 0) =
              (P.filter (fun q => q ^ 2 ∣ m)).card := by
          symm
          exact Finset.card_filter _ _
        rw [hcountsum]
        exact hcount
  calc
    Bad.card ≤ ∑ m ∈ Bad, ∑ p ∈ P, if p ^ 2 ∣ m then 1 else 0 := hsumBad
    _ = ∑ p ∈ P, ∑ m ∈ Bad, if p ^ 2 ∣ m then 1 else 0 := Finset.sum_comm
    _ = ∑ p ∈ P, (Bad.filter (fun m => p ^ 2 ∣ m)).card := by
      apply Finset.sum_congr rfl
      intro p hp
      symm
      exact Finset.card_filter (fun m => p ^ 2 ∣ m) Bad
    _ ≤ ∑ p ∈ P, ⌊2 * M / (p : ℝ) ^ 2⌋₊ := by
      apply Finset.sum_le_sum
      intro p hp
      have hpPrime : p.Prime := by
        rcases Finset.mem_filter.mp hp with ⟨hp₁, _⟩
        exact (Finset.mem_filter.mp hp₁).2
      have hsub : Bad.filter (fun (m : ℕ) => p ^ 2 ∣ m) ⊆
          (dyadicIntegers M).filter (fun (m : ℕ) => p ^ 2 ∣ m) := by
        intro m hm
        rcases Finset.mem_filter.mp hm with ⟨hmB, hmdiv⟩
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hmB).1, hmdiv⟩
      exact (Finset.card_le_card hsub).trans
        (dyadic_multiples_card_le_floor M hM p hpPrime)

theorem rough_square_error_pointwise (x γ wMax δ M : ℝ) (m : ℕ)
    (hx : 1 < x) (hγ : 0 < γ) (hδ : 0 < δ) (hM : 1 ≤ M)
    (hMδ : Real.rpow x δ ≤ M) (hScale : 2 * M ≤ Real.rpow x wMax)
    (hmDy : m ∈ dyadicIntegers M) :
    |roughIndicator x γ m - roughConvolution x γ wMax M m| ≤
      if roughAbove m (Real.rpow x γ) ∧ ¬ Squarefree m then 1 else 0 := by
  have hδpow : 1 < Real.rpow x δ := by
    rw [← Real.rpow_zero x]
    exact Real.rpow_lt_rpow_of_exponent_lt hx hδ
  have hMgt : 1 < M := lt_of_lt_of_le hδpow hMδ
  change m ∈ (Finset.range (⌊2 * M⌋₊ + 1) : Finset ℕ).filter
    (fun (n : ℕ) => M ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * M) at hmDy
  rcases Finset.mem_filter.mp hmDy with ⟨_, ⟨hmLower, hmUpper⟩⟩
  have hm2 : 2 ≤ m := by
    have hmReal : 1 < (m : ℝ) := lt_of_lt_of_le hMgt hmLower
    have hmNat : 1 < m := by exact_mod_cast hmReal
    omega
  by_cases hrough : roughAbove m (Real.rpow x γ)
  · by_cases hSq : Squarefree m
    · have hconv := roughConvolution_eq_one_of_rough_squarefree x γ wMax M m
        hx hγ hm2 hrough hmUpper hScale hSq
      have hind : roughIndicator x γ m = 1 := by
        unfold roughIndicator
        rw [if_pos hrough]
      rw [hind, hconv]
      have hrough' : roughAbove m (x ^ γ) := hrough
      simp [hrough', hSq]
    · have hconv := roughConvolution_bounds_of_rough x γ wMax M m
        hx hγ hm2 hrough hmUpper hScale
      have hdiff : |1 - roughConvolution x γ wMax M m| ≤ 1 := by
        rw [abs_of_nonneg (sub_nonneg.mpr hconv.2)]
        exact sub_le_self 1 hconv.1
      have hind : roughIndicator x γ m = 1 := by
        unfold roughIndicator
        rw [if_pos hrough]
      rw [hind]
      have hrough' : roughAbove m (x ^ γ) := hrough
      simpa [hrough', hSq] using hdiff
  · have hconv : roughConvolution x γ wMax M m = 0 := by
      unfold roughConvolution
      apply Finset.sum_eq_zero
      intro j hj
      exact roughConvolutionTerm_eq_zero_of_not_rough x γ M j m hrough
    have hind : roughIndicator x γ m = 0 := by
      unfold roughIndicator
      rw [if_neg hrough]
    rw [hind, hconv]
    have hrough' : ¬ roughAbove m (x ^ γ) := hrough
    simp [hrough']

/-- `t2:square-error` — 08-type-ii.tex:351-371. The dyad lies below `x^{wMax}` (`2M ≤ x^{wMax}`), which bounds the
number of prime factors by `Jγ`; added 2026-10-07 after lane `r2` refuted the form without it. -/
theorem square_error (γ wMax δ : ℝ) (hγ : 0 < γ) (hδ : 0 < δ)
    (hγw : γ < wMax) :
    ∃ C x₀ : ℝ, 0 < C ∧ 2 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        ∀ M : ℝ, 1 ≤ M → Real.rpow x δ ≤ M → 2 * M ≤ Real.rpow x wMax →
          let Jγ := ⌊wMax / γ⌋₊
          (∑ m ∈ dyadicIntegers M,
            |roughIndicator x γ m - roughConvolution x γ wMax M m|) ≤
              (∑ p ∈ (primesUpTo (Real.sqrt (2 * M))).filter
                  (fun p => Real.rpow x γ < (p : ℝ)),
                ⌊2 * M / (p : ℝ) ^ 2⌋₊) ∧
          (∑ p ∈ (primesUpTo (Real.sqrt (2 * M))).filter
                  (fun p => Real.rpow x γ < (p : ℝ)),
                ⌊2 * M / (p : ℝ) ^ 2⌋₊ : ℝ) ≤ C * M * Real.rpow x (-γ) := by
  let x₀ : ℝ := max 2 (Real.exp (Real.log 2 / γ))
  refine ⟨4, x₀, by norm_num, le_max_left _ _, ?_⟩
  intro x hx M hM hMδ hScale
  have hx2 : 2 ≤ x := (le_max_left 2 _).trans hx
  have hx1 : 1 < x := by linarith
  let xCut : ℝ := Real.exp (Real.log 2 / γ)
  have hxCut : xCut ≤ x := (le_max_right 2 _).trans hx
  have hlogCut : Real.log 2 / γ ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos _) hxCut
    simpa [xCut] using h
  have hlogMul : Real.log 2 ≤ γ * Real.log x := by
    have h := (div_le_iff₀ hγ).mp hlogCut
    nlinarith
  have hY2 : 2 ≤ Real.rpow x γ := by
    have hpow : Real.rpow x γ = Real.exp (Real.log x * γ) :=
      Real.rpow_def_of_pos (by linarith : 0 < x) γ
    calc
      2 = Real.exp (Real.log 2) := by rw [Real.exp_log (by norm_num)]
      _ ≤ Real.exp (γ * Real.log x) := Real.exp_le_exp.mpr hlogMul
      _ = Real.rpow x γ := by rw [hpow]; congr 1; ring
  have hδpow : 1 < Real.rpow x δ := by
    rw [← Real.rpow_zero x]
    exact Real.rpow_lt_rpow_of_exponent_lt hx1 hδ
  have hMgt : 1 < M := lt_of_lt_of_le hδpow hMδ
  let Y := Real.rpow x γ
  let P : Finset ℕ := (primesUpTo (Real.sqrt (2 * M))).filter
    (fun (p : ℕ) => Y < (p : ℝ))
  let Q : Finset ℝ := ((primesUpTo (Real.sqrt (2 * M))).image
      (fun (p : ℕ) => (p : ℝ))).filter (fun p => Y < p)
  have hPMap : P.image (fun (p : ℕ) => (p : ℝ)) = Q := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
      rcases Finset.mem_filter.mp hq with ⟨hqPrime, hqY⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨q, hqPrime, rfl⟩, hqY⟩
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hpImage, hpY⟩
      rcases Finset.mem_image.mp hpImage with ⟨q, hqPrime, rfl⟩
      exact Finset.mem_image.mpr
        ⟨q, Finset.mem_filter.mpr ⟨hqPrime, hpY⟩, rfl⟩
  have hsumImage :
      (∑ p ∈ P.image (fun (p : ℕ) => (p : ℝ)),
        (⌊2 * M / (p : ℝ) ^ 2⌋₊ : ℝ)) =
      ∑ p ∈ P, (⌊2 * M / (p : ℝ) ^ 2⌋₊ : ℝ) := by
    apply Finset.sum_image
    intro a ha b hb hab
    exact Nat.cast_injective hab
  constructor
  · let Bad := (dyadicIntegers M).filter
      (fun m => roughAbove m Y ∧ ¬ Squarefree m)
    have hpoint : ∀ m ∈ dyadicIntegers M,
        |roughIndicator x γ m - roughConvolution x γ wMax M m| ≤
          if roughAbove m Y ∧ ¬ Squarefree m then (1 : ℝ) else 0 := by
      intro m hm
      exact rough_square_error_pointwise x γ wMax δ M m hx1 hγ hδ hM hMδ hScale hm
    have hsumBad :
        (∑ m ∈ dyadicIntegers M,
          if roughAbove m Y ∧ ¬ Squarefree m then (1 : ℝ) else 0) =
          (Bad.card : ℝ) := by
      calc
        _ = ∑ m ∈ Bad, (1 : ℝ) := by
          symm
          exact (Finset.sum_filter (s := dyadicIntegers M)
            (fun m => roughAbove m Y ∧ ¬ Squarefree m) (fun _ => (1 : ℝ)))
        _ = _ := by simp [Bad]
    have hbadNat := roughBadDyadic_card_le_square_count x γ M hM
    have hbadNat' : Bad.card ≤ ∑ p ∈ P, ⌊2 * M / (p : ℝ) ^ 2⌋₊ := by
      simpa [Bad, P, Y] using hbadNat
    have hbadCast : (Bad.card : ℝ) ≤
        ∑ p ∈ P, (⌊2 * M / (p : ℝ) ^ 2⌋₊ : ℝ) := by
      calc
        _ ≤ ((∑ p ∈ P, ⌊2 * M / (p : ℝ) ^ 2⌋₊ : ℕ) : ℝ) := by
          exact_mod_cast hbadNat'
        _ = _ := by simp
    have hbadReal : (Bad.card : ℝ) ≤
        (∑ p ∈ Q, (⌊2 * M / p ^ 2⌋₊ : ℝ)) := by
      calc
        _ ≤ ∑ p ∈ P, (⌊2 * M / (p : ℝ) ^ 2⌋₊ : ℝ) := hbadCast
        _ = ∑ p ∈ P.image (fun (p : ℕ) => (p : ℝ)),
            (⌊2 * M / (p : ℝ) ^ 2⌋₊ : ℝ) := hsumImage.symm
        _ = _ := by rw [hPMap]
    have hsumQCast : (∑ p ∈ Q, (⌊2 * M / p ^ 2⌋₊ : ℝ)) =
        ((∑ p ∈ Q, ⌊2 * M / p ^ 2⌋₊ : ℕ) : ℝ) := by
      rw [Nat.cast_sum]
    have hbadRealNat : (Bad.card : ℝ) ≤
        ((∑ p ∈ Q, ⌊2 * M / p ^ 2⌋₊ : ℕ) : ℝ) := by
      calc
        _ ≤ ∑ p ∈ Q, (⌊2 * M / p ^ 2⌋₊ : ℝ) := hbadReal
        _ = _ := hsumQCast
    calc
      _ ≤ ∑ m ∈ dyadicIntegers M,
          if roughAbove m Y ∧ ¬ Squarefree m then (1 : ℝ) else 0 := by
            apply Finset.sum_le_sum
            intro m hm
            exact hpoint m hm
      _ = (Bad.card : ℝ) := hsumBad
      _ ≤ _ := by simpa [Bad, Y, Q] using hbadRealNat
  · have htail := RoughProofs.prime_square_count_bound
      (Real.rpow x γ) M hY2 (by linarith : 0 ≤ M)
    have hneg : Real.rpow x (-γ) = (Real.rpow x γ)⁻¹ := by
      change x ^ (-γ) = (x ^ γ)⁻¹
      exact Real.rpow_neg (by positivity : 0 ≤ x) γ
    have htailQ : (∑ p ∈ Q, (⌊2 * M / p ^ 2⌋₊ : ℝ)) ≤
        4 * M * Real.rpow x (-γ) := by
      calc
        _ = ∑ p ∈ P.image (fun (p : ℕ) => (p : ℝ)),
            (⌊2 * M / (p : ℝ) ^ 2⌋₊ : ℝ) := by rw [← hPMap]
        _ = ∑ p ∈ P, (⌊2 * M / (p : ℝ) ^ 2⌋₊ : ℝ) := hsumImage
        _ ≤ 4 * M / Real.rpow x γ := htail
        _ = 4 * M * Real.rpow x (-γ) := by rw [hneg]; ring
    simpa [Q, Y] using htailQ

/-- `t2:sw-slot` — 08-type-ii.tex:385-407, `eq:rough-slot-siegel-walfisz`. -/
theorem sw_slot (γ : ℝ) (hγ : 0 < γ) :
    ∀ A₀ A₂ : ℝ, 0 < A₀ → 0 < A₂ →
      ∃ C x₀ : ℝ, 0 < C ∧ 2 ≤ x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          ∀ P : ℝ, Real.rpow x γ / 2 ≤ P → P ≤ 2 * x →
            ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.rpow (Real.log x) A₀ →
              ∀ χ : DirichletCharacter ℂ k, ∀ l r : ℝ,
                P ≤ l → l ≤ r → r ≤ 2 * P →
                  ‖∑ p ∈ (primesInInterval l r),
                    (χ (p : ZMod k) : ℂ) -
                    (if χ = 1 then (1 : ℂ) else 0) *
                      (∫ y in l..r, (1 / Real.log y : ℝ) : ℂ)‖ ≤
                    C * P * Real.rpow (Real.log x) (-A₂) := by
  sorry

/-- `t2:density-pushforward` — 08-type-ii.tex:272-294. -/
theorem density_pushforward (γ : ℝ) (hγ : 0 < γ) :
    ∀ x : ℝ, 2 ≤ x → ∀ j : ℕ, 1 ≤ j → ∀ l r : ℝ,
      Real.rpow x γ < l → l ≤ r →
        roughTupleIntegral x γ l r j =
          (1 / Real.log x) *
            ∫ y in l..r,
              ArtinPrimitiveRoots.Sieve.roughDensityTerm γ
                (Real.log y / Real.log x) j := by
  sorry

/-- `t2:density-regularity` — 08-type-ii.tex:296-315. Joint continuity, local Lipschitz
continuity in the second variable, and bounded variation of `w D_γ(w)`. -/
theorem density_regularity :
    ContinuousOn (fun p : ℝ × ℝ => ArtinPrimitiveRoots.Sieve.roughDensity p.1 p.2)
      {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2} ∧
    (∀ γ w₀ w₁ : ℝ, 0 < γ → γ < w₀ → w₀ ≤ w₁ →
      ∃ C : ℝ, 0 < C ∧ ∀ u v : ℝ, w₀ ≤ u → u ≤ w₁ → w₀ ≤ v → v ≤ w₁ →
        |ArtinPrimitiveRoots.Sieve.roughDensity γ u -
          ArtinPrimitiveRoots.Sieve.roughDensity γ v| ≤ C * |u - v|) ∧
    (∀ γ w₀ w₁ : ℝ, 0 < γ → γ < w₀ → w₀ ≤ w₁ →
      BoundedVariationOn (fun w => w * ArtinPrimitiveRoots.Sieve.roughDensity γ w)
        (Set.uIcc w₀ w₁)) := by
  sorry

/-- `t2:low-count` — 08-type-ii.tex:373-427, `eq:rough-convolution-low-count`. -/
theorem low_count (γ : ℝ) (hγ : 0 < γ) :
    ∀ A₀ A₁ : ℝ, 0 < A₀ → 0 < A₁ →
      ∃ C x₀ : ℝ, 0 < C ∧ 2 ≤ x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          ∀ M : ℝ, Real.rpow x γ ≤ M →
            ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.rpow (Real.log x) A₀ →
              ∀ χ : DirichletCharacter ℂ k, ∀ l r : ℝ,
                M ≤ l → l ≤ r → r ≤ 2 * M →
                  ‖(∑ m ∈ (Finset.range (⌊r⌋₊ + 1)).filter (fun (m : ℕ) =>
                        l ≤ (m : ℝ) ∧ (m : ℝ) ≤ r),
                      (roughIndicator x γ m : ℂ) * χ (m : ZMod k)) -
                    (if χ = 1 then
                      ((1 / Real.log x) *
                        ∫ y in l..r, ArtinPrimitiveRoots.Sieve.roughDensity γ
                          (Real.log y / Real.log x) : ℝ) else 0 : ℂ)‖ ≤
                    C * M * Real.rpow (Real.log x) (-A₁) := by
  sorry

/-- `t2:low-frequency` — 08-type-ii.tex:439-453. -/
theorem low_frequency (γ wMin wMax C δ : ℝ)
    (hγ : 0 < γ) (hγw : γ < wMin) (hw : wMin < wMax) (hδ : 0 < δ)
    (hC : 0 < C) :
    ∀ A₀ A B₂ : ℝ, 0 < A₀ → 0 < A → 0 < B₂ →
      ∃ C₀ x₀ : ℝ, 0 < C₀ ∧ 2 ≤ x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          ∀ M : ℝ, Real.rpow x δ ≤ M →
            Real.log M / Real.log x ∈ Set.Icc wMin wMax →
            ∀ l r : ℝ, M ≤ l → l ≤ r → r ≤ 2 * M →
              ∀ v t : ℝ, |v| ≤ Real.rpow (Real.log x) C →
                |t| ≤ Real.rpow (Real.log x) B₂ →
                  ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.rpow (Real.log x) A₀ →
                    ∀ χ : DirichletCharacter ℂ k,
                      ‖(∑ m ∈ (Finset.range (⌊r⌋₊ + 1)).filter (fun (m : ℕ) =>
                            l ≤ (m : ℝ) ∧ (m : ℝ) ≤ r),
                          roughCoefficient x γ v m * χ (m : ZMod k) *
                            Complex.exp (Complex.I * t * Real.log (m : ℝ))) / M‖ ≤
                        C₀ * Real.rpow (Real.log x) (-A) := by
  sorry

/-- `t2:prime-high` — 08-type-ii.tex:455-480. -/
theorem prime_high (γ wMax : ℝ) (hγ : 0 < γ) (hw : wMax < 1) :
    ∀ τ θ A₀ A₃ : ℝ, 0 < τ → τ < γ → wMax < θ → θ < 1 →
      0 < A₀ → 0 < A₃ →
      ∃ B₀ C₀ x₀ : ℝ, 0 < B₀ ∧ 0 < C₀ ∧ 2 ≤ x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          ∀ M : ℝ, Real.rpow x τ / 2 ≤ M → M ≤ Real.rpow x θ →
            ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.rpow (Real.log x) A₀ →
              ∀ χ : DirichletCharacter ℂ k, ∀ u : ℝ,
                Real.rpow (Real.log x) B₀ ≤ |u| → |u| ≤ Real.rpow x 2 →
                  ∀ l r : ℝ, M ≤ l → l ≤ r → r ≤ 2 * M →
                    ‖(∑ m ∈ (Finset.range (⌊r⌋₊ + 1)).filter (fun (m : ℕ) =>
                          l ≤ (m : ℝ) ∧ (m : ℝ) ≤ r),
                        (roughIndicator x γ m : ℂ) * χ (m : ZMod k) *
                          Complex.exp (Complex.I * u * Real.log (m : ℝ)))‖ ≤
                      C₀ * M * Real.rpow (Real.log x) (-A₃) := by
  sorry

/-- `t2:proxy-high` — 08-type-ii.tex:482-516; the source estimate is also the proof of PD
Lemma 5.2 (`05-major-arcs.tex:57-125`). -/
theorem proxy_high :
    ∃ C₃ : ℝ, 0 < C₃ ∧
      ∀ δ γ wMin wMax : ℝ, 0 < δ → 0 < γ → γ < wMin → wMin < wMax → wMax < 1 →
        ∀ A₀ : ℝ, 0 < A₀ →
          ∃ C₀ c₀ : ℝ, 0 < C₀ ∧ 0 < c₀ ∧
            ∀ A₄ : ℝ, 0 < A₄ → ∃ x₀ : ℝ, 2 ≤ x₀ ∧
              ∀ x : ℝ, x₀ ≤ x →
              let L := Real.log x
              let Tstar := Real.exp (L / Real.log L ^ 2)
              ∀ M : ℝ, Real.rpow x δ ≤ M →
                Real.log M / L ∈ Set.Icc wMin wMax →
                Real.log (2 * M) / L ∈ Set.Icc wMin wMax →
                ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.rpow L A₀ →
                  ∀ χ : DirichletCharacter ℂ k, ∀ l r u : ℝ,
                    M ≤ l → l ≤ r → r ≤ 2 * M → 1 ≤ |u| → |u| < Real.rpow x 2 →
                      (‖(∑ m ∈ (Finset.range (⌊r⌋₊ + 1)).filter (fun (m : ℕ) =>
                            l ≤ (m : ℝ) ∧ (m : ℝ) ≤ r ∧
                              roughAbove m (roughCutoff x)),
                          (χ (m : ZMod k) : ℂ) *
                            Complex.exp (Complex.I * u * Real.log (m : ℝ)) /
                            Real.log (m : ℝ)) /
                        (M * roughSieveProduct (roughCutoff x))‖ ≤
                      Real.rpow L (-A₄) +
                          C₀ * (if |u| ≤ Tstar then
                            Real.rpow L C₀ * (|u|⁻¹ + Real.rpow x (-c₀))
                          else Real.rpow L C₀ *
                            Real.exp (-L / Real.rpow (Real.log L) C₃))) ∧
                      (‖(∑ m ∈ (Finset.range (⌊r⌋₊ + 1)).filter (fun (m : ℕ) =>
                            l ≤ (m : ℝ) ∧ (m : ℝ) ≤ r ∧
                              roughAbove m (roughCutoff x)),
                          (χ (m : ZMod k) : ℂ) *
                            Complex.exp (Complex.I * u * Real.log (m : ℝ)) *
                            roughProxy x γ m) / M‖ ≤
                        Real.rpow L (-A₄) +
                          C₀ * (if |u| ≤ Tstar then
                            Real.rpow L C₀ * (|u|⁻¹ + Real.rpow x (-c₀))
                          else Real.rpow L C₀ *
                            Real.exp (-L / Real.rpow (Real.log L) C₃))) := by
  sorry

/-- `t2:high-frequency` — 08-type-ii.tex:513-527. -/
theorem high_frequency
    (γ wMin wMax δ C A : ℝ) (hγ : 0 < γ) (hγw : γ < wMin)
    (hw : wMin < wMax) (hwMax : wMax < 1) (hδ : 0 < δ)
    (hC : 0 < C) (hA : 0 < A) :
    ∀ B : ℝ, 0 < B →
      ∃ B₂ C₀ x₀ : ℝ, 0 < B₂ ∧ 0 < C₀ ∧ 2 ≤ x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          ∀ Hm Hn : ℝ, Real.rpow x δ ≤ Hm → Real.rpow x δ ≤ Hn →
            x / 2 ≤ Hm * Hn → Hm * Hn ≤ 2 * x →
            Real.log Hm / Real.log x ∈ Set.Icc wMin wMax →
            Real.log (2 * Hm) / Real.log x ∈ Set.Icc wMin wMax →
            ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.rpow (Real.log x) C →
              ∀ χ : DirichletCharacter ℂ k, ∀ v t : ℝ,
                Real.rpow (Real.log x) B₂ ≤ |t| →
                |t| ≤ 2 * (Hm * Hn) * Real.rpow (Real.log x) B →
                |v| ≤ Real.rpow (Real.log x) C →
                  ∀ l r : ℝ, Hm ≤ l → l ≤ r → r ≤ 2 * Hm →
                    ‖(∑ m ∈ (Finset.range (⌊r⌋₊ + 1)).filter (fun (m : ℕ) =>
                          l ≤ (m : ℝ) ∧ (m : ℝ) ≤ r),
                        roughCoefficient x γ v m * χ (m : ZMod k) *
                          Complex.exp (Complex.I * t * Real.log (m : ℝ))) / Hm‖ ≤
                      C₀ * Real.rpow (Real.log x) (-A) := by
  sorry

end ArtinPrimitiveRoots.TypeII.Rough
