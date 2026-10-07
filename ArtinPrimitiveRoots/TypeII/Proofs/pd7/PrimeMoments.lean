import ArtinPrimitiveRoots.TypeII.PD.Preliminaries

/-! Elementary coefficient bounds for growing powers of prime sums.

The `r!` loss comes from the number of ordered prime tuples with a fixed
product. This is the arithmetic input needed for the high-moment part of
`PD.sparse_frequency`.
-/

namespace ArtinPrimitiveRoots.TypeII.PD

open Finset
open scoped Classical

lemma pd7_prime_tuples_perm {r : ℕ} (v w : Fin r → ℕ)
    (hv : ∀ i, (v i).Prime) (hw : ∀ i, (w i).Prime)
    (hprod : (∏ i, v i) = ∏ i, w i) : List.Perm (List.ofFn v) (List.ofFn w) := by
  have hpv := Nat.primeFactorsList_unique (List.prod_ofFn (f := v)) (by
    intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    exact hv i)
  have hpw := Nat.primeFactorsList_unique (List.prod_ofFn (f := w)) (by
    intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    exact hw i)
  rw [hprod] at hpv
  exact hpv.trans hpw.symm

lemma pd7_prime_tuples_sorted_eq {r : ℕ} (v w : Fin r → ℕ)
    (hv : ∀ i, (v i).Prime) (hw : ∀ i, (w i).Prime)
    (hprod : (∏ i, v i) = ∏ i, w i) :
    v ∘ Tuple.sort v = w ∘ Tuple.sort w := by
  have hp := ((Tuple.sort v).ofFn_comp_perm v).trans
    ((pd7_prime_tuples_perm v w hv hw hprod).trans ((Tuple.sort w).ofFn_comp_perm w).symm)
  exact List.ofFn_injective (hp.eq_of_pairwise'
    (Tuple.monotone_sort v).sortedLE_ofFn.pairwise
    (Tuple.monotone_sort w).sortedLE_ofFn.pairwise)

theorem pd7_prime_product_fiber_card {r : ℕ} (S : Finset (Fin r → ℕ))
    (hS : ∀ v ∈ S, ∀ i, (v i).Prime) (n : ℕ) :
    (S.filter (fun v => (∏ i, v i) = n)).card ≤ r.factorial := by
  let T := S.filter (fun v => (∏ i, v i) = n)
  have hcard : T.card ≤ (univ : Finset (Equiv.Perm (Fin r))).card := by
    apply card_le_card_of_injOn Tuple.sort (fun _ _ => mem_univ _)
    intro v hv w hw he
    have hv' := mem_filter.mp hv
    have hw' := mem_filter.mp hw
    have hs := pd7_prime_tuples_sorted_eq v w (hS v hv'.1) (hS w hw'.1)
      (hv'.2.trans hw'.2.symm)
    funext i
    have hi := congrFun hs ((Tuple.sort v).symm i)
    rw [← he] at hi
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hi
  simpa only [T, card_univ, Fintype.card_perm, Fintype.card_fin] using hcard

lemma pd7_norm_sum_sq_le_card {α : Type*} (S : Finset α) (a : α → ℂ) :
    ‖∑ i ∈ S, a i‖ ^ 2 ≤ (S.card : ℝ) * ∑ i ∈ S, ‖a i‖ ^ 2 := by
  calc
    _ ≤ (∑ i ∈ S, ‖a i‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ _ := by
      simpa using sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun i => ‖a i‖)

theorem pd7_prime_product_coefficient_sq {r : ℕ} (S : Finset (Fin r → ℕ))
    (hS : ∀ v ∈ S, ∀ i, (v i).Prime) (a : (Fin r → ℕ) → ℂ) (n : ℕ) :
    ‖∑ v ∈ S.filter (fun v => (∏ i, v i) = n), a v‖ ^ 2 ≤
      (r.factorial : ℝ) * ∑ v ∈ S.filter (fun v => (∏ i, v i) = n), ‖a v‖ ^ 2 := by
  apply (pd7_norm_sum_sq_le_card _ a).trans
  apply mul_le_mul_of_nonneg_right _ (sum_nonneg fun _ _ => sq_nonneg _)
  exact_mod_cast pd7_prime_product_fiber_card S hS n

noncomputable def pd7PrimePowerCoefficient (P : Finset ℕ) (a : ℕ → ℂ)
    (r n : ℕ) : ℂ :=
  ∑ v ∈ (Fintype.piFinset fun _ : Fin r => P).filter
    (fun v => (∏ i, v i) = n), ∏ i, a (v i)

lemma pd7_prime_tuple_range (P : Finset ℕ) (N r : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hN : ∀ p ∈ P, p ≤ N)
    (v : Fin r → ℕ) (hv : v ∈ Fintype.piFinset fun _ : Fin r => P) :
    (∏ i, v i) ∈ Finset.Ioc 0 (N ^ r) := by
  have hm : ∀ i, v i ∈ P := Fintype.mem_piFinset.mp hv
  refine mem_Ioc.mpr ⟨Finset.prod_pos fun i _ => (hP _ (hm i)).pos, ?_⟩
  calc
    _ ≤ ∏ _i : Fin r, N := Finset.prod_le_prod fun i _ => hN _ (hm i)
    _ = _ := by simp

theorem pd7_prime_power_coefficient_mass (P : Finset ℕ) (a : ℕ → ℂ)
    (N r : ℕ) (hP : ∀ p ∈ P, p.Prime) (hN : ∀ p ∈ P, p ≤ N) :
    (∑ n ∈ Finset.Ioc 0 (N ^ r), ‖pd7PrimePowerCoefficient P a r n‖ ^ 2) ≤
      (r.factorial : ℝ) * (∑ p ∈ P, ‖a p‖ ^ 2) ^ r := by
  let S := Fintype.piFinset fun _ : Fin r => P
  have hs : ∀ v ∈ S, ∀ i, (v i).Prime := by
    intro v hv i
    exact hP _ (Fintype.mem_piFinset.mp hv i)
  calc
    _ ≤ ∑ n ∈ Finset.Ioc 0 (N ^ r), (r.factorial : ℝ) *
        ∑ v ∈ S.filter (fun v => (∏ i, v i) = n), ‖∏ i, a (v i)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro n _
      exact pd7_prime_product_coefficient_sq S hs (fun v => ∏ i, a (v i)) n
    _ = (r.factorial : ℝ) * ∑ v ∈ S, ‖∏ i, a (v i)‖ ^ 2 := by
      rw [← Finset.mul_sum]
      congr 1
      exact Finset.sum_fiberwise_of_maps_to
        (fun v hv => pd7_prime_tuple_range P N r hP hN v hv) _
    _ = _ := by
      congr 1
      simp only [norm_prod, ← Finset.prod_pow]
      exact (Finset.sum_pow' P (fun p => ‖a p‖ ^ 2) r).symm

noncomputable def pd7PrimePhase (u : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (((u * Real.log (n : ℝ) : ℝ) : ℂ) * Complex.I)

lemma pd7_prime_phase_eq (u : ℝ) (n : ℕ) :
    pd7PrimePhase u n = Complex.exp (Complex.I * u * Real.log (n : ℝ)) := by
  unfold pd7PrimePhase
  congr 1
  push_cast
  ring

@[simp] lemma pd7_prime_phase_norm (u : ℝ) (n : ℕ) :
    ‖pd7PrimePhase u n‖ = 1 := by
  unfold pd7PrimePhase
  exact Complex.norm_exp_ofReal_mul_I _

lemma pd7_prime_phase_add (u v : ℝ) (n : ℕ) :
    pd7PrimePhase (u + v) n = pd7PrimePhase u n * pd7PrimePhase v n := by
  unfold pd7PrimePhase
  have harg :
      (((((u + v) * Real.log (n : ℝ)) : ℝ) : ℂ) * Complex.I) =
        (((u * Real.log (n : ℝ) : ℝ) : ℂ) * Complex.I) +
          (((v * Real.log (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [harg, Complex.exp_add]

lemma pd7_dirichletPolynomial_eq_Ioc (Y : ℕ) (c : ℕ → ℂ) (u : ℝ) :
    dirichletPolynomial Y (fun n => if n = 0 then 0 else c n) u =
      ∑ n ∈ Finset.Ioc 0 Y, c n * pd7PrimePhase u n := by
  unfold dirichletPolynomial
  have hfilter : (Finset.range (Y + 1)).filter (fun n => 0 < n) = Finset.Ioc 0 Y := by
    ext n
    simp [and_comm]
  calc
    _ = ∑ n ∈ Finset.range (Y + 1),
        (if 0 < n then c n * pd7PrimePhase u n else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      by_cases h : n = 0
      · subst n
        simp
      · have hn0 : 0 < n := Nat.pos_of_ne_zero h
        simp [h, pd7_prime_phase_eq]
    _ = ∑ n ∈ (Finset.range (Y + 1)).filter (fun n => 0 < n),
        c n * pd7PrimePhase u n := by
      rw [← Finset.sum_filter]
    _ = _ := by rw [hfilter]

noncomputable def pd7PrimePolynomial (P : Finset ℕ) (a : ℕ → ℂ) (u : ℝ) : ℂ :=
  ∑ p ∈ P, a p * pd7PrimePhase u p

lemma pd7_prime_tuple_phase {r : ℕ} (v : Fin r → ℕ)
    (hv : ∀ i, 0 < v i) (u : ℝ) :
    (∏ i, pd7PrimePhase u (v i)) = pd7PrimePhase u (∏ i, v i) := by
  unfold pd7PrimePhase
  rw [← Complex.exp_sum]
  have hl : Real.log ((∏ i, v i : ℕ) : ℝ) = ∑ i, Real.log (v i : ℝ) := by
    push_cast
    exact Real.log_prod fun i _ => by exact_mod_cast (hv i).ne'
  rw [hl]
  congr 1
  simp only [Complex.ofReal_sum, Complex.ofReal_mul]
  rw [← Finset.sum_mul]
  congr 1
  rw [Finset.mul_sum]

theorem pd7_prime_polynomial_power (P : Finset ℕ) (a : ℕ → ℂ)
    (N r : ℕ) (hP : ∀ p ∈ P, p.Prime) (hN : ∀ p ∈ P, p ≤ N) (u : ℝ) :
    (pd7PrimePolynomial P a u) ^ r =
      ∑ n ∈ Finset.Ioc 0 (N ^ r),
        pd7PrimePowerCoefficient P a r n * pd7PrimePhase u n := by
  unfold pd7PrimePolynomial
  rw [Finset.sum_pow']
  symm
  calc
    _ = ∑ n ∈ Finset.Ioc 0 (N ^ r),
        ∑ v ∈ (Fintype.piFinset fun _ : Fin r => P).filter
          (fun v => (∏ i, v i) = n),
          (∏ i, a (v i)) * pd7PrimePhase u n := by
      apply Finset.sum_congr rfl
      intro n _
      exact Finset.sum_mul _ _ _
    _ = ∑ n ∈ Finset.Ioc 0 (N ^ r),
        ∑ v ∈ (Fintype.piFinset fun _ : Fin r => P).filter
          (fun v => (∏ i, v i) = n),
          (∏ i, a (v i)) * pd7PrimePhase u (∏ i, v i) := by
      apply Finset.sum_congr rfl
      intro n _
      apply Finset.sum_congr rfl
      intro v hv
      rw [(Finset.mem_filter.mp hv).2]
    _ = ∑ v ∈ Fintype.piFinset fun _ : Fin r => P,
        (∏ i, a (v i)) * pd7PrimePhase u (∏ i, v i) :=
      Finset.sum_fiberwise_of_maps_to
        (fun v hv => pd7_prime_tuple_range P N r hP hN v hv) _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [Finset.prod_mul_distrib, pd7_prime_tuple_phase v
        (fun i => (hP _ (Fintype.mem_piFinset.mp hv i)).pos) u]

lemma pd7_prime_power_coeff_range_mass (P : Finset ℕ) (a : ℕ → ℂ)
    (N r : ℕ) :
    (∑ n ∈ Finset.range (N ^ r + 1),
      ‖(if n = 0 then 0 else pd7PrimePowerCoefficient P a r n)‖ ^ 2) =
      ∑ n ∈ Finset.Ioc 0 (N ^ r),
        ‖pd7PrimePowerCoefficient P a r n‖ ^ 2 := by
  have hfilter : (Finset.range (N ^ r + 1)).filter (fun n => 0 < n) =
      Finset.Ioc 0 (N ^ r) := by
    ext n
    simp [and_comm]
  calc
    _ = ∑ n ∈ Finset.range (N ^ r + 1),
        (if 0 < n then ‖pd7PrimePowerCoefficient P a r n‖ ^ 2 else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      by_cases h : n = 0
      · subst n
        simp
      · have hn0 : 0 < n := Nat.pos_of_ne_zero h
        simp [h, hn0]
    _ = ∑ n ∈ (Finset.range (N ^ r + 1)).filter (fun n => 0 < n),
        ‖pd7PrimePowerCoefficient P a r n‖ ^ 2 := by
      rw [← Finset.sum_filter]
    _ = _ := by rw [hfilter]

theorem pd7_prime_polynomial_separated_moment :
    ∃ Cmv : ℝ, 0 < Cmv ∧
      ∀ (P : Finset ℕ) (a : ℕ → ℂ) (N r : ℕ),
        (∀ p ∈ P, p.Prime) → (∀ p ∈ P, p ≤ N) → 1 ≤ N →
        ∀ (S : Finset ℝ) (lo hi : ℝ), lo ≤ hi →
          (∀ t ∈ S, lo ≤ t ∧ t ≤ hi) →
          (∀ t₁ ∈ S, ∀ t₂ ∈ S, t₁ ≠ t₂ → 1 ≤ |t₁ - t₂|) →
      (∑ t ∈ S, ‖pd7PrimePolynomial P a t‖ ^ (2 * r)) ≤
        Cmv * (hi - lo + 1 + ((N ^ r : ℕ) : ℝ) *
          Real.log (2 * ((N ^ r : ℕ) : ℝ))) *
          Real.rpow (Real.log (2 * ((N ^ r : ℕ) : ℝ))) 2 *
            (r.factorial : ℝ) * (∑ p ∈ P, ‖a p‖ ^ 2) ^ r := by
  obtain ⟨_, _, ⟨Cmv, hCmv, hmv⟩⟩ := moment_bounds
  refine ⟨Cmv, hCmv, ?_⟩
  intro P a N r hP hN hN0 S lo hi hlohi hS hsep
  let c₀ : ℕ → ℂ := fun n =>
    if n = 0 then 0 else pd7PrimePowerCoefficient P a r n
  have hpoly (t : ℝ) :
      (pd7PrimePolynomial P a t) ^ r = dirichletPolynomial (N ^ r) c₀ t := by
    calc
      _ = ∑ n ∈ Finset.Ioc 0 (N ^ r),
          pd7PrimePowerCoefficient P a r n * pd7PrimePhase t n :=
        pd7_prime_polynomial_power P a N r hP hN t
      _ = _ := (pd7_dirichletPolynomial_eq_Ioc (N ^ r)
        (fun n => pd7PrimePowerCoefficient P a r n) t).symm
  have hpow (t : ℝ) :
      ‖pd7PrimePolynomial P a t‖ ^ (2 * r) =
        ‖dirichletPolynomial (N ^ r) c₀ t‖ ^ 2 := by
    rw [← hpoly t, norm_pow, ← pow_mul]
    rw [Nat.mul_comm]
  have hcoeff :
      (∑ n ∈ Finset.range (N ^ r + 1), ‖c₀ n‖ ^ 2) ≤
        (r.factorial : ℝ) * (∑ p ∈ P, ‖a p‖ ^ 2) ^ r := by
    rw [pd7_prime_power_coeff_range_mass]
    exact pd7_prime_power_coefficient_mass P a N r hP hN
  have hNcast : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN0
  have harg : (1 : ℝ) ≤ 2 * ((N ^ r : ℕ) : ℝ) := by
    rw [Nat.cast_pow]
    have hp : (1 : ℝ) ≤ (N : ℝ) ^ r := one_le_pow₀ hNcast
    nlinarith
  have hlog : 0 ≤ Real.log (2 * ((N ^ r : ℕ) : ℝ)) := Real.log_nonneg harg
  have hlogPow : 0 ≤ Real.rpow (Real.log (2 * ((N ^ r : ℕ) : ℝ))) 2 :=
    Real.rpow_nonneg hlog _
  have hlen : 0 ≤ hi - lo + 1 + ((N ^ r : ℕ) : ℝ) *
      Real.log (2 * ((N ^ r : ℕ) : ℝ)) := by
    have hspan : 0 ≤ hi - lo + 1 := by linarith
    have hterm : 0 ≤ ((N ^ r : ℕ) : ℝ) * Real.log (2 * ((N ^ r : ℕ) : ℝ)) :=
      mul_nonneg (by positivity) hlog
    exact add_nonneg hspan hterm
  have hfactor : 0 ≤ Cmv * (hi - lo + 1 + ((N ^ r : ℕ) : ℝ) *
      Real.log (2 * ((N ^ r : ℕ) : ℝ))) *
        Real.rpow (Real.log (2 * ((N ^ r : ℕ) : ℝ))) 2 :=
    mul_nonneg (mul_nonneg hCmv.le hlen) hlogPow
  have hsample := hmv (N ^ r) c₀ lo hi hlohi S hS hsep
  calc
    _ = ∑ t ∈ S, ‖dirichletPolynomial (N ^ r) c₀ t‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro t ht
      exact hpow t
    _ ≤ Cmv * (hi - lo + 1 + ((N ^ r : ℕ) : ℝ) *
          Real.log (2 * ((N ^ r : ℕ) : ℝ))) *
        Real.rpow (Real.log (2 * ((N ^ r : ℕ) : ℝ))) 2 *
          ∑ n ∈ Finset.range (N ^ r + 1), ‖c₀ n‖ ^ 2 := hsample
    _ ≤ Cmv * (hi - lo + 1 + ((N ^ r : ℕ) : ℝ) *
          Real.log (2 * ((N ^ r : ℕ) : ℝ))) *
        Real.rpow (Real.log (2 * ((N ^ r : ℕ) : ℝ))) 2 *
          ((r.factorial : ℝ) * (∑ p ∈ P, ‖a p‖ ^ 2) ^ r) :=
      mul_le_mul_of_nonneg_left hcoeff hfactor
    _ = _ := by ring

theorem pd7_prime_set_card_over_log_bound :
    ∃ C P₀ : ℝ, 0 < C ∧ 2 ≤ P₀ ∧
      ∀ P : ℝ, P₀ ≤ P → ∀ S : Finset ℕ,
        (∀ p ∈ S, p.Prime ∧ P ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * P) →
          (S.card : ℝ) ≤ C * P / Real.log P := by
  have hev := Chebyshev.eventually_primeCounting_le (by norm_num : (0 : ℝ) < 1)
  obtain ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.1 hev
  let C : ℝ := 2 * (Real.log 4 + 1)
  let P₀ : ℝ := max 2 (Y₀ / 2)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, P₀, hC, ?_, ?_⟩
  · dsimp [P₀]
    exact le_max_left _ _
  · intro P hP S hS
    have hP2 : 2 ≤ P := (le_max_left 2 (Y₀ / 2)).trans hP
    have hY : Y₀ ≤ 2 * P := by
      have hy : Y₀ / 2 ≤ P := (le_max_right 2 (Y₀ / 2)).trans hP
      linarith
    have hcheb := hY₀ (2 * P) hY
    have hsubset : S ⊆ Nat.primesLE ⌊2 * P⌋₊ := by
      intro p hp
      have h := hS p hp
      apply Nat.mem_primesLE.mpr
      constructor
      · exact Nat.le_floor (by exact_mod_cast h.2.2)
      · exact h.1
    have hcardNat := Finset.card_le_card hsubset
    have hcard : (S.card : ℝ) ≤ (Nat.primesLE ⌊2 * P⌋₊).card := by
      exact_mod_cast hcardNat
    rw [Nat.primesLE_card_eq_primeCounting] at hcard
    have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
    have hlog2P : 0 < Real.log (2 * P) := Real.log_pos (by linarith)
    have hlogle : Real.log P ≤ Real.log (2 * P) :=
      Real.log_le_log (by linarith) (by nlinarith)
    have hfinal :
        (Real.log 4 + 1) * (2 * P) / Real.log (2 * P) ≤ C * P / Real.log P := by
      apply (div_le_div_iff₀ hlog2P hlogP).2
      dsimp [C]
      calc
        (Real.log 4 + 1) * (2 * P) * Real.log P =
            (2 * (Real.log 4 + 1) * P) * Real.log P := by ring
        _ ≤ (2 * (Real.log 4 + 1) * P) * Real.log (2 * P) :=
          mul_le_mul_of_nonneg_left hlogle (by positivity)
    exact hcard.trans (hcheb.trans hfinal)

end ArtinPrimitiveRoots.TypeII.PD
