import ArtinPrimitiveRoots.TypeII.PD.Preliminaries
import Mathlib.Data.Set.Operations
import Mathlib.NumberTheory.Harmonic.Bounds

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
  have hfilter : (Finset.range (Y + 1)).filter (fun n => 1 ≤ n) = Finset.Ioc 0 Y := by
    ext n
    simp [Finset.mem_Ioc]
    omega
  rw [hfilter]
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : 0 < n := (Finset.mem_Ioc.mp hn).1
  simp [Nat.ne_of_gt hnpos, pd7_prime_phase_eq]

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
  have hcoeffFilter :
      (∑ n ∈ (Finset.range (N ^ r + 1)).filter (fun n => 1 ≤ n), ‖c₀ n‖ ^ 2) ≤
        ∑ n ∈ Finset.range (N ^ r + 1), ‖c₀ n‖ ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro n hn hnot
    exact sq_nonneg ‖c₀ n‖
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
  have hNpow : 1 ≤ N ^ r := Nat.one_le_pow _ _ hN0
  have hsample := hmv (N ^ r) hNpow c₀ lo hi hlohi S hS hsep
  calc
    _ = ∑ t ∈ S, ‖dirichletPolynomial (N ^ r) c₀ t‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro t ht
      exact hpow t
    _ ≤ Cmv * (hi - lo + 1 + ((N ^ r : ℕ) : ℝ) *
          Real.log (2 * ((N ^ r : ℕ) : ℝ))) *
        Real.rpow (Real.log (2 * ((N ^ r : ℕ) : ℝ))) 2 *
          ∑ n ∈ (Finset.range (N ^ r + 1)).filter (fun n => 1 ≤ n),
            ‖c₀ n‖ ^ 2 := hsample
    _ ≤ Cmv * (hi - lo + 1 + ((N ^ r : ℕ) : ℝ) *
          Real.log (2 * ((N ^ r : ℕ) : ℝ))) *
        Real.rpow (Real.log (2 * ((N ^ r : ℕ) : ℝ))) 2 *
          ∑ n ∈ Finset.range (N ^ r + 1), ‖c₀ n‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hcoeffFilter hfactor
    _ ≤ Cmv * (hi - lo + 1 + ((N ^ r : ℕ) : ℝ) *
          Real.log (2 * ((N ^ r : ℕ) : ℝ))) *
        Real.rpow (Real.log (2 * ((N ^ r : ℕ) : ℝ))) 2 *
          ((r.factorial : ℝ) * (∑ p ∈ P, ‖a p‖ ^ 2) ^ r) :=
      mul_le_mul_of_nonneg_left hcoeff hfactor
    _ = _ := by ring

theorem pd7_schur_bilinear_bound {α : Type*} [DecidableEq α]
    (S : Finset α) (G : α → α → ℂ) (b : α → ℂ) (R : ℝ)
    (hsym : ∀ i ∈ S, ∀ j ∈ S, ‖G i j‖ = ‖G j i‖)
    (hrow : ∀ i ∈ S, ∑ j ∈ S, ‖G i j‖ ≤ R) :
    ‖∑ i ∈ S, ∑ j ∈ S, star (b i) * b j * G i j‖ ≤
      R * ∑ i ∈ S, ‖b i‖ ^ 2 := by
  let a : α → ℝ := fun i => ‖b i‖
  have hnorm :
      ‖∑ i ∈ S, ∑ j ∈ S, star (b i) * b j * G i j‖ ≤
        ∑ i ∈ S, ∑ j ∈ S, a i * a j * ‖G i j‖ := by
    calc
      _ ≤ ∑ i ∈ S, ‖∑ j ∈ S, star (b i) * b j * G i j‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ S, ∑ j ∈ S, ‖star (b i) * b j * G i j‖ := by
        apply Finset.sum_le_sum
        intro i hi
        exact norm_sum_le _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        simp [a, norm_mul, mul_assoc]
  have hweight :
      (∑ i ∈ S, ∑ j ∈ S, a i * a j * ‖G i j‖) ≤
        ∑ i ∈ S, ∑ j ∈ S, ((a i ^ 2 + a j ^ 2) / 2) * ‖G i j‖ := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    have h2 : a i * a j ≤ (a i ^ 2 + a j ^ 2) / 2 := by
      dsimp [a]
      nlinarith [sq_nonneg (‖b i‖ - ‖b j‖)]
    exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
  have hdecomp :
      (∑ i ∈ S, ∑ j ∈ S, ((a i ^ 2 + a j ^ 2) / 2) * ‖G i j‖) =
        (∑ i ∈ S, (a i ^ 2 / 2) * ∑ j ∈ S, ‖G i j‖) +
          ∑ j ∈ S, (a j ^ 2 / 2) * ∑ i ∈ S, ‖G i j‖ := by
    calc
      _ = ∑ i ∈ S, ∑ j ∈ S,
          ((a i ^ 2 / 2) * ‖G i j‖ + (a j ^ 2 / 2) * ‖G i j‖) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = (∑ i ∈ S, ∑ j ∈ S, (a i ^ 2 / 2) * ‖G i j‖) +
          ∑ i ∈ S, ∑ j ∈ S, (a j ^ 2 / 2) * ‖G i j‖ := by
        simp_rw [Finset.sum_add_distrib]
      _ = _ := by
        have hfirst :
            (∑ i ∈ S, ∑ j ∈ S, (a i ^ 2 / 2) * ‖G i j‖) =
              ∑ i ∈ S, (a i ^ 2 / 2) * ∑ j ∈ S, ‖G i j‖ := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [← Finset.mul_sum]
        have hsecond :
            (∑ i ∈ S, ∑ j ∈ S, (a j ^ 2 / 2) * ‖G i j‖) =
              ∑ j ∈ S, (a j ^ 2 / 2) * ∑ i ∈ S, ‖G i j‖ := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j hj
          rw [← Finset.mul_sum]
        rw [hfirst, hsecond]
  have hrowTerm :
      (∑ i ∈ S, (a i ^ 2 / 2) * ∑ j ∈ S, ‖G i j‖) ≤
        (R / 2) * ∑ i ∈ S, a i ^ 2 := by
    calc
      _ ≤ ∑ i ∈ S, (a i ^ 2 / 2) * R := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hrow i hi)
          (div_nonneg (sq_nonneg _) (by norm_num))
      _ = _ := by
        simp_rw [div_eq_mul_inv, mul_assoc]
        rw [← Finset.sum_mul]
        ring
  have hcol (j : α) (hj : j ∈ S) : ∑ i ∈ S, ‖G i j‖ ≤ R := by
    calc
      _ = ∑ i ∈ S, ‖G j i‖ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hsym j hj i hi]
      _ ≤ R := hrow j hj
  have hcolTerm :
      (∑ j ∈ S, (a j ^ 2 / 2) * ∑ i ∈ S, ‖G i j‖) ≤
        (R / 2) * ∑ j ∈ S, a j ^ 2 := by
    calc
      _ ≤ ∑ j ∈ S, (a j ^ 2 / 2) * R := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (hcol j hj)
          (div_nonneg (sq_nonneg _) (by norm_num))
      _ = _ := by
        simp_rw [div_eq_mul_inv, mul_assoc]
        rw [← Finset.sum_mul]
        ring
  calc
    _ ≤ ∑ i ∈ S, ∑ j ∈ S, a i * a j * ‖G i j‖ := hnorm
    _ ≤ ∑ i ∈ S, ∑ j ∈ S, ((a i ^ 2 + a j ^ 2) / 2) * ‖G i j‖ := hweight
    _ = _ := hdecomp
    _ ≤ (R / 2) * ∑ i ∈ S, a i ^ 2 + (R / 2) * ∑ j ∈ S, a j ^ 2 :=
      add_le_add hrowTerm hcolTerm
    _ = _ := by dsimp [a]; ring

theorem pd7_finite_exponential_sample_bound {ι κ : Type*} [DecidableEq ι]
    [DecidableEq κ] (S : Finset ι) (T : Finset κ)
    (phase : ι → κ → ℂ) (c : κ → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hrow : ∀ i ∈ S, ∑ j ∈ S,
      ‖∑ n ∈ T, phase i n * star (phase j n)‖ ≤ R) :
    (∑ i ∈ S, ‖∑ n ∈ T, c n * phase i n‖ ^ 2) ≤
      R * ∑ n ∈ T, ‖c n‖ ^ 2 := by
  let F : ι → ℂ := fun i => ∑ n ∈ T, c n * phase i n
  let b : ι → ℂ := fun i => star (F i)
  let G : ι → ι → ℂ := fun i j => ∑ n ∈ T, star (phase i n) * phase j n
  let v : κ → ℂ := fun n => ∑ i ∈ S, star (F i) * phase i n
  have hnormSq (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = star z * z := by
    simpa using (Complex.conj_mul' z).symm
  have hGrel (i j : ι) :
      G i j = star (∑ n ∈ T, phase i n * star (phase j n)) := by
    dsimp [G]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro n hn
    simp [mul_comm]
  have hGstar (i j : ι) : star (G i j) = G j i := by
    dsimp [G]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro n hn
    simp [mul_comm]
  have hsym (i : ι) (hi : i ∈ S) (j : ι) (hj : j ∈ S) :
      ‖G i j‖ = ‖G j i‖ := by
    calc
      ‖G i j‖ = ‖star (G i j)‖ := by rw [norm_star]
      _ = ‖G j i‖ := by rw [hGstar]
  have hrowG (i : ι) (hi : i ∈ S) : ∑ j ∈ S, ‖G i j‖ ≤ R := by
    calc
      _ = ∑ j ∈ S, ‖star (∑ n ∈ T, phase i n * star (phase j n))‖ := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hGrel]
      _ = ∑ j ∈ S, ‖∑ n ∈ T, phase i n * star (phase j n)‖ := by
        apply Finset.sum_congr rfl
        intro j hj
        exact norm_star _
      _ ≤ R := hrow i hi
  have hSchur := pd7_schur_bilinear_bound S G b R hsym hrowG
  have hvSq (n : κ) :
      (‖v n‖ ^ 2 : ℂ) =
        ∑ i ∈ S, ∑ j ∈ S,
          star (b i) * b j * (star (phase i n) * phase j n) := by
    have hnsq : (‖v n‖ ^ 2 : ℂ) = star (v n) * v n := by
      simpa only [Complex.ofReal_pow] using hnormSq (v n)
    have hstar (n : κ) : star (v n) =
        ∑ i ∈ S, F i * star (phase i n) := by
      dsimp [v]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp
    calc
      _ = star (v n) * v n := hnsq
      _ = (∑ i ∈ S, F i * star (phase i n)) *
          ∑ j ∈ S, star (F j) * phase j n := by rw [hstar]
      _ = _ := by
        rw [Finset.sum_mul]
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        simp [b]
        ring
  have hgram :
      (∑ n ∈ T, (‖v n‖ ^ 2 : ℂ)) =
        ∑ i ∈ S, ∑ j ∈ S, star (b i) * b j * G i j := by
    calc
      _ = ∑ n ∈ T, ∑ i ∈ S, ∑ j ∈ S,
          star (b i) * b j * (star (phase i n) * phase j n) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact hvSq n
      _ = ∑ i ∈ S, ∑ j ∈ S, ∑ n ∈ T,
          star (b i) * b j * (star (phase i n) * phase j n) := by
        calc
          _ = ∑ i ∈ S, ∑ n ∈ T, ∑ j ∈ S,
              star (b i) * b j * (star (phase i n) * phase j n) := Finset.sum_comm
          _ = _ := by
            apply Finset.sum_congr rfl
            intro i hi
            exact Finset.sum_comm
      _ = ∑ i ∈ S, ∑ j ∈ S,
          star (b i) * b j * G i j := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [← Finset.mul_sum]
  have hVnonneg : 0 ≤ ∑ i ∈ S, ‖F i‖ ^ 2 :=
    Finset.sum_nonneg fun i hi => sq_nonneg _
  have hdiag :
      ((∑ i ∈ S, ‖F i‖ ^ 2 : ℝ) : ℂ) =
        ∑ i ∈ S, star (F i) * F i := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact hnormSq (F i)
  have hident :
      ((∑ i ∈ S, ‖F i‖ ^ 2 : ℝ) : ℂ) = ∑ n ∈ T, c n * v n := by
    calc
      _ = ∑ i ∈ S, star (F i) * F i := hdiag
      _ = ∑ i ∈ S, star (F i) * ∑ n ∈ T, c n * phase i n := by
        apply Finset.sum_congr rfl
        intro i hi
        rfl
      _ = ∑ n ∈ T, ∑ i ∈ S, star (F i) * (c n * phase i n) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
      _ = ∑ n ∈ T, c n * ∑ i ∈ S, star (F i) * phase i n := by
        apply Finset.sum_congr rfl
        intro n hn
        calc
          _ = ∑ i ∈ S, c n * (star (F i) * phase i n) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ = _ := by rw [Finset.mul_sum]
      _ = ∑ n ∈ T, c n * v n := by rfl
  have hgramReal :
      (∑ n ∈ T, ‖v n‖ ^ 2 : ℝ) =
        ‖∑ i ∈ S, ∑ j ∈ S, star (b i) * b j * G i j‖ := by
    have hCast :
        ((∑ n ∈ T, ‖v n‖ ^ 2 : ℝ) : ℂ) =
          ∑ n ∈ T, (‖v n‖ ^ 2 : ℂ) := by
      rw [Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro n hn
      exact Complex.ofReal_pow _ _
    calc
      _ = ‖((∑ n ∈ T, ‖v n‖ ^ 2 : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
        exact Finset.sum_nonneg fun n hn => sq_nonneg _
      _ = ‖∑ n ∈ T, (‖v n‖ ^ 2 : ℂ)‖ := by rw [hCast]
      _ = _ := by rw [hgram]
  have hVbound : (∑ n ∈ T, ‖v n‖ ^ 2 : ℝ) ≤
      R * ∑ i ∈ S, ‖F i‖ ^ 2 := by
    calc
      _ = ‖∑ i ∈ S, ∑ j ∈ S, star (b i) * b j * G i j‖ := hgramReal
      _ ≤ R * ∑ i ∈ S, ‖b i‖ ^ 2 := hSchur
      _ = R * ∑ i ∈ S, ‖F i‖ ^ 2 := by simp [b]
  have hCauchy : ‖∑ n ∈ T, c n * v n‖ ^ 2 ≤
      (∑ n ∈ T, ‖c n‖ ^ 2) * (∑ n ∈ T, ‖v n‖ ^ 2) := by
    calc
      _ ≤ (∑ n ∈ T, ‖c n * v n‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ = (∑ n ∈ T, ‖c n‖ * ‖v n‖) ^ 2 := by simp [norm_mul]
      _ ≤ _ := by
        simpa using sum_mul_sq_le_sq_mul_sq T (fun n => ‖c n‖) (fun n => ‖v n‖)
  let E : ℝ := ∑ i ∈ S, ‖F i‖ ^ 2
  have hE : 0 ≤ E := by dsimp [E]; exact hVnonneg
  have hVbound' : (∑ n ∈ T, ‖v n‖ ^ 2 : ℝ) ≤ R * E := by
    simpa [E] using hVbound
  have hEqNorm : E = ‖∑ n ∈ T, c n * v n‖ := by
    calc
      _ = ‖(E : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hE]
      _ = ‖∑ n ∈ T, c n * v n‖ := by rw [hident]
  have hCauchyE : E ^ 2 ≤
      (∑ n ∈ T, ‖c n‖ ^ 2) * (∑ n ∈ T, ‖v n‖ ^ 2) := by
    rw [hEqNorm]
    exact hCauchy
  have hEineq : E ^ 2 ≤ (∑ n ∈ T, ‖c n‖ ^ 2) * (R * E) :=
    hCauchyE.trans (mul_le_mul_of_nonneg_left hVbound'
      (Finset.sum_nonneg fun n hn => sq_nonneg _))
  have hEbound : E ≤ R * ∑ n ∈ T, ‖c n‖ ^ 2 := by
    by_cases hE0 : E = 0
    · rw [hE0]
      exact mul_nonneg hR (Finset.sum_nonneg fun n hn => sq_nonneg _)
    · have hEpos : 0 < E := lt_of_le_of_ne hE (Ne.symm hE0)
      have hmul : E * E ≤ (R * ∑ n ∈ T, ‖c n‖ ^ 2) * E := by
        nlinarith [hEineq]
      exact le_of_mul_le_mul_right hmul hEpos
  simpa [E, F] using hEbound

lemma pd7_exists_unit_interval_value_close_to_sSup (g : ℝ → ℝ) (j : ℤ) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ t ∈ Set.Icc (j : ℝ) ((j : ℝ) + 1),
      sSup (g '' Set.Icc (j : ℝ) ((j : ℝ) + 1)) - ε < g t := by
  have hne : (g '' Set.Icc (j : ℝ) ((j : ℝ) + 1)).Nonempty := by
    refine ⟨g (j : ℝ), Set.mem_image_of_mem _ ?_⟩
    simp
  obtain ⟨y, hy, hlt⟩ := exists_lt_of_lt_csSup hne (sub_lt_self _ hε)
  have hmem := (Set.mem_image g (Set.Icc (j : ℝ) ((j : ℝ) + 1)) y).1 hy
  obtain ⟨t, ht, hty⟩ := hmem
  subst y
  exact ⟨t, ht, hlt⟩

theorem pd7_unit_interval_sup_sum_bound (J : Finset ℤ) (f : ℝ → ℂ) (A R N : ℝ)
    (hJ : ∀ j ∈ J, |(j : ℝ)| ≤ R) (hcardJ : (J.card : ℝ) ≤ N)
    (hSample : ∀ S : Finset ℝ,
      (∀ t₁ ∈ S, ∀ t₂ ∈ S, t₁ ≠ t₂ → 1 ≤ |t₁ - t₂|) →
        (∀ t ∈ S, |t| ≤ R + 1) → (S.card : ℝ) ≤ N →
        (∑ t ∈ S, ‖f t‖ ^ 2) ≤ A) :
    (∑ j ∈ J, sSup ((fun t : ℝ => ‖f t‖ ^ 2) ''
      Set.Icc (j : ℝ) ((j : ℝ) + 1))) ≤ 2 * A := by
  let g : ℝ → ℝ := fun t => ‖f t‖ ^ 2
  let E : ℤ → ℝ := fun j => sSup (g '' Set.Icc (j : ℝ) ((j : ℝ) + 1))
  by_contra hnot
  have hlarge : 2 * A < ∑ j ∈ J, E j := lt_of_not_ge hnot
  let ε : ℝ := (∑ j ∈ J, E j - 2 * A) / (2 * ((J.card : ℝ) + 1))
  have hcard : 0 ≤ (J.card : ℝ) := Nat.cast_nonneg _
  have hε : 0 < ε := by
    dsimp [ε]
    have hden : 0 < 2 * ((J.card : ℝ) + 1) := by positivity
    exact div_pos (by linarith) hden
  let w : ℤ → ℝ := fun j => Classical.choose
    (pd7_exists_unit_interval_value_close_to_sSup g j ε hε)
  have hw (j : ℤ) :
      (j : ℝ) ≤ w j ∧ w j ≤ (j : ℝ) + 1 ∧ E j - ε < g (w j) := by
    have hspec := Classical.choose_spec
      (pd7_exists_unit_interval_value_close_to_sSup g j ε hε)
    obtain ⟨ht, hlt⟩ := hspec
    rcases Set.mem_Icc.mp ht with ⟨hlo, hhi⟩
    exact ⟨hlo, hhi, by simpa [E, w] using hlt⟩
  let J₀ := J.filter fun j => j % 2 = 0
  let J₁ := J.filter fun j => j % 2 = 1
  let S₀ := J₀.image w
  let S₁ := J₁.image w
  have hgap (j k : ℤ) (hj : j % 2 = 0) (hk : k % 2 = 0) (hjk : j ≠ k) :
      j + 2 ≤ k ∨ k + 2 ≤ j := by omega
  have hgap' (j k : ℤ) (hj : j % 2 = 1) (hk : k % 2 = 1) (hjk : j ≠ k) :
      j + 2 ≤ k ∨ k + 2 ≤ j := by omega
  have hinj₀ : Set.InjOn w (↑J₀ : Set ℤ) := by
    intro j hj k hk hEq
    have hj' := Finset.mem_filter.mp hj
    have hk' := Finset.mem_filter.mp hk
    by_contra hjk
    have hgapjk := hgap j k hj'.2 hk'.2 hjk
    have hwj := hw j
    have hwk := hw k
    rcases hgapjk with hgapjk | hgapjk
    · have hgapR : (j : ℝ) + 2 ≤ (k : ℝ) := by exact_mod_cast hgapjk
      have hstrict : w j < w k := by linarith [hwj.2.1, hwk.1]
      exact (ne_of_lt hstrict) hEq
    · have hgapR : (k : ℝ) + 2 ≤ (j : ℝ) := by exact_mod_cast hgapjk
      have hstrict : w k < w j := by linarith [hwk.2.1, hwj.1]
      exact (ne_of_lt hstrict) hEq.symm
  have hinj₁ : Set.InjOn w (↑J₁ : Set ℤ) := by
    intro j hj k hk hEq
    have hj' := Finset.mem_filter.mp hj
    have hk' := Finset.mem_filter.mp hk
    by_contra hjk
    have hgapjk := hgap' j k hj'.2 hk'.2 hjk
    have hwj := hw j
    have hwk := hw k
    rcases hgapjk with hgapjk | hgapjk
    · have hgapR : (j : ℝ) + 2 ≤ (k : ℝ) := by exact_mod_cast hgapjk
      have hstrict : w j < w k := by linarith [hwj.2.1, hwk.1]
      exact (ne_of_lt hstrict) hEq
    · have hgapR : (k : ℝ) + 2 ≤ (j : ℝ) := by exact_mod_cast hgapjk
      have hstrict : w k < w j := by linarith [hwk.2.1, hwj.1]
      exact (ne_of_lt hstrict) hEq.symm
  have hsep₀ : ∀ t₁ ∈ S₀, ∀ t₂ ∈ S₀, t₁ ≠ t₂ → 1 ≤ |t₁ - t₂| := by
    intro t₁ ht₁ t₂ ht₂ hne
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht₁
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ht₂
    have hj' := Finset.mem_filter.mp hj
    have hk' := Finset.mem_filter.mp hk
    have hjk : j ≠ k := by
      intro h
      exact hne (congrArg w h)
    rcases hgap j k hj'.2 hk'.2 hjk with hgapjk | hgapjk
    · have hgapR : (j : ℝ) + 2 ≤ (k : ℝ) := by exact_mod_cast hgapjk
      have hdiff : 1 ≤ w k - w j := by linarith [(hw j).2.1, (hw k).1]
      rw [abs_of_nonpos (by linarith : w j - w k ≤ 0)]
      linarith
    · have hgapR : (k : ℝ) + 2 ≤ (j : ℝ) := by exact_mod_cast hgapjk
      have hdiff : 1 ≤ w j - w k := by linarith [(hw k).2.1, (hw j).1]
      rw [abs_of_nonneg (by linarith : 0 ≤ w j - w k)]
      linarith
  have hsep₁ : ∀ t₁ ∈ S₁, ∀ t₂ ∈ S₁, t₁ ≠ t₂ → 1 ≤ |t₁ - t₂| := by
    intro t₁ ht₁ t₂ ht₂ hne
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht₁
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ht₂
    have hj' := Finset.mem_filter.mp hj
    have hk' := Finset.mem_filter.mp hk
    have hjk : j ≠ k := by
      intro h
      exact hne (congrArg w h)
    rcases hgap' j k hj'.2 hk'.2 hjk with hgapjk | hgapjk
    · have hgapR : (j : ℝ) + 2 ≤ (k : ℝ) := by exact_mod_cast hgapjk
      have hdiff : 1 ≤ w k - w j := by linarith [(hw j).2.1, (hw k).1]
      rw [abs_of_nonpos (by linarith : w j - w k ≤ 0)]
      linarith
    · have hgapR : (k : ℝ) + 2 ≤ (j : ℝ) := by exact_mod_cast hgapjk
      have hdiff : 1 ≤ w j - w k := by linarith [(hw k).2.1, (hw j).1]
      rw [abs_of_nonneg (by linarith : 0 ≤ w j - w k)]
      linarith
  have hbound₀ : ∀ t ∈ S₀, |t| ≤ R + 1 := by
    intro t ht
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht
    have hj' := Finset.mem_filter.mp hj
    have hjR := abs_le.mp (hJ j hj'.1)
    have hwj := hw j
    rw [abs_le]
    constructor <;> linarith
  have hbound₁ : ∀ t ∈ S₁, |t| ≤ R + 1 := by
    intro t ht
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht
    have hj' := Finset.mem_filter.mp hj
    have hjR := abs_le.mp (hJ j hj'.1)
    have hwj := hw j
    rw [abs_le]
    constructor <;> linarith
  have hcard₀Nat : S₀.card ≤ J.card := by
    calc
      S₀.card ≤ J₀.card := Finset.card_image_le
      _ ≤ J.card := Finset.card_le_card (Finset.filter_subset _ _)
  have hcard₁Nat : S₁.card ≤ J.card := by
    calc
      S₁.card ≤ J₁.card := Finset.card_image_le
      _ ≤ J.card := Finset.card_le_card (Finset.filter_subset _ _)
  have hcard₀ : (S₀.card : ℝ) ≤ N := by
    have hcard₀R : (S₀.card : ℝ) ≤ (J.card : ℝ) := by exact_mod_cast hcard₀Nat
    exact hcard₀R.trans hcardJ
  have hcard₁ : (S₁.card : ℝ) ≤ N := by
    have hcard₁R : (S₁.card : ℝ) ≤ (J.card : ℝ) := by exact_mod_cast hcard₁Nat
    exact hcard₁R.trans hcardJ
  have hsample₀ := hSample S₀ hsep₀ hbound₀ hcard₀
  have hsample₁ := hSample S₁ hsep₁ hbound₁ hcard₁
  have hsum₀ : (∑ j ∈ J₀, E j) ≤ A + ε * (J₀.card : ℝ) := by
    calc
      _ ≤ ∑ j ∈ J₀, (g (w j) + ε) := by
        apply Finset.sum_le_sum
        intro j hj
        linarith [(hw j).2.2]
      _ = (∑ t ∈ S₀, g t) + ε * (J₀.card : ℝ) := by
        rw [Finset.sum_add_distrib]
        have himage : (∑ j ∈ J₀, g (w j)) = ∑ t ∈ S₀, g t := by
          dsimp [S₀]
          rw [Finset.sum_image hinj₀]
        rw [himage]
        simp [mul_comm]
      _ ≤ _ := add_le_add hsample₀ le_rfl
  have hsum₁ : (∑ j ∈ J₁, E j) ≤ A + ε * (J₁.card : ℝ) := by
    calc
      _ ≤ ∑ j ∈ J₁, (g (w j) + ε) := by
        apply Finset.sum_le_sum
        intro j hj
        linarith [(hw j).2.2]
      _ = (∑ t ∈ S₁, g t) + ε * (J₁.card : ℝ) := by
        rw [Finset.sum_add_distrib]
        have himage : (∑ j ∈ J₁, g (w j)) = ∑ t ∈ S₁, g t := by
          dsimp [S₁]
          rw [Finset.sum_image hinj₁]
        rw [himage]
        simp [mul_comm]
      _ ≤ _ := add_le_add hsample₁ le_rfl
  have hdisj : Disjoint J₀ J₁ := by
    apply Finset.disjoint_left.mpr
    intro j hj₀ hj₁
    change j ∈ J.filter (fun j => j % 2 = 0) at hj₀
    change j ∈ J.filter (fun j => j % 2 = 1) at hj₁
    have h0 := (Finset.mem_filter.mp hj₀).2
    have h1 := (Finset.mem_filter.mp hj₁).2
    omega
  have hunion : J₀ ∪ J₁ = J := by
    ext j
    simp only [Finset.mem_union, J₀, J₁, Finset.mem_filter]
    constructor
    · rintro (⟨hj, hmod⟩ | ⟨hj, hmod⟩) <;> exact hj
    · intro hj
      have hmod : j % 2 = 0 ∨ j % 2 = 1 := by omega
      rcases hmod with hmod | hmod
      · exact Or.inl ⟨hj, hmod⟩
      · exact Or.inr ⟨hj, hmod⟩
  have htotal : (∑ j ∈ J, E j) ≤ 2 * A + ε * (J.card : ℝ) := by
    calc
      _ = (∑ j ∈ J₀, E j) + ∑ j ∈ J₁, E j := by
        rw [← hunion, Finset.sum_union hdisj]
      _ ≤ (A + ε * (J₀.card : ℝ)) + (A + ε * (J₁.card : ℝ)) :=
        add_le_add hsum₀ hsum₁
      _ = _ := by
        have hcardUnion : J₀.card + J₁.card = J.card := by
          rw [← Finset.card_union_of_disjoint hdisj, hunion]
        have hcardUnionR : (J₀.card : ℝ) + (J₁.card : ℝ) = (J.card : ℝ) := by
          exact_mod_cast hcardUnion
        calc
          _ = 2 * A + ε * ((J₀.card : ℝ) + (J₁.card : ℝ)) := by ring
          _ = _ := by rw [hcardUnionR]
  have hεcard : ε * (J.card : ℝ) < ∑ j ∈ J, E j - 2 * A := by
    dsimp [ε]
    have hpos : 0 < (∑ j ∈ J, E j - 2 * A) := by linarith
    have hden : 0 < 2 * ((J.card : ℝ) + 1) := by positivity
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hden).2
    nlinarith [hcard]
  linarith

theorem pd7_interval_sup_exponential_bound {κ : Type*} [DecidableEq κ]
    (J : Finset ℤ) (T : Finset κ) (phase : ℝ → κ → ℂ) (c : κ → ℂ)
    (Rfreq N Rgram : ℝ) (hRgram : 0 ≤ Rgram)
    (hJ : ∀ j ∈ J, |(j : ℝ)| ≤ Rfreq) (hcardJ : (J.card : ℝ) ≤ N)
    (hrow : ∀ S : Finset ℝ,
      (∀ t₁ ∈ S, ∀ t₂ ∈ S, t₁ ≠ t₂ → 1 ≤ |t₁ - t₂|) →
        (∀ t ∈ S, |t| ≤ Rfreq + 1) → (S.card : ℝ) ≤ N →
          ∀ i ∈ S, ∑ j ∈ S,
            ‖∑ n ∈ T, phase i n * star (phase j n)‖ ≤ Rgram) :
    (∑ j ∈ J, sSup ((fun t : ℝ =>
      ‖∑ n ∈ T, c n * phase t n‖ ^ 2) ''
        Set.Icc (j : ℝ) ((j : ℝ) + 1))) ≤
      2 * Rgram * (∑ n ∈ T, ‖c n‖ ^ 2) := by
  let f : ℝ → ℂ := fun t => ∑ n ∈ T, c n * phase t n
  have hsum := pd7_unit_interval_sup_sum_bound J f
    (Rgram * ∑ n ∈ T, ‖c n‖ ^ 2) Rfreq N hJ hcardJ (by
      intro S hsep hbound hcard
      have hrowS : ∀ i ∈ S, ∑ j ∈ S,
          ‖∑ n ∈ T, phase i n * star (phase j n)‖ ≤ Rgram :=
        hrow S hsep hbound hcard
      simpa [f] using
        pd7_finite_exponential_sample_bound S T phase c Rgram hRgram hrowS)
  calc
    _ ≤ 2 * (Rgram * ∑ n ∈ T, ‖c n‖ ^ 2) := hsum
    _ = _ := by ring

theorem pd7_positive_reciprocal_sum_bound (D : Finset ℝ) (R : ℝ)
    (hR : 1 ≤ R)
    (hD : ∀ d ∈ D, 1 ≤ d ∧ d ≤ R)
    (hsep : ∀ d₁ ∈ D, ∀ d₂ ∈ D, d₁ ≠ d₂ → 1 ≤ |d₁ - d₂|) :
    (∑ d ∈ D, d⁻¹) ≤ 1 + Real.log R := by
  let f : ℝ → ℕ := fun d => ⌊d⌋₊
  have hfloorLow (d : ℝ) (hd : d ∈ D) : 1 ≤ f d := by
    apply Nat.le_floor
    exact_mod_cast (hD d hd).1
  have hfloorLe (d : ℝ) (hd : d ∈ D) : (f d : ℝ) ≤ d := by
    dsimp [f]
    exact Nat.floor_le (by linarith [(hD d hd).1])
  have hinj : Set.InjOn f (↑D : Set ℝ) := by
    intro d hd e he hfe
    have hd' : d ∈ D := Finset.mem_coe.mp hd
    have he' : e ∈ D := Finset.mem_coe.mp he
    by_contra hne
    have hdt : d < (f d : ℝ) + 1 := by
      dsimp [f]
      exact Nat.lt_floor_add_one d
    have het : e < (f e : ℝ) + 1 := by
      dsimp [f]
      exact Nat.lt_floor_add_one e
    have hde : d - e < 1 := by
      calc
        d - e < (f d : ℝ) + 1 - e := by linarith
        _ = (f e : ℝ) + 1 - e := by rw [hfe]
        _ ≤ 1 := by linarith [hfloorLe e he']
    have hed : e - d < 1 := by
      calc
        e - d < (f e : ℝ) + 1 - d := by linarith
        _ = (f d : ℝ) + 1 - d := by rw [hfe]
        _ ≤ 1 := by linarith [hfloorLe d hd']
    have habs : |d - e| < 1 := by rw [abs_lt]; exact ⟨by linarith, by linarith⟩
    exact (not_lt_of_ge (hsep d hd' e he' hne)) habs
  have himageBound : D.image f ⊆ Finset.Icc 1 (⌊R⌋₊) := by
    intro n hn
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hn
    rw [Finset.mem_Icc]
    constructor
    · exact hfloorLow d hd
    · exact Nat.floor_le_floor (hD d hd).2
  have hsumFloor : (∑ d ∈ D, (f d : ℝ)⁻¹) =
      ∑ n ∈ D.image f, (n : ℝ)⁻¹ := by
    dsimp [f]
    rw [Finset.sum_image hinj]
  have hsumIcc : (∑ n ∈ Finset.Icc 1 (⌊R⌋₊), (n : ℝ)⁻¹) =
      harmonic ⌊R⌋₊ := by
    simp [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  calc
    _ ≤ ∑ d ∈ D, (f d : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro d hd
      have hfloorPos : (0 : ℝ) < (f d : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hfloorLow d hd))
      simpa only [one_div] using
        one_div_le_one_div_of_le hfloorPos (hfloorLe d hd)
    _ = ∑ n ∈ D.image f, (n : ℝ)⁻¹ := hsumFloor
    _ ≤ ∑ n ∈ Finset.Icc 1 (⌊R⌋₊), (n : ℝ)⁻¹ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg himageBound
      intro n hn hnot
      exact inv_nonneg.mpr (by exact_mod_cast Nat.zero_le n)
    _ = harmonic ⌊R⌋₊ := hsumIcc
    _ ≤ 1 + Real.log R := harmonic_floor_le_one_add_log R hR

theorem pd7_separated_sample_reciprocal_sum_bound (S : Finset ℝ) (t₀ R : ℝ)
    (ht₀ : t₀ ∈ S) (hR : 1 ≤ R)
    (hbound : ∀ t ∈ S, |t - t₀| ≤ R)
    (hsep : ∀ t₁ ∈ S, ∀ t₂ ∈ S, t₁ ≠ t₂ → 1 ≤ |t₁ - t₂|) :
    (∑ t ∈ S, if t = t₀ then (0 : ℝ) else (|t - t₀|)⁻¹) ≤
      2 * (1 + Real.log R) := by
  let L := S.filter fun t => t < t₀
  let U := S.filter fun t => t₀ < t
  let dL : ℝ → ℝ := fun t => t₀ - t
  let dU : ℝ → ℝ := fun t => t - t₀
  let DL := L.image dL
  let DU := U.image dU
  have hdisj : Disjoint L U := by
    apply Finset.disjoint_left.mpr
    intro t htL htU
    have htL' : t ∈ S.filter (fun t => t < t₀) := by simpa [L] using htL
    have htU' : t ∈ S.filter (fun t => t₀ < t) := by simpa [U] using htU
    have hl : t < t₀ := (Finset.mem_filter.mp htL').2
    have hu : t₀ < t := (Finset.mem_filter.mp htU').2
    linarith
  have hpartition : S.erase t₀ = L ∪ U := by
    ext t
    by_cases htS : t ∈ S <;> by_cases hteq : t = t₀ <;>
      simp [L, U, htS, hteq] <;> omega
  have hleftInj : Set.InjOn dL (↑L : Set ℝ) := by
    intro t ht s hs hEq
    dsimp [dL] at hEq
    linarith
  have hrightInj : Set.InjOn dU (↑U : Set ℝ) := by
    intro t ht s hs hEq
    dsimp [dU] at hEq
    linarith
  have hleftRange : ∀ d ∈ DL, 1 ≤ d ∧ d ≤ R := by
    intro d hd
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hd
    have ht' := Finset.mem_filter.mp ht
    have hne : t₀ ≠ t := by
      intro heq
      subst t
      exact (not_lt_of_ge (le_of_eq rfl)) ht'.2
    have hsep' := hsep t₀ ht₀ t ht'.1 hne
    have hpos : 0 < t₀ - t := sub_pos.mpr ht'.2
    constructor
    · simpa [dL, abs_of_pos hpos] using hsep'
    · have hbd := hbound t ht'.1
      simpa [dL, abs_of_pos hpos, abs_sub_comm] using hbd
  have hrightRange : ∀ d ∈ DU, 1 ≤ d ∧ d ≤ R := by
    intro d hd
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hd
    have ht' := Finset.mem_filter.mp ht
    have hne : t₀ ≠ t := ne_of_lt ht'.2
    have hsep' := hsep t₀ ht₀ t ht'.1 hne
    have hpos : 0 < t - t₀ := sub_pos.mpr ht'.2
    have habs : |t₀ - t| = t - t₀ := by
      rw [abs_sub_comm, abs_of_pos hpos]
    constructor
    · simpa [dU, habs] using hsep'
    · have hbd := hbound t ht'.1
      simpa [dU, abs_of_pos hpos] using hbd
  have hleftSep : ∀ d₁ ∈ DL, ∀ d₂ ∈ DL, d₁ ≠ d₂ →
      1 ≤ |d₁ - d₂| := by
    intro d₁ hd₁ d₂ hd₂ hne
    obtain ⟨t₁, ht₁, rfl⟩ := Finset.mem_image.mp hd₁
    obtain ⟨t₂, ht₂, rfl⟩ := Finset.mem_image.mp hd₂
    have ht₁' := Finset.mem_filter.mp ht₁
    have ht₂' := Finset.mem_filter.mp ht₂
    have htne : t₁ ≠ t₂ := by
      intro h
      apply hne
      subst t₂
      rfl
    have hsep' := hsep t₁ ht₁'.1 t₂ ht₂'.1 htne
    have habs : |dL t₁ - dL t₂| = |t₁ - t₂| := by
      dsimp [dL]
      rw [show (t₀ - t₁) - (t₀ - t₂) = t₂ - t₁ by ring, abs_sub_comm]
    rw [habs]
    exact hsep'
  have hrightSep : ∀ d₁ ∈ DU, ∀ d₂ ∈ DU, d₁ ≠ d₂ →
      1 ≤ |d₁ - d₂| := by
    intro d₁ hd₁ d₂ hd₂ hne
    obtain ⟨t₁, ht₁, rfl⟩ := Finset.mem_image.mp hd₁
    obtain ⟨t₂, ht₂, rfl⟩ := Finset.mem_image.mp hd₂
    have ht₁' := Finset.mem_filter.mp ht₁
    have ht₂' := Finset.mem_filter.mp ht₂
    have htne : t₁ ≠ t₂ := by
      intro h
      apply hne
      subst t₂
      rfl
    have hsep' := hsep t₁ ht₁'.1 t₂ ht₂'.1 htne
    have habs : |dU t₁ - dU t₂| = |t₁ - t₂| := by
      dsimp [dU]
      rw [show (t₁ - t₀) - (t₂ - t₀) = t₁ - t₂ by ring]
    rw [habs]
    exact hsep'
  have hsumL : (∑ t ∈ L, (|t - t₀|)⁻¹) = ∑ d ∈ DL, d⁻¹ := by
    calc
      _ = ∑ t ∈ L, (dL t)⁻¹ := by
        apply Finset.sum_congr rfl
        intro t ht
        have hlt := (Finset.mem_filter.mp ht).2
        dsimp [dL]
        rw [abs_of_neg (sub_neg.mpr hlt)]
        ring
      _ = _ := by
        dsimp [DL, dL]
        rw [Finset.sum_image hleftInj]
  have hsumU : (∑ t ∈ U, (|t - t₀|)⁻¹) = ∑ d ∈ DU, d⁻¹ := by
    calc
      _ = ∑ t ∈ U, (dU t)⁻¹ := by
        apply Finset.sum_congr rfl
        intro t ht
        have hlt := (Finset.mem_filter.mp ht).2
        dsimp [dU]
        rw [abs_of_pos (sub_pos.mpr hlt)]
      _ = _ := by
        dsimp [DU, dU]
        rw [Finset.sum_image hrightInj]
  have hsumSplit :
      (∑ t ∈ S, if t = t₀ then (0 : ℝ) else (|t - t₀|)⁻¹) =
        (∑ t ∈ L, (|t - t₀|)⁻¹) + ∑ t ∈ U, (|t - t₀|)⁻¹ := by
    rw [← Finset.sum_erase_add _ _ ht₀]
    simp only [if_pos, zero_add]
    rw [hpartition, Finset.sum_union hdisj]
    have hL :
        (∑ t ∈ L, if t = t₀ then (0 : ℝ) else (|t - t₀|)⁻¹) =
          ∑ t ∈ L, (|t - t₀|)⁻¹ := by
      apply Finset.sum_congr rfl
      intro t ht
      have htL' : t ∈ S.filter (fun t => t < t₀) := by simpa [L] using ht
      have hlt : t < t₀ := (Finset.mem_filter.mp htL').2
      simp [ne_of_lt hlt]
    have hU :
        (∑ t ∈ U, if t = t₀ then (0 : ℝ) else (|t - t₀|)⁻¹) =
          ∑ t ∈ U, (|t - t₀|)⁻¹ := by
      apply Finset.sum_congr rfl
      intro t ht
      have htU' : t ∈ S.filter (fun t => t₀ < t) := by simpa [U] using ht
      have hlt : t₀ < t := (Finset.mem_filter.mp htU').2
      simp [ne_of_gt hlt]
    rw [hL, hU]
    simp
  have hboundL := pd7_positive_reciprocal_sum_bound DL R hR hleftRange hleftSep
  have hboundU := pd7_positive_reciprocal_sum_bound DU R hR hrightRange hrightSep
  rw [hsumSplit, hsumL, hsumU]
  linarith

theorem pd7_gram_row_bound (S : Finset ℝ) (t₀ R Hfac T ρ σ : ℝ)
    (ht₀ : t₀ ∈ S) (hR : 1 ≤ R) (hHfac : 0 ≤ Hfac) (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hbound : ∀ t ∈ S, |t - t₀| ≤ R)
    (hsep : ∀ t₁ ∈ S, ∀ t₂ ∈ S, t₁ ≠ t₂ → 1 ≤ |t₁ - t₂|)
    (G : ℝ → ℝ → ℂ)
    (hdiag : ‖G t₀ t₀‖ ≤ Hfac)
    (hnear : ∀ t ∈ S, t ≠ t₀ → 1 ≤ |t - t₀| → |t - t₀| ≤ T →
      ‖G t₀ t‖ ≤ Hfac * ((|t - t₀|)⁻¹ + ρ))
    (hfar : ∀ t ∈ S, t ≠ t₀ → 1 ≤ |t - t₀| → T < |t - t₀| →
      ‖G t₀ t‖ ≤ Hfac * σ) :
    (∑ t ∈ S, ‖G t₀ t‖) ≤
      Hfac * (1 + 2 * (1 + Real.log R) + (S.card : ℝ) * (ρ + σ)) := by
  let W : ℝ → ℝ := fun t =>
    if t = t₀ then 1 else (|t - t₀|)⁻¹ + ρ + σ
  have hterm (t : ℝ) (ht : t ∈ S) : ‖G t₀ t‖ ≤ Hfac * W t := by
    by_cases hEq : t = t₀
    · subst t
      simpa [W] using hdiag
    · have hdist : 1 ≤ |t - t₀| := by
        have h := hsep t₀ ht₀ t ht (Ne.symm hEq)
        simpa [abs_sub_comm] using h
      by_cases hsmall : |t - t₀| ≤ T
      · have h := hnear t ht hEq hdist hsmall
        have hscale := mul_le_mul_of_nonneg_left
          (show (|t - t₀|)⁻¹ + ρ ≤ (|t - t₀|)⁻¹ + ρ + σ by linarith) hHfac
        simpa [W, hEq] using h.trans hscale
      · have hlarge : T < |t - t₀| := lt_of_not_ge hsmall
        have h := hfar t ht hEq hdist hlarge
        have hscale := mul_le_mul_of_nonneg_left
          (show σ ≤ (|t - t₀|)⁻¹ + ρ + σ by
            have hinv : 0 ≤ (|t - t₀|)⁻¹ := inv_nonneg.mpr (abs_nonneg _)
            linarith [hρ]) hHfac
        simpa [W, hEq] using h.trans hscale
  have htemplate : (∑ t ∈ S, W t) ≤
      1 + 2 * (1 + Real.log R) + (S.card : ℝ) * (ρ + σ) := by
    let B : ℝ → ℝ := fun t => if t = t₀ then 1 else (|t - t₀|)⁻¹
    let E : ℝ → ℝ := fun t => if t = t₀ then 0 else ρ + σ
    have hdecomp (t : ℝ) : W t = B t + E t := by
      by_cases h : t = t₀ <;> simp [W, B, E, h] <;> ring
    have hB : (∑ t ∈ S, B t) =
        1 + ∑ t ∈ S, if t = t₀ then (0 : ℝ) else (|t - t₀|)⁻¹ := by
      have hbase : (∑ t ∈ S, B t) =
          (∑ t ∈ S.erase t₀, (|t - t₀|)⁻¹) + 1 := by
        calc
          _ = (∑ t ∈ S.erase t₀, B t) + B t₀ := by
            rw [← Finset.sum_erase_add _ _ ht₀]
          _ = (∑ t ∈ S.erase t₀, (|t - t₀|)⁻¹) + 1 := by
            have herase : (∑ t ∈ S.erase t₀, B t) =
                ∑ t ∈ S.erase t₀, (|t - t₀|)⁻¹ := by
              apply Finset.sum_congr rfl
              intro t ht
              have hne := (Finset.mem_erase.mp ht).1
              simp [B, hne]
            rw [herase]
            simp [B]
      have hrecip : (∑ t ∈ S, if t = t₀ then (0 : ℝ) else (|t - t₀|)⁻¹) =
          ∑ t ∈ S.erase t₀, (|t - t₀|)⁻¹ := by
        rw [← Finset.sum_erase_add _ _ ht₀]
        simp only [if_pos, add_zero]
        apply Finset.sum_congr rfl
        intro t ht
        have hne := (Finset.mem_erase.mp ht).1
        simp [hne]
      rw [hbase, hrecip]
      ring
    have hE : (∑ t ∈ S, E t) ≤ (S.card : ℝ) * (ρ + σ) := by
      calc
        _ ≤ ∑ _t ∈ S, (ρ + σ) := by
          apply Finset.sum_le_sum
          intro t ht
          by_cases h : t = t₀
          · simp [E, h]
            exact add_nonneg hρ hσ
          · simp [E, h]
        _ = _ := by simp [Finset.sum_const, mul_comm]; ring
    have hrecip := pd7_separated_sample_reciprocal_sum_bound S t₀ R ht₀ hR hbound hsep
    have hbaseBound : (∑ t ∈ S, B t) ≤ 1 + 2 * (1 + Real.log R) := by
      rw [hB]
      linarith
    calc
      _ = (∑ t ∈ S, B t) + ∑ t ∈ S, E t := by
        calc
          _ = ∑ t ∈ S, (B t + E t) := by
            apply Finset.sum_congr rfl
            intro t ht
            exact hdecomp t
          _ = _ := Finset.sum_add_distrib
      _ ≤ (1 + 2 * (1 + Real.log R)) + (S.card : ℝ) * (ρ + σ) :=
        add_le_add hbaseBound hE
      _ = _ := by ring
  calc
    _ ≤ ∑ t ∈ S, Hfac * W t := by
      apply Finset.sum_le_sum
      intro t ht
      exact hterm t ht
    _ = Hfac * ∑ t ∈ S, W t := by rw [← Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left htemplate hHfac

theorem pd7_gram_all_rows_bound (S : Finset ℝ) (F Hfac T ρ σ : ℝ)
    (hF : 0 ≤ F) (hHfac : 0 ≤ Hfac) (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hrange : ∀ t ∈ S, |t| ≤ F)
    (hsep : ∀ t₁ ∈ S, ∀ t₂ ∈ S, t₁ ≠ t₂ → 1 ≤ |t₁ - t₂|)
    (G : ℝ → ℝ → ℂ)
    (hdiag : ∀ i ∈ S, ‖G i i‖ ≤ Hfac)
    (hnear : ∀ i ∈ S, ∀ t ∈ S, t ≠ i → 1 ≤ |t - i| → |t - i| ≤ T →
      ‖G i t‖ ≤ Hfac * ((|t - i|)⁻¹ + ρ))
    (hfar : ∀ i ∈ S, ∀ t ∈ S, t ≠ i → 1 ≤ |t - i| → T < |t - i| →
      ‖G i t‖ ≤ Hfac * σ) :
    ∀ i ∈ S, (∑ t ∈ S, ‖G i t‖) ≤
      Hfac * (1 + 2 * (1 + Real.log (2 * (F + 1))) +
        (S.card : ℝ) * (ρ + σ)) := by
  intro i hi
  have hR : 1 ≤ 2 * (F + 1) := by linarith
  have hbound : ∀ t ∈ S, |t - i| ≤ 2 * (F + 1) := by
    intro t ht
    have ht' := abs_le.mp (hrange t ht)
    have hi' := abs_le.mp (hrange i hi)
    apply abs_le.mpr
    constructor <;> linarith
  exact pd7_gram_row_bound S i (2 * (F + 1)) Hfac T ρ σ hi hR
    hHfac hρ hσ hbound hsep G (hdiag i hi)
    (fun t ht hne hdist hsmall => hnear i hi t ht hne hdist hsmall)
    (fun t ht hne hdist hlarge => hfar i hi t ht hne hdist hlarge)

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

theorem pd7_sparse_log_product_length_bound
    (L P C₁ : ℝ) (r U : ℕ)
    (hL : 1 ≤ L) (hP : 1 ≤ P) (hC₁ : 0 < C₁)
    (hlogP : Real.log P ≤ C₁ * Real.rpow L (1 / 5 : ℝ))
    (hUone : 1 ≤ U)
    (hU : (U : ℝ) ≤ (2 * P) ^ r)
    (hr : (r : ℝ) ≤ 21 * Real.rpow L (9 / 10 : ℝ)) :
    0 ≤ Real.log (2 * (U : ℝ)) ∧
      Real.log (2 * (U : ℝ)) ≤ (1 + 21 * (1 + C₁)) * Real.rpow L (11 / 10 : ℝ) := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hLpow : 1 ≤ Real.rpow L (1 / 5 : ℝ) := Real.one_le_rpow hL (by norm_num)
  have hLpow09 : 0 ≤ Real.rpow L (9 / 10 : ℝ) := Real.rpow_nonneg hLpos.le _
  have hargPos : 0 < 2 * (U : ℝ) := by
    have hUpos : 0 < (U : ℝ) := by exact_mod_cast (show 0 < U by omega)
    positivity
  have hlogNonneg : 0 ≤ Real.log (2 * (U : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * U by omega))
  have hmulPos : 0 < 2 * P := by positivity
  have hUbound : 2 * (U : ℝ) ≤ 2 * (2 * P) ^ r := by nlinarith [hU]
  have hlogMonotone := Real.log_le_log hargPos hUbound
  have hpowNe : (2 * P) ^ r ≠ 0 := pow_ne_zero _ (ne_of_gt hmulPos)
  have hlogRight : Real.log (2 * (2 * P) ^ r) =
      Real.log 2 + (r : ℝ) * Real.log (2 * P) := by
    rw [Real.log_mul (by norm_num) hpowNe, Real.log_pow]
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    nlinarith
  have hlog2P : Real.log (2 * P) = Real.log 2 + Real.log P :=
    Real.log_mul (by norm_num) (ne_of_gt (by positivity : (0 : ℝ) < P))
  have hlog2Pbound : Real.log (2 * P) ≤ (1 + C₁) * Real.rpow L (1 / 5 : ℝ) := by
    rw [hlog2P]
    calc
      Real.log 2 + Real.log P ≤ 1 + C₁ * Real.rpow L (1 / 5 : ℝ) :=
        add_le_add hlog2 hlogP
      _ ≤ (1 + C₁) * Real.rpow L (1 / 5 : ℝ) := by
        nlinarith [hLpow, le_of_lt hC₁]
  have hlog2Pnonneg : 0 ≤ Real.log (2 * P) :=
    Real.log_nonneg (by nlinarith [hP])
  have hlogRightBound :
      Real.log 2 + (r : ℝ) * Real.log (2 * P) ≤
        (1 + 21 * (1 + C₁)) * Real.rpow L (11 / 10 : ℝ) := by
    have hprod : Real.rpow L (9 / 10 : ℝ) * Real.rpow L (1 / 5 : ℝ) =
        Real.rpow L (11 / 10 : ℝ) := by
      calc
        _ = Real.rpow L ((9 / 10 : ℝ) + 1 / 5) :=
          (Real.rpow_add hLpos _ _).symm
        _ = Real.rpow L (11 / 10 : ℝ) := by congr 1 <;> norm_num
    have hbase : 1 ≤ Real.rpow L (11 / 10 : ℝ) := Real.one_le_rpow hL (by norm_num)
    have hprodBound : (r : ℝ) * Real.log (2 * P) ≤
        (21 * Real.rpow L (9 / 10 : ℝ)) *
          ((1 + C₁) * Real.rpow L (1 / 5 : ℝ)) := by
      calc
        _ ≤ (21 * Real.rpow L (9 / 10 : ℝ)) * Real.log (2 * P) :=
          mul_le_mul_of_nonneg_right hr hlog2Pnonneg
        _ ≤ _ := mul_le_mul_of_nonneg_left hlog2Pbound
          (mul_nonneg (by norm_num) hLpow09)
    calc
      _ ≤ 1 + (21 * Real.rpow L (9 / 10 : ℝ)) *
          ((1 + C₁) * Real.rpow L (1 / 5 : ℝ)) := add_le_add hlog2 hprodBound
      _ = 1 + 21 * (1 + C₁) * Real.rpow L (11 / 10 : ℝ) := by
        congr 1
        calc
          21 * Real.rpow L (9 / 10 : ℝ) *
              ((1 + C₁) * Real.rpow L (1 / 5 : ℝ)) =
            21 * (1 + C₁) *
              (Real.rpow L (9 / 10 : ℝ) * Real.rpow L (1 / 5 : ℝ)) := by ring
          _ = _ := by rw [hprod]
      _ ≤ _ := by nlinarith [hbase]
  exact ⟨hlogNonneg, hlogMonotone.trans (hlogRight ▸ hlogRightBound)⟩

noncomputable def pd7_sparse_moment_count_constant (B A_s C₁ Cmv : ℝ) : ℝ :=
  1 + |Real.log (2 * Cmv * (9 + (1 + 21 * (1 + C₁))) *
      (1 + 21 * (1 + C₁)) ^ 2)| +
    (max B (11 / 10 : ℝ) + 11 / 5) +
      21 * (Real.log 6 + Real.log 21 + 1 + 2 * A_s)

set_option maxHeartbeats 1000000 in
theorem pd7_sparse_moment_expression_bound
    (L P R B A_s C₁ Cmv Pcard : ℝ) (r U : ℕ)
    (hL : 2 ≤ L) (hlogL : Real.log L ≤ Real.rpow L (1 / 100 : ℝ))
    (hP : 1 ≤ P) (hB : 0 < B) (hAs : 0 < A_s)
    (hC₁ : 0 < C₁) (hCmv : 0 < Cmv)
    (hlogP : Real.log P ≤ C₁ * Real.rpow L (1 / 5 : ℝ))
    (hR : 0 ≤ R) (hRbound : R ≤ 4 * Real.exp L * Real.rpow L B)
    (hPr : Real.exp L ≤ P ^ r) (hUone : 1 ≤ U)
    (hUbound : (U : ℝ) ≤ (2 * P) ^ r)
    (hPcard : 0 ≤ Pcard) (hPcardBound : Pcard ≤ 3 * P)
    (hrLow : 4 ≤ r)
    (hr : (r : ℝ) ≤ 21 * Real.rpow L (9 / 10 : ℝ)) :
    0 < pd7_sparse_moment_count_constant B A_s C₁ Cmv ∧
      2 * Cmv * (2 * R + 1 + (U : ℝ) * Real.log (2 * (U : ℝ))) *
          Real.log (2 * (U : ℝ)) ^ 2 * (r.factorial : ℝ) * Pcard ^ r *
          (1 / P) ^ (2 * r) / (Real.rpow L (-A_s)) ^ (2 * r) ≤
        Real.exp (pd7_sparse_moment_count_constant B A_s C₁ Cmv *
          Real.rpow L (91 / 100 : ℝ)) := by
  let u : ℝ := Real.log (2 * (U : ℝ))
  let e : ℝ := 11 / 10
  let d : ℝ := max B e
  let cu : ℝ := 1 + 21 * (1 + C₁)
  let K0 : ℝ := 2 * Cmv * (9 + cu) * cu ^ 2
  let m : ℝ := d + 11 / 5
  let c : ℝ := 1 + |Real.log K0| + m +
    21 * (Real.log 6 + Real.log 21 + 1 + 2 * A_s)
  have hLge : 1 ≤ L := by linarith
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hLge
  have hPpos : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hLpowB : 1 ≤ Real.rpow L B := Real.one_le_rpow hLge hB.le
  have hLpowE : 1 ≤ Real.rpow L e := Real.one_le_rpow hLge (by norm_num [e])
  have hLpowD : 1 ≤ Real.rpow L d := Real.one_le_rpow hLge (by
    dsimp [d, e]
    positivity)
  have hD_B : B ≤ d := le_max_left _ _
  have hE_D : e ≤ d := le_max_right _ _
  have hpowB_D : Real.rpow L B ≤ Real.rpow L d :=
    Real.rpow_le_rpow_of_exponent_le hLge hD_B
  have hpowE_D : Real.rpow L e ≤ Real.rpow L d :=
    Real.rpow_le_rpow_of_exponent_le hLge hE_D
  have hlogU := pd7_sparse_log_product_length_bound L P C₁ r U hLge hP hC₁
    hlogP hUone hUbound hr
  have hu0 : 0 ≤ u := by simpa [u] using hlogU.1
  have hu : u ≤ cu * Real.rpow L e := by
    simpa [u, cu, e] using hlogU.2
  have hPrOne : 1 ≤ P ^ r := by
    have hExpOne : 1 ≤ Real.exp L := (Real.one_le_exp_iff).2 (by linarith)
    exact hExpOne.trans hPr
  have hRscaled : 2 * R + 1 ≤ 9 * (P ^ r) * Real.rpow L B := by
    have hR' : R ≤ 4 * (P ^ r) * Real.rpow L B := by
      calc
        R ≤ 4 * Real.exp L * Real.rpow L B := hRbound
        _ ≤ 4 * (P ^ r) * Real.rpow L B := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hPr (by norm_num)) (Real.rpow_nonneg hLpos.le _)
    have hprodOne : 1 ≤ (P ^ r) * Real.rpow L B := by
      calc
        1 = 1 * 1 := by ring
        _ ≤ (P ^ r) * Real.rpow L B :=
          mul_le_mul hPrOne hLpowB (by norm_num) (by positivity)
    nlinarith
  have hUscaled : (U : ℝ) * u ≤ (2 : ℝ) ^ r * P ^ r * (cu * Real.rpow L e) := by
    have hmul := mul_le_mul hUbound hu hu0 (by positivity : 0 ≤ (2 * P) ^ r)
    calc
      _ ≤ (2 * P) ^ r * (cu * Real.rpow L e) := hmul
      _ = (2 : ℝ) ^ r * P ^ r * (cu * Real.rpow L e) := by rw [mul_pow]
  have hbracket : 2 * R + 1 + (U : ℝ) * u ≤
      P ^ r * ((9 + cu) * (2 : ℝ) ^ r * Real.rpow L d) := by
    have hfirst : 2 * R + 1 + (U : ℝ) * u ≤
        9 * (P ^ r) * Real.rpow L B +
          (2 : ℝ) ^ r * P ^ r * (cu * Real.rpow L e) :=
      add_le_add hRscaled hUscaled
    have hbase : 9 * Real.rpow L B + (2 : ℝ) ^ r * cu * Real.rpow L e ≤
        (9 + cu) * (2 : ℝ) ^ r * Real.rpow L d := by
      have hpow2 : 1 ≤ (2 : ℝ) ^ r := by exact_mod_cast (Nat.one_le_pow r 2 (by omega))
      calc
        _ ≤ 9 * Real.rpow L d + (2 : ℝ) ^ r * cu * Real.rpow L d := by
          gcongr
        _ ≤ (9 + cu) * (2 : ℝ) ^ r * Real.rpow L d := by
          have hcu : 0 ≤ cu := by dsimp [cu]; positivity
          have hdiff : 0 ≤ (9 + cu) * (2 : ℝ) ^ r - (9 + (2 : ℝ) ^ r * cu) := by
            nlinarith [mul_nonneg (show 0 ≤ (9 : ℝ) + cu by linarith) (sub_nonneg.mpr hpow2)]
          nlinarith [mul_nonneg hdiff (le_trans zero_le_one hLpowD)]
    calc
      _ ≤ 9 * (P ^ r) * Real.rpow L B +
          (2 : ℝ) ^ r * P ^ r * (cu * Real.rpow L e) := hfirst
      _ = (P ^ r) * (9 * Real.rpow L B + (2 : ℝ) ^ r * cu * Real.rpow L e) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hbase (by positivity)
  have hcardPow : Pcard ^ r ≤ (3 * P) ^ r := by gcongr
  have hmassNorm :
      (P ^ r) * (3 * P) ^ r * (1 / P) ^ (2 * r) = (3 : ℝ) ^ r := by
    have h2r : 2 * r = r + r := by omega
    rw [h2r, pow_add, one_div_pow, mul_pow]
    field_simp [ne_of_gt hPpos]
    <;> ring
  have hcombined :
      (2 * R + 1 + (U : ℝ) * u) * Pcard ^ r * (1 / P) ^ (2 * r) ≤
        (9 + cu) * (6 : ℝ) ^ r * Real.rpow L d := by
    have hinvNonneg : 0 ≤ (1 / P) ^ (2 * r) := by positivity
    have hfirst :
        (2 * R + 1 + (U : ℝ) * u) * Pcard ^ r * (1 / P) ^ (2 * r) ≤
          (P ^ r * ((9 + cu) * (2 : ℝ) ^ r * Real.rpow L d)) *
            (3 * P) ^ r * (1 / P) ^ (2 * r) := by
      apply mul_le_mul_of_nonneg_right _ hinvNonneg
      apply mul_le_mul
      · exact hbracket
      · exact hcardPow
      · positivity
      · positivity
    calc
      _ ≤ _ := hfirst
      _ = (9 + cu) * Real.rpow L d *
          ((2 : ℝ) ^ r * ((P ^ r) * (3 * P) ^ r * (1 / P) ^ (2 * r))) := by ring
      _ = (9 + cu) * Real.rpow L d * ((2 : ℝ) ^ r * (3 : ℝ) ^ r) := by rw [hmassNorm]
      _ = (9 + cu) * Real.rpow L d * (6 : ℝ) ^ r := by
        congr 1
        rw [← mul_pow]
        norm_num
      _ = _ := by ring
  have hthresholdInv :
      ((Real.rpow L (-A_s)) ^ (2 * r))⁻¹ = Real.rpow L (2 * A_s * (r : ℝ)) := by
    have hpow : (Real.rpow L (-A_s)) ^ (2 * r) =
        Real.rpow L ((-A_s) * (2 * (r : ℝ))) := by
      rw [← Real.rpow_natCast]
      convert (Real.rpow_mul hLpos.le (-A_s) ((2 * r : ℕ) : ℝ)).symm using 1 <;> simp
    have hneg : Real.rpow L (-(2 * A_s * (r : ℝ))) =
        (Real.rpow L (2 * A_s * (r : ℝ)))⁻¹ :=
      Real.rpow_neg hLpos.le (2 * A_s * (r : ℝ))
    have hexp : (-A_s) * (2 * (r : ℝ)) = -(2 * A_s * (r : ℝ)) := by ring
    have hpow' : (Real.rpow L (-A_s)) ^ (2 * r) =
        Real.rpow L (-(2 * A_s * (r : ℝ))) := by rw [hpow, hexp]
    calc
      _ = (Real.rpow L (-(2 * A_s * (r : ℝ))))⁻¹ := by rw [hpow']
      _ = Real.rpow L (2 * A_s * (r : ℝ)) := by
        have h := congrArg Inv.inv hneg
        simpa using h
  have hfactNat := Nat.factorial_le_pow r
  have hfact : (r.factorial : ℝ) ≤ (r : ℝ) ^ r := by exact_mod_cast hfactNat
  have hfactNonneg : 0 ≤ (r.factorial : ℝ) := by positivity
  have hpowU2 : (Real.rpow L e) ^ 2 = Real.rpow L (11 / 5 : ℝ) := by
    calc
      (Real.rpow L e) ^ 2 = Real.rpow L (e * 2) :=
        (Real.rpow_mul_natCast hLpos.le e 2).symm
      _ = Real.rpow L (11 / 5 : ℝ) := by congr 1 <;> norm_num [e]
  have huSq : u ^ 2 ≤ cu ^ 2 * Real.rpow L (11 / 5 : ℝ) := by
    have hcu0 : 0 ≤ cu := by dsimp [cu]; positivity
    have hM0 : 0 ≤ cu * Real.rpow L e :=
      mul_nonneg hcu0 (Real.rpow_nonneg hLpos.le _)
    have hboundSq : u ^ 2 ≤ (cu * Real.rpow L e) ^ 2 :=
      (sq_le_sq₀ hu0 hM0).2 hu
    calc
      _ ≤ (cu * Real.rpow L e) ^ 2 := hboundSq
      _ = cu ^ 2 * Real.rpow L (11 / 5 : ℝ) := by rw [mul_pow, hpowU2]
  have hK0pos : 0 < K0 := by dsimp [K0, cu]; positivity
  have hK0exp : K0 ≤ Real.exp |Real.log K0| := by
    calc
      K0 = Real.exp (Real.log K0) := (Real.exp_log hK0pos).symm
      _ ≤ Real.exp |Real.log K0| := Real.exp_le_exp.mpr (le_abs_self _)
  have hpolyExp : Real.rpow L m ≤ Real.exp (m * Real.rpow L (1 / 100 : ℝ)) := by
    calc
      Real.rpow L m = Real.exp (Real.log L * m) := Real.rpow_def_of_pos hLpos m
      _ ≤ Real.exp (m * Real.rpow L (1 / 100 : ℝ)) := by
        apply Real.exp_le_exp.mpr
        have hm : 0 ≤ m := by dsimp [m, d, e]; positivity
        calc
          Real.log L * m ≤ Real.rpow L (1 / 100 : ℝ) * m :=
            mul_le_mul_of_nonneg_right hlogL hm
          _ = m * Real.rpow L (1 / 100 : ℝ) := by ring
  have h6Eq : (6 : ℝ) ^ r = Real.exp ((r : ℝ) * Real.log 6) := by
    calc
      _ = (Real.exp (Real.log 6)) ^ r := by rw [Real.exp_log (by norm_num : (0 : ℝ) < 6)]
      _ = _ := by rw [← Real.exp_nat_mul]
  have h6Exp : (6 : ℝ) ^ r ≤ Real.exp (21 * Real.rpow L (91 / 100 : ℝ) * Real.log 6) := by
    rw [h6Eq]
    apply Real.exp_le_exp.mpr
    have hpow : Real.rpow L (9 / 10 : ℝ) ≤ Real.rpow L (91 / 100 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hLge (by norm_num)
    calc
      (r : ℝ) * Real.log 6 ≤ 21 * Real.rpow L (9 / 10 : ℝ) * Real.log 6 :=
        mul_le_mul_of_nonneg_right hr (Real.log_nonneg (by norm_num))
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow (by norm_num)) (Real.log_nonneg (by norm_num))
  have hrPos : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hrLe21L : (r : ℝ) ≤ 21 * L := by
    have hExponent : (9 / 10 : ℝ) ≤ 1 := by norm_num
    have hpow : Real.rpow L (9 / 10 : ℝ) ≤ Real.rpow L 1 :=
      Real.rpow_le_rpow_of_exponent_le hLge hExponent
    calc
      (r : ℝ) ≤ 21 * Real.rpow L (9 / 10 : ℝ) := hr
      _ ≤ 21 * Real.rpow L 1 := mul_le_mul_of_nonneg_left hpow (by norm_num)
      _ = 21 * L := congrArg (fun z : ℝ => 21 * z) (Real.rpow_one L)
  have hlogr : Real.log (r : ℝ) ≤ Real.log 21 + Real.log L := by
    calc
      Real.log (r : ℝ) ≤ Real.log (21 * L) :=
        Real.log_le_log hrPos hrLe21L
      _ = Real.log 21 + Real.log L := Real.log_mul (by norm_num) (ne_of_gt hLpos)
  have hlogrBound : Real.log (r : ℝ) ≤ Real.log 21 + Real.rpow L (1 / 100 : ℝ) := by
    calc
      Real.log (r : ℝ) ≤ Real.log 21 + Real.log L := hlogr
      _ = Real.log L + Real.log 21 := by ring
      _ ≤ Real.rpow L (1 / 100 : ℝ) + Real.log 21 :=
        add_le_add_left hlogL (Real.log 21)
      _ = _ := by ring
  have hlogrNonneg : 0 ≤ Real.log (r : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ r by omega))
  have hrLogExp : (r : ℝ) ^ r = Real.exp ((r : ℝ) * Real.log (r : ℝ)) := by
    calc
      _ = (Real.exp (Real.log (r : ℝ))) ^ r := by rw [Real.exp_log hrPos]
      _ = _ := by rw [← Real.exp_nat_mul]
  have hrExp : (r : ℝ) ^ r ≤
      Real.exp (21 * (Real.log 21 + 1) * Real.rpow L (91 / 100 : ℝ)) := by
    rw [hrLogExp]
    apply Real.exp_le_exp.mpr
    have hpow09 : Real.rpow L (9 / 10 : ℝ) ≤ Real.rpow L (91 / 100 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hLge (by norm_num)
    have hprodPow : Real.rpow L (9 / 10 : ℝ) * Real.rpow L (1 / 100 : ℝ) =
        Real.rpow L (91 / 100 : ℝ) := by
      calc
        _ = Real.rpow L ((9 / 10 : ℝ) + 1 / 100) :=
          (Real.rpow_add hLpos _ _).symm
        _ = Real.rpow L (91 / 100 : ℝ) := by congr 1 <;> norm_num
    calc
      _ ≤ 21 * Real.rpow L (9 / 10 : ℝ) *
          (Real.log 21 + Real.rpow L (1 / 100 : ℝ)) := by
        have hright : 0 ≤ Real.log 21 + Real.rpow L (1 / 100 : ℝ) :=
          add_nonneg (Real.log_nonneg (by norm_num)) (Real.rpow_nonneg hLpos.le _)
        have hleft : 0 ≤ 21 * Real.rpow L (9 / 10 : ℝ) :=
          mul_nonneg (by norm_num) (Real.rpow_nonneg hLpos.le _)
        exact mul_le_mul hr hlogrBound hlogrNonneg hleft
      _ = 21 * (Real.log 21 * Real.rpow L (9 / 10 : ℝ) +
          Real.rpow L (91 / 100 : ℝ)) := by
        calc
          _ = 21 * (Real.log 21 * Real.rpow L (9 / 10 : ℝ) +
              Real.rpow L (9 / 10 : ℝ) * Real.rpow L (1 / 100 : ℝ)) := by ring
          _ = _ := by rw [hprodPow]
      _ ≤ 21 * (Real.log 21 + 1) * Real.rpow L (91 / 100 : ℝ) := by
        have hlog21 : 0 ≤ Real.log 21 := Real.log_nonneg (by norm_num)
        have hpow09 : Real.rpow L (9 / 10 : ℝ) ≤ Real.rpow L (91 / 100 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hLge (by norm_num)
        have hterm : Real.log 21 * Real.rpow L (9 / 10 : ℝ) ≤
            Real.log 21 * Real.rpow L (91 / 100 : ℝ) :=
          mul_le_mul_of_nonneg_left hpow09 hlog21
        have hsum : Real.log 21 * Real.rpow L (9 / 10 : ℝ) +
            Real.rpow L (91 / 100 : ℝ) ≤
              Real.log 21 * Real.rpow L (91 / 100 : ℝ) +
                Real.rpow L (91 / 100 : ℝ) := add_le_add hterm le_rfl
        calc
          _ = 21 * (Real.log 21 * Real.rpow L (9 / 10 : ℝ) +
              Real.rpow L (91 / 100 : ℝ)) := rfl
          _ ≤ 21 * (Real.log 21 * Real.rpow L (91 / 100 : ℝ) +
              Real.rpow L (91 / 100 : ℝ)) := mul_le_mul_of_nonneg_left hsum (by norm_num)
          _ = _ := by ring
  have hthresholdExp : Real.rpow L (2 * A_s * (r : ℝ)) ≤
      Real.exp (42 * A_s * Real.rpow L (91 / 100 : ℝ)) := by
    have hpowProd : Real.rpow L (9 / 10 : ℝ) * Real.rpow L (1 / 100 : ℝ) =
        Real.rpow L (91 / 100 : ℝ) := by
      calc
        _ = Real.rpow L ((9 / 10 : ℝ) + 1 / 100) :=
          (Real.rpow_add hLpos _ _).symm
        _ = Real.rpow L (91 / 100 : ℝ) := by congr 1 <;> norm_num
    have hlogL0 : 0 ≤ Real.log L := Real.log_nonneg hLge
    have hfactor : 2 * A_s * (r : ℝ) ≤
        2 * A_s * (21 * Real.rpow L (9 / 10 : ℝ)) :=
      mul_le_mul_of_nonneg_left hr (by positivity)
    have hAs2 : 0 ≤ 2 * A_s := by positivity
    have hpow09Nonneg : 0 ≤ Real.rpow L (9 / 10 : ℝ) :=
      Real.rpow_nonneg hLpos.le _
    have hcoef0 : 0 ≤ 2 * A_s * (21 * Real.rpow L (9 / 10 : ℝ)) :=
      mul_nonneg hAs2 (mul_nonneg (by norm_num) hpow09Nonneg)
    have hscaled : Real.log L * (2 * A_s * (r : ℝ)) ≤
        (2 * A_s * (21 * Real.rpow L (9 / 10 : ℝ))) *
          Real.rpow L (1 / 100 : ℝ) := by
      calc
        _ ≤ Real.log L * (2 * A_s * (21 * Real.rpow L (9 / 10 : ℝ))) :=
          mul_le_mul_of_nonneg_left hfactor hlogL0
        _ ≤ Real.rpow L (1 / 100 : ℝ) *
            (2 * A_s * (21 * Real.rpow L (9 / 10 : ℝ))) :=
          mul_le_mul_of_nonneg_right hlogL hcoef0
        _ = _ := by ring
    calc
      Real.rpow L (2 * A_s * (r : ℝ)) =
          Real.exp (Real.log L * (2 * A_s * (r : ℝ))) :=
        Real.rpow_def_of_pos hLpos (2 * A_s * (r : ℝ))
      _ ≤ Real.exp ((2 * A_s * (21 * Real.rpow L (9 / 10 : ℝ))) *
          Real.rpow L (1 / 100 : ℝ)) := Real.exp_le_exp.mpr hscaled
      _ = Real.exp (42 * A_s * Real.rpow L (91 / 100 : ℝ)) := by
        congr 1
        calc
          (2 * A_s * (21 * Real.rpow L (9 / 10 : ℝ))) *
              Real.rpow L (1 / 100 : ℝ) =
            42 * A_s * (Real.rpow L (9 / 10 : ℝ) *
              Real.rpow L (1 / 100 : ℝ)) := by ring
          _ = _ := by rw [hpowProd]
  have hpolyPow : Real.rpow L (1 / 100 : ℝ) ≤ Real.rpow L (91 / 100 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hLge (by norm_num)
  have hconstantPow : 1 ≤ Real.rpow L (91 / 100 : ℝ) :=
    Real.one_le_rpow hLge (by norm_num)
  have hsumExponent :
      |Real.log K0| + m * Real.rpow L (1 / 100 : ℝ) +
        21 * Real.rpow L (91 / 100 : ℝ) * Real.log 6 +
        21 * (Real.log 21 + 1) * Real.rpow L (91 / 100 : ℝ) +
        42 * A_s * Real.rpow L (91 / 100 : ℝ) ≤
      c * Real.rpow L (91 / 100 : ℝ) := by
    have hm : 0 ≤ m := by dsimp [m, d]; positivity
    have hconst : |Real.log K0| ≤ |Real.log K0| * Real.rpow L (91 / 100 : ℝ) := by
      calc
        |Real.log K0| = |Real.log K0| * 1 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hconstantPow (abs_nonneg _)
    have hpoly : m * Real.rpow L (1 / 100 : ℝ) ≤
        m * Real.rpow L (91 / 100 : ℝ) :=
      mul_le_mul_of_nonneg_left hpolyPow hm
    have hRest :
        21 * Real.rpow L (91 / 100 : ℝ) * Real.log 6 +
          21 * (Real.log 21 + 1) * Real.rpow L (91 / 100 : ℝ) +
          42 * A_s * Real.rpow L (91 / 100 : ℝ) =
        21 * (Real.log 6 + Real.log 21 + 1 + 2 * A_s) *
          Real.rpow L (91 / 100 : ℝ) := by ring
    have hpowNonneg : 0 ≤ Real.rpow L (91 / 100 : ℝ) :=
      Real.rpow_nonneg hLpos.le _
    calc
      _ = (|Real.log K0| + m * Real.rpow L (1 / 100 : ℝ)) +
          (21 * Real.rpow L (91 / 100 : ℝ) * Real.log 6 +
            21 * (Real.log 21 + 1) * Real.rpow L (91 / 100 : ℝ) +
            42 * A_s * Real.rpow L (91 / 100 : ℝ)) := by ring
      _ ≤ (|Real.log K0| * Real.rpow L (91 / 100 : ℝ) +
          m * Real.rpow L (91 / 100 : ℝ)) +
          (21 * Real.rpow L (91 / 100 : ℝ) * Real.log 6 +
            21 * (Real.log 21 + 1) * Real.rpow L (91 / 100 : ℝ) +
            42 * A_s * Real.rpow L (91 / 100 : ℝ)) :=
        add_le_add (add_le_add hconst hpoly) le_rfl
      _ ≤ (|Real.log K0| * Real.rpow L (91 / 100 : ℝ) +
          m * Real.rpow L (91 / 100 : ℝ)) +
          (21 * Real.rpow L (91 / 100 : ℝ) * Real.log 6 +
            21 * (Real.log 21 + 1) * Real.rpow L (91 / 100 : ℝ) +
            42 * A_s * Real.rpow L (91 / 100 : ℝ)) +
            Real.rpow L (91 / 100 : ℝ) := le_add_of_nonneg_right hpowNonneg
      _ = (|Real.log K0| * Real.rpow L (91 / 100 : ℝ) +
          m * Real.rpow L (91 / 100 : ℝ)) +
          ((21 * Real.rpow L (91 / 100 : ℝ) * Real.log 6 +
            21 * (Real.log 21 + 1) * Real.rpow L (91 / 100 : ℝ) +
            42 * A_s * Real.rpow L (91 / 100 : ℝ)) +
            Real.rpow L (91 / 100 : ℝ)) := by ring
      _ = (|Real.log K0| * Real.rpow L (91 / 100 : ℝ) +
          m * Real.rpow L (91 / 100 : ℝ)) +
          (21 * (Real.log 6 + Real.log 21 + 1 + 2 * A_s) *
            Real.rpow L (91 / 100 : ℝ) + Real.rpow L (91 / 100 : ℝ)) := by rw [hRest]
      _ = c * Real.rpow L (91 / 100 : ℝ) := by dsimp [c]; ring
  have hmain :
      2 * Cmv * (2 * R + 1 + (U : ℝ) * u) * u ^ 2 *
          (r.factorial : ℝ) * Pcard ^ r * (1 / P) ^ (2 * r) /
            (Real.rpow L (-A_s)) ^ (2 * r) ≤
        K0 * (6 : ℝ) ^ r * (r : ℝ) ^ r * Real.rpow L m *
          Real.rpow L (2 * A_s * (r : ℝ)) := by
    have hUpperMass : 0 ≤ (9 + cu) * (6 : ℝ) ^ r * Real.rpow L d := by
      have hco : 0 ≤ 9 + cu := by positivity
      have h6 : 0 ≤ (6 : ℝ) ^ r := pow_nonneg (by norm_num) _
      have hLd : 0 ≤ Real.rpow L d := Real.rpow_nonneg hLpos.le d
      exact mul_nonneg (mul_nonneg hco h6) hLd
    have hUpperU : 0 ≤ cu ^ 2 * Real.rpow L (11 / 5 : ℝ) :=
      mul_nonneg (sq_nonneg cu) (Real.rpow_nonneg hLpos.le _)
    have hTail : 0 ≤ Real.rpow L (2 * A_s * (r : ℝ)) :=
      Real.rpow_nonneg hLpos.le _
    have hPowAdd : Real.rpow L d * Real.rpow L (11 / 5 : ℝ) =
        Real.rpow L (d + 11 / 5 : ℝ) := (Real.rpow_add hLpos d (11 / 5 : ℝ)).symm
    calc
      _ = 2 * Cmv * ((2 * R + 1 + (U : ℝ) * u) * Pcard ^ r *
          (1 / P) ^ (2 * r)) * u ^ 2 * (r.factorial : ℝ) *
          Real.rpow L (2 * A_s * (r : ℝ)) := by rw [div_eq_mul_inv, hthresholdInv]; ring
      _ ≤ 2 * Cmv * ((9 + cu) * (6 : ℝ) ^ r * Real.rpow L d) *
          u ^ 2 * (r.factorial : ℝ) * Real.rpow L (2 * A_s * (r : ℝ)) := by
        have hcoef : 0 ≤ 2 * Cmv := by positivity
        have htail₁ : 0 ≤ u ^ 2 * (r.factorial : ℝ) *
            Real.rpow L (2 * A_s * (r : ℝ)) :=
          mul_nonneg (mul_nonneg (sq_nonneg u) hfactNonneg) hTail
        simpa [mul_assoc] using mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcombined hcoef) htail₁
      _ ≤ 2 * Cmv * ((9 + cu) * (6 : ℝ) ^ r * Real.rpow L d) *
          (cu ^ 2 * Real.rpow L (11 / 5 : ℝ)) * (r.factorial : ℝ) *
            Real.rpow L (2 * A_s * (r : ℝ)) := by
        have hcoef : 0 ≤ 2 * Cmv * ((9 + cu) * (6 : ℝ) ^ r * Real.rpow L d) :=
          mul_nonneg (by positivity) hUpperMass
        have htail₁ : 0 ≤ (r.factorial : ℝ) * Real.rpow L (2 * A_s * (r : ℝ)) :=
          mul_nonneg hfactNonneg hTail
        simpa [mul_assoc] using mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left huSq hcoef) htail₁
      _ ≤ 2 * Cmv * ((9 + cu) * (6 : ℝ) ^ r * Real.rpow L d) *
          (cu ^ 2 * Real.rpow L (11 / 5 : ℝ)) * (r : ℝ) ^ r *
            Real.rpow L (2 * A_s * (r : ℝ)) := by
        have hcoef : 0 ≤ 2 * Cmv * ((9 + cu) * (6 : ℝ) ^ r * Real.rpow L d) *
            (cu ^ 2 * Real.rpow L (11 / 5 : ℝ)) := by positivity
        simpa [mul_assoc] using mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hfact hcoef) hTail
      _ = 2 * Cmv * (9 + cu) * cu ^ 2 * (6 : ℝ) ^ r * (r : ℝ) ^ r *
          (Real.rpow L d * Real.rpow L (11 / 5 : ℝ)) *
          Real.rpow L (2 * A_s * (r : ℝ)) := by ring
      _ = 2 * Cmv * (9 + cu) * cu ^ 2 * (6 : ℝ) ^ r * (r : ℝ) ^ r *
          Real.rpow L (d + 11 / 5 : ℝ) * Real.rpow L (2 * A_s * (r : ℝ)) := by
        rw [hPowAdd]
      _ = _ := by dsimp [K0, m]
  have hK0Bound : K0 ≤ Real.exp |Real.log K0| := hK0exp
  have htotal :
      K0 * (6 : ℝ) ^ r * (r : ℝ) ^ r * Real.rpow L m *
          Real.rpow L (2 * A_s * (r : ℝ)) ≤
        Real.exp (c * Real.rpow L (91 / 100 : ℝ)) := by
    have h6Nonneg : 0 ≤ (6 : ℝ) ^ r := pow_nonneg (by norm_num) _
    have hrNonneg : 0 ≤ (r : ℝ) ^ r := pow_nonneg (Nat.cast_nonneg _) _
    have hLmNonneg : 0 ≤ Real.rpow L m := Real.rpow_nonneg hLpos.le _
    have hTailTotal : 0 ≤ Real.rpow L (2 * A_s * (r : ℝ)) :=
      Real.rpow_nonneg hLpos.le _
    have hLmTailNonneg : 0 ≤ Real.rpow L m * Real.rpow L (2 * A_s * (r : ℝ)) :=
      mul_nonneg hLmNonneg hTailTotal
    have hrLmTailNonneg : 0 ≤ (r : ℝ) ^ r *
        (Real.rpow L m * Real.rpow L (2 * A_s * (r : ℝ))) :=
      mul_nonneg hrNonneg hLmTailNonneg
    calc
      _ = K0 * ((6 : ℝ) ^ r *
          ((r : ℝ) ^ r * (Real.rpow L m *
            Real.rpow L (2 * A_s * (r : ℝ))))) := by ring
      _ ≤ Real.exp |Real.log K0| * ((6 : ℝ) ^ r *
          ((r : ℝ) ^ r * (Real.rpow L m *
            Real.rpow L (2 * A_s * (r : ℝ))))) :=
        mul_le_mul_of_nonneg_right hK0Bound
          (mul_nonneg h6Nonneg hrLmTailNonneg)
      _ ≤ Real.exp |Real.log K0| * (Real.exp
          (21 * Real.rpow L (91 / 100 : ℝ) * Real.log 6) *
          ((r : ℝ) ^ r * (Real.rpow L m *
            Real.rpow L (2 * A_s * (r : ℝ))))) := by
        apply mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right h6Exp hrLmTailNonneg)
        exact (Real.exp_pos _).le
      _ ≤ Real.exp |Real.log K0| * (Real.exp
          (21 * Real.rpow L (91 / 100 : ℝ) * Real.log 6) *
          (Real.exp (21 * (Real.log 21 + 1) * Real.rpow L (91 / 100 : ℝ)) *
            (Real.rpow L m * Real.rpow L (2 * A_s * (r : ℝ))))) := by
        apply mul_le_mul_of_nonneg_left
        · apply mul_le_mul_of_nonneg_left
          · exact mul_le_mul_of_nonneg_right hrExp
              (mul_nonneg hLmNonneg hTailTotal)
          · exact (Real.exp_pos _).le
        · exact (Real.exp_pos _).le
      _ ≤ Real.exp |Real.log K0| * (Real.exp
          (21 * Real.rpow L (91 / 100 : ℝ) * Real.log 6) *
          (Real.exp (21 * (Real.log 21 + 1) * Real.rpow L (91 / 100 : ℝ)) *
            (Real.exp (m * Real.rpow L (1 / 100 : ℝ)) *
              Real.rpow L (2 * A_s * (r : ℝ))))) := by
        apply mul_le_mul_of_nonneg_left
        · apply mul_le_mul_of_nonneg_left
          · exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hpolyExp hTailTotal)
              (Real.exp_nonneg _)
          · exact (Real.exp_pos _).le
        · exact (Real.exp_pos _).le
      _ ≤ Real.exp |Real.log K0| * (Real.exp
          (21 * Real.rpow L (91 / 100 : ℝ) * Real.log 6) *
          (Real.exp (21 * (Real.log 21 + 1) * Real.rpow L (91 / 100 : ℝ)) *
            (Real.exp (m * Real.rpow L (1 / 100 : ℝ)) *
              Real.exp (42 * A_s * Real.rpow L (91 / 100 : ℝ))))) := by
        apply mul_le_mul_of_nonneg_left
        · apply mul_le_mul_of_nonneg_left
          · apply mul_le_mul_of_nonneg_left
            · exact mul_le_mul_of_nonneg_left hthresholdExp
                (Real.exp_nonneg _)
            · exact (Real.exp_pos _).le
          · exact (Real.exp_pos _).le
        · exact (Real.exp_pos _).le
      _ = Real.exp (|Real.log K0| + m * Real.rpow L (1 / 100 : ℝ) +
          21 * Real.rpow L (91 / 100 : ℝ) * Real.log 6 +
          21 * (Real.log 21 + 1) * Real.rpow L (91 / 100 : ℝ) +
          42 * A_s * Real.rpow L (91 / 100 : ℝ)) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        ring_nf
      _ ≤ _ := Real.exp_le_exp.mpr hsumExponent
  have hcEq : c = pd7_sparse_moment_count_constant B A_s C₁ Cmv := by
    dsimp [c, K0, cu, m, d, e, pd7_sparse_moment_count_constant]
  constructor
  · dsimp [pd7_sparse_moment_count_constant]
    positivity
  · have hbound := hmain.trans htotal
    rw [hcEq] at hbound
    simpa [u] using hbound

end ArtinPrimitiveRoots.TypeII.PD
