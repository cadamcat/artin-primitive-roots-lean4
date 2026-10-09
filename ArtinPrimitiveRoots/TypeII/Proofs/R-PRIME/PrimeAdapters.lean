import ArtinPrimitiveRoots.TypeII.Marked
import ArtinPrimitiveRoots.TypeII.PP.Results
import Mathlib.NumberTheory.Harmonic.Bounds

namespace ArtinPrimitiveRoots.Proofs.RImplP.RPrime

open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.TypeII.PP

set_option maxHeartbeats 1000000 in
theorem norm_sum_range_nat_mul_le
    (U : ℕ) (g : ℕ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hprefix : ∀ k ≤ U, ‖∑ n ∈ Finset.range k, g n‖ ≤ B) :
    ‖∑ n ∈ Finset.range U, (n : ℂ) * g n‖ ≤ 2 * (U : ℝ) * B := by
  cases U with
  | zero => simp
  | succ n =>
    have hAbel :
        (∑ i ∈ Finset.range (n + 1), (i : ℂ) * g i) =
          (n : ℂ) * (∑ i ∈ Finset.range (n + 1), g i) -
            ∑ i ∈ Finset.range n,
              (((i + 1 : ℂ) - (i : ℂ)) * ∑ j ∈ Finset.range (i + 1), g j) := by
      simpa [smul_eq_mul] using
        (Finset.sum_range_by_parts (fun i : ℕ => (i : ℂ)) g (n + 1))
    have hboundary :
        ‖(n : ℂ) * (∑ i ∈ Finset.range (n + 1), g i)‖ ≤ (n : ℝ) * B := by
      rw [norm_mul]
      have hcast : ‖(n : ℂ)‖ = (n : ℝ) := by simp
      rw [hcast]
      exact mul_le_mul_of_nonneg_left (hprefix (n + 1) le_rfl) (by positivity)
    have hvariation :
        ‖∑ i ∈ Finset.range n,
            (((i + 1 : ℂ) - (i : ℂ)) * ∑ j ∈ Finset.range (i + 1), g j)‖ ≤
          (n : ℝ) * B := by
      calc
        _ ≤ ∑ i ∈ Finset.range n,
            ‖((i + 1 : ℂ) - (i : ℂ)) * ∑ j ∈ Finset.range (i + 1), g j‖ := norm_sum_le _ _
        _ ≤ ∑ _i ∈ Finset.range n, B := by
          apply Finset.sum_le_sum
          intro i hi
          have hik : i + 1 ≤ n + 1 := Nat.succ_le_succ (Nat.le_of_lt (Finset.mem_range.mp hi))
          have hp := hprefix (i + 1) hik
          simpa using hp
        _ = (n : ℝ) * B := by simp
    have hnorm :
        ‖∑ i ∈ Finset.range (n + 1), (i : ℂ) * g i‖ ≤
          (n : ℝ) * B + (n : ℝ) * B := by
      rw [hAbel]
      exact (norm_sub_le _ _).trans (add_le_add hboundary hvariation)
    have hstep : 2 * (n : ℝ) * B ≤ 2 * ((n : ℝ) + 1) * B := by
      have hn : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
      nlinarith [hB, hn]
    have hbound : ‖∑ i ∈ Finset.range (n + 1), (i : ℂ) * g i‖ ≤
        2 * ((n : ℝ) + 1) * B := by nlinarith [hnorm, hstep]
    simpa [Nat.cast_succ] using hbound

private theorem prime_phase_weight_identity
    (p q : ℕ) (hp : p.Prime) (χ : DirichletCharacter ℂ q) (t : ℝ) :
    (p : ℂ) * (χ (p : ZMod q) : ℂ) *
        Complex.exp ((-1 + Complex.I * t) * Real.log (p : ℝ)) =
      (χ (p : ZMod q) : ℂ) * Complex.exp (Complex.I * t * Real.log (p : ℝ)) := by
  have hpReal : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hneg : Complex.exp (-(Real.log (p : ℝ) : ℂ)) = (p : ℂ)⁻¹ := by
    rw [← Complex.ofReal_neg]
    rw [← Complex.ofReal_exp, Real.exp_neg, Real.exp_log hpReal]
    simp
  have hphase : Complex.exp ((-1 + Complex.I * t) * Real.log (p : ℝ)) =
      (p : ℂ)⁻¹ * Complex.exp (Complex.I * t * Real.log (p : ℝ)) := by
    calc
      Complex.exp ((-1 + Complex.I * t) * Real.log (p : ℝ)) =
          Complex.exp (-(Real.log (p : ℝ) : ℂ) + Complex.I * t * Real.log (p : ℝ)) := by
            congr 1
            push_cast
            ring
      _ = Complex.exp (-(Real.log (p : ℝ) : ℂ)) *
          Complex.exp (Complex.I * t * Real.log (p : ℝ)) := by rw [Complex.exp_add]
      _ = (p : ℂ)⁻¹ * Complex.exp (Complex.I * t * Real.log (p : ℝ)) := by rw [hneg]
  calc
    (p : ℂ) * (χ (p : ZMod q) : ℂ) *
        Complex.exp ((-1 + Complex.I * t) * Real.log (p : ℝ)) =
      (p : ℂ) * (χ (p : ZMod q) : ℂ) *
        ((p : ℂ)⁻¹ * Complex.exp (Complex.I * t * Real.log (p : ℝ))) := by rw [hphase]
    _ = (χ (p : ZMod q) : ℂ) * Complex.exp (Complex.I * t * Real.log (p : ℝ)) := by
      calc
        (p : ℂ) * (χ (p : ZMod q) : ℂ) *
            ((p : ℂ)⁻¹ * Complex.exp (Complex.I * t * Real.log (p : ℝ))) =
          ((p : ℂ) * (p : ℂ)⁻¹) * (χ (p : ZMod q) : ℂ) *
            Complex.exp (Complex.I * t * Real.log (p : ℝ)) := by ring
        _ = (χ (p : ZMod q) : ℂ) * Complex.exp (Complex.I * t * Real.log (p : ℝ)) := by
          simp [hpC]

set_option maxHeartbeats 1000000 in
theorem prime_phase_sum_bound_of_weighted_interval
    (N : ℝ) (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ) (I : Set ℕ)
    (B : ℝ) (hN : 1 ≤ N) (hB : 0 ≤ B)
    (hIinterval : IsNatInterval I)
    (hI : I ⊆ {p : ℕ | N ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * N})
    (hweighted : ∀ J : Set ℕ, IsNatInterval J →
      J ⊆ {p : ℕ | N ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * N} →
        ‖PP.primeDirichletPolynomial N q χ t J‖ ≤ B) :
    ‖PP.primePhaseSum N q χ t I‖ ≤ 6 * N * B := by
  classical
  let U : ℕ := ⌊2 * N⌋₊ + 1
  let cond : ℕ → Prop := fun p => p.Prime ∧ N ≤ (p : ℝ) ∧
    (p : ℝ) ≤ 2 * N ∧ p ∈ I
  let weight : ℕ → ℂ := fun p =>
    if cond p then (χ (p : ZMod q) : ℂ) *
      Complex.exp ((-1 + Complex.I * t) * Real.log (p : ℝ)) else 0
  let Sphase : Finset ℕ := (Finset.range U).filter cond
  have hphaseSet : PP.primePhaseSum N q χ t I =
      ∑ p ∈ Sphase, (χ (p : ZMod q) : ℂ) *
        Complex.exp (Complex.I * t * Real.log (p : ℝ)) := by
    rfl
  have hweightedSum :
      (∑ p ∈ Finset.range U, (p : ℂ) * weight p) =
        ∑ p ∈ Sphase, (χ (p : ZMod q) : ℂ) *
          Complex.exp (Complex.I * t * Real.log (p : ℝ)) := by
    dsimp [weight, Sphase, cond]
    simp only [mul_ite, mul_zero]
    rw [← Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨_, hpcond⟩
    simpa [mul_assoc] using prime_phase_weight_identity p q hpcond.1 χ t
  have hprefix : ∀ k ≤ U, ‖∑ p ∈ Finset.range k, weight p‖ ≤ B := by
    intro k hk
    let Ik : Set ℕ := {p | p ∈ I ∧ p < k}
    let Sleft : Finset ℕ := (Finset.range k).filter cond
    let Sright : Finset ℕ := (Finset.range U).filter fun p =>
      p.Prime ∧ N ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * N ∧ p ∈ Ik
    have hIkInterval : IsNatInterval Ik := by
      intro m n j hm hn hjmin hjmax
      rcases hm with ⟨hmI, hmk⟩
      rcases hn with ⟨hnI, hnk⟩
      refine ⟨hIinterval hmI hnI hjmin hjmax, ?_⟩
      have hmax : max m n < k := max_lt_iff.mpr ⟨hmk, hnk⟩
      exact lt_of_le_of_lt hjmax hmax
    have hIk : Ik ⊆ {p : ℕ | N ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * N} := by
      intro p hp
      exact hI hp.1
    have hsets : Sleft = Sright := by
      apply Finset.ext
      intro p
      simp only [Sleft, Sright, Ik, Finset.mem_filter, Finset.mem_range,
        Set.mem_setOf_eq, cond]
      constructor
      · rintro ⟨hpk, hp, hlo, hhi, hI'⟩
        exact ⟨Nat.lt_of_lt_of_le hpk hk, hp, hlo, hhi, hI', hpk⟩
      · rintro ⟨hpU, hp, hlo, hhi, hI', hpk⟩
        exact ⟨hpk, hp, hlo, hhi, hI'⟩
    have hleft : (∑ p ∈ Finset.range k, weight p) =
        ∑ p ∈ Sleft, (χ (p : ZMod q) : ℂ) *
          Complex.exp ((-1 + Complex.I * t) * Real.log (p : ℝ)) := by
      dsimp [weight, Sleft, cond]
      rw [← Finset.sum_filter]
    have hright : PP.primeDirichletPolynomial N q χ t Ik =
        ∑ p ∈ Sright, (χ (p : ZMod q) : ℂ) *
          Complex.exp ((-1 + Complex.I * t) * Real.log (p : ℝ)) := by
      unfold PP.primeDirichletPolynomial
      dsimp [Sright, U]
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p hp
      simp
    have hprefixEq : (∑ p ∈ Finset.range k, weight p) =
        PP.primeDirichletPolynomial N q χ t Ik := by
      calc
        _ = ∑ p ∈ Sleft, (χ (p : ZMod q) : ℂ) *
            Complex.exp ((-1 + Complex.I * t) * Real.log (p : ℝ)) := hleft
        _ = ∑ p ∈ Sright, (χ (p : ZMod q) : ℂ) *
            Complex.exp ((-1 + Complex.I * t) * Real.log (p : ℝ)) := by rw [hsets]
        _ = PP.primeDirichletPolynomial N q χ t Ik := hright.symm
    rw [hprefixEq]
    exact hweighted Ik hIkInterval hIk
  have hAbel := norm_sum_range_nat_mul_le U weight B hB hprefix
  have hfloor : (⌊2 * N⌋₊ : ℝ) ≤ 2 * N := Nat.floor_le (by positivity)
  have hU : (U : ℝ) ≤ 3 * N := by
    dsimp [U]
    push_cast
    nlinarith [hfloor, hN]
  calc
    ‖PP.primePhaseSum N q χ t I‖ =
        ‖∑ p ∈ Finset.range U, (p : ℂ) * weight p‖ := by rw [hphaseSet, ← hweightedSum]
    _ ≤ 2 * (U : ℝ) * B := hAbel
    _ = (U : ℝ) * (2 * B) := by ring
    _ ≤ (3 * N) * (2 * B) := mul_le_mul_of_nonneg_right hU (by positivity)
    _ = 6 * N * B := by ring

set_option maxHeartbeats 1000000 in
theorem prime_phase_sum_bound
    (τ η A₀ A : ℝ) (hτ : 0 < τ) (hτη : τ < η) (hη : η < 1)
    (hA₀ : 0 < A₀) (hA : 0 < A) :
    ∃ B₀ C₀ x₀ : ℝ, 0 < B₀ ∧ 0 < C₀ ∧ 2 < x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        ∀ N : ℝ, Real.rpow x τ / 2 ≤ N → N ≤ Real.rpow x η →
          ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.rpow (Real.log x) A₀ →
            ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
              Real.rpow (Real.log x) B₀ ≤ |t| → |t| ≤ Real.rpow x 2 →
                ∀ I : Set ℕ, IsNatInterval I →
                  I ⊆ {p : ℕ | N ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * N} →
                    ‖PP.primePhaseSum N q χ t I‖ ≤
                      6 * N * C₀ * Real.rpow (Real.log x) (-A) := by
  obtain ⟨B₀, C₀, x₀, hB₀, hC₀, hx₀, hpoly⟩ :=
    PP.prime_polynomial τ η A₀ A hτ hτη hη hA₀ hA
  have hpowLim : Filter.Tendsto (fun x : ℝ => Real.rpow x τ)
      Filter.atTop Filter.atTop := tendsto_rpow_atTop hτ
  obtain ⟨xτ, hxτ⟩ := Filter.eventually_atTop.mp
    (hpowLim.eventually_ge_atTop (2 : ℝ))
  let x₀' := max x₀ (max 2 xτ)
  have hx₀' : 2 < x₀' := lt_of_lt_of_le hx₀ (le_max_left _ _)
  refine ⟨B₀, C₀, x₀', hB₀, hC₀, hx₀', ?_⟩
  intro x hx N hNlo hNhi q hq hqle χ t htlo hthi I hIinterval hI
  have hxold : x₀ ≤ x := le_trans (le_max_left x₀ (max 2 xτ)) hx
  have hxtau : xτ ≤ x :=
    (le_max_right 2 xτ).trans ((le_max_right x₀ (max 2 xτ)).trans hx)
  have hpowLarge : 2 ≤ Real.rpow x τ := hxτ x hxtau
  have hweighted : ∀ J : Set ℕ, IsNatInterval J →
      J ⊆ {p : ℕ | N ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * N} →
        ‖PP.primeDirichletPolynomial N q χ t J‖ ≤
          C₀ * Real.rpow (Real.log x) (-A) := by
    intro J hJinterval hJ
    exact hpoly x hxold N hNlo hNhi q hq hqle χ t htlo hthi J hJinterval hJ
  have hNpos : 0 < N := by
    have : 0 < Real.rpow x τ := Real.rpow_pos_of_pos (by linarith : 0 < x) τ
    exact lt_of_lt_of_le (div_pos this (by norm_num)) hNlo
  have hNone : 1 ≤ N := by nlinarith [hNlo, hpowLarge]
  have hLpos : 0 < Real.log x := Real.log_pos (by linarith : 1 < x)
  have hrpow : 0 < Real.rpow (Real.log x) (-A) := Real.rpow_pos_of_pos hLpos _
  have hB : 0 ≤ C₀ * Real.rpow (Real.log x) (-A) := mul_nonneg hC₀.le hrpow.le
  calc
    ‖PP.primePhaseSum N q χ t I‖ ≤
        6 * N * (C₀ * Real.rpow (Real.log x) (-A)) :=
      prime_phase_sum_bound_of_weighted_interval N q χ t I
        (C₀ * Real.rpow (Real.log x) (-A)) hNone hB hIinterval hI hweighted
    _ = 6 * N * C₀ * Real.rpow (Real.log x) (-A) := by ring


/-- Reciprocal mass of prime tuples is bounded by a power of the harmonic sum. -/
theorem primeTuple_reciprocal_sum_le_harmonic
    (n B : ℕ) (Y : ℝ) :
    (∑ s ∈ (boundedTuples n B).filter
        (fun s => ∀ i, (s i).Prime ∧ Y < (s i : ℝ)),
      1 / (∏ i : Fin n, (s i : ℝ))) ≤ (harmonic B : ℝ) ^ n := by
  classical
  let f : ℕ → ℝ := fun p => if p = 0 then 0 else 1 / (p : ℝ)
  let P : Finset (Fin n → ℕ) :=
    (boundedTuples n B).filter (fun s => ∀ i, (s i).Prime ∧ Y < (s i : ℝ))
  let Q : Finset (Fin n → ℕ) := Fintype.piFinset (fun _ : Fin n => Finset.Icc 0 B)
  have hsubset : P ⊆ Q := by
    intro s hs
    rw [Fintype.mem_piFinset]
    intro i
    have hi : s ∈ boundedTuples n B := (Finset.mem_filter.mp hs).1
    change s ∈ (Finset.univ : Finset (Fin n → Fin (B + 1))).image
      (fun v i => (v i : ℕ)) at hi
    rcases Finset.mem_image.mp hi with ⟨v, _, rfl⟩
    simp only [Finset.mem_Icc]
    exact ⟨Nat.zero_le _, by omega⟩
  have hsingle : (∑ p ∈ Finset.Icc 0 B, f p) = (harmonic B : ℝ) := by
    have hIcc : Finset.Icc 0 B = insert 0 (Finset.Icc 1 B) := by
      ext p
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hIcc, Finset.sum_insert (by simp)]
    simp only [f, if_pos rfl, zero_add]
    have hsum : (∑ p ∈ Finset.Icc 1 B, if p = 0 then 0 else 1 / (p : ℝ)) =
        ∑ p ∈ Finset.Icc 1 B, (p : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro p hp
      have hp0 : 0 < p := (Finset.mem_Icc.mp hp).1
      simp [hp0.ne']
    rw [hsum]
    have hrat := harmonic_eq_sum_Icc (n := B)
    have hcast := congrArg (fun q : ℚ => (q : ℝ)) hrat
    simpa only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using hcast.symm
  have hall : (∑ s ∈ Q, ∏ i : Fin n, f (s i)) =
      (harmonic B : ℝ) ^ n := by
    dsimp [Q]
    rw [← Finset.sum_pow']
    rw [hsingle]
  calc
    _ = ∑ s ∈ P, ∏ i : Fin n, f (s i) := by
      apply Finset.sum_congr rfl
      intro s hs
      have hs' := (Finset.mem_filter.mp hs).2
      have hpne : ∀ i : Fin n, (s i : ℝ) ≠ 0 := by
        intro i
        exact_mod_cast (hs' i).1.ne_zero
      have hprod : (∏ i : Fin n, (s i : ℝ)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun i hi => hpne i)
      have hinv : (∏ i : Fin n, (s i : ℝ))⁻¹ =
          ∏ i : Fin n, (s i : ℝ)⁻¹ := by rw [Finset.prod_inv_distrib]
      rw [one_div, hinv]
      apply Finset.prod_congr rfl
      intro i hi
      simp [f, (hs' i).1.ne_zero]
    _ ≤ ∑ s ∈ Q, ∏ i : Fin n, f (s i) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro s hs hsq
      apply Finset.prod_nonneg
      intro i hi
      dsimp [f]
      split_ifs <;> positivity
    _ = (harmonic B : ℝ) ^ n := hall


private theorem boundedTuples_mem_of_forall_le {n B : ℕ} (t : Fin n → ℕ)
    (ht : ∀ i, t i ≤ B) : t ∈ boundedTuples n B := by
  unfold boundedTuples
  refine Finset.mem_image.mpr ⟨fun i => ⟨t i, Nat.lt_succ_of_le (ht i)⟩,
    Finset.mem_univ _, ?_⟩
  funext i
  rfl

private theorem boundedTuples_coordinate_le {n B : ℕ} (t : Fin n → ℕ)
    (ht : t ∈ boundedTuples n B) (i : Fin n) : t i ≤ B := by
  change t ∈ (Finset.univ : Finset (Fin n → Fin (B + 1))).image
    (fun v i => (v i : ℕ)) at ht
  rcases Finset.mem_image.mp ht with ⟨v, _, rfl⟩
  have h := (v i).isLt
  exact Nat.le_of_lt_succ h

/-- Reindex bounded ordered tuples by their first coordinate and their tail. -/
theorem boundedTuples_cons_sum {n B : ℕ}
    (F : (Fin (n + 1) → ℕ) → ℂ) :
    (∑ t ∈ boundedTuples (n + 1) B, F t) =
      ∑ p ∈ Finset.range (B + 1),
        ∑ s ∈ boundedTuples n B, F (Fin.cons p s) := by
  classical
  let target : Finset (ℕ × (Fin n → ℕ)) :=
    (Finset.range (B + 1)).product (boundedTuples n B)
  let split : (Fin (n + 1) → ℕ) → ℕ × (Fin n → ℕ) :=
    fun t => (t 0, fun i => t i.succ)
  have hsum :
      (∑ z ∈ target, F (Fin.cons z.1 z.2)) =
        ∑ p ∈ Finset.range (B + 1),
          ∑ s ∈ boundedTuples n B, F (Fin.cons p s) := by
    dsimp [target]
    rw [Finset.sum_product]
  rw [← hsum]
  apply Finset.sum_bij (fun t _ => split t)
  · intro t ht
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_range.mpr
      change t 0 < B + 1
      have hp := boundedTuples_coordinate_le t ht 0
      omega
    · apply boundedTuples_mem_of_forall_le
      intro i
      exact boundedTuples_coordinate_le t ht i.succ
  · intro t ht u hu htu
    have h0 : t 0 = u 0 := congrArg Prod.fst htu
    have hs : ∀ i : Fin n, t i.succ = u i.succ := fun i => congrArg (fun z => z.2 i) htu
    funext i
    refine Fin.cases ?_ ?_ i
    · exact h0
    · intro i
      exact hs i
  · intro z hz
    rcases Finset.mem_product.mp hz with ⟨hp, hs⟩
    rcases z with ⟨p, s⟩
    have hpB : p ≤ B := by
      have := Finset.mem_range.mp hp
      omega
    refine ⟨Fin.cons p s, ?_, ?_⟩
    · apply boundedTuples_mem_of_forall_le
      intro i
      refine Fin.cases ?_ ?_ i
      · simpa using hpB
      · intro i
        exact boundedTuples_coordinate_le s hs i
    · simp [split]
  · intro t ht
    have hcons : t = Fin.cons (t 0) (fun i => t i.succ) := by
      funext i
      refine Fin.cases ?_ ?_ i
      · simp
      · intro i
        simp
    simpa [split] using congrArg F hcons


noncomputable def phaseNat (u : ℝ) (m : ℕ) : ℂ :=
  Complex.exp (Complex.I * u * Real.log (m : ℝ))

private theorem phaseNat_mul (u : ℝ) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    phaseNat u (m * n) = phaseNat u m * phaseNat u n := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [phaseNat, phaseNat, phaseNat, ← Complex.exp_add]
  congr 1
  rw [Nat.cast_mul, Real.log_mul hmR.ne' hnR.ne']
  push_cast
  ring

private theorem charPhaseNat_mul (k : ℕ) (χ : DirichletCharacter ℂ k)
    (u : ℝ) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    (χ ((m * n : ℕ) : ZMod k) : ℂ) * phaseNat u (m * n) =
      ((χ (m : ZMod k) : ℂ) * phaseNat u m) *
        ((χ (n : ZMod k) : ℂ) * phaseNat u n) := by
  have hcast : ((m * n : ℕ) : ZMod k) = (m : ZMod k) * (n : ZMod k) := by norm_cast
  rw [hcast, map_mul, phaseNat_mul u m n hm hn]
  ring

private theorem isNatInterval_real_bounds (a y b : ℝ) :
    IsNatInterval {p : ℕ | a ≤ (p : ℝ) ∧ y < (p : ℝ) ∧ (p : ℝ) ≤ b} := by
  intro m n k hm hn hmin hmax
  rcases hm with ⟨hma, hmy, hmb⟩
  rcases hn with ⟨hna, hny, hnb⟩
  rcases le_total m n with hmn | hnm
  · have hmk : m ≤ k := by simpa [min_eq_left hmn] using hmin
    have hkn : k ≤ n := by simpa [max_eq_right hmn] using hmax
    have hmkR : (m : ℝ) ≤ (k : ℝ) := by exact_mod_cast hmk
    have hknR : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
    exact ⟨hma.trans hmkR, lt_of_lt_of_le hmy hmkR, hknR.trans hnb⟩
  · have hnk : n ≤ k := by simpa [min_eq_right hnm] using hmin
    have hkm : k ≤ m := by simpa [max_eq_left hnm] using hmax
    have hnkR : (n : ℝ) ≤ (k : ℝ) := by exact_mod_cast hnk
    have hkmR : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hkm
    exact ⟨hna.trans hnkR, lt_of_lt_of_le hny hnkR, hkmR.trans hmb⟩


set_option maxHeartbeats 1000000 in
theorem prime_tuple_product_interval_phase_bound
    (M l r Y Nlow Nup D Cp : ℝ) (n B k : ℕ)
    (χ : DirichletCharacter ℂ k) (u : ℝ)
    (hM : 0 ≤ M) (hlM : M ≤ l) (hlr : l ≤ r) (hrM : r ≤ 2 * M)
    (hB : 2 * M ≤ (B : ℝ)) (hY : 0 < Y) (hNlow : Nlow ≤ Y)
    (hNup : 2 * M ≤ Nup) (hD : 0 ≤ D) (hCp : 0 ≤ Cp)
    (hslot : ∀ N : ℝ, Nlow ≤ N → N ≤ Nup →
      ∀ I : Set ℕ, IsNatInterval I →
        I ⊆ {p : ℕ | N ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * N} →
          ‖PP.primePhaseSum N k χ u I‖ ≤ 6 * N * Cp * D) :
    ‖∑ t ∈ (boundedTuples (n + 1) B).filter (fun t =>
        (∀ i, (t i).Prime ∧ Y < (t i : ℝ)) ∧
        l ≤ ((∏ i : Fin (n + 1), t i : ℕ) : ℝ) ∧
        ((∏ i : Fin (n + 1), t i : ℕ) : ℝ) ≤ r),
      (χ ((∏ i : Fin (n + 1), t i : ℕ) : ZMod k) : ℂ) *
        phaseNat u (∏ i : Fin (n + 1), t i : ℕ)‖ ≤
      12 * Cp * M * D * (harmonic B : ℝ) ^ n := by
  classical
  let factors (t : Fin (n + 1) → ℕ) : Prop :=
    ∀ i, (t i).Prime ∧ Y < (t i : ℝ)
  let productN (t : Fin (n + 1) → ℕ) : ℕ := ∏ i, t i
  let tupleGood (t : Fin (n + 1) → ℕ) : Prop :=
    factors t ∧ l ≤ (productN t : ℝ) ∧ (productN t : ℝ) ≤ r
  let tailGood (s : Fin n → ℕ) : Prop :=
    ∀ i, (s i).Prime ∧ Y < (s i : ℝ)
  let tailProduct (s : Fin n → ℕ) : ℕ := ∏ i, s i
  let tailSet : Finset (Fin n → ℕ) :=
    (boundedTuples n B).filter tailGood
  let tailPhase (m : ℕ) : ℂ :=
    (χ (m : ZMod k) : ℂ) * phaseNat u m
  let tailScale (s : Fin n → ℕ) : ℝ :=
    max Y (l / (tailProduct s : ℝ))
  let firstSet (s : Fin n → ℕ) : Set ℕ :=
    {p | tailScale s ≤ (p : ℝ) ∧ Y < (p : ℝ) ∧
      (p : ℝ) ≤ r / (tailProduct s : ℝ)}
  have hqPos (s : Fin n → ℕ) (hs : tailGood s) : 0 < (tailProduct s : ℝ) := by
    have hprod : 0 < ∏ i : Fin n, (s i : ℝ) := by
      apply Finset.prod_pos
      intro i hi
      exact_mod_cast (hs i).1.pos
    simpa [tailProduct] using hprod
  have hqOne (s : Fin n → ℕ) (hs : tailGood s) :
      1 ≤ (tailProduct s : ℝ) := by
    have hq : 1 ≤ tailProduct s := Nat.succ_le_of_lt (by
      exact_mod_cast hqPos s hs)
    exact_mod_cast hq
  have hProductCons (p : ℕ) (s : Fin n → ℕ) :
      productN (Fin.cons p s) = p * tailProduct s := by
    simp [productN, tailProduct, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  have hFactorsCons (p : ℕ) (s : Fin n → ℕ) :
      factors (Fin.cons p s) ↔ (p.Prime ∧ Y < (p : ℝ)) ∧ tailGood s := by
    simp [factors, tailGood, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]
  have hProductBounds (p : ℕ) (s : Fin n → ℕ) (hs : tailGood s) :
      (l ≤ ((p * tailProduct s : ℕ) : ℝ) ∧
        ((p * tailProduct s : ℕ) : ℝ) ≤ r) ↔
        (l / (tailProduct s : ℝ) ≤ (p : ℝ) ∧
          (p : ℝ) ≤ r / (tailProduct s : ℝ)) := by
    have hq : 0 < (tailProduct s : ℝ) := hqPos s hs
    constructor
    · rintro ⟨hlo, hhi⟩
      have hloR : l ≤ (p : ℝ) * (tailProduct s : ℝ) := by
        simpa [Nat.cast_mul, mul_comm] using hlo
      have hhiR : (p : ℝ) * (tailProduct s : ℝ) ≤ r := by
        simpa [Nat.cast_mul, mul_comm] using hhi
      exact ⟨(div_le_iff₀ hq).2 (by nlinarith [hloR]),
        (le_div_iff₀ hq).2 (by nlinarith [hhiR])⟩
    · rintro ⟨hlo, hhi⟩
      have hloR : l ≤ (p : ℝ) * (tailProduct s : ℝ) :=
        (div_le_iff₀ hq).1 hlo
      have hhiR : (p : ℝ) * (tailProduct s : ℝ) ≤ r :=
        (le_div_iff₀ hq).1 hhi
      exact ⟨by simpa [Nat.cast_mul, mul_comm] using hloR,
        by simpa [Nat.cast_mul, mul_comm] using hhiR⟩
  have hGoodCons (p : ℕ) (s : Fin n → ℕ) (hs : tailGood s) :
      tupleGood (Fin.cons p s) ↔ p.Prime ∧ p ∈ firstSet s := by
    dsimp [tupleGood, firstSet, tailScale]
    rw [hFactorsCons, hProductCons]
    constructor
    · rintro ⟨⟨⟨hp, hpy⟩, htail⟩, hlo, hhi⟩
      have hbounds := (hProductBounds p s hs).mp ⟨hlo, hhi⟩
      have hN : max Y (l / (tailProduct s : ℝ)) ≤ (p : ℝ) :=
        (max_le_iff).2 ⟨hpy.le, hbounds.1⟩
      exact ⟨hp, hN, hpy, hbounds.2⟩
    · rintro ⟨hp, hN, hpy, hhi⟩
      have hlow : l / (tailProduct s : ℝ) ≤ (p : ℝ) :=
        (max_le_iff.mp hN).2
      have hbounds := (hProductBounds p s hs).mpr ⟨hlow, hhi⟩
      exact ⟨⟨⟨hp, hpy⟩, hs⟩, ⟨hbounds.1, hbounds.2⟩⟩
  have hInterval (s : Fin n → ℕ) (hs : tailGood s) : IsNatInterval (firstSet s) := by
    exact isNatInterval_real_bounds (tailScale s) Y (r / (tailProduct s : ℝ))
  have hSubset (s : Fin n → ℕ) (hs : tailGood s) :
      firstSet s ⊆ {p : ℕ | tailScale s ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * tailScale s} := by
    have hq : 0 < (tailProduct s : ℝ) := hqPos s hs
    have hrl : r ≤ 2 * l := by
      have h2M : 2 * M ≤ 2 * l := mul_le_mul_of_nonneg_left hlM (by norm_num)
      linarith
    have hdiv : r / (tailProduct s : ℝ) ≤ 2 * (l / (tailProduct s : ℝ)) := by
      calc
        r / (tailProduct s : ℝ) ≤ (2 * l) / (tailProduct s : ℝ) :=
          div_le_div_of_nonneg_right hrl hq.le
        _ = 2 * (l / (tailProduct s : ℝ)) := by ring
    intro p hp
    refine ⟨hp.1, ?_⟩
    calc
      (p : ℝ) ≤ r / (tailProduct s : ℝ) := hp.2.2
      _ ≤ 2 * (l / (tailProduct s : ℝ)) := hdiv
      _ ≤ 2 * tailScale s :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)
  let Pleft (s : Fin n → ℕ) : Finset ℕ :=
    (Finset.range (B + 1)).filter (fun p => p.Prime ∧ p ∈ firstSet s)
  let Pright (s : Fin n → ℕ) : Finset ℕ :=
    (Finset.range (⌊2 * tailScale s⌋₊ + 1)).filter fun p =>
      p.Prime ∧ tailScale s ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * tailScale s ∧ p ∈ firstSet s
  have hPsets (s : Fin n → ℕ) (hs : tailGood s) : Pleft s = Pright s := by
    ext p
    simp only [Pleft, Pright, Finset.mem_filter, Finset.mem_range, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hpB, hp, hpI⟩
      have hpU := (hSubset s hs) hpI
      have hfloor : p ≤ ⌊2 * tailScale s⌋₊ := Nat.le_floor hpU.2
      exact ⟨Nat.lt_succ_of_le hfloor, hp, hpU.1, hpU.2, hpI⟩
    · rintro ⟨hpN, hp, hlo, hhi, hpI⟩
      have hqpos' := hqPos s hs
      have hqone := hqOne s hs
      have hpupper : (p : ℝ) ≤ 2 * M := by
        calc
          (p : ℝ) ≤ r / (tailProduct s : ℝ) := hpI.2.2
          _ ≤ (2 * M) / (tailProduct s : ℝ) :=
            div_le_div_of_nonneg_right hrM hqpos'.le
          _ ≤ 2 * M := by
            apply (div_le_iff₀ hqpos').2
            nlinarith [hM, hqone]
      have hpB' : p ≤ B := by exact_mod_cast hpupper.trans hB
      exact ⟨Nat.lt_succ_of_le hpB', hp, hpI⟩
  have hTupleSum :
      (∑ t ∈ (boundedTuples (n + 1) B).filter (fun t => tupleGood t),
        (χ ((productN t : ℕ) : ZMod k) : ℂ) * phaseNat u (productN t)) =
        ∑ s ∈ tailSet, tailPhase (tailProduct s) *
          PP.primePhaseSum (tailScale s) k χ u (firstSet s) := by
    let z (m : ℕ) : ℂ := (χ (m : ZMod k) : ℂ) * phaseNat u m
    let F (t : Fin (n + 1) → ℕ) : ℂ :=
      if tupleGood t then z (productN t) else 0
    have hfilter :
        (∑ t ∈ (boundedTuples (n + 1) B).filter (fun t => tupleGood t),
          z (productN t)) =
          ∑ t ∈ boundedTuples (n + 1) B, F t := by
      rw [← Finset.sum_filter]
    have hsplit := boundedTuples_cons_sum (n := n) (B := B) F
    have hinner (s : Fin n → ℕ) (hs : tailGood s) :
        (∑ p ∈ Finset.range (B + 1),
          if tupleGood (Fin.cons p s) then z (productN (Fin.cons p s)) else 0) =
          z (tailProduct s) * PP.primePhaseSum (tailScale s) k χ u (firstSet s) := by
      have hterm (p : ℕ) :
          (if tupleGood (Fin.cons p s) then z (productN (Fin.cons p s)) else 0) =
            if p.Prime ∧ p ∈ firstSet s then z (tailProduct s) * z p else 0 := by
        by_cases hp : p.Prime ∧ p ∈ firstSet s
        · have hgood := (hGoodCons p s hs).mpr hp
          have hpPos : 0 < p := hp.1.pos
          have hqPosNat : 0 < tailProduct s := by exact_mod_cast hqPos s hs
          have hphase : z (p * tailProduct s) = z p * z (tailProduct s) := by
            simpa [z] using charPhaseNat_mul k χ u p (tailProduct s) hpPos hqPosNat
          have hphase' : z (p * tailProduct s) = z (tailProduct s) * z p := by
            rw [hphase]
            ring
          simp [hp, hgood, hProductCons, hphase']
        · have hbad : ¬ tupleGood (Fin.cons p s) := by
            intro hg
            exact hp ((hGoodCons p s hs).mp hg)
          simp [hp, hbad]
      have hsumP :
          (∑ p ∈ Finset.range (B + 1),
            if p.Prime ∧ p ∈ firstSet s then z (tailProduct s) * z p else 0) =
            z (tailProduct s) * PP.primePhaseSum (tailScale s) k χ u (firstSet s) := by
        calc
          _ = ∑ p ∈ Finset.range (B + 1),
                z (tailProduct s) *
                  (if p.Prime ∧ p ∈ firstSet s then z p else 0) := by
            apply Finset.sum_congr rfl
            intro p hp
            split_ifs <;> simp [mul_assoc]
          _ = z (tailProduct s) *
              ∑ p ∈ Finset.range (B + 1),
                if p.Prime ∧ p ∈ firstSet s then z p else 0 := by
            rw [Finset.mul_sum]
          _ = z (tailProduct s) * ∑ p ∈ Pleft s, z p := by
            congr 1
            rw [← Finset.sum_filter]
          _ = z (tailProduct s) * ∑ p ∈ Pright s, z p := by rw [hPsets s hs]
          _ = z (tailProduct s) * PP.primePhaseSum (tailScale s) k χ u (firstSet s) := by
            apply congrArg (fun w : ℂ => z (tailProduct s) * w)
            unfold PP.primePhaseSum
            dsimp [Pright, z, phaseNat]
            apply Finset.sum_bij (fun p _ => p)
            · intro p hp
              simpa [Pright] using hp
            · intro p hp q hq hpq
              exact hpq
            · intro p hp
              exact ⟨p, by simpa [Pright] using hp, rfl⟩
            · intro p hp
              rfl
      calc
        _ = ∑ p ∈ Finset.range (B + 1),
            if p.Prime ∧ p ∈ firstSet s then z (tailProduct s) * z p else 0 := by
              apply Finset.sum_congr rfl
              intro p hp
              exact hterm p
        _ = _ := hsumP
    calc
      _ = ∑ t ∈ boundedTuples (n + 1) B, F t := hfilter
      _ = ∑ p ∈ Finset.range (B + 1),
          ∑ s ∈ boundedTuples n B, F (Fin.cons p s) := hsplit
      _ = ∑ s ∈ boundedTuples n B,
          ∑ p ∈ Finset.range (B + 1), F (Fin.cons p s) := by rw [Finset.sum_comm]
      _ = ∑ s ∈ boundedTuples n B,
          if tailGood s then tailPhase (tailProduct s) *
            PP.primePhaseSum (tailScale s) k χ u (firstSet s) else 0 := by
        apply Finset.sum_congr rfl
        intro s hs
        by_cases hsGood : tailGood s
        · simpa [F, tupleGood, factors, tailGood, tailPhase, z, hsGood] using hinner s hsGood
        · have hbad : ∀ p, ¬ tupleGood (Fin.cons p s) := by
            intro p hp
            have hpTail := (hFactorsCons p s).mp (hp.1)
            exact hsGood hpTail.2
          simp [F, tupleGood, factors, tailGood, hsGood, hbad]
      _ = ∑ s ∈ tailSet,
          tailPhase (tailProduct s) * PP.primePhaseSum (tailScale s) k χ u (firstSet s) := by
        rw [show tailSet = (boundedTuples n B).filter tailGood from rfl]
        exact (Finset.sum_filter (s := boundedTuples n B)
          (p := tailGood) (f := fun s => tailPhase (tailProduct s) *
            PP.primePhaseSum (tailScale s) k χ u (firstSet s))).symm
  have hinnerBound (s : Fin n → ℕ) (hs : s ∈ tailSet) :
      ‖tailPhase (tailProduct s) *
        PP.primePhaseSum (tailScale s) k χ u (firstSet s)‖ ≤
        12 * Cp * M * D / (tailProduct s : ℝ) := by
    have hsGood : tailGood s := (Finset.mem_filter.mp hs).2
    have hqPos' := hqPos s hsGood
    have hqOne' := hqOne s hsGood
    have hNlow' : Nlow ≤ tailScale s := le_trans hNlow (le_max_left _ _)
    have hIbound := hSubset s hsGood
    by_cases hIempty : firstSet s = ∅
    · have hzero : PP.primePhaseSum (tailScale s) k χ u (firstSet s) = 0 := by
        simp [PP.primePhaseSum, hIempty]
      simp [hzero]
      positivity
    · have hIexists : ∃ p, p ∈ firstSet s := by
        by_contra h
        apply hIempty
        ext p
        constructor
        · intro hp
          exact False.elim (h ⟨p, hp⟩)
        · simp
      rcases hIexists with ⟨p, hpI⟩
      have hNupper' : tailScale s ≤ 2 * M / (tailProduct s : ℝ) := by
        calc
          _ ≤ (p : ℝ) := hpI.1
          _ ≤ r / (tailProduct s : ℝ) := hpI.2.2
          _ ≤ (2 * M) / (tailProduct s : ℝ) :=
            div_le_div_of_nonneg_right hrM hqPos'.le
      have hNupper : tailScale s ≤ Nup := by
        have hdiv : (2 * M) / (tailProduct s : ℝ) ≤ 2 * M := by
          apply (div_le_iff₀ hqPos').2
          nlinarith [hM, hqOne']
        exact (hNupper'.trans hdiv).trans hNup
      have hslot' := hslot (tailScale s) hNlow' hNupper
        (firstSet s) (hInterval s hsGood) hIbound
      have hphaseNorm : ‖phaseNat u (tailProduct s)‖ = 1 := by
        rw [phaseNat]
        have harg : Complex.I * (u : ℂ) * (Real.log (tailProduct s : ℝ) : ℂ) =
            Complex.I * ((u * Real.log (tailProduct s : ℝ) : ℝ) : ℂ) := by
          push_cast
          ring
        rw [harg, Complex.norm_exp_I_mul_ofReal]
      have hzNorm : ‖tailPhase (tailProduct s)‖ ≤ 1 := by
        calc
          ‖tailPhase (tailProduct s)‖ =
              ‖χ (tailProduct s : ZMod k)‖ * ‖phaseNat u (tailProduct s)‖ := by
                dsimp [tailPhase]
                rw [norm_mul]
          _ = ‖χ (tailProduct s : ZMod k)‖ := by rw [hphaseNorm]; ring
          _ ≤ 1 := χ.norm_le_one _
      have hNbound : tailScale s ≤ 2 * M / (tailProduct s : ℝ) := hNupper'
      calc
        ‖tailPhase (tailProduct s) *
            PP.primePhaseSum (tailScale s) k χ u (firstSet s)‖ =
            ‖tailPhase (tailProduct s)‖ *
              ‖PP.primePhaseSum (tailScale s) k χ u (firstSet s)‖ := norm_mul _ _
        _ ≤ 1 * (6 * tailScale s * Cp * D) := by
          apply mul_le_mul hzNorm hslot'
          · exact norm_nonneg _
          · positivity
        _ ≤ 6 * (2 * M / (tailProduct s : ℝ)) * Cp * D := by
          have hconst : 0 ≤ 6 * Cp * D := by positivity
          calc
            1 * (6 * tailScale s * Cp * D) = tailScale s * (6 * Cp * D) := by ring
            _ ≤ (2 * M / (tailProduct s : ℝ)) * (6 * Cp * D) :=
              mul_le_mul_of_nonneg_right hNbound hconst
            _ = 6 * (2 * M / (tailProduct s : ℝ)) * Cp * D := by ring
        _ = 12 * Cp * M * D / (tailProduct s : ℝ) := by ring
  have hmass :
      (∑ s ∈ tailSet, 1 / (tailProduct s : ℝ)) ≤ (harmonic B : ℝ) ^ n := by
    simpa [tailSet, tailGood, tailProduct, Nat.cast_prod] using
      primeTuple_reciprocal_sum_le_harmonic n B Y
  have hcoef : 0 ≤ 12 * Cp * M * D := by positivity
  calc
    _ ≤ ∑ s ∈ tailSet,
        ‖tailPhase (tailProduct s) *
          PP.primePhaseSum (tailScale s) k χ u (firstSet s)‖ := by
      rw [hTupleSum]
      exact norm_sum_le _ _
    _ ≤ ∑ s ∈ tailSet, 12 * Cp * M * D / (tailProduct s : ℝ) :=
      Finset.sum_le_sum fun s hs => hinnerBound s hs
    _ = (12 * Cp * M * D) * ∑ s ∈ tailSet, 1 / (tailProduct s : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      ring
    _ ≤ 12 * Cp * M * D * (harmonic B : ℝ) ^ n :=
      mul_le_mul_of_nonneg_left hmass hcoef

end ArtinPrimitiveRoots.Proofs.RImplP.RPrime
