import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-CANCEL».C3.Dual

/-!
# Finite-sum decompositions for the remainder kernels

* divisors of a coprime product: `e ∣ c d ↔ e = e₁ e₂`, `e₁ = e ⊔ c ∣ c`, `e₂ = e ⊔ d ∣ d`;
* dyadic splitting of divisor sums by `⌊log₂ N e⌋` and of admissible row sums into
  `qsUpTo (2^{k+1})` blocks;
* pulling a finite sum out of a coprime pair sum.
-/

set_option autoImplicit false

open scoped NumberField ComplexConjugate
open NumberField IsDedekindDomain
open ClassFieldTheory

noncomputable section

namespace ArtinPrimitiveRoots.A2.QSC3

open QSC2

variable {K : Type} [Field K] [NumberField K]
variable {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}

omit [NumberField K] in
theorem sup_mul_sup_of_coprime {e c d : Ideal (𝓞 K)} (hcd : IsCoprime c d) :
    (e ⊔ c) * (e ⊔ d) = e ⊔ c * d := by
  apply le_antisymm
  · rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
    refine sup_le (sup_le ?_ ?_) (sup_le ?_ le_sup_right)
    · exact le_trans (Ideal.mul_le_right (I := e) (J := e)) le_sup_left
    · exact le_trans (Ideal.mul_le_left (I := e) (J := d)) le_sup_left
    · exact le_trans (Ideal.mul_le_right (I := c) (J := e)) le_sup_left
  · refine sup_le ?_ (Ideal.mul_mono le_sup_right le_sup_right)
    have htop : c ⊔ d = ⊤ := (Ideal.isCoprime_iff_sup_eq).mp hcd
    calc e = e * (c ⊔ d) := by rw [htop, Ideal.mul_top]
      _ = e * c ⊔ e * d := Ideal.mul_sup _ _ _
      _ ≤ (e ⊔ c) * (e ⊔ d) := by
          refine sup_le ?_ (Ideal.mul_mono le_sup_left le_sup_right)
          rw [mul_comm]
          exact Ideal.mul_mono le_sup_right le_sup_left

omit [NumberField K] in
theorem mul_sup_eq_left {e₁ e₂ c d : Ideal (𝓞 K)} (hcd : IsCoprime c d) (h₁ : e₁ ∣ c)
    (h₂ : e₂ ∣ d) : e₁ * e₂ ⊔ c = e₁ := by
  apply le_antisymm
  · exact sup_le (Ideal.mul_le_left (I := e₁) (J := e₂)) (Ideal.le_of_dvd h₁)
  · have hcop : IsCoprime e₂ c := isCoprime_of_le hcd.symm (Ideal.le_of_dvd h₂)
    have htop : e₂ ⊔ c = ⊤ := (Ideal.isCoprime_iff_sup_eq).mp hcop
    calc e₁ = e₁ * (e₂ ⊔ c) := by rw [htop, Ideal.mul_top]
      _ = e₁ * e₂ ⊔ e₁ * c := Ideal.mul_sup _ _ _
      _ ≤ e₁ * e₂ ⊔ c := sup_le_sup_left (Ideal.mul_le_right (I := e₁) (J := c)) _

open Classical in
/-- Divisors of a coprime product. -/
theorem sum_divisors_mul {M : Type*} [AddCommMonoid M] {c d : Ideal (𝓞 K)} (hc : c ≠ ⊥)
    (hd : d ≠ ⊥) (hcd : IsCoprime c d) (Q : Ideal (𝓞 K) → Prop) [DecidablePred Q]
    (g : Ideal (𝓞 K) → M) :
    ∑ e ∈ (qsDivisors (c * d)).filter Q, g e =
      ∑ e₁ ∈ qsDivisors c, ∑ e₂ ∈ qsDivisors d, if Q (e₁ * e₂) then g (e₁ * e₂) else 0 := by
  have hcd0 : c * d ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot]
    exact mul_ne_zero (by rwa [Ideal.zero_eq_bot]) (by rwa [Ideal.zero_eq_bot])
  rw [← Finset.sum_product', Finset.sum_filter]
  symm
  refine Finset.sum_nbij' (fun p => p.1 * p.2) (fun e => (e ⊔ c, e ⊔ d)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_product, mem_qsDivisors hc, mem_qsDivisors hd] at hp
    rw [mem_qsDivisors hcd0]
    exact mul_dvd_mul hp.1 hp.2
  · intro e he
    rw [Finset.mem_product, mem_qsDivisors hc, mem_qsDivisors hd]
    exact ⟨Ideal.dvd_iff_le.mpr le_sup_right, Ideal.dvd_iff_le.mpr le_sup_right⟩
  · intro p hp
    rw [Finset.mem_product, mem_qsDivisors hc, mem_qsDivisors hd] at hp
    rw [mul_sup_eq_left hcd hp.1 hp.2, mul_comm p.1 p.2,
      mul_sup_eq_left hcd.symm hp.2 hp.1]
  · intro e he
    rw [mem_qsDivisors hcd0] at he
    show (e ⊔ c) * (e ⊔ d) = e
    rw [sup_mul_sup_of_coprime hcd, sup_eq_left.mpr (Ideal.le_of_dvd he)]
  · intro p _
    rfl

open Classical in
/-- Dyadic splitting by `⌊log₂ N e⌋`. -/
theorem sum_dyadic {M : Type*} [AddCommMonoid M] (S : Finset (Ideal (𝓞 K))) (J : ℕ)
    (hS : ∀ e ∈ S, Nat.log 2 (Ideal.absNorm e) < J) (f : Ideal (𝓞 K) → M) :
    ∑ e ∈ S, f e = ∑ j ∈ Finset.range J, ∑ e ∈ S.filter (fun e => Nat.log 2 (Ideal.absNorm e) = j),
      f e :=
  (Finset.sum_fiberwise_of_maps_to (fun e he => Finset.mem_range.mpr (hS e he)) f).symm

theorem dyad_bounds {e : Ideal (𝓞 K)} (he : e ≠ ⊥) {j : ℕ}
    (hj : Nat.log 2 (Ideal.absNorm e) = j) :
    (2 : ℝ) ^ j ≤ qsN e ∧ qsN e ≤ 2 * 2 ^ j := by
  have h0 : Ideal.absNorm e ≠ 0 := fun h => he (Ideal.absNorm_eq_zero_iff.mp h)
  have h1 := Nat.pow_log_le_self 2 h0
  have h2 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (Ideal.absNorm e)
  rw [hj] at h1 h2
  constructor
  · simp only [qsN]; exact_mod_cast h1
  · simp only [qsN]
    have : Ideal.absNorm e ≤ 2 * 2 ^ j := by rw [pow_succ] at h2; omega
    exact_mod_cast this

theorem log_lt_of_le {N : ℕ} {X : ℝ} {J : ℕ} (hN : (N : ℝ) ≤ X) (hX : X < 2 ^ J) (hN0 : N ≠ 0) :
    Nat.log 2 N < J := by
  refine Nat.log_lt_of_lt_pow hN0 ?_
  have : (N : ℝ) < 2 ^ J := lt_of_le_of_lt hN hX
  exact_mod_cast this

open Classical in
/-- Admissible rows split into the blocks `qsUpTo (2^{k+1})` with `⌊log₂ N a⌋ = k`. -/
theorem sum_rows_dyadic {M : Type*} [AddCommMonoid M] (X : ℝ) (KB : ℕ) (hX : X < 2 ^ KB)
    (C : Ideal (𝓞 K) → Prop) [DecidablePred C] (hC : ∀ a, C a → qsN a ≤ X)
    (G : Ideal (𝓞 K) → M) :
    ∑ a ∈ qsUpTo m qS X, (if C a then G a else 0) =
      ∑ k ∈ Finset.range KB, ∑ a ∈ qsUpTo m qS (2 ^ (k + 1)),
        if C a ∧ Nat.log 2 (Ideal.absNorm a) = k then G a else 0 := by
  have hmaps : ∀ a ∈ qsUpTo m qS X, Nat.log 2 (Ideal.absNorm a) ∈ Finset.range KB := by
    intro a ha
    rw [mem_qsUpTo] at ha
    exact Finset.mem_range.mpr (log_lt_of_le ha.2 hX
      (fun h => ne_bot_of_QSAdm ha.1 (Ideal.absNorm_eq_zero_iff.mp h)))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hfil : (qsUpTo m qS X).filter (fun a => C a ∧ Nat.log 2 (Ideal.absNorm a) = k) =
      (qsUpTo m qS (2 ^ (k + 1))).filter (fun a => C a ∧ Nat.log 2 (Ideal.absNorm a) = k) := by
    ext a
    simp only [Finset.mem_filter, mem_qsUpTo]
    constructor
    · rintro ⟨⟨hA, _⟩, hC', hk⟩
      refine ⟨⟨hA, ?_⟩, hC', hk⟩
      have := (dyad_bounds (ne_bot_of_QSAdm hA) hk).2
      calc qsN a ≤ 2 * 2 ^ k := this
        _ = 2 ^ (k + 1) := by rw [pow_succ]; ring
    · rintro ⟨⟨hA, _⟩, hC', hk⟩
      exact ⟨⟨hA, hC a hC'⟩, hC', hk⟩
  calc ∑ a ∈ (qsUpTo m qS X).filter (fun a => Nat.log 2 (Ideal.absNorm a) = k),
        (if C a then G a else 0)
      = ∑ a ∈ qsUpTo m qS X, if C a ∧ Nat.log 2 (Ideal.absNorm a) = k then G a else 0 := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun a _ => ?_
        by_cases h1 : Nat.log 2 (Ideal.absNorm a) = k <;> by_cases h2 : C a <;> simp [h1, h2]
    _ = ∑ a ∈ (qsUpTo m qS X).filter (fun a => C a ∧ Nat.log 2 (Ideal.absNorm a) = k), G a :=
        (Finset.sum_filter _ _).symm
    _ = _ := by rw [hfil, Finset.sum_filter]

/-- Pulling a finite sum out of a pair sum. -/
theorem pair_sum_sum {M : Type*} [AddCommMonoid M] {ι α : Type*} (I : Finset ι)
    (cols : Finset α) (p : α → α → Prop) [∀ c d, Decidable (p c d)] (f : ι → α → α → M) :
    ∑ c ∈ cols, ∑ d ∈ cols, (if p c d then ∑ i ∈ I, f i c d else 0) =
      ∑ i ∈ I, ∑ c ∈ cols, ∑ d ∈ cols, if p c d then f i c d else 0 := by
  have h : ∀ c d, (if p c d then ∑ i ∈ I, f i c d else 0) =
      ∑ i ∈ I, if p c d then f i c d else 0 := by
    intro c d; split_ifs <;> simp
  simp_rw [h]
  calc ∑ c ∈ cols, ∑ d ∈ cols, ∑ i ∈ I, (if p c d then f i c d else 0)
      = ∑ c ∈ cols, ∑ i ∈ I, ∑ d ∈ cols, (if p c d then f i c d else 0) :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

end ArtinPrimitiveRoots.A2.QSC3
