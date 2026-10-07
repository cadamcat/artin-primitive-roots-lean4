import ArtinPrimitiveRoots.TypeII.PD.MemoryResults
import ArtinPrimitiveRoots.TypeII.PP.Results
import ArtinPrimitiveRoots.TypeII.Proofs.pd7.PrimeMoments

/-!
# Design B-PD-MajorArcs: drop-in replacement for `TypeII/PD/MajorArcs.lean` (PD §5)

Replaces the mismatched `major_separation` and `major_energy`, and corrects the stated `major_term`
(it lacked the size hypothesis on `β` and the smoothness/support
hypotheses on `η`, so it was false as stated).  Declarations marked COPY are verbatim copies of
the frozen ones and stay unchanged.

What changed mathematically (PD 05:257-433):
* `B_λ(t)` is `(1/Y) Σ_b η(b/Y) e(-λb/Y) (∏V_i^{-1}) χ(b) b^{it}` over products `b` of one prime
  per group (maj:polynomials) — not a product over bands: the cutoff `η(b/Y)e(-λb/Y)` couples
  the bands, and PD isolates one band by Mellin inversion of `f_λ(y) = η(y)e(-λy)` (05:381-415).
* All three polynomials carry Dirichlet characters modulo the arc denominator `k ≤ L^{A₀}`
  (the six-character expansion, 05:263-276).  The frozen `major_energy` allowed arbitrary
  bounded twists of `α`, for which the long-coefficient hypothesis gives nothing.
* `major_separation` is the reduction (maj:bound) ⇐ (maj:energy) for all characters and arc
  parameters; `major_energy` proves (maj:energy).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical MeasureTheory
open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.TypeII.PP

noncomputable section

/-- COPY. Small-prime polynomial on one prime band. -/
noncomputable def bandPrimePolynomial (P : ℝ) (Pset : Finset ℕ)
    (chiValue : ℕ → ℂ) (xi t : ℝ) : ℂ :=
  (1 / P) * ∑ p ∈ Pset,
    chiValue p * Complex.exp (Complex.I * (t + xi) * Real.log (p : ℝ))

lemma prime_band_card_le_three_mul (P : ℝ) (hP : 1 ≤ P) (Pset : Finset ℕ)
    (hset : ∀ p ∈ Pset, P ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * P) :
    (Pset.card : ℝ) ≤ 3 * P := by
  have hsub : Pset ⊆ Finset.range (⌊2 * P⌋₊ + 1) := by
    intro p hp
    apply Finset.mem_range.mpr
    have h := hset p hp
    exact Nat.lt_succ_of_le (Nat.le_floor h.2)
  have hcard : Pset.card ≤ ⌊2 * P⌋₊ + 1 := by
    calc
      Pset.card ≤ (Finset.range (⌊2 * P⌋₊ + 1)).card := Finset.card_le_card hsub
      _ = ⌊2 * P⌋₊ + 1 := Finset.card_range _
  have hcardR : (Pset.card : ℝ) ≤ (⌊2 * P⌋₊ : ℝ) + 1 := by exact_mod_cast hcard
  have hfloor : (⌊2 * P⌋₊ : ℝ) ≤ 2 * P := Nat.floor_le (by linarith)
  linarith

lemma bandPrimePolynomial_eq_pd7 (P : ℝ) (Pset : Finset ℕ)
    (chiValue : ℕ → ℂ) (xi t : ℝ) :
    bandPrimePolynomial P Pset chiValue xi t =
      (1 / P : ℂ) * pd7PrimePolynomial Pset
        (fun p => chiValue p * pd7PrimePhase xi p) t := by
  unfold bandPrimePolynomial pd7PrimePolynomial
  apply congrArg (fun z : ℂ => (1 / P : ℂ) * z)
  apply Finset.sum_congr rfl
  intro p hp
  have hphase : pd7PrimePhase (t + xi) p =
      Complex.exp (Complex.I * ((t : ℂ) + (xi : ℂ)) * Real.log (p : ℝ)) := by
    simpa only [Complex.ofReal_add] using pd7_prime_phase_eq (t + xi) p
  rw [← hphase, pd7_prime_phase_add t xi p]
  ring

lemma bandPrimePolynomial_norm_le (P : ℝ) (hP : 0 < P) (Pset : Finset ℕ)
    (chiValue : ℕ → ℂ) (xi t : ℝ)
    (hchi : ∀ p ∈ Pset, ‖chiValue p‖ ≤ 1) :
    ‖bandPrimePolynomial P Pset chiValue xi t‖ ≤ (Pset.card : ℝ) / P := by
  have hcoef (p : ℕ) (hp : p ∈ Pset) :
      ‖chiValue p * pd7PrimePhase xi p * pd7PrimePhase t p‖ ≤ 1 := by
    rw [norm_mul, norm_mul, pd7_prime_phase_norm, pd7_prime_phase_norm]
    simpa using hchi p hp
  have hsum :
      ‖pd7PrimePolynomial Pset (fun p => chiValue p * pd7PrimePhase xi p) t‖ ≤
        (Pset.card : ℝ) := by
    unfold pd7PrimePolynomial
    calc
      _ ≤ ∑ p ∈ Pset,
          ‖chiValue p * pd7PrimePhase xi p * pd7PrimePhase t p‖ := norm_sum_le _ _
      _ ≤ ∑ _p ∈ Pset, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        exact hcoef p hp
      _ = (Pset.card : ℝ) := by simp
  have hscale : ‖(1 / P : ℂ)‖ = 1 / P := by
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hP]
  calc
    _ = ‖(1 / P : ℂ)‖ *
        ‖pd7PrimePolynomial Pset (fun p => chiValue p * pd7PrimePhase xi p) t‖ := by
      rw [bandPrimePolynomial_eq_pd7, norm_mul]
    _ = (1 / P : ℝ) *
        ‖pd7PrimePolynomial Pset (fun p => chiValue p * pd7PrimePhase xi p) t‖ := by
      rw [hscale]
    _ ≤ (1 / P : ℝ) * (Pset.card : ℝ) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (Pset.card : ℝ) / P := by ring

lemma bandPrimePolynomial_separated_moment :
    ∃ Cmv : ℝ, 0 < Cmv ∧
      ∀ (P : ℝ), 1 ≤ P → ∀ (Pset : Finset ℕ),
        (∀ p ∈ Pset, p.Prime ∧ P ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * P) →
        ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (xi : ℝ) (r : ℕ),
        ∀ (S : Finset ℝ) (lo hi : ℝ), lo ≤ hi →
          (∀ t ∈ S, lo ≤ t ∧ t ≤ hi) →
          (∀ t₁ ∈ S, ∀ t₂ ∈ S, t₁ ≠ t₂ → 1 ≤ |t₁ - t₂|) →
          (∑ t ∈ S, ‖bandPrimePolynomial P Pset
            (fun p => (χ (p : ZMod q) : ℂ)) xi t‖ ^ (2 * r)) ≤
            Cmv * (hi - lo + 1 + ((⌊2 * P⌋₊ ^ r : ℕ) : ℝ) *
              Real.log (2 * ((⌊2 * P⌋₊ ^ r : ℕ) : ℝ))) *
              Real.rpow (Real.log (2 * ((⌊2 * P⌋₊ ^ r : ℕ) : ℝ))) 2 *
                (r.factorial : ℝ) * (Pset.card : ℝ) ^ r * (1 / P) ^ (2 * r) := by
  obtain ⟨Cmv, hCmv, hMoment⟩ := pd7_prime_polynomial_separated_moment
  refine ⟨Cmv, hCmv, ?_⟩
  intro P hP Pset hPset q χ xi r S lo hi hlohi hS hsep
  let N : ℕ := ⌊2 * P⌋₊
  let coeff : ℕ → ℂ := fun p => (χ (p : ZMod q) : ℂ) * pd7PrimePhase xi p
  have hN0 : 1 ≤ N := by
    dsimp [N]
    have htwo : (1 : ℝ) ≤ 2 * P := by linarith
    exact Nat.le_floor (by exact_mod_cast htwo)
  have hPprime : ∀ p ∈ Pset, p.Prime := fun p hp => (hPset p hp).1
  have hNbound : ∀ p ∈ Pset, p ≤ N := by
    intro p hp
    dsimp [N]
    exact Nat.le_floor (by exact_mod_cast (hPset p hp).2.2)
  have hcoeff (p : ℕ) (hp : p ∈ Pset) : ‖coeff p‖ ≤ 1 := by
    dsimp [coeff]
    rw [norm_mul, pd7_prime_phase_norm]
    simpa using χ.norm_le_one (p : ZMod q)
  have hcoeffSq : (∑ p ∈ Pset, ‖coeff p‖ ^ 2) ≤ (Pset.card : ℝ) := by
    calc
      _ ≤ ∑ _p ∈ Pset, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        simpa using pow_le_pow_left₀ (norm_nonneg _) (hcoeff p hp) 2
      _ = (Pset.card : ℝ) := by simp
  have hcoeffSq0 : 0 ≤ ∑ p ∈ Pset, ‖coeff p‖ ^ 2 :=
    Finset.sum_nonneg fun p hp => sq_nonneg _
  have hcoeffPow : (∑ p ∈ Pset, ‖coeff p‖ ^ 2) ^ r ≤
      (Pset.card : ℝ) ^ r :=
    pow_le_pow_left₀ hcoeffSq0 hcoeffSq r
  have hNcast : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN0
  have hYcast : (1 : ℝ) ≤ ((N ^ r : ℕ) : ℝ) := by
    rw [Nat.cast_pow]
    exact one_le_pow₀ hNcast
  have hlog : 0 ≤ Real.log (2 * ((N ^ r : ℕ) : ℝ)) :=
    Real.log_nonneg (by nlinarith)
  have hMoment' := hMoment Pset coeff N r hPprime hNbound hN0 S lo hi
    hlohi hS hsep
  have hpolyMoment :
      (∑ t ∈ S, ‖pd7PrimePolynomial Pset coeff t‖ ^ (2 * r)) ≤
        Cmv * (hi - lo + 1 + ((N ^ r : ℕ) : ℝ) *
          Real.log (2 * ((N ^ r : ℕ) : ℝ))) *
          Real.rpow (Real.log (2 * ((N ^ r : ℕ) : ℝ))) 2 *
            (r.factorial : ℝ) * (Pset.card : ℝ) ^ r := by
    calc
      _ ≤ Cmv * (hi - lo + 1 + ((N ^ r : ℕ) : ℝ) *
            Real.log (2 * ((N ^ r : ℕ) : ℝ))) *
          Real.rpow (Real.log (2 * ((N ^ r : ℕ) : ℝ))) 2 *
            (r.factorial : ℝ) * (∑ p ∈ Pset, ‖coeff p‖ ^ 2) ^ r := hMoment'
      _ ≤ _ := by
        have hspan : 0 ≤ hi - lo + 1 := by linarith
        have hlen : 0 ≤ hi - lo + 1 + ((N ^ r : ℕ) : ℝ) *
            Real.log (2 * ((N ^ r : ℕ) : ℝ)) :=
          add_nonneg hspan (mul_nonneg (by positivity) hlog)
        have hpow : 0 ≤ Real.rpow (Real.log (2 * ((N ^ r : ℕ) : ℝ))) 2 :=
          Real.rpow_nonneg hlog _
        have hfac : 0 ≤ Cmv * (hi - lo + 1 + ((N ^ r : ℕ) : ℝ) *
            Real.log (2 * ((N ^ r : ℕ) : ℝ))) *
            Real.rpow (Real.log (2 * ((N ^ r : ℕ) : ℝ))) 2 *
              (r.factorial : ℝ) :=
          mul_nonneg (mul_nonneg (mul_nonneg hCmv.le hlen) hpow) (by positivity)
        exact mul_le_mul_of_nonneg_left hcoeffPow hfac
  have hscale : ‖(1 / P : ℂ)‖ = 1 / P := by
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith : 0 < P)]
  have hnorm (t : ℝ) :
      ‖bandPrimePolynomial P Pset (fun p => (χ (p : ZMod q) : ℂ)) xi t‖ ^ (2 * r) =
        (1 / P) ^ (2 * r) * ‖pd7PrimePolynomial Pset coeff t‖ ^ (2 * r) := by
    rw [bandPrimePolynomial_eq_pd7, norm_mul, hscale, mul_pow]
  have hscale0 : 0 ≤ (1 / P : ℝ) ^ (2 * r) := pow_nonneg (by positivity) _
  have hsum :
      (∑ t ∈ S, ‖bandPrimePolynomial P Pset
          (fun p => (χ (p : ZMod q) : ℂ)) xi t‖ ^ (2 * r)) =
        (1 / P) ^ (2 * r) *
          (∑ t ∈ S, ‖pd7PrimePolynomial Pset coeff t‖ ^ (2 * r)) := by
    calc
      _ = ∑ t ∈ S, (1 / P) ^ (2 * r) *
          ‖pd7PrimePolynomial Pset coeff t‖ ^ (2 * r) := by
        apply Finset.sum_congr rfl
        intro t ht
        exact hnorm t
      _ = _ := by rw [← Finset.mul_sum]
  calc
    _ = (1 / P) ^ (2 * r) *
        (∑ t ∈ S, ‖pd7PrimePolynomial Pset coeff t‖ ^ (2 * r)) := hsum
    _ ≤ (1 / P) ^ (2 * r) *
        (Cmv * (hi - lo + 1 + ((N ^ r : ℕ) : ℝ) *
          Real.log (2 * ((N ^ r : ℕ) : ℝ))) *
          Real.rpow (Real.log (2 * ((N ^ r : ℕ) : ℝ))) 2 *
            (r.factorial : ℝ) * (Pset.card : ℝ) ^ r) :=
      mul_le_mul_of_nonneg_left hpolyMoment hscale0
    _ = _ := by dsimp [N]; ring

lemma pd7_card_le_high_moment {α : Type*} (S : Finset α) (f : α → ℂ)
    (T : ℝ) (r : ℕ) (hT : 0 < T)
    (hlarge : ∀ t ∈ S, T ≤ ‖f t‖) :
    (S.card : ℝ) * T ^ (2 * r) ≤ ∑ t ∈ S, ‖f t‖ ^ (2 * r) := by
  calc
    _ = ∑ _t ∈ S, T ^ (2 * r) := by simp
    _ ≤ ∑ t ∈ S, ‖f t‖ ^ (2 * r) := by
      apply Finset.sum_le_sum
      intro t ht
      exact pow_le_pow_left₀ hT.le (hlarge t ht) _

lemma pd7_two_color_interval_sample_bound (J : Finset ℤ) (w : ℤ → ℝ)
    (f : ℝ → ℂ) (V R A : ℝ) (r : ℕ) (hV : 0 < V)
    (hinterval : ∀ j ∈ J, (j : ℝ) ≤ w j ∧ w j ≤ (j : ℝ) + 1 ∧ |w j| ≤ R)
    (hlarge : ∀ j ∈ J, V ≤ ‖f (w j)‖)
    (hmoment : ∀ S : Finset ℝ, (∀ t ∈ S, |t| ≤ R) →
      (∀ t₁ ∈ S, ∀ t₂ ∈ S, t₁ ≠ t₂ → 1 ≤ |t₁ - t₂|) →
        (∑ t ∈ S, ‖f t‖ ^ (2 * r)) ≤ A) :
    (J.card : ℝ) * V ^ (2 * r) ≤ 2 * A := by
  let J₀ := J.filter fun j => j % 2 = 0
  let J₁ := J.filter fun j => j % 2 = 1
  let S₀ := J₀.image w
  let S₁ := J₁.image w
  have hcover : J ⊆ J₀ ∪ J₁ := by
    intro j hj
    have hmod : j % 2 = 0 ∨ j % 2 = 1 := by omega
    rcases hmod with h0 | h1
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hj, h0⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hj, h1⟩)
  have hJcard : J.card ≤ J₀.card + J₁.card := by
    calc
      J.card ≤ (J₀ ∪ J₁).card := Finset.card_le_card hcover
      _ ≤ J₀.card + J₁.card := Finset.card_union_le _ _
  have hgap0 (j k : ℤ) (hj : j % 2 = 0) (hk : k % 2 = 0) (hjk : j ≠ k) :
      j + 2 ≤ k ∨ k + 2 ≤ j := by omega
  have hgap1 (j k : ℤ) (hj : j % 2 = 1) (hk : k % 2 = 1) (hjk : j ≠ k) :
      j + 2 ≤ k ∨ k + 2 ≤ j := by omega
  have hinj0 : Set.InjOn w (↑J₀ : Set ℤ) := by
    intro j hj k hk heq
    have hj' := Finset.mem_filter.mp hj
    have hk' := Finset.mem_filter.mp hk
    by_contra hjk
    have hgap := hgap0 j k hj'.2 hk'.2 hjk
    have hji := hinterval j hj'.1
    have hki := hinterval k hk'.1
    rcases hgap with hgap | hgap
    · have hgapR : (j : ℝ) + 2 ≤ (k : ℝ) := by exact_mod_cast hgap
      have hstrict : w j < w k := by linarith [hji.2.1, hki.1, hgapR]
      exact (ne_of_lt hstrict) heq
    · have hgapR : (k : ℝ) + 2 ≤ (j : ℝ) := by exact_mod_cast hgap
      have hstrict : w k < w j := by linarith [hki.2.1, hji.1, hgapR]
      exact (ne_of_lt hstrict) heq.symm
  have hinj1 : Set.InjOn w (↑J₁ : Set ℤ) := by
    intro j hj k hk heq
    have hj' := Finset.mem_filter.mp hj
    have hk' := Finset.mem_filter.mp hk
    by_contra hjk
    have hgap := hgap1 j k hj'.2 hk'.2 hjk
    have hji := hinterval j hj'.1
    have hki := hinterval k hk'.1
    rcases hgap with hgap | hgap
    · have hgapR : (j : ℝ) + 2 ≤ (k : ℝ) := by exact_mod_cast hgap
      have hstrict : w j < w k := by linarith [hji.2.1, hki.1, hgapR]
      exact (ne_of_lt hstrict) heq
    · have hgapR : (k : ℝ) + 2 ≤ (j : ℝ) := by exact_mod_cast hgap
      have hstrict : w k < w j := by linarith [hki.2.1, hji.1, hgapR]
      exact (ne_of_lt hstrict) heq.symm
  have hcardImage0 : S₀.card = J₀.card := Finset.card_image_iff.mpr hinj0
  have hcardImage1 : S₁.card = J₁.card := Finset.card_image_iff.mpr hinj1
  have hrange0 : ∀ t ∈ S₀, |t| ≤ R := by
    intro t ht
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht
    exact (hinterval j (Finset.mem_filter.mp hj).1).2.2
  have hlarge0 : ∀ t ∈ S₀, V ≤ ‖f t‖ := by
    intro t ht
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht
    exact hlarge j (Finset.mem_filter.mp hj).1
  have hsep0 : ∀ t₁ ∈ S₀, ∀ t₂ ∈ S₀, t₁ ≠ t₂ → 1 ≤ |t₁ - t₂| := by
    intro t₁ ht₁ t₂ ht₂ hne
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht₁
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ht₂
    have hj' := Finset.mem_filter.mp hj
    have hk' := Finset.mem_filter.mp hk
    have hjk : j ≠ k := by
      intro h
      apply hne
      simpa [h]
    have hgap := hgap0 j k hj'.2 hk'.2 hjk
    have hji := hinterval j hj'.1
    have hki := hinterval k hk'.1
    rcases hgap with hgap | hgap
    · have hgapR : (j : ℝ) + 2 ≤ (k : ℝ) := by exact_mod_cast hgap
      have hdiff : 1 ≤ w k - w j := by linarith [hji.2.1, hki.1, hgapR]
      rw [abs_of_nonpos (by linarith : w j - w k ≤ 0)]
      linarith
    · have hgapR : (k : ℝ) + 2 ≤ (j : ℝ) := by exact_mod_cast hgap
      have hdiff : 1 ≤ w j - w k := by linarith [hki.2.1, hji.1, hgapR]
      rw [abs_of_nonneg (by linarith : 0 ≤ w j - w k)]
      linarith
  have hbound0 : (S₀.card : ℝ) * V ^ (2 * r) ≤ A := by
    calc
      _ ≤ ∑ t ∈ S₀, ‖f t‖ ^ (2 * r) := pd7_card_le_high_moment S₀ f V r hV hlarge0
      _ ≤ A := hmoment S₀ hrange0 hsep0
  have hrange1 : ∀ t ∈ S₁, |t| ≤ R := by
    intro t ht
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht
    exact (hinterval j (Finset.mem_filter.mp hj).1).2.2
  have hlarge1 : ∀ t ∈ S₁, V ≤ ‖f t‖ := by
    intro t ht
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht
    exact hlarge j (Finset.mem_filter.mp hj).1
  have hsep1 : ∀ t₁ ∈ S₁, ∀ t₂ ∈ S₁, t₁ ≠ t₂ → 1 ≤ |t₁ - t₂| := by
    intro t₁ ht₁ t₂ ht₂ hne
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht₁
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ht₂
    have hj' := Finset.mem_filter.mp hj
    have hk' := Finset.mem_filter.mp hk
    have hjk : j ≠ k := by
      intro h
      apply hne
      simpa [h]
    have hgap := hgap1 j k hj'.2 hk'.2 hjk
    have hji := hinterval j hj'.1
    have hki := hinterval k hk'.1
    rcases hgap with hgap | hgap
    · have hgapR : (j : ℝ) + 2 ≤ (k : ℝ) := by exact_mod_cast hgap
      have hdiff : 1 ≤ w k - w j := by linarith [hji.2.1, hki.1, hgapR]
      rw [abs_of_nonpos (by linarith : w j - w k ≤ 0)]
      linarith
    · have hgapR : (k : ℝ) + 2 ≤ (j : ℝ) := by exact_mod_cast hgap
      have hdiff : 1 ≤ w j - w k := by linarith [hki.2.1, hji.1, hgapR]
      rw [abs_of_nonneg (by linarith : 0 ≤ w j - w k)]
      linarith
  have hbound1 : (S₁.card : ℝ) * V ^ (2 * r) ≤ A := by
    calc
      _ ≤ ∑ t ∈ S₁, ‖f t‖ ^ (2 * r) := pd7_card_le_high_moment S₁ f V r hV hlarge1
      _ ≤ A := hmoment S₁ hrange1 hsep1
  have hcardR : (J.card : ℝ) ≤ (J₀.card : ℝ) + (J₁.card : ℝ) := by
    exact_mod_cast hJcard
  calc
    _ ≤ ((J₀.card : ℝ) + (J₁.card : ℝ)) * V ^ (2 * r) :=
      mul_le_mul_of_nonneg_right hcardR (pow_nonneg hV.le _)
    _ = (S₀.card : ℝ) * V ^ (2 * r) + (S₁.card : ℝ) * V ^ (2 * r) := by
      rw [hcardImage0, hcardImage1]
      ring
    _ ≤ A + A := add_le_add hbound0 hbound1
    _ = 2 * A := by ring

lemma finite_set_of_bounded_unit_intervals {S : Set ℤ} {R : ℝ} (hR : 0 ≤ R)
    (hS : ∀ j ∈ S, ∃ t : ℝ, (j : ℝ) ≤ t ∧ t ≤ (j : ℝ) + 1 ∧ |t| ≤ R) :
    S.Finite := by
  let M : ℕ := ⌈R + 1⌉₊
  have hM : R + 1 ≤ (M : ℝ) := by
    dsimp [M]
    exact Nat.le_ceil _
  have hsubset : S ⊆ Set.Icc (-(M : ℤ)) (M : ℤ) := by
    intro j hj
    obtain ⟨t, hjt, htj, htR⟩ := hS j hj
    have ht := abs_le.mp htR
    constructor
    · have hlow : -(M : ℝ) ≤ (j : ℝ) := by linarith
      exact_mod_cast hlow
    · have hhigh : (j : ℝ) ≤ (M : ℝ) := by linarith
      exact_mod_cast hhigh
  exact (Set.finite_Icc (-(M : ℤ)) (M : ℤ)).subset hsubset

lemma pd7_sparse_bad_card_bound {bad : Set ℤ} (R V : ℝ) (f : ℝ → ℂ)
    (r : ℕ) (A : ℝ) (hR : 0 ≤ R) (hV : 0 < V)
    (hbad : ∀ j ∈ bad, ∃ t : ℝ,
      (j : ℝ) ≤ t ∧ t ≤ (j : ℝ) + 1 ∧ |t| ≤ R ∧ V ≤ ‖f t‖)
    (hmoment : ∀ S : Finset ℝ, (∀ t ∈ S, |t| ≤ R) →
      (∀ t₁ ∈ S, ∀ t₂ ∈ S, t₁ ≠ t₂ → 1 ≤ |t₁ - t₂|) →
        (∑ t ∈ S, ‖f t‖ ^ (2 * r)) ≤ A) :
    (bad.ncard : ℝ) ≤ 2 * A / V ^ (2 * r) := by
  have hfinite : bad.Finite := finite_set_of_bounded_unit_intervals hR (by
    intro j hj
    obtain ⟨t, hjt, htj, htR, _⟩ := hbad j hj
    exact ⟨t, hjt, htj, htR⟩)
  let J := hfinite.toFinset
  let w : ℤ → ℝ := fun j => if hj : j ∈ bad then Classical.choose (hbad j hj) else 0
  have hw (j : ℤ) (hj : j ∈ bad) :
      (j : ℝ) ≤ w j ∧ w j ≤ (j : ℝ) + 1 ∧ |w j| ≤ R ∧ V ≤ ‖f (w j)‖ := by
    simp [w, hj, Classical.choose_spec (hbad j hj)]
  have hinterval : ∀ j ∈ J, (j : ℝ) ≤ w j ∧ w j ≤ (j : ℝ) + 1 ∧ |w j| ≤ R := by
    intro j hj
    have hj' : j ∈ bad := hfinite.mem_toFinset.mp hj
    exact ⟨(hw j hj').1, (hw j hj').2.1, (hw j hj').2.2.1⟩
  have hlarge : ∀ j ∈ J, V ≤ ‖f (w j)‖ := by
    intro j hj
    exact (hw j (hfinite.mem_toFinset.mp hj)).2.2.2
  have hsample := pd7_two_color_interval_sample_bound J w f V R A r hV
    hinterval hlarge hmoment
  have hcard : (bad.ncard : ℝ) = (J.card : ℝ) := by
    rw [Set.ncard_eq_toFinset_card bad hfinite]
  have hpow : 0 < V ^ (2 * r) := pow_pos hV _
  rw [hcard]
  exact (le_div_iff₀ hpow).2 hsample

theorem bandPrimePolynomial_bad_interval_count :
    ∃ Cmv : ℝ, 0 < Cmv ∧
      ∀ (P : ℝ), 1 ≤ P → ∀ (Pset : Finset ℕ),
        (∀ p ∈ Pset, p.Prime ∧ P ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * P) →
        ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (xi R V : ℝ),
          0 ≤ R → 0 < V → ∀ r : ℕ,
            let bad : Set ℤ := {j : ℤ | ∃ t : ℝ, (j : ℝ) ≤ t ∧ t ≤ (j : ℝ) + 1 ∧
              |t| ≤ R ∧ V ≤ ‖bandPrimePolynomial P Pset
                (fun p => (χ (p : ZMod q) : ℂ)) xi t‖}
            (bad.ncard : ℝ) ≤
              2 * Cmv * (2 * R + 1 + ((⌊2 * P⌋₊ ^ r : ℕ) : ℝ) *
                Real.log (2 * ((⌊2 * P⌋₊ ^ r : ℕ) : ℝ))) *
                Real.rpow (Real.log (2 * ((⌊2 * P⌋₊ ^ r : ℕ) : ℝ))) 2 *
                (r.factorial : ℝ) * (Pset.card : ℝ) ^ r * (1 / P) ^ (2 * r) /
                V ^ (2 * r) := by
  obtain ⟨Cmv, hCmv, hBand⟩ := bandPrimePolynomial_separated_moment
  refine ⟨Cmv, hCmv, ?_⟩
  intro P hP Pset hPset q χ xi R V hR hV r
  let bad : Set ℤ := {j : ℤ | ∃ t : ℝ, (j : ℝ) ≤ t ∧ t ≤ (j : ℝ) + 1 ∧
    |t| ≤ R ∧ V ≤ ‖bandPrimePolynomial P Pset
      (fun p => (χ (p : ZMod q) : ℂ)) xi t‖}
  have hmoment : ∀ S : Finset ℝ, (∀ t ∈ S, |t| ≤ R) →
      (∀ t₁ ∈ S, ∀ t₂ ∈ S, t₁ ≠ t₂ → 1 ≤ |t₁ - t₂|) →
        (∑ t ∈ S, ‖bandPrimePolynomial P Pset
          (fun p => (χ (p : ZMod q) : ℂ)) xi t‖ ^ (2 * r)) ≤
          Cmv * (2 * R + 1 + ((⌊2 * P⌋₊ ^ r : ℕ) : ℝ) *
            Real.log (2 * ((⌊2 * P⌋₊ ^ r : ℕ) : ℝ))) *
            Real.rpow (Real.log (2 * ((⌊2 * P⌋₊ ^ r : ℕ) : ℝ))) 2 *
              (r.factorial : ℝ) * (Pset.card : ℝ) ^ r * (1 / P) ^ (2 * r) := by
    intro S hS hsep
    have h := hBand P hP Pset hPset q χ xi r S (-R) R
      (by linarith [hR])
      (by
        intro t ht
        rcases abs_le.mp (hS t ht) with ⟨hlt, hgt⟩
        constructor <;> linarith)
      hsep
    convert h using 1 <;> ring
  have hbound := pd7_sparse_bad_card_bound (bad := bad) R V
    (bandPrimePolynomial P Pset (fun p => (χ (p : ZMod q) : ℂ)) xi)
    r (Cmv * (2 * R + 1 + ((⌊2 * P⌋₊ ^ r : ℕ) : ℝ) *
      Real.log (2 * ((⌊2 * P⌋₊ ^ r : ℕ) : ℝ))) *
      Real.rpow (Real.log (2 * ((⌊2 * P⌋₊ ^ r : ℕ) : ℝ))) 2 *
      (r.factorial : ℝ) * (Pset.card : ℝ) ^ r * (1 / P) ^ (2 * r))
    hR hV (by
      intro j hj
      change ∃ t : ℝ, (j : ℝ) ≤ t ∧ t ≤ (j : ℝ) + 1 ∧ |t| ≤ R ∧
        V ≤ ‖bandPrimePolynomial P Pset (fun p => (χ (p : ZMod q) : ℂ)) xi t‖ at hj
      exact hj) hmoment
  change (bad.ncard : ℝ) ≤ _
  simpa [mul_assoc, mul_left_comm, mul_comm] using hbound

/-- COPY. The long coefficient polynomial `M_α(t)` with an arbitrary twist. -/
noncomputable def alphaFrequency {δ C c₁ c₂ : ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (x t : ℝ) (chiValue : ℕ → ℂ) : ℂ :=
  (1 / family.Hm x) *
    ∑ m ∈ familyTerms family x,
      family.alpha x m * chiValue m * Complex.exp (Complex.I * t * Real.log (m : ℝ))

/-- COPY. The second-variable polynomial `N_β(t)` with an arbitrary twist. -/
noncomputable def betaFrequency (Hn : ℝ) (beta chiValue : ℕ → ℂ) (t : ℝ) : ℂ :=
  (1 / Hn) *
    ∑ n ∈ dyadicIntegers Hn,
      beta n * chiValue n * Complex.exp (Complex.I * t * Real.log (n : ℝ))

/-- COPY. The finite family of unit intervals that meet the large-frequency set. -/
def sparseUnitIntervals (x X B P A_s : ℝ) (Pset : Finset ℕ)
    (chiValue : ℕ → ℂ) (xi : ℝ) : Set ℤ :=
  {j : ℤ | ∃ t : ℝ, (j : ℝ) ≤ t ∧ t ≤ (j : ℝ) + 1 ∧
    |t| ≤ 2 * X * Real.rpow (Real.log x) B ∧
    Real.rpow (Real.log x) A_s *
      ‖bandPrimePolynomial P Pset chiValue xi t‖ > 1}

/-- COPY. Supremum of the `N_β` energy on one unit interval. -/
noncomputable def betaUnitIntervalEnergy (Hn : ℝ) (beta chiValue : ℕ → ℂ)
    (j : ℤ) : ℝ :=
  sSup ((fun t : ℝ => ‖betaFrequency Hn beta chiValue t‖ ^ 2) ''
    Set.Icc (j : ℝ) ((j : ℝ) + 1))

lemma exists_unit_interval_value_close_to_sSup (f : ℝ → ℝ) (j : ℤ) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ t ∈ Set.Icc (j : ℝ) ((j : ℝ) + 1),
      sSup (f '' Set.Icc (j : ℝ) ((j : ℝ) + 1)) - ε < f t := by
  have hne : (f '' Set.Icc (j : ℝ) ((j : ℝ) + 1)).Nonempty := by
    refine ⟨f (j : ℝ), Set.mem_image_of_mem _ ?_⟩
    simp
  obtain ⟨y, hy, hlt⟩ := Set.exists_lt_of_lt_csSup hne (sub_lt_self _ hε)
  obtain ⟨t, ht, rfl⟩ := Set.mem_image.mp hy
  exact ⟨t, ht, hlt⟩

/-- COPY. The energy integral in `maj:energy`. -/
noncomputable def majorEnergyIntegral (T : ℝ) (B M N : ℝ → ℂ) : ℝ :=
  ∫ t in (-T)..T, ‖B t * M t * N t‖ ^ 2

/-- COPY. `maj:sparse-frequency` — PD `05-major-arcs.tex:165-255`, Lemma 5.3. Correction from
refutation lane `sol-gate-b` fixes `C₁` before the asymptotic constants. -/
theorem sparse_frequency (δ C : ℝ) (hδ : 0 < δ) (hC : 0 < C) :
    ∀ C₁ : ℝ, 0 < C₁ → ∀ B A_s : ℝ, 0 < B → 0 < A_s →
      ∃ C₀ x₀ : ℝ, 0 < C₀ ∧ 2 < x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          let L := Real.log x
          ∀ X : ℝ, x / 2 ≤ X → X ≤ 2 * x →
          ∀ P : ℝ, (1 / 20 : ℝ) * Real.rpow L (1 / 10 : ℝ) ≤ Real.log P →
              Real.log P ≤ C₁ * Real.rpow L (1 / 5 : ℝ) →
              ∀ Pset : Finset ℕ,
                (∀ p ∈ Pset, p.Prime ∧ P ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * P) →
                ∀ q : ℕ, 1 ≤ q →
                  ∀ χ : DirichletCharacter ℂ q, ∀ xi : ℝ,
                    ∀ Hn : ℝ, Real.rpow x δ ≤ Hn → Hn ≤ 2 * x →
                      ∀ beta chiN : ℕ → ℂ,
                        (∀ n ∈ dyadicIntegers Hn, ‖beta n‖ ≤ Real.rpow L C) →
                        (∀ n, ‖chiN n‖ ≤ 1) →
                          let bad := sparseUnitIntervals x X B P A_s Pset
                            (fun p => (χ (p : ZMod q) : ℂ)) xi
                          (Set.ncard bad : ℝ) ≤
                            Real.exp (C₀ * Real.rpow L (91 / 100 : ℝ)) ∧
                          (∑' j : ℤ, if j ∈ bad then
                            betaUnitIntervalEnergy Hn beta chiN j else 0) ≤
                            C₀ * Real.rpow L (2 * C + 1) := by
  sorry

/-- NEW. Products `b` of one prime from every group, as a finite set of tuples. -/
def markedTupleSet (x : ℝ) (K : ℕ) (a : Fin K → ℝ) : Finset (Fin K → ℕ) :=
  Fintype.piFinset fun i => primeBand x (a i)

/-- NEW. `B_λ(t)` of (maj:polynomials), PD 05:311-313:
`(1/Y) Σ_b η(b/Y) e(-λb/Y) (∏_i V_i^{-1}) χ(b) b^{it}`. -/
def majorBPolynomial (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (Y lam : ℝ) (eta : ℝ → ℝ)
    {k : ℕ} (χ : DirichletCharacter ℂ k) (t : ℝ) : ℂ :=
  (1 / Y : ℂ) * ∑ tb ∈ markedTupleSet x K a,
    (eta ((tupleProduct tb : ℝ) / Y) : ℂ) *
      additiveCharacter (-lam * (tupleProduct tb : ℝ) / Y) *
      ((∏ i : Fin K, (bandMass x (a i))⁻¹ : ℝ) : ℂ) *
      χ ((tupleProduct tb : ℕ) : ZMod k) *
      Complex.exp (Complex.I * t * Real.log (tupleProduct tb : ℝ))

/-- NEW. `M_α(t)` with a Dirichlet character (maj:M-definition, PD 05:44-55). -/
def majorMPolynomial {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂) (x : ℝ)
    {k : ℕ} (χ : DirichletCharacter ℂ k) (t : ℝ) : ℂ :=
  alphaFrequency family x t (fun m => χ (m : ZMod k))

/-- NEW. `N_β(t)` with a Dirichlet character (maj:polynomials). -/
def majorNPolynomial (Hn : ℝ) (beta : ℕ → ℂ) {k : ℕ} (χ : DirichletCharacter ℂ k) (t : ℝ) : ℂ :=
  betaFrequency Hn beta (fun n => χ (n : ZMod k)) t

/-- NEW. The energy of (maj:energy): `∫_{|t| ≤ 2XL^{B₁}} |B_λ M_α N_β|²`, one modulus `k`
for the three characters. -/
def majorEnergy (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (Y lam B₁ : ℝ) (eta : ℝ → ℝ)
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ)
    {k : ℕ} (χb χm χn : DirichletCharacter ℂ k) : ℝ :=
  majorEnergyIntegral (2 * (family.Hm x * family.Hn x) * Real.rpow (Real.log x) B₁)
    (majorBPolynomial x K a Y lam eta χb) (majorMPolynomial family x χm)
    (majorNPolynomial (family.Hn x) beta χn)

/-- `t2:pd.major-separation` — PD 05:257-376.  REPLACES the frozen `major_separation`.  The
reduction of (maj:bound) to (maj:energy): arcs disjoint; on an arc `θ = h/k + λ/Y` all
variables are units mod `k`; six-character Fourier expansion of `e(h(bmn-ars-b+a)/k)` with total
mass `≤ k⁶`; exact Mellin separation (maj:Mellin-separation) of `ψ_λ(X(w-w'))` with transform
decay (maj:transform-decay) (`B₀` fixed after `A₀`); normalization (maj:XY-normalization);
product mean square (maj:product-mean) (exponent `C₄(C)`); tails beyond the retained rectangle
`|s'| ≤ L^{B₁}`, `|t| ≤ XL^{B₁}` (maj:retained-rectangle); Cauchy in `t`; the conjugate endpoint
polynomial `Q'` is covered by the same hypothesis (conjugate characters, `-λ`, `t ↦ -t`). -/
theorem major_separation (δ C c₁ c₂ : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (hδ : 0 < δ) (hC : 0 < C) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (ha : ValidBands K a)
    (eta psi : ℝ → ℝ) (heta : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) eta) (heta_supp : Function.support eta ⊆ Set.Icc 1 4)
    (heta_nonneg : ∀ y, 0 ≤ eta y) (heta_part : IsDyadicPartition eta)
    (hpsi : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) psi) (hpsi_supp : HasCompactSupport psi)
    (hpsi_one : ∀ t ∈ Set.Icc (-4 : ℝ) 4, psi t = 1) :
    ∀ A₀ D : ℝ, 0 < A₀ → 0 < D →
      ∃ B₁ A' : ℝ, 0 < B₁ ∧ 0 < A' ∧
        ∀ family : CoefficientFamily δ C c₁ c₂,
          ∃ C' x₀ : ℝ, 0 < C' ∧ 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
            ∀ beta : ℕ → ℂ,
              (∀ n, beta n ≠ 0 → n ∈ dyadicIntegers (family.Hn x) ∧
                roughAbove n (roughCutoff x)) →
              (∀ n ∈ dyadicIntegers (family.Hn x),
                ‖beta n‖ ≤ Real.rpow (Real.log x) C) →
              ∀ Y ∈ dyadicScales x K,
                (∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.rpow (Real.log x) A₀ →
                  ∀ χb χm χn : DirichletCharacter ℂ k, ∀ lam : ℝ,
                    |lam| ≤ 2 * Real.rpow (Real.log x) A₀ →
                      majorEnergy x K a Y lam B₁ eta family beta χb χm χn ≤
                        Real.rpow (Real.log x) (-A')) →
                ‖majorArcSum x K a Y A₀ family beta eta psi‖ ≤
                  C' * (family.Hm x * family.Hn x) * Y * Real.rpow (Real.log x) (-D) := by
  sorry

/-- `t2:pd.major-energy` — PD 05:371-433.  REPLACES the frozen `major_energy`.  (maj:energy):
for every fixed `A₀, B₁, A'` the energy is `≪ L^{-A'}`, uniformly in the characters of modulus
`≤ L^{A₀}` and `|λ| ≤ 2L^{A₀}`.  Proof: write `b = p b'` with `p ∈ 𝒫₁` in `O(L)` dyads `[P,2P)`;
Mellin inversion of `f_λ(y) = η(y)e(-λy)` with `L¹` norm `≪ L^{C₅}`; Minkowski reduces to
(maj:isolated-energy) uniformly in the shift `ξ` (`|Q_{b'}| ≪ 1`); on `|P_s| ≤ L^{-A_s}` use
(maj:product-mean); on the sparse unit intervals of `sparse_frequency` use
`|M_α(t)| ≪ L^{-A}` — this is exactly the hypothesis `HasLongCoefficientCancellation` (the role
of PD Lemma 5.2) applied with `B = B₁ + 1`. -/
theorem major_energy (δ C c₁ c₂ : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (hδ : 0 < δ) (hC : 0 < C) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (ha : ValidBands K a)
    (eta : ℝ → ℝ) (heta : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) eta) (heta_supp : Function.support eta ⊆ Set.Icc 1 4)
    (heta_nonneg : ∀ y, 0 ≤ eta y) :
    ∀ A₀ B₁ A' : ℝ, 0 < A₀ → 0 < B₁ → 0 < A' →
      ∀ family : CoefficientFamily δ C c₁ c₂, HasLongCoefficientCancellation family →
        ∃ C' x₀ : ℝ, 0 < C' ∧ 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
          ∀ beta : ℕ → ℂ,
            (∀ n, beta n ≠ 0 → n ∈ dyadicIntegers (family.Hn x) ∧
              roughAbove n (roughCutoff x)) →
            (∀ n ∈ dyadicIntegers (family.Hn x),
              ‖beta n‖ ≤ Real.rpow (Real.log x) C) →
            ∀ Y ∈ dyadicScales x K,
              ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.rpow (Real.log x) A₀ →
                ∀ χb χm χn : DirichletCharacter ℂ k, ∀ lam : ℝ,
                  |lam| ≤ 2 * Real.rpow (Real.log x) A₀ →
                    majorEnergy x K a Y lam B₁ eta family beta χb χm χn ≤
                      C' * Real.rpow (Real.log x) (-A') := by
  sorry

/-- `prop:major-term` — PD 05:9-30, Proposition 5.1.  CORRECTED restatement of the frozen
`major_term`: adds `‖β_n‖ ≤ L^C` and the smoothness/support of `η` (without them the bound is
false).  Proof: `major_separation` with `D`, then `major_energy` with the resulting `B₁, A'`.
Correction from refutation lane `sol-gate-b` fixes the family and cutoffs before `C_D` and `x₀`. -/
theorem major_term
    (δ C Dstar q_d c₁ c₂ : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (hδ : 0 < δ) (hC : 0 < C) (hD : 0 < Dstar)
    (hqd₀ : 0 < q_d) (hqd₁ : q_d < 1)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (ha : ValidBands K a) :
    ∀ A₀ : ℝ, 0 < A₀ →
      ∀ family : CoefficientFamily δ C c₁ c₂,
        HasLongCoefficientCancellation family →
        ∀ eta psi : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) eta → Function.support eta ⊆ Set.Icc 1 4 →
          (∀ y, 0 ≤ eta y) → IsDyadicPartition eta →
          ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) psi → HasCompactSupport psi →
          (∀ t ∈ Set.Icc (-4) 4, psi t = 1) →
          ∃ C_D x₀ : ℝ, 0 < C_D ∧ 2 ≤ x₀ ∧
          ∀ x : ℝ, x₀ ≤ x →
            ∀ Y, Y ∈ dyadicScales x K →
            ∀ beta : ℕ → ℂ,
              (∀ n, beta n ≠ 0 → n ∈ dyadicIntegers (family.Hn x) ∧
                roughAbove n (roughCutoff x)) →
              (∀ n ∈ dyadicIntegers (family.Hn x),
                ‖beta n‖ ≤ Real.rpow (Real.log x) C) →
                ‖majorArcSum x K a Y A₀ family beta eta psi‖ ≤
                  C_D * (family.Hm x * family.Hn x) * Y *
                    Real.rpow (Real.log x) (-Dstar) := by
  sorry

/-- COPY. `t2:pd.completion` — PD `05-major-arcs.tex:435-465` and 08-type-ii.tex:236-250.
Its proof now uses `minor_replacement` (B-PD-Chain) and the corrected `major_term`. -/
theorem completion
    (δ C Dstar q_d c₁ c₂ : ℝ)
    (hδ : 0 < δ) (hC : 0 < C) (hD : 0 < Dstar)
    (hqd₀ : 0 < q_d) (hqd₁ : q_d < 1)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ a : Fin K → ℝ, ValidBands K a →
      ∀ family : CoefficientFamily δ C c₁ c₂,
        HasLongCoefficientCancellation family →
        ∃ C' x₀ : ℝ, 0 < C' ∧ 2 ≤ x₀ ∧
          ∀ x : ℝ, x₀ ≤ x →
            ∀ beta : ℕ → ℂ,
              (∀ n, beta n ≠ 0 → n ∈ dyadicIntegers (family.Hn x) ∧
                roughAbove n (roughCutoff x)) →
              (∀ n ∈ dyadicIntegers (family.Hn x),
                ‖beta n‖ ≤ Real.rpow (Real.log x) C) →
              ∀ F : ℕ → ℂ, IsMarkedInvariant x K a F →
                ‖markedBilinearSum x K a q_d F (family.Hm x) (family.Hn x)
                  (family.interval x) (family.alpha x) beta‖ ≤
                    C' * (family.Hm x * family.Hn x) *
                      Real.rpow (Real.log x) (-Dstar) := by
  sorry

end

end ArtinPrimitiveRoots.TypeII.PD
