import ArtinPrimitiveRoots.TypeII.PD.MemoryResults
import ArtinPrimitiveRoots.TypeII.PP.Results
import ArtinPrimitiveRoots.TypeII.Proofs.pd7.PrimeMoments
import ArtinPrimitiveRoots.TypeII.Proofs.pd7.Cutoffs
import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.SparseEnergy
import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.Dyads
import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.TailPolynomial
import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.WeightedIntegral
import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.CharacterExpansion
import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.MajorArcArithmetic
import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.SeparationCutoff
import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.MajorArcPhase

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
set_option maxHeartbeats 1000000

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical Filter MeasureTheory
open scoped Topology FourierTransform
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

/-- Supremum of the `N_β` energy on one unit interval. -/
noncomputable def betaUnitIntervalEnergy (Hn : ℝ) (beta chiValue : ℕ → ℂ)
    (j : ℤ) : ℝ :=
  sSup ((fun t : ℝ => ‖betaFrequency Hn beta chiValue t‖ ^ 2) ''
    Set.Icc (j : ℝ) ((j : ℝ) + 1))

lemma pd7_beta_interval_bessel_bound (J : Finset ℤ) (Hn L C Rfreq N Rgram : ℝ)
    (hHn : 1 ≤ Hn) (hL : 0 ≤ L) (hRgram : 0 ≤ Rgram)
    (hJ : ∀ j ∈ J, |(j : ℝ)| ≤ Rfreq) (hcardJ : (J.card : ℝ) ≤ N)
    (hrow : ∀ S : Finset ℝ,
      (∀ t₁ ∈ S, ∀ t₂ ∈ S, t₁ ≠ t₂ → 1 ≤ |t₁ - t₂|) →
        (∀ t ∈ S, |t| ≤ Rfreq + 1) → (S.card : ℝ) ≤ N →
          ∀ i ∈ S, ∑ j ∈ S,
            ‖∑ n ∈ dyadicIntegers Hn,
              Complex.exp (Complex.I * i * Real.log (n : ℝ)) *
                star (Complex.exp (Complex.I * j * Real.log (n : ℝ)))‖ ≤ Rgram)
    (beta chiN : ℕ → ℂ)
    (hbeta : ∀ n ∈ dyadicIntegers Hn, ‖beta n‖ ≤ Real.rpow L C)
    (hchi : ∀ n, ‖chiN n‖ ≤ 1) :
    (∑ j ∈ J, betaUnitIntervalEnergy Hn beta chiN j) ≤
      6 * Rgram * (Real.rpow L C) ^ 2 / Hn := by
  let T : Finset ℕ := dyadicIntegers Hn
  let phase : ℝ → ℕ → ℂ := fun t n =>
    Complex.exp (Complex.I * t * Real.log (n : ℝ))
  let coeff : ℕ → ℂ := fun n => (1 / (Hn : ℂ)) * beta n * chiN n
  have hHnPos : 0 < Hn := lt_of_lt_of_le zero_lt_one hHn
  have hscale : ‖(1 / (Hn : ℂ))‖ = 1 / Hn := by
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hHnPos]
  have hKnonneg : 0 ≤ (1 / Hn) * Real.rpow L C :=
    mul_nonneg (by positivity) (Real.rpow_nonneg hL _)
  have hTcard : (T.card : ℝ) ≤ 3 * Hn := by
    apply prime_band_card_le_three_mul Hn hHn T
    intro n hn
    exact (Finset.mem_filter.mp hn).2
  have hcoef (n : ℕ) (hn : n ∈ T) :
      ‖coeff n‖ ≤ (1 / Hn) * Real.rpow L C := by
    have hβ := hbeta n hn
    have hχ := hchi n
    dsimp [coeff]
    rw [norm_mul, norm_mul, hscale]
    calc
      (1 / Hn) * ‖beta n‖ * ‖chiN n‖ ≤
          ((1 / Hn) * Real.rpow L C) * ‖chiN n‖ := by
        apply mul_le_mul_of_nonneg_right
        exact mul_le_mul_of_nonneg_left hβ
          (div_nonneg (by norm_num) (le_of_lt hHnPos))
        exact norm_nonneg _
      _ ≤ ((1 / Hn) * Real.rpow L C) * 1 :=
        mul_le_mul_of_nonneg_left hχ hKnonneg
      _ = (1 / Hn) * Real.rpow L C := by ring
  have hcoeffSq :
      (∑ n ∈ T, ‖coeff n‖ ^ 2) ≤ 3 * (Real.rpow L C) ^ 2 / Hn := by
    calc
      _ ≤ ∑ _n ∈ T, ((1 / Hn) * Real.rpow L C) ^ 2 := by
        apply Finset.sum_le_sum
        intro n hn
        exact (sq_le_sq₀ (norm_nonneg _) hKnonneg).2 (hcoef n hn)
      _ = (T.card : ℝ) * ((1 / Hn) * Real.rpow L C) ^ 2 := by simp
      _ ≤ (3 * Hn) * ((1 / Hn) * Real.rpow L C) ^ 2 :=
        mul_le_mul_of_nonneg_right hTcard (sq_nonneg _)
      _ = _ := by field_simp [ne_of_gt hHnPos]
  have hpoly (t : ℝ) : betaFrequency Hn beta chiN t =
      ∑ n ∈ T, coeff n * phase t n := by
    calc
      _ = (1 / (Hn : ℂ)) *
          ∑ n ∈ T, beta n * chiN n *
            Complex.exp (Complex.I * t * Real.log (n : ℝ)) := rfl
      _ = ∑ n ∈ T, (1 / (Hn : ℂ)) *
          (beta n * chiN n * Complex.exp (Complex.I * t * Real.log (n : ℝ))) := by
        rw [Finset.mul_sum]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro n hn
        dsimp [coeff, phase]
        ring
  have hBessel := pd7_interval_sup_exponential_bound J T phase coeff
    Rfreq N Rgram hRgram hJ hcardJ hrow
  have henergy :
      (∑ j ∈ J, betaUnitIntervalEnergy Hn beta chiN j) ≤
        2 * Rgram * (∑ n ∈ T, ‖coeff n‖ ^ 2) := by
    simpa [betaUnitIntervalEnergy, hpoly] using hBessel
  calc
    _ ≤ 2 * Rgram * (∑ n ∈ T, ‖coeff n‖ ^ 2) := henergy
    _ ≤ 2 * Rgram * (3 * (Real.rpow L C) ^ 2 / Hn) :=
      mul_le_mul_of_nonneg_left hcoeffSq (by positivity)
    _ = _ := by ring

/-- COPY. The finite family of unit intervals that meet the large-frequency set. -/
def sparseUnitIntervals (x X B P A_s : ℝ) (Pset : Finset ℕ)
    (chiValue : ℕ → ℂ) (xi : ℝ) : Set ℤ :=
  {j : ℤ | ∃ t : ℝ, (j : ℝ) ≤ t ∧ t ≤ (j : ℝ) + 1 ∧
    |t| ≤ 2 * X * Real.rpow (Real.log x) B ∧
    Real.rpow (Real.log x) A_s *
      ‖bandPrimePolynomial P Pset chiValue xi t‖ > 1}

lemma sparseUnitIntervals_empty_of_small_density
    (x X B P A_s : ℝ) (Pset : Finset ℕ) (chiValue : ℕ → ℂ) (xi : ℝ)
    (hL : 0 < Real.log x) (hAs : 0 < A_s) (hP : 0 < P)
    (hchi : ∀ p ∈ Pset, ‖chiValue p‖ ≤ 1)
    (hdensity : (Pset.card : ℝ) / P ≤ Real.rpow (Real.log x) (-A_s)) :
    sparseUnitIntervals x X B P A_s Pset chiValue xi = ∅ := by
  ext j
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨t, hjlo, hjhi, ht, hbad⟩
  have hpoly := bandPrimePolynomial_norm_le P hP Pset chiValue xi t hchi
  have hthreshold : Real.rpow (Real.log x) A_s * ((Pset.card : ℝ) / P) ≤ 1 := by
    calc
      _ ≤ Real.rpow (Real.log x) A_s * Real.rpow (Real.log x) (-A_s) :=
        mul_le_mul_of_nonneg_left hdensity (Real.rpow_nonneg (le_of_lt hL) _)
      _ = 1 := by
        calc
          _ = Real.rpow (Real.log x) (A_s + -A_s) :=
            (Real.rpow_add hL A_s (-A_s)).symm
          _ = 1 := by simp
  have hle : Real.rpow (Real.log x) A_s *
      ‖bandPrimePolynomial P Pset chiValue xi t‖ ≤ 1 :=
    (mul_le_mul_of_nonneg_left hpoly (Real.rpow_nonneg (le_of_lt hL) _)).trans hthreshold
  exact (not_lt_of_ge hle) hbad

lemma sparseUnitIntervals_empty_of_large_logP
    (x X B P A_s Ccard : ℝ) (Pset : Finset ℕ) (chiValue : ℕ → ℂ) (xi : ℝ)
    (hL : 0 < Real.log x) (hAs : 0 < A_s) (hP : 0 < P) (hCcard : 0 < Ccard)
    (hcard : (Pset.card : ℝ) ≤ Ccard * P / Real.log P)
    (hlogP : Ccard * Real.rpow (Real.log x) A_s ≤ Real.log P)
    (hchi : ∀ p ∈ Pset, ‖chiValue p‖ ≤ 1) :
    sparseUnitIntervals x X B P A_s Pset chiValue xi = ∅ := by
  have hlogPpos : 0 < Real.log P := by
    have hpow : 0 < Real.rpow (Real.log x) A_s := Real.rpow_pos_of_pos hL A_s
    exact lt_of_lt_of_le (mul_pos hCcard hpow) hlogP
  have hcardDensity : (Pset.card : ℝ) / P ≤ Ccard / Real.log P := by
    apply (div_le_div_iff₀ hP hlogPpos).2
    have hmul := mul_le_mul_of_nonneg_right hcard hlogPpos.le
    calc
      (Pset.card : ℝ) * Real.log P ≤
          (Ccard * P / Real.log P) * Real.log P := hmul
      _ = Ccard * P := by field_simp [ne_of_gt hlogPpos]
  have hdensity' : Ccard / Real.log P ≤ 1 / Real.rpow (Real.log x) A_s := by
    apply (div_le_div_iff₀ hlogPpos (Real.rpow_pos_of_pos hL A_s)).2
    simpa using hlogP
  have hdensityInv : Ccard / Real.log P ≤ (Real.rpow (Real.log x) A_s)⁻¹ := by
    simpa [one_div] using hdensity'
  have hdensity : (Pset.card : ℝ) / P ≤ Real.rpow (Real.log x) (-A_s) := by
    calc
      _ ≤ Ccard / Real.log P := hcardDensity
      _ ≤ (Real.rpow (Real.log x) A_s)⁻¹ := hdensityInv
      _ = Real.rpow (Real.log x) (-A_s) :=
        (Real.rpow_neg (le_of_lt hL) A_s).symm
  exact sparseUnitIntervals_empty_of_small_density x X B P A_s Pset chiValue xi
    hL hAs hP hchi hdensity

lemma pd7_sparse_moment_order (L D : ℝ) (hL : 1 ≤ L)
    (hD : (1 / 20 : ℝ) * Real.rpow L (1 / 10 : ℝ) ≤ D) :
    ∃ r : ℕ, 4 ≤ r ∧ (r : ℝ) ≤ 21 * Real.rpow L (9 / 10 : ℝ) ∧ L ≤ (r : ℝ) * D := by
  let r : ℕ := ⌈20 * Real.rpow L (9 / 10 : ℝ)⌉₊
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hpowpos : 0 < Real.rpow L (9 / 10 : ℝ) := Real.rpow_pos_of_pos hLpos _
  have hlow : 20 * Real.rpow L (9 / 10 : ℝ) ≤ (r : ℝ) := by
    dsimp [r]
    exact_mod_cast Nat.le_ceil (20 * Real.rpow L (9 / 10 : ℝ))
  have hhigh : (r : ℝ) ≤ 21 * Real.rpow L (9 / 10 : ℝ) := by
    have hceil := Nat.ceil_lt_add_one
      (show 0 ≤ 20 * Real.rpow L (9 / 10 : ℝ) by positivity)
    have hceilR : (r : ℝ) < 20 * Real.rpow L (9 / 10 : ℝ) + 1 := by
      dsimp [r]
      exact_mod_cast hceil
    have hpowone : 1 ≤ Real.rpow L (9 / 10 : ℝ) :=
      Real.one_le_rpow hL (by norm_num)
    linarith
  have hrfour : 4 ≤ r := by
    have hrR : (4 : ℝ) ≤ (r : ℝ) := by
      calc
        (4 : ℝ) ≤ 20 * Real.rpow L (9 / 10 : ℝ) := by
          have : 1 ≤ Real.rpow L (9 / 10 : ℝ) := Real.one_le_rpow hL (by norm_num)
          norm_num at this ⊢
          nlinarith
        _ ≤ (r : ℝ) := hlow
    exact_mod_cast hrR
  have hpow : Real.rpow L (9 / 10 : ℝ) * Real.rpow L (1 / 10 : ℝ) = L := by
    calc
      _ = Real.rpow L ((9 / 10 : ℝ) + 1 / 10) :=
        (Real.rpow_add hLpos _ _).symm
      _ = L := by norm_num [Real.rpow_one]
  have hprod : L ≤ (r : ℝ) * D := by
    have hD0 : 0 ≤ (1 / 20 : ℝ) * Real.rpow L (1 / 10 : ℝ) :=
      mul_nonneg (by norm_num) (Real.rpow_nonneg (le_trans (by norm_num) hL) _)
    have hr0 : 0 ≤ (r : ℝ) := Nat.cast_nonneg _
    have hmul := mul_le_mul hlow hD hD0 hr0
    calc
      L = 20 * Real.rpow L (9 / 10 : ℝ) *
          ((1 / 20 : ℝ) * Real.rpow L (1 / 10 : ℝ)) := by
        calc
          L = Real.rpow L (9 / 10 : ℝ) * Real.rpow L (1 / 10 : ℝ) := hpow.symm
          _ = _ := by ring
      _ ≤ (r : ℝ) * D := hmul
  exact ⟨r, hrfour, hhigh, hprod⟩

lemma pd7_log_le_rpow_one_hundredth_eventually :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      2 ≤ L ∧ Real.log L ≤ Real.rpow L (1 / 100 : ℝ) := by
  have hlittle :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 100)).bound
      (by norm_num : (0 : ℝ) < 1)
  have heventual : ∀ᶠ L : ℝ in atTop,
      2 ≤ L ∧ Real.log L ≤ Real.rpow L (1 / 100 : ℝ) := by
    filter_upwards [hlittle, eventually_ge_atTop (2 : ℝ)] with L hsmall hL
    have hsmall' :
        ‖Real.log L‖ ≤ 1 * ‖Real.rpow L (1 / 100 : ℝ)‖ := by
      change ‖Real.log L‖ ≤ 1 * ‖Real.rpow L (1 / 100 : ℝ)‖ at hsmall
      exact hsmall
    change |Real.log L| ≤ 1 * |Real.rpow L (1 / 100 : ℝ)| at hsmall'
    have hpowAbs : |Real.rpow L (1 / 100 : ℝ)| = Real.rpow L (1 / 100 : ℝ) :=
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _)
    rw [hpowAbs, one_mul] at hsmall'
    exact ⟨hL, (le_abs_self _).trans hsmall'⟩
  obtain ⟨L₁, hL₁⟩ := (eventually_atTop.1 heventual)
  refine ⟨max 2 L₁, ?_⟩
  intro L hL
  have hL₁' : L₁ ≤ L := le_trans (le_max_right 2 L₁) hL
  exact hL₁ L hL₁'

lemma pd7_log_rpow_small_eventually (s ε : ℝ) (hs : 0 < s) (hε : 0 < ε) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      3 ≤ L ∧ 1 ≤ Real.log L ∧
        Real.rpow (Real.log L) s ≤ ε * Real.rpow L (9 / 100 : ℝ) := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop s
    (by norm_num : (0 : ℝ) < 9 / 100)).bound hε
  have heventual : ∀ᶠ L : ℝ in atTop,
      3 ≤ L ∧ 1 ≤ Real.log L ∧
        Real.rpow (Real.log L) s ≤ ε * Real.rpow L (9 / 100 : ℝ) := by
    filter_upwards [hsmall, eventually_ge_atTop (3 : ℝ)] with L hnorm hL
    have hExp1 : Real.exp 1 ≤ L := Real.exp_one_lt_three.le.trans hL
    have hLlog : 1 ≤ Real.log L := by
      calc
        1 = Real.log (Real.exp 1) := by simp
        _ ≤ Real.log L := Real.log_le_log (Real.exp_pos _) hExp1
    have hnorm' : ‖Real.rpow (Real.log L) s‖ ≤
        ε * ‖Real.rpow L (9 / 100 : ℝ)‖ := by
      change ‖Real.rpow (Real.log L) s‖ ≤
        ε * ‖Real.rpow L (9 / 100 : ℝ)‖ at hnorm
      exact hnorm
    change |Real.rpow (Real.log L) s| ≤
      ε * |Real.rpow L (9 / 100 : ℝ)| at hnorm'
    have hA0 : 0 ≤ Real.rpow (Real.log L) s := Real.rpow_nonneg (by linarith) _
    have hB0 : 0 ≤ Real.rpow L (9 / 100 : ℝ) := Real.rpow_nonneg (by linarith) _
    have hbound : Real.rpow (Real.log L) s ≤ ε * Real.rpow L (9 / 100 : ℝ) := by
      calc
        _ = |Real.rpow (Real.log L) s| := (abs_of_nonneg hA0).symm
        _ ≤ ε * |Real.rpow L (9 / 100 : ℝ)| := hnorm'
        _ = _ := congrArg (fun z : ℝ => ε * z) (abs_of_nonneg hB0)
    exact ⟨hL, hLlog, hbound⟩
  obtain ⟨L₁, hL₁⟩ := eventually_atTop.1 heventual
  refine ⟨max 3 L₁, ?_⟩
  intro L hL
  have hL₁' : L₁ ≤ L := (le_max_right 3 L₁).trans hL
  exact hL₁ L hL₁'

lemma pd7_sparse_unit_interval_count_bound
    (L P R B A_s C₁ Cmv Pcard : ℝ) (r U : ℕ)
    (bad : Set ℤ) (f : ℝ → ℂ)
    (hL : 2 ≤ L) (hlogL : Real.log L ≤ Real.rpow L (1 / 100 : ℝ))
    (hP : 1 ≤ P) (hB : 0 < B) (hAs : 0 < A_s)
    (hC₁ : 0 < C₁) (hCmv : 0 < Cmv)
    (hlogP : Real.log P ≤ C₁ * Real.rpow L (1 / 5 : ℝ))
    (hR : 0 ≤ R) (hRbound : R ≤ 4 * Real.exp L * Real.rpow L B)
    (hPr : Real.exp L ≤ P ^ r) (hUone : 1 ≤ U)
    (hUbound : (U : ℝ) ≤ (2 * P) ^ r)
    (hPcard : 0 ≤ Pcard) (hPcardBound : Pcard ≤ 3 * P)
    (hrLow : 4 ≤ r)
    (hr : (r : ℝ) ≤ 21 * Real.rpow L (9 / 10 : ℝ))
    (hbad : ∀ j ∈ bad, ∃ t : ℝ, (j : ℝ) ≤ t ∧ t ≤ (j : ℝ) + 1 ∧
      |t| ≤ R ∧ Real.rpow L (-A_s) ≤ ‖f t‖)
    (hmoment : ∀ S : Finset ℝ, (∀ t ∈ S, |t| ≤ R) →
      (∀ t₁ ∈ S, ∀ t₂ ∈ S, t₁ ≠ t₂ → 1 ≤ |t₁ - t₂|) →
        (∑ t ∈ S, ‖f t‖ ^ (2 * r)) ≤
          Cmv * (2 * R + 1 + (U : ℝ) * Real.log (2 * (U : ℝ))) *
            Real.log (2 * (U : ℝ)) ^ 2 * (r.factorial : ℝ) * Pcard ^ r *
              (1 / P) ^ (2 * r)) :
    (bad.ncard : ℝ) ≤
      Real.exp (pd7_sparse_moment_count_constant B A_s C₁ Cmv *
        Real.rpow L (91 / 100 : ℝ)) := by
  let u : ℝ := Real.log (2 * (U : ℝ))
  let V : ℝ := Real.rpow L (-A_s)
  let A : ℝ := Cmv * (2 * R + 1 + (U : ℝ) * u) * u ^ 2 *
    (r.factorial : ℝ) * Pcard ^ r * (1 / P) ^ (2 * r)
  have hV : 0 < V := Real.rpow_pos_of_pos (by linarith) _
  have hbad' : ∀ j ∈ bad, ∃ t : ℝ, (j : ℝ) ≤ t ∧ t ≤ (j : ℝ) + 1 ∧
      |t| ≤ R ∧ V ≤ ‖f t‖ := by
    intro j hj
    simpa [V] using hbad j hj
  have hmoment' : ∀ S : Finset ℝ, (∀ t ∈ S, |t| ≤ R) →
      (∀ t₁ ∈ S, ∀ t₂ ∈ S, t₁ ≠ t₂ → 1 ≤ |t₁ - t₂|) →
        (∑ t ∈ S, ‖f t‖ ^ (2 * r)) ≤ A := by
    intro S hS hsep
    have h := hmoment S hS hsep
    simpa [A, u, mul_assoc] using h
  have hcount := pd7_sparse_bad_card_bound R V f r A hR hV hbad' hmoment'
  have hscalar := pd7_sparse_moment_expression_bound L P R B A_s C₁ Cmv Pcard
    r U hL hlogL hP hB hAs hC₁ hCmv hlogP hR hRbound hPr hUone hUbound
    hPcard hPcardBound hrLow hr
  have hcountExpr : (bad.ncard : ℝ) ≤
      2 * Cmv * (2 * R + 1 + (U : ℝ) * u) * u ^ 2 *
        (r.factorial : ℝ) * Pcard ^ r * (1 / P) ^ (2 * r) /
          (Real.rpow L (-A_s)) ^ (2 * r) := by
    calc
      _ ≤ 2 * A / V ^ (2 * r) := hcount
      _ = _ := by dsimp [A, V]; ring
  simpa [u] using hcountExpr.trans hscalar.2

lemma pd7_sparse_tail_error_bound (c cδ C3 : ℝ)
    (hc : 0 < c) (hcδ : 0 < cδ) (hC3 : 0 < C3) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      3 ≤ L ∧ 1 ≤ Real.log L ∧
        Real.exp (c * Real.rpow L (91 / 100 : ℝ)) *
          (Real.exp (-cδ * L) +
            Real.exp (-L / Real.rpow (Real.log L) C3)) ≤ 1 := by
  let log2 : ℝ := Real.log 2
  let ε : ℝ := 1 / (4 * (c + log2 + 1))
  have hlog2 : 0 < log2 := Real.log_pos (by norm_num)
  have hε : 0 < ε := by dsimp [ε, log2]; positivity
  have hnegT : Tendsto (fun L : ℝ => Real.rpow L (-(9 / 100 : ℝ)))
      atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 9 / 100)
  have hnegSmall : ∀ᶠ L : ℝ in atTop,
      Real.rpow L (-(9 / 100 : ℝ)) < cδ / (4 * c) :=
    hnegT.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < cδ / (4 * c)))
  have hinvT : Tendsto (fun L : ℝ => L⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hinvSmall : ∀ᶠ L : ℝ in atTop,
      log2 * L⁻¹ < cδ / 4 :=
    (hinvT.const_mul log2).eventually
      (Iio_mem_nhds (by simpa using (div_pos hcδ (by norm_num : (0 : ℝ) < 4))))
  obtain ⟨L₁, hL₁⟩ := eventually_atTop.1 hnegSmall
  obtain ⟨L₂, hL₂⟩ := eventually_atTop.1 hinvSmall
  obtain ⟨L₃, hL₃⟩ := pd7_log_rpow_small_eventually C3 ε hC3 hε
  let L₀ := max L₁ (max L₂ L₃)
  refine ⟨L₀, ?_⟩
  intro L hL₀
  have hL₁' : L₁ ≤ L := le_trans (le_max_left _ _) hL₀
  have hL₂' : L₂ ≤ L := le_trans (le_max_left _ _)
    ((le_max_right L₁ (max L₂ L₃)).trans hL₀)
  have hL₃' : L₃ ≤ L := le_trans (le_max_right _ _)
    ((le_max_right L₁ (max L₂ L₃)).trans hL₀)
  have hbig : 3 ≤ L ∧ 1 ≤ Real.log L ∧
      Real.rpow (Real.log L) C3 ≤ ε * Real.rpow L (9 / 100 : ℝ) := hL₃ L hL₃'
  have hLpos : 0 < L := by linarith
  have hlogLpos : 0 < Real.log L := by linarith
  have hlogLnonneg : 0 ≤ Real.log L := hlogLpos.le
  have hsmall₁ : c * Real.rpow L (-(9 / 100 : ℝ)) < cδ / 4 := by
    have h := hL₁ L hL₁'
    calc
      _ < c * (cδ / (4 * c)) := mul_lt_mul_of_pos_left h hc
      _ = cδ / 4 := by field_simp [ne_of_gt hc]
  have hsmall₂ : log2 / L < cδ / 4 := by
    have h := hL₂ L hL₂'
    simpa [div_eq_mul_inv] using h
  have hpowDiv : Real.rpow L (91 / 100 : ℝ) / L =
      Real.rpow L (-(9 / 100 : ℝ)) := by
    calc
      _ = Real.rpow L (91 / 100 : ℝ) / Real.rpow L (1 : ℝ) := by
        exact congrArg (fun z : ℝ => Real.rpow L (91 / 100 : ℝ) / z)
          (Real.rpow_one L).symm
      _ = Real.rpow L ((91 / 100 : ℝ) - 1) := (Real.rpow_sub hLpos _ _).symm
      _ = _ := by congr 1 <;> norm_num
  have hratio : (c * Real.rpow L (91 / 100 : ℝ) + log2) / L < cδ / 2 := by
    calc
      _ = c * (Real.rpow L (91 / 100 : ℝ) / L) + log2 / L := by
        field_simp [ne_of_gt hLpos]
        <;> ring
      _ = c * Real.rpow L (-(9 / 100 : ℝ)) + log2 / L := by rw [hpowDiv]
      _ < _ := by linarith [hsmall₁, hsmall₂]
  have hexp₁ : c * Real.rpow L (91 / 100 : ℝ) - cδ * L < -log2 := by
    have hnum := (div_lt_iff₀ hLpos).mp hratio
    have hhalf : (cδ / 2) * L ≤ cδ * L :=
      mul_le_mul_of_nonneg_right (by linarith) hLpos.le
    linarith
  have htail₁ : Real.exp (c * Real.rpow L (91 / 100 : ℝ)) *
      Real.exp (-cδ * L) ≤ 1 / 2 := by
    calc
      _ = Real.exp (c * Real.rpow L (91 / 100 : ℝ) - cδ * L) := by
        rw [← Real.exp_add]
        congr 1 <;> ring
      _ ≤ Real.exp (-log2) := Real.exp_le_exp.mpr hexp₁.le
      _ = 1 / 2 := by
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        norm_num [log2]
  have hpowProd : Real.rpow L (91 / 100 : ℝ) * Real.rpow L (9 / 100 : ℝ) = L := by
    calc
      _ = Real.rpow L ((91 / 100 : ℝ) + 9 / 100) :=
        (Real.rpow_add hLpos _ _).symm
      _ = Real.rpow L 1 := by congr 1 <;> norm_num
      _ = L := Real.rpow_one L
  have hpow09LE : Real.rpow L (9 / 100 : ℝ) ≤ L := by
    have hLge : 1 ≤ L := le_trans (by norm_num : 1 ≤ (3 : ℝ)) hbig.1
    have hExponent : (9 / 100 : ℝ) ≤ 1 := by norm_num
    calc
      Real.rpow L (9 / 100 : ℝ) ≤ Real.rpow L 1 :=
        Real.rpow_le_rpow_of_exponent_le hLge hExponent
      _ = L := Real.rpow_one L
  have hlogPowSmall := hbig.2.2
  have hlogPowNonneg : 0 ≤ Real.rpow (Real.log L) C3 :=
    Real.rpow_nonneg hlogLnonneg _
  have hlog2eps : 0 ≤ log2 * ε := mul_nonneg hlog2.le hε.le
  have hceps : 0 ≤ c * ε := mul_nonneg hc.le hε.le
  have hcoef : c * ε + log2 * ε ≤ 1 := by
    have hden : 0 < 4 * (c + log2 + 1) := by positivity
    dsimp [ε]
    field_simp [ne_of_gt hden]
    nlinarith [hc, hlog2]
  have htailProd :
      (c * Real.rpow L (91 / 100 : ℝ) + log2) * Real.rpow (Real.log L) C3 ≤ L := by
    calc
      _ = c * Real.rpow L (91 / 100 : ℝ) * Real.rpow (Real.log L) C3 +
          log2 * Real.rpow (Real.log L) C3 := by ring
      _ ≤ c * Real.rpow L (91 / 100 : ℝ) *
            (ε * Real.rpow L (9 / 100 : ℝ)) +
          log2 * (ε * Real.rpow L (9 / 100 : ℝ)) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hlogPowSmall
            (mul_nonneg hc.le (Real.rpow_nonneg hLpos.le _))
        · exact mul_le_mul_of_nonneg_left hlogPowSmall hlog2.le
      _ = c * ε * (Real.rpow L (91 / 100 : ℝ) *
          Real.rpow L (9 / 100 : ℝ)) + log2 * ε * Real.rpow L (9 / 100 : ℝ) := by ring
      _ = c * ε * L + log2 * ε * Real.rpow L (9 / 100 : ℝ) := by rw [hpowProd]
      _ ≤ c * ε * L + log2 * ε * L := by
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hpow09LE hlog2eps)
      _ = (c * ε + log2 * ε) * L := by ring
      _ ≤ L := by
        have := mul_le_mul_of_nonneg_right hcoef hLpos.le
        simpa using this
  have hdiv : c * Real.rpow L (91 / 100 : ℝ) + log2 ≤
      L / Real.rpow (Real.log L) C3 := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hlogLpos C3)).2
    exact htailProd
  have hexp₂ : c * Real.rpow L (91 / 100 : ℝ) -
      L / Real.rpow (Real.log L) C3 ≤ -log2 := by linarith
  have htail₂ : Real.exp (c * Real.rpow L (91 / 100 : ℝ)) *
      Real.exp (-L / Real.rpow (Real.log L) C3) ≤ 1 / 2 := by
    calc
      _ = Real.exp (c * Real.rpow L (91 / 100 : ℝ) -
          L / Real.rpow (Real.log L) C3) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-log2) := Real.exp_le_exp.mpr hexp₂
      _ = 1 / 2 := by
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        norm_num [log2]
  have hsum : Real.exp (c * Real.rpow L (91 / 100 : ℝ)) *
      (Real.exp (-cδ * L) +
        Real.exp (-L / Real.rpow (Real.log L) C3)) ≤ 1 := by
    calc
      _ = Real.exp (c * Real.rpow L (91 / 100 : ℝ)) * Real.exp (-cδ * L) +
          Real.exp (c * Real.rpow L (91 / 100 : ℝ)) *
            Real.exp (-L / Real.rpow (Real.log L) C3) := by rw [mul_add]
      _ ≤ 1 / 2 + 1 / 2 := add_le_add htail₁ htail₂
      _ = 1 := by norm_num
  exact ⟨hbig.1, hbig.2.1, hsum⟩

lemma pd7_integer_phase_sum_one_eq_dyadic (Hn v : ℝ) :
    integerResiduePhaseSum 1 (0 : ZMod 1) v Hn (2 * Hn) =
      ∑ n ∈ dyadicIntegers Hn,
        Complex.exp (Complex.I * v * Real.log (n : ℝ)) := by
  unfold integerResiduePhaseSum dyadicIntegers
  have hfilter :
      (Finset.range (⌊2 * Hn⌋₊ + 1)).filter (fun n : ℕ =>
        Hn ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * Hn ∧ (n : ZMod 1) = 0) =
      (Finset.range (⌊2 * Hn⌋₊ + 1)).filter (fun n : ℕ =>
        Hn ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * Hn) := by
    apply Finset.ext
    intro n
    have hres (n : ℕ) : (n : ZMod 1) = (0 : ZMod 1) := Subsingleton.elim _ _
    simp [hres]
  have hfilter' :
      (Finset.range (⌊2 * Hn⌋₊ + 1)).filter (fun n : ℕ =>
        Hn ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * Hn ∧ (n : ZMod 1) = 0) =
      (Finset.range (⌊2 * Hn⌋₊ + 1)).filter (fun n : ℕ =>
        Hn ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * Hn) := by
    simpa using hfilter
  rw [hfilter']

lemma pd7_residue_phase_sum_one_eq_dyadic (Hn v : ℝ) :
    residuePhaseSum Hn 1 (0 : ZMod 1) v
      {n : ℕ | Hn ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * Hn} =
      ∑ n ∈ dyadicIntegers Hn,
        Complex.exp (Complex.I * v * Real.log (n : ℝ)) := by
  have hres (n : ℕ) : (n : ZMod 1) = (0 : ZMod 1) := Subsingleton.elim _ _
  simp [residuePhaseSum, dyadicIntegers, Set.mem_setOf_eq, hres,
    and_assoc, and_left_comm]

lemma pd7_complex_exp_phase_difference (u v : ℝ) (n : ℕ) :
    Complex.exp (Complex.I * u * Real.log (n : ℝ)) *
        star (Complex.exp (Complex.I * v * Real.log (n : ℝ))) =
      Complex.exp (Complex.I * (u - v) * Real.log (n : ℝ)) := by
  let a : ℝ := Real.log (n : ℝ)
  change Complex.exp (Complex.I * u * (a : ℂ)) *
      star (Complex.exp (Complex.I * v * (a : ℂ))) =
    Complex.exp (Complex.I * (u - v) * (a : ℂ))
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp [Complex.conj_ofReal, Complex.conj_I]
  ring

lemma pd7_dyadic_gram_rows_from_phase_bounds (S : Finset ℝ) (Hn F Cnear Cfar T ρ σ : ℝ)
    (hHn : 1 ≤ Hn) (hF : 0 ≤ F) (hCnear3 : 3 ≤ Cnear)
    (hCnear : 0 ≤ Cnear) (hCfar : 0 ≤ Cfar)
    (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hrange : ∀ t ∈ S, |t| ≤ F)
    (hsep : ∀ t₁ ∈ S, ∀ t₂ ∈ S, t₁ ≠ t₂ → 1 ≤ |t₁ - t₂|)
    (hmoderate : ∀ v : ℝ, 1 ≤ |v| → |v| ≤ T →
      ‖∑ n ∈ dyadicIntegers Hn,
        Complex.exp (Complex.I * v * Real.log (n : ℝ))‖ ≤
          Cnear * Hn * (|v|⁻¹ + ρ))
    (hhigh : ∀ v : ℝ, 1 ≤ |v| → T < |v| → |v| ≤ 2 * F →
      ‖∑ n ∈ dyadicIntegers Hn,
        Complex.exp (Complex.I * v * Real.log (n : ℝ))‖ ≤ Cfar * Hn * σ) :
    ∀ i ∈ S,
      (∑ j ∈ S,
        ‖∑ n ∈ dyadicIntegers Hn,
          Complex.exp (Complex.I * i * Real.log (n : ℝ)) *
            star (Complex.exp (Complex.I * j * Real.log (n : ℝ)))‖) ≤
        max Cnear Cfar * Hn *
          (1 + 2 * (1 + Real.log (2 * (F + 1))) + (S.card : ℝ) * (ρ + σ)) := by
  let G : ℝ → ℝ → ℂ := fun i j =>
    ∑ n ∈ dyadicIntegers Hn,
      Complex.exp (Complex.I * i * Real.log (n : ℝ)) *
        star (Complex.exp (Complex.I * j * Real.log (n : ℝ)))
  have hTcard : (dyadicIntegers Hn).card ≤ 3 * Hn :=
    prime_band_card_le_three_mul Hn hHn (dyadicIntegers Hn)
      (by intro n hn; exact (Finset.mem_filter.mp hn).2)
  have hGdiff (i j : ℝ) : G i j =
      ∑ n ∈ dyadicIntegers Hn,
        Complex.exp (Complex.I * (i - j) * Real.log (n : ℝ)) := by
    dsimp [G]
    apply Finset.sum_congr rfl
    intro n hn
    exact pd7_complex_exp_phase_difference i j n
  have hdiag : ∀ i ∈ S, ‖G i i‖ ≤ 3 * Hn := by
    intro i hi
    have hG : G i i = ((dyadicIntegers Hn).card : ℂ) := by
      rw [hGdiff]
      simp
    rw [hG, Complex.norm_natCast]
    exact hTcard
  have hnear : ∀ i ∈ S, ∀ j ∈ S, j ≠ i →
      1 ≤ |j - i| → |j - i| ≤ T →
        ‖G i j‖ ≤ Cnear * Hn * ((|j - i|)⁻¹ + ρ) := by
    intro i hi j hj hne hdist hsmall
    rw [hGdiff]
    have h := hmoderate (i - j) (by simpa [abs_sub_comm] using hdist)
      (by simpa [abs_sub_comm] using hsmall)
    simpa [Complex.ofReal_sub, abs_sub_comm] using h
  have hfar : ∀ i ∈ S, ∀ j ∈ S, j ≠ i →
      1 ≤ |j - i| → T < |j - i| → ‖G i j‖ ≤ Cfar * Hn * σ := by
    intro i hi j hj hne hdist hlarge
    have hi' := abs_le.mp (hrange i hi)
    have hj' := abs_le.mp (hrange j hj)
    have hdiff : |i - j| ≤ 2 * F := by
      rw [abs_le]
      constructor <;> linarith
    rw [hGdiff]
    simpa [Complex.ofReal_sub, abs_sub_comm] using
      hhigh (i - j) (by simpa [abs_sub_comm] using hdist)
        (by simpa [abs_sub_comm] using hlarge)
        (by simpa [abs_sub_comm] using hdiff)
  let Cg := max Cnear Cfar
  have hCg : 0 ≤ Cg := le_max_of_le_left hCnear
  have hnearC : Cnear ≤ Cg := le_max_left _ _
  have hfarC : Cfar ≤ Cg := le_max_right _ _
  have h3Cg : 3 ≤ Cg := hCnear3.trans hnearC
  have hdiag' : ∀ i ∈ S, ‖G i i‖ ≤ Cg * Hn := by
    intro i hi
    exact (hdiag i hi).trans (mul_le_mul_of_nonneg_right h3Cg (by positivity))
  have hnear' : ∀ i ∈ S, ∀ j ∈ S, j ≠ i →
      1 ≤ |j - i| → |j - i| ≤ T →
        ‖G i j‖ ≤ Cg * Hn * ((|j - i|)⁻¹ + ρ) := by
    intro i hi j hj hne hdist hsmall
    exact (hnear i hi j hj hne hdist hsmall).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hnearC (by positivity)) (by positivity))
  have hfar' : ∀ i ∈ S, ∀ j ∈ S, j ≠ i →
      1 ≤ |j - i| → T < |j - i| → ‖G i j‖ ≤ Cg * Hn * σ := by
    intro i hi j hj hne hdist hlarge
    calc
      _ ≤ Cfar * Hn * σ := hfar i hi j hj hne hdist hlarge
      _ ≤ Cg * Hn * σ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hfarC (by positivity)) hσ
  have hrows := pd7_gram_all_rows_bound S F (Cg * Hn) T ρ σ hF
    (mul_nonneg hCg (by positivity)) hρ hσ hrange hsep G hdiag' hnear' hfar'
  intro i hi
  have h := hrows i hi
  simpa [G, Cg, mul_assoc] using h

lemma pd7_beta_energy_from_phase_bounds (J : Finset ℤ)
    (Hn L C F N Cnear Cfar T ρ σ : ℝ)
    (hHn : 1 ≤ Hn) (hL : 0 ≤ L) (hF : 0 ≤ F) (hN : 0 ≤ N)
    (hCnear3 : 3 ≤ Cnear) (hCnear : 0 ≤ Cnear) (hCfar : 0 ≤ Cfar)
    (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hJ : ∀ j ∈ J, |(j : ℝ)| ≤ F) (hcardJ : (J.card : ℝ) ≤ N)
    (beta chiN : ℕ → ℂ)
    (hbeta : ∀ n ∈ dyadicIntegers Hn, ‖beta n‖ ≤ Real.rpow L C)
    (hchi : ∀ n, ‖chiN n‖ ≤ 1)
    (hmoderate : ∀ v : ℝ, 1 ≤ |v| → |v| ≤ T →
      ‖∑ n ∈ dyadicIntegers Hn,
        Complex.exp (Complex.I * v * Real.log (n : ℝ))‖ ≤
          Cnear * Hn * (|v|⁻¹ + ρ))
    (hhigh : ∀ v : ℝ, 1 ≤ |v| → T < |v| → |v| ≤ 2 * (F + 1) →
      ‖∑ n ∈ dyadicIntegers Hn,
        Complex.exp (Complex.I * v * Real.log (n : ℝ))‖ ≤ Cfar * Hn * σ) :
    (∑ j ∈ J, betaUnitIntervalEnergy Hn beta chiN j) ≤
      6 * (max Cnear Cfar * Hn) *
        (1 + 2 * (1 + Real.log (2 * (F + 2))) + N * (ρ + σ)) *
          (Real.rpow L C) ^ 2 / Hn := by
  let Rgram := max Cnear Cfar * Hn *
    (1 + 2 * (1 + Real.log (2 * (F + 2))) + N * (ρ + σ))
  have hRgram : 0 ≤ Rgram := by
    dsimp [Rgram]
    have hlog : 0 ≤ Real.log (2 * (F + 2)) := Real.log_nonneg (by linarith)
    positivity
  have hrow : ∀ S : Finset ℝ,
      (∀ t₁ ∈ S, ∀ t₂ ∈ S, t₁ ≠ t₂ → 1 ≤ |t₁ - t₂|) →
        (∀ t ∈ S, |t| ≤ F + 1) → (S.card : ℝ) ≤ N →
          ∀ i ∈ S, ∑ j ∈ S,
            ‖∑ n ∈ dyadicIntegers Hn,
              Complex.exp (Complex.I * i * Real.log (n : ℝ)) *
                star (Complex.exp (Complex.I * j * Real.log (n : ℝ)))‖ ≤ Rgram := by
    intro S hsep hbound hcard i hi
    have hrows := pd7_dyadic_gram_rows_from_phase_bounds S Hn (F + 1)
      Cnear Cfar T ρ σ hHn (by linarith) hCnear3 hCnear hCfar hρ hσ
      hbound hsep hmoderate hhigh
    have hrowi := hrows i hi
    have hcardErr : (S.card : ℝ) * (ρ + σ) ≤ N * (ρ + σ) :=
      mul_le_mul_of_nonneg_right hcard (add_nonneg hρ hσ)
    have hinner :
        1 + 2 * (1 + Real.log (2 * (F + 2))) + (S.card : ℝ) * (ρ + σ) ≤
          1 + 2 * (1 + Real.log (2 * (F + 2))) + N * (ρ + σ) := by
      linarith
    have hinner' :
        1 + 2 * (1 + Real.log (2 * (F + 1 + 1))) + (S.card : ℝ) * (ρ + σ) ≤
          1 + 2 * (1 + Real.log (2 * (F + 2))) + N * (ρ + σ) := by
      have hlog : Real.log (2 * (F + 1 + 1)) = Real.log (2 * (F + 2)) := by
        congr 1 <;> ring
      rw [hlog]
      exact hinner
    exact hrowi.trans (mul_le_mul_of_nonneg_left hinner' (by positivity))
  have hB := pd7_beta_interval_bessel_bound J Hn L C F N Rgram
    hHn hL hRgram hJ hcardJ hrow beta chiN hbeta hchi
  calc
    _ ≤ 6 * Rgram * (Real.rpow L C) ^ 2 / Hn := hB
    _ = _ := by dsimp [Rgram]; ring

lemma pd7_beta_energy_log_bound (J : Finset ℤ)
    (Hn L C F N Cnear Cfar T ρ σ D : ℝ)
    (hHn : 1 ≤ Hn) (hL : 1 ≤ L) (hF : 0 ≤ F) (hN : 0 ≤ N) (hD : 0 ≤ D)
    (hCnear3 : 3 ≤ Cnear) (hCnear : 0 ≤ Cnear) (hCfar : 0 ≤ Cfar)
    (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hJ : ∀ j ∈ J, |(j : ℝ)| ≤ F) (hcardJ : (J.card : ℝ) ≤ N)
    (hlog : Real.log (2 * (F + 2)) ≤ D * L)
    (herr : N * (ρ + σ) ≤ 1)
    (beta chiN : ℕ → ℂ)
    (hbeta : ∀ n ∈ dyadicIntegers Hn, ‖beta n‖ ≤ Real.rpow L C)
    (hchi : ∀ n, ‖chiN n‖ ≤ 1)
    (hmoderate : ∀ v : ℝ, 1 ≤ |v| → |v| ≤ T →
      ‖∑ n ∈ dyadicIntegers Hn,
        Complex.exp (Complex.I * v * Real.log (n : ℝ))‖ ≤
          Cnear * Hn * (|v|⁻¹ + ρ))
    (hhigh : ∀ v : ℝ, 1 ≤ |v| → T < |v| → |v| ≤ 2 * (F + 1) →
      ‖∑ n ∈ dyadicIntegers Hn,
        Complex.exp (Complex.I * v * Real.log (n : ℝ))‖ ≤ Cfar * Hn * σ) :
    (∑ j ∈ J, betaUnitIntervalEnergy Hn beta chiN j) ≤
      6 * max Cnear Cfar * (4 + 2 * D) * Real.rpow L (2 * C + 1) := by
  have hbase := pd7_beta_energy_from_phase_bounds J Hn L C F N Cnear Cfar T ρ σ
    hHn (le_trans (by norm_num) hL) hF hN hCnear3 hCnear hCfar hρ hσ
    hJ hcardJ beta chiN hbeta hchi
    hmoderate hhigh
  have hfac :
      1 + 2 * (1 + Real.log (2 * (F + 2))) + N * (ρ + σ) ≤ (4 + 2 * D) * L := by
    calc
      _ ≤ 1 + 2 * (1 + D * L) + 1 := by
        gcongr <;> assumption
      _ = 4 + 2 * D * L := by ring
      _ ≤ (4 + 2 * D) * L := by nlinarith [hL]
  have hcancel :
      6 * (max Cnear Cfar * Hn) *
        (1 + 2 * (1 + Real.log (2 * (F + 2))) + N * (ρ + σ)) *
          (Real.rpow L C) ^ 2 / Hn =
        6 * max Cnear Cfar *
          (1 + 2 * (1 + Real.log (2 * (F + 2))) + N * (ρ + σ)) *
            (Real.rpow L C) ^ 2 := by
    field_simp [ne_of_gt (lt_of_lt_of_le zero_lt_one hHn)] <;> ring
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hpow : (Real.rpow L C) ^ 2 * L = Real.rpow L (2 * C + 1) := by
    have hpowC : (Real.rpow L C) ^ 2 = Real.rpow L (C * 2) := by
      calc
        _ = Real.rpow (Real.rpow L C) (2 : ℝ) :=
          (Real.rpow_natCast (Real.rpow L C) 2).symm
        _ = Real.rpow L (C * 2) :=
          (Real.rpow_mul (le_of_lt hLpos) C 2).symm
    have hOne : Real.rpow L 1 = L := Real.rpow_one L
    calc
      _ = Real.rpow L (C * 2) * L := by rw [hpowC]
      _ = Real.rpow L (C * 2) * Real.rpow L 1 :=
        congrArg (fun z : ℝ => Real.rpow L (C * 2) * z) hOne.symm
      _ = Real.rpow L (C * 2 + 1) := (Real.rpow_add hLpos _ _).symm
      _ = _ := by congr 1 <;> ring
  calc
    _ ≤ 6 * (max Cnear Cfar * Hn) *
        (1 + 2 * (1 + Real.log (2 * (F + 2))) + N * (ρ + σ)) *
          (Real.rpow L C) ^ 2 / Hn := hbase
    _ = 6 * max Cnear Cfar *
        (1 + 2 * (1 + Real.log (2 * (F + 2))) + N * (ρ + σ)) *
          (Real.rpow L C) ^ 2 := hcancel
    _ ≤ 6 * max Cnear Cfar * ((4 + 2 * D) * L) * (Real.rpow L C) ^ 2 := by
      calc
        _ = (6 * max Cnear Cfar * (Real.rpow L C) ^ 2) *
            (1 + 2 * (1 + Real.log (2 * (F + 2))) + N * (ρ + σ)) := by ring
        _ ≤ (6 * max Cnear Cfar * (Real.rpow L C) ^ 2) * ((4 + 2 * D) * L) :=
          mul_le_mul_of_nonneg_left hfac (by positivity)
        _ = _ := by ring
    _ = 6 * max Cnear Cfar * (4 + 2 * D) * Real.rpow L (2 * C + 1) := by
      calc
        _ = 6 * max Cnear Cfar * (4 + 2 * D) * ((Real.rpow L C) ^ 2 * L) := by ring
        _ = _ := by rw [hpow]

theorem pd7_dyadic_moderate_phase_bound (δ C : ℝ) (hδ : 0 < δ) (hC : 0 < C) :
    ∃ Cmod cδ x₀ : ℝ, 0 < Cmod ∧ 0 < cδ ∧ 2 < x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        let L := Real.log x
        ∀ Hn : ℝ, Real.rpow x δ ≤ Hn →
          ∀ v : ℝ, 1 ≤ |v| → |v| ≤ Real.exp (L / (Real.log L) ^ 2) →
            ‖∑ n ∈ dyadicIntegers Hn,
              Complex.exp (Complex.I * v * Real.log (n : ℝ))‖ ≤
                Cmod * Hn * (|v|⁻¹ + Real.rpow x (-cδ)) := by
  obtain ⟨Cmod, cδ, x₀m, hCmod, hcδ, hx₀m, hmod⟩ :=
    ArtinPrimitiveRoots.TypeII.PD.moderate_phase δ C hδ hC
  let x₀ := max x₀m 3
  have hx₀m' : x₀m ≤ x₀ := by dsimp [x₀]; exact le_max_left _ _
  have h3 : 2 < x₀ := by dsimp [x₀]; linarith [le_max_right x₀m (3 : ℝ)]
  refine ⟨Cmod, cδ, x₀, hCmod, hcδ, h3, ?_⟩
  intro x hx L Hn hHn v hv1 hvT
  have hxM : x₀m ≤ x := hx₀m'.trans hx
  have hx3 : (3 : ℝ) ≤ x := (le_max_right x₀m (3 : ℝ)).trans hx
  have hxgt : 1 < x := by
    linarith
  have hLpos : 0 < L := Real.log_pos hxgt
  have hExp1 : Real.exp 1 ≤ x := by
    have hExp1' : Real.exp 1 ≤ (3 : ℝ) := Real.exp_one_lt_three.le
    exact hExp1'.trans hx3
  have hLge : 1 ≤ L := by
    calc
      1 = Real.log (Real.exp 1) := by simp
      _ ≤ Real.log x := Real.log_le_log (Real.exp_pos _) hExp1
  have hq : (1 : ℝ) ≤ Real.rpow L C := Real.one_le_rpow hLge hC.le
  have hqcast : ((1 : ℕ) : ℝ) ≤ Real.rpow (Real.log x) C := by
    simpa [L] using hq
  have hHnpos : 0 < Hn := lt_of_lt_of_le (Real.rpow_pos_of_pos (by linarith : 0 < x) δ) hHn
  have hphase := hmod x hxM Hn hHn 1 (by norm_num) hqcast
    (0 : ZMod 1) v hv1 hvT Hn (2 * Hn) le_rfl (by linarith) (by rfl)
  have hthird := hphase.2.2
  rw [pd7_integer_phase_sum_one_eq_dyadic] at hthird
  have hthird' :
      (1 / Hn) *
        ‖∑ n ∈ dyadicIntegers Hn,
          Complex.exp (Complex.I * v * Real.log (n : ℝ))‖ ≤
          Cmod * (|v|⁻¹ + Real.rpow x (-cδ)) := by
    simpa using hthird
  calc
    _ = Hn * ((1 / Hn) *
        ‖∑ n ∈ dyadicIntegers Hn,
          Complex.exp (Complex.I * v * Real.log (n : ℝ))‖) := by
      field_simp [ne_of_gt hHnpos]
    _ ≤ Hn * (Cmod * (|v|⁻¹ + Real.rpow x (-cδ))) :=
      mul_le_mul_of_nonneg_left hthird' hHnpos.le
    _ = Cmod * Hn * (|v|⁻¹ + Real.rpow x (-cδ)) := by ring

theorem pd7_dyadic_high_phase_bound (C : ℝ) (hC : 0 < C) :
    ∃ Cfar C3 x₀ : ℝ, 0 < Cfar ∧ 0 < C3 ∧ 2 < x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        let L := Real.log x
        ∀ Hn : ℝ, Real.exp (L / (Real.log L) ^ 2) ≤ Hn → Hn ≤ 2 * x →
          ∀ v : ℝ, Real.exp (L / (2 * (Real.log L) ^ 2)) ≤ |v| →
            |v| ≤ 4 * x ^ 3 →
              ‖∑ n ∈ dyadicIntegers Hn,
                Complex.exp (Complex.I * v * Real.log (n : ℝ))‖ ≤
                  Cfar * Hn * Real.exp (-L / (Real.rpow (Real.log L) C3)) := by
  obtain ⟨C3, hC3⟩ := ArtinPrimitiveRoots.TypeII.PP.log_phase
  rcases hC3 with ⟨hC3pos, hC3fun⟩
  obtain ⟨Cfar, x₀p, hCfar, hx₀p, hphase⟩ := hC3fun C hC
  let x₀ := max x₀p 3
  have hx₀p' : x₀p ≤ x₀ := by dsimp [x₀]; exact le_max_left _ _
  have h3 : 2 < x₀ := by dsimp [x₀]; linarith [le_max_right x₀p (3 : ℝ)]
  refine ⟨Cfar, C3, x₀, hCfar, hC3pos, h3, ?_⟩
  intro x hx L Hn hHnLo hHnHi v hvLo hvHi
  have hxP : x₀p ≤ x := hx₀p'.trans hx
  have hx3 : (3 : ℝ) ≤ x := (le_max_right x₀p (3 : ℝ)).trans hx
  have hxgt : 1 < x := by linarith
  have hLge : 1 ≤ L := by
    have hExp1 : Real.exp 1 ≤ x := by
      exact Real.exp_one_lt_three.le.trans hx3
    calc
      1 = Real.log (Real.exp 1) := by simp
      _ ≤ Real.log x := Real.log_le_log (Real.exp_pos _) hExp1
  have hq : (1 : ℝ) ≤ Real.rpow L C := Real.one_le_rpow hLge hC.le
  have hqcast : ((1 : ℕ) : ℝ) ≤ Real.rpow (Real.log x) C := by
    simpa [L] using hq
  have hN5 : Hn ≤ 2 * Real.rpow x 5 := by
    calc
      Hn ≤ 2 * x := hHnHi
      _ ≤ 2 * Real.rpow x 5 := by
        have hxPow : x ≤ Real.rpow x 5 := by
          calc
            x = Real.rpow x 1 := by simp
            _ ≤ Real.rpow x 5 :=
              Real.rpow_le_rpow_of_exponent_le (le_of_lt hxgt) (by norm_num)
        exact mul_le_mul_of_nonneg_left hxPow (by norm_num : (0 : ℝ) ≤ 2)
  have hvHi' : |v| ≤ 4 * Real.rpow x 3 := by
    have hpow3 : x ^ (3 : ℕ) = Real.rpow x (3 : ℝ) :=
      (Real.rpow_natCast x 3).symm
    simpa only [hpow3] using hvHi
  have hphase' := hphase x hxP Hn hHnLo hN5 1 (by norm_num) hqcast
    (0 : ZMod 1) v hvLo hvHi' Hn (2 * Hn) le_rfl (by rfl)
  rw [pd7_residue_phase_sum_one_eq_dyadic] at hphase'
  simpa using hphase'

lemma exists_unit_interval_value_close_to_sSup (f : ℝ → ℝ) (j : ℤ) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ t ∈ Set.Icc (j : ℝ) ((j : ℝ) + 1),
      sSup (f '' Set.Icc (j : ℝ) ((j : ℝ) + 1)) - ε < f t := by
  have hne : (f '' Set.Icc (j : ℝ) ((j : ℝ) + 1)).Nonempty := by
    refine ⟨f (j : ℝ), Set.mem_image_of_mem _ ?_⟩
    simp
  obtain ⟨y, hy, hlt⟩ := exists_lt_of_lt_csSup hne (sub_lt_self _ hε)
  have hmem := (Set.mem_image f (Set.Icc (j : ℝ) ((j : ℝ) + 1)) y).1 hy
  obtain ⟨t, ht, hty⟩ := hmem
  subst y
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
  intro C₁ hC₁ B A_s hB hA_s
  obtain ⟨Cmod, cδ, xmod, hCmod, hcδ, hxmod, hmod⟩ :=
    pd7_dyadic_moderate_phase_bound δ C hδ hC
  obtain ⟨Cfar, C3, xfar, hCfar, hC3, hxfar, hfar⟩ :=
    pd7_dyadic_high_phase_bound 1 (by norm_num)
  obtain ⟨Cmv, hCmv, hMoment⟩ := bandPrimePolynomial_separated_moment
  let Ccount := pd7_sparse_moment_count_constant B A_s C₁ Cmv
  have hlog6 : 0 < Real.log 6 := Real.log_pos (by norm_num)
  have hlog21 : 0 < Real.log 21 := Real.log_pos (by norm_num)
  have hCcount : 0 < Ccount := by
    dsimp [Ccount, pd7_sparse_moment_count_constant]
    positivity
  let Cnear : ℝ := max 3 Cmod
  have hCnear3 : 3 ≤ Cnear := le_max_left _ _
  have hCnear : 0 ≤ Cnear := le_trans (by norm_num) hCnear3
  let Dfreq : ℝ := B + 5
  have hDfreq : 0 < Dfreq := by dsimp [Dfreq]; linarith
  let Cenergy : ℝ := 6 * max Cnear Cfar * (4 + 2 * Dfreq)
  have hCenergy : 0 < Cenergy := by dsimp [Cenergy]; positivity
  let C₀ : ℝ := max Ccount Cenergy + 1
  have hC₀ : 0 < C₀ := by
    have hmax : Ccount ≤ max Ccount Cenergy := le_max_left _ _
    dsimp [C₀]
    linarith
  obtain ⟨Lsmall, hLsmall⟩ := pd7_log_le_rpow_one_hundredth_eventually
  obtain ⟨Ltail, hLtail⟩ :=
    pd7_sparse_tail_error_bound Ccount cδ C3 hCcount hcδ hC3
  have hlogAtTop : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  let LδTarget : ℝ := max 1 (1 / δ)
  have hLδEvent : ∀ᶠ L : ℝ in atTop, LδTarget ≤ Real.log L :=
    hlogAtTop.eventually_ge_atTop LδTarget
  obtain ⟨Lδ, hLδ⟩ := eventually_atTop.1 hLδEvent
  have hpowBAtTop : Tendsto (fun L : ℝ => Real.rpow L (99 / 100 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 99 / 100)
  have hLBEvent : ∀ᶠ L : ℝ in atTop, B ≤ Real.rpow L (99 / 100 : ℝ) :=
    hpowBAtTop.eventually_ge_atTop B
  obtain ⟨LB, hLB⟩ := eventually_atTop.1 hLBEvent
  let Lbase := max Lsmall (max Ltail (max Lδ LB))
  let x₀ := max 3 (max xmod (max xfar (Real.exp Lbase)))
  refine ⟨C₀, x₀, hC₀, ?_, ?_⟩
  · have hthree : 3 ≤ x₀ := by dsimp [x₀]; exact le_max_left _ _
    exact lt_of_lt_of_le (by norm_num : (2 : ℝ) < 3) hthree
  · intro x hx
    dsimp only
    intro X hXlo hXhi P hPlo hPhi Pset hPset q hq χ xi Hn hHnlo hHnhi beta chiN hbeta hchiN
    let L : ℝ := Real.log x
    let R : ℝ := 2 * X * Real.rpow L B
    let f : ℝ → ℂ := fun t => bandPrimePolynomial P Pset
      (fun p => (χ (p : ZMod q) : ℂ)) xi t
    let bad : Set ℤ := sparseUnitIntervals x X B P A_s Pset
      (fun p => (χ (p : ZMod q) : ℂ)) xi
    have hxthree : 3 ≤ x := by
      have hxsub : max xmod (max xfar (Real.exp Lbase)) ≤ x :=
        (le_max_right _ _).trans hx
      exact le_trans (le_max_left _ _) hx
    have hxmod' : xmod ≤ x := by
      have hxsub : max xmod (max xfar (Real.exp Lbase)) ≤ x :=
        (le_max_right _ _).trans hx
      exact (le_max_left _ _).trans hxsub
    have hxsub : max xfar (Real.exp Lbase) ≤ x := by
      have h := (le_max_right _ _).trans hx
      exact (le_max_right _ _).trans h
    have hxfar' : xfar ≤ x := (le_max_left _ _).trans hxsub
    have hexpBase : Real.exp Lbase ≤ x := (le_max_right _ _).trans hxsub
    have hxpos : 0 < x := by linarith
    have hLbase : Lbase ≤ L := by
      calc
        Lbase = Real.log (Real.exp Lbase) := by rw [Real.log_exp]
        _ ≤ Real.log x := Real.log_le_log (Real.exp_pos _) hexpBase
    have hLsmall' : Lsmall ≤ L := le_trans (le_max_left _ _) hLbase
    have hLtail' : Ltail ≤ L := by
      have h := (le_max_right Lsmall (max Ltail (max Lδ LB))).trans hLbase
      exact le_trans (le_max_left _ _) h
    have hLδ' : Lδ ≤ L := by
      have h := (le_max_right Lsmall (max Ltail (max Lδ LB))).trans hLbase
      have h' := (le_max_right Ltail (max Lδ LB)).trans h
      exact le_trans (le_max_left _ _) h'
    have hLB' : LB ≤ L := by
      have h := (le_max_right Lsmall (max Ltail (max Lδ LB))).trans hLbase
      have h' := (le_max_right Ltail (max Lδ LB)).trans h
      exact (le_max_right Lδ LB).trans h'
    have hLinfo := hLsmall L hLsmall'
    have hTailInfo := hLtail L hLtail'
    have hLge : 1 ≤ L := by linarith [hLinfo.1]
    have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hLge
    have hlogLsmall : Real.log L ≤ Real.rpow L (1 / 100 : ℝ) := hLinfo.2
    have hL3 : 3 ≤ L := hTailInfo.1
    have hlogLge : 1 ≤ Real.log L := hTailInfo.2.1
    have hlogLpos : 0 < Real.log L := lt_of_lt_of_le zero_lt_one hlogLge
    have hlogLnonneg : 0 ≤ Real.log L := le_trans (by norm_num) hlogLge
    have hdeltaLog : LδTarget ≤ Real.log L := hLδ L hLδ'
    have hlogLDelta : 1 / δ ≤ Real.log L := (le_max_right _ _).trans hdeltaLog
    have hLpowBbound : B ≤ Real.rpow L (99 / 100 : ℝ) := hLB L hLB'
    have hLpowBge : 1 ≤ Real.rpow L B := Real.one_le_rpow hLge hB.le
    have hLpowSmall : Real.rpow L (1 / 100 : ℝ) ≤ L := by
      calc
        Real.rpow L (1 / 100 : ℝ) ≤ Real.rpow L 1 :=
          Real.rpow_le_rpow_of_exponent_le hLge (by norm_num)
        _ = L := Real.rpow_one L
    have hBLog : B * Real.log L ≤ L := by
      have h₁ : B * Real.log L ≤ Real.rpow L (99 / 100 : ℝ) * Real.log L :=
        mul_le_mul_of_nonneg_right hLpowBbound hlogLnonneg
      have h₂ : Real.rpow L (99 / 100 : ℝ) * Real.log L ≤
          Real.rpow L (99 / 100 : ℝ) * Real.rpow L (1 / 100 : ℝ) :=
        mul_le_mul_of_nonneg_left hlogLsmall
          (Real.rpow_nonneg hLpos.le _)
      have hPowOne : Real.rpow L (99 / 100 : ℝ) *
          Real.rpow L (1 / 100 : ℝ) = L := by
        calc
          _ = Real.rpow L ((99 / 100 : ℝ) + 1 / 100) :=
            (Real.rpow_add hLpos _ _).symm
          _ = Real.rpow L 1 := by congr 1 <;> norm_num
          _ = L := Real.rpow_one L
      calc
        B * Real.log L ≤ Real.rpow L (99 / 100 : ℝ) * Real.log L := h₁
        _ ≤ Real.rpow L (99 / 100 : ℝ) * Real.rpow L (1 / 100 : ℝ) := h₂
        _ = L := hPowOne
    have hLpowBexp : Real.rpow L B ≤ x := by
      calc
        Real.rpow L B = Real.exp (Real.log L * B) := Real.rpow_def_of_pos hLpos B
        _ ≤ Real.exp L := Real.exp_le_exp.mpr (by
          calc
            Real.log L * B = B * Real.log L := by ring
            _ ≤ L := hBLog)
        _ = x := Real.exp_log hxpos
    have hXpos : 0 < X := lt_of_lt_of_le (div_pos hxpos (by norm_num)) hXlo
    have hR0 : 0 ≤ R := by
      dsimp [R]
      exact mul_nonneg (mul_nonneg (by norm_num) hXpos.le)
        (Real.rpow_nonneg hLpos.le _)
    have hRbound : R ≤ 4 * Real.exp L * Real.rpow L B := by
      dsimp [R]
      rw [Real.exp_log hxpos]
      have hXm : 2 * X ≤ 4 * x := by
        calc
          2 * X ≤ 2 * (2 * x) := mul_le_mul_of_nonneg_left hXhi (by norm_num)
          _ = 4 * x := by ring
      exact mul_le_mul_of_nonneg_right
        hXm (Real.rpow_nonneg hLpos.le _)
    have hRquad : R ≤ 4 * x ^ 2 := by
      calc
        R ≤ 4 * x * Real.rpow L B := by
          dsimp [R]
          have hXm : 2 * X ≤ 4 * x := by
            calc
              2 * X ≤ 2 * (2 * x) := mul_le_mul_of_nonneg_left hXhi (by norm_num)
              _ = 4 * x := by ring
          exact mul_le_mul_of_nonneg_right hXm (Real.rpow_nonneg hLpos.le _)
        _ ≤ 4 * x * x := mul_le_mul_of_nonneg_left hLpowBexp (by positivity)
        _ = 4 * x ^ 2 := by ring
    have hhighFreq : 2 * (R + 2) ≤ 4 * x ^ 3 := by
      have hxSq : 9 ≤ x ^ 2 := by
        have hsq : (3 : ℝ) ^ 2 ≤ x ^ 2 :=
          (sq_le_sq₀ (by norm_num) (by linarith [hxthree])).2 hxthree
        norm_num at hsq ⊢
        exact hsq
      have hxMinus : 1 ≤ x - 2 := by linarith
      have hprod : 9 ≤ x ^ 2 * (x - 2) := by
        have h := mul_le_mul hxSq hxMinus (by norm_num : (0 : ℝ) ≤ 1)
          (by positivity : 0 ≤ x ^ 2)
        simpa using h
      have hpoly : 8 * x ^ 2 + 4 ≤ 4 * x ^ 3 := by
        have h₁ : 4 ≤ 4 * (x ^ 2 * (x - 2)) := by
          calc
            4 ≤ 36 := by norm_num
            _ ≤ 4 * (x ^ 2 * (x - 2)) := by
              have hmul := mul_le_mul_of_nonneg_left hprod
                (by norm_num : (0 : ℝ) ≤ 4)
              have hprod4 : 36 ≤ 4 * (x ^ 2 * (x - 2)) := by
                calc
                  36 = 4 * 9 := by norm_num
                  _ ≤ 4 * (x ^ 2 * (x - 2)) := hmul
              exact hprod4
        calc
          8 * x ^ 2 + 4 ≤ 8 * x ^ 2 + 4 * (x ^ 2 * (x - 2)) := by linarith
          _ = 4 * x ^ 3 := by ring
      calc
        2 * (R + 2) ≤ 2 * (4 * x ^ 2 + 2) :=
          mul_le_mul_of_nonneg_left (add_le_add_left hRquad 2) (by norm_num)
        _ = 8 * x ^ 2 + 4 := by ring
        _ ≤ 4 * x ^ 3 := hpoly
    have hlogFreq : Real.log (2 * (R + 3)) ≤ Dfreq * L := by
      have hLBone : 1 ≤ Real.rpow L B := hLpowBge
      have hupper : 2 * (R + 3) ≤ 10 * x * Real.rpow L B := by
        have hR' : R ≤ 4 * x * Real.rpow L B := by
          calc
            R ≤ 4 * Real.exp L * Real.rpow L B := hRbound
            _ = 4 * x * Real.rpow L B := by rw [Real.exp_log hxpos]
        have hxLB : 3 ≤ x * Real.rpow L B := by
          have h := mul_le_mul (by linarith : 3 ≤ x) hLBone
            (by norm_num : (0 : ℝ) ≤ 1) (by positivity)
          simpa using h
        calc
          2 * (R + 3) ≤ 2 * (4 * x * Real.rpow L B + 3) := by
            apply mul_le_mul_of_nonneg_left
            · linarith [hR']
            · norm_num
          _ = 8 * x * Real.rpow L B + 6 := by ring
          _ ≤ 10 * x * Real.rpow L B := by
            have h6 : 6 ≤ 2 * (x * Real.rpow L B) := by
              calc
                6 = 2 * 3 := by norm_num
                _ ≤ 2 * (x * Real.rpow L B) :=
                  mul_le_mul_of_nonneg_left hxLB (by norm_num : (0 : ℝ) ≤ 2)
            nlinarith [h6]
      have hlogMono : Real.log (2 * (R + 3)) ≤
          Real.log (10 * x * Real.rpow L B) :=
        Real.log_le_log (by positivity) hupper
      have hlog10 : Real.log 10 ≤ 9 := by
        have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10)
        linarith
      have hlogProduct : Real.log (10 * x * Real.rpow L B) =
          Real.log 10 + Real.log x + B * Real.log L := by
        have hlogPow : Real.log (Real.rpow L B) = B * Real.log L := by
          calc
            Real.log (Real.rpow L B) = Real.log (Real.exp (Real.log L * B)) :=
              congrArg Real.log (Real.rpow_def_of_pos hLpos B)
            _ = Real.log L * B := Real.log_exp _
            _ = B * Real.log L := by ring
        calc
          Real.log (10 * x * Real.rpow L B) =
              Real.log (10 * x) + Real.log (Real.rpow L B) :=
            Real.log_mul (mul_ne_zero (by norm_num : (10 : ℝ) ≠ 0) (ne_of_gt hxpos))
              (ne_of_gt (Real.rpow_pos_of_pos hLpos B))
          _ = Real.log 10 + Real.log x + B * Real.log L := by
            rw [Real.log_mul (by norm_num : (10 : ℝ) ≠ 0) (ne_of_gt hxpos), hlogPow]
      have hlogRHS : Real.log 10 + Real.log x + B * Real.log L ≤ (B + 5) * L := by
        rw [show Real.log x = L by rfl]
        have hlog10L : Real.log 10 ≤ 3 * L := by
          calc
            Real.log 10 ≤ 9 := hlog10
            _ = 3 * 3 := by norm_num
            _ ≤ 3 * L := mul_le_mul_of_nonneg_left hL3 (by norm_num : (0 : ℝ) ≤ 3)
        calc
          _ ≤ 3 * L + L + L := add_le_add (add_le_add hlog10L le_rfl) hBLog
          _ = 5 * L := by ring
          _ ≤ (B + 5) * L := by
            have hBL : 0 ≤ B * L := mul_nonneg hB.le hLpos.le
            calc
              5 * L ≤ 5 * L + B * L := by linarith
              _ = (B + 5) * L := by ring
      dsimp [Dfreq]
      calc
        _ ≤ Real.log (10 * x * Real.rpow L B) := hlogMono
        _ = _ := hlogProduct
        _ ≤ _ := hlogRHS
    have hdeltaSquare : (1 / δ) ≤ (Real.log L) ^ 2 := by
      have h₁ : 1 / δ ≤ Real.log L := hlogLDelta
      have h₂ : 1 ≤ Real.log L := hlogLge
      have h := mul_le_mul h₁ h₂ (by norm_num : (0 : ℝ) ≤ 1)
        (by linarith : 0 ≤ Real.log L)
      nlinarith [h]
    have hdenPos : 0 < (Real.log L) ^ 2 := pow_pos hlogLpos 2
    have hdeltaInv : 1 / (Real.log L) ^ 2 ≤ δ := by
      apply (div_le_iff₀ hdenPos).2
      calc
        1 = δ * (1 / δ) := by field_simp [ne_of_gt hδ]
        _ ≤ δ * (Real.log L) ^ 2 :=
          mul_le_mul_of_nonneg_left hdeltaSquare hδ.le
    have hTle : Real.exp (L / (Real.log L) ^ 2) ≤ Real.rpow x δ := by
      have harg : L / (Real.log L) ^ 2 ≤ δ * L := by
        calc
          _ = (1 / (Real.log L) ^ 2) * L := by ring
          _ ≤ δ * L := mul_le_mul_of_nonneg_right hdeltaInv hLpos.le
      have hxPow : Real.rpow x δ = Real.exp (δ * L) := by
        calc
          Real.rpow x δ = Real.exp (Real.log x * δ) := Real.rpow_def_of_pos hxpos δ
          _ = Real.exp (δ * L) := by rw [show Real.log x = L by rfl]; ring
      rw [hxPow]
      exact Real.exp_le_exp.mpr harg
    let Tphase : ℝ := Real.exp (L / (Real.log L) ^ 2)
    let Rfreq : ℝ := R
    let Ffreq : ℝ := Rfreq + 1
    let Nbad : ℝ := Real.exp (Ccount * Real.rpow L (91 / 100 : ℝ))
    let rho : ℝ := Real.rpow x (-cδ)
    let sigma : ℝ := Real.exp (-L / Real.rpow (Real.log L) C3)
    have hRhoNonneg : 0 ≤ rho := by dsimp [rho]; positivity
    have hSigmaNonneg : 0 ≤ sigma := by dsimp [sigma]; positivity
    have hTail : Nbad * (rho + sigma) ≤ 1 := by
      have hTail' := hTailInfo.2.2
      have hRhoEq : rho = Real.exp (-cδ * L) := by
        dsimp [rho]
        rw [Real.rpow_def_of_pos hxpos]
        simp [L]
        ring
      change Real.exp (Ccount * Real.rpow L (91 / 100 : ℝ)) * (rho + sigma) ≤ 1
      rw [hRhoEq]
      change Real.exp (Ccount * Real.rpow L (91 / 100 : ℝ)) *
        (Real.exp (-cδ * L) + Real.exp (-L / Real.rpow (Real.log L) C3)) ≤ 1
      exact hTail'
    have hFnonneg : 0 ≤ Ffreq := by dsimp [Ffreq, Rfreq, R]; positivity
    have hDnonneg : 0 ≤ Dfreq := le_of_lt hDfreq
    have hNnonneg : 0 ≤ Nbad := by dsimp [Nbad]; positivity
    have hchiPrime : ∀ p ∈ Pset,
        ‖(χ (p : ZMod q) : ℂ)‖ ≤ 1 := by
      intro p hp
      exact χ.norm_le_one (p : ZMod q)
    let bad : Set ℤ := sparseUnitIntervals x X B P A_s Pset
      (fun p => (χ (p : ZMod q) : ℂ)) xi
    by_cases hPone : 1 ≤ P
    · have hlogPLo : (1 / 20 : ℝ) * Real.rpow L (1 / 10 : ℝ) ≤ Real.log P := hPlo
      obtain ⟨r', hrLow, hrHigh, hrProd⟩ :=
        pd7_sparse_moment_order L (Real.log P) hLge hlogPLo
      let U : ℕ := ⌊2 * P⌋₊ ^ r'
      have hUone : 1 ≤ U := by
        dsimp [U]
        have hfloor : 1 ≤ ⌊2 * P⌋₊ := by
          apply Nat.le_floor
          exact_mod_cast (show (1 : ℝ) ≤ 2 * P by nlinarith [hPone])
        exact Nat.one_le_pow _ _ hfloor
      have hUbound : (U : ℝ) ≤ (2 * P) ^ r' := by
        dsimp [U]
        rw [Nat.cast_pow]
        gcongr
        exact Nat.floor_le (by linarith [hPone])
      have hPcardNat : (Pset.card : ℝ) ≤ 3 * P :=
        prime_band_card_le_three_mul P hPone Pset (by
          intro p hp
          exact (hPset p hp).2)
      have hPcard : 0 ≤ (Pset.card : ℝ) := by positivity
      have hPpos : 0 < P := lt_of_lt_of_le zero_lt_one hPone
      have hexpL : Real.exp L = x := by dsimp [L]; exact Real.exp_log hxpos
      have hRbound' : R ≤ 4 * Real.exp L * Real.rpow L B := by
        dsimp [R]
        rw [hexpL]
        have hXm : 2 * X ≤ 4 * x := by
          calc
            2 * X ≤ 2 * (2 * x) := mul_le_mul_of_nonneg_left hXhi (by norm_num)
            _ = 4 * x := by ring
        exact mul_le_mul_of_nonneg_right
          hXm (Real.rpow_nonneg hLpos.le _)
      have hPr : Real.exp L ≤ P ^ r' := by
        have hpowEq : P ^ r' = Real.exp ((r' : ℝ) * Real.log P) := by
          calc
            P ^ r' = (Real.exp (Real.log P)) ^ r' := by rw [Real.exp_log hPpos]
            _ = Real.exp ((r' : ℝ) * Real.log P) := by rw [← Real.exp_nat_mul]
        calc
          Real.exp L ≤ Real.exp ((r' : ℝ) * Real.log P) :=
            Real.exp_le_exp.mpr hrProd
          _ = P ^ r' := hpowEq.symm
      have hbadSamples : ∀ j ∈ bad, ∃ t : ℝ,
          (j : ℝ) ≤ t ∧ t ≤ (j : ℝ) + 1 ∧ |t| ≤ R ∧
            Real.rpow L (-A_s) ≤ ‖f t‖ := by
        intro j hj
        change ∃ t : ℝ, (j : ℝ) ≤ t ∧ t ≤ (j : ℝ) + 1 ∧
          |t| ≤ R ∧ Real.rpow L A_s * ‖f t‖ > 1 at hj
        rcases hj with ⟨t, hjlo, hjhi, ht, hlarge⟩
        have hAsPos : 0 < Real.rpow L A_s := Real.rpow_pos_of_pos hLpos A_s
        have hsmall : (Real.rpow L A_s)⁻¹ < ‖f t‖ := by
          have hlarge' : 1 < ‖f t‖ * Real.rpow L A_s := by
            simpa [mul_comm] using hlarge
          have hdiv : (1 : ℝ) / Real.rpow L A_s < ‖f t‖ :=
            (div_lt_iff₀ hAsPos).2 hlarge'
          simpa [one_div] using hdiv
        have hVeq : Real.rpow L (-A_s) = (Real.rpow L A_s)⁻¹ :=
          Real.rpow_neg hLpos.le A_s
        exact ⟨t, hjlo, hjhi, ht, le_of_lt (hVeq ▸ hsmall)⟩
      have hMomentBound : ∀ S : Finset ℝ, (∀ t ∈ S, |t| ≤ R) →
          (∀ t₁ ∈ S, ∀ t₂ ∈ S, t₁ ≠ t₂ → 1 ≤ |t₁ - t₂|) →
            (∑ t ∈ S, ‖f t‖ ^ (2 * r')) ≤
              Cmv * (2 * R + 1 + (U : ℝ) * Real.log (2 * (U : ℝ))) *
                Real.log (2 * (U : ℝ)) ^ 2 * (r'.factorial : ℝ) *
                  (Pset.card : ℝ) ^ r' * (1 / P) ^ (2 * r') := by
        intro S hS hsep
        have hSlohi : ∀ t ∈ S, -R ≤ t ∧ t ≤ R := by
          intro t ht
          rcases abs_le.mp (hS t ht) with ⟨hlo, hhi⟩
          exact ⟨hlo, hhi⟩
        have h := hMoment P hPone Pset hPset q χ xi r' S (-R) R
          (by linarith [hR0]) hSlohi hsep
        have hUcast : (↑(⌊2 * P⌋₊ ^ r') : ℝ) = (U : ℝ) := by
          simp [U, Nat.cast_pow]
        have hLogsq : Real.rpow (Real.log (2 * (U : ℝ))) (2 : ℝ) =
            (Real.log (2 * (U : ℝ))) ^ 2 := by
          convert Real.rpow_natCast (Real.log (2 * (U : ℝ))) 2 using 1 <;> norm_num
        calc
          (∑ t ∈ S, ‖f t‖ ^ (2 * r')) =
              ∑ t ∈ S, ‖bandPrimePolynomial P Pset
                (fun p => (χ (p : ZMod q) : ℂ)) xi t‖ ^ (2 * r') := by
                  simp only [f]
          _ ≤ Cmv * (R - -R + 1 +
                (↑(⌊2 * P⌋₊ ^ r') : ℝ) *
                  Real.log (2 * (↑(⌊2 * P⌋₊ ^ r') : ℝ))) *
                Real.rpow (Real.log (2 * (↑(⌊2 * P⌋₊ ^ r') : ℝ))) 2 *
                (r'.factorial : ℝ) * (Pset.card : ℝ) ^ r' * (1 / P) ^ (2 * r') := h
          _ = Cmv * (2 * R + 1 + (U : ℝ) * Real.log (2 * (U : ℝ))) *
                Real.log (2 * (U : ℝ)) ^ 2 * (r'.factorial : ℝ) *
                (Pset.card : ℝ) ^ r' * (1 / P) ^ (2 * r') := by
                  rw [hUcast]
                  rw [hLogsq]
                  ring
      have hcount := pd7_sparse_unit_interval_count_bound L P R B A_s C₁ Cmv
        (Pset.card : ℝ) r' U bad f hLinfo.1 hlogLsmall hPone hB hA_s
        hC₁ hCmv hPhi hR0 hRbound' hPr hUone hUbound hPcard hPcardNat
        hrLow hrHigh hbadSamples hMomentBound
      have hfinite : bad.Finite := finite_set_of_bounded_unit_intervals hR0 (by
        intro j hj
        obtain ⟨t, hjlo, hjhi, ht, _⟩ := hbadSamples j hj
        exact ⟨t, hjlo, hjhi, ht⟩)
      let J : Finset ℤ := hfinite.toFinset
      have hcardJ : (J.card : ℝ) ≤ Nbad := by
        have hcard : (J.card : ℝ) = (bad.ncard : ℝ) := by
          simp [J, Set.ncard_eq_toFinset_card bad hfinite]
        rw [hcard]
        simpa [Nbad] using hcount
      have hJ : ∀ j ∈ J, |(j : ℝ)| ≤ R + 1 := by
        intro j hj
        have hjbad : j ∈ bad := hfinite.mem_toFinset.mp (by simpa [J] using hj)
        obtain ⟨t, hjlo, hjhi, ht, _⟩ := hbadSamples j hjbad
        rcases abs_le.mp ht with ⟨htlo, hthi⟩
        rw [abs_le]
        constructor <;> linarith
      let Tphase : ℝ := Real.exp (L / (Real.log L) ^ 2)
      have hHnOne : 1 ≤ Hn := by
        have hxOne : 1 ≤ x := by linarith
        exact (Real.one_le_rpow hxOne hδ.le).trans hHnlo
      have hmod' : ∀ v : ℝ, 1 ≤ |v| → |v| ≤ Tphase →
          ‖∑ n ∈ dyadicIntegers Hn,
            Complex.exp (Complex.I * v * Real.log (n : ℝ))‖ ≤
              Cnear * Hn * (|v|⁻¹ + rho) := by
        intro v hv1 hvT
        have h := hmod x hxmod' Hn hHnlo v hv1 (by simpa [Tphase, L] using hvT)
        have hCmod : Cmod ≤ Cnear := le_max_right _ _
        calc
          _ ≤ Cmod * Hn * (|v|⁻¹ + rho) := by simpa [rho] using h
          _ ≤ Cnear * Hn * (|v|⁻¹ + rho) := by
            apply mul_le_mul_of_nonneg_right
            · apply mul_le_mul_of_nonneg_right hCmod
              exact le_trans (by norm_num : (0 : ℝ) ≤ 1) hHnOne
            · exact add_nonneg (inv_nonneg.mpr (abs_nonneg v)) hRhoNonneg
      have hTlower : Real.exp (L / (2 * (Real.log L) ^ 2)) ≤ Tphase := by
        apply Real.exp_le_exp.mpr
        have hden : 0 < (Real.log L) ^ 2 := pow_pos hlogLpos 2
        have hdenLe : (Real.log L) ^ 2 ≤ 2 * (Real.log L) ^ 2 := by
          nlinarith [hden]
        exact (div_le_div_iff₀
          (mul_pos (by norm_num : (0 : ℝ) < 2) hden) hden).2
          (mul_le_mul_of_nonneg_left hdenLe hLpos.le)
      have hfar' : ∀ v : ℝ, Real.exp (L / (2 * (Real.log L) ^ 2)) ≤ |v| →
          |v| ≤ 4 * x ^ 3 →
          ‖∑ n ∈ dyadicIntegers Hn,
            Complex.exp (Complex.I * v * Real.log (n : ℝ))‖ ≤ Cfar * Hn * sigma := by
        intro v hvlo hvhi
        have hTleHn : Tphase ≤ Hn := by
          calc
            Tphase ≤ Real.rpow x δ := by simpa [Tphase] using hTle
            _ ≤ Hn := hHnlo
        have h := hfar x hxfar' Hn hTleHn
          hHnhi v hvlo hvhi
        simpa [sigma, L] using h
      have hrowHigh : ∀ v : ℝ, 1 ≤ |v| → Tphase < |v| →
          |v| ≤ 2 * (Ffreq + 1) →
          ‖∑ n ∈ dyadicIntegers Hn,
            Complex.exp (Complex.I * v * Real.log (n : ℝ))‖ ≤ Cfar * Hn * sigma := by
        intro v hv1 hvlarge hvbound
        have hvlo : Real.exp (L / (2 * (Real.log L) ^ 2)) ≤ |v| :=
          le_trans hTlower (le_of_lt hvlarge)
        have hvhi : |v| ≤ 4 * x ^ 3 := by
          have hfreqEq : 2 * (Ffreq + 1) = 2 * (R + 2) := by
            dsimp [Ffreq, Rfreq]
            ring
          have : |v| ≤ 2 * (R + 2) := by rw [hfreqEq] at hvbound; exact hvbound
          exact this.trans hhighFreq
        exact hfar' v hvlo hvhi
      have hlogTerm : Real.log (2 * (Ffreq + 2)) ≤ Dfreq * L := by
        have hfreqEq : 2 * (Ffreq + 2) = 2 * (R + 3) := by
          dsimp [Ffreq, Rfreq]
          ring
        rw [hfreqEq]
        exact hlogFreq
      have hBetaEnergy := pd7_beta_energy_log_bound J Hn L C Ffreq Nbad
        Cnear Cfar Tphase rho sigma Dfreq hHnOne hLge hFnonneg
        hNnonneg hDnonneg hCnear3 (le_trans (by norm_num) hCnear3) hCfar.le
        hRhoNonneg hSigmaNonneg hJ hcardJ hlogTerm hTail beta chiN hbeta hchiN
        (by
          intro v hv1 hvv
          exact hmod' v hv1 hvv)
        (by
          intro v hv1 hvLarge hvBound
          exact hrowHigh v hv1 hvLarge hvBound)
      have hCenergy_le : Cenergy ≤ C₀ := by
        dsimp [C₀]
        exact le_trans (le_max_right Ccount Cenergy) (le_add_of_nonneg_right (by norm_num))
      have hcount_le : (bad.ncard : ℝ) ≤
          Real.exp (C₀ * Real.rpow L (91 / 100 : ℝ)) := by
        calc
          _ ≤ Nbad := hcount
          _ = Real.exp (Ccount * Real.rpow L (91 / 100 : ℝ)) := rfl
          _ ≤ _ := Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_right
              (le_trans (le_max_left Ccount Cenergy) (le_add_of_nonneg_right (by norm_num)))
              (Real.rpow_nonneg hLpos.le _))
      have hsumEnergy : (∑ j ∈ J, betaUnitIntervalEnergy Hn beta chiN j) ≤
          Cenergy * Real.rpow L (2 * C + 1) := by
        simpa [Cenergy, Dfreq] using hBetaEnergy
      have hsumTsum : (∑' j : ℤ, if j ∈ bad then
          betaUnitIntervalEnergy Hn beta chiN j else 0) =
          ∑ j ∈ J, betaUnitIntervalEnergy Hn beta chiN j := by
        calc
          (∑' j : ℤ, if j ∈ bad then betaUnitIntervalEnergy Hn beta chiN j else 0) =
              ∑ j ∈ J, (if j ∈ bad then betaUnitIntervalEnergy Hn beta chiN j else 0) := by
                apply tsum_eq_sum (s := J)
                intro j hj
                have hnot : j ∉ bad := by
                  intro hjbad
                  exact hj (by simpa [J] using hfinite.mem_toFinset.mpr hjbad)
                simp [hnot]
          _ = ∑ j ∈ J, betaUnitIntervalEnergy Hn beta chiN j := by
                apply Finset.sum_congr rfl
                intro j hj
                have hjbad : j ∈ bad := by
                  apply hfinite.mem_toFinset.mp
                  simpa [J] using hj
                simp [hjbad]
      constructor
      · exact hcount_le
      · calc
          _ = ∑ j ∈ J, betaUnitIntervalEnergy Hn beta chiN j := hsumTsum
          _ ≤ Cenergy * Real.rpow L (2 * C + 1) := hsumEnergy
          _ ≤ C₀ * Real.rpow L (2 * C + 1) :=
            mul_le_mul_of_nonneg_right hCenergy_le (Real.rpow_nonneg hLpos.le _)
    · have hPsmall : P < 1 := lt_of_not_ge hPone
      have hPsetEmpty : Pset = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro p hp
        have hp' := hPset p hp
        have hpNat : 2 ≤ p := hp'.1.two_le
        have hpReal : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpNat
        have htwoP : 2 * P < 2 := by
          calc
            2 * P < 2 * 1 := mul_lt_mul_of_pos_left hPsmall (by norm_num)
            _ = 2 := by ring
        exact (not_lt_of_ge hpReal) (lt_of_le_of_lt hp'.2.2 htwoP)
      have hbadEmpty : bad = ∅ := by
        ext j
        constructor
        · intro hj
          change ∃ t : ℝ, (j : ℝ) ≤ t ∧ t ≤ (j : ℝ) + 1 ∧
            |t| ≤ 2 * X * Real.rpow L B ∧
              Real.rpow L A_s * ‖bandPrimePolynomial P Pset
                (fun p => (χ (p : ZMod q) : ℂ)) xi t‖ > 1 at hj
          obtain ⟨t, _, _, _, hlarge⟩ := hj
          have hzero : bandPrimePolynomial P Pset
              (fun p => (χ (p : ZMod q) : ℂ)) xi t = 0 := by
            simp [bandPrimePolynomial, hPsetEmpty]
          rw [hzero] at hlarge
          norm_num at hlarge
        · simp
      have hbadEmpty' :
          sparseUnitIntervals x X B P A_s Pset
            (fun p => (χ (p : ZMod q) : ℂ)) xi = ∅ := hbadEmpty
      constructor
      · simpa [hbadEmpty'] using (le_of_lt (Real.exp_pos _))
      · simpa [hbadEmpty'] using
          (show 0 ≤ C₀ * Real.rpow L (2 * C + 1) by
            exact mul_nonneg (le_of_lt hC₀) (Real.rpow_nonneg hLpos.le _))

/-- NEW. Products `b` of one prime from every group, as a finite set of tuples. -/
def markedTupleSet (x : ℝ) (K : ℕ) (a : Fin K → ℝ) : Finset (Fin K → ℕ) :=
  Fintype.piFinset fun i => primeBand x (a i)

/-- Every marked prime tuple has positive product. -/
lemma marked_tuple_pos (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (tb : Fin K → ℕ) (htb : tb ∈ markedTupleSet x K a) :
    0 < tupleProduct tb := by
  have hprime : ∀ i : Fin K, (tb i).Prime := by
    intro i
    have hi : tb i ∈ primeBand x (a i) :=
      Fintype.mem_piFinset.mp (by simpa [markedTupleSet] using htb) i
    exact (Finset.mem_filter.mp hi).2.1
  unfold tupleProduct
  apply Finset.prod_pos
  intro i hi
  exact (hprime i).pos

/-- Split a marked tuple into its first coordinate and the remaining prime choices. -/
lemma markedTupleSet_cons (x : ℝ) (n : ℕ) (a : Fin (n + 1) → ℝ) :
    markedTupleSet x (n + 1) a =
      (primeBand x (a 0) ×ˢ
        Fintype.piFinset (Fin.tail (fun i : Fin (n + 1) => primeBand x (a i)))).map
          (Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)).toEmbedding := by
  classical
  unfold markedTupleSet
  simpa using (Finset.filter_piFinset_eq_map_consEquiv
    (S := fun i : Fin (n + 1) => primeBand x (a i))
    (P := fun _ : (∀ i : Fin n, ℕ) => True))

/-- Sums over marked tuples can be evaluated as sums over the first prime and its tail. -/
lemma sum_markedTupleSet_cons (x : ℝ) (n : ℕ) (a : Fin (n + 1) → ℝ)
    (F : (Fin (n + 1) → ℕ) → ℂ) :
    (∑ tb ∈ markedTupleSet x (n + 1) a, F tb) =
      ∑ p ∈ primeBand x (a 0),
        ∑ rest ∈ Fintype.piFinset (Fin.tail (fun i : Fin (n + 1) => primeBand x (a i))),
          F (Fin.cons p rest) := by
  classical
  rw [markedTupleSet_cons, Finset.sum_map, Finset.sum_product]
  simp [Fin.consEquiv]

lemma tupleProduct_cons (n : ℕ) (p : ℕ) (rest : Fin n → ℕ) :
    tupleProduct (Fin.cons p rest) = p * tupleProduct rest := by
  unfold tupleProduct
  rw [Fin.prod_univ_succ]
  simp [Fin.cons]

/-- The normalized reciprocal mass of all marked prime tuples is one. -/
lemma marked_reciprocal_mass (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (hMass : ∀ i : Fin K, bandMass x (a i) ≠ 0) :
    (∑ tb ∈ markedTupleSet x K a,
      (∏ i : Fin K, (bandMass x (a i))⁻¹) / (tupleProduct tb : ℝ)) = 1 := by
  classical
  calc
    _ = ∑ tb ∈ Fintype.piFinset (fun i : Fin K => primeBand x (a i)),
        ∏ i : Fin K, (bandMass x (a i))⁻¹ / (tb i : ℝ) := by
          apply Finset.sum_congr rfl
          intro tb htb
          simp only [markedTupleSet] at htb
          rw [tupleProduct, Nat.cast_prod]
          simp only [div_eq_mul_inv]
          rw [Finset.prod_inv_distrib]
          rw [Finset.prod_mul_distrib]
          simp only [Finset.prod_inv_distrib]
    _ = ∏ i : Fin K,
        ∑ p ∈ primeBand x (a i), (bandMass x (a i))⁻¹ / (p : ℝ) := by
          symm
          exact Finset.prod_univ_sum _ _
    _ = ∏ i : Fin K,
        ((bandMass x (a i))⁻¹ * bandMass x (a i)) := by
          apply Finset.prod_congr rfl
          intro i hi
          simp [bandMass, div_eq_mul_inv, ← Finset.mul_sum]
    _ = 1 := by
          simp [hMass]

/-- A smooth cutoff supported in `[1,4]` is uniformly bounded. -/
lemma exists_major_eta_bound (eta : ℝ → ℝ)
    (heta : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) eta)
    (heta_supp : Function.support eta ⊆ Set.Icc 1 4) :
    ∃ Mη : ℝ, 0 < Mη ∧ ∀ y : ℝ, ‖(eta y : ℂ)‖ ≤ Mη := by
  let f : ℝ → ℝ := fun y => ‖(eta y : ℂ)‖
  have hf : Continuous f := by
    dsimp [f]
    exact continuous_norm.comp (Complex.continuous_ofReal.comp heta.continuous)
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hf.continuousOn
  refine ⟨max 1 M, ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  · intro y
    by_cases hy : eta y = 0
    · simp [hy, f]
    · have hySupp : y ∈ Function.support eta := by
        change eta y ≠ 0
        exact hy
      have hyIcc : y ∈ Set.Icc (1 : ℝ) 4 := heta_supp hySupp
      have hval : f y ≤ M := hM (Set.mem_image_of_mem f hyIcc)
      exact le_trans hval (le_max_right _ _)

/-- A compact interval bound for the cutoff and its first two derivatives. -/
lemma exists_major_eta_C2_bound (eta : ℝ → ℝ)
    (heta : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) eta) :
    ∃ Mη : ℝ, 0 < Mη ∧ ∀ y ∈ Set.Icc (1 : ℝ) 4,
      |eta y| + |deriv eta y| + |deriv (deriv eta) y| ≤ Mη := by
  have hη₁ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv eta) := by
    simpa using heta.deriv'
  have hη₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv (deriv eta)) := by
    simpa using hη₁.deriv'
  let f : ℝ → ℝ := fun y => |eta y| + |deriv eta y| + |deriv (deriv eta) y|
  have hf : Continuous f := by
    dsimp [f]
    fun_prop
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hf.continuousOn
  refine ⟨max 1 M, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro y hy
  have hyBound : f y ≤ M := hM (Set.mem_image_of_mem f hy)
  exact le_trans hyBound (le_max_right _ _)

/-- A pair fiber of the multiplication map injects into the divisors of its product. -/
lemma pair_product_fiber_card_le_tau (S T : Finset ℕ)
    (hS : ∀ m ∈ S, 1 ≤ m) (hT : ∀ n ∈ T, 1 ≤ n) (u : ℕ) :
    ((S.product T).filter (fun z => z.1 * z.2 = u)).card ≤ tau u := by
  classical
  let F := (S.product T).filter (fun z => z.1 * z.2 = u)
  have hcard : F.card ≤ ((Finset.range (u + 1)).filter (fun d => d ∣ u)).card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro z hz
      have hz' := Finset.mem_filter.mp hz
      have hpair := Finset.mem_product.mp hz'.1
      have hprod := hz'.2
      have hnpos := hT z.2 hpair.2
      have hdiv : z.1 ∣ u := ⟨z.2, hprod.symm⟩
      have hle : z.1 ≤ u := by
        calc
          z.1 ≤ z.1 * z.2 := Nat.le_mul_of_pos_right _ (by omega)
          _ = u := hprod
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hle), hdiv⟩
    · intro z hz w hw hfst
      have hz' := Finset.mem_filter.mp hz
      have hw' := Finset.mem_filter.mp hw
      have hzpair := Finset.mem_product.mp hz'.1
      have hmpos := hS z.1 hzpair.1
      have hzprod := hz'.2
      have hwprod := hw'.2
      have hmul : z.1 * z.2 = z.1 * w.2 := by
        calc
          z.1 * z.2 = u := hzprod
          _ = w.1 * w.2 := hwprod.symm
          _ = z.1 * w.2 := by rw [← hfst]
      have hn : z.2 = w.2 := Nat.mul_left_cancel (by omega : 0 < z.1) hmul
      exact Prod.ext hfst hn
  simpa [F, tau] using hcard

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

/-- The coupled marked polynomial, with the first marked prime exposed as an outer summation
variable. -/
lemma majorBPolynomial_cons (x Y lam : ℝ) (eta : ℝ → ℝ) {n : ℕ}
    (a : Fin (n + 1) → ℝ) {k : ℕ} (χ : DirichletCharacter ℂ k) (t : ℝ) :
    majorBPolynomial x (n + 1) a Y lam eta χ t =
      (1 / Y : ℂ) * ∑ p ∈ primeBand x (a 0),
        ∑ rest ∈ Fintype.piFinset
          (Fin.tail (fun i : Fin (n + 1) => primeBand x (a i))),
          (eta ((tupleProduct (Fin.cons p rest) : ℝ) / Y) : ℂ) *
            additiveCharacter (-lam * (tupleProduct (Fin.cons p rest) : ℝ) / Y) *
            ((∏ i : Fin (n + 1), (bandMass x (a i))⁻¹ : ℝ) : ℂ) *
            χ ((tupleProduct (Fin.cons p rest) : ℕ) : ZMod k) *
            Complex.exp (Complex.I * t *
              Real.log (tupleProduct (Fin.cons p rest) : ℝ)) := by
  classical
  unfold majorBPolynomial
  rw [sum_markedTupleSet_cons]

/-- The cutoff-weighted marked tuple polynomial has bounded size independent of the tuple count.
The reciprocal prime masses cancel after summing over all tuples. -/
lemma majorBPolynomial_norm_le (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (Y lam Mη : ℝ) (eta : ℝ → ℝ) {k : ℕ} (χ : DirichletCharacter ℂ k) (t : ℝ)
    (hY : 0 < Y) (heta_supp : Function.support eta ⊆ Set.Icc 1 4)
    (hEtaBound : ∀ y : ℝ, ‖(eta y : ℂ)‖ ≤ Mη) (hMη : 0 ≤ Mη)
    (hMass : ∀ i : Fin K, 0 < bandMass x (a i)) :
    ‖majorBPolynomial x K a Y lam eta χ t‖ ≤ 4 * Mη := by
  classical
  let W : ℝ := ∏ i : Fin K, (bandMass x (a i))⁻¹
  have hMassNe : ∀ i : Fin K, bandMass x (a i) ≠ 0 :=
    fun i => ne_of_gt (hMass i)
  have hW : 0 ≤ W := by
    dsimp [W]
    apply Finset.prod_nonneg
    intro i hi
    exact inv_nonneg.mpr (le_of_lt (hMass i))
  have hWnorm : ‖(W : ℂ)‖ = W := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hW]
  have htuplePos (tb : Fin K → ℕ) (htb : tb ∈ markedTupleSet x K a) :
      0 < tupleProduct tb := by
    rw [tupleProduct]
    apply Finset.prod_pos
    intro i hi
    have hpi : tb i ∈ primeBand x (a i) :=
      (Fintype.mem_piFinset.mp (by simpa [markedTupleSet] using htb)) i
    have hprime : (tb i).Prime := by
      unfold primeBand at hpi
      exact (Finset.mem_filter.mp hpi).2.1
    exact hprime.pos
  have hterm (tb : Fin K → ℕ) (htb : tb ∈ markedTupleSet x K a) :
      ‖(eta ((tupleProduct tb : ℝ) / Y) : ℂ) *
          additiveCharacter (-lam * (tupleProduct tb : ℝ) / Y) *
          (W : ℂ) * χ ((tupleProduct tb : ℕ) : ZMod k) *
          Complex.exp (Complex.I * t * Real.log (tupleProduct tb : ℝ))‖ ≤
        4 * Mη * Y * (W / (tupleProduct tb : ℝ)) := by
    have hbposN := htuplePos tb htb
    have hbpos : 0 < (tupleProduct tb : ℝ) := by exact_mod_cast hbposN
    by_cases heta0 : eta ((tupleProduct tb : ℝ) / Y) = 0
    · simp [heta0]
      positivity
    · have hySupp : (tupleProduct tb : ℝ) / Y ∈ Function.support eta := by
        change eta ((tupleProduct tb : ℝ) / Y) ≠ 0
        exact heta0
      have hy := heta_supp hySupp
      have hbLow : Y ≤ (tupleProduct tb : ℝ) := by
        have hmul := mul_le_mul_of_nonneg_right hy.1 hY.le
        have hdiv : ((tupleProduct tb : ℝ) / Y) * Y = (tupleProduct tb : ℝ) := by
          field_simp [ne_of_gt hY]
        nlinarith
      have hbHigh : (tupleProduct tb : ℝ) ≤ 4 * Y := by
        have hmul := mul_le_mul_of_nonneg_right hy.2 hY.le
        have hdiv : ((tupleProduct tb : ℝ) / Y) * Y = (tupleProduct tb : ℝ) := by
          field_simp [ne_of_gt hY]
        nlinarith
      have hratio : 1 ≤ 4 * Y / (tupleProduct tb : ℝ) := by
        apply (le_div_iff₀ hbpos).2
        nlinarith
      have hadd : ‖additiveCharacter (-lam * (tupleProduct tb : ℝ) / Y)‖ = 1 := by
        simp [additiveCharacter, Complex.norm_exp]
      have hexp : ‖Complex.exp
          (Complex.I * t * Real.log (tupleProduct tb : ℝ))‖ = 1 := by
        have harg : Complex.I * (t : ℂ) *
            (Real.log (tupleProduct tb : ℝ) : ℂ) =
              ((t * Real.log (tupleProduct tb : ℝ) : ℝ) : ℂ) * Complex.I := by
          push_cast
          ring
        rw [harg, Complex.norm_exp_ofReal_mul_I]
      have hchi : ‖χ ((tupleProduct tb : ℕ) : ZMod k)‖ ≤ 1 :=
        χ.norm_le_one _
      have hEta := hEtaBound ((tupleProduct tb : ℝ) / Y)
      calc
        _ = ‖(eta ((tupleProduct tb : ℝ) / Y) : ℂ)‖ *
              ‖additiveCharacter (-lam * (tupleProduct tb : ℝ) / Y)‖ *
              ‖(W : ℂ)‖ * ‖χ ((tupleProduct tb : ℕ) : ZMod k)‖ *
              ‖Complex.exp (Complex.I * t * Real.log (tupleProduct tb : ℝ))‖ := by
                simp only [norm_mul]
        _ ≤ Mη * 1 * W * 1 * 1 := by
              rw [hadd, hWnorm, hexp]
              gcongr <;> first | assumption | positivity
        _ = Mη * W := by ring
        _ = Mη * W * 1 := by ring
        _ ≤ Mη * W * (4 * Y / (tupleProduct tb : ℝ)) :=
              mul_le_mul_of_nonneg_left hratio (mul_nonneg hMη hW)
        _ = 4 * Mη * Y * (W / (tupleProduct tb : ℝ)) := by
              field_simp [ne_of_gt hbpos]
  have hsum :
      (∑ tb ∈ markedTupleSet x K a,
        ‖(eta ((tupleProduct tb : ℝ) / Y) : ℂ) *
          additiveCharacter (-lam * (tupleProduct tb : ℝ) / Y) *
          (W : ℂ) * χ ((tupleProduct tb : ℕ) : ZMod k) *
          Complex.exp (Complex.I * t * Real.log (tupleProduct tb : ℝ))‖) ≤
        (4 * Mη * Y) *
          (∑ tb ∈ markedTupleSet x K a, W / (tupleProduct tb : ℝ)) := by
    calc
      _ ≤ ∑ tb ∈ markedTupleSet x K a,
          4 * Mη * Y * (W / (tupleProduct tb : ℝ)) := by
            apply Finset.sum_le_sum
            intro tb htb
            exact hterm tb htb
      _ = (4 * Mη * Y) *
          (∑ tb ∈ markedTupleSet x K a, W / (tupleProduct tb : ℝ)) := by
            rw [Finset.mul_sum]
  have hscale : ‖(1 / Y : ℂ)‖ = 1 / Y := by
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hY]
  unfold majorBPolynomial
  rw [norm_mul]
  calc
    _ ≤ (1 / Y) *
        (∑ tb ∈ markedTupleSet x K a,
          ‖(eta ((tupleProduct tb : ℝ) / Y) : ℂ) *
            additiveCharacter (-lam * (tupleProduct tb : ℝ) / Y) *
            (W : ℂ) * χ ((tupleProduct tb : ℕ) : ZMod k) *
            Complex.exp (Complex.I * t * Real.log (tupleProduct tb : ℝ))‖) := by
          rw [hscale]
          exact mul_le_mul_of_nonneg_left (norm_sum_le _ _)
            (by positivity)
    _ ≤ (1 / Y) * ((4 * Mη * Y) *
        (∑ tb ∈ markedTupleSet x K a, W / (tupleProduct tb : ℝ))) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 4 * Mη := by
          rw [marked_reciprocal_mass x K a hMassNe]
          field_simp [ne_of_gt hY]

/-- NEW. `M_α(t)` with a Dirichlet character (maj:M-definition, PD 05:44-55). -/
def majorMPolynomial {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂) (x : ℝ)
    {k : ℕ} (χ : DirichletCharacter ℂ k) (t : ℝ) : ℂ :=
  alphaFrequency family x t (fun m => χ (m : ZMod k))

/-- NEW. `N_β(t)` with a Dirichlet character (maj:polynomials). -/
def majorNPolynomial (Hn : ℝ) (beta : ℕ → ℂ) {k : ℕ} (χ : DirichletCharacter ℂ k) (t : ℝ) : ℂ :=
  betaFrequency Hn beta (fun n => χ (n : ZMod k)) t

/-- Convolution coefficients of `M_α(t) N_β(t)`, grouped by the product index. -/
noncomputable def majorMNProductCoeff {δ C c₁ c₂ : ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (x : ℝ) (beta : ℕ → ℂ)
    {k : ℕ} (χm χn : DirichletCharacter ℂ k) (u : ℕ) : ℂ := by
  classical
  exact (1 / (family.Hm x * family.Hn x) : ℂ) *
    ∑ z ∈ ((familyTerms family x).product (dyadicIntegers (family.Hn x))).filter
      (fun z => z.1 * z.2 = u),
      family.alpha x z.1 * χm (z.1 : ZMod k) * beta z.2 * χn (z.2 : ZMod k)

/-- The normalized convolution coefficient is bounded by the divisor count times the
pointwise coefficient bounds. -/
lemma majorMNProductCoeff_norm_le {δ C c₁ c₂ : ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (x : ℝ) (beta : ℕ → ℂ)
    {k : ℕ} (χm χn : DirichletCharacter ℂ k) (u : ℕ) (A : ℝ)
    (hX : 0 < family.Hm x * family.Hn x) (hA : 0 ≤ A)
    (hMpos : ∀ m ∈ familyTerms family x, 1 ≤ m)
    (hNpos : ∀ n ∈ dyadicIntegers (family.Hn x), 1 ≤ n)
    (hAlpha : ∀ m ∈ familyTerms family x, ‖family.alpha x m‖ ≤ A)
    (hBeta : ∀ n ∈ dyadicIntegers (family.Hn x), ‖beta n‖ ≤ A) :
    ‖majorMNProductCoeff family x beta χm χn u‖ ≤
      (tau u : ℝ) * A ^ 2 / (family.Hm x * family.Hn x) := by
  classical
  let S := familyTerms family x
  let T := dyadicIntegers (family.Hn x)
  let F := (S.product T).filter (fun z => z.1 * z.2 = u)
  have hcard := pair_product_fiber_card_le_tau S T
    (by simpa [S] using hMpos) (by simpa [T] using hNpos) u
  have hterm (z : ℕ × ℕ) (hz : z ∈ F) :
      ‖family.alpha x z.1 * χm (z.1 : ZMod k) * beta z.2 *
        χn (z.2 : ZMod k)‖ ≤ A ^ 2 := by
    have hz' := Finset.mem_filter.mp hz
    have hpair := Finset.mem_product.mp hz'.1
    have hα := hAlpha z.1 (by simpa [S] using hpair.1)
    have hβ := hBeta z.2 (by simpa [T] using hpair.2)
    have hχm : ‖χm (z.1 : ZMod k)‖ ≤ 1 := χm.norm_le_one _
    have hχn : ‖χn (z.2 : ZMod k)‖ ≤ 1 := χn.norm_le_one _
    calc
      _ = ‖family.alpha x z.1‖ * ‖χm (z.1 : ZMod k)‖ *
          ‖beta z.2‖ * ‖χn (z.2 : ZMod k)‖ := by simp only [norm_mul]
      _ ≤ A * 1 * A * 1 := by gcongr
      _ = A ^ 2 := by ring
  have hsum :
      ‖∑ z ∈ F, family.alpha x z.1 * χm (z.1 : ZMod k) * beta z.2 *
          χn (z.2 : ZMod k)‖ ≤ (tau u : ℝ) * A ^ 2 := by
    calc
      _ ≤ ∑ z ∈ F,
          ‖family.alpha x z.1 * χm (z.1 : ZMod k) * beta z.2 *
            χn (z.2 : ZMod k)‖ := norm_sum_le _ _
      _ ≤ ∑ _z ∈ F, A ^ 2 := by
          apply Finset.sum_le_sum
          intro z hz
          exact hterm z hz
      _ = (F.card : ℝ) * A ^ 2 := by simp
      _ ≤ (tau u : ℝ) * A ^ 2 :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (sq_nonneg A)
  have hscale : ‖(1 / (family.Hm x * family.Hn x) : ℂ)‖ =
      1 / (family.Hm x * family.Hn x) := by
    have hden :
        ‖(family.Hm x : ℂ) * (family.Hn x : ℂ)‖ =
          family.Hm x * family.Hn x := by
      calc
        _ = ‖(family.Hm x : ℂ)‖ * ‖(family.Hn x : ℂ)‖ := norm_mul _ _
        _ = |family.Hm x| * |family.Hn x| := by
              simp [Complex.norm_real, Real.norm_eq_abs]
        _ = |family.Hm x * family.Hn x| := (abs_mul _ _).symm
        _ = family.Hm x * family.Hn x := abs_of_pos hX
    rw [norm_div, norm_one, hden]
  unfold majorMNProductCoeff
  rw [norm_mul, hscale]
  calc
    _ ≤ (1 / (family.Hm x * family.Hn x)) * ((tau u : ℝ) * A ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (tau u : ℝ) * A ^ 2 / (family.Hm x * family.Hn x) := by ring

/-- The coefficient square sum is controlled by the second divisor moment. -/
lemma majorMNProductCoeff_sq_mass_bound {δ C c₁ c₂ : ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (x : ℝ) (beta : ℕ → ℂ)
    {k : ℕ} (χm χn : DirichletCharacter ℂ k) (N : ℕ) (A Cτ : ℝ)
    (hX : 0 < family.Hm x * family.Hn x) (hA : 0 ≤ A)
    (hTau :
      (∑ n ∈ Finset.range (N + 1), (tau n : ℝ) ^ 2) ≤
        Cτ * (4 * (family.Hm x * family.Hn x)) *
          Real.rpow (Real.log (8 * (family.Hm x * family.Hn x))) Cτ)
    (hMpos : ∀ m ∈ familyTerms family x, 1 ≤ m)
    (hNpos : ∀ n ∈ dyadicIntegers (family.Hn x), 1 ≤ n)
    (hAlpha : ∀ m ∈ familyTerms family x, ‖family.alpha x m‖ ≤ A)
    (hBeta : ∀ n ∈ dyadicIntegers (family.Hn x), ‖beta n‖ ≤ A) :
    (∑ n ∈ (Finset.range (N + 1)).filter (fun n => 1 ≤ n),
      ‖(if n = 0 then 0 else majorMNProductCoeff family x beta χm χn n)‖ ^ 2) ≤
      (A ^ 4 / (family.Hm x * family.Hn x) ^ 2) *
        (Cτ * (4 * (family.Hm x * family.Hn x)) *
          Real.rpow (Real.log (8 * (family.Hm x * family.Hn x))) Cτ) := by
  have hterm (n : ℕ) (hn : n ∈ (Finset.range (N + 1)).filter (fun n => 1 ≤ n)) :
      ‖(if n = 0 then 0 else majorMNProductCoeff family x beta χm χn n)‖ ^ 2 ≤
        ((tau n : ℝ) ^ 2) * (A ^ 4 / (family.Hm x * family.Hn x) ^ 2) := by
    have hnpos : 1 ≤ n := (Finset.mem_filter.mp hn).2
    have hcoeff := majorMNProductCoeff_norm_le family x beta χm χn n A hX hA
      hMpos hNpos hAlpha hBeta
    have hcoeff' :
        ‖(if n = 0 then 0 else majorMNProductCoeff family x beta χm χn n)‖ ≤
          (tau n : ℝ) * A ^ 2 / (family.Hm x * family.Hn x) := by
      simpa [Nat.ne_of_gt (by omega : 0 < n)] using hcoeff
    calc
      _ ≤ ((tau n : ℝ) * A ^ 2 / (family.Hm x * family.Hn x)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hcoeff' 2
      _ = ((tau n : ℝ) ^ 2) * (A ^ 4 / (family.Hm x * family.Hn x) ^ 2) := by ring
  calc
    _ ≤ ∑ n ∈ (Finset.range (N + 1)).filter (fun n => 1 ≤ n),
        (tau n : ℝ) ^ 2 * (A ^ 4 / (family.Hm x * family.Hn x) ^ 2) := by
          apply Finset.sum_le_sum
          intro n hn
          exact hterm n hn
    _ = (A ^ 4 / (family.Hm x * family.Hn x) ^ 2) *
        ∑ n ∈ (Finset.range (N + 1)).filter (fun n => 1 ≤ n), (tau n : ℝ) ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n hn
          ring
    _ ≤ (A ^ 4 / (family.Hm x * family.Hn x) ^ 2) *
        (Cτ * (4 * (family.Hm x * family.Hn x)) *
          Real.rpow (Real.log (8 * (family.Hm x * family.Hn x))) Cτ) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg
            (show (Finset.range (N + 1)).filter (fun n => 1 ≤ n) ⊆ Finset.range (N + 1) by
              intro n hn
              exact (Finset.mem_filter.mp hn).1)
            (fun n hn hnot => by positivity)) hTau

lemma major_exp_log_mul (t : ℝ) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    Complex.exp (Complex.I * t * Real.log (m : ℝ)) *
      Complex.exp (Complex.I * t * Real.log (n : ℝ)) =
        Complex.exp (Complex.I * t * Real.log (m * n : ℝ)) := by
  rw [← Complex.exp_add]
  congr 1
  have hlog : Real.log (m * n : ℝ) = Real.log (m : ℝ) + Real.log (n : ℝ) := by
    exact Real.log_mul (by exact_mod_cast (Nat.ne_of_gt hm))
      (by exact_mod_cast (Nat.ne_of_gt hn))
  rw [hlog]
  push_cast
  ring

/-- The product of the two normalized coefficient polynomials is the Dirichlet polynomial
whose coefficients are `majorMNProductCoeff`. -/
lemma majorMNProduct_eq_dirichletPolynomial {δ C c₁ c₂ : ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (x t : ℝ) (beta : ℕ → ℂ)
    {k : ℕ} (χm χn : DirichletCharacter ℂ k) (N : ℕ)
    (hHm : 0 < family.Hm x) (hHn : 0 < family.Hn x)
    (hMpos : ∀ m ∈ familyTerms family x, 1 ≤ m)
    (hNpos : ∀ n ∈ dyadicIntegers (family.Hn x), 1 ≤ n)
    (hprod : ∀ m ∈ familyTerms family x, ∀ n ∈ dyadicIntegers (family.Hn x), m * n ≤ N) :
    majorMPolynomial family x χm t * majorNPolynomial (family.Hn x) beta χn t =
      dirichletPolynomial N
        (fun u => if u = 0 then 0 else majorMNProductCoeff family x beta χm χn u) t := by
  classical
  let S := familyTerms family x
  let T := dyadicIntegers (family.Hn x)
  let pairs := S.product T
  have hmap : ∀ z ∈ pairs, z.1 * z.2 ∈ Finset.Ioc 0 N := by
    intro z hz
    have hp := Finset.mem_product.mp (by simpa [pairs, S, T] using hz)
    have hmone := hMpos z.1 (by simpa [S] using hp.1)
    have hnone := hNpos z.2 (by simpa [T] using hp.2)
    refine Finset.mem_Ioc.mpr ⟨Nat.mul_pos (by omega) (by omega), ?_⟩
    exact hprod z.1 (by simpa [S] using hp.1) z.2 (by simpa [T] using hp.2)
  have hscale :
      (1 / (family.Hm x) : ℂ) * (1 / (family.Hn x) : ℂ) =
        (1 / (family.Hm x * family.Hn x) : ℂ) := by
    push_cast
    field_simp [ne_of_gt hHm, ne_of_gt hHn]
  have hsum :
      (∑ m ∈ S, family.alpha x m * χm (m : ZMod k) *
        Complex.exp (Complex.I * t * Real.log (m : ℝ))) *
      (∑ n ∈ T, beta n * χn (n : ZMod k) *
        Complex.exp (Complex.I * t * Real.log (n : ℝ))) =
      ∑ z ∈ pairs,
        family.alpha x z.1 * χm (z.1 : ZMod k) * beta z.2 * χn (z.2 : ZMod k) *
          Complex.exp (Complex.I * t * Real.log (z.1 * z.2 : ℝ)) := by
    rw [Finset.sum_mul_sum, ← Finset.sum_product']
    apply Finset.sum_congr rfl
    intro z hz
    have hp := Finset.mem_product.mp hz
    have hmone := hMpos z.1 (by simpa [S] using hp.1)
    have hnone := hNpos z.2 (by simpa [T] using hp.2)
    have hm : 0 < z.1 := by omega
    have hn : 0 < z.2 := by omega
    calc
      _ = family.alpha x z.1 * χm (z.1 : ZMod k) * beta z.2 * χn (z.2 : ZMod k) *
          (Complex.exp (Complex.I * t * Real.log (z.1 : ℝ)) *
            Complex.exp (Complex.I * t * Real.log (z.2 : ℝ))) := by ring
      _ = family.alpha x z.1 * χm (z.1 : ZMod k) * beta z.2 * χn (z.2 : ZMod k) *
          Complex.exp (Complex.I * t * Real.log (z.1 * z.2 : ℝ)) := by
            rw [major_exp_log_mul t z.1 z.2 hm hn]
      _ = _ := by ring
  have hfiber :
      (∑ u ∈ Finset.Ioc 0 N,
        (∑ z ∈ pairs.filter (fun z => z.1 * z.2 = u),
          family.alpha x z.1 * χm (z.1 : ZMod k) * beta z.2 * χn (z.2 : ZMod k) *
            Complex.exp (Complex.I * t * Real.log (u : ℝ)))) =
        ∑ z ∈ pairs,
          family.alpha x z.1 * χm (z.1 : ZMod k) * beta z.2 * χn (z.2 : ZMod k) *
            Complex.exp (Complex.I * t * Real.log (z.1 * z.2 : ℝ)) := by
    calc
      _ = ∑ u ∈ Finset.Ioc 0 N,
          ∑ z ∈ pairs.filter (fun z => z.1 * z.2 = u),
            family.alpha x z.1 * χm (z.1 : ZMod k) * beta z.2 * χn (z.2 : ZMod k) *
              Complex.exp (Complex.I * t * Real.log (z.1 * z.2 : ℝ)) := by
            apply Finset.sum_congr rfl
            intro u hu
            apply Finset.sum_congr rfl
            intro z hz
            have hcast : (u : ℝ) = (z.1 * z.2 : ℝ) := by
              exact_mod_cast (Finset.mem_filter.mp hz).2.symm
            rw [hcast]
      _ = _ := Finset.sum_fiberwise_of_maps_to hmap _
  rw [pd7_dirichletPolynomial_eq_Ioc]
  have hleft :
      majorMPolynomial family x χm t * majorNPolynomial (family.Hn x) beta χn t =
        (1 / (family.Hm x * family.Hn x) : ℂ) *
          ∑ z ∈ pairs,
            family.alpha x z.1 * χm (z.1 : ZMod k) * beta z.2 * χn (z.2 : ZMod k) *
              Complex.exp (Complex.I * t * Real.log (z.1 * z.2 : ℝ)) := by
    unfold majorMPolynomial majorNPolynomial alphaFrequency betaFrequency
    calc
      _ = ((1 / (family.Hm x) : ℂ) * (1 / (family.Hn x) : ℂ)) *
          ((∑ m ∈ S, family.alpha x m * χm (m : ZMod k) *
              Complex.exp (Complex.I * t * Real.log (m : ℝ))) *
            (∑ n ∈ T, beta n * χn (n : ZMod k) *
              Complex.exp (Complex.I * t * Real.log (n : ℝ)))) := by ring
      _ = (1 / (family.Hm x * family.Hn x) : ℂ) *
          ((∑ m ∈ S, family.alpha x m * χm (m : ZMod k) *
              Complex.exp (Complex.I * t * Real.log (m : ℝ))) *
            (∑ n ∈ T, beta n * χn (n : ZMod k) *
              Complex.exp (Complex.I * t * Real.log (n : ℝ)))) := by rw [hscale]
      _ = _ := by rw [hsum]
  have hcoeffFiber :
      (∑ u ∈ Finset.Ioc 0 N,
        (if u = 0 then 0 else majorMNProductCoeff family x beta χm χn u) *
          pd7PrimePhase t u) =
        (1 / (family.Hm x * family.Hn x) : ℂ) *
          ∑ z ∈ pairs,
            family.alpha x z.1 * χm (z.1 : ZMod k) * beta z.2 * χn (z.2 : ZMod k) *
              Complex.exp (Complex.I * t * Real.log (z.1 * z.2 : ℝ)) := by
    calc
      _ = ∑ u ∈ Finset.Ioc 0 N,
          ((1 / (family.Hm x * family.Hn x) : ℂ) *
            ∑ z ∈ pairs.filter (fun z => z.1 * z.2 = u),
              family.alpha x z.1 * χm (z.1 : ZMod k) * beta z.2 * χn (z.2 : ZMod k)) *
            Complex.exp (Complex.I * t * Real.log (u : ℝ)) := by
          apply Finset.sum_congr rfl
          intro u hu
          have huPos : 0 < u := (Finset.mem_Ioc.mp hu).1
          simp [S, T, pairs, Nat.ne_of_gt huPos, majorMNProductCoeff,
            pd7_prime_phase_eq]
      _ = (1 / (family.Hm x * family.Hn x) : ℂ) *
          (∑ u ∈ Finset.Ioc 0 N,
            ∑ z ∈ pairs.filter (fun z => z.1 * z.2 = u),
              family.alpha x z.1 * χm (z.1 : ZMod k) * beta z.2 * χn (z.2 : ZMod k) *
                Complex.exp (Complex.I * t * Real.log (u : ℝ))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro u hu
          calc
            _ = (1 / (family.Hm x * family.Hn x) : ℂ) *
                ((∑ z ∈ pairs.filter (fun z => z.1 * z.2 = u),
                  family.alpha x z.1 * χm (z.1 : ZMod k) * beta z.2 *
                    χn (z.2 : ZMod k)) *
                  Complex.exp (Complex.I * t * Real.log (u : ℝ))) := by ring
            _ = (1 / (family.Hm x * family.Hn x) : ℂ) *
                (∑ z ∈ pairs.filter (fun z => z.1 * z.2 = u),
                  family.alpha x z.1 * χm (z.1 : ZMod k) * beta z.2 *
                    χn (z.2 : ZMod k) *
                    Complex.exp (Complex.I * t * Real.log (u : ℝ))) := by
                  rw [Finset.sum_mul]
      _ = _ := by rw [hfiber]
  rw [hleft, ← hcoeffFiber]
  apply Finset.sum_congr rfl
  intro u hu
  simp only [if_neg (Nat.ne_of_gt (Finset.mem_Ioc.mp hu).1)]

/-- The product polynomial inherits the continuous mean-value estimate in `moment_bounds`. -/
lemma majorMN_product_mean_square_bound {δ C c₁ c₂ : ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (x : ℝ) (beta : ℕ → ℂ)
    {k : ℕ} (χm χn : DirichletCharacter ℂ k) (N : ℕ)
    (hHm : 0 < family.Hm x) (hHn : 0 < family.Hn x)
    (hMpos : ∀ m ∈ familyTerms family x, 1 ≤ m)
    (hNpos : ∀ n ∈ dyadicIntegers (family.Hn x), 1 ≤ n)
    (hprod : ∀ m ∈ familyTerms family x, ∀ n ∈ dyadicIntegers (family.Hn x), m * n ≤ N)
    (hN : 1 ≤ N) :
    ∃ Cmv : ℝ, 0 < Cmv ∧ Cmv = Classical.choose moment_bounds.2.1 ∧ ∀ u v : ℝ, u ≤ v →
      ∫ t in u..v,
        ‖majorMPolynomial family x χm t * majorNPolynomial (family.Hn x) beta χn t‖ ^ 2 ≤
        Cmv * (v - u + (N : ℝ) * Real.log (2 * (N : ℝ))) *
          (∑ n ∈ (Finset.range (N + 1)).filter (fun n => 1 ≤ n),
            ‖(if n = 0 then 0 else majorMNProductCoeff family x beta χm χn n)‖ ^ 2) := by
  let Cmv := Classical.choose moment_bounds.2.1
  obtain ⟨hCmv, hmean⟩ := Classical.choose_spec moment_bounds.2.1
  refine ⟨Cmv, hCmv, rfl, ?_⟩
  intro u v huv
  let coeff : ℕ → ℂ := fun n =>
    if n = 0 then 0 else majorMNProductCoeff family x beta χm χn n
  have hfun :
      (fun t : ℝ =>
        ‖majorMPolynomial family x χm t * majorNPolynomial (family.Hn x) beta χn t‖ ^ 2) =
      (fun t : ℝ => ‖dirichletPolynomial N coeff t‖ ^ 2) := by
    funext t
    rw [majorMNProduct_eq_dirichletPolynomial family x t beta χm χn N
      hHm hHn hMpos hNpos hprod]
  rw [hfun]
  simpa [coeff] using hmean N hN coeff u v huv

/-- Combine the polynomial mean-value inequality with the divisor-moment coefficient bound. -/
lemma majorMN_product_mean_square_tau_bound {δ C c₁ c₂ : ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (x : ℝ) (beta : ℕ → ℂ)
    {k : ℕ} (χm χn : DirichletCharacter ℂ k) (N : ℕ) (A Cτ : ℝ)
    (hHm : 0 < family.Hm x) (hHn : 0 < family.Hn x)
    (hMpos : ∀ m ∈ familyTerms family x, 1 ≤ m)
    (hNpos : ∀ n ∈ dyadicIntegers (family.Hn x), 1 ≤ n)
    (hprod : ∀ m ∈ familyTerms family x, ∀ n ∈ dyadicIntegers (family.Hn x), m * n ≤ N)
    (hN : 1 ≤ N) (hX : 0 < family.Hm x * family.Hn x) (hA : 0 ≤ A)
    (hTau :
      (∑ n ∈ Finset.range (N + 1), (tau n : ℝ) ^ 2) ≤
        Cτ * (4 * (family.Hm x * family.Hn x)) *
          Real.rpow (Real.log (8 * (family.Hm x * family.Hn x))) Cτ)
    (hAlpha : ∀ m ∈ familyTerms family x, ‖family.alpha x m‖ ≤ A)
    (hBeta : ∀ n ∈ dyadicIntegers (family.Hn x), ‖beta n‖ ≤ A) :
    ∃ Cmv : ℝ, 0 < Cmv ∧ Cmv = Classical.choose moment_bounds.2.1 ∧ ∀ u v : ℝ, u ≤ v →
      ∫ t in u..v,
        ‖majorMPolynomial family x χm t * majorNPolynomial (family.Hn x) beta χn t‖ ^ 2 ≤
          Cmv * (v - u + (N : ℝ) * Real.log (2 * (N : ℝ))) *
            ((A ^ 4 / (family.Hm x * family.Hn x) ^ 2) *
              (Cτ * (4 * (family.Hm x * family.Hn x)) *
                Real.rpow (Real.log (8 * (family.Hm x * family.Hn x))) Cτ)) := by
  obtain ⟨Cmv, hCmv, hCmvEq, hmean⟩ := majorMN_product_mean_square_bound family x beta χm χn N
    hHm hHn hMpos hNpos hprod hN
  refine ⟨Cmv, hCmv, hCmvEq, ?_⟩
  intro u v huv
  have hmass := majorMNProductCoeff_sq_mass_bound family x beta χm χn N A Cτ
    hX hA hTau hMpos hNpos hAlpha hBeta
  have hmeanAt := hmean u v huv
  calc
    _ ≤ Cmv * (v - u + (N : ℝ) * Real.log (2 * (N : ℝ))) *
        (∑ n ∈ (Finset.range (N + 1)).filter (fun n => 1 ≤ n),
          ‖(if n = 0 then 0 else majorMNProductCoeff family x beta χm χn n)‖ ^ 2) := by
          simpa using hmeanAt
    _ ≤ Cmv * (v - u + (N : ℝ) * Real.log (2 * (N : ℝ))) *
        ((A ^ 4 / (family.Hm x * family.Hn x) ^ 2) *
          (Cτ * (4 * (family.Hm x * family.Hn x)) *
            Real.rpow (Real.log (8 * (family.Hm x * family.Hn x))) Cτ)) := by
          apply mul_le_mul_of_nonneg_left hmass
          have hspan : 0 ≤ v - u := sub_nonneg.mpr huv
          have hNcast : 1 ≤ (N : ℝ) := by exact_mod_cast hN
          have hlog : 0 ≤ Real.log (2 * (N : ℝ)) :=
            Real.log_nonneg (by nlinarith)
          positivity

/-- Once `X ≍ x`, the product mean-square bound is a logarithmic power. -/
lemma majorMN_product_mean_square_log_bound {δ C c₁ c₂ : ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (x L : ℝ) (beta : ℕ → ℂ)
    {k : ℕ} (χm χn : DirichletCharacter ℂ k) (N : ℕ) (C Cτ : ℝ)
    (hHm : 0 < family.Hm x) (hHn : 0 < family.Hn x)
    (hMpos : ∀ m ∈ familyTerms family x, 1 ≤ m)
    (hNpos : ∀ n ∈ dyadicIntegers (family.Hn x), 1 ≤ n)
    (hprod : ∀ m ∈ familyTerms family x, ∀ n ∈ dyadicIntegers (family.Hn x), m * n ≤ N)
    (hN : 1 ≤ N) (hX : 1 ≤ family.Hm x * family.Hn x)
    (hNfloor : N = ⌊4 * (family.Hm x * family.Hn x)⌋₊)
    (hL : 1 ≤ L) (hC : 0 < C) (hCτ : 0 < Cτ)
    (hLog8 : Real.log (8 * (family.Hm x * family.Hn x)) ≤ 2 * L)
    (hTau :
      (∑ n ∈ Finset.range (N + 1), (tau n : ℝ) ^ 2) ≤
        Cτ * (4 * (family.Hm x * family.Hn x)) *
          Real.rpow (Real.log (8 * (family.Hm x * family.Hn x))) Cτ)
    (hAlpha : ∀ m ∈ familyTerms family x,
      ‖family.alpha x m‖ ≤ Real.rpow L C)
    (hBeta : ∀ n ∈ dyadicIntegers (family.Hn x), ‖beta n‖ ≤ Real.rpow L C) :
    ∃ Cmn C₄ : ℝ, 0 < Cmn ∧ 0 < C₄ ∧
      Cmn = 32 * (Classical.choose moment_bounds.2.1) * Cτ * Real.rpow 2 Cτ ∧
      C₄ = 4 * C + Cτ + 2 ∧ ∀ u v : ℝ, u ≤ v →
      ∫ t in u..v,
        ‖majorMPolynomial family x χm t * majorNPolynomial (family.Hn x) beta χn t‖ ^ 2 ≤
          Cmn * Real.rpow L C₄ * (1 + (v - u) / (family.Hm x * family.Hn x)) := by
  let X : ℝ := family.Hm x * family.Hn x
  let A : ℝ := Real.rpow L C
  let C₄ : ℝ := 4 * C + Cτ + 2
  obtain ⟨Cmv, hCmv, hCmvEq, hmean⟩ := majorMN_product_mean_square_tau_bound family x beta χm χn N A Cτ
    hHm hHn hMpos hNpos hprod hN (by linarith [hX])
    (Real.rpow_nonneg (le_trans (by norm_num) hL) C)
    (by simpa [X, hNfloor] using hTau) (by simpa [A] using hAlpha) (by simpa [A] using hBeta)
  let Cmn : ℝ := 32 * Cmv * Cτ * Real.rpow 2 Cτ
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hXle : (N : ℝ) ≤ 4 * X := by
    rw [hNfloor]
    exact Nat.floor_le (by positivity)
  have h2Nle : 2 * (N : ℝ) ≤ 8 * X := by
    calc
      2 * (N : ℝ) ≤ 2 * (4 * X) := mul_le_mul_of_nonneg_left hXle (by norm_num)
      _ = 8 * X := by ring
  have h2Npos : 0 < 2 * (N : ℝ) := by positivity
  have h8Xpos : 0 < 8 * X := by positivity
  have hlog2N : Real.log (2 * (N : ℝ)) ≤ 2 * L := by
    exact (Real.log_le_log h2Npos h2Nle).trans (by simpa [X] using hLog8)
  have hlog2Nnonneg : 0 ≤ Real.log (2 * (N : ℝ)) := by
    apply Real.log_nonneg
    have hNcast : 1 ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith
  have hlog8nonneg : 0 ≤ Real.log (8 * X) :=
    Real.log_nonneg (by nlinarith [hX])
  have hlogPow : Real.rpow (Real.log (8 * X)) Cτ ≤ Real.rpow (2 * L) Cτ :=
    Real.rpow_le_rpow hlog8nonneg (by simpa [X] using hLog8) hCτ.le
  have hsplit : Real.rpow (2 * L) Cτ = Real.rpow 2 Cτ * Real.rpow L Cτ := by
    change (2 * L) ^ Cτ = 2 ^ Cτ * L ^ Cτ
    exact Real.mul_rpow (by norm_num) (by linarith [hL])
  have hA4 : A ^ 4 = Real.rpow L (4 * C) := by
    dsimp [A]
    calc
      _ = Real.rpow (Real.rpow L C) (4 : ℝ) := (Real.rpow_natCast _ 4).symm
      _ = Real.rpow L (C * 4) := (Real.rpow_mul (by linarith [hL]) C 4).symm
      _ = _ := by congr 1 <;> ring
  have hLpower : A ^ 4 * Real.rpow L Cτ * L = Real.rpow L (4 * C + Cτ + 1) := by
    rw [hA4]
    have hLone : Real.rpow L 1 = L := Real.rpow_one L
    calc
      _ = Real.rpow L (4 * C) * Real.rpow L Cτ * Real.rpow L 1 := by
            rw [hLone]
      _ = Real.rpow L (4 * C + Cτ) * Real.rpow L 1 := by
            exact congrArg (fun z : ℝ => z * Real.rpow L 1)
              ((Real.rpow_add hLpos (4 * C) Cτ).symm)
      _ = Real.rpow L (4 * C + Cτ + 1) := (Real.rpow_add hLpos _ _).symm
  have hCmn : 0 < Cmn := by
    dsimp [Cmn]
    positivity
  have hC₄ : 0 < C₄ := by
    dsimp [C₄]
    linarith
  refine ⟨Cmn, C₄, hCmn, hC₄, ?_, rfl, ?_⟩
  · dsimp [Cmn]
    rw [hCmvEq]
  · intro u v huv
    have hq : 0 ≤ (v - u) / X := div_nonneg (sub_nonneg.mpr huv) hXpos.le
    have hlength : v - u + (N : ℝ) * Real.log (2 * (N : ℝ)) ≤
        X * 8 * L * (1 + (v - u) / X) := by
      have hNlog : (N : ℝ) * Real.log (2 * (N : ℝ)) ≤ 8 * X * L := by
        calc
          _ ≤ (N : ℝ) * (2 * L) := mul_le_mul_of_nonneg_left hlog2N (by positivity)
          _ ≤ (4 * X) * (2 * L) := mul_le_mul_of_nonneg_right hXle (by positivity)
          _ = 8 * X * L := by ring
      calc
        _ ≤ (v - u) + 8 * X * L := add_le_add_right hNlog (v - u)
        _ = X * ((v - u) / X + 8 * L) := by
              field_simp [ne_of_gt hXpos]
        _ ≤ X * (8 * L * (1 + (v - u) / X)) := by
              apply mul_le_mul_of_nonneg_left _ hXpos.le
              have h8L : 1 ≤ 8 * L := by nlinarith [hL]
              nlinarith [mul_nonneg (sub_nonneg.mpr h8L) hq]
        _ = X * 8 * L * (1 + (v - u) / X) := by ring
    have hmass := majorMNProductCoeff_sq_mass_bound family x beta χm χn N A Cτ
      hXpos (Real.rpow_nonneg (le_trans (by norm_num) hL) C) hTau
      hMpos hNpos hAlpha hBeta
    have hA_nonneg : 0 ≤ A := Real.rpow_nonneg (le_trans (by norm_num) hL) C
    have hscaleNonneg : 0 ≤ A ^ 4 / X ^ 2 :=
      div_nonneg (pow_nonneg hA_nonneg 4) (sq_nonneg X)
    have hsplitPowNonneg : 0 ≤ Real.rpow 2 Cτ * Real.rpow L Cτ :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) Cτ)
        (Real.rpow_nonneg (le_trans (by norm_num) hL) Cτ)
    have hmassFactorNonneg :
        0 ≤ (A ^ 4 / X ^ 2) * (Cτ * (4 * X) *
          (Real.rpow 2 Cτ * Real.rpow L Cτ)) := by
      exact mul_nonneg hscaleNonneg
        (mul_nonneg (mul_nonneg hCτ.le (by positivity)) hsplitPowNonneg)
    have hmass' :
        (A ^ 4 / X ^ 2) * (Cτ * (4 * X) * Real.rpow (Real.log (8 * X)) Cτ) ≤
          (A ^ 4 / X ^ 2) *
            (Cτ * (4 * X) * (Real.rpow 2 Cτ * Real.rpow L Cτ)) := by
      apply mul_le_mul_of_nonneg_left ?_ hscaleNonneg
      calc
        Cτ * (4 * X) * Real.rpow (Real.log (8 * X)) Cτ ≤
            Cτ * (4 * X) * Real.rpow (2 * L) Cτ :=
              mul_le_mul_of_nonneg_left hlogPow (by positivity)
        _ = Cτ * (4 * X) * (Real.rpow 2 Cτ * Real.rpow L Cτ) := by rw [hsplit]
    have hmnAt := hmean u v huv
    calc
      _ ≤ Cmv * (v - u + (N : ℝ) * Real.log (2 * (N : ℝ))) *
          ((A ^ 4 / X ^ 2) * (Cτ * (4 * X) * Real.rpow (Real.log (8 * X)) Cτ)) := hmnAt
      _ ≤ Cmv * (v - u + (N : ℝ) * Real.log (2 * (N : ℝ))) *
          ((A ^ 4 / X ^ 2) *
            (Cτ * (4 * X) * (Real.rpow 2 Cτ * Real.rpow L Cτ))) :=
            mul_le_mul_of_nonneg_left hmass' (by positivity)
      _ ≤ Cmn * Real.rpow L (4 * C + Cτ + 1) * (1 + (v - u) / X) := by
            calc
              _ ≤ Cmv * (X * 8 * L * (1 + (v - u) / X)) *
                  ((A ^ 4 / X ^ 2) * (Cτ * (4 * X) *
                    (Real.rpow 2 Cτ * Real.rpow L Cτ))) := by
                      apply mul_le_mul_of_nonneg_right _ hmassFactorNonneg
                      exact mul_le_mul_of_nonneg_left hlength hCmv.le
              _ = (32 * Cmv * Cτ * Real.rpow 2 Cτ) *
                  (A ^ 4 * Real.rpow L Cτ * L) * (1 + (v - u) / X) := by
                      field_simp [ne_of_gt hXpos]
                      ring
              _ = Cmn * Real.rpow L (4 * C + Cτ + 1) *
                  (1 + (v - u) / X) := by
                      dsimp [Cmn]
                      exact congrArg
                        (fun z : ℝ =>
                          (32 * Cmv * Cτ * Real.rpow 2 Cτ) * z *
                            (1 + (v - u) / X)) hLpower
      _ ≤ Cmn * Real.rpow L C₄ * (1 + (v - u) / X) := by
            apply mul_le_mul_of_nonneg_right
            · apply mul_le_mul_of_nonneg_left
              · apply Real.rpow_le_rpow_of_exponent_le hL
                dsimp [C₄]
                linarith
              · exact hCmn.le
            · positivity

/-- The logarithmic Fourier transform of a compactly supported smooth complex function. -/
noncomputable def pd7ComplexFourierTransform (f : ℝ → ℂ) (v : ℝ) : ℂ :=
  (1 / (2 * Real.pi : ℝ) : ℂ) *
    ∫ s : ℝ, f s * Complex.exp (-Complex.I * v * s)

lemma pd7ComplexFourierTransform_eq_scaled_fourier (f : ℝ → ℂ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hcompact : HasCompactSupport f)
    (v : ℝ) :
    pd7ComplexFourierTransform f v =
      (1 / (2 * Real.pi : ℝ) : ℂ) * 𝓕 (hcompact.toSchwartzMap hf : ℝ → ℂ)
        (v / (2 * Real.pi)) := by
  let F : SchwartzMap ℝ ℂ := hcompact.toSchwartzMap hf
  have hFcoe : (F : ℝ → ℂ) = f := rfl
  unfold pd7ComplexFourierTransform
  rw [Real.fourier_eq']
  congr 1
  apply integral_congr_ae
  filter_upwards [] with s
  rw [hFcoe, Real.inner_apply]
  simp only [smul_eq_mul]
  have harg :
      (↑(-2 * Real.pi * (s * (v / (2 * Real.pi))) : ℝ) : ℂ) * Complex.I =
        -Complex.I * (v : ℂ) * s := by
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [harg]
  ring

/-- Fourier inversion in logarithmic coordinates for a compactly supported smooth complex
function. -/
theorem pd7_complex_fourier_inversion (f : ℝ → ℂ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hcompact : HasCompactSupport f) :
    ∀ x : ℝ,
      f x = ∫ v : ℝ,
        pd7ComplexFourierTransform f v * Complex.exp (Complex.I * v * x) := by
  classical
  let F : SchwartzMap ℝ ℂ := hcompact.toSchwartzMap hf
  have hFcoe : (F : ℝ → ℂ) = f := rfl
  have hFT (v : ℝ) :
      pd7ComplexFourierTransform f v =
        (1 / (2 * Real.pi : ℝ) : ℂ) * 𝓕 (F : ℝ → ℂ) (v / (2 * Real.pi)) := by
    unfold pd7ComplexFourierTransform
    rw [Real.fourier_eq']
    congr 1
    apply integral_congr_ae
    filter_upwards [] with s
    rw [hFcoe, Real.inner_apply]
    simp only [smul_eq_mul]
    have harg :
        (↑(-2 * Real.pi * (s * (v / (2 * Real.pi))) : ℝ) : ℂ) * Complex.I =
          -Complex.I * (v : ℂ) * s := by
      push_cast
      field_simp [Real.pi_ne_zero]
    rw [harg]
    ring
  intro x
  let H : ℝ → ℂ := fun v => pd7ComplexFourierTransform f v * Complex.exp (Complex.I * v * x)
  have hπ : 0 < 2 * Real.pi := by positivity
  have hchange : (∫ v : ℝ, H v) = (2 * Real.pi : ℝ) • ∫ w : ℝ, H ((2 * Real.pi) * w) := by
    have h := Measure.integral_comp_mul_left H (2 * Real.pi)
    rw [abs_of_pos (inv_pos.mpr hπ)] at h
    calc
      (∫ v : ℝ, H v) = (2 * Real.pi : ℝ) •
          ((2 * Real.pi : ℝ)⁻¹ • ∫ v : ℝ, H v) := by
            rw [smul_smul, mul_inv_cancel₀ hπ.ne', one_smul]
      _ = (2 * Real.pi : ℝ) • ∫ w : ℝ, H ((2 * Real.pi) * w) := by rw [h.symm]
  have hscaled (w : ℝ) :
      (2 * Real.pi : ℝ) • H ((2 * Real.pi) * w) =
        Complex.exp ((↑(2 * Real.pi * (w * x) : ℝ) : ℂ) * Complex.I) *
          𝓕 (F : ℝ → ℂ) w := by
    dsimp [H]
    rw [hFT]
    have hfreq : (2 * Real.pi * w) / (2 * Real.pi) = w := by
      field_simp [Real.pi_ne_zero]
    rw [hfreq]
    have hexpArg :
        Complex.I * (↑(2 * Real.pi * w : ℝ) : ℂ) * (x : ℂ) =
          (↑(2 * Real.pi * (w * x) : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [congrArg Complex.exp hexpArg]
    have hcoef :
        ((2 * Real.pi : ℝ) : ℂ) * (1 / (2 * Real.pi : ℝ) : ℂ) = 1 := by
      push_cast
      field_simp [Real.pi_ne_zero]
    calc
      ((2 * Real.pi : ℝ) : ℂ) *
          (((1 / (2 * Real.pi : ℝ) : ℂ) * 𝓕 (F : ℝ → ℂ) w) *
            Complex.exp ((↑(2 * Real.pi * (w * x) : ℝ) : ℂ) * Complex.I)) =
        (((2 * Real.pi : ℝ) : ℂ) * (1 / (2 * Real.pi : ℝ) : ℂ)) *
          𝓕 (F : ℝ → ℂ) w *
            Complex.exp ((↑(2 * Real.pi * (w * x) : ℝ) : ℂ) * Complex.I) := by ring
      _ = _ := by rw [hcoef]; ring
  have hInvSch : 𝓕⁻ (𝓕 F) = F := by
    ext z
    rw [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe]
    exact congrFun (F.continuous.fourierInv_fourier_eq F.integrable (𝓕 F).integrable) z
  have hInv : 𝓕⁻ (𝓕 (F : ℝ → ℂ)) x = F x := by
    have h := congrArg (fun G : SchwartzMap ℝ ℂ => (G : ℝ → ℂ)) hInvSch
    simpa only [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe] using congrFun h x
  have hInvIntegral :
      𝓕⁻ (𝓕 (F : ℝ → ℂ)) x =
        ∫ w : ℝ, Complex.exp ((↑(2 * Real.pi * (w * x) : ℝ) : ℂ) * Complex.I) *
          𝓕 (F : ℝ → ℂ) w := by
    rw [Real.fourierInv_eq']
    apply integral_congr_ae
    filter_upwards [] with w
    rw [Real.inner_apply]
    simp only [smul_eq_mul]
  have hInvToIntegral :
      (∫ v : ℝ, H v) = 𝓕⁻ (𝓕 (F : ℝ → ℂ)) x := by
    calc
      (∫ v : ℝ, H v) = (2 * Real.pi : ℝ) • ∫ w : ℝ, H ((2 * Real.pi) * w) := hchange
      _ = ∫ w : ℝ, (2 * Real.pi : ℝ) • H ((2 * Real.pi) * w) := by rw [← integral_smul]
      _ = ∫ w : ℝ,
          Complex.exp ((↑(2 * Real.pi * (w * x) : ℝ) : ℂ) * Complex.I) *
            𝓕 (F : ℝ → ℂ) w := by
            apply integral_congr_ae
            filter_upwards [] with w
            exact hscaled w
      _ = 𝓕⁻ (𝓕 (F : ℝ → ℂ)) x := hInvIntegral.symm
  calc
    f x = F x := rfl
    _ = 𝓕⁻ (𝓕 (F : ℝ → ℂ)) x := hInv.symm
    _ = ∫ v : ℝ, H v := hInvToIntegral.symm
    _ = ∫ v : ℝ,
        pd7ComplexFourierTransform f v * Complex.exp (Complex.I * v * x) := by
          simp [H]

/-- The coupled smooth cutoff `η(y)e(-λy)` in logarithmic coordinates. -/
noncomputable def pd7MajorCutoff (eta : ℝ → ℝ) (lam y : ℝ) : ℂ :=
  (eta y : ℂ) * additiveCharacter (-lam * y)

noncomputable def pd7MajorCutoffTransform (eta : ℝ → ℝ) (lam ξ : ℝ) : ℂ :=
  pd7ComplexFourierTransform (fun s => pd7MajorCutoff eta lam (Real.exp s)) ξ

noncomputable def pd7MajorCutoffLog (eta : ℝ → ℝ) (lam s : ℝ) : ℂ :=
  pd7MajorCutoff eta lam (Real.exp s)

noncomputable def pd7MajorCutoffLogPhaseDeriv (lam s : ℝ) : ℂ :=
  Complex.I * ((2 * Real.pi : ℂ) * ((-lam * Real.exp s : ℝ) : ℂ))

noncomputable def pd7MajorCutoffLogD1 (eta : ℝ → ℝ) (lam s : ℝ) : ℂ :=
  (((deriv eta (Real.exp s) * Real.exp s : ℝ) : ℂ) *
      additiveCharacter (-lam * Real.exp s)) +
    (eta (Real.exp s) : ℂ) * additiveCharacter (-lam * Real.exp s) *
      pd7MajorCutoffLogPhaseDeriv lam s

/-- First logarithmic derivative of the cutoff transform's source function. -/
lemma pd7_major_cutoff_log_deriv (eta : ℝ → ℝ)
    (heta : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) eta) (lam s : ℝ) :
    deriv (pd7MajorCutoffLog eta lam) s = pd7MajorCutoffLogD1 eta lam s := by
  let y := Real.exp s
  have hExp : HasDerivAt Real.exp y s := Real.hasDerivAt_exp s
  have hEtaAt : HasDerivAt eta (deriv eta y) y :=
    (heta.contDiffAt.differentiableAt (by simp)).hasDerivAt
  have hEtaComp : HasDerivAt (fun z => eta (Real.exp z)) (deriv eta y * y) s :=
    hEtaAt.comp s hExp
  have hEtaComplex :
      HasDerivAt (fun z => (eta (Real.exp z) : ℂ))
        ((deriv eta y * y : ℝ) : ℂ) s := hEtaComp.ofReal_comp
  have hLamExp : HasDerivAt (fun z : ℝ => -lam * Real.exp z) (-lam * y) s :=
    hExp.const_mul (-lam)
  have hArg : HasDerivAt
      (fun z : ℝ => Complex.I * ((2 * Real.pi : ℂ) * ((-lam * Real.exp z : ℝ) : ℂ)))
      (pd7MajorCutoffLogPhaseDeriv lam s) s := by
    simpa [pd7MajorCutoffLogPhaseDeriv, y] using
      ((hLamExp.ofReal_comp).const_mul (2 * Real.pi : ℂ)).const_mul Complex.I
  have hPhase : HasDerivAt
      (fun z : ℝ => additiveCharacter (-lam * Real.exp z))
      (additiveCharacter (-lam * y) * pd7MajorCutoffLogPhaseDeriv lam s) s := by
    have hexp := (Complex.hasDerivAt_exp
      (Complex.I * ((2 * Real.pi : ℂ) * ((-lam * Real.exp s : ℝ) : ℂ)))).comp s hArg
    convert hexp using 1
    · funext z
      simp [additiveCharacter]
    · simp [additiveCharacter, pd7MajorCutoffLogPhaseDeriv, y]
  have hprod := hEtaComplex.mul hPhase
  change deriv ((fun z => (eta (Real.exp z) : ℂ)) *
      (fun z => additiveCharacter (-lam * Real.exp z))) s =
    pd7MajorCutoffLogD1 eta lam s
  simpa [pd7MajorCutoffLogD1, y, mul_assoc] using hprod.deriv

noncomputable def pd7MajorCutoffLogD2 (eta : ℝ → ℝ) (lam s : ℝ) : ℂ :=
  (((deriv (deriv eta) (Real.exp s) * Real.exp s * Real.exp s +
      deriv eta (Real.exp s) * Real.exp s : ℝ) : ℂ) *
      additiveCharacter (-lam * Real.exp s)) +
    (2 : ℂ) * (((deriv eta (Real.exp s) * Real.exp s : ℝ) : ℂ) *
      additiveCharacter (-lam * Real.exp s) * pd7MajorCutoffLogPhaseDeriv lam s) +
    (eta (Real.exp s) : ℂ) * additiveCharacter (-lam * Real.exp s) *
      (pd7MajorCutoffLogPhaseDeriv lam s * pd7MajorCutoffLogPhaseDeriv lam s +
        pd7MajorCutoffLogPhaseDeriv lam s)

/-- Second logarithmic derivative of the cutoff transform's source function. -/
lemma pd7_major_cutoff_log_second_deriv (eta : ℝ → ℝ)
    (heta : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) eta) (lam s : ℝ) :
    deriv (deriv (pd7MajorCutoffLog eta lam)) s = pd7MajorCutoffLogD2 eta lam s := by
  let y := Real.exp s
  have hη₁ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv eta) := by simpa using heta.deriv'
  have hExp : HasDerivAt Real.exp y s := Real.hasDerivAt_exp s
  have hEtaAt : HasDerivAt eta (deriv eta y) y :=
    (heta.contDiffAt.differentiableAt (by simp)).hasDerivAt
  have hEtaComp : HasDerivAt (fun z => eta (Real.exp z)) (deriv eta y * y) s :=
    hEtaAt.comp s hExp
  have hEtaComplex : HasDerivAt (fun z => (eta (Real.exp z) : ℂ))
      ((deriv eta y * y : ℝ) : ℂ) s := hEtaComp.ofReal_comp
  have hEta1At : HasDerivAt (deriv eta) (deriv (deriv eta) y) y :=
    (hη₁.contDiffAt.differentiableAt (by simp)).hasDerivAt
  have hEta1Comp : HasDerivAt (deriv eta ∘ Real.exp)
      (deriv (deriv eta) y * y) s := hEta1At.comp s hExp
  have hEta1Real : HasDerivAt
      (fun z => (deriv eta ∘ Real.exp) z * Real.exp z)
      (deriv (deriv eta) y * y * y + deriv eta y * y) s := hEta1Comp.mul hExp
  have hEta1Complex : HasDerivAt
      (fun z => (((deriv eta ∘ Real.exp) z * Real.exp z : ℝ) : ℂ))
      ((deriv (deriv eta) y * y * y + deriv eta y * y : ℝ) : ℂ) s :=
    hEta1Real.ofReal_comp
  have hLamExp : HasDerivAt (fun z : ℝ => -lam * Real.exp z) (-lam * y) s :=
    hExp.const_mul (-lam)
  have hArg : HasDerivAt
      (fun z : ℝ => Complex.I * ((2 * Real.pi : ℂ) * ((-lam * Real.exp z : ℝ) : ℂ)))
      (pd7MajorCutoffLogPhaseDeriv lam s) s := by
    simpa [pd7MajorCutoffLogPhaseDeriv, y] using
      ((hLamExp.ofReal_comp).const_mul (2 * Real.pi : ℂ)).const_mul Complex.I
  have hPhase : HasDerivAt
      (fun z : ℝ => additiveCharacter (-lam * Real.exp z))
      (additiveCharacter (-lam * y) * pd7MajorCutoffLogPhaseDeriv lam s) s := by
    have hexp := (Complex.hasDerivAt_exp
      (Complex.I * ((2 * Real.pi : ℂ) * ((-lam * Real.exp s : ℝ) : ℂ)))).comp s hArg
    convert hexp using 1
    · funext z
      simp [additiveCharacter]
    · simp [additiveCharacter, pd7MajorCutoffLogPhaseDeriv, y]
  have hPhaseD : HasDerivAt
      (pd7MajorCutoffLogPhaseDeriv lam)
      (pd7MajorCutoffLogPhaseDeriv lam s) s := by
    change HasDerivAt
      (fun z : ℝ => Complex.I * ((2 * Real.pi : ℂ) * ((-lam * Real.exp z : ℝ) : ℂ)))
      (pd7MajorCutoffLogPhaseDeriv lam s) s
    exact hArg
  have hterm1 := hEta1Complex.mul hPhase
  have hterm2 := hEtaComplex.mul (hPhase.mul hPhaseD)
  have hD1 : HasDerivAt (pd7MajorCutoffLogD1 eta lam)
      (pd7MajorCutoffLogD2 eta lam s) s := by
    convert hterm1.add hterm2 using 1
    · funext z
      simp [pd7MajorCutoffLogD1, pd7MajorCutoffLogD2, mul_assoc]
      <;> ring
    · simp [pd7MajorCutoffLogD1, pd7MajorCutoffLogD2, y, mul_assoc,
        mul_add, add_mul, add_assoc, add_left_comm, add_comm]
      <;> ring
  have hfun : (fun z => deriv (pd7MajorCutoffLog eta lam) z) =
      pd7MajorCutoffLogD1 eta lam := by
    funext z
    exact pd7_major_cutoff_log_deriv eta heta lam z
  have hEq := congrArg (fun f : ℝ → ℂ => deriv f s) hfun
  calc
    deriv (deriv (pd7MajorCutoffLog eta lam)) s =
        deriv (pd7MajorCutoffLogD1 eta lam) s := by simpa using hEq
    _ = pd7MajorCutoffLogD2 eta lam s := hD1.deriv

/-- Uniform pointwise bound for the second logarithmic derivative of the cutoff source. -/
lemma pd7_major_cutoff_log_second_deriv_bound (eta : ℝ → ℝ)
    (heta : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) eta)
    (heta_supp : Function.support eta ⊆ Set.Icc 1 4)
    (Mη : ℝ) (hMη : 0 ≤ Mη)
    (hC2 : ∀ y ∈ Set.Icc (1 : ℝ) 4,
      |eta y| + |deriv eta y| + |deriv (deriv eta) y| ≤ Mη) (lam s : ℝ) :
    ‖pd7MajorCutoffLogD2 eta lam s‖ ≤
      Mη * (20 + 72 * Real.pi + 64 * Real.pi ^ 2) * (1 + |lam|) ^ 2 := by
  let g : ℝ → ℂ := pd7MajorCutoffLog eta lam
  have hgsupp : Function.support g ⊆ Set.Icc (0 : ℝ) (Real.log 4) := by
    intro z hz
    have hgne : g z ≠ 0 := by change g z ≠ 0 at hz; exact hz
    have hηne : eta (Real.exp z) ≠ 0 := by
      intro hz0
      apply hgne
      simp [g, pd7MajorCutoffLog, pd7MajorCutoff, hz0]
    have hmem : Real.exp z ∈ Function.support eta := by
      change eta (Real.exp z) ≠ 0
      exact hηne
    have hband := heta_supp hmem
    constructor
    · have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 1) hband.1
      simpa [Real.log_exp] using hlog
    · have hlog := Real.log_le_log (Real.exp_pos z) hband.2
      simpa [Real.log_exp] using hlog
  have hclosed : IsClosed (Set.Icc (0 : ℝ) (Real.log 4)) := isClosed_Icc
  have htsupp : tsupport g ⊆ Set.Icc (0 : ℝ) (Real.log 4) :=
    closure_minimal hgsupp hclosed
  have hD2support :
      Function.support (deriv (deriv g)) ⊆ Set.Icc (0 : ℝ) (Real.log 4) :=
    support_deriv_subset.trans (tsupport_deriv_subset.trans htsupp)
  let cutoffConst : ℝ := 20 + 72 * Real.pi + 64 * Real.pi ^ 2
  have hcutoffConst : 0 ≤ cutoffConst := by positivity
  by_cases hs : s ∈ Set.Icc (0 : ℝ) (Real.log 4)
  · have hy1 : 1 ≤ Real.exp s := by
      calc
        1 = Real.exp 0 := by simp
        _ ≤ Real.exp s := Real.exp_le_exp.mpr hs.1
    have hy4 : Real.exp s ≤ 4 := by
      calc
        Real.exp s ≤ Real.exp (Real.log 4) := Real.exp_le_exp.mpr hs.2
        _ = 4 := Real.exp_log (by norm_num)
    have hC2s := hC2 (Real.exp s) ⟨hy1, hy4⟩
    have hη0 : |eta (Real.exp s)| ≤ Mη := by
      have h1 := abs_nonneg (deriv eta (Real.exp s))
      have h2 := abs_nonneg (deriv (deriv eta) (Real.exp s))
      nlinarith
    have hη1 : |deriv eta (Real.exp s)| ≤ Mη := by
      have h0 := abs_nonneg (eta (Real.exp s))
      have h2 := abs_nonneg (deriv (deriv eta) (Real.exp s))
      nlinarith
    have hη2 : |deriv (deriv eta) (Real.exp s)| ≤ Mη := by
      have h0 := abs_nonneg (eta (Real.exp s))
      have h1 := abs_nonneg (deriv eta (Real.exp s))
      nlinarith
    have hypos : 0 < Real.exp s := Real.exp_pos s
    have ha2 :
        ‖(((deriv (deriv eta) (Real.exp s) * Real.exp s * Real.exp s +
          deriv eta (Real.exp s) * Real.exp s : ℝ) : ℂ))‖ ≤ 20 * Mη := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      calc
        _ ≤ |deriv (deriv eta) (Real.exp s) * Real.exp s * Real.exp s| +
            |deriv eta (Real.exp s) * Real.exp s| := abs_add_le _ _
        _ = |deriv (deriv eta) (Real.exp s)| * Real.exp s * Real.exp s +
            |deriv eta (Real.exp s)| * Real.exp s := by
              simp [abs_mul, abs_of_pos hypos]
        _ ≤ Mη * Real.exp s * Real.exp s + Mη * Real.exp s := by
              gcongr
        _ ≤ Mη * 4 * 4 + Mη * 4 := by gcongr <;> ring
        _ = 20 * Mη := by ring
    have ha1 :
        ‖((deriv eta (Real.exp s) * Real.exp s : ℝ) : ℂ)‖ ≤ 4 * Mη := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hypos]
      calc
        _ ≤ Mη * Real.exp s := mul_le_mul_of_nonneg_right hη1 (Real.exp_pos s).le
        _ ≤ 4 * Mη := by
              calc
                _ ≤ Mη * 4 := mul_le_mul_of_nonneg_left hy4 hMη
                _ = 4 * Mη := by ring
    have ha0 : ‖(eta (Real.exp s) : ℂ)‖ ≤ Mη := by
      simpa [Complex.norm_real, Real.norm_eq_abs] using hη0
    have hq : ‖additiveCharacter (-lam * Real.exp s)‖ = 1 := by
      simp [additiveCharacter, Complex.norm_exp]
    have hcNorm :
        ‖pd7MajorCutoffLogPhaseDeriv lam s‖ ≤ 8 * Real.pi * |lam| := by
      have hTwoPi : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
        have hcast : (2 * Real.pi : ℂ) = (2 : ℂ) * (Real.pi : ℂ) := by
          push_cast
          ring
        rw [hcast, norm_mul]
        simp [Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (show 0 < Real.pi by positivity)]
      have hReal : ‖((-lam * Real.exp s : ℝ) : ℂ)‖ = |lam| * Real.exp s := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_neg,
          abs_of_pos (Real.exp_pos s)]
      have hnorm :
          ‖pd7MajorCutoffLogPhaseDeriv lam s‖ =
            (2 * Real.pi) * (|lam| * Real.exp s) := by
        unfold pd7MajorCutoffLogPhaseDeriv
        calc
          _ = ‖Complex.I‖ * (‖(2 * Real.pi : ℂ)‖ *
              ‖((-lam * Real.exp s : ℝ) : ℂ)‖) := by rw [norm_mul, norm_mul]
          _ = (2 * Real.pi) * (|lam| * Real.exp s) := by
                rw [Complex.norm_I, hTwoPi, hReal]
                ring
      rw [hnorm]
      have hbase : 0 ≤ 2 * Real.pi * |lam| := by positivity
      calc
        _ = (2 * Real.pi * |lam|) * Real.exp s := by ring
        _ ≤ (2 * Real.pi * |lam|) * 4 := mul_le_mul_of_nonneg_left hy4 hbase
        _ = 8 * Real.pi * |lam| := by ring
    let a2c : ℂ :=
      ((deriv (deriv eta) (Real.exp s) * Real.exp s * Real.exp s +
        deriv eta (Real.exp s) * Real.exp s : ℝ) : ℂ)
    let a1c : ℂ := ((deriv eta (Real.exp s) * Real.exp s : ℝ) : ℂ)
    let a0c : ℂ := (eta (Real.exp s) : ℂ)
    let q : ℂ := additiveCharacter (-lam * Real.exp s)
    let c : ℂ := pd7MajorCutoffLogPhaseDeriv lam s
    have ha1c : ‖a1c‖ ≤ 4 * Mη := by simpa [a1c] using ha1
    have ha0c : ‖a0c‖ ≤ Mη := by simpa [a0c] using ha0
    have hqnorm : ‖q‖ = 1 := by simpa [q] using hq
    have hcnorm : ‖c‖ ≤ 8 * Real.pi * |lam| := by simpa [c] using hcNorm
    have haTerm : ‖a2c * q‖ ≤ 20 * Mη := by
      calc
        _ = ‖a2c‖ * ‖q‖ := norm_mul _ _
        _ ≤ 20 * Mη := by rw [hqnorm]; simpa [a2c] using ha2
    have hbTerm : ‖(2 : ℂ) * a1c * q * c‖ ≤ 64 * Real.pi * Mη * |lam| := by
      have hnorm2 : ‖(2 : ℂ)‖ = 2 := by norm_num
      calc
        _ = ‖(2 : ℂ)‖ * ‖a1c‖ * ‖q‖ * ‖c‖ := by simp only [norm_mul]
        _ ≤ 2 * (4 * Mη) * 1 * (8 * Real.pi * |lam|) := by
              rw [hnorm2, hqnorm]
              gcongr
        _ = 64 * Real.pi * Mη * |lam| := by ring
    have hcSum : ‖c * c + c‖ ≤ 64 * Real.pi ^ 2 * |lam| ^ 2 + 8 * Real.pi * |lam| := by
      calc
        _ ≤ ‖c * c‖ + ‖c‖ := norm_add_le _ _
        _ = ‖c‖ ^ 2 + ‖c‖ := by rw [norm_mul]; ring
        _ ≤ (8 * Real.pi * |lam|) ^ 2 + 8 * Real.pi * |lam| := by
              gcongr <;> exact hcnorm
        _ = 64 * Real.pi ^ 2 * |lam| ^ 2 + 8 * Real.pi * |lam| := by ring
    have hcTerm : ‖a0c * q * (c * c + c)‖ ≤
        Mη * (64 * Real.pi ^ 2 * |lam| ^ 2 + 8 * Real.pi * |lam|) := by
      calc
        _ = ‖a0c‖ * ‖q‖ * ‖c * c + c‖ := by simp only [norm_mul]
        _ ≤ Mη * 1 * (64 * Real.pi ^ 2 * |lam| ^ 2 + 8 * Real.pi * |lam|) := by
              rw [hqnorm]
              gcongr
        _ = Mη * (64 * Real.pi ^ 2 * |lam| ^ 2 + 8 * Real.pi * |lam|) := by ring
    have hsumTerms :
        ‖(a2c * q) + (2 : ℂ) * a1c * q * c + a0c * q * (c * c + c)‖ ≤
          20 * Mη + 64 * Real.pi * Mη * |lam| +
            Mη * (64 * Real.pi ^ 2 * |lam| ^ 2 + 8 * Real.pi * |lam|) := by
      calc
        _ ≤ ‖a2c * q‖ + ‖(2 : ℂ) * a1c * q * c‖ + ‖a0c * q * (c * c + c)‖ := by
              calc
                _ ≤ ‖a2c * q + (2 : ℂ) * a1c * q * c‖ +
                    ‖a0c * q * (c * c + c)‖ := norm_add_le _ _
                _ ≤ _ := add_le_add (norm_add_le _ _) le_rfl
        _ ≤ _ := add_le_add (add_le_add haTerm hbTerm) hcTerm
    have hterms : ‖pd7MajorCutoffLogD2 eta lam s‖ ≤
        20 * Mη + 64 * Real.pi * Mη * |lam| +
          Mη * (64 * Real.pi ^ 2 * |lam| ^ 2 + 8 * Real.pi * |lam|) := by
      simpa [pd7MajorCutoffLogD2, a2c, a1c, a0c, q, c, mul_assoc] using hsumTerms
    have hpoly :
        20 * Mη + 64 * Real.pi * Mη * |lam| +
          Mη * (64 * Real.pi ^ 2 * |lam| ^ 2 + 8 * Real.pi * |lam|) ≤
        Mη * cutoffConst * (1 + |lam|) ^ 2 := by
      dsimp [cutoffConst]
      have hAbsLam : 0 ≤ |lam| := abs_nonneg lam
      have hπ : 0 < Real.pi := Real.pi_pos
      have hK0 : 20 ≤ 20 + 72 * Real.pi + 64 * Real.pi ^ 2 := by nlinarith [sq_nonneg Real.pi]
      have hKlinear : 72 * Real.pi ≤ 2 * (20 + 72 * Real.pi + 64 * Real.pi ^ 2) := by
        nlinarith [hπ, sq_nonneg Real.pi]
      have hK2 : 64 * Real.pi ^ 2 ≤ 20 + 72 * Real.pi + 64 * Real.pi ^ 2 := by
        nlinarith [hπ, sq_nonneg Real.pi]
      have h0 : 20 * Mη ≤ Mη * (20 + 72 * Real.pi + 64 * Real.pi ^ 2) := by
        calc
          _ = Mη * 20 := by ring
          _ ≤ Mη * (20 + 72 * Real.pi + 64 * Real.pi ^ 2) := mul_le_mul_of_nonneg_left hK0 hMη
      have hlinear : 64 * Real.pi * Mη * |lam| + 8 * Real.pi * Mη * |lam| ≤
          2 * Mη * (20 + 72 * Real.pi + 64 * Real.pi ^ 2) * |lam| := by
        have hu : 0 ≤ Mη * |lam| := mul_nonneg hMη hAbsLam
        calc
          _ = (Mη * |lam|) * (72 * Real.pi) := by ring
          _ ≤ (Mη * |lam|) * (2 * (20 + 72 * Real.pi + 64 * Real.pi ^ 2)) :=
                mul_le_mul_of_nonneg_left hKlinear hu
          _ = _ := by ring
      have h2 : Mη * (64 * Real.pi ^ 2 * |lam| ^ 2) ≤
          Mη * (20 + 72 * Real.pi + 64 * Real.pi ^ 2) * |lam| ^ 2 := by
        calc
          _ ≤ Mη * ((20 + 72 * Real.pi + 64 * Real.pi ^ 2) * |lam| ^ 2) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hK2 (sq_nonneg |lam|)) hMη
          _ = _ := by ring
      have hleft :
          20 * Mη + 64 * Real.pi * Mη * |lam| +
            Mη * (64 * Real.pi ^ 2 * |lam| ^ 2 + 8 * Real.pi * |lam|) ≤
          Mη * (20 + 72 * Real.pi + 64 * Real.pi ^ 2) +
            2 * Mη * (20 + 72 * Real.pi + 64 * Real.pi ^ 2) * |lam| +
            Mη * (20 + 72 * Real.pi + 64 * Real.pi ^ 2) * |lam| ^ 2 := by
        calc
          _ = 20 * Mη + (64 * Real.pi * Mη * |lam| + 8 * Real.pi * Mη * |lam|) +
              Mη * (64 * Real.pi ^ 2 * |lam| ^ 2) := by ring
          _ ≤ Mη * (20 + 72 * Real.pi + 64 * Real.pi ^ 2) +
              2 * Mη * (20 + 72 * Real.pi + 64 * Real.pi ^ 2) * |lam| +
              Mη * (20 + 72 * Real.pi + 64 * Real.pi ^ 2) * |lam| ^ 2 :=
                add_le_add (add_le_add h0 hlinear) h2
      calc
        _ ≤ Mη * (20 + 72 * Real.pi + 64 * Real.pi ^ 2) +
            2 * Mη * (20 + 72 * Real.pi + 64 * Real.pi ^ 2) * |lam| +
            Mη * (20 + 72 * Real.pi + 64 * Real.pi ^ 2) * |lam| ^ 2 := hleft
        _ = _ := by ring
    exact hterms.trans hpoly
  · have hnot : s ∉ Function.support (deriv (deriv g)) := by
      intro hsD
      have hts1 : s ∈ tsupport (deriv g) := support_deriv_subset hsD
      have hts0 : s ∈ tsupport g := tsupport_deriv_subset hts1
      exact hs (htsupp hts0)
    have hz : deriv (deriv g) s = 0 := by
      by_contra hne
      apply hnot
      change deriv (deriv g) s ≠ 0
      exact hne
    have hD2zero : pd7MajorCutoffLogD2 eta lam s = 0 := by
      rw [← pd7_major_cutoff_log_second_deriv eta heta lam s]
      exact hz
    rw [hD2zero]
    simp
    exact mul_nonneg (mul_nonneg hMη hcutoffConst) (sq_nonneg (1 + |lam|))

/-- Differentiating a compactly supported smooth source twice multiplies its logarithmic
Fourier transform by `-(ξ^2)`. -/
lemma pd7ComplexFourierTransform_second_deriv (f : ℝ → ℂ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hcompact : HasCompactSupport f) (ξ : ℝ) :
    pd7ComplexFourierTransform (deriv (deriv f)) ξ =
      (Complex.I * ξ) ^ 2 * pd7ComplexFourierTransform f ξ := by
  let f₁ := deriv f
  let f₂ := deriv f₁
  have hf₁ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f₁ := by
    dsimp [f₁]
    simpa using hf.deriv'
  have hf₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f₂ := by
    dsimp [f₂, f₁]
    simpa using hf₁.deriv'
  have hc₁ : HasCompactSupport f₁ := by
    dsimp [f₁]
    exact hcompact.deriv
  have hc₂ : HasCompactSupport f₂ := by
    dsimp [f₂]
    exact hc₁.deriv
  have hi₀ : Integrable f := hf.continuous.integrable_of_hasCompactSupport hcompact
  have hi₁ : Integrable f₁ := hf₁.continuous.integrable_of_hasCompactSupport hc₁
  have hi₂ : Integrable f₂ := hf₂.continuous.integrable_of_hasCompactSupport hc₂
  have hFourier₁ := Real.fourier_deriv hi₀ (hf.differentiable (by simp)) hi₁
  have hFourier₂ := Real.fourier_deriv hi₁ (hf₁.differentiable (by simp)) hi₂
  have hscaled₀ := pd7ComplexFourierTransform_eq_scaled_fourier f hf hcompact ξ
  have hscaled₂ := pd7ComplexFourierTransform_eq_scaled_fourier f₂ hf₂ hc₂ ξ
  let w : ℝ := ξ / (2 * Real.pi)
  have hF₁ : 𝓕 f₁ w = (2 * Real.pi * Complex.I * w) * 𝓕 f w := by
    have h := congrFun hFourier₁ w
    simpa only [f₁, smul_eq_mul] using h
  have hF₂ : 𝓕 f₂ w = (2 * Real.pi * Complex.I * w) * 𝓕 f₁ w := by
    have h := congrFun hFourier₂ w
    simpa only [f₁, f₂, smul_eq_mul] using h
  have hfreq : (2 * Real.pi * Complex.I * w) = Complex.I * ξ := by
    dsimp [w]
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [hscaled₂, hscaled₀]
  have hco₂ : (hc₂.toSchwartzMap hf₂ : ℝ → ℂ) = f₂ := rfl
  have hco₀ : (hcompact.toSchwartzMap hf : ℝ → ℂ) = f := rfl
  have hFC₂ := congrArg 𝓕 hco₂
  have hFC₀ := congrArg 𝓕 hco₀
  rw [hFC₂, hFC₀, hF₂, hF₁, hfreq]
  ring

/-- The logarithmic Fourier transform is bounded pointwise by the normalized L¹ norm of its
source. -/
lemma pd7ComplexFourierTransform_norm_le (f : ℝ → ℂ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hcompact : HasCompactSupport f) (ξ : ℝ) :
    ‖pd7ComplexFourierTransform f ξ‖ ≤
      (1 / (2 * Real.pi)) * ∫ s : ℝ, ‖f s‖ := by
  rw [pd7ComplexFourierTransform_eq_scaled_fourier f hf hcompact ξ]
  rw [norm_mul]
  have hscale : ‖(1 / (2 * Real.pi : ℝ) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
    positivity
  have hFcoe : (hcompact.toSchwartzMap hf : ℝ → ℂ) = f := rfl
  have hFourier : ‖𝓕 (hcompact.toSchwartzMap hf : ℝ → ℂ)
      (ξ / (2 * Real.pi))‖ ≤ ∫ s : ℝ, ‖f s‖ := by
    change ‖VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ)
      (hcompact.toSchwartzMap hf : ℝ → ℂ) (ξ / (2 * Real.pi))‖ ≤ _
    calc
      _ ≤ ∫ s : ℝ, ‖(hcompact.toSchwartzMap hf : ℝ → ℂ) s‖ :=
        VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
      _ = ∫ s : ℝ, ‖f s‖ := by simp [hFcoe]
  calc
    _ = (1 / (2 * Real.pi)) *
        ‖𝓕 (hcompact.toSchwartzMap hf : ℝ → ℂ)
          (ξ / (2 * Real.pi))‖ := by rw [hscale]
    _ ≤ _ := mul_le_mul_of_nonneg_left hFourier (by positivity)

/-- The Fourier transform of a compactly supported smooth source is integrable in frequency. -/
lemma pd7ComplexFourierTransform_integrable (f : ℝ → ℂ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hcompact : HasCompactSupport f) :
    Integrable (fun ξ : ℝ => pd7ComplexFourierTransform f ξ) := by
  let F : SchwartzMap ℝ ℂ := hcompact.toSchwartzMap hf
  have hFint : Integrable (𝓕 (F : ℝ → ℂ)) := (𝓕 F).integrable
  have hscaleNe : (1 / (2 * Real.pi) : ℝ) ≠ 0 := by positivity
  have hscaled₀ : Integrable (fun ξ : ℝ =>
      𝓕 (F : ℝ → ℂ) ((1 / (2 * Real.pi)) * ξ)) :=
    hFint.comp_mul_left' hscaleNe
  have hscaled : Integrable (fun ξ : ℝ =>
      𝓕 (F : ℝ → ℂ) (ξ / (2 * Real.pi)) ) := by
    apply hscaled₀.congr
    filter_upwards [] with ξ
    congr 1
    field_simp [Real.pi_ne_zero]
  have hmul : Integrable (fun ξ : ℝ =>
      (1 / (2 * Real.pi : ℝ) : ℂ) *
        𝓕 (F : ℝ → ℂ) (ξ / (2 * Real.pi))) := by
    have hsmul := hscaled.smul (1 / (2 * Real.pi : ℝ) : ℂ)
    exact hsmul.congr (ae_of_all _ fun ξ => by
      change (1 / (2 * Real.pi : ℝ) : ℂ) •
        𝓕 (F : ℝ → ℂ) (ξ / (2 * Real.pi)) =
          (1 / (2 * Real.pi : ℝ) : ℂ) *
            𝓕 (F : ℝ → ℂ) (ξ / (2 * Real.pi))
      rfl)
  apply hmul.congr
  filter_upwards [] with ξ
  exact (pd7ComplexFourierTransform_eq_scaled_fourier f hf hcompact ξ).symm

/-- Integrate a compactly supported nonnegative function using a pointwise bound on its support. -/
lemma pd7_real_integral_bound_of_support_interval (f : ℝ → ℝ) (a b M : ℝ)
    (hab : a ≤ b) (hf : Continuous f)
    (hsupport : Function.support f ⊆ Set.Ioc a b)
    (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ M) :
    ∫ x : ℝ, f x ≤ M * (b - a) := by
  have hglobal :=
    intervalIntegral.integral_eq_integral_of_support_subset (μ := volume) hsupport
  have hfInt : IntervalIntegrable f volume a b := hf.intervalIntegrable (μ := volume) a b
  have hconstInt : IntervalIntegrable (fun _ : ℝ => M) volume a b :=
    continuous_const.intervalIntegrable (μ := volume) a b
  calc
    _ = ∫ x in a..b, f x := hglobal.symm
    _ ≤ ∫ x in a..b, M :=
      intervalIntegral.integral_mono_on hab hfInt hconstInt (fun x _ => (hbound x).2)
    _ = M * (b - a) := by simp [intervalIntegral.integral_const]; ring

/-- The Mellin cutoff transform has an L¹ norm with at most quadratic growth in its additive
frequency. -/
lemma pd7_major_cutoff_transform_L1_bound (eta : ℝ → ℝ)
    (heta : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) eta)
    (heta_supp : Function.support eta ⊆ Set.Icc 1 4) :
    ∃ Cη : ℝ, 0 < Cη ∧ ∀ lam : ℝ,
      ∫ ξ : ℝ, ‖pd7MajorCutoffTransform eta lam ξ‖ ≤ Cη * (1 + |lam|) ^ 2 := by
  obtain ⟨Mη₀, hMη₀, hηnorm⟩ := exists_major_eta_bound eta heta heta_supp
  obtain ⟨Mη₁, hMη₁, hηC2⟩ := exists_major_eta_C2_bound eta heta
  let Mη := max Mη₀ Mη₁
  have hMη : 0 < Mη := by dsimp [Mη]; positivity
  have hηnorm' : ∀ y : ℝ, ‖(eta y : ℂ)‖ ≤ Mη := by
    intro y
    exact (hηnorm y).trans (le_max_left _ _)
  have hηC2' : ∀ y ∈ Set.Icc (1 : ℝ) 4,
      |eta y| + |deriv eta y| + |deriv (deriv eta) y| ≤ Mη := by
    intro y hy
    exact (hηC2 y hy).trans (le_max_right _ _)
  have hg (lam : ℝ) :
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pd7MajorCutoffLog eta lam) := by
    have hη : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun s => (eta (Real.exp s) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (heta.comp Real.contDiff_exp)
    have hRarg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun s => -lam * Real.exp s) := by fun_prop
    have hCvalue : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun s => ((-lam * Real.exp s : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp hRarg
    have hCarg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun s => Complex.I * ((2 * Real.pi : ℂ) *
          ((-lam * Real.exp s : ℝ) : ℂ))) :=
      contDiff_const.mul (contDiff_const.mul hCvalue)
    have hphase : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun s => additiveCharacter (-lam * Real.exp s)) := by
      unfold additiveCharacter
      exact Complex.contDiff_exp.comp hCarg
    change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      ((fun s => (eta (Real.exp s) : ℂ)) *
        (fun s => additiveCharacter (-lam * Real.exp s)))
    exact hη.mul hphase
  have hgsupp (lam : ℝ) :
      Function.support (pd7MajorCutoffLog eta lam) ⊆
        Set.Icc (0 : ℝ) (Real.log 4) := by
    intro s hs
    have hgne : pd7MajorCutoffLog eta lam s ≠ 0 := by
      change pd7MajorCutoffLog eta lam s ≠ 0 at hs
      exact hs
    have hηne : eta (Real.exp s) ≠ 0 := by
      intro hz
      apply hgne
      simp [pd7MajorCutoffLog, pd7MajorCutoff, hz]
    have hηmem : Real.exp s ∈ Function.support eta := by
      change eta (Real.exp s) ≠ 0
      exact hηne
    have hband := heta_supp hηmem
    constructor
    · have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 1) hband.1
      simpa [Real.log_exp] using hlog
    · have hlog := Real.log_le_log (Real.exp_pos s) hband.2
      simpa [Real.log_exp] using hlog
  let len : ℝ := Real.log 4 + 2
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num : (1 : ℝ) < 4)
  have hlen : 0 < len := by
    dsimp [len]
    linarith
  let normScale : ℝ := 1 / (2 * Real.pi)
  have hnormScale : 0 < normScale := by dsimp [normScale]; positivity
  let cutoffConst : ℝ := 20 + 72 * Real.pi + 64 * Real.pi ^ 2
  have hcutoffConst : 0 < cutoffConst := by dsimp [cutoffConst]; positivity
  let A0 : ℝ := normScale * (Mη * len)
  let A2 : ℝ := normScale * (Mη * cutoffConst * len)
  have hA0 : 0 < A0 := by dsimp [A0]; positivity
  have hA2 : 0 < A2 := by dsimp [A2]; positivity
  let Cbase : ℝ := 2 * max A0 A2
  let Cη : ℝ := Cbase * Real.pi
  have hCbase : 0 < Cbase := by dsimp [Cbase]; positivity
  have hCη : 0 < Cη := by dsimp [Cη]; positivity
  refine ⟨Cη, hCη, ?_⟩
  intro lam
  let f : ℝ → ℂ := pd7MajorCutoffLog eta lam
  have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f := by
    simpa [f] using hg lam
  have hfsupp : Function.support f ⊆ Set.Icc (0 : ℝ) (Real.log 4) := by
    simpa [f] using hgsupp lam
  have hclosed : IsClosed (Set.Icc (0 : ℝ) (Real.log 4)) := isClosed_Icc
  have htsupp : tsupport f ⊆ Set.Icc (0 : ℝ) (Real.log 4) :=
    closure_minimal hfsupp hclosed
  have hfc : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hfsupp
  have hf₁ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv f) := by
    simpa using hf.deriv'
  have hf₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv (deriv f)) := by
    simpa using hf₁.deriv'
  have hfc₁ : HasCompactSupport (deriv f) := hfc.deriv
  have hfc₂ : HasCompactSupport (deriv (deriv f)) := hfc₁.deriv
  have hfsupp₂ : Function.support (deriv (deriv f)) ⊆
      Set.Icc (0 : ℝ) (Real.log 4) :=
    support_deriv_subset.trans (tsupport_deriv_subset.trans htsupp)
  have hnormf : ∀ s : ℝ, ‖f s‖ ≤ Mη := by
    intro s
    dsimp [f, pd7MajorCutoffLog, pd7MajorCutoff]
    rw [norm_mul]
    have hphase : ‖additiveCharacter (-lam * Real.exp s)‖ = 1 := by
      simp [additiveCharacter, Complex.norm_exp]
    rw [hphase]
    simpa using hηnorm' (Real.exp s)
  have hD2norm : ∀ s : ℝ,
      ‖deriv (deriv f) s‖ ≤
        Mη * cutoffConst * (1 + |lam|) ^ 2 := by
    intro s
    change ‖deriv (deriv (pd7MajorCutoffLog eta lam)) s‖ ≤ _
    rw [pd7_major_cutoff_log_second_deriv eta heta lam s]
    exact pd7_major_cutoff_log_second_deriv_bound eta heta heta_supp Mη hMη.le
      hηC2' lam s
  have hnormfsupp : Function.support (fun s : ℝ => ‖f s‖) ⊆
      Set.Ioc (-1) (Real.log 4 + 1) := by
    intro s hs
    change ‖f s‖ ≠ 0 at hs
    have hne : f s ≠ 0 := by
      intro hz
      apply hs
      simp [hz]
    have hmem : s ∈ Function.support f := by
      change f s ≠ 0
      exact hne
    have hb := hfsupp hmem
    exact ⟨by linarith [hb.1], by linarith [hb.2]⟩
  have hD2normsupp : Function.support (fun s : ℝ => ‖deriv (deriv f) s‖) ⊆
      Set.Ioc (-1) (Real.log 4 + 1) := by
    intro s hs
    change ‖deriv (deriv f) s‖ ≠ 0 at hs
    have hne : deriv (deriv f) s ≠ 0 := by
      intro hz
      apply hs
      simp [hz]
    have hmem : s ∈ Function.support (deriv (deriv f)) := by
      change deriv (deriv f) s ≠ 0
      exact hne
    have hb := hfsupp₂ hmem
    exact ⟨by linarith [hb.1], by linarith [hb.2]⟩
  have hI0 : ∫ s : ℝ, ‖f s‖ ≤ Mη * len := by
    have h := pd7_real_integral_bound_of_support_interval
      (fun s : ℝ => ‖f s‖) (-1) (Real.log 4 + 1) Mη (by linarith [hlog4])
      (continuous_norm.comp hf.continuous) hnormfsupp (fun s => ⟨norm_nonneg _, hnormf s⟩)
    calc
      _ ≤ Mη * ((Real.log 4 + 1) - (-1)) := h
      _ = Mη * len := by dsimp [len]; ring
  have hD2nonneg : 0 ≤ Mη * cutoffConst * (1 + |lam|) ^ 2 := by positivity
  have hI2 : ∫ s : ℝ, ‖deriv (deriv f) s‖ ≤
      (Mη * cutoffConst * (1 + |lam|) ^ 2) * len := by
    have h := pd7_real_integral_bound_of_support_interval
      (fun s : ℝ => ‖deriv (deriv f) s‖) (-1) (Real.log 4 + 1)
      (Mη * cutoffConst * (1 + |lam|) ^ 2)
      (by linarith [hlog4])
      (continuous_norm.comp hf₂.continuous) hD2normsupp
      (fun s => ⟨norm_nonneg _, hD2norm s⟩)
    calc
      _ ≤ (Mη * cutoffConst * (1 + |lam|) ^ 2) *
          ((Real.log 4 + 1) - (-1)) := h
      _ = (Mη * cutoffConst * (1 + |lam|) ^ 2) * len := by dsimp [len]; ring
  let factor : ℝ := (1 + |lam|) ^ 2
  have hfactor : 1 ≤ factor := by
    dsimp [factor]
    have habs : 0 ≤ |lam| := abs_nonneg lam
    nlinarith [sq_nonneg |lam|]
  have hfactor0 : 0 ≤ factor := le_trans (by norm_num) hfactor
  have hT0 (ξ : ℝ) :
      ‖pd7ComplexFourierTransform f ξ‖ ≤ A0 := by
    have h := pd7ComplexFourierTransform_norm_le f hf hfc ξ
    calc
      _ ≤ normScale * ∫ s : ℝ, ‖f s‖ := by simpa [normScale] using h
      _ ≤ normScale * (Mη * len) := mul_le_mul_of_nonneg_left hI0 hnormScale.le
      _ = A0 := by rfl
  have hT2 (ξ : ℝ) :
      ‖pd7ComplexFourierTransform (deriv (deriv f)) ξ‖ ≤ A2 * factor := by
    have h := pd7ComplexFourierTransform_norm_le (deriv (deriv f)) hf₂ hfc₂ ξ
    calc
      _ ≤ normScale * ∫ s : ℝ, ‖deriv (deriv f) s‖ := by
            simpa [normScale] using h
      _ ≤ normScale * ((Mη * cutoffConst * factor) * len) :=
            mul_le_mul_of_nonneg_left (by simpa [factor] using hI2) hnormScale.le
      _ = A2 * factor := by dsimp [A2]; dsimp [factor]; ring
  have hnormIξ (ξ : ℝ) : ‖Complex.I * (ξ : ℂ)‖ = |ξ| := by
    rw [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
    ring
  have hnormRel (ξ : ℝ) :
      ‖pd7ComplexFourierTransform (deriv (deriv f)) ξ‖ =
        ξ ^ 2 * ‖pd7ComplexFourierTransform f ξ‖ := by
    rw [pd7ComplexFourierTransform_second_deriv f hf hfc ξ]
    rw [norm_mul, norm_pow, hnormIξ]
    rw [sq_abs]
  have hdecay (ξ : ℝ) :
      ‖pd7ComplexFourierTransform f ξ‖ ≤ Cbase * factor / (1 + ξ ^ 2) := by
    have hden : 0 < 1 + ξ ^ 2 := by positivity
    by_cases hsmall : |ξ| ≤ 1
    · have hξsq : ξ ^ 2 ≤ 1 := by
        have hAbs : |ξ| ≤ |(1 : ℝ)| := by simpa using hsmall
        simpa using (sq_le_sq).2 hAbs
      apply (le_div_iff₀ hden).2
      calc
        ‖pd7ComplexFourierTransform f ξ‖ * (1 + ξ ^ 2) ≤
            A0 * (1 + ξ ^ 2) := mul_le_mul_of_nonneg_right (hT0 ξ) (by positivity)
        _ ≤ A0 * 2 := mul_le_mul_of_nonneg_left (by nlinarith) hA0.le
        _ ≤ Cbase * factor := by
          calc
            _ ≤ Cbase := by
              have hA0base : 2 * A0 ≤ Cbase := by
                dsimp [Cbase]
                nlinarith [le_max_left A0 A2]
              nlinarith [hA0base]
            _ = Cbase * 1 := by ring
            _ ≤ Cbase * factor := mul_le_mul_of_nonneg_left hfactor hCbase.le
    · have hlarge : 1 < |ξ| := lt_of_not_ge hsmall
      have hξsq : 1 < ξ ^ 2 := by
        have hAbs : |(1 : ℝ)| < |ξ| := by simpa using hlarge
        have hsquare : (1 : ℝ) ^ 2 < ξ ^ 2 := (sq_lt_sq).2 hAbs
        simpa using hsquare
      have hξsqpos : 0 < ξ ^ 2 := lt_trans zero_lt_one hξsq
      have hξne : ξ ≠ 0 := by
        intro hzero
        simp [hzero] at hξsqpos
      have hmul : ξ ^ 2 * ‖pd7ComplexFourierTransform f ξ‖ ≤ A2 * factor := by
        rw [← hnormRel ξ]
        exact hT2 ξ
      have hdiv : ‖pd7ComplexFourierTransform f ξ‖ ≤ A2 * factor / ξ ^ 2 := by
        calc
          _ = (ξ ^ 2 * ‖pd7ComplexFourierTransform f ξ‖) / ξ ^ 2 := by
                field_simp [ne_of_gt hξsqpos, hξne]
                <;> ring
          _ ≤ _ := div_le_div_of_nonneg_right hmul hξsqpos.le
      have hinv : 1 / ξ ^ 2 ≤ 2 / (1 + ξ ^ 2) := by
        apply (div_le_div_iff₀ hξsqpos hden).2
        nlinarith
      have hA2base : 2 * A2 ≤ Cbase := by
        dsimp [Cbase]
        nlinarith [le_max_right A0 A2]
      calc
        _ ≤ A2 * factor * (1 / ξ ^ 2) := by
              simpa [div_eq_mul_inv, mul_assoc] using hdiv
        _ ≤ A2 * factor * (2 / (1 + ξ ^ 2)) :=
              mul_le_mul_of_nonneg_left hinv (mul_nonneg hA2.le hfactor0)
        _ = (2 * A2 * factor) / (1 + ξ ^ 2) := by ring
        _ ≤ (Cbase * factor) / (1 + ξ ^ 2) :=
              div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_right hA2base hfactor0) hden.le
  have hTintegrable : Integrable (fun ξ : ℝ => pd7ComplexFourierTransform f ξ) :=
    pd7ComplexFourierTransform_integrable f hf hfc
  have hTnorm : Integrable (fun ξ : ℝ => ‖pd7ComplexFourierTransform f ξ‖) := hTintegrable.norm
  have hMajor : Integrable (fun ξ : ℝ => Cbase * factor * (1 + ξ ^ 2)⁻¹) := by
    have hsmul := integrable_inv_one_add_sq.smul (Cbase * factor)
    exact hsmul.congr (ae_of_all _ fun ξ => by rfl)
  change ∫ ξ : ℝ, ‖pd7ComplexFourierTransform f ξ‖ ≤ Cη * factor
  calc
    _ ≤ ∫ ξ : ℝ, Cbase * factor * (1 + ξ ^ 2)⁻¹ :=
      integral_mono_ae hTnorm hMajor (ae_of_all _ hdecay)
    _ = Cη * factor := by
      rw [integral_const_mul, integral_univ_inv_one_add_sq]
      dsimp [Cη, Cbase]
      ring

/-- Mellin inversion for the cutoff transform, with the normalization used in `majorBPolynomial`. -/
lemma pd7_major_cutoff_mellin_inversion (eta : ℝ → ℝ)
    (heta : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) eta)
    (heta_supp : Function.support eta ⊆ Set.Icc 1 4) (lam y : ℝ) (hy : 0 < y) :
    pd7MajorCutoff eta lam y =
      ∫ ξ : ℝ, pd7MajorCutoffTransform eta lam ξ *
        Complex.exp (Complex.I * ξ * Real.log y) := by
  let g : ℝ → ℂ := fun s => pd7MajorCutoff eta lam (Real.exp s)
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g := by
    have hη : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun s => (eta (Real.exp s) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (heta.comp Real.contDiff_exp)
    have hRarg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun s => -lam * Real.exp s) := by
      fun_prop
    have hCvalue : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun s => ((-lam * Real.exp s : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp hRarg
    have hCarg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun s => Complex.I * ((2 * Real.pi : ℂ) *
          ((-lam * Real.exp s : ℝ) : ℂ))) :=
      contDiff_const.mul (contDiff_const.mul hCvalue)
    have hphase : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun s => additiveCharacter (-lam * Real.exp s)) := by
      unfold additiveCharacter
      exact Complex.contDiff_exp.comp hCarg
    dsimp [g, pd7MajorCutoff]
    exact hη.mul hphase
  have hgsupp : Function.support g ⊆ Set.Icc 0 (Real.log 4) := by
    intro s hs
    have hgne : g s ≠ 0 := by
      change g s ≠ 0 at hs
      exact hs
    have hηne : eta (Real.exp s) ≠ 0 := by
      intro hz
      apply hgne
      simp [g, pd7MajorCutoff, hz]
    have hmem : Real.exp s ∈ Function.support eta := by
      change eta (Real.exp s) ≠ 0
      exact hηne
    have hband := heta_supp hmem
    constructor
    · have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 1) hband.1
      simpa [Real.log_exp] using hlog
    · have hlog := Real.log_le_log (Real.exp_pos s) hband.2
      simpa [Real.log_exp] using hlog
  have hgcompact : HasCompactSupport g :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hgsupp
  have hinv := pd7_complex_fourier_inversion g hg hgcompact (Real.log y)
  simpa [g, pd7MajorCutoffTransform, Real.exp_log hy] using hinv

lemma pd7_exp_log_mul (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (t : ℝ) :
    Complex.exp (Complex.I * t * Real.log (u * v)) =
      Complex.exp (Complex.I * t * Real.log u) *
        Complex.exp (Complex.I * t * Real.log v) := by
  rw [Real.log_mul hu.ne' hv.ne']
  have harg : Complex.I * (t : ℂ) *
      ((Real.log u + Real.log v : ℝ) : ℂ) =
      Complex.I * (t : ℂ) * (Real.log u : ℂ) +
        Complex.I * (t : ℂ) * (Real.log v : ℂ) := by
    push_cast
    ring
  rw [harg, Complex.exp_add]

lemma pd7_exp_log_div (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (t : ℝ) :
    Complex.exp (Complex.I * t * Real.log (u / v)) =
      Complex.exp (Complex.I * t * Real.log u) *
        Complex.exp (-Complex.I * t * Real.log v) := by
  rw [Real.log_div hu.ne' hv.ne']
  have harg : Complex.I * (t : ℂ) *
      ((Real.log u - Real.log v : ℝ) : ℂ) =
      Complex.I * (t : ℂ) * (Real.log u : ℂ) +
        (-Complex.I * (t : ℂ) * (Real.log v : ℂ)) := by
    push_cast
    ring
  rw [harg, Complex.exp_add]

lemma pd7_exp_log_add_time (u t₁ t₂ : ℝ) :
    Complex.exp (Complex.I * (t₁ + t₂) * Real.log u) =
      Complex.exp (Complex.I * t₁ * Real.log u) *
        Complex.exp (Complex.I * t₂ * Real.log u) := by
  have harg : Complex.I * ((t₁ + t₂) : ℂ) * (Real.log u : ℂ) =
      Complex.I * (t₁ : ℂ) * (Real.log u : ℂ) +
        Complex.I * (t₂ : ℂ) * (Real.log u : ℂ) := by
    push_cast
    ring
  rw [harg, Complex.exp_add]

lemma pd7_complex_exp_phase_norm (u v : ℝ) :
    ‖Complex.exp (Complex.I * u * v)‖ = 1 := by
  have harg : Complex.I * (u : ℂ) * (v : ℂ) = ((u * v : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.norm_exp_ofReal_mul_I]

lemma pd7_exp_log_product_ratio (p b Y t ξ : ℝ)
    (hp : 0 < p) (hb : 0 < b) (hY : 0 < Y) :
    Complex.exp (Complex.I * ξ * Real.log ((p * b) / Y)) *
        Complex.exp (Complex.I * t * Real.log (p * b)) =
      Complex.exp (-Complex.I * ξ * Real.log Y) *
        Complex.exp (Complex.I * (t + ξ) * Real.log p) *
        Complex.exp (Complex.I * (t + ξ) * Real.log b) := by
  rw [pd7_exp_log_div (p * b) Y (mul_pos hp hb) hY ξ,
    pd7_exp_log_mul p b hp hb ξ, pd7_exp_log_mul p b hp hb t]
  calc
    _ = Complex.exp (-Complex.I * ξ * Real.log Y) *
        (Complex.exp (Complex.I * ξ * Real.log p) *
          Complex.exp (Complex.I * t * Real.log p)) *
        (Complex.exp (Complex.I * ξ * Real.log b) *
          Complex.exp (Complex.I * t * Real.log b)) := by ring
    _ = _ := by
      rw [← pd7_exp_log_add_time p ξ t, ← pd7_exp_log_add_time b ξ t]
      have hargP : Complex.I * ((ξ + t : ℝ) : ℂ) * (Real.log p : ℂ) =
          Complex.I * ((t + ξ : ℝ) : ℂ) * (Real.log p : ℂ) := by
        push_cast
        ring
      have hargB : Complex.I * ((ξ + t : ℝ) : ℂ) * (Real.log b : ℂ) =
          Complex.I * ((t + ξ : ℝ) : ℂ) * (Real.log b : ℂ) := by
        push_cast
        ring
      simp only [Complex.ofReal_add] at hargP hargB
      rw [hargP, hargB]

lemma markedBandMass_cons (x : ℝ) (n : ℕ) (a : Fin (n + 1) → ℝ) :
    (∏ i : Fin (n + 1), (bandMass x (a i))⁻¹) =
      (bandMass x (a 0))⁻¹ *
        (∏ i : Fin n, (bandMass x (a i.succ))⁻¹) := by
  rw [Fin.prod_univ_succ]

lemma markedCharacter_cons {k n : ℕ} (χ : DirichletCharacter ℂ k)
    (p : ℕ) (rest : Fin n → ℕ) :
    χ ((tupleProduct (Fin.cons p rest) : ℕ) : ZMod k) =
      χ (p : ZMod k) * χ (tupleProduct rest : ZMod k) := by
  rw [tupleProduct_cons, Nat.cast_mul, map_mul]

/-- Mellin inversion replaces the coupled cutoff in the marked polynomial by its logarithmic
Fourier transform. -/
lemma majorBPolynomial_mellin (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (Y lam : ℝ) (eta : ℝ → ℝ)
    (heta : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) eta)
    (heta_supp : Function.support eta ⊆ Set.Icc 1 4)
    (hY : 0 < Y) {k : ℕ} (χ : DirichletCharacter ℂ k) (t : ℝ) :
    majorBPolynomial x K a Y lam eta χ t =
      (1 / Y : ℂ) * ∑ tb ∈ markedTupleSet x K a,
        (∫ ξ : ℝ, pd7MajorCutoffTransform eta lam ξ *
          Complex.exp (Complex.I * ξ *
            Real.log ((tupleProduct tb : ℝ) / Y))) *
        ((∏ i : Fin K, (bandMass x (a i))⁻¹ : ℝ) : ℂ) *
        χ ((tupleProduct tb : ℕ) : ZMod k) *
        Complex.exp (Complex.I * t * Real.log (tupleProduct tb : ℝ)) := by
  classical
  unfold majorBPolynomial
  congr 1
  apply Finset.sum_congr rfl
  intro tb htb
  let b := tupleProduct tb
  have hbposN : 0 < b := by simpa [b] using marked_tuple_pos x K a tb htb
  have hbpos : 0 < (b : ℝ) := by exact_mod_cast hbposN
  have hy : 0 < (b : ℝ) / Y := div_pos hbpos hY
  have hinv := pd7_major_cutoff_mellin_inversion eta heta heta_supp lam
    ((b : ℝ) / Y) hy
  have harg : -lam * (b : ℝ) / Y = -lam * ((b : ℝ) / Y) := by ring
  calc
    _ = pd7MajorCutoff eta lam ((b : ℝ) / Y) *
        ((∏ i : Fin K, (bandMass x (a i))⁻¹ : ℝ) : ℂ) *
        χ (b : ZMod k) * Complex.exp (Complex.I * t * Real.log (b : ℝ)) := by
          simp only [pd7MajorCutoff]
          rw [harg]
    _ = (∫ ξ : ℝ, pd7MajorCutoffTransform eta lam ξ *
          Complex.exp (Complex.I * ξ * Real.log ((b : ℝ) / Y))) *
        ((∏ i : Fin K, (bandMass x (a i))⁻¹ : ℝ) : ℂ) *
        χ (b : ZMod k) * Complex.exp (Complex.I * t * Real.log (b : ℝ)) := by
          rw [hinv]
    _ = _ := by rfl

/-- Factor the logarithmic Mellin kernel at the first marked prime. -/
lemma majorBPolynomial_mellin_cons_factorized (x Y lam : ℝ) (eta : ℝ → ℝ)
    (n : ℕ) (a : Fin (n + 1) → ℝ)
    (heta : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) eta)
    (heta_supp : Function.support eta ⊆ Set.Icc 1 4) (hY : 0 < Y)
    {k : ℕ} (χ : DirichletCharacter ℂ k) (t : ℝ) :
    majorBPolynomial x (n + 1) a Y lam eta χ t =
      (((bandMass x (a 0))⁻¹ : ℝ) : ℂ) * (1 / Y : ℂ) *
        ∫ ξ : ℝ,
          pd7MajorCutoffTransform eta lam ξ *
            Complex.exp (-Complex.I * ξ * Real.log Y) *
            (∑ p ∈ primeBand x (a 0),
              (χ (p : ZMod k) : ℂ) *
                Complex.exp (Complex.I * (t + ξ) * Real.log (p : ℝ))) *
            (∑ rest ∈ Fintype.piFinset
                (Fin.tail (fun i : Fin (n + 1) => primeBand x (a i))),
              (((∏ i : Fin n, (bandMass x (a i.succ))⁻¹ : ℝ) : ℝ) : ℂ) *
                χ (tupleProduct rest : ZMod k) *
                Complex.exp (Complex.I * (t + ξ) *
                  Real.log (tupleProduct rest : ℝ))) := by
  classical
  let P := primeBand x (a 0)
  let R := Fintype.piFinset
    (Fin.tail (fun i : Fin (n + 1) => primeBand x (a i)))
  let m₀ : ℝ := (bandMass x (a 0))⁻¹
  let mR : ℝ := ∏ i : Fin n, (bandMass x (a i.succ))⁻¹
  let f : ℝ → ℂ := pd7MajorCutoffLog eta lam
  have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f := by
    have hη : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun s => (eta (Real.exp s) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (heta.comp Real.contDiff_exp)
    have hRarg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun s => -lam * Real.exp s) := by fun_prop
    have hCvalue : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun s => ((-lam * Real.exp s : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp hRarg
    have hCarg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun s => Complex.I * ((2 * Real.pi : ℂ) *
          ((-lam * Real.exp s : ℝ) : ℂ))) :=
      contDiff_const.mul (contDiff_const.mul hCvalue)
    have hphase : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun s => additiveCharacter (-lam * Real.exp s)) := by
      unfold additiveCharacter
      exact Complex.contDiff_exp.comp hCarg
    change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      ((fun s => (eta (Real.exp s) : ℂ)) *
        (fun s => additiveCharacter (-lam * Real.exp s)))
    exact hη.mul hphase
  have hfsupp : Function.support f ⊆ Set.Icc (0 : ℝ) (Real.log 4) := by
    intro s hs
    have hgne : f s ≠ 0 := by change f s ≠ 0 at hs; exact hs
    have hηne : eta (Real.exp s) ≠ 0 := by
      intro hz
      apply hgne
      simp [f, pd7MajorCutoffLog, pd7MajorCutoff, hz]
    have hηmem : Real.exp s ∈ Function.support eta := by
      change eta (Real.exp s) ≠ 0
      exact hηne
    have hband := heta_supp hηmem
    constructor
    · have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 1) hband.1
      simpa [Real.log_exp] using hh
    · have hh := Real.log_le_log (Real.exp_pos s) hband.2
      simpa [Real.log_exp] using hh
  have hfc : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hfsupp
  have hT : Integrable (fun ξ : ℝ => pd7ComplexFourierTransform f ξ) :=
    pd7ComplexFourierTransform_integrable f hf hfc
  have hpProductPos (p : ℕ) (hp : p ∈ P) : 0 < (p : ℝ) := by
    have hprime : p.Prime := (Finset.mem_filter.mp hp).2.1
    exact_mod_cast hprime.pos
  have hrProductPos (r : Fin n → ℕ) (hr : r ∈ R) : 0 < (tupleProduct r : ℝ) := by
    have hcoords : ∀ i : Fin n, (r i).Prime := by
      intro i
      have hi : r i ∈ (Fin.tail (fun j : Fin (n + 1) => primeBand x (a j))) i :=
        Fintype.mem_piFinset.mp hr i
      simp only [Fin.tail] at hi
      exact (Finset.mem_filter.mp hi).2.1
    have hposN : 0 < tupleProduct r := by
      unfold tupleProduct
      apply Finset.prod_pos
      intro i hi
      exact (hcoords i).pos
    exact_mod_cast hposN
  let phase (p : ℕ) (r : Fin n → ℕ) (ξ : ℝ) : ℂ :=
    Complex.exp (-Complex.I * ξ * Real.log Y) *
      ((χ (p : ZMod k) : ℂ) *
        Complex.exp (Complex.I * (t + ξ) * Real.log (p : ℝ))) *
      (((mR : ℝ) : ℂ) * χ (tupleProduct r : ZMod k) *
        Complex.exp (Complex.I * (t + ξ) * Real.log (tupleProduct r : ℝ)))
  have hphaseCont (p : ℕ) (r : Fin n → ℕ) : Continuous (phase p r) := by
    dsimp [phase]
    fun_prop
  have hphaseNorm (p : ℕ) (r : Fin n → ℕ) (ξ : ℝ) :
      ‖phase p r ξ‖ ≤ ‖((mR : ℝ) : ℂ)‖ := by
    have hYphase : ‖Complex.exp (-Complex.I * ξ * Real.log Y)‖ = 1 := by
      have hh : -Complex.I * (ξ : ℂ) * (Real.log Y : ℂ) =
          Complex.I * ((-ξ : ℝ) : ℂ) * (Real.log Y : ℂ) := by
        push_cast
        ring
      rw [hh]
      exact pd7_complex_exp_phase_norm (-ξ) (Real.log Y)
    have hPphase : ‖Complex.exp
        (Complex.I * (t + ξ) * Real.log (p : ℝ))‖ = 1 :=
      by simpa only [Complex.ofReal_add] using
        pd7_complex_exp_phase_norm (t + ξ) (Real.log (p : ℝ))
    have hRphase : ‖Complex.exp
        (Complex.I * (t + ξ) * Real.log (tupleProduct r : ℝ))‖ = 1 :=
      by simpa only [Complex.ofReal_add] using
        pd7_complex_exp_phase_norm (t + ξ) (Real.log (tupleProduct r : ℝ))
    have hχp : ‖χ (p : ZMod k)‖ ≤ 1 := χ.norm_le_one _
    have hχr : ‖χ (tupleProduct r : ZMod k)‖ ≤ 1 := χ.norm_le_one _
    dsimp [phase]
    calc
      _ = ‖Complex.exp (-Complex.I * ξ * Real.log Y)‖ *
          (‖χ (p : ZMod k)‖ *
            ‖Complex.exp (Complex.I * (t + ξ) * Real.log (p : ℝ))‖) *
          (‖((mR : ℝ) : ℂ)‖ * ‖χ (tupleProduct r : ZMod k)‖ *
            ‖Complex.exp (Complex.I * (t + ξ) * Real.log (tupleProduct r : ℝ))‖) := by
            simp only [norm_mul]
      _ = ‖χ (p : ZMod k)‖ * ‖((mR : ℝ) : ℂ)‖ *
          ‖χ (tupleProduct r : ZMod k)‖ := by
            rw [hYphase, hPphase, hRphase]
            ring
      _ ≤ 1 * ‖((mR : ℝ) : ℂ)‖ * ‖χ (tupleProduct r : ZMod k)‖ := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hχp (norm_nonneg _)) (norm_nonneg _)
      _ ≤ 1 * ‖((mR : ℝ) : ℂ)‖ * 1 := by
            exact mul_le_mul_of_nonneg_left hχr
              (mul_nonneg (by norm_num) (norm_nonneg _))
      _ = ‖((mR : ℝ) : ℂ)‖ := by ring
  let F (p : ℕ) (r : Fin n → ℕ) (ξ : ℝ) : ℂ :=
    pd7ComplexFourierTransform f ξ * phase p r ξ
  have hFint (p : ℕ) (hp : p ∈ P) (r : Fin n → ℕ) (hr : r ∈ R) :
      Integrable (fun ξ : ℝ => F p r ξ) := by
    dsimp [F]
    exact hT.mul_bdd (hphaseCont p r).aestronglyMeasurable
      (ae_of_all _ fun ξ => hphaseNorm p r ξ)
  have hfactorSum (ξ : ℝ) :
      (∑ p ∈ P, ∑ r ∈ R, F p r ξ) =
        pd7ComplexFourierTransform f ξ *
          Complex.exp (-Complex.I * ξ * Real.log Y) *
          (∑ p ∈ P, (χ (p : ZMod k) : ℂ) *
            Complex.exp (Complex.I * (t + ξ) * Real.log (p : ℝ))) *
          (∑ r ∈ R, (((mR : ℝ) : ℂ) * χ (tupleProduct r : ZMod k)) *
            Complex.exp (Complex.I * (t + ξ) * Real.log (tupleProduct r : ℝ))) := by
    simp only [F, phase]
    calc
      _ = ∑ p ∈ P, ∑ r ∈ R,
          (pd7ComplexFourierTransform f ξ *
            Complex.exp (-Complex.I * ξ * Real.log Y) *
            ((χ (p : ZMod k) : ℂ) *
              Complex.exp (Complex.I * (t + ξ) * Real.log (p : ℝ)))) *
            ((((mR : ℝ) : ℂ) * χ (tupleProduct r : ZMod k)) *
              Complex.exp (Complex.I * (t + ξ) * Real.log (tupleProduct r : ℝ))) := by
            apply Finset.sum_congr rfl
            intro p hp
            apply Finset.sum_congr rfl
            intro r hr
            ring
      _ = ∑ p ∈ P,
          (pd7ComplexFourierTransform f ξ *
            Complex.exp (-Complex.I * ξ * Real.log Y) *
            ((χ (p : ZMod k) : ℂ) *
              Complex.exp (Complex.I * (t + ξ) * Real.log (p : ℝ)))) *
            (∑ r ∈ R,
              (((mR : ℝ) : ℂ) * χ (tupleProduct r : ZMod k)) *
                Complex.exp (Complex.I * (t + ξ) * Real.log (tupleProduct r : ℝ))) := by
            apply Finset.sum_congr rfl
            intro p hp
            rw [Finset.mul_sum]
      _ = (∑ p ∈ P,
            (pd7ComplexFourierTransform f ξ *
              Complex.exp (-Complex.I * ξ * Real.log Y)) *
              ((χ (p : ZMod k) : ℂ) *
                Complex.exp (Complex.I * (t + ξ) * Real.log (p : ℝ)))) *
          (∑ r ∈ R,
            (((mR : ℝ) : ℂ) * χ (tupleProduct r : ZMod k)) *
              Complex.exp (Complex.I * (t + ξ) * Real.log (tupleProduct r : ℝ))) := by
            rw [Finset.sum_mul]
      _ = _ := by rw [← Finset.mul_sum]
  have hIntSum :
      (∫ ξ : ℝ, ∑ p ∈ P, ∑ r ∈ R, F p r ξ) =
        ∑ p ∈ P, ∑ r ∈ R, ∫ ξ : ℝ, F p r ξ := by
    have hsum (ξ : ℝ) :
        (∑ p ∈ P, ∑ r ∈ R, F p r ξ) =
          ∑ z ∈ P.product R, F z.1 z.2 ξ := by
      exact (Finset.sum_product' P R (fun p r => F p r ξ)).symm
    calc
      _ = ∫ ξ : ℝ, ∑ z ∈ P.product R, F z.1 z.2 ξ := by
        apply integral_congr_ae
        exact ae_of_all _ fun ξ => hsum ξ
      _ = ∑ z ∈ P.product R, ∫ ξ : ℝ, F z.1 z.2 ξ := by
        apply integral_finsetSum
        intro z hz
        have hz' := Finset.mem_product.mp hz
        exact hFint z.1 hz'.1 z.2 hz'.2
      _ = _ := by
        exact Finset.sum_product' P R (fun p r => ∫ ξ : ℝ, F p r ξ)
  have hterm (p : ℕ) (hp : p ∈ P) (r : Fin n → ℕ) (hr : r ∈ R) :
      (∫ ξ : ℝ, pd7ComplexFourierTransform f ξ *
          Complex.exp (Complex.I * ξ *
            Real.log ((tupleProduct (Fin.cons p r) : ℝ) / Y))) *
        ((∏ i : Fin (n + 1), (bandMass x (a i))⁻¹ : ℝ) : ℂ) *
        χ ((tupleProduct (Fin.cons p r) : ℕ) : ZMod k) *
        Complex.exp (Complex.I * t * Real.log (tupleProduct (Fin.cons p r) : ℝ)) =
      (((m₀ : ℝ) : ℂ) * ∫ ξ : ℝ, F p r ξ) := by
    have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2.1
    have hppos : 0 < (p : ℝ) := by exact_mod_cast hpPrime.pos
    have hrpos := hrProductPos r hr
    have hmassC :
        ((∏ i : Fin (n + 1), (bandMass x (a i))⁻¹ : ℝ) : ℂ) =
          ((m₀ : ℝ) : ℂ) * ((mR : ℝ) : ℂ) := by
      rw [markedBandMass_cons]
      simp [m₀, mR]
    have hchar : χ ((p * tupleProduct r : ℕ) : ZMod k) =
        χ (p : ZMod k) * χ (tupleProduct r : ZMod k) := by
      rw [Nat.cast_mul, map_mul]
    have hphase (ξ : ℝ) :
        Complex.exp (Complex.I * ξ *
          Real.log (((p * tupleProduct r : ℕ) : ℝ) / Y)) *
          Complex.exp (Complex.I * t * Real.log ((p * tupleProduct r : ℕ) : ℝ)) =
        Complex.exp (-Complex.I * ξ * Real.log Y) *
          Complex.exp (Complex.I * (t + ξ) * Real.log (p : ℝ)) *
          Complex.exp (Complex.I * (t + ξ) * Real.log (tupleProduct r : ℝ)) := by
      simpa only [Nat.cast_mul] using
        pd7_exp_log_product_ratio (p : ℝ) (tupleProduct r : ℝ) Y t ξ hppos hrpos hY
    have hIntPhase :
        (∫ ξ : ℝ, pd7ComplexFourierTransform f ξ *
          Complex.exp (Complex.I * ξ *
            Real.log (((p * tupleProduct r : ℕ) : ℝ) / Y)) *
          Complex.exp (Complex.I * t * Real.log ((p * tupleProduct r : ℕ) : ℝ))) =
        ∫ ξ : ℝ, pd7ComplexFourierTransform f ξ *
          (Complex.exp (-Complex.I * ξ * Real.log Y) *
            Complex.exp (Complex.I * (t + ξ) * Real.log (p : ℝ)) *
            Complex.exp (Complex.I * (t + ξ) * Real.log (tupleProduct r : ℝ))) := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      calc
        _ = pd7ComplexFourierTransform f ξ *
            (Complex.exp (Complex.I * ξ *
              Real.log (((p * tupleProduct r : ℕ) : ℝ) / Y)) *
              Complex.exp (Complex.I * t * Real.log ((p * tupleProduct r : ℕ) : ℝ))) := by ring
        _ = _ := by rw [hphase ξ]
    rw [tupleProduct_cons]
    calc
      _ = (((∏ i : Fin (n + 1), (bandMass x (a i))⁻¹ : ℝ) : ℂ) *
          χ ((p * tupleProduct r : ℕ) : ZMod k)) *
          ((∫ ξ : ℝ, pd7ComplexFourierTransform f ξ *
            Complex.exp (Complex.I * ξ *
              Real.log (((p * tupleProduct r : ℕ) : ℝ) / Y))) *
            Complex.exp (Complex.I * t *
              Real.log ((p * tupleProduct r : ℕ) : ℝ))) := by ring
      _ = (((m₀ : ℝ) : ℂ) * ((mR : ℝ) : ℂ) *
          (χ (p : ZMod k) * χ (tupleProduct r : ZMod k))) *
          (∫ ξ : ℝ, pd7ComplexFourierTransform f ξ *
            (Complex.exp (-Complex.I * ξ * Real.log Y) *
              Complex.exp (Complex.I * (t + ξ) * Real.log (p : ℝ)) *
              Complex.exp (Complex.I * (t + ξ) *
                Real.log (tupleProduct r : ℝ)))) := by
            rw [hmassC, hchar, ← integral_mul_const, hIntPhase]
      _ = ((m₀ : ℝ) : ℂ) *
          ∫ ξ : ℝ,
            ((mR : ℝ) : ℂ) * χ (p : ZMod k) * χ (tupleProduct r : ZMod k) *
              (pd7ComplexFourierTransform f ξ *
                (Complex.exp (-Complex.I * ξ * Real.log Y) *
                  Complex.exp (Complex.I * (t + ξ) * Real.log (p : ℝ)) *
                    Complex.exp (Complex.I * (t + ξ) *
                    Real.log (tupleProduct r : ℝ)))) := by
            rw [integral_const_mul]
            ring
      _ = ((m₀ : ℝ) : ℂ) * ∫ ξ : ℝ, F p r ξ := by
            congr 1
            apply integral_congr_ae
            filter_upwards [] with ξ
            simp [F, phase, m₀, mR, mul_assoc, mul_left_comm, mul_comm]
  have hPtail :
      (∑ p ∈ P, ∑ r ∈ R,
        (∫ ξ : ℝ, pd7ComplexFourierTransform f ξ *
          Complex.exp (Complex.I * ξ *
            Real.log ((tupleProduct (Fin.cons p r) : ℝ) / Y))) *
          ((∏ i : Fin (n + 1), (bandMass x (a i))⁻¹ : ℝ) : ℂ) *
          χ ((tupleProduct (Fin.cons p r) : ℕ) : ZMod k) *
          Complex.exp (Complex.I * t * Real.log (tupleProduct (Fin.cons p r) : ℝ))) =
      ((m₀ : ℝ) : ℂ) * ∫ ξ : ℝ, ∑ p ∈ P, ∑ r ∈ R, F p r ξ := by
    calc
      _ = ∑ p ∈ P, ∑ r ∈ R,
          (((m₀ : ℝ) : ℂ) * ∫ ξ : ℝ, F p r ξ) := by
            apply Finset.sum_congr rfl
            intro p hp
            apply Finset.sum_congr rfl
            intro r hr
            exact hterm p hp r hr
      _ = ((m₀ : ℝ) : ℂ) *
          ∑ p ∈ P, ∑ r ∈ R, ∫ ξ : ℝ, F p r ξ := by
            simp_rw [Finset.mul_sum]
      _ = _ := by rw [← hIntSum]
  have hPsum (ξ : ℝ) :
      ∑ p ∈ P, ∑ r ∈ R, F p r ξ =
        pd7ComplexFourierTransform f ξ *
          Complex.exp (-Complex.I * ξ * Real.log Y) *
          (∑ p ∈ P,
            (χ (p : ZMod k) : ℂ) *
              Complex.exp (Complex.I * (t + ξ) * Real.log (p : ℝ))) *
          (∑ r ∈ R,
            (((mR : ℝ) : ℂ) * χ (tupleProduct r : ZMod k)) *
              Complex.exp (Complex.I * (t + ξ) *
                Real.log (tupleProduct r : ℝ))) := hfactorSum ξ
  calc
    _ = (1 / Y : ℂ) *
        ∑ p ∈ P, ∑ r ∈ R,
          (∫ ξ : ℝ, pd7ComplexFourierTransform f ξ *
            Complex.exp (Complex.I * ξ *
              Real.log ((tupleProduct (Fin.cons p r) : ℝ) / Y))) *
            ((∏ i : Fin (n + 1), (bandMass x (a i))⁻¹ : ℝ) : ℂ) *
            χ ((tupleProduct (Fin.cons p r) : ℕ) : ZMod k) *
            Complex.exp (Complex.I * t * Real.log (tupleProduct (Fin.cons p r) : ℝ)) := by
          rw [majorBPolynomial_mellin x (n + 1) a Y lam eta heta heta_supp hY χ t,
            sum_markedTupleSet_cons]
          rfl
    _ = ((m₀ : ℝ) : ℂ) * (1 / Y : ℂ) *
        ∫ ξ : ℝ, ∑ p ∈ P, ∑ r ∈ R, F p r ξ := by
          rw [hPtail]
          ring
    _ = ((m₀ : ℝ) : ℂ) * (1 / Y : ℂ) *
        ∫ ξ : ℝ,
          pd7ComplexFourierTransform f ξ *
            Complex.exp (-Complex.I * ξ * Real.log Y) *
            (∑ p ∈ P,
              (χ (p : ZMod k) : ℂ) *
                Complex.exp (Complex.I * (t + ξ) * Real.log (p : ℝ))) *
            (∑ r ∈ R,
              (((mR : ℝ) : ℂ) * χ (tupleProduct r : ZMod k)) *
                Complex.exp (Complex.I * (t + ξ) *
                  Real.log (tupleProduct r : ℝ))) := by
          have hI :
              (∫ ξ : ℝ, ∑ p ∈ P, ∑ r ∈ R, F p r ξ) =
                ∫ ξ : ℝ,
                  pd7ComplexFourierTransform f ξ *
                    Complex.exp (-Complex.I * ξ * Real.log Y) *
                    (∑ p ∈ P,
                      (χ (p : ZMod k) : ℂ) *
                        Complex.exp (Complex.I * (t + ξ) * Real.log (p : ℝ))) *
                    (∑ r ∈ R,
                      (((mR : ℝ) : ℂ) * χ (tupleProduct r : ZMod k)) *
                        Complex.exp (Complex.I * (t + ξ) *
                          Real.log (tupleProduct r : ℝ))) := by
              apply integral_congr_ae
              exact ae_of_all _ hPsum
          rw [hI]
    _ = _ := by rfl

lemma pd7d_rpow_add {L : ℝ} (hL : 0 < L) (a b : ℝ) :
    Real.rpow L (a + b) = Real.rpow L a * Real.rpow L b := Real.rpow_add hL a b
lemma pd7d_rpow_neg {L : ℝ} (hL : 0 ≤ L) (a : ℝ) :
    Real.rpow L (-a) = (Real.rpow L a)⁻¹ := Real.rpow_neg hL a
lemma pd7d_rpow_sub {L : ℝ} (hL : 0 < L) (a b : ℝ) :
    Real.rpow L (a - b) = Real.rpow L a / Real.rpow L b := Real.rpow_sub hL a b
lemma pd7d_rpow_one (L : ℝ) : Real.rpow L 1 = L := Real.rpow_one L
lemma pd7d_rpow_zero (L : ℝ) : Real.rpow L 0 = 1 := Real.rpow_zero L
lemma pd7d_rpow_natCast (L : ℝ) (n : ℕ) : Real.rpow L (n : ℝ) = L ^ n := Real.rpow_natCast L n

/-- The product mean square has constants fixed before the family, coefficients and characters. -/
lemma pd7d_product_mean_square_eventually (δ C c₁ c₂ : ℝ)
    (hδ : 0 < δ) (hC : 0 < C) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    ∃ Cmn C₄ : ℝ, 0 < Cmn ∧ 0 < C₄ ∧
      ∀ family : CoefficientFamily δ C c₁ c₂,
        ∃ x₀ : ℝ, 2 ≤ x₀ ∧ family.xMin ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
          ∀ beta : ℕ → ℂ,
            (∀ n ∈ dyadicIntegers (family.Hn x), ‖beta n‖ ≤ Real.rpow (Real.log x) C) →
            ∀ k : ℕ, ∀ χm χn : DirichletCharacter ℂ k, ∀ u v : ℝ, u ≤ v →
              (∫ t in u..v,
                ‖majorMPolynomial family x χm t * majorNPolynomial (family.Hn x) beta χn t‖ ^ 2) ≤
                Cmn * Real.rpow (Real.log x) C₄ * (1 + (v - u) / (family.Hm x * family.Hn x)) := by
  obtain ⟨Cτ, hCτ, Y₀, hY₀, htau⟩ := moment_bounds.1 2
  let Cmv := Classical.choose moment_bounds.2.1
  have hCmv : 0 < Cmv := (Classical.choose_spec moment_bounds.2.1).1
  let Cmn := 32 * Cmv * Cτ * Real.rpow 2 Cτ
  let C₄ := 4 * C + Cτ + 2
  refine ⟨Cmn, C₄, by dsimp [Cmn]; positivity, by dsimp [C₄]; linarith, ?_⟩
  intro family
  let x₀ := max family.xMin (max (Real.exp 1)
    (max (8 * c₂) (max (Y₀ / (4 * c₁)) (1 / c₁))))
  have hxMin : family.xMin ≤ x₀ := le_max_left _ _
  refine ⟨x₀, family.xMin_ge_two.trans hxMin, hxMin, ?_⟩
  intro x hx beta hbeta k χm χn u v huv
  have hxmin : family.xMin ≤ x := hxMin.trans hx
  have hx₂ : 2 ≤ x := family.xMin_ge_two.trans hxmin
  have hxpos : 0 < x := by linarith
  have hxExp : Real.exp 1 ≤ x :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hL : 1 ≤ Real.log x := by
    have hh := Real.log_le_log (Real.exp_pos 1) hxExp
    simpa using hh
  have hx8 : 8 * c₂ ≤ x :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hx))
  have hxtau : Y₀ / (4 * c₁) ≤ x :=
    (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hx)))
  have hxunit : 1 / c₁ ≤ x :=
    (le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hx)))
  obtain ⟨hHmlo, hHnlo, hXlo, hXhi⟩ := family.scales x hxmin
  have hHm : 0 < family.Hm x := (Real.rpow_pos_of_pos hxpos δ).trans_le hHmlo
  have hHn : 0 < family.Hn x := (Real.rpow_pos_of_pos hxpos δ).trans_le hHnlo
  let X := family.Hm x * family.Hn x
  have hX : 1 ≤ X := by
    have hh := (div_le_iff₀ hc₁).mp hxunit
    dsimp [X]
    nlinarith
  have htauX : Y₀ ≤ 4 * X := by
    have hh := (div_le_iff₀ (by positivity : 0 < 4 * c₁)).mp hxtau
    dsimp [X]
    nlinarith
  have hlog8 : Real.log (8 * X) ≤ 2 * Real.log x := by
    have hle : 8 * X ≤ x * x := by
      have h8X : 8 * X ≤ (8 * c₂) * x := by dsimp [X]; nlinarith
      exact h8X.trans (mul_le_mul_of_nonneg_right hx8 hxpos.le)
    calc
      _ ≤ Real.log (x * x) := Real.log_le_log (by positivity) hle
      _ = _ := by rw [Real.log_mul (ne_of_gt hxpos) (ne_of_gt hxpos)]; ring
  let N := ⌊4 * X⌋₊
  have hN : 1 ≤ N := Nat.le_floor (by norm_num; nlinarith)
  have hMpos : ∀ m ∈ familyTerms family x, 1 ≤ m := by
    intro m hm
    have hmB := (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).2
    have hmp : 0 < (m : ℝ) := hHm.trans_le hmB.1
    have hmn : 0 < m := by exact_mod_cast hmp
    exact hmn
  have hNpos : ∀ n ∈ dyadicIntegers (family.Hn x), 1 ≤ n := by
    intro n hn
    have hnB := (Finset.mem_filter.mp hn).2
    have hnp : 0 < (n : ℝ) := hHn.trans_le hnB.1
    exact_mod_cast hnp
  have hprod : ∀ m ∈ familyTerms family x,
      ∀ n ∈ dyadicIntegers (family.Hn x), m * n ≤ N := by
    intro m hm n hn
    have hmB := (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).2
    have hnB := (Finset.mem_filter.mp hn).2
    apply Nat.le_floor
    have hh := mul_le_mul hmB.2 hnB.2 (by positivity : 0 ≤ (n : ℝ)) (by positivity : 0 ≤ 2 * family.Hm x)
    push_cast
    try dsimp [X] at hh
    nlinarith [hh]
  have hAlpha : ∀ m ∈ familyTerms family x, ‖family.alpha x m‖ ≤ Real.rpow (Real.log x) C := by
    intro m hm
    exact family.coefficient_bound x hxmin m (Finset.mem_filter.mp hm).2
  obtain ⟨Cmn', C₄', hCmn', hC₄', hCmnEq, hC₄Eq, hbound⟩ :=
    majorMN_product_mean_square_log_bound family x (Real.log x) beta χm χn N C Cτ
      hHm hHn hMpos hNpos hprod hN hX rfl hL hC hCτ hlog8
      (by simpa [X, N, show (2 : ℝ) * (4 * (family.Hm x * family.Hn x)) =
        8 * (family.Hm x * family.Hn x) by ring] using (htau (4 * X) htauX).1) hAlpha hbeta
  rw [hCmnEq, hC₄Eq] at hbound
  exact hbound u v huv

/-- The sparse frequency estimate gives the exceptional part of the isolated prime energy. -/
lemma pd7d_isolated_prime_energy_bound (x X B P A_s Hn xi T m Emean Esp : ℝ)
    (Pset : Finset ℕ) (chi beta chiN : ℕ → ℂ) (M : ℝ → ℂ)
    (hL : 0 < Real.log x) (hX : 0 ≤ X) (hP : 1 ≤ P)
    (hT : 0 ≤ T) (hTwindow : T ≤ 2 * X * Real.rpow (Real.log x) B)
    (hm : 0 ≤ m) (hM : Continuous M)
    (hset : ∀ p ∈ Pset, P ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * P)
    (hchi : ∀ p ∈ Pset, ‖chi p‖ ≤ 1)
    (hcancel : ∀ t ∈ Set.Icc (-T) T, ‖M t‖ ≤ m)
    (hmean : (∫ t in (-T)..T, ‖M t * betaFrequency Hn beta chiN t‖ ^ 2) ≤ Emean)
    (hsparse : (∑' j : ℤ,
      if j ∈ sparseUnitIntervals x X B P A_s Pset chi xi then
        betaUnitIntervalEnergy Hn beta chiN j else 0) ≤ Esp) :
    (∫ t in (-T)..T,
      ‖bandPrimePolynomial P Pset chi xi t * M t * betaFrequency Hn beta chiN t‖ ^ 2) ≤
      (Real.rpow (Real.log x) (-A_s)) ^ 2 * Emean + 9 * m ^ 2 * Esp := by
  classical
  let bad := sparseUnitIntervals x X B P A_s Pset chi xi
  have hfinite : bad.Finite := by
    apply finite_set_of_bounded_unit_intervals
      (R := 2 * X * Real.rpow (Real.log x) B)
      (mul_nonneg (mul_nonneg (by norm_num) hX) (Real.rpow_nonneg hL.le B))
    intro j hj
    obtain ⟨t, hlow, hhigh, hwindow, _⟩ := hj
    exact ⟨t, hlow, hhigh, hwindow⟩
  let J := hfinite.toFinset
  have hN : Continuous (betaFrequency Hn beta chiN) := by
    unfold betaFrequency
    fun_prop
  have hPcont : Continuous (bandPrimePolynomial P Pset chi xi) := by
    unfold bandPrimePolynomial
    fun_prop
  have hNsup (j : ℤ) : BddAbove
      ((fun t => ‖betaFrequency Hn beta chiN t‖ ^ 2) ''
        Set.Icc (j : ℝ) ((j : ℝ) + 1)) :=
    (isCompact_Icc.image (hN.norm.pow 2)).bddAbove
  have hsup (j : ℤ) (t : ℝ) (ht : t ∈ Set.Icc (j : ℝ) ((j : ℝ) + 1)) :
      ‖betaFrequency Hn beta chiN t‖ ^ 2 ≤ betaUnitIntervalEnergy Hn beta chiN j :=
    le_csSup (hNsup j) (Set.mem_image_of_mem _ ht)
  have hW (j : ℤ) (hj : j ∈ J) : 0 ≤ betaUnitIntervalEnergy Hn beta chiN j :=
    (sq_nonneg _).trans (hsup j (j : ℝ) (by simp))
  have hsum : (∑ j ∈ J, betaUnitIntervalEnergy Hn beta chiN j) ≤ Esp := by
    have hEq : (∑' j : ℤ, if j ∈ bad then betaUnitIntervalEnergy Hn beta chiN j else 0) =
        ∑ j ∈ J, betaUnitIntervalEnergy Hn beta chiN j := by
      rw [tsum_eq_sum (s := J) (fun j hj => by
        have hnot : j ∉ bad := by simpa [J] using hj
        simp [hnot])]
      apply Finset.sum_congr rfl
      intro j hj
      have hjbad : j ∈ bad := by simpa [J] using hj
      simp [hjbad]
    rw [← hEq]
    exact hsparse
  have hprimeBound (t : ℝ) : ‖bandPrimePolynomial P Pset chi xi t‖ ≤ 3 := by
    calc
      _ ≤ (Pset.card : ℝ) / P := bandPrimePolynomial_norm_le P (by linarith) Pset chi xi t hchi
      _ ≤ 3 := (div_le_iff₀ (by linarith : 0 < P)).2
        (by simpa [mul_comm] using prime_band_card_le_three_mul P hP Pset hset)
  have hbad (t : ℝ) (ht : t ∈ Set.Icc (-T) T)
      (hlarge : Real.rpow (Real.log x) (-A_s) < ‖bandPrimePolynomial P Pset chi xi t‖) :
      ∃ j ∈ J, t ∈ Set.Icc (j : ℝ) ((j : ℝ) + 1) ∧
        ‖betaFrequency Hn beta chiN t‖ ^ 2 ≤ betaUnitIntervalEnergy Hn beta chiN j := by
    let j : ℤ := ⌊t⌋
    have hjt : t ∈ Set.Icc (j : ℝ) ((j : ℝ) + 1) :=
      ⟨Int.floor_le t, (Int.lt_floor_add_one t).le⟩
    have hwindow : |t| ≤ 2 * X * Real.rpow (Real.log x) B :=
      (abs_le.mpr ⟨ht.1, ht.2⟩).trans hTwindow
    have hpow : Real.rpow (Real.log x) A_s * Real.rpow (Real.log x) (-A_s) = 1 := by
      rw [← pd7d_rpow_add hL, add_neg_cancel, pd7d_rpow_zero]
    have hlarge' : 1 < Real.rpow (Real.log x) A_s * ‖bandPrimePolynomial P Pset chi xi t‖ := by
      rw [← hpow]
      exact mul_lt_mul_of_pos_left hlarge (Real.rpow_pos_of_pos hL _)
    have hjbad : j ∈ bad := ⟨t, hjt.1, hjt.2, hwindow, hlarge'⟩
    exact ⟨j, by simpa [J] using hjbad, hjt, hsup j t hjt⟩
  have henergy := pd7d_sparse_energy_bound
    (bandPrimePolynomial P Pset chi xi) M (betaFrequency Hn beta chiN)
    T (Real.rpow (Real.log x) (-A_s)) 3 m J
    (betaUnitIntervalEnergy Hn beta chiN) hPcont hM hN hT
    (Real.rpow_nonneg hL.le _) (by norm_num) hm hW hprimeBound hcancel hbad
  calc
    _ ≤ (Real.rpow (Real.log x) (-A_s)) ^ 2 *
        (∫ t in (-T)..T, ‖M t * betaFrequency Hn beta chiN t‖ ^ 2) +
          9 * m ^ 2 * ∑ j ∈ J, betaUnitIntervalEnergy Hn beta chiN j := by
      simpa only [show (3 : ℝ) ^ 2 = 9 by norm_num] using henergy
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left hmean (sq_nonneg _))
      (mul_le_mul_of_nonneg_left hsum (by positivity))

lemma pd7d_rpow_sq (L v : ℝ) (hL : 0 ≤ L) : (Real.rpow L v) ^ 2 = Real.rpow L (2 * v) := by
  calc
    _ = Real.rpow (Real.rpow L v) (2 : ℝ) := (Real.rpow_natCast _ 2).symm
    _ = Real.rpow L (v * 2) := (Real.rpow_mul hL v 2).symm
    _ = _ := by congr 1; ring

/-- PD's isolated energy bound is uniform in the entire real Mellin shift. -/
lemma pd7d_isolated_prime_energy_eventually (δ C c₁ c₂ A₀ B₁ Aiso : ℝ)
    (hδ : 0 < δ) (hC : 0 < C) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hA₀ : 0 < A₀) (hB₁ : 0 < B₁) (hAiso : 0 < Aiso)
    (family : CoefficientFamily δ C c₁ c₂) (hcancel : HasLongCoefficientCancellation family) :
    ∃ Ciso x₀ : ℝ, 0 < Ciso ∧ 2 ≤ x₀ ∧ family.xMin ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x → ∀ P : ℝ, 1 ≤ P →
        (1 / 20 : ℝ) * Real.rpow (Real.log x) (1 / 10 : ℝ) ≤ Real.log P →
        Real.log P ≤ 3 * Real.rpow (Real.log x) (1 / 5 : ℝ) →
        ∀ Pset : Finset ℕ, (∀ p ∈ Pset, p.Prime ∧ P ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * P) →
        ∀ beta : ℕ → ℂ,
          (∀ n ∈ dyadicIntegers (family.Hn x), ‖beta n‖ ≤ Real.rpow (Real.log x) C) →
        ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.rpow (Real.log x) A₀ →
        ∀ χb χm χn : DirichletCharacter ℂ k, ∀ xi : ℝ,
          (∫ t in (-(2 * (family.Hm x * family.Hn x) * Real.rpow (Real.log x) B₁))..
              (2 * (family.Hm x * family.Hn x) * Real.rpow (Real.log x) B₁),
            ‖bandPrimePolynomial P Pset (fun p => χb (p : ZMod k)) xi t *
              majorMPolynomial family x χm t * majorNPolynomial (family.Hn x) beta χn t‖ ^ 2) ≤
            Ciso * Real.rpow (Real.log x) (-Aiso) := by
  obtain ⟨Cmn, C₄, hCmn, hC₄, hmeanFamilies⟩ :=
    pd7d_product_mean_square_eventually δ C c₁ c₂ hδ hC hc₁ hc₂
  let A_s := (Aiso + C₄ + B₁ + 2) / 2
  let A := (Aiso + 2 * C + 3) / 2
  have hA_s : 0 < A_s := by dsimp [A_s]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  obtain ⟨Csp, xsp, hCsp, hxsp, hsparse⟩ :=
    sparse_frequency δ C hδ hC 3 (by norm_num) (B₁ + 1) A_s (by linarith) hA_s
  obtain ⟨CM, xM, hCM, hxM, hxMmin, hMbound⟩ :=
    hcancel A₀ B₁ A hA₀ hB₁ hA
  obtain ⟨xmn, hxmn, hxmnmin, hmean⟩ := hmeanFamilies family
  let Ciso := 5 * Cmn + 9 * CM ^ 2 * Csp
  have hCiso : 0 < Ciso := by dsimp [Ciso]; positivity
  have hxpow : ∀ᶠ x : ℝ in atTop, c₂ / 2 ≤ Real.rpow x δ :=
    (tendsto_rpow_atTop hδ).eventually_ge_atTop (c₂ / 2)
  have hLlarge : ∀ᶠ x : ℝ in atTop, max 1 c₂ ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually_ge_atTop (max 1 c₂)
  have hevent : ∀ᶠ x : ℝ in atTop, xsp ≤ x ∧ xM ≤ x ∧ xmn ≤ x ∧
      c₂ / 2 ≤ Real.rpow x δ ∧ max 1 c₂ ≤ Real.log x := by
    filter_upwards [eventually_ge_atTop xsp, eventually_ge_atTop xM,
      eventually_ge_atTop xmn, hxpow, hLlarge] with x hxsp hxM hxmn hxpow hL
    exact ⟨hxsp, hxM, hxmn, hxpow, hL⟩
  obtain ⟨xbase, hxbase⟩ := eventually_atTop.1 hevent
  let x₀ := max xbase family.xMin
  refine ⟨Ciso, x₀, hCiso, family.xMin_ge_two.trans (le_max_right _ _), le_max_right _ _, ?_⟩
  intro x hx P hP hPlo hPhi Pset hPset beta hbeta k hk hkle χb χm χn xi
  obtain ⟨hxsp', hxM', hxmn', hxpow', hLlarge'⟩ := hxbase x ((le_max_left _ _).trans hx)
  have hxmin : family.xMin ≤ x := (le_max_right _ _).trans hx
  have hxpos : 0 < x := by linarith [family.xMin_ge_two]
  let L := Real.log x
  let X := family.Hm x * family.Hn x
  let T := 2 * X * Real.rpow L B₁
  have hL : 1 ≤ L := (le_max_left _ _).trans hLlarge'
  have hLpos : 0 < L := by linarith
  have hpowA : 0 < Real.rpow L (-A) := Real.rpow_pos_of_pos hLpos _
  have hpowC₄ : 0 < Real.rpow L C₄ := Real.rpow_pos_of_pos hLpos _
  have hpowB₁ : 0 < Real.rpow L B₁ := Real.rpow_pos_of_pos hLpos _
  have hLc₂ : c₂ ≤ L := (le_max_right _ _).trans hLlarge'
  obtain ⟨hHmlo, hHnlo, hXlo, hXhi⟩ := family.scales x hxmin
  have hHm : 0 < family.Hm x := (Real.rpow_pos_of_pos hxpos δ).trans_le hHmlo
  have hHn : 0 < family.Hn x := (Real.rpow_pos_of_pos hxpos δ).trans_le hHnlo
  have hX : 0 < X := mul_pos hHm hHn
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hTwindow : T ≤ 2 * x * Real.rpow L (B₁ + 1) := by
    rw [pd7d_rpow_add hLpos, pd7d_rpow_one]
    dsimp [T]
    have hXL : X ≤ x * L := by
      calc
        _ ≤ c₂ * x := hXhi
        _ ≤ L * x := mul_le_mul_of_nonneg_right hLc₂ hxpos.le
        _ = _ := mul_comm _ _
    nlinarith [Real.rpow_pos_of_pos hLpos B₁]
  have hHnhi : family.Hn x ≤ 2 * x := by
    have hh : c₂ ≤ 2 * family.Hm x := by linarith
    nlinarith
  have hsp := (hsparse x hxsp' x (by linarith) (by linarith) P hPlo hPhi Pset hPset k hk
    χb xi (family.Hn x) hHnlo hHnhi beta (fun n => χn (n : ZMod k)) hbeta
    (fun n => χn.norm_le_one _)).2
  have hMsmall : ∀ t ∈ Set.Icc (-T) T,
      ‖majorMPolynomial family x χm t‖ ≤ CM * Real.rpow L (-A) := by
    intro t ht
    have htbound : |t| ≤ T := abs_le.mpr ht
    have hh := hMbound x hxM' k hk hkle χm t htbound
    have hnorm : ‖majorMPolynomial family x χm t‖ =
        ‖∑ m ∈ familyTerms family x, family.alpha x m * χm (m : ZMod k) *
          Complex.exp (Complex.I * t * Real.log (m : ℝ))‖ / family.Hm x := by
      unfold majorMPolynomial alphaFrequency
      rw [norm_mul, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hHm]
      ring
    rw [hnorm]
    exact hh
  have hMcont : Continuous (majorMPolynomial family x χm) := by
    unfold majorMPolynomial alphaFrequency
    fun_prop
  have hproductMean : (∫ t in (-T)..T,
      ‖majorMPolynomial family x χm t * majorNPolynomial (family.Hn x) beta χn t‖ ^ 2) ≤
      5 * Cmn * Real.rpow L (C₄ + B₁) := by
    have hh := hmean x hxmn' beta hbeta k χm χn (-T) T (by linarith)
    have hratio : 1 + (T - -T) / X = 1 + 4 * Real.rpow L B₁ := by
      dsimp [T]
      field_simp
      <;> ring
    have hpow : 1 ≤ Real.rpow L B₁ := Real.one_le_rpow hL hB₁.le
    calc
      _ ≤ Cmn * Real.rpow L C₄ * (1 + (T - -T) / X) := hh
      _ ≤ Cmn * Real.rpow L C₄ * (5 * Real.rpow L B₁) := by
        rw [hratio]
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by rw [pd7d_rpow_add hLpos]; ring
  have hiso := pd7d_isolated_prime_energy_bound x x (B₁ + 1) P A_s (family.Hn x) xi T
    (CM * Real.rpow L (-A)) (5 * Cmn * Real.rpow L (C₄ + B₁))
    (Csp * Real.rpow L (2 * C + 1)) Pset (fun p => χb (p : ZMod k)) beta
    (fun n => χn (n : ZMod k)) (majorMPolynomial family x χm)
    hLpos hxpos.le hP hT hTwindow (by positivity) hMcont
    (fun p hp => (hPset p hp).2) (fun p _ => χb.norm_le_one _) hMsmall hproductMean hsp
  have hsmallExponent : -2 * A_s + C₄ + B₁ = -Aiso - 2 := by dsimp [A_s]; ring
  have hbadExponent : -2 * A + 2 * C + 1 = -Aiso - 2 := by dsimp [A]; ring
  have hfinalPower : Real.rpow L (-Aiso - 2) ≤ Real.rpow L (-Aiso) :=
    Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  change (∫ t in (-T)..T, _) ≤ _
  calc
    _ ≤ (Real.rpow L (-A_s)) ^ 2 * (5 * Cmn * Real.rpow L (C₄ + B₁)) +
        9 * (CM * Real.rpow L (-A)) ^ 2 * (Csp * Real.rpow L (2 * C + 1)) := hiso
    _ = Ciso * Real.rpow L (-Aiso - 2) := by
      rw [mul_pow, pd7d_rpow_sq L (-A_s) hLpos.le, pd7d_rpow_sq L (-A) hLpos.le]
      have hfirst : Real.rpow L (2 * -A_s) * Real.rpow L (C₄ + B₁) =
          Real.rpow L (-Aiso - 2) := by rw [← pd7d_rpow_add hLpos]; congr 1; linarith
      have hsecond : Real.rpow L (2 * -A) * Real.rpow L (2 * C + 1) =
          Real.rpow L (-Aiso - 2) := by rw [← pd7d_rpow_add hLpos]; congr 1; linarith
      calc
        _ = 5 * Cmn * (Real.rpow L (2 * -A_s) * Real.rpow L (C₄ + B₁)) +
            9 * CM ^ 2 * Csp * (Real.rpow L (2 * -A) * Real.rpow L (2 * C + 1)) := by ring
        _ = _ := by rw [hfirst, hsecond]; dsimp [Ciso]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hfinalPower hCiso.le

lemma pd7d_cutoff_transform_integrable (eta : ℝ → ℝ)
    (heta : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) eta)
    (heta_supp : Function.support eta ⊆ Set.Icc 1 4) (lam : ℝ) :
    Integrable (pd7MajorCutoffTransform eta lam) := by
  let f := pd7MajorCutoffLog eta lam
  have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f := by
    have hη := Complex.ofRealCLM.contDiff.comp (heta.comp Real.contDiff_exp)
    have hRarg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s => -lam * Real.exp s) := by fun_prop
    have hCvalue := Complex.ofRealCLM.contDiff.comp hRarg
    have hCarg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun s => Complex.I * ((2 * Real.pi : ℂ) * ((-lam * Real.exp s : ℝ) : ℂ))) :=
      contDiff_const.mul (contDiff_const.mul hCvalue)
    have hphase : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun s => additiveCharacter (-lam * Real.exp s)) := by
      unfold additiveCharacter
      exact Complex.contDiff_exp.comp hCarg
    change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      ((fun s => (eta (Real.exp s) : ℂ)) * (fun s => additiveCharacter (-lam * Real.exp s)))
    exact hη.mul hphase
  have hsupp : Function.support f ⊆ Set.Icc (0 : ℝ) (Real.log 4) := by
    intro s hs
    have hη : eta (Real.exp s) ≠ 0 := by
      intro hz
      exact hs (by simp [f, pd7MajorCutoffLog, pd7MajorCutoff, hz])
    have hband := heta_supp hη
    constructor
    · simpa using Real.log_le_log (by norm_num : (0 : ℝ) < 1) hband.1
    · simpa using Real.log_le_log (Real.exp_pos s) hband.2
  exact pd7ComplexFourierTransform_integrable f hf
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp)

/-- Finite Mellin separation works for an arbitrary first-prime subset and tail subset. -/
lemma pd7d_mellin_finite_product {α : Type*} (Pset : Finset ℕ) (Rset : Finset α)
    (b : α → ℕ) (W Y lam t : ℝ) (eta : ℝ → ℝ) {k : ℕ} (χ : DirichletCharacter ℂ k)
    (heta : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) eta)
    (heta_supp : Function.support eta ⊆ Set.Icc 1 4) (hY : 0 < Y)
    (hp : ∀ p ∈ Pset, 0 < p) (hb : ∀ r ∈ Rset, 0 < b r) :
    (∑ p ∈ Pset, ∑ r ∈ Rset,
      pd7MajorCutoff eta lam (((p * b r : ℕ) : ℝ) / Y) *
        (W : ℂ) * χ ((p * b r : ℕ) : ZMod k) *
        Complex.exp (Complex.I * t * Real.log ((p * b r : ℕ) : ℝ))) =
      ∫ ξ : ℝ, pd7MajorCutoffTransform eta lam ξ *
        Complex.exp (-Complex.I * ξ * Real.log Y) *
        (∑ p ∈ Pset, χ (p : ZMod k) * Complex.exp (Complex.I * (t + ξ) * Real.log (p : ℝ))) *
        (∑ r ∈ Rset, (W : ℂ) * χ (b r : ZMod k) *
          Complex.exp (Complex.I * (t + ξ) * Real.log (b r : ℝ))) := by
  classical
  let phase (p : ℕ) (r : α) (ξ : ℝ) : ℂ :=
    Complex.exp (-Complex.I * ξ * Real.log Y) *
      (χ (p : ZMod k) * Complex.exp (Complex.I * (t + ξ) * Real.log (p : ℝ))) *
      ((W : ℂ) * χ (b r : ZMod k) * Complex.exp (Complex.I * (t + ξ) * Real.log (b r : ℝ)))
  have hphase : ∀ p r ξ, ‖phase p r ξ‖ ≤ |W| := by
    intro p r ξ
    dsimp [phase]
    have hYphase : ‖Complex.exp (-Complex.I * ξ * Real.log Y)‖ = 1 := by
      rw [Complex.norm_exp]
      simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im, Complex.add_re, Complex.add_im,
        zero_mul, mul_zero, one_mul, zero_sub, sub_zero, add_zero, zero_add,
        neg_zero, Real.exp_zero]
    have hpPhase : ‖Complex.exp (Complex.I * (t + ξ) * Real.log (p : ℝ))‖ = 1 := by
      rw [Complex.norm_exp]
      simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im, Complex.add_re, Complex.add_im,
        zero_mul, mul_zero, one_mul, zero_sub, sub_zero, add_zero, zero_add,
        neg_zero, Real.exp_zero]
    have hbPhase : ‖Complex.exp (Complex.I * (t + ξ) * Real.log (b r : ℝ))‖ = 1 := by
      rw [Complex.norm_exp]
      simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im, Complex.add_re, Complex.add_im,
        zero_mul, mul_zero, one_mul, zero_sub, sub_zero, add_zero, zero_add,
        neg_zero, Real.exp_zero]
    simp only [norm_mul, hYphase, hpPhase, hbPhase, one_mul, mul_one,
      Complex.norm_real, Real.norm_eq_abs]
    calc
      ‖χ (p : ZMod k)‖ * (|W| * ‖χ (b r : ZMod k)‖) ≤ 1 * (|W| * 1) :=
        mul_le_mul (χ.norm_le_one _) (mul_le_mul_of_nonneg_left (χ.norm_le_one _) (abs_nonneg _))
          (mul_nonneg (abs_nonneg _) (norm_nonneg _)) (by norm_num)
      _ = _ := by ring
  have hTi := pd7d_cutoff_transform_integrable eta heta heta_supp lam
  have hFi (p : ℕ) (r : α) : Integrable (fun ξ => pd7MajorCutoffTransform eta lam ξ * phase p r ξ) :=
    hTi.mul_bdd (show Continuous (phase p r) by dsimp [phase]; fun_prop).aestronglyMeasurable (ae_of_all _ fun ξ => hphase p r ξ)
  have hterm (p : ℕ) (hpp : p ∈ Pset) (r : α) (hrr : r ∈ Rset) :
      pd7MajorCutoff eta lam (((p * b r : ℕ) : ℝ) / Y) * (W : ℂ) *
        χ ((p * b r : ℕ) : ZMod k) * Complex.exp (Complex.I * t * Real.log ((p * b r : ℕ) : ℝ)) =
      ∫ ξ : ℝ, pd7MajorCutoffTransform eta lam ξ * phase p r ξ := by
    have hpR : 0 < (p : ℝ) := by exact_mod_cast hp p hpp
    have hbR : 0 < (b r : ℝ) := by exact_mod_cast hb r hrr
    have hprodR : 0 < ((p * b r : ℕ) : ℝ) / Y := by push_cast; positivity
    rw [pd7_major_cutoff_mellin_inversion eta heta heta_supp lam _ hprodR,
      ← integral_mul_const, ← integral_mul_const, ← integral_mul_const]
    apply integral_congr_ae
    filter_upwards [] with ξ
    simp only [Nat.cast_mul, map_mul]
    have hph := pd7_exp_log_product_ratio (p : ℝ) (b r : ℝ) Y t ξ hpR hbR hY
    dsimp [phase]
    calc
      _ = pd7MajorCutoffTransform eta lam ξ * (W : ℂ) * χ (p : ZMod k) * χ (b r : ZMod k) *
          (Complex.exp (Complex.I * ξ * Real.log ((p : ℝ) * b r / Y)) *
            Complex.exp (Complex.I * t * Real.log ((p : ℝ) * b r))) := by ring
      _ = _ := by rw [hph]; ring
  calc
    _ = ∑ p ∈ Pset, ∑ r ∈ Rset, ∫ ξ : ℝ, pd7MajorCutoffTransform eta lam ξ * phase p r ξ := by
      apply Finset.sum_congr rfl
      intro p hpp
      exact Finset.sum_congr rfl (fun r hrr => hterm p hpp r hrr)
    _ = ∫ ξ : ℝ, ∑ p ∈ Pset, ∑ r ∈ Rset, pd7MajorCutoffTransform eta lam ξ * phase p r ξ := by
      rw [integral_finsetSum _ (fun p _ => integrable_finsetSum _ (fun r _ => hFi p r))]
      apply Finset.sum_congr rfl
      intro p hpp
      rw [integral_finsetSum _ (fun r _ => hFi p r)]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      dsimp [phase]
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r hrr
      apply Finset.sum_congr rfl
      intro p hpp
      ring

noncomputable def pd7dMajorDyadPolynomial (x Y lam : ℝ) (eta : ℝ → ℝ)
    {n : ℕ} (a : Fin (n + 1) → ℝ) (j : ℕ) {k : ℕ}
    (χ : DirichletCharacter ℂ k) (t : ℝ) : ℂ :=
  (1 / Y : ℂ) * ∑ p ∈ pd7dPrimeDyad (primeBand x (a 0)) j,
    ∑ rest ∈ Fintype.piFinset (Fin.tail (fun i : Fin (n + 1) => primeBand x (a i))),
      (eta ((tupleProduct (Fin.cons p rest) : ℝ) / Y) : ℂ) *
        additiveCharacter (-lam * (tupleProduct (Fin.cons p rest) : ℝ) / Y) *
        ((∏ i : Fin (n + 1), (bandMass x (a i))⁻¹ : ℝ) : ℂ) *
        χ (tupleProduct (Fin.cons p rest) : ZMod k) *
        Complex.exp (Complex.I * t * Real.log (tupleProduct (Fin.cons p rest) : ℝ))

lemma pd7d_majorB_sum_dyads (x Y lam : ℝ) (eta : ℝ → ℝ)
    {n : ℕ} (a : Fin (n + 1) → ℝ) {k : ℕ} (χ : DirichletCharacter ℂ k) (t : ℝ) :
    majorBPolynomial x (n + 1) a Y lam eta χ t =
      ∑ j ∈ pd7dPrimeDyads (primeBand x (a 0)), pd7dMajorDyadPolynomial x Y lam eta a j χ t := by
  rw [majorBPolynomial_cons, pd7d_sum_prime_dyads]
  exact Finset.mul_sum _ _ _

lemma pd7d_major_dyad_mellin (x Y lam : ℝ) (eta : ℝ → ℝ)
    {n : ℕ} (a : Fin (n + 1) → ℝ) (j : ℕ) {k : ℕ} (χ : DirichletCharacter ℂ k) (t : ℝ)
    (heta : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) eta)
    (heta_supp : Function.support eta ⊆ Set.Icc 1 4) (hY : 0 < Y) :
    let P := (2 : ℝ) ^ j
    let S := pd7dPrimeDyad (primeBand x (a 0)) j
    let Rset := Fintype.piFinset (fun i : Fin n => primeBand x (a i.succ))
    let W := ∏ i : Fin n, (bandMass x (a i.succ))⁻¹
    pd7dMajorDyadPolynomial x Y lam eta a j χ t =
      (((bandMass x (a 0))⁻¹ : ℝ) : ℂ) * ∫ ξ : ℝ,
        pd7MajorCutoffTransform eta lam ξ * Complex.exp (-Complex.I * ξ * Real.log Y) *
          bandPrimePolynomial P S (fun p => χ (p : ZMod k)) ξ t *
          pd7dTailPolynomial Rset tupleProduct W P Y (fun b => χ (b : ZMod k)) (t + ξ) := by
  classical
  dsimp only
  let P := (2 : ℝ) ^ j
  let S := pd7dPrimeDyad (primeBand x (a 0)) j
  let Rset := Fintype.piFinset (fun i : Fin n => primeBand x (a i.succ))
  let W : ℝ := ∏ i : Fin n, (bandMass x (a i.succ))⁻¹
  let m₀ : ℝ := (bandMass x (a 0))⁻¹
  let Rsub := Rset.filter (fun r => Y / (2 * P) ≤ (tupleProduct r : ℝ) ∧
    (tupleProduct r : ℝ) ≤ 4 * Y / P)
  have hP : 0 < P := by dsimp [P]; positivity
  have hp (p : ℕ) (hp : p ∈ S) : 0 < p :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1.pos
  have hb (r : Fin n → ℕ) (hr : r ∈ Rset) : 0 < tupleProduct r :=
    marked_tuple_pos x n (Fin.tail a) r hr
  let F (p : ℕ) (r : Fin n → ℕ) : ℂ := pd7MajorCutoff eta lam (((p * tupleProduct r : ℕ) : ℝ) / Y) *
    (W : ℂ) * χ ((p * tupleProduct r : ℕ) : ZMod k) *
    Complex.exp (Complex.I * t * Real.log ((p * tupleProduct r : ℕ) : ℝ))
  have hzero (p : ℕ) (hpp : p ∈ S) (r : Fin n → ℕ) (hrr : r ∈ Rset)
      (hrout : r ∉ Rsub) : F p r = 0 := by
    have hpR : 0 < (p : ℝ) := by exact_mod_cast hp p hpp
    have hbR : 0 < (tupleProduct r : ℝ) := by exact_mod_cast hb r hrr
    obtain ⟨hpLo, hpHi⟩ := pd7dPrimeDyad_bounds _ j p hpp (hp p hpp)
    change P ≤ (p : ℝ) at hpLo
    change (p : ℝ) < 2 * P at hpHi
    have hηzero : eta (((p * tupleProduct r : ℕ) : ℝ) / Y) = 0 := by
      by_contra hη
      have hηband := heta_supp hη
      simp only [Nat.cast_mul] at hηband
      have hYlo : Y ≤ (p : ℝ) * tupleProduct r := by
        simpa only [one_mul] using (le_div_iff₀ hY).mp hηband.1
      have hYhi : (p : ℝ) * tupleProduct r ≤ 4 * Y := (div_le_iff₀ hY).mp hηband.2
      apply hrout
      apply Finset.mem_filter.mpr
      refine ⟨hrr, ?_, ?_⟩
      · apply (div_le_iff₀ (by positivity : 0 < 2 * P)).2
        have hh := mul_le_mul_of_nonneg_right hpHi.le hbR.le
        nlinarith
      · apply (le_div_iff₀ hP).2
        have hh := mul_le_mul_of_nonneg_right hpLo hbR.le
        nlinarith
    dsimp only [F, pd7MajorCutoff]
    rw [hηzero]
    simp only [Complex.ofReal_zero, zero_mul]
  have hrestrict : (∑ p ∈ S, ∑ r ∈ Rset, F p r) = ∑ p ∈ S, ∑ r ∈ Rsub, F p r := by
    apply Finset.sum_congr rfl
    intro p hpp
    exact (Finset.sum_subset (Finset.filter_subset _ _) (fun r hr hout => hzero p hpp r hr hout)).symm
  have hstart : pd7dMajorDyadPolynomial x Y lam eta a j χ t =
      (m₀ / Y : ℂ) * ∑ p ∈ S, ∑ r ∈ Rset, F p r := by
    unfold pd7dMajorDyadPolynomial
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hpp
    try simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hrr
    simp only [tupleProduct_cons, markedBandMass_cons]
    dsimp [F, pd7MajorCutoff, m₀, W]
    push_cast
    simp only [mul_div_assoc]
    ring
  rw [hstart, hrestrict, pd7d_mellin_finite_product S Rsub tupleProduct W Y lam t eta χ
    heta heta_supp hY hp (fun r hr => hb r (Finset.mem_filter.mp hr).1)]
  change (m₀ / Y : ℂ) * (∫ ξ : ℝ, _) = (m₀ : ℂ) * (∫ ξ : ℝ, _)
  rw [← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with ξ
  dsimp only [bandPrimePolynomial, pd7dTailPolynomial]
  simp only [Complex.ofReal_add]
  have hPc : (P : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hP
  have hYc : (Y : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hY
  have halg (F A B : ℂ) : (m₀ / Y : ℂ) * (F * A * B) =
      (m₀ : ℂ) * (F * ((1 / P : ℂ) * A) * ((P / Y : ℂ) * B)) := by
    field_simp [hPc, hYc]
    <;> ring
  exact halg _ _ _

lemma pd7d_continuous_first_section (F : ℝ → ℝ → ℂ)
    (hF : Continuous (Function.uncurry F)) (ξ : ℝ) : Continuous (fun t => F ξ t) := by
  have hPair : Continuous (fun t : ℝ => (ξ, t)) := continuous_const.prodMk continuous_id
  exact hF.comp hPair

set_option maxHeartbeats 4000000 in
lemma pd7d_major_dyad_energy_bound (x Y lam : ℝ) (eta : ℝ → ℝ)
    {n : ℕ} (a : Fin (n + 1) → ℝ) (j : ℕ) {k : ℕ} (χ : DirichletCharacter ℂ k)
    (M N : ℝ → ℂ) (T Rm Rn E : ℝ)
    (heta : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) eta)
    (heta_supp : Function.support eta ⊆ Set.Icc 1 4) (hY : 0 < Y)
    (hMass : ∀ i : Fin n, 0 < bandMass x (a i.succ))
    (hT : 0 ≤ T) (hM : Continuous M) (hN : Continuous N)
    (hRm : 0 ≤ Rm) (hRn : 0 ≤ Rn)
    (hMb : ∀ t, ‖M t‖ ≤ Rm) (hNb : ∀ t, ‖N t‖ ≤ Rn)
    (hIso : ∀ ξ : ℝ,
      (∫ t in (-T)..T, ‖bandPrimePolynomial ((2 : ℝ) ^ j)
        (pd7dPrimeDyad (primeBand x (a 0)) j) (fun p => χ (p : ZMod k)) ξ t * M t * N t‖ ^ 2) ≤ E) :
    (∫ t in (-T)..T, ‖pd7dMajorDyadPolynomial x Y lam eta a j χ t * M t * N t‖ ^ 2) ≤
      16 * ((bandMass x (a 0))⁻¹) ^ 2 *
        (∫ ξ : ℝ, ‖pd7MajorCutoffTransform eta lam ξ‖) ^ 2 * E := by
  let P := (2 : ℝ) ^ j
  let S := pd7dPrimeDyad (primeBand x (a 0)) j
  let Rset := Fintype.piFinset (fun i : Fin n => primeBand x (a i.succ))
  let W : ℝ := ∏ i : Fin n, (bandMass x (a i.succ))⁻¹
  let Q := pd7dTailPolynomial Rset tupleProduct W P Y (fun b => χ (b : ZMod k))
  let Ps := bandPrimePolynomial P S (fun p => χ (p : ZMod k))
  let U (ξ t : ℝ) : ℂ := Complex.exp (-Complex.I * ξ * Real.log Y) * Ps ξ t * Q (t + ξ) * M t * N t
  have hP : 0 < P := by dsimp [P]; positivity
  have hPone : 1 ≤ P := by dsimp [P]; exact one_le_pow₀ (by norm_num)
  have hW : 0 ≤ W := by
    dsimp [W]
    exact (Finset.prod_pos (fun i _ => inv_pos.mpr (hMass i))).le
  have htailPos (r : Fin n → ℕ) (hr : r ∈ Rset) : 0 < tupleProduct r :=
    marked_tuple_pos x n (Fin.tail a) r hr
  have htailMass : (∑ r ∈ Rset, W / (tupleProduct r : ℝ)) = 1 :=
    marked_reciprocal_mass x n (Fin.tail a) (fun i => ne_of_gt (hMass i))
  have hQ (u : ℝ) : ‖Q u‖ ≤ 4 := by
    have hh := pd7dTailPolynomial_norm_le Rset tupleProduct W P Y (fun b => χ (b : ZMod k)) u
      hW hP hY htailPos (fun _ _ => χ.norm_le_one _)
    simpa [Q, htailMass] using hh
  have hPs (ξ t : ℝ) : ‖Ps ξ t‖ ≤ 3 := by
    have hset : ∀ p ∈ S, P ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * P := by
      intro p hp
      have hprime := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1
      obtain ⟨hl, hu⟩ := pd7dPrimeDyad_bounds _ j p hp hprime.pos
      exact ⟨hl, hu.le⟩
    have hh := bandPrimePolynomial_norm_le P hP S (fun p => χ (p : ZMod k)) ξ t
      (fun _ _ => χ.norm_le_one _)
    exact hh.trans ((div_le_iff₀ hP).2 (by simpa [mul_comm] using
        (prime_band_card_le_three_mul P hPone S hset)))
  have hphase (ξ : ℝ) : ‖Complex.exp (-Complex.I * ξ * Real.log Y)‖ = 1 := by
    have heq : -Complex.I * (ξ : ℂ) * (Real.log Y : ℂ) =
        Complex.I * ((-ξ : ℝ) : ℂ) * (Real.log Y : ℂ) := by push_cast; ring
    rw [heq]
    exact pd7_complex_exp_phase_norm (-ξ) (Real.log Y)
  have hPsCont : Continuous (fun z : ℝ × ℝ => Ps z.1 z.2) := by
    change Continuous (fun z : ℝ × ℝ => bandPrimePolynomial P S (fun p => χ (p : ZMod k)) z.1 z.2)
    unfold bandPrimePolynomial
    fun_prop
  have hQCont : Continuous Q := by
    change Continuous (fun u : ℝ => pd7dTailPolynomial Rset tupleProduct W P Y (fun b => χ (b : ZMod k)) u)
    unfold pd7dTailPolynomial
    fun_prop
  have hphaseCont : Continuous (fun z : ℝ × ℝ => Complex.exp (-Complex.I * z.1 * Real.log Y)) := by fun_prop
  have hUcont : Continuous (Function.uncurry U) := by
    change Continuous (fun z : ℝ × ℝ => Complex.exp (-Complex.I * z.1 * Real.log Y) *
      Ps z.1 z.2 * Q (z.2 + z.1) * M z.2 * N z.2)
    exact (((hphaseCont.mul hPsCont).mul (hQCont.comp (continuous_snd.add continuous_fst))).mul
      (hM.comp continuous_snd)).mul (hN.comp continuous_snd)
  have hUb (ξ t : ℝ) : ‖U ξ t‖ ≤ 12 * Rm * Rn := by
    dsimp [U]
    simp only [norm_mul, hphase, one_mul]
    calc
      _ ≤ 3 * 4 * Rm * Rn := by
        gcongr
        · exact hPs ξ t
        · exact hQ (t + ξ)
        · exact hMb t
        · exact hNb t
      _ = _ := by ring
  have hUpoint (ξ t : ℝ) : ‖U ξ t‖ ^ 2 ≤ 16 * ‖Ps ξ t * M t * N t‖ ^ 2 := by
    have hEq : U ξ t = Complex.exp (-Complex.I * ξ * Real.log Y) * Q (t + ξ) *
        (Ps ξ t * M t * N t) := by dsimp [U]; ring
    rw [hEq, norm_mul, norm_mul, hphase, one_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right
      (by simpa only [show (4 : ℝ) ^ 2 = 16 by norm_num] using
        pow_le_pow_left₀ (norm_nonneg _) (hQ (t + ξ)) 2) (sq_nonneg _)
  have hUInt (ξ : ℝ) : (∫ t in (-T)..T, ‖U ξ t‖ ^ 2) ≤ 16 * E := by
    have hUξ : Continuous (fun t => U ξ t) := pd7d_continuous_first_section U hUcont ξ
    have hPsξ : Continuous (Ps ξ) := pd7d_continuous_first_section Ps hPsCont ξ
    calc
      _ ≤ ∫ t in (-T)..T, 16 * ‖Ps ξ t * M t * N t‖ ^ 2 :=
        intervalIntegral.integral_mono_on (by linarith)
          ((hUξ.norm.pow 2).intervalIntegrable _ _)
          ((((hPsξ.mul hM).mul hN).norm.pow 2).intervalIntegrable _ _ |>.const_mul 16)
          (fun t _ => hUpoint ξ t)
      _ = 16 * (∫ t in (-T)..T, ‖Ps ξ t * M t * N t‖ ^ 2) :=
        intervalIntegral.integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hIso ξ) (by norm_num)
  have hweighted := pd7d_mellin_energy_bound (pd7MajorCutoffTransform eta lam) U T
    (12 * Rm * Rn) (16 * E) (pd7d_cutoff_transform_integrable eta heta heta_supp lam)
    hUcont hT (by positivity) hUb hUInt
  have hfun (t : ℝ) : pd7dMajorDyadPolynomial x Y lam eta a j χ t * M t * N t =
      (((bandMass x (a 0))⁻¹ : ℝ) : ℂ) * ∫ ξ : ℝ, pd7MajorCutoffTransform eta lam ξ * U ξ t := by
    rw [pd7d_major_dyad_mellin x Y lam eta a j χ t heta heta_supp hY]
    calc
      _ = (((bandMass x (a 0))⁻¹ : ℝ) : ℂ) *
          ((∫ ξ : ℝ, pd7MajorCutoffTransform eta lam ξ *
            Complex.exp (-Complex.I * ξ * Real.log Y) * Ps ξ t * Q (t + ξ)) * M t * N t) := by ring
      _ = _ := by
        congr 1
        rw [← integral_mul_const, ← integral_mul_const]
        apply integral_congr_ae
        filter_upwards [] with ξ
        dsimp [U]
        ring
  have hnorm (t : ℝ) : ‖pd7dMajorDyadPolynomial x Y lam eta a j χ t * M t * N t‖ ^ 2 =
      ((bandMass x (a 0))⁻¹) ^ 2 * ‖∫ ξ : ℝ, pd7MajorCutoffTransform eta lam ξ * U ξ t‖ ^ 2 := by
    rw [hfun, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp_rw [hnorm]
  rw [intervalIntegral.integral_const_mul]
  calc
    _ ≤ ((bandMass x (a 0))⁻¹) ^ 2 *
        ((∫ ξ : ℝ, ‖pd7MajorCutoffTransform eta lam ξ‖) ^ 2 * (16 * E)) :=
      mul_le_mul_of_nonneg_left hweighted (sq_nonneg _)
    _ = _ := by ring

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
  intro A₀ B₁ A' hA₀ hB₁ hA' family hcancel
  cases K with
  | zero => have hK := ha.1; omega
  | succ n =>
    let Aiso := A' + 4 * A₀ + 4
    have hAiso : 0 < Aiso := by dsimp [Aiso]; positivity
    obtain ⟨Ciso, xiso, hCiso, hxiso, hxisoMin, hiso⟩ :=
      pd7d_isolated_prime_energy_eventually δ C c₁ c₂ A₀ B₁ Aiso
        hδ hC hc₁ hc₂ hA₀ hB₁ hAiso family hcancel
    obtain ⟨Cη, hCη, hcutoff⟩ := pd7_major_cutoff_transform_L1_bound eta heta heta_supp
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    let cd : ℝ := 2 / Real.log 2 + 1
    let Cd : ℝ := 16 * (2 / Real.log 2) ^ 2 * 81 * Cη ^ 2 * Ciso
    let C' : ℝ := cd ^ 2 * Cd
    have hCd : 0 < Cd := by dsimp [Cd]; positivity
    have hC' : 0 < C' := by dsimp [C', cd]; positivity
    have hbands : ∀ᶠ x : ℝ in atTop, ∀ i : Fin (n + 1),
        Real.log 2 / 2 ≤ bandMass x (a i) ∧ 0 < bandMass x (a i) := by
      apply Filter.eventually_all.2
      intro i
      have hai := ha.2.1 i
      obtain ⟨xb, hxb, hband⟩ := band_mass (a i) (by linarith) (by linarith)
        (Real.log 2 / 2) (by positivity)
      filter_upwards [eventually_ge_atTop xb] with x hx
      have hb := hband x hx
      exact ⟨by have hh := abs_le.mp hb.1; linarith, hb.2⟩
    have hlarge : ∀ᶠ x : ℝ in atTop,
        2 * Real.log 2 ≤ Real.rpow (Real.log x) (1 / 10 : ℝ) :=
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
        Real.tendsto_log_atTop).eventually_ge_atTop _
    have hevent : ∀ᶠ x : ℝ in atTop, xiso ≤ x ∧ 1 ≤ Real.log x ∧
        2 * Real.log 2 ≤ Real.rpow (Real.log x) (1 / 10 : ℝ) ∧
        ∀ i : Fin (n + 1), Real.log 2 / 2 ≤ bandMass x (a i) ∧ 0 < bandMass x (a i) := by
      filter_upwards [eventually_ge_atTop xiso,
        Real.tendsto_log_atTop.eventually_ge_atTop 1, hlarge, hbands] with x hx hL hlarge hbands
      exact ⟨hx, hL, hlarge, hbands⟩
    obtain ⟨xbase, hxbase⟩ := eventually_atTop.1 hevent
    let x₀ := max 2 xbase
    refine ⟨C', x₀, hC', le_max_left _ _, ?_⟩
    intro x hx beta hbetaSupport hbetaBound Y hY k hk hkle χb χm χn lam hlam
    obtain ⟨hxiso', hL, hlarge', hbands'⟩ := hxbase x ((le_max_right _ _).trans hx)
    have hxmin : family.xMin ≤ x := hxisoMin.trans hxiso'
    have hxpos : 0 < x := by linarith [family.xMin_ge_two]
    let L := Real.log x
    let X := family.Hm x * family.Hn x
    let T := 2 * X * Real.rpow L B₁
    let Dset := pd7dPrimeDyads (primeBand x (a 0))
    let M := majorMPolynomial family x χm
    let N := majorNPolynomial (family.Hn x) beta χn
    have hLpos : 0 < L := by dsimp [L]; linarith
    obtain ⟨hHmlo, hHnlo, hXlo, hXhi⟩ := family.scales x hxmin
    have hHm : 0 < family.Hm x := (Real.rpow_pos_of_pos hxpos δ).trans_le hHmlo
    have hHn : 0 < family.Hn x := (Real.rpow_pos_of_pos hxpos δ).trans_le hHnlo
    have hpowIso : 0 < Real.rpow L (-Aiso) := Real.rpow_pos_of_pos hLpos _
    have hpowEnergy : 0 < Real.rpow L (4 * A₀ - Aiso) := Real.rpow_pos_of_pos hLpos _
    have hpowFour : 0 < Real.rpow L (4 * A₀) := Real.rpow_pos_of_pos hLpos _
    have hT : 0 ≤ T := by dsimp [T, X]; positivity
    have hYpos : 0 < Y := by
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hY).1
      positivity
    have hM : Continuous M := by
      change Continuous (fun t : ℝ => majorMPolynomial family x χm t)
      unfold majorMPolynomial alphaFrequency
      fun_prop
    have hN : Continuous N := by
      change Continuous (fun t : ℝ => majorNPolynomial (family.Hn x) beta χn t)
      unfold majorNPolynomial betaFrequency
      fun_prop
    let Rm := (∑ m ∈ familyTerms family x, ‖family.alpha x m * χm (m : ZMod k)‖) / family.Hm x
    let Rn := (∑ m ∈ dyadicIntegers (family.Hn x), ‖beta m * χn (m : ZMod k)‖) / family.Hn x
    have hRm : 0 ≤ Rm := by dsimp [Rm]; positivity
    have hRn : 0 ≤ Rn := by dsimp [Rn]; positivity
    have hMb (t : ℝ) : ‖M t‖ ≤ Rm :=
      pd7d_normalized_polynomial_norm_le (family.Hm x) (familyTerms family x)
        (fun m => family.alpha x m * χm (m : ZMod k)) t hHm
    have hNb (t : ℝ) : ‖N t‖ ≤ Rn :=
      pd7d_normalized_polynomial_norm_le (family.Hn x) (dyadicIntegers (family.Hn x))
        (fun m => beta m * χn (m : ZMod k)) t hHn
    have hMassInv : (bandMass x (a 0))⁻¹ ≤ 2 / Real.log 2 := by
      calc
        _ ≤ 1 / (Real.log 2 / 2) := by
          simpa only [one_div] using one_div_le_one_div_of_le (by positivity : 0 < Real.log 2 / 2)
            (hbands' 0).1
        _ = _ := by field_simp
    have hMassSq : ((bandMass x (a 0))⁻¹) ^ 2 ≤ (2 / Real.log 2) ^ 2 :=
      pow_le_pow_left₀ (inv_nonneg.mpr (hbands' 0).2.le) hMassInv 2
    have hcut : (∫ ξ : ℝ, ‖pd7MajorCutoffTransform eta lam ξ‖) ≤
        9 * Cη * Real.rpow L (2 * A₀) := by
      have hpowOne : 1 ≤ Real.rpow L A₀ := Real.one_le_rpow hL hA₀.le
      have hbase : 1 + |lam| ≤ 3 * Real.rpow L A₀ := by linarith
      calc
        _ ≤ Cη * (1 + |lam|) ^ 2 := hcutoff lam
        _ ≤ Cη * (3 * Real.rpow L A₀) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase 2) hCη.le
        _ = _ := by rw [mul_pow, pd7d_rpow_sq L A₀ hLpos.le]; ring
    have hcutSq : (∫ ξ : ℝ, ‖pd7MajorCutoffTransform eta lam ξ‖) ^ 2 ≤
        81 * Cη ^ 2 * Real.rpow L (4 * A₀) := by
      have hh := pow_le_pow_left₀ (integral_nonneg (fun _ => norm_nonneg _)) hcut 2
      rw [mul_pow, mul_pow, pd7d_rpow_sq L (2 * A₀) hLpos.le] at hh
      convert hh using 1 <;> ring
    have hdyad (j : ℕ) (hj : j ∈ Dset) :
        (∫ t in (-T)..T, ‖pd7dMajorDyadPolynomial x Y lam eta a j χb t * M t * N t‖ ^ 2) ≤
          Cd * Real.rpow L (4 * A₀ - Aiso) := by
      obtain ⟨hPlo, hPhi⟩ := pd7d_prime_band_dyad_sparse_range x (a 0) j hL
        (ha.2.1 0).1.le (ha.2.1 0).2.le hlarge' hj
      have hIso (ξ : ℝ) :
          (∫ t in (-T)..T, ‖bandPrimePolynomial ((2 : ℝ) ^ j)
            (pd7dPrimeDyad (primeBand x (a 0)) j) (fun p => χb (p : ZMod k)) ξ t * M t * N t‖ ^ 2) ≤
          Ciso * Real.rpow L (-Aiso) := by
        have hPset : ∀ p ∈ pd7dPrimeDyad (primeBand x (a 0)) j,
            p.Prime ∧ (2 : ℝ) ^ j ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * (2 : ℝ) ^ j := by
          intro p hp
          have hprime := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1
          obtain ⟨hlo, hhi⟩ := pd7dPrimeDyad_bounds _ j p hp hprime.pos
          exact ⟨hprime, hlo, hhi.le⟩
        exact hiso x hxiso' ((2 : ℝ) ^ j) (one_le_pow₀ (by norm_num)) hPlo hPhi _ hPset beta hbetaBound k hk hkle χb χm χn ξ
      have hh := pd7d_major_dyad_energy_bound x Y lam eta a j χb M N T Rm Rn
        (Ciso * Real.rpow L (-Aiso)) heta heta_supp hYpos
        (fun i => (hbands' i.succ).2) hT hM hN hRm hRn hMb hNb hIso
      calc
        _ ≤ 16 * ((bandMass x (a 0))⁻¹) ^ 2 *
            (∫ ξ : ℝ, ‖pd7MajorCutoffTransform eta lam ξ‖) ^ 2 * (Ciso * Real.rpow L (-Aiso)) := hh
        _ ≤ 16 * (2 / Real.log 2) ^ 2 * (81 * Cη ^ 2 * Real.rpow L (4 * A₀)) *
            (Ciso * Real.rpow L (-Aiso)) := by gcongr
        _ = _ := by
          rw [show 4 * A₀ - Aiso = 4 * A₀ + (-Aiso) by ring, pd7d_rpow_add hLpos]
          dsimp [Cd]
          ring
    have hDcard : (Dset.card : ℝ) ≤ cd * L := pd7d_prime_band_dyads_card x (a 0) hL (by linarith [(ha.2.1 0).2])
    have hDsq : (Dset.card : ℝ) ^ 2 ≤ cd ^ 2 * L ^ 2 := by
      have hh := pow_le_pow_left₀ (by positivity : 0 ≤ (Dset.card : ℝ)) hDcard 2
      simpa [mul_pow] using hh
    have hFcont (j : ℕ) (hj : j ∈ Dset) :
        Continuous (fun t => pd7dMajorDyadPolynomial x Y lam eta a j χb t * M t * N t) := by
      dsimp [pd7dMajorDyadPolynomial]
      fun_prop
    have hsum := pd7d_finite_sum_energy_bound Dset
      (fun j t => pd7dMajorDyadPolynomial x Y lam eta a j χb t * M t * N t) T hT hFcont
    have hsumLe : (∑ j ∈ Dset, ∫ t in (-T)..T,
        ‖pd7dMajorDyadPolynomial x Y lam eta a j χb t * M t * N t‖ ^ 2) ≤
        (Dset.card : ℝ) * (Cd * Real.rpow L (4 * A₀ - Aiso)) := by
      simpa using Finset.sum_le_sum hdyad
    unfold majorEnergy majorEnergyIntegral
    simp_rw [pd7d_majorB_sum_dyads, Finset.sum_mul]
    calc
      _ ≤ (Dset.card : ℝ) * (∑ j ∈ Dset, ∫ t in (-T)..T,
          ‖pd7dMajorDyadPolynomial x Y lam eta a j χb t * M t * N t‖ ^ 2) := hsum
      _ ≤ (Dset.card : ℝ) ^ 2 * (Cd * Real.rpow L (4 * A₀ - Aiso)) := by
        have hh := mul_le_mul_of_nonneg_left hsumLe (by positivity : 0 ≤ (Dset.card : ℝ))
        convert hh using 1 <;> ring
      _ ≤ (cd ^ 2 * L ^ 2) * (Cd * Real.rpow L (4 * A₀ - Aiso)) :=
        mul_le_mul_of_nonneg_right hDsq (by positivity)
      _ = C' * Real.rpow L (2 + (4 * A₀ - Aiso)) := by
        rw [← pd7d_rpow_natCast L 2, pd7d_rpow_add hLpos]
        dsimp [C']
        ring
      _ ≤ C' * Real.rpow L (-A') := by
        apply mul_le_mul_of_nonneg_left _ hC'.le
        apply Real.rpow_le_rpow_of_exponent_le hL
        dsimp [Aiso]
        linarith

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
  intro A₀ hA₀ family hcancel eta psi heta heta_supp heta_nonneg heta_part
    hpsi hpsi_supp hpsi_one
  obtain ⟨B₁, A', hB₁, hA', hsep⟩ :=
    major_separation δ C c₁ c₂ K a hδ hC hc₁ hc₂ ha
      eta psi heta heta_supp heta_nonneg heta_part hpsi hpsi_supp hpsi_one
      A₀ Dstar hA₀ hD
  obtain ⟨Csep, xsep, hCsep, hxsep, hsepFamily⟩ := hsep family
  obtain ⟨Cen, xen, hCen, hxen, henergyFamily⟩ :=
    major_energy δ C c₁ c₂ K a hδ hC hc₁ hc₂ ha eta heta heta_supp heta_nonneg
      A₀ B₁ (A' + 1) hA₀ hB₁ (by linarith) family hcancel
  let x₀ := max xsep (max xen (max 3 (Real.exp Cen)))
  refine ⟨Csep, x₀, hCsep, ?_, ?_⟩
  · dsimp [x₀]
    exact le_trans hxsep (le_max_left _ _)
  · intro x hx Y hY beta hbetaSupport hbetaBound
    have hxsep' : xsep ≤ x := (le_max_left _ _).trans hx
    have hxsub : max xen (max 3 (Real.exp Cen)) ≤ x :=
      (le_max_right _ _).trans hx
    have hxen' : xen ≤ x := (le_max_left _ _).trans hxsub
    have hxsub' : max 3 (Real.exp Cen) ≤ x := (le_max_right _ _).trans hxsub
    have hxthree : 3 ≤ x := (le_max_left _ _).trans hxsub'
    have hexp : Real.exp Cen ≤ x := (le_max_right _ _).trans hxsub'
    have hLpos : 0 < Real.log x := Real.log_pos (by linarith)
    have hLbound : Cen ≤ Real.log x := by
      calc
        Cen = Real.log (Real.exp Cen) := by rw [Real.log_exp]
        _ ≤ Real.log x := Real.log_le_log (Real.exp_pos _) hexp
    have henergySmall : ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.rpow (Real.log x) A₀ →
        ∀ χb χm χn : DirichletCharacter ℂ k, ∀ lam : ℝ,
          |lam| ≤ 2 * Real.rpow (Real.log x) A₀ →
            majorEnergy x K a Y lam B₁ eta family beta χb χm χn ≤
              Real.rpow (Real.log x) (-A') := by
      intro k hk hkle χb χm χn lam hlam
      have hE := henergyFamily x hxen' beta hbetaSupport hbetaBound Y hY
        k hk hkle χb χm χn lam hlam
      have hpowInv : Real.rpow (Real.log x) (-1 : ℝ) =
          (Real.log x)⁻¹ := by
        calc
          _ = (Real.rpow (Real.log x) (1 : ℝ))⁻¹ :=
            Real.rpow_neg hLpos.le 1
          _ = _ := congrArg Inv.inv (Real.rpow_one (Real.log x))
      have hpowrel : Real.rpow (Real.log x) (-(A' + 1)) =
          Real.rpow (Real.log x) (-A') / Real.log x := by
        calc
          _ = Real.rpow (Real.log x) ((-A') + (-1)) := by congr 1 <;> ring
          _ = Real.rpow (Real.log x) (-A') *
              Real.rpow (Real.log x) (-1) := Real.rpow_add hLpos _ _
          _ = _ := by rw [hpowInv, div_eq_mul_inv]
      have hratio : Cen / Real.log x ≤ 1 := by
        apply (div_le_iff₀ hLpos).2
        simpa using hLbound
      have hpowerNonneg : 0 ≤ Real.rpow (Real.log x) (-A') :=
        Real.rpow_nonneg hLpos.le _
      calc
        _ ≤ Cen * Real.rpow (Real.log x) (-(A' + 1)) := hE
        _ = (Cen / Real.log x) * Real.rpow (Real.log x) (-A') := by
          rw [hpowrel]
          ring
        _ ≤ Real.rpow (Real.log x) (-A') := by
          simpa using mul_le_mul_of_nonneg_right hratio hpowerNonneg
    exact hsepFamily x hxsep' beta hbetaSupport hbetaBound Y hY henergySmall

private def pd7_liftFamilyUpper {δ C c₁ c₂ : ℝ}
    (family : CoefficientFamily δ C c₁ c₂) :
    CoefficientFamily δ C c₁ (max c₁ c₂) where
  xMin := family.xMin
  xMin_ge_two := family.xMin_ge_two
  Hm := family.Hm
  Hn := family.Hn
  interval := family.interval
  alpha := family.alpha
  interval_property := family.interval_property
  scales := by
    intro x hx
    rcases family.scales x hx with ⟨hm, hn, hlo, hhi⟩
    have hxnonneg : 0 ≤ x := by
      have hx2 : 2 ≤ x := family.xMin_ge_two.trans hx
      linarith
    exact ⟨hm, hn, hlo,
      le_trans hhi (mul_le_mul_of_nonneg_right (le_max_right c₁ c₂) hxnonneg)⟩
  interval_bounds := family.interval_bounds
  rough_support := family.rough_support
  coefficient_bound := family.coefficient_bound

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
  let eta : ℝ → ℝ := pd7_cauchyEta
  let psi : ℝ → ℝ := pd7_arcPsi
  rcases pd7_cauchyEta_isCauchyCutoff with
    ⟨heta, heta_supp, heta_nonneg, heta_part⟩
  rcases pd7_arcPsi_isCutoff with ⟨hpsi, hpsi_supp, hpsi_one⟩
  let Aerr : ℝ := 2 * Dstar + 2
  have hAerr : 0 < Aerr := by dsimp [Aerr]; linarith
  let c₂' : ℝ := max c₁ c₂
  have hc₁₂' : c₁ ≤ c₂' := le_max_left _ _
  obtain ⟨A₀, hA₀, K₀, hminorAll⟩ :=
    minor_replacement δ C c₁ c₂' hδ hC hc₁ hc₁₂' q_d eta psi Aerr hAerr
  refine ⟨K₀, ?_⟩
  intro K hKK a ha family hcancel
  let familyLift := pd7_liftFamilyUpper family
  let fixed : PDFix K := ⟨a, q_d, A₀, eta, psi⟩
  have hfixedValid : fixed.Valid := by
    exact ⟨ha, hqd₀, hqd₁, hA₀,
      pd7_cauchyEta_isCauchyCutoff, pd7_arcPsi_isCutoff⟩
  have hfixedHas : fixed.Has q_d A₀ eta psi := ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨Cminor, xminor, hCminor, hxmin, hminor⟩ :=
    hminorAll K hKK fixed hfixedValid hfixedHas familyLift
  obtain ⟨Cmajor, xmajor, hCmajor, hxmajor, hmajor⟩ :=
    major_term δ C Aerr q_d c₁ c₂ K a hδ hC hAerr hqd₀ hqd₁ hc₁ hc₂ ha
      A₀ hA₀ family hcancel eta psi heta heta_supp heta_nonneg heta_part
      hpsi hpsi_supp hpsi_one
  obtain ⟨CA, Cscale, Cmain, CDiv, xC, hCA, hCscale, hCmain, hCDiv, hxC, hdecomp⟩ :=
    cauchy_decomposition δ C Dstar q_d c₁ c₂ K a hδ hC hD hqd₀ hqd₁ hc₁ hc₂ ha
      Aerr hAerr
  let xA : ℝ := max xminor xC
  let xB : ℝ := max xA xmajor
  let xInner : ℝ := max family.xMin xB
  let x₀ : ℝ := max 3 xInner
  let E : ℝ := Cminor + Cmajor
  let Cpiece : ℝ := Real.sqrt (Cmain * E)
  let C' : ℝ := CA + Cscale * Cpiece + 1
  have hE : 0 < E := by dsimp [E]; positivity
  have hCpiece : 0 ≤ Cpiece := by dsimp [Cpiece]; positivity
  have hC' : 0 < C' := by dsimp [C']; positivity
  refine ⟨C', x₀, hC', ?_, ?_⟩
  · have h3 : 3 ≤ x₀ := by dsimp [x₀]; exact le_max_left _ _
    exact le_trans (by norm_num : (2 : ℝ) ≤ 3) h3
  · intro x hx beta hbetaSupport hbetaBound F hFmarked
    have hx0' : max 3 xInner ≤ x := by simpa [x₀] using hx
    have hx3 : 3 ≤ x := (le_max_left 3 xInner).trans hx0'
    have hxinner : xInner ≤ x := (le_max_right 3 xInner).trans hx0'
    have hxmin' : family.xMin ≤ x :=
      (le_max_left family.xMin xB).trans hxinner
    have hxB : xB ≤ x := (le_max_right family.xMin xB).trans hxinner
    have hxA : xA ≤ x := (le_max_left xA xmajor).trans hxB
    have hxminor' : xminor ≤ x := (le_max_left xminor xC).trans hxA
    have hxC' : xC ≤ x := (le_max_right xminor xC).trans hxA
    have hxmajor' : xmajor ≤ x := (le_max_right xA xmajor).trans hxB
    have hxpos : 0 < x := by linarith
    have hLge : 1 ≤ Real.log x := by
      have hxExp : Real.exp 1 ≤ x :=
        Real.exp_one_lt_three.le.trans hx3
      calc
        1 = Real.log (Real.exp 1) := by simp
        _ ≤ Real.log x := Real.log_le_log (Real.exp_pos _) hxExp
    have hLpos : 0 < Real.log x := lt_of_lt_of_le zero_lt_one hLge
    let L : ℝ := Real.log x
    let X : ℝ := family.Hm x * family.Hn x
    have hfamilyScales := family.scales x hxmin'
    rcases hfamilyScales with ⟨_, _, hXlower, _⟩
    have hXpos : 0 < X := by
      have hcx : 0 < c₁ * x := mul_pos hc₁ hxpos
      exact lt_of_lt_of_le hcx hXlower
    have hdecompAt := hdecomp family hcancel x hxC' hxmin' eta heta heta_supp
      heta_nonneg heta_part beta hbetaSupport hbetaBound F hFmarked
    rcases hdecompAt with ⟨happrox, hpieces, _, _, hscaleCard, _⟩
    let pieces : ℂ := ∑ Y ∈ dyadicScales x K,
      dyadicCauchyPiece x K a q_d Y family beta F eta
    have hsecond : IsFamilySecondCoefficient familyLift x beta :=
      ⟨hbetaSupport, hbetaBound⟩
    let Q (Y : ℝ) : ℝ := cauchySquare x K a Y family beta eta
    let M (Y : ℝ) : ℂ := majorArcSum x K a Y A₀ family beta eta psi
    have hEpos : 0 < E := hE
    have hpowOrder : Real.rpow L (-Aerr) ≤ Real.rpow L (-Dstar) := by
      apply Real.rpow_le_rpow_of_exponent_le hLge
      dsimp [Aerr]
      linarith
    have happrox' : ‖coefficientBilinearSum x K a q_d family beta F - pieces‖ ≤
        CA * X * Real.rpow L (-Aerr) := by
      simpa [pieces, L, X] using happrox
    have hsumPieces :
        ‖pieces‖ ≤ Cscale * Cpiece * X * Real.rpow L (-Dstar) := by
      have hfactorNonneg : 0 ≤ Cpiece * X * Real.rpow L (-(Dstar + 1)) := by
        dsimp [Cpiece]
        positivity
      have hpowSq :
          (Real.rpow L (-(Dstar + 1))) ^ 2 = Real.rpow L (-Aerr) := by
        calc
          _ = Real.rpow (Real.rpow L (-(Dstar + 1))) (2 : ℝ) :=
            (Real.rpow_natCast (Real.rpow L (-(Dstar + 1))) 2).symm
          _ = Real.rpow L ((-(Dstar + 1)) * 2) :=
            (Real.rpow_mul (le_of_lt hLpos) (-(Dstar + 1)) 2).symm
          _ = _ := by
            congr 1
            dsimp [Aerr]
            ring
      have hCpieceSq : Cpiece ^ 2 = Cmain * E := by
        dsimp [Cpiece]
        exact Real.sq_sqrt (le_of_lt (mul_pos hCmain hEpos))
      have hpieceBound : ∀ Y ∈ dyadicScales x K,
          ‖dyadicCauchyPiece x K a q_d Y family beta F eta‖ ≤
            Cpiece * X * Real.rpow L (-(Dstar + 1)) := by
        intro Y hY
        rcases hpieces Y hY with ⟨hQnonneg, hpieceSq, _⟩
        have hYpos : 0 < Y := by
          have hYimage := (Finset.mem_filter.mp hY).1
          dsimp [dyadicScales] at hYimage
          rcases Finset.mem_image.mp hYimage with ⟨k, _, rfl⟩
          positivity
        have hminorAt :
            ‖(Q Y : ℂ) - M Y‖ ≤ Cminor * X * Y * Real.rpow L (-Aerr) := by
          have h := hminor x hxminor' beta hsecond Y hY
          simpa [Q, M, L, X, familyLift, pd7_liftFamilyUpper, cauchySquare,
            majorArcSum, familyTerms] using h
        have hmajorAt : ‖M Y‖ ≤ Cmajor * X * Y * Real.rpow L (-Aerr) := by
          simpa [M, L, X, Aerr] using
            hmajor x hxmajor' Y hY beta hbetaSupport hbetaBound
        have hQle : Q Y ≤ E * X * Y * Real.rpow L (-Aerr) := by
          calc
            Q Y = ‖(Q Y : ℂ)‖ := by
              calc
                Q Y = |Q Y| := (abs_of_nonneg hQnonneg).symm
                _ = ‖(Q Y : ℂ)‖ := by
                  rw [Complex.norm_real, Real.norm_eq_abs]
            _ = ‖((Q Y : ℂ) - M Y) + M Y‖ := by congr 1 <;> abel
            _ ≤ ‖(Q Y : ℂ) - M Y‖ + ‖M Y‖ := norm_add_le _ _
            _ ≤ Cminor * X * Y * Real.rpow L (-Aerr) +
                  Cmajor * X * Y * Real.rpow L (-Aerr) := add_le_add hminorAt hmajorAt
            _ = E * X * Y * Real.rpow L (-Aerr) := by dsimp [E]; ring
        have hmulNonneg : 0 ≤ Cmain * (X / Y) :=
          mul_nonneg hCmain.le (div_nonneg hXpos.le hYpos.le)
        have hsq :
            ‖dyadicCauchyPiece x K a q_d Y family beta F eta‖ ^ 2 ≤
              (Cpiece * X * Real.rpow L (-(Dstar + 1))) ^ 2 := by
          calc
            _ ≤ Cmain * (X / Y) * Q Y := hpieceSq
            _ ≤ Cmain * (X / Y) * (E * X * Y * Real.rpow L (-Aerr)) :=
              mul_le_mul_of_nonneg_left hQle hmulNonneg
            _ = (Cpiece * X * Real.rpow L (-(Dstar + 1))) ^ 2 := by
              calc
                _ = Cmain * E * X ^ 2 * Real.rpow L (-Aerr) := by
                  field_simp [ne_of_gt hYpos]
                _ = _ := by rw [← hCpieceSq, ← hpowSq]; ring
        exact (sq_le_sq₀ (norm_nonneg _) hfactorNonneg).mp hsq
      calc
        ‖pieces‖ ≤
            ∑ Y ∈ dyadicScales x K,
              ‖dyadicCauchyPiece x K a q_d Y family beta F eta‖ := norm_sum_le _ _
        _ ≤ ∑ Y ∈ dyadicScales x K,
              Cpiece * X * Real.rpow L (-(Dstar + 1)) :=
          Finset.sum_le_sum fun Y hY => hpieceBound Y hY
        _ = (dyadicScales x K).card *
              (Cpiece * X * Real.rpow L (-(Dstar + 1))) := by simp
        _ ≤ (Cscale * L) * (Cpiece * X * Real.rpow L (-(Dstar + 1))) :=
          mul_le_mul_of_nonneg_right (by simpa [L] using hscaleCard) hfactorNonneg
        _ = Cscale * Cpiece * X * Real.rpow L (-Dstar) := by
          have hpowRel : L * Real.rpow L (-(Dstar + 1)) = Real.rpow L (-Dstar) := by
            have hLone : Real.rpow L (1 : ℝ) = L := Real.rpow_one L
            calc
              _ = Real.rpow L 1 * Real.rpow L (-(Dstar + 1)) := by
                exact congrArg (fun z : ℝ => z * Real.rpow L (-(Dstar + 1))) hLone.symm
              _ = Real.rpow L (1 + (-(Dstar + 1))) :=
                (Real.rpow_add hLpos _ _).symm
              _ = _ := by congr 1 <;> ring
          rw [← hpowRel]
          ring
    have hSigmaBound :
        ‖coefficientBilinearSum x K a q_d family beta F‖ ≤
          CA * X * Real.rpow L (-Aerr) + Cscale * Cpiece * X * Real.rpow L (-Dstar) := by
      calc
        _ = ‖(coefficientBilinearSum x K a q_d family beta F - pieces) + pieces‖ := by
          congr 1
          abel
        _ ≤ ‖coefficientBilinearSum x K a q_d family beta F - pieces‖ + ‖pieces‖ :=
          norm_add_le _ _
        _ ≤ CA * X * Real.rpow L (-Aerr) + Cscale * Cpiece * X * Real.rpow L (-Dstar) :=
          add_le_add happrox' hsumPieces
    have hsumAbsorb :
        CA * X * Real.rpow L (-Aerr) + Cscale * Cpiece * X * Real.rpow L (-Dstar) ≤
          C' * X * Real.rpow L (-Dstar) := by
      calc
        _ ≤ CA * X * Real.rpow L (-Dstar) +
              Cscale * Cpiece * X * Real.rpow L (-Dstar) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hpowOrder (mul_nonneg hCA.le hXpos.le)) le_rfl
        _ = (CA + Cscale * Cpiece) * (X * Real.rpow L (-Dstar)) := by ring
        _ ≤ C' * (X * Real.rpow L (-Dstar)) := by
          apply mul_le_mul_of_nonneg_right
            (show CA + Cscale * Cpiece ≤ C' by dsimp [C']; linarith)
            (mul_nonneg hXpos.le (Real.rpow_nonneg hLpos.le _))
        _ = C' * X * Real.rpow L (-Dstar) := by ring
    simpa [coefficientBilinearSum, X, L] using hSigmaBound.trans hsumAbsorb

end

end ArtinPrimitiveRoots.TypeII.PD
