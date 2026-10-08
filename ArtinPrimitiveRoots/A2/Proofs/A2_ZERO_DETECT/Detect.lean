import ArtinPrimitiveRoots.A2.ZeroFree.Results
import ArtinPrimitiveRoots.A2.FSide
import ArtinPrimitiveRoots.A1.Coeff.IdealSummable
import ArtinPrimitiveRoots.A2.Proofs.A2_ZERO_DETECT.MaxBound

/-!
# A2-ZERO-DETECT: the detector count

The smoothed detector sum of a nonprincipal character with a zero at `β + iγ` splits into the
unit term `exp (-U⁻¹⁰)`, the finite middle range `U² < N I ≤ U¹¹` and an exponentially small tail.
The middle range is cut into dyads `2^j ≤ N I < 2^(j+1)`; on each dyad the detector is a finite
Dirichlet polynomial in `(β - 0.996, γ)` and `dirichlet_poly_max_bound` together with the conductor
sieve bounds the family sum of its squares. Finite Chebyshev then counts the detecting characters.

The ideal count, divisor bound and detector shift enter as hypotheses: they are proved in
`ZeroFree/Nodes.lean`, which imports this file.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A2.Proofs.A2ZeroDetect

open ArtinPrimitiveRoots.A2

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Integral ideals of norm at most `⌊t⌋`, as indexed by the conductor sieve. -/
abbrev idealsUpTo (t : ℝ) : Finset (Ideal (𝓞 F)) :=
  (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊t⌋₊).toFinset

/-- One term of the smoothed detector sum `detectorSmoothedSum`. -/
def smoothedTerm (U β γ : ℝ) (ω : ArtinPrimitiveRoots.A1.HeckeChar F) (I : Ideal (𝓞 F)) : ℂ :=
  (detectorCoeff U I : ℂ) * ω.idealValue I *
    ((Ideal.absNorm I : ℕ) : ℂ) ^ (-(β + γ * Complex.I)) *
    Complex.exp (-((Ideal.absNorm I : ℕ) : ℂ) / (U : ℂ) ^ 10)

/-- The finite middle range `U² < N I ≤ U¹¹`. -/
def midIdeals (U : ℝ) : Finset (Ideal (𝓞 F)) :=
  (idealsUpTo (F := F) (U ^ 11)).filter fun I => U ^ 2 < (Ideal.absNorm I : ℝ)

/-- Number of binary norm dyads covering the middle range. -/
def dyadCount (U : ℝ) : ℕ := Nat.log 2 ⌊U ^ 11⌋₊ + 1

/-- The middle-range ideals with `2^j ≤ N I < 2^(j+1)`. -/
def dyadIdeals (U : ℝ) (j : ℕ) : Finset (Ideal (𝓞 F)) :=
  (midIdeals (F := F) U).filter fun I => Nat.log 2 (Ideal.absNorm I) = j

private theorem norm_multiset_map_prod_le_one {α : Type*} (s : Multiset α) (f : α → ℂ)
    (hf : ∀ x, x ∈ s → ‖f x‖ ≤ 1) : ‖(s.map f).prod‖ ≤ 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, norm_mul]
    have h1 := hf a (by simp)
    have h2 := ih fun x hx => hf x (Multiset.mem_cons_of_mem hx)
    calc ‖f a‖ * ‖(s.map f).prod‖ ≤ 1 * 1 := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

/-- Finite-order Hecke characters take ideal values of norm at most one. -/
theorem idealValue_norm_le_one_of_finOrder (ω : ArtinPrimitiveRoots.A1.HeckeChar F)
    (hω : IsOfFinOrder ω) (I : Ideal (𝓞 F)) : ‖ω.idealValue I‖ ≤ 1 := by
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hω
  have hval : ∀ x, ‖((ω x : ℂˣ) : ℂ)‖ = 1 := by
    intro x
    have h1 : (ω x) ^ n = 1 := by
      have := congrArg (fun φ : ArtinPrimitiveRoots.A1.HeckeChar F => φ x) hpow
      simpa using this
    have h2 : ((ω x : ℂˣ) : ℂ) ^ n = 1 := by
      have := congrArg (fun z : ℂˣ => (z : ℂ)) h1
      simpa using this
    exact Complex.norm_eq_one_of_pow_eq_one h2 (by omega)
  unfold ArtinPrimitiveRoots.A1.HeckeChar.idealValue
  apply norm_multiset_map_prod_le_one
  intro P _
  by_cases h : P.IsPrime ∧ P ≠ ⊥
  · rw [dif_pos h]
    unfold ArtinPrimitiveRoots.A1.HeckeChar.primeValue
    split_ifs
    · exact le_of_eq (by simpa [ArtinPrimitiveRoots.A1.HeckeChar.loc] using hval _)
    · simp
  · rw [dif_neg h]
    simp

theorem idealValue_top (ω : ArtinPrimitiveRoots.A1.HeckeChar F) :
    ω.idealValue (⊤ : Ideal (𝓞 F)) = 1 := by
  rw [show (⊤ : Ideal (𝓞 F)) = 1 by simp,
    ArtinPrimitiveRoots.A1.HeckeChar.idealValue,
    UniqueFactorizationMonoid.normalizedFactors_of_isUnit isUnit_one]
  rfl

theorem mem_dyadIdeals {U : ℝ} (hU : 0 ≤ U) {j : ℕ} {I : Ideal (𝓞 F)}
    (hI : I ∈ dyadIdeals U j) :
    U ^ 2 < (Ideal.absNorm I : ℝ) ∧ (Ideal.absNorm I : ℝ) ≤ U ^ 11 ∧
      (2 : ℝ) ^ j ≤ Ideal.absNorm I ∧ (Ideal.absNorm I : ℝ) < 2 ^ (j + 1) := by
  simp only [dyadIdeals, midIdeals, Finset.mem_filter, Set.Finite.mem_toFinset,
    Set.mem_ofPred_eq] at hI
  obtain ⟨⟨hle, hlt⟩, hj⟩ := hI
  have hle' : (Ideal.absNorm I : ℝ) ≤ U ^ 11 :=
    (Nat.le_floor_iff (by positivity)).mp hle
  have hne : Ideal.absNorm I ≠ 0 := by
    intro h
    rw [h] at hlt
    simp at hlt
    nlinarith [sq_nonneg U]
  refine ⟨hlt, hle', ?_, ?_⟩
  · have := Nat.pow_log_le_self 2 hne
    rw [hj] at this
    exact_mod_cast this
  · have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (Ideal.absNorm I)
    rw [hj] at this
    exact_mod_cast this

/-- Cauchy–Schwarz over the binary dyads of the middle range. -/
theorem dyadic_split (U : ℝ) (g : Ideal (𝓞 F) → ℂ) :
    ‖∑ I ∈ midIdeals U, g I‖ ^ 2 ≤
      (dyadCount U : ℝ) * ∑ j ∈ Finset.range (dyadCount U), ‖∑ I ∈ dyadIdeals U j, g I‖ ^ 2 := by
  have hmaps : ∀ I ∈ midIdeals (F := F) U,
      Nat.log 2 (Ideal.absNorm I) ∈ Finset.range (dyadCount U) := by
    intro I hI
    simp only [midIdeals, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hI
    rw [Finset.mem_range, dyadCount]
    exact Nat.lt_succ_of_le (Nat.log_mono_right hI.1)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc ‖∑ j ∈ Finset.range (dyadCount U), ∑ I ∈ midIdeals U with Nat.log 2 (Ideal.absNorm I) = j,
        g I‖ ^ 2
      ≤ (∑ j ∈ Finset.range (dyadCount U), ‖∑ I ∈ dyadIdeals U j, g I‖) ^ 2 := by
        gcongr
        exact norm_sum_le _ _
    _ ≤ ((Finset.range (dyadCount U)).card : ℝ) *
          ∑ j ∈ Finset.range (dyadCount U), ‖∑ I ∈ dyadIdeals U j, g I‖ ^ 2 :=
        sq_sum_le_card_mul_sum_sq
    _ = _ := by rw [Finset.card_range]

/-- Logarithmic factors are absorbed by any positive power. -/
theorem log_factors_absorb (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ, 2 ≤ U →
      (dyadCount U : ℝ) ^ 2 * (1 + (12 * Real.log U) ^ 2) ^ 2 ≤ C * Real.rpow U a := by
  refine ⟨18 ^ 2 * 147 ^ 2 * (6 / a) ^ 6, by positivity, ?_⟩
  intro U hU
  have hU0 : 0 < U := by linarith
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlogU : Real.log 2 ≤ Real.log U := Real.log_le_log (by norm_num) hU
  have hl0 : 0 < Real.log U := by linarith
  -- dyad count
  have hJ : (dyadCount U : ℝ) ≤ 18 * Real.log U := by
    have hn : (⌊U ^ 11⌋₊ : ℝ) ≤ U ^ 11 := Nat.floor_le (by positivity)
    have hn1 : 1 ≤ ⌊U ^ 11⌋₊ := by
      apply Nat.le_floor
      have : (1 : ℝ) ≤ U ^ 11 := one_le_pow₀ (by linarith)
      exact_mod_cast this
    have hpow : (2 : ℝ) ^ (Nat.log 2 ⌊U ^ 11⌋₊) ≤ U ^ 11 := by
      have := Nat.pow_log_le_self 2 (show ⌊U ^ 11⌋₊ ≠ 0 by omega)
      calc (2 : ℝ) ^ (Nat.log 2 ⌊U ^ 11⌋₊) = ((2 ^ (Nat.log 2 ⌊U ^ 11⌋₊) : ℕ) : ℝ) := by
            push_cast; ring
        _ ≤ (⌊U ^ 11⌋₊ : ℝ) := by exact_mod_cast this
        _ ≤ U ^ 11 := hn
    have hlogs := Real.log_le_log (by positivity) hpow
    rw [Real.log_pow, Real.log_pow] at hlogs
    have hk : (Nat.log 2 ⌊U ^ 11⌋₊ : ℝ) ≤ 16 * Real.log U := by
      have h16 : (11 : ℝ) * Real.log U ≤ 16 * Real.log U * Real.log 2 := by nlinarith
      have h2 : (Nat.log 2 ⌊U ^ 11⌋₊ : ℝ) * Real.log 2 ≤ 16 * Real.log U * Real.log 2 := by
        push_cast at hlogs; linarith
      exact le_of_mul_le_mul_right h2 (by linarith)
    simp only [dyadCount]
    push_cast
    nlinarith
  have hJ0 : (0 : ℝ) ≤ dyadCount U := by positivity
  have hL : 1 + (12 * Real.log U) ^ 2 ≤ 147 * Real.log U ^ 2 := by nlinarith
  have hlog6 : Real.log U ≤ U ^ (a / 6) / (a / 6) :=
    Real.log_le_rpow_div hU0.le (by positivity)
  have hpow6 : Real.log U ^ 6 ≤ (6 / a) ^ 6 * Real.rpow U a := by
    have h1 : Real.log U ^ 6 ≤ (U ^ (a / 6) / (a / 6)) ^ 6 :=
      pow_le_pow_left₀ hl0.le hlog6 6
    have h2 : (U ^ (a / 6) / (a / 6)) ^ 6 = (6 / a) ^ 6 * Real.rpow U a := by
      rw [div_pow, ← Real.rpow_natCast (U ^ (a / 6)), ← Real.rpow_mul hU0.le]
      rw [show a / 6 * ((6 : ℕ) : ℝ) = a by push_cast; ring, Real.rpow_eq_pow]
      field_simp
    linarith
  calc (dyadCount U : ℝ) ^ 2 * (1 + (12 * Real.log U) ^ 2) ^ 2
      ≤ (18 * Real.log U) ^ 2 * (147 * Real.log U ^ 2) ^ 2 := by
        gcongr
    _ = 18 ^ 2 * 147 ^ 2 * Real.log U ^ 6 := by ring
    _ ≤ 18 ^ 2 * 147 ^ 2 * ((6 / a) ^ 6 * Real.rpow U a) := by gcongr
    _ = 18 ^ 2 * 147 ^ 2 * (6 / a) ^ 6 * Real.rpow U a := by ring


theorem exp_neg_le_factorial_div (y : ℝ) (hy : 0 < y) (k : ℕ) :
    Real.exp (-y) ≤ (k.factorial : ℝ) / y ^ k := by
  have h := Real.pow_div_factorial_le_exp y hy.le k
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos y) (by positivity), inv_div]
  exact h

theorem smoothedTerm_norm_le (U β γ : ℝ) (hU : 1 ≤ U) (ω : ArtinPrimitiveRoots.A1.HeckeChar F)
    (hω : IsOfFinOrder ω) (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    ‖smoothedTerm U β γ ω I‖ ≤ (idealDivisorCount I : ℝ) * (Ideal.absNorm I : ℝ) ^ (-β) *
      Real.exp (-(Ideal.absNorm I : ℝ) / U ^ 10) := by
  have hn : 0 < Ideal.absNorm I :=
    Nat.pos_of_ne_zero fun h => hI (Ideal.absNorm_eq_zero_iff.mp h)
  obtain ⟨-, -, -, hτ⟩ := detector_identity (K := F) U hU (fun _ => 0) (by simp) (by simp)
    (s := 2) (by norm_num)
  have h1 := hτ I hI
  have h2 := idealValue_norm_le_one_of_finOrder ω hω I
  have h3 : ‖((Ideal.absNorm I : ℕ) : ℂ) ^ (-((β : ℂ) + (γ : ℂ) * Complex.I))‖ =
      (Ideal.absNorm I : ℝ) ^ (-β) := by
    rw [Complex.norm_natCast_cpow_of_pos hn]
    simp
  have h4 : ‖Complex.exp (-((Ideal.absNorm I : ℕ) : ℂ) / (U : ℂ) ^ 10)‖ =
      Real.exp (-(Ideal.absNorm I : ℝ) / U ^ 10) := by
    rw [Complex.norm_exp]
    congr 1
    have : (-((Ideal.absNorm I : ℕ) : ℂ) / (U : ℂ) ^ 10) =
        ((-(Ideal.absNorm I : ℝ) / U ^ 10 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.ofReal_re]
  unfold smoothedTerm
  rw [norm_mul, norm_mul, norm_mul, h3, h4]
  have hx : 0 ≤ (Ideal.absNorm I : ℝ) ^ (-β) := by positivity
  have hy : 0 ≤ Real.exp (-(Ideal.absNorm I : ℝ) / U ^ 10) := (Real.exp_pos _).le
  calc ‖(detectorCoeff U I : ℂ)‖ * ‖ω.idealValue I‖ * (Ideal.absNorm I : ℝ) ^ (-β) *
        Real.exp (-(Ideal.absNorm I : ℝ) / U ^ 10)
      ≤ (idealDivisorCount I : ℝ) * 1 * (Ideal.absNorm I : ℝ) ^ (-β) *
        Real.exp (-(Ideal.absNorm I : ℝ) / U ^ 10) := by
        gcongr
    _ = _ := by ring

/-- Unit term, vanishing range and tail of the smoothed detector sum. -/
theorem smoothed_detection
    (hdiv : ∃ C : ℝ, 0 < C ∧ ∀ I : Ideal (𝓞 F), I ≠ ⊥ →
      (idealDivisorCount I : ℝ) ≤ C * Real.rpow (Ideal.absNorm I : ℝ) (1 / 2)) :
    ∃ Ct : ℝ, 0 < Ct ∧ ∀ (U β γ : ℝ) (ω : ArtinPrimitiveRoots.A1.HeckeChar F), 2 ≤ U →
      IsOfFinOrder ω → 996 / 1000 ≤ β →
      ‖(∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥}, smoothedTerm U β γ ω I.1) -
          (Complex.exp (-1 / (U : ℂ) ^ 10) + ∑ I ∈ midIdeals U, smoothedTerm U β γ ω I)‖ ≤
        Ct / U ^ 2 := by
  obtain ⟨Cτ, hCτ, hτ⟩ := hdiv
  have hZ : Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      ((Ideal.absNorm I.1 : ℝ) ^ 3)⁻¹) := by
    have h := ArtinPrimitiveRoots.A1.Coeff.summable_absNorm_rpow (F := F) 3 (by norm_num)
    refine (h.subtype {I : Ideal (𝓞 F) | I ≠ ⊥}).congr ?_
    intro I
    simp only [Function.comp_apply]
    rw [Real.rpow_neg (by positivity)]
    norm_cast
  set Z : ℝ := ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥}, ((Ideal.absNorm I.1 : ℝ) ^ 3)⁻¹ with hZdef
  have hZ0 : 0 ≤ Z := tsum_nonneg fun I => by positivity
  refine ⟨Cτ * (Nat.factorial 35 : ℝ) * (Z + 1), by positivity, ?_⟩
  intro U β γ ω hU hω hβ
  have hU1 : (1 : ℝ) ≤ U := by linarith
  have hU0 : 0 < U := by linarith
  have hnorm1 : ∀ I : Ideal (𝓞 F), I ≠ ⊥ → (1 : ℝ) ≤ Ideal.absNorm I := by
    intro I hI
    have : 0 < Ideal.absNorm I :=
      Nat.pos_of_ne_zero fun h => hI (Ideal.absNorm_eq_zero_iff.mp h)
    exact_mod_cast this
  -- pointwise bound by the exponential
  have hpt : ∀ I : Ideal (𝓞 F), I ≠ ⊥ →
      ‖smoothedTerm U β γ ω I‖ ≤ Cτ * Real.exp (-(Ideal.absNorm I : ℝ) / U ^ 10) := by
    intro I hI
    have hn := hnorm1 I hI
    refine (smoothedTerm_norm_le U β γ hU1 ω hω I hI).trans ?_
    have h1 : (idealDivisorCount I : ℝ) * (Ideal.absNorm I : ℝ) ^ (-β) ≤ Cτ := by
      calc (idealDivisorCount I : ℝ) * (Ideal.absNorm I : ℝ) ^ (-β)
          ≤ Cτ * (Ideal.absNorm I : ℝ) ^ (1 / 2 : ℝ) * (Ideal.absNorm I : ℝ) ^ (-β) := by
            gcongr
            exact hτ I hI
        _ = Cτ * (Ideal.absNorm I : ℝ) ^ (1 / 2 - β) := by
            rw [mul_assoc, ← Real.rpow_add (by linarith)]
            ring_nf
        _ ≤ Cτ * 1 := by
            gcongr
            exact Real.rpow_le_one_of_one_le_of_nonpos hn (by linarith)
        _ = Cτ := mul_one _
    have he : 0 ≤ Real.exp (-(Ideal.absNorm I : ℝ) / U ^ 10) := (Real.exp_pos _).le
    nlinarith
  -- the two exponential bounds
  have hexp3 : ∀ I : Ideal (𝓞 F), I ≠ ⊥ →
      Real.exp (-(Ideal.absNorm I : ℝ) / U ^ 10) ≤
        (Nat.factorial 3 : ℝ) * (U ^ 10) ^ 3 * ((Ideal.absNorm I : ℝ) ^ 3)⁻¹ := by
    intro I hI
    have hn := hnorm1 I hI
    have h := exp_neg_le_factorial_div ((Ideal.absNorm I : ℝ) / U ^ 10) (by positivity) 3
    rw [neg_div]
    refine h.trans (le_of_eq ?_)
    field_simp
  have hexp35 : ∀ I : Ideal (𝓞 F), I ≠ ⊥ → U ^ 11 < (Ideal.absNorm I : ℝ) →
      Real.exp (-(Ideal.absNorm I : ℝ) / U ^ 10) ≤
        (Nat.factorial 35 : ℝ) / U ^ 2 * ((Ideal.absNorm I : ℝ) ^ 3)⁻¹ := by
    intro I hI hbig
    have hn := hnorm1 I hI
    set n : ℝ := (Ideal.absNorm I : ℝ) with hn_def
    have h := exp_neg_le_factorial_div (n / U ^ 10) (by positivity) 35
    rw [neg_div]
    refine h.trans ?_
    have hpow : (U ^ 11) ^ 32 ≤ n ^ 32 := pow_le_pow_left₀ (by positivity) hbig.le 32
    have hf : (0 : ℝ) ≤ (Nat.factorial 35 : ℝ) := by positivity
    have hkey : (U ^ 10) ^ 35 * (U ^ 2 * n ^ 3) ≤ n ^ 35 * 1 := by
      have e1 : (U ^ 10) ^ 35 * (U ^ 2 * n ^ 3) = (U ^ 11) ^ 32 * n ^ 3 := by ring
      have e2 : n ^ 35 * 1 = n ^ 32 * n ^ 3 := by ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_right hpow (by positivity)
    have e : (Nat.factorial 35 : ℝ) / (n / U ^ 10) ^ 35 =
        (Nat.factorial 35 : ℝ) * (U ^ 10) ^ 35 / n ^ 35 := by
      field_simp
    have e2 : (Nat.factorial 35 : ℝ) / U ^ 2 * (n ^ 3)⁻¹ =
        (Nat.factorial 35 : ℝ) / (U ^ 2 * n ^ 3) := by
      field_simp
    rw [e, e2, div_le_div_iff₀ (by positivity) (by positivity)]
    calc (Nat.factorial 35 : ℝ) * (U ^ 10) ^ 35 * (U ^ 2 * n ^ 3)
        = (Nat.factorial 35 : ℝ) * ((U ^ 10) ^ 35 * (U ^ 2 * n ^ 3)) := by ring
      _ ≤ (Nat.factorial 35 : ℝ) * (n ^ 35 * 1) := mul_le_mul_of_nonneg_left hkey hf
      _ = (Nat.factorial 35 : ℝ) * n ^ 35 := by ring
  -- summability
  let f : {I : Ideal (𝓞 F) // I ≠ ⊥} → ℂ := fun x => smoothedTerm U β γ ω x.1
  let p : {I : Ideal (𝓞 F) // I ≠ ⊥} → Prop := fun x => (Ideal.absNorm x.1 : ℝ) ≤ U ^ 11
  let g : {I : Ideal (𝓞 F) // I ≠ ⊥} → ℂ := fun x => if p x then f x else 0
  let h : {I : Ideal (𝓞 F) // I ≠ ⊥} → ℂ := fun x => if p x then 0 else f x
  have hfb : ∀ x, ‖f x‖ ≤ Cτ * ((Nat.factorial 3 : ℝ) * (U ^ 10) ^ 3) *
      ((Ideal.absNorm x.1 : ℝ) ^ 3)⁻¹ := by
    intro x
    refine (hpt x.1 x.2).trans ?_
    have := hexp3 x.1 x.2
    calc Cτ * Real.exp (-(Ideal.absNorm x.1 : ℝ) / U ^ 10)
        ≤ Cτ * ((Nat.factorial 3 : ℝ) * (U ^ 10) ^ 3 * ((Ideal.absNorm x.1 : ℝ) ^ 3)⁻¹) := by
          gcongr
      _ = _ := by ring
  have hfs : Summable f := Summable.of_norm_bounded (hZ.mul_left _) hfb
  have hgs : Summable g := by
    refine Summable.of_norm_bounded hfs.norm fun x => ?_
    simp only [g]
    split_ifs <;> simp
  have hhs : Summable h := by
    refine Summable.of_norm_bounded hfs.norm fun x => ?_
    simp only [h]
    split_ifs <;> simp
  have hfgh : (∑' x, f x) = (∑' x, g x) + ∑' x, h x := by
    rw [← hgs.tsum_add hhs]
    congr 1
    funext x
    simp only [g, h]
    split_ifs <;> simp
  -- the finite part
  let T : Finset (Ideal (𝓞 F)) := (idealsUpTo (F := F) (U ^ 11)).filter fun I => I ≠ ⊥
  have hU11 : (0 : ℝ) ≤ U ^ 11 := by positivity
  have hmemT : ∀ I : Ideal (𝓞 F), I ∈ idealsUpTo (F := F) (U ^ 11) ↔
      (Ideal.absNorm I : ℝ) ≤ U ^ 11 := by
    intro I
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    exact Nat.le_floor_iff hU11
  have hg_sum : (∑' x, g x) = ∑ I ∈ T, smoothedTerm U β γ ω I := by
    rw [tsum_eq_sum (s := (idealsUpTo (F := F) (U ^ 11)).subtype fun I => I ≠ ⊥)]
    · rw [Finset.sum_subtype_eq_sum_filter (f := fun I => if (Ideal.absNorm I : ℝ) ≤ U ^ 11 then
        smoothedTerm U β γ ω I else 0)]
      refine Finset.sum_congr rfl fun I hI => ?_
      have : (Ideal.absNorm I : ℝ) ≤ U ^ 11 := (hmemT I).1 (Finset.mem_filter.1 hI).1
      simp [this]
    · intro x hx
      have hnp : ¬ p x := by
        intro hp
        apply hx
        rw [Finset.mem_subtype]
        exact (hmemT x.1).2 hp
      simp [g, hnp]
  obtain ⟨-, htop, hzero, -⟩ := detector_identity (K := F) U hU1 (fun _ => 0) (by simp) (by simp)
    (s := 2) (by norm_num)
  have hterm_top : smoothedTerm U β γ ω ⊤ = Complex.exp (-1 / (U : ℂ) ^ 10) := by
    unfold smoothedTerm
    rw [htop, idealValue_top, Ideal.absNorm_top]
    simp
  have hT : ∑ I ∈ T, smoothedTerm U β γ ω I =
      Complex.exp (-1 / (U : ℂ) ^ 10) + ∑ I ∈ midIdeals U, smoothedTerm U β γ ω I := by
    have hsplit : ∀ I ∈ T, smoothedTerm U β γ ω I =
        (if I = ⊤ then Complex.exp (-1 / (U : ℂ) ^ 10) else 0) +
          (if U ^ 2 < (Ideal.absNorm I : ℝ) then smoothedTerm U β γ ω I else 0) := by
      intro I hI
      have hI0 : I ≠ ⊥ := (Finset.mem_filter.mp hI).2
      by_cases htop' : I = ⊤
      · subst htop'
        have hn : ¬ (U ^ 2 < ((Ideal.absNorm (⊤ : Ideal (𝓞 F)) : ℕ) : ℝ)) := by
          rw [Ideal.absNorm_top]; push_cast; nlinarith
        rw [if_pos rfl, if_neg hn, add_zero, hterm_top]
      · rw [if_neg htop', zero_add]
        by_cases hmid : U ^ 2 < (Ideal.absNorm I : ℝ)
        · rw [if_pos hmid]
        · rw [if_neg hmid]
          have hn0 : Ideal.absNorm I ≠ 0 := fun h => hI0 (Ideal.absNorm_eq_zero_iff.mp h)
          have hn1 : Ideal.absNorm I ≠ 1 := fun h => htop' (Ideal.absNorm_eq_one_iff.mp h)
          have h1 : 1 < Ideal.absNorm I := by omega
          have := hzero I hI0 h1 (not_lt.mp hmid)
          unfold smoothedTerm
          rw [this]
          simp
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq']
    have htopT : (⊤ : Ideal (𝓞 F)) ∈ T := by
      refine Finset.mem_filter.mpr ⟨(hmemT ⊤).2 ?_, by simp⟩
      rw [Ideal.absNorm_top]; push_cast
      exact one_le_pow₀ hU1
    rw [if_pos htopT]
    congr 1
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext I
    simp only [T, midIdeals, Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨h1, ?_⟩, h2⟩
      rintro rfl
      simp at h2
      nlinarith
  have hmain : (∑' x, f x) - (Complex.exp (-1 / (U : ℂ) ^ 10) +
      ∑ I ∈ midIdeals U, smoothedTerm U β γ ω I) = ∑' x, h x := by
    rw [hfgh, hg_sum, hT]
    ring
  change ‖(∑' x, f x) - _‖ ≤ _
  rw [hmain]
  have hhb : ∀ x, ‖h x‖ ≤ (Cτ * (Nat.factorial 35 : ℝ) / U ^ 2) *
      ((Ideal.absNorm x.1 : ℝ) ^ 3)⁻¹ := by
    intro x
    simp only [h]
    split_ifs with hp
    · simp only [norm_zero]
      positivity
    · have hbig : U ^ 11 < (Ideal.absNorm x.1 : ℝ) := not_le.mp hp
      calc ‖f x‖ ≤ Cτ * Real.exp (-(Ideal.absNorm x.1 : ℝ) / U ^ 10) := hpt x.1 x.2
        _ ≤ Cτ * ((Nat.factorial 35 : ℝ) / U ^ 2 * ((Ideal.absNorm x.1 : ℝ) ^ 3)⁻¹) := by
            gcongr
            exact hexp35 x.1 x.2 hbig
        _ = _ := by ring
  calc ‖∑' x, h x‖ ≤ ∑' x, ‖h x‖ := norm_tsum_le_tsum_norm hhs.norm
    _ ≤ ∑' x : {I : Ideal (𝓞 F) // I ≠ ⊥}, (Cτ * (Nat.factorial 35 : ℝ) / U ^ 2) *
          ((Ideal.absNorm x.1 : ℝ) ^ 3)⁻¹ :=
        Summable.tsum_le_tsum hhb hhs.norm (hZ.mul_left _)
    _ = (Cτ * (Nat.factorial 35 : ℝ) / U ^ 2) * Z := tsum_mul_left
    _ ≤ Cτ * (Nat.factorial 35 : ℝ) * (Z + 1) / U ^ 2 := by
        rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
        have : (0 : ℝ) ≤ Cτ * (Nat.factorial 35 : ℝ) := by positivity
        nlinarith

theorem natCast_cpow_split (n : ℕ) (hn : 0 < n) (β γ : ℝ) :
    ((n : ℕ) : ℂ) ^ (-((β : ℂ) + (γ : ℂ) * Complex.I)) =
      ((n : ℕ) : ℂ) ^ (-(996 / 1000 : ℂ)) *
        Complex.exp (-(((β - 996 / 1000 : ℝ) : ℂ) + (γ : ℂ) * Complex.I) * (Real.log n : ℂ)) := by
  have hn0 : ((n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Complex.cpow_def_of_ne_zero hn0, Complex.cpow_def_of_ne_zero hn0, ← Complex.exp_add]
  congr 1
  have hlog : Complex.log ((n : ℕ) : ℂ) = (Real.log n : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n)]
  rw [hlog]
  push_cast
  ring

theorem dyad_arith (X U δ : ℝ) (hX1 : 1 ≤ X) (hXU : X ≤ U ^ 11) (hU : 1 ≤ U) (hδ : 0 ≤ δ)
    (hδ1 : δ ≤ 1) :
    X ^ 2 * (X ^ (δ - 996 / 1000)) ^ 2 * (2 * X * U) ^ δ ≤
      2 * U ^ (88 / 1000 + 34 * δ) := by
  have hX0 : 0 < X := by linarith
  have hU0 : 0 < U := by linarith
  have e1 : X ^ 2 * (X ^ (δ - 996 / 1000)) ^ 2 * (2 * X * U) ^ δ =
      (2 : ℝ) ^ δ * (X ^ (3 * δ + 8 / 1000) * U ^ δ) := by
    rw [Real.mul_rpow (by positivity) hU0.le, Real.mul_rpow (by norm_num) hX0.le]
    rw [← Real.rpow_natCast X 2, ← Real.rpow_natCast (X ^ (δ - 996 / 1000)) 2,
      ← Real.rpow_mul hX0.le]
    have : X ^ ((2 : ℕ) : ℝ) * X ^ ((δ - 996 / 1000) * ((2 : ℕ) : ℝ)) * X ^ δ =
        X ^ (3 * δ + 8 / 1000) := by
      rw [← Real.rpow_add hX0, ← Real.rpow_add hX0]
      congr 1
      push_cast
      ring
    rw [← this]
    ring
  rw [e1]
  have h1 : X ^ (3 * δ + 8 / 1000) ≤ U ^ (11 * (3 * δ + 8 / 1000)) := by
    calc X ^ (3 * δ + 8 / 1000) ≤ (U ^ 11) ^ (3 * δ + 8 / 1000) :=
          Real.rpow_le_rpow hX0.le hXU (by positivity)
      _ = U ^ (11 * (3 * δ + 8 / 1000)) := by
          rw [← Real.rpow_natCast U 11, ← Real.rpow_mul hU0.le]
          push_cast
          ring_nf
  have h2 : (2 : ℝ) ^ δ ≤ 2 := by
    calc (2 : ℝ) ^ δ ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hδ1
      _ = 2 := Real.rpow_one 2
  have h3 : U ^ (11 * (3 * δ + 8 / 1000)) * U ^ δ = U ^ (88 / 1000 + 34 * δ) := by
    rw [← Real.rpow_add hU0]
    congr 1
    ring
  calc (2 : ℝ) ^ δ * (X ^ (3 * δ + 8 / 1000) * U ^ δ)
      ≤ 2 * (U ^ (11 * (3 * δ + 8 / 1000)) * U ^ δ) := by
        gcongr
    _ = 2 * U ^ (88 / 1000 + 34 * δ) := by rw [h3]

/-- Per-dyad family estimate: conductor sieve plus `dirichlet_poly_max_bound`. -/
theorem dyad_family_bound
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (η : ArtinPrimitiveRoots.A1.HeckeChar F) (fd : FrequencyData S D η)
    (ρ δ : ℝ) (hρ : 0 < ρ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 100)
    (hcount : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t → ((idealsUpTo (F := F) t).card : ℝ) ≤ C * t)
    (hdiv : ∃ C : ℝ, 0 < C ∧ ∀ I : Ideal (𝓞 F), I ≠ ⊥ →
      (idealDivisorCount I : ℝ) ≤ C * Real.rpow (Ideal.absNorm I : ℝ) δ) :
    ∃ K : ℝ, 0 < K ∧ ∀ U : ℝ, 2 ≤ U → ∀ j : ℕ, ∀ E : Finset fd.U,
      (∀ u ∈ E, U ≤ fd.q u ∧ fd.q u < 2 * U) →
      ∀ β γ : fd.U → ℝ, (∀ u ∈ E, 996 / 1000 ≤ β u ∧ β u ≤ 1 ∧ |γ u| ≤ 4 * Real.rpow U ρ) →
        ∑ u ∈ E, ‖∑ I ∈ dyadIdeals U j, smoothedTerm U (β u) (γ u) (fd.omega u) I‖ ^ 2 ≤
          K * (1 + 16 * Real.rpow U ρ) * (1 + (12 * Real.log U) ^ 2) ^ 2 *
            Real.rpow U (88 / 1000 + 34 * δ) := by
  obtain ⟨Cf, hCf, hcond⟩ := fd.conductor_bound
  obtain ⟨LS, hLS⟩ := fd.local_components_finite
  obtain ⟨Csv, hCsv, hsv⟩ := lem_conductor_sieve S (2 * Cf) (by positivity) LS δ hδ
  obtain ⟨Cid, hCid, hid⟩ := hcount
  obtain ⟨Cτ, hCτ, hτ⟩ := hdiv
  refine ⟨96 * Csv * Cid * Cτ ^ 2, by positivity, ?_⟩
  intro U hU j E hE β γ hβγ
  have hU1 : (1 : ℝ) ≤ U := by linarith
  have hU0 : 0 < U := by linarith
  have hUρ : 0 ≤ Real.rpow U ρ := Real.rpow_nonneg hU0.le ρ
  have hUe : 0 ≤ Real.rpow U (88 / 1000 + 34 * δ) := Real.rpow_nonneg hU0.le _
  set B := dyadIdeals (F := F) U j with hB
  rcases B.eq_empty_or_nonempty with hBe | ⟨I0, hI0⟩
  · rw [hBe]
    simp only [Finset.sum_empty, norm_zero]
    have : (0 : ℝ) ≤ 96 * Csv * Cid * Cτ ^ 2 * (1 + 16 * Real.rpow U ρ) *
        (1 + (12 * Real.log U) ^ 2) ^ 2 * Real.rpow U (88 / 1000 + 34 * δ) := by positivity
    simpa using this
  obtain ⟨_, hI0b, hI0c, _⟩ := mem_dyadIdeals hU0.le hI0
  set X : ℝ := 2 ^ j with hXdef
  have hX1 : 1 ≤ X := one_le_pow₀ (by norm_num)
  have hX0 : 0 < X := by linarith
  have hXU : X ≤ U ^ 11 := hI0c.trans hI0b
  have hpowj : (2 : ℝ) ^ (j + 1) = 2 * X := by rw [pow_succ]; ring
  have hU2X : U ^ 2 < 2 * X := by
    have := (mem_dyadIdeals hU0.le hI0).1
    have := (mem_dyadIdeals hU0.le hI0).2.2.2
    linarith
  set N : ℝ := 2 * X with hNdef
  have hN2 : 2 ≤ N := by linarith
  have hmemB : ∀ I ∈ B, 0 < Ideal.absNorm I ∧ X ≤ Ideal.absNorm I ∧ (Ideal.absNorm I : ℝ) < N := by
    intro I hI
    obtain ⟨h1, _, h3, h4⟩ := mem_dyadIdeals hU0.le hI
    refine ⟨?_, h3, by rw [← hpowj]; exact h4⟩
    have : (0 : ℝ) < Ideal.absNorm I := lt_of_lt_of_le (by positivity) h1.le
    exact_mod_cast this
  -- data of the Dirichlet polynomial
  let c : Ideal (𝓞 F) → ℂ := fun I => (detectorCoeff U I : ℂ) *
    ((Ideal.absNorm I : ℕ) : ℂ) ^ (-(996 / 1000 : ℂ)) *
    Complex.exp (-((Ideal.absNorm I : ℕ) : ℂ) / (U : ℂ) ^ 10)
  let χ : fd.U → Ideal (𝓞 F) → ℂ := fun u I => (fd.omega u).idealValue I
  let lam : Ideal (𝓞 F) → ℝ := fun I => Real.log (Ideal.absNorm I)
  let σ : fd.U → ℝ := fun u => β u - 996 / 1000
  have hrepr : ∀ u, ∑ I ∈ B, smoothedTerm U (β u) (γ u) (fd.omega u) I =
      dpoly B (fun I => c I * χ u I) lam (σ u) (γ u) := by
    intro u
    unfold dpoly
    refine Finset.sum_congr rfl fun I hI => ?_
    unfold smoothedTerm
    rw [natCast_cpow_split _ (hmemB I hI).1]
    simp only [c, χ, lam, σ]
    ring
  -- the sieve on this dyad
  set Ssv : ℝ := Csv * (N + U ^ 2) * Real.rpow (N * U) δ with hSsv
  have hS0 : 0 ≤ Ssv := by
    have := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ N * U) δ
    positivity
  have hsub : B ⊆ idealsUpTo (F := F) N := by
    intro I hI
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    apply Nat.le_floor
    exact (hmemB I hI).2.2.le
  have hsieve : ∀ b : Ideal (𝓞 F) → ℂ,
      ∑ u ∈ E, ‖∑ I ∈ B, b I * χ u I‖ ^ 2 ≤ Ssv * ∑ I ∈ B, ‖b I‖ ^ 2 := by
    intro b
    have hX : ∀ ω ∈ E.image fd.omega, IsOfFinOrder ω ∧ SComponent S ω ∈ LS ∧
        ∃ 𝔣 : Ideal (𝓞 F), IsPrimitiveConductor ω 𝔣 ∧ (Ideal.absNorm 𝔣 : ℝ) ≤ 2 * Cf * U := by
      intro ω hω
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hω
      obtain ⟨𝔣, hprim, hnorm⟩ := hcond u
      refine ⟨fd.omega_finiteOrder u, hLS u, 𝔣, hprim, ?_⟩
      have := (hE u hu).2
      nlinarith
    have h := hsv N U hN2 hU (E.image fd.omega) hX (fun I => if I ∈ B then b I else 0)
    rw [Finset.sum_image (fun u _ v _ huv => fd.omega_injective u v huv)] at h
    have e1 : ∀ u : fd.U, ∑ I ∈ idealsUpTo (F := F) N,
        (if I ∈ B then b I else 0) * (fd.omega u).idealValue I = ∑ I ∈ B, b I * χ u I := by
      intro u
      simp only [ite_mul, zero_mul]
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsub]
    have e2 : ∑ I ∈ idealsUpTo (F := F) N, ‖if I ∈ B then b I else 0‖ ^ 2 =
        ∑ I ∈ B, ‖b I‖ ^ 2 := by
      have : ∀ I, ‖if I ∈ B then b I else 0‖ ^ 2 = if I ∈ B then ‖b I‖ ^ 2 else 0 := by
        intro I
        split_ifs <;> simp
      simp only [this]
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsub]
    have e1' : ∀ u : fd.U, ‖∑ I ∈ idealsUpTo (F := F) N,
        (if I ∈ B then b I else 0) * (fd.omega u).idealValue I‖ ^ 2 =
        ‖∑ I ∈ B, b I * χ u I‖ ^ 2 := fun u => by rw [e1 u]
    rw [Finset.sum_congr rfl fun u _ => e1' u, e2] at h
    exact h
  -- the maximal bound
  have hlam : ∀ I ∈ B, 0 ≤ lam I ∧ lam I ≤ Real.log N := by
    intro I hI
    obtain ⟨h1, _, h3⟩ := hmemB I hI
    have hn1 : (1 : ℝ) ≤ Ideal.absNorm I := by exact_mod_cast h1
    exact ⟨Real.log_nonneg hn1, Real.log_le_log (by linarith) h3.le⟩
  have hT : 0 < 4 * Real.rpow U ρ := by
    have := Real.rpow_pos_of_pos hU0 ρ
    positivity
  have hσ : ∀ u ∈ E, σ u ∈ Set.Icc (0 : ℝ) 1 := by
    intro u hu
    obtain ⟨h1, h2, _⟩ := hβγ u hu
    simp only [σ, Set.mem_Icc]
    constructor <;> linarith
  have hγ : ∀ u ∈ E, γ u ∈ Set.Icc (-(4 * Real.rpow U ρ)) (4 * Real.rpow U ρ) := by
    intro u hu
    exact abs_le.mp (hβγ u hu).2.2
  have hmax := dirichlet_poly_max_bound E B χ c lam hlam hT hS0 hsieve σ γ hσ hγ
  -- coefficient bound
  obtain ⟨-, -, -, hτdet⟩ := detector_identity (K := F) U hU1 (fun _ => 0) (by simp) (by simp)
    (s := 2) (by norm_num)
  have hcI : ∀ I ∈ B, ‖c I‖ ≤ Cτ * X ^ (δ - 996 / 1000) := by
    intro I hI
    obtain ⟨hn, hXn, _⟩ := hmemB I hI
    have hI0 : I ≠ ⊥ := by
      rintro rfl
      simp at hn
    have hn1 : (1 : ℝ) ≤ Ideal.absNorm I := by exact_mod_cast hn
    have hα : ‖(detectorCoeff U I : ℂ)‖ ≤ Cτ * (Ideal.absNorm I : ℝ) ^ δ :=
      (hτdet I hI0).trans (hτ I hI0)
    have hexp : ‖Complex.exp (-((Ideal.absNorm I : ℕ) : ℂ) / (U : ℂ) ^ 10)‖ ≤ 1 := by
      rw [Complex.norm_exp]
      apply Real.exp_le_one_iff.mpr
      have : (-((Ideal.absNorm I : ℕ) : ℂ) / (U : ℂ) ^ 10) =
          ((-(Ideal.absNorm I : ℝ) / U ^ 10 : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.ofReal_re]
      have : (0 : ℝ) ≤ (Ideal.absNorm I : ℝ) / U ^ 10 := by positivity
      rw [neg_div]
      linarith
    simp only [c, norm_mul]
    rw [Complex.norm_natCast_cpow_of_pos hn]
    have hre : (-(996 / 1000 : ℂ)).re = -(996 / 1000) := by norm_num
    rw [hre]
    have hp0 : 0 ≤ (Ideal.absNorm I : ℝ) ^ (-(996 / 1000 : ℝ)) := by positivity
    calc ‖(detectorCoeff U I : ℂ)‖ * (Ideal.absNorm I : ℝ) ^ (-(996 / 1000 : ℝ)) *
          ‖Complex.exp (-((Ideal.absNorm I : ℕ) : ℂ) / (U : ℂ) ^ 10)‖
        ≤ (Cτ * (Ideal.absNorm I : ℝ) ^ δ) * (Ideal.absNorm I : ℝ) ^ (-(996 / 1000 : ℝ)) * 1 := by
          gcongr
      _ = Cτ * (Ideal.absNorm I : ℝ) ^ (δ - 996 / 1000) := by
          rw [mul_one, mul_assoc, ← Real.rpow_add (by linarith)]
          ring_nf
      _ ≤ Cτ * X ^ (δ - 996 / 1000) := by
          have hz : δ - 996 / 1000 ≤ (0 : ℝ) := by linarith
          exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hX0 hXn hz) hCτ.le
  have hQ : ∑ I ∈ B, ‖c I‖ ^ 2 ≤ Cid * N * (Cτ ^ 2 * (X ^ (δ - 996 / 1000)) ^ 2) := by
    calc ∑ I ∈ B, ‖c I‖ ^ 2 ≤ ∑ _I ∈ B, Cτ ^ 2 * (X ^ (δ - 996 / 1000)) ^ 2 := by
          refine Finset.sum_le_sum fun I hI => ?_
          rw [← mul_pow]
          exact pow_le_pow_left₀ (norm_nonneg _) (hcI I hI) 2
      _ = (B.card : ℝ) * (Cτ ^ 2 * (X ^ (δ - 996 / 1000)) ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Cid * N * (Cτ ^ 2 * (X ^ (δ - 996 / 1000)) ^ 2) := by
          gcongr
          calc (B.card : ℝ) ≤ ((idealsUpTo (F := F) N).card : ℝ) := by
                exact_mod_cast Finset.card_le_card hsub
            _ ≤ Cid * N := hid N (by linarith)
  have hSQ : Ssv * ∑ I ∈ B, ‖c I‖ ^ 2 ≤ 16 * Csv * Cid * Cτ ^ 2 * Real.rpow U (88 / 1000 + 34 * δ) := by
    have hNU : N + U ^ 2 ≤ 2 * N := by linarith
    have hpow0 : 0 ≤ Real.rpow (N * U) δ := Real.rpow_nonneg (by positivity) δ
    have harith := dyad_arith X U δ hX1 hXU hU1 hδ.le (by linarith)
    have hQ0' : 0 ≤ ∑ I ∈ B, ‖c I‖ ^ 2 := Finset.sum_nonneg fun I _ => by positivity
    have hNU' : Real.rpow (N * U) δ = (2 * X * U) ^ δ := by
      rw [Real.rpow_eq_pow, hNdef]
    calc Ssv * ∑ I ∈ B, ‖c I‖ ^ 2
        ≤ (Csv * (2 * N) * Real.rpow (N * U) δ) * (Cid * N * (Cτ ^ 2 * (X ^ (δ - 996 / 1000)) ^ 2)) := by
          have hSle : Ssv ≤ Csv * (2 * N) * Real.rpow (N * U) δ := by
            rw [hSsv]
            gcongr
          exact mul_le_mul hSle hQ hQ0' (by positivity)
      _ = 8 * Csv * Cid * Cτ ^ 2 * (X ^ 2 * (X ^ (δ - 996 / 1000)) ^ 2 * (2 * X * U) ^ δ) := by
          rw [hNU', hNdef]
          ring
      _ ≤ 8 * Csv * Cid * Cτ ^ 2 * (2 * U ^ (88 / 1000 + 34 * δ)) := by
          gcongr
      _ = 16 * Csv * Cid * Cτ ^ 2 * Real.rpow U (88 / 1000 + 34 * δ) := by
          rw [Real.rpow_eq_pow]
          ring
  have hlogN : (1 + Real.log N ^ 2) ^ 2 ≤ (1 + (12 * Real.log U) ^ 2) ^ 2 := by
    have hl0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
    have hl1 : Real.log N ≤ 12 * Real.log U := by
      have h2U : N ≤ 2 * U ^ 11 := by linarith
      calc Real.log N ≤ Real.log (2 * U ^ 11) := Real.log_le_log (by linarith) h2U
        _ = Real.log 2 + 11 * Real.log U := by
            rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
            push_cast
            ring
        _ ≤ 12 * Real.log U := by
            have := Real.log_le_log (by norm_num) hU
            linarith
    have : Real.log N ^ 2 ≤ (12 * Real.log U) ^ 2 := pow_le_pow_left₀ hl0 hl1 2
    gcongr
  rw [Finset.sum_congr rfl fun u _ => by rw [hrepr u]]
  have hQ0 : 0 ≤ ∑ I ∈ B, ‖c I‖ ^ 2 := Finset.sum_nonneg fun I _ => by positivity
  calc ∑ u ∈ E, ‖dpoly B (fun I => c I * χ u I) lam (σ u) (γ u)‖ ^ 2
      ≤ 3 * (1 + 4 * (4 * Real.rpow U ρ)) * Ssv * (1 + Real.log N ^ 2) ^ 2 *
          ∑ I ∈ B, ‖c I‖ ^ 2 := hmax
    _ = 3 * (1 + 16 * Real.rpow U ρ) * (1 + Real.log N ^ 2) ^ 2 *
          (Ssv * ∑ I ∈ B, ‖c I‖ ^ 2) := by ring
    _ ≤ 3 * (1 + 16 * Real.rpow U ρ) * (1 + (12 * Real.log U) ^ 2) ^ 2 *
          (16 * Csv * Cid * Cτ ^ 2 * Real.rpow U (88 / 1000 + 34 * δ)) := by
        gcongr
    _ ≤ 96 * Csv * Cid * Cτ ^ 2 * (1 + 16 * Real.rpow U ρ) * (1 + (12 * Real.log U) ^ 2) ^ 2 *
          Real.rpow U (88 / 1000 + 34 * δ) := by
        have : 0 ≤ Csv * Cid * Cτ ^ 2 * (1 + 16 * Real.rpow U ρ) * (1 + (12 * Real.log U) ^ 2) ^ 2 *
          Real.rpow U (88 / 1000 + 34 * δ) := by positivity
        nlinarith

/-- **Detector count core** (A2-ZERO-DETECT): `zf_detector_count` with the ideal count, divisor
bound and detector shift supplied as hypotheses. -/
theorem detector_count_core
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (η : ArtinPrimitiveRoots.A1.HeckeChar F) (fd : FrequencyData S D η)
    (L : ∀ u : fd.U, fd.omega u ≠ 1 → HeckeLContinuation (fd.omega u))
    (A_F ρ ε : ℝ) (hρ : 0 < ρ) (hAρ : A_F * ρ < 1) (hε : 0 < ε)
    (hcount : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊t⌋₊).toFinset.card : ℝ) ≤ C * t)
    (hdiv : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 < C ∧ ∀ I : Ideal (𝓞 F), I ≠ ⊥ →
      (idealDivisorCount I : ℝ) ≤ C * Real.rpow (Ideal.absNorm I : ℝ) δ)
    (hshift : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 < C ∧
      ∀ (u : fd.U) (hnon : fd.omega u ≠ 1) (U β γ : ℝ), 2 ≤ U → U ≤ fd.q u → fd.q u < 2 * U →
        (L u hnon).value (β + γ * Complex.I) = 0 → 996 / 1000 ≤ β →
        |γ| ≤ 4 * Real.rpow U ρ →
        β ≤ 1 ∧ ‖∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥}, smoothedTerm U β γ (fd.omega u) I.1‖ ≤
          C * Real.rpow U (-(346 / 100 : ℝ) + A_F * ρ + δ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ, 2 ≤ U →
      ∀ E : Finset fd.U,
        (∀ u ∈ E, U ≤ fd.q u ∧ fd.q u < 2 * U ∧
          ∃ hnon : fd.omega u ≠ 1, ∃ s : ℂ,
            996 / 1000 ≤ s.re ∧ |s.im| ≤ 4 * Real.rpow U ρ ∧ (L u hnon).value s = 0) →
        (E.card : ℝ) ≤ C * Real.rpow U (88 / 1000 + ρ + ε) := by
  set δ : ℝ := min (ε / 100) (1 / 100) with hδdef
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδ1 : δ ≤ 1 / 100 := min_le_right _ _
  have hδε : δ ≤ ε / 100 := min_le_left _ _
  obtain ⟨Csh, hCsh, hsh⟩ := hshift δ hδ
  obtain ⟨Ct, hCt, hdet⟩ := smoothed_detection (F := F) (hdiv (1 / 2) (by norm_num))
  obtain ⟨K, hK, hdyad⟩ := dyad_family_bound S D η fd ρ δ hρ hδ hδ1 hcount (hdiv δ hδ)
  obtain ⟨Clog, hClog, hlog⟩ := log_factors_absorb (ε / 2) (by positivity)
  obtain ⟨Cc, hCc, hdc⟩ := fd.dyadic_count
  set κ : ℝ := 346 / 100 - A_F * ρ - δ with hκdef
  have hκ : 0 < κ := by linarith
  have hev1 : ∀ᶠ U : ℝ in Filter.atTop, Csh * U ^ (-κ) < 1 / 8 := by
    have h : Filter.Tendsto (fun U : ℝ => Csh * U ^ (-κ)) Filter.atTop (nhds (Csh * 0)) :=
      (tendsto_rpow_neg_atTop hκ).const_mul Csh
    rw [mul_zero] at h
    exact h.eventually (gt_mem_nhds (by norm_num))
  have hev2 : ∀ᶠ U : ℝ in Filter.atTop, Ct / U ^ 2 < 1 / 8 := by
    have h : Filter.Tendsto (fun U : ℝ => Ct / U ^ 2) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop (Filter.tendsto_pow_atTop (by norm_num))
    exact h.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨U1, hU1⟩ := Filter.eventually_atTop.mp (hev1.and hev2)
  set U1' : ℝ := max U1 2 with hU1'
  have hU1'0 : 0 < U1' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  refine ⟨272 * K * Clog + Cc * U1', by positivity, ?_⟩
  intro U hU E hE
  have hU0 : 0 < U := by linarith
  have hU1le : (1 : ℝ) ≤ U := by linarith
  set p : ℝ := 88 / 1000 + ρ + ε with hpdef
  have hp1 : 1 ≤ Real.rpow U p := Real.one_le_rpow hU1le (by positivity)
  have hC1 : 0 ≤ 272 * K * Clog := by positivity
  by_cases hsmall : U < U1'
  · have hcard : (E.card : ℝ) ≤ Cc * U := by
      obtain ⟨hfin, hbound⟩ := hdc U hU
      have hsubset : (E : Set fd.U) ⊆ {u | U ≤ fd.q u ∧ fd.q u < 2 * U} :=
        fun u hu => ⟨(hE u hu).1, (hE u hu).2.1⟩
      have hcardle := Set.ncard_le_ncard hsubset hfin
      calc (E.card : ℝ) = (Set.ncard (E : Set fd.U) : ℝ) := by simp
        _ ≤ (Set.ncard {u : fd.U | U ≤ fd.q u ∧ fd.q u < 2 * U} : ℝ) := by
            exact_mod_cast hcardle
        _ ≤ Cc * U := hbound
    calc (E.card : ℝ) ≤ Cc * U := hcard
      _ ≤ Cc * U1' := by gcongr
      _ ≤ Cc * U1' * Real.rpow U p := le_mul_of_one_le_right (by positivity) hp1
      _ ≤ (272 * K * Clog + Cc * U1') * Real.rpow U p := by
          gcongr
          linarith
  have hUbig : U1 ≤ U := le_trans (le_max_left _ _) (not_lt.mp hsmall)
  obtain ⟨hA1, hA2⟩ := hU1 U hUbig
  -- choose the zeros
  have hE' : ∀ u : fd.U, ∃ s : ℂ, u ∈ E → ∃ hnon : fd.omega u ≠ 1,
      996 / 1000 ≤ s.re ∧ |s.im| ≤ 4 * Real.rpow U ρ ∧ (L u hnon).value s = 0 := by
    intro u
    by_cases hu : u ∈ E
    · obtain ⟨_, _, hnon, s, h1, h2, h3⟩ := hE u hu
      exact ⟨s, fun _ => ⟨hnon, h1, h2, h3⟩⟩
    · exact ⟨0, fun h => absurd h hu⟩
  choose sz hsz using hE'
  let β : fd.U → ℝ := fun u => (sz u).re
  let γ : fd.U → ℝ := fun u => (sz u).im
  have hzero : ∀ u ∈ E, ∃ hnon : fd.omega u ≠ 1,
      (L u hnon).value ((β u : ℂ) + (γ u : ℂ) * Complex.I) = 0 := by
    intro u hu
    obtain ⟨hnon, _, _, h3⟩ := hsz u hu
    refine ⟨hnon, ?_⟩
    simp only [β, γ, Complex.re_add_im]
    exact h3
  have hshift_u : ∀ u ∈ E, β u ≤ 1 ∧
      ‖∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥}, smoothedTerm U (β u) (γ u) (fd.omega u) I.1‖ <
        1 / 8 := by
    intro u hu
    obtain ⟨hnon, hz⟩ := hzero u hu
    obtain ⟨_, _, _, h1, h2, _⟩ := hE u hu
    obtain ⟨hb1, hb2⟩ := hsh u hnon U (β u) (γ u) hU (hE u hu).1 (hE u hu).2.1 hz
      (hsz u hu).2.1 (hsz u hu).2.2.1
    refine ⟨hb1, lt_of_le_of_lt hb2 ?_⟩
    have : -(346 / 100 : ℝ) + A_F * ρ + δ = -κ := by rw [hκdef]; ring
    rw [this]
    exact hA1
  -- the detection inequality for each member
  have hdetect : ∀ u ∈ E, (1 / 16 : ℝ) ≤ (dyadCount U : ℝ) *
      ∑ j ∈ Finset.range (dyadCount U),
        ‖∑ I ∈ dyadIdeals U j, smoothedTerm U (β u) (γ u) (fd.omega u) I‖ ^ 2 := by
    intro u hu
    set tot := ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥}, smoothedTerm U (β u) (γ u) (fd.omega u) I.1
    set ex := Complex.exp (-1 / (U : ℂ) ^ 10)
    set mid := ∑ I ∈ midIdeals U, smoothedTerm U (β u) (γ u) (fd.omega u) I
    have hd := hdet U (β u) (γ u) (fd.omega u) hU (fd.omega_finiteOrder u) (hsz u hu).2.1
    have ht := (hshift_u u hu).2
    have hex : (1 / 2 : ℝ) ≤ ‖ex‖ := by
      have hre : ex = Complex.exp ((-1 / U ^ 10 : ℝ) : ℂ) := by
        simp only [ex]
        congr 1
        push_cast
        ring
      rw [hre, Complex.norm_exp_ofReal]
      have hU10 : (2 : ℝ) ≤ U ^ 10 := by
        calc (2 : ℝ) ≤ U := hU
          _ ≤ U ^ 10 := le_self_pow₀ hU1le (by norm_num)
      have hx : -(1 / 2 : ℝ) ≤ -1 / U ^ 10 := by
        rw [neg_div, neg_le_neg_iff, div_le_div_iff₀ (by positivity) (by positivity)]
        linarith
      have := Real.add_one_le_exp (-1 / U ^ 10)
      linarith
    have htri : ‖ex‖ ≤ ‖tot‖ + ‖mid‖ + ‖tot - (ex + mid)‖ := by
      have : ex = tot - mid - (tot - (ex + mid)) := by ring
      calc ‖ex‖ = ‖tot - mid - (tot - (ex + mid))‖ := by rw [← this]
        _ ≤ ‖tot - mid‖ + ‖tot - (ex + mid)‖ := norm_sub_le _ _
        _ ≤ ‖tot‖ + ‖mid‖ + ‖tot - (ex + mid)‖ := by
            gcongr
            exact norm_sub_le _ _
    have hmid : (1 / 4 : ℝ) ≤ ‖mid‖ := by linarith
    have hmid2 : (1 / 16 : ℝ) ≤ ‖mid‖ ^ 2 := by
      have := pow_le_pow_left₀ (by norm_num) hmid 2
      calc (1 / 16 : ℝ) = (1 / 4) ^ 2 := by norm_num
        _ ≤ ‖mid‖ ^ 2 := this
    exact hmid2.trans (dyadic_split U _)
  -- sum over the family
  have hbound := fun j => hdyad U hU j E (fun u hu => ⟨(hE u hu).1, (hE u hu).2.1⟩) β γ
    (fun u hu => ⟨(hsz u hu).2.1, (hshift_u u hu).1, (hsz u hu).2.2.1⟩)
  set J : ℝ := (dyadCount U : ℝ) with hJ
  set Bd : ℝ := K * (1 + 16 * Real.rpow U ρ) * (1 + (12 * Real.log U) ^ 2) ^ 2 *
    Real.rpow U (88 / 1000 + 34 * δ) with hBd
  have hJ0 : 0 ≤ J := by positivity
  have hsum : (E.card : ℝ) * (1 / 16) ≤ J * (J * Bd) := by
    calc (E.card : ℝ) * (1 / 16) = ∑ _u ∈ E, (1 / 16 : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ u ∈ E, J * ∑ j ∈ Finset.range (dyadCount U),
            ‖∑ I ∈ dyadIdeals U j, smoothedTerm U (β u) (γ u) (fd.omega u) I‖ ^ 2 :=
          Finset.sum_le_sum hdetect
      _ = J * ∑ j ∈ Finset.range (dyadCount U), ∑ u ∈ E,
            ‖∑ I ∈ dyadIdeals U j, smoothedTerm U (β u) (γ u) (fd.omega u) I‖ ^ 2 := by
          rw [← Finset.mul_sum, Finset.sum_comm]
      _ ≤ J * ∑ _j ∈ Finset.range (dyadCount U), Bd := by
          gcongr with j hj
          exact hbound j
      _ = J * (J * Bd) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hUρ1 : 1 ≤ Real.rpow U ρ := Real.one_le_rpow hU1le hρ.le
  have hlogb := hlog U hU
  have hexp_le : Real.rpow U (ε / 2) * Real.rpow U ρ * Real.rpow U (88 / 1000 + 34 * δ) ≤
      Real.rpow U p := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add hU0, ← Real.rpow_add hU0]
    exact Real.rpow_le_rpow_of_exponent_le hU1le (by rw [hpdef]; linarith)
  have hUe0 : 0 ≤ Real.rpow U (88 / 1000 + 34 * δ) := Real.rpow_nonneg hU0.le _
  have hfinal : (E.card : ℝ) ≤ 272 * K * Clog * Real.rpow U p := by
    have h1 : (E.card : ℝ) ≤ 16 * (J ^ 2 * Bd) := by
      have : J * (J * Bd) = J ^ 2 * Bd := by ring
      linarith
    have h2 : J ^ 2 * Bd ≤ K * 17 * Clog *
        (Real.rpow U (ε / 2) * Real.rpow U ρ * Real.rpow U (88 / 1000 + 34 * δ)) := by
      have hl : J ^ 2 * (1 + (12 * Real.log U) ^ 2) ^ 2 ≤ Clog * Real.rpow U (ε / 2) := hlogb
      have h16 : 1 + 16 * Real.rpow U ρ ≤ 17 * Real.rpow U ρ := by linarith
      calc J ^ 2 * Bd = K * (1 + 16 * Real.rpow U ρ) *
            (J ^ 2 * (1 + (12 * Real.log U) ^ 2) ^ 2) * Real.rpow U (88 / 1000 + 34 * δ) := by
            rw [hBd]; ring
        _ ≤ K * (17 * Real.rpow U ρ) * (Clog * Real.rpow U (ε / 2)) *
              Real.rpow U (88 / 1000 + 34 * δ) := by
            gcongr
        _ = _ := by ring
    have h3 := mul_le_mul_of_nonneg_left hexp_le (by positivity : (0 : ℝ) ≤ K * 17 * Clog)
    calc (E.card : ℝ) ≤ 16 * (J ^ 2 * Bd) := h1
      _ ≤ 16 * (K * 17 * Clog *
          (Real.rpow U (ε / 2) * Real.rpow U ρ * Real.rpow U (88 / 1000 + 34 * δ))) := by
          gcongr
      _ ≤ 16 * (K * 17 * Clog * Real.rpow U p) := by gcongr
      _ = 272 * K * Clog * Real.rpow U p := by ring
  have hCU : 0 ≤ Cc * U1' := by positivity
  calc (E.card : ℝ) ≤ 272 * K * Clog * Real.rpow U p := hfinal
    _ ≤ (272 * K * Clog + Cc * U1') * Real.rpow U p := by
        gcongr
        linarith

end ArtinPrimitiveRoots.A2.Proofs.A2ZeroDetect
