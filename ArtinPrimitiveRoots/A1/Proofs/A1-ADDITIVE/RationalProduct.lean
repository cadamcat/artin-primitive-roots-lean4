import ArtinPrimitiveRoots.A1.Proofs.«A1-ADDITIVE».RationalCharacter
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Nat.Factorization.Induction

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped BigOperators

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_bdata_sol

theorem rationalChar_product
    (θ : (v : HeightOneSpectrum (𝓞 ℚ)) → AddChar (v.adicCompletion ℚ) ℂ)
    (hθ : ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ),
      θ v x = 1 ↔ x ∈ v.adicCompletionIntegers ℚ)
    (hformula : ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (a : ℤ) (n : ℕ),
      θ v (algebraMap ℚ (v.adicCompletion ℚ)
        ((a : ℚ) / ((Rat.HeightOneSpectrum.primesEquiv v).1 : ℚ) ^ n)) =
      Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) /
        ((Rat.HeightOneSpectrum.primesEquiv v).1 : ℂ) ^ n)) (r : ℚ) :
    (Function.mulSupport fun v => θ v (algebraMap ℚ (v.adicCompletion ℚ) r)).Finite ∧
      (∏ᶠ v, θ v (algebraMap ℚ (v.adicCompletion ℚ) r)) *
        Complex.exp (-(2 * Real.pi * Complex.I * (r : ℂ))) = 1 := by
  classical
  let p (v : HeightOneSpectrum (𝓞 ℚ)) : ℕ :=
    (Rat.HeightOneSpectrum.primesEquiv v).1
  have hpinj : Function.Injective p := by
    intro v w h
    exact Rat.HeightOneSpectrum.primesEquiv.injective (Subtype.ext h)
  have hker (v : HeightOneSpectrum (𝓞 ℚ)) (s : ℚ) :
      θ v (algebraMap ℚ (v.adicCompletion ℚ) s) = 1 ↔ ¬ p v ∣ s.den := by
    let : Fact (p v).Prime := ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
    rw [hθ v _, HeightOneSpectrum.mem_adicCompletionIntegers]
    rw [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      v.valuedAdicCompletion_eq_valuation']
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
    exact (Rat.HeightOneSpectrum.valuation_equiv_padicValuation v).le_one_iff_le_one.trans
      Rat.padicValuation_le_one_iff
  have hfinite (s : ℚ) :
      (Function.mulSupport fun v => θ v (algebraMap ℚ (v.adicCompletion ℚ) s)).Finite := by
    refine ((Set.finite_Iic s.den).preimage hpinj.injOn).subset ?_
    intro v hv
    change θ v (algebraMap ℚ (v.adicCompletion ℚ) s) ≠ 1 at hv
    change p v ≤ s.den
    have hdiv : p v ∣ s.den := by
      by_contra h
      exact hv ((hker v s).mpr h)
    exact Nat.le_of_dvd s.pos hdiv
  let P (s : ℚ) : ℂ :=
    (∏ᶠ v, θ v (algebraMap ℚ (v.adicCompletion ℚ) s)) *
      Complex.exp (-(2 * Real.pi * Complex.I * (s : ℂ)))
  have hadd (s t : ℚ) : P (s + t) = P s * P t := by
    dsimp only [P]
    simp_rw [map_add, AddChar.map_add_eq_mul]
    rw [finprod_mul_distrib (hfinite s) (hfinite t)]
    rw [Rat.cast_add, mul_add, neg_add, Complex.exp_add]
    ring
  have hint (a : ℤ) : P (a : ℚ) = 1 := by
    have hlocal (v : HeightOneSpectrum (𝓞 ℚ)) :
        θ v (algebraMap ℚ (v.adicCompletion ℚ) (a : ℚ)) = 1 := by
      apply (hker v (a : ℚ)).mpr
      simpa only [Rat.den_intCast] using (Rat.HeightOneSpectrum.primesEquiv v).2.not_dvd_one
    dsimp only [P]
    rw [finprod_congr hlocal, finprod_one, one_mul]
    rw [Rat.cast_intCast]
    have he : -(2 * Real.pi * Complex.I * (a : ℂ)) =
        ((-a : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
    rw [he]
    exact Complex.exp_int_mul_two_pi_mul_I (-a)
  have hpp (q n : ℕ) (hq : q.Prime) (a : ℤ) :
      P ((a : ℚ) / (q : ℚ) ^ n) = 1 := by
    let v : HeightOneSpectrum (𝓞 ℚ) := Rat.HeightOneSpectrum.primesEquiv.symm ⟨q, hq⟩
    have hpv : p v = q := by
      exact congrArg Subtype.val (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply ⟨q, hq⟩)
    have hd : ((a : ℚ) / (q : ℚ) ^ n).den ∣ q ^ n := by
      have hz := Rat.den_dvd a ((q : ℤ) ^ n)
      rw [Rat.divInt_eq_div] at hz
      exact_mod_cast hz
    have haway (w : HeightOneSpectrum (𝓞 ℚ)) (hw : w ≠ v) :
        θ w (algebraMap ℚ (w.adicCompletion ℚ) ((a : ℚ) / (q : ℚ) ^ n)) = 1 := by
      apply (hker w _).mpr
      intro hden
      have hdiv : p w ∣ q :=
        (Rat.HeightOneSpectrum.primesEquiv w).2.dvd_of_dvd_pow (hden.trans hd)
      have heq : p w = q :=
        (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.primesEquiv w).2 hq).mp hdiv
      exact hw (hpinj (heq.trans hpv.symm))
    have hf := hformula v a n
    change θ v (algebraMap ℚ (v.adicCompletion ℚ) ((a : ℚ) / (p v : ℚ) ^ n)) =
      Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / (p v : ℂ) ^ n) at hf
    rw [hpv] at hf
    dsimp only [P]
    rw [finprod_eq_single _ v haway, hf, ← Complex.exp_add]
    convert Complex.exp_zero using 1
    congr 1
    push_cast
    ring
  have hall (b : ℕ) : ∀ a : ℤ, P ((a : ℚ) / (b : ℚ)) = 1 := by
    refine Nat.recOnPosPrimePosCoprime ?_ ?_ ?_ ?_ b
    · intro q n hq _ a
      simpa only [Nat.cast_pow] using hpp q n hq a
    · intro a
      simpa only [Nat.cast_zero, div_zero, Int.cast_zero] using hint 0
    · intro a
      simpa only [Nat.cast_one, div_one] using hint a
    · intro b c hb hc hcop hPb hPc a
      have hbez : (b : ℤ) * Nat.gcdA b c + (c : ℤ) * Nat.gcdB b c = 1 := by
        rw [← Nat.gcd_eq_gcd_ab, hcop.gcd_eq_one, Nat.cast_one]
      have hbezQ : (b : ℚ) * (Nat.gcdA b c : ℚ) +
          (c : ℚ) * (Nat.gcdB b c : ℚ) = 1 := by exact_mod_cast hbez
      have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
      have hc0 : (c : ℚ) ≠ 0 := by exact_mod_cast (by omega : c ≠ 0)
      have heq : (a : ℚ) / ((b * c : ℕ) : ℚ) =
          ((a * Nat.gcdB b c : ℤ) : ℚ) / (b : ℚ) +
          ((a * Nat.gcdA b c : ℤ) : ℚ) / (c : ℚ) := by
        push_cast
        field_simp
        linear_combination -(a : ℚ) * hbezQ
      rw [heq, hadd, hPb, hPc, one_mul]
  refine ⟨hfinite r, ?_⟩
  change P r = 1
  simpa only [Rat.num_div_den] using hall r.den r.num

end ArtinPrimitiveRoots.Proofs.a1_bdata_sol
