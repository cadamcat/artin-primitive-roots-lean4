import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GlobalSupport
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GlobalReindex
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.TraceDiagonal
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.TraceArch
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.TraceTransfer
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.RationalProduct

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

private theorem wi_tracePrime_finiteSupport {a : Fˣ} (T : QuadraticTraceDiagonal a) :
    (Function.mulSupport fun p : Nat.Primes => tracePrimePhase T p).Finite := by
  classical
  change Function.HasFiniteMulSupport
    (fun p : Nat.Primes => tracePrimePhase T p)
  unfold tracePrimePhase
  exact Function.HasFiniteMulSupport.prod
    (f := fun i p => rationalPrimePhase p (T.coeff i))
    (fun i => (rational_phase_product (T.coeff i)).1) Finset.univ

private theorem wi_tracePrime_product_eq_one {a : Fˣ} (T : QuadraticTraceDiagonal a)
    (harch : traceArchPhase T = 1) :
    ∏ᶠ p : Nat.Primes, tracePrimePhase T p = 1 := by
  classical
  have hswap :
      (∏ᶠ p : Nat.Primes, tracePrimePhase T p) =
        ∏ i : Fin (Module.finrank ℚ F),
          ∏ᶠ p : Nat.Primes, rationalPrimePhase p (T.coeff i) := by
    simpa [tracePrimePhase] using
      (finprod_prod_comm (Finset.univ : Finset (Fin (Module.finrank ℚ F)))
        (fun p i => rationalPrimePhase p (T.coeff i))
        (by
          intro i hi
          exact (rational_phase_product (T.coeff i)).1))
  rw [hswap]
  calc
    (∏ i : Fin (Module.finrank ℚ F),
        ∏ᶠ p : Nat.Primes, rationalPrimePhase p (T.coeff i)) =
      ∏ i : Fin (Module.finrank ℚ F), (rationalArchPhase (T.coeff i))⁻¹ := by
        apply Finset.prod_congr rfl
        intro i hi
        exact eq_inv_of_mul_eq_one_left (rational_phase_product (T.coeff i)).2
    _ = (traceArchPhase T)⁻¹ := by
      simp [traceArchPhase, Finset.prod_inv_distrib]
    _ = 1 := by rw [harch]; simp

/-- Assemble the global quadratic index product from trace transfer and rational reciprocity.
Guide: PROOFS.md:480–485. Uses: global_index_finite_support; global_index_prime_fibers; quadratic_trace_transfer; quadratic_trace_arch_phase_one; rational_phase_product. -/
theorem weil_product (D : FieldData F) (A : AddCharData F)
    (W : LocalGaussianData A) : ∀ a : Fˣ,
      (Function.mulSupport fun v => W.index v (toLoc v a)).Finite ∧
        ∏ᶠ v, W.index v (toLoc v a) = 1 := by
  intro a
  classical
  obtain ⟨T⟩ := quadratic_trace_diagonal_exists a
  obtain ⟨T1⟩ := quadratic_trace_diagonal_exists (1 : Fˣ)
  have hsupport := global_index_finite_support D A W a
  have harch : traceArchPhase T = 1 := quadratic_trace_arch_phase_one D a T
  have harch1 : traceArchPhase T1 = 1 := quadratic_trace_arch_phase_one D 1 T1
  have hphaseSupport := wi_tracePrime_finiteSupport T
  have hphaseSupport1 := wi_tracePrime_finiteSupport T1
  have hphaseProduct := wi_tracePrime_product_eq_one T harch
  have hphaseProduct1 := wi_tracePrime_product_eq_one T1 harch1
  have hratio :
      ∏ᶠ p : Nat.Primes, tracePrimePhase T p / tracePrimePhase T1 p = 1 := by
    rw [finprod_div_distrib hphaseSupport hphaseSupport1, hphaseProduct, hphaseProduct1]
    simp
  have hcomplex :
      ∏ᶠ v : FinPlace F, ((W.index v (toLoc v a) : ℂˣ) : ℂ) = 1 := by
    calc
      (∏ᶠ v : FinPlace F, ((W.index v (toLoc v a) : ℂˣ) : ℂ)) =
          ∏ᶠ p : Nat.Primes, primeFiberIndex W p a :=
        global_index_prime_fibers A W a hsupport
      _ = ∏ᶠ p : Nat.Primes, tracePrimePhase T p / tracePrimePhase T1 p := by
        apply finprod_congr
        intro p
        exact quadratic_trace_transfer D A W a T T1 p
      _ = 1 := hratio
  have hunit : ∏ᶠ v : FinPlace F, W.index v (toLoc v a) = 1 := by
    apply Units.ext
    calc
      ((∏ᶠ v : FinPlace F, W.index v (toLoc v a) : ℂˣ) : ℂ) =
          ∏ᶠ v : FinPlace F, ((W.index v (toLoc v a) : ℂˣ) : ℂ) :=
        (Units.coeHom ℂ).map_finprod hsupport
      _ = 1 := hcomplex
  exact ⟨hsupport, hunit⟩

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
