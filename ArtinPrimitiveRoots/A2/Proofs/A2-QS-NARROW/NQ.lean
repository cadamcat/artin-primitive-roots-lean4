import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-BOOT».Boot
import ArtinPrimitiveRoots.A1.Residue
import ArtinPrimitiveRoots.Proofs.qs_nq0_sol.Generators

/-!
# A2-QS-NARROW: canonical narrow family, representatives, and the three frozen endpoints

Guide: `runs/lanes/sol-thin-found/PROOFS.md:585-602` (NQ0-NQ2), III.10 (found:604-621, G0-G3),
`runs/lanes/sol-thin-a2rp/PROOFS.md:348-388`.

Route decision (lead): the narrow theorem is glued directly from the core
(`qs_core_large_sieve_B2`) through the canonical narrow family (NQ0, trivial ray factor,
`qS ≠ ⊥`, totally complex by `μ₁₂`), not through the general `ext_goldmakher_louvel`.  The
general family theorem needs, beyond the core, the qS/profile reduction (G0), the ray-factor
generalisation of `qs_family_mul_S0`/C2 (G1) and the real-place gamma factors (G2); these are
stated as two deferred SOL-LEAD units off the narrow critical path.  `ext_heath_brown_quadratic`
(over `ℚ`, totally real, nontrivial ray factor) goes through the general theorem.
-/

set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain
open ClassFieldTheory

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]

/-! ### Narrow route -/

/-- NQ (IMPL): a field with a primitive 12th (indeed 4th) root of unity is totally complex. -/
theorem qs_totallyComplex_of_mu12_NQ (hμ : ∃ ζ : K, IsPrimitiveRoot ζ 12) :
    IsTotallyComplex K := by
  sorry

/-- NQ0 (SOL-LEAD; RETIER `qs_canonical_family_NQ0`, found:585-592): enlarge `S` to `S'`
(primes over 6, the different, class-group generators; `O_{S'}` a PID), build the canonical
allowed family `Ξ_c = κ_{a_c}^3` on squarefree `S'`-exterior ideals with ray modulus supported
on `S'`, trivial ray factor, exact conductors `c s_c`, `s_c ∣ qS ≠ ⊥`, exact product conductor
`c d` on equal classes, and integral exterior representatives `gen₀` (allowed generators times
an even power of an `S'`-supported integer) whose quadratic symbols are the family values. -/
theorem qs_canonical_family_NQ0 (hμ : ∃ ζ : K, IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    ∃ (S' : Finset (HeightOneSpectrum (𝓞 K))) (m : ClassFieldTheory.RayClassModulus K)
      (qS : Ideal (𝓞 K)) (F : QSFamily m qS)
      (gen₀ : Finset (HeightOneSpectrum (𝓞 K)) → 𝓞 K),
      S ⊆ S' ∧ qS ≠ ⊥ ∧ (∀ g h, F.rayFactor g h = 1) ∧
      (∀ T : Finset (HeightOneSpectrum (𝓞 K)), Disjoint T S' →
        QSAdm m qS (qsIdealOf T) ∧ qsIsExteriorGenerator S' T (gen₀ T)) ∧
      (∀ T D : Finset (HeightOneSpectrum (𝓞 K)), Disjoint T S' → Disjoint D S' →
        (F.character (qsIdealOf T)).idealValue (qsIdealOf D) = (qsQuadSymbol D (gen₀ T) : ℂ)) := by
  sorry

/-- NQ0a (IMPL): the core bound transported to finite prime supports
(`T ↦ ∏_{v∈T} 𝔭_v` is injective on finite sets of primes, `N(qsIdealOf T) = qsNormT T`;
`qs_finite_energy_of_core_M0`). -/
theorem qs_core_symbol_bound_NQ0a (S' : Finset (HeightOneSpectrum (𝓞 K)))
    (m : ClassFieldTheory.RayClassModulus K) (qS : Ideal (𝓞 K)) (F : QSFamily m qS)
    (gen₀ : Finset (HeightOneSpectrum (𝓞 K)) → 𝓞 K)
    (hadm : ∀ T : Finset (HeightOneSpectrum (𝓞 K)), Disjoint T S' → QSAdm m qS (qsIdealOf T))
    (hsym : ∀ T D : Finset (HeightOneSpectrum (𝓞 K)), Disjoint T S' → Disjoint D S' →
      (F.character (qsIdealOf T)).idealValue (qsIdealOf D) = (qsQuadSymbol D (gen₀ T) : ℂ))
    (hcore : QSCoreBound F) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (Cmax Dmax : ℝ), 1 ≤ Cmax → 1 ≤ Dmax →
      ∀ (cols rows : Finset (Finset (HeightOneSpectrum (𝓞 K)))),
        (∀ T ∈ cols, Disjoint T S' ∧ (qsNormT T : ℝ) ≤ Cmax) →
        (∀ T ∈ rows, Disjoint T S' ∧ (qsNormT T : ℝ) ≤ Dmax) →
        ∀ z : Finset (HeightOneSpectrum (𝓞 K)) → ℂ,
          ∑ D ∈ rows, ‖∑ T ∈ cols, z T * (qsQuadSymbol D (gen₀ T) : ℂ)‖ ^ 2 ≤
            C * (Cmax + Dmax) * (Cmax * Dmax) ^ ε * ∑ T ∈ cols, ‖z T‖ ^ 2 := by
  sorry

/-- NQ1 (IMPL; found:593-598): arbitrary integral representatives and the smaller set `S`.
Split rows and columns by their (finitely many) intersections with `S' \ S` (deletion is
injective and lowers norms; the deleted symbols are diagonal twists in `{0, ±1}`), and columns
by the class of `gen T / gen₀ (T \ S')` in the finite group `U_{S'}/U_{S'}²` (a row twist of
modulus `≤ 1`); recombine by Cauchy–Schwarz.  Constants depend on `K, S, S', ε` only. -/
theorem qs_arbitrary_representatives_NQ1 (hμ : ∃ ζ : K, IsPrimitiveRoot ζ 12)
    (S S' : Finset (HeightOneSpectrum (𝓞 K))) (hSS' : S ⊆ S')
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (gen₀ : Finset (HeightOneSpectrum (𝓞 K)) → 𝓞 K)
    (hgen₀ : ∀ T : Finset (HeightOneSpectrum (𝓞 K)), Disjoint T S' →
      qsIsExteriorGenerator S' T (gen₀ T))
    (hbound : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (Cmax Dmax : ℝ), 1 ≤ Cmax → 1 ≤ Dmax →
      ∀ (cols rows : Finset (Finset (HeightOneSpectrum (𝓞 K)))),
        (∀ T ∈ cols, Disjoint T S' ∧ (qsNormT T : ℝ) ≤ Cmax) →
        (∀ T ∈ rows, Disjoint T S' ∧ (qsNormT T : ℝ) ≤ Dmax) →
        ∀ z : Finset (HeightOneSpectrum (𝓞 K)) → ℂ,
          ∑ D ∈ rows, ‖∑ T ∈ cols, z T * (qsQuadSymbol D (gen₀ T) : ℂ)‖ ^ 2 ≤
            C * (Cmax + Dmax) * (Cmax * Dmax) ^ ε * ∑ T ∈ cols, ‖z T‖ ^ 2) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (Cmax Dmax : ℝ), 1 ≤ Cmax → 1 ≤ Dmax →
      ∀ (gen : Finset (HeightOneSpectrum (𝓞 K)) → 𝓞 K)
        (cols rows : Finset (Finset (HeightOneSpectrum (𝓞 K)))),
        (∀ T ∈ cols, Disjoint T S ∧ (qsNormT T : ℝ) ≤ Cmax ∧ qsIsExteriorGenerator S T (gen T)) →
        (∀ T ∈ rows, Disjoint T S ∧ (qsNormT T : ℝ) ≤ Dmax) →
        ∀ z : Finset (HeightOneSpectrum (𝓞 K)) → ℂ,
          ∑ D ∈ rows, ‖∑ T ∈ cols, z T * (qsQuadSymbol D (gen T) : ℂ)‖ ^ 2 ≤
            C * (Cmax + Dmax) * (Cmax * Dmax) ^ ε * ∑ T ∈ cols, ‖z T‖ ^ 2 := by
  sorry

/-- The narrow theorem in the mirrored vocabulary (glue, proved here from the parts); the
frozen `narrow_quadratic_large_sieve` is this statement up to unfolding the copied
definitions. -/
theorem qs_narrow_large_sieve (hμ : ∃ ζ : K, IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (Cmax Dmax : ℝ), 1 ≤ Cmax → 1 ≤ Dmax →
      ∀ (gen : Finset (HeightOneSpectrum (𝓞 K)) → 𝓞 K)
        (cols rows : Finset (Finset (HeightOneSpectrum (𝓞 K)))),
        (∀ T ∈ cols, Disjoint T S ∧ (qsNormT T : ℝ) ≤ Cmax ∧ qsIsExteriorGenerator S T (gen T)) →
        (∀ T ∈ rows, Disjoint T S ∧ (qsNormT T : ℝ) ≤ Dmax) →
        ∀ z : Finset (HeightOneSpectrum (𝓞 K)) → ℂ,
          ∑ D ∈ rows, ‖∑ T ∈ cols, z T * (qsQuadSymbol D (gen T) : ℂ)‖ ^ 2 ≤
            C * (Cmax + Dmax) * (Cmax * Dmax) ^ ε * ∑ T ∈ cols, ‖z T‖ ^ 2 := by
  obtain ⟨S', m, qS, F, gen₀, hSS', hqS, hrf, hadm, hsym⟩ := qs_canonical_family_NQ0 hμ S hS
  haveI : IsTotallyComplex K := qs_totallyComplex_of_mu12_NQ hμ
  exact qs_arbitrary_representatives_NQ1 hμ S S' hSS' hS gen₀ (fun T hT => (hadm T hT).2)
    (qs_core_symbol_bound_NQ0a S' m qS F gen₀ (fun T hT => (hadm T hT).1) hsym
      (qs_core_large_sieve_B2 F hrf hqS))

/-- NQ2 (IMPL; consumer helper for `lem_reflection_quadratic_sieve`, found:599-602 and
`runs/lanes/sol-thin-a2rp/PROOFS.md:374-382`; schema `IntegralSquareClearing` in
`runs/lanes/sol-thin-a2rp/wt/ArtinPrimitiveRoots/Review/sol-thin-a2rp/Schemas.lean:23-28`):
an `S`-integer becomes integral after multiplying by the square of an integer supported on `S`
(class-group finiteness: a power of each prime of `S` is principal). -/
theorem qs_integralize_generators_NQ2 {CE : ℕ} {condη : Ideal (𝓞 K)}
    (S : ArtinPrimitiveRoots.A1.SData K CE condη) :
    ∀ c : Kˣ, (c : K) ∈ S.R → ∃ b : 𝓞 K, b ≠ 0 ∧
      (∀ v : ArtinPrimitiveRoots.A1.FinPlace K, v ∉ S.Sf →
        ArtinPrimitiveRoots.A1.residue v (b : K) ≠ 0) ∧
      ∃ a : 𝓞 K, (a : K) = (c : K) * (b : K) ^ 2 := by
  sorry

/-! ### General family route (off the narrow critical path) -/

/-- G0+G1 (SOL-LEAD, deferred): the general family theorem over a totally complex field
(found:606-616): arbitrary ray factor (class-dependent unitary row twists in
`qs_family_mul_S0`/C2 and in the duality, constant `h⁴`), arbitrary `qS` including `⊥`
(fixed ramification profiles, uniform conductor bound), rows and columns not coprime to `qS`.
Whole-theorem-sized: it re-runs the core with twisted multiplicativity. -/
theorem qs_general_totally_complex_G01 [IsTotallyComplex K]
    (m : ClassFieldTheory.RayClassModulus K) (qS : Ideal (𝓞 K)) (F : QSFamily m qS) :
    QSFamilyBound F := by
  sorry

/-- G2 (SOL-LEAD, deferred): the general family theorem over a field with a real place
(found:616-617): needs the primitive FE and root number `+1` with `Γ_ℝ(s)^{r₁}Γ_ℂ(s)^{r₂}`
(the Hecke layer is totally complex only) and the P0-P2 bounds for that gamma factor. -/
theorem qs_general_real_places_G2 (hK : ¬ IsTotallyComplex K)
    (m : ClassFieldTheory.RayClassModulus K) (qS : Ideal (𝓞 K)) (F : QSFamily m qS) :
    QSFamilyBound F := by
  sorry

/-- The general family theorem for the mirrored record (glue, proved here). -/
theorem qs_goldmakher_louvel (m : ClassFieldTheory.RayClassModulus K) (qS : Ideal (𝓞 K))
    (F : QSFamily m qS) : QSFamilyBound F := by
  by_cases hK : IsTotallyComplex K
  · haveI := hK
    exact qs_general_totally_complex_G01 m qS F
  · exact qs_general_real_places_G2 hK m qS F

/-! ### Rational specialisation (Heath-Brown) -/

open Classical in
/-- Copy of the frozen `rationalQuadraticSymbol` (`A2/QuadraticSieve.lean:159-165`). -/
def qsRationalQuadraticSymbol (a p : ℕ) : ℤ :=
  if hp : p.Prime then
    letI : Fact p.Prime := ⟨hp⟩
    quadraticChar (ZMod p) (a : ZMod p)
  else 1

open Classical in
/-- Copy of the frozen `rationalJacobiSymbol`. -/
def qsRationalJacobiSymbol (a m : ℕ) : ℤ :=
  ∏ p ∈ m.primeFactors, qsRationalQuadraticSymbol a p

open Classical in
/-- Copy of the frozen `oddSquarefreeUpTo`. -/
def qsOddSquarefreeUpTo (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun n => n % 2 = 1 ∧ Squarefree n)

/-- HB0 (SOL-LEAD, deferred; a2rp guide 384-388): the primitive quadratic Jacobi family over
`ℚ` with modulus `4` (characters of `ℚ(√n)`, conductor `n` or `4n`, reciprocity factor the
mod-4 sign) as a mirrored family whose values are the Jacobi symbols. -/
theorem qs_rational_jacobi_family_HB :
    ∃ (m : ClassFieldTheory.RayClassModulus ℚ) (qS : Ideal (𝓞 ℚ)) (F : QSFamily m qS),
      (∀ n : ℕ, n % 2 = 1 → Squarefree n →
        Squarefree (Ideal.span {(n : 𝓞 ℚ)}) ∧
          ArtinPrimitiveRoots.Hecke.IsCoprimeTo m (Ideal.span {(n : 𝓞 ℚ)})) ∧
      (∀ n k : ℕ, n % 2 = 1 → Squarefree n → k % 2 = 1 → Squarefree k →
        (F.character (Ideal.span {(n : 𝓞 ℚ)})).idealValue (Ideal.span {(k : 𝓞 ℚ)}) =
          (qsRationalJacobiSymbol n k : ℂ)) := by
  sorry

/-- HB1 (IMPL): the family theorem for the rational Jacobi family gives Heath-Brown's bound
(identify odd squarefree integers with their ideals; `absNorm (span {n}) = n`). -/
theorem qs_heath_brown_of_family_HB (m : ClassFieldTheory.RayClassModulus ℚ)
    (qS : Ideal (𝓞 ℚ)) (F : QSFamily m qS)
    (hadm : ∀ n : ℕ, n % 2 = 1 → Squarefree n →
      Squarefree (Ideal.span {(n : 𝓞 ℚ)}) ∧
        ArtinPrimitiveRoots.Hecke.IsCoprimeTo m (Ideal.span {(n : 𝓞 ℚ)}))
    (hval : ∀ n k : ℕ, n % 2 = 1 → Squarefree n → k % 2 = 1 → Squarefree k →
      (F.character (Ideal.span {(n : 𝓞 ℚ)})).idealValue (Ideal.span {(k : 𝓞 ℚ)}) =
        (qsRationalJacobiSymbol n k : ℂ))
    (hF : QSFamilyBound F) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ M N : ℕ, 1 ≤ M → 1 ≤ N → ∀ a : ℕ → ℂ,
        (∑ m ∈ qsOddSquarefreeUpTo M,
          ‖∑ n ∈ qsOddSquarefreeUpTo N,
            a n * (qsRationalJacobiSymbol n m : ℂ)‖ ^ 2) ≤
          C * Real.rpow ((M : ℝ) * N) ε * (M + N) *
            ∑ n ∈ qsOddSquarefreeUpTo N, ‖a n‖ ^ 2 := by
  sorry

/-- Heath-Brown in the mirrored vocabulary (glue, proved here). -/
theorem qs_heath_brown :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ M N : ℕ, 1 ≤ M → 1 ≤ N → ∀ a : ℕ → ℂ,
        (∑ m ∈ qsOddSquarefreeUpTo M,
          ‖∑ n ∈ qsOddSquarefreeUpTo N,
            a n * (qsRationalJacobiSymbol n m : ℂ)‖ ^ 2) ≤
          C * Real.rpow ((M : ℝ) * N) ε * (M + N) *
            ∑ n ∈ qsOddSquarefreeUpTo N, ‖a n‖ ^ 2 := by
  obtain ⟨m, qS, F, hadm, hval⟩ := qs_rational_jacobi_family_HB
  exact qs_heath_brown_of_family_HB m qS F hadm hval (qs_goldmakher_louvel m qS F)

end ArtinPrimitiveRoots.A2
