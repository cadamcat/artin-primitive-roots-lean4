import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-BOOT».Boot
import ArtinPrimitiveRoots.A1.Residue

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
open scoped nonZeroDivisors Classical

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]

/-! ### Narrow route -/

/-- NQ (IMPL): a field with a primitive 12th (indeed 4th) root of unity is totally complex. -/
theorem qs_totallyComplex_of_mu12_NQ (hμ : ∃ ζ : K, IsPrimitiveRoot ζ 12) :
    IsTotallyComplex K := by
  obtain ⟨ζ, hζ⟩ := hμ
  refine ⟨fun v => ?_⟩
  rw [InfinitePlace.isComplex_iff]
  intro hreal
  let ι : K →+* ℝ := hreal.embedding
  have hprim : IsPrimitiveRoot (ι ζ) 12 :=
    IsPrimitiveRoot.map_of_injective (f := ι) hζ (RingHom.injective ι)
  have hsq : ((ι ζ) ^ 6) ^ 2 = 1 := by
    calc
      ((ι ζ) ^ 6) ^ 2 = (ι ζ) ^ (6 * 2) := by rw [pow_mul]
      _ = (ι ζ) ^ 12 := by norm_num
      _ = 1 := hprim.pow_eq_one
  have hnonneg : 0 ≤ (ι ζ) ^ 6 := by positivity
  rcases sq_eq_one_iff.mp hsq with h | h
  · exact hprim.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num) h
  · have : (ι ζ) ^ 6 = -1 := h
    linarith

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
  classical
  have hnorm (T : Finset (HeightOneSpectrum (𝓞 K))) :
      Ideal.absNorm (qsIdealOf T) = qsNormT T := by
    simp [qsIdealOf, qsNormT]
  have hmem_iff (T : Finset (HeightOneSpectrum (𝓞 K)))
      (v : HeightOneSpectrum (𝓞 K)) :
      v ∈ T ↔ qsIdealOf T ≤ v.asIdeal := by
    constructor
    · intro hv
      rw [qsIdealOf, v.isPrime.prod_le]
      exact ⟨v, hv, le_rfl⟩
    · intro h
      have h' : (∏ w ∈ T, w.asIdeal) ≤ v.asIdeal := by simpa [qsIdealOf] using h
      obtain ⟨w, hw, hwv⟩ := v.isPrime.prod_le.mp h'
      have heq : w.asIdeal = v.asIdeal := w.isMaximal.eq_of_le v.isPrime.ne_top hwv
      have : w = v := HeightOneSpectrum.ext heq
      simpa [this] using hw
  have hIdealInj : Function.Injective (qsIdealOf (K := K)) := by
    intro T U hTU
    apply Finset.ext
    intro v
    rw [hmem_iff, hmem_iff, hTU]
  intro ε hε
  obtain ⟨C, hC, hfinite⟩ := qs_finite_energy_of_core_M0 F hcore ε hε
  refine ⟨C, hC, ?_⟩
  intro Cmax Dmax hCmax hDmax cols rows hcols hrows z
  let rowsI : Finset (Ideal (𝓞 K)) := rows.image qsIdealOf
  let colsI : Finset (Ideal (𝓞 K)) := cols.image qsIdealOf
  let zI : Ideal (𝓞 K) → ℂ := fun I => ∑ T ∈ cols, if qsIdealOf T = I then z T else 0
  have hrowsI (I : Ideal (𝓞 K)) (hI : I ∈ rowsI) :
      QSAdm m qS I ∧ (Ideal.absNorm I : ℝ) ≤ Dmax := by
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hI
    obtain ⟨hdisj, hnormD⟩ := hrows D hD
    refine ⟨hadm D hdisj, ?_⟩
    rw [hnorm]
    exact hnormD
  have hcolsI (I : Ideal (𝓞 K)) (hI : I ∈ colsI) :
      QSAdm m qS I ∧ (Ideal.absNorm I : ℝ) ≤ Cmax := by
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hI
    obtain ⟨hdisj, hnormT⟩ := hcols T hT
    refine ⟨hadm T hdisj, ?_⟩
    rw [hnorm]
    exact hnormT
  have hzI (T : Finset (HeightOneSpectrum (𝓞 K))) (hT : T ∈ cols) :
      zI (qsIdealOf T) = z T := by
    dsimp [zI]
    rw [Finset.sum_eq_single_of_mem T hT]
    · simp
    · intro U hU hUT
      have hne : qsIdealOf U ≠ qsIdealOf T := by
        intro heq
        exact hUT (hIdealInj heq)
      simp [hne]
  have henergy := hfinite Cmax Dmax hCmax hDmax rowsI colsI hrowsI hcolsI zI
  have hrowinj : Set.InjOn qsIdealOf rows := hIdealInj.injOn
  have hcolinj : Set.InjOn qsIdealOf cols := hIdealInj.injOn
  have hsumInner (D : Finset (HeightOneSpectrum (𝓞 K))) (hD : D ∈ rows) :
      (∑ J ∈ colsI, zI J * (F.character J).idealValue (qsIdealOf D)) =
        ∑ T ∈ cols, z T * (qsQuadSymbol D (gen₀ T) : ℂ) := by
    rw [Finset.sum_image hcolinj]
    refine Finset.sum_congr rfl ?_
    intro T hT
    rw [hzI T hT, hsym T D (hcols T hT).1 (hrows D hD).1]
  have hsumRows :
      (∑ I ∈ rowsI, ‖∑ J ∈ colsI, zI J * (F.character J).idealValue I‖ ^ 2) =
        ∑ D ∈ rows, ‖∑ T ∈ cols, z T * (qsQuadSymbol D (gen₀ T) : ℂ)‖ ^ 2 := by
    rw [Finset.sum_image hrowinj]
    refine Finset.sum_congr rfl ?_
    intro D hD
    exact congrArg (fun x : ℂ => ‖x‖ ^ 2) (hsumInner D hD)
  have hsumCoeff :
      (∑ I ∈ colsI, ‖zI I‖ ^ 2) = ∑ T ∈ cols, ‖z T‖ ^ 2 := by
    rw [Finset.sum_image hcolinj]
    refine Finset.sum_congr rfl ?_
    intro T hT
    rw [hzI T hT]
  rw [hsumRows, hsumCoeff] at henergy
  exact henergy

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

private theorem qs_fractional_count_span_power_NQ2
    (v w : HeightOneSpectrum (𝓞 K)) (n : ℕ) {a : 𝓞 K}
    (ha : Ideal.span {a} = v.asIdeal ^ n) :
    FractionalIdeal.count K w (Ideal.span {a} : FractionalIdeal (𝓞 K)⁰ K) =
      if w = v then n else 0 := by
  classical
  rw [ha, FractionalIdeal.coeIdeal_pow]
  by_cases hwv : w = v
  · subst w
    simpa using (FractionalIdeal.count_pow_self K v n)
  · have hvw : v ≠ w := Ne.symm hwv
    rw [FractionalIdeal.count_pow, FractionalIdeal.count_maximal_coprime K w hvw]
    simp [hwv]

private theorem qs_valuation_eq_exp_neg_fractional_count_NQ2
    (v : HeightOneSpectrum (𝓞 K)) {a : 𝓞 K} (ha : a ≠ 0) :
    v.valuation K (a : K) =
      WithZero.exp (-FractionalIdeal.count K v
        (Ideal.span {a} : FractionalIdeal (𝓞 K)⁰ K)) := by
  rw [v.valuation_of_algebraMap, v.intValuation_if_neg ha]
  congr 1
  have hspan : Ideal.span {a} ≠ ⊥ := by
    intro h
    exact ha (Ideal.span_singleton_eq_bot.mp h)
  have hfrac : (Ideal.span {a} : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr hspan
  rw [FractionalIdeal.count_well_defined K v hfrac (a := 1)
    (J := Ideal.span {a}) (by simp)]
  rw [Ideal.span_singleton_one, ← Ideal.one_eq_top, Associates.mk_one,
    Associates.factors_one, Associates.count_zero v.associates_irreducible]
  ring

private theorem qs_residue_ne_zero_of_not_mem_NQ2 (v : ArtinPrimitiveRoots.A1.FinPlace K)
    {a : 𝓞 K} (ha : a ∉ v.asIdeal) :
    ArtinPrimitiveRoots.A1.residue v (a : K) ≠ 0 := by
  let hx : ∃ ab : 𝓞 K × 𝓞 K, ab.2 ∉ v.asIdeal ∧
      (a : K) * algebraMap (𝓞 K) K ab.2 = algebraMap (𝓞 K) K ab.1 :=
    ⟨(a, 1), by
      intro h
      exact v.isMaximal.ne_top ((Ideal.eq_top_iff_one _).mpr h), by simp⟩
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  unfold ArtinPrimitiveRoots.A1.residue
  rw [dif_pos hx]
  have hspec := hx.choose_spec
  have hd : Ideal.Quotient.mk v.asIdeal hx.choose.2 ≠ 0 := by
    intro hz
    exact hspec.1 (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  have hmulK : algebraMap (𝓞 K) K (a * hx.choose.2) = algebraMap (𝓞 K) K hx.choose.1 := by
    simpa [map_mul] using hspec.2
  have hmul : a * hx.choose.2 = hx.choose.1 :=
    (IsFractionRing.injective (𝓞 K) K) hmulK
  have hnum : Ideal.Quotient.mk v.asIdeal hx.choose.1 =
      Ideal.Quotient.mk v.asIdeal a * Ideal.Quotient.mk v.asIdeal hx.choose.2 := by
    calc
      Ideal.Quotient.mk v.asIdeal hx.choose.1 =
          Ideal.Quotient.mk v.asIdeal (a * hx.choose.2) := by rw [hmul]
      _ = Ideal.Quotient.mk v.asIdeal a * Ideal.Quotient.mk v.asIdeal hx.choose.2 := map_mul _ _ _
  have hres : Ideal.Quotient.mk v.asIdeal hx.choose.1 *
      (Ideal.Quotient.mk v.asIdeal hx.choose.2)⁻¹ = Ideal.Quotient.mk v.asIdeal a := by
    rw [hnum]
    simp [mul_assoc, hd]
  change Ideal.Quotient.mk v.asIdeal hx.choose.1 *
      (Ideal.Quotient.mk v.asIdeal hx.choose.2)⁻¹ ≠ 0
  rw [hres]
  intro hz
  exact ha (Ideal.Quotient.eq_zero_iff_mem.mp hz)

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
  classical
  intro c hR
  let h : ℕ := Fintype.card (ClassGroup (𝓞 K))
  have hh : 0 < h := by
    dsimp [h]
    exact (Fintype.card_pos : 0 < Fintype.card (ClassGroup (𝓞 K)))
  have hpower (v : ArtinPrimitiveRoots.A1.FinPlace K) :
      ∃ a : 𝓞 K, Ideal.span {a} = v.asIdeal ^ h := by
    let p₀ : (Ideal (𝓞 K))⁰ :=
      ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩
    have hClass : ClassGroup.mk0 p₀ ^ h = 1 := by
      simpa [h, p₀] using (pow_card_eq_one (x := ClassGroup.mk0 p₀))
    have hpow0 : v.asIdeal ^ h ≠ ⊥ := pow_ne_zero _ v.ne_bot
    have hClassPow :
        ClassGroup.mk0 ⟨v.asIdeal ^ h, mem_nonZeroDivisors_iff_ne_zero.mpr hpow0⟩ = 1 := by
      change ClassGroup.mk0 (p₀ ^ h) = 1
      rw [map_pow]
      exact hClass
    have hPrincipal : (v.asIdeal ^ h).IsPrincipal :=
      (ClassGroup.mk0_eq_one_iff (mem_nonZeroDivisors_iff_ne_zero.mpr hpow0)).mp hClassPow
    obtain ⟨a, ha⟩ := hPrincipal.principal
    exact ⟨a, ha.symm⟩
  let π : ArtinPrimitiveRoots.A1.FinPlace K → 𝓞 K := fun v => Classical.choose (hpower v)
  have hπ (v : ArtinPrimitiveRoots.A1.FinPlace K) : Ideal.span {π v} = v.asIdeal ^ h :=
    Classical.choose_spec (hpower v)
  have hπ_ne (v : ArtinPrimitiveRoots.A1.FinPlace K) : π v ≠ 0 := by
    intro hz
    have hpow0 : v.asIdeal ^ h ≠ ⊥ := pow_ne_zero _ v.ne_bot
    apply hpow0
    calc
      v.asIdeal ^ h = Ideal.span {π v} := (hπ v).symm
      _ = ⊥ := by simp [hz]
  let e : ℕ := ∑ v ∈ S.Sf, (WithZero.log (v.valuation K (c : K))).toNat
  let b : 𝓞 K := ∏ v ∈ S.Sf, (π v) ^ e
  have hb_ne : b ≠ 0 := by
    dsimp [b]
    apply Finset.prod_ne_zero_iff.mpr
    intro v hv
    exact pow_ne_zero _ (hπ_ne v)
  have hvalπ (w v : ArtinPrimitiveRoots.A1.FinPlace K) :
      w.valuation K (π v : K) = if w = v then WithZero.exp (-(h : ℤ)) else 1 := by
    rw [qs_valuation_eq_exp_neg_fractional_count_NQ2 w (hπ_ne v),
      qs_fractional_count_span_power_NQ2 v w h (hπ v)]
    by_cases hwv : w = v <;> simp [hwv]
  have hvalb (w : ArtinPrimitiveRoots.A1.FinPlace K) :
      w.valuation K (b : K) =
        if w ∈ S.Sf then WithZero.exp ((e : ℕ) • (-(h : ℤ))) else 1 := by
    dsimp [b]
    change w.valuation K
      (algebraMap (𝓞 K) K (∏ v ∈ S.Sf, (π v) ^ e)) = _
    rw [map_prod, map_prod]
    simp_rw [map_pow]
    by_cases hw : w ∈ S.Sf
    · rw [if_pos hw, Finset.prod_eq_single w]
      · rw [hvalπ]
        by_cases hEq : w = w
        · rw [if_pos hEq]
          rw [← WithZero.exp_nsmul]
          congr 1
        · exact False.elim (hEq rfl)
      · intro v hv hne
        rw [hvalπ]
        have hwv : w ≠ v := by
          intro hEq
          exact hne hEq.symm
        simp [hwv]
      · intro hnot
        exact (hnot hw).elim
    · rw [if_neg hw, Finset.prod_eq_one]
      intro v hv
      rw [hvalπ]
      have hwv : w ≠ v := by
        intro hEq
        exact hw (hEq ▸ hv)
      simp [hwv]
  have htoNat (z : ℤ) : z ≤ (z.toNat : ℤ) := by
    by_cases hz : 0 ≤ z
    · rw [Int.toNat_of_nonneg hz]
    · have hneg : z < 0 := lt_of_not_ge hz
      have hzNat : z.toNat = 0 := by omega
      rw [hzNat]
      omega
  have heBound (v : ArtinPrimitiveRoots.A1.FinPlace K) (hv : v ∈ S.Sf) :
      WithZero.log (v.valuation K (c : K)) ≤ (e : ℤ) := by
    let z := WithZero.log (v.valuation K (c : K))
    have hsum := Finset.single_le_sum
      (s := S.Sf) (f := fun w => (WithZero.log (w.valuation K (c : K))).toNat)
      (fun _ _ => Nat.zero_le _) hv
    dsimp [e, z]
    calc
      z ≤ (z.toNat : ℤ) := htoNat z
      _ ≤ (e : ℤ) := by exact_mod_cast hsum
  have hvalCorrected (v : ArtinPrimitiveRoots.A1.FinPlace K) :
      v.valuation K ((c : K) * (b : K) ^ 2) ≤ 1 := by
    have hc_ne : v.valuation K (c : K) ≠ 0 := by simp [c.ne_zero]
    have hbval_ne : v.valuation K (b : K) ≠ 0 := by
      rw [hvalb]
      split_ifs <;> simp
    have hx_ne : v.valuation K ((c : K) * (b : K) ^ 2) ≠ 0 := by
      have hx : (c : K) * (b : K) ^ 2 ≠ 0 := mul_ne_zero c.ne_zero (pow_ne_zero _ (by exact_mod_cast hb_ne))
      simp [hx, hb_ne]
    have hlog : WithZero.log (v.valuation K ((c : K) * (b : K) ^ 2)) =
        WithZero.log (v.valuation K (c : K)) +
          2 * WithZero.log (v.valuation K (b : K)) := by
      rw [map_mul, map_pow, WithZero.log_mul hc_ne (pow_ne_zero _ hbval_ne), WithZero.log_pow]
      norm_num
    by_cases hv : v ∈ S.Sf
    · rw [← WithZero.exp_log hx_ne, ← WithZero.exp_zero, WithZero.exp_le_exp]
      rw [hlog, hvalb, if_pos hv]
      simp only [WithZero.log_exp]
      have he_nonneg : (0 : ℤ) ≤ (e : ℤ) := by exact_mod_cast Nat.zero_le e
      have hh_ge : (1 : ℤ) ≤ (h : ℤ) := by exact_mod_cast hh
      have hprod : (0 : ℤ) ≤ (e : ℤ) * ((h : ℤ) - 1) :=
        mul_nonneg he_nonneg (by omega)
      have hbound := heBound v hv
      simp only [nsmul_eq_mul]
      nlinarith
    · have hc_int : v.valuation K (c : K) ≤ 1 := by
        change (c : K) ∈ ((S.Sf : Set (ArtinPrimitiveRoots.A1.FinPlace K)).integer K) at hR
        exact hR v hv
      calc
        v.valuation K ((c : K) * (b : K) ^ 2) =
            v.valuation K (c : K) * v.valuation K (b : K) ^ 2 := by rw [map_mul, map_pow]
        _ = v.valuation K (c : K) := by rw [hvalb, if_neg hv]; simp
        _ ≤ 1 := hc_int
  obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K
    ((c : K) * (b : K) ^ 2) hvalCorrected
  refine ⟨b, hb_ne, ?_, a, ha⟩
  intro v hv
  have hbval : v.valuation K (b : K) = 1 := by rw [hvalb, if_neg hv]
  have hbnot : b ∉ v.asIdeal :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem v).mp hbval
  exact qs_residue_ne_zero_of_not_mem_NQ2 v hbnot

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
