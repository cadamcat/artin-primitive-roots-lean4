import ArtinPrimitiveRoots.A1.Hilbert

/-!
Core interface for the local perfect-pairing proof. This file takes the finite local characters
and their global compatibility fields as arguments so `AddChar.lean` can import it without a cycle
through `AddCharData`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots.A1
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_dual_p

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- The fixed additive character on `F_S`, with the finite characters passed explicitly. -/
def eOnFS (S : SData F CE condη)
    (ψ : (v : FinPlace F) → AddChar (v.adicCompletion F) ℂ) (x : S.FS) : ℂ :=
  (∏ v : S.Sf, ψ v.1 (x.1 v)) *
    ∏ w : InfinitePlace F,
      Complex.exp (-(4 * Real.pi * Complex.I * (x.2 w).re))

/-- The archimedean character is the trace character on a totally complex field. -/
theorem arch_product_eq_trace [IsTotallyComplex F] (z : F) :
    (∏ w : InfinitePlace F,
      Complex.exp (-(4 * Real.pi * Complex.I * ((w.embedding z).re : ℂ)))) =
      Complex.exp (-(2 * Real.pi * Complex.I * (Algebra.trace ℚ F z : ℂ))) := by
  sorry

/-- On a diagonal argument, the S-character times one omitted finite-place factor is one when
all other omitted factors are trivial. -/
theorem eOnFS_diag_mul_one_exceptional [IsTotallyComplex F]
    (S : SData F CE condη)
    (ψ : (v : FinPlace F) → AddChar (v.adicCompletion F) ℂ)
    (hglobal : ∀ z : F,
      (Function.mulSupport fun v => ψ v (algebraMap F _ z)).Finite ∧
        (∏ᶠ v, ψ v (algebraMap F _ z)) *
          Complex.exp (-(2 * Real.pi * Complex.I * (Algebra.trace ℚ F z : ℂ))) = 1)
    (z : F) (v : FinPlace F) (hv : v ∉ S.Sf)
    (hother : ∀ u : FinPlace F, u ∉ S.Sf → u ≠ v → ψ u (algebraMap F _ z) = 1) :
    eOnFS S ψ (S.diag z) * ψ v (algebraMap F _ z) = 1 := by
  sorry

private theorem exists_denominator_clearer (z : F) (hz : z ≠ 0)
    (v : FinPlace F) (hvz : 1 < v.valuation F z) :
    ∃ a : 𝓞 F, a ∉ v.asIdeal ∧
      ∀ q : FinPlace F, q ≠ v → 1 < q.valuation F z →
        q.valuation F (a : F) ≤ (q.valuation F z)⁻¹ := by
  classical
  obtain ⟨num, den, hden, hzdiv⟩ := IsFractionRing.div_surjective (𝓞 F) z
  have hden0 : den ≠ 0 := nonZeroDivisors.ne_zero hden
  have hspan : (Ideal.span {den} : Ideal (𝓞 F)) ≠ ⊥ := by
    simpa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hden0
  have hbadFinite : {q : FinPlace F | 1 < q.valuation F z}.Finite := by
    apply (Ideal.finite_factors hspan).subset
    intro q hq
    by_contra hqden
    have hdenNot : den ∉ q.asIdeal := by
      intro hmem
      exact hqden ((Ideal.dvd_span_singleton).2 hmem)
    have hvalden : q.valuation F (den : F) = 1 :=
      (q.valuation_eq_one_iff_notMem).2 hdenNot
    have hvalz : q.valuation F z ≤ 1 := by
      rw [← hzdiv, map_div₀, hvalden, div_one]
      exact q.valuation_le_one num
    exact not_lt_of_ge hvalz hq
  let B := hbadFinite.toFinset
  have hvB : v ∈ B := hbadFinite.mem_toFinset.mpr hvz
  let k : FinPlace F → ℕ := fun q => (WithZero.log (q.valuation F z)).toNat
  have hlog_pos (q : FinPlace F) (hq : 1 < q.valuation F z) :
      0 < WithZero.log (q.valuation F z) := by
    have hq0 : q.valuation F z ≠ 0 := (q.valuation F).ne_zero_iff.mpr hz
    have hh := (WithZero.log_lt_log (by simp) hq0).2 hq
    simpa using hh
  have hk_nat (q : FinPlace F) (hq : 1 < q.valuation F z) :
      ((k q : ℕ) : ℤ) = WithZero.log (q.valuation F z) := by
    dsimp [k]
    exact Int.toNat_of_nonneg (le_of_lt (hlog_pos q hq))
  let J : Ideal (𝓞 F) := ∏ q ∈ B.erase v, q.asIdeal ^ k q
  have hJnot : ¬ J ≤ v.asIdeal := by
    intro hle
    obtain ⟨q, hqmem, hqle⟩ := v.isPrime.prod_le.mp (by simpa [J] using hle)
    rcases Finset.mem_erase.mp hqmem with ⟨hqne, hqB⟩
    have hqbad : 1 < q.valuation F z := hbadFinite.mem_toFinset.mp hqB
    have hqk : 0 < k q := by
      have : 0 < (k q : ℤ) := by rw [hk_nat q hqbad]; exact hlog_pos q hqbad
      exact_mod_cast this
    have hqleP : q.asIdeal ≤ v.asIdeal :=
      (v.isPrime.pow_le_iff (Nat.ne_of_gt hqk)).mp hqle
    have heq : q.asIdeal = v.asIdeal := q.isMaximal.eq_of_le v.isPrime.ne_top hqleP
    exact hqne (HeightOneSpectrum.ext heq)
  have hJnotSet : ¬ (J : Set (𝓞 F)) ⊆ v.asIdeal := by
    simpa using hJnot
  obtain ⟨a, haJ, haV⟩ := Set.not_subset.mp hJnotSet
  refine ⟨a, haV, ?_⟩
  intro q hqv hqbad
  have hqB : q ∈ B := hbadFinite.mem_toFinset.mpr hqbad
  have hqErase : q ∈ B.erase v := Finset.mem_erase.mpr ⟨hqv, hqB⟩
  have hJle : J ≤ q.asIdeal ^ k q := by
    dsimp [J]
    exact (Ideal.prod_le_inf (s := B.erase v) (f := fun p => p.asIdeal ^ k p)).trans
      (Finset.inf_le hqErase)
  have haPow : a ∈ q.asIdeal ^ k q := hJle haJ
  have hvalA : q.valuation F (a : F) ≤ WithZero.exp (-(k q : ℤ)) := by
    rw [q.valuation_of_algebraMap]
    exact (q.intValuation_le_pow_iff_mem a (k q)).2 haPow
  have hq0 : q.valuation F z ≠ 0 := (q.valuation F).ne_zero_iff.mpr hz
  have hvalz : q.valuation F z = WithZero.exp (k q : ℤ) := by
    rw [← WithZero.exp_log hq0, hk_nat q hqbad]
  calc
    q.valuation F (a : F) ≤ WithZero.exp (-(k q : ℤ)) := hvalA
    _ = (q.valuation F z)⁻¹ := by rw [hvalz, WithZero.exp_neg]

/-- A nonintegral diagonal argument can be detected by pairing against an ordinary integer.
The exact conductor condition outside `S` is supplied by `unramified`; global compatibility
fixes the archimedean component. -/
theorem external_character_detector [IsTotallyComplex F]
    (S : SData F CE condη)
    (ψ : (v : FinPlace F) → AddChar (v.adicCompletion F) ℂ)
    (hglobal : ∀ z : F,
      (Function.mulSupport fun v => ψ v (algebraMap F _ z)).Finite ∧
        (∏ᶠ v, ψ v (algebraMap F _ z)) *
          Complex.exp (-(2 * Real.pi * Complex.I * (Algebra.trace ℚ F z : ℂ))) = 1)
    (hintegral : ∀ (v : FinPlace F) (x : v.adicCompletion F),
      x ∈ v.adicCompletionIntegers F → ψ v x = 1)
    (hunramified : ∀ v : FinPlace F,
      ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal →
        (∀ x : v.adicCompletion F, x ∈ v.adicCompletionIntegers F → ψ v x = 1) ∧
        ∀ π : F, HeightOneSpectrum.valuation F v π = WithZero.exp (-1) →
          ∃ x : 𝓞 F, ψ v (algebraMap F _ ((x : F) / π)) ≠ 1)
    (z : F) (hz : z ∉ S.R) :
    ∃ d : 𝓞 F, eOnFS S ψ (S.diag (z * (d : F))) ≠ 1 := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_dual_p
