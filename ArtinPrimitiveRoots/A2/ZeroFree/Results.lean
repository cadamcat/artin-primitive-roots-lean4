import ArtinPrimitiveRoots.A2.Defs
import ArtinPrimitiveRoots.A2.Dictionary
import ArtinPrimitiveRoots.A1.Characters
import ArtinPrimitiveRoots.Hecke.Defs

/-!
# Section 6: conductor sieve, zero density, and the final A2 theorem
-/

set_option autoImplicit false

open NumberField IsDedekindDomain
open ClassFieldTheory
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- **ext:primitive-conductor** (06-zero-free.tex:37-73): a modulus of least norm on which the
idelic character is trivial in A1's local congruence sense. -/
def IsPrimitiveConductor (χ : ArtinPrimitiveRoots.A1.HeckeChar F)
    (𝔣 : Ideal (𝓞 F)) : Prop :=
  χ.ConductorDvd 𝔣 ∧ ∀ 𝔤 : Ideal (𝓞 F), χ.ConductorDvd 𝔤 →
    Ideal.absNorm 𝔣 ≤ Ideal.absNorm 𝔤

/-- The finite-place local components at a fixed finite set `S`. -/
abbrev SLocalCharacter (S : ArtinPrimitiveRoots.A1.SData F CE condη) :=
  ∀ v : S.Sf, (v.1.adicCompletion F)ˣ →* ℂˣ

/-- Restriction of an idelic Hecke character to the fixed finite places in `S`. -/
def SComponent (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (χ : ArtinPrimitiveRoots.A1.HeckeChar F) : SLocalCharacter S :=
  fun v => χ.loc v.1

/-- The complete ideal Dirichlet series associated with an idelic character. -/
def heckeLSeries (χ : ArtinPrimitiveRoots.A1.HeckeChar F) (s : ℂ) : ℂ :=
  ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥},
    χ.idealValue I.1 * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)

/-- The incomplete ideal Dirichlet series with the Euler factors at `S` omitted. -/
def incompleteHeckeLSeries (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (χ : ArtinPrimitiveRoots.A1.HeckeChar F) (s : ℂ) : ℂ :=
  ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ ∀ v ∈ S.Sf, ¬ I ≤ v.asIdeal},
    χ.idealValue I.1 * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)

/-- **lem:conductor-sieve** (06-zero-free.tex:37-137). Fixed data and `ε` precede both growing
lengths; the constant is uniform over the family and its coefficients. -/
theorem lem_conductor_sieve
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (C₀ : ℝ) (hC₀ : 0 < C₀)
    (𝓛S : Finset (SLocalCharacter S)) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (N U : ℝ), 2 ≤ N → 2 ≤ U →
        ∀ (𝓧 : Finset (ArtinPrimitiveRoots.A1.HeckeChar F)),
          (∀ ω ∈ 𝓧, IsOfFinOrder ω ∧ SComponent S ω ∈ 𝓛S ∧
            ∃ 𝔣 : Ideal (𝓞 F), IsPrimitiveConductor ω 𝔣 ∧
              (Ideal.absNorm 𝔣 : ℝ) ≤ C₀ * U) →
          ∀ b : Ideal (𝓞 F) → ℂ,
            (∑ ω ∈ 𝓧,
              ‖∑ I ∈ (Ideal.finite_setOfPred_absNorm_le
                  (S := 𝓞 F) ⌊N⌋₊).toFinset,
                  b I * ω.idealValue I‖ ^ 2) ≤
              C * (N + U ^ 2) * Real.rpow (N * U) ε *
                ∑ I ∈ (Ideal.finite_setOfPred_absNorm_le
                    (S := 𝓞 F) ⌊N⌋₊).toFinset, ‖b I‖ ^ 2 := by
  sorry

/-- **MISSING A1 frequency interface**: the sixth-power-free representative set `𝒰`, its norm,
Kummer characters, primitive twists, and the unique factorization map of 02:285-387. -/
structure FrequencyData (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (η : ArtinPrimitiveRoots.A1.HeckeChar F) where
  U : Type
  q : U → ℝ
  q_pos : ∀ u, 0 < q u
  one : U
  q_one : q one = 1
  repr : U → S.R
  repr_nonzero : ∀ u, (repr u : F) ≠ 0
  q_eq_absS : ∀ u, q u = S.absS (S.diag (repr u : F))
  sixth_power_free : ∀ u (v : ArtinPrimitiveRoots.A1.FinPlace F), v ∉ S.Sf →
    0 ≤ FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (repr u : F)) ∧
    FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (repr u : F)) < 6
  decomposition : ∀ x : S.R, (x : F) ≠ 0 →
    ∃! ui : U × ArtinPrimitiveRoots.A1.SData.ExtIdeal S,
      ∃ ε : S.US, ∃ a : Fˣ,
        S.IsGen (a : F) ui.2.1 ∧
        (x : F) = (repr ui.1 : F) * ((ε : Fˣ) : F) ^ 6 * (a : F) ^ 6
  kummer : U → ArtinPrimitiveRoots.A1.HeckeChar F
  kummer_one : kummer one = 1
  kummer_principal_iff : ∀ u, kummer u = 1 ↔ u = one
  omega : U → ArtinPrimitiveRoots.A1.HeckeChar F
  omega_finiteOrder : ∀ u, IsOfFinOrder (omega u)
  omega_primitive : ∀ u, ∃ 𝔣 : Ideal (𝓞 F), IsPrimitiveConductor (omega u) 𝔣
  omega_induces_twist : ∀ u (v : ArtinPrimitiveRoots.A1.FinPlace F), v ∉ S.Sf →
    (omega u).UnramifiedAt v ∧ (omega u).primeValue v =
      (η * (kummer u)⁻¹).primeValue v
  kummer_local : ∀ u (v : ArtinPrimitiveRoots.A1.FinPlace F), v ∉ S.Sf →
    ArtinPrimitiveRoots.A1.residue v (repr u) ≠ 0 →
      (kummer u).UnramifiedAt v ∧
        (kummer u).primeValue v = ArtinPrimitiveRoots.A1.chi D v (repr u)

/-- **prop:zero-density** (06-zero-free.tex:165-185). Constants are fixed before the dyadic
variable, and the exceptional set covers every principal row and every row with a zero in the
specified rectangle.  The `h_missing_` argument is the explicit frequency dictionary absent from
the frozen A1 API. -/
theorem prop_zero_density
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (η : ArtinPrimitiveRoots.A1.HeckeChar F) (hη : IsOfFinOrder η)
    (hηoutsideS : ∀ v : ArtinPrimitiveRoots.A1.FinPlace F,
      v ∉ S.Sf → η.UnramifiedAt v)
    (h_missing_frequency_decomposition : FrequencyData S D η) :
    ∃ ρ U₀ Cexc : ℝ, 0 < ρ ∧ 2 ≤ U₀ ∧ 0 < Cexc ∧
      ∀ U : ℝ, U₀ ≤ U →
        ∃ E : Finset h_missing_frequency_decomposition.U,
          (∀ u ∈ E, U ≤ h_missing_frequency_decomposition.q u ∧
            h_missing_frequency_decomposition.q u < 2 * U) ∧
          (E.card : ℝ) ≤ Cexc * Real.rpow U (1 / 2 : ℝ) ∧
          (∀ u, U ≤ h_missing_frequency_decomposition.q u →
            h_missing_frequency_decomposition.q u < 2 * U →
            (h_missing_frequency_decomposition.omega u = 1 ∨
              ∃ s : ℂ, 996 / 1000 ≤ s.re ∧ ‖s.im‖ ≤ 4 * Real.rpow U ρ ∧
                heckeLSeries (h_missing_frequency_decomposition.omega u) s = 0) →
            u ∈ E) ∧
          ∀ ε : ℝ, 0 < ε → ∃ Cε : ℝ, 0 < Cε ∧
            ∀ u, U ≤ h_missing_frequency_decomposition.q u →
              h_missing_frequency_decomposition.q u < 2 * U → u ∉ E →
              ∀ ξ : ℂ, 998 / 1000 ≤ ξ.re → ‖ξ.im‖ ≤ 2 * Real.rpow U ρ →
                ‖(incompleteHeckeLSeries S
                    (η * (h_missing_frequency_decomposition.kummer u)⁻¹) ξ)⁻¹‖ ≤
                  Cε * Real.rpow U ε := by
  sorry

/-- The frozen A/B boundary width `δ₀ = 10⁻⁶`. -/
def a2Delta0 : ℝ := 1 / 10 ^ 6

/-- **thm:hecke-zero-free** (06-zero-free.tex:754-764). Every differentiable continuation of a
ray-class Hecke L-series is nonzero in the frozen half-plane, except for the principal pole point.
-/
theorem thm_hecke_zero_free (n : ℕ) [NeZero n] (h12 : 12 ∣ n)
    (m : RayClassModulus (CyclotomicField n ℚ))
    (η : RayClassGroup m →* ℂˣ) (Λ : ℂ → ℂ)
    (hΛ : DifferentiableOn ℂ Λ
      ({s : ℂ | 1 - a2Delta0 < s.re} \ {s | η = 1 ∧ s = 1}))
    (hL : ∀ s : ℂ, 1 < s.re → Λ s = ArtinPrimitiveRoots.Hecke.LSeriesRay η s) :
    ∀ s : ℂ, 1 - a2Delta0 < s.re → (η ≠ 1 ∨ s ≠ 1) → Λ s ≠ 0 := by
  sorry

end ArtinPrimitiveRoots.A2
