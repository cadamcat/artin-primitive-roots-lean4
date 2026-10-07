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
idelic character is trivial in A1's local congruence sense. Corrected per rev-a2 to exclude the
zero ideal from the minimization. -/
def IsPrimitiveConductor (χ : ArtinPrimitiveRoots.A1.HeckeChar F)
    (𝔣 : Ideal (𝓞 F)) : Prop :=
  𝔣 ≠ ⊥ ∧ χ.ConductorDvd 𝔣 ∧
    ∀ 𝔤 : Ideal (𝓞 F), 𝔤 ≠ ⊥ → χ.ConductorDvd 𝔤 →
      Ideal.absNorm 𝔣 ≤ Ideal.absNorm 𝔤

/-- The finite-place local components at a fixed finite set `S`. -/
abbrev SLocalCharacter (S : ArtinPrimitiveRoots.A1.SData F CE condη) :=
  ∀ v : S.Sf, (v.1.adicCompletion F)ˣ →* ℂˣ

/-- Restriction of an idelic Hecke character to the fixed finite places in `S`. -/
def SComponent (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (χ : ArtinPrimitiveRoots.A1.HeckeChar F) : SLocalCharacter S :=
  fun v => χ.loc v.1

/-- The raw complete ideal Dirichlet series associated with an idelic character; its stated
continuation is packaged separately below. Corrected per rev-a2. -/
def heckeLSeries (χ : ArtinPrimitiveRoots.A1.HeckeChar F) (s : ℂ) : ℂ :=
  ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥},
    χ.idealValue I.1 * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)

/-- The raw incomplete ideal Dirichlet series with the Euler factors at `S` omitted; its stated
continuation is packaged separately below. Corrected per rev-a2. -/
def incompleteHeckeLSeries (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (χ : ArtinPrimitiveRoots.A1.HeckeChar F) (s : ℂ) : ℂ :=
  ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ ∀ v ∈ S.Sf, ¬ I ≤ v.asIdeal},
    χ.idealValue I.1 * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)

/-- Entire continuation of a complete Hecke Dirichlet series, identified with the raw sum only
where that sum converges absolutely. Added for the rev-a2 continuation correction. -/
structure HeckeLContinuation (χ : ArtinPrimitiveRoots.A1.HeckeChar F) where
  value : ℂ → ℂ
  differentiable : Differentiable ℂ value
  agrees : ∀ s : ℂ, 1 < s.re → value s = heckeLSeries χ s

/-- Analytic continuation of an incomplete Hecke series to the zero-free half-plane, identified
with its raw sum only in the absolute-convergence region. Added per rev-a2. -/
structure IncompleteHeckeLContinuation
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (χ : ArtinPrimitiveRoots.A1.HeckeChar F) where
  value : ℂ → ℂ
  differentiableOn : DifferentiableOn ℂ value {s : ℂ | 997 / 1000 < s.re}
  agrees : ∀ s : ℂ, 1 < s.re → value s = incompleteHeckeLSeries S χ s

/-- Uniform convexity growth for primitive finite-order Hecke characters. The exponent `A_F`
is part of the hypothesis, so detector estimates cannot choose it independently of the bound.
Corrected per sol-gate-a2, `zf:detector-shift` and `zf:detector-count` (06:139-153, 249-264). -/
def ConductorHeightBound (A_F : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ (ω : ArtinPrimitiveRoots.A1.HeckeChar F), IsOfFinOrder ω → ω ≠ 1 →
      ∀ f : Ideal (𝓞 F), IsPrimitiveConductor ω f →
        ∀ L : HeckeLContinuation ω, ∀ s : ℂ,
          3 / 1000 ≤ s.re → s.re ≤ 4 →
            ‖L.value s‖ ≤ C * Real.rpow (Ideal.absNorm f : ℝ) (1 / 2 + ε) *
              Real.rpow (2 + |s.im|) A_F

/-- **lem:conductor-sieve** (06-zero-free.tex:37-137). Fixed data and `ε` precede both growing
lengths; the constant is uniform over the family and its coefficients. Uses the corrected
nonzero primitive-conductor predicate from rev-a2. -/
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
Kummer characters, primitive twists, and the unique factorization map of 02:285-387. Corrected per
rev-a2 to include the quantitative row, conductor, distinctness, and decomposition hypotheses
needed by the zero-density argument. -/
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
  /-- The primitive induction preserves the full idelic character, including ramified places. -/
  omega_induces_twist : ∀ u, omega u = η * (kummer u)⁻¹
  kummer_local : ∀ u (v : ArtinPrimitiveRoots.A1.FinPlace F), v ∉ S.Sf →
    ArtinPrimitiveRoots.A1.residue v (repr u) ≠ 0 →
      (kummer u).UnramifiedAt v ∧
        (kummer u).primeValue v = ArtinPrimitiveRoots.A1.chi D v (repr u)

  q_ge_one : ∀ u, 1 ≤ q u
  dyadic_count : ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 2 ≤ X →
    {u : U | X ≤ q u ∧ q u < 2 * X}.Finite ∧
    (Set.ncard {u : U | X ≤ q u ∧ q u < 2 * X} : ℝ) ≤ C * X
  /-- The compact initial shell needed when the requested dyadic parameter is in [1,2). -/
  low_shell_bound : ∃ C : ℝ, 0 < C ∧
    {u : U | 1 ≤ q u ∧ q u < 4}.Finite ∧
      (Set.ncard {u : U | 1 ≤ q u ∧ q u < 4} : ℝ) ≤ C
  kummer_injective : ∀ u v, kummer u = kummer v → u = v
  omega_injective : ∀ u v, omega u = omega v → u = v
  conductor_bound : ∃ C : ℝ, 0 < C ∧ ∀ u,
    ∃ 𝔣 : Ideal (𝓞 F), IsPrimitiveConductor (omega u) 𝔣 ∧
      (Ideal.absNorm 𝔣 : ℝ) ≤ C * q u
  local_components_finite : ∃ 𝓛S : Finset (SLocalCharacter S),
    ∀ u, SComponent S (omega u) ∈ 𝓛S
  decomposition_surjective : ∀ u : U, ∀ I : ArtinPrimitiveRoots.A1.SData.ExtIdeal S,
    ∃ x : S.R, (x : F) ≠ 0 ∧ ∃ ε : S.US, ∃ a : Fˣ,
      S.IsGen (a : F) I.1 ∧
      (x : F) = (repr u : F) * ((ε : Fˣ) : F) ^ 6 * (a : F) ^ 6
  /-- S-integer conductor bounds, including the possibly ramified induced twist. -/
  kummer_twist_conductor_bound : IsOfFinOrder η →
    (∀ v : ArtinPrimitiveRoots.A1.FinPlace F, v ∉ S.Sf → η.UnramifiedAt v) →
      ∃ C : ℝ, 0 < C ∧ ∀ u,
        (∃ m : Ideal (𝓞 F), m ≠ ⊥ ∧ (kummer u).ConductorDvd m ∧
          (Ideal.absNorm m : ℝ) ≤ C * q u) ∧
        (∃ m : Ideal (𝓞 F), m ≠ ⊥ ∧ (η * (kummer u)⁻¹).ConductorDvd m ∧
          (Ideal.absNorm m : ℝ) ≤ C * q u)

/-- A1/Characters producer obligation for the complete corrected frequency dictionary
(02:285-387), including idelic induction, dyadic finiteness, and S-integer conductor bounds. -/
theorem FrequencyData.nonempty
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (η : ArtinPrimitiveRoots.A1.HeckeChar F) : Nonempty (FrequencyData S D η) := by
  sorry

/-- **prop:zero-density** (06-zero-free.tex:165-185). One exceptional family `E(U)` is chosen
before `ε`, and each reciprocal constant is uniform in the growing dyadic variable. Corrected per
sol-gate-a2 to keep the same exceptional set for every `ε`. -/
theorem prop_zero_density
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (η : ArtinPrimitiveRoots.A1.HeckeChar F) (hη : IsOfFinOrder η)
    (hηoutsideS : ∀ v : ArtinPrimitiveRoots.A1.FinPlace F,
      v ∉ S.Sf → η.UnramifiedAt v)
    (fd : FrequencyData S D η)
    (L : ∀ u : fd.U, fd.omega u ≠ 1 → HeckeLContinuation (fd.omega u))
    (Linc : ∀ u : fd.U, fd.omega u ≠ 1 →
      IncompleteHeckeLContinuation S (η * (fd.kummer u)⁻¹))
    (A_F : ℝ) (hAF : 0 < A_F) :
    ∃ ρ U₀ Cexc : ℝ, ∃ E : ℝ → Finset fd.U,
      0 < ρ ∧ ρ < min (1 / 10) (1 / (A_F + 1)) ∧
      2 ≤ U₀ ∧ 0 < Cexc ∧
      (∀ U : ℝ, U₀ ≤ U →
        (∀ u ∈ E U, U ≤ fd.q u ∧ fd.q u < 2 * U) ∧
        ((E U).card : ℝ) ≤ Cexc * Real.rpow U (1 / 2 : ℝ) ∧
        (∀ u, U ≤ fd.q u → fd.q u < 2 * U →
          (fd.omega u = 1 ∨ ∃ hnon : fd.omega u ≠ 1, ∃ s : ℂ,
            996 / 1000 ≤ s.re ∧ |s.im| ≤ 4 * Real.rpow U ρ ∧
              (L u hnon).value s = 0) → u ∈ E U)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ Cε : ℝ, 0 < Cε ∧
        ∀ U : ℝ, U₀ ≤ U → ∀ u, U ≤ fd.q u → fd.q u < 2 * U →
          u ∉ E U → ∀ hnon : fd.omega u ≠ 1, ∀ ξ : ℂ,
            998 / 1000 ≤ ξ.re → |ξ.im| ≤ 2 * Real.rpow U ρ →
              ‖((Linc u hnon).value ξ)⁻¹‖ ≤ Cε * Real.rpow U ε) := by
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
