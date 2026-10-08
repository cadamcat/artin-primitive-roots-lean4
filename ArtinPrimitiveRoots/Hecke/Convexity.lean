import ArtinPrimitiveRoots.Hecke.Defs
import ArtinPrimitiveRoots.Hecke.Continuation
import ArtinPrimitiveRoots.Hecke.Proofs.«HK-ANALYTIC».Growth
import ArtinPrimitiveRoots.Hecke.Proofs.«HK-ANALYTIC».EulerBound

/-!
# Hecke L-function package: uniform convexity (H3, H3')

Frozen interface. Design: `research/design/A2-HeckeAPI.lean` and `A2-DESIGN.md` (Opus A2 sub-agent, 2026-10-07).
-/

set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain
open Complex Filter Topology

noncomputable section

namespace ArtinPrimitiveRoots.Hecke

open ClassFieldTheory

variable {K : Type*} [Field K] [NumberField K]

/-- **(H3) Convexity bound, uniform in the modulus and the character.**
For a totally complex `K` there is a height exponent `A` (depending on `K` only) such that for
every `ε > 0` and every `σ₀ > 0` one constant `C(K, ε, σ₀)` serves all moduli `𝔪` and all
nontrivial `η` mod `𝔪`: on `σ₀ ≤ Re s ≤ 4`,
`‖L^{(𝔪)}(s,η)‖ ≤ C · (N𝔣_η)^{1/2+ε} · (N𝔪)^ε · (2 + |Im s|)^A`
(`N𝔣_η = conductorNorm η`; the factor `(N𝔪)^ε` absorbs the imprimitive Euler factors).
Stated for every continuation `Λ` (unique by the identity theorem), so no junk values enter.
Consumers: A2 `zf:convexity` (paper eq. `Hecke-conservative-convexity`, 06:139-163, used with
`σ₀ = .003`), hence `zf:detector-shift` (at `Re = 1/2`), `zf:reciprocal-bound`,
`zf:small-rows` / `zf:intermediate-rows` (numerator `L^S(w, χ_•(u))` at `Re w = .003`).
The exponent `1/2` at `σ₀ = .003` is needed: with a trivial (Gauss-sum-free) dual bound the
exponent there is `≈ 1` and the margin of `zf:small-rows` fails (A2-DESIGN §2.3). -/
theorem LSeriesRay_convexity [IsTotallyComplex K] :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ε : ℝ, 0 < ε → ∀ σ₀ : ℝ, 0 < σ₀ → ∃ C : ℝ, 0 < C ∧
      ∀ (m : RayClassModulus K) (η : RayClassGroup m →* ℂˣ), η ≠ 1 →
      ∀ Λ : ℂ → ℂ, Differentiable ℂ Λ → (∀ s : ℂ, 1 < s.re → Λ s = LSeriesRay η s) →
      ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ 4 →
        ‖Λ s‖ ≤ C * (conductorNorm η : ℝ) ^ ((1 : ℝ) / 2 + ε) *
          (modulusNorm m : ℝ) ^ ε * (2 + |s.im|) ^ A := sorry

private theorem isCoprimeTo_prime_of_not_mem (m : RayClassModulus K)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ m.finitePart.support) :
    IsCoprimeTo m v.asIdeal := by
  refine ⟨v.ne_bot, ?_⟩
  change ∀ w, w ∈ m.finitePart.support →
    FractionalIdeal.count K w
      ((idealUnit v.asIdeal v.ne_bot : NumberFieldFractionalIdealGroup K) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0
  intro w hw
  have hwv : w ≠ v := by
    intro h
    exact hv (h ▸ hw)
  simpa [idealUnit] using
    (FractionalIdeal.count_maximal_coprime K w (Ne.symm hwv))

private theorem charValue_trivial_prime_of_not_mem (m : RayClassModulus K)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ m.finitePart.support) :
    charValue (1 : RayClassGroup m →* ℂˣ) v.asIdeal = 1 := by
  have hcop := isCoprimeTo_prime_of_not_mem m v hv
  simp [charValue, hcop]

private theorem charValue_trivial_empty_prime (v : HeightOneSpectrum (𝓞 K)) :
    charValue (1 : RayClassGroup (⟨0, ∅⟩ : RayClassModulus K) →* ℂˣ)
      v.asIdeal = 1 := by
  have hv : v ∉ (⟨0, ∅⟩ : RayClassModulus K).finitePart.support := by simp
  exact charValue_trivial_prime_of_not_mem (⟨0, ∅⟩ : RayClassModulus K) v hv

/-- **(H3') Polynomial growth for the trivial character**, uniform in `𝔪` up to `(N𝔪)^ε`.
Consumers: A2 `zf:principal-row` (`ζ_F^S(w)` on `Re w = .95`, `ζ_F^S(6z)` on `Re 6z = .96`),
`zf:height-decay`. -/
theorem LSeriesRay_trivial_growth :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ε : ℝ, 0 < ε → ∀ σ₀ : ℝ, 0 < σ₀ → ∃ C : ℝ, 0 < C ∧
      ∀ (m : RayClassModulus K) (G : ℂ → ℂ), Differentiable ℂ G →
      (∀ s : ℂ, 1 < s.re → G s = (s - 1) * LSeriesRay (1 : RayClassGroup m →* ℂˣ) s) →
      ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ 4 →
        ‖G s‖ ≤ C * (modulusNorm m : ℝ) ^ ε * (2 + |s.im|) ^ A := by
  classical
  let d : ℕ := Module.finrank ℚ K
  let A : ℝ := (d + 2 : ℕ)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A, hA, ?_⟩
  intro ε hε σ₀ hσ₀
  obtain ⟨G₀, hG₀diff, hG₀eq, C₀, hC₀, hG₀bound⟩ :=
    ArtinPrimitiveRoots.Proofs.HK_MISC_P.exists_dedekind_simple_pole_poly_bound K
  obtain ⟨B, hB, hEulerBound⟩ :=
    ArtinPrimitiveRoots.Proofs.HK_MISC_P.exists_omittedEuler_bound (K := K) ε hε
  let C : ℝ := C₀ * B
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro m G hGdiff hGeq s hs₀ hs₄
  let η₀ : RayClassGroup (⟨0, ∅⟩ : RayClassModulus K) →* ℂˣ := 1
  let E : ℂ → ℂ := ArtinPrimitiveRoots.Proofs.HK_MISC_P.omittedEuler m η₀
  let G₁ : ℂ → ℂ := fun z => G₀ z * E z
  have hEdiff : Differentiable ℂ E := by
    simpa [E] using
      ArtinPrimitiveRoots.Proofs.HK_MISC_P.omittedEuler_differentiable m η₀
  have hG₁diff : Differentiable ℂ G₁ := by
    dsimp [G₁]
    exact hG₀diff.mul hEdiff
  have hAgree : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ m.finitePart.support →
      charValue (1 : RayClassGroup m →* ℂˣ) v.asIdeal = charValue η₀ v.asIdeal := by
    intro v hv
    rw [charValue_trivial_prime_of_not_mem m v hv,
      charValue_trivial_empty_prime v]
  have hchange (z : ℂ) (hz : 1 < z.re) :
      LSeriesRay (1 : RayClassGroup m →* ℂˣ) z =
        LSeriesRay η₀ z * ∏ v ∈ m.finitePart.support,
          (1 - charValue η₀ v.asIdeal *
            ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-z)) :=
    LSeriesRay_change_modulus (η := (1 : RayClassGroup m →* ℂˣ))
      (η' := η₀) hAgree hz
  have htrivial (z : ℂ) : LSeriesRay η₀ z = dedekindZeta K z := by
    dsimp [η₀]
    exact LSeriesRay_trivial_eq_dedekindZeta (K := K) z
  have hfactor (z : ℂ) :
      (∏ v ∈ m.finitePart.support,
        (1 - charValue η₀ v.asIdeal *
          ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-z))) = E z := by
    unfold E ArtinPrimitiveRoots.Proofs.HK_MISC_P.omittedEuler
    apply Finset.prod_congr rfl
    intro v hv
    rw [charValue_trivial_empty_prime]
  have hG₁eq (z : ℂ) (hz : 1 < z.re) :
      G₁ z = (z - 1) * LSeriesRay (1 : RayClassGroup m →* ℂˣ) z := by
    calc
      G₁ z = G₀ z * E z := rfl
      _ = ((z - 1) * dedekindZeta K z) * E z := by rw [hG₀eq z hz]
      _ = (z - 1) * LSeriesRay η₀ z *
            (∏ v ∈ m.finitePart.support,
              (1 - charValue η₀ v.asIdeal *
                ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-z))) := by
        rw [htrivial, hfactor]
      _ = (z - 1) * LSeriesRay (1 : RayClassGroup m →* ℂˣ) z := by
        rw [hchange z hz]
        ring
  have hopen : IsOpen {z : ℂ | 1 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have h2mem : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by norm_num
  have hEqOn : Set.EqOn G G₁ {z : ℂ | 1 < z.re} := by
    intro z hz
    rw [hGeq z hz, hG₁eq z hz]
  have hEqual : ∀ z : ℂ, G z = G₁ z := by
    have hagree := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      (𝕜 := ℂ) (f := G) (g := G₁)
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hGdiff)
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hG₁diff)
      isPreconnected_univ (Set.mem_univ (2 : ℂ))
      (hEqOn.eventuallyEq_of_mem (hopen.mem_nhds h2mem))
    intro z
    exact hagree (Set.mem_univ z)
  have hImNonneg : 0 ≤ s.re := le_trans (le_of_lt hσ₀) hs₀
  have hG₀s := hG₀bound s hImNonneg hs₄
  have hEs := hEulerBound m (⟨0, ∅⟩ : RayClassModulus K) η₀ s hImNonneg
  have hG₁s : ‖G₁ s‖ ≤
      C₀ * (2 + |s.im|) ^ (d + 2 : ℕ) *
        (B * (modulusNorm m : ℝ) ^ ε) := by
    dsimp [G₁]
    rw [norm_mul]
    exact mul_le_mul hG₀s hEs (norm_nonneg _) (by positivity)
  calc
    ‖G s‖ = ‖G₁ s‖ := by rw [hEqual s]
    _ ≤ C₀ * (2 + |s.im|) ^ (d + 2 : ℕ) *
          (B * (modulusNorm m : ℝ) ^ ε) := hG₁s
    _ = C * (modulusNorm m : ℝ) ^ ε * (2 + |s.im|) ^ A := by
      dsimp [C, A, d]
      simp only [Real.rpow_natCast]
      ring


end ArtinPrimitiveRoots.Hecke
