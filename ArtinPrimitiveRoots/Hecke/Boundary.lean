import ArtinPrimitiveRoots.Hecke.Continuation
import ArtinPrimitiveRoots.A2.Endpoint

/-!
# The A/B boundary: Theorem `thm:hecke-zero-free`

`a2_zero_free_every_continuation` is part A's theorem (`sorry` until the A chain is done);
`thm_hecke_zero_free` is the form part B consumes, proved from it and (H1), (H2).
-/

set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ArtinPrimitiveRoots.HeckeBoundary

open ClassFieldTheory ArtinPrimitiveRoots.Hecke


/-- The common width `δ₀ = 10⁻⁶` (B's N8). -/
def δ₀ : ℝ := 1 / 10 ^ 6

/-- **A2's theorem, "every continuation" form** (A2 node `thm:hecke-zero-free`, proof chain
`zf:mellin-identification` etc.).  For `F = ℚ(μ_n)`, `12 ∣ n`, `n ≠ 0`, every modulus `𝔪`
and every `η` mod `𝔪`: every function holomorphic on `{Re s > 1 - δ₀}` (minus `s = 1` when
`η = 1`) that equals `L^{(𝔪)}(s, η)` on `Re s > 1` has no zero there.  Sorry: this is what
part A proves. -/
theorem a2_zero_free_every_continuation (n : ℕ) [NeZero n] (h12 : 12 ∣ n)
    (m : RayClassModulus (CyclotomicField n ℚ)) (η : RayClassGroup m →* ℂˣ) (Λ : ℂ → ℂ)
    (hΛ : DifferentiableOn ℂ Λ ({s : ℂ | 1 - δ₀ < s.re} \ {s | η = 1 ∧ s = 1}))
    (hL : ∀ s : ℂ, 1 < s.re → Λ s = LSeriesRay η s) :
    ∀ s : ℂ, 1 - δ₀ < s.re → (η ≠ 1 ∨ s ≠ 1) → Λ s ≠ 0 := by
  have hΛ' : DifferentiableOn ℂ Λ
      ({s : ℂ | 1 - ArtinPrimitiveRoots.A2.a2Delta0 < s.re} \
        {s | η = 1 ∧ s = 1}) := by
    simpa [δ₀, ArtinPrimitiveRoots.A2.a2Delta0] using hΛ
  simpa [δ₀, ArtinPrimitiveRoots.A2.a2Delta0] using
    ArtinPrimitiveRoots.A2.thm_hecke_zero_free n h12 m η Λ hΛ' hL

/-- An analytic function with a nonzero value has order `0`, so `≤ 0`. -/
theorem meromorphicOrderAt_nonpos_of_analyticAt {f : ℂ → ℂ} {x : ℂ} (hf : AnalyticAt ℂ f x)
    (hx : f x ≠ 0) : meromorphicOrderAt f x ≤ 0 := by
  rw [hf.meromorphicOrderAt_eq, (analyticOrderAt_eq_zero).mpr (Or.inr hx)]
  simp

/-- **Frozen A/B boundary (B's consumer form, B node `thm:hecke-zero-free`, line 70).**
For every `n` with `12 ∣ n` and `n ≠ 0` (see A2-DESIGN §3: `n = 0` must be excluded, since
`CyclotomicField 0 ℚ = ℚ`), every modulus `𝔪` of `F = CyclotomicField n ℚ` and every
character `η` of `Cl_𝔪(F)`: there is `Λ` meromorphic on an open `U ⊇ {Re s > 1 - δ₀}` with
`Λ = L_F^{(𝔪)}(·, η)` on `Re s > 1` and `meromorphicOrderAt Λ s ≤ 0` (no zero) on
`Re s > 1 - δ₀`.

Proved from (H1), (H2) and `a2_zero_free_every_continuation`. -/
theorem thm_hecke_zero_free (n : ℕ) [NeZero n] (h12 : 12 ∣ n)
    (m : RayClassModulus (CyclotomicField n ℚ)) (η : RayClassGroup m →* ℂˣ) :
    ∃ (U : Set ℂ) (Λ : ℂ → ℂ), IsOpen U ∧ {s : ℂ | 1 - δ₀ < s.re} ⊆ U ∧
      MeromorphicOn Λ U ∧ (∀ s : ℂ, 1 < s.re → Λ s = LSeriesRay η s) ∧
      ∀ s : ℂ, 1 - δ₀ < s.re → meromorphicOrderAt Λ s ≤ 0 := by
  have hn : 2 < n := by
    have h0 : n ≠ 0 := NeZero.ne n
    obtain ⟨k, rfl⟩ := h12
    have hk : k ≠ 0 := by rintro rfl; exact h0 rfl
    omega
  have : NeZero ((n : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne n⟩
  have : IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ) :=
    CyclotomicField.isCyclotomicExtension n ℚ
  have : IsTotallyComplex (CyclotomicField n ℚ) :=
    IsCyclotomicExtension.Rat.isTotallyComplex (CyclotomicField n ℚ) hn
  by_cases hη : η = 1
  · -- trivial character: `Λ = G / (s - 1)` with `G` entire, `G 1 ≠ 0`
    subst hη
    obtain ⟨G, hGd, hGeq, hG1⟩ := LSeriesRay_trivial_continuation m
    refine ⟨Set.univ, fun s => G s * (s - 1)⁻¹, isOpen_univ, Set.subset_univ _, ?_, ?_, ?_⟩
    · intro s _
      exact (hGd.analyticAt s).meromorphicAt.mul
        ((analyticAt_id.sub analyticAt_const).meromorphicAt.inv)
    · intro s hs
      have hs1 : s - 1 ≠ 0 := by
        intro h
        have : s = 1 := sub_eq_zero.mp h
        rw [this] at hs
        simp at hs
      show G s * (s - 1)⁻¹ = _
      rw [hGeq s hs]
      field_simp
    · have hG1ne : G 1 ≠ 0 := by
        rw [hG1]
        have hres := dedekindZeta_residue_pos (CyclotomicField n ℚ)
        have hprod : 0 < ∏ v ∈ m.finitePart.support,
            (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹) := by
          apply Finset.prod_pos
          intro v _
          have h2 : (1 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
            exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
          have : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h2
          linarith
        exact_mod_cast (mul_pos hres hprod).ne'
      intro s hs
      by_cases hs1 : s = 1
      · subst hs1
        -- order of `G · (s-1)⁻¹` at `1` is `-1`
        have hmul : meromorphicOrderAt (fun s => G s * (s - 1)⁻¹) 1 =
            meromorphicOrderAt (fun s : ℂ => (s - 1)⁻¹) 1 := by
          have := meromorphicOrderAt_mul_of_ne_zero (x := (1 : ℂ))
            (f := fun s : ℂ => (s - 1)⁻¹) (hGd.analyticAt 1) hG1ne
          simpa [Pi.mul_def] using this
        rw [hmul]
        have hfun : (fun s : ℂ => (s - 1)⁻¹) = (fun s : ℂ => s - 1)⁻¹ := rfl
        rw [hfun, meromorphicOrderAt_inv, meromorphicOrderAt_id_sub_const]
        decide
      · -- `s ≠ 1`: analytic and nonzero by A2's theorem
        have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
        have han : AnalyticAt ℂ (fun s => G s * (s - 1)⁻¹) s :=
          (hGd.analyticAt s).mul ((analyticAt_id.sub analyticAt_const).inv hsub)
        apply meromorphicOrderAt_nonpos_of_analyticAt han
        refine a2_zero_free_every_continuation n h12 m 1 (fun s => G s * (s - 1)⁻¹) ?_ ?_ s hs
          (Or.inr hs1)
        · intro z hz
          have hz1 : z - 1 ≠ 0 := by
            intro h
            exact hz.2 ⟨rfl, sub_eq_zero.mp h⟩
          exact ((hGd.analyticAt z).mul
            ((analyticAt_id.sub analyticAt_const).inv hz1)).differentiableAt.differentiableWithinAt
        · intro z hz
          have hz1 : z - 1 ≠ 0 := by
            intro h
            have : z = 1 := sub_eq_zero.mp h
            rw [this] at hz
            simp at hz
          show G z * (z - 1)⁻¹ = _
          rw [hGeq z hz]
          field_simp
  · -- nontrivial character: entire continuation
    obtain ⟨Λ, hΛd, hΛeq⟩ := LSeriesRay_entire η hη
    refine ⟨Set.univ, Λ, isOpen_univ, Set.subset_univ _,
      fun s _ => (hΛd.analyticAt s).meromorphicAt, hΛeq, ?_⟩
    intro s hs
    exact meromorphicOrderAt_nonpos_of_analyticAt (hΛd.analyticAt s)
      (a2_zero_free_every_continuation n h12 m η Λ hΛd.differentiableOn hΛeq s hs (Or.inl hη))


end ArtinPrimitiveRoots.HeckeBoundary
