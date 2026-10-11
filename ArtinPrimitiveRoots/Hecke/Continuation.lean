import ArtinPrimitiveRoots.Hecke.Elementary
import ArtinPrimitiveRoots.Hecke.Dedekind.SimplePole
import ArtinPrimitiveRoots.Hecke.Theta.RayMellinAgreement

/-!
# Hecke L-function package: continuation (H1, H2)

Frozen interface.
-/

set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ArtinPrimitiveRoots.Hecke

open ClassFieldTheory

variable {K : Type*} [Field K] [NumberField K]

/-! ## §3 Analytic statements for ray class characters -/

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

private noncomputable def trivialEulerFactor (m : RayClassModulus K) (s : ℂ) : ℂ :=
  ∏ v ∈ m.finitePart.support,
    (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))

private theorem trivialEulerFactor_differentiable (m : RayClassModulus K) :
    Differentiable ℂ (trivialEulerFactor m) := by
  unfold trivialEulerFactor
  refine Differentiable.fun_finsetProd ?_
  intro v hv
  have hNnat : Ideal.absNorm v.asIdeal ≠ 0 := by
    intro h
    exact v.ne_bot ((Ideal.absNorm_eq_zero_iff).mp h)
  have hN : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast hNnat
  have hpow : Differentiable ℂ
      (fun s : ℂ => ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) := by
    intro s
    exact (differentiableAt_id.neg).const_cpow (Or.inl hN)
  exact (differentiable_const (1 : ℂ)).sub hpow

/-- **(H2) Continuation, trivial character: one simple pole at `s = 1`, positive residue.**
`(s - 1) L^{(𝔪)}(s, 1)` extends to an entire `G` with
`G 1 = Res_{s=1} ζ_K · ∏_{v ∈ supp 𝔪} (1 - N𝔭_v^{-1}) > 0`.
Consumers: A2 `zf:principal-row` (`R_S > 0`), `def:zf-principal-mellin`; §5 below.
Holds for every number field (from AINTLIB's Dedekind zeta and §2 change of modulus). -/
theorem LSeriesRay_trivial_continuation (m : RayClassModulus K) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧
      (∀ s : ℂ, 1 < s.re → G s = (s - 1) * LSeriesRay (1 : RayClassGroup m →* ℂˣ) s) ∧
      G 1 = ((dedekindZeta_residue K * ∏ v ∈ m.finitePart.support,
        (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹) : ℝ) : ℂ) := by
  classical
  obtain ⟨G₀, hG₀diff, hG₀eq, hG₀one⟩ := dedekindZeta_simple_pole_continuation K
  let η₀ : RayClassGroup (⟨0, ∅⟩ : RayClassModulus K) →* ℂˣ := 1
  let E : ℂ → ℂ := trivialEulerFactor m
  let G : ℂ → ℂ := fun s => G₀ s * E s
  have hEdiff : Differentiable ℂ E := by
    simpa [E] using trivialEulerFactor_differentiable (K := K) m
  have hGdiff : Differentiable ℂ G := by
    dsimp [G]
    exact hG₀diff.mul hEdiff
  have hAgree : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ m.finitePart.support →
      charValue (1 : RayClassGroup m →* ℂˣ) v.asIdeal = charValue η₀ v.asIdeal := by
    intro v hv
    have hm := charValue_trivial_prime_of_not_mem m v hv
    have hv₀ : v ∉ (⟨0, ∅⟩ : RayClassModulus K).finitePart.support := by simp
    have hzero : charValue η₀ v.asIdeal = 1 := by
      simpa [η₀] using charValue_trivial_prime_of_not_mem
        (⟨0, ∅⟩ : RayClassModulus K) v hv₀
    rw [hm, hzero]
  have hchange : ∀ s : ℂ, 1 < s.re →
      LSeriesRay (1 : RayClassGroup m →* ℂˣ) s =
        LSeriesRay η₀ s * ∏ v ∈ m.finitePart.support,
          (1 - charValue η₀ v.asIdeal *
            ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) := by
    intro s hs
    exact LSeriesRay_change_modulus
      (η := (1 : RayClassGroup m →* ℂˣ)) (η' := η₀) hAgree hs
  have htrivial : ∀ s : ℂ, LSeriesRay η₀ s = dedekindZeta K s := by
    intro s
    dsimp [η₀]
    exact LSeriesRay_trivial_eq_dedekindZeta (K := K) s
  have hfactor : ∀ s : ℂ,
      (∏ v ∈ m.finitePart.support,
        (1 - charValue η₀ v.asIdeal *
          ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))) = E s := by
    intro s
    unfold E trivialEulerFactor
    apply Finset.prod_congr rfl
    intro v hv
    have hv₀ : v ∉ (⟨0, ∅⟩ : RayClassModulus K).finitePart.support := by simp
    rw [show charValue η₀ v.asIdeal = 1 by
      simpa [η₀] using charValue_trivial_prime_of_not_mem
        (⟨0, ∅⟩ : RayClassModulus K) v hv₀]
    ring
  have hGeq : ∀ s : ℂ, 1 < s.re →
      G s = (s - 1) * LSeriesRay (1 : RayClassGroup m →* ℂˣ) s := by
    intro s hs
    have hchange' := hchange s hs
    calc
      G s = G₀ s * E s := rfl
      _ = (s - 1) * dedekindZeta K s * E s := by rw [hG₀eq s hs]
      _ = (s - 1) * LSeriesRay (1 : RayClassGroup m →* ℂˣ) s := by
        rw [hchange', htrivial s, hfactor s]
        ring
  have hNreal (v : HeightOneSpectrum (𝓞 K)) :
      (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 := by
    have hNnat : Ideal.absNorm v.asIdeal ≠ 0 := by
      intro h
      exact v.ne_bot ((Ideal.absNorm_eq_zero_iff).mp h)
    exact_mod_cast hNnat
  have hEone : E 1 =
      ((∏ v ∈ m.finitePart.support,
        (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹) : ℝ) : ℂ) := by
    unfold E trivialEulerFactor
    calc
      (∏ v ∈ m.finitePart.support,
          (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(1 : ℂ)))) =
          ∏ v ∈ m.finitePart.support,
            (((1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹) : ℝ) : ℂ) := by
        apply Finset.prod_congr rfl
        intro v hv
        have hNnat : Ideal.absNorm v.asIdeal ≠ 0 := by
          intro h
          exact v.ne_bot ((Ideal.absNorm_eq_zero_iff).mp h)
        have hNcomplex : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
          exact_mod_cast hNnat
        have hbase : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) =
            ((Ideal.absNorm v.asIdeal : ℝ) : ℂ) := by norm_cast
        have hpow : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(1 : ℂ)) =
            (((Ideal.absNorm v.asIdeal : ℝ)⁻¹ : ℝ) : ℂ) := by
          rw [show (-(1 : ℂ)) = (-1 : ℂ) by norm_num,
            Complex.cpow_neg, Complex.cpow_one, hbase]
          rw [← Complex.ofReal_inv]
        rw [hpow]
        push_cast
        ring
      _ = ((∏ v ∈ m.finitePart.support,
          (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹) : ℝ) : ℂ) := by
        norm_cast
  have hGone : G 1 =
      ((dedekindZeta_residue K * ∏ v ∈ m.finitePart.support,
        (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹) : ℝ) : ℂ) := by
    change G₀ 1 * E 1 = _
    rw [hG₀one, hEone]
    push_cast
    ring
  exact ⟨G, hGdiff, hGeq, hGone⟩

/-- **(H1) Continuation, nontrivial characters: entire.**
Consumers: B `ext:hecke-L-holomorphic` (via `sp:quotient-factor`), §5 below;
A2 `zf:convexity`, `zf:detector-shift`, `zf:reciprocal-bound`, `zf:small-rows`,
`zf:intermediate-rows`. -/
theorem LSeriesRay_entire [IsTotallyComplex K] {m : RayClassModulus K}
    (η : RayClassGroup m →* ℂˣ) (hη : η ≠ 1) :
    ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧ ∀ s : ℂ, 1 < s.re → Λ s = LSeriesRay η s := by
  classical
  obtain ⟨R⟩ := exists_integralRayRepresentatives m
  apply LSeriesRay_entire_of_real_rayMellinAgreement R η hη
  intro C σ hσ
  have h := rayFEPair_Λ_eq_partialZeta_real m
    ⟨R.ideal C, mem_nonZeroDivisors_of_ne_zero (R.coprime C).1⟩ (R.coprime C) hσ
  have hclass : (rayClass m (R.ideal C) (R.coprime C))⁻¹ = C := by
    rw [R.class_eq C]
    exact inv_inv C
  simpa only [hclass] using h

end ArtinPrimitiveRoots.Hecke
