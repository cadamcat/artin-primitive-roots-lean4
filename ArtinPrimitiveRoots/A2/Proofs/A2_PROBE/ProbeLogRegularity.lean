import ArtinPrimitiveRoots.A2.Interface
import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE.LogArchKernel
import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE.LogFamilyRegularity

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical Topology
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_probe_sol

open ArtinPrimitiveRoots A1 A2

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}
variable {μ : ∀ v : FinPlace F, Theta.LocHaar v} {v0 : InfinitePlace F}

/-- The tensor probe kernel in the logarithm of the positive scale. -/
def probeLogKernel (D : FieldData F) (S : SData F CE condη)
    (G : SheetGeometry D S μ v0) (f0 : S.FS → ℂ) (f1 : ℝ → ℂ)
    (u : ℝ) (x : S.FS) : ℂ :=
  ((Real.exp u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * f1 (Real.exp u) *
    f0 (x * ((G.ellU (Real.exp u))⁻¹ : S.FSˣ).val)

/-- Real derivatives of the logarithmic probe kernel are jointly continuous, including
the finite-place parameters. Only the archimedean tensor participates in real calculus. -/
theorem probe_log_regular (D : FieldData F) (S : SData F CE condη)
    (G : SheetGeometry D S μ v0) (f0 : S.FS → ℂ) (f1 : ℝ → ℂ)
    (arch : InfinitePlace F → SchwartzMap ℂ ℂ) (finite : ∀ v : S.Sf, S.FiniteTest v)
    (hf1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f1)
    (htensor : ∀ y, f0 y = (∏ v : S.Sf, (finite v).1 (y.1 v)) *
      ∏ w : InfinitePlace F, arch w (y.2 w)) :
    (∀ x : S.FS, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : ℝ => probeLogKernel D S G f0 f1 u x)) ∧
      ∀ n : ℕ, Continuous (fun p : ℝ × S.FS =>
        iteratedDeriv n (fun u : ℝ => probeLogKernel D S G f0 f1 u p.2) p.1) := by
  let κ : ℝ := 1 / (2 * (numComplex F : ℝ))
  let c : (∀ v : S.Sf, v.1.adicCompletion F) → ℂ :=
    fun y => ∏ v : S.Sf, (finite v).1 (y v)
  have hc : Continuous c := by
    apply continuous_finsetProd
    intro v _
    exact (finite v).2.1.comp (continuous_apply v)
  have hpow (u r : ℝ) : Real.exp u ^ r = Real.exp (u * r) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos u), Real.log_exp]
  have hinverse (u : ℝ) :
      ((G.ellU (Real.exp u))⁻¹ : S.FSˣ).val =
        ((fun _ : S.Sf => 1),
          fun _ : InfinitePlace F => ((Real.exp (-κ * u) : ℝ) : ℂ)) := by
    rw [Units.val_inv_eq_inv_val, G.ellU_val (Real.exp u) (Real.exp_pos u)]
    apply Prod.ext
    · funext v
      simp [SData.ell]
    · funext w
      simp [SData.ell, κ, hpow, Real.exp_neg, mul_comm]
  have hkernel (u : ℝ) (x : S.FS) :
      probeLogKernel D S G f0 f1 u x = c x.1 * archLogKernel f1 arch κ (u, x.2) := by
    have hhalf : Real.exp u ^ (-(1 / 2 : ℝ)) = Real.exp (-u / 2) := by
      rw [hpow]
      congr 1
      ring
    rw [probeLogKernel, hhalf, htensor, hinverse]
    simp only [Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, mul_one]
    dsimp [c, archLogKernel]
    ring
  have hregular := separated_family_regular c hc (archLogKernel f1 arch κ)
    (archLogKernel_smooth f1 arch κ hf1)
  constructor
  · intro x
    simpa only [hkernel] using hregular.1 x
  · intro n
    simpa only [hkernel] using hregular.2 n

end ArtinPrimitiveRoots.Proofs.a2_probe_sol
