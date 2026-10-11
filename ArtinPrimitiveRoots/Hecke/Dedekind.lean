import ArtinPrimitiveRoots.Hecke.Defs
import ArtinPrimitiveRoots.Hecke.Dedekind.Bounds
import DedekindResidue.CompletedZeta.Existence
import DedekindResidue.CompletedZeta.FunctionalEquation

/-!
# Hecke L-function package: the Dedekind zeta function of a number field (D1, D2)

Frozen interface.
-/

set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ArtinPrimitiveRoots.Hecke

/-! ## §4 Dedekind zeta function of an arbitrary number field (B's needs) -/

/-- The completed Dedekind zeta prefactor `D^{s/2} Γ_ℝ(s)^{r₁} Γ_ℂ(s)^{r₂}` (Deligne
normalization, as AINTLIB `DedekindResidue.completedZetaPrefactor`,
`CompletedZeta/FunctionalEquation.lean:44`). -/
def dedekindPrefactor (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2) *
    (Complex.Gammaℝ s ^ InfinitePlace.nrRealPlaces K *
      Complex.Gammaℂ s ^ InfinitePlace.nrComplexPlaces K)

theorem dedekindPrefactor_eq_completedZetaPrefactor (K : Type*) [Field K] [NumberField K]
    (s : ℂ) :
  dedekindPrefactor K s = DedekindResidue.completedZetaPrefactor K s := by
  simp [dedekindPrefactor, DedekindResidue.completedZetaPrefactor,
    DedekindResidue.gammaFactor]

/-- **(D1) Hecke–Tate for `ζ_K`, every number field:** `ξ_K(s) = s(s-1)·prefactor·ζ_K(s)`
extends to an entire function with `ξ_K(1-s) = ξ_K(s)`, `ξ_K(0) = ξ_K(1) ≠ 0`.
Consumers: B `ext:dedekind-fe` (and through it `spl:left-line`, `spl:explicit-formula`,
`sp:upstairs-factor`, `spl:kummer-zero-free`, `ext:dedekind-zero-count`).
Library: AINTLIB `DedekindResidue.exists_isCompletedDedekindZeta`
(`CompletedZeta/Existence.lean:369`) and `completedDedekindZeta_one_sub` (`:412`): same
statement up to the factor `s(s-1)` and the `H`-witness form. -/
theorem dedekind_completed (K : Type*) [Field K] [NumberField K] :
    ∃ ξ : ℂ → ℂ, Differentiable ℂ ξ ∧
      (∀ s : ℂ, 1 < s.re → ξ s = s * (s - 1) * dedekindPrefactor K s * dedekindZeta K s) ∧
      (∀ s : ℂ, ξ (1 - s) = ξ s) ∧ ξ 1 ≠ 0 := by
  classical
  let ξ : ℂ → ℂ := DedekindResidue.completedDedekindZetaEntire K
  have hξ : Differentiable ℂ ξ := by
    simpa [ξ] using DedekindResidue.differentiable_completedDedekindZetaEntire K
  have hFE : ∀ s : ℂ, ξ (1 - s) = ξ s := by
    have hleft : Differentiable ℂ (fun s : ℂ => ξ (1 - s)) :=
      hξ.comp (by fun_prop)
    have hopen : IsOpen {s : ℂ | 1 < s.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have hpre : Set.EqOn (fun s : ℂ => ξ (1 - s)) ξ {s : ℂ | 1 < s.re} := by
      intro s hs
      change ξ (1 - s) = ξ s
      have hs0 : s ≠ 0 := by
        intro hz
        rw [hz] at hs
        norm_num [Complex.zero_re] at hs
      have hs1 : s ≠ 1 := by
        intro hz
        rw [hz] at hs
        norm_num [Complex.one_re] at hs
      have h10 : 1 - s ≠ 0 := by
        intro hz
        apply hs1
        calc
          s = 1 - (1 - s) := by ring
          _ = 1 := by rw [hz]; norm_num
      have h11 : 1 - s ≠ 1 := by
        intro hz
        apply hs0
        calc
          s = 1 - (1 - s) := by ring
          _ = 0 := by rw [hz]; ring
      rw [show ξ (1 - s) =
          (1 - s) * ((1 - s) - 1) * DedekindResidue.completedDedekindZeta K (1 - s) by
            simpa [ξ] using DedekindResidue.completedDedekindZetaEntire_eq K h10 h11,
        show ξ s = s * (s - 1) * DedekindResidue.completedDedekindZeta K s by
            simpa [ξ] using DedekindResidue.completedDedekindZetaEntire_eq K hs0 hs1,
        DedekindResidue.completedDedekindZeta_one_sub K s]
      ring
    have h2mem : (2 : ℂ) ∈ {s : ℂ | 1 < s.re} := by
      norm_num [Set.mem_ofPred_eq]
    have hagree := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      (𝕜 := ℂ) (f := fun s : ℂ => ξ (1 - s)) (g := ξ)
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hleft)
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hξ)
      isPreconnected_univ (Set.mem_univ (2 : ℂ))
      (hpre.eventuallyEq_of_mem (hopen.mem_nhds h2mem))
    exact fun s => hagree (Set.mem_univ s)
  have hEq : ∀ s : ℂ, 1 < s.re →
      ξ s = s * (s - 1) * dedekindPrefactor K s * dedekindZeta K s := by
    intro s hs
    have hs0 : s ≠ 0 := by
      intro hz
      rw [hz] at hs
      norm_num [Complex.zero_re] at hs
    have hs1 : s ≠ 1 := by
      intro hz
      rw [hz] at hs
      norm_num [Complex.one_re] at hs
    rw [show ξ s = s * (s - 1) * DedekindResidue.completedDedekindZeta K s by
      simpa [ξ] using DedekindResidue.completedDedekindZetaEntire_eq K hs0 hs1,
      DedekindResidue.completedDedekindZeta_eq_of_one_lt_re K hs,
      ← dedekindPrefactor_eq_completedZetaPrefactor K s]
    ring
  have hξ1 : ξ 1 ≠ 0 := by
    have hvalue : ξ 1 = ((DedekindResidue.heckeAdjust K : ℝ) : ℂ)⁻¹ *
        (2 * ((DedekindResidue.heckeFConst K : ℝ) : ℂ)) := by
      change DedekindResidue.completedDedekindZetaEntire K 1 = _
      rw [DedekindResidue.completedDedekindZetaEntire]
      have hg : (DedekindResidue.heckeFEPair K).g₀ =
          ((DedekindResidue.heckeFConst K : ℝ) : ℂ) := rfl
      rw [hg]
      ring
    have hconst : 0 < DedekindResidue.heckeFConst K := by
      rw [DedekindResidue.heckeFConst]
      have hcard : 0 < (Fintype.card (ClassGroup (𝓞 K)) : ℝ) := by
        exact_mod_cast Fintype.card_pos
      have hvol := DedekindResidue.unitBoxVol_pos K
      have htors : 0 < (NumberField.Units.torsionOrder K : ℝ) := by
        exact_mod_cast NumberField.Units.torsionOrder_pos K
      positivity
    rw [hvalue]
    refine mul_ne_zero (inv_ne_zero ?_) (mul_ne_zero two_ne_zero ?_)
    · exact_mod_cast (DedekindResidue.heckeAdjust_pos K).ne'
    · exact_mod_cast hconst.ne'
  exact ⟨ξ, hξ, hEq, hFE, hξ1⟩

/-- **(D2) Order at most one** (constant may depend on `K`): every entire `ξ` as in (D1)
satisfies `‖ξ s‖ ≤ exp(C (‖s‖ + 1) log(‖s‖ + 2))` (the form without `+ 1` fails at `s = 0`).
Consumers: B `ext:dedekind-fe` (order-one clause), `ext:hadamard-order-one`,
`spl:explicit-formula`.  Library: AINTLIB strip bound
`exists_completedDedekindZetaEntire_strip_bound` (`CompletedZeta/AnalyticControl.lean:119`)
plus Stirling for `Re s ≥ 2` and the functional equation; the global statement is new glue. -/
theorem dedekind_order_one (K : Type*) [Field K] [NumberField K] (ξ : ℂ → ℂ)
    (hξ : Differentiable ℂ ξ)
    (heq : ∀ s : ℂ, 1 < s.re → ξ s = s * (s - 1) * dedekindPrefactor K s * dedekindZeta K s) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, ‖ξ s‖ ≤ Real.exp (C * (‖s‖ + 1) * Real.log (‖s‖ + 2)) := by
  classical
  let H : ℂ → ℂ := DedekindResidue.completedDedekindZetaEntire K
  have hHdiff : Differentiable ℂ H := by
    simpa [H] using DedekindResidue.differentiable_completedDedekindZetaEntire K
  have hH_eq : ∀ s : ℂ, 1 < s.re →
      H s = s * (s - 1) * dedekindPrefactor K s * dedekindZeta K s := by
    intro s hs
    have hs0 : s ≠ 0 := by
      intro hz
      rw [hz] at hs
      norm_num [Complex.zero_re] at hs
    have hs1 : s ≠ 1 := by
      intro hz
      rw [hz] at hs
      norm_num [Complex.one_re] at hs
    rw [show H s = s * (s - 1) * DedekindResidue.completedDedekindZeta K s by
        simpa [H] using DedekindResidue.completedDedekindZetaEntire_eq K hs0 hs1,
      DedekindResidue.completedDedekindZeta_eq_of_one_lt_re K hs,
      ← dedekindPrefactor_eq_completedZetaPrefactor K s]
    ring
  have hopen : IsOpen {s : ℂ | 1 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hpre : Set.EqOn ξ H {s : ℂ | 1 < s.re} := by
    intro s hs
    calc ξ s = s * (s - 1) * dedekindPrefactor K s * dedekindZeta K s := heq s hs
      _ = H s := (hH_eq s hs).symm
  have h2mem : (2 : ℂ) ∈ {s : ℂ | 1 < s.re} := by norm_num [Complex.ofReal_re]
  have hagree := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (𝕜 := ℂ) (f := ξ) (g := H)
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hξ)
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hHdiff)
    isPreconnected_univ (Set.mem_univ (2 : ℂ))
    (hpre.eventuallyEq_of_mem (hopen.mem_nhds h2mem))
  have hident : ∀ s : ℂ, ξ s = H s := fun s => hagree (Set.mem_univ s)
  obtain ⟨C, hC, hbound⟩ := DedekindBounds.exists_completedDedekindZetaEntire_order_one K
  refine ⟨C, hC, fun s => ?_⟩
  rw [hident s]
  simpa [H] using hbound s

end ArtinPrimitiveRoots.Hecke
