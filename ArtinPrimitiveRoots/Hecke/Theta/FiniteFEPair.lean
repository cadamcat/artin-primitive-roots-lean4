import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import ArtinPrimitiveRoots.Hecke.Theta.CharacterOrthogonality

/-!
# Finite linear combinations of functional-equation pairs

This helper combines finitely many weight-one `WeakFEPair`s. The combined constant terms are
their character-weighted sums, so orthogonality can make both constant terms vanish.
-/

set_option autoImplicit false

open Set Filter
open MeasureTheory
open scoped Topology BigOperators

noncomputable section

namespace ArtinPrimitiveRoots.Hecke.Theta

private theorem locallyIntegrableOn_finiteSum {ι : Type*} (s : Finset ι)
    (f : ι → ℝ → ℂ) (hf : ∀ i ∈ s, LocallyIntegrableOn (f i) (Ioi 0)) :
    LocallyIntegrableOn (∑ i ∈ s, f i) (Ioi 0) := by
  exact Finset.sum_induction f (fun g => LocallyIntegrableOn g (Ioi 0))
    (fun _ _ => LocallyIntegrableOn.add) (locallyIntegrableOn_const 0) hf

/-- The finite weighted sum of pairs with a common weight, with their root numbers absorbed into
the dual component. -/
def finiteFEPair {ι : Type*} [Fintype ι] (k : ℝ) (hk : 0 < k)
    (P : ι → WeakFEPair ℂ) (hP : ∀ i, (P i).k = k) (w : ι → ℂ) :
    WeakFEPair ℂ where
  f := ∑ i, w i • (P i).f
  g := ∑ i, (w i * (P i).ε) • (P i).g
  k := k
  ε := 1
  f₀ := ∑ i, w i * (P i).f₀
  g₀ := ∑ i, w i * (P i).ε * (P i).g₀
  hf_int := locallyIntegrableOn_finiteSum Finset.univ _
    (fun i _ => (P i).hf_int.smul (w i))
  hg_int := locallyIntegrableOn_finiteSum Finset.univ _
    (fun i _ => (P i).hg_int.smul (w i * (P i).ε))
  hk := hk
  hε := one_ne_zero
  h_feq x hx := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, one_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [(P i).h_feq x hx, hP i]
    simp only [smul_eq_mul]
    ring
  hf_top r := by
    have h := Asymptotics.IsBigO.fun_sum (s := Finset.univ)
      (fun i _ => ((P i).hf_top r).const_mul_left (w i))
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← Finset.sum_sub_distrib,
      mul_sub] using h
  hg_top r := by
    have h := Asymptotics.IsBigO.fun_sum (s := Finset.univ)
      (fun i _ => ((P i).hg_top r).const_mul_left (w i * (P i).ε))
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← Finset.sum_sub_distrib,
      mul_sub] using h

/-- Orthogonality cancels a class-independent constant term in a finite character-weighted pair. -/
theorem finiteFEPair_f₀_eq_zero_of_nontrivialCharacter {G : Type*} [Group G] [Fintype G]
    (χ : G →* ℂˣ) (hχ : χ ≠ 1) (P : G → WeakFEPair ℂ)
    (c : ℂ) (hc : ∀ g, (P g).f₀ = c) (k : ℝ) (hk : 0 < k)
    (hP : ∀ g, (P g).k = k) :
    (finiteFEPair k hk P hP (fun g => (χ g : ℂ))).f₀ = 0 := by
  classical
  change ∑ g : G, (χ g : ℂ) * (P g).f₀ = 0
  calc
    ∑ g : G, (χ g : ℂ) * (P g).f₀ = ∑ g : G, (χ g : ℂ) * c := by
      apply Finset.sum_congr rfl
      intro g _
      rw [hc]
    _ = (∑ g : G, (χ g : ℂ)) * c := by rw [← Finset.sum_mul]
    _ = 0 := by rw [sum_char_eq_zero_of_nontrivial χ hχ]; simp

/-- The dual constant term cancels when the root-number-weighted constants are independent of
the character index. -/
theorem finiteFEPair_g₀_eq_zero_of_nontrivialCharacter {G : Type*} [Group G] [Fintype G]
    (χ : G →* ℂˣ) (hχ : χ ≠ 1) (P : G → WeakFEPair ℂ)
    (c : ℂ) (hc : ∀ g, (P g).ε * (P g).g₀ = c) (k : ℝ) (hk : 0 < k)
    (hP : ∀ g, (P g).k = k) :
    (finiteFEPair k hk P hP (fun g => (χ g : ℂ))).g₀ = 0 := by
  classical
  change ∑ g : G, (χ g : ℂ) * (P g).ε * (P g).g₀ = 0
  calc
    ∑ g : G, (χ g : ℂ) * (P g).ε * (P g).g₀ =
        ∑ g : G, (χ g : ℂ) * c := by
      apply Finset.sum_congr rfl
      intro g _
      rw [mul_assoc, hc]
    _ = (∑ g : G, (χ g : ℂ)) * c := by rw [← Finset.sum_mul]
    _ = 0 := by rw [sum_char_eq_zero_of_nontrivial χ hχ]; simp

/-- A character-weighted finite pair is entire once its two constant terms are class-independent:
orthogonality makes it a strong pair, and Mathlib's strong-pair theorem supplies differentiability. -/
theorem finiteFEPair_character_differentiable {G : Type*} [Group G] [Fintype G]
    (χ : G →* ℂˣ) (hχ : χ ≠ 1) (P : G → WeakFEPair ℂ)
    (k : ℝ) (hk : 0 < k) (hP : ∀ g, (P g).k = k)
    (cf cg : ℂ) (hcf : ∀ g, (P g).f₀ = cf)
    (hcg : ∀ g, (P g).ε * (P g).g₀ = cg) :
    Differentiable ℂ (finiteFEPair k hk P hP (fun g => (χ g : ℂ))).Λ := by
  let Q := finiteFEPair k hk P hP (fun g => (χ g : ℂ))
  have hQ : IsStrongFEPair Q := {
    hf₀ := finiteFEPair_f₀_eq_zero_of_nontrivialCharacter χ hχ P cf hcf k hk hP
    hg₀ := finiteFEPair_g₀_eq_zero_of_nontrivialCharacter χ hχ P cg hcg k hk hP
  }
  exact hQ.differentiable_Λ

end ArtinPrimitiveRoots.Hecke.Theta

end
