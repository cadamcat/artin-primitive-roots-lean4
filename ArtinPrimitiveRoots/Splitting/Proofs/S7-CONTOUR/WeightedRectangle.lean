import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».RectangleResidues
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».RectanglePatch

set_option autoImplicit false

open scoped NumberField Interval BigOperators
open NumberField MeasureTheory intervalIntegral

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.s7sol_mellin

open ArtinPrimitiveRoots.Splitting

/-- Separate the endpoint and nontrivial-zero residues of a weighted sharp logarithmic derivative. -/
theorem sharp_weighted_rectangle_identity (K : Type*) [Field K] [NumberField K]
    (W : ℂ → ℂ) (hW : Differentiable ℂ W) (a b : ℝ) (ha : a < 0) (hb : 0 < b)
    (hna : ∀ ρ ∈ nontrivialZeros K, ρ.im ≠ a)
    (hnb : ∀ ρ ∈ nontrivialZeros K, ρ.im ≠ b)
    (Z : Finset ℂ)
    (hZ : ∀ ρ : ℂ, ρ ∈ Z ↔ ρ ∈ nontrivialZeros K ∧ a ≤ ρ.im ∧ ρ.im ≤ b) :
    let H : ℂ → ℂ := fun s => dedekindZetaLogDerivative K s * W s
    (∫ t : ℝ in (-1 / 2 : ℝ)..2, H ((t : ℂ) + (a : ℂ) * Complex.I)) -
      (∫ t : ℝ in (-1 / 2 : ℝ)..2, H ((t : ℂ) + (b : ℂ) * Complex.I)) +
      Complex.I * (∫ t : ℝ in a..b, H ((2 : ℂ) + (t : ℂ) * Complex.I)) -
      Complex.I * (∫ t : ℝ in a..b,
        H (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) =
      2 * (Real.pi : ℂ) * Complex.I *
        (W 1 -
          ((InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1 : ℕ) : ℂ) * W 0 -
          ∑ ρ ∈ Z, (zeroMultiplicity K ρ : ℂ) * W ρ) := by
  classical
  let H : ℂ → ℂ := fun s => dedekindZetaLogDerivative K s * W s
  obtain ⟨S, G, hS, hG, hEq⟩ := sharp_weighted_rectangle_patch K W hW a b
  let coeff : ℂ → ℂ := fun p => if p = 1 then W 1 else if p = 0 then
    -((InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1 : ℕ) : ℂ) * W 0
    else -(zeroMultiplicity K p : ℂ) * W p
  have hinside : ∀ p ∈ S, (-1 / 2 : ℝ) < p.re ∧ p.re < 2 ∧ a < p.im ∧ p.im < b := by
    intro p hp
    rcases (hS p).mp hp with hp₀ | hp₁ | hpz
    · subst p
      refine ⟨by norm_num, by norm_num, ?_, ?_⟩
      · simpa using ha
      · simpa using hb
    · subst p
      refine ⟨by norm_num, by norm_num, ?_, ?_⟩
      · simpa using ha
      · simpa using hb
    · refine ⟨by linarith [hpz.1.1], by linarith [hpz.1.2.1], ?_, ?_⟩
      · exact lt_of_le_of_ne hpz.2.1 (hna p hpz.1).symm
      · exact lt_of_le_of_ne hpz.2.2 (hnb p hpz.1)
  have hres := rectangle_finite_residues H G S coeff (-1 / 2) 2 a b
    (by norm_num) (ha.le.trans hb.le) hinside hG (by
      intro s hs
      exact hEq s hs)
  have hZ₀ : (0 : ℂ) ∉ Z := by
    intro hp
    have hpos := ((hZ 0).mp hp).1.1
    simpa using hpos
  have hZ₁ : (1 : ℂ) ∉ Z := by
    intro hp
    have hlt := ((hZ 1).mp hp).1.2.1
    simpa using hlt
  have hSet : S = insert (0 : ℂ) (insert 1 Z) := by
    ext p
    rw [hS p]
    simp only [Finset.mem_insert, hZ]
  have hcoefZ : (∑ p ∈ Z, coeff p) = -∑ p ∈ Z, (zeroMultiplicity K p : ℂ) * W p := by
    calc
      _ = ∑ p ∈ Z, -((zeroMultiplicity K p : ℂ) * W p) := by
        apply Finset.sum_congr rfl
        intro p hp
        have hp₀ : p ≠ 0 := by
          intro heq
          subst p
          exact hZ₀ hp
        have hp₁ : p ≠ 1 := by
          intro heq
          subst p
          exact hZ₁ hp
        simp [coeff, hp₀, hp₁, neg_mul]
      _ = _ := Finset.sum_neg_distrib (fun p : ℂ => (zeroMultiplicity K p : ℂ) * W p)
  have hsum : (∑ p ∈ S, coeff p) = W 1 -
      ((InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1 : ℕ) : ℂ) * W 0 -
      ∑ p ∈ Z, (zeroMultiplicity K p : ℂ) * W p := by
    have h0not : (0 : ℂ) ∉ insert 1 Z := by simp [hZ₀]
    rw [hSet, Finset.sum_insert h0not, Finset.sum_insert hZ₁, hcoefZ]
    simp [coeff]
    <;> ring
  rw [hsum] at hres
  simpa [H] using hres

end ArtinPrimitiveRoots.Proofs.s7sol_mellin
