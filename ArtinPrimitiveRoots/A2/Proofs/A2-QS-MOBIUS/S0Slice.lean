import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-MOBIUS».S0

/-!
# A2-QS-MOBIUS, part S0: class/dyad slicing for positive row scale

`qs_class_dyad_slice_S0` has no hypothesis on the row scale `M`.  For `M ≤ 0` every row has
`N a / M ≤ 0`, where the cap weight need not vanish (`W(0) ≥ 1`), so `qsHighEnergy` has no
finite row support and the Cauchy–Schwarz step over the parts has no finite sum to act on.  The
corrected statement below adds `0 < M` and is otherwise identical.  With `0 < M`,
`W(N a / M) = 0` once `N a ≥ 5M/2`, so each energy is a finite sum.  Its consumer is the
high-core bound B0 (`qs_high_core_bound_B0`), whose rows are empty at `M = 0` and which has
`M > 0` otherwise.
-/

set_option autoImplicit false

open scoped NumberField ComplexConjugate
open NumberField IsDedekindDomain
open ClassFieldTheory

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]
variable {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}

/-- S0 (IMPL, corrected `qs_class_dyad_slice_S0`): class and dyad slicing for `0 < M`: the
up-to columns split into at most `h_m (⌈log₂ N⌉₊ + 1)` pairwise disjoint parts, each inside one
ray class and one dyad `(N/2^{j+1}, N/2^j]`, and the high-core energy is at most the number of
parts times the sum of the part energies. -/
theorem qs_class_dyad_slice_pos_S0 (F : QSFamily m qS) (W : ℝ → ℝ) (hW : IsCapWeight W)
    (M N κ : ℝ) (hM : 0 < M) (hN : 1 ≤ N) (z : Ideal (𝓞 K) → ℂ) :
    ∃ parts : Finset (Finset (Ideal (𝓞 K))),
      ((parts.card : ℕ) : ℝ) ≤
          (Nat.card (ClassFieldTheory.RayClassGroup m) : ℝ) *
            ((Nat.ceil (Real.logb 2 N) + 1 : ℕ) : ℝ) ∧
      (∀ P ∈ parts, P ⊆ qsUpTo m qS N) ∧
      (∀ P ∈ parts, ∀ Q ∈ parts, P ≠ Q → Disjoint P Q) ∧
      (∀ P ∈ parts, ∃ j : ℕ, ∀ c ∈ P, N / 2 ^ (j + 1) < qsN c ∧ qsN c ≤ N / 2 ^ j) ∧
      (∀ P ∈ parts, ∀ c ∈ P, ∀ d ∈ P, ∃ (hc : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m c)
        (hd : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m d),
        ArtinPrimitiveRoots.Hecke.rayClass m c hc = ArtinPrimitiveRoots.Hecke.rayClass m d hd) ∧
      qsHighEnergy F W M κ (qsUpTo m qS N) z ≤
        ((parts.card : ℕ) : ℝ) * ∑ P ∈ parts, qsHighEnergy F W M κ P z := by
  sorry

end ArtinPrimitiveRoots.A2
