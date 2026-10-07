import ArtinPrimitiveRoots.Ext.SplittingInputs
import ArtinPrimitiveRoots.Hecke.Boundary

/-!
# §7 algebraic field and splitting nodes

Blueprint nodes `spl:kummer-degree`, `spl:discriminant-bound`, `spl:field-bounds`,
`sp:compositum`, and `alg:splitting-test`; source `07-splitting.tex:37-99` and
`01a-reduction.tex:69-99`.
-/

set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ArtinPrimitiveRoots.Splitting

open ArtinPrimitiveRoots.Ext.SplittingInputs

/-- **`spl:kummer-degree`**, `07-splitting.tex:37-51`. For `q > log₂ |a|`, the Kummer
polynomial is irreducible over `E_q`, its splitting field has relative degree `q`, and the
absolute degree is `q(q-1)`. The Galois group over `E_q` is identified with `μ_q` by
`ext:kummer-galois`. -/
theorem spl_kummer_degree (a : ℤ) (ha : 1 < |a|) (q : ℕ) [NeZero q] (hq : q.Prime)
    (hqlarge : Nat.log2 a.natAbs < q) :
    Irreducible (kummerPolynomial a q) ∧
      Module.finrank (cyclotomicField q) (kummerField a q) = q ∧
      Module.finrank ℚ (cyclotomicField q) = q - 1 ∧
      kummerDegree a q = q * (q - 1) ∧
      Nonempty (Gal(kummerField a q / cyclotomicField q) ≃*
        rootsOfUnity q (cyclotomicField q)) := by
  sorry

/-- **`spl:discriminant-bound`**, `07-splitting.tex:53-68`. The norm-argument degree node and
the discriminant tower yield the power-basis discriminant bound and a logarithmic estimate. The
constant depends on `a`, not on `q`. -/
theorem spl_discriminant_bound (a : ℤ) (ha : 1 < |a|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q], q.Prime →
      Nat.log2 a.natAbs < q →
        absoluteDiscriminant (kummerField a q) ≤
            (q : ℝ) ^ (q * (q - 2)) *
              ((q : ℝ) ^ q * (a.natAbs : ℝ) ^ (q - 1)) ^ (q - 1) ∧
          Real.log (absoluteDiscriminant (kummerField a q)) + kummerDegree a q ≤
            C * (kummerDegree a q : ℝ) * Real.log (2 * (q : ℝ)) := by
  sorry

/-- **`spl:field-bounds`**, `07-splitting.tex:19-99`. There are thresholds and constants
depending only on `a` such that, for every sufficiently large prime `q`, the degree and
discriminant estimates and the inherited zero-free region hold. The unramifiedness clause is not
consumed by §7's splitting test. -/
theorem spl_field_bounds (a : ℤ) (ha : 1 < |a|) :
    ∃ qₐ : ℕ, ∃ C : ℝ, 5 ≤ qₐ ∧ 0 < C ∧
      ∀ (q : ℕ) [NeZero q], q.Prime → qₐ ≤ q →
        kummerDegree a q = q * (q - 1) ∧
        absoluteDiscriminant (kummerField a q) ≤
          (q : ℝ) ^ (q * (q - 2)) *
            ((q : ℝ) ^ q * (a.natAbs : ℝ) ^ (q - 1)) ^ (q - 1) ∧
        Real.log (absoluteDiscriminant (kummerField a q)) + kummerDegree a q ≤
          C * (kummerDegree a q : ℝ) * Real.log (2 * (q : ℝ)) ∧
        IsGalois ℚ (kummerField a q) ∧
        (∀ p : ℕ, p.Prime → ¬ (p : ℤ) ∣ a * (q : ℤ) →
          (Ideal.span {(p : ℤ)}).ramificationIdxIn (𝓞 (kummerField a q)) = 1) ∧
        ∀ s : ℂ, 1 - ArtinPrimitiveRoots.HeckeBoundary.δ₀ < s.re → s ≠ 1 →
          meromorphicOrderAt (dedekindZetaSharp (kummerField a q)) s ≤ 0 := by
  sorry

/-- **`alg:splitting-test`** (only `⇐`), `01a-reduction.tex:69-99`. The elementary Kummer
congruences imply complete splitting in `K_q`. The explicit `p ∤ aq` hypothesis is retained from
the source statement. -/
theorem alg_splitting_test (a : ℤ) (ha0 : a ≠ 0) (p q : ℕ) [NeZero q]
    (hp : p.Prime) (hq : q.Prime)
    (hpaq : ¬ (p : ℤ) ∣ a * (q : ℤ))
    (hclass : q ∣ p - 1)
    (hpow : (a : ZMod p) ^ ((p - 1) / q) = 1) :
    splitsCompletely (kummerField a q) p := by
  sorry

/-- **`sp:compositum`**, `07-splitting.tex:70-77`. The chosen top field represents `K_qF_q`.
Its extension over `F_q` is cyclic of degree dividing `q`; over `K_q` it is abelian of exponent
two. All three fields are totally imaginary. -/
theorem sp_compositum (a : ℤ) (ha : 1 < |a|) (q : ℕ) [NeZero q] [NeZero (12 * q)] (hq : q.Prime)
    (hq5 : 5 ≤ q) :
    ∃ dK : AbelianExtensionData (kummerField a q) (compositumField a q),
    ∃ dF : AbelianExtensionData (heckeBaseField q) (compositumField a q),
      letI : AbelianExtensionData (kummerField a q) (compositumField a q) := dK
      letI : AbelianExtensionData (heckeBaseField q) (compositumField a q) := dF
      IsTotallyComplex (kummerField a q) ∧
      IsTotallyComplex (heckeBaseField q) ∧
      IsTotallyComplex (compositumField a q) ∧
      Module.finrank (heckeBaseField q) (compositumField a q) ≤ q ∧
      (∀ σ : Gal(compositumField a q / heckeBaseField q), σ ^ q = 1) ∧
      (∀ σ : Gal(compositumField a q / kummerField a q), σ ^ 2 = 1) ∧
      Nat.card (Gal(compositumField a q / kummerField a q)) ≤ 4 := by
  sorry

end ArtinPrimitiveRoots.Splitting

end
