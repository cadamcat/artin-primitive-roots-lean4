import ArtinPrimitiveRoots.Proofs.qs_nq0_sol.GlobalCharacter
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.Valued.ValuationTopology

/-!
# Uniform local bounds for the canonical quadratic family

The first conductor helper, in this module's context, is:
```
theorem qs_nq0_adic_square_congruence (v : FinPlace K) :
    ∃ e : ℕ, 0 < e ∧
      ∀ u : (v.adicCompletion K)ˣ,
        Valued.v ((u : v.adicCompletion K) - 1) ≤
          WithZero.exp (-(e : ℤ)) →
        ∃ b : (v.adicCompletion K)ˣ, u = b ^ 2
```
The square neighborhood comes from the strict inverse function theorem.
The valuation basis then supplies a positive integral congruence exponent.
-/

set_option autoImplicit false

open scoped NumberField Topology WithZero
open NumberField IsDedekindDomain ArtinPrimitiveRoots.A1

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]

/-- A fixed sufficiently deep congruence neighborhood at a finite place consists of squares. -/
theorem qs_nq0_adic_square_congruence (v : FinPlace K) :
    ∃ e : ℕ, 0 < e ∧
      ∀ u : (v.adicCompletion K)ˣ,
        Valued.v ((u : v.adicCompletion K) - 1) ≤
          WithZero.exp (-(e : ℤ)) →
        ∃ b : (v.adicCompletion K)ˣ, u = b ^ 2 := by
  let L := v.adicCompletion K
  obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  let x : L := NumberField.FinitePlace.embedding v (algebraMap (𝓞 K) K t)
  have htK : algebraMap (𝓞 K) K t ≠ 0 :=
    NumberField.RingOfIntegers.coe_ne_zero_iff.mpr ht0
  have hx0 : x ≠ 0 := (NumberField.FinitePlace.embedding v).injective.ne htK
  have hxnorm : ‖x‖ < 1 :=
    (NumberField.FinitePlace.norm_lt_one_iff_mem (K := K) v t).mpr ht
  let : NontriviallyNormedField L :=
    NontriviallyNormedField.ofNormNeOne ⟨x, hx0, ne_of_lt hxnorm⟩
  have h2 : (2 : L) ≠ 0 := by
    intro h
    have hk : (2 : K) = 0 := (algebraMap K L).injective
      (by simpa only [map_ofNat, map_zero] using h)
    exact (two_ne_zero : (2 : K) ≠ 0) hk
  have hs := qs_nq0_power_units_neighborhood L 2 h2
  rw [(Units.isEmbedding_val₀ (G₀ := L)).isInducing.nhds_eq_comap 1] at hs
  obtain ⟨V, hV, hVs⟩ := Filter.mem_comap.mp hs
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp hV
  let δ : ℤᵐ⁰ˣ := Units.map
    (MonoidWithZeroHom.ValueGroup₀.embedding
      (f := (.ofClass (Valued.v : Valuation L ℤᵐ⁰)))) γ
  let e : ℕ := (-WithZero.log (δ : ℤᵐ⁰)).toNat + 1
  have hbound : WithZero.exp (-(e : ℤ)) < (δ : ℤᵐ⁰) := by
    rw [← WithZero.exp_log (Units.ne_zero δ), WithZero.exp_lt_exp]
    dsimp only [e]
    omega
  refine ⟨e, by dsimp only [e]; omega, ?_⟩
  intro u hu
  apply hVs
  apply hγ
  change (Valued.v : Valuation L ℤᵐ⁰).restrict ((u : L) - 1) < (γ : _)
  rw [Valuation.restrict_lt_iff_lt_embedding]
  exact lt_of_le_of_lt hu hbound

end ArtinPrimitiveRoots.A2
