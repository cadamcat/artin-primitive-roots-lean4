import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import ArtinPrimitiveRoots.A1.Field

/-! A neighborhood of sixth powers in each finite completion. -/

set_option autoImplicit false
open NumberField IsDedekindDomain Filter Topology
open scoped Classical WithZero
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.th_cover_sol

open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]

/-- Every sufficiently small principal unit is a sixth power. -/
theorem exists_sixthPowerNeighborhood (v : FinPlace F) :
    ∃ m0 : ℕ, 1 ≤ m0 ∧ ∀ u : (v.adicCompletion F)ˣ,
      Valued.v ((u : v.adicCompletion F) - 1) ≤ WithZero.exp (-(m0 : ℤ)) →
        ∃ r : (v.adicCompletion F)ˣ, u = r ^ 6 := by
  let K := v.adicCompletion F
  let : NontriviallyNormedField K := Valued.toNontriviallyNormedField K ℤᵐ⁰
  let : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  have h6 : (6 : K) ≠ 0 := by norm_num
  have hf : HasStrictDerivAt (fun x : K => x ^ 6) (6 : K) 1 := by
    simpa using hasStrictDerivAt_pow 6 (1 : K)
  have hroot : {u : K | ∃ r : K, r ^ 6 = u} ∈ nhds (1 : K) := by
    have heq : Filter.map (fun x : K => x ^ 6) (nhds 1) = nhds 1 := by
      simpa only [one_pow] using hf.map_nhds_eq h6
    rw [← heq]
    change {x : K | ∃ r : K, r ^ 6 = x ^ 6} ∈ nhds (1 : K)
    exact Filter.Eventually.of_forall fun r => ⟨r, rfl⟩
  obtain ⟨γ, hγ⟩ := (Valued.mem_nhds (Γ₀ := ℤᵐ⁰)).mp hroot
  let γ' : ℤᵐ⁰ˣ := Units.map
    (MonoidWithZeroHom.ValueGroup₀.embedding (f := .ofClass (Valued.v : Valuation K ℤᵐ⁰))) γ
  let n : ℤ := WithZero.log (γ' : ℤᵐ⁰)
  let m0 : ℕ := (1 - n).toNat + 1
  have hm0 : -(m0 : ℤ) < n := by
    dsimp [m0]
    omega
  refine ⟨m0, by omega, fun u hu => ?_⟩
  have huγ : Valued.v ((u : K) - 1) < (γ' : ℤᵐ⁰) := by
    apply lt_of_le_of_lt hu
    rw [← WithZero.exp_log γ'.ne_zero]
    exact WithZero.exp_lt_exp.mpr hm0
  have huγ' : (Valued.v : Valuation K ℤᵐ⁰).restrict ((u : K) - 1) < γ := by
    rw [Valuation.restrict_lt_iff_lt_embedding]
    exact huγ
  obtain ⟨r, hr⟩ := hγ huγ'
  have hr0 : r ≠ 0 := by
    intro hr0
    simpa [hr0] using hr.trans_ne u.ne_zero
  refine ⟨Units.mk0 r hr0, ?_⟩
  apply Units.ext
  simpa using hr.symm

end ArtinPrimitiveRoots.Proofs.th_cover_sol
