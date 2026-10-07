import ArtinPrimitiveRoots.Proofs.qs_nq0_sol.Generators
import ArtinPrimitiveRoots.A1.Characters

/-!
# Local quadratic characters for the narrow family

Read the cubed Hilbert symbol through the fixed complex embedding. The
algebraic local character is quadratic because the Hilbert value is a sixth
root of unity. Continuity and global descent are subsequent steps.

The remaining intermediate statements, in this module's context, are:
```
theorem qs_nq0_quadratic_local_continuous (D : FieldData K) (H : HilbertData K)
    (v : FinPlace K) (a : (v.adicCompletion K)ˣ) :
    Continuous (qsNQQuadraticLocal D H v a)

theorem qs_nq0_quadratic_character_exists (D : FieldData K) (H : HilbertData K)
    (a : Kˣ) :
    ∃ χ : HeckeChar K, χ ^ 2 = 1 ∧
      (∀ (w : InfinitePlace K) (u : w.Completionˣ), χ.locInf w u = 1) ∧
      (∀ v : FinPlace K, χ.loc v = qsNQQuadraticLocal D H v (toLoc v a))
```
-/

set_option autoImplicit false

open scoped NumberField Topology
open ArtinPrimitiveRoots.A1

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]

/-- The cubed Hilbert character at one finite place, read through `D.σ0`. -/
def qsNQQuadraticLocal (D : FieldData K) (H : HilbertData K)
    (v : FinPlace K) (a : (v.adicCompletion K)ˣ) :
    (v.adicCompletion K)ˣ →* ℂˣ :=
  (powMonoidHom 3 : ℂˣ →* ℂˣ).comp
    ((Units.map D.σ0.toMonoidHom).comp
      ((rootsOfUnity 6 K).subtype.comp
        (MonoidHom.mk' (fun u => H.hilb v a u) (fun u u' => H.mul_right v a u u'))))

/-- Cubing a sextic Hilbert character gives a character whose square is trivial. -/
theorem qs_nq0_quadratic_local_square (D : FieldData K) (H : HilbertData K)
    (v : FinPlace K) (a : (v.adicCompletion K)ˣ) :
    qsNQQuadraticLocal D H v a ^ 2 = 1 := by
  apply MonoidHom.ext
  intro u
  change (Units.map D.σ0.toMonoidHom (H.hilb v a u : Kˣ) ^ 3) ^ 2 = 1
  have h6 : (H.hilb v a u : Kˣ) ^ 6 = 1 :=
    (mem_rootsOfUnity 6 _).mp (H.hilb v a u).property
  rw [← pow_mul]
  change Units.map D.σ0.toMonoidHom (H.hilb v a u : Kˣ) ^ 6 = 1
  rw [← map_pow, h6, map_one]

/-- Powers with nonzero exponent in the field contain a unit neighborhood of `1`. -/
theorem qs_nq0_power_units_neighborhood (L : Type*)
    [NontriviallyNormedField L] [CompleteSpace L]
    (n : ℕ) (hn : (n : L) ≠ 0) :
    {u : Lˣ | ∃ b : Lˣ, u = b ^ n} ∈ 𝓝 (1 : Lˣ) := by
  have hnNat : n ≠ 0 := by
    intro h
    apply hn
    simp [h]
  have hd : HasStrictDerivAt (fun x : L => x ^ n) (n : L) 1 := by
    simpa using hasStrictDerivAt_pow n (1 : L)
  have hm : Filter.map (fun x : L => x ^ n) (𝓝 1) = 𝓝 1 := by
    simpa using hd.map_nhds_eq hn
  have hp : {x : L | ∃ y : L, x = y ^ n} ∈
      Filter.map (fun x : L => x ^ n) (𝓝 1) := by
    exact Filter.mem_map.mpr (Filter.Eventually.of_forall (fun x => ⟨x, rfl⟩))
  rw [hm] at hp
  filter_upwards [(Units.continuous_val.tendsto (1 : Lˣ)).eventually hp] with u hu
  obtain ⟨y, hy⟩ := hu
  have hy0 : y ≠ 0 := by
    intro h
    apply Units.ne_zero u
    rw [hy, h, zero_pow hnNat]
  refine ⟨Units.mk0 y hy0, ?_⟩
  apply Units.ext
  change (u : L) = y ^ n
  exact hy

end ArtinPrimitiveRoots.A2
