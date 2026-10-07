import ArtinPrimitiveRoots.Proofs.qs_nq0_sol.Generators
import ArtinPrimitiveRoots.A1.Characters

/-!
# Local quadratic characters for the narrow family

Read the cubed Hilbert symbol through the fixed complex embedding. The
algebraic local character is quadratic because the Hilbert value is a sixth
root of unity. Continuity and global descent are subsequent steps.

The remaining global-character statement, in this module's context, is:
```
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

/-- The local quadratic Hilbert homomorphism is continuous. -/
theorem qs_nq0_quadratic_local_continuous (D : FieldData K) (H : HilbertData K)
    (v : FinPlace K) (a : (v.adicCompletion K)ˣ) :
    Continuous (qsNQQuadraticLocal D H v a) := by
  let L := v.adicCompletion K
  obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  let x : L := NumberField.FinitePlace.embedding v (algebraMap (𝓞 K) K t)
  have htK : algebraMap (𝓞 K) K t ≠ 0 :=
    NumberField.RingOfIntegers.coe_ne_zero_iff.mpr ht0
  have hx0 : x ≠ 0 := (NumberField.FinitePlace.embedding v).injective.ne htK
  have hxnorm : ‖x‖ < 1 :=
    (NumberField.FinitePlace.norm_lt_one_iff_mem (K := K) v t).mpr ht
  letI : NontriviallyNormedField L :=
    NontriviallyNormedField.ofNormNeOne ⟨x, hx0, ne_of_lt hxnorm⟩
  have h2 : (2 : L) ≠ 0 := by
    intro h
    have hk : (2 : K) = 0 := (algebraMap K L).injective
      (by simpa only [map_ofNat, map_zero] using h)
    exact (two_ne_zero : (2 : K) ≠ 0) hk
  let f : Lˣ →* ℂˣ := qsNQQuadraticLocal D H v a
  apply continuous_of_tendsto_nhds_one f
  have hs := qs_nq0_power_units_neighborhood L 2 h2
  have heq : (fun u : Lˣ => f u) =ᶠ[𝓝 (1 : Lˣ)] (fun _ => (1 : ℂˣ)) := by
    filter_upwards [hs] with u hu
    obtain ⟨b, rfl⟩ := hu
    rw [map_pow]
    have hval := congrArg (fun g : Lˣ →* ℂˣ => g b)
      (qs_nq0_quadratic_local_square D H v a)
    exact hval
  apply (Filter.tendsto_congr' heq).mpr
  exact tendsto_const_nhds

/-- The finite quadratic local product is trivial on principal ideles. -/
theorem qs_nq0_quadratic_product_formula (D : FieldData K) (H : HilbertData K)
    (a b : Kˣ) :
    (Function.mulSupport (fun v : FinPlace K =>
      qsNQQuadraticLocal D H v (toLoc v a) (toLoc v b))).Finite ∧
      ∏ᶠ v : FinPlace K,
        qsNQQuadraticLocal D H v (toLoc v a) (toLoc v b) = 1 := by
  let g : rootsOfUnity 6 K →* ℂˣ :=
    (powMonoidHom 3 : ℂˣ →* ℂˣ).comp
      ((Units.map D.σ0.toMonoidHom).comp (rootsOfUnity 6 K).subtype)
  obtain ⟨hf, hp⟩ := H.product_formula a b
  constructor
  · change Function.HasFiniteMulSupport
      (fun v : FinPlace K => g (H.hilb v (toLoc v a) (toLoc v b)))
    exact Function.HasFiniteMulSupport.fun_comp hf g.map_one
  · change (∏ᶠ v : FinPlace K, g (H.hilb v (toLoc v a) (toLoc v b))) = 1
    rw [← g.map_finprod hf, hp, g.map_one]

end ArtinPrimitiveRoots.A2
