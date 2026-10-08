import ArtinPrimitiveRoots.Proofs.qs_nq0_sol.LocalCharacter

/-!
# Finite idelic quadratic characters

The planned finite product construction, in this module's context, is:
```
theorem qs_nq0_finite_idelic_character_exists
    (D : FieldData K) (H : HilbertData K) (a : Kˣ) :
    ∃ Ξ : ContinuousMonoidHom (FiniteAdeleRing (𝓞 K) K)ˣ ℂˣ,
      Ξ ^ 2 = 1 ∧ ∀ x,
        Ξ x = ∏ᶠ v : FinPlace K,
          qsNQQuadraticLocal D H v (toLoc v a) (RestrictedProduct.coeUnits x v)
```
-/

set_option autoImplicit false

open scoped NumberField Topology
open NumberField IsDedekindDomain ArtinPrimitiveRoots.A1

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]

/-- The product of the local quadratic maps is a continuous finite idelic character. -/
theorem qs_nq0_finite_idelic_character_exists
    (D : FieldData K) (H : HilbertData K) (a : Kˣ) :
    ∃ Ξ : ContinuousMonoidHom (FiniteAdeleRing (𝓞 K) K)ˣ ℂˣ,
      Ξ ^ 2 = 1 ∧ ∀ x,
        Ξ x = ∏ᶠ v : FinPlace K,
          qsNQQuadraticLocal D H v (toLoc v a) (RestrictedProduct.coeUnits x v) := by
  classical
  let A := FiniteAdeleRing (𝓞 K) K
  let f (v : FinPlace K) : (v.adicCompletion K)ˣ →* ℂˣ :=
    qsNQQuadraticLocal D H v (toLoc v a)
  let c (v : FinPlace K) : Aˣ →* (v.adicCompletion K)ˣ :=
    (Pi.evalMonoidHom (fun w : FinPlace K => (w.adicCompletion K)ˣ) v).comp
      RestrictedProduct.coeUnits
  have hc (v : FinPlace K) : Continuous (c v) := by
    apply Units.continuous_iff.mpr
    exact ⟨(RestrictedProduct.continuous_eval v).comp Units.continuous_val,
      (RestrictedProduct.continuous_eval v).comp Units.continuous_coe_inv⟩
  have hf (v : FinPlace K) : Continuous (fun x : Aˣ => f v (c v x)) :=
    (qs_nq0_quadratic_local_continuous D H v (toLoc v a)).comp (hc v)
  have hgood := qs_nq0_quadratic_local_eventually_unit_trivial D H a
  have hfinite (x : Aˣ) : Function.HasFiniteMulSupport (fun v => f v (c v x)) := by
    apply Filter.eventually_cofinite.mp
    filter_upwards [hgood, x.val.2, x.inv.2] with v hv hx hx'
    exact hv (c v x) ⟨hx, hx'⟩
  let F : Aˣ →* ℂˣ := MonoidHom.mk'
    (fun x => ∏ᶠ v : FinPlace K, f v (c v x)) (fun x y => by
      simp_rw [map_mul]
      exact finprod_mul_distrib (hfinite x) (hfinite y))
  have hF : Continuous F := by
    apply continuous_of_tendsto_nhds_one F
    have hO : IsOpen {x : A | ∀ v : FinPlace K, x v ∈ v.adicCompletionIntegers K} :=
      RestrictedProduct.isOpen_forall_mem
        (fun v : FinPlace K => Valued.isOpen_valuationSubring (v.adicCompletion K))
    have hV : {x : Aˣ | ∀ v : FinPlace K,
        (x : A) v ∈ v.adicCompletionIntegers K} ∈ 𝓝 (1 : Aˣ) :=
      (hO.preimage Units.continuous_val).mem_nhds (by intro v; exact one_mem _)
    have hI : {x : Aˣ | ∀ v : FinPlace K,
        ((x⁻¹ : Aˣ) : A) v ∈ v.adicCompletionIntegers K} ∈ 𝓝 (1 : Aˣ) :=
      (hO.preimage Units.continuous_coe_inv).mem_nhds (by intro v; exact one_mem _)
    have hC : {x : Aˣ | ∀ v : FinPlace K,
        c v x ∈ (v.adicCompletionIntegers K).units} ∈ 𝓝 (1 : Aˣ) := by
      filter_upwards [hV, hI] with x hx hx'
      intro v
      exact ⟨hx v, hx' v⟩
    let T : Finset (FinPlace K) := (Filter.eventually_cofinite.mp hgood).toFinset
    have houtside (v : FinPlace K) (hv : v ∉ T) :
        ∀ u : (v.adicCompletion K)ˣ,
          u ∈ (v.adicCompletionIntegers K).units → f v u = 1 := by
      simpa only [T, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using hv
    have hlocal (v : FinPlace K) :
        {x : Aˣ | f v (c v x) = 1} ∈ 𝓝 (1 : Aˣ) := by
      have htend : Filter.Tendsto (fun x : Aˣ => ((f v (c v x) : ℂˣ) : ℂ))
          (𝓝 (1 : Aˣ)) (𝓝 (1 : ℂ)) := by
        simpa only [Function.comp_def, map_one, Units.val_one] using
          (Units.continuous_val.comp (hf v)).tendsto (1 : Aˣ)
      have hne : {z : ℂ | z ≠ -1} ∈ 𝓝 (1 : ℂ) :=
        (isClosed_singleton (x := (-1 : ℂ))).isOpen_compl.mem_nhds (by norm_num)
      filter_upwards [htend.eventually hne] with x hx
      apply Units.ext
      have hs := congrArg
        (fun g : (v.adicCompletion K)ˣ →* ℂˣ => ((g (c v x) : ℂˣ) : ℂ))
        (qs_nq0_quadratic_local_square D H v (toLoc v a))
      change (((f v (c v x) : ℂˣ) : ℂ) ^ 2) = 1 at hs
      rcases sq_eq_one_iff.mp hs with h | h
      · exact h
      · exact (hx h).elim
    have hT : {x : Aˣ | ∀ v ∈ T, f v (c v x) = 1} ∈ 𝓝 (1 : Aˣ) :=
      (Filter.eventually_all_finset T).mpr (fun v _ => hlocal v)
    have hall : {x : Aˣ | ∀ v : FinPlace K, f v (c v x) = 1} ∈ 𝓝 (1 : Aˣ) := by
      filter_upwards [hC, hT] with x hx hxT
      intro v
      by_cases hv : v ∈ T
      · exact hxT v hv
      · exact houtside v hv (c v x) (hx v)
    have heq : (fun x : Aˣ => F x) =ᶠ[𝓝 (1 : Aˣ)] (fun _ => (1 : ℂˣ)) := by
      filter_upwards [hall] with x hx
      exact finprod_eq_one_of_forall_eq_one hx
    apply (Filter.tendsto_congr' heq).mpr
    exact tendsto_const_nhds
  refine ⟨⟨F, hF⟩, ?_, fun _ => rfl⟩
  apply ContinuousMonoidHom.ext
  intro x
  simp only [ContinuousMonoidHom.pow_apply, ContinuousMonoidHom.one_toFun]
  change (∏ᶠ v : FinPlace K, f v (c v x)) ^ 2 = 1
  rw [finprod_pow (hfinite x) 2]
  apply finprod_eq_one_of_forall_eq_one
  intro v
  exact congrArg (fun g : (v.adicCompletion K)ˣ →* ℂˣ => g (c v x))
    (qs_nq0_quadratic_local_square D H v (toLoc v a))

end ArtinPrimitiveRoots.A2
