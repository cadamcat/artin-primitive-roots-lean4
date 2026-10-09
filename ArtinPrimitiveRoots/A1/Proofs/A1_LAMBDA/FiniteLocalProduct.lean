import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.Definitions

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a1_lambda_sol
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- A1-LAMBDA IMPL: Adapt Kummer/Idelic finite-product support and continuity at one; localUnit is the two valuation-subring memberships and restricted-product neighborhoods make all exterior factors trivial.
Guide: sol-thin-a1/PROOFS.md:428-439. Uses: Definitions. -/
theorem finite_local_product_exists
    (f : ∀ v : FinPlace F, ContinuousMonoidHom (v.adicCompletion F)ˣ ℂˣ)
    (hgood : ∀ᶠ v : FinPlace F in Filter.cofinite,
      ∀ u : (v.adicCompletion F)ˣ, localUnit v u → f v u = 1) :
    ∃ g : ContinuousMonoidHom (NumberField.IdeleGroup (𝓞 F) F) ℂˣ,
      (∀ x, g x = ∏ᶠ v : FinPlace F, f v (Dictionary.ideleFiniteCoord v x)) ∧
      ∀ x : NumberField.IdeleGroup (𝓞 F) F,
        Function.HasFiniteMulSupport (fun v : FinPlace F =>
          f v (Dictionary.ideleFiniteCoord v x)) := by
  classical
  let A := FiniteAdeleRing (𝓞 F) F
  let c (v : FinPlace F) : Aˣ →* (v.adicCompletion F)ˣ :=
    (Pi.evalMonoidHom (fun w : FinPlace F => (w.adicCompletion F)ˣ) v).comp
      RestrictedProduct.coeUnits
  have hc (v : FinPlace F) : Continuous (c v) := by
    apply Units.continuous_iff.mpr
    exact ⟨(RestrictedProduct.continuous_eval v).comp Units.continuous_val,
      (RestrictedProduct.continuous_eval v).comp Units.continuous_coe_inv⟩
  have hf (v : FinPlace F) : Continuous (fun x : Aˣ => f v (c v x)) :=
    (f v).continuous.comp (hc v)
  have hfinite (x : Aˣ) :
      Function.HasFiniteMulSupport (fun v : FinPlace F => f v (c v x)) := by
    apply Filter.eventually_cofinite.mp
    filter_upwards [hgood, x.val.2, x.inv.2] with v hv hx hxi
    exact hv (c v x) ⟨hx, hxi⟩
  let g : Aˣ →* ℂˣ := MonoidHom.mk'
    (fun x => ∏ᶠ v : FinPlace F, f v (c v x)) (by
      intro x y
      simp_rw [map_mul]
      exact finprod_mul_distrib (hfinite x) (hfinite y))
  have hg : Continuous g := by
    apply continuous_of_tendsto_nhds_one g
    have hO : IsOpen {x : A | ∀ v : FinPlace F,
        x v ∈ v.adicCompletionIntegers F} :=
      RestrictedProduct.isOpen_forall_mem
        (fun v : FinPlace F => Valued.isOpen_valuationSubring (v.adicCompletion F))
    have hV : {x : Aˣ | ∀ v : FinPlace F,
        (x : A) v ∈ v.adicCompletionIntegers F} ∈ 𝓝 (1 : Aˣ) :=
      (hO.preimage Units.continuous_val).mem_nhds (by intro v; exact one_mem _)
    have hI : {x : Aˣ | ∀ v : FinPlace F,
        ((x⁻¹ : Aˣ) : A) v ∈ v.adicCompletionIntegers F} ∈ 𝓝 (1 : Aˣ) :=
      (hO.preimage Units.continuous_coe_inv).mem_nhds (by intro v; exact one_mem _)
    have hC : {x : Aˣ | ∀ v : FinPlace F,
        c v x ∈ (v.adicCompletionIntegers F).units} ∈ 𝓝 (1 : Aˣ) := by
      filter_upwards [hV, hI] with x hx hxi
      intro v
      exact ⟨hx v, hxi v⟩
    let T : Finset (FinPlace F) := (Filter.eventually_cofinite.mp hgood).toFinset
    have houtside (v : FinPlace F) (hv : v ∉ T) :
        ∀ u : (v.adicCompletion F)ˣ,
          u ∈ (v.adicCompletionIntegers F).units → f v u = 1 := by
      have hv' : ∀ u : (v.adicCompletion F)ˣ, localUnit v u → f v u = 1 := by
        simpa only [T, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using hv
      intro u hu
      exact hv' u ⟨hu.1, hu.2⟩
    let E : Aˣ → ℂˣ := fun x => ∏ v ∈ T, f v (c v x)
    have hE : Continuous E := continuous_finsetProd T (fun v _ => hf v)
    have hEone : E 1 = 1 := by simp [E]
    have heq : (fun x : Aˣ => g x) =ᶠ[𝓝 (1 : Aˣ)] E := by
      filter_upwards [hC] with x hx
      change (∏ᶠ v : FinPlace F, f v (c v x)) = ∏ v ∈ T, f v (c v x)
      apply finprod_eq_prod_of_mulSupport_subset
      intro v hv
      by_contra hvT
      exact hv (houtside v hvT (c v x) (hx v))
    apply (Filter.tendsto_congr' heq).mpr
    simpa only [hEone] using hE.tendsto (1 : Aˣ)
  let p : NumberField.IdeleGroup (𝓞 F) F →* Aˣ :=
    Units.map (MonoidHom.snd (InfiniteAdeleRing F) A)
  have hp : Continuous p := by
    apply Units.continuous_iff.mpr
    exact ⟨continuous_snd.comp Units.continuous_val,
      continuous_snd.comp Units.continuous_coe_inv⟩
  let G : ContinuousMonoidHom (NumberField.IdeleGroup (𝓞 F) F) ℂˣ :=
    ⟨g.comp p, hg.comp hp⟩
  refine ⟨G, ?_, ?_⟩
  · intro x
    change (∏ᶠ v : FinPlace F, f v (c v (p x))) =
      ∏ᶠ v : FinPlace F, f v (Dictionary.ideleFiniteCoord v x)
    rfl
  · intro x
    change Function.HasFiniteMulSupport
      (fun v : FinPlace F => f v (c v (p x)))
    exact hfinite (p x)

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
