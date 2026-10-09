import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.FiniteLocalProduct

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a1_lambda_sol
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- A1-LAMBDA IMPL: Multiply the finite product by the finite product of infinite coordinates, descend using L.principal_product and QuotientGroup.lift. Compute single-place coordinates with Dictionary lemmas; local norms one give unitarity.
Guide: sol-thin-a1/PROOFS.md:428-439. Uses: FiniteLocalProduct. -/
theorem local_character_descent (L : LocalCharacterData F) :
    ∃ χ : LambdaChar F, unitary χ ∧
      (∀ (v : FinPlace F) (u : (v.adicCompletion F)ˣ),
        localComponent χ v u = L.finite v u) ∧
      ∀ (w : InfinitePlace F) (u : w.Completionˣ),
        infiniteComponent χ w u = L.infinite w u := by
  classical
  obtain ⟨g, hg, hfinite⟩ :=
    finite_local_product_exists L.finite L.eventually_unit_trivial
  let infProd (x : NumberField.IdeleGroup (𝓞 F) F) : ℂˣ :=
    ∏ w : InfinitePlace F, L.infinite w (Dictionary.ideleInfiniteCoordUnit w x)
  let H : NumberField.IdeleGroup (𝓞 F) F →* ℂˣ := MonoidHom.mk'
    (fun x => infProd x * g x) (by
      intro x y
      simp only [infProd, map_mul, Finset.prod_mul_distrib]
      ac_rfl)
  have hinfCoord (w : InfinitePlace F) :
      Continuous (Dictionary.ideleInfiniteCoordUnit w :
        NumberField.IdeleGroup (𝓞 F) F →* w.Completionˣ) := by
    apply Units.continuous_iff.mpr
    exact ⟨((continuous_apply w).comp continuous_fst).comp Units.continuous_val,
      ((continuous_apply w).comp continuous_fst).comp Units.continuous_coe_inv⟩
  have hinfFactor (w : InfinitePlace F) :
      Continuous (fun x : NumberField.IdeleGroup (𝓞 F) F =>
        L.infinite w (Dictionary.ideleInfiniteCoordUnit w x)) :=
    (L.infinite w).continuous.comp (hinfCoord w)
  have hinfProd : Continuous infProd := by
    exact continuous_finsetProd Finset.univ (fun w _ => hinfFactor w)
  have hH : Continuous H := by
    change Continuous (fun x : NumberField.IdeleGroup (𝓞 F) F => infProd x * g x)
    exact hinfProd.mul g.continuous
  have hprincipalFinite (a : Fˣ) :
      g (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a) =
        ∏ᶠ v : FinPlace F, L.finite v (toLoc v a) := by
    rw [hg]
    have hcoord (v : FinPlace F) :
        Dictionary.ideleFiniteCoord v (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a) =
          toLoc v a := by
      apply Units.ext
      rfl
    apply finprod_congr
    intro v
    exact congrArg (L.finite v) (hcoord v)
  have hprincipal (a : Fˣ) :
      H (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a) = 1 := by
    change (∏ w : InfinitePlace F,
        L.infinite w (Dictionary.ideleInfiniteCoordUnit w
          (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a))) *
      g (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a) = 1
    rw [hprincipalFinite]
    exact L.principal_product a
  let N := NumberField.IdeleGroup.principalSubgroup (𝓞 F) F
  have hN : N ≤ H.ker := by
    intro x hx
    obtain ⟨a, rfl⟩ := hx
    exact hprincipal a
  let C : NumberField.IdeleClassGroup (𝓞 F) F →* ℂˣ := QuotientGroup.lift N H hN
  have hC : Continuous C := by
    apply (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr
    exact hH
  let χ : LambdaChar F := ⟨C, hC⟩
  have hprodNorm {α : Type} (s : Finset α) (f : α → ℂˣ)
      (hf : ∀ a ∈ s, ‖((f a : ℂˣ) : ℂ)‖ = 1) :
      ‖((∏ a ∈ s, f a : ℂˣ) : ℂ)‖ = 1 := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Units.val_mul, norm_mul, hf a (by simp)]
      simpa using ih (by
        intro b hb
        exact hf b (by simp [hb]))
  have hfiniteUnitary (x : NumberField.IdeleGroup (𝓞 F) F) :
      ‖((g x : ℂˣ) : ℂ)‖ = 1 := by
    have hsupp : (Function.mulSupport fun v : FinPlace F =>
        L.finite v (Dictionary.ideleFiniteCoord v x)).Finite := hfinite x
    rw [hg]
    rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ Set.Subset.rfl hsupp]
    apply hprodNorm
    intro v hv
    exact L.finite_unitary v (Dictionary.ideleFiniteCoord v x)
  have hinfiniteUnitary (x : NumberField.IdeleGroup (𝓞 F) F) :
      ‖((infProd x : ℂˣ) : ℂ)‖ = 1 := by
    change ‖((∏ w : InfinitePlace F,
      L.infinite w (Dictionary.ideleInfiniteCoordUnit w x) : ℂˣ) : ℂ)‖ = 1
    apply hprodNorm
    intro w hw
    exact L.infinite_unitary w (Dictionary.ideleInfiniteCoordUnit w x)
  have hHunitary (x : NumberField.IdeleGroup (𝓞 F) F) :
      ‖((H x : ℂˣ) : ℂ)‖ = 1 := by
    change ‖((infProd x : ℂˣ) : ℂ) * ((g x : ℂˣ) : ℂ)‖ = 1
    rw [norm_mul, hinfiniteUnitary x, hfiniteUnitary x]
    norm_num
  have hfiniteComponent (v : FinPlace F) (u : (v.adicCompletion F)ˣ) :
      H (NumberField.IdeleGroup.ofAdicCompletion (𝓞 F) F v u) = L.finite v u := by
    change (∏ w : InfinitePlace F,
        L.infinite w (Dictionary.ideleInfiniteCoordUnit w
          (NumberField.IdeleGroup.ofAdicCompletion (𝓞 F) F v u))) *
      g (NumberField.IdeleGroup.ofAdicCompletion (𝓞 F) F v u) = L.finite v u
    simp only [Dictionary.ideleInfiniteCoordUnit_ofAdicCompletion, map_one,
      Finset.prod_const_one, one_mul]
    rw [hg]
    rw [finprod_eq_single _ v (fun v' hv' => by
      rw [Dictionary.ideleFiniteCoord_ofAdicCompletion_of_ne v' v hv']
      simp)]
    simp [Dictionary.ideleFiniteCoord_ofAdicCompletion]
  have hinfiniteComponent (w : InfinitePlace F) (u : w.Completionˣ) :
      H (NumberField.IdeleGroup.ofCompletion (𝓞 F) F w u) = L.infinite w u := by
    change (∏ w' : InfinitePlace F,
        L.infinite w' (Dictionary.ideleInfiniteCoordUnit w'
          (NumberField.IdeleGroup.ofCompletion (𝓞 F) F w u))) *
      g (NumberField.IdeleGroup.ofCompletion (𝓞 F) F w u) = L.infinite w u
    have hInf : (∏ w' : InfinitePlace F,
        L.infinite w' (Dictionary.ideleInfiniteCoordUnit w'
          (NumberField.IdeleGroup.ofCompletion (𝓞 F) F w u))) = L.infinite w u := by
      rw [Finset.prod_eq_single_of_mem w (Finset.mem_univ w)]
      · rw [Dictionary.ideleInfiniteCoordUnit_ofCompletion_self]
      · intro w' _ hne
        rw [Dictionary.ideleInfiniteCoordUnit_ofCompletion_of_ne w' w hne, map_one]
    have hFin : g (NumberField.IdeleGroup.ofCompletion (𝓞 F) F w u) = 1 := by
      rw [hg]
      apply finprod_eq_one_of_forall_eq_one
      intro v
      simp [Dictionary.ideleFiniteCoord_ofCompletion]
    rw [hInf, hFin]
    simp
  refine ⟨χ, ?_, ?_, ?_⟩
  · intro q
    refine QuotientGroup.induction_on q ?_
    intro x
    change ‖((QuotientGroup.lift N H hN (QuotientGroup.mk x) : ℂˣ) : ℂ)‖ = 1
    rw [QuotientGroup.lift_mk N hN]
    exact hHunitary x
  · intro v u
    change QuotientGroup.lift N H hN
      (QuotientGroup.mk (NumberField.IdeleGroup.ofAdicCompletion (𝓞 F) F v u)) =
      L.finite v u
    rw [QuotientGroup.lift_mk N hN]
    exact hfiniteComponent v u
  · intro w u
    change QuotientGroup.lift N H hN
      (QuotientGroup.mk (NumberField.IdeleGroup.ofCompletion (𝓞 F) F w u)) =
      L.infinite w u
    rw [QuotientGroup.lift_mk N hN]
    exact hinfiniteComponent w u

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
