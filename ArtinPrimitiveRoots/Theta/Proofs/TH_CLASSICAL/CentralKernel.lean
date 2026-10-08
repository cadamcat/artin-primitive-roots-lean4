import ArtinPrimitiveRoots.Theta.Cover

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Trivial projected components leave precisely one global cubic central phase. -/
theorem th_classical_central_kernel (P : CoverPackage D S H A) (r : P.RP)
    (hF : ∀ v, (P.loc v).pr (P.compF v r) = 1)
    (hC : ∀ w, P.compC w r = 1) :
    ∃! ζ : rootsOfUnity 3 ℂ, P.q r = P.tc.z ζ := by
  classical
  have hlocal : ∀ v, ∃ ζ : rootsOfUnity 3 ℂ, (P.loc v).z ζ = P.compF v r := by
    intro v
    have hr : P.compF v r ∈ (P.loc v).pr.ker := hF v
    rw [(P.loc v).pr_ker] at hr
    exact hr
  choose ξ hξ using hlocal
  have hsupp : (Function.mulSupport ξ).Finite := by
    apply (S.Sf.finite_toSet.union (P.comp_restricted r)).subset
    intro v hv
    change ξ v ≠ 1 at hv
    by_cases hvS : v ∈ S.Sf
    · exact Or.inl hvS
    · right
      by_contra hbad
      have hk : P.compF v r ∈ (P.tame v hvS).Kmax := by
        by_contra hnot
        exact hbad ⟨hvS, hnot⟩
      have he : P.compF v r = 1 := (P.tame v hvS).inj hk
        (P.tame v hvS).Kmax.one_mem (by simpa only [map_one] using hF v)
      apply hv
      apply (P.loc v).z_inj
      rw [hξ v, map_one]
      exact he
  let T := hsupp.toFinset
  let lift : FinPlace F → P.RP := fun v => P.incl v ((P.loc v).z (ξ v))
  let r' : P.RP := (T.toList.map lift).prod
  have hF' : ∀ v, P.compF v r' = P.compF v r := by
    intro v
    change P.compF v ((T.toList.map lift).prod) = P.compF v r
    rw [map_list_prod]
    simp only [List.map_map]
    change (T.toList.map fun u => P.compF v (lift u)).prod = P.compF v r
    by_cases hv : v ∈ T
    · have hmem : v ∈ T.toList := Finset.mem_toList.mpr hv
      rw [List.prod_map_eq_pow_single v (fun u => P.compF v (lift u)) (by
        intro u hne hu
        exact P.incl_compF_other u v hne ((P.loc u).z (ξ u)))]
      rw [List.count_eq_one_of_mem (Finset.nodup_toList T) hmem, pow_one]
      change P.compF v (P.incl v ((P.loc v).z (ξ v))) = P.compF v r
      rw [P.incl_compF, hξ]
    · have hroot : ξ v = 1 := by
        by_contra hne
        exact hv (hsupp.mem_toFinset.mpr hne)
      have hprod : (T.toList.map fun u => P.compF v (lift u)).prod = 1 := by
        apply List.prod_eq_one
        intro a ha
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ha
        have hne : u ≠ v := by
          intro he
          subst u
          exact hv (Finset.mem_toList.mp hu)
        exact P.incl_compF_other u v hne ((P.loc u).z (ξ u))
      rw [hprod, ← hξ v, hroot, map_one]
  have hC' : ∀ w, P.compC w r' = 1 := by
    intro w
    change P.compC w ((T.toList.map lift).prod) = 1
    rw [map_list_prod]
    apply List.prod_eq_one
    intro a ha
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ha
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    exact P.incl_compC v ((P.loc v).z (ξ v)) w
  have hr : r' = r := P.comp_ext r' r hF' (fun w => (hC' w).trans (hC w).symm)
  let ζ : rootsOfUnity 3 ℂ := (T.toList.map ξ).prod
  have hq : P.q r' = P.tc.z ζ := by
    change P.q ((T.toList.map lift).prod) = P.tc.z ((T.toList.map ξ).prod)
    rw [map_list_prod, map_list_prod]
    simp only [List.map_map]
    congr 1
    apply List.map_congr_left
    intro v hv
    exact (P.q_incl v ((P.loc v).z (ξ v))).trans (P.emb_z v (ξ v))
  have hqr : P.q r = P.tc.z ζ := hr ▸ hq
  refine ⟨ζ, hqr, ?_⟩
  intro ζ' hζ'
  exact P.tc.z_inj (hζ'.symm.trans hqr)

end ArtinPrimitiveRoots.A1.Theta
