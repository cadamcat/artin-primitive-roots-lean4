import ArtinPrimitiveRoots.A1.SLattice

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_probe_sol

open ArtinPrimitiveRoots A1

/-- Translation and dilation by a unit preserve the Bruhat--Schwartz space. -/
theorem bruhatSchwartz_affine
    {F : Type} [Field F] [NumberField F] {CE : ℕ} {condη : Ideal (𝓞 F)}
    (S : SData F CE condη) (f : S.BruhatSchwartz) (b : S.FS) (k : S.FSˣ) :
    (fun x : S.FS => (f : S.FS → ℂ) ((b + x) * (k⁻¹ : S.FSˣ).val)) ∈
      S.BruhatSchwartz := by
  let kf (v : S.Sf) : (v.1.adicCompletion F)ˣ :=
    ⟨(k⁻¹ : S.FSˣ).val.1 v, k.val.1 v,
      congrArg (fun x : S.FS => x.1 v) k.inv_val,
      congrArg (fun x : S.FS => x.1 v) k.val_inv⟩
  let kc (w : InfinitePlace F) : ℂˣ :=
    ⟨(k⁻¹ : S.FSˣ).val.2 w, k.val.2 w,
      congrArg (fun x : S.FS => x.2 w) k.inv_val,
      congrArg (fun x : S.FS => x.2 w) k.val_inv⟩
  let ef (v : S.Sf) : v.1.adicCompletion F ≃ₜ v.1.adicCompletion F :=
    (Homeomorph.addLeft (b.1 v)).trans
      (Homeomorph.mulRight₀ (kf v : v.1.adicCompletion F) (Units.ne_zero (kf v)))
  let ec : (InfinitePlace F → ℂ) ≃L[ℝ] (InfinitePlace F → ℂ) :=
    (ContinuousLinearEquiv.piCongrRight
      (fun w => ContinuousLinearEquiv.unitsEquivAut ℂ (kc w))).restrictScalars ℝ
  have hpreserve (g : S.FS → ℂ) (hg : g ∈ S.BruhatSchwartz) :
      (fun x : S.FS => g ((b + x) * (k⁻¹ : S.FSˣ).val)) ∈ S.BruhatSchwartz := by
    refine Submodule.span_induction
      (p := fun g _ =>
        (fun x : S.FS => g ((b + x) * (k⁻¹ : S.FSˣ).val)) ∈ S.BruhatSchwartz)
      ?_ ?_ ?_ ?_ hg
    · rintro g ⟨⟨arch, finite⟩, rfl⟩
      let arch' : SData.ArchSchwartz F :=
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ ec arch).compSubConstCLM ℂ (-b.2)
      let finite' (v : S.Sf) : S.FiniteTest v :=
        ⟨(finite v).1 ∘ ef v, (finite v).2.1.comp (ef v).continuous,
          (finite v).2.2.1.comp_homeomorph (ef v),
          (finite v).2.2.2.comp_continuous (ef v).continuous⟩
      have htensor :
          (fun x : S.FS => S.tensorFunction arch finite
            ((b + x) * (k⁻¹ : S.FSˣ).val)) = S.tensorFunction arch' finite' := by
        funext x
        change arch (((b + x) * (k⁻¹ : S.FSˣ).val).2) *
            ∏ v : S.Sf, (finite v).1 (((b + x) * (k⁻¹ : S.FSˣ).val).1 v) =
          arch (ec (x.2 - -b.2)) * ∏ v : S.Sf, (finite v).1 (ef v (x.1 v))
        congr 1
        · congr 1
          ext w
          simp [ec, kc, sub_neg_eq_add, add_comm]
      rw [htensor]
      exact Submodule.subset_span ⟨(arch', finite'), rfl⟩
    · exact S.BruhatSchwartz.zero_mem
    · intro g h hg hh hgp hhp
      exact S.BruhatSchwartz.add_mem hgp hhp
    · intro c g hg hgp
      exact S.BruhatSchwartz.smul_mem c hgp
  exact hpreserve f f.property

end ArtinPrimitiveRoots.Proofs.a2_probe_sol
