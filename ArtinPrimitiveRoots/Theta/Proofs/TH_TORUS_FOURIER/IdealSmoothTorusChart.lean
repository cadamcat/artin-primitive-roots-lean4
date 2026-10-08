import ArtinPrimitiveRoots.Theta.Proofs.TH_TORUS_FOURIER.IdealCharacterChart
import ArtinPrimitiveRoots.Theta.Proofs.TH_TORUS_FOURIER.PeriodicFourierSummable

set_option autoImplicit false

open NumberField IsDedekindDomain Module AddCircle
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.thsol_torusf

open ArtinPrimitiveRoots.A1 ArtinPrimitiveRoots.A1.Theta

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

theorem ideal_smooth_torus_chart
    (P : CoverPackage D S H A) (Ψ : P.tc.G → ℂ) (g : P.tc.G)
    (I : (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ)
    (hper : ∀ ξ ∈ (I : Submodule (𝓞 F) F), ∀ x,
      Ψ (nInf P (x + infEmbA ξ) * g) = Ψ (nInf P x * g))
    (hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => Ψ (nInf P x * g))) :
    ∃ (n : ℕ) (b : Basis (Fin (n + 1)) ℝ (InfinitePlace F → ℂ))
      (e : {ν : F // ∀ ξ ∈ (I : Submodule (𝓞 F) F),
          psiInf ν (infEmbA ξ) = 1} ≃ (Fin (n + 1) → ℤ))
      (F₀ : C(UnitAddTorus (Fin (n + 1)), ℂ)),
      (Submodule.span ℤ (Set.range b)).toAddSubgroup =
        (I : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom ∧
      (∀ x : Fin (n + 1) → ℝ,
        F₀ (fun j => (x j : UnitAddCircle)) = Ψ (nInf P (b.equivFun.symm x) * g)) ∧
      Summable (UnitAddTorus.mFourierCoeff F₀) ∧
      ∀ (ν : {ν : F // ∀ ξ ∈ (I : Submodule (𝓞 F) F),
          psiInf ν (infEmbA ξ) = 1}) (x : Fin (n + 1) → ℝ),
        psiInf (-ν.1) (b.equivFun.symm x) =
          UnitAddTorus.mFourier (-(e ν)) (fun j => (x j : UnitAddCircle)) := by
  classical
  obtain ⟨b₀, e₀, _, hspan₀, hchar₀⟩ := ideal_character_chart D I
  let d := Free.ChooseBasisIndex ℤ I
  let : Nonempty d := b₀.index_nonempty
  let n := Fintype.card d - 1
  have hcard : Fintype.card d = n + 1 := by
    have hp : 0 < Fintype.card d := Fintype.card_pos
    dsimp [n]
    omega
  let r : d ≃ Fin (n + 1) := (Fintype.equivFin d).trans (finCongr hcard)
  let b := b₀.reindex r
  let e := e₀.trans (Equiv.piCongrLeft' (fun _ : d => ℤ) r)
  have hspan : (Submodule.span ℤ (Set.range b)).toAddSubgroup =
      (I : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom := by
    rw [show Set.range b = Set.range b₀ from b₀.range_reindex r]
    exact hspan₀
  have hcoord (x : Fin (n + 1) → ℝ) :
      b.equivFun.symm x = b₀.equivFun.symm (fun i => x (r i)) := by
    apply b₀.equivFun.injective
    rw [LinearEquiv.apply_symm_apply]
    funext i
    have h := congrFun (b.equivFun.apply_symm_apply x) (r i)
    simpa only [b, Basis.equivFun_apply, Basis.repr_reindex_apply,
      Equiv.symm_apply_apply] using h
  let f : (Fin (n + 1) → ℝ) → ℂ := fun x => Ψ (nInf P (b.equivFun.symm x) * g)
  have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f :=
    hsmooth.comp b.equivFunL.symm.contDiff
  have hfper (x : Fin (n + 1) → ℝ) (k : Fin (n + 1) → ℤ) :
      f (x + fun j => (k j : ℝ)) = f x := by
    let v := b.equivFun.symm (fun j => (k j : ℝ))
    have hv : v ∈ Submodule.span ℤ (Set.range b) := by
      apply (b.mem_span_iff_repr_mem (R := ℤ) v).mpr
      intro i
      refine ⟨k i, ?_⟩
      change algebraMap ℤ ℝ (k i) = b.equivFun v i
      rw [show b.equivFun v = (fun j => (k j : ℝ)) from
        b.equivFun.apply_symm_apply _]
      rfl
    have hv' : v ∈ (I : Submodule (𝓞 F) F).toAddSubgroup.map
        infEmbA.toAddMonoidHom := by
      rw [← hspan]
      exact hv
    obtain ⟨ξ, hξ, hξv⟩ := hv'
    change infEmbA ξ = v at hξv
    change Ψ (nInf P (b.equivFun.symm (x + fun j => (k j : ℝ))) * g) = _
    rw [map_add]
    change Ψ (nInf P (b.equivFun.symm x + v) * g) = _
    rw [← hξv]
    exact hper ξ hξ (b.equivFun.symm x)
  obtain ⟨F₀, hF₀, hSum⟩ := periodic_fourier_coeff_summable f hf hfper
  refine ⟨n, b, e, F₀, hspan, hF₀, hSum, ?_⟩
  intro ν x
  have hneg : psiInf (-ν.1) (b.equivFun.symm x) =
      psiInf ν.1 (b.equivFun.symm (-x)) := by
    rw [map_neg]
    simp only [psiInf, map_neg, Pi.neg_apply, neg_mul, mul_neg]
  rw [hneg, hcoord, hchar₀]
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk,
    fourier_coe_apply, Pi.neg_apply, Complex.ofReal_one, Complex.ofReal_neg, div_one]
  rw [← Complex.exp_sum]
  apply congrArg Complex.exp
  rw [Finset.mul_sum]
  apply Fintype.sum_equiv r
  intro i
  simp only [e, Equiv.trans_apply, Equiv.piCongrLeft'_apply,
    Equiv.symm_apply_apply, Int.cast_neg]
  ring

end ArtinPrimitiveRoots.Proofs.thsol_torusf
