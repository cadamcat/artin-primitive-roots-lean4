import ArtinPrimitiveRoots.A1.Proofs.A1_KUMMER.Types
import ArtinPrimitiveRoots.Hecke.Dict.IdeleCoordinates

/-! Continuous characters are determined by their local components. -/

set_option autoImplicit false

open NumberField IsDedekindDomain Filter Topology
open scoped Classical RestrictedProduct

noncomputable section

namespace ArtinPrimitiveRoots.A1.KummerProofs

variable {F : Type} [Field F] [NumberField F]

theorem kummer_char_ext (κ κ' : KummerChar F)
    (hinf : ∀ (w : InfinitePlace F) (x : w.Completionˣ),
      infiniteComponent κ w x = infiniteComponent κ' w x)
    (hfin : ∀ (P : FinPlace F) (x : (P.adicCompletion F)ˣ),
      localComponent κ P x = localComponent κ' P x) : κ = κ' := by
  classical
  let finiteTrunc (z : FiniteAdeleRing (𝓞 F) F) (T : Finset (FinPlace F)) :
      FiniteAdeleRing (𝓞 F) F :=
    ⟨fun P => if P ∈ T then z P else 1, by
      filter_upwards [T.finite_toSet.compl_mem_cofinite] with P hP
      have hPT : P ∉ T := by simpa using hP
      simp [hPT]⟩
  have hfiniteTrunc (z : FiniteAdeleRing (𝓞 F) F) :
      Tendsto (finiteTrunc z) atTop (𝓝 z) := by
    let G : FinPlace F → Type := fun P => P.adicCompletion F
    let A : ∀ P, Set (G P) := fun P => P.adicCompletionIntegers F
    let S : Set (FinPlace F) := {P | z P ∈ A P}
    have hS : cofinite ≤ 𝓟 S := le_principal_iff.mpr z.2
    let zS : Πʳ P, [G P, A P]_[𝓟 S] := ⟨z, by
      rw [eventually_principal]
      intro P hP
      exact hP⟩
    let truncS (T : Finset (FinPlace F)) : Πʳ P, [G P, A P]_[𝓟 S] :=
      ⟨fun P => if P ∈ T then zS P else 1, by
        rw [eventually_principal]
        intro P hP
        change z P ∈ A P at hP
        change (if P ∈ T then z P else 1) ∈ A P
        by_cases hPT : P ∈ T
        · rw [ite_eq_left hPT]
          exact hP
        · rw [ite_eq_right hPT]
          exact (P.adicCompletionIntegers F).one_mem⟩
    have hpi : Tendsto (fun T : Finset (FinPlace F) =>
        fun P => if P ∈ T then zS P else 1) atTop (𝓝 (zS : ∀ P, G P)) := by
      apply tendsto_pi_nhds.2
      intro P
      have hmem : ∀ᶠ T : Finset (FinPlace F) in atTop, P ∈ T :=
        eventually_atTop.2 ⟨{P}, fun T hT => Finset.singleton_subset_iff.mp hT⟩
      have heq : (fun T : Finset (FinPlace F) => if P ∈ T then zS P else 1) =ᶠ[atTop]
          fun _ => zS P := by
        filter_upwards [hmem] with T hT
        simp only [ite_eq_left hT]
      exact tendsto_const_nhds.congr' heq.symm
    have hprincipal : Tendsto truncS atTop
        (@nhds (Πʳ P, [G P, A P]_[𝓟 S])
          (RestrictedProduct.topologicalSpace G A (𝓟 S)) zS) := by
      apply (RestrictedProduct.isEmbedding_coe_of_principal (R := G) (A := A)
        (S := S)).tendsto_nhds_iff.mpr
      exact hpi
    have hinc := (RestrictedProduct.continuous_inclusion (R := G) (A := A) hS).tendsto zS
      |>.comp hprincipal
    -- Keep the specified restricted-product topology during this conversion.
    exact hinc
  let trunc (x : IdeleGroup (𝓞 F) F) (T : Finset (FinPlace F)) : IdeleGroup (𝓞 F) F :=
    (∏ w ∈ Finset.univ,
        IdeleGroup.ofCompletion (𝓞 F) F w (Dictionary.ideleInfiniteCoordUnit w x)) *
      ∏ P ∈ T, IdeleGroup.ofAdicCompletion (𝓞 F) F P (Dictionary.ideleFiniteCoord P x)
  have hcoe (x : IdeleGroup (𝓞 F) F) (T : Finset (FinPlace F)) :
      (trunc x T : AdeleRing (𝓞 F) F) =
        ((x : AdeleRing (𝓞 F) F).1, finiteTrunc (x : AdeleRing (𝓞 F) F).2 T) := by
    apply Prod.ext
    · funext w
      change ((Dictionary.ideleInfiniteCoordUnit w (trunc x T) : w.Completionˣ) :
        w.Completion) = ((x : AdeleRing (𝓞 F) F).1 w)
      have hw : Dictionary.ideleInfiniteCoordUnit w (trunc x T) =
          Dictionary.ideleInfiniteCoordUnit w x := by
        dsimp only [trunc]
        rw [map_mul, Dictionary.ideleInfiniteCoordUnit_finsetProduct]
        simp only [Finset.mem_univ, ite_true, map_prod,
          Dictionary.ideleInfiniteCoordUnit_ofAdicCompletion, Finset.prod_const_one, mul_one]
      exact congrArg (fun u : w.Completionˣ => (u : w.Completion)) hw
    · apply Subtype.ext
      funext P
      change ((Dictionary.ideleFiniteCoord P (trunc x T) : (P.adicCompletion F)ˣ) :
        P.adicCompletion F) = if P ∈ T then (x : AdeleRing (𝓞 F) F).2 P else 1
      have hP : Dictionary.ideleFiniteCoord P (trunc x T) =
          if P ∈ T then Dictionary.ideleFiniteCoord P x else 1 := by
        dsimp only [trunc]
        rw [map_mul, Dictionary.ideleFiniteCoord_finsetProduct, map_prod]
        simp only [Dictionary.ideleFiniteCoord_ofCompletion, Finset.prod_const_one, one_mul]
      by_cases hPT : P ∈ T
      · rw [ite_eq_left hPT] at hP
        rw [ite_eq_left hPT]
        exact congrArg (fun u : (P.adicCompletion F)ˣ => (u : P.adicCompletion F)) hP
      · rw [ite_eq_right hPT] at hP
        rw [ite_eq_right hPT]
        exact congrArg (fun u : (P.adicCompletion F)ˣ => (u : P.adicCompletion F)) hP
  have hval (x : IdeleGroup (𝓞 F) F) :
      Tendsto (fun T : Finset (FinPlace F) => (trunc x T : AdeleRing (𝓞 F) F))
        atTop (𝓝 (x : AdeleRing (𝓞 F) F)) := by
    have hprod : Tendsto (fun T : Finset (FinPlace F) =>
        ((x : AdeleRing (𝓞 F) F).1, finiteTrunc (x : AdeleRing (𝓞 F) F).2 T)) atTop
        (𝓝 ((x : AdeleRing (𝓞 F) F).1, (x : AdeleRing (𝓞 F) F).2)) :=
      (Prod.tendsto_iff _ _).2 ⟨tendsto_const_nhds, hfiniteTrunc _⟩
    exact hprod.congr' (Eventually.of_forall (fun T => (hcoe x T).symm))
  have hinv (x : IdeleGroup (𝓞 F) F) (T : Finset (FinPlace F)) :
      (trunc x T)⁻¹ = trunc x⁻¹ T := by
    simp [trunc, map_inv, Finset.prod_inv_distrib]
    ac_rfl
  have htrunc (x : IdeleGroup (𝓞 F) F) : Tendsto (trunc x) atTop (𝓝 x) := by
    have hvalInv : Tendsto (fun T : Finset (FinPlace F) =>
        (((trunc x T)⁻¹ : IdeleGroup (𝓞 F) F) : AdeleRing (𝓞 F) F)) atTop
        (𝓝 ((x⁻¹ : IdeleGroup (𝓞 F) F) : AdeleRing (𝓞 F) F)) :=
      (hval x⁻¹).congr' (Eventually.of_forall (fun T =>
        congrArg (fun y : IdeleGroup (𝓞 F) F => (y : AdeleRing (𝓞 F) F)) (hinv x T).symm))
    have hvalOp : Tendsto (fun T : Finset (FinPlace F) =>
        MulOpposite.op (((trunc x T)⁻¹ : IdeleGroup (𝓞 F) F) : AdeleRing (𝓞 F) F)) atTop
        (𝓝 (MulOpposite.op ((x⁻¹ : IdeleGroup (𝓞 F) F) : AdeleRing (𝓞 F) F))) :=
      (MulOpposite.opHomeomorph.continuous.tendsto
        ((x⁻¹ : IdeleGroup (𝓞 F) F) : AdeleRing (𝓞 F) F)).comp hvalInv
    have hEmbed : Tendsto (fun T : Finset (FinPlace F) =>
        Units.embedProduct (AdeleRing (𝓞 F) F) (trunc x T)) atTop
        (𝓝 (Units.embedProduct (AdeleRing (𝓞 F) F) x)) := by
      exact (Prod.tendsto_iff _ _).2 ⟨hval x, hvalOp⟩
    exact Units.isEmbedding_embedProduct.tendsto_nhds_iff.mpr hEmbed
  let q : IdeleGroup (𝓞 F) F →* IdeleClassGroup (𝓞 F) F := QuotientGroup.mk' _
  let fa : IdeleGroup (𝓞 F) F →* ℂˣ := κ.toMonoidHom.comp q
  let fb : IdeleGroup (𝓞 F) F →* ℂˣ := κ'.toMonoidHom.comp q
  have hfa : Continuous fa := κ.continuous.comp QuotientGroup.continuous_mk
  have hfb : Continuous fb := κ'.continuous.comp QuotientGroup.continuous_mk
  have hfinite (P : FinPlace F) (x : (P.adicCompletion F)ˣ) :
      fa (IdeleGroup.ofAdicCompletion (𝓞 F) F P x) =
        fb (IdeleGroup.ofAdicCompletion (𝓞 F) F P x) := hfin P x
  have hinfinite (w : InfinitePlace F) (x : w.Completionˣ) :
      fa (IdeleGroup.ofCompletion (𝓞 F) F w x) =
        fb (IdeleGroup.ofCompletion (𝓞 F) F w x) := hinf w x
  have htruncEq (x : IdeleGroup (𝓞 F) F) (T : Finset (FinPlace F)) :
      fa (trunc x T) = fb (trunc x T) := by
    simp only [trunc, map_mul, map_prod, hfinite, hinfinite]
  have hglobal (x : IdeleGroup (𝓞 F) F) : fa x = fb x :=
    (isClosed_eq hfa hfb).mem_of_tendsto (htrunc x) (Eventually.of_forall (htruncEq x))
  apply ContinuousMonoidHom.ext
  intro y
  exact QuotientGroup.induction_on y (fun x => hglobal x)

end ArtinPrimitiveRoots.A1.KummerProofs
