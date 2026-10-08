import ArtinPrimitiveRoots.A1.Proofs.A1_KUMMER.ContinuousCharacters
import ArtinPrimitiveRoots.Hecke.Dict.WeakApproximation

/-! Prime-value uniqueness through approximation and local normalization. -/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots.A1 Filter Topology
open ArtinPrimitiveRoots.A1.KummerProofs
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_kummer_sol

variable {F : Type} [Field F] [NumberField F]

theorem char_eq_of_local_eq_away (κ κ' : KummerChar F) (T : Finset (FinPlace F))
    (h : ∀ P : FinPlace F, P ∉ T → localComponent κ P = localComponent κ' P) :
    κ = κ' := by
  classical
  let η : KummerChar F := κ / κ'
  have hout (P : FinPlace F) (hP : P ∉ T) : localComponent η P = 1 := by
    apply MonoidHom.ext
    intro x
    change localComponent κ P x / localComponent κ' P x = 1
    exact div_eq_one.mpr (congrArg (fun f : (P.adicCompletion F)ˣ →* ℂˣ => f x) (h P hP))
  let W := (Finset.univ : Finset (InfinitePlace F))
  let U := (∀ P : T, (P.1.adicCompletion F)ˣ) × (∀ w : W, w.1.Completionˣ)
  let R := (∀ P : T, P.1.adicCompletion F) × (∀ w : W, w.1.Completion)
  let φ : U → ℂˣ := fun z =>
    (∏ P : T, localComponent η P.1 (z.1 P)) *
      ∏ w : W, infiniteComponent η w.1 (z.2 w)
  have hφ : Continuous φ := by
    apply Continuous.mul
    · apply continuous_finsetProd
      intro P _
      exact (η.continuous.comp
        (IdeleClassGroup.continuous_ofAdicCompletion (𝓞 F) F P.1)).comp
          ((continuous_apply P).comp continuous_fst)
    · apply continuous_finsetProd
      intro w _
      exact (η.continuous.comp
        (IdeleClassGroup.continuous_ofCompletion (𝓞 F) F w.1)).comp
          ((continuous_apply w).comp continuous_snd)
  let ρ : IdeleGroup (𝓞 F) F → U := fun x =>
    (fun P => Dictionary.ideleFiniteCoord P.1 x,
      fun w => Dictionary.ideleInfiniteCoordUnit w.1 x)
  have hρ : Continuous ρ := by
    apply Continuous.prodMk
    · apply continuous_pi
      intro P
      apply Units.continuous_iff.mpr
      exact ⟨((RestrictedProduct.continuous_eval P.1).comp continuous_snd).comp
          Units.continuous_val,
        ((RestrictedProduct.continuous_eval P.1).comp continuous_snd).comp
          Units.continuous_coe_inv⟩
    · apply continuous_pi
      intro w
      apply Units.continuous_iff.mpr
      exact ⟨((continuous_apply w.1).comp continuous_fst).comp Units.continuous_val,
        ((continuous_apply w.1).comp continuous_fst).comp Units.continuous_coe_inv⟩
  let g : ContinuousMonoidHom (IdeleGroup (𝓞 F) F) ℂˣ :=
    ⟨MonoidHom.mk' (fun x => φ (ρ x)) (fun x y => by
      simp only [φ, ρ, map_mul, Finset.prod_mul_distrib]
      ac_rfl), hφ.comp hρ⟩
  let q : IdeleGroup (𝓞 F) F →* IdeleClassGroup (𝓞 F) F := QuotientGroup.mk' _
  let f : ContinuousMonoidHom (IdeleGroup (𝓞 F) F) ℂˣ :=
    ⟨η.toMonoidHom.comp q, η.continuous.comp QuotientGroup.continuous_mk⟩
  have hfg : f = g := by
    apply idele_hom_ext
    · intro w x
      change infiniteComponent η w x = φ (ρ (IdeleGroup.ofCompletion (𝓞 F) F w x))
      dsimp only [φ, ρ]
      simp only [Dictionary.ideleFiniteCoord_ofCompletion, map_one, Finset.prod_const_one,
        one_mul]
      symm
      rw [Finset.prod_eq_single (⟨w, Finset.mem_univ w⟩ : W)]
      · rw [Dictionary.ideleInfiniteCoordUnit_ofCompletion_self]
      · intro v _ hv
        have hvw : v.1 ≠ w := fun heq => hv (Subtype.ext heq)
        rw [Dictionary.ideleInfiniteCoordUnit_ofCompletion_of_ne v.1 w hvw, map_one]
      · simp
    · intro P x
      change localComponent η P x = φ (ρ (IdeleGroup.ofAdicCompletion (𝓞 F) F P x))
      dsimp only [φ, ρ]
      simp only [Dictionary.ideleInfiniteCoordUnit_ofAdicCompletion, map_one,
        Finset.prod_const_one, mul_one]
      by_cases hPT : P ∈ T
      · symm
        rw [Finset.prod_eq_single (⟨P, hPT⟩ : T)]
        · rw [Dictionary.ideleFiniteCoord_ofAdicCompletion]
        · intro Q _ hQ
          have hQP : Q.1 ≠ P := fun heq => hQ (Subtype.ext heq)
          rw [Dictionary.ideleFiniteCoord_ofAdicCompletion_of_ne Q.1 P hQP, map_one]
        · simp
      · rw [hout P hPT, MonoidHom.one_apply]
        symm
        apply Finset.prod_eq_one
        intro Q _
        have hQP : Q.1 ≠ P := fun heq => hPT (heq ▸ Q.2)
        rw [Dictionary.ideleFiniteCoord_ofAdicCompletion_of_ne Q.1 P hQP, map_one]
  let d : F → R := fun a =>
    (fun P => algebraMap F (P.1.adicCompletion F) a,
      fun w => algebraMap F w.1.Completion a)
  have hd : DenseRange d := Dictionary.weakApproximation_denseRange T W
  let du : Fˣ → U := fun a =>
    (fun P => Units.map (algebraMap F (P.1.adicCompletion F)).toMonoidHom a,
      fun w => Units.map (algebraMap F w.1.Completion).toMonoidHom a)
  let val : U → R := fun z => (fun P => (z.1 P : P.1.adicCompletion F),
    fun w => (z.2 w : w.1.Completion))
  have hval : IsOpenEmbedding val :=
    (IsOpenEmbedding.piMap (fun P : T =>
      IsOpenUnits.isOpenEmbedding_unitsVal (M := P.1.adicCompletion F))).prodMap
      (IsOpenEmbedding.piMap (fun w : W =>
        IsOpenUnits.isOpenEmbedding_unitsVal (M := w.1.Completion)))
  have hdu : DenseRange du := by
    rw [DenseRange, dense_iff_inter_open]
    intro V hV hVne
    obtain ⟨a, ha⟩ := hd.exists_mem_open (hval.isOpenMap V hV)
      (hVne.image val)
    obtain ⟨z, hzV, hza⟩ := ha
    have ha0 : a ≠ 0 := by
      intro ha0
      let w : W := ⟨Classical.arbitrary (InfinitePlace F), Finset.mem_univ _⟩
      have heq := congrArg (fun t : R => t.2 w) hza
      change (z.2 w : w.1.Completion) = algebraMap F w.1.Completion a at heq
      rw [ha0, map_zero] at heq
      exact (z.2 w).ne_zero heq
    let au : Fˣ := Units.mk0 a ha0
    have heq : du au = z := by
      apply Prod.ext
      · funext P
        apply Units.ext
        exact (congrArg (fun t : R => t.1 P) hza).symm
      · funext w
        apply Units.ext
        exact (congrArg (fun t : R => t.2 w) hza).symm
    exact ⟨du au, heq ▸ hzV, au, rfl⟩
  have hprincipal (a : Fˣ) : φ (du a) = 1 := by
    have hr : ρ (IdeleGroup.unitEmbedding (𝓞 F) F a) = du a := by
      apply Prod.ext
      · funext P
        apply Units.ext
        rfl
      · funext w
        apply Units.ext
        rfl
    rw [← hr]
    change g (IdeleGroup.unitEmbedding (𝓞 F) F a) = 1
    rw [← hfg]
    change η (q (IdeleGroup.unitEmbedding (𝓞 F) F a)) = 1
    have hq : q (IdeleGroup.unitEmbedding (𝓞 F) F a) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨a, rfl⟩
    rw [hq, map_one]
  have hφone : φ = fun _ => (1 : ℂˣ) :=
    hdu.equalizer hφ continuous_const (funext hprincipal)
  have hη : η = 1 := by
    apply ContinuousMonoidHom.ext
    intro y
    refine QuotientGroup.induction_on y (fun x => ?_)
    change f x = 1
    rw [hfg]
    exact congrFun hφone (ρ x)
  exact div_eq_one.mp hη


theorem local_eq_of_prime_values (κ κ' : KummerChar F) (P : FinPlace F)
    (hκ : unramifiedAt κ P) (hκ' : unramifiedAt κ' P)
    (hv : primeValue κ P = primeValue κ' P) : localComponent κ P = localComponent κ' P := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_kummer_sol
