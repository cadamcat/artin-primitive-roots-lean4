import ArtinPrimitiveRoots.A1.Proofs.A1_KUMMER.Local
import Mathlib.Topology.Algebra.Group.Quotient

/-! Finite Hilbert products and descent to the actual idèle class group. -/

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical Topology

noncomputable section

namespace ArtinPrimitiveRoots.A1.KummerProofs

variable {F : Type} [Field F] [NumberField F]

theorem kummer_character_exists (D : FieldData F) (H : HilbertData F) (a : Fˣ) :
    ∃ κ : KummerChar F, κ ^ 6 = 1 ∧
      (∀ (w : InfinitePlace F) (x : w.Completionˣ), infiniteComponent κ w x = 1) ∧
      (∀ P : FinPlace F, localComponent κ P = kummerLocal D H P (toLoc P a)) := by
  classical
  let A := FiniteAdeleRing (𝓞 F) F
  let f (P : FinPlace F) : (P.adicCompletion F)ˣ →* ℂˣ :=
    kummerLocal D H P (toLoc P a)
  let c (P : FinPlace F) : Aˣ →* (P.adicCompletion F)ˣ :=
    (Pi.evalMonoidHom (fun Q : FinPlace F => (Q.adicCompletion F)ˣ) P).comp
      RestrictedProduct.coeUnits
  have hc (P : FinPlace F) : Continuous (c P) := by
    apply Units.continuous_iff.mpr
    exact ⟨(RestrictedProduct.continuous_eval P).comp Units.continuous_val,
      (RestrictedProduct.continuous_eval P).comp Units.continuous_coe_inv⟩
  have hf (P : FinPlace F) : Continuous (fun x : Aˣ => f P (c P x)) :=
    (kummer_local_continuous D H P (toLoc P a)).comp (hc P)
  have hgood := kummer_local_eventually_unit_trivial D H a
  have hfinite (x : Aˣ) : Function.HasFiniteMulSupport (fun P => f P (c P x)) := by
    apply Filter.eventually_cofinite.mp
    filter_upwards [hgood, x.val.2, x.inv.2] with P hP hx hx'
    exact hP (c P x) ⟨hx, hx'⟩
  let g : Aˣ →* ℂˣ := MonoidHom.mk'
    (fun x => ∏ᶠ P : FinPlace F, f P (c P x)) (fun x y => by
      simp_rw [map_mul]
      exact finprod_mul_distrib (hfinite x) (hfinite y))
  have hg : Continuous g := by
    apply continuous_of_tendsto_nhds_one g
    have hO : IsOpen {x : A | ∀ P : FinPlace F, x P ∈ P.adicCompletionIntegers F} :=
      RestrictedProduct.isOpen_forall_mem
        (fun P : FinPlace F => Valued.isOpen_valuationSubring (P.adicCompletion F))
    have hV : {x : Aˣ | ∀ P : FinPlace F,
        (x : A) P ∈ P.adicCompletionIntegers F} ∈ 𝓝 (1 : Aˣ) :=
      (hO.preimage Units.continuous_val).mem_nhds (by intro P; exact one_mem _)
    have hI : {x : Aˣ | ∀ P : FinPlace F,
        ((x⁻¹ : Aˣ) : A) P ∈ P.adicCompletionIntegers F} ∈ 𝓝 (1 : Aˣ) :=
      (hO.preimage Units.continuous_coe_inv).mem_nhds (by intro P; exact one_mem _)
    have hC : {x : Aˣ | ∀ P : FinPlace F,
        c P x ∈ (P.adicCompletionIntegers F).units} ∈ 𝓝 (1 : Aˣ) := by
      filter_upwards [hV, hI] with x hx hx'
      intro P
      exact ⟨hx P, hx' P⟩
    let T : Finset (FinPlace F) := (Filter.eventually_cofinite.mp hgood).toFinset
    have houtside (P : FinPlace F) (hP : P ∉ T) :
        ∀ u : (P.adicCompletion F)ˣ,
          u ∈ (P.adicCompletionIntegers F).units → f P u = 1 := by
      simpa only [T, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using hP
    let E : Aˣ → ℂˣ := fun x => ∏ P ∈ T, f P (c P x)
    have hE : Continuous E := continuous_finsetProd T (fun P _ => hf P)
    have hEone : E 1 = 1 := by simp [E]
    have heq : (fun x : Aˣ => g x) =ᶠ[𝓝 (1 : Aˣ)] E := by
      filter_upwards [hC] with x hx
      apply finprod_eq_prod_of_mulSupport_subset
      intro P hP
      by_contra hPT
      exact hP (houtside P hPT (c P x) (hx P))
    apply (Filter.tendsto_congr' heq).mpr
    simpa only [hEone] using hE.tendsto (1 : Aˣ)
  have hpow (x : Aˣ) : g x ^ 6 = 1 := by
    change (∏ᶠ P : FinPlace F, f P (c P x)) ^ 6 = 1
    rw [finprod_pow (hfinite x) 6]
    apply finprod_eq_one_of_forall_eq_one
    intro P
    change Units.map D.σ0.toMonoidHom (H.hilb P (toLoc P a) (c P x) : Fˣ) ^ 6 = 1
    have hroot : (H.hilb P (toLoc P a) (c P x) : Fˣ) ^ 6 = 1 :=
      (mem_rootsOfUnity 6 _).mp (H.hilb P (toLoc P a) (c P x)).property
    rw [← map_pow, hroot, map_one]
  let p : IdeleGroup (𝓞 F) F →* Aˣ :=
    Units.map (MonoidHom.snd (InfiniteAdeleRing F) A)
  have hp : Continuous p := by
    apply Units.continuous_iff.mpr
    exact ⟨continuous_snd.comp Units.continuous_val,
      continuous_snd.comp Units.continuous_coe_inv⟩
  let G : IdeleGroup (𝓞 F) F →* ℂˣ := g.comp p
  have hG : Continuous G := hg.comp hp
  let N := IdeleGroup.principalSubgroup (𝓞 F) F
  have hN : N ≤ G.ker := by
    intro x hx
    obtain ⟨b, rfl⟩ := hx
    let rootMap : rootsOfUnity 6 F →* ℂˣ :=
      (Units.map D.σ0.toMonoidHom).comp (rootsOfUnity 6 F).subtype
    obtain ⟨hsupport, hprod⟩ := H.product_formula a b
    change (∏ᶠ P : FinPlace F,
      rootMap (H.hilb P (toLoc P a) (toLoc P b))) = 1
    rw [← rootMap.map_finprod hsupport, hprod, rootMap.map_one]
  let C : IdeleClassGroup (𝓞 F) F →* ℂˣ := QuotientGroup.lift N G hN
  have hC : Continuous C := by
    apply (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr
    exact hG
  let κ : KummerChar F := ⟨C, hC⟩
  refine ⟨κ, ?_, ?_, ?_⟩
  · apply ContinuousMonoidHom.ext
    intro q
    refine QuotientGroup.induction_on q (fun x => ?_)
    simp only [ContinuousMonoidHom.pow_apply, ContinuousMonoidHom.one_toFun]
    change g (p x) ^ 6 = 1
    exact hpow (p x)
  · intro w u
    change g (p (IdeleGroup.ofCompletion (𝓞 F) F w u)) = 1
    have hproj : p (IdeleGroup.ofCompletion (𝓞 F) F w u) = 1 := by
      apply Units.ext
      rfl
    rw [hproj, map_one]
  · intro P
    apply MonoidHom.ext
    intro u
    change (∏ᶠ Q : FinPlace F,
      f Q (c Q (p (IdeleGroup.ofAdicCompletion (𝓞 F) F P u)))) = f P u
    have hout (Q : FinPlace F) (hQ : Q ≠ P) :
        c Q (p (IdeleGroup.ofAdicCompletion (𝓞 F) F P u)) = 1 := by
      apply Units.ext
      change FiniteAdeleRing.ofAdicCompletion F P (u : P.adicCompletion F) Q = 1
      exact RestrictedProduct.mulSingle_eq_of_ne _ _ hQ
    rw [finprod_eq_single _ P (fun Q hQ => by rw [hout Q hQ, map_one])]
    congr 1
    apply Units.ext
    change FiniteAdeleRing.ofAdicCompletion F P (u : P.adicCompletion F) P =
      (u : P.adicCompletion F)
    exact RestrictedProduct.mulSingle_eq_same _ _ _

end ArtinPrimitiveRoots.A1.KummerProofs
