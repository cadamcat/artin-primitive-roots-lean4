import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.BridgeDefinitions
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Definitions

set_option autoImplicit false
set_option maxHeartbeats 800000
open NumberField IsDedekindDomain MeasureTheory
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a2_euler_sol
open ArtinPrimitiveRoots A1 A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}
variable (R : ReflectionSetup D S H Bd A ϑ bc μ v0)
  (η : HeckeChar F) (U : FrequencyData S D η)

private theorem eb_qI_pos (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) : 0 < qI I := by
  unfold qI
  have h := Ideal.absNorm_pos_of_nonZeroDivisors
    ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr (by simpa [Ideal.zero_eq_bot] using hI)⟩
  exact_mod_cast h

private theorem eb_multiset_norm_le_one {α : Type*} (s : Multiset α)
    (f : α → ℂ) (hf : ∀ x, x ∈ s → ‖f x‖ ≤ 1) : ‖(s.map f).prod‖ ≤ 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, norm_mul]
      exact mul_le_one₀ (hf a (by simp)) (norm_nonneg _)
        (ih fun x hx => hf x (Multiset.mem_cons_of_mem hx))

private theorem eb_theta_norm (hϑ : ∀ x, ‖((ϑ x : ℂˣ) : ℂ)‖ = 1)
    (I : Ideal (𝓞 F)) : ‖ϑ.idealValue I‖ ≤ 1 := by
  classical
  unfold HeckeChar.idealValue
  apply eb_multiset_norm_le_one
  intro P hP
  by_cases h : P.IsPrime ∧ P ≠ ⊥
  · have hprime : ‖ϑ.primeValue ⟨P, h.1, h.2⟩‖ ≤ 1 := by
      unfold HeckeChar.primeValue
      split_ifs with hUnram
      · have hχ := hϑ (IdeleClassGroup.ofAdicCompletion (𝓞 F) F
          ⟨P, h.1, h.2⟩ (toLoc ⟨P, h.1, h.2⟩
            (Units.mk0 (unif ⟨P, h.1, h.2⟩) (unif_ne_zero ⟨P, h.1, h.2⟩))))
        exact le_of_eq (by simpa [HeckeChar.loc] using hχ)
      · simp
    simpa [h] using hprime
  · simp [h]

private theorem eb_term_norm (u : U.U) (ξ w z : ℂ)
    (hgamma : ∀ c : S.SqfExtIdeal, ‖gamma D S A 2 c.1 (cgen R c)‖ ≤ 1)
    (hfinite : ∀ p : IdealTuple S,
      ‖finiteFactor R p.2.2.1 (Aideal R p.1 p.2.1) (Agen R p.1 p.2.1)
        ((U.repr u : F) * (bc.gen p.2.2.2 : F) ^ 6)‖ ≤
        qI p.2.2.1.1 * qI (Aideal R p.1 p.2.1).1)
    (p : IdealTuple S) :
    ‖calFTerm R η U u ξ w z p‖ ≤
      qI p.1.1 ^ (1 / 2 - ξ.re) * qI p.2.1.1 ^ (2 - 3 * ξ.re) *
        qI p.2.2.1.1 ^ (1 - w.re) * qI p.2.2.2.1 ^ (-6 * z.re) := by
  let qC := qI p.1.1
  let qN := qI p.2.1.1
  let qS := qI p.2.2.1.1
  let qR := qI p.2.2.2.1
  have hcpos : 0 < qC := eb_qI_pos _ p.1.2.1.1
  have hnpos : 0 < qN := eb_qI_pos _ p.2.1.2.1
  have hspos : 0 < qS := eb_qI_pos _ p.2.2.1.2.1
  have hrpos : 0 < qR := eb_qI_pos _ p.2.2.2.2.1
  have hAq : qI (Aideal R p.1 p.2.1).1 = qC * qN ^ 3 := by
    simp [qC, qN, Aideal, qI, R.exterior.mul_val, R.exterior.ofSqf_val,
      R.exterior.pow_val]
  have hcPow : ‖(qC : ℂ) ^ ((-1 / 2 : ℂ) - ξ)‖ = qC ^ (-1 / 2 - ξ.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hcpos]
    simp
  have hnPow : ‖(qN : ℂ) ^ ((-1 : ℂ) - 3 * ξ)‖ = qN ^ (-1 - 3 * ξ.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
    simp
  have hsPow : ‖(qS : ℂ) ^ (-w)‖ = qS ^ (-w.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hspos]
    simp
  have hrPow : ‖(qR : ℂ) ^ (-6 * z)‖ = qR ^ (-6 * z.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hrpos]
    simp
  have hmajor : ‖calFTerm R η U u ξ w z p‖ ≤
      1 * 1 * (qS * (qC * qN ^ 3)) * qC ^ (-1 / 2 - ξ.re) *
        qN ^ (-1 - 3 * ξ.re) * qS ^ (-w.re) * qR ^ (-6 * z.re) := by
    simp only [calFTerm, norm_mul]
    rw [hcPow, hnPow, hsPow, hrPow]
    have hFF := hfinite p
    rw [hAq] at hFF
    gcongr
    all_goals first
    | exact hgamma p.1
    | exact eb_theta_norm R.vartheta_unitary _
  have hcGroup : qC * qC ^ (-1 / 2 - ξ.re) = qC ^ (1 / 2 - ξ.re) := by
    conv_lhs => arg 1; rw [← Real.rpow_one qC]
    rw [← Real.rpow_add hcpos]
    congr 1 <;> ring
  have hnGroup : qN ^ (3 : ℕ) * qN ^ (-1 - 3 * ξ.re) =
      qN ^ (2 - 3 * ξ.re) := by
    rw [← Real.rpow_natCast qN 3, ← Real.rpow_add hnpos]
    congr 1 <;> ring
  have hsGroup : qS * qS ^ (-w.re) = qS ^ (1 - w.re) := by
    conv_lhs => arg 1; rw [← Real.rpow_one qS]
    rw [← Real.rpow_add hspos]
    congr 1 <;> ring
  calc
    _ ≤ 1 * 1 * (qS * (qC * qN ^ 3)) * qC ^ (-1 / 2 - ξ.re) *
        qN ^ (-1 - 3 * ξ.re) * qS ^ (-w.re) * qR ^ (-6 * z.re) := hmajor
    _ = (qC * qC ^ (-1 / 2 - ξ.re)) * (qN ^ 3 * qN ^ (-1 - 3 * ξ.re)) *
        (qS * qS ^ (-w.re)) * qR ^ (-6 * z.re) := by ring
    _ = _ := by rw [hcGroup, hnGroup, hsGroup]

private theorem eb_summable_product {α β : Type*} (f : α → ℝ) (g : β → ℝ)
    (hf : Summable f) (hg : Summable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ y, 0 ≤ g y) :
    Summable (fun p : α × β => f p.1 * g p.2) := by
  apply (summable_prod_of_nonneg (fun p : α × β => mul_nonneg (hf0 p.1) (hg0 p.2))).2
  constructor
  · intro x
    exact hg.mul_left (f x)
  · simp_rw [hg.tsum_mul_left]
    exact hf.mul_right (∑' y, g y)

theorem global_absolute (u : U.U) (ξ w z : ℂ)
    (hreg : initialRegion ξ w z)
    (hgamma : ∀ c : S.SqfExtIdeal, ‖gamma D S A 2 c.1 (cgen R c)‖ ≤ 1)
    (hfinite : ∀ p : IdealTuple S,
      ‖finiteFactor R p.2.2.1 (Aideal R p.1 p.2.1) (Agen R p.1 p.2.1)
        ((U.repr u : F) * (bc.gen p.2.2.2 : F) ^ 6)‖ ≤
        qI p.2.2.1.1 * qI (Aideal R p.1 p.2.1).1) :
    Summable (fun p : IdealTuple S => ‖calFTerm R η U u ξ w z p‖) := by
  obtain ⟨hξ, hw, hz⟩ := hreg
  let fC : S.SqfExtIdeal → ℝ := fun c => qI c.1 ^ (1 / 2 - ξ.re)
  let fN : S.ExtIdeal → ℝ := fun n => qI n.1 ^ (2 - 3 * ξ.re)
  let fS : S.ExtIdeal → ℝ := fun s => qI s.1 ^ (1 - w.re)
  let fR : S.ExtIdeal → ℝ := fun r => qI r.1 ^ (-6 * z.re)
  have hext (s : ℝ) (hs : 1 < s) :
      Summable (fun I : S.ExtIdeal => qI I.1 ^ (-s)) := by
    simpa [qI, idealNorm] using a2_bridge_COUNT_summable S s hs
  have hC : Summable fC := by
    have hs := (hext (ξ.re - 1 / 2) (by linarith)).comp_injective
      (show Function.Injective R.exterior.ofSqf from by
        intro c d h
        apply Subtype.ext
        simpa only [R.exterior.ofSqf_val] using congrArg Subtype.val h)
    change Summable (fun c : S.SqfExtIdeal =>
      qI (R.exterior.ofSqf c).1 ^ (-(ξ.re - 1 / 2))) at hs
    simpa only [R.exterior.ofSqf_val, neg_sub, fC] using hs
  have hN : Summable fN := by
    convert hext (3 * ξ.re - 2) (by linarith) using 1
    funext n
    dsimp [fN]
    congr 1 <;> ring
  have hS : Summable fS := by
    convert hext (w.re - 1) (by linarith) using 1
    funext s
    dsimp [fS]
    congr 1 <;> ring
  have hR : Summable fR := by
    convert hext (6 * z.re) (by linarith) using 1
    funext r
    dsimp [fR]
    congr 1 <;> ring
  have hC0 : ∀ c, 0 ≤ fC c := fun c => Real.rpow_nonneg (eb_qI_pos _ c.2.1.1).le _
  have hN0 : ∀ n, 0 ≤ fN n := fun n => Real.rpow_nonneg (eb_qI_pos _ n.2.1).le _
  have hS0 : ∀ s, 0 ≤ fS s := fun s => Real.rpow_nonneg (eb_qI_pos _ s.2.1).le _
  have hR0 : ∀ r, 0 ≤ fR r := fun r => Real.rpow_nonneg (eb_qI_pos _ r.2.1).le _
  have hSR : Summable (fun p : S.ExtIdeal × S.ExtIdeal => fS p.1 * fR p.2) :=
    eb_summable_product fS fR hS hR hS0 hR0
  have hNSR : Summable (fun p : S.ExtIdeal × S.ExtIdeal × S.ExtIdeal =>
      fN p.1 * (fS p.2.1 * fR p.2.2)) :=
    eb_summable_product fN (fun p : S.ExtIdeal × S.ExtIdeal => fS p.1 * fR p.2)
      hN hSR hN0
      (fun p : S.ExtIdeal × S.ExtIdeal => mul_nonneg (hS0 p.1) (hR0 p.2))
  have hAll : Summable (fun p : IdealTuple S =>
      fC p.1 * (fN p.2.1 * (fS p.2.2.1 * fR p.2.2.2))) :=
    eb_summable_product fC
      (fun p : S.ExtIdeal × S.ExtIdeal × S.ExtIdeal =>
        fN p.1 * (fS p.2.1 * fR p.2.2)) hC hNSR hC0
      (fun p : S.ExtIdeal × S.ExtIdeal × S.ExtIdeal =>
        mul_nonneg (hN0 p.1) (mul_nonneg (hS0 p.2.1) (hR0 p.2.2)))
  refine hAll.of_norm_bounded_eventually (Filter.Eventually.of_forall fun p => ?_)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
    fC, fN, fS, fR, mul_assoc] using eb_term_norm R η U u ξ w z hgamma hfinite p

end ArtinPrimitiveRoots.Proofs.a2_euler_sol
