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

private theorem ea_hecke_primeValue_norm_le_one (χ : HeckeChar F)
    (hχ : IsOfFinOrder χ) (v : FinPlace F) : ‖χ.primeValue v‖ ≤ 1 := by
  classical
  unfold HeckeChar.primeValue
  split_ifs with hram
  · obtain ⟨n, hn, hpow⟩ := (isOfFinOrder_iff_pow_eq_one.mp hχ)
    let x : IdeleClassGroup (𝓞 F) F :=
      IdeleClassGroup.ofAdicCompletion (𝓞 F) F v
        (toLoc v (Units.mk0 (unif v) (unif_ne_zero v)))
    have hxpow : (χ x : ℂˣ) ^ n = 1 := by
      have h := congrArg (fun f : HeckeChar F => f x) hpow
      simpa using h
    have hxpowC : ((χ x : ℂ) ^ n) = 1 := by
      have h := congrArg (fun y : ℂˣ => (y : ℂ)) hxpow
      change (((χ x : ℂˣ) ^ n : ℂ) = 1) at h
      simpa only [Units.val_pow_eq_pow_val] using h
    have hxnorm : ‖(χ x : ℂ)‖ = 1 :=
      Complex.norm_eq_one_of_pow_eq_one hxpowC (Nat.ne_of_gt hn)
    have hloc : χ.loc v
        (toLoc v (Units.mk0 (unif v) (unif_ne_zero v))) = χ x := rfl
    rw [hloc]
    exact hxnorm.le
  · simp

private theorem ea_vartheta_primeValue_norm_le_one
    (R0 : ReflectionSetup D S H Bd A ϑ bc μ v0) (v : FinPlace F) :
    ‖ϑ.primeValue v‖ ≤ 1 := by
  classical
  unfold HeckeChar.primeValue
  split_ifs with hram
  · have hunit := ReflectionSetup.vartheta_unitary R0
      (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v
        (toLoc v (Units.mk0 (unif v) (unif_ne_zero v))) )
    simpa [HeckeChar.loc] using hunit.le
  · simp

theorem local_parameter_norms (hE : EulerHypotheses R η)
    (u : U.U) (v : FinPlace F) (hv : v ∉ S.Sf) (ξ w z : ℂ) :
    ‖localV v z‖ ≤ qI v.asIdeal ^ (-6 * z.re) ∧
    ‖localWvar η U u v w‖ ≤ qI v.asIdeal ^ (-w.re) ∧
    ‖localDvar η U u v ξ‖ ≤ qI v.asIdeal ^ (-ξ.re) ∧
    ‖localEvar (ϑ := ϑ) v ξ z‖ ≤ qI v.asIdeal ^ (4 - 6 * ξ.re - 6 * z.re) := by
  have hq : 0 < qI v.asIdeal := lt_trans zero_lt_one (qI_prime_gt_one v)
  have hcpow (s : ℂ) :
      ‖(qI v.asIdeal : ℂ) ^ s‖ = qI v.asIdeal ^ s.re := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hq]
  have hchi : ‖chi D v (U.repr u : F)‖ ≤ 1 :=
    (a2_bridge_SYMBOL D S).chi_norm_le v _
  have heta : ‖η.primeValue v‖ ≤ 1 := ea_hecke_primeValue_norm_le_one η hE.1 v
  have htheta : ‖ϑ.primeValue v‖ ≤ 1 := ea_vartheta_primeValue_norm_le_one R v
  refine ⟨?_, ?_, ?_, ?_⟩
  · change ‖(qI v.asIdeal : ℂ) ^ (-6 * z)‖ ≤ _
    rw [hcpow]
    congr 1
    simp
  · change ‖chi D v (U.repr u : F) * (qI v.asIdeal : ℂ) ^ (-w)‖ ≤ _
    rw [norm_mul, hcpow]
    calc
      ‖chi D v (U.repr u : F)‖ * qI v.asIdeal ^ (-w).re ≤
          1 * qI v.asIdeal ^ (-w).re :=
        mul_le_mul_of_nonneg_right hchi (Real.rpow_nonneg hq.le _)
      _ = qI v.asIdeal ^ (-w.re) := by congr 1 <;> simp
  · change ‖η.primeValue v * star (chi D v (U.repr u : F)) *
      (qI v.asIdeal : ℂ) ^ (-ξ)‖ ≤ _
    rw [norm_mul, norm_mul, norm_star, hcpow]
    calc
      ‖η.primeValue v‖ * ‖chi D v (U.repr u : F)‖ * qI v.asIdeal ^ (-ξ).re ≤
          (1 : ℝ) * 1 * qI v.asIdeal ^ (-ξ).re := by
        gcongr
      _ = qI v.asIdeal ^ (-ξ.re) := by congr 1 <;> simp
  · change ‖ϑ.primeValue v ^ 6 * (qI v.asIdeal : ℂ) ^ (4 - 6 * ξ) *
      (qI v.asIdeal : ℂ) ^ (-6 * z)‖ ≤ _
    rw [norm_mul, norm_mul, norm_pow, hcpow, hcpow]
    have hξ : (4 - 6 * ξ).re = 4 - 6 * ξ.re := by simp
    have hz : (-6 * z).re = -6 * z.re := by simp
    rw [hξ, hz]
    calc
      ‖ϑ.primeValue v‖ ^ 6 * qI v.asIdeal ^ (4 - 6 * ξ.re) *
          qI v.asIdeal ^ (-6 * z.re) ≤
        (1 : ℝ) ^ 6 * qI v.asIdeal ^ (4 - 6 * ξ.re) *
          qI v.asIdeal ^ (-6 * z.re) := by
            gcongr
      _ = qI v.asIdeal ^ (4 - 6 * ξ.re - 6 * z.re) := by
        simp only [one_pow, one_mul]
        rw [← Real.rpow_add hq]
        congr 1 <;> ring

end ArtinPrimitiveRoots.Proofs.a2_euler_sol
