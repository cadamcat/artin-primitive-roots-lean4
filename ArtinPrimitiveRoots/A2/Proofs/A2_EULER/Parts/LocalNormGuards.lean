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

theorem local_norm_guards (u : U.U) (v : FinPlace F) (hv : v ∉ S.Sf) (ξ w z : ℂ)
    (hθ : ‖ϑ.primeValue v‖ ≤ 1)
    (hξ : 2 / 3 < ξ.re) (hw : 0 < w.re) (hz : 0 < z.re) :
    ‖localV v z‖ < 1 ∧ ‖localWvar η U u v w‖ < 1 ∧
      ‖localEvar (ϑ := ϑ) v ξ z‖ < 1 := by
  have _ := hv
  have hq1 : 1 < qI v.asIdeal := qI_prime_gt_one v
  have hq : 0 < qI v.asIdeal := lt_trans zero_lt_one hq1
  have hcpow (s : ℂ) :
      ‖(qI v.asIdeal : ℂ) ^ s‖ = qI v.asIdeal ^ s.re :=
    Complex.norm_cpow_eq_rpow_re_of_pos hq s
  refine ⟨?_, ?_, ?_⟩
  · change ‖(qI v.asIdeal : ℂ) ^ (-6 * z)‖ < 1
    rw [hcpow]
    have hz_re : (-6 * z).re = -6 * z.re := by simp
    rw [hz_re]
    have hz_exp : -6 * z.re < 0 := by linarith
    exact Real.rpow_lt_one_of_one_lt_of_neg hq1 hz_exp
  · change ‖chi D v (U.repr u : F) * (qI v.asIdeal : ℂ) ^ (-w)‖ < 1
    rw [norm_mul, hcpow]
    have hw_re : (-w).re = -w.re := by simp
    rw [hw_re]
    have hw_exp : -w.re < 0 := by linarith
    have hw_lt : qI v.asIdeal ^ (-w.re) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hq1 hw_exp
    have hchi : ‖chi D v (U.repr u : F)‖ ≤ 1 :=
      (a2_bridge_SYMBOL D S).chi_norm_le v _
    calc
      ‖chi D v (U.repr u : F)‖ * qI v.asIdeal ^ (-w.re)
        ≤ 1 * qI v.asIdeal ^ (-w.re) :=
          mul_le_mul_of_nonneg_right hchi (Real.rpow_nonneg hq.le _)
      _ = qI v.asIdeal ^ (-w.re) := by rw [one_mul]
      _ < 1 := hw_lt
  · change ‖ϑ.primeValue v ^ 6 * (qI v.asIdeal : ℂ) ^ (4 - 6 * ξ) *
        (qI v.asIdeal : ℂ) ^ (-6 * z)‖ < 1
    rw [norm_mul, norm_mul, norm_pow, hcpow, hcpow]
    have hξ_re : (4 - 6 * ξ).re = 4 - 6 * ξ.re := by simp
    have hz_re : (-6 * z).re = -6 * z.re := by simp
    rw [hξ_re, hz_re]
    have hE_exp : 4 - 6 * ξ.re - 6 * z.re < 0 := by linarith
    have hE_lt : qI v.asIdeal ^ (4 - 6 * ξ.re - 6 * z.re) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hq1 hE_exp
    calc
      ‖ϑ.primeValue v‖ ^ 6 * qI v.asIdeal ^ (4 - 6 * ξ.re) *
          qI v.asIdeal ^ (-6 * z.re)
        ≤ (1 : ℝ) ^ 6 * qI v.asIdeal ^ (4 - 6 * ξ.re) *
          qI v.asIdeal ^ (-6 * z.re) := by
            gcongr
      _ = qI v.asIdeal ^ (4 - 6 * ξ.re - 6 * z.re) := by
        simp only [one_pow, one_mul]
        rw [← Real.rpow_add hq]
        congr 1; ring
      _ < 1 := hE_lt

end ArtinPrimitiveRoots.Proofs.a2_euler_sol
