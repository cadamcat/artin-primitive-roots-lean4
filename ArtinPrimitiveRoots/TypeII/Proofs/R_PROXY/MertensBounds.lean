import ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY.SieveAlgebra
import ArtinPrimitiveRoots.Ext.TypeIIInputs

/-!
Mertens bounds for the reciprocal mass and sieve product at the rough cutoff.
-/

namespace ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY

open ArtinPrimitiveRoots.TypeII
open Filter

/-- At the Type II rough cutoff, the reciprocal-prime mass is `O(log log x)`
and the Mertens product has its expected `L^(-0.24)` lower bound. -/
theorem rough_mertens_bounds :
    ∃ s₀ vMin x₀ : ℝ, 0 < s₀ ∧ 0 < vMin ∧ 2 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        let L := Real.log x
        (∑ p ∈ primesUpTo (roughCutoff x), 1 / (p : ℝ) ≤ s₀ * Real.log L) ∧
        vMin * Real.rpow L (-(24 / 100 : ℝ)) ≤ roughSieveProduct (roughCutoff x) := by
  let b : ℝ := 24 / 100
  let c : ℝ := Real.exp (-Real.eulerMascheroniConstant)
  let v : ℝ := c / 2
  let s₀ : ℝ := 2 + |Real.log v|
  have hb : 0 < b := by norm_num [b]
  have hc : 0 < c := by positivity
  have hv : 0 < v := by dsimp [v]; positivity
  have hs₀ : 0 < s₀ := by dsimp [s₀]; positivity
  obtain ⟨y₀, hy₀, hmertens⟩ :=
    ArtinPrimitiveRoots.Ext.TypeIIInputs.mertens.2 v hv
  have hW : Tendsto (fun x : ℝ => roughCutoff x) atTop atTop := by
    unfold roughCutoff
    have hpow : Tendsto (fun x : ℝ => Real.rpow (Real.log x) b) atTop atTop :=
      (tendsto_rpow_atTop hb).comp Real.tendsto_log_atTop
    exact Real.tendsto_exp_atTop.comp hpow
  have hWevent : ∀ᶠ x : ℝ in atTop, y₀ ≤ roughCutoff x :=
    hW.eventually (eventually_ge_atTop y₀)
  have hlogLog : Tendsto (fun x : ℝ => Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hlogLogEvent : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log (Real.log x) :=
    hlogLog.eventually_ge_atTop 1
  have htwoEvent : ∀ᶠ x : ℝ in atTop, 2 ≤ x := eventually_ge_atTop 2
  have hfinal : ∀ᶠ x : ℝ in atTop,
      2 ≤ x ∧ y₀ ≤ roughCutoff x ∧ 1 ≤ Real.log (Real.log x) := by
    filter_upwards [htwoEvent, hWevent, hlogLogEvent] with x hx₂ hxW hxLL
    exact ⟨hx₂, hxW, hxLL⟩
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp hfinal
  refine ⟨s₀, v, x₀, hs₀, hv, ?_, ?_⟩
  · exact (hx₀ x₀ le_rfl).1
  · intro x hx
    dsimp
    obtain ⟨hx₂, hxW, hlogLogOne⟩ := hx₀ x hx
    let L : ℝ := Real.log x
    let W : ℝ := roughCutoff x
    have hxpos : 0 < x := by linarith
    have hLpos : 0 < L := by dsimp [L]; exact Real.log_pos (by linarith)
    have hlogW : Real.log W = Real.rpow L b := by
      dsimp [W, roughCutoff, L, b]
      rw [Real.log_exp]
    have hlogWpos : 0 < Real.log W := by
      rw [hlogW]
      exact Real.rpow_pos_of_pos hLpos b
    have hMertens := hmertens W hxW
    have hprodLower : v ≤ roughSieveProduct W * Real.log W := by
      have hlow := (abs_le.mp hMertens).1
      dsimp [v, c] at hlow ⊢
      linarith
    have hVratio : v / Real.log W ≤ roughSieveProduct W :=
      (div_le_iff₀ hlogWpos).2 hprodLower
    have hVlower : v * Real.rpow L (-b) ≤ roughSieveProduct W := by
      calc
        v * Real.rpow L (-b) = v * (Real.rpow L b)⁻¹ := by
          exact congrArg (fun z : ℝ => v * z) (Real.rpow_neg hLpos.le b)
        _ = v / Real.rpow L b := by rw [div_eq_mul_inv]
        _ = v / Real.log W := by rw [hlogW]
        _ ≤ roughSieveProduct W := hVratio
    have hVtermPos : 0 < v * Real.rpow L (-b) :=
      mul_pos hv (Real.rpow_pos_of_pos hLpos _)
    have hVpos : 0 < roughSieveProduct W := lt_of_lt_of_le hVtermPos hVlower
    have hlogCompare := Real.log_le_log hVtermPos hVlower
    have hMass := reciprocal_prime_sum_le_neg_log_sieve_product W
    have hlogVfactor :
        Real.log (v * Real.rpow L (-b)) =
          Real.log v + (-b) * Real.log L := by
      calc
        Real.log (v * Real.rpow L (-b)) =
            Real.log v + Real.log (Real.rpow L (-b)) :=
              Real.log_mul hv.ne' (Real.rpow_pos_of_pos hLpos _).ne'
        _ = Real.log v + (-b) * Real.log L := by
          exact congrArg (fun z : ℝ => Real.log v + z)
            (Real.log_rpow hLpos (-b))
    have hMassLog :
        (∑ p ∈ primesUpTo W, 1 / (p : ℝ)) ≤
          -Real.log v + b * Real.log L := by
      calc
        _ ≤ -Real.log (roughSieveProduct W) := hMass
        _ ≤ -Real.log (v * Real.rpow L (-b)) := neg_le_neg hlogCompare
        _ = -Real.log v + b * Real.log L := by
          rw [hlogVfactor]
          ring
    have hlogL : 1 ≤ Real.log L := by simpa [L] using hlogLogOne
    have hlogLnonneg : 0 ≤ Real.log L := le_trans (by norm_num) hlogL
    have hconstant : -Real.log v ≤ |Real.log v| := neg_le_abs _
    have hbound : -Real.log v + b * Real.log L ≤ s₀ * Real.log L := by
      dsimp [s₀]
      have hAbsMul : |Real.log v| ≤ |Real.log v| * Real.log L := by
        nlinarith [mul_nonneg (abs_nonneg (Real.log v)) (by linarith : 0 ≤ Real.log L - 1)]
      have hbMul : b * Real.log L ≤ 2 * Real.log L := by
        apply mul_le_mul_of_nonneg_right _ hlogLnonneg
        norm_num [b]
      nlinarith
    exact ⟨hMassLog.trans hbound, by simpa [W] using hVlower⟩

end ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY
