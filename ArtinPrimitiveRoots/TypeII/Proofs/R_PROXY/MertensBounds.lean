import ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY.SieveAlgebra
import ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY.SieveRemainder
import ArtinPrimitiveRoots.Ext.TypeIIInputs

/-!
Mertens bounds for the reciprocal mass and sieve product at the rough cutoff.
-/

namespace ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY

open ArtinPrimitiveRoots.TypeII
open Filter
open Classical

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

private theorem cast_nat_product_for_cutoff (S : Finset ℕ) :
    ((∏ p ∈ S, p : ℕ) : ℝ) = ∏ p ∈ S, (p : ℝ) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih => simp [Finset.prod_insert, hp, ih]

private theorem cast_nat_product_le_pow (W : ℝ) (S : Finset ℕ)
    (hbound : ∀ p ∈ S, (p : ℝ) ≤ W) :
    ((∏ p ∈ S, p : ℕ) : ℝ) ≤ W ^ S.card := by
  rw [cast_nat_product_for_cutoff]
  calc
    ∏ p ∈ S, (p : ℝ) ≤ ∏ p ∈ S, W :=
      Finset.prod_le_prod₀ (fun p hp => Nat.cast_nonneg p) hbound
    _ = W ^ S.card := by simp

/-- A product of fewer than `lam log log x` primes below the rough cutoff is
eventually at most `x^(δ/8)`. -/
theorem retained_subset_product_bound (δ lam : ℝ) (hδ : 0 < δ) (hlam : 0 < lam) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        let L := Real.log x
        let r : ℕ := ⌈lam * Real.log L⌉₊
        ∀ S ∈ (primesUpTo (roughCutoff x)).powerset.filter
            (fun S => S.card < r),
          ((∏ p ∈ S, p : ℕ) : ℝ) ≤ Real.rpow x (δ / 8) := by
  let α : ℝ := 24 / 100
  let β : ℝ := 74 / 100
  let η : ℝ := 26 / 100
  let K : ℝ := (8 / δ) * (2 * lam + 1)
  have hα : 0 < α := by norm_num [α]
  have hη : 0 < η := by norm_num [η]
  have hK : 0 < K := by dsimp [K]; positivity
  have hLpow : Tendsto (fun x : ℝ => Real.rpow (Real.log x) η) atTop atTop :=
    (tendsto_rpow_atTop hη).comp Real.tendsto_log_atTop
  have hGrowEvent : ∀ᶠ x : ℝ in atTop, K ≤ Real.rpow (Real.log x) η :=
    hLpow.eventually_ge_atTop K
  have hLogEvent : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually_ge_atTop 1
  have hTwoEvent : ∀ᶠ x : ℝ in atTop, 2 ≤ x := eventually_ge_atTop 2
  have hfinal : ∀ᶠ x : ℝ in atTop,
      2 ≤ x ∧ 1 ≤ Real.log x ∧ K ≤ Real.rpow (Real.log x) η := by
    filter_upwards [hTwoEvent, hLogEvent, hGrowEvent] with x hx₂ hL hKx
    exact ⟨hx₂, hL, hKx⟩
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp hfinal
  refine ⟨x₀, ?_, ?_⟩
  · exact (hx₀ x₀ le_rfl).1
  · intro x hx
    dsimp
    obtain ⟨hx₂, hLone, hGrow⟩ := hx₀ x hx
    let L : ℝ := Real.log x
    let W : ℝ := roughCutoff x
    let r : ℕ := ⌈lam * Real.log L⌉₊
    have hxpos : 0 < x := by linarith
    have hLpos : 0 < L := by linarith
    have hLnonneg : 0 ≤ L := hLpos.le
    have hWge : 1 ≤ W := by
      dsimp [W, roughCutoff]
      exact Real.one_le_exp (Real.rpow_nonneg hLnonneg α)
    have hLogLnonneg : 0 ≤ Real.log L := Real.log_nonneg hLone
    have harg : 0 ≤ lam * Real.log L := mul_nonneg hlam.le hLogLnonneg
    have hrLower : lam * Real.log L ≤ (r : ℝ) := by
      dsimp [r]
      exact_mod_cast (Nat.le_ceil (lam * Real.log L))
    have hrUpper : (r : ℝ) ≤ lam * Real.log L + 1 := by
      dsimp [r]
      exact (Nat.ceil_lt_add_one harg).le
    have hlogHalfRaw := Real.log_le_rpow_div hLnonneg (by norm_num : (0 : ℝ) < 1 / 2)
    have hlogHalf : Real.log L ≤ 2 * Real.rpow L (1 / 2 : ℝ) := by
      calc
        Real.log L ≤ Real.rpow L (1 / 2 : ℝ) / (1 / 2 : ℝ) := hlogHalfRaw
        _ = 2 * Real.rpow L (1 / 2 : ℝ) := by ring
    have hpowHalfAlpha :
        Real.rpow L (1 / 2 : ℝ) * Real.rpow L α = Real.rpow L β := by
      calc
        _ = Real.rpow L ((1 / 2 : ℝ) + α) :=
          (Real.rpow_add hLpos _ _).symm
        _ = Real.rpow L β := by congr 1 <;> norm_num [α, β]
    have hpowAlphaBeta : Real.rpow L α ≤ Real.rpow L β :=
      Real.rpow_le_rpow_of_exponent_le hLone (by norm_num [α, β])
    have hpowAlphanonneg : 0 ≤ Real.rpow L α := Real.rpow_nonneg hLnonneg α
    have hpowBetanonneg : 0 ≤ Real.rpow L β := Real.rpow_nonneg hLnonneg β
    have hcoef : 2 * lam + 1 ≤ (δ / 8) * Real.rpow L η := by
      have hmul := mul_le_mul_of_nonneg_left hGrow (by positivity : 0 ≤ δ / 8)
      calc
        2 * lam + 1 = (δ / 8) * K := by dsimp [K]; field_simp [ne_of_gt hδ]
        _ ≤ (δ / 8) * Real.rpow L η := hmul
    have hexponent : (r : ℝ) * Real.rpow L α ≤ (δ / 8) * L := by
      have hargBound : lam * Real.log L + 1 ≤
          2 * lam * Real.rpow L (1 / 2 : ℝ) + 1 := by
        have hmul := mul_le_mul_of_nonneg_left hlogHalf hlam.le
        nlinarith
      have hceilMul := mul_le_mul_of_nonneg_right hrUpper hpowAlphanonneg
      have hargMul := mul_le_mul_of_nonneg_right hargBound hpowAlphanonneg
      have hhalfProduct :
          (2 * lam * Real.rpow L (1 / 2 : ℝ) + 1) * Real.rpow L α ≤
            (2 * lam + 1) * Real.rpow L β := by
        have hsplit :
            (2 * lam * Real.rpow L (1 / 2 : ℝ) + 1) * Real.rpow L α =
              2 * lam * Real.rpow L β + Real.rpow L α := by
          calc
            _ = 2 * lam *
                (Real.rpow L (1 / 2 : ℝ) * Real.rpow L α) + Real.rpow L α := by ring
            _ = _ := by rw [hpowHalfAlpha]
        rw [hsplit]
        have hcoeffNonneg : 0 ≤ 2 * lam := by positivity
        have hscaled := mul_le_mul_of_nonneg_left hpowAlphaBeta hcoeffNonneg
        nlinarith
      calc
        (r : ℝ) * Real.rpow L α ≤
            (lam * Real.log L + 1) * Real.rpow L α := hceilMul
        _ ≤ (2 * lam * Real.rpow L (1 / 2 : ℝ) + 1) * Real.rpow L α := hargMul
        _ ≤ (2 * lam + 1) * Real.rpow L β := hhalfProduct
        _ ≤ ((δ / 8) * Real.rpow L η) * Real.rpow L β :=
          mul_le_mul_of_nonneg_right hcoef hpowBetanonneg
        _ = (δ / 8) * L := by
          have hpowEtaBeta : Real.rpow L η * Real.rpow L β = L := by
            calc
              _ = Real.rpow L (η + β) := (Real.rpow_add hLpos _ _).symm
              _ = Real.rpow L 1 := by congr 1 <;> norm_num [η, β]
              _ = L := Real.rpow_one L
          calc
            (δ / 8 * Real.rpow L η) * Real.rpow L β =
                δ / 8 * (Real.rpow L η * Real.rpow L β) := by ring
            _ = δ / 8 * L := by rw [hpowEtaBeta]
    have hWpower : W ^ r = Real.exp ((r : ℝ) * Real.rpow L α) := by
      change (Real.exp (Real.rpow L α)) ^ r = _
      exact (Real.exp_nat_mul (Real.rpow L α) r).symm
    have hxpower : Real.rpow x (δ / 8) = Real.exp ((δ / 8) * L) := by
      calc
        Real.rpow x (δ / 8) = Real.exp (Real.log x * (δ / 8)) :=
          Real.rpow_def_of_pos hxpos _
        _ = Real.exp ((δ / 8) * L) := by
          rw [show Real.log x = L by rfl, mul_comm]
    have hWpowerLe : W ^ r ≤ Real.rpow x (δ / 8) := by
      rw [hWpower, hxpower]
      exact Real.exp_le_exp.mpr hexponent
    intro S hS
    have hSmem := Finset.mem_filter.mp hS
    have hSP : S ⊆ primesUpTo W := Finset.mem_powerset.mp hSmem.1
    have hcard : S.card < r := hSmem.2
    have hprimeMem (p : ℕ) (hp : p ∈ primesUpTo W) :
        p.Prime ∧ (p : ℝ) ≤ W := by
      have hWnonneg : 0 ≤ W := le_of_lt (Real.exp_pos _)
      simp only [primesUpTo, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff,
        Nat.le_floor_iff hWnonneg] at hp
      exact and_comm.mp hp
    have hprimeLe (p : ℕ) (hp : p ∈ S) : (p : ℝ) ≤ W :=
      (hprimeMem p (hSP hp)).2
    have hprodBound := cast_nat_product_le_pow W S hprimeLe
    calc
      ((∏ p ∈ S, p : ℕ) : ℝ) ≤ W ^ S.card := hprodBound
      _ ≤ W ^ r := pow_le_pow_right₀ hWge (Nat.le_of_lt hcard)
      _ ≤ Real.rpow x (δ / 8) := hWpowerLe

/-- Choose a fixed sieve order coefficient so the factorial tail beats any
prescribed power of `log x`. -/
theorem factorial_decay_choice (s₀ H : ℝ) (hs₀ : 0 < s₀) (hH : 0 < H) :
    ∃ lam x₀ : ℝ, 0 < lam ∧ 2 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        let L := Real.log x
        let r : ℕ := ⌈lam * Real.log L⌉₊
        1 ≤ r ∧
          ∀ s : ℝ, 0 ≤ s → s ≤ s₀ * Real.log L →
            s ^ r / (r.factorial : ℝ) ≤ Real.rpow L (-H) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let lam : ℝ := 2 * Real.exp 1 * s₀ + (H + 1) / Real.log 2
  have hlam : 0 < lam := by
    dsimp [lam]
    positivity
  have hlamS : 2 * Real.exp 1 * s₀ ≤ lam := by
    dsimp [lam]
    exact le_add_of_nonneg_right (by positivity)
  have hlamH : H ≤ lam * Real.log 2 := by
    have hterm : H + 1 ≤ lam * Real.log 2 := by
      dsimp [lam]
      have heq : ((H + 1) / Real.log 2) * Real.log 2 = H + 1 :=
        div_mul_cancel₀ _ hlog2.ne'
      nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (Real.exp_pos 1).le) hs₀.le, hlog2]
    linarith
  have hlogLog : Tendsto (fun x : ℝ => Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hlogLogEvent : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log (Real.log x) :=
    hlogLog.eventually_ge_atTop 1
  have htwoEvent : ∀ᶠ x : ℝ in atTop, 2 ≤ x := eventually_ge_atTop 2
  have hfinal : ∀ᶠ x : ℝ in atTop,
      2 ≤ x ∧ 1 ≤ Real.log (Real.log x) := by
    filter_upwards [htwoEvent, hlogLogEvent] with x hx₂ hlog
    exact ⟨hx₂, hlog⟩
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp hfinal
  refine ⟨lam, x₀, hlam, (hx₀ x₀ le_rfl).1, ?_⟩
  intro x hx
  dsimp
  obtain ⟨hx₂, hlogLogOne⟩ := hx₀ x hx
  let L : ℝ := Real.log x
  let r : ℕ := ⌈lam * Real.log L⌉₊
  have hxpos : 0 < x := by linarith
  have hLpos : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by linarith)
  have hlogLone : 1 ≤ Real.log L := by simpa [L] using hlogLogOne
  have hlogLnonneg : 0 ≤ Real.log L := by linarith
  have hargNonneg : 0 ≤ lam * Real.log L := mul_nonneg hlam.le hlogLnonneg
  have hrLower : lam * Real.log L ≤ (r : ℝ) := by
    dsimp [r]
    exact_mod_cast (Nat.le_ceil (lam * Real.log L))
  have hrpos : 0 < (r : ℝ) := lt_of_lt_of_le
    (mul_pos hlam (by linarith : 0 < Real.log L)) hrLower
  have hr : 1 ≤ r := by
    have hrNat : 0 < r := by exact_mod_cast hrpos
    exact Nat.succ_le_iff.mpr hrNat
  refine ⟨hr, ?_⟩
  intro s hs0 hs
  have hsTail : 2 * Real.exp 1 * s ≤ (r : ℝ) := by
    calc
      2 * Real.exp 1 * s ≤ 2 * Real.exp 1 * (s₀ * Real.log L) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = (2 * Real.exp 1 * s₀) * Real.log L := by ring
      _ ≤ lam * Real.log L := mul_le_mul_of_nonneg_right hlamS hlogLnonneg
      _ ≤ (r : ℝ) := hrLower
  have htail := factorial_tail_bound s r hs0 hr hsTail
  have hhalf : (1 / 2 : ℝ) ^ r =
      Real.exp (-(Real.log 2) * (r : ℝ)) := by
    have hexp : Real.exp (-(Real.log 2)) = (1 / 2 : ℝ) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num
    calc
      (1 / 2 : ℝ) ^ r = (Real.exp (-(Real.log 2))) ^ r := by rw [hexp]
      _ = Real.exp ((r : ℝ) * (-(Real.log 2))) := (Real.exp_nat_mul _ _).symm
      _ = Real.exp (-(Real.log 2) * (r : ℝ)) := by congr 1 <;> ring
  have hexponent : -(Real.log 2) * (r : ℝ) ≤ -H * Real.log L := by
    have hscale : H * Real.log L ≤ lam * Real.log 2 * Real.log L :=
      mul_le_mul_of_nonneg_right hlamH hlogLnonneg
    have hceil : lam * Real.log 2 * Real.log L ≤ Real.log 2 * (r : ℝ) := by
      calc
        lam * Real.log 2 * Real.log L =
            Real.log 2 * (lam * Real.log L) := by ring
        _ ≤ Real.log 2 * (r : ℝ) :=
            mul_le_mul_of_nonneg_left hrLower hlog2.le
    nlinarith [hscale.trans hceil]
  have hhalfLe : (1 / 2 : ℝ) ^ r ≤ Real.rpow L (-H) := by
    calc
      (1 / 2 : ℝ) ^ r = Real.exp (-(Real.log 2) * (r : ℝ)) := hhalf
      _ ≤ Real.exp (-H * Real.log L) := Real.exp_le_exp.mpr hexponent
      _ = Real.rpow L (-H) := by
        rw [show -H * Real.log L = Real.log L * (-H) by ring]
        exact (Real.rpow_def_of_pos hLpos _).symm
  exact htail.trans hhalfLe

/-- The normalized truncated-sieve error is small once the reciprocal-prime
mass has factorial decay and the Mertens product has its lower bound. -/
theorem normalized_sieve_remainder_bound (x M A H s₀ vMin : ℝ) (r : ℕ)
    (I : Finset ℕ) (hx : 2 ≤ x) (hM : 0 < M) (hr : 1 ≤ r)
    (hvMin : 0 < vMin)
    (hI : ∀ m ∈ I, 0 < m ∧ (m : ℝ) ≤ 2 * M)
    (hMass : (∑ p ∈ primesUpTo (roughCutoff x), 1 / (p : ℝ)) ≤
      s₀ * Real.log (Real.log x))
    (hDecay : ∀ s : ℝ, 0 ≤ s → s ≤ s₀ * Real.log (Real.log x) →
      s ^ r / (r.factorial : ℝ) ≤ Real.rpow (Real.log x) (-H))
    (hVlower : vMin * Real.rpow (Real.log x) (-(24 / 100 : ℝ)) ≤
      roughSieveProduct (roughCutoff x))
    (hVlarge : 2 ≤ vMin * Real.rpow (Real.log x) (H - A - 24 / 100)) :
    (∑ m ∈ I,
      |(if roughAbove m (roughCutoff x) then (1 : ℝ) else 0) -
        smallPrimeTruncation x r m|) /
      (M * roughSieveProduct (roughCutoff x)) ≤ Real.rpow (Real.log x) (-A) := by
  classical
  let L : ℝ := Real.log x
  let P : Finset ℕ := primesUpTo (roughCutoff x)
  have hLpos : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by linarith)
  have hLnonneg : 0 ≤ L := hLpos.le
  have hVpos : 0 < roughSieveProduct (roughCutoff x) := by
    have hpos : 0 < vMin * Real.rpow L (-(24 / 100 : ℝ)) :=
      mul_pos hvMin (Real.rpow_pos_of_pos hLpos _)
    exact lt_of_lt_of_le hpos (by simpa [L] using hVlower)
  have hPprime : ∀ p ∈ P, p.Prime := by
    intro p hp
    dsimp [P, primesUpTo] at hp
    exact (Finset.mem_filter.mp hp).2
  have hmass_nonneg :
      0 ≤ ∑ p ∈ primesUpTo (roughCutoff x), 1 / (p : ℝ) := by
    apply Finset.sum_nonneg
    intro p hp
    have hpprime : p.Prime := hPprime p (by simpa [P] using hp)
    positivity
  have hmass_decay :
      (∑ p ∈ primesUpTo (roughCutoff x), 1 / (p : ℝ)) ^ r /
          (r.factorial : ℝ) ≤ Real.rpow L (-H) := by
    apply hDecay
    · exact hmass_nonneg
    · simpa [L] using hMass
  have hdivisorMass :
      (∑ S ∈ (P.powerset.filter (fun S => S.card = r)),
        1 / ((∏ p ∈ S, p : ℕ) : ℝ)) ≤ Real.rpow L (-H) := by
    calc
      _ ≤ (∑ p ∈ P, 1 / (p : ℝ)) ^ r / (r.factorial : ℝ) :=
        elementary_symmetric_reciprocals P hPprime r
      _ = (∑ p ∈ primesUpTo (roughCutoff x), 1 / (p : ℝ)) ^ r /
          (r.factorial : ℝ) := by simp [P, div_eq_mul_inv]
      _ ≤ Real.rpow L (-H) := by simpa using hmass_decay
  have hsum := sieve_remainder_sum_bound x M r I hM hI hr
  have herror :
      (∑ m ∈ I,
        |(if roughAbove m (roughCutoff x) then (1 : ℝ) else 0) -
          smallPrimeTruncation x r m|) ≤ 2 * M * Real.rpow L (-H) := by
    calc
      _ ≤ 2 * M *
          (∑ S ∈ P.powerset.filter (fun S => S.card = r),
            1 / ((∏ p ∈ S, p : ℕ) : ℝ)) := by simpa [P] using hsum
      _ ≤ 2 * M * Real.rpow L (-H) :=
        mul_le_mul_of_nonneg_left hdivisorMass (by positivity)
  have hpowMul (a b : ℝ) :
      Real.rpow L a * Real.rpow L b = Real.rpow L (a + b) :=
    (Real.rpow_add hLpos a b).symm
  have hpowCancel :
      Real.rpow L (H - A - 24 / 100) * Real.rpow L (-H) =
        Real.rpow L (-(24 / 100 : ℝ) - A) := by
    calc
      _ = Real.rpow L ((H - A - 24 / 100) + (-H)) := hpowMul _ _
      _ = Real.rpow L (-(24 / 100 : ℝ) - A) := by congr 1 <;> ring
  have hpowSplit : Real.rpow L (-(24 / 100 : ℝ) - A) =
      Real.rpow L (-(24 / 100 : ℝ)) * Real.rpow L (-A) := by
    calc
      _ = Real.rpow L (-(24 / 100 : ℝ) + (-A)) := by congr 1 <;> ring
      _ = Real.rpow L (-(24 / 100 : ℝ)) * Real.rpow L (-A) := (hpowMul _ _).symm
  have hcore : 2 * Real.rpow L (-H) ≤
      roughSieveProduct (roughCutoff x) * Real.rpow L (-A) := by
    calc
      2 * Real.rpow L (-H) ≤
          (vMin * Real.rpow L (H - A - 24 / 100)) * Real.rpow L (-H) :=
        mul_le_mul_of_nonneg_right hVlarge (Real.rpow_nonneg hLnonneg _)
      _ = vMin * (Real.rpow L (H - A - 24 / 100) * Real.rpow L (-H)) := by ring
      _ = vMin * (Real.rpow L (-(24 / 100 : ℝ)) * Real.rpow L (-A)) := by
        rw [hpowCancel, hpowSplit]
      _ ≤ roughSieveProduct (roughCutoff x) * Real.rpow L (-A) := by
        calc
          vMin * (Real.rpow L (-(24 / 100 : ℝ)) * Real.rpow L (-A)) =
              (vMin * Real.rpow L (-(24 / 100 : ℝ))) * Real.rpow L (-A) := by ring
          _ ≤ roughSieveProduct (roughCutoff x) * Real.rpow L (-A) :=
            mul_le_mul_of_nonneg_right (by simpa [L] using hVlower)
              (Real.rpow_nonneg hLnonneg _)
  apply (div_le_iff₀ (mul_pos hM hVpos)).2
  calc
    _ ≤ 2 * M * Real.rpow L (-H) := herror
    _ ≤ M * (roughSieveProduct (roughCutoff x) * Real.rpow L (-A)) := by
      calc
        2 * M * Real.rpow L (-H) = M * (2 * Real.rpow L (-H)) := by ring
        _ ≤ M * (roughSieveProduct (roughCutoff x) * Real.rpow L (-A)) :=
          mul_le_mul_of_nonneg_left hcore hM.le
    _ = Real.rpow (Real.log x) (-A) * (M * roughSieveProduct (roughCutoff x)) := by
      dsimp [L]
      ring

end ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY
