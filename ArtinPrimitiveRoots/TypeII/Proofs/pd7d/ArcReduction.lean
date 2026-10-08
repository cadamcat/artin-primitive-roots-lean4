import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.ArcIndicator

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical
set_option autoImplicit false

lemma pd7d_majorArc_eq_reduced (x Y A₀ theta : ℝ) (hL : 0 ≤ Real.log x) :
    majorArc x Y A₀ theta ↔ ∃ p ∈ pd7dReducedPairs (Real.rpow (Real.log x) A₀),
      pd7dPairArc (Real.rpow (Real.log x) A₀) Y p theta := by
  let M := Real.rpow (Real.log x) A₀
  have hM : 0 ≤ M := Real.rpow_nonneg hL A₀
  change majorArc x Y A₀ theta ↔ ∃ p ∈ pd7dReducedPairs M, pd7dPairArc M Y p theta
  constructor
  · rintro ⟨h, k, hk, hkle, hcop, z, hz⟩
    have hkpos : 0 < k := hk
    have hkp : 0 < (k : ℝ) := by exact_mod_cast hkpos
    letI : NeZero k := ⟨Nat.ne_of_gt hkpos⟩
    let r := (h : ZMod k).val
    have hunit : IsUnit (h : ZMod k) :=
      (ZMod.coe_int_isUnit_iff_isCoprime h k).2
        ((Int.isCoprime_iff_gcd_eq_one.mpr hcop).symm)
    have hrunit : IsUnit (r : ZMod k) := by simpa only [r, ZMod.natCast_zmod_val] using hunit
    have hrcop : Nat.Coprime r k := (ZMod.isUnit_iff_coprime r k).1 hrunit
    have hrlt : r < k := ZMod.val_lt (h : ZMod k)
    have hkfloor : k ≤ ⌊M⌋₊ := Nat.le_floor hkle
    have hp : (r, k) ∈ pd7dReducedPairs M :=
      (pd7dReducedPairs_mem M (r, k)).2 ⟨hrlt.le.trans hkfloor, hkfloor, hk, hrlt, hrcop⟩
    let q : ℤ := h / (k : ℤ)
    have hrepI : (r : ℤ) + (k : ℤ) * q = h := by
      dsimp [r, q]
      rw [ZMod.val_intCast]
      exact Int.emod_add_mul_ediv h (k : ℤ)
    have hrep : (r : ℝ) + (k : ℝ) * (q : ℝ) = (h : ℝ) := by exact_mod_cast hrepI
    have hfrac : (h : ℝ) / k = (r : ℝ) / k + (q : ℝ) := by
      rw [← hrep]
      field_simp
      <;> ring
    refine ⟨(r, k), hp, q + z, ?_⟩
    have heq : theta - (r : ℝ) / k - ((q + z : ℤ) : ℝ) = theta - (h : ℝ) / k - (z : ℝ) := by
      rw [hfrac]
      push_cast
      ring
    rw [heq]
    exact hz
  · rintro ⟨p, hp, z, hz⟩
    obtain ⟨_, hkfloor, hk, hhlt, hcop⟩ := (pd7dReducedPairs_mem M p).1 hp
    have hkM : (p.2 : ℝ) ≤ M :=
      (by exact_mod_cast hkfloor : (p.2 : ℝ) ≤ (⌊M⌋₊ : ℝ)) |>.trans (Nat.floor_le hM)
    have hcopI : Int.gcd (p.1 : ℤ) (p.2 : ℤ) = 1 := by
      simpa only [Int.gcd_def, Int.natAbs_natCast] using hcop
    refine ⟨(p.1 : ℤ), p.2, hk, hkM, hcopI, z, ?_⟩
    simpa only [Int.cast_natCast] using hz

end ArtinPrimitiveRoots.TypeII.PD
