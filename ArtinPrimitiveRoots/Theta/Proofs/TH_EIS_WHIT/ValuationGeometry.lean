import ArtinPrimitiveRoots.Theta.Proofs.«TH-GLOBAL-DATUM».TameGeometry

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

/-- Canonical valuation arithmetic and unit decomposition for ordinary quotient classes. -/
theorem whit_ordv_geometry {F : Type} [Field F] [NumberField F] (v : FinPlace F) :
    (ordv v (unifLoc v) = 1) ∧
    (∀ x y : (v.adicCompletion F)ˣ,
      ordv v (x * y) = ordv v x + ordv v y) ∧
    (∀ (x : (v.adicCompletion F)ˣ) (j : ℤ),
      ordv v (x ^ j) = j * ordv v x) ∧
    (∀ u : (v.adicCompletion F)ˣ, IsLocUnit v u ↔ ordv v u = 0) ∧
    (∀ x : (v.adicCompletion F)ˣ,
      IsLocUnit v (unitPart v x) ∧ x = unifLoc v ^ ordv v x * unitPart v x) := by
  let K := (v.adicCompletion F)ˣ
  have hxv (x : K) : Valued.v (x : v.adicCompletion F) = WithZero.exp (-ordv v x) := by
    have hx0 : Valued.v (x : v.adicCompletion F) ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr x.ne_zero
    rw [← WithZero.exp_log hx0]
    simp [ordv, WithZero.toAdd_unzero_eq_log hx0]
  have hπ : Valued.v (unifLoc v : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    change Valued.v ((unif v : F) : v.adicCompletion F) = WithZero.exp (-1 : ℤ)
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (HeightOneSpectrum.valuation_exists_uniformizer F v).choose_spec
  have hπord : ordv v (unifLoc v) = 1 := by
    have h := WithZero.exp_injective ((hxv (unifLoc v)).symm.trans hπ)
    omega
  have hmul (x y : K) : ordv v (x * y) = ordv v x + ordv v y := by
    have hval : WithZero.exp (-ordv v (x * y)) =
        WithZero.exp (-ordv v x + -ordv v y) := by
      rw [← hxv (x * y), Units.val_mul, map_mul, hxv x, hxv y, WithZero.exp_add]
    have h := WithZero.exp_injective hval
    omega
  have hpow (x : K) (j : ℤ) : ordv v (x ^ j) = j * ordv v x := by
    have hval : WithZero.exp (-ordv v (x ^ j)) =
        WithZero.exp (j • (-ordv v x)) := by
      rw [← hxv (x ^ j), Units.val_zpow_eq_zpow_val, map_zpow₀, hxv x,
        WithZero.exp_zsmul]
    simpa only [zsmul_eq_mul, Int.cast_id, mul_neg, neg_inj] using
      WithZero.exp_injective hval
  have hinv (x : K) : ordv v x⁻¹ = -ordv v x := by
    simpa using hpow x (-1)
  have hmem (x : K) : (x : v.adicCompletion F) ∈ v.adicCompletionIntegers F ↔
      0 ≤ ordv v x := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hxv x, WithZero.exp_le_one_iff]
    omega
  have hunit (u : K) : IsLocUnit v u ↔ ordv v u = 0 := by
    change ((u : v.adicCompletion F) ∈ v.adicCompletionIntegers F ∧
      ((u⁻¹ : K) : v.adicCompletion F) ∈ v.adicCompletionIntegers F) ↔ ordv v u = 0
    rw [hmem u, hmem u⁻¹, hinv u]
    omega
  have hdecomp (x : K) :
      IsLocUnit v (unitPart v x) ∧ x = unifLoc v ^ ordv v x * unitPart v x := by
    have hval : Valued.v (unitPart v x : v.adicCompletion F) = 1 := by
      simp only [unitPart, Units.val_mul, Units.val_zpow_eq_zpow_val]
      change Valued.v ((x : v.adicCompletion F) *
        (unifLoc v : v.adicCompletion F) ^ (-ordv v x)) = 1
      rw [map_mul, map_zpow₀, hxv x, hπ]
      rw [← WithZero.exp_zsmul, ← WithZero.exp_add]
      congr 1
      simp
    constructor
    · constructor
      · rw [HeightOneSpectrum.mem_adicCompletionIntegers, hval]
      · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
        have hval' : Valued.v (((unitPart v x)⁻¹ : K) : v.adicCompletion F) = 1 := by
          rw [Units.val_inv_eq_inv_val, map_inv₀, hval, inv_one]
        rw [hval']
    · symm
      dsimp [unitPart]
      calc
        unifLoc v ^ ordv v x * (x * unifLoc v ^ (-ordv v x)) =
            x * (unifLoc v ^ ordv v x * (unifLoc v ^ ordv v x)⁻¹) := by
          rw [zpow_neg]
          ac_rfl
        _ = x := by simp
  exact ⟨hπord, hmul, hpow, hunit, hdecomp⟩

end ArtinPrimitiveRoots.A1.Theta
