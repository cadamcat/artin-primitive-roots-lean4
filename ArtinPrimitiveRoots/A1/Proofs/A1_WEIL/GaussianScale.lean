import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.IndexValue
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.LocalCharacter
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.HaarScale

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

local instance rankOneGaussianScale (v : FinPlace F) :
    (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).RankOne :=
  inferInstance

local instance normedFieldGaussianScale (v : FinPlace F) :
    NormedField (v.adicCompletion F) :=
  Valued.toNormedField (v.adicCompletion F) (WithZero (Multiplicative ℤ))

local instance measurableGaussianScale (v : FinPlace F) :
    MeasurableSpace (v.adicCompletion F) := borel _
local instance borelGaussianScale (v : FinPlace F) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

/-- Multiplication by an element of valuation `exp e` shifts the radius exponent by `e`. -/
private theorem localBall_mul_preimage (v : FinPlace F) (b : (v.adicCompletion F)ˣ)
    (N M : ℕ) (e : ℤ) (hb : Valued.v (b : v.adicCompletion F) = WithZero.exp e)
    (he : e + (N : ℤ) = M) :
    (MeasurableEquiv.mulLeft₀ (b : v.adicCompletion F) (Units.ne_zero b)) ⁻¹'
      localBall v M = localBall v N := by
  ext x
  change Valued.v ((b : v.adicCompletion F) * x) ≤ WithZero.exp (M : ℤ) ↔
    Valued.v x ≤ WithZero.exp (N : ℤ)
  rw [map_mul, hb]
  have hexp : WithZero.exp e * WithZero.exp (N : ℤ) = WithZero.exp (M : ℤ) := by
    rw [← WithZero.exp_add, he]
  rw [← hexp]
  have hepos : 0 < (WithZero.exp e : WithZero (Multiplicative ℤ)) := WithZero.exp_pos
  exact mul_le_mul_iff_right₀ hepos

/-- Change variables in one finite-ball Gaussian integral by multiplication by a scalar. -/
private theorem quadraticIntegral_mul_scale (A : AddCharData F) (v : FinPlace F)
    (μ : Measure (v.adicCompletion F)) (hμ : Measure.IsAddHaarMeasure μ)
    (a b : (v.adicCompletion F)ˣ) (N M : ℕ) (e : ℤ)
    (hb : Valued.v (b : v.adicCompletion F) = WithZero.exp e)
    (he : e + (N : ℤ) = M) :
    quadraticIntegral A v μ (a * b ^ 2) N =
      (absFin v (b : v.adicCompletion F) : ℂ)⁻¹ *
        quadraticIntegral A v μ a M := by
  let K := v.adicCompletion F
  let _ : NormedField K := normedFieldGaussianScale v
  let g : K ≃ᵐ K := MeasurableEquiv.mulLeft₀ (b : K) (Units.ne_zero b)
  let f : K → ℂ := fun y => A.ψ v ((a : K) * y ^ 2)
  have hpre : g ⁻¹' localBall v M = localBall v N := by
    simpa [g] using localBall_mul_preimage v b N M e hb he
  have hmap := setIntegral_map_equiv (μ := μ) g f (localBall v M)
  rw [hpre] at hmap
  have hscaled := hmap
  have hhaar : Measure.map g μ =
      (ENNReal.ofReal (absFin v (b : K)))⁻¹ • μ := by
    simpa [g] using local_haar_scale v μ hμ b
  rw [hhaar] at hscaled
  simp only [Measure.restrict_smul, integral_smul_measure] at hscaled
  have hr : 0 < absFin v (b : K) := (local_absolute_value v).2.1 b
  have hscalar :
      ((((ENNReal.ofReal (absFin v (b : K)))⁻¹).toReal : ℝ) : ℂ) =
        (absFin v (b : K) : ℂ)⁻¹ := by
    simp [ENNReal.toReal_inv, ENNReal.toReal_ofReal hr.le, Complex.ofReal_inv]
  have hintegrand (x : K) :
      A.ψ v (((a * b ^ 2 : Kˣ) : K) * x ^ 2) = f (g x) := by
    change A.ψ v (((a : K) * (b : K) ^ 2) * x ^ 2) = _
    simp only [f, g, MeasurableEquiv.coe_mulLeft₀]
    congr 1
    ring
  calc
    quadraticIntegral A v μ (a * b ^ 2) N =
        ∫ x in localBall v N, f (g x) ∂μ := by
          simp only [quadraticIntegral]
          change (∫ x, A.ψ v (((a * b ^ 2 : Kˣ) : K) * x ^ 2)
              ∂μ.restrict (localBall v N)) = _
          exact integral_congr_ae (ae_of_all _ hintegrand)
    _ = ∫ y in localBall v M, f y ∂Measure.map g μ := hmap.symm
    _ = (((ENNReal.ofReal (absFin v (b : K)))⁻¹).toReal : ℝ) •
          (∫ y in localBall v M, f y ∂μ) := hmap.trans hscaled.symm
    _ = (absFin v (b : K) : ℂ)⁻¹ *
          quadraticIntegral A v μ a M := by
          change (((ENNReal.ofReal (absFin v (b : K)))⁻¹).toReal : ℂ) *
            (∫ y in localBall v M, f y ∂μ) = _
          rw [hscalar]
          rfl

/-- Change the variable in stabilized integrals by multiplication by a local unit.
Uses: local_haar_scale; local_character_regular; W.stable. -/
theorem stable_value_square_scale (D : FieldData F) (A : AddCharData F) (W : LocalGaussianData A)
    (v : FinPlace F) (a b : (v.adicCompletion F)ˣ) :
    W.stableValue v (a * b ^ 2) =
      (absFin v (b : v.adicCompletion F) : ℂ)⁻¹ * W.stableValue v a := by
  have hb0 : Valued.v (b : v.adicCompletion F) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 (Units.ne_zero b)
  let e : ℤ := WithZero.log (Valued.v (b : v.adicCompletion F))
  have hb : Valued.v (b : v.adicCompletion F) = WithZero.exp e := by
    dsimp [e]
    exact (WithZero.exp_log hb0).symm
  let T : ℤ := max 0 ((W.cutoff v a : ℤ) - e)
  let N : ℕ := max (W.cutoff v (a * b ^ 2)) T.toNat
  let M : ℕ := Int.toNat ((N : ℤ) + e)
  have hT : 0 ≤ T := le_max_left _ _
  have hTto : (T.toNat : ℤ) = T := Int.toNat_of_nonneg hT
  have hNge : T.toNat ≤ N := le_max_right _ _
  have hTleN : T ≤ (N : ℤ) := by
    calc
      T = (T.toNat : ℤ) := hTto.symm
      _ ≤ (N : ℤ) := by exact_mod_cast hNge
  have hcutT : (W.cutoff v a : ℤ) - e ≤ T :=
    le_max_of_le_right le_rfl
  have hshift_nonneg : 0 ≤ (N : ℤ) + e := by
    omega
  have hshift : (M : ℤ) = (N : ℤ) + e := Int.toNat_of_nonneg hshift_nonneg
  have hNcut : W.cutoff v (a * b ^ 2) ≤ N := le_max_left _ _
  have hMcut : W.cutoff v a ≤ M := by
    have hcutZ : (W.cutoff v a : ℤ) ≤ (M : ℤ) := by
      rw [hshift]
      omega
    exact_mod_cast hcutZ
  calc
    W.stableValue v (a * b ^ 2) =
        quadraticIntegral A v (W.measure v) (a * b ^ 2) (W.cutoff v (a * b ^ 2)) := rfl
    _ = quadraticIntegral A v (W.measure v) (a * b ^ 2) N :=
      (W.stable v (a * b ^ 2) N hNcut).symm
    _ = (absFin v (b : v.adicCompletion F) : ℂ)⁻¹ *
          quadraticIntegral A v (W.measure v) a M :=
      quadraticIntegral_mul_scale A v (W.measure v) (W.isHaar v) a b N M e hb
        (by omega)
    _ = (absFin v (b : v.adicCompletion F) : ℂ)⁻¹ *
          quadraticIntegral A v (W.measure v) a (W.cutoff v a) := by
      rw [W.stable v a M hMcut]
    _ = (absFin v (b : v.adicCompletion F) : ℂ)⁻¹ * W.stableValue v a := rfl

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
