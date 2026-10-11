import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.IndexValue

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

local instance finiteScaleMeasurable (v : FinPlace F) : MeasurableSpace (v.adicCompletion F) :=
  borel _
local instance finiteScaleBorel (v : FinPlace F) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

/-- Integer radii allow a rescaled truncation ball to lie inside the integer ring. -/
def localBallInt (v : FinPlace F) (N : ℤ) : Set (v.adicCompletion F) :=
  {x | Valued.v x ≤ WithZero.exp N}

/-- The same actual quadratic integral, with the radius extended to integers. -/
def quadraticIntegralInt (A : AddCharData F) (v : FinPlace F)
    (μ : Measure (v.adicCompletion F)) (a : (v.adicCompletion F)ˣ) (N : ℤ) : ℂ :=
  ∫ x in localBallInt v N, A.ψ v ((a : v.adicCompletion F) * x ^ 2) ∂μ

private theorem localBallInt_preimage_mul (v : FinPlace F)
    (b : (v.adicCompletion F)ˣ) (N k : ℤ)
    (hb : Valued.v (b : v.adicCompletion F) = WithZero.exp k) :
    (fun x : v.adicCompletion F => (b : v.adicCompletion F) * x) ⁻¹'
      localBallInt v (N + k) = localBallInt v N := by
  ext x
  change Valued.v ((b : v.adicCompletion F) * x) ≤ WithZero.exp (N + k) ↔
    Valued.v x ≤ WithZero.exp N
  rw [map_mul, hb, add_comm N k, WithZero.exp_add]
  exact mul_le_mul_iff_right₀ WithZero.exp_pos

/-- Scalar change of variables for each actual finite-ball Gaussian integral.
The measure Jacobian is an explicit hypothesis, supplied later by local_haar_scale.
The formula includes negative integer truncation radii and
uses a measurable equivalence, so it needs no whole-field integrability hypothesis. -/
theorem quadratic_integral_square_scale_int (A : AddCharData F) (v : FinPlace F)
    (μ : Measure (v.adicCompletion F)) (a b : (v.adicCompletion F)ˣ)
    (J : ℝ) (hJ : 0 < J)
    (hmap : Measure.map (fun x : v.adicCompletion F => (b : v.adicCompletion F) * x) μ =
      (ENNReal.ofReal J)⁻¹ • μ)
    (N k : ℤ) (hb : Valued.v (b : v.adicCompletion F) = WithZero.exp k) :
    quadraticIntegralInt A v μ (a * b ^ 2) N =
      (J : ℂ)⁻¹ * quadraticIntegralInt A v μ a (N + k) := by
  let e : v.adicCompletion F ≃ᵐ v.adicCompletion F :=
    (Homeomorph.mulLeft₀ (b : v.adicCompletion F) b.ne_zero).toMeasurableEquiv
  have he : (e : v.adicCompletion F → v.adicCompletion F) =
      (fun x => (b : v.adicCompletion F) * x) := rfl
  have hmapE : Measure.map e μ = (ENNReal.ofReal J)⁻¹ • μ := by
    simpa only [he] using hmap
  have hintegrand :
      (fun x : v.adicCompletion F => A.ψ v (((a * b ^ 2 : (v.adicCompletion F)ˣ) :
        v.adicCompletion F) * x ^ 2)) =
      (fun x => A.ψ v ((a : v.adicCompletion F) * ((b : v.adicCompletion F) * x) ^ 2)) := by
    funext x
    congr 1
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    ring
  unfold quadraticIntegralInt
  rw [hintegrand]
  calc
    (∫ x in localBallInt v N,
      A.ψ v ((a : v.adicCompletion F) * ((b : v.adicCompletion F) * x) ^ 2) ∂μ) =
        ∫ y in localBallInt v (N + k), A.ψ v ((a : v.adicCompletion F) * y ^ 2)
          ∂Measure.map e μ := by
      symm
      simpa only [he, localBallInt_preimage_mul v b N k hb] using
        (setIntegral_map_equiv e
          (fun y => A.ψ v ((a : v.adicCompletion F) * y ^ 2))
          (localBallInt v (N + k)) (μ := μ))
    _ = (J : ℂ)⁻¹ *
        ∫ y in localBallInt v (N + k), A.ψ v ((a : v.adicCompletion F) * y ^ 2) ∂μ := by
      rw [hmapE, Measure.restrict_smul, integral_smul_measure]
      simp only [ENNReal.toReal_inv, ENNReal.toReal_ofReal hJ.le,
        Complex.real_smul, Complex.ofReal_inv]

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
