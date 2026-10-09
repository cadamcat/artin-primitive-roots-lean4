import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.IndexValue
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianSquare
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianNorm

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1
open scoped ComplexConjugate

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

local instance measurableGaussianSign (v : FinPlace F) :
    MeasurableSpace (v.adicCompletion F) := borel _
local instance borelGaussianSign (v : FinPlace F) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

private theorem quadraticIntegral_neg_conj (A : AddCharData F) (v : FinPlace F)
    (μ : Measure (v.adicCompletion F)) (hψ : LocalCharacterRegular A v)
    (a : (v.adicCompletion F)ˣ) (N : ℕ) :
    quadraticIntegral A v μ (-a) N =
    conj (quadraticIntegral A v μ a N) := by
  have hpoint (x : v.adicCompletion F) :
      A.ψ v (((-a : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x ^ 2) =
        conj (A.ψ v ((a : v.adicCompletion F) * x ^ 2)) := by
    have hnorm : ‖A.ψ v ((a : v.adicCompletion F) * x ^ 2)‖ = 1 :=
      hψ.2.2 _
    rw [show ((-a : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x ^ 2 =
      -((a : v.adicCompletion F) * x ^ 2) by simp]
    rw [(A.ψ v).map_neg_eq_inv]
    exact Complex.inv_eq_conj hnorm
  change (∫ x, A.ψ v (((-a : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x ^ 2)
      ∂μ.restrict (localBall v N)) =
    conj (∫ x, A.ψ v ((a : v.adicCompletion F) * x ^ 2)
      ∂μ.restrict (localBall v N))
  rw [← integral_conj]
  apply integral_congr_ae
  exact ae_of_all _ hpoint

private theorem stableValue_neg_conj (D : FieldData F) (A : AddCharData F)
    (W : LocalGaussianData A) (v : FinPlace F) (a : (v.adicCompletion F)ˣ) :
    conj (W.stableValue v a) = W.stableValue v (-a) := by
  let N := max (W.cutoff v a) (W.cutoff v (-a))
  have ha : W.cutoff v a ≤ N := le_max_left _ _
  have hna : W.cutoff v (-a) ≤ N := le_max_right _ _
  calc
    conj (W.stableValue v a) =
        conj (quadraticIntegral A v (W.measure v) a N) := by
          change conj (quadraticIntegral A v (W.measure v) a (W.cutoff v a)) = _
          rw [← W.stable v a N ha]
    _ = quadraticIntegral A v (W.measure v) (-a) N :=
      (quadraticIntegral_neg_conj A v (W.measure v)
        (local_character_regular D A v) a N).symm
    _ = W.stableValue v (-a) := W.stable v (-a) N hna

/-- The index is real of unit modulus because -1 is a local square.
Guide: PROOFS.md:468–475. Uses: local_index_square; local_index_norm; primitive fourth root from D. -/
theorem local_index_sign (D : FieldData F) (A : AddCharData F) (W : LocalGaussianData A)
    (v : FinPlace F) (a : (v.adicCompletion F)ˣ) :
    ((W.index v a : ℂˣ) : ℂ) = 1 ∨ ((W.index v a : ℂˣ) : ℂ) = -1 := by
  let ζu : Fˣ := Units.mk0 D.ζ12 (D.hζ12.ne_zero (by norm_num))
  let ξ : (v.adicCompletion F)ˣ := toLoc v ζu
  let i : (v.adicCompletion F)ˣ := ξ ^ 3
  have hnegF : D.ζ12 ^ 6 = -1 := by
    have hroot : IsPrimitiveRoot (D.ζ12 ^ 6) 2 := by
      simpa using D.hζ12.pow_of_dvd (p := 6) (by norm_num : (6 : ℕ) ≠ 0)
        (by norm_num : 6 ∣ 12)
    exact hroot.eq_neg_one_of_two_right
  have hξ : ξ ^ 6 = -1 := by
    apply Units.ext
    change ((algebraMap F (v.adicCompletion F)) D.ζ12) ^ 6 = -1
    rw [← map_pow, hnegF, map_neg, map_one]
  have hi : i ^ 2 = -1 := by
    calc
      i ^ 2 = ξ ^ 6 := by
        dsimp [i]
        rw [← pow_mul]
      _ = -1 := hξ

  have hnegAbsOne : absFin v ((-1 : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
    have hpos := (local_absolute_value v).2.1 (-1 : (v.adicCompletion F)ˣ)
    have hsq :
        absFin v ((-1 : (v.adicCompletion F)ˣ) : v.adicCompletion F) ^ 2 = 1 := by
      simpa [pow_two, (local_absolute_value v).1] using
        ((local_absolute_value v).2.2 (-1 : (v.adicCompletion F)ˣ)
          (-1 : (v.adicCompletion F)ˣ)).symm
    nlinarith
  have hnegAbs (u : (v.adicCompletion F)ˣ) :
      absFin v ((-u : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
        absFin v (u : v.adicCompletion F) := by
    calc
      absFin v ((-u : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
          absFin v (((-1 : (v.adicCompletion F)ˣ) * u : (v.adicCompletion F)ˣ) :
            v.adicCompletion F) := by congr 1; ext; simp
      _ = absFin v ((-1 : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
          absFin v (u : v.adicCompletion F) :=
        (local_absolute_value v).2.2 (-1 : (v.adicCompletion F)ˣ) u
      _ = absFin v (u : v.adicCompletion F) := by rw [hnegAbsOne]; simp

  have hindexOne : W.index v (1 : (v.adicCompletion F)ˣ) = 1 := by
    apply Units.ext
    simp [LocalGaussianData.index, (local_absolute_value v).1,
      W.integral_ne_zero v (1 : (v.adicCompletion F)ˣ)]
  have hindexNegOne : W.index v (-1 : (v.adicCompletion F)ˣ) =
      W.index v (1 : (v.adicCompletion F)ˣ) := by
    have h := local_index_square D A W v (1 : (v.adicCompletion F)ˣ) i
    have hsquare : (1 : (v.adicCompletion F)ˣ) * i ^ 2 = -1 := by
      rw [hi]
      simp
    rw [hsquare] at h
    exact h
  let Ineg : ℂ := quadraticIntegral A v (W.measure v) (-1 : (v.adicCompletion F)ˣ)
    (W.cutoff v (-1 : (v.adicCompletion F)ˣ))
  let J : ℂ := quadraticIntegral A v (W.measure v) 1 (W.cutoff v 1)
  have hindexNegOneVal : ((W.index v (-1 : (v.adicCompletion F)ˣ) : ℂˣ) : ℂ) = 1 := by
    rw [hindexNegOne, hindexOne]
    rfl
  have hratioNegOne : Ineg / J = 1 := by
    have h := hindexNegOneVal
    change ((absFin v ((-1 : (v.adicCompletion F)ˣ) : v.adicCompletion F) ^
      (1 / 2 : ℝ) : ℝ) : ℂ) * Ineg / J = 1 at h
    rw [hnegAbsOne] at h
    simp only [Real.one_rpow, Complex.ofReal_one, one_mul] at h
    exact h
  have hJ : J ≠ 0 := by
    exact W.integral_ne_zero v (1 : (v.adicCompletion F)ˣ)
  have hInegJ : Ineg = J := by
    have h := hratioNegOne
    field_simp [hJ] at h
    exact h
  have hstableNegOne : W.stableValue v (-1 : (v.adicCompletion F)ˣ) =
      W.stableValue v (1 : (v.adicCompletion F)ˣ) := by
    simpa [LocalGaussianData.stableValue, Ineg, J] using hInegJ

  have hindexNeg : W.index v (-a) = W.index v a := by
    have h := local_index_square D A W v a i
    have hsquare : a * i ^ 2 = -a := by
      rw [hi]
      simp
    rw [hsquare] at h
    exact h
  have hconjIndex : conj ((W.index v a : ℂˣ) : ℂ) =
      ((W.index v (-a) : ℂˣ) : ℂ) := by
    change conj ((((absFin v (a : v.adicCompletion F) ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
      W.stableValue v a / W.stableValue v 1)) =
        ((absFin v ((-a : (v.adicCompletion F)ˣ) : v.adicCompletion F) ^
          (1 / 2 : ℝ) : ℝ) : ℂ) * W.stableValue v (-a) / W.stableValue v 1
    rw [map_div₀, map_mul, Complex.conj_ofReal]
    rw [stableValue_neg_conj D A W v a,
      stableValue_neg_conj D A W v (1 : (v.adicCompletion F)ˣ), hstableNegOne,
      hnegAbs a]
  have hconjSelf : conj ((W.index v a : ℂˣ) : ℂ) =
      ((W.index v a : ℂˣ) : ℂ) := by
    rw [hconjIndex, hindexNeg]
  have hsq : ((W.index v a : ℂˣ) : ℂ) ^ 2 = 1 := by
    calc
      ((W.index v a : ℂˣ) : ℂ) ^ 2 =
          ((W.index v a : ℂˣ) : ℂ) * conj ((W.index v a : ℂˣ) : ℂ) := by
            rw [hconjSelf]
            ring
      _ = ‖((W.index v a : ℂˣ) : ℂ)‖ ^ 2 := Complex.mul_conj' _
      _ = 1 := by rw [local_index_norm D A W v a]; norm_num
  exact (sq_eq_one_iff.mp hsq)

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
