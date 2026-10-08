import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_WHIT.GoodFactor
import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_WHIT.GaussBound

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {H : HilbertData F} {v : FinPlace F}

/-- The two nonzero valuation classes in the spherical Whittaker factor. -/
theorem whit_spherical_factor_norm_le (L : FinLocalCover D H v) (τ : TameSplitting L)
    (T : TorusRep D H v) (B : TameTorusBasis T) (A : AddCharData F) (μ : LocHaar v)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal) (hd : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal)
    (s : ℂ) (f : L.L → T.V) (hf : IsSection L T s f) (h1 : f 1 = B.e 0)
    (hK : ∀ g, ∀ k ∈ τ.Kmax, f (g * k) = f g)
    (lam : T.V →ₗ[ℂ] ℂ) (hlam : ∀ k : ZMod 3, lam (B.e k) = if k = 0 then 1 else 0)
    (j : ℤ) (u : (v.adicCompletion F)ˣ) (hu : IsLocUnit v u)
    (k : L.L) (hk : k ∈ τ.Kmax) :
    ‖lam (T.σa (unifLoc v ^ j * u) (jacquet L A μ (rtr k f)))‖ ≤
      if (j : ZMod 3) = 0 then 1 else
        if (j : ZMod 3) = 1 then qv v ^ (-2 * s.re) else 0 := by
  classical
  have hrtr : rtr k f = f := by
    funext g
    exact hK g k hk
  have hrtrOne : rtr (1 : L.L) f = f := by
    funext g
    exact congrArg f (mul_one g)
  have hJ : jacquet L A μ f =
      B.e 0 + ((qv v : ℂ) ^ (-2 * s) * shellTerm D A v 1) • B.e 2 := by
    simpa [L.a_one, hrtrOne] using
      jacquet_spherical L τ T B A μ hv hd s f hf h1 hK 0
  have hchi : ‖localChi D v u‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one ((localChi_basic (D := D) hv).2.2.2.1 u hu)
      (by decide)
  have hphase (m : ℤ) : ‖localChi D v u ^ m‖ = 1 := by
    rw [norm_zpow, hchi]
    simp
  have hq : 0 < qv v := lt_trans zero_lt_one (qv_gt_one v)
  have hnorm : ‖(qv v : ℂ) ^ (-2 * s)‖ = qv v ^ (-2 * s.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hq]
    congr 1
    simp
  have hcoeff : ‖(qv v : ℂ) ^ (-2 * s) * shellTerm D A v 1‖ ≤
      qv v ^ (-2 * s.re) := by
    rw [norm_mul, hnorm]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (whit_shellTerm_one_norm_le D A v) (Real.rpow_nonneg hq.le (-2 * s.re))
  have hj2 : (2 : ZMod 3) + (j : ZMod 3) = 0 ↔ (j : ZMod 3) = 1 := by
    constructor
    · intro h
      exact add_left_cancel (h.trans (by decide : (2 : ZMod 3) + 1 = 0).symm)
    · intro h
      rw [h]
      decide
  rw [hrtr, hJ]
  simp only [map_add, map_smul, B.act j u hu, hlam, zero_add, smul_eq_mul, hj2]
  by_cases hj0 : (j : ZMod 3) = 0
  · simp [hj0, hphase]
  · by_cases hj1 : (j : ZMod 3) = 1
    · simpa [hj1, norm_mul, hphase] using hcoeff
    · simp [hj0, hj1]

end ArtinPrimitiveRoots.A1.Theta
