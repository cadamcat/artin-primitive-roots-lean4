import ArtinPrimitiveRoots.A1.ThetaInterface
import ArtinPrimitiveRoots.Theta.TorusInd
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

/-! Shared declarations used by the local Jacquet packages and P-ANALYSIS-S. -/

open MeasureTheory Filter
open Set

/-- Borel σ-algebra on a completion (Mathlib has no `MeasurableSpace` instance on `adicCompletion`). -/
noncomputable instance instMeasurableSpaceAdicCompletion (v : FinPlace F) :
    MeasurableSpace (v.adicCompletion F) := borel _

instance instBorelSpaceAdicCompletion (v : FinPlace F) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

/-- **def:loc-haar**: the additive Haar measure of `K_v` normalized by `μ(O_v) = 1`. -/
structure LocHaar (v : FinPlace F) where
  μ : Measure (v.adicCompletion F)
  isHaar : μ.IsAddHaarMeasure
  norm_O : μ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) = 1

attribute [instance] LocHaar.isHaar

section SharedJacquet

variable {D : FieldData F} {H : HilbertData F} {v : FinPlace F}

/-- **jq:localchi**: basic properties of `localChi` on local units at `v ∤ 6`. -/
theorem localChi_basic (hv : (6 : 𝓞 F) ∉ v.asIdeal) :
    localChi D v 1 = 1 ∧ localChi D v (-1) = 1 ∧
    (∀ u u', IsLocUnit v u → IsLocUnit v u' → localChi D v (u * u') = localChi D v u * localChi D v u') ∧
    (∀ u, IsLocUnit v u → localChi D v u ^ 6 = 1) ∧
    (∀ u u', IsLocUnit v u → IsLocUnit v u' →
      Valued.v ((u : v.adicCompletion F) - u') < 1 → localChi D v u = localChi D v u') := by
  sorry

/-- **jq:hilb-unit** (tame case of P-COVER cov:ext-law): `C(ϖ^e, u) = χ(u)^{-2e}`. -/
theorem muThree_hilb_unif_unit (hv : (6 : 𝓞 F) ∉ v.asIdeal) (e : ℤ) (u : (v.adicCompletion F)ˣ)
    (hu : IsLocUnit v u) :
    ((muThree D (H.hilb v (unifLoc v ^ e) u) : ℂˣ) : ℂ) = localChi D v u ^ (-(2 * e)) := by
  sorry

/-- Normalized prime Gauss sums `g_j = q^{-1/2} Σ_{x mod 𝔭} χ(x)^j ψ(x/ϖ)` (10:384–390). -/
def gaussLoc (D : FieldData F) (A : AddCharData F) (v : FinPlace F) (j : ℤ) : ℂ :=
  ((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) *
    ∑ᶠ x : 𝓞 F ⧸ v.asIdeal, chiPow D v (algebraMap (𝓞 F) F x.out) j *
      A.ψ v (algebraMap F _ (algebraMap (𝓞 F) F x.out / unif v))

theorem g2_eq_gaussLoc (D : FieldData F) (A : AddCharData F) (v : FinPlace F) :
    g2 D A v = gaussLoc D A v 2 := rfl

/-- **jq:gauss-product** (10:391–400): `g_j g_{-j} = 1` for `6 ∤ j` at `v ∤ 6𝔇`. -/
theorem gaussLoc_mul_neg (D : FieldData F) (A : AddCharData F) (v : FinPlace F)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal) (hd : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal) (j : ℤ)
    (hj : ¬ (6 : ℤ) ∣ j) : gaussLoc D A v j * gaussLoc D A v (-j) = 1 := by
  sorry

private def besselExpKernel (ν x u : ℝ) : ℝ :=
  Real.exp (-x * Real.cosh u + ν * u)

private def schlafliKernel (ν x t : ℝ) : ℝ :=
  t ^ (ν - 1) * Real.exp (-t - x ^ 2 / (4 * t))

private theorem integrableOn_besselExpKernel_pos (ν x : ℝ) (hx : 0 < x) :
    IntegrableOn (fun u => besselExpKernel ν x u) (Ioi 0) := by
  let g : ℝ → ℝ := fun t => t⁻¹ * Real.exp (-x * Real.cosh (Real.log t) + ν * Real.log t)
  rw [show (fun u => besselExpKernel ν x u) =
      (fun u => Real.exp u * g (Real.exp u)) by
        funext u
        simp [g, besselExpKernel, Real.log_exp]
      ]
  have hbase : IntegrableOn
      (fun t : ℝ => t ^ |ν| * Real.exp (-(x / 2) * t ^ (1 : ℝ))) (Ioi 0) := by
    exact integrableOn_rpow_mul_exp_neg_mul_rpow (s := |ν|) (p := 1) (b := x / 2)
      (by have := abs_nonneg ν; linarith) one_pos (by linarith)
  have hbase1 : IntegrableOn
      (fun t : ℝ => t ^ |ν| * Real.exp (-(x / 2) * t ^ (1 : ℝ))) (Ioi 1) :=
    hbase.mono_set (by intro t ht; change 1 < t at ht; exact lt_trans zero_lt_one ht)
  have hg : IntegrableOn g (Ioi 1) := by
    apply Integrable.mono' hbase1
    · apply Measurable.aestronglyMeasurable
      fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      change 1 < t at ht
      have ht0 : 0 < t := lt_trans zero_lt_one ht
      have htlog : 0 < Real.log t := Real.log_pos ht
      have hcosh : t / 2 ≤ Real.cosh (Real.log t) := by
        rw [Real.cosh_eq, Real.exp_log ht0]
        have he := Real.exp_pos (-Real.log t)
        nlinarith
      have hexp : -x * Real.cosh (Real.log t) + ν * Real.log t ≤
          -(x / 2) * t + |ν| * Real.log t := by
        nlinarith [mul_le_mul_of_nonpos_left hcosh (neg_nonpos.mpr hx.le),
          mul_le_mul_of_nonneg_right (le_abs_self ν) htlog.le]
      have h_exp_le :
          Real.exp (-x * Real.cosh (Real.log t) + ν * Real.log t) ≤
            Real.exp (-(x / 2) * t + |ν| * Real.log t) :=
        Real.exp_le_exp.mpr hexp
      have h_inv : t⁻¹ ≤ 1 := by
        rw [inv_le_one₀ ht0]
        exact le_of_lt ht
      have hpow : Real.exp (|ν| * Real.log t) = t ^ |ν| := by
        rw [Real.rpow_def_of_pos ht0]
        congr 1
        ring
      have hnonneg : 0 ≤ Real.exp (-x * Real.cosh (Real.log t) + ν * Real.log t) :=
        (Real.exp_pos _).le
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (inv_nonneg.mpr ht0.le) hnonneg)]
      calc
        t⁻¹ * Real.exp (-x * Real.cosh (Real.log t) + ν * Real.log t) ≤
            1 * Real.exp (-(x / 2) * t + |ν| * Real.log t) :=
          (mul_le_mul_of_nonneg_right h_inv hnonneg).trans
            (mul_le_mul_of_nonneg_left h_exp_le (by norm_num))
        _ = t ^ |ν| * Real.exp (-(x / 2) * t ^ (1 : ℝ)) := by
          rw [one_mul, Real.exp_add, hpow, Real.rpow_one]
          ring
  have hfun : (fun u => Real.exp u * g (Real.exp u)) =
      (fun u => Real.exp u • g (Real.exp u)) := by
    funext u
    simp
  rw [hfun]
  have hg' : IntegrableOn g (Ioi (Real.exp 0)) := by simpa using hg
  exact (integrableOn_comp_exp_Ioi g 0).mpr hg'

private theorem integrable_besselExpKernel (ν x : ℝ) (hx : 0 < x) :
    Integrable (fun u => besselExpKernel ν x u) := by
  rw [← integrableOn_univ, ← @Iio_union_Ici ℝ _ (0 : ℝ), integrableOn_union]
  constructor
  · rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
    simp only [Function.comp_def, neg_preimage, neg_Iio, neg_zero]
    have hpos := integrableOn_besselExpKernel_pos (-ν) x hx
    convert hpos using 1
    funext u
    simp [besselExpKernel, Real.cosh_neg]
  · rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact integrableOn_besselExpKernel_pos ν x hx

private theorem integral_besselExpKernel_eq_two_besselK (ν x : ℝ) (hx : 0 < x) :
    (∫ u, besselExpKernel ν x u) = 2 * besselK ν x := by
  have hfull := integrable_besselExpKernel ν x hx
  rw [← integral_add_compl measurableSet_Ioi hfull]
  rw [compl_Ioi]
  rw [← integral_comp_neg_Ioi 0 (fun u => besselExpKernel ν x u)]
  simp only [neg_zero]
  have hnegEq : (fun u => besselExpKernel ν x (-u)) =
      (fun u => besselExpKernel (-ν) x u) := by
    funext u
    simp [besselExpKernel, Real.cosh_neg]
  rw [hnegEq]
  have hpoint' : ∀ u ∈ Ioi (0 : ℝ),
      besselExpKernel ν x u + besselExpKernel (-ν) x u =
        2 * (Real.exp (-x * Real.cosh u) * Real.cosh (ν * u)) := by
    intro u hu
    simp_rw [besselExpKernel, Real.cosh_eq, Real.exp_add]
    ring
  calc
    (∫ u in Ioi (0 : ℝ), besselExpKernel ν x u) +
        ∫ u in Ioi (0 : ℝ), besselExpKernel (-ν) x u =
      ∫ u in Ioi (0 : ℝ),
        (besselExpKernel ν x u + besselExpKernel (-ν) x u) := by
          exact (integral_add (integrableOn_besselExpKernel_pos ν x hx)
            (integrableOn_besselExpKernel_pos (-ν) x hx)).symm
    _ = ∫ u in Ioi (0 : ℝ),
        2 * (Real.exp (-x * Real.cosh u) * Real.cosh (ν * u)) := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
          exact hpoint' u hu
    _ = 2 * ∫ u in Ioi (0 : ℝ),
        Real.exp (-x * Real.cosh u) * Real.cosh (ν * u) := by
          rw [integral_const_mul]
    _ = 2 * besselK ν x := rfl

private theorem integral_schlafliKernel_eq (ν x : ℝ) (hx : 0 < x) :
    (∫ t in Ioi (0 : ℝ), schlafliKernel ν x t) =
      (x / 2) ^ ν * ∫ u, besselExpKernel ν x u := by
  let c := x / 2
  have hc : 0 < c := by dsimp [c]; linarith
  calc
    (∫ t in Ioi (0 : ℝ), schlafliKernel ν x t) =
        c * ∫ s in Ioi (0 : ℝ), schlafliKernel ν x (c * s) := by
          symm
          simpa [c] using (integral_comp_mul_left_Ioi' (fun t => schlafliKernel ν x t)
            0 hc)
    _ = ∫ u, (Real.exp u * (c * schlafliKernel ν x (c * Real.exp u))) := by
          rw [← integral_const_mul]
          exact (integral_comp_exp (fun s => c * schlafliKernel ν x (c * s))).symm
    _ = _ := by
          have hEq : ∀ u : ℝ,
              Real.exp u * (c * schlafliKernel ν x (c * Real.exp u)) =
                c ^ ν * besselExpKernel ν x u := by
            intro u
            have hcpos : 0 < c := hc
            have hepos : 0 < Real.exp u := Real.exp_pos u
            have hcosh : c * Real.exp u + x ^ 2 / (4 * (c * Real.exp u)) =
                x * Real.cosh u := by
              dsimp [c]
              rw [Real.cosh_eq]
              rw [Real.exp_neg]
              field_simp
              ring
            rw [schlafliKernel, besselExpKernel]
            have hneg : -(c * Real.exp u) - x ^ 2 / (4 * (c * Real.exp u)) =
                -x * Real.cosh u := by linarith [hcosh]
            rw [hneg]
            have hpower : Real.exp u * (c * (c * Real.exp u) ^ (ν - 1)) =
                c ^ ν * Real.exp (ν * u) := by
              have hstep : (c * Real.exp u) ^ ν =
                  (c * Real.exp u) ^ (ν - 1) * (c * Real.exp u) := by
                simpa [sub_add_cancel] using
                  (Real.rpow_add_one (mul_ne_zero hcpos.ne' hepos.ne') (ν - 1))
              calc
                Real.exp u * (c * (c * Real.exp u) ^ (ν - 1)) =
                    (c * Real.exp u) ^ (ν - 1) * (c * Real.exp u) := by ring
                _ = (c * Real.exp u) ^ ν := hstep.symm
                _ = c ^ ν * (Real.exp u) ^ ν := Real.mul_rpow hcpos.le hepos.le
                _ = c ^ ν * Real.exp (ν * u) := by
                  rw [Real.rpow_def_of_pos hepos, Real.log_exp]
                  congr 1
                  ring
            calc
              Real.exp u * (c * ((c * Real.exp u) ^ (ν - 1) *
                  Real.exp (-x * Real.cosh u))) =
                  (Real.exp u * (c * (c * Real.exp u) ^ (ν - 1))) *
                    Real.exp (-x * Real.cosh u) := by ring
              _ = (c ^ ν * Real.exp (ν * u)) * Real.exp (-x * Real.cosh u) :=
                    congrArg (fun z => z * Real.exp (-x * Real.cosh u)) hpower
              _ = c ^ ν * Real.exp (-x * Real.cosh u + ν * u) := by
                    rw [Real.exp_add]
                    ring
          calc
            (∫ u, Real.exp u * (c * schlafliKernel ν x (c * Real.exp u))) =
                ∫ u, c ^ ν * besselExpKernel ν x u := by
                  apply integral_congr_ae
                  filter_upwards [] with u
                  exact hEq u
            _ = c ^ ν * ∫ u, besselExpKernel ν x u := by rw [integral_const_mul]

private theorem besselK_eq_schlafli_proof (ν x : ℝ) (hx : 0 < x) :
    besselK ν x = 1 / 2 * (x / 2) ^ (-ν) *
      ∫ t in Set.Ioi (0 : ℝ), t ^ (ν - 1) * Real.exp (-t - x ^ 2 / (4 * t)) := by
  have hSch := integral_schlafliKernel_eq ν x hx
  have hfull := integral_besselExpKernel_eq_two_besselK ν x hx
  have hc : 0 < x / 2 := by linarith
  have hI :
      (∫ t in Ioi (0 : ℝ), t ^ (ν - 1) * Real.exp (-t - x ^ 2 / (4 * t))) =
        (x / 2) ^ ν * (2 * besselK ν x) := by
    dsimp [schlafliKernel] at hSch
    exact hSch.trans (congrArg (fun z : ℝ => (x / 2) ^ ν * z) hfull)
  calc
    besselK ν x = (1 / 2 : ℝ) * (x / 2) ^ (-ν) *
        ((x / 2) ^ ν * (2 * besselK ν x)) := by
          rw [Real.rpow_neg hc.le]
          field_simp
    _ = (1 / 2 : ℝ) * (x / 2) ^ (-ν) *
        ∫ t in Ioi (0 : ℝ), t ^ (ν - 1) * Real.exp (-t - x ^ 2 / (4 * t)) := by
          rw [← hI]

/-- **jq:bessel-bridge**: the frozen `besselK` (cosh form) equals Schläfli's form. -/
theorem besselK_eq_schlafli (ν x : ℝ) (hx : 0 < x) :
    besselK ν x = 1 / 2 * (x / 2) ^ (-ν) *
      ∫ t in Set.Ioi (0 : ℝ), t ^ (ν - 1) * Real.exp (-t - x ^ 2 / (4 * t)) := by
  exact besselK_eq_schlafli_proof ν x hx

end SharedJacquet

end ArtinPrimitiveRoots.A1.Theta
