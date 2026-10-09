import ArtinPrimitiveRoots.A2.ZeroFree.Results
import ArtinPrimitiveRoots.A2.Proofs.«A2-FE-GLUE».CharacterBridge
import ArtinPrimitiveRoots.Hecke.Convexity
import ArtinPrimitiveRoots.Hecke.Dedekind

set_option autoImplicit false

open NumberField IsDedekindDomain ClassFieldTheory Filter Topology
open scoped Classical Topology

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.A2FreqP

open ArtinPrimitiveRoots.A2

variable {F : Type} [Field F] [NumberField F]

private theorem zf_dedekind_zeta_right_bound :
    ∃ A C : ℝ, 0 ≤ A ∧ 0 < C ∧
      ∀ s : ℂ, 1 < s.re → s.re ≤ 4 →
        ‖(s - 1) * NumberField.dedekindZeta F s‖ ≤
          C * (2 + |s.im|) ^ A := by
  obtain ⟨A, hA, htrivial⟩ :=
    ArtinPrimitiveRoots.Hecke.LSeriesRay_trivial_growth (K := F)
  obtain ⟨G, hGdiff, hGagree, _hGone⟩ :=
    ArtinPrimitiveRoots.Hecke.dedekindZeta_simple_pole_continuation F
  let m : ClassFieldTheory.RayClassModulus F := ⟨0, ∅⟩
  have hAgree : ∀ s : ℂ, 1 < s.re →
      G s = (s - 1) * ArtinPrimitiveRoots.Hecke.LSeriesRay
        (1 : ClassFieldTheory.RayClassGroup m →* ℂˣ) s := by
    intro s hs
    rw [hGagree s hs, ← ArtinPrimitiveRoots.Hecke.LSeriesRay_trivial_eq_dedekindZeta]
  obtain ⟨C, hC, hbound⟩ := htrivial 1 (by norm_num) (3 / 1000) (by norm_num)
  refine ⟨A, C, hA, hC, ?_⟩
  intro s hs₀ hs₄
  have h := hbound m G hGdiff hAgree s (by linarith) hs₄
  calc
    ‖(s - 1) * NumberField.dedekindZeta F s‖ = ‖G s‖ := by rw [hGagree s hs₀]
    _ ≤ C * (2 + |s.im|) ^ A := by
      simpa [m, ArtinPrimitiveRoots.Hecke.modulusNorm] using h

private def zf_dedekindCoeff : ℕ → ℂ := fun n =>
  Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n}

private theorem zf_dedekind_not_summable_one :
    ¬ LSeriesSummable (zf_dedekindCoeff (F := F)) (1 : ℂ) := by
  classical
  intro hsum
  have hsumNorm : Summable (fun n => ‖LSeries.term (zf_dedekindCoeff (F := F))
      (1 : ℂ) n‖) := hsum.norm
  let B : ℝ := ∑' n, ‖LSeries.term (zf_dedekindCoeff (F := F)) (1 : ℂ) n‖
  have hresPos : 0 < NumberField.dedekindZeta_residue F :=
    NumberField.dedekindZeta_residue_pos F
  have hbound (x : ℝ) (hx : 1 < x) :
      ‖NumberField.dedekindZeta F (x : ℂ)‖ ≤ B := by
    have hsumX : LSeriesSummable (zf_dedekindCoeff (F := F)) (x : ℂ) := by
      exact_mod_cast DedekindResidue.count_LSeriesSummable F (by simpa using hx)
    have hterm (n : ℕ) :
        ‖LSeries.term (zf_dedekindCoeff (F := F)) (x : ℂ) n‖ ≤
          ‖LSeries.term (zf_dedekindCoeff (F := F)) (1 : ℂ) n‖ := by
      rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
      split_ifs with hn
      · rfl
      · have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
        have hpow : (n : ℝ) ^ (1 : ℝ) ≤ (n : ℝ) ^ x :=
          Real.rpow_le_rpow_of_exponent_le hnreal (by linarith)
        have hnum : 0 ≤ ‖(zf_dedekindCoeff (F := F) n)‖ := norm_nonneg _
        exact div_le_div_of_nonneg_left hnum (by positivity) hpow
    calc
      ‖NumberField.dedekindZeta F (x : ℂ)‖ =
          ‖∑' n, LSeries.term (zf_dedekindCoeff (F := F)) (x : ℂ) n‖ := rfl
      _ ≤ ∑' n, ‖LSeries.term (zf_dedekindCoeff (F := F)) (x : ℂ) n‖ :=
        norm_tsum_le_tsum_norm hsumX.norm
      _ ≤ B := by
        dsimp [B]
        exact hsumX.norm.tsum_le_tsum hterm hsumNorm
  have hlinear : Tendsto (fun x : ℝ => (x - 1) * B)
      (𝓝[>] 1) (𝓝 0) := by
    have hid : Tendsto (fun x : ℝ => x) (𝓝[>] 1) (𝓝 1) :=
      (tendsto_id : Tendsto (fun x : ℝ => x) (𝓝 1) (𝓝 1)).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
    have hsub : Tendsto (fun x : ℝ => x - 1) (𝓝[>] 1) (𝓝 0) := by
      simpa using hid.sub_const (1 : ℝ)
    simpa using hsub.mul_const B
  have hsmall : ∀ᶠ x : ℝ in 𝓝[>] 1, (x - 1) * B <
      NumberField.dedekindZeta_residue F / 2 := by
    have hr : 0 < NumberField.dedekindZeta_residue F / 2 := by positivity
    have hevent := hlinear.eventually (Iio_mem_nhds hr)
    filter_upwards [hevent] with x hx
    simpa using hx
  have hlimit := NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT F
  have hnear : ∀ᶠ x : ℝ in 𝓝[>] 1,
      dist (((x - 1 : ℝ) : ℂ) * NumberField.dedekindZeta F (x : ℂ))
        (NumberField.dedekindZeta_residue F : ℂ) <
          NumberField.dedekindZeta_residue F / 2 := by
    have hr : 0 < NumberField.dedekindZeta_residue F / 2 := by positivity
    have hball : Metric.ball (NumberField.dedekindZeta_residue F : ℂ)
        (NumberField.dedekindZeta_residue F / 2) ∈
          𝓝 (NumberField.dedekindZeta_residue F : ℂ) := by
      exact Metric.ball_mem_nhds _ hr
    filter_upwards [hlimit.eventually hball] with x hx
    simpa only [Metric.mem_ball, Complex.ofReal_sub, Complex.ofReal_one] using hx
  have hgt : Set.Ioi (1 : ℝ) ∈ 𝓝[>] 1 := self_mem_nhdsWithin
  have hfalse : ∀ᶠ x : ℝ in 𝓝[>] 1, False := by
    filter_upwards [hsmall, hnear, hgt] with x hxsmall hxnear hxgt
    have hxgt : 1 < x := hxgt
    let z : ℂ := ((x - 1 : ℝ) : ℂ) * NumberField.dedekindZeta F (x : ℂ)
    have hupper : ‖z‖ ≤ (x - 1) * B := by
      dsimp [z]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (sub_pos.mpr hxgt)]
      exact mul_le_mul_of_nonneg_left (hbound x hxgt) (by linarith)
    have hdist : ‖(NumberField.dedekindZeta_residue F : ℂ) - z‖ <
        NumberField.dedekindZeta_residue F / 2 := by
      simpa [z, dist_eq_norm, norm_sub_rev] using hxnear
    have htriangle : ‖(NumberField.dedekindZeta_residue F : ℂ)‖ ≤
        ‖z‖ + ‖(NumberField.dedekindZeta_residue F : ℂ) - z‖ := by
      calc
        ‖(NumberField.dedekindZeta_residue F : ℂ)‖ =
            ‖z + ((NumberField.dedekindZeta_residue F : ℂ) - z)‖ := by congr 1 <;> ring
        _ ≤ ‖z‖ + ‖(NumberField.dedekindZeta_residue F : ℂ) - z‖ := norm_add_le _ _
    have hresNorm : ‖(NumberField.dedekindZeta_residue F : ℂ)‖ =
        NumberField.dedekindZeta_residue F := by
      rw [Complex.norm_real, Real.norm_of_nonneg hresPos.le]
    rw [hresNorm] at htriangle
    have hlower : NumberField.dedekindZeta_residue F / 2 < ‖z‖ := by linarith
    linarith
  obtain ⟨x, hxFalse⟩ := Filter.Eventually.exists hfalse
  exact hxFalse.elim

private theorem zf_dedekind_zeta_eq_zero_of_re_le_one {s : ℂ} (hs : s.re ≤ 1) :
    NumberField.dedekindZeta F s = 0 := by
  classical
  let f := zf_dedekindCoeff (F := F)
  have hnot : ¬ LSeriesSummable f s := by
    intro hsumm
    have hnorm : Summable (fun n => ‖LSeries.term f s n‖) := hsumm.norm
    have hterm (n : ℕ) : ‖LSeries.term f (1 : ℂ) n‖ ≤ ‖LSeries.term f s n‖ := by
      rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
      split_ifs with hn
      · rfl
      · have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
        have hpow : (n : ℝ) ^ s.re ≤ (n : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hnreal hs
        have hnum : 0 ≤ ‖f n‖ := norm_nonneg _
        exact div_le_div_of_nonneg_left hnum (by positivity) hpow
    have hnormOne : Summable (fun n => ‖LSeries.term f (1 : ℂ) n‖) :=
      hnorm.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
    have hsumOne : LSeriesSummable f (1 : ℂ) := by
      rw [LSeriesSummable, ← summable_norm_iff]
      exact hnormOne
    exact zf_dedekind_not_summable_one hsumOne
  change LSeries f s = 0
  exact LSeries.eq_zero_of_not_LSeriesSummable f s hnot

private theorem zf_dedekind_zeta_full_strip_bound :
    ∃ A C : ℝ, 0 ≤ A ∧ 0 < C ∧
      ∀ s : ℂ, 3 / 1000 ≤ s.re → s.re ≤ 4 →
        ‖(s - 1) * NumberField.dedekindZeta F s‖ ≤
          C * (2 + |s.im|) ^ A := by
  obtain ⟨A, C, hA, hC, hright⟩ := zf_dedekind_zeta_right_bound (F := F)
  refine ⟨A, C, hA, hC, ?_⟩
  intro s hs₀ hs₄
  by_cases hs : 1 < s.re
  · exact hright s hs hs₄
  · have hζ : NumberField.dedekindZeta F s = 0 :=
      zf_dedekind_zeta_eq_zero_of_re_le_one (F := F) (by linarith)
    simp [hζ]
    positivity

theorem zf_convexity_totallyComplex (hTC : IsTotallyComplex F) :
    ∃ A_F : ℝ, 0 < A_F ∧
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
        ∀ (ω : ArtinPrimitiveRoots.A1.HeckeChar F), IsOfFinOrder ω → ω ≠ 1 →
          ∀ 𝔣 : Ideal (𝓞 F), IsPrimitiveConductor ω 𝔣 →
            ∀ Λ : ℂ → ℂ,
              Differentiable ℂ Λ ∧
              (∀ s : ℂ, 1 < s.re → Λ s = heckeLSeries ω s) →
              (∀ s : ℂ, 3 / 1000 ≤ s.re → s.re ≤ 4 →
                ‖Λ s‖ ≤ C * Real.rpow (Ideal.absNorm 𝔣 : ℝ) (1 / 2 + ε) *
                  Real.rpow (2 + |s.im|) A_F) ∧
              (∀ s : ℂ, 3 / 1000 ≤ s.re → s.re ≤ 4 →
                ‖(s - 1) * NumberField.dedekindZeta F s‖ ≤
                  C * Real.rpow (2 + |s.im|) A_F) := by
  letI : IsTotallyComplex F := hTC
  obtain ⟨A_Z, C_Z, hA_Z, hC_Z, hZeta⟩ :=
    zf_dedekind_zeta_full_strip_bound (F := F)
  obtain ⟨A_H, hA_H, hRayConv⟩ :=
    ArtinPrimitiveRoots.Hecke.LSeriesRay_convexity (K := F)
  let A_F : ℝ := max A_H A_Z + 1
  have hA_F : 0 < A_F := by
    dsimp [A_F]
    have hmax : 0 ≤ max A_H A_Z := le_trans hA_H (le_max_left _ _)
    linarith
  have hA_Hle : A_H ≤ A_F := by
    dsimp [A_F]
    linarith [le_max_left A_H A_Z]
  have hA_Zle : A_Z ≤ A_F := by
    dsimp [A_F]
    linarith [le_max_right A_H A_Z]
  refine ⟨A_F, hA_F, ?_⟩
  intro ε hε
  obtain ⟨C_H, hC_H, hRay⟩ := hRayConv (ε / 2) (by linarith) (3 / 1000) (by norm_num)
  let C : ℝ := C_H + C_Z + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hC_Hle : C_H ≤ C := by dsimp [C]; linarith
  have hC_Zle : C_Z ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro ω hω hωne f hf Λ hΛ
  obtain ⟨m, ψ, hm, hψ, _hprimitive, hseries, _hseriesInv⟩ :=
    ArtinPrimitiveRoots.Proofs.A2FreqP.exists_primitive_ray_bridge
      ω hω hωne f hf
  have hAgreeRay : ∀ s : ℂ, 1 < s.re →
      Λ s = ArtinPrimitiveRoots.Hecke.LSeriesRay ψ s := by
    intro s hs
    rw [hΛ.2 s hs, hseries s hs]
  have hnormfNat : 0 < Ideal.absNorm f :=
    Ideal.absNorm_pos_of_nonZeroDivisors
      ⟨f, mem_nonZeroDivisors_iff_ne_zero.mpr (by simpa [Ideal.zero_eq_bot] using hf.1)⟩
  have hnormf : 0 < (Ideal.absNorm f : ℝ) := Nat.cast_pos.mpr hnormfNat
  have hnormfOne : 1 ≤ (Ideal.absNorm f : ℝ) := by
    exact_mod_cast Nat.succ_le_iff.mpr hnormfNat
  have hcondNat := ArtinPrimitiveRoots.Dictionary.conductorNorm_le_modulusNorm ψ
  have hcond : (ArtinPrimitiveRoots.Hecke.conductorNorm ψ : ℝ) ≤
      (Ideal.absNorm f : ℝ) := by
    exact_mod_cast (by simpa [hm] using hcondNat)
  have hmod : (ArtinPrimitiveRoots.Hecke.modulusNorm m : ℝ) =
      (Ideal.absNorm f : ℝ) := by exact_mod_cast hm
  have hcondPow :
      Real.rpow (ArtinPrimitiveRoots.Hecke.conductorNorm ψ : ℝ) (1 / 2 + ε / 2) ≤
        Real.rpow (Ideal.absNorm f : ℝ) (1 / 2 + ε / 2) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hcond (by positivity)
  have hbase :
      Real.rpow (ArtinPrimitiveRoots.Hecke.conductorNorm ψ : ℝ) (1 / 2 + ε / 2) *
        Real.rpow (ArtinPrimitiveRoots.Hecke.modulusNorm m : ℝ) (ε / 2) ≤
      Real.rpow (Ideal.absNorm f : ℝ) (1 / 2 + ε) := by
    calc
      _ ≤ Real.rpow (Ideal.absNorm f : ℝ) (1 / 2 + ε / 2) *
          Real.rpow (Ideal.absNorm f : ℝ) (ε / 2) := by
        rw [hmod]
        exact mul_le_mul_of_nonneg_right hcondPow
          (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = Real.rpow (Ideal.absNorm f : ℝ)
          ((1 / 2 + ε / 2) + ε / 2) :=
            (Real.rpow_add hnormf (1 / 2 + ε / 2) (ε / 2)).symm
      _ = Real.rpow (Ideal.absNorm f : ℝ) (1 / 2 + ε) := by congr 1 <;> ring
  have hheight1 (s : ℂ) : 1 ≤ 2 + |s.im| := by nlinarith [abs_nonneg s.im]
  have hheightH (s : ℂ) :
      Real.rpow (2 + |s.im|) A_H ≤ Real.rpow (2 + |s.im|) A_F :=
    Real.rpow_le_rpow_of_exponent_le (hheight1 s) hA_Hle
  have hheightZ (s : ℂ) :
      Real.rpow (2 + |s.im|) A_Z ≤ Real.rpow (2 + |s.im|) A_F :=
    Real.rpow_le_rpow_of_exponent_le (hheight1 s) hA_Zle
  refine ⟨?_, ?_⟩
  · intro s hs₀ hs₄
    have hray := hRay m ψ hψ Λ hΛ.1 hAgreeRay s hs₀ hs₄
    have hLraw : ‖Λ s‖ ≤
        C_H * Real.rpow (ArtinPrimitiveRoots.Hecke.conductorNorm ψ : ℝ) (1 / 2 + ε / 2) *
          Real.rpow (ArtinPrimitiveRoots.Hecke.modulusNorm m : ℝ) (ε / 2) *
            Real.rpow (2 + |s.im|) A_H := hray
    have hLcond : ‖Λ s‖ ≤
        C_H * Real.rpow (Ideal.absNorm f : ℝ) (1 / 2 + ε) *
          Real.rpow (2 + |s.im|) A_H := by
      calc
        ‖Λ s‖ ≤
            C_H * Real.rpow (ArtinPrimitiveRoots.Hecke.conductorNorm ψ : ℝ)
                (1 / 2 + ε / 2) *
              Real.rpow (ArtinPrimitiveRoots.Hecke.modulusNorm m : ℝ) (ε / 2) *
                Real.rpow (2 + |s.im|) A_H := hLraw
        _ = C_H * (Real.rpow (ArtinPrimitiveRoots.Hecke.conductorNorm ψ : ℝ)
              (1 / 2 + ε / 2) *
            Real.rpow (ArtinPrimitiveRoots.Hecke.modulusNorm m : ℝ) (ε / 2)) *
              Real.rpow (2 + |s.im|) A_H := by ring
        _ ≤ C_H * Real.rpow (Ideal.absNorm f : ℝ) (1 / 2 + ε) *
              Real.rpow (2 + |s.im|) A_H := by
            have hheightNonneg : 0 ≤ (2 + |s.im| : ℝ) := by linarith [hheight1 s]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hbase (le_of_lt hC_H))
              (Real.rpow_nonneg hheightNonneg _)
    have hLAF : ‖Λ s‖ ≤
        C_H * Real.rpow (Ideal.absNorm f : ℝ) (1 / 2 + ε) *
          Real.rpow (2 + |s.im|) A_F := by
      have hcoefNonneg : 0 ≤ C_H * Real.rpow (Ideal.absNorm f : ℝ) (1 / 2 + ε) :=
        mul_nonneg (le_of_lt hC_H) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      exact hLcond.trans (mul_le_mul_of_nonneg_left (hheightH s) hcoefNonneg)
    have hLfinal : ‖Λ s‖ ≤
        C * Real.rpow (Ideal.absNorm f : ℝ) (1 / 2 + ε) *
          Real.rpow (2 + |s.im|) A_F := by
      have hnormPowNonneg : 0 ≤ Real.rpow (Ideal.absNorm f : ℝ) (1 / 2 + ε) :=
        Real.rpow_nonneg (Nat.cast_nonneg _) _
      have hheightNonneg : 0 ≤ Real.rpow (2 + |s.im|) A_F :=
        Real.rpow_nonneg (by linarith [hheight1 s]) _
      exact hLAF.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC_Hle
          hnormPowNonneg)
        hheightNonneg)
    exact hLfinal
  · intro s hs₀ hs₄
    have hZ := hZeta s hs₀ hs₄
    have hZfinal :
        ‖(s - 1) * NumberField.dedekindZeta F s‖ ≤
          C * Real.rpow (2 + |s.im|) A_F := by
      calc
        ‖(s - 1) * NumberField.dedekindZeta F s‖ ≤
            C_Z * Real.rpow (2 + |s.im|) A_Z := hZ
        _ ≤ C_Z * Real.rpow (2 + |s.im|) A_F :=
          mul_le_mul_of_nonneg_left (hheightZ s) (le_of_lt hC_Z)
        _ ≤ C * Real.rpow (2 + |s.im|) A_F :=
          mul_le_mul_of_nonneg_right hC_Zle
            (Real.rpow_nonneg (by linarith [hheight1 s]) _)
    exact hZfinal


end ArtinPrimitiveRoots.Proofs.A2FreqP

end
