import ArtinPrimitiveRoots.Splitting.Proofs.S7_EULER.Defs

set_option autoImplicit false
open scoped NumberField BigOperators
open NumberField IsDedekindDomain
noncomputable section
namespace ArtinPrimitiveRoots.Splitting
open ClassFieldTheory ArtinPrimitiveRoots.Hecke

/-- Finite deleted-prime corrections are analytic and nonzero on `Re s > 0`.
Uses positive prime norms and complex
powers; feeds `upstairs_rhp_euler_identity` and `quotient_factor_of_euler_identity`. -/
theorem finite_euler_correction_analytic (T : Type*) [Field T] [NumberField T]
    (S : Finset (HeightOneSpectrum (𝓞 T))) :
    AnalyticOn ℂ (fun s : ℂ =>
      ∏ w ∈ S, (1 - (Ideal.absNorm w.asIdeal : ℂ) ^ (-s))⁻¹)
      {s : ℂ | 0 < s.re} ∧
    (∀ s : ℂ, 0 < s.re →
      (∏ w ∈ S, (1 - (Ideal.absNorm w.asIdeal : ℂ) ^ (-s))⁻¹) ≠ 0) := by
  classical
  let D : Set ℂ := {s : ℂ | 0 < s.re}
  letI : NormedAddCommGroup ℂ := Complex.instNormedAddCommGroup
  letI : NormedAlgebra ℂ ℂ :=
    (inferInstance : CommCStarAlgebra ℂ).toCStarAlgebra.toNormedAlgebra
  letI : NormedSpace ℂ ℂ :=
    (CommCStarAlgebra.toNonUnitalCommCStarAlgebra ℂ).toNonUnitalCStarAlgebra.toNormedSpace
  have hnorm_lt (w : HeightOneSpectrum (𝓞 T)) {s : ℂ} (hs : 0 < s.re) :
      ‖(Ideal.absNorm w.asIdeal : ℂ) ^ (-s)‖ < 1 := by
    have hN := NumberField.HeightOneSpectrum.one_lt_absNorm w
    have hNpos : 0 < Ideal.absNorm w.asIdeal := lt_trans zero_lt_one hN
    rw [Complex.norm_natCast_cpow_of_pos hNpos]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hN) (by
      simpa using (neg_lt_zero.mpr hs))
  have hden_ne (w : HeightOneSpectrum (𝓞 T)) {s : ℂ} (hs : 0 < s.re) :
      1 - (Ideal.absNorm w.asIdeal : ℂ) ^ (-s) ≠ 0 := by
    intro h
    have hpow : (Ideal.absNorm w.asIdeal : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
    have hnorm : ‖(Ideal.absNorm w.asIdeal : ℂ) ^ (-s)‖ = 1 := by rw [hpow]; norm_num
    exact (ne_of_lt (hnorm_lt w hs)) hnorm
  have hfactorAnalytic (w : HeightOneSpectrum (𝓞 T)) :
      AnalyticOn ℂ (fun s : ℂ =>
        (1 - (Ideal.absNorm w.asIdeal : ℂ) ^ (-s))⁻¹) D := by
    let N : ℕ := Ideal.absNorm w.asIdeal
    have hN : 1 < N := by
      simpa [N] using NumberField.HeightOneSpectrum.one_lt_absNorm w
    have hNpos : 0 < N := Nat.zero_lt_of_lt hN
    have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
    have hbase : (N : ℂ) ∈ Complex.slitPlane := by
      simpa using (Complex.ofReal_mem_slitPlane.mpr hNreal)
    have hbaseAnalytic : AnalyticOn ℂ (fun _ : ℂ => (N : ℂ)) D := analyticOn_const
    have hexpAnalytic : AnalyticOn ℂ (fun s : ℂ => -s) D := by
      have hneg : -(fun s : ℂ => s) = (fun s => -s) := by funext s; rfl
      rw [← hneg]
      exact analyticOn_id.neg
    have hpowAnalytic : AnalyticOn ℂ (fun s : ℂ => (N : ℂ) ^ (-s)) D :=
      hbaseAnalytic.cpow hexpAnalytic (fun _ _ => hbase)
    have honeAnalytic : AnalyticOn ℂ (fun _ : ℂ => (1 : ℂ)) D := analyticOn_const
    have hdenAnalytic : AnalyticOn ℂ (fun s : ℂ => 1 - (N : ℂ) ^ (-s)) D := by
      have hsub : (fun s : ℂ => (1 : ℂ)) - (fun s : ℂ => (N : ℂ) ^ (-s)) =
          (fun s : ℂ => 1 - (N : ℂ) ^ (-s)) := by funext s; rfl
      rw [← hsub]
      exact honeAnalytic.sub hpowAnalytic
    have hdenNonzero : ∀ s ∈ D, 1 - (N : ℂ) ^ (-s) ≠ 0 := by
      intro s hs
      have hs' : 0 < s.re := hs
      have hw := hden_ne w hs'
      simpa [N] using hw
    have hinvFun : (fun s : ℂ => (1 - (N : ℂ) ^ (-s))⁻¹) =
        (fun s : ℂ => 1 - (N : ℂ) ^ (-s))⁻¹ := by funext s; rfl
    rw [hinvFun]
    simpa [N] using hdenAnalytic.inv hdenNonzero
  have hprodAnalytic :
      AnalyticOn ℂ (fun s : ℂ =>
        ∏ w ∈ S, (1 - (Ideal.absNorm w.asIdeal : ℂ) ^ (-s))⁻¹) D := by
    exact Finset.analyticOn_fun_prod S (fun w hw => hfactorAnalytic w)
  refine ⟨?_, ?_⟩
  · simpa [D] using hprodAnalytic
  · intro s hs
    apply Finset.prod_ne_zero_iff.mpr
    intro w hw
    exact inv_ne_zero (hden_ne w hs)

end ArtinPrimitiveRoots.Splitting
end
