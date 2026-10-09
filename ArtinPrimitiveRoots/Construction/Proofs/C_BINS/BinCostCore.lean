import ArtinPrimitiveRoots.Construction.Proofs.C_BINS.BinTypeIIError
import ArtinPrimitiveRoots.Construction.Proofs.C_BINS.DivisorConvolution
import ArtinPrimitiveRoots.Construction.Proofs.c1.SieveProductHelpers

namespace ArtinPrimitiveRoots.Proofs.c_bins_sol

open Classical ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.Rough
open ArtinPrimitiveRoots.Construction ArtinPrimitiveRoots.Construction.Proofs.C_BINS

/-- The bin cost from the common Type II bound and the natural divisor-bin estimate. -/
theorem bin_cost_of_estimates
    (M c K : ℕ) (u : ℤ) (a : Fin K → ℝ) (Ψ : ℝ → ℝ)
    (b κ γ γ' : ℝ) (hM : 0 < M) (hc24 : c = 2 ∨ c = 4)
    (hu : Int.gcd u M = 1) (ha : ValidBands K a)
    (hΨ : IsTestFunction Ψ) (hb : 0 < b) (hκ : 0 < κ)
    (hκsmall : κ < 1 / 100) (hγlo : b ≤ γ)
    (hγγ' : γ < γ') (hγhi : γ' ≤ 1 / 2 - κ)
    (htw : ArtinPrimitiveRoots.Proofs.c_typeii_sol.TwistedEstimate
      (b / 2) γ (1 / 2 + κ / 2) (1 - b / 2) (1 / 4) 2 M K a)
    (c₀ xMass xSupport xJ : ℝ) (hc₀ : 0 < c₀)
    (hMass : ∀ x : ℝ, xMass ≤ x →
      c₀ * x * groupHarmonicMass x K a / Real.log x ≤
        conTotalMass x M c u K a Ψ)
    (hSupport : ∀ x : ℝ, xSupport ≤ x → ∀ d,
      (conWeight x M c u K a Ψ d ≠ 0 →
        x < (d : ℝ) ∧ (d : ℝ) < 2 * x) ∧
      0 ≤ conWeight x M c u K a Ψ d)
    (hJ : ∀ x : ℝ, xJ ≤ x → 1 ≤ groupHarmonicMass x K a)
    (hBin : ∀ ρ : ℝ, 0 < ρ → ∃ x₀ : ℝ, 2 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        |primeDivisorBinSum x M c u K a Ψ γ γ' -
          (singularProduct M * conTotalMass x M c u K a Ψ *
            roughSieveProduct (roughCutoff x) * Real.log (γ' / γ))| ≤
          ρ * singularProduct M * conTotalMass x M c u K a Ψ *
            roughSieveProduct (roughCutoff x)) :
    ∀ η : ℝ, 0 < η → ∃ C x₀ : ℝ, 0 < C ∧ 2 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        (∑ q ∈ (primesUpTo (Real.rpow x γ')).filter
            (fun q : ℕ => Real.rpow x γ < (q : ℝ)),
          ∑ m ∈ Finset.range (⌊2 * x⌋₊ + 1),
            if roughAbove m (Real.rpow x γ) then
              conWeight x M c u K a Ψ (m * q) else 0) ≤
          (singularProduct M * conTotalMass x M c u K a Ψ / Real.log x) *
            (sSup ((fun t : ℝ => roughDensity γ (1 - t)) '' Set.Icc γ γ') *
              Real.log (γ' / γ) + η) := by
  classical
  have hγ : 0 < γ := hb.trans_le hγlo
  have hγs : γ < 1 / 2 + κ / 2 := by linarith
  have hs : 1 / 2 + κ / 2 ≤ 1 - b / 2 := by linarith
  obtain ⟨Cd, hCd, hDensity⟩ := density_regularity.2.1 γ
    (1 / 2 + κ / 2) (1 - b / 2) hγ hγs hs
  let D : ℝ := sSup ((fun t : ℝ => roughDensity γ (1 - t)) '' Set.Icc γ γ')
  let Q : ℝ := Real.log (γ' / γ)
  let S : ℝ := singularProduct M
  have hS : 0 < S := singularProduct_pos M
  have hQ : 0 < Q := by
    apply Real.log_pos
    exact (lt_div_iff₀ hγ).mpr (by simpa only [one_mul] using hγγ')
  have hD : 0 ≤ D := roughDensityBinSup_nonneg γ γ' hγ hγγ'.le (by linarith)
  have hVWindow (t : ℝ) (ht : t ∈ Set.Icc γ γ') :
      1 / 2 + κ / 2 ≤ 1 - t ∧ 1 - t ≤ 1 - b / 2 := by
    constructor <;> linarith [ht.1, ht.2]
  have hImageBdd : BddAbove ((fun t : ℝ => roughDensity γ (1 - t)) '' Set.Icc γ γ') := by
    refine ⟨roughDensity γ (1 / 2 + κ / 2) + Cd * ((1 - b / 2) - (1 / 2 + κ / 2)), ?_⟩
    rintro y ⟨t, ht, rfl⟩
    have hv := hVWindow t ht
    have hLip := hDensity (1 - t) (1 / 2 + κ / 2) hv.1 hv.2 le_rfl hs
    rw [abs_of_nonneg (sub_nonneg.mpr hv.1)] at hLip
    have hVal : roughDensity γ (1 - t) ≤ roughDensity γ (1 / 2 + κ / 2) +
        |roughDensity γ (1 - t) - roughDensity γ (1 / 2 + κ / 2)| := by
      linarith [le_abs_self (roughDensity γ (1 - t) - roughDensity γ (1 / 2 + κ / 2))]
    exact hVal.trans (add_le_add le_rfl
      (hLip.trans (mul_le_mul_of_nonneg_left (sub_le_sub_right hv.2 _) hCd.le)))
  obtain ⟨Cerr, xErr, hCerr, hxErr₂, hErr⟩ :=
    bin_type_ii_error M c K u a Ψ b κ γ γ' hM hc24 hu ha hΨ hb hκ hκsmall
      hγlo hγγ' hγhi htw xSupport (fun x hx d => (hSupport x hx d).1)
  obtain ⟨xLarge, hxLarge₂, hLarge⟩ := large_prime_coprime_group M K a b hM ha hb
  intro η hη
  let ρ : ℝ := min 1 ((η / 4) / (D + 1))
  have hρ : 0 < ρ := lt_min (by norm_num) (div_pos (by positivity) (by linarith))
  have hρone : ρ ≤ 1 := min_le_left _ _
  have hρD : D * ρ ≤ η / 4 := by
    have h := (le_div_iff₀ (by linarith : 0 < D + 1)).mp (min_le_right 1 ((η / 4) / (D + 1)))
    nlinarith only [h, hρ.le]
  obtain ⟨xBin, hxBin₂, hBinEstimate⟩ := hBin ρ hρ
  have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let Lreq : ℝ := max 1 (max (2 * Real.log 2 / b)
    (max (4 * Cd * Real.log 2 * (Q + 1) / η) (2 * Cerr / (η * S * c₀))))
  let x₀ : ℝ := max 2 (max xErr (max xLarge
    (max xMass (max xSupport (max xJ (max xBin (Real.exp Lreq)))))))
  refine ⟨1, x₀, by norm_num, le_max_left _ _, ?_⟩
  intro x hx
  have hAll : 2 ≤ x ∧ xErr ≤ x ∧ xLarge ≤ x ∧ xMass ≤ x ∧ xSupport ≤ x ∧
      xJ ≤ x ∧ xBin ≤ x ∧ Real.exp Lreq ≤ x := by
    simpa only [x₀, max_le_iff] using hx
  rcases hAll with ⟨hx₂, hxErr, hxLarge, hxMass, hxSupport, hxJ, hxBin, hxExp⟩
  have hxpos : 0 < x := by linarith
  have hxone : 1 ≤ x := by linarith
  let L : ℝ := Real.log x
  let V : ℝ := roughSieveProduct (roughCutoff x)
  let Mass : ℝ := conTotalMass x M c u K a Ψ
  let Scale : ℝ := S * Mass / L
  let w : ℕ → ℝ := conWeight x M c u K a Ψ
  let Bin : Finset ℕ := (primesUpTo (Real.rpow x γ')).filter
    (fun q : ℕ => Real.rpow x γ < (q : ℝ))
  let R : Finset ℕ := Finset.range (⌊2 * x⌋₊ + 1)
  let T : ℝ := ∑ q ∈ Bin, ∑ m ∈ R,
    if roughAbove m (Real.rpow x γ) then w (m * q) else 0
  let P : ℝ := ∑ q ∈ Bin, ∑ m ∈ R, roughProxy x γ m * w (m * q)
  let small : ℝ := Cd * Real.log 2 / L
  have hLreq : Lreq ≤ L := by
    simpa only [L, Real.log_exp] using Real.log_le_log (Real.exp_pos _) hxExp
  have hLone : 1 ≤ L := (le_max_left _ _).trans hLreq
  have hLpos : 0 < L := by linarith
  have hbThreshold : 2 * Real.log 2 ≤ b * L := by
    have h := (le_max_left _ _).trans ((le_max_right _ _).trans hLreq)
    have h' := (div_le_iff₀ hb).mp h
    simpa only [mul_comm] using h'
  have hCdThreshold : 4 * Cd * Real.log 2 * (Q + 1) ≤ η * L := by
    have h := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hLreq))
    have h' := (div_le_iff₀ hη).mp h
    simpa only [mul_comm] using h'
  have hErrThreshold : 2 * Cerr ≤ (η * S * c₀) * L := by
    have h := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hLreq))
    have h' := (div_le_iff₀ (by positivity : 0 < η * S * c₀)).mp h
    simpa only [mul_comm] using h'
  have hVpos : 0 < V := by
    unfold V roughSieveProduct
    apply Finset.prod_pos
    intro p hp
    have hpP : p.Prime := (Finset.mem_filter.mp hp).2
    have hp₂ : (2 : ℝ) ≤ p := by exact_mod_cast hpP.two_le
    exact sub_pos.mpr ((div_lt_one₀ (by linarith : 0 < (p : ℝ))).mpr (by linarith))
  have hOneMass : c₀ * x / L ≤ Mass := by
    calc
      _ = c₀ * x * 1 / L := by rw [mul_one]
      _ ≤ c₀ * x * groupHarmonicMass x K a / L :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hJ x hxJ) (by positivity)) hLpos.le
      _ ≤ _ := hMass x hxMass
  have hMasspos : 0 < Mass := (div_pos (mul_pos hc₀ hxpos) hLpos).trans_le hOneMass
  have hScale : 0 ≤ Scale := by dsimp only [Scale]; positivity
  have hScaleLower : S * c₀ * x / L ^ 2 ≤ Scale := by
    calc
      _ = S * (c₀ * x / L) / L := by field_simp [ne_of_gt hLpos] <;> ring
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hOneMass hS.le) hLpos.le
  have hSmall : 0 ≤ small := by dsimp only [small]; positivity
  have hSmallLoss : small * (Q + 1) ≤ η / 4 := by
    dsimp only [small]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hLpos).mpr
    nlinarith only [hCdThreshold]
  have hLossBase : 2 * Cerr ≤ (η * S * c₀) * L ^ 3 := by
    have hLsq : 1 ≤ L ^ 2 := one_le_pow₀ hLone
    have hLcube : L ≤ L ^ 3 := by
      have h := mul_le_mul_of_nonneg_right hLsq hLpos.le
      nlinarith only [h]
    exact hErrThreshold.trans (mul_le_mul_of_nonneg_left hLcube (by positivity))
  have hRatio : Cerr / L ^ 3 ≤ η * S * c₀ / 2 := by
    apply (div_le_iff₀ (pow_pos hLpos 3)).mpr
    nlinarith only [hLossBase]
  have hNegPower : Real.rpow L (-5 : ℝ) = (L ^ 5)⁻¹ := by
    calc
      _ = (Real.rpow L (5 : ℝ))⁻¹ := Real.rpow_neg hLpos.le 5
      _ = (L ^ 5)⁻¹ := congrArg (fun t : ℝ => t⁻¹) (Real.rpow_natCast L 5)
  have hErrorScale : Cerr * x * Real.rpow L (-5 : ℝ) ≤ (η / 2) * Scale := by
    calc
      _ = (Cerr / L ^ 3) * (x / L ^ 2) := by
        rw [hNegPower]
        field_simp [ne_of_gt hLpos] <;> ring
      _ ≤ (η * S * c₀ / 2) * (x / L ^ 2) := mul_le_mul_of_nonneg_right hRatio (by positivity)
      _ = (η / 2) * (S * c₀ * x / L ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hScaleLower (by positivity)
  have hBinFacts (q : ℕ) (hq : q ∈ Bin) :
      q.Prime ∧ Real.rpow x γ < (q : ℝ) ∧ (q : ℝ) ≤ Real.rpow x γ' := by
    rcases Finset.mem_filter.mp hq with ⟨hqPrime, hqlo⟩
    have hP : q.Prime := (Finset.mem_filter.mp hqPrime).2
    have hqRange := (Finset.mem_filter.mp hqPrime).1
    have hqFloor : q ≤ ⌊Real.rpow x γ'⌋₊ :=
      Nat.lt_succ_iff.mp (Finset.mem_range.mp hqRange)
    refine ⟨hP, hqlo, ?_⟩
    exact (Nat.cast_le.mpr hqFloor).trans (Nat.floor_le (Real.rpow_nonneg hxpos.le _))
  have hPrimeRough (q : ℕ) (hq : q ∈ Bin) : roughAbove q (roughCutoff x) := by
    obtain ⟨hqP, hqlo, hqhi⟩ := hBinFacts q hq
    have hqb : Real.rpow x b < (q : ℝ) :=
      (Real.rpow_le_rpow_of_exponent_le hxone hγlo).trans_lt hqlo
    have hWq := (hLarge x hxLarge q hqP hqb).1
    intro p hp hpdvd
    have hpq : p = q := ((Nat.dvd_prime hqP).mp hpdvd).resolve_left hp.ne_one
    simpa only [hpq] using hWq
  have hDensityBound (q m : ℕ) (hq : q ∈ Bin) (hw : w (m * q) ≠ 0) :
      roughDensity γ (Real.log (m : ℝ) / L) ≤ D + small := by
    obtain ⟨hqP, hqlo, hqhi⟩ := hBinFacts q hq
    have hqpos : 0 < (q : ℝ) := by exact_mod_cast hqP.pos
    have hprod : x < (m : ℝ) * (q : ℝ) ∧ (m : ℝ) * (q : ℝ) < 2 * x := by
      simpa only [Nat.cast_mul] using (hSupport x hxSupport (m * q)).1 hw
    have hmpos : 0 < (m : ℝ) := by
      by_contra hbad
      have hmzero : (m : ℝ) = 0 := le_antisymm (not_lt.mp hbad) (Nat.cast_nonneg m)
      rw [hmzero, zero_mul] at hprod
      linarith only [hprod.1, hxpos]
    have hLogQlo : γ * L < Real.log (q : ℝ) := by
      simpa only [Real.log_rpow hxpos, L] using
        Real.log_lt_log (Real.rpow_pos_of_pos hxpos _) hqlo
    have hLogQhi : Real.log (q : ℝ) ≤ γ' * L := by
      calc
        _ ≤ Real.log (Real.rpow x γ') := Real.log_le_log hqpos hqhi
        _ = γ' * L := Real.log_rpow hxpos γ'
    have hLogProdLo : L < Real.log (m : ℝ) + Real.log (q : ℝ) := by
      simpa only [Real.log_mul (ne_of_gt hmpos) (ne_of_gt hqpos), L] using
        Real.log_lt_log hxpos hprod.1
    have hLogProdHi : Real.log (m : ℝ) + Real.log (q : ℝ) < Real.log 2 + L := by
      simpa only [Real.log_mul (ne_of_gt hmpos) (ne_of_gt hqpos),
        Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hxpos), L] using
        Real.log_lt_log (mul_pos hmpos hqpos) hprod.2
    let t : ℝ := Real.log (q : ℝ) / L
    let v : ℝ := 1 - t
    let vM : ℝ := Real.log (m : ℝ) / L
    have ht : t ∈ Set.Icc γ γ' :=
      ⟨(le_div_iff₀ hLpos).mpr hLogQlo.le, (div_le_iff₀ hLpos).mpr hLogQhi⟩
    have hv := hVWindow t ht
    have hVLeft : (1 / 2 + κ / 2) * L ≤ (1 - γ') * L :=
      mul_le_mul_of_nonneg_right (by linarith) hLpos.le
    have hMlo : 1 / 2 + κ / 2 ≤ vM := by
      apply (le_div_iff₀ hLpos).mpr
      linarith only [hLogProdLo, hLogQhi, hVLeft]
    have hMhi : vM ≤ 1 - b / 2 := by
      apply (div_le_iff₀ hLpos).mpr
      have hγL := mul_le_mul_of_nonneg_right hγlo hLpos.le
      linarith only [hLogProdHi, hLogQlo, hγL, hbThreshold]
    have hGapEq : vM - v = (Real.log (m : ℝ) + Real.log (q : ℝ) - L) / L := by
      dsimp only [vM, v, t]
      field_simp [ne_of_gt hLpos] <;> ring
    have hGap₀ : 0 ≤ vM - v := by
      rw [hGapEq]
      exact div_nonneg (by linarith only [hLogProdLo]) hLpos.le
    have hGap : vM - v ≤ Real.log 2 / L := by
      rw [hGapEq]
      exact div_le_div_of_nonneg_right (by linarith only [hLogProdHi]) hLpos.le
    have hLip := hDensity vM v hMlo hMhi hv.1 hv.2
    have hDifference : |roughDensity γ vM - roughDensity γ v| ≤ Cd * (Real.log 2 / L) := by
      rw [abs_of_nonneg hGap₀] at hLip
      exact hLip.trans (mul_le_mul_of_nonneg_left hGap hCd.le)
    have hSup : roughDensity γ v ≤ D :=
      le_csSup hImageBdd ⟨t, ht, rfl⟩
    calc
      _ ≤ roughDensity γ v + |roughDensity γ vM - roughDensity γ v| := by
        linarith [le_abs_self (roughDensity γ vM - roughDensity γ v)]
      _ ≤ D + Cd * (Real.log 2 / L) := add_le_add hSup hDifference
      _ = _ := by simp only [small, mul_div_assoc]
  have hTerm (q m : ℕ) (hq : q ∈ Bin) :
      roughProxy x γ m * w (m * q) ≤
        (D + small) / (L * V) *
          (if roughAbove m (roughCutoff x) then w (m * q) else 0) := by
    by_cases hwZero : w (m * q) = 0
    · simp only [hwZero, ite_self, mul_zero, le_refl]
    · by_cases hr : roughAbove m (roughCutoff x)
      · simp only [roughProxy, if_pos hr, mul_one]
        exact mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (hDensityBound q m hq hwZero) (by positivity))
          (hSupport x hxSupport (m * q)).2
      · simp only [roughProxy, if_neg hr, mul_zero, zero_mul, le_refl]
  have hConv : (∑ q ∈ Bin, ∑ m ∈ R,
      if roughAbove m (roughCutoff x) then w (m * q) else 0) =
      primeDivisorBinSum x M c u K a Ψ γ γ' := by
    change _ = ∑ q ∈ Bin, ∑ d ∈ R,
      if q ∣ d ∧ roughAbove d (roughCutoff x) then w d else 0
    apply Finset.sum_congr rfl
    intro q hq
    exact rough_divisor_convolution x (roughCutoff x) q w hxpos (hBinFacts q hq).1.pos
      (hPrimeRough q hq) (fun d hd => ((hSupport x hxSupport d).1 hd).2)
  have hBinUpper : primeDivisorBinSum x M c u K a Ψ γ γ' ≤ S * Mass * V * (Q + ρ) := by
    have h := hBinEstimate x hxBin
    calc
      _ = (primeDivisorBinSum x M c u K a Ψ γ γ' - S * Mass * V * Q) + S * Mass * V * Q := by ring
      _ ≤ |primeDivisorBinSum x M c u K a Ψ γ γ' - S * Mass * V * Q| + S * Mass * V * Q :=
        add_le_add (le_abs_self _) le_rfl
      _ ≤ ρ * S * Mass * V + S * Mass * V * Q := add_le_add h le_rfl
      _ = _ := by ring
  have hProxy : P ≤ Scale * ((D + small) * (Q + ρ)) := by
    have hCoef : 0 ≤ (D + small) / (L * V) := by positivity
    calc
      _ ≤ ∑ q ∈ Bin, ∑ m ∈ R, (D + small) / (L * V) *
          (if roughAbove m (roughCutoff x) then w (m * q) else 0) :=
        Finset.sum_le_sum (fun q hq => Finset.sum_le_sum (fun m hm => hTerm q m hq))
      _ = (D + small) / (L * V) * (∑ q ∈ Bin, ∑ m ∈ R,
          if roughAbove m (roughCutoff x) then w (m * q) else 0) := by
        simp_rw [Finset.mul_sum]
      _ = (D + small) / (L * V) * primeDivisorBinSum x M c u K a Ψ γ γ' := by rw [hConv]
      _ ≤ (D + small) / (L * V) * (S * Mass * V * (Q + ρ)) :=
        mul_le_mul_of_nonneg_left hBinUpper hCoef
      _ = _ := by
        dsimp only [Scale]
        field_simp [ne_of_gt hLpos, ne_of_gt hVpos] <;> ring
  have hScalar : (D + small) * (Q + ρ) ≤ D * Q + η / 2 := by
    have hSmallRho : small * (Q + ρ) ≤ η / 4 :=
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl hρone) hSmall).trans hSmallLoss
    calc
      _ = D * Q + D * ρ + small * (Q + ρ) := by ring
      _ ≤ D * Q + η / 4 + η / 4 :=
        add_le_add (add_le_add le_rfl hρD) hSmallRho
      _ = _ := by ring
  have hError : |T - P| ≤ Cerr * x * Real.rpow L (-5 : ℝ) := by
    have h := hErr x hxErr
    simpa only [sub_mul, Finset.sum_sub_distrib, roughIndicator, ite_mul, one_mul, zero_mul] using h
  change T ≤ Scale * (D * Q + η)
  calc
    _ ≤ P + Cerr * x * Real.rpow L (-5 : ℝ) := by
      linarith only [le_abs_self (T - P), hError]
    _ ≤ Scale * ((D + small) * (Q + ρ)) + (η / 2) * Scale := add_le_add hProxy hErrorScale
    _ ≤ Scale * (D * Q + η / 2) + (η / 2) * Scale :=
      add_le_add (mul_le_mul_of_nonneg_left hScalar hScale) le_rfl
    _ = _ := by ring

end ArtinPrimitiveRoots.Proofs.c_bins_sol
