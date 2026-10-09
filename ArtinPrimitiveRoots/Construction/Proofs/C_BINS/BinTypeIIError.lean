import ArtinPrimitiveRoots.Construction.Proofs.C_BINS.UniformTypeII
import ArtinPrimitiveRoots.Construction.Proofs.C_BINS.TwoCofactorBoxes
import ArtinPrimitiveRoots.Construction.Proofs.C_BINS.LargePrime
import Mathlib.Data.Nat.Log

namespace ArtinPrimitiveRoots.Proofs.c_bins_sol

open Classical ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.Rough
open ArtinPrimitiveRoots.Construction

/-- The Type II error summed over a natural prime-divisor bin. -/
theorem bin_type_ii_error
    (M c K : ℕ) (u : ℤ) (a : Fin K → ℝ) (Ψ : ℝ → ℝ)
    (b κ γ γ' : ℝ) (hM : 0 < M) (hc24 : c = 2 ∨ c = 4)
    (hu : Int.gcd u M = 1) (ha : ValidBands K a)
    (hΨ : IsTestFunction Ψ) (hb : 0 < b) (hκ : 0 < κ)
    (hκsmall : κ < 1 / 100) (hγlo : b ≤ γ)
    (hγγ' : γ < γ') (hγhi : γ' ≤ 1 / 2 - κ)
    (htw : ArtinPrimitiveRoots.Proofs.c_typeii_sol.TwistedEstimate
      (b / 2) γ (1 / 2 + κ / 2) (1 - b / 2) (1 / 4) 2 M K a)
    (xSupport : ℝ)
    (hSupport : ∀ x : ℝ, xSupport ≤ x → ∀ d,
      conWeight x M c u K a Ψ d ≠ 0 →
        x < (d : ℝ) ∧ (d : ℝ) < 2 * x) :
    ∃ C x₀ : ℝ, 0 < C ∧ 2 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        |(∑ q ∈ (primesUpTo (Real.rpow x γ')).filter
            (fun q : ℕ => Real.rpow x γ < (q : ℝ)),
          ∑ m ∈ Finset.range (⌊2 * x⌋₊ + 1),
            (roughIndicator x γ m - roughProxy x γ m) *
              conWeight x M c u K a Ψ (m * q))| ≤
          C * x * Real.rpow (Real.log x) (-5 : ℝ) := by
  classical
  have hγ : 0 < γ := hb.trans_le hγlo
  have hγs : γ < 1 / 2 + κ / 2 := by linarith
  have hs : 1 / 2 + κ / 2 < 1 - b / 2 := by linarith
  have hsMax : 1 - b / 2 < 1 := by linarith
  obtain ⟨Ctype, xtype, hCtype, hxtype, hType⟩ :=
    ArtinPrimitiveRoots.Proofs.c_typeii_sol.fourier_progression
      (b / 2) γ (1 / 2 + κ / 2) (1 - b / 2) (1 / 4) 2
      (by positivity) hγ hγs hs hsMax M c K u a ha hM hc24 hu
      Ψ hΨ.2.2.1 hΨ.2.2.2.1 hΨ.2.1 hΨ.1 htw
  obtain ⟨xLarge, hxLarge₂, hLarge⟩ := large_prime_coprime_group M K a b hM ha hb
  have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog₃ : 0 < Real.log 3 := Real.log_pos (by norm_num)
  let Cindex : ℝ := (1 + Real.log 3) / Real.log 2 + 1
  have hCindex : 0 < Cindex := by dsimp [Cindex]; positivity
  let Lreq : ℝ := max 1 (max (4 * Real.log 2 / b) (4 * Real.log 2 / κ))
  let C : ℝ := 2 * Ctype * Cindex
  let x₀ : ℝ := max xtype (max xSupport (max xLarge (Real.exp Lreq)))
  refine ⟨C, x₀, by dsimp [C]; positivity,
    hxtype.trans (le_max_left _ _), ?_⟩
  intro x hx
  have hxType : xtype ≤ x := (le_max_left _ _).trans hx
  have hxSupport : xSupport ≤ x :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hxLarge : xLarge ≤ x :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hx))
  have hxExp : Real.exp Lreq ≤ x :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hx))
  have hx₂ : 2 ≤ x := hxtype.trans hxType
  have hxpos : 0 < x := by linarith
  have hxone : 1 ≤ x := by linarith
  let L : ℝ := Real.log x
  have hLreq : Lreq ≤ L := by
    simpa only [L, Real.log_exp] using Real.log_le_log (Real.exp_pos _) hxExp
  have hLone : 1 ≤ L := (le_max_left _ _).trans hLreq
  have hLpos : 0 < L := by linarith
  have hbL : 4 * Real.log 2 ≤ b * L := by
    have h := (le_max_left _ _).trans ((le_max_right _ _).trans hLreq)
    have h' := (div_le_iff₀ hb).mp h
    simpa only [mul_comm] using h'
  have hκL : 4 * Real.log 2 ≤ κ * L := by
    have h := (le_max_right _ _).trans ((le_max_right _ _).trans hLreq)
    have h' := (div_le_iff₀ hκ).mp h
    simpa only [mul_comm] using h'
  let Bin : Finset ℕ := (primesUpTo (Real.rpow x γ')).filter
    (fun q : ℕ => Real.rpow x γ < (q : ℝ))
  let Idx : Finset ℕ := Bin.image (Nat.log 2)
  let H : ℕ → ℝ := fun j => (2 : ℝ) ^ j
  let F : ℕ → Finset ℕ := fun j => Bin.filter (fun q => Nat.log 2 q = j)
  let R : Finset ℕ := Finset.range (⌊2 * x⌋₊ + 1)
  let f : ℕ → ℕ → ℂ := fun q m =>
    ((roughIndicator x γ m - roughProxy x γ m : ℝ) : ℂ) *
      (conWeight x M c u K a Ψ (m * q) : ℂ)
  have hBinFacts (q : ℕ) (hq : q ∈ Bin) :
      q.Prime ∧ Real.rpow x γ < (q : ℝ) ∧ (q : ℝ) ≤ Real.rpow x γ' := by
    rcases Finset.mem_filter.mp hq with ⟨hqPrime, hqlo⟩
    have hP : q.Prime := (Finset.mem_filter.mp hqPrime).2
    have hqRange := (Finset.mem_filter.mp hqPrime).1
    have hqFloor : q ≤ ⌊Real.rpow x γ'⌋₊ :=
      Nat.lt_succ_iff.mp (Finset.mem_range.mp hqRange)
    refine ⟨hP, hqlo, ?_⟩
    exact (Nat.cast_le.mpr hqFloor).trans (Nat.floor_le (Real.rpow_nonneg hxpos.le _))
  have hDyad (V : ℝ) (hV : 0 ≤ V) (m : ℕ) :
      m ∈ dyadicIntegers V ↔ V ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * V := by
    unfold dyadicIntegers
    rw [Finset.mem_filter, Finset.mem_range]
    constructor
    · exact fun hm => hm.2
    · intro hm
      exact ⟨Nat.lt_succ_iff.mpr
        ((Nat.le_floor_iff (by positivity : 0 ≤ 2 * V)).mpr hm.2), hm⟩
  have hHone (j : ℕ) : 1 ≤ H j := by
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hHpos (j : ℕ) : 0 < H j := by dsimp [H]; positivity
  have hPrimeDyad (q : ℕ) (hq : q ∈ Bin) :
      H (Nat.log 2 q) ≤ (q : ℝ) ∧ (q : ℝ) < 2 * H (Nat.log 2 q) := by
    have hqP := (hBinFacts q hq).1
    have hlo := Nat.pow_log_le_self 2 hqP.ne_zero
    have hhi := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) q
    constructor
    · change (2 : ℝ) ^ Nat.log 2 q ≤ (q : ℝ)
      exact_mod_cast hlo
    · simpa only [H, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_succ, mul_comm]
        using (Nat.cast_lt.mpr hhi : (q : ℝ) < ((2 ^ (Nat.log 2 q).succ : ℕ) : ℝ))
  have hPrimeRough (q : ℕ) (hq : q ∈ Bin) : roughAbove q (roughCutoff x) := by
    obtain ⟨hqP, hqlo, hqhi⟩ := hBinFacts q hq
    have hqb : Real.rpow x b < (q : ℝ) :=
      (Real.rpow_le_rpow_of_exponent_le hxone hγlo).trans_lt hqlo
    have hWq := (hLarge x hxLarge q hqP hqb).1
    intro p hp hpdvd
    have hpq : p = q := ((Nat.dvd_prime hqP).mp hpdvd).resolve_left hp.ne_one
    simpa only [hpq] using hWq
  have hScale (j : ℕ) (hj : j ∈ Idx) (d : ℝ) (hd : d = 1 ∨ d = 2) :
      Real.rpow x (b / 2) ≤ x / (d * H j) ∧
      Real.rpow x (b / 2) ≤ H j ∧
      (1 / 4 : ℝ) * x ≤ (x / (d * H j)) * H j ∧
      (x / (d * H j)) * H j ≤ 2 * x ∧
      Real.log (x / (d * H j)) / L ∈ Set.Icc (1 / 2 + κ / 2) (1 - b / 2) ∧
      Real.log (2 * (x / (d * H j))) / L ∈
        Set.Icc (1 / 2 + κ / 2) (1 - b / 2) := by
    obtain ⟨q, hq, hqj⟩ := Finset.mem_image.mp hj
    obtain ⟨hqP, hqlo, hqhi⟩ := hBinFacts q hq
    have hqpos : 0 < (q : ℝ) := by exact_mod_cast hqP.pos
    have hqDyad := hPrimeDyad q hq
    rw [hqj] at hqDyad
    have hLogQlo : γ * L < Real.log (q : ℝ) := by
      simpa only [Real.log_rpow hxpos, L] using
        Real.log_lt_log (Real.rpow_pos_of_pos hxpos _) hqlo
    have hLogQhi : Real.log (q : ℝ) ≤ γ' * L := by
      calc
        _ ≤ Real.log (Real.rpow x γ') := Real.log_le_log hqpos hqhi
        _ = γ' * L := Real.log_rpow hxpos γ'
    have hLogHhi : Real.log (H j) ≤ γ' * L :=
      (Real.log_le_log (hHpos j) hqDyad.1).trans hLogQhi
    have hLogHlo : b * L - Real.log 2 < Real.log (H j) := by
      have h := Real.log_lt_log hqpos hqDyad.2
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt (hHpos j))] at h
      have hg := mul_le_mul_of_nonneg_right hγlo hLpos.le
      linarith
    have hdpos : 0 < d := by rcases hd with rfl | rfl <;> norm_num
    have hLogd : 0 ≤ Real.log d ∧ Real.log d ≤ Real.log 2 := by
      rcases hd with rfl | rfl
      · simpa only [Real.log_one] using ⟨le_rfl, hlog₂.le⟩
      · exact ⟨hlog₂.le, le_rfl⟩
    have hmpos : 0 < x / (d * H j) := by positivity
    have hlogM : Real.log (x / (d * H j)) = L - Real.log d - Real.log (H j) := by
      rw [Real.log_div (ne_of_gt hxpos) (ne_of_gt (mul_pos hdpos (hHpos j))),
        Real.log_mul (ne_of_gt hdpos) (ne_of_gt (hHpos j))]
      dsimp only [L]
      ring
    have hlog2M : Real.log (2 * (x / (d * H j))) =
        Real.log 2 + (L - Real.log d - Real.log (H j)) := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hmpos), hlogM]
    have hγ'L : γ' * L ≤ (1 / 2 - κ) * L :=
      mul_le_mul_of_nonneg_right hγhi hLpos.le
    have hWinLower : (1 / 2 + κ / 2) * L ≤ Real.log (x / (d * H j)) := by
      rw [hlogM]
      linarith [hLogd.2]
    have hWinUpper : Real.log (2 * (x / (d * H j))) ≤ (1 - b / 2) * L := by
      rw [hlog2M]
      linarith [hLogd.1]
    have hTwoLog : Real.log (x / (d * H j)) ≤
        Real.log (2 * (x / (d * H j))) := by
      rw [hlogM, hlog2M]
      linarith
    have hMScale : Real.rpow x (b / 2) ≤ x / (d * H j) := by
      apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hxpos _) hmpos).mp
      rw [Real.log_rpow hxpos]
      have hbs : b / 2 ≤ 1 / 2 + κ / 2 := by linarith
      exact (mul_le_mul_of_nonneg_right hbs hLpos.le).trans hWinLower
    have hNScale : Real.rpow x (b / 2) ≤ H j := by
      apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hxpos _) (hHpos j)).mp
      rw [Real.log_rpow hxpos]
      linarith
    have hProd : (x / (d * H j)) * H j = x / d := by
      field_simp [ne_of_gt hdpos, ne_of_gt (hHpos j)]
    refine ⟨hMScale, hNScale, ?_, ?_, ?_, ?_⟩
    · rw [hProd]
      rcases hd with rfl | rfl <;> norm_num <;> linarith
    · rw [hProd]
      rcases hd with rfl | rfl <;> norm_num <;> linarith
    · exact ⟨(le_div_iff₀ hLpos).mpr hWinLower,
        (div_le_iff₀ hLpos).mpr (hTwoLog.trans hWinUpper)⟩
    · exact ⟨(le_div_iff₀ hLpos).mpr (hWinLower.trans hTwoLog),
        (div_le_iff₀ hLpos).mpr hWinUpper⟩
  have hIndexCard : (Idx.card : ℝ) ≤ Cindex * L := by
    let N : ℕ := ⌊2 * x⌋₊ + 1
    let J : ℕ := Nat.log 2 N
    have hNpos : 0 < N := by dsimp [N]; omega
    have hNbound : (N : ℝ) ≤ 3 * x := by
      have hf := Nat.floor_le (by positivity : 0 ≤ 2 * x)
      dsimp only [N]
      push_cast
      linarith
    have hQbound (q : ℕ) (hq : q ∈ Bin) : q ≤ N := by
      have hqhi := (hBinFacts q hq).2.2
      have hγ'one : γ' ≤ 1 := by linarith
      have hpow : Real.rpow x γ' ≤ x := by
        calc
          _ ≤ Real.rpow x 1 := Real.rpow_le_rpow_of_exponent_le hxone hγ'one
          _ = x := Real.rpow_one x
      have hq2 : (q : ℝ) ≤ 2 * x := by linarith [hqhi.trans hpow]
      exact ((Nat.le_floor_iff (by positivity : 0 ≤ 2 * x)).mpr hq2).trans
        (Nat.le_succ _)
    have hSub : Idx ⊆ Finset.range (J + 1) := by
      intro j hj
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hj
      apply Finset.mem_range.mpr
      apply Nat.lt_succ_iff.mpr
      apply Nat.le_log_of_pow_le (by norm_num : 1 < 2)
      exact (Nat.pow_log_le_self 2 (hBinFacts q hq).1.ne_zero).trans (hQbound q hq)
    have hCard : (Idx.card : ℝ) ≤ (J : ℝ) + 1 := by
      have h := Finset.card_le_card hSub
      rw [Finset.card_range] at h
      exact_mod_cast h
    have hPow : (2 : ℝ) ^ J ≤ (N : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 (ne_of_gt hNpos)
    have hLogN : (J : ℝ) * Real.log 2 ≤ Real.log (N : ℝ) := by
      simpa only [Real.log_pow] using
        Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ J) hPow
    have hLogBound : (J : ℝ) * Real.log 2 ≤ L + Real.log 3 := by
      have h := Real.log_le_log (by exact_mod_cast hNpos : 0 < (N : ℝ)) hNbound
      rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (ne_of_gt hxpos)] at h
      dsimp only [L]
      linarith
    have hLLog : L + Real.log 3 ≤ (1 + Real.log 3) * L := by
      nlinarith
    have hJbound : (J : ℝ) ≤ (1 + Real.log 3) / Real.log 2 * L := by
      rw [div_mul_eq_mul_div]
      exact (le_div_iff₀ hlog₂).mpr (hLogBound.trans hLLog)
    dsimp only [Cindex]
    linarith
  have hBox (j : ℕ) (hj : j ∈ Idx) (d : ℝ) (hd : d = 1 ∨ d = 2) :
      ‖∑ m ∈ (dyadicIntegers (x / (d * H j))).filter
          (fun m : ℕ => (m : ℝ) < 2 * (x / (d * H j))),
        ∑ q ∈ F j, f q m‖ ≤ Ctype * x * Real.rpow L (-6 : ℝ) := by
    obtain ⟨hmScale, hnScale, hProdLo, hProdHi, hWinLo, hWinHi⟩ := hScale j hj d hd
    have hdpos : 0 < d := by rcases hd with rfl | rfl <;> norm_num
    let Hm : ℝ := x / (d * H j)
    have hmpos : 0 < Hm := by dsimp only [Hm]; positivity
    let I : Set ℕ := {m | Hm ≤ (m : ℝ) ∧ (m : ℝ) < 2 * Hm}
    have hI : IsNatInterval I := by
      intro m n k hm hn hmk hkn
      rcases le_total m n with hmn | hnm
      · rw [min_eq_left hmn] at hmk
        rw [max_eq_right hmn] at hkn
        refine ⟨hm.1.trans ?_, lt_of_le_of_lt ?_ hn.2⟩
        · exact_mod_cast hmk
        · exact_mod_cast hkn
      · rw [min_eq_right hnm] at hmk
        rw [max_eq_left hnm] at hkn
        refine ⟨hn.1.trans ?_, lt_of_le_of_lt ?_ hm.2⟩
        · exact_mod_cast hmk
        · exact_mod_cast hkn
    have hISub : I ⊆ {m : ℕ | Hm ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * Hm} :=
      fun m hm => ⟨hm.1, hm.2.le⟩
    have hFSub : F j ⊆ dyadicIntegers (H j) := by
      intro q hq
      rcases Finset.mem_filter.mp hq with ⟨hqBin, hqj⟩
      have hD := hPrimeDyad q hqBin
      rw [hqj] at hD
      exact (hDyad _ (hHpos j).le q).mpr ⟨hD.1, hD.2.le⟩
    let β : ℕ → ℂ := fun q => if q ∈ F j then 1 else 0
    have hβsupp : ∀ q, β q ≠ 0 → q ∈ dyadicIntegers (H j) ∧
        roughAbove q (roughCutoff x) := by
      intro q hNZ
      have hq : q ∈ F j := by
        by_contra hnot
        exact hNZ (by simp only [β, if_neg hnot])
      exact ⟨hFSub hq, hPrimeRough q (Finset.mem_filter.mp hq).1⟩
    have hβbound : ∀ q ∈ dyadicIntegers (H j), ‖β q‖ ≤ 1 := by
      intro q hq
      by_cases hqF : q ∈ F j <;> simp [β, hqF]
    have hBound := hType x hxType Hm (H j) hmScale hnScale hProdLo hProdHi
      hWinLo hWinHi I hI hISub β hβsupp hβbound
    have hInner (m : ℕ) :
        (∑ q ∈ dyadicIntegers (H j),
          ((roughIndicator x γ m - roughProxy x γ m : ℝ) : ℂ) * β q *
            (conWeight x M c u K a Ψ (m * q) : ℂ)) = ∑ q ∈ F j, f q m := by
      have hEq :
          (∑ q ∈ F j,
            ((roughIndicator x γ m - roughProxy x γ m : ℝ) : ℂ) * β q *
              (conWeight x M c u K a Ψ (m * q) : ℂ)) =
          ∑ q ∈ dyadicIntegers (H j),
            ((roughIndicator x γ m - roughProxy x γ m : ℝ) : ℂ) * β q *
              (conWeight x M c u K a Ψ (m * q) : ℂ) := by
        apply Finset.sum_subset hFSub
        intro q hq hqNot
        simp only [β, if_neg hqNot, mul_zero, zero_mul]
      rw [← hEq]
      apply Finset.sum_congr rfl
      intro q hq
      simp only [β, if_pos hq, mul_one, f]
    simp_rw [hInner] at hBound
    have hBoundUpper :
        ‖∑ m ∈ (dyadicIntegers Hm).filter (fun m : ℕ => (m : ℝ) < 2 * Hm),
          ∑ q ∈ F j, f q m‖ ≤ Ctype * (Hm * H j) * Real.rpow L (-6 : ℝ) := by
      convert hBound using 1
      congr 1
      apply Finset.sum_congr
      · ext m
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hm, hmhi⟩
          exact ⟨hm, ((hDyad _ hmpos.le m).mp hm).1, hmhi⟩
        · rintro ⟨hm, hmlo, hmhi⟩
          exact ⟨hm, hmhi⟩
      · intro m hm
        rfl
    have hProd : Hm * H j ≤ x := by
      have hEq : Hm * H j = x / d := by
        dsimp only [Hm]
        field_simp [ne_of_gt hdpos, ne_of_gt (hHpos j)]
      rw [hEq]
      rcases hd with rfl | rfl <;> norm_num <;> linarith
    exact hBoundUpper.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hProd hCtype.le) (Real.rpow_nonneg hLpos.le _))
  have hFiber (j : ℕ) (hj : j ∈ Idx) :
      ‖∑ q ∈ F j, ∑ m ∈ R, f q m‖ ≤ 2 * Ctype * x * Real.rpow L (-6 : ℝ) := by
    let A := (dyadicIntegers (x / (2 * H j))).filter (fun m : ℕ => (m : ℝ) < x / H j)
    let B := (dyadicIntegers (x / H j)).filter (fun m : ℕ => (m : ℝ) < 2 * (x / H j))
    have hSupportF (q : ℕ) (m : ℕ) (hNZ : f q m ≠ 0) :
        x < ((m * q : ℕ) : ℝ) ∧ ((m * q : ℕ) : ℝ) < 2 * x := by
      apply hSupport x hxSupport (m * q)
      intro hwZero
      apply hNZ
      simp only [f, hwZero, Complex.ofReal_zero, mul_zero]
    have hSplit : (∑ q ∈ F j, ∑ m ∈ R, f q m) =
        (∑ m ∈ A, ∑ q ∈ F j, f q m) + (∑ m ∈ B, ∑ q ∈ F j, f q m) := by
      calc
        _ = ∑ q ∈ F j, ((∑ m ∈ A, f q m) + (∑ m ∈ B, f q m)) := by
          apply Finset.sum_congr rfl
          intro q hq
          rcases Finset.mem_filter.mp hq with ⟨hqBin, hqj⟩
          have hD := hPrimeDyad q hqBin
          rw [hqj] at hD
          exact two_cofactor_boxes_reindex x (H j) q (f q) hxpos (hHone j)
            hD.1 hD.2 (hSupportF q)
        _ = _ := by
          rw [Finset.sum_add_distrib]
          congr 1 <;> rw [Finset.sum_comm]
    have hMiddle : 2 * (x / (2 * H j)) = x / H j := by
      field_simp [ne_of_gt (hHpos j)]
    have hBox₂ := hBox j hj 2 (Or.inr rfl)
    rw [hMiddle] at hBox₂
    have hBox₁ := hBox j hj 1 (Or.inl rfl)
    simp only [one_mul] at hBox₁
    rw [hSplit]
    calc
      _ ≤ ‖∑ m ∈ A, ∑ q ∈ F j, f q m‖ + ‖∑ m ∈ B, ∑ q ∈ F j, f q m‖ :=
        norm_add_le _ _
      _ ≤ Ctype * x * Real.rpow L (-6 : ℝ) + Ctype * x * Real.rpow L (-6 : ℝ) :=
        add_le_add hBox₂ hBox₁
      _ = _ := by ring
  have hPartition : (∑ j ∈ Idx, ∑ q ∈ F j, ∑ m ∈ R, f q m) =
      ∑ q ∈ Bin, ∑ m ∈ R, f q m := by
    exact Finset.sum_fiberwise_of_maps_to
      (fun q hq => Finset.mem_image_of_mem (Nat.log 2) hq) (fun q => ∑ m ∈ R, f q m)
  have hLpow : L * Real.rpow L (-6 : ℝ) = Real.rpow L (-5 : ℝ) := by
    calc
      _ = Real.rpow L (1 : ℝ) * Real.rpow L (-6 : ℝ) :=
        congrArg (fun t : ℝ => t * Real.rpow L (-6 : ℝ)) (Real.rpow_one L).symm
      _ = Real.rpow L ((1 : ℝ) + (-6 : ℝ)) := (Real.rpow_add hLpos 1 (-6)).symm
      _ = _ := by norm_num
  have hSummandNonneg : 0 ≤ 2 * Ctype * x * Real.rpow L (-6 : ℝ) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCtype.le) hxpos.le)
      (Real.rpow_nonneg hLpos.le _)
  have hComplex : ‖∑ q ∈ Bin, ∑ m ∈ R, f q m‖ ≤ C * x * Real.rpow L (-5 : ℝ) := by
    calc
      _ = ‖∑ j ∈ Idx, ∑ q ∈ F j, ∑ m ∈ R, f q m‖ := by rw [hPartition]
      _ ≤ ∑ j ∈ Idx, ‖∑ q ∈ F j, ∑ m ∈ R, f q m‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Idx, 2 * Ctype * x * Real.rpow L (-6 : ℝ) :=
        Finset.sum_le_sum (fun j hj => hFiber j hj)
      _ = (Idx.card : ℝ) * (2 * Ctype * x * Real.rpow L (-6 : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Cindex * L) * (2 * Ctype * x * Real.rpow L (-6 : ℝ)) :=
        mul_le_mul_of_nonneg_right hIndexCard hSummandNonneg
      _ = (2 * Ctype * Cindex) * x * (L * Real.rpow L (-6 : ℝ)) := by ring
      _ = C * x * Real.rpow L (-5 : ℝ) := by rw [hLpow]
  have hCast :
      ((∑ q ∈ Bin, ∑ m ∈ R,
        (roughIndicator x γ m - roughProxy x γ m) *
          conWeight x M c u K a Ψ (m * q) : ℝ) : ℂ) =
      ∑ q ∈ Bin, ∑ m ∈ R, f q m := by
    simp only [f, Complex.ofReal_sum, Complex.ofReal_mul]
  rw [← hCast] at hComplex
  simpa only [Complex.norm_real, Real.norm_eq_abs] using hComplex

end ArtinPrimitiveRoots.Proofs.c_bins_sol
