import ArtinPrimitiveRoots.TypeII.PD.Defs
import ArtinPrimitiveRoots.TypeII.Proofs.pd0.MomentArithmetic
import ArtinPrimitiveRoots.TypeII.Proofs.pd0.ModeratePhase
import ArtinPrimitiveRoots.TypeII.Proofs.pd0.RoughCounts

/-! Elementary mean-value, rough-count, and moderate-phase estimates from PD
`02-preliminaries.tex:73-235`. -/

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical MeasureTheory
open ArtinPrimitiveRoots.TypeII
open scoped ComplexConjugate

/-- A finite Dirichlet polynomial in logarithmic coordinates, with its zero index excluded as
required by correction 1 from review lane `rev-b`. -/
noncomputable def dirichletPolynomial (Y : ℕ) (coeff : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ (Finset.range (Y + 1)).filter (fun n => 1 ≤ n),
    coeff n * Complex.exp (Complex.I * t * Real.log (n : ℝ))

private noncomputable def exponentialPhase (u t : ℝ) : ℂ :=
  Complex.exp ((u : ℂ) * ((t : ℂ) * Complex.I))

private noncomputable def exponentialAntiderivative (u t : ℝ) : ℂ :=
  exponentialPhase u t / ((u : ℂ) * Complex.I)

private lemma real_phase_pair (x y : ℝ) :
    Complex.exp (((x : ℝ) : ℂ) * Complex.I) *
        conj (Complex.exp (((y : ℝ) : ℂ) * Complex.I)) =
      Complex.exp (((x - y : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_sub]
  ring_nf

private lemma exponentialPhase_pair (u v t : ℝ) :
    exponentialPhase u t * conj (exponentialPhase v t) =
      exponentialPhase (u - v) t := by
  simpa [exponentialPhase, mul_sub, mul_comm, mul_left_comm, mul_assoc] using
    real_phase_pair (u * t) (v * t)

private lemma exponentialAntiderivative_hasDerivAt (u t : ℝ) (hu : u ≠ 0) :
    HasDerivAt (exponentialAntiderivative u) (exponentialPhase u t) t := by
  have hreal : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
    simpa using (hasDerivAt_id t).ofReal_comp
  have harg : HasDerivAt (fun s : ℝ => (u : ℂ) * ((s : ℂ) * Complex.I))
      ((u : ℂ) * Complex.I) t := by
    have h := hreal.const_mul ((u : ℂ) * Complex.I)
    have hfun : (fun s : ℝ => (u : ℂ) * ((s : ℂ) * Complex.I)) =
        fun s : ℝ => ((u : ℂ) * Complex.I) * (s : ℂ) := by
      funext s
      ring
    rw [hfun]
    simpa using h
  have hexp := (Complex.hasDerivAt_exp ((u : ℂ) * ((t : ℂ) * Complex.I))).comp t harg
  have hden : ((u : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hu) Complex.I_ne_zero
  have hquot := hexp.div_const ((u : ℂ) * Complex.I)
  convert hquot using 1
  · rfl
  · change Complex.exp ((u : ℂ) * ((t : ℂ) * Complex.I)) =
      Complex.exp ((u : ℂ) * ((t : ℂ) * Complex.I)) * ((u : ℂ) * Complex.I) /
        ((u : ℂ) * Complex.I)
    field_simp [hden, hu]

private lemma exponentialPhase_integral_bound (u a b : ℝ) (hu : u ≠ 0)
    (hab : a ≤ b) :
    ‖∫ t in a..b, exponentialPhase u t‖ ≤ 2 / |u| := by
  have hphaseCont : Continuous (exponentialPhase u) := by
    unfold exponentialPhase
    fun_prop
  have hphaseInt : IntervalIntegrable (exponentialPhase u) MeasureTheory.volume a b :=
    Continuous.intervalIntegrable hphaseCont a b
  have hderivEq : ∀ t ∈ Set.Icc a b,
      deriv (exponentialAntiderivative u) t = exponentialPhase u t := by
    intro t ht
    exact (exponentialAntiderivative_hasDerivAt u t hu).deriv
  have hdiff : ∀ t ∈ Set.uIcc a b,
      DifferentiableAt ℝ (exponentialAntiderivative u) t := by
    intro t ht
    exact (exponentialAntiderivative_hasDerivAt u t hu).differentiableAt
  have hderivInt : IntervalIntegrable (deriv (exponentialAntiderivative u))
      MeasureTheory.volume a b := by
    apply hphaseInt.congr
    intro t ht
    have ht' : t ∈ Set.Icc a b := by
      have ht'' : t ∈ Set.Ioc a b := by
        simpa [Set.uIoc_of_le hab] using ht
      exact ⟨ht''.1.le, ht''.2⟩
    exact (hderivEq t ht').symm
  have hFTC : ∫ t in a..b, deriv (exponentialAntiderivative u) t =
      exponentialAntiderivative u b - exponentialAntiderivative u a :=
    intervalIntegral.integral_deriv_eq_sub hdiff hderivInt
  have hreplace : ∫ t in a..b, deriv (exponentialAntiderivative u) t =
      ∫ t in a..b, exponentialPhase u t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Set.Icc a b := by
      simpa [Set.uIcc_of_le hab] using ht
    exact hderivEq t ht'
  have hphaseNorm (t : ℝ) : ‖exponentialPhase u t‖ = 1 := by
    simp [exponentialPhase, Complex.norm_exp]
  have hdenNorm : ‖(u : ℂ) * Complex.I‖ = |u| := by
    simp [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hantiNorm (t : ℝ) : ‖exponentialAntiderivative u t‖ = 1 / |u| := by
    simp [exponentialAntiderivative, norm_div, hphaseNorm, hdenNorm]
  calc
    ‖∫ t in a..b, exponentialPhase u t‖ =
        ‖exponentialAntiderivative u b - exponentialAntiderivative u a‖ := by
      rw [← hreplace, hFTC]
    _ ≤ ‖exponentialAntiderivative u b‖ + ‖exponentialAntiderivative u a‖ := norm_sub_le _ _
    _ = 1 / |u| + 1 / |u| := by rw [hantiNorm, hantiNorm]
    _ = 2 / |u| := by ring

private lemma log_gap_lower (m n Y : ℕ) (hm : 1 ≤ m) (hmn : m < n)
    (hnY : n ≤ Y) :
    ((n - m : ℕ) : ℝ) / (Y : ℝ) ≤ Real.log (n : ℝ) - Real.log (m : ℝ) := by
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hYpos : 0 < (Y : ℝ) := by exact_mod_cast (by omega : 0 < Y)
  have hmnR : (m : ℝ) < (n : ℝ) := by exact_mod_cast hmn
  have hnYR : (n : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hnY
  have hratio : 0 < (m : ℝ) / (n : ℝ) := div_pos hmpos hnpos
  have hlogUpper := Real.log_le_sub_one_of_pos hratio
  have hlogEq : Real.log (n : ℝ) - Real.log (m : ℝ) =
      -Real.log ((m : ℝ) / (n : ℝ)) := by
    rw [Real.log_div hmpos.ne' hnpos.ne']
    ring
  have hlogLower : 1 - (m : ℝ) / (n : ℝ) ≤
      Real.log (n : ℝ) - Real.log (m : ℝ) := by
    rw [hlogEq]
    linarith
  have hgap : ((n - m : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) := by
    rw [Nat.cast_sub (Nat.le_of_lt hmn)]
  have hgapNonneg : 0 ≤ ((n - m : ℕ) : ℝ) := by positivity
  calc
    ((n - m : ℕ) : ℝ) / (Y : ℝ) ≤ ((n - m : ℕ) : ℝ) / (n : ℝ) :=
      div_le_div_of_nonneg_left hgapNonneg hnpos hnYR
    _ = 1 - (m : ℝ) / (n : ℝ) := by rw [hgap]; field_simp
    _ ≤ Real.log (n : ℝ) - Real.log (m : ℝ) := hlogLower

private lemma reciprocalGapRowBound (Y n : ℕ)
    (hn : n ∈ ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.positiveRange Y) :
    (∑ m ∈ (ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.positiveRange Y).filter
        (fun m => m ≠ n),
      (1 : ℝ) / |(m : ℝ) - (n : ℝ)|) ≤
      2 * ∑ d ∈ ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.positiveRange Y,
        (1 : ℝ) / (d : ℝ) := by
  classical
  let S := ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.positiveRange Y
  let T := S.filter (fun m => m ≠ n)
  let L := S.filter (fun m => m < n)
  let U := S.filter (fun m => n < m)
  have hsplit : T = L ∪ U := by
    ext m
    simp only [T, L, U, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hmS, hmne⟩
      by_cases hmn : m < n
      · exact Or.inl ⟨hmS, hmn⟩
      · have hnm : n < m := by omega
        exact Or.inr ⟨hmS, hnm⟩
    · rintro (⟨hmS, hmn⟩ | ⟨hmS, hnm⟩)
      · exact ⟨hmS, ne_of_lt hmn⟩
      · exact ⟨hmS, ne_of_gt hnm⟩
  have hdisj : Disjoint L U := by
    apply Finset.disjoint_left.mpr
    intro m hmL hmU
    have hmn := (Finset.mem_filter.mp hmL).2
    have hnm := (Finset.mem_filter.mp hmU).2
    omega
  have hninfo := Finset.mem_filter.mp hn
  have hnpos : 0 < n := by omega
  have hnle : n ≤ Y := Nat.le_of_lt_succ (Finset.mem_range.mp hninfo.1)
  have hleftImg : L.image (fun m => n - m) ⊆ S := by
    intro d hd
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hd
    have hmL := Finset.mem_filter.mp hm
    have hmn : m < n := hmL.2
    have hmS : m ∈ S := hmL.1
    change m ∈ ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.positiveRange Y at hmS
    have hmpos : 1 ≤ m := (Finset.mem_filter.mp hmS).2
    change n - m ∈ ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.positiveRange Y
    simp only [ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.positiveRange,
      Finset.mem_filter, Finset.mem_range]
    omega
  have hrightImg : U.image (fun m => m - n) ⊆ S := by
    intro d hd
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hd
    have hmU := Finset.mem_filter.mp hm
    have hnm : n < m := hmU.2
    have hmS : m ∈ S := hmU.1
    change m ∈ ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.positiveRange Y at hmS
    have hMle : m ≤ Y := Nat.le_of_lt_succ (Finset.mem_range.mp
      (Finset.mem_filter.mp hmS).1)
    have hposm : 1 ≤ m := (Finset.mem_filter.mp hmS).2
    change m - n ∈ ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.positiveRange Y
    simp only [ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.positiveRange,
      Finset.mem_filter, Finset.mem_range]
    omega
  have hinjL : ∀ m ∈ L, ∀ m' ∈ L, n - m = n - m' → m = m' := by
    intro m hm m' hm' he
    have hmn : m < n := (Finset.mem_filter.mp hm).2
    have hmn' : m' < n := (Finset.mem_filter.mp hm').2
    omega
  have hinjU : ∀ m ∈ U, ∀ m' ∈ U, m - n = m' - n → m = m' := by
    intro m hm m' hm' he
    have hnm : n < m := (Finset.mem_filter.mp hm).2
    have hnm' : n < m' := (Finset.mem_filter.mp hm').2
    omega
  have hleftImageSum :
      (∑ m ∈ L, (1 : ℝ) / ((n - m : ℕ) : ℝ)) =
        ∑ d ∈ L.image (fun m => n - m), (1 : ℝ) / (d : ℝ) := by
    have hinj : Set.InjOn (fun m => n - m) (L : Set ℕ) := by
      intro m hm m' hm' he
      exact hinjL m hm m' hm' he
    exact (Finset.sum_image (s := L) (g := fun m : ℕ => n - m)
      (f := fun d : ℕ => (1 : ℝ) / (d : ℝ)) hinj).symm
  have hrightImageSum :
      (∑ m ∈ U, (1 : ℝ) / ((m - n : ℕ) : ℝ)) =
        ∑ d ∈ U.image (fun m => m - n), (1 : ℝ) / (d : ℝ) := by
    have hinj : Set.InjOn (fun m => m - n) (U : Set ℕ) := by
      intro m hm m' hm' he
      exact hinjU m hm m' hm' he
    exact (Finset.sum_image (s := U) (g := fun m : ℕ => m - n)
      (f := fun d : ℕ => (1 : ℝ) / (d : ℝ)) hinj).symm
  have hleftBound :
      (∑ m ∈ L, (1 : ℝ) / ((n - m : ℕ) : ℝ)) ≤
        ∑ d ∈ S, (1 : ℝ) / (d : ℝ) := by
    rw [hleftImageSum]
    apply Finset.sum_le_sum_of_subset_of_nonneg hleftImg
    intro d hd hnot
    positivity
  have hrightBound :
      (∑ m ∈ U, (1 : ℝ) / ((m - n : ℕ) : ℝ)) ≤
        ∑ d ∈ S, (1 : ℝ) / (d : ℝ) := by
    rw [hrightImageSum]
    apply Finset.sum_le_sum_of_subset_of_nonneg hrightImg
    intro d hd hnot
    positivity
  have hleftAbs :
      (∑ m ∈ L, (1 : ℝ) / |(m : ℝ) - (n : ℝ)|) =
        ∑ m ∈ L, (1 : ℝ) / ((n - m : ℕ) : ℝ) := by
    apply Finset.sum_congr rfl
    intro m hm
    have hmn : m < n := (Finset.mem_filter.mp hm).2
    have hcast : ((n - m : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) := by
      rw [Nat.cast_sub (Nat.le_of_lt hmn)]
    rw [hcast, abs_of_nonpos]
    · congr 1 <;> ring
    · exact sub_nonpos.mpr (by exact_mod_cast hmn.le)
  have hrightAbs :
      (∑ m ∈ U, (1 : ℝ) / |(m : ℝ) - (n : ℝ)|) =
        ∑ m ∈ U, (1 : ℝ) / ((m - n : ℕ) : ℝ) := by
    apply Finset.sum_congr rfl
    intro m hm
    have hnm : n < m := (Finset.mem_filter.mp hm).2
    have hcast : ((m - n : ℕ) : ℝ) = (m : ℝ) - (n : ℝ) := by
      rw [Nat.cast_sub (Nat.le_of_lt hnm)]
    rw [hcast, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hnm.le))]
  have hleftBoundAbs :
      (∑ m ∈ L, (1 : ℝ) / |(m : ℝ) - (n : ℝ)|) ≤
        ∑ d ∈ S, (1 : ℝ) / (d : ℝ) := by
    calc
      _ = ∑ m ∈ L, (1 : ℝ) / ((n - m : ℕ) : ℝ) := hleftAbs
      _ ≤ _ := hleftBound
  have hrightBoundAbs :
      (∑ m ∈ U, (1 : ℝ) / |(m : ℝ) - (n : ℝ)|) ≤
        ∑ d ∈ S, (1 : ℝ) / (d : ℝ) := by
    calc
      _ = ∑ m ∈ U, (1 : ℝ) / ((m - n : ℕ) : ℝ) := hrightAbs
      _ ≤ _ := hrightBound
  calc
    _ = (∑ m ∈ L, (1 : ℝ) / |(m : ℝ) - (n : ℝ)|) +
        ∑ m ∈ U, (1 : ℝ) / |(m : ℝ) - (n : ℝ)| := by
      rw [← Finset.sum_union hdisj, ← hsplit]
    _ ≤ (∑ d ∈ S, (1 : ℝ) / (d : ℝ)) +
        ∑ d ∈ S, (1 : ℝ) / (d : ℝ) :=
      add_le_add hleftBoundAbs hrightBoundAbs
    _ = 2 * ∑ d ∈ S, (1 : ℝ) / (d : ℝ) := by ring

private lemma symmetricRowQuadraticBound {ι : Type*} (S : Finset ι)
    (K : ι → ι → ℝ) (v : ι → ℝ) (C : ℝ)
    (hK : ∀ i ∈ S, ∀ j ∈ S, 0 ≤ K i j)
    (hsymm : ∀ i ∈ S, ∀ j ∈ S, K i j = K j i)
    (hrow : ∀ i ∈ S, (∑ j ∈ S, K i j) ≤ C) :
    (∑ i ∈ S, ∑ j ∈ S, v i * v j * K i j) ≤
      C * ∑ i ∈ S, (v i) ^ 2 := by
  have he : (∑ i ∈ S, ∑ j ∈ S, ((v i) ^ 2 + (v j) ^ 2) / 2 * K i j) =
      ∑ i ∈ S, (v i) ^ 2 * ∑ j ∈ S, K i j := by
    simp only [add_div, add_mul, Finset.sum_add_distrib]
    rw [Finset.sum_comm (s := S) (t := S) (f := fun i j => (v j) ^ 2 / 2 * K i j)]
    simp only [← Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hk : (∑ j ∈ S, K j i) = ∑ j ∈ S, K i j :=
      Finset.sum_congr rfl fun j hj => hsymm j hj i hi
    rw [hk]
    ring
  calc
    _ ≤ ∑ i ∈ S, ∑ j ∈ S, ((v i) ^ 2 + (v j) ^ 2) / 2 * K i j := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_right _ (hK i hi j hj)
      nlinarith [sq_nonneg (v i - v j)]
    _ = _ := he
    _ ≤ ∑ i ∈ S, (v i) ^ 2 * C := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hrow i hi) (sq_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

private noncomputable def dirichletPairKernel (D Y : ℝ) (m n : ℕ) : ℝ :=
  if m = n then D else 2 * Y / |(m : ℝ) - (n : ℝ)|

private lemma dirichletPairKernel_nonneg (D Y : ℝ) (hD : 0 ≤ D) (hY : 0 ≤ Y)
    (m n : ℕ) : 0 ≤ dirichletPairKernel D Y m n := by
  by_cases h : m = n
  · simp [dirichletPairKernel, h, hD]
  · have hcast : (m : ℝ) ≠ (n : ℝ) := by exact_mod_cast h
    have hden : 0 < |(m : ℝ) - (n : ℝ)| := abs_pos.mpr (sub_ne_zero.mpr hcast)
    simp only [dirichletPairKernel, if_neg h]
    exact div_nonneg (mul_nonneg (by norm_num) hY) hden.le

private lemma dirichletPairKernel_symmetric (D Y : ℝ) (m n : ℕ) :
    dirichletPairKernel D Y m n = dirichletPairKernel D Y n m := by
  by_cases h : m = n
  · subst n
    simp [dirichletPairKernel]
  · have h' : n ≠ m := Ne.symm h
    simp [dirichletPairKernel, h, h', abs_sub_comm]

private lemma dirichletPairKernel_rowBound (Y : ℕ) (a b : ℝ) (hab : a ≤ b)
    (m : ℕ) (hm : m ∈ ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.positiveRange Y) :
    (∑ n ∈ ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.positiveRange Y,
      dirichletPairKernel (b - a) (Y : ℝ) m n) ≤
        (b - a) + 4 * (Y : ℝ) *
          ∑ n ∈ ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.positiveRange Y,
            (1 : ℝ) / (n : ℝ) := by
  classical
  let S := ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.positiveRange Y
  have hmS : m ∈ S := hm
  have hD : 0 ≤ b - a := sub_nonneg.mpr hab
  have hY : 0 ≤ (Y : ℝ) := Nat.cast_nonneg _
  have hgap := reciprocalGapRowBound Y m hm
  have hgap' :
      (∑ n ∈ S.filter (fun n => n ≠ m), (1 : ℝ) / |(m : ℝ) - (n : ℝ)|) ≤
        2 * ∑ n ∈ S, (1 : ℝ) / (n : ℝ) := by
    simpa [S, abs_sub_comm] using hgap
  have hsum :
      (∑ n ∈ S, dirichletPairKernel (b - a) (Y : ℝ) m n) =
        (b - a) + ∑ n ∈ S.filter (fun n => n ≠ m),
          2 * (Y : ℝ) / |(m : ℝ) - (n : ℝ)| := by
    have hErase : S.erase m = S.filter (fun n => n ≠ m) := by
      ext n
      simp [eq_comm, and_comm]
    have hsumFilter :
        (∑ n ∈ S.filter (fun n => n ≠ m), dirichletPairKernel (b - a) (Y : ℝ) m n) =
          ∑ n ∈ S.filter (fun n => n ≠ m),
            2 * (Y : ℝ) / |(m : ℝ) - (n : ℝ)| := by
      apply Finset.sum_congr rfl
      intro n hn
      have hne : m ≠ n := (Finset.mem_filter.mp hn).2.symm
      simp [dirichletPairKernel, hne]
    calc
      _ = (∑ n ∈ S.erase m, dirichletPairKernel (b - a) (Y : ℝ) m n) +
          dirichletPairKernel (b - a) (Y : ℝ) m m := by
        exact (Finset.sum_erase_add S (fun n => dirichletPairKernel (b - a) (Y : ℝ) m n) hmS).symm
      _ = (∑ n ∈ S.filter (fun n => n ≠ m), dirichletPairKernel (b - a) (Y : ℝ) m n) +
          (b - a) := by rw [hErase]; simp [dirichletPairKernel]
      _ = (b - a) + ∑ n ∈ S.filter (fun n => n ≠ m),
          2 * (Y : ℝ) / |(m : ℝ) - (n : ℝ)| := by rw [hsumFilter]; ring
  calc
    _ = (b - a) + ∑ n ∈ S.filter (fun n => n ≠ m),
          2 * (Y : ℝ) / |(m : ℝ) - (n : ℝ)| := hsum
    _ = (b - a) + 2 * (Y : ℝ) *
          ∑ n ∈ S.filter (fun n => n ≠ m),
            (1 : ℝ) / |(m : ℝ) - (n : ℝ)| := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ ≤ (b - a) + 2 * (Y : ℝ) *
          (2 * ∑ n ∈ S, (1 : ℝ) / (n : ℝ)) := by
      calc
        _ = (2 * (Y : ℝ) *
            ∑ n ∈ S.filter (fun n => n ≠ m), (1 : ℝ) / |(m : ℝ) - (n : ℝ)|) +
              (b - a) := by ring
        _ ≤ (2 * (Y : ℝ) *
            (2 * ∑ n ∈ S, (1 : ℝ) / (n : ℝ))) + (b - a) :=
          by
            have hcoef : 0 ≤ (2 : ℝ) * (Y : ℝ) := by positivity
            have hmult := mul_le_mul_of_nonneg_left hgap' hcoef
            exact add_le_add_left hmult (b - a)
        _ = _ := by ring
    _ = (b - a) + 4 * (Y : ℝ) *
          ∑ n ∈ S, (1 : ℝ) / (n : ℝ) := by ring

private lemma expPhase_eq (u t : ℝ) :
    Complex.exp (Complex.I * t * u) = exponentialPhase u t := by
  unfold exponentialPhase
  congr 1
  push_cast
  ring_nf

private lemma dirichletPolynomial_mul_conj_expansion (Y : ℕ) (coeff : ℕ → ℂ) (t : ℝ) :
    dirichletPolynomial Y coeff t * conj (dirichletPolynomial Y coeff t) =
      ∑ m ∈ ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.positiveRange Y,
        ∑ n ∈ ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.positiveRange Y,
          coeff m * conj (coeff n) *
            exponentialPhase (Real.log (m : ℝ) - Real.log (n : ℝ)) t := by
  classical
  let S := ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.positiveRange Y
  change (∑ m ∈ S, coeff m * Complex.exp (Complex.I * t * Real.log (m : ℝ))) *
      conj (∑ n ∈ S, coeff n * Complex.exp (Complex.I * t * Real.log (n : ℝ))) = _
  simp_rw [expPhase_eq]
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm (s := S) (t := S)]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  rw [map_mul]
  calc
    (coeff m * exponentialPhase (Real.log (m : ℝ)) t) *
        (conj (coeff n) * conj (exponentialPhase (Real.log (n : ℝ)) t)) =
      coeff m * conj (coeff n) *
        (exponentialPhase (Real.log (m : ℝ)) t *
          conj (exponentialPhase (Real.log (n : ℝ)) t)) := by ring
    _ = coeff m * conj (coeff n) *
        exponentialPhase (Real.log (m : ℝ) - Real.log (n : ℝ)) t := by
      rw [exponentialPhase_pair]

private lemma dirichletPolynomial_normSq_expansion (Y : ℕ) (coeff : ℕ → ℂ) (t : ℝ) :
    ‖dirichletPolynomial Y coeff t‖ ^ 2 =
      ∑ m ∈ ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.positiveRange Y,
        ∑ n ∈ ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.positiveRange Y,
          (coeff m * conj (coeff n) *
            exponentialPhase (Real.log (m : ℝ) - Real.log (n : ℝ)) t).re := by
  classical
  have hnorm : ‖dirichletPolynomial Y coeff t‖ ^ 2 =
      (dirichletPolynomial Y coeff t * conj (dirichletPolynomial Y coeff t)).re := by
    rw [Complex.mul_conj']
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  calc
    _ = (dirichletPolynomial Y coeff t * conj (dirichletPolynomial Y coeff t)).re := hnorm
    _ = (∑ m ∈ ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.positiveRange Y,
          ∑ n ∈ ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.positiveRange Y,
            coeff m * conj (coeff n) *
              exponentialPhase (Real.log (m : ℝ) - Real.log (n : ℝ)) t).re := by
      rw [dirichletPolynomial_mul_conj_expansion]
    _ = _ := by simp

private noncomputable def differentiatedCoeff (coeff : ℕ → ℂ) (n : ℕ) : ℂ :=
  coeff n * (Real.log (n : ℝ) : ℂ) * Complex.I

private lemma dirichletPolynomial_hasDerivAt (Y : ℕ) (coeff : ℕ → ℂ) (t : ℝ) :
    HasDerivAt (dirichletPolynomial Y coeff)
      (dirichletPolynomial Y (differentiatedCoeff coeff) t) t := by
  classical
  let S := ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.positiveRange Y
  have hreal : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
    simpa using (hasDerivAt_id t).ofReal_comp
  change HasDerivAt
    (fun x : ℝ => ∑ n ∈ S, coeff n * Complex.exp (Complex.I * x * Real.log (n : ℝ)))
    (∑ n ∈ S, differentiatedCoeff coeff n *
      Complex.exp (Complex.I * t * Real.log (n : ℝ))) t
  have hsum : HasDerivAt
      (∑ n ∈ S, fun x : ℝ => coeff n * Complex.exp (Complex.I * x * Real.log (n : ℝ)))
      (∑ n ∈ S, differentiatedCoeff coeff n *
        Complex.exp (Complex.I * t * Real.log (n : ℝ))) t := by
    apply HasDerivAt.sum
    intro n hn
    have harg0 : HasDerivAt (fun s : ℝ => Complex.I * (s : ℂ)) Complex.I t := by
      simpa using hreal.const_mul Complex.I
    have harg : HasDerivAt
        (fun s : ℝ => Complex.I * (s : ℂ) * (Real.log (n : ℝ) : ℂ))
        (Complex.I * (Real.log (n : ℝ) : ℂ)) t := by
      convert harg0.mul_const (Real.log (n : ℝ) : ℂ) using 1 <;> simp [mul_assoc]
    have hexp :=
      (Complex.hasDerivAt_exp (Complex.I * (t : ℂ) * (Real.log (n : ℝ) : ℂ))).comp t harg
    have hterm := hexp.const_mul (coeff n)
    simpa [differentiatedCoeff, mul_assoc, mul_comm, mul_left_comm] using hterm
  convert hsum using 1
  · funext x
    simp

private lemma intervalIntegral_re {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℂ)
    (hf : IntervalIntegrable f MeasureTheory.volume a b) :
    (∫ t in a..b, (f t).re) = (∫ t in a..b, f t).re := by
  have hfIoc : IntegrableOn f (Set.Ioc a b) MeasureTheory.volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hf
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  exact integral_re hfIoc

private lemma dirichletPolynomial_integral_expansion (Y : ℕ) (coeff : ℕ → ℂ)
    (a b : ℝ) (hab : a ≤ b) :
    (∫ t in a..b, ‖dirichletPolynomial Y coeff t‖ ^ 2) =
      ∑ m ∈ ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.positiveRange Y,
        ∑ n ∈ ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.positiveRange Y,
          (coeff m * conj (coeff n) *
            ∫ t in a..b,
              exponentialPhase (Real.log (m : ℝ) - Real.log (n : ℝ)) t).re := by
  classical
  let S := ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.positiveRange Y
  have hpoint (t : ℝ) : ‖dirichletPolynomial Y coeff t‖ ^ 2 =
      ∑ m ∈ S, ∑ n ∈ S,
        (coeff m * conj (coeff n) *
          exponentialPhase (Real.log (m : ℝ) - Real.log (n : ℝ)) t).re := by
    simpa [S] using dirichletPolynomial_normSq_expansion Y coeff t
  have htermCont (m n : ℕ) : Continuous (fun t : ℝ =>
      (coeff m * conj (coeff n) *
        exponentialPhase (Real.log (m : ℝ) - Real.log (n : ℝ)) t).re) := by
    unfold exponentialPhase
    fun_prop
  have hinnerCont (m : ℕ) : Continuous (fun t : ℝ =>
      ∑ n ∈ S, (coeff m * conj (coeff n) *
        exponentialPhase (Real.log (m : ℝ) - Real.log (n : ℝ)) t).re) := by
    unfold exponentialPhase
    fun_prop
  have htermComplexCont (m n : ℕ) : Continuous (fun t : ℝ =>
      coeff m * conj (coeff n) *
        exponentialPhase (Real.log (m : ℝ) - Real.log (n : ℝ)) t) := by
    unfold exponentialPhase
    fun_prop
  calc
    _ = ∫ t in a..b, ∑ m ∈ S, ∑ n ∈ S,
          (coeff m * conj (coeff n) *
            exponentialPhase (Real.log (m : ℝ) - Real.log (n : ℝ)) t).re := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact hpoint t
    _ = ∑ m ∈ S, ∫ t in a..b, ∑ n ∈ S,
          (coeff m * conj (coeff n) *
            exponentialPhase (Real.log (m : ℝ) - Real.log (n : ℝ)) t).re := by
      rw [intervalIntegral.integral_finsetSum]
      intro m hm
      exact Continuous.intervalIntegrable (hinnerCont m) a b
    _ = ∑ m ∈ S, ∑ n ∈ S, ∫ t in a..b,
          (coeff m * conj (coeff n) *
            exponentialPhase (Real.log (m : ℝ) - Real.log (n : ℝ)) t).re := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [intervalIntegral.integral_finsetSum]
      intro n hn
      exact Continuous.intervalIntegrable (htermCont m n) a b
    _ = ∑ m ∈ S, ∑ n ∈ S,
          (coeff m * conj (coeff n) *
            ∫ t in a..b,
              exponentialPhase (Real.log (m : ℝ) - Real.log (n : ℝ)) t).re := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      rw [intervalIntegral_re hab _ (Continuous.intervalIntegrable
        (htermComplexCont m n) a b), intervalIntegral.integral_const_mul]

private lemma nonnegSubintervalIntegral_le {l s t r : ℝ} (hls : l ≤ s) (hst : s ≤ t)
    (htr : t ≤ r) (f : ℝ → ℝ) (hf : Continuous f) (hnonneg : ∀ y, 0 ≤ f y) :
    (∫ y in s..t, f y) ≤ ∫ y in l..r, f y := by
  have hlsInt : IntervalIntegrable f MeasureTheory.volume l s :=
    Continuous.intervalIntegrable hf l s
  have hstInt : IntervalIntegrable f MeasureTheory.volume s t :=
    Continuous.intervalIntegrable hf s t
  have htrInt : IntervalIntegrable f MeasureTheory.volume t r :=
    Continuous.intervalIntegrable hf t r
  have hltInt : IntervalIntegrable f MeasureTheory.volume l t :=
    Continuous.intervalIntegrable hf l t
  have hleft := intervalIntegral.integral_add_adjacent_intervals hlsInt hstInt
  have hright := intervalIntegral.integral_add_adjacent_intervals hltInt htrInt
  have hleftNonneg :=
    intervalIntegral.integral_nonneg_of_forall (μ := MeasureTheory.volume) hls hnonneg
  have hrightNonneg :=
    intervalIntegral.integral_nonneg_of_forall (μ := MeasureTheory.volume) htr hnonneg
  linarith

private lemma unitIntervalSquareBound {l r : ℝ} (hlr : l ≤ r) (hlen : r - l = 1)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc l r)) :
    (∫ y in l..r, f y) ^ 2 ≤ ∫ y in l..r, (f y) ^ 2 := by
  let A : ℝ := ∫ y in l..r, f y
  have hInt : IntervalIntegrable f MeasureTheory.volume l r := hf.intervalIntegrable_of_Icc hlr
  have hSqCont : ContinuousOn (fun y => (f y) ^ 2) (Set.Icc l r) := by
    fun_prop
  have hSqInt : IntervalIntegrable (fun y => (f y) ^ 2) MeasureTheory.volume l r :=
    hSqCont.intervalIntegrable_of_Icc hlr
  have hlinCont : ContinuousOn (fun y => (2 * A) * f y) (Set.Icc l r) :=
    continuousOn_const.mul hf
  have hlinInt : IntervalIntegrable (fun y => (2 * A) * f y) MeasureTheory.volume l r :=
    hlinCont.intervalIntegrable_of_Icc hlr
  have hconstInt : IntervalIntegrable (fun _ : ℝ => A ^ 2) MeasureTheory.volume l r :=
    intervalIntegrable_const
  have hlinEq : (∫ y in l..r, (2 * A) * f y) = 2 * A * A := by
    rw [intervalIntegral.integral_const_mul]
  have hconstEq : (∫ y in l..r, A ^ 2) = A ^ 2 := by
    simp [intervalIntegral.integral_const, hlen]
  have hnonneg : 0 ≤ ∫ y in l..r, (f y - A) ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall (μ := MeasureTheory.volume) hlr
      (fun y => sq_nonneg (f y - A))
  have hvariance : (∫ y in l..r, (f y - A) ^ 2) =
      (∫ y in l..r, (f y) ^ 2) - A ^ 2 := by
    calc
      _ = ∫ y in l..r, ((f y) ^ 2 - (2 * A) * f y + A ^ 2) := by
        apply intervalIntegral.integral_congr
        intro y hy
        ring
      _ = (∫ y in l..r, (f y) ^ 2) -
            (∫ y in l..r, (2 * A) * f y) +
            ∫ y in l..r, A ^ 2 := by
        rw [intervalIntegral.integral_add (hSqInt.sub hlinInt) hconstInt,
          intervalIntegral.integral_sub hSqInt hlinInt]
      _ = (∫ y in l..r, (f y) ^ 2) - (2 * A * A) + A ^ 2 := by
        rw [hlinEq, hconstEq]
      _ = (∫ y in l..r, (f y) ^ 2) - A ^ 2 := by ring
  nlinarith [hnonneg, hvariance]

private lemma unitCellPointBound (f g : ℝ → ℂ) (t : ℝ)
    (hderiv : ∀ y ∈ Set.Icc (t - 1 / 2) (t + 1 / 2), HasDerivAt f (g y) y)
    (hf : Continuous f) (hg : Continuous g) :
    ‖f t‖ ^ 2 ≤ 2 *
      (∫ y in (t - 1 / 2)..(t + 1 / 2), (‖f y‖ ^ 2 + ‖g y‖ ^ 2)) := by
  have hlr : t - (1 / 2 : ℝ) ≤ t + 1 / 2 := by linarith
  have hlen : (t + 1 / 2) - (t - 1 / 2) = 1 := by ring
  let l : ℝ := t - 1 / 2
  let r : ℝ := t + 1 / 2
  let gn : ℝ → ℝ := fun y => ‖g y‖
  let fn : ℝ → ℝ := fun y => ‖f y‖
  let G : ℝ := ∫ y in l..r, gn y
  let A : ℝ := ∫ y in l..r, fn y
  have hlr' : l ≤ r := by dsimp [l, r]; linarith
  have hlen' : r - l = 1 := by dsimp [l, r]; linarith
  have hgn : Continuous gn := by dsimp [gn]; exact hg.norm
  have hfn : Continuous fn := by dsimp [fn]; exact hf.norm
  have hgnInt : IntervalIntegrable gn MeasureTheory.volume l r :=
    Continuous.intervalIntegrable hgn l r
  have hfnInt : IntervalIntegrable fn MeasureTheory.volume l r :=
    Continuous.intervalIntegrable hfn l r
  have hgnSqCont : ContinuousOn (fun y => (gn y) ^ 2) (Set.Icc l r) := by
    fun_prop
  have hfnSqCont : ContinuousOn (fun y => (fn y) ^ 2) (Set.Icc l r) := by
    fun_prop
  have hgnSqInt : IntervalIntegrable (fun y => (gn y) ^ 2) MeasureTheory.volume l r :=
    hgnSqCont.intervalIntegrable_of_Icc hlr'
  have hfnSqInt : IntervalIntegrable (fun y => (fn y) ^ 2) MeasureTheory.volume l r :=
    hfnSqCont.intervalIntegrable_of_Icc hlr'
  have hGnonneg : 0 ≤ G := by
    dsimp [G, gn]
    exact intervalIntegral.integral_nonneg_of_forall (μ := MeasureTheory.volume) hlr'
      (fun y => norm_nonneg _)
  have hAnonneg : 0 ≤ A := by
    dsimp [A, fn]
    exact intervalIntegral.integral_nonneg_of_forall (μ := MeasureTheory.volume) hlr'
      (fun y => norm_nonneg _)
  have hGsq : G ^ 2 ≤ ∫ y in l..r, (gn y) ^ 2 := by
    dsimp [G]
    exact unitIntervalSquareBound hlr' hlen' gn hgn.continuousOn
  have hAsq : A ^ 2 ≤ ∫ y in l..r, (fn y) ^ 2 := by
    dsimp [A]
    exact unitIntervalSquareBound hlr' hlen' fn hfn.continuousOn
  have hpoint (s : ℝ) (hs : s ∈ Set.Icc l r) : ‖f t‖ ≤ ‖f s‖ + G := by
    have hdiff : ‖f t - f s‖ ≤ G := by
      rcases le_total s t with hst | hts
      · have hderivST : ∀ y ∈ Set.uIcc s t, HasDerivAt f (g y) y := by
          intro y hy
          have hyST : y ∈ Set.Icc s t := by simpa [Set.uIcc_of_le hst] using hy
          have hyCell : y ∈ Set.Icc (t - 1 / 2) (t + 1 / 2) := by
            constructor
            · exact le_trans (by dsimp [l] at hs; exact hs.1) hyST.1
            · exact le_trans hyST.2 (by linarith [hs.2])
          exact hderiv y hyCell
        have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderivST
          (Continuous.intervalIntegrable hg s t)
        have hnorm := intervalIntegral.norm_integral_le_integral_norm
          (f := g) (μ := MeasureTheory.volume) hst
        have hsub := nonnegSubintervalIntegral_le
          (l := l) (s := s) (t := t) (r := r) hs.1 hst (by linarith [hs.2])
          gn hgn (fun y => norm_nonneg _)
        calc
          ‖f t - f s‖ = ‖∫ y in s..t, g y‖ := by rw [hFTC]
          _ ≤ ∫ y in s..t, ‖g y‖ := hnorm
          _ ≤ G := by simpa [G, gn] using hsub
      · have hderivTS : ∀ y ∈ Set.uIcc t s, HasDerivAt f (g y) y := by
          intro y hy
          have hyTS : y ∈ Set.Icc t s := by simpa [Set.uIcc_of_le hts] using hy
          have hyCell : y ∈ Set.Icc (t - 1 / 2) (t + 1 / 2) := by
            constructor
            · exact le_trans (by linarith) hyTS.1
            · exact le_trans hyTS.2 (by dsimp [r] at hs; exact hs.2)
          exact hderiv y hyCell
        have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderivTS
          (Continuous.intervalIntegrable hg t s)
        have hnorm := intervalIntegral.norm_integral_le_integral_norm
          (f := g) (μ := MeasureTheory.volume) hts
        have hsub := nonnegSubintervalIntegral_le
          (l := l) (s := t) (t := s) (r := r) (by linarith) hts hs.2
          gn hgn (fun y => norm_nonneg _)
        have hrev : f t - f s = -(f s - f t) := by abel
        calc
          ‖f t - f s‖ = ‖f s - f t‖ := by rw [hrev, norm_neg]
          _ = ‖∫ y in t..s, g y‖ := by rw [hFTC]
          _ ≤ ∫ y in t..s, ‖g y‖ := hnorm
          _ ≤ G := by simpa [G, gn] using hsub
    have htri : ‖f t‖ ≤ ‖f s‖ + ‖f t - f s‖ := by
      have heq : f t = (f t - f s) + f s := by abel
      calc
        ‖f t‖ = ‖(f t - f s) + f s‖ := congrArg norm heq
        _ ≤ ‖f t - f s‖ + ‖f s‖ := norm_add_le _ _
        _ = ‖f s‖ + ‖f t - f s‖ := by ring
    exact le_trans htri (by nlinarith)
  have hpointAverage : ‖f t‖ ≤ A + G := by
    have hmono :
        (∫ s in l..r, ‖f t‖) ≤
          ∫ s in l..r, ‖f s‖ + G := by
      apply intervalIntegral.integral_mono_on hlr'
        (Continuous.intervalIntegrable (continuous_const : Continuous fun _ : ℝ => ‖f t‖) l r)
        (Continuous.intervalIntegrable (hfn.add continuous_const) l r)
      intro s hs
      have hsCell : s ∈ Set.Icc l r := ⟨hs.1, hs.2⟩
      simpa [fn, G] using hpoint s hsCell
    have hleft : (∫ s in l..r, ‖f t‖) = ‖f t‖ := by
      simp [intervalIntegral.integral_const, hlen']
    have hright : (∫ s in l..r, ‖f s‖ + G) = A + G := by
      rw [intervalIntegral.integral_add hfnInt (intervalIntegrable_const)]
      simp [A, G, fn, intervalIntegral.integral_const, hlen']
    linarith
  have hsq : ‖f t‖ ^ 2 ≤ 2 * A ^ 2 + 2 * G ^ 2 := by
    have h1 : ‖f t‖ ^ 2 ≤ (A + G) ^ 2 := by
      nlinarith [hpointAverage, norm_nonneg (f t), hAnonneg, hGnonneg]
    nlinarith [h1, sq_nonneg (A - G)]
  have hsumInt :
      (∫ y in l..r, (fn y) ^ 2) + ∫ y in l..r, (gn y) ^ 2 =
        ∫ y in l..r, ((fn y) ^ 2 + (gn y) ^ 2) := by
    rw [intervalIntegral.integral_add hfnSqInt hgnSqInt]
  calc
    ‖f t‖ ^ 2 ≤ 2 * A ^ 2 + 2 * G ^ 2 := hsq
    _ ≤ 2 * (∫ y in l..r, (fn y) ^ 2) +
        2 * (∫ y in l..r, (gn y) ^ 2) := by nlinarith [hAsq, hGsq]
    _ = 2 * (∫ y in l..r, ((fn y) ^ 2 + (gn y) ^ 2)) := by
      rw [← hsumInt]
      ring
    _ = 2 * (∫ y in (t - 1 / 2)..(t + 1 / 2),
          (‖f y‖ ^ 2 + ‖g y‖ ^ 2)) := by rfl

private lemma separatedCellIntegralContract (T : Finset ℝ) (a b : ℝ)
    (hab : a ≤ b)
    (hT : ∀ t ∈ T, a ≤ t ∧ t ≤ b)
    (hsep : ∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ ≠ t₂ → 1 ≤ |t₁ - t₂|)
    (F : ℝ → ℝ) (hF : Continuous F) (hFnonneg : ∀ y, 0 ≤ F y) :
    (∑ t ∈ T, ∫ y in (t - 1 / 2)..(t + 1 / 2), F y) ≤
      ∫ y in (a - 1 / 2)..(b + 1 / 2), F y := by
  classical
  let cell : ℝ → Set ℝ := fun t => Set.Ioo (t - 1 / 2) (t + 1 / 2)
  let A : ℝ := a - 1 / 2
  let B : ℝ := b + 1 / 2
  have hAB : A ≤ B := by dsimp [A, B]; linarith
  have hdisj : (T : Set ℝ).PairwiseDisjoint cell := by
    intro t ht s hs hne
    apply Set.disjoint_left.mpr
    intro y hyt hys
    rcases Set.mem_Ioo.mp hyt with ⟨hytL, hytR⟩
    rcases Set.mem_Ioo.mp hys with ⟨hysL, hysR⟩
    rcases lt_or_gt_of_ne hne with hts | hst
    · have hgap : 1 ≤ s - t := by
        have h := hsep t ht s hs hne
        rw [abs_of_nonpos (sub_nonpos.mpr hts.le)] at h
        linarith
      have hoverlap : s - 1 / 2 < t + 1 / 2 := lt_trans hysL hytR
      linarith
    · have hgap : 1 ≤ t - s := by
        have h := hsep s hs t ht hne.symm
        rw [abs_of_nonpos (sub_nonpos.mpr hst.le)] at h
        linarith
      have hoverlap : t - 1 / 2 < s + 1 / 2 := lt_trans hytL hysR
      linarith
  have hsubset : (⋃ t ∈ (T : Set ℝ), cell t) ⊆ Set.Ioo A B := by
    intro y hy
    simp only [Set.mem_iUnion] at hy
    obtain ⟨t, htT, hy⟩ := hy
    rcases Set.mem_Ioo.mp hy with ⟨hyL, hyR⟩
    rcases hT t htT with ⟨hat, htb⟩
    constructor <;> dsimp [A, B] <;> linarith
  have hBigInt : IntegrableOn F (Set.Ioo A B) MeasureTheory.volume := by
    have hIcc : IntegrableOn F (Set.Icc A B) MeasureTheory.volume :=
      hF.continuousOn.integrableOn_Icc
    exact hIcc.mono_set (by intro y hy; exact ⟨hy.1.le, hy.2.le⟩)
  have hBigNonneg : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioo A B)] F :=
    Filter.Eventually.of_forall hFnonneg
  have hCellInt : ∀ t ∈ T, IntegrableOn F (cell t) MeasureTheory.volume := by
    intro t ht
    have hIcc : IntegrableOn F (Set.Icc (t - 1 / 2) (t + 1 / 2)) MeasureTheory.volume :=
      hF.continuousOn.integrableOn_Icc
    exact hIcc.mono_set (by
      intro y hy
      have hy' := Set.mem_Ioo.mp hy
      exact ⟨hy'.1.le, hy'.2.le⟩)
  have hCells :
      ∫ y in ⋃ t ∈ (T : Set ℝ), cell t, F y = ∑ t ∈ T, ∫ y in cell t, F y :=
    MeasureTheory.integral_biUnion_finset T (fun _ _ => measurableSet_Ioo) hdisj hCellInt
  have hCellEq (t : ℝ) :
      (∫ y in (t - 1 / 2)..(t + 1 / 2), F y) = ∫ y in cell t, F y := by
    have hwidth : t - 1 / 2 ≤ t + 1 / 2 := by linarith
    rw [intervalIntegral.integral_of_le hwidth, integral_Ioc_eq_integral_Ioo]
  have hsumEq :
      (∑ t ∈ T, ∫ y in cell t, F y) =
        ∑ t ∈ T, ∫ y in (t - 1 / 2)..(t + 1 / 2), F y := by
    apply Finset.sum_congr rfl
    intro t ht
    exact (hCellEq t).symm
  have hmono :
      (∫ y in ⋃ t ∈ (T : Set ℝ), cell t, F y) ≤ ∫ y in Set.Ioo A B, F y :=
    setIntegral_mono_set hBigInt hBigNonneg hsubset.eventuallySubset
  have hBigEq :
      (∫ y in A..B, F y) = ∫ y in Set.Ioo A B, F y := by
    rw [intervalIntegral.integral_of_le hAB, integral_Ioc_eq_integral_Ioo]
  calc
    _ = ∫ y in ⋃ t ∈ (T : Set ℝ), cell t, F y := (hCells.trans hsumEq).symm
    _ ≤ ∫ y in Set.Ioo A B, F y := hmono
    _ = ∫ y in (a - 1 / 2)..(b + 1 / 2), F y := by
      rw [hBigEq]

private lemma exponentialIntegral_le_pairKernel (Y : ℕ) (a b : ℝ) (hab : a ≤ b)
    (m n : ℕ)
    (hm : m ∈ ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.positiveRange Y)
    (hn : n ∈ ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.positiveRange Y) :
    ‖∫ t in a..b, exponentialPhase
        (Real.log (m : ℝ) - Real.log (n : ℝ)) t‖ ≤
      dirichletPairKernel (b - a) (Y : ℝ) m n := by
  classical
  have hmInfo := Finset.mem_filter.mp hm
  have hnInfo := Finset.mem_filter.mp hn
  have hmPos : 1 ≤ m := hmInfo.2
  have hnPos : 1 ≤ n := hnInfo.2
  have hmY : m ≤ Y := Nat.le_of_lt_succ (Finset.mem_range.mp hmInfo.1)
  have hnY : n ≤ Y := Nat.le_of_lt_succ (Finset.mem_range.mp hnInfo.1)
  by_cases hmn : m = n
  · subst n
    have hconst : ∫ t in a..b, exponentialPhase 0 t = ((b - a : ℝ) : ℂ) := by
      simp [exponentialPhase, intervalIntegral.integral_const]
    have hnorm : ‖((b - a : ℝ) : ℂ)‖ = b - a := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)]
    have hArg : Real.log (m : ℝ) - Real.log (m : ℝ) = 0 := sub_self _
    rw [hArg, dirichletPairKernel, if_pos rfl, hconst]
    rw [hnorm]
  · have hcast : (m : ℝ) ≠ (n : ℝ) := by exact_mod_cast hmn
    have hgapAbs :
        (|(m : ℝ) - (n : ℝ)|) / (Y : ℝ) ≤
          |Real.log (m : ℝ) - Real.log (n : ℝ)| := by
      rcases lt_or_gt_of_ne hmn with h | h
      · have hlog := log_gap_lower m n Y hmPos h hnY
        have hgapNatPos : 0 < n - m := Nat.sub_pos_of_lt h
        have hYNatPos : 0 < Y := by omega
        have hlogPos : 0 < Real.log (n : ℝ) - Real.log (m : ℝ) := by
          have hpos : 0 < ((n - m : ℕ) : ℝ) / (Y : ℝ) :=
            div_pos (by exact_mod_cast hgapNatPos) (by exact_mod_cast hYNatPos)
          exact lt_of_lt_of_le hpos hlog
        have hgapCast : ((n - m : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) := by
          rw [Nat.cast_sub (Nat.le_of_lt h)]
        have hgapAbs : |(m : ℝ) - (n : ℝ)| = ((n - m : ℕ) : ℝ) := by
          rw [hgapCast, abs_of_nonpos]
          · ring
          · exact sub_nonpos.mpr (by exact_mod_cast h.le)
        calc
          |(m : ℝ) - (n : ℝ)| / (Y : ℝ) =
              ((n - m : ℕ) : ℝ) / (Y : ℝ) := by rw [hgapAbs]
          _ ≤ Real.log (n : ℝ) - Real.log (m : ℝ) := hlog
          _ = |Real.log (m : ℝ) - Real.log (n : ℝ)| := by
            rw [abs_of_nonpos (by linarith [hlogPos])]
            ring
      · have hlog := log_gap_lower n m Y hnPos h hmY
        have hgapNatPos : 0 < m - n := Nat.sub_pos_of_lt h
        have hYNatPos : 0 < Y := by omega
        have hlogPos : 0 < Real.log (m : ℝ) - Real.log (n : ℝ) := by
          have hpos : 0 < ((m - n : ℕ) : ℝ) / (Y : ℝ) :=
            div_pos (by exact_mod_cast hgapNatPos) (by exact_mod_cast hYNatPos)
          exact lt_of_lt_of_le hpos hlog
        have hgapCast : ((m - n : ℕ) : ℝ) = (m : ℝ) - (n : ℝ) := by
          rw [Nat.cast_sub (Nat.le_of_lt h)]
        have hmnR : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast h.le
        have hgapNonneg : 0 ≤ (m : ℝ) - (n : ℝ) := sub_nonneg.mpr hmnR
        have hgapAbs : |(m : ℝ) - (n : ℝ)| = ((m - n : ℕ) : ℝ) := by
          rw [hgapCast, abs_of_nonneg hgapNonneg]
        calc
          |(m : ℝ) - (n : ℝ)| / (Y : ℝ) =
              ((m - n : ℕ) : ℝ) / (Y : ℝ) := by rw [hgapAbs]
          _ ≤ Real.log (m : ℝ) - Real.log (n : ℝ) := hlog
          _ = |Real.log (m : ℝ) - Real.log (n : ℝ)| := by
            rw [abs_of_nonneg (le_of_lt hlogPos)]
    have hgapPos : 0 < |(m : ℝ) - (n : ℝ)| := abs_pos.mpr (sub_ne_zero.mpr hcast)
    have hdenPos : 0 < |Real.log (m : ℝ) - Real.log (n : ℝ)| :=
      lt_of_lt_of_le (div_pos hgapPos (by exact_mod_cast (show 0 < Y by omega))) hgapAbs
    have hu : Real.log (m : ℝ) - Real.log (n : ℝ) ≠ 0 := abs_pos.mp hdenPos
    have hkernel := exponentialPhase_integral_bound
      (Real.log (m : ℝ) - Real.log (n : ℝ)) a b hu hab
    have hrecip :
        1 / |Real.log (m : ℝ) - Real.log (n : ℝ)| ≤
          (Y : ℝ) / |(m : ℝ) - (n : ℝ)| := by
      have hpos : 0 < |(m : ℝ) - (n : ℝ)| / (Y : ℝ) :=
        div_pos hgapPos (by exact_mod_cast (show 0 < Y by omega))
      calc
        _ ≤ 1 / (|(m : ℝ) - (n : ℝ)| / (Y : ℝ)) :=
          one_div_le_one_div_of_le hpos hgapAbs
        _ = _ := by
          have hYpos : 0 < (Y : ℝ) := by exact_mod_cast (show 0 < Y by omega)
          field_simp [ne_of_gt hgapPos, ne_of_gt hYpos]
    rw [dirichletPairKernel, if_neg hmn]
    calc
      _ ≤ 2 / |Real.log (m : ℝ) - Real.log (n : ℝ)| := hkernel
      _ = 2 * (1 / |Real.log (m : ℝ) - Real.log (n : ℝ)|) := by ring
      _ ≤ 2 * ((Y : ℝ) / |(m : ℝ) - (n : ℝ)|) :=
        mul_le_mul_of_nonneg_left hrecip (by norm_num)
      _ = 2 * (Y : ℝ) / |(m : ℝ) - (n : ℝ)| := by ring

private lemma dirichletPolynomial_mean_square_bound (Y : ℕ) (coeff : ℕ → ℂ)
    (a b : ℝ) (hab : a ≤ b) :
    (∫ t in a..b, ‖dirichletPolynomial Y coeff t‖ ^ 2) ≤
      ((b - a) + 4 * (Y : ℝ) *
        (∑ n ∈ ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.positiveRange Y,
          (1 : ℝ) / (n : ℝ))) *
        ∑ n ∈ ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.positiveRange Y, ‖coeff n‖ ^ 2 := by
  classical
  let S := ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.positiveRange Y
  let D : ℝ := b - a
  let H : ℝ := ∑ n ∈ S, (1 : ℝ) / (n : ℝ)
  let K : ℕ → ℕ → ℝ := dirichletPairKernel D (Y : ℝ)
  let v : ℕ → ℝ := fun n => ‖coeff n‖
  have hD : 0 ≤ D := by dsimp [D]; exact sub_nonneg.mpr hab
  have hY : 0 ≤ (Y : ℝ) := Nat.cast_nonneg _
  have hK : ∀ m ∈ S, ∀ n ∈ S, 0 ≤ K m n := by
    intro m hm n hn
    exact dirichletPairKernel_nonneg D (Y : ℝ) hD hY m n
  have hsymm : ∀ m ∈ S, ∀ n ∈ S, K m n = K n m := by
    intro m hm n hn
    exact dirichletPairKernel_symmetric D (Y : ℝ) m n
  have hrow : ∀ m ∈ S, (∑ n ∈ S, K m n) ≤ D + 4 * (Y : ℝ) * H := by
    intro m hm
    have h := dirichletPairKernel_rowBound Y a b hab m hm
    simpa [K, D, H, S] using h
  have hterm (m : ℕ) (hm : m ∈ S) (n : ℕ) (hn : n ∈ S) :
      (coeff m * conj (coeff n) *
        ∫ t in a..b, exponentialPhase (Real.log (m : ℝ) - Real.log (n : ℝ)) t).re ≤
      v m * v n * K m n := by
    have hkernel := exponentialIntegral_le_pairKernel Y a b hab m n hm hn
    calc
      _ ≤ ‖coeff m * conj (coeff n) *
          ∫ t in a..b, exponentialPhase (Real.log (m : ℝ) - Real.log (n : ℝ)) t‖ :=
        Complex.re_le_norm _
      _ = ‖coeff m‖ * ‖coeff n‖ *
          ‖∫ t in a..b, exponentialPhase (Real.log (m : ℝ) - Real.log (n : ℝ)) t‖ := by
        simp only [norm_mul, Complex.norm_conj]
      _ ≤ v m * v n * K m n := by
        dsimp [v, K]
        exact mul_le_mul_of_nonneg_left hkernel (by positivity)
  have hquad := symmetricRowQuadraticBound S K v (D + 4 * (Y : ℝ) * H)
    hK hsymm hrow
  calc
    _ = ∑ m ∈ S, ∑ n ∈ S,
          (coeff m * conj (coeff n) *
            ∫ t in a..b,
              exponentialPhase (Real.log (m : ℝ) - Real.log (n : ℝ)) t).re :=
      dirichletPolynomial_integral_expansion Y coeff a b hab
    _ ≤ ∑ m ∈ S, ∑ n ∈ S, v m * v n * K m n := by
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum
      intro n hn
      exact hterm m hm n hn
    _ ≤ (D + 4 * (Y : ℝ) * H) * ∑ n ∈ S, (v n) ^ 2 := hquad
    _ = ((b - a) + 4 * (Y : ℝ) *
        (∑ n ∈ ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.positiveRange Y,
          (1 : ℝ) / (n : ℝ))) *
        ∑ n ∈ ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.positiveRange Y, ‖coeff n‖ ^ 2 := by
      simp [D, H, S, v]

/-- Integers in a real interval that are rough above `W`. -/
noncomputable def roughIntegersInInterval (lo hi W : ℝ) : Finset ℕ :=
  (Finset.range (⌊hi⌋₊ + 1)).filter fun n => lo ≤ (n : ℝ) ∧ (n : ℝ) ≤ hi ∧ roughAbove n W

/-- Rough integers in an interval occupying one specified residue class. -/
noncomputable def roughResidueCount (lo hi W : ℝ) (d : ℕ) (b : ZMod d) : ℝ :=
  (((Finset.range (⌊hi⌋₊ + 1)).filter fun (n : ℕ) =>
    lo ≤ (n : ℝ) ∧ (n : ℝ) ≤ hi ∧ roughAbove n W ∧ (n : ZMod d) = b).card : ℝ)

/-- `t2:pd.moment-bounds` — PD `02-preliminaries.tex:73-114`, Lemma 2.2. Correction 1 from
review lane `rev-b` excludes the zero index and requires positive polynomial length. -/
theorem moment_bounds :
    (∀ k : ℕ, ∃ Ck : ℝ, 0 < Ck ∧ ∃ Y₀ : ℝ, 2 ≤ Y₀ ∧
      ∀ Y : ℝ, Y₀ ≤ Y →
        (∑ n ∈ Finset.range (⌊Y⌋₊ + 1), (tau n : ℝ) ^ k) ≤
            Ck * Y * Real.rpow (Real.log (2 * Y)) Ck ∧
        (∑ n ∈ Finset.range (⌊Y⌋₊ + 1), (tau n : ℝ) ^ k / (n + 1 : ℝ)) ≤
            Ck * Real.rpow (Real.log (2 * Y)) Ck) ∧
    (∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ Y : ℕ, 1 ≤ Y → ∀ coeff : ℕ → ℂ, ∀ a b : ℝ, a ≤ b →
        ∫ t in a..b, ‖dirichletPolynomial Y coeff t‖ ^ 2 ≤
          C₀ * (b - a + (Y : ℝ) * Real.log (2 * (Y : ℝ))) *
            ∑ n ∈ (Finset.range (Y + 1)).filter (fun n => 1 ≤ n), ‖coeff n‖ ^ 2) ∧
    (∃ C₁ : ℝ, 0 < C₁ ∧
      ∀ Y : ℕ, 1 ≤ Y → ∀ coeff : ℕ → ℂ, ∀ a b : ℝ, a ≤ b →
        ∀ T : Finset ℝ,
          (∀ t ∈ T, a ≤ t ∧ t ≤ b) →
          (∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ ≠ t₂ → 1 ≤ |t₁ - t₂|) →
            (∑ t ∈ T, ‖dirichletPolynomial Y coeff t‖ ^ 2) ≤
              C₁ * (b - a + 1 + (Y : ℝ) * Real.log (2 * (Y : ℝ))) *
                Real.rpow (Real.log (2 * (Y : ℝ))) 2 *
            ∑ n ∈ (Finset.range (Y + 1)).filter (fun n => 1 ≤ n), ‖coeff n‖ ^ 2) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k
    let R : ℕ := 2 ^ k
    let Ck : ℝ := (2 : ℝ) ^ R + (R : ℝ) + 2
    refine ⟨Ck, ?_, 2, by norm_num, ?_⟩
    · dsimp [Ck]
      positivity
    · intro Y hY
      let N : ℕ := ⌊Y⌋₊
      let B : ℝ := Real.log (2 * Y)
      have hYpos : 0 < Y := by linarith
      have hNle : (N : ℝ) ≤ Y := by
        dsimp [N]
        exact Nat.floor_le hYpos.le
      have hN2 : 2 ≤ N := by
        dsimp [N]
        exact Nat.le_floor hY
      have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
        have h := Real.le_log_one_add_of_nonneg (x := (1 : ℝ)) (by norm_num)
        norm_num at h
        linarith
      have hlogY : Real.log 2 ≤ Real.log Y :=
        Real.log_le_log (by norm_num) hY
      have hBlog : B = Real.log 2 + Real.log Y := by
        dsimp [B]
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hYpos)]
      have hB1 : 1 ≤ B := by
        rw [hBlog]
        linarith [hlog2, hlogY]
      have hlogN : Real.log (N : ℝ) ≤ Real.log Y := by
        apply Real.log_le_log
        · exact_mod_cast (show 0 < N by omega)
        · exact hNle
      let H : ℝ := ∑ n ∈ ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.positiveRange N,
        ((n : ℝ)⁻¹)
      have hHle : H ≤ 2 * B := by
        have hH := ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.harmonicRange_le_one_add_log N
        dsimp [H] at hH ⊢
        calc
          _ ≤ 1 + Real.log (N : ℝ) := hH
          _ ≤ 1 + Real.log Y := by linarith
          _ ≤ 2 * B := by rw [hBlog]; nlinarith [hlog2, hlogY]
      have hHnonneg : 0 ≤ H := by
        dsimp [H]
        apply Finset.sum_nonneg
        intro n hn
        positivity
      have hHpow : H ^ R ≤ (2 * B) ^ R :=
        pow_le_pow_left₀ hHnonneg hHle R
      have hBpow : 1 ≤ B ^ R := one_le_pow₀ hB1
      have hPowExpand : (2 * B) ^ R = (2 : ℝ) ^ R * B ^ R := by rw [mul_pow]
      have hMain : (N : ℝ) * H ^ R ≤ Y * (2 * B) ^ R := by
        calc
          _ ≤ (N : ℝ) * (2 * B) ^ R :=
            mul_le_mul_of_nonneg_left hHpow (Nat.cast_nonneg _)
          _ ≤ Y * (2 * B) ^ R :=
            mul_le_mul_of_nonneg_right hNle (by positivity)
      have hCcoeff : 1 + (2 : ℝ) ^ R ≤ Ck := by
        dsimp [Ck]
        linarith
      have hCexp : (R : ℝ) ≤ Ck := by
        dsimp [Ck]
        have hpowNonneg : 0 ≤ (2 : ℝ) ^ R := by positivity
        linarith
      have hRpow : B ^ R ≤ Real.rpow B Ck := by
        calc
          B ^ R = Real.rpow B (R : ℝ) := (Real.rpow_natCast B R).symm
          _ ≤ Real.rpow B Ck := Real.rpow_le_rpow_of_exponent_le hB1 hCexp
      have hUnweighted :
          (∑ n ∈ Finset.range (N + 1),
            (ArtinPrimitiveRoots.TypeII.PD.tau n : ℝ) ^ k) ≤
            (1 + (2 : ℝ) ^ R) * Y * B ^ R := by
        have hbase := ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.sum_tau_pow_le k N
        have hbase' :
            (∑ n ∈ Finset.range (N + 1),
              (ArtinPrimitiveRoots.TypeII.PD.tau n : ℝ) ^ k) ≤ 1 + (N : ℝ) * H ^ R := by
          simpa [H, R] using hbase
        have hfirst :
            (∑ n ∈ Finset.range (N + 1),
              (ArtinPrimitiveRoots.TypeII.PD.tau n : ℝ) ^ k) ≤
                1 + Y * (2 * B) ^ R := by nlinarith [hbase', hMain]
        rw [hPowExpand] at hfirst
        have hYB : 1 ≤ Y * B ^ R := by nlinarith [hY, hBpow]
        calc
          _ ≤ 1 + Y * ((2 : ℝ) ^ R * B ^ R) := hfirst
          _ = 1 + Y * (2 : ℝ) ^ R * B ^ R := by ring
          _ ≤ Y * B ^ R + Y * (2 : ℝ) ^ R * B ^ R :=
            add_le_add_left hYB _
          _ = (1 + (2 : ℝ) ^ R) * Y * B ^ R := by ring
      have hU :
          (∑ n ∈ Finset.range (N + 1),
            (ArtinPrimitiveRoots.TypeII.PD.tau n : ℝ) ^ k) ≤
            Ck * Y * Real.rpow B Ck := by
        calc
          _ ≤ (1 + (2 : ℝ) ^ R) * Y * B ^ R := hUnweighted
          _ ≤ Ck * Y * B ^ R := by
            calc
              (1 + (2 : ℝ) ^ R) * Y * B ^ R =
                  ((1 + (2 : ℝ) ^ R) * Y) * B ^ R := by ring
              _ ≤ (Ck * Y) * B ^ R := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hCcoeff (le_of_lt hYpos)) (by positivity)
              _ = Ck * Y * B ^ R := by ring
          _ ≤ Ck * Y * Real.rpow B Ck := by
            apply mul_le_mul_of_nonneg_left hRpow
            positivity
      have hWeighted :
          (∑ n ∈ Finset.range (N + 1),
            (ArtinPrimitiveRoots.TypeII.PD.tau n : ℝ) ^ k / ((n : ℝ) + 1)) ≤
            Ck * Real.rpow B Ck := by
        have hbase := ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.sum_tau_pow_div_succ_le k N
        have hbase' :
            (∑ n ∈ Finset.range (N + 1),
              (ArtinPrimitiveRoots.TypeII.PD.tau n : ℝ) ^ k / ((n : ℝ) + 1)) ≤
                1 + H ^ R := by
          simpa [H, R] using hbase
        have hfirst :
            (∑ n ∈ Finset.range (N + 1),
              (ArtinPrimitiveRoots.TypeII.PD.tau n : ℝ) ^ k / ((n : ℝ) + 1)) ≤
                1 + (2 * B) ^ R := by nlinarith [hbase', hHpow]
        rw [hPowExpand] at hfirst
        have hlarge :
            1 + (2 : ℝ) ^ R * B ^ R ≤ (1 + (2 : ℝ) ^ R) * B ^ R := by
          calc
            _ = 1 + (2 : ℝ) ^ R * B ^ R := by ring
            _ ≤ B ^ R + (2 : ℝ) ^ R * B ^ R :=
              add_le_add_left hBpow _
            _ = _ := by ring
        calc
          _ ≤ 1 + (2 : ℝ) ^ R * B ^ R := hfirst
          _ ≤ (1 + (2 : ℝ) ^ R) * B ^ R := hlarge
          _ ≤ Ck * B ^ R :=
            mul_le_mul_of_nonneg_right hCcoeff (by positivity)
          _ ≤ Ck * Real.rpow B Ck :=
            mul_le_mul_of_nonneg_left hRpow (by dsimp [Ck]; positivity)
      constructor
      · simpa [N, B, Ck] using hU
      · simpa [N, B, Ck] using hWeighted
  · refine ⟨8, by norm_num, ?_⟩
    intro Y hY coeff a b hab
    let B : ℝ := Real.log (2 * (Y : ℝ))
    let H : ℝ :=
      ∑ n ∈ ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.positiveRange Y, ((n : ℝ)⁻¹)
    let D : ℝ := b - a
    let E : ℝ :=
      ∑ n ∈ ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.positiveRange Y, ‖coeff n‖ ^ 2
    have hYpos : 0 < (Y : ℝ) := by exact_mod_cast (show 0 < Y by omega)
    have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have h := Real.le_log_one_add_of_nonneg (x := (1 : ℝ)) (by norm_num)
      norm_num at h
      linarith
    have hlogY : 0 ≤ Real.log (Y : ℝ) := Real.log_nonneg (by exact_mod_cast hY)
    have hBlog : B = Real.log 2 + Real.log (Y : ℝ) := by
      dsimp [B]
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hYpos)]
    have hHle : H ≤ 2 * B := by
      have h := ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.harmonicRange_le_one_add_log Y
      dsimp [H] at h ⊢
      calc
        _ ≤ 1 + Real.log (Y : ℝ) := h
        _ ≤ 2 * B := by rw [hBlog]; linarith [hlog2]
    have hD : 0 ≤ D := by dsimp [D]; exact sub_nonneg.mpr hab
    have hE : 0 ≤ E := by
      dsimp [E]
      apply Finset.sum_nonneg
      intro n hn
      positivity
    have hMean :
        (∫ t in a..b, ‖dirichletPolynomial Y coeff t‖ ^ 2) ≤
          (D + 4 * (Y : ℝ) * H) * E := by
      simpa [D, H, E] using
        dirichletPolynomial_mean_square_bound Y coeff a b hab
    have hmult : 4 * (Y : ℝ) * H ≤ 8 * (Y : ℝ) * B := by
      calc
        _ ≤ 4 * (Y : ℝ) * (2 * B) :=
          mul_le_mul_of_nonneg_left hHle (by positivity)
        _ = 8 * (Y : ℝ) * B := by ring
    have hCoeffOne : D + 4 * (Y : ℝ) * H ≤ D + 8 * (Y : ℝ) * B := by
      linarith [hmult]
    have hCoeffTwo : D + 8 * (Y : ℝ) * B ≤ 8 * (D + (Y : ℝ) * B) := by
      nlinarith [hD]
    calc
      _ ≤ (D + 4 * (Y : ℝ) * H) * E := hMean
      _ ≤ (D + 8 * (Y : ℝ) * B) * E :=
        mul_le_mul_of_nonneg_right hCoeffOne hE
      _ ≤ 8 * (D + (Y : ℝ) * B) * E :=
        mul_le_mul_of_nonneg_right hCoeffTwo hE
  · refine ⟨80, by norm_num, ?_⟩
    intro Y hY coeff a b hab T hT hsep
    let S := ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.positiveRange Y
    let L : ℝ := Real.log (2 * (Y : ℝ))
    let H : ℝ := ∑ n ∈ S, ((n : ℝ)⁻¹)
    let leftExt : ℝ := a - 1 / 2
    let rightExt : ℝ := b + 1 / 2
    let M : ℝ := (b - a + 1) + (Y : ℝ) * L
    let C : ℝ := (rightExt - leftExt) + 4 * (Y : ℝ) * H
    let E : ℝ := ∑ n ∈ S, ‖coeff n‖ ^ 2
    let coeffD : ℕ → ℂ := differentiatedCoeff coeff
    let ED : ℝ := ∑ n ∈ S, ‖coeffD n‖ ^ 2
    let P : ℝ → ℂ := dirichletPolynomial Y coeff
    let Q : ℝ → ℂ := dirichletPolynomial Y coeffD
    let F : ℝ → ℝ := fun y => ‖P y‖ ^ 2 + ‖Q y‖ ^ 2
    have hYpos : 0 < (Y : ℝ) := by exact_mod_cast (show 0 < Y by omega)
    have hY1 : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
    have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have h := Real.le_log_one_add_of_nonneg (x := (1 : ℝ)) (by norm_num)
      norm_num at h
      linarith
    have hlogY : 0 ≤ Real.log (Y : ℝ) := Real.log_nonneg hY1
    have hLexpr : L = Real.log 2 + Real.log (Y : ℝ) := by
      dsimp [L]
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hYpos)]
    have hLhalf : (1 / 2 : ℝ) ≤ L := by rw [hLexpr]; linarith
    have hHle : H ≤ 2 * L := by
      have h := ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.harmonicRange_le_one_add_log Y
      dsimp [H, S] at h ⊢
      calc
        _ ≤ 1 + Real.log (Y : ℝ) := h
        _ ≤ 2 * L := by rw [hLexpr]; linarith [hlog2]
    have hExt : leftExt ≤ rightExt := by dsimp [leftExt, rightExt]; linarith
    have hExtLength : rightExt - leftExt = b - a + 1 := by
      dsimp [leftExt, rightExt]
      ring
    have hPcont : Continuous P := by
      dsimp [P]
      unfold dirichletPolynomial
      fun_prop
    have hQcont : Continuous Q := by
      dsimp [Q, coeffD]
      unfold dirichletPolynomial
      fun_prop
    have hFcont : Continuous F := by
      dsimp [F]
      exact (hPcont.norm.pow 2).add (hQcont.norm.pow 2)
    have hFnonneg : ∀ y, 0 ≤ F y := by
      intro y
      dsimp [F]
      positivity
    have hContract := separatedCellIntegralContract T a b hab hT hsep F hFcont hFnonneg
    have hCellPoint (t : ℝ) (ht : t ∈ T) :
        ‖P t‖ ^ 2 ≤ 2 * ∫ y in (t - 1 / 2)..(t + 1 / 2), F y := by
      have hderiv : ∀ y ∈ Set.Icc (t - 1 / 2) (t + 1 / 2), HasDerivAt P (Q y) y := by
        intro y hy
        dsimp [P, Q, coeffD]
        exact dirichletPolynomial_hasDerivAt Y coeff y
      simpa [F] using unitCellPointBound P Q t hderiv hPcont hQcont
    have hSampleToCells :
        (∑ t ∈ T, ‖P t‖ ^ 2) ≤ 2 *
          ∑ t ∈ T, ∫ y in (t - 1 / 2)..(t + 1 / 2), F y := by
      calc
        _ ≤ ∑ t ∈ T, 2 * ∫ y in (t - 1 / 2)..(t + 1 / 2), F y :=
          Finset.sum_le_sum fun t ht => hCellPoint t ht
        _ = 2 * ∑ t ∈ T, ∫ y in (t - 1 / 2)..(t + 1 / 2), F y := by
          rw [Finset.mul_sum]
    have hSample :
        (∑ t ∈ T, ‖P t‖ ^ 2) ≤ 2 * ∫ y in leftExt..rightExt, F y := by
      calc
        _ ≤ 2 * ∑ t ∈ T, ∫ y in (t - 1 / 2)..(t + 1 / 2), F y := hSampleToCells
        _ ≤ 2 * ∫ y in leftExt..rightExt, F y :=
          mul_le_mul_of_nonneg_left hContract (by norm_num)
    have hPInt : IntervalIntegrable (fun y => ‖P y‖ ^ 2) MeasureTheory.volume leftExt rightExt :=
      Continuous.intervalIntegrable (hPcont.norm.pow 2) leftExt rightExt
    have hQInt : IntervalIntegrable (fun y => ‖Q y‖ ^ 2) MeasureTheory.volume leftExt rightExt :=
      Continuous.intervalIntegrable (hQcont.norm.pow 2) leftExt rightExt
    have hFInt : (∫ y in leftExt..rightExt, F y) =
        (∫ y in leftExt..rightExt, ‖P y‖ ^ 2) +
          ∫ y in leftExt..rightExt, ‖Q y‖ ^ 2 := by
      dsimp [F]
      exact intervalIntegral.integral_add hPInt hQInt
    have hCoeffNorm (n : ℕ) : ‖differentiatedCoeff coeff n‖ =
        ‖coeff n‖ * |Real.log (n : ℝ)| := by
      calc
        ‖differentiatedCoeff coeff n‖ =
            ‖coeff n‖ * ‖(Real.log (n : ℝ) : ℂ)‖ * ‖Complex.I‖ := by
          simp [differentiatedCoeff, norm_mul, mul_assoc]
        _ = ‖coeff n‖ * |Real.log (n : ℝ)| := by
          rw [Complex.norm_real, Real.norm_eq_abs]
          simp
    have hED : ED ≤ L ^ 2 * E := by
      calc
        ED ≤ ∑ n ∈ S, L ^ 2 * ‖coeff n‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro n hn
          have hnInfo := Finset.mem_filter.mp hn
          have hnPos : 0 < n := by omega
          have hnY : n ≤ Y := Nat.le_of_lt_succ (Finset.mem_range.mp hnInfo.1)
          have hlogNonneg : 0 ≤ Real.log (n : ℝ) :=
            Real.log_nonneg (by exact_mod_cast hnInfo.2)
          have hlogLe : Real.log (n : ℝ) ≤ Real.log (Y : ℝ) := by
            apply Real.log_le_log
            · exact_mod_cast hnPos
            · exact_mod_cast hnY
          have hlogBound : |Real.log (n : ℝ)| ≤ L := by
            rw [abs_of_nonneg hlogNonneg]
            calc
              _ ≤ Real.log (Y : ℝ) := hlogLe
              _ ≤ L := by rw [hLexpr]; linarith [hlog2]
          have hmul : ‖coeff n‖ * |Real.log (n : ℝ)| ≤ ‖coeff n‖ * L :=
            mul_le_mul_of_nonneg_left hlogBound (norm_nonneg _)
          calc
            ‖differentiatedCoeff coeff n‖ ^ 2 =
                (‖coeff n‖ * |Real.log (n : ℝ)|) ^ 2 := by rw [hCoeffNorm]
            _ ≤ (‖coeff n‖ * L) ^ 2 :=
              pow_le_pow_left₀ (by positivity) hmul 2
            _ = L ^ 2 * ‖coeff n‖ ^ 2 := by ring
        _ = L ^ 2 * E := by
          dsimp [E]
          rw [← Finset.mul_sum]
    have hMeanP :
        (∫ y in leftExt..rightExt, ‖P y‖ ^ 2) ≤ C * E := by
      have h := dirichletPolynomial_mean_square_bound Y coeff leftExt rightExt hExt
      simpa [P, C, H, E, S] using h
    have hMeanQ :
        (∫ y in leftExt..rightExt, ‖Q y‖ ^ 2) ≤ C * ED := by
      have h := dirichletPolynomial_mean_square_bound Y coeffD leftExt rightExt hExt
      simpa [Q, C, H, ED, S] using h
    have hCnonneg : 0 ≤ C := by
      dsimp [C]
      have hlenNonneg : 0 ≤ rightExt - leftExt := sub_nonneg.mpr hExt
      positivity
    have hCbound : C ≤ 8 * M := by
      have hHterm : 4 * (Y : ℝ) * H ≤ 8 * (Y : ℝ) * L := by
        calc
          _ ≤ 4 * (Y : ℝ) * (2 * L) :=
            mul_le_mul_of_nonneg_left hHle (by positivity)
          _ = 8 * (Y : ℝ) * L := by ring
      have hlenpos : 0 ≤ b - a + 1 := by linarith [hab]
      calc
        C ≤ (rightExt - leftExt) + 8 * (Y : ℝ) * L := by
          dsimp [C]
          linarith [hHterm]
        _ = (b - a + 1) + 8 * (Y : ℝ) * L := by rw [hExtLength]
        _ ≤ 8 * M := by
          dsimp [M]
          nlinarith [hlenpos, hlog2]
    have hLone : (1 / 2 : ℝ) ≤ L := by rw [hLexpr]; linarith [hlog2, hlogY]
    have hOnePlus : 1 + L ^ 2 ≤ 5 * L ^ 2 := by
      nlinarith [sq_nonneg (L - 1 / 2)]
    have hBoth : (∫ y in leftExt..rightExt, F y) ≤ C * (1 + L ^ 2) * E := by
      rw [hFInt]
      calc
        _ ≤ C * E + C * ED := add_le_add hMeanP hMeanQ
        _ ≤ C * E + C * (L ^ 2 * E) := by
          have h := mul_le_mul_of_nonneg_left hED hCnonneg
          nlinarith [h]
        _ = C * (1 + L ^ 2) * E := by ring
    have hMnonneg : 0 ≤ M := by
      dsimp [M]
      have hDpos : 0 ≤ b - a + 1 := by linarith [hab]
      have hLpos : 0 ≤ L := by linarith [hLone]
      positivity
    have hE : 0 ≤ E := by
      dsimp [E]
      apply Finset.sum_nonneg
      intro n hn
      positivity
    have hFBound :
        (∫ y in leftExt..rightExt, F y) ≤ 40 * M * L ^ 2 * E := by
      calc
        _ ≤ C * (1 + L ^ 2) * E := hBoth
        _ ≤ 8 * M * (1 + L ^ 2) * E := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hCbound (by positivity)) hE
        _ ≤ 40 * M * L ^ 2 * E := by
          calc
            _ ≤ (8 * M) * (5 * L ^ 2) * E := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hOnePlus (by positivity)) hE
            _ = 40 * M * L ^ 2 * E := by ring
    have hSampleBound : (∑ t ∈ T, ‖P t‖ ^ 2) ≤ 80 * M * L ^ 2 * E := by
      calc
        _ ≤ 2 * ∫ y in leftExt..rightExt, F y := hSample
        _ ≤ 2 * (40 * M * L ^ 2 * E) :=
          mul_le_mul_of_nonneg_left hFBound (by norm_num)
        _ = 80 * M * L ^ 2 * E := by ring
    have hPowCast : (L : ℝ) ^ 2 = Real.rpow L (2 : ℝ) :=
      (Real.rpow_natCast L 2).symm
    have hSampleBoundRpow :
        (∑ t ∈ T, ‖P t‖ ^ 2) ≤ 80 * M * Real.rpow L (2 : ℝ) * E := by
      rw [← hPowCast]
      exact hSampleBound
    simpa [P, M, L, E, S,
      ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.positiveRange] using hSampleBoundRpow

private lemma nat_range_floor_le_real (r : ℝ) (hr : 0 ≤ r) {n : ℕ}
    (hn : n ∈ Finset.range (⌊r⌋₊ + 1)) : (n : ℝ) ≤ r := by
  have hnrange : n < ⌊r⌋₊ + 1 := Finset.mem_range.mp hn
  by_cases hn0 : n = 0
  · simp [hn0, hr]
  · have hnfloor : n ≤ ⌊r⌋₊ := by omega
    exact (Nat.le_floor_iff' hn0).mp hnfloor

private lemma rough_interval_residue_filter_eq (l r W : ℝ) (m : ℕ) (b : ZMod m)
    (hr : 0 ≤ r) :
    (Finset.range (⌊r⌋₊ + 1)).filter (fun n : ℕ =>
      l ≤ (n : ℝ) ∧ (n : ℝ) ≤ r ∧ roughAbove n W ∧ (n : ZMod m) = b) =
    (Finset.range (⌊r⌋₊ + 1)).filter (fun n : ℕ =>
      l ≤ (n : ℝ) ∧ roughAbove n W ∧ (n : ZMod m) = b) := by
  ext n
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hn, hl, _, hrough, hb⟩
    exact ⟨hn, hl, hrough, hb⟩
  · rintro ⟨hn, hl, hrough, hb⟩
    exact ⟨hn, hl, nat_range_floor_le_real r hr hn, hrough, hb⟩

private noncomputable def naturalAvoidingResidues (N m : ℕ) (b : ZMod m)
    (P : Finset ℕ) (l : ℝ) : Finset ℕ :=
  (Finset.range N).filter fun n =>
    l ≤ (n : ℝ) ∧ (n : ZMod m) = b ∧ ∀ p ∈ P, ¬ p ∣ n

private lemma nat_avoiding_residue_image (N m : ℕ) (b : ZMod m) (P : Finset ℕ)
    (l : ℝ) (hl : 0 ≤ l) :
    (naturalAvoidingResidues N m b P l).image (fun n : ℕ => (n : ℤ)) =
      (OAI.Erdos970.ErdosCoprimeResidueInterval.realCoprimeResidues
        1 m {b} l (N : ℝ)).filter
        (fun z : ℤ => ∀ p ∈ P, ¬ (p : ℤ) ∣ z) := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨n, hn, hzn⟩ := Finset.mem_image.mp hz
    subst z
    obtain ⟨hnrange, hnlow, hres, havoid⟩ := Finset.mem_filter.mp hn
    apply Finset.mem_filter.mpr
    constructor
    · rw [OAI.Erdos970.ErdosCoprimeResidueInterval.mem_realCoprimeResidues]
      refine ⟨hnlow, ?_, by simp, by simp [hres]⟩
      have hnlt : n < N := Finset.mem_range.mp hnrange
      exact_mod_cast hnlt
    · intro p hp hpz
      exact havoid p hp ((Int.natCast_dvd_natCast).mp hpz)
  · intro hz
    obtain ⟨hzresidues, hzavoid⟩ := Finset.mem_filter.mp hz
    rw [OAI.Erdos970.ErdosCoprimeResidueInterval.mem_realCoprimeResidues] at hzresidues
    rcases hzresidues with ⟨hzlow, hzupper, hcop, hzres⟩
    have hznonneg : 0 ≤ z := by exact_mod_cast hl.trans hzlow
    let n := z.toNat
    have hcast : (n : ℤ) = z := Int.toNat_of_nonneg hznonneg
    have hnlt : n < N := by
      have hzupperInt : z < (N : ℤ) := by exact_mod_cast hzupper
      rw [← hcast] at hzupperInt
      exact_mod_cast hzupperInt
    have hcastR : (n : ℝ) = (z : ℝ) := by exact_mod_cast hcast
    have hnlow : l ≤ (n : ℝ) := by rw [hcastR]; exact hzlow
    have hnres : (n : ZMod m) = b := by
      have hcastZMod : (n : ZMod m) = (z : ZMod m) := by
        have hh := congrArg (fun w : ℤ => (w : ZMod m)) hcast
        simpa only [Int.cast_natCast] using hh
      exact hcastZMod.trans (Finset.mem_singleton.mp hzres)
    have hnavoid : ∀ p ∈ P, ¬ p ∣ n := by
      intro p hp hpn
      apply hzavoid p hp
      rw [← hcast]
      exact Int.natCast_dvd_natCast.mpr hpn
    apply Finset.mem_image.mpr
    refine ⟨n, Finset.mem_filter.mpr ?_, hcast⟩
    exact ⟨Finset.mem_range.mpr hnlt, hnlow, hnres, hnavoid⟩

set_option maxHeartbeats 1000000 in
/-- `t2:pd.rough-counts` — PD `02-preliminaries.tex:175-235`, Lemma 2.5. -/
theorem rough_counts :
    ∀ δ C aExp A : ℝ, 0 < δ → 0 < C → 0 < aExp → aExp < 1 → 0 < A →
      ∃ C₀ x₀ : ℝ, 0 < C₀ ∧ 2 ≤ x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          let L := Real.log x
          let W := roughCutoff x
          ∀ H : ℝ, Real.rpow x δ ≤ H → H ≤ Real.rpow x C →
            ∀ l r : ℝ, H ≤ l → l ≤ r → r ≤ 2 * H →
              (|((roughIntegersInInterval l r W).card : ℝ) -
                roughSieveProduct W * (r - l + 1)| ≤ H * Real.rpow L (-A)) ∧
              (∀ d : ℕ, 1 ≤ d → (d : ℝ) ≤ Real.exp (Real.rpow L aExp) →
                roughAbove d W →
                ∀ b : ZMod d,
                  |roughResidueCount l r W d b -
                    roughSieveProduct W * (r - l + 1) / (d : ℝ)| ≤
                    (H / d) * Real.rpow L (-A)) ∧
              ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.rpow L C →
                ∀ χ : DirichletCharacter ℂ q,
                  ‖(∑ n ∈ (Finset.range (⌊r⌋₊ + 1)).filter (fun (n : ℕ) =>
                        l ≤ (n : ℝ) ∧ (n : ℝ) ≤ r ∧ roughAbove n W),
                      (χ (n : ZMod q) : ℂ)) -
                    (if χ = 1 then
                      (roughSieveProduct W * (r - l + 1) : ℝ) else 0 : ℂ)‖ ≤
                  H * Real.rpow L (-A) := by
  intro δ C aExp A hδ hC haExp haExp1 hA
  let aMod : ℝ := max aExp (1 / 2)
  have haModPos : 0 < aMod := by dsimp [aMod]; positivity
  have haModLt : aMod < 1 := by
    dsimp [aMod]
    exact max_lt_iff.mpr ⟨haExp1, by norm_num⟩
  let B : ℝ := A + C + 4
  have hBpos : 0 < B := by dsimp [B]; linarith
  have hB_A : A + 4 ≤ B := by dsimp [B]; linarith
  have hA_B : A ≤ B := by linarith [hB_A]
  obtain ⟨L₀, hL₀, hPrecision⟩ :=
    ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.exists_sieve_precision
      δ aMod B hδ haModPos haModLt (le_of_lt hBpos)
  have hLogGrowth : ∀ᶠ z : ℝ in Filter.atTop,
      C * Real.log z ≤ Real.rpow z (24 / 100 : ℝ) := by
    have hsmall := (isLittleO_log_rpow_atTop
      (show (0 : ℝ) < 24 / 100 by norm_num)).bound
      (show (0 : ℝ) < 1 / (C + 1) by positivity)
    filter_upwards [hsmall, Filter.eventually_ge_atTop (1 : ℝ)] with z hsmall hz
    have hnorm : |Real.log z| ≤ (1 / (C + 1)) *
        |Real.rpow z (24 / 100 : ℝ)| := by simpa using hsmall
    have hscaled : C * Real.log z ≤
        C * (Real.rpow z (24 / 100 : ℝ) / (C + 1)) := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hC)
      calc
        Real.log z ≤ (1 / (C + 1)) * |Real.rpow z (24 / 100 : ℝ)| := by
          rw [abs_of_nonneg (Real.log_nonneg hz)] at hnorm
          exact hnorm
        _ = (1 / (C + 1)) * Real.rpow z (24 / 100 : ℝ) := by
          have habs : |Real.rpow z (24 / 100 : ℝ)| =
              Real.rpow z (24 / 100 : ℝ) :=
            abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ z) _)
          rw [habs]
        _ = Real.rpow z (24 / 100 : ℝ) / (C + 1) := by ring
    calc
      C * Real.log z ≤ C * (Real.rpow z (24 / 100 : ℝ) / (C + 1)) := hscaled
      _ ≤ Real.rpow z (24 / 100 : ℝ) := by
        have hzpow : 0 ≤ Real.rpow z (24 / 100 : ℝ) :=
          Real.rpow_nonneg (by linarith : 0 ≤ z) _
        have hden : 0 < C + 1 := by linarith
        rw [show C * (Real.rpow z (24 / 100 : ℝ) / (C + 1)) =
          (C / (C + 1)) * Real.rpow z (24 / 100 : ℝ) by ring]
        exact mul_le_of_le_one_left hzpow (by
          rw [div_le_one hden]
          linarith)
  obtain ⟨L_W, hL_W⟩ := Filter.eventually_atTop.1 hLogGrowth
  let Lcut : ℝ := max (max 2 L₀) L_W
  let x₀ : ℝ := max 2 (Real.exp Lcut)
  refine ⟨1, x₀, by norm_num, le_max_left _ _, ?_⟩
  intro x hx
  dsimp
  intro H hHx hHX l r hl hlr hr
  let L : ℝ := Real.log x
  let W : ℝ := roughCutoff x
  let N : ℕ := ⌊r⌋₊ + 1
  let u : ℝ := N
  let P : Finset ℕ := primesUpTo W
  let S : ℝ := ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.sieveDepth L
  let V : ℝ := roughSieveProduct W
  let natResidueSet : (m : ℕ) → ZMod m → Finset ℕ := fun m b =>
    (Finset.range N).filter fun n =>
      l ≤ (n : ℝ) ∧ roughAbove n W ∧ (n : ZMod m) = b
  have hx0 : x₀ ≤ x := hx
  have hExpLe : Real.exp Lcut ≤ x :=
    (le_max_right 2 (Real.exp Lcut)).trans hx0
  have hLcutx : Lcut ≤ L := by
    have hh := Real.log_le_log (Real.exp_pos Lcut) hExpLe
    simpa [L] using hh
  have hL₀x' : L₀ ≤ Real.log x := by
    exact (le_trans (le_max_right 2 L₀) (le_max_left (max 2 L₀) L_W)).trans hLcutx
  have hPrecisionNow := hPrecision (Real.log x) hL₀x'
  have hL_Wx : L_W ≤ L := by
    exact (le_max_right (max 2 L₀) L_W).trans hLcutx
  have hx2 : 2 ≤ x := le_trans (le_max_left _ _) hx0
  have hx1 : 1 ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  have hL2 : 2 ≤ L := (le_max_left 2 L₀).trans
    ((le_max_left (max 2 L₀) L_W).trans hLcutx)
  have hL1 : 1 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hHone : 1 ≤ H := by
    have hxpow : 1 ≤ Real.rpow x δ := Real.one_le_rpow hx1 hδ.le
    exact hxpow.trans hHx
  have hHpos : 0 < H := by linarith
  have hr0 : 0 ≤ r := by linarith
  have hl0 : 0 ≤ l := by linarith
  have hLpow24 : 1 ≤ Real.rpow L (24 / 100 : ℝ) :=
    Real.one_le_rpow hL1 (by norm_num)
  have hW2 : 2 ≤ W := by
    change 2 ≤ Real.exp (Real.rpow L (24 / 100 : ℝ))
    calc
      (2 : ℝ) = Real.exp (Real.log 2) :=
        (Real.exp_log (show (0 : ℝ) < 2 by norm_num)).symm
      _ ≤ Real.exp 1 := by
        apply Real.exp_le_exp.mpr
        have hh := Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num)
        norm_num at hh ⊢
        exact hh
      _ ≤ Real.exp (Real.rpow L (24 / 100 : ℝ)) :=
        Real.exp_le_exp.mpr hLpow24
  have hSdepth : 480024 ≤ S := by
    dsimp [S, ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.sieveDepth]
    exact le_add_of_nonneg_right (Real.rpow_nonneg hLpos.le _)
  have hPprime : ∀ p ∈ P, p.Prime := by
    intro p hp
    have hp' : p ∈ (Finset.range (⌊W⌋₊ + 1)).filter Nat.Prime := by
      simpa [P, primesUpTo] using hp
    exact (Finset.mem_filter.mp hp').2
  have hPsize : ∀ p ∈ P, (p : ℝ) ≤ W := by
    intro p hp
    have hp' : p ∈ (Finset.range (⌊W⌋₊ + 1)).filter Nat.Prime := by
      simpa [P, primesUpTo] using hp
    obtain ⟨hpRange, hpPrime⟩ := Finset.mem_filter.mp hp'
    have hpfloor : p ≤ ⌊W⌋₊ := by
      have := Finset.mem_range.mp hpRange
      omega
    exact (Nat.le_floor_iff' hpPrime.ne_zero).mp hpfloor
  have hVfactor (p : ℕ) (hp : p ∈ P) :
      0 ≤ 1 - (p : ℝ)⁻¹ ∧ 1 - (p : ℝ)⁻¹ ≤ 1 := by
    have hpPrime := hPprime p hp
    have hpR : 1 ≤ (p : ℝ) := by exact_mod_cast hpPrime.one_le
    have hpPos : 0 < (p : ℝ) := by linarith
    have hInv0 : 0 ≤ (p : ℝ)⁻¹ := by positivity
    have hInv1 : (p : ℝ)⁻¹ ≤ 1 := by
      rw [← one_div]
      exact (div_le_one hpPos).2 hpR
    exact ⟨by linarith, by linarith⟩
  have hVfactor' (p : ℕ) (hp : p ∈ P) :
      0 ≤ 1 - 1 / (p : ℝ) ∧ 1 - 1 / (p : ℝ) ≤ 1 := by
    simpa only [one_div] using hVfactor p hp
  have hV0 : 0 ≤ V := by
    dsimp [V, roughSieveProduct]
    exact Finset.prod_nonneg fun p hp => (hVfactor' p hp).1
  have hV1 : V ≤ 1 := by
    dsimp [V, roughSieveProduct]
    exact Finset.prod_le_one₀
      (fun p hp => (hVfactor' p hp).1)
      (fun p hp => (hVfactor' p hp).2)
  have hWpowEq : W ^ S =
      Real.exp (480024 * L ^ (24 / 100 : ℝ) + L ^ (94 / 100 : ℝ)) := by
    have hprod : L ^ (24 / 100 : ℝ) * L ^ (7 / 10 : ℝ) =
        L ^ (94 / 100 : ℝ) := by
      calc
        _ = L ^ ((24 / 100 : ℝ) + 7 / 10) :=
          (Real.rpow_add hLpos _ _).symm
        _ = L ^ (94 / 100 : ℝ) := by congr 1 <;> norm_num
    change (Real.exp (L ^ (24 / 100 : ℝ))) ^
      (480024 + L ^ (7 / 10 : ℝ)) = _
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    rw [mul_add, hprod]
    congr 1
    ring
  have hPrecisionTail : 8 * W ^ S * Real.exp (L ^ aMod) * L ^ B ≤ H := by
    calc
      _ = 8 * (W ^ S * Real.exp (L ^ aMod)) * L ^ B := by ring
      _ = 8 * Real.exp (480024 * L ^ (24 / 100 : ℝ) +
          L ^ (94 / 100 : ℝ) + L ^ aMod) * L ^ B := by
        rw [hWpowEq]
        calc
          _ = 8 * (Real.exp (480024 * L ^ (24 / 100 : ℝ) +
              L ^ (94 / 100 : ℝ)) * Real.exp (L ^ aMod)) * L ^ B := by ring
          _ = _ := by rw [← Real.exp_add]
      _ ≤ Real.exp (δ * L) := hPrecisionNow.2.1
      _ ≤ H := by
        have hxrpow : Real.rpow x δ = Real.exp (δ * L) := by
          calc
            Real.rpow x δ = Real.exp (Real.log x * δ) :=
              Real.rpow_def_of_pos hxpos δ
            _ = Real.exp (δ * L) := by simp [L, mul_comm]
        rw [← hxrpow]
        exact hHx
  have hLengthLower : 0 ≤ u - l := by
    apply sub_nonneg.mpr
    dsimp [u, N]
    have hrFloor := (Nat.lt_floor_add_one r).le
    have hrFloor' : r ≤ ((⌊r⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hrFloor
    linarith
  have hrLtU : r < u := by
    dsimp [u, N]
    exact_mod_cast Nat.lt_floor_add_one r
  have huUpper : u ≤ r + 1 := by
    dsimp [u, N]
    have hfloor : (⌊r⌋₊ : ℝ) ≤ r := Nat.floor_le hr0
    push_cast
    linarith
  have hLenUpper : u - l ≤ 2 * H := by linarith
  have hlu : l ≤ u := sub_nonneg.mp hLengthLower
  have hPcopOne : ∀ p ∈ P, Nat.Coprime 1 p := by
    intro p hp
    exact Nat.coprime_one_left p
  have hRaw (m : ℕ) (b : ZMod m) (hm : 0 < m)
      (hcop : ∀ p ∈ P, Nat.Coprime m p) :
      |((natResidueSet m b).card : ℝ) - ((u - l) / (m : ℝ)) * V| ≤
        ((u - l) / (m : ℝ)) * V * Real.exp (-S / 96) + 4 * W ^ S := by
    have hImage := ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.nat_rough_residue_image
      N m b W l hl0
    have hci : ((natResidueSet m b).image (fun n : ℕ => (n : ℤ))).card =
        (natResidueSet m b).card := by
      apply Finset.card_image_of_injective
      intro n₁ n₂ h
      exact Int.ofNat.inj h
    have hCard : ((natResidueSet m b).card : ℝ) =
        (((OAI.Erdos970.ErdosCoprimeResidueInterval.realCoprimeResidues
          1 m {b} l u).filter
          (fun z : ℤ => ∀ p ∈ P, ¬ (p : ℤ) ∣ z)).card : ℝ) := by
      have hNat : (natResidueSet m b).card =
          ((OAI.Erdos970.ErdosCoprimeResidueInterval.realCoprimeResidues
            1 m {b} l u).filter
            (fun z : ℤ => ∀ p ∈ P, ¬ (p : ℤ) ∣ z)).card := by
        calc
          _ = ((natResidueSet m b).image (fun n : ℕ => (n : ℤ))).card := hci.symm
          _ = _ := congrArg Finset.card hImage
      exact_mod_cast hNat
    have hsieve := ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.rough_sieve_residue_class_bound
      m b P W S l u hm hl0 hlu hW2 hSdepth hPprime hPsize hcop
    rw [hCard]
    simpa [V, P, roughSieveProduct, primesUpTo] using hsieve
  have hFinalFromRaw (m : ℕ) (count Vp : ℝ) (hm0 : 0 < m) (hm1 : 1 ≤ m)
      (hmexp : (m : ℝ) ≤ Real.exp (L ^ aMod))
      (hVp0 : 0 ≤ Vp) (hVp1 : Vp ≤ 1)
      (hraw : |count - ((u - l) / (m : ℝ)) * Vp| ≤
        ((u - l) / (m : ℝ)) * Vp * Real.exp (-S / 96) + 4 * W ^ S) :
      |count - Vp * (r - l + 1) / (m : ℝ)| ≤
        (H / (m : ℝ)) * L ^ (-A) := by
    have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm0
    have hLnegPos : 0 < L ^ (-A) := Real.rpow_pos_of_pos hLpos _
    let E : ℝ := (H / (m : ℝ)) * L ^ (-A)
    have hEpos : 0 < E := by dsimp [E]; positivity
    have hModLog : (m : ℝ) * L ^ A ≤ Real.exp (L ^ aMod) * L ^ B := by
      calc
        _ ≤ Real.exp (L ^ aMod) * L ^ A :=
          mul_le_mul_of_nonneg_right hmexp (Real.rpow_nonneg hLpos.le A)
        _ ≤ Real.exp (L ^ aMod) * L ^ B :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hL1 hA_B) (Real.exp_pos _).le
    have hTailStrength : 8 * W ^ S * (m : ℝ) * L ^ A ≤ H := by
      calc
        _ = 8 * W ^ S * ((m : ℝ) * L ^ A) := by ring
        _ ≤ 8 * W ^ S * (Real.exp (L ^ aMod) * L ^ B) :=
          mul_le_mul_of_nonneg_left hModLog (by positivity)
        _ ≤ H := by
          convert hPrecisionTail using 1 <;> ring
    have hWpow1 : 1 ≤ W ^ S := Real.one_le_rpow (by linarith) (by
      dsimp [S, ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.sieveDepth]
      positivity)
    have hTailDen : 8 * (m : ℝ) * L ^ A ≤ H := by
      calc
        _ = 8 * (1 * ((m : ℝ) * L ^ A)) := by ring
        _ ≤ 8 * (W ^ S * ((m : ℝ) * L ^ A)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hWpow1 (mul_nonneg (by exact_mod_cast (Nat.cast_nonneg m))
              (Real.rpow_nonneg hLpos.le A))) (by norm_num)
        _ ≤ H := by
          convert hTailStrength using 1 <;> ring
    have hDenPos : 0 < (m : ℝ) * L ^ A := mul_pos hmpos (Real.rpow_pos_of_pos hLpos _)
    have hPowApos : 0 < L ^ A := Real.rpow_pos_of_pos hLpos A
    have hElarge : 8 ≤ E := by
      have hTailDen' : 8 * ((m : ℝ) * L ^ A) ≤ H := by
        convert hTailDen using 1 <;> ring
      have hdiv := (le_div_iff₀ hDenPos).2 hTailDen'
      have heq : H / ((m : ℝ) * L ^ A) = E := by
        dsimp [E]
        rw [Real.rpow_neg hLpos.le A]
        field_simp [ne_of_gt hmpos, ne_of_gt hPowApos]
      rw [heq] at hdiv
      exact hdiv
    have hTailSmall : 4 * W ^ S ≤ E / 2 := by
      have heq : H / ((m : ℝ) * L ^ A) = E := by
        dsimp [E]
        rw [Real.rpow_neg hLpos.le A]
        field_simp [ne_of_gt hmpos, ne_of_gt hPowApos]
      have hTailStrength' : (8 * W ^ S) * ((m : ℝ) * L ^ A) ≤ H := by
        convert hTailStrength using 1 <;> ring
      have hdiv8 := (le_div_iff₀ hDenPos).2 hTailStrength'
      rw [heq] at hdiv8
      nlinarith [hdiv8]
    have hPowA : L ^ (-B) ≤ (1 / 16 : ℝ) * L ^ (-A) := by
      have hExpLe : -B ≤ -(A + 4) := by dsimp [B]; linarith
      have hpowCmp : L ^ (-B) ≤ L ^ (-(A + 4)) :=
        Real.rpow_le_rpow_of_exponent_le hL1 hExpLe
      have hpowMul : L ^ (-(A + 4)) = L ^ (-A) * L ^ (-4 : ℝ) := by
        calc
          L ^ (-(A + 4)) = L ^ ((-A) + (-4 : ℝ)) := by congr 1 <;> ring
          _ = L ^ (-A) * L ^ (-4 : ℝ) := Real.rpow_add hLpos _ _
      have hfour : L ^ (-4 : ℝ) ≤ (1 / 16 : ℝ) := by
        calc
          L ^ (-4 : ℝ) ≤ (2 : ℝ) ^ (-4 : ℝ) :=
            Real.rpow_le_rpow_of_nonpos (by norm_num) hL2 (by norm_num)
          _ = 1 / 16 := by norm_num
      calc
        _ ≤ L ^ (-A) * L ^ (-4 : ℝ) := hpowCmp.trans_eq hpowMul
        _ ≤ L ^ (-A) * (1 / 16) :=
          mul_le_mul_of_nonneg_left hfour (Real.rpow_nonneg hLpos.le _)
        _ = (1 / 16) * L ^ (-A) := by ring
    have hExpSmall : 2 * Real.exp (-S / 96) ≤ (1 / 16 : ℝ) * L ^ (-A) :=
      hPrecisionNow.1.trans hPowA
    have hLenBound : (u - l) / (m : ℝ) ≤ 2 * (H / (m : ℝ)) := by
      calc
        _ ≤ (2 * H) / (m : ℝ) :=
          div_le_div_of_nonneg_right hLenUpper hmpos.le
        _ = 2 * (H / (m : ℝ)) := by ring
    have hDensBound : ((u - l) / (m : ℝ)) * Vp ≤ 2 * (H / (m : ℝ)) := by
      calc
        _ ≤ ((u - l) / (m : ℝ)) * 1 :=
          mul_le_mul_of_nonneg_left hVp1 (div_nonneg hLengthLower hmpos.le)
        _ = (u - l) / (m : ℝ) := by ring
        _ ≤ 2 * (H / (m : ℝ)) := hLenBound
    have hExpPart :
        ((u - l) / (m : ℝ)) * Vp * Real.exp (-S / 96) ≤ E / 16 := by
      calc
        _ ≤ (2 * (H / (m : ℝ))) * Real.exp (-S / 96) :=
          mul_le_mul_of_nonneg_right hDensBound (Real.exp_pos _).le
        _ = (H / (m : ℝ)) * (2 * Real.exp (-S / 96)) := by ring
        _ ≤ (H / (m : ℝ)) * ((1 / 16 : ℝ) * L ^ (-A)) :=
          mul_le_mul_of_nonneg_left hExpSmall (by positivity)
        _ = E / 16 := by dsimp [E]; ring
    have hRawSmall : |count - ((u - l) / (m : ℝ)) * Vp| ≤
        E / 16 + E / 2 := by
      exact hraw.trans (add_le_add hExpPart hTailSmall)
    have hLenErr : |(u - l) - (r - l + 1)| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    have hRatioErr :
        |(u - l) / (m : ℝ) - (r - l + 1) / (m : ℝ)| ≤ 1 := by
      rw [← sub_div, abs_div, abs_of_pos hmpos]
      apply (div_le_one hmpos).2
      have hmCast : 1 ≤ (m : ℝ) := by exact_mod_cast hm1
      exact le_trans hLenErr hmCast
    have hMainErr :
        |((u - l) / (m : ℝ)) * Vp - Vp * (r - l + 1) / (m : ℝ)| ≤ 1 := by
      have heq : ((u - l) / (m : ℝ)) * Vp - Vp * (r - l + 1) / (m : ℝ) =
          Vp * ((u - l) / (m : ℝ) - (r - l + 1) / (m : ℝ)) := by ring
      rw [heq, abs_mul, abs_of_nonneg hVp0]
      calc
        _ ≤ 1 * 1 := mul_le_mul hVp1 hRatioErr (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    calc
      _ = |(count - ((u - l) / (m : ℝ)) * Vp) +
          (((u - l) / (m : ℝ)) * Vp - Vp * (r - l + 1) / (m : ℝ))| := by congr 1 <;> ring
      _ ≤ |count - ((u - l) / (m : ℝ)) * Vp| +
          |((u - l) / (m : ℝ)) * Vp - Vp * (r - l + 1) / (m : ℝ)| := by
            exact abs_add_le _ _
      _ ≤ E / 16 + E / 2 + 1 := add_le_add hRawSmall hMainErr
      _ ≤ E := by nlinarith [hElarge]
  have hFinalCount (m : ℕ) (b : ZMod m) (hm0 : 0 < m) (hm1 : 1 ≤ m)
      (hcop : ∀ p ∈ P, Nat.Coprime m p)
      (hmexp : (m : ℝ) ≤ Real.exp (L ^ aMod)) :
      |((natResidueSet m b).card : ℝ) - V * (r - l + 1) / (m : ℝ)| ≤
        (H / (m : ℝ)) * L ^ (-A) := by
    exact hFinalFromRaw m ((natResidueSet m b).card : ℝ) V hm0 hm1 hmexp hV0 hV1
      (hRaw m b hm0 hcop)
  have hRawAvoid (m : ℕ) (b : ZMod m) (P' : Finset ℕ) (hm : 0 < m)
      (hprime : ∀ p ∈ P', p.Prime) (hsize : ∀ p ∈ P', (p : ℝ) ≤ W)
      (hcop : ∀ p ∈ P', Nat.Coprime m p) :
      |((naturalAvoidingResidues N m b P' l).card : ℝ) -
          ((u - l) / (m : ℝ)) * ∏ p ∈ P', (1 - 1 / (p : ℝ))| ≤
        ((u - l) / (m : ℝ)) *
            (∏ p ∈ P', (1 - 1 / (p : ℝ))) * Real.exp (-S / 96) + 4 * W ^ S := by
    have hImage := nat_avoiding_residue_image N m b P' l hl0
    have hci :
        ((naturalAvoidingResidues N m b P' l).image (fun n : ℕ => (n : ℤ))).card =
          (naturalAvoidingResidues N m b P' l).card := by
      apply Finset.card_image_of_injective
      intro n₁ n₂ h
      exact Int.ofNat.inj h
    have hCard : ((naturalAvoidingResidues N m b P' l).card : ℝ) =
        (((OAI.Erdos970.ErdosCoprimeResidueInterval.realCoprimeResidues
          1 m {b} l u).filter
          (fun z : ℤ => ∀ p ∈ P', ¬ (p : ℤ) ∣ z)).card : ℝ) := by
      have hNat : (naturalAvoidingResidues N m b P' l).card =
          ((OAI.Erdos970.ErdosCoprimeResidueInterval.realCoprimeResidues
            1 m {b} l u).filter
            (fun z : ℤ => ∀ p ∈ P', ¬ (p : ℤ) ∣ z)).card := by
        calc
          _ = ((naturalAvoidingResidues N m b P' l).image
              (fun n : ℕ => (n : ℤ))).card := hci.symm
          _ = _ := congrArg Finset.card hImage
      exact_mod_cast hNat
    have hsieve := ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.rough_sieve_residue_class_bound
      m b P' W S l u hm hl0 hlu hW2 hSdepth hprime hsize hcop
    rw [hCard]
    simpa only [one_div] using hsieve
  constructor
  · have hOne : |((natResidueSet 1 0).card : ℝ) -
        V * (r - l + 1) / (1 : ℝ)| ≤ (H / (1 : ℝ)) * L ^ (-A) :=
      by
        have hExpOne : 1 ≤ Real.exp (L ^ aMod) :=
          Real.one_le_exp (Real.rpow_nonneg hLpos.le aMod)
        simpa using hFinalCount 1 0 (by norm_num) (by norm_num) hPcopOne
          (by exact_mod_cast hExpOne)
    have hFirstSet : roughIntegersInInterval l r W = natResidueSet 1 0 := by
      unfold roughIntegersInInterval natResidueSet
      ext n
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨hn, hl, hnr, hrough⟩
        exact ⟨hn, hl, hrough, Subsingleton.elim _ _⟩
      · rintro ⟨hn, hl, hrough, _⟩
        exact ⟨hn, hl, nat_range_floor_le_real r hr0 (Finset.mem_range.mpr hn), hrough⟩
    rw [← hFirstSet] at hOne
    simpa [V, roughSieveProduct] using hOne
  constructor
  · intro d hd1 hdexp hroughD b
    have hcopD : ∀ p ∈ P, Nat.Coprime d p := by
      intro p hp
      have hpPrime := hPprime p hp
      have hpSize := hPsize p hp
      apply (hpPrime.coprime_iff_not_dvd.mpr ?_).symm
      intro hpd
      have hrough := hroughD p hpPrime hpd
      exact (not_lt_of_ge hpSize) hrough
    have hmodD : (d : ℝ) ≤ Real.exp (L ^ aMod) := by
      apply le_trans hdexp
      exact Real.exp_le_exp.mpr
        (Real.rpow_le_rpow_of_exponent_le hL1 (le_max_left aExp (1 / 2)))
    have hD := hFinalCount d b (by exact_mod_cast hd1) hd1 hcopD hmodD
    have hCountEq : roughResidueCount l r W d b = ((natResidueSet d b).card : ℝ) := by
      unfold roughResidueCount natResidueSet
      rw [rough_interval_residue_filter_eq l r W d b hr0]
    rw [← hCountEq] at hD
    simpa [V, roughSieveProduct] using hD
  · intro q hq hqBound χ
    letI : NeZero q := ⟨by omega⟩
    have hqpos : 0 < q := by omega
    have hqRpos : 0 < (q : ℝ) := by exact_mod_cast hqpos
    have hLogGrowthNow := hL_W L hL_Wx
    have hqW : (q : ℝ) ≤ W := by
      change (q : ℝ) ≤ Real.exp (Real.rpow L (24 / 100 : ℝ))
      calc
        (q : ℝ) ≤ Real.rpow L C := hqBound
        _ = Real.exp (C * Real.log L) := by
          calc
            _ = Real.exp (Real.log L * C) := Real.rpow_def_of_pos hLpos C
            _ = _ := by congr 1 <;> ring
        _ ≤ Real.exp (Real.rpow L (24 / 100 : ℝ)) :=
          Real.exp_le_exp.mpr hLogGrowthNow
    let Pq : Finset ℕ := P.filter fun p => ¬ p ∣ q
    let Vq : ℝ := ∏ p ∈ Pq, (1 - 1 / (p : ℝ))
    let U : Finset (ZMod q) := Finset.univ.filter IsUnit
    have hqne : q ≠ 0 := Nat.ne_of_gt hqpos
    have hPFsubset : q.primeFactors ⊆ P := by
      intro p hp
      have hdata := Nat.mem_primeFactors.mp hp
      have hpLe : p ≤ q := Nat.le_of_dvd hqpos hdata.2.1
      have hpLeR : (p : ℝ) ≤ (q : ℝ) := by exact_mod_cast hpLe
      have hpW : (p : ℝ) ≤ W := hpLeR.trans hqW
      have hWnonneg : 0 ≤ W := by linarith [hW2]
      have hpfloor : p ≤ ⌊W⌋₊ := (Nat.le_floor_iff hWnonneg).mpr hpW
      change p ∈ primesUpTo W
      unfold primesUpTo
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_of_le hpfloor, hdata.1⟩
    have hPqEq : Pq = P \ q.primeFactors := by
      ext p
      simp only [Pq, Finset.mem_filter, Finset.mem_sdiff]
      constructor
      · rintro ⟨hpP, hnot⟩
        exact ⟨hpP, fun hpF => hnot (Nat.mem_primeFactors.mp hpF).2.1⟩
      · rintro ⟨hpP, hpF⟩
        exact ⟨hpP, fun hpdvd => hpF
          (Nat.Prime.mem_primeFactors (hPprime p hpP) hpdvd hqne)⟩
    have hVprod : V = ∏ p ∈ P, (1 - 1 / (p : ℝ)) := by
      simp [V, roughSieveProduct, P, primesUpTo]
    have hprodSplit : Vq *
        (∏ p ∈ q.primeFactors, (1 - 1 / (p : ℝ))) = V := by
      change (∏ p ∈ Pq, (1 - 1 / (p : ℝ))) *
          (∏ p ∈ q.primeFactors, (1 - 1 / (p : ℝ))) = V
      rw [hPqEq, hVprod]
      exact Finset.prod_sdiff hPFsubset
    have hTotientProd : (Nat.totient q : ℝ) = (q : ℝ) *
        ∏ p ∈ q.primeFactors, (1 - (p : ℝ)⁻¹) := by
      have hRat := Nat.totient_eq_mul_prod_factors q
      have hCast := congrArg (fun z : ℚ => (z : ℝ)) hRat
      simpa using hCast
    have hTotientProd' : (Nat.totient q : ℝ) = (q : ℝ) *
        ∏ p ∈ q.primeFactors, (1 - 1 / (p : ℝ)) := by
      simpa only [one_div] using hTotientProd
    have hphiPos : 0 < (Nat.totient q : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hqpos
    have hDensity : Vq / (q : ℝ) = V / (Nat.totient q : ℝ) := by
      rw [div_eq_div_iff hqRpos.ne' hphiPos.ne']
      rw [hTotientProd', ← hprodSplit]
      ring
    have hVqfactor (p : ℕ) (hp : p ∈ Pq) :
        0 ≤ 1 - 1 / (p : ℝ) ∧ 1 - 1 / (p : ℝ) ≤ 1 := by
      have hpP : p ∈ P := (Finset.mem_filter.mp hp).1
      exact hVfactor' p hpP
    have hVq0 : 0 ≤ Vq := by
      dsimp [Vq]
      exact Finset.prod_nonneg fun p hp => (hVqfactor p hp).1
    have hVq1 : Vq ≤ 1 := by
      dsimp [Vq]
      exact Finset.prod_le_one₀ (fun p hp => (hVqfactor p hp).1)
        (fun p hp => (hVqfactor p hp).2)
    have hPqPrime : ∀ p ∈ Pq, p.Prime := by
      intro p hp
      exact hPprime p (Finset.mem_filter.mp hp).1
    have hPqSize : ∀ p ∈ Pq, (p : ℝ) ≤ W := by
      intro p hp
      exact hPsize p (Finset.mem_filter.mp hp).1
    have hPqCop : ∀ p ∈ Pq, Nat.Coprime q p := by
      intro p hp
      have hpPrime := hPqPrime p hp
      have hpNotDvd := (Finset.mem_filter.mp hp).2
      exact (hpPrime.coprime_iff_not_dvd.mpr hpNotDvd).symm
    have hqModExp : (q : ℝ) ≤ Real.exp (L ^ aMod) := by
      calc
        (q : ℝ) ≤ Real.rpow L C := hqBound
        _ ≤ Real.rpow L B :=
          Real.rpow_le_rpow_of_exponent_le hL1 (by dsimp [B]; linarith)
        _ ≤ Real.exp (L ^ aMod) := hPrecisionNow.2.2
    have hRoughAvoid (n : ℕ) (b : ZMod q) (hb : IsUnit b)
        (hn : (n : ZMod q) = b) :
        roughAbove n W ↔ ∀ p ∈ Pq, ¬ p ∣ n := by
      have hnCoprime : Nat.Coprime n q := by
        apply (ZMod.isUnit_iff_coprime n q).mp
        rw [hn]
        exact hb
      have hNotCommon (p : ℕ) (hpPrime : p.Prime) (hpn : p ∣ n) (hpq : p ∣ q) :
          False := by
        have hgcd := hnCoprime.gcd_eq_one
        have hpgcd : p ∣ Nat.gcd n q := Nat.dvd_gcd hpn hpq
        rw [hgcd] at hpgcd
        exact hpPrime.ne_one (Nat.dvd_one.mp hpgcd)
      constructor
      · intro hrough p hp hpn
        have hpP := (Finset.mem_filter.mp hp).1
        exact (not_lt_of_ge (hPsize p hpP)) (hrough p (hPprime p hpP) hpn)
      · intro havoid p hpPrime hpn
        by_contra hpNotW
        have hpLe : (p : ℝ) ≤ W := le_of_not_gt hpNotW
        have hWnonneg : 0 ≤ W := by linarith [hW2]
        have hpfloor : p ≤ ⌊W⌋₊ := (Nat.le_floor_iff hWnonneg).mpr hpLe
        have hpP : p ∈ P := by
          change p ∈ primesUpTo W
          unfold primesUpTo
          simp only [Finset.mem_filter, Finset.mem_range]
          exact ⟨Nat.lt_succ_of_le hpfloor, hpPrime⟩
        by_cases hpq : p ∣ q
        · exact hNotCommon p hpPrime hpn hpq
        · exact havoid p (Finset.mem_filter.mpr ⟨hpP, hpq⟩) hpn
    have hAvoidEq (b : ZMod q) (hb : IsUnit b) :
        naturalAvoidingResidues N q b Pq l = natResidueSet q b := by
      ext n
      simp only [naturalAvoidingResidues, natResidueSet, Finset.mem_filter]
      constructor
      · rintro ⟨hn, hl, hres, havoid⟩
        exact ⟨hn, hl, (hRoughAvoid n b hb hres).2 havoid, hres⟩
      · rintro ⟨hn, hl, hrough, hres⟩
        exact ⟨hn, hl, hres, (hRoughAvoid n b hb hres).1 hrough⟩
    have hClass (b : ZMod q) (hb : b ∈ U) :
        |roughResidueCount l r W q b -
          V * (r - l + 1) / (Nat.totient q : ℝ)| ≤
            (H / (q : ℝ)) * L ^ (-A) := by
      have hbunit : IsUnit b := (Finset.mem_filter.mp hb).2
      have hAvoid := hAvoidEq b hbunit
      have hraw := hRawAvoid q b Pq hqpos hPqPrime hPqSize hPqCop
      rw [hAvoid] at hraw
      have hcountEq : roughResidueCount l r W q b =
          ((natResidueSet q b).card : ℝ) := by
        unfold roughResidueCount natResidueSet
        rw [rough_interval_residue_filter_eq l r W q b hr0]
      rw [hcountEq]
      have happrox := hFinalFromRaw q ((natResidueSet q b).card : ℝ) Vq
        hqpos (by omega) hqModExp hVq0 hVq1 hraw
      have hModels : Vq * (r - l + 1) / (q : ℝ) =
          V * (r - l + 1) / (Nat.totient q : ℝ) := by
        calc
          _ = (Vq / (q : ℝ)) * (r - l + 1) := by ring
          _ = (V / (Nat.totient q : ℝ)) * (r - l + 1) := by rw [hDensity]
          _ = _ := by ring
      rw [hModels] at happrox
      exact happrox
    let T : Finset ℕ := (Finset.range (⌊r⌋₊ + 1)).filter fun n =>
      l ≤ (n : ℝ) ∧ (n : ℝ) ≤ r ∧ roughAbove n W
    have hFiberSet (b : ZMod q) :
        Finset.filter (fun n : ℕ => (n : ZMod q) = b) T =
          (Finset.range (⌊r⌋₊ + 1)).filter
            (fun n : ℕ => l ≤ (n : ℝ) ∧ roughAbove n W ∧ (n : ZMod q) = b) := by
      ext n
      simp only [T, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hn, hlow, hhigh, hrough⟩, hres⟩
        exact ⟨hn, hlow, hrough, hres⟩
      · rintro ⟨hn, hlow, hrough, hres⟩
        exact ⟨⟨hn, hlow, nat_range_floor_le_real r hr0 hn, hrough⟩, hres⟩
    have hFiberCount (b : ZMod q) :
        roughResidueCount l r W q b =
          ((Finset.filter (fun n : ℕ => (n : ZMod q) = b) T).card : ℝ) := by
      unfold roughResidueCount
      rw [rough_interval_residue_filter_eq l r W q b hr0]
      rw [← hFiberSet b]
    have hPoint (n : ℕ) :
        (∑ b ∈ U, if (n : ZMod q) = b then χ b else 0) = χ (n : ZMod q) := by
      by_cases hnunit : IsUnit (n : ZMod q)
      · have hnmem : (n : ZMod q) ∈ U := by simp [U, hnunit]
        have hsum0 :
            (∑ b ∈ U, if (n : ZMod q) = b then χ b else (0 : ℂ)) =
              (if (n : ZMod q) = (n : ZMod q) then χ (n : ZMod q) else 0) :=
          Finset.sum_eq_single (n : ZMod q)
            (fun b hb hbn => by
              have hneq : (n : ZMod q) ≠ b := by
                intro heq
                exact hbn heq.symm
              by_cases heq : (n : ZMod q) = b
              · exact (hneq heq).elim
              · exact if_neg heq)
            (fun hnot => (hnot hnmem).elim)
        simpa using hsum0
      · have hsum :
            (∑ b ∈ U, if (n : ZMod q) = b then χ b else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro b hb
          have hneq : (n : ZMod q) ≠ b := by
            intro heq
            exact hnunit (heq ▸ (Finset.mem_filter.mp hb).2)
          by_cases heq : (n : ZMod q) = b
          · exact (hneq heq).elim
          · exact if_neg heq
        rw [hsum, χ.map_nonunit hnunit]
    have hPartition :
        (∑ n ∈ T, (χ (n : ZMod q) : ℂ)) =
          ∑ b ∈ U, χ b * (roughResidueCount l r W q b : ℂ) := by
      calc
        _ = ∑ n ∈ T, ∑ b ∈ U,
              if (n : ZMod q) = b then χ b else 0 := by
          apply Finset.sum_congr rfl
          intro n hn
          exact (hPoint n).symm
        _ = ∑ b ∈ U, ∑ n ∈ T,
              if (n : ZMod q) = b then χ b else 0 := by
          rw [Finset.sum_comm]
        _ = ∑ b ∈ U, χ b * (roughResidueCount l r W q b : ℂ) := by
          apply Finset.sum_congr rfl
          intro b hb
          let F : Finset ℕ := Finset.filter (fun n : ℕ => (n : ZMod q) = b) T
          have hsumFilter :
              (∑ n ∈ T, if (n : ZMod q) = b then χ b else 0) =
                ∑ n ∈ F, χ b := by
            rw [← Finset.sum_filter]
          have hcardCast : (roughResidueCount l r W q b : ℂ) = (F.card : ℂ) := by
            exact_mod_cast hFiberCount b
          rw [hsumFilter]
          simp only [Finset.sum_const, nsmul_eq_mul]
          rw [hcardCast]
          ring
    have hCharSum : (∑ b ∈ U, χ b) =
        if χ = 1 then (Nat.totient q : ℂ) else 0 := by
      have hsumAll : (∑ b : ZMod q, χ b) =
          if χ = 1 then (Nat.totient q : ℂ) else 0 := by
        by_cases hχ : χ = 1
        · subst χ
          simp [MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient q]
        · simp [hχ, MulChar.sum_eq_zero_of_ne_one hχ]
      calc
        _ = ∑ b : ZMod q, if IsUnit b then χ b else 0 := by
          simp [U, Finset.sum_filter]
        _ = ∑ b : ZMod q, χ b := by
          apply Finset.sum_congr rfl
          intro b hb
          by_cases hbunit : IsUnit b
          · simp [hbunit]
          · simp [hbunit, χ.map_nonunit hbunit]
        _ = _ := hsumAll
    let M : ℝ := V * (r - l + 1) / (Nat.totient q : ℝ)
    have hMainCancel : (Nat.totient q : ℝ) * M = V * (r - l + 1) := by
      dsimp [M]
      field_simp [ne_of_gt hphiPos]
    have hMainSum :
        (∑ b ∈ U, χ b * (M : ℂ)) =
          (if χ = 1 then (V * (r - l + 1) : ℝ) else 0 : ℂ) := by
      rw [← Finset.sum_mul, hCharSum]
      by_cases hχ : χ = 1
      · have hMainCancelC : (Nat.totient q : ℂ) * (M : ℂ) =
            ((V * (r - l + 1) : ℝ) : ℂ) := by exact_mod_cast hMainCancel
        simp [hχ, hMainCancelC]
      · simp [hχ]
    have hErrorSum :
        ‖∑ b ∈ U, χ b *
            ((roughResidueCount l r W q b : ℂ) - (M : ℂ))‖ ≤
          H * L ^ (-A) := by
      have hTerm (b : ZMod q) (hb : b ∈ U) :
          ‖χ b * ((roughResidueCount l r W q b : ℂ) - (M : ℂ))‖ ≤
            (H / (q : ℝ)) * L ^ (-A) := by
        have hNormReal :
            ‖(roughResidueCount l r W q b : ℂ) - (M : ℂ)‖ =
              |roughResidueCount l r W q b - M| := by
          rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        have hClass' : |roughResidueCount l r W q b - M| ≤
            (H / (q : ℝ)) * L ^ (-A) := by
          simpa [M] using hClass b hb
        calc
          _ = ‖χ b‖ *
                ‖(roughResidueCount l r W q b : ℂ) - (M : ℂ)‖ := norm_mul _ _
          _ ≤ 1 * ((H / (q : ℝ)) * L ^ (-A)) :=
            mul_le_mul (χ.norm_le_one b) (by rw [hNormReal]; exact hClass')
              (norm_nonneg _) (by norm_num)
          _ = _ := by ring
      have hUcard : (U.card : ℝ) ≤ (q : ℝ) := by
        have hcard := Finset.card_le_univ U
        rw [ZMod.card] at hcard
        exact_mod_cast hcard
      have hErrorNonneg : 0 ≤ (H / (q : ℝ)) * L ^ (-A) := by positivity
      calc
        _ ≤ ∑ b ∈ U, ‖χ b *
              ((roughResidueCount l r W q b : ℂ) - (M : ℂ))‖ := norm_sum_le _ _
        _ ≤ ∑ b ∈ U, (H / (q : ℝ)) * L ^ (-A) := by
          apply Finset.sum_le_sum
          intro b hb
          exact hTerm b hb
        _ = (U.card : ℝ) * ((H / (q : ℝ)) * L ^ (-A)) := by simp
        _ ≤ H * L ^ (-A) := by
          calc
            _ ≤ (q : ℝ) * ((H / (q : ℝ)) * L ^ (-A)) :=
              mul_le_mul_of_nonneg_right hUcard hErrorNonneg
            _ = H * L ^ (-A) := by field_simp [ne_of_gt hqRpos]
    have hExact :
        (∑ n ∈ T, (χ (n : ZMod q) : ℂ)) -
            (if χ = 1 then (V * (r - l + 1) : ℝ) else 0 : ℂ) =
          ∑ b ∈ U, χ b *
            ((roughResidueCount l r W q b : ℂ) - (M : ℂ)) := by
      calc
        _ = (∑ b ∈ U, χ b * (roughResidueCount l r W q b : ℂ)) -
              (∑ b ∈ U, χ b * (M : ℂ)) := by rw [hPartition, hMainSum]
        _ = ∑ b ∈ U,
              (χ b * (roughResidueCount l r W q b : ℂ) - χ b * (M : ℂ)) :=
                by rw [Finset.sum_sub_distrib]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro b hb
          ring
    have hErrorBound :
        ‖∑ b ∈ U, χ b *
            ((roughResidueCount l r W q b : ℂ) - (M : ℂ))‖ ≤
          H * Real.rpow (Real.log x) (-A) := by
      simpa [L] using hErrorSum
    by_cases hχ : χ = 1
    · simp only [if_pos hχ]
      have hExactχ :
          (∑ n ∈ (Finset.range (⌊r⌋₊ + 1)).filter (fun n : ℕ =>
            l ≤ (n : ℝ) ∧ (n : ℝ) ≤ r ∧ roughAbove n (roughCutoff x)),
            (χ (n : ZMod q) : ℂ)) -
              ((roughSieveProduct (roughCutoff x) * (r - l + 1) : ℝ) : ℂ) =
            ∑ b ∈ U, χ b *
              ((roughResidueCount l r W q b : ℂ) - (M : ℂ)) := by
        simpa [hχ, T, V, W] using hExact
      calc
        _ = ‖∑ b ∈ U, χ b *
              ((roughResidueCount l r W q b : ℂ) - (M : ℂ))‖ :=
                congrArg (fun z : ℂ => ‖z‖) hExactχ
        _ ≤ H * Real.rpow (Real.log x) (-A) := hErrorBound
    · simp only [if_neg hχ]
      have hExactχ :
          (∑ n ∈ (Finset.range (⌊r⌋₊ + 1)).filter (fun n : ℕ =>
            l ≤ (n : ℝ) ∧ (n : ℝ) ≤ r ∧ roughAbove n (roughCutoff x)),
            (χ (n : ZMod q) : ℂ)) - 0 =
            ∑ b ∈ U, χ b *
              ((roughResidueCount l r W q b : ℂ) - (M : ℂ)) := by
        simpa [hχ, T, V, W] using hExact
      calc
        _ = ‖∑ b ∈ U, χ b *
              ((roughResidueCount l r W q b : ℂ) - (M : ℂ))‖ :=
                congrArg (fun z : ℂ => ‖z‖) hExactχ
        _ ≤ H * Real.rpow (Real.log x) (-A) := hErrorBound

/-- The residue-restricted sum in the moderate-frequency estimate. -/
noncomputable def integerResiduePhaseSum (q : ℕ) (a : ZMod q)
    (t : ℝ) (l r : ℝ) : ℂ :=
  ∑ n ∈ (Finset.range (⌊r⌋₊ + 1)).filter (fun (n : ℕ) =>
      l ≤ (n : ℝ) ∧ (n : ℝ) ≤ r ∧ (n : ZMod q) = a),
    Complex.exp (Complex.I * t * Real.log (n : ℝ))

/-- `t2:pd.moderate-phase` — PD `02-preliminaries.tex:160-173` and `05-major-arcs.tex:89-104`.
-/
theorem moderate_phase (δ C : ℝ) (hδ : 0 < δ) (hC : 0 < C) :
    ∃ C₀ cδ x₀ : ℝ, 0 < C₀ ∧ 0 < cδ ∧ 2 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        let L := Real.log x
        let T := Real.exp (L / Real.log L ^ 2)
        ∀ N : ℝ, Real.rpow x δ ≤ N →
          ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.rpow L C →
            ∀ a : ZMod q, ∀ t : ℝ, 1 ≤ |t| → |t| ≤ T →
              ∀ l r : ℝ, N ≤ l → l ≤ r → r ≤ 2 * N →
                ‖integerResiduePhaseSum q a t l r -
                  ((1 / (q : ℂ)) *
                    ∫ y in l..r, Complex.exp (Complex.I * t * Real.log y))‖ ≤
                  C₀ * (1 + |t|) ∧
                ‖∫ y in l..r, Complex.exp (Complex.I * t * Real.log y)‖ ≤
                  C₀ * N / |t| ∧
              ((q : ℝ) / N) *
                    ‖integerResiduePhaseSum q a t l r‖ ≤
                  C₀ * (|t|⁻¹ + Real.rpow x (-cδ)) := by
  obtain ⟨xA, hxA, hAbsorb⟩ :=
    ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.exists_moderate_absorption δ C hδ hC
  refine ⟨4, δ / 2, max 2 xA, by norm_num, by positivity, le_max_left _ _, ?_⟩
  intro x hx
  dsimp
  intro N hN q hq hqBound a t ht hT l r hl hlr hr
  let L : ℝ := Real.log x
  let T : ℝ := Real.exp (L / Real.log L ^ 2)
  have hxA' : xA ≤ x := (le_max_right 2 xA).trans hx
  have hx2 : 2 ≤ x := (le_max_left 2 xA).trans hx
  have hxpos : 0 < x := by linarith
  have hAbsRaw := hAbsorb x hxA'
  have hAbs : Real.rpow L C * (1 + T) ≤ Real.rpow x (δ / 2) := by
    simpa [L, T] using hAbsRaw
  have hNpos : 0 < N := by
    have : 0 < Real.rpow x δ := Real.rpow_pos_of_pos hxpos δ
    exact lt_of_lt_of_le this hN
  have hqpos : 0 < q := Nat.zero_lt_of_lt hq
  have hlogPos : 0 < L := by dsimp [L]; exact Real.log_pos (by linarith)
  have hfac : 1 ≤ 1 + T := by
    have hTpos : 0 < T := by dsimp [T]; positivity
    linarith
  have hlogpow : Real.rpow L C ≤ Real.rpow x (δ / 2) := by
    calc
      Real.rpow L C = Real.rpow L C * 1 := by ring
      _ ≤ Real.rpow L C * (1 + T) :=
        mul_le_mul_of_nonneg_left hfac (Real.rpow_nonneg hlogPos.le C)
      _ ≤ Real.rpow x (δ / 2) := hAbs
  have hxone : 1 ≤ x := by linarith
  have hhalfLe : Real.rpow x (δ / 2) ≤ Real.rpow x δ :=
    Real.rpow_le_rpow_of_exponent_le hxone (by linarith)
  have hqN : (q : ℝ) ≤ N := by
    calc
      (q : ℝ) ≤ Real.rpow L C := hqBound
      _ ≤ Real.rpow x (δ / 2) := hlogpow
      _ ≤ Real.rpow x δ := hhalfLe
      _ ≤ N := hN
  have hEst := ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.phase_residue_interval_bounds
    t N l r q a hNpos hl hlr hr hqpos hqN ht
  have hEst' :
      ‖integerResiduePhaseSum q a t l r -
        (1 / (q : ℂ)) * ∫ y in l..r, Complex.exp (Complex.I * t * Real.log y)‖ ≤
        4 * (1 + |t|) ∧
      ‖∫ y in l..r, Complex.exp (Complex.I * t * Real.log y)‖ ≤ 4 * N / |t| ∧
      ((q : ℝ) / N) * ‖integerResiduePhaseSum q a t l r‖ ≤
        4 / |t| + 4 * ((q : ℝ) / N) * (1 + |t|) := by
    simpa [integerResiduePhaseSum, ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.phase] using hEst
  have hqT : (q : ℝ) * (1 + |t|) ≤ Real.rpow x (δ / 2) := by
    calc
      (q : ℝ) * (1 + |t|) ≤ Real.rpow L C * (1 + |t|) :=
        mul_le_mul_of_nonneg_right hqBound (by positivity)
      _ ≤ Real.rpow L C * (1 + T) :=
        mul_le_mul_of_nonneg_left (by linarith [hT])
          (Real.rpow_nonneg hlogPos.le C)
      _ ≤ Real.rpow x (δ / 2) := hAbs
  have hhalfPos : 0 < Real.rpow x (δ / 2) := Real.rpow_pos_of_pos hxpos _
  have hhalfSq : (Real.rpow x (δ / 2)) ^ 2 = Real.rpow x δ := by
    calc
      (Real.rpow x (δ / 2)) ^ 2 = Real.rpow x ((δ / 2) * 2) :=
        (Real.rpow_mul_natCast hxpos.le (δ / 2) 2).symm
      _ = Real.rpow x δ := by congr 1 <;> ring
  have hprodN : ((q : ℝ) * (1 + |t|)) * Real.rpow x (δ / 2) ≤ N := by
    calc
      _ ≤ (Real.rpow x (δ / 2)) ^ 2 := by
        have hhalfNN : 0 ≤ Real.rpow x (δ / 2) := Real.rpow_nonneg hxpos.le (δ / 2)
        have hprod := mul_nonneg (sub_nonneg.mpr hqT) hhalfNN
        nlinarith [hprod]
      _ = Real.rpow x δ := hhalfSq
      _ ≤ N := hN
  have hratio : ((q : ℝ) * (1 + |t|)) / N ≤ (Real.rpow x (δ / 2))⁻¹ := by
    apply (div_le_iff₀ hNpos).2
    simpa [div_eq_mul_inv, mul_comm] using (le_div_iff₀ hhalfPos).2 hprodN
  have hratio' : ((q : ℝ) / N) * (1 + |t|) ≤ Real.rpow x (-δ / 2) := by
    have heq : ((q : ℝ) / N) * (1 + |t|) = ((q : ℝ) * (1 + |t|)) / N := by ring
    calc
      ((q : ℝ) / N) * (1 + |t|) = ((q : ℝ) * (1 + |t|)) / N := heq
      _ ≤ (Real.rpow x (δ / 2))⁻¹ := hratio
      _ = Real.rpow x (-(δ / 2)) := (Real.rpow_neg hxpos.le (δ / 2)).symm
      _ = Real.rpow x (-δ / 2) := by congr 1 <;> ring
  constructor
  · exact hEst'.1
  constructor
  · simpa [mul_comm] using hEst'.2.1
  · calc
      _ ≤ 4 / |t| + 4 * Real.rpow x (-δ / 2) := by
        nlinarith [hEst'.2.2, hratio', abs_nonneg t]
      _ = 4 * (|t|⁻¹ + Real.rpow x (-(δ / 2))) := by ring_nf

end ArtinPrimitiveRoots.TypeII.PD
