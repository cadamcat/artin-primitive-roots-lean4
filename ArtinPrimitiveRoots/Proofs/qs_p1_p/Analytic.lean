import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-POISSON».RootNumber
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-POISSON».P0
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-MATRIX».M1
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# P1 analytic helpers

The initial helper proves absolute convergence of the transformed ideal series. The contour and
Mellin continuation arguments are added below as they are established.
-/

set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain MeasureTheory
open Asymptotics
open Set
open Filter Topology
open scoped FourierTransform
open scoped Interval

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]

private theorem qs_p1_norm_multiset_map_prod_le_one {α : Type} (s : Multiset α)
    (f : α → ℂ) (hf : ∀ x, x ∈ s → ‖f x‖ ≤ 1) : ‖(s.map f).prod‖ ≤ 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, norm_mul]
      exact mul_le_one₀ (hf a (by simp)) (norm_nonneg _) <|
        ih (fun x hx => hf x (Multiset.mem_cons_of_mem hx))

private theorem qs_p1_idealValue_norm_le_one
    (χ : ArtinPrimitiveRoots.A1.HeckeChar K) (hsq : χ ^ 2 = 1)
    (I : Ideal (𝓞 K)) : ‖χ.idealValue I‖ ≤ 1 := by
  classical
  have hχ : ∀ x : IdeleClassGroup (𝓞 K) K,
    ‖((χ x : ℂˣ) : ℂ)‖ = 1 := by
    intro x
    have hpow : (χ x : ℂˣ) ^ 2 = 1 := by
      have h := congrArg (fun ψ : ArtinPrimitiveRoots.A1.HeckeChar K => ψ x) hsq
      simpa using h
    have hval : (((χ x : ℂˣ) : ℂ) ^ 2) = 1 := congrArg Units.val hpow
    have hnorm : ‖((χ x : ℂˣ) : ℂ)‖ ^ 2 = 1 := by
      rw [← norm_pow, hval]
      norm_num
    nlinarith [norm_nonneg (((χ x : ℂˣ) : ℂ))]
  have hprime (v : ArtinPrimitiveRoots.A1.FinPlace K) :
      ‖χ.primeValue v‖ ≤ 1 := by
    unfold ArtinPrimitiveRoots.A1.HeckeChar.primeValue
    split_ifs with hv
    · have hχ' := hχ (IdeleClassGroup.ofAdicCompletion
        (𝓞 K) K v (ArtinPrimitiveRoots.A1.toLoc v
          (Units.mk0 (ArtinPrimitiveRoots.A1.unif v)
            (ArtinPrimitiveRoots.A1.unif_ne_zero v))))
      exact le_of_eq (by simpa [ArtinPrimitiveRoots.A1.HeckeChar.loc] using hχ')
    · simp
  unfold ArtinPrimitiveRoots.A1.HeckeChar.idealValue
  apply qs_p1_norm_multiset_map_prod_le_one
  intro P hP
  by_cases h : P.IsPrime ∧ P ≠ ⊥
  · simpa [h] using hprime ⟨P, h.1, h.2⟩
  · simp [h]

/-- The transformed ideal series in the frozen P1 statement is absolutely summable. -/
theorem qs_p1_dual_summable [IsTotallyComplex K]
    (χ : ArtinPrimitiveRoots.A1.HeckeChar K) (f : Ideal (𝓞 K))
    (hf : IsPrimitiveConductor χ f) (hsq : χ ^ 2 = 1) (hne : χ ≠ 1)
    (hinf : ∀ w : InfinitePlace K, ∀ u : w.Completionˣ, χ.locInf w u = 1)
    (h : ℝ → ℂ) (hh : IsQSWeight h) (X : ℝ) (hX : 0 < X) :
    Summable (fun a : {I : Ideal (𝓞 K) // I ≠ ⊥} =>
      ‖χ.idealValue a.1 * qsTransform K h
        (X * (Ideal.absNorm a.1 : ℝ) / (Ideal.absNorm f : ℝ))‖) := by
  have hf0 : f ≠ ⊥ := hf.1
  have hNf0 : Ideal.absNorm f ≠ 0 := by
    intro hN
    exact hf0 (Ideal.absNorm_eq_zero_iff.mp hN)
  have hNf : 0 < (Ideal.absNorm f : ℝ) := Nat.cast_pos.mpr (Nat.pos_iff_ne_zero.mpr hNf0)
  let c : ℝ := X / (Ideal.absNorm f : ℝ)
  have hc : 0 < c := div_pos hX hNf
  obtain ⟨_, ⟨C, hC, hbound⟩⟩ :=
    qs_transform_bounds_P0 (K := K) h hh 2 0 2 (by norm_num)
  let D : ℝ := C * c ^ (-2 : ℝ)
  have hD : 0 ≤ D := mul_nonneg hC.le (Real.rpow_nonneg (le_of_lt hc) _)
  let g : {I : Ideal (𝓞 K) // I ≠ ⊥} → ℝ := fun a =>
    D * ArtinPrimitiveRoots.Hecke.idealNormRpowTerm (K := K) 2 a.1
  have hg : Summable g := by
    have hs : Summable (fun I : Ideal (𝓞 K) =>
        ArtinPrimitiveRoots.Hecke.idealNormRpowTerm (K := K) 2 I) :=
      ArtinPrimitiveRoots.Hecke.summable_idealNormRpow (K := K) (by norm_num)
    exact (hs.mul_left D).subtype (fun I : Ideal (𝓞 K) => I ≠ ⊥)
  apply Summable.of_norm_bounded hg
  intro a
  have hNa0 : Ideal.absNorm a.1 ≠ 0 := by
    intro hN
    exact a.2 (Ideal.absNorm_eq_zero_iff.mp hN)
  have hn : 0 < (Ideal.absNorm a.1 : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_iff_ne_zero.mpr hNa0)
  have hx : 0 < X * (Ideal.absNorm a.1 : ℝ) / (Ideal.absNorm f : ℝ) :=
    div_pos (mul_pos hX hn) hNf
  have hxform : X * (Ideal.absNorm a.1 : ℝ) / (Ideal.absNorm f : ℝ) =
      c * (Ideal.absNorm a.1 : ℝ) := by
    dsimp [c]
    ring
  have hscale :
      (X * (Ideal.absNorm a.1 : ℝ) / (Ideal.absNorm f : ℝ)) ^ (-2 : ℝ) =
        c ^ (-2 : ℝ) * (Ideal.absNorm a.1 : ℝ) ^ (-2 : ℝ) := by
    rw [hxform, Real.mul_rpow (le_of_lt hc) (le_of_lt hn)]
  have hT : ‖qsTransform K h
      (X * (Ideal.absNorm a.1 : ℝ) / (Ideal.absNorm f : ℝ))‖ ≤
        C * (X * (Ideal.absNorm a.1 : ℝ) / (Ideal.absNorm f : ℝ)) ^ (-2 : ℝ) := by
    rcases le_total (X * (Ideal.absNorm a.1 : ℝ) / (Ideal.absNorm f : ℝ)) 1 with hsmall | hlarge
    · simpa [iteratedDeriv_zero] using (hbound _ hx).1 hsmall
    · simpa [iteratedDeriv_zero] using (hbound _ hx).2 hlarge
  have hnormχ := qs_p1_idealValue_norm_le_one χ hsq a.1
  rw [norm_mul]
  have hT' := hT
  rw [hscale] at hT'
  have hmul := mul_le_mul hnormχ hT' (norm_nonneg _)
    (show 0 ≤ (1 : ℝ) by norm_num)
  have hterm : ArtinPrimitiveRoots.Hecke.idealNormRpowTerm (K := K) 2 a.1 =
      (Ideal.absNorm a.1 : ℝ) ^ (-2 : ℝ) := by
    simp [ArtinPrimitiveRoots.Hecke.idealNormRpowTerm, hNa0,
      Real.rpow_neg (Nat.cast_nonneg _)]
  simpa [g, D, hterm, mul_assoc] using hmul

private theorem qs_p1_integrable_of_tails {f : ℝ → ℂ} (hcont : Continuous f)
    (A B b : ℝ) (hAB : A ≤ B) (hb : 0 < b)
    (hleft : ∀ x, x < A → f x = 0)
    (hright : ∃ c : ℂ, ∀ x, B < x → f x = c * ((Real.exp (-b * x) : ℝ) : ℂ)) :
    Integrable f := by
  rcases hright with ⟨c, hright⟩
  have hleftI : IntegrableOn f (Set.Iio A) := by
    have hz : IntegrableOn (fun _ : ℝ => (0 : ℂ)) (Set.Iio A) := integrableOn_zero
    apply hz.congr_fun
    · intro x hx
      exact (hleft x hx).symm
    · exact measurableSet_Iio
  have hmidI : IntegrableOn f (Set.Icc A B) :=
    hcont.continuousOn.integrableOn_compact isCompact_Icc
  have hleftMid : IntegrableOn f (Set.Iic B) := by
    have hdecomp : Set.Iic B = Set.Iio A ∪ Set.Icc A B := by
      ext x
      simp only [Set.mem_Iic, Set.mem_Iio, Set.mem_Icc, Set.mem_union]
      constructor
      · intro hx
        by_cases hxa : x < A
        · exact Or.inl hxa
        · right
          constructor
          · exact le_of_not_gt hxa
          · exact hx
      · rintro (hx | ⟨_, hx⟩)
        · exact (lt_of_lt_of_le hx hAB).le
        · exact hx
    rw [hdecomp, integrableOn_union]
    exact ⟨hleftI, hmidI⟩
  have hexpI : IntegrableOn (fun x : ℝ => Real.exp (-b * x)) (Set.Ioi B) :=
    integrableOn_exp_mul_Ioi (by linarith) B
  have hrightI : IntegrableOn f (Set.Ioi B) := by
    have hbase : IntegrableOn (fun x : ℝ => c * ((Real.exp (-b * x) : ℝ) : ℂ))
        (Set.Ioi B) := by
      have hsmul : IntegrableOn (fun x : ℝ => (Real.exp (-b * x)) • c) (Set.Ioi B) :=
        hexpI.smul_const c
      simpa [smul_eq_mul, mul_comm] using hsmul
    apply hbase.congr_fun
    · intro x hx
      exact (hright x hx).symm
    · exact measurableSet_Ioi
  have huniv : Set.univ = Set.Iic B ∪ Set.Ioi B := by
    ext x
    simp only [Set.mem_univ, true_iff, Set.mem_union, Set.mem_Iic, Set.mem_Ioi]
    exact le_or_gt x B
  rw [← integrableOn_univ, huniv, integrableOn_union]
  exact ⟨hleftMid, hrightI⟩

private theorem qs_p1_integrable_of_exponential_tails {f : ℝ → ℂ}
    (hcont : Continuous f) (A B a b Cleft Cright : ℝ)
    (hAB : A ≤ B) (ha : 0 < a) (hb : 0 < b)
    (hCleft : 0 ≤ Cleft) (hCright : 0 ≤ Cright)
    (hleft : ∀ x, x < A → ‖f x‖ ≤ Cleft * Real.exp (a * x))
    (hright : ∀ x, B < x → ‖f x‖ ≤ Cright * Real.exp (-b * x)) : Integrable f := by
  have hleftExp : IntegrableOn (fun x : ℝ => Real.exp (a * x)) (Set.Iio A) := by
    exact (integrableOn_exp_mul_Iic ha A).mono_set Set.Iio_subset_Iic_self
  have hleftMajor : IntegrableOn
      (fun x : ℝ => Cleft * Real.exp (a * x)) (Set.Iio A) := by
    change Integrable (fun x : ℝ => Cleft * Real.exp (a * x))
      (volume.restrict (Set.Iio A))
    exact hleftExp.const_mul Cleft
  have hleftI : IntegrableOn f (Set.Iio A) := by
    change Integrable f (volume.restrict (Set.Iio A))
    change Integrable (fun x : ℝ => Cleft * Real.exp (a * x))
      (volume.restrict (Set.Iio A)) at hleftMajor
    refine hleftMajor.mono' (hcont.aestronglyMeasurable.restrict) ?_
    filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
    exact hleft x hx
  have hmidI : IntegrableOn f (Set.Icc A B) :=
    hcont.continuousOn.integrableOn_compact isCompact_Icc
  have hleftMid : IntegrableOn f (Set.Iic B) := by
    have hdecomp : Set.Iic B = Set.Iio A ∪ Set.Icc A B := by
      ext x
      simp only [Set.mem_Iic, Set.mem_Iio, Set.mem_Icc, Set.mem_union]
      constructor
      · intro hx
        by_cases hxa : x < A
        · exact Or.inl hxa
        · right
          exact ⟨le_of_not_gt hxa, hx⟩
      · rintro (hx | ⟨_, hx⟩)
        · exact (lt_of_lt_of_le hx hAB).le
        · exact hx
    rw [hdecomp, integrableOn_union]
    exact ⟨hleftI, hmidI⟩
  have hrightExp : IntegrableOn (fun x : ℝ => Real.exp (-b * x)) (Set.Ioi B) :=
    integrableOn_exp_mul_Ioi (by linarith) B
  have hrightMajor : IntegrableOn
      (fun x : ℝ => Cright * Real.exp (-b * x)) (Set.Ioi B) := by
    change Integrable (fun x : ℝ => Cright * Real.exp (-b * x))
      (volume.restrict (Set.Ioi B))
    exact hrightExp.const_mul Cright
  have hrightI : IntegrableOn f (Set.Ioi B) := by
    change Integrable f (volume.restrict (Set.Ioi B))
    change Integrable (fun x : ℝ => Cright * Real.exp (-b * x))
      (volume.restrict (Set.Ioi B)) at hrightMajor
    refine hrightMajor.mono' (hcont.aestronglyMeasurable.restrict) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hright x hx
  have huniv : Set.univ = Set.Iic B ∪ Set.Ioi B := by
    ext x
    simp only [Set.mem_univ, true_iff, Set.mem_union, Set.mem_Iic, Set.mem_Ioi]
    exact le_or_gt x B
  rw [← integrableOn_univ, huniv, integrableOn_union]
  exact ⟨hleftMid, hrightI⟩

private def qsP1MellinLogKernel (c : ℝ) (h : ℝ → ℂ) (u : ℝ) : ℂ :=
  (Real.exp (-c * u) : ℝ) • h (Real.exp (-u))

private def qsP1LogKernel (h : ℝ → ℂ) (u : ℝ) : ℂ :=
  qsP1MellinLogKernel 2 h u

private theorem qs_p1_iteratedDeriv_logKernel_integrable
    (h : ℝ → ℂ) (hh : IsQSWeight h) (c : ℝ) (hc : 0 < c) (j : ℕ) :
    Integrable (fun u : ℝ => iteratedDeriv j (qsP1MellinLogKernel c h) u) := by
  obtain ⟨B, hB⟩ := hh.2.1
  obtain ⟨δ, hδ, hconst⟩ := hh.2.2
  let B₀ := max B 1
  let δ₀ := min δ (1 / 2)
  have hB₀ : 0 < B₀ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hδ₀ : 0 < δ₀ := lt_min hδ (by norm_num)
  have hδ₀δ : δ₀ ≤ δ := min_le_left _ _
  have hδ₀_le : δ₀ ≤ 1 / 2 := min_le_right _ _
  let A := -Real.log B₀
  let C := -Real.log δ₀
  have hAC : A ≤ C := by
    have hA : A ≤ 0 := by
      dsimp [A]
      exact neg_nonpos.mpr (Real.log_nonneg (by dsimp [B₀]; exact le_max_right _ _))
    have hC : 0 ≤ C := by
      dsimp [C]
      have hδ₀_le_one : δ₀ ≤ 1 := hδ₀_le.trans (by norm_num)
      exact neg_nonneg.mpr (Real.log_nonpos hδ₀.le hδ₀_le_one)
    linarith
  have hker : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (qsP1MellinLogKernel c h) := by
    have hhs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h := hh.1
    unfold qsP1MellinLogKernel
    fun_prop
  have hdercont : Continuous (fun u : ℝ => iteratedDeriv j (qsP1MellinLogKernel c h) u) :=
    hker.continuous_iteratedDeriv j (by simp)
  have hleft : ∀ u : ℝ, u < A → iteratedDeriv j (qsP1MellinLogKernel c h) u = 0 := by
    intro u hu
    have hloc : qsP1MellinLogKernel c h =ᶠ[𝓝 u] (fun _ : ℝ => (0 : ℂ)) := by
      filter_upwards [IsOpen.mem_nhds isOpen_Iio hu] with v hv
      change v < A at hv
      have hlog : Real.log B₀ < -v := by
        have := neg_lt_neg hv
        simpa [A] using this
      have hnorm : B₀ < Real.exp (-v) := by
        have he := Real.exp_lt_exp.mpr hlog
        simpa [Real.exp_log hB₀] using he
      have hzero := hB (Real.exp (-v)) (le_trans (le_max_left _ _) hnorm.le)
      simp [qsP1MellinLogKernel, hzero]
    rw [hloc.iteratedDeriv_eq j]
    simp [iteratedDeriv_const]
  have hright : ∃ coef : ℂ, ∀ u : ℝ, C < u →
      iteratedDeriv j (qsP1MellinLogKernel c h) u =
        coef * ((Real.exp (-c * u) : ℝ) : ℂ) := by
    let coef : ℂ := ((((-c : ℝ) ^ j) : ℝ) : ℂ) * h 0
    refine ⟨coef, ?_⟩
    intro u hu
    have hloc : qsP1MellinLogKernel c h =ᶠ[𝓝 u]
        (fun v : ℝ => (Real.exp (-c * v) : ℝ) • h 0) := by
      filter_upwards [IsOpen.mem_nhds isOpen_Ioi hu] with v hv
      change C < v at hv
      have hlog : -v < Real.log δ₀ := by
        have := neg_lt_neg hv
        simpa [C] using this
      have hnorm : Real.exp (-v) < δ₀ := by
        have he := Real.exp_lt_exp.mpr hlog
        simpa [Real.exp_log hδ₀] using he
      have hval := hconst (Real.exp (-v))
        ⟨(Real.exp_pos _).le, hnorm.le.trans hδ₀δ⟩
      simpa [qsP1MellinLogKernel, hval]
    have hEq := hloc.iteratedDeriv_eq j
    have hexp : iteratedDeriv j (fun v : ℝ => Real.exp (-c * v)) u =
        (-c : ℝ) ^ j * Real.exp (-c * u) := by
      simpa using congrFun (iteratedDeriv_exp_const_mul j (-c : ℝ)) u
    rw [hEq]
    have hExpCont : ContDiffAt ℝ (j : ℕ∞) (fun v : ℝ => Real.exp (-c * v)) u := by
      fun_prop
    rw [iteratedDeriv_smul_const hExpCont (h 0), hexp]
    dsimp [coef]
    simp only [smul_eq_mul, Complex.ofReal_mul]
    ring
  exact qs_p1_integrable_of_tails hdercont A C c hAC hc hleft hright

private theorem qs_p1_mellin_convergent (h : ℝ → ℂ) (hh : IsQSWeight h)
    (s : ℂ) (hs : 0 < s.re) : MellinConvergent h s := by
  obtain ⟨B, hB⟩ := hh.2.1
  have hlocal : LocallyIntegrableOn h (Set.Ioi (0 : ℝ)) :=
    hh.1.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi
  have htop : h =O[atTop] (fun x : ℝ => x ^ (-(s.re + 1) : ℝ)) := by
    rw [Asymptotics.isBigO_iff_eventually]
    filter_upwards [eventually_atTop.2 ⟨1, fun _ hc => hc⟩] with C hC
    filter_upwards [eventually_atTop.2 ⟨max B 1, fun _ hx => hx⟩] with x hx
    have hxB : B ≤ x := (le_max_left _ _).trans hx
    simp [hB x hxB]
    have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
    positivity
  have hbot : h =O[nhdsWithin 0 (Set.Ioi (0 : ℝ))] (fun _ : ℝ => (1 : ℂ)) := by
    simpa using
      (hh.1.continuous.continuousAt.mono_left nhdsWithin_le_nhds).isBigO_one ℂ
  exact mellinConvergent_of_isBigO_rpow (a := s.re + 1) (b := 0) hlocal htop
    (by linarith) (by simpa using hbot) hs

/-- The Mellin transform of the indicator of `(0, δ]`. -/
private theorem qs_p1_mellin_indicator_Ioc {δ : ℝ} (hδ : 0 < δ) (s : ℂ)
    (hs : 0 < s.re) :
    mellin (Set.indicator (Set.Ioc (0 : ℝ) δ) (fun _ : ℝ => (1 : ℂ))) s =
      (δ : ℂ) ^ s / s := by
  let f : ℝ → ℂ := Set.indicator (Set.Ioc (0 : ℝ) δ) (fun _ => 1)
  have hscaled : (fun t : ℝ => f (δ * t)) =
      Set.indicator (Set.Ioc (0 : ℝ) 1) (fun _ => (1 : ℂ)) := by
    funext t
    by_cases ht : t ∈ Set.Ioc (0 : ℝ) 1
    · have hδt : δ * t ∈ Set.Ioc (0 : ℝ) δ := by
        constructor
        · exact mul_pos hδ ht.1
        · nlinarith [mul_le_mul_of_nonneg_left ht.2 hδ.le]
      simp [f, ht, hδt]
    · have hδt : δ * t ∉ Set.Ioc (0 : ℝ) δ := by
        intro h
        apply ht
        constructor
        · exact (mul_pos_iff_of_pos_left hδ).mp h.1
        · exact (mul_le_mul_iff_of_pos_left hδ).mp (by simpa using h.2)
      simp [f, ht, hδt]
  have hbase := (hasMellin_one_Ioc hs).2
  have hcomp := mellin_comp_mul_left f s hδ
  rw [hscaled] at hcomp
  rw [hbase] at hcomp
  simp only [smul_eq_mul] at hcomp
  have hδpow : (δ : ℂ) ^ s ≠ 0 := by
    apply Complex.cpow_ne_zero_iff.mpr
    left
    exact_mod_cast hδ.ne'
  calc
    mellin (Set.indicator (Set.Ioc 0 δ) fun _ : ℝ => (1 : ℂ)) s =
        (δ : ℂ) ^ s * ((δ : ℂ) ^ (-s) *
          mellin (Set.indicator (Set.Ioc 0 δ) fun _ : ℝ => (1 : ℂ)) s) := by
            rw [Complex.cpow_neg]
            simp [hδpow, mul_assoc]
    _ = (δ : ℂ) ^ s * (1 / s) := by
          exact congrArg (fun z : ℂ => (δ : ℂ) ^ s * z) hcomp.symm
    _ = (δ : ℂ) ^ s / s := by ring

/-- Mellin transform with the constant near zero separated as its meromorphic term. -/
def qsP1Mellin (h : ℝ → ℂ) (δ : ℝ) (s : ℂ) : ℂ :=
  mellin (fun x => h x - (if x ≤ δ then h 0 else 0)) s +
    ((δ : ℂ) ^ s * h 0 / s)

/-- On the half-plane of convergence, the regularized transform equals the raw Mellin transform. -/
theorem qs_p1_regularized_mellin_agrees (h : ℝ → ℂ) (hh : IsQSWeight h)
    (δ : ℝ) (hδ : 0 < δ)
    (hconst : ∀ x ∈ Set.Icc (0 : ℝ) δ, h x = h 0) (s : ℂ) (hs : 0 < s.re) :
    qsP1Mellin h δ s = mellin h s := by
  let c : ℝ → ℂ := fun x => if x ≤ δ then h 0 else 0
  let i : ℝ → ℂ := Set.indicator (Set.Ioc (0 : ℝ) δ) (fun _ => h 0)
  have hci : ∀ x ∈ Set.Ioi (0 : ℝ), c x = i x := by
    intro x hx
    by_cases hxd : x ≤ δ
    · have hxi : x ∈ Set.Ioc (0 : ℝ) δ := ⟨hx, hxd⟩
      simp [c, i, hxd, hxi]
    · have hxi : x ∉ Set.Ioc (0 : ℝ) δ := by
        intro hmem
        exact hxd hmem.2
      simp [c, i, hxd, hxi]
  have hconstM : MellinConvergent i s := by
    have hbase := (hasMellin_one_Ioc hs).1
    let f : ℝ → ℂ := Set.indicator (Set.Ioc (0 : ℝ) δ) (fun _ => (1 : ℂ))
    have heq : (fun x : ℝ => f (δ * x)) =
        Set.indicator (Set.Ioc (0 : ℝ) 1) (fun _ => (1 : ℂ)) := by
      funext x
      by_cases hx : x ∈ Set.Ioc (0 : ℝ) 1
      · have hδx : δ * x ∈ Set.Ioc (0 : ℝ) δ := by
          constructor
          · exact mul_pos hδ hx.1
          · nlinarith [mul_le_mul_of_nonneg_left hx.2 hδ.le]
        simp [f, hx, hδx]
      · have hδx : δ * x ∉ Set.Ioc (0 : ℝ) δ := by
          intro hmem
          apply hx
          constructor
          · exact (mul_pos_iff_of_pos_left hδ).mp hmem.1
          · exact (mul_le_mul_iff_of_pos_left hδ).mp (by simpa using hmem.2)
        simp [f, hx, hδx]
    have hscaled : MellinConvergent (fun x : ℝ => f (δ * x)) s := by
      rw [heq]
      exact hbase
    have hfM : MellinConvergent f s :=
      (MellinConvergent.comp_mul_left (f := f) (s := s) hδ).1 hscaled
    have hconstM' := hfM.const_smul (h 0)
    have hieq : i = fun x => h 0 • f x := by
      funext x
      by_cases hx : x ∈ Set.Ioc (0 : ℝ) δ <;> simp [i, f, hx]
    rw [hieq]
    exact hconstM'
  have hcM : MellinConvergent c s := by
    change IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) • c x) (Set.Ioi 0)
    exact hconstM.congr_fun (fun x hx => by rw [hci x hx]) measurableSet_Ioi
  have hraw : MellinConvergent h s := qs_p1_mellin_convergent h hh s hs
  have hsub := hasMellin_sub hraw hcM
  have hciM : mellin c s = mellin i s := by
    unfold mellin
    change (∫ x in Set.Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) • c x) =
      ∫ x in Set.Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) • i x
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [hci x hx]
  have hiM : mellin i s = (δ : ℂ) ^ s * h 0 / s := by
    have hi : i = fun t => h 0 • Set.indicator (Set.Ioc (0 : ℝ) δ) (fun _ => (1 : ℂ)) t := by
      funext x
      by_cases hx : x ∈ Set.Ioc (0 : ℝ) δ <;> simp [i, hx]
    rw [hi, mellin_const_smul, qs_p1_mellin_indicator_Ioc hδ s hs]
    ring
  unfold qsP1Mellin
  rw [show (fun x : ℝ => h x - (if x ≤ δ then h 0 else 0)) = fun x => h x - c x by rfl]
  rw [hsub.2, hciM, hiM]
  ring

/-- The regularized Mellin transform is differentiable away from its simple pole at zero. -/
theorem qs_p1_regularized_mellin_differentiable (h : ℝ → ℂ) (hh : IsQSWeight h)
    (δ : ℝ) (hδ : 0 < δ)
    (hconst : ∀ x ∈ Set.Icc (0 : ℝ) δ, h x = h 0) :
    DifferentiableOn ℂ (qsP1Mellin h δ) {s : ℂ | s ≠ 0} := by
  obtain ⟨B, hB⟩ := hh.2.1
  let c : ℝ → ℂ := fun x => if x ≤ δ then h 0 else 0
  let r : ℝ → ℂ := fun x => h x - c x
  have hcLoc : LocallyIntegrable c := by
    have hloc : LocallyIntegrable ((Set.Iic δ).indicator (fun _ : ℝ => h 0)) :=
      (locallyIntegrable_const (h 0)).indicator
        (measurableSet_Iic : MeasurableSet (Set.Iic δ))
    have hcEq : c = (Set.Iic δ).indicator (fun _ : ℝ => h 0) := by
      funext x
      by_cases hx : x ≤ δ <;> simp [c, hx, Set.mem_Iic]
    rw [hcEq]
    exact hloc
  have hrLoc : LocallyIntegrableOn r (Set.Ioi (0 : ℝ)) := by
    have hhLoc : LocallyIntegrableOn h (Set.Ioi (0 : ℝ)) :=
      hh.1.continuous.locallyIntegrable.locallyIntegrableOn (Set.Ioi (0 : ℝ))
    have hcLoc' : LocallyIntegrableOn c (Set.Ioi (0 : ℝ)) :=
      hcLoc.locallyIntegrableOn (Set.Ioi (0 : ℝ))
    exact hhLoc.sub hcLoc'
  have hrZeroTop : r =ᶠ[atTop] (fun _ : ℝ => (0 : ℂ)) := by
    let B' : ℝ := max B δ + 1
    filter_upwards [eventually_atTop.2 ⟨B', fun _ hx => hx⟩] with x hx
    have hxmax : max B δ ≤ x := by dsimp [B'] at hx; linarith
    have hxB : B ≤ x := (le_max_left B δ).trans hxmax
    have hδx : δ < x := by
      have hle : δ ≤ max B δ := le_max_right B δ
      linarith
    simp [r, c, hB x hxB, not_le.mpr hδx]
  have hrZeroBot : r =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      (fun _ : ℝ => (0 : ℂ)) := by
    have hδevent : ∀ᶠ x : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), x < δ := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards [isOpen_Iio.mem_nhds hδ] with x hx _
      exact hx
    filter_upwards [hδevent, (eventually_mem_nhdsWithin :
        ∀ᶠ x : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), x ∈ Set.Ioi 0)] with x hxd hx
    have hcx : x ∈ Set.Icc (0 : ℝ) δ := ⟨hx.le, hxd.le⟩
    simp [r, c, hconst x hcx, hxd.le]
  intro s hs
  let a : ℝ := s.re + 1
  let b : ℝ := s.re - 1
  have hrTop : r =O[atTop] (fun x : ℝ => x ^ (-a)) :=
    hrZeroTop.trans_isBigO (isBigO_zero (fun x : ℝ => x ^ (-a)) atTop)
  have hrBot : r =O[nhdsWithin (0 : ℝ) (Set.Ioi 0)] (fun x : ℝ => x ^ (-b)) :=
    hrZeroBot.trans_isBigO
      (isBigO_zero (fun x : ℝ => x ^ (-b)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)))
  have hrDiff : DifferentiableAt ℂ (mellin r) s :=
    mellin_differentiableAt_of_isBigO_rpow (a := a) (b := b) (s := s)
      hrLoc hrTop (by dsimp [a]; linarith) hrBot (by dsimp [b]; linarith)
  have hδc : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  have hterm : DifferentiableAt ℂ (fun z : ℂ => (δ : ℂ) ^ z * h 0 / z) s := by
    have hpow : DifferentiableAt ℂ (fun z : ℂ => (δ : ℂ) ^ z) s :=
      differentiableAt_id.const_cpow (Or.inl hδc)
    exact (hpow.mul_const (h 0)).div differentiableAt_id hs
  change DifferentiableWithinAt ℂ (fun z : ℂ =>
    mellin (fun x : ℝ => h x - (if x ≤ δ then h 0 else 0)) z +
      (δ : ℂ) ^ z * h 0 / z) {z : ℂ | z ≠ 0} s
  exact (hrDiff.add hterm).differentiableWithinAt

private theorem qs_p1_transform_mellin_differentiableAt [IsTotallyComplex K]
    (h : ℝ → ℂ) (hh : IsQSWeight h) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (qsTransform K h) s ∧
      DifferentiableAt ℂ (mellin (qsTransform K h)) s := by
  let A : ℕ := ⌈s.re⌉₊ + 2
  let η : ℝ := s.re / 4
  let b : ℝ := s.re / 2
  have hη : 0 < η := by dsimp [η]; positivity
  have hsA : s.re < (A : ℝ) := by
    have hceil : s.re ≤ (⌈s.re⌉₊ : ℝ) := Nat.le_ceil s.re
    dsimp [A]
    push_cast
    linarith
  obtain ⟨hTdiff, ⟨C, hC, hbd⟩⟩ :=
    qs_transform_bounds_P0 (K := K) h hh A 0 η hη
  have htop : qsTransform K h =O[atTop] (fun x : ℝ => x ^ (-(A : ℝ))) := by
    rw [Asymptotics.isBigO_iff_eventually]
    filter_upwards [eventually_atTop.2 ⟨C, fun _ hx => hx⟩] with M hM
    filter_upwards [eventually_atTop.2 ⟨1, fun _ hx => hx⟩] with x hx
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
    have hT := (hbd x hxpos).2 hx
    have hpow : 0 ≤ x ^ (-(A : ℝ)) := Real.rpow_nonneg hxpos.le _
    calc
      ‖qsTransform K h x‖ ≤ C * x ^ (-(A : ℝ)) := by
        simpa [iteratedDeriv_zero] using hT
      _ ≤ M * ‖x ^ (-(A : ℝ) )‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg hpow]
        exact mul_le_mul_of_nonneg_right hM hpow
  have hηb : η < b := by dsimp [η, b]; linarith
  have hb : b < s.re := by dsimp [b]; linarith
  have hle : ∀ᶠ x : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), x ≤ 1 := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) < 1)] with x hx _
    exact hx.le
  have hbot : qsTransform K h =O[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      (fun x : ℝ => x ^ (-b)) := by
    rw [Asymptotics.isBigO_iff_eventually]
    filter_upwards [eventually_atTop.2 ⟨C, fun _ hx => hx⟩] with M hM
    filter_upwards [hle, (eventually_mem_nhdsWithin :
        ∀ᶠ x : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), x ∈ Set.Ioi 0)] with x hxle hxpos
    have hT := (hbd x hxpos).1 hxle
    have hpow : x ^ (-η) ≤ x ^ (-b) :=
      Real.rpow_le_rpow_of_exponent_ge hxpos hxle (by dsimp [η, b]; linarith)
    have hpowNonneg : 0 ≤ x ^ (-η) := Real.rpow_nonneg hxpos.le _
    have hpowBNonneg : 0 ≤ x ^ (-b) := Real.rpow_nonneg hxpos.le _
    have hM0 : 0 ≤ M := (le_of_lt hC).trans hM
    calc
      ‖qsTransform K h x‖ ≤ C * x ^ (-η) := by
        simpa [iteratedDeriv_zero] using hT
      _ ≤ M * ‖x ^ (-b)‖ := by
        calc
          C * x ^ (-η) ≤ M * x ^ (-η) := mul_le_mul_of_nonneg_right hM hpowNonneg
          _ ≤ M * x ^ (-b) := mul_le_mul_of_nonneg_left hpow hM0
          _ = M * ‖x ^ (-b)‖ := by
            rw [Real.norm_eq_abs, abs_of_nonneg hpowBNonneg]
  have hfc : LocallyIntegrableOn (qsTransform K h) (Set.Ioi 0) :=
    hTdiff.continuousOn.locallyIntegrableOn measurableSet_Ioi
  have hconv := mellinConvergent_of_isBigO_rpow hfc htop hsA hbot hb
  have hdiff := mellin_differentiableAt_of_isBigO_rpow (a := (A : ℝ)) (b := b)
    hfc htop hsA hbot hb
  exact ⟨hconv, hdiff⟩

private theorem qs_p1_prefactor_inv_differentiable [IsTotallyComplex K] :
    Differentiable ℂ (fun s : ℂ => (Hecke.dedekindPrefactor K s)⁻¹) := by
  let d : ℂ := ((|(NumberField.discr K : ℝ)| : ℝ) : ℂ)
  have hd : d ≠ 0 := by
    dsimp [d]
    apply Complex.ofReal_ne_zero.mpr
    apply abs_ne_zero.mpr
    exact_mod_cast NumberField.discr_ne_zero K
  have hpow : Differentiable ℂ (fun s : ℂ => d ^ (s / 2)) := by
    exact (differentiable_id.div_const (2 : ℂ)).const_cpow (Or.inl hd)
  have hpowInv : Differentiable ℂ (fun s : ℂ => (d ^ (s / 2))⁻¹) := by
    apply hpow.inv
    intro s
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl hd)
  have hEq : (fun s : ℂ => (Hecke.dedekindPrefactor K s)⁻¹) =
      fun s : ℂ => (d ^ (s / 2))⁻¹ * (Complex.Gammaℂ s)⁻¹ ^
        NumberField.InfinitePlace.nrComplexPlaces K := by
    funext s
    simp [d, Hecke.dedekindPrefactor, IsTotallyComplex.nrRealPlaces_eq_zero,
      mul_inv, inv_pow]
    ring
  rw [hEq]
  exact hpowInv.mul (Complex.differentiable_Gammaℂ_inv.pow _)

/-- The completed factor multiplying the Hecke L-series in the P1 functional equation. -/
def qsP1CompletedFactor [IsTotallyComplex K] (f : Ideal (𝓞 K)) (s : ℂ) : ℂ :=
  ((Ideal.absNorm f : ℝ) : ℂ) ^ (s / 2) * Hecke.dedekindPrefactor K s

/-- The analytic continuation of the raw Hecke series obtained by dividing out the completed
factor from the root-number witness. -/
def qsP1LContinuation [IsTotallyComplex K] (f : Ideal (𝓞 K)) (Λ : ℂ → ℂ) (s : ℂ) : ℂ :=
  (qsP1CompletedFactor f s)⁻¹ * Λ s

private theorem qs_p1_completedFactor_inv_differentiable [IsTotallyComplex K]
    (f : Ideal (𝓞 K)) (hf0 : f ≠ ⊥) :
    Differentiable ℂ (fun s : ℂ => (qsP1CompletedFactor f s)⁻¹) := by
  let d : ℂ := ((Ideal.absNorm f : ℝ) : ℂ)
  have hd : d ≠ 0 := by
    dsimp [d]
    apply Complex.ofReal_ne_zero.mpr
    intro h
    have hN : Ideal.absNorm f = 0 := by exact_mod_cast h
    exact hf0 (Ideal.absNorm_eq_zero_iff.mp hN)
  have hpow : Differentiable ℂ (fun s : ℂ => d ^ (s / 2)) := by
    exact (differentiable_id.div_const (2 : ℂ)).const_cpow (Or.inl hd)
  have hpowInv : Differentiable ℂ (fun s : ℂ => (d ^ (s / 2))⁻¹) := by
    apply hpow.inv
    intro s
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl hd)
  have hEq : (fun s : ℂ => (qsP1CompletedFactor f s)⁻¹) =
      fun s : ℂ => (Hecke.dedekindPrefactor K s)⁻¹ * (d ^ (s / 2))⁻¹ := by
    funext s
    simp [qsP1CompletedFactor, d, mul_inv, mul_comm]
  rw [hEq]
  exact (qs_p1_prefactor_inv_differentiable (K := K)).mul hpowInv

private theorem qs_p1_completedFactor_ne_zero [IsTotallyComplex K]
    (f : Ideal (𝓞 K)) (hf0 : f ≠ ⊥) {s : ℂ} (hs : 0 < s.re) :
    qsP1CompletedFactor f s ≠ 0 := by
  have hN : Ideal.absNorm f ≠ 0 := by
    intro h
    exact hf0 (Ideal.absNorm_eq_zero_iff.mp h)
  have hd : ((Ideal.absNorm f : ℝ) : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact_mod_cast hN
  have hpow : ((Ideal.absNorm f : ℝ) : ℂ) ^ (s / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hd)
  have hdisc : ((|(NumberField.discr K : ℝ)| : ℝ) : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact abs_ne_zero.mpr (by exact_mod_cast NumberField.discr_ne_zero K)
  have hdiscPow : ((|(NumberField.discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hdisc)
  have hbase : (2 * Real.pi : ℂ) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hgammaPow : (2 * Real.pi : ℂ) ^ (-s) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hbase)
  have hgamma : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs
  have hGammaC : Complex.Gammaℂ s ≠ 0 := by
    rw [Complex.Gammaℂ_def]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hgammaPow) hgamma
  have hprefactor : Hecke.dedekindPrefactor K s ≠ 0 := by
    rw [Hecke.dedekindPrefactor, IsTotallyComplex.nrRealPlaces_eq_zero]
    simp only [pow_zero, one_mul]
    exact mul_ne_zero hdiscPow (pow_ne_zero _ hGammaC)
  exact mul_ne_zero hpow hprefactor

/-- Dividing the completed root-number witness gives an entire continuation of the raw Hecke
Dirichlet series, with the induced functional equation on `0 < Re s < 1`. -/
theorem qs_p1_Lcont_of_root_number [IsTotallyComplex K]
    (χ : ArtinPrimitiveRoots.A1.HeckeChar K) (f : Ideal (𝓞 K))
    (hf : IsPrimitiveConductor χ f) (hsq : χ ^ 2 = 1) (hne : χ ≠ 1)
    (hinf : ∀ w : InfinitePlace K, ∀ u : w.Completionˣ, χ.locInf w u = 1) :
    ∃ Λ Lc : ℂ → ℂ, Differentiable ℂ Λ ∧ Differentiable ℂ Lc ∧
      (∀ s : ℂ, 1 < s.re → Lc s = heckeLSeries χ s) ∧
      (∀ s : ℂ, 0 < s.re → s.re < 1 →
        Lc s = (qsP1CompletedFactor f s)⁻¹ *
          qsP1CompletedFactor f (1 - s) * Lc (1 - s)) := by
  obtain ⟨Λ, hΛdiff, hΛseries, hΛFE, _⟩ :=
    qs_quadratic_FE_root_one χ f hf hsq hne hinf
  let Lc : ℂ → ℂ := qsP1LContinuation f Λ
  have hLdiff : Differentiable ℂ Lc := by
    change Differentiable ℂ (fun s : ℂ =>
      (qsP1CompletedFactor f s)⁻¹ * Λ s)
    exact (qs_p1_completedFactor_inv_differentiable (K := K) f hf.1).mul hΛdiff
  refine ⟨Λ, Lc, hΛdiff, hLdiff, ?_, ?_⟩
  · intro s hs
    have hQ : qsP1CompletedFactor f s ≠ 0 :=
      qs_p1_completedFactor_ne_zero (K := K) f hf.1 (by linarith)
    have hΛ : Λ s = qsP1CompletedFactor f s * heckeLSeries χ s := by
      simpa [qsP1CompletedFactor] using hΛseries s hs
    calc
      Lc s = (qsP1CompletedFactor f s)⁻¹ * Λ s := rfl
      _ = (qsP1CompletedFactor f s)⁻¹ *
          (qsP1CompletedFactor f s * heckeLSeries χ s) := by rw [hΛ]
      _ = heckeLSeries χ s := by simp [hQ, mul_assoc]
  · intro s hs0 hs1
    have hs' : 0 < (1 - s).re := by
      rw [Complex.sub_re, Complex.one_re]
      linarith
    have hQs : qsP1CompletedFactor f s ≠ 0 :=
      qs_p1_completedFactor_ne_zero (K := K) f hf.1 hs0
    have hQ1 : qsP1CompletedFactor f (1 - s) ≠ 0 :=
      qs_p1_completedFactor_ne_zero (K := K) f hf.1 hs'
    have hQmul : qsP1CompletedFactor f (1 - s) * Lc (1 - s) = Λ (1 - s) := by
      calc
        qsP1CompletedFactor f (1 - s) * Lc (1 - s) =
            qsP1CompletedFactor f (1 - s) *
              ((qsP1CompletedFactor f (1 - s))⁻¹ * Λ (1 - s)) := rfl
        _ = Λ (1 - s) := by simp [hQ1, mul_assoc]
    calc
      Lc s = (qsP1CompletedFactor f s)⁻¹ * Λ s := rfl
      _ = (qsP1CompletedFactor f s)⁻¹ * Λ (1 - s) := by rw [← hΛFE s]
      _ = (qsP1CompletedFactor f s)⁻¹ *
          (qsP1CompletedFactor f (1 - s) * Lc (1 - s)) := by rw [← hQmul]
      _ = (qsP1CompletedFactor f s)⁻¹ *
          qsP1CompletedFactor f (1 - s) * Lc (1 - s) := by ring

private theorem qs_p1_prefactor_differentiableAt [IsTotallyComplex K]
    {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (Hecke.dedekindPrefactor K) s := by
  let d : ℂ := ((|(NumberField.discr K : ℝ)| : ℝ) : ℂ)
  have hd : d ≠ 0 := by
    dsimp [d]
    apply Complex.ofReal_ne_zero.mpr
    apply abs_ne_zero.mpr
    exact_mod_cast NumberField.discr_ne_zero K
  have hpow : DifferentiableAt ℂ (fun z : ℂ => d ^ (z / 2)) s :=
    (differentiableAt_id.div_const (2 : ℂ)).const_cpow (Or.inl hd)
  have hGamma : DifferentiableAt ℂ Complex.Gamma s := by
    apply Complex.differentiableAt_Gamma
    intro n hn
    have hre := congrArg Complex.re hn
    have hneg : ((-(n : ℂ)).re) ≤ 0 := by simp
    rw [hre] at hs
    linarith
  have hcpow : DifferentiableAt ℂ (fun z : ℂ => (2 * Real.pi : ℂ) ^ (-z)) s := by
    apply (differentiableAt_id.neg.const_cpow ?_)
    left
    exact mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hGammaC : DifferentiableAt ℂ (fun z : ℂ => Complex.Gammaℂ z) s := by
    have h := (hcpow.mul hGamma).const_mul (2 : ℂ)
    simpa [Complex.Gammaℂ_def, mul_assoc] using h
  have hEq : (fun z : ℂ => Hecke.dedekindPrefactor K z) =
      fun z : ℂ => d ^ (z / 2) * (Complex.Gammaℂ z) ^
        NumberField.InfinitePlace.nrComplexPlaces K := by
    funext z
    simp [d, Hecke.dedekindPrefactor, IsTotallyComplex.nrRealPlaces_eq_zero]
  change DifferentiableAt ℂ (fun z : ℂ => Hecke.dedekindPrefactor K z) s
  rw [hEq]
  exact hpow.mul (hGammaC.pow _)

private theorem qs_p1_gammaRatio_differentiableAt [IsTotallyComplex K]
    {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ (qsGammaRatio K) s := by
  have hnum := qs_p1_prefactor_differentiableAt (K := K) hs
  have hinv := qs_p1_prefactor_inv_differentiable (K := K)
  have hden : DifferentiableAt ℂ
      (fun z : ℂ => (Hecke.dedekindPrefactor K (1 - z))⁻¹) s :=
    hinv.differentiableAt.comp s (by fun_prop)
  change DifferentiableAt ℂ
    (fun z : ℂ => Hecke.dedekindPrefactor K z *
      (Hecke.dedekindPrefactor K (1 - z))⁻¹) s
  exact hnum.mul hden

private theorem qs_p1_iteratedDeriv_mul_one {W V : ℝ → ℂ} {u : ℝ}
    (hW : ContDiffAt ℝ ((2 : ℕ∞) : WithTop ℕ∞) W u)
    (hV : ContDiffAt ℝ ((2 : ℕ∞) : WithTop ℕ∞) V u) :
    iteratedDeriv 1 (W * V) u = deriv W u * V u + W u * deriv V u := by
  simp only [iteratedDeriv_one]
  exact deriv_mul (hW.differentiableAt (by norm_num)) (hV.differentiableAt (by norm_num))

private theorem qs_p1_iteratedDeriv_mul_two {W V : ℝ → ℂ} {u : ℝ}
    (hW : ContDiffAt ℝ ((2 : ℕ∞) : WithTop ℕ∞) W u)
    (hV : ContDiffAt ℝ ((2 : ℕ∞) : WithTop ℕ∞) V u) :
    iteratedDeriv 2 (W * V) u = iteratedDeriv 2 W u * V u +
      2 * deriv W u * deriv V u + W u * iteratedDeriv 2 V u := by
  have h := iteratedDeriv_mul hW hV
  have h' : iteratedDeriv 2 (W * V) u =
      ∑ i ∈ Finset.range 3, (Nat.choose 2 i : ℂ) * iteratedDeriv i W u *
        iteratedDeriv (2 - i) V u := by
    simpa only [show 2 + 1 = 3 by norm_num] using h
  rw [h']
  norm_num [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one]
  ring

private theorem qs_p1_transform_log_comp_deriv1 [IsTotallyComplex K]
    (h : ℝ → ℂ) (hh : IsQSWeight h) (u : ℝ) :
    iteratedDeriv 1 (fun v : ℝ => qsTransform K h (Real.exp (-v))) u =
      deriv (qsTransform K h) (Real.exp (-u)) * (-Real.exp (-u)) := by
  obtain ⟨hTdiff, _⟩ := qs_transform_bounds_P0 (K := K) h hh 1 0 1 (by norm_num)
  let T : ℝ → ℂ := qsTransform K h
  let φ : ℝ → ℝ := fun v => Real.exp (-v)
  have hφ : DifferentiableAt ℝ φ u := by fun_prop
  have hTdiff' : ContDiffOn ℝ 2 T (Set.Ioi 0) := by
    change ContDiffOn ℝ 2 (qsTransform K h) (Set.Ioi 0)
    exact hTdiff.of_le (by norm_num)
  have hTu : ContDiffAt ℝ 2 T (φ u) := by
    exact hTdiff'.contDiffAt (isOpen_Ioi.mem_nhds (Real.exp_pos _))
  have hφder : deriv φ u = -Real.exp (-u) := by
    have h := congrFun (iteratedDeriv_exp_const_mul 1 (-1 : ℝ)) u
    simpa [φ, iteratedDeriv_one, mul_comm] using h
  change iteratedDeriv 1 (fun v : ℝ => T (φ v)) u =
    deriv T (Real.exp (-u)) * (-Real.exp (-u))
  rw [iteratedDeriv_one]
  have hcompD : HasDerivAt (fun v : ℝ => T (φ v))
      (deriv φ u • deriv T (φ u)) u :=
    (hTu.differentiableAt (by norm_num)).hasDerivAt.scomp u hφ.hasDerivAt
  have hcompD' : HasDerivAt (fun v : ℝ => T (φ v))
      (deriv T (φ u) * deriv φ u) u := by
    simpa [smul_eq_mul, mul_comm] using hcompD
  have hfinal := hcompD'.deriv
  rw [show φ u = Real.exp (-u) by rfl, hφder] at hfinal
  simpa [Complex.ofReal_neg, mul_comm] using hfinal

private theorem qs_p1_transform_log_comp_deriv2 [IsTotallyComplex K]
    (h : ℝ → ℂ) (hh : IsQSWeight h) (u : ℝ) :
    iteratedDeriv 2 (fun v : ℝ => qsTransform K h (Real.exp (-v))) u =
      iteratedDeriv 2 (qsTransform K h) (Real.exp (-u)) * (Real.exp (-u)) ^ 2 +
        deriv (qsTransform K h) (Real.exp (-u)) * Real.exp (-u) := by
  obtain ⟨hTdiff, _⟩ := qs_transform_bounds_P0 (K := K) h hh 1 0 1 (by norm_num)
  let T : ℝ → ℂ := qsTransform K h
  let φ : ℝ → ℝ := fun v => Real.exp (-v)
  have hφAt : ContDiffAt ℝ 2 φ u := by fun_prop
  have hTdiff' : ContDiffOn ℝ 2 T (Set.Ioi 0) := by
    change ContDiffOn ℝ 2 (qsTransform K h) (Set.Ioi 0)
    exact hTdiff.of_le (by norm_num)
  have hTu : ContDiffAt ℝ 2 T (φ u) := by
    exact hTdiff'.contDiffAt (isOpen_Ioi.mem_nhds (Real.exp_pos _))
  have hφder : deriv φ u = -Real.exp (-u) := by
    have h := congrFun (iteratedDeriv_exp_const_mul 1 (-1 : ℝ)) u
    simpa [φ, iteratedDeriv_one, mul_comm] using h
  have hφder2 : iteratedDeriv 2 φ u = Real.exp (-u) := by
    have h := congrFun (iteratedDeriv_exp_const_mul 2 (-1 : ℝ)) u
    simpa [φ, mul_comm, pow_two] using h
  have hTderAt : ContDiffAt ℝ 1 (deriv T) (φ u) :=
    hTu.derivWithin (by norm_num)
  let φ' : ℝ → ℝ := deriv (𝕜 := ℝ) φ
  let A : ℝ → ℂ := fun v => deriv T (φ v)
  let B : ℝ → ℂ := fun v => (φ' v : ℂ)
  have hACont : ContDiffAt ℝ 1 A u := by
    change ContDiffAt ℝ 1 (fun v => deriv T (φ v)) u
    exact hTderAt.comp u (hφAt.of_le (by norm_num))
  have hBCont : ContDiffAt ℝ 1 B u := by
    change ContDiffAt ℝ 1 (fun v => Complex.ofReal (deriv φ v)) u
    exact Complex.ofRealCLM.contDiff.comp_contDiffAt u (hφAt.derivWithin (by norm_num))
  have hA : DifferentiableAt ℝ A u := hACont.differentiableAt (by norm_num)
  have hB : DifferentiableAt ℝ B u := hBCont.differentiableAt (by norm_num)
  have hVder : deriv (fun v : ℝ => T (φ v)) = fun v => A v * B v := by
    funext v
    have hTv : ContDiffAt ℝ 2 T (φ v) :=
      hTdiff'.contDiffAt (isOpen_Ioi.mem_nhds (Real.exp_pos _))
    have hφv : DifferentiableAt ℝ φ v := by fun_prop
    have hcompV : HasDerivAt (fun w : ℝ => T (φ w))
        (deriv φ v • deriv T (φ v)) v :=
      (hTv.differentiableAt (by norm_num)).hasDerivAt.scomp v hφv.hasDerivAt
    have hcompV' : HasDerivAt (fun w : ℝ => T (φ w))
        (deriv T (φ v) * deriv φ v) v := by
      simpa [smul_eq_mul, mul_comm] using hcompV
    change deriv (fun w : ℝ => T (φ w)) v = _
    simpa [A, B] using hcompV'.deriv
  have hAder : deriv A u = iteratedDeriv 2 T (φ u) * deriv φ u := by
    have hcompA : HasDerivAt (fun v : ℝ => deriv T (φ v))
        (deriv φ u • deriv (deriv T) (φ u)) u :=
      (hTderAt.differentiableAt (by norm_num)).hasDerivAt.scomp u
        (hφAt.differentiableAt (by norm_num)).hasDerivAt
    have hEq := hcompA.deriv
    simpa [A, iteratedDeriv_succ, iteratedDeriv_one, smul_eq_mul, mul_comm] using hEq
  have hφderAt : ContDiffAt ℝ 1 φ' u := by
    simpa [φ'] using hφAt.derivWithin (by norm_num)
  have hBder : deriv (𝕜 := ℝ) B u = (Real.exp (-u) : ℂ) := by
    have hphiSecond : deriv (𝕜 := ℝ) φ' u = Real.exp (-u) := by
      simpa [φ', iteratedDeriv_succ, iteratedDeriv_one] using hφder2
    have hcast : HasDerivAt (fun v : ℝ => (φ' v : ℂ))
        ((deriv (𝕜 := ℝ) φ' u : ℝ) : ℂ) u :=
      HasDerivAt.ofReal_comp ((hφderAt.differentiableAt (by norm_num)).hasDerivAt)
    have hEq : deriv (𝕜 := ℝ) B u = (Real.exp (-u) : ℂ) := by
      change deriv (fun v : ℝ => (φ' v : ℂ)) u = _
      rw [hcast.deriv, hphiSecond]
    exact hEq
  have hVsecond : deriv (𝕜 := ℝ) (deriv (𝕜 := ℝ) (fun v : ℝ => T (φ v))) u =
      deriv A u * B u + A u * deriv B u := by
    calc
      deriv (𝕜 := ℝ) (deriv (𝕜 := ℝ) (fun v : ℝ => T (φ v))) u =
          deriv (𝕜 := ℝ) (fun v : ℝ => A v * B v) u := by
        rw [hVder]
      _ = deriv A u * B u + A u * deriv B u := deriv_mul hA hB
  calc
    iteratedDeriv 2 (fun v : ℝ => T (φ v)) u =
        deriv (𝕜 := ℝ) (deriv (𝕜 := ℝ) (fun v : ℝ => T (φ v))) u := by
          simp [iteratedDeriv_succ, iteratedDeriv_one]
    _ = deriv A u * B u + A u * deriv B u := hVsecond
    _ = iteratedDeriv 2 T (Real.exp (-u)) * (Real.exp (-u)) ^ 2 +
        deriv T (Real.exp (-u)) * Real.exp (-u) := by
          rw [hAder, hBder]
          dsimp [A, B]
          rw [show φ u = Real.exp (-u) by rfl, hφder]
          rw [show φ' u = -Real.exp (-u) by simpa [φ'] using hφder]
          simp only [Complex.ofReal_neg]
          ring_nf

private theorem qs_p1_expWeight_deriv1 (c u : ℝ) :
    deriv (fun v : ℝ => (Real.exp (-c * v) : ℝ) : ℝ → ℂ) u =
      ((-c * Real.exp (-c * u) : ℝ) : ℂ) := by
  let f : ℝ → ℝ := fun v => Real.exp (-c * v)
  have hreal : deriv (𝕜 := ℝ) (F := ℝ) f u = -c * Real.exp (-c * u) := by
    have h := congrFun (iteratedDeriv_exp_const_mul 1 (-c : ℝ)) u
    simpa [f, iteratedDeriv_one, mul_comm] using h
  have hhas : HasDerivAt f (deriv (𝕜 := ℝ) (F := ℝ) f u) u :=
    (by fun_prop : DifferentiableAt ℝ f u).hasDerivAt
  have hcast : HasDerivAt (fun v : ℝ => (f v : ℂ)) ((deriv f u : ℝ) : ℂ) u :=
    HasDerivAt.ofReal_comp hhas
  change deriv (fun v : ℝ => (f v : ℂ)) u = _
  rw [hcast.deriv, hreal]

private theorem qs_p1_expWeight_deriv2 (c u : ℝ) :
    iteratedDeriv 2 (fun v : ℝ => (Real.exp (-c * v) : ℝ) : ℝ → ℂ) u =
      ((c ^ 2 * Real.exp (-c * u) : ℝ) : ℂ) := by
  let f : ℝ → ℝ := fun v => Real.exp (-c * v)
  let E : ℝ → ℂ := fun v => (f v : ℂ)
  have hEderiv : deriv (𝕜 := ℝ) (F := ℂ) E =
      fun v => (deriv (𝕜 := ℝ) (F := ℝ) f v : ℂ) := by
    funext v
    have hhas : HasDerivAt f (deriv (𝕜 := ℝ) (F := ℝ) f v) v :=
      (by fun_prop : DifferentiableAt ℝ f v).hasDerivAt
    have hcast : HasDerivAt (fun w : ℝ => (f w : ℂ))
        ((deriv (𝕜 := ℝ) (F := ℝ) f v : ℝ) : ℂ) v :=
      HasDerivAt.ofReal_comp hhas
    change deriv (fun w : ℝ => (f w : ℂ)) v = _
    exact hcast.deriv
  have hreal2 : deriv (𝕜 := ℝ) (F := ℝ)
      (deriv (𝕜 := ℝ) (F := ℝ) f) u =
      c ^ 2 * Real.exp (-c * u) := by
    have h := congrFun (iteratedDeriv_exp_const_mul 2 (-c : ℝ)) u
    simpa [f, iteratedDeriv_succ, iteratedDeriv_one, pow_two, mul_comm] using h
  have hderiv : HasDerivAt
      (fun v : ℝ => (deriv (𝕜 := ℝ) (F := ℝ) f v : ℂ))
      ((deriv (𝕜 := ℝ) (F := ℝ)
        (deriv (𝕜 := ℝ) (F := ℝ) f) u : ℝ) : ℂ) u := by
    have hdiff : DifferentiableAt ℝ (deriv (𝕜 := ℝ) (F := ℝ) f) u := by fun_prop
    exact HasDerivAt.ofReal_comp hdiff.hasDerivAt
  change iteratedDeriv 2 E u = _
  rw [iteratedDeriv_succ, iteratedDeriv_one, hEderiv]
  change deriv (fun v : ℝ => (deriv (𝕜 := ℝ) (F := ℝ) f v : ℂ)) u = _
  rw [hderiv.deriv, hreal2]

private def qsP1LogKernelLine (c : ℝ) (h : ℝ → ℂ) (u : ℝ) : ℂ :=
  ((Real.exp (-c * u) : ℝ) : ℂ) * qsTransform K h (Real.exp (-u))

private theorem qs_p1_logKernelLine_deriv1 [IsTotallyComplex K]
    (c : ℝ) (h : ℝ → ℂ) (hh : IsQSWeight h) (u : ℝ) :
    iteratedDeriv 1 (qsP1LogKernelLine (K := K) c h) u =
      ((-c * Real.exp (-c * u) : ℝ) : ℂ) * qsTransform K h (Real.exp (-u)) +
        ((Real.exp (-c * u) : ℝ) : ℂ) *
          (deriv (qsTransform K h) (Real.exp (-u)) * (-Real.exp (-u))) := by
  obtain ⟨hTdiff, _⟩ := qs_transform_bounds_P0 (K := K) h hh 1 0 1 (by norm_num)
  let E : ℝ → ℂ := fun v => (Real.exp (-c * v) : ℝ)
  let H : ℝ → ℂ := fun v => qsTransform K h (Real.exp (-v))
  have hE : ContDiffAt ℝ 1 E u := by
    change ContDiffAt ℝ 1 (fun v : ℝ => Complex.ofReal (Real.exp (-c * v))) u
    have hlin : ContDiffAt ℝ 1 (fun v : ℝ => -c * v) u := by fun_prop
    exact Complex.ofRealCLM.contDiff.comp_contDiffAt u
      (Real.contDiff_exp.contDiffAt.comp u hlin)
  have hT : ContDiffAt ℝ 1 (qsTransform K h) (Real.exp (-u)) := by
    have hT' : ContDiffOn ℝ 1 (qsTransform K h) (Set.Ioi 0) :=
      hTdiff.of_le (by norm_num)
    exact hT'.contDiffAt (isOpen_Ioi.mem_nhds (Real.exp_pos _))
  have hH : ContDiffAt ℝ 1 H u := by
    dsimp [H]
    exact hT.comp u (by fun_prop)
  have hHderiv : deriv H u =
      deriv (qsTransform K h) (Real.exp (-u)) * (-Real.exp (-u)) := by
    simpa [H, iteratedDeriv_one] using
      (qs_p1_transform_log_comp_deriv1 (K := K) h hh u)
  have hmul := deriv_mul (hE.differentiableAt (by norm_num))
    (hH.differentiableAt (by norm_num))
  change iteratedDeriv 1 (E * H) u = _
  rw [iteratedDeriv_one, hmul, qs_p1_expWeight_deriv1, hHderiv]

private theorem qs_p1_logKernelLine_deriv2 [IsTotallyComplex K]
    (c : ℝ) (h : ℝ → ℂ) (hh : IsQSWeight h) (u : ℝ) :
    iteratedDeriv 2 (qsP1LogKernelLine (K := K) c h) u =
      ((c ^ 2 * Real.exp (-c * u) : ℝ) : ℂ) *
          qsTransform K h (Real.exp (-u)) +
        2 * ((-c * Real.exp (-c * u) : ℝ) : ℂ) *
          (deriv (qsTransform K h) (Real.exp (-u)) * (-Real.exp (-u))) +
        ((Real.exp (-c * u) : ℝ) : ℂ) *
          (iteratedDeriv 2 (qsTransform K h) (Real.exp (-u)) *
              (Real.exp (-u)) ^ 2 +
            deriv (qsTransform K h) (Real.exp (-u)) * Real.exp (-u)) := by
  obtain ⟨hTdiff, _⟩ := qs_transform_bounds_P0 (K := K) h hh 1 0 1 (by norm_num)
  let E : ℝ → ℂ := fun v => (Real.exp (-c * v) : ℝ)
  let H : ℝ → ℂ := fun v => qsTransform K h (Real.exp (-v))
  have hE : ContDiffAt ℝ 2 E u := by
    change ContDiffAt ℝ 2 (fun v : ℝ => Complex.ofReal (Real.exp (-c * v))) u
    have hlin : ContDiffAt ℝ 2 (fun v : ℝ => -c * v) u := by fun_prop
    exact Complex.ofRealCLM.contDiff.comp_contDiffAt u
      (Real.contDiff_exp.contDiffAt.comp u hlin)
  have hT : ContDiffAt ℝ 2 (qsTransform K h) (Real.exp (-u)) := by
    have hT' : ContDiffOn ℝ 2 (qsTransform K h) (Set.Ioi 0) :=
      hTdiff.of_le (by norm_num)
    exact hT'.contDiffAt (isOpen_Ioi.mem_nhds (Real.exp_pos _))
  have hH : ContDiffAt ℝ 2 H u := by
    dsimp [H]
    exact hT.comp u (by fun_prop)
  have hHderiv1 : deriv H u =
      deriv (qsTransform K h) (Real.exp (-u)) * (-Real.exp (-u)) := by
    simpa [H, iteratedDeriv_one] using
      (qs_p1_transform_log_comp_deriv1 (K := K) h hh u)
  have hHderiv2 : iteratedDeriv 2 H u =
      iteratedDeriv 2 (qsTransform K h) (Real.exp (-u)) * (Real.exp (-u)) ^ 2 +
        deriv (qsTransform K h) (Real.exp (-u)) * Real.exp (-u) := by
    simpa [H] using (qs_p1_transform_log_comp_deriv2 (K := K) h hh u)
  have hmul := qs_p1_iteratedDeriv_mul_two hE hH
  change iteratedDeriv 2 (E * H) u = _
  rw [hmul, qs_p1_expWeight_deriv2, qs_p1_expWeight_deriv1, hHderiv1, hHderiv2]

private def qsP1LogTerm (c : ℝ) (j : ℕ) (h : ℝ → ℂ) (u : ℝ) : ℂ :=
  ((Real.exp (-c * u) : ℝ) : ℂ) *
    ((Real.exp (-u) : ℝ) : ℂ) ^ j *
      iteratedDeriv j (qsTransform K h) (Real.exp (-u))

private theorem qs_p1_logTerm_integrable [IsTotallyComplex K]
    (h : ℝ → ℂ) (hh : IsQSWeight h) (c : ℝ) (hc : 0 < c)
    (j : ℕ) (A : ℕ) (hAc : c + (j : ℝ) < (A : ℝ)) :
    Integrable (qsP1LogTerm (K := K) c j h) := by
  let η : ℝ := c / 2
  let a : ℝ := (A : ℝ) - c - j
  obtain ⟨hTdiff, ⟨C, hC, hbound⟩⟩ :=
    qs_transform_bounds_P0 (K := K) h hh A j η (by dsimp [η]; linarith)
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < η := by dsimp [η]; linarith
  have hTjCont : ContinuousOn (iteratedDeriv j (qsTransform K h)) (Set.Ioi 0) := by
    have hwithin := hTdiff.continuousOn_iteratedDerivWithin
      (m := j) (by exact_mod_cast (show j ≤ (⊤ : ℕ∞) by simp)) (uniqueDiffOn_Ioi 0)
    apply hwithin.congr
    intro x hx
    symm
    have hTjAt : ContDiffAt ℝ (j : ℕ∞) (qsTransform K h) x :=
      (hTdiff.contDiffAt (isOpen_Ioi.mem_nhds hx)).of_le (by simp)
    exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioi 0)
      hTjAt hx
  have hargCont : Continuous (fun u : ℝ => Real.exp (-u)) := by fun_prop
  have hcompCont : Continuous
      (fun u : ℝ => iteratedDeriv j (qsTransform K h) (Real.exp (-u))) :=
    hTjCont.comp_continuous hargCont (fun u => Set.mem_Ioi.mpr (Real.exp_pos _))
  have hEcont : Continuous (fun u : ℝ => Real.exp (-c * u)) := by fun_prop
  have htermCont : Continuous (qsP1LogTerm (K := K) c j h) := by
    unfold qsP1LogTerm
    exact ((Complex.continuous_ofReal.comp hEcont).mul
      ((Complex.continuous_ofReal.comp hargCont).pow j)).mul hcompCont
  apply qs_p1_integrable_of_exponential_tails htermCont 0 0 a η C C
    (by norm_num) ha hb hC.le hC.le
  · intro u hu
    let x : ℝ := Real.exp (-u)
    have hx : 0 < x := by dsimp [x]; exact Real.exp_pos _
    have hlog : Real.log x = -u := by dsimp [x]; rw [Real.log_exp]
    have hxge : 1 ≤ x := by
      dsimp [x]
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    have hpow : x ^ j * x ^ (-(A : ℝ)) = Real.exp (((A : ℝ) - j) * u) := by
      calc
        x ^ j * x ^ (-(A : ℝ)) = x ^ ((j : ℝ)) * x ^ (-(A : ℝ)) := by
          rw [← Real.rpow_natCast]
        _ = x ^ ((j : ℝ) + (-(A : ℝ))) := by rw [← Real.rpow_add hx]
        _ = Real.exp (Real.log x * ((j : ℝ) - (A : ℝ))) := by
          rw [Real.rpow_def_of_pos hx]
          congr 1
        _ = Real.exp (((A : ℝ) - j) * u) := by rw [hlog]; congr 1 <;> ring
    have hnorm : ‖qsP1LogTerm (K := K) c j h u‖ =
        Real.exp (-c * u) * x ^ j *
          ‖iteratedDeriv j (qsTransform K h) x‖ := by
      unfold qsP1LogTerm
      rw [Complex.ofReal_exp, Complex.ofReal_exp, norm_mul, norm_mul,
        Complex.norm_exp_ofReal, norm_pow, Complex.norm_exp_ofReal]
    have hT := (hbound x hx).2 hxge
    calc
      ‖qsP1LogTerm (K := K) c j h u‖ =
          Real.exp (-c * u) * x ^ j * ‖iteratedDeriv j (qsTransform K h) x‖ := hnorm
      _ ≤ Real.exp (-c * u) * x ^ j * (C * x ^ (-(A : ℝ))) := by
        gcongr
      _ = C * Real.exp ((A - c - j) * u) := by
        calc
          _ = C * (Real.exp (-c * u) * (x ^ j * x ^ (-(A : ℝ)))) := by ring
          _ = C * (Real.exp (-c * u) * Real.exp (((A : ℝ) - j) * u)) := by rw [hpow]
          _ = C * Real.exp ((A - c - j) * u) := by
            rw [← Real.exp_add]
            congr 1
            congr 1
            ring
      _ ≤ C * Real.exp (a * u) := by
        apply mul_le_mul_of_nonneg_left _ hC.le
        apply Real.exp_le_exp.mpr
        dsimp [a]
        have hu : u ≤ 0 := le_of_lt hu
        nlinarith
  · intro u hu
    let x : ℝ := Real.exp (-u)
    have hx : 0 < x := by dsimp [x]; exact Real.exp_pos _
    have hlog : Real.log x = -u := by dsimp [x]; rw [Real.log_exp]
    have hxle : x ≤ 1 := by
      dsimp [x]
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    have hpow : x ^ j * x ^ (-(j : ℝ) - η) = Real.exp (η * u) := by
      calc
        x ^ j * x ^ (-(j : ℝ) - η) = x ^ ((j : ℝ)) * x ^ (-(j : ℝ) - η) := by
          rw [← Real.rpow_natCast]
        _ = x ^ ((j : ℝ) + (-(j : ℝ) - η)) := by rw [← Real.rpow_add hx]
        _ = x ^ (-η) := by congr 1 <;> ring
        _ = Real.exp (Real.log x * (-η)) := by rw [Real.rpow_def_of_pos hx]
        _ = Real.exp (η * u) := by rw [hlog]; congr 1 <;> ring
    have hnorm : ‖qsP1LogTerm (K := K) c j h u‖ =
        Real.exp (-c * u) * x ^ j *
          ‖iteratedDeriv j (qsTransform K h) x‖ := by
      unfold qsP1LogTerm
      rw [Complex.ofReal_exp, Complex.ofReal_exp, norm_mul, norm_mul,
        Complex.norm_exp_ofReal, norm_pow, Complex.norm_exp_ofReal]
    have hT := (hbound x hx).1 hxle
    calc
      ‖qsP1LogTerm (K := K) c j h u‖ =
          Real.exp (-c * u) * x ^ j * ‖iteratedDeriv j (qsTransform K h) x‖ := hnorm
      _ ≤ Real.exp (-c * u) * x ^ j * (C * x ^ (-(j : ℝ) - η)) := by
        gcongr
      _ = C * Real.exp (-c * u) * Real.exp (η * u) := by
        calc
          _ = C * (Real.exp (-c * u) * (x ^ j * x ^ (-(j : ℝ) - η))) := by ring
          _ = C * (Real.exp (-c * u) * Real.exp (η * u)) := by rw [hpow]
          _ = C * Real.exp (-c * u) * Real.exp (η * u) := by ring
      _ = C * Real.exp (-η * u) := by
        calc
          _ = C * (Real.exp (-c * u) * Real.exp (η * u)) := by ring
          _ = C * Real.exp ((-c + η) * u) := by
            rw [← Real.exp_add]
            congr 1
            congr 1
            ring
          _ = C * Real.exp (-η * u) := by
            congr 2
            dsimp [η]
            ring

private theorem qs_p1_logTerm_uniform_majorant [IsTotallyComplex K]
    (h : ℝ → ℂ) (hh : IsQSWeight h) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (j A : ℕ) (hbAc : b + (j : ℝ) < (A : ℝ)) :
    ∃ G : ℝ → ℝ, Integrable G ∧ ∀ c ∈ Set.Icc a b, ∀ u : ℝ,
      ‖qsP1LogTerm (K := K) c j h u‖ ≤ G u := by
  let η : ℝ := a / 2
  let q : ℝ := (A : ℝ) - b - j
  let r : ℝ := a / 2
  obtain ⟨_, ⟨C, hC, hbound⟩⟩ :=
    qs_transform_bounds_P0 (K := K) h hh A j η (by dsimp [η]; linarith)
  have hq : 0 < q := by dsimp [q]; linarith
  have hr : 0 < r := by dsimp [r]; linarith
  let G : ℝ → ℝ := fun u => C * Real.exp (q * min u 0 - r * max u 0)
  have hGcont : Continuous G := by
    have hmin : Continuous (fun u : ℝ => min u 0) :=
      continuous_id.min continuous_const
    have hmax : Continuous (fun u : ℝ => max u 0) :=
      continuous_id.max continuous_const
    change Continuous (fun u : ℝ => C * Real.exp (q * min u 0 - r * max u 0))
    exact continuous_const.mul (Real.continuous_exp.comp
      ((continuous_const.mul hmin).sub (continuous_const.mul hmax)))
  have hG : Integrable G := by
    have hleftBase : IntegrableOn (fun u : ℝ => C * Real.exp (q * u)) (Set.Iic 0) := by
      have h := (integrableOn_exp_mul_Iic hq 0).const_mul C
      simpa [IntegrableOn, mul_comm] using h
    have hrightBase : IntegrableOn (fun u : ℝ => C * Real.exp (-r * u)) (Set.Ioi 0) := by
      have h := (integrableOn_exp_mul_Ioi (neg_neg_of_pos hr) 0).const_mul C
      simpa [IntegrableOn, mul_comm] using h
    have hleft : IntegrableOn G (Set.Iic 0) := by
      apply hleftBase.congr_fun
      · intro u hu
        change u ≤ 0 at hu
        change C * Real.exp (q * u) =
          C * Real.exp (q * min u 0 - r * max u 0)
        rw [min_eq_left hu, max_eq_right hu]
        ring_nf
      · exact measurableSet_Iic
    have hright : IntegrableOn G (Set.Ioi 0) := by
      apply hrightBase.congr_fun
      · intro u hu
        change 0 < u at hu
        change C * Real.exp (-r * u) =
          C * Real.exp (q * min u 0 - r * max u 0)
        rw [min_eq_right hu.le, max_eq_left hu.le]
        ring_nf
      · exact measurableSet_Ioi
    have huniv : (Set.univ : Set ℝ) = Set.Iic 0 ∪ Set.Ioi 0 := by
      ext u
      simp only [Set.mem_univ, true_iff, Set.mem_union, Set.mem_Iic, Set.mem_Ioi]
      exact le_or_gt u 0
    have hU : IntegrableOn G (Set.Iic 0 ∪ Set.Ioi 0) := by
      rw [integrableOn_union]
      exact ⟨hleft, hright⟩
    have hsub : (Set.univ : Set ℝ) ⊆ Set.Iic 0 ∪ Set.Ioi 0 := by
      intro u hu
      simp only [Set.mem_univ, true_iff, Set.mem_union, Set.mem_Iic, Set.mem_Ioi]
      exact le_or_gt u 0
    exact integrableOn_univ.mp (hU.mono_set hsub)
  refine ⟨G, hG, ?_⟩
  intro c hc u
  have hca : a ≤ c := hc.1
  have hcb : c ≤ b := hc.2
  let x : ℝ := Real.exp (-u)
  have hx : 0 < x := by dsimp [x]; exact Real.exp_pos _
  have hlog : Real.log x = -u := by dsimp [x]; rw [Real.log_exp]
  have hnorm : ‖qsP1LogTerm (K := K) c j h u‖ =
      Real.exp (-c * u) * x ^ j *
        ‖iteratedDeriv j (qsTransform K h) x‖ := by
    unfold qsP1LogTerm
    rw [Complex.ofReal_exp, Complex.ofReal_exp, norm_mul, norm_mul,
      Complex.norm_exp_ofReal, norm_pow, Complex.norm_exp_ofReal]
  by_cases hu : u ≤ 0
  · have hxge : 1 ≤ x := by
      dsimp [x]
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    have hpow : x ^ j * x ^ (-(A : ℝ)) = Real.exp (((A : ℝ) - j) * u) := by
      calc
        x ^ j * x ^ (-(A : ℝ)) = x ^ ((j : ℝ)) * x ^ (-(A : ℝ)) := by
          rw [← Real.rpow_natCast]
        _ = x ^ ((j : ℝ) + (-(A : ℝ))) := by rw [← Real.rpow_add hx]
        _ = Real.exp (Real.log x * ((j : ℝ) - (A : ℝ))) := by
          rw [Real.rpow_def_of_pos hx]
          congr 1
        _ = Real.exp (((A : ℝ) - j) * u) := by rw [hlog]; congr 1 <;> ring
    have hT := (hbound x hx).2 hxge
    have hbase : ‖qsP1LogTerm (K := K) c j h u‖ ≤
        C * Real.exp (((A : ℝ) - c - j) * u) := by
      rw [hnorm]
      calc
        Real.exp (-c * u) * x ^ j *
            ‖iteratedDeriv j (qsTransform K h) x‖ ≤
            Real.exp (-c * u) * x ^ j * (C * x ^ (-(A : ℝ))) := by
          gcongr
        _ = C * Real.exp (((A : ℝ) - c - j) * u) := by
          calc
            _ = C * (Real.exp (-c * u) * (x ^ j * x ^ (-(A : ℝ)))) := by ring
            _ = C * (Real.exp (-c * u) * Real.exp (((A : ℝ) - j) * u)) := by rw [hpow]
            _ = C * Real.exp (((A : ℝ) - c - j) * u) := by
              rw [← Real.exp_add]
              congr 1
              congr 1
              ring
    have hcoef : q ≤ (A : ℝ) - c - j := by dsimp [q]; linarith
    have hexp : Real.exp (((A : ℝ) - c - j) * u) ≤ Real.exp (q * u) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hcoef hu)
    have hGform : G u = C * Real.exp (q * u) := by
      simp [G, min_eq_left hu, max_eq_right hu]
    calc
      _ ≤ C * Real.exp (((A : ℝ) - c - j) * u) := hbase
      _ ≤ C * Real.exp (q * u) := mul_le_mul_of_nonneg_left hexp hC.le
      _ = G u := hGform.symm
  · have hu' : 0 < u := lt_of_not_ge hu
    have hxle : x ≤ 1 := by
      dsimp [x]
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    have hpow : x ^ j * x ^ (-(j : ℝ) - η) = Real.exp (η * u) := by
      calc
        x ^ j * x ^ (-(j : ℝ) - η) = x ^ ((j : ℝ)) * x ^ (-(j : ℝ) - η) := by
          rw [← Real.rpow_natCast]
        _ = x ^ ((j : ℝ) + (-(j : ℝ) - η)) := by rw [← Real.rpow_add hx]
        _ = x ^ (-η) := by congr 1 <;> ring
        _ = Real.exp (Real.log x * (-η)) := by rw [Real.rpow_def_of_pos hx]
        _ = Real.exp (η * u) := by rw [hlog]; congr 1 <;> ring
    have hT := (hbound x hx).1 hxle
    have hbase : ‖qsP1LogTerm (K := K) c j h u‖ ≤
        C * Real.exp ((-c + η) * u) := by
      rw [hnorm]
      calc
        Real.exp (-c * u) * x ^ j *
            ‖iteratedDeriv j (qsTransform K h) x‖ ≤
            Real.exp (-c * u) * x ^ j * (C * x ^ (-(j : ℝ) - η)) := by
          gcongr
        _ = C * Real.exp ((-c + η) * u) := by
          calc
            _ = C * (Real.exp (-c * u) * (x ^ j * x ^ (-(j : ℝ) - η))) := by ring
            _ = C * (Real.exp (-c * u) * Real.exp (η * u)) := by rw [hpow]
            _ = C * Real.exp ((-c + η) * u) := by
              rw [← Real.exp_add]
              congr 1
              congr 1
              ring
    have hcoef : -c + η ≤ -r := by dsimp [η, r]; linarith
    have hexp : Real.exp ((-c + η) * u) ≤ Real.exp (-r * u) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hcoef hu'.le)
    have hGform : G u = C * Real.exp (-r * u) := by
      simp [G, min_eq_right hu'.le, max_eq_left hu'.le]
    calc
      _ ≤ C * Real.exp ((-c + η) * u) := hbase
      _ ≤ C * Real.exp (-r * u) := mul_le_mul_of_nonneg_left hexp hC.le
      _ = G u := hGform.symm

private theorem qs_p1_logKernelLine_iteratedDeriv_integrable [IsTotallyComplex K]
    (h : ℝ → ℂ) (hh : IsQSWeight h) (c : ℝ) (hc : 0 < c)
    (A : ℕ) (hAc : c + 2 < (A : ℝ)) (j : ℕ) (hj : j ≤ 2) :
    Integrable (fun u : ℝ => iteratedDeriv j (qsP1LogKernelLine (K := K) c h) u) := by
  have hAc0 : c + (0 : ℝ) < (A : ℝ) := by
    calc
      c + 0 < c + 2 := by norm_num
      _ < (A : ℝ) := hAc
  have hAc1 : c + (1 : ℝ) < (A : ℝ) := by
    calc
      c + 1 < c + 2 := by norm_num
      _ < (A : ℝ) := hAc
  have hterm0 := qs_p1_logTerm_integrable (K := K) h hh c hc 0 A (by simpa using hAc0)
  have hterm1 := qs_p1_logTerm_integrable (K := K) h hh c hc 1 A (by simpa using hAc1)
  have hterm2 := qs_p1_logTerm_integrable (K := K) h hh c hc 2 A hAc
  interval_cases j
  · have hEq : (fun u : ℝ => iteratedDeriv 0 (qsP1LogKernelLine (K := K) c h) u) =
        qsP1LogTerm (K := K) c 0 h := by
      funext u
      simp [qsP1LogKernelLine, qsP1LogTerm, iteratedDeriv_zero]
    rw [hEq]
    exact hterm0
  · have hEq : (fun u : ℝ => iteratedDeriv 1 (qsP1LogKernelLine (K := K) c h) u) =
        fun u => (-c : ℂ) * qsP1LogTerm (K := K) c 0 h u -
          qsP1LogTerm (K := K) c 1 h u := by
      funext u
      rw [qs_p1_logKernelLine_deriv1 (K := K) c h hh u]
      simp [qsP1LogTerm, iteratedDeriv_zero, Complex.ofReal_mul, Complex.ofReal_neg]
      ring
    rw [hEq]
    exact (hterm0.const_mul (-c : ℂ)).sub hterm1
  · have hEq : (fun u : ℝ => iteratedDeriv 2 (qsP1LogKernelLine (K := K) c h) u) =
        fun u => (c ^ 2 : ℂ) * qsP1LogTerm (K := K) c 0 h u +
          ((2 * c + 1 : ℝ) : ℂ) * qsP1LogTerm (K := K) c 1 h u +
            qsP1LogTerm (K := K) c 2 h u := by
      funext u
      rw [qs_p1_logKernelLine_deriv2 (K := K) c h hh u]
      simp [qsP1LogTerm, iteratedDeriv_zero, Complex.ofReal_mul, Complex.ofReal_neg]
      ring
    rw [hEq]
    exact ((hterm0.const_mul (c ^ 2 : ℂ)).add
      (hterm1.const_mul ((2 * c + 1 : ℝ) : ℂ))).add hterm2

private theorem qs_p1_iteratedDeriv_ofReal_comp (f : ℝ → ℝ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (n : ℕ) :
    iteratedDeriv n (fun x : ℝ => (f x : ℂ)) =
      fun x => ((iteratedDeriv n f x : ℝ) : ℂ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iteratedDeriv_succ, iteratedDeriv_succ, ih]
      funext x
      have hdiff : DifferentiableAt ℝ (iteratedDeriv n f) x :=
        (hf.differentiable_iteratedDeriv n
          (WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top n))).differentiableAt
      have hcast := HasDerivAt.ofReal_comp hdiff.hasDerivAt
      change deriv (fun y : ℝ => ((iteratedDeriv n f y : ℝ) : ℂ)) x =
        ((deriv (iteratedDeriv n f) x : ℝ) : ℂ)
      exact hcast.deriv

private theorem qs_p1_mellinLogKernel_iteratedDeriv_uniform_majorant
    (h : ℝ → ℂ) (hh : IsQSWeight h) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (j : ℕ) :
    ∃ G : ℝ → ℝ, Integrable G ∧ ∀ c ∈ Set.Icc a b, ∀ u : ℝ,
      ‖iteratedDeriv j (qsP1MellinLogKernel c h) u‖ ≤ G u := by
  classical
  obtain ⟨B, hB⟩ := hh.2.1
  obtain ⟨δ, hδ, hconst⟩ := hh.2.2
  let B₀ : ℝ := max B 1
  let δ₀ : ℝ := min δ (1 / 2)
  have hB₀ : 0 < B₀ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hδ₀ : 0 < δ₀ := lt_min hδ (by norm_num)
  have hδ₀δ : δ₀ ≤ δ := min_le_left _ _
  have hδ₀_le : δ₀ ≤ 1 / 2 := min_le_right _ _
  let A : ℝ := -Real.log B₀
  let C : ℝ := -Real.log δ₀
  have hAC : A ≤ C := by
    have hA : A ≤ 0 := by
      dsimp [A]
      exact neg_nonpos.mpr (Real.log_nonneg (by dsimp [B₀]; exact le_max_right _ _))
    have hC : 0 ≤ C := by
      dsimp [C]
      have hδ₀_le_one : δ₀ ≤ 1 := hδ₀_le.trans (by norm_num)
      exact neg_nonneg.mpr (Real.log_nonpos hδ₀.le hδ₀_le_one)
    linarith
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    have hδ₀_le_one : δ₀ ≤ 1 := hδ₀_le.trans (by norm_num)
    exact neg_nonneg.mpr (Real.log_nonpos hδ₀.le hδ₀_le_one)
  let H : ℝ → ℂ := fun u => h (Real.exp (-u))
  let E : ℝ → ℝ → ℂ := fun c u => ((Real.exp (-c * u) : ℝ) : ℂ)
  have hHtop : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H := by
    have hExp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun u : ℝ => Real.exp (-u)) := by fun_prop
    simpa [H, Function.comp_def] using hh.1.comp hExp
  have hEtop (c : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (E c) := by
    apply contDiff_iff_contDiffAt.2
    intro u
    dsimp [E]
    have hlin : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun v : ℝ => -c * v) u := by fun_prop
    exact Complex.ofRealCLM.contDiff.comp_contDiffAt u
      (Real.contDiff_exp.contDiffAt.comp u hlin)
  have hEderiv (c : ℝ) (i : ℕ) (u : ℝ) :
      iteratedDeriv i (E c) u =
        ((((-c : ℝ) ^ i * Real.exp (-c * u) : ℝ) : ℂ)) := by
    have hcast := congrFun
      (qs_p1_iteratedDeriv_ofReal_comp (fun v : ℝ => Real.exp (-c * v))
        (by fun_prop) i) u
    have hreal := congrFun (iteratedDeriv_exp_const_mul i (-c : ℝ)) u
    simpa [E, neg_mul] using hcast.trans (congrArg (fun x : ℝ => (x : ℂ)) hreal)
  have hformula (c u : ℝ) :
      iteratedDeriv j (E c * H) u =
        ∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℂ) * iteratedDeriv i (E c) u *
            iteratedDeriv (j - i) H u := by
    have hE : ContDiffAt ℝ (j : ℕ∞) (E c) u :=
      ((contDiff_iff_contDiffAt.1 (hEtop c)) u).of_le (by simp)
    have hH : ContDiffAt ℝ (j : ℕ∞) H u :=
      ((contDiff_iff_contDiffAt.1 hHtop u).of_le (by simp))
    exact iteratedDeriv_mul hE hH
  let F : ℝ × ℝ → ℂ := fun z =>
    ∑ i ∈ Finset.range (j + 1),
      (j.choose i : ℂ) *
        ((((-z.1 : ℝ) ^ i * Real.exp (-z.1 * z.2) : ℝ) : ℂ)) *
          iteratedDeriv (j - i) H z.2
  have hHderivCont (k : ℕ) : Continuous (iteratedDeriv k H) :=
    hHtop.continuous_iteratedDeriv k (by simp)
  have hFcont : Continuous F := by
    dsimp [F]
    fun_prop
  have hformulaF (c u : ℝ) : iteratedDeriv j (E c * H) u = F (c, u) := by
    rw [hformula c u]
    simp [F, hEderiv]
  have hline (c : ℝ) : qsP1MellinLogKernel c h = E c * H := by
    funext u
    simp [qsP1MellinLogKernel, E, H, smul_eq_mul]
  let S : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Set.Icc A C
  have hScompact : IsCompact S := isCompact_Icc.prod isCompact_Icc
  have hSnonempty : S.Nonempty := by
    refine ⟨(a, A), ?_⟩
    exact ⟨⟨le_rfl, hab⟩, ⟨le_rfl, hAC⟩⟩
  let Fnorm : ℝ × ℝ → ℝ := fun z => ‖F z‖
  have hFnormCont : Continuous Fnorm := by
    dsimp [Fnorm]
    exact hFcont.norm
  obtain ⟨zmax, hzmax, hmax⟩ := hScompact.exists_isMaxOn hSnonempty hFnormCont.continuousOn
  let M : ℝ := Fnorm zmax
  have hM : 0 ≤ M := by dsimp [M, Fnorm]; exact norm_nonneg _
  have hcompactBound (c : ℝ) (hc : c ∈ Set.Icc a b) (u : ℝ)
      (huA : A ≤ u) (huC : u ≤ C) :
      ‖iteratedDeriv j (qsP1MellinLogKernel c h) u‖ ≤ M := by
    rw [hline c, hformulaF c u]
    apply hmax
    exact ⟨hc, ⟨huA, huC⟩⟩
  have hleft (c : ℝ) (u : ℝ) (hu : u < A) :
      iteratedDeriv j (qsP1MellinLogKernel c h) u = 0 := by
    have hloc : qsP1MellinLogKernel c h =ᶠ[𝓝 u] (fun _ : ℝ => (0 : ℂ)) := by
      filter_upwards [IsOpen.mem_nhds isOpen_Iio hu] with v hv
      change v < A at hv
      have hlog : Real.log B₀ < -v := by
        have := neg_lt_neg hv
        simpa [A] using this
      have hnorm : B₀ < Real.exp (-v) := by
        have he := Real.exp_lt_exp.mpr hlog
        simpa [Real.exp_log hB₀] using he
      have hzero := hB (Real.exp (-v)) (le_trans (le_max_left _ _) hnorm.le)
      simp [qsP1MellinLogKernel, hzero]
    rw [hloc.iteratedDeriv_eq j]
    simp [iteratedDeriv_const]
  let coef : ℝ → ℂ := fun c => ((((-c : ℝ) ^ j : ℝ) : ℂ) * h 0)
  have hright (c : ℝ) (u : ℝ) (hu : C < u) :
      iteratedDeriv j (qsP1MellinLogKernel c h) u =
        coef c * ((Real.exp (-c * u) : ℝ) : ℂ) := by
    have hloc : qsP1MellinLogKernel c h =ᶠ[𝓝 u]
        (fun v : ℝ => (Real.exp (-c * v) : ℝ) • h 0) := by
      filter_upwards [IsOpen.mem_nhds isOpen_Ioi hu] with v hv
      change C < v at hv
      have hlog : -v < Real.log δ₀ := by
        have := neg_lt_neg hv
        simpa [C] using this
      have hnorm : Real.exp (-v) < δ₀ := by
        have he := Real.exp_lt_exp.mpr hlog
        simpa [Real.exp_log hδ₀] using he
      have hval := hconst (Real.exp (-v))
        ⟨(Real.exp_pos _).le, hnorm.le.trans hδ₀δ⟩
      simpa [qsP1MellinLogKernel, hval]
    rw [hloc.iteratedDeriv_eq j]
    have hExpCont : ContDiffAt ℝ (j : ℕ∞)
        (fun v : ℝ => Real.exp (-c * v)) u := by fun_prop
    have hexp : iteratedDeriv j (fun v : ℝ => Real.exp (-c * v)) u =
        (-c : ℝ) ^ j * Real.exp (-c * u) := by
      simpa using congrFun (iteratedDeriv_exp_const_mul j (-c : ℝ)) u
    rw [iteratedDeriv_smul_const hExpCont (h 0), hexp]
    dsimp [coef]
    simp only [smul_eq_mul, Complex.ofReal_mul]
    ring
  have hbc : max 1 b ≥ 0 := le_trans (by norm_num) (le_max_left 1 b)
  let Bc : ℝ := max 1 b
  let D : ℝ := Bc ^ j * ‖h 0‖
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hrightBound (c : ℝ) (hc : c ∈ Set.Icc a b) (u : ℝ)
      (hu : C < u) :
      ‖iteratedDeriv j (qsP1MellinLogKernel c h) u‖ ≤ D * Real.exp (-a * u) := by
    have hcpos : 0 < c := lt_of_lt_of_le ha hc.1
    have hcBc : c ≤ Bc := le_trans hc.2 (le_max_right _ _)
    have hu0 : 0 ≤ u := le_trans hC_nonneg hu.le
    have hpow : c ^ j ≤ Bc ^ j := pow_le_pow_left₀ (le_of_lt hcpos) hcBc j
    have hexp : Real.exp (-c * u) ≤ Real.exp (-a * u) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hc.1 hu0]
    calc
      ‖iteratedDeriv j (qsP1MellinLogKernel c h) u‖ =
          c ^ j * Real.exp (-c * u) * ‖h 0‖ := by
        rw [hright c u hu, norm_mul]
        have hcoefNorm : ‖coef c‖ = c ^ j * ‖h 0‖ := by
          dsimp [coef]
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_pow, abs_neg, abs_of_pos hcpos]
        rw [hcoefNorm, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _)]
        ring
      _ ≤ Bc ^ j * Real.exp (-c * u) * ‖h 0‖ := by gcongr
      _ ≤ Bc ^ j * Real.exp (-a * u) * ‖h 0‖ := by
        gcongr
      _ = D * Real.exp (-a * u) := by dsimp [D]; ring
  let K₀ : ℝ := max (M * Real.exp (-A))
    (max (M * Real.exp (a * C)) D)
  have hK₀ : 0 ≤ K₀ := by dsimp [K₀]; positivity
  have hKleft : M * Real.exp (-A) ≤ K₀ := le_max_left _ _
  have hKright : M * Real.exp (a * C) ≤ K₀ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hKD : D ≤ K₀ := le_trans (le_max_right _ _) (le_max_right _ _)
  let G : ℝ → ℝ := fun u => K₀ * Real.exp (min u 0 - a * max u 0)
  have hGcont : Continuous G := by
    have hmin : Continuous (fun u : ℝ => min u 0) := continuous_id.min continuous_const
    have hmax : Continuous (fun u : ℝ => max u 0) := continuous_id.max continuous_const
    change Continuous (fun u : ℝ => K₀ * Real.exp (min u 0 - a * max u 0))
    exact continuous_const.mul (Real.continuous_exp.comp
      (hmin.sub (continuous_const.mul hmax)))
  have hG : Integrable G := by
    have hleftBase : IntegrableOn (fun u : ℝ => K₀ * Real.exp u) (Set.Iic 0) := by
      have h := (integrableOn_exp_mul_Iic (by norm_num : 0 < (1 : ℝ)) 0).const_mul K₀
      simpa [IntegrableOn, mul_comm] using h
    have hrightBase : IntegrableOn (fun u : ℝ => K₀ * Real.exp (-a * u)) (Set.Ioi 0) := by
      have h := (integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) 0).const_mul K₀
      simpa [IntegrableOn, mul_comm] using h
    have hleft : IntegrableOn G (Set.Iic 0) := by
      apply hleftBase.congr_fun
      · intro u hu
        change u ≤ 0 at hu
        change K₀ * Real.exp u = K₀ * Real.exp (min u 0 - a * max u 0)
        rw [min_eq_left hu, max_eq_right hu]
        ring_nf
      · exact measurableSet_Iic
    have hright : IntegrableOn G (Set.Ioi 0) := by
      apply hrightBase.congr_fun
      · intro u hu
        change 0 < u at hu
        change K₀ * Real.exp (-a * u) = K₀ * Real.exp (min u 0 - a * max u 0)
        rw [min_eq_right hu.le, max_eq_left hu.le]
        ring_nf
      · exact measurableSet_Ioi
    have hU : IntegrableOn G (Set.Iic 0 ∪ Set.Ioi 0) := by
      rw [integrableOn_union]
      exact ⟨hleft, hright⟩
    have hsub : (Set.univ : Set ℝ) ⊆ Set.Iic 0 ∪ Set.Ioi 0 := by
      intro u _
      simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ioi]
      exact le_or_gt u 0
    exact integrableOn_univ.mp (hU.mono_set hsub)
  refine ⟨G, hG, ?_⟩
  intro c hc u
  have hGnonneg : 0 ≤ G u := by
    dsimp [G]
    exact mul_nonneg hK₀ (Real.exp_pos _).le
  by_cases huA : u < A
  · rw [hleft c u huA]
    simpa using hGnonneg
  · have huA' : A ≤ u := le_of_not_gt huA
    by_cases huC : C < u
    · have hGform : G u = K₀ * Real.exp (-a * u) := by
        simp [G, min_eq_right (le_trans hC_nonneg huC.le),
          max_eq_left (le_trans hC_nonneg huC.le)]
      calc
        ‖iteratedDeriv j (qsP1MellinLogKernel c h) u‖ ≤ D * Real.exp (-a * u) :=
          hrightBound c hc u huC
        _ ≤ K₀ * Real.exp (-a * u) :=
          mul_le_mul_of_nonneg_right hKD (Real.exp_pos _).le
        _ = G u := hGform.symm
    · have huC' : u ≤ C := le_of_not_gt huC
      have hcomp := hcompactBound c hc u huA' huC'
      by_cases hu0 : u ≤ 0
      · have hGform : G u = K₀ * Real.exp u := by
          simp [G, min_eq_left hu0, max_eq_right hu0]
        have hExp : 1 ≤ Real.exp (u - A) :=
          Real.one_le_exp_iff.mpr (sub_nonneg.mpr (by linarith))
        calc
          _ ≤ M := hcomp
          _ ≤ M * Real.exp (u - A) := by
            calc
              M = M * 1 := by ring
              _ ≤ M * Real.exp (u - A) := mul_le_mul_of_nonneg_left hExp hM
          _ = M * Real.exp (-A) * Real.exp u := by
            have hExpEq : Real.exp (u - A) = Real.exp (-A) * Real.exp u := by
              rw [show u - A = (-A) + u by ring, Real.exp_add]
            rw [hExpEq]
            ring
          _ ≤ K₀ * Real.exp u := mul_le_mul_of_nonneg_right hKleft (Real.exp_pos _).le
          _ = G u := hGform.symm
      · have hu0' : 0 ≤ u := (lt_of_not_ge hu0).le
        have hExp : 1 ≤ Real.exp (a * (C - u)) :=
          Real.one_le_exp_iff.mpr (mul_nonneg ha.le (sub_nonneg.mpr huC'))
        have hGform : G u = K₀ * Real.exp (-a * u) := by
          simp [G, min_eq_right hu0', max_eq_left hu0']
        calc
          _ ≤ M := hcomp
          _ ≤ M * Real.exp (a * (C - u)) := by
            calc
              M = M * 1 := by ring
              _ ≤ M * Real.exp (a * (C - u)) := mul_le_mul_of_nonneg_left hExp hM
          _ = M * Real.exp (a * C) * Real.exp (-a * u) := by
            have hExpEq : Real.exp (a * (C - u)) =
                Real.exp (a * C) * Real.exp (-a * u) := by
              rw [show a * (C - u) = a * C + (-a * u) by ring, Real.exp_add]
            rw [hExpEq]
            ring
          _ ≤ K₀ * Real.exp (-a * u) := mul_le_mul_of_nonneg_right hKright (Real.exp_pos _).le
          _ = G u := hGform.symm

private def qsP1LogCompTerm (c : ℝ) (h : ℝ → ℂ) {j : ℕ}
    (p : OrderedFinpartition j) (u : ℝ) : ℂ :=
  ((Real.exp (-c * u) : ℝ) : ℂ) *
    ((∏ i : Fin p.length,
      iteratedDeriv (p.partSize i) (fun v : ℝ => Real.exp (-v)) u) •
      iteratedDeriv p.length (qsTransform K h) (Real.exp (-u)))

private theorem qs_p1_weighted_logComp_integrable [IsTotallyComplex K]
    (h : ℝ → ℂ) (hh : IsQSWeight h) (c : ℝ) (hc : 0 < c)
    (j A : ℕ) (hAc : c + (j : ℝ) < (A : ℝ)) :
    Integrable (fun u : ℝ => ((Real.exp (-c * u) : ℝ) : ℂ) *
      iteratedDeriv j (fun v : ℝ => qsTransform K h (Real.exp (-v))) u) := by
  classical
  let T : ℝ → ℂ := qsTransform K h
  let φ : ℝ → ℝ := fun v => Real.exp (-v)
  let H : ℝ → ℂ := fun v => T (φ v)
  let E : ℝ → ℂ := fun v => ((Real.exp (-c * v) : ℝ) : ℂ)
  have hTtop : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) T (Set.Ioi 0) := by
    obtain ⟨hT, _⟩ := qs_transform_bounds_P0 (K := K) h hh 1 0 1 (by norm_num)
    simpa [T] using hT
  have hparts (p : OrderedFinpartition j) :
      ∑ i : Fin p.length, p.partSize i = j := by
    have hcard := Fintype.card_congr p.equivSigma
    calc
      ∑ i : Fin p.length, p.partSize i =
          Fintype.card (Σ i : Fin p.length, Fin (p.partSize i)) := by simp
      _ = Fintype.card (Fin j) := hcard
      _ = j := by simp
  have hformula (u : ℝ) :
      iteratedDeriv j H u =
        ∑ p : OrderedFinpartition j,
          (∏ i : Fin p.length, iteratedDeriv (p.partSize i) φ u) •
            iteratedDeriv p.length T (φ u) := by
    have hT : ContDiffAt ℝ (j : ℕ∞) T (φ u) := by
      have h := hTtop.contDiffAt (isOpen_Ioi.mem_nhds (Real.exp_pos (-u)))
      exact h.of_le (by simp)
    have hφ : ContDiffAt ℝ (j : ℕ∞) φ u := by
      change ContDiffAt ℝ (j : ℕ∞) (fun v : ℝ => Real.exp (-v)) u
      fun_prop
    simpa [H, T, φ, Function.comp_def] using
      (iteratedDeriv_scomp_eq_sum_orderedFinpartition hT hφ (by simp))
  have hprod (p : OrderedFinpartition j) (u : ℝ) :
      (∏ i : Fin p.length,
        iteratedDeriv (p.partSize i) (fun v : ℝ => Real.exp (-v)) u) =
        (-1 : ℝ) ^ j * (Real.exp (-u)) ^ p.length := by
    calc
      _ = ∏ i : Fin p.length,
          ((-1 : ℝ) ^ p.partSize i * Real.exp (-u)) := by
        apply Finset.prod_congr rfl
        intro i hi
        have h := congrFun (iteratedDeriv_exp_const_mul (p.partSize i) (-1 : ℝ)) u
        simpa [neg_one_mul] using h
      _ = (∏ i : Fin p.length, (-1 : ℝ) ^ p.partSize i) *
          (∏ _i : Fin p.length, Real.exp (-u)) := by
        rw [← Finset.prod_mul_distrib]
      _ = (-1 : ℝ) ^ j * (Real.exp (-u)) ^ p.length := by
        rw [Finset.prod_pow_eq_pow_sum, hparts p]
        simp
  have hpartInt (p : OrderedFinpartition j) :
      Integrable (qsP1LogCompTerm (K := K) c h p) := by
    have hlen : (p.length : ℝ) ≤ (j : ℝ) := by exact_mod_cast p.length_le
    have hAc' : c + (p.length : ℝ) < (A : ℝ) := by linarith
    have hbase := qs_p1_logTerm_integrable (K := K) h hh c hc p.length A hAc'
    have heq : qsP1LogCompTerm (K := K) c h p =
        fun u => ((-1 : ℂ) ^ j) * qsP1LogTerm (K := K) c p.length h u := by
      funext u
      simp only [qsP1LogCompTerm]
      rw [hprod]
      simp [qsP1LogTerm, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_pow]
      ring
    rw [heq]
    exact hbase.const_mul ((-1 : ℂ) ^ j)
  have hsum : Integrable (fun u : ℝ =>
      ∑ p : OrderedFinpartition j, qsP1LogCompTerm (K := K) c h p u) := by
    have hall : ∀ s : Finset (OrderedFinpartition j),
        Integrable (fun u : ℝ => ∑ p ∈ s, qsP1LogCompTerm (K := K) c h p u) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert p s hp ih =>
          have hsumEq :
              (fun u : ℝ => ∑ q ∈ insert p s, qsP1LogCompTerm (K := K) c h q u) =
                qsP1LogCompTerm (K := K) c h p +
                  (fun u : ℝ => ∑ q ∈ s, qsP1LogCompTerm (K := K) c h q u) := by
            funext u
            simp [Finset.sum_insert, hp]
          rw [hsumEq]
          exact (hpartInt p).add ih
    simpa using hall Finset.univ
  have heq : (fun u : ℝ => E u * iteratedDeriv j H u) =
      fun u => ∑ p : OrderedFinpartition j, qsP1LogCompTerm (K := K) c h p u := by
    funext u
    rw [hformula u]
    simp [E, qsP1LogCompTerm, T, H, φ, Finset.mul_sum, smul_eq_mul]
  rw [show (fun u : ℝ => ((Real.exp (-c * u) : ℝ) : ℂ) *
      iteratedDeriv j (fun v : ℝ => qsTransform K h (Real.exp (-v))) u) =
      fun u => E u * iteratedDeriv j H u by rfl]
  rw [heq]
  exact hsum

private theorem qs_p1_weighted_logComp_uniform_majorant [IsTotallyComplex K]
    (h : ℝ → ℂ) (hh : IsQSWeight h) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (j A : ℕ) (hAc : b + (j : ℝ) < (A : ℝ)) :
    ∃ G : ℝ → ℝ, Integrable G ∧ ∀ c ∈ Set.Icc a b, ∀ u : ℝ,
      ‖((Real.exp (-c * u) : ℝ) : ℂ) *
        iteratedDeriv j (fun v : ℝ => qsTransform K h (Real.exp (-v))) u‖ ≤ G u := by
  classical
  let T : ℝ → ℂ := qsTransform K h
  let φ : ℝ → ℝ := fun v => Real.exp (-v)
  let H : ℝ → ℂ := fun v => T (φ v)
  have hTtop : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) T (Set.Ioi 0) := by
    obtain ⟨hT, _⟩ := qs_transform_bounds_P0 (K := K) h hh 1 0 1 (by norm_num)
    simpa [T] using hT
  have hparts (p : OrderedFinpartition j) :
      ∑ i : Fin p.length, p.partSize i = j := by
    have hcard := Fintype.card_congr p.equivSigma
    calc
      ∑ i : Fin p.length, p.partSize i =
          Fintype.card (Σ i : Fin p.length, Fin (p.partSize i)) := by simp
      _ = Fintype.card (Fin j) := hcard
      _ = j := by simp
  have hformula (u : ℝ) :
      iteratedDeriv j H u =
        ∑ p : OrderedFinpartition j,
          (∏ i : Fin p.length, iteratedDeriv (p.partSize i) φ u) •
            iteratedDeriv p.length T (φ u) := by
    have hT : ContDiffAt ℝ (j : ℕ∞) T (φ u) := by
      have h := hTtop.contDiffAt (isOpen_Ioi.mem_nhds (Real.exp_pos (-u)))
      exact h.of_le (by simp)
    have hφ : ContDiffAt ℝ (j : ℕ∞) φ u := by
      change ContDiffAt ℝ (j : ℕ∞) (fun v : ℝ => Real.exp (-v)) u
      fun_prop
    simpa [H, T, φ, Function.comp_def] using
      (iteratedDeriv_scomp_eq_sum_orderedFinpartition hT hφ (by simp))
  have hprod (p : OrderedFinpartition j) (u : ℝ) :
      (∏ i : Fin p.length,
        iteratedDeriv (p.partSize i) (fun v : ℝ => Real.exp (-v)) u) =
        (-1 : ℝ) ^ j * (Real.exp (-u)) ^ p.length := by
    calc
      _ = ∏ i : Fin p.length,
          ((-1 : ℝ) ^ p.partSize i * Real.exp (-u)) := by
        apply Finset.prod_congr rfl
        intro i hi
        have h := congrFun (iteratedDeriv_exp_const_mul (p.partSize i) (-1 : ℝ)) u
        simpa [neg_one_mul] using h
      _ = (∏ i : Fin p.length, (-1 : ℝ) ^ p.partSize i) *
          (∏ _i : Fin p.length, Real.exp (-u)) := by
        rw [← Finset.prod_mul_distrib]
      _ = (-1 : ℝ) ^ j * (Real.exp (-u)) ^ p.length := by
        rw [Finset.prod_pow_eq_pow_sum, hparts p]
        simp
  have hEx (p : OrderedFinpartition j) :
      ∃ G : ℝ → ℝ, Integrable G ∧ ∀ c ∈ Set.Icc a b, ∀ u : ℝ,
        ‖qsP1LogTerm (K := K) c p.length h u‖ ≤ G u := by
    have hlen : (p.length : ℝ) ≤ (j : ℝ) := by exact_mod_cast p.length_le
    apply qs_p1_logTerm_uniform_majorant (K := K) h hh a b ha hab p.length A
    linarith
  let Gp : OrderedFinpartition j → (ℝ → ℝ) := fun p => Classical.choose (hEx p)
  have hGp : ∀ p : OrderedFinpartition j, Integrable (Gp p) := by
    intro p
    exact (Classical.choose_spec (hEx p)).1
  have hGp_bound (p : OrderedFinpartition j) (c : ℝ) (hc : c ∈ Set.Icc a b)
      (u : ℝ) : ‖qsP1LogTerm (K := K) c p.length h u‖ ≤ Gp p u :=
    (Classical.choose_spec (hEx p)).2 c hc u
  let G : ℝ → ℝ := fun u => ∑ p : OrderedFinpartition j, Gp p u
  have hG : Integrable G := by
    have hall : ∀ s : Finset (OrderedFinpartition j),
        Integrable (fun u : ℝ => ∑ p ∈ s, Gp p u) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert p s hp ih =>
          have hsumEq :
              (fun u : ℝ => ∑ q ∈ insert p s, Gp q u) =
                Gp p + (fun u : ℝ => ∑ q ∈ s, Gp q u) := by
            funext u
            simp [Finset.sum_insert, hp]
          rw [hsumEq]
          exact (hGp p).add ih
    simpa [G] using hall Finset.univ
  have hcompEq (p : OrderedFinpartition j) (c u : ℝ) :
      qsP1LogCompTerm (K := K) c h p u =
        ((-1 : ℂ) ^ j) * qsP1LogTerm (K := K) c p.length h u := by
    simp only [qsP1LogCompTerm]
    rw [hprod]
    simp [qsP1LogTerm, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_pow]
    ring
  have hsumEq (c u : ℝ) :
      ((Real.exp (-c * u) : ℝ) : ℂ) * iteratedDeriv j H u =
        ∑ p : OrderedFinpartition j, qsP1LogCompTerm (K := K) c h p u := by
    rw [hformula u]
    simp [qsP1LogCompTerm, T, H, φ, Finset.mul_sum, smul_eq_mul]
  refine ⟨G, hG, ?_⟩
  intro c hc u
  have hsumBound :
      ‖∑ p : OrderedFinpartition j, qsP1LogCompTerm (K := K) c h p u‖ ≤
        ∑ p : OrderedFinpartition j, Gp p u := by
    calc
      _ ≤ ∑ p : OrderedFinpartition j,
          ‖qsP1LogCompTerm (K := K) c h p u‖ := norm_sum_le _ _
      _ ≤ ∑ p : OrderedFinpartition j, Gp p u := by
        apply Finset.sum_le_sum
        intro p hp
        calc
          ‖qsP1LogCompTerm (K := K) c h p u‖ =
              ‖(-1 : ℂ) ^ j‖ * ‖qsP1LogTerm (K := K) c p.length h u‖ := by
            rw [hcompEq, norm_mul]
          _ = ‖qsP1LogTerm (K := K) c p.length h u‖ := by simp
          _ ≤ Gp p u := hGp_bound p c hc u
  calc
    _ = ‖∑ p : OrderedFinpartition j, qsP1LogCompTerm (K := K) c h p u‖ := by
      rw [hsumEq c u]
    _ ≤ G u := by simpa [G] using hsumBound

private theorem qs_p1_logKernelLine_iteratedDeriv_uniform_majorant
    [IsTotallyComplex K] (h : ℝ → ℂ) (hh : IsQSWeight h)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (j A : ℕ)
    (hAc : b + (j : ℝ) < (A : ℝ)) :
    ∃ G : ℝ → ℝ, Integrable G ∧ ∀ c ∈ Set.Icc a b, ∀ u : ℝ,
      ‖iteratedDeriv j (qsP1LogKernelLine (K := K) c h) u‖ ≤ G u := by
  classical
  let T : ℝ → ℂ := qsTransform K h
  let φ : ℝ → ℝ := fun v => Real.exp (-v)
  let H : ℝ → ℂ := fun v => T (φ v)
  let E : ℝ → ℝ → ℂ := fun c v => ((Real.exp (-c * v) : ℝ) : ℂ)
  have hTtop : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) T (Set.Ioi 0) := by
    obtain ⟨hT, _⟩ := qs_transform_bounds_P0 (K := K) h hh 1 0 1 (by norm_num)
    simpa [T] using hT
  have hHtop : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H := by
    apply contDiff_iff_contDiffAt.2
    intro u
    have hT : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) T (φ u) :=
      hTtop.contDiffAt (isOpen_Ioi.mem_nhds (Real.exp_pos (-u)))
    exact hT.comp u (by fun_prop)
  have hEtop (c : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (E c) := by
    apply contDiff_iff_contDiffAt.2
    intro u
    dsimp [E]
    have hlin : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun v : ℝ => -c * v) u := by fun_prop
    exact Complex.ofRealCLM.contDiff.comp_contDiffAt u
      (Real.contDiff_exp.contDiffAt.comp u hlin)
  have hEderiv (c : ℝ) (i : ℕ) (u : ℝ) :
      iteratedDeriv i (E c) u =
        ((((-c : ℝ) ^ i * Real.exp (-c * u) : ℝ) : ℂ)) := by
    have hcast := congrFun
      (qs_p1_iteratedDeriv_ofReal_comp (fun v : ℝ => Real.exp (-c * v))
        (by fun_prop) i) u
    have hreal := congrFun (iteratedDeriv_exp_const_mul i (-c : ℝ)) u
    simpa [E, neg_mul] using hcast.trans (congrArg (fun x : ℝ => (x : ℂ)) hreal)
  have hformula (c u : ℝ) :
      iteratedDeriv j (E c * H) u =
        ∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℂ) * iteratedDeriv i (E c) u *
            iteratedDeriv (j - i) H u := by
    have hE : ContDiffAt ℝ (j : ℕ∞) (E c) u :=
      ((contDiff_iff_contDiffAt.1 (hEtop c)) u).of_le (by simp)
    have hH : ContDiffAt ℝ (j : ℕ∞) H u :=
      ((contDiff_iff_contDiffAt.1 hHtop u).of_le (by simp))
    exact iteratedDeriv_mul hE hH
  have hEx (k : ℕ) (hk : k ≤ j) :
      ∃ G : ℝ → ℝ, Integrable G ∧ ∀ c ∈ Set.Icc a b, ∀ u : ℝ,
        ‖E c u * iteratedDeriv k H u‖ ≤ G u := by
    have hk' : b + (k : ℝ) < (A : ℝ) := by
      have hk'' : (k : ℝ) ≤ (j : ℝ) := by exact_mod_cast hk
      linarith
    simpa [E, H, T, φ] using
      qs_p1_weighted_logComp_uniform_majorant (K := K) h hh a b ha hab k A hk'
  let Gk : ℕ → (ℝ → ℝ) := fun k =>
    if hk : k ≤ j then Classical.choose (hEx k hk) else 0
  have hGk_int (k : ℕ) : Integrable (Gk k) := by
    by_cases hk : k ≤ j
    · simpa [Gk, hk] using (Classical.choose_spec (hEx k hk)).1
    · simp [Gk, hk]
  have hGk_bound (k : ℕ) (hk : k ≤ j) (c : ℝ) (hc : c ∈ Set.Icc a b)
      (u : ℝ) : ‖E c u * iteratedDeriv k H u‖ ≤ Gk k u := by
    have hGkeq : Gk k = Classical.choose (hEx k hk) := by simp [Gk, hk]
    rw [hGkeq]
    exact (Classical.choose_spec (hEx k hk)).2 c hc u
  let M : ℝ := max 1 b
  let D : ℕ → ℝ := fun i => (j.choose i : ℝ) * M ^ i
  let G : ℝ → ℝ := fun u =>
    ∑ i ∈ Finset.range (j + 1), D i * Gk (j - i) u
  have hD_nonneg (i : ℕ) : 0 ≤ D i := by
    dsimp [D]
    positivity
  have hG : Integrable G := by
    have hterm (i : ℕ) : Integrable (fun u : ℝ => D i * Gk (j - i) u) := by
      simpa [mul_comm] using (hGk_int (j - i)).const_mul (D i)
    have hall : ∀ s : Finset ℕ,
        Integrable (fun u : ℝ => ∑ i ∈ s, D i * Gk (j - i) u) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih =>
          have hsumEq :
              (fun u : ℝ => ∑ k ∈ insert i s, D k * Gk (j - k) u) =
                (fun u : ℝ => D i * Gk (j - i) u) +
                  (fun u : ℝ => ∑ k ∈ s, D k * Gk (j - k) u) := by
            funext u
            simp [Finset.sum_insert, hi]
          rw [hsumEq]
          exact (hterm i).add ih
    simpa [G] using hall (Finset.range (j + 1))
  have hterm_bound (i : ℕ) (hi : i ∈ Finset.range (j + 1))
      (c u : ℝ) (hc : c ∈ Set.Icc a b) :
      ‖(j.choose i : ℂ) * iteratedDeriv i (E c) u *
          iteratedDeriv (j - i) H u‖ ≤ D i * Gk (j - i) u := by
    have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hcpos : 0 < c := lt_of_lt_of_le ha hc.1
    have hcM : c ≤ M := le_trans hc.2 (le_max_right _ _)
    have hcoef : ‖(((j.choose i : ℝ) * (-c) ^ i : ℝ) : ℂ)‖ ≤ D i := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (Nat.cast_nonneg _), abs_pow, abs_neg, abs_of_pos hcpos]
      dsimp [D]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (le_of_lt hcpos) hcM i) (Nat.cast_nonneg _)
    have heq :
        (j.choose i : ℂ) * iteratedDeriv i (E c) u * iteratedDeriv (j - i) H u =
          (((j.choose i : ℝ) * (-c) ^ i : ℝ) : ℂ) *
            (E c u * iteratedDeriv (j - i) H u) := by
      rw [hEderiv]
      simp [E, Complex.ofReal_mul]
      ring
    have hbase := hGk_bound (j - i) (Nat.sub_le _ _) c hc u
    rw [heq, norm_mul]
    calc
      ‖(((j.choose i : ℝ) * (-c) ^ i : ℝ) : ℂ)‖ *
          ‖E c u * iteratedDeriv (j - i) H u‖ ≤
          D i * ‖E c u * iteratedDeriv (j - i) H u‖ :=
        mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
      _ ≤ D i * Gk (j - i) u :=
        mul_le_mul_of_nonneg_left hbase (hD_nonneg i)
  refine ⟨G, hG, ?_⟩
  intro c hc u
  have hsumBound :
      ‖∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℂ) * iteratedDeriv i (E c) u *
            iteratedDeriv (j - i) H u‖ ≤ G u := by
    calc
      _ ≤ ∑ i ∈ Finset.range (j + 1),
          ‖(j.choose i : ℂ) * iteratedDeriv i (E c) u *
            iteratedDeriv (j - i) H u‖ := norm_sum_le _ _
      _ ≤ G u := by
        apply Finset.sum_le_sum
        intro i hi
        exact hterm_bound i hi c u hc
  have hline : qsP1LogKernelLine (K := K) c h = E c * H := by
    funext v
    rfl
  calc
    ‖iteratedDeriv j (qsP1LogKernelLine (K := K) c h) u‖ =
        ‖∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℂ) * iteratedDeriv i (E c) u *
            iteratedDeriv (j - i) H u‖ := by
      rw [hline, hformula]
    _ ≤ G u := hsumBound

private theorem qs_p1_logKernelLine_iteratedDeriv_integrable_all [IsTotallyComplex K]
    (h : ℝ → ℂ) (hh : IsQSWeight h) (c : ℝ) (hc : 0 < c)
    (j A : ℕ) (hAc : c + (j : ℝ) < (A : ℝ)) :
    Integrable (fun u : ℝ =>
      iteratedDeriv j (qsP1LogKernelLine (K := K) c h) u) := by
  classical
  let T : ℝ → ℂ := qsTransform K h
  let φ : ℝ → ℝ := fun v => Real.exp (-v)
  let H : ℝ → ℂ := fun v => T (φ v)
  let E : ℝ → ℂ := fun v => ((Real.exp (-c * v) : ℝ) : ℂ)
  let G : ℝ → ℂ := fun v => E v * H v
  have hTtop : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) T (Set.Ioi 0) := by
    obtain ⟨hT, _⟩ := qs_transform_bounds_P0 (K := K) h hh 1 0 1 (by norm_num)
    simpa [T] using hT
  have hEtop : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) E := by
    apply contDiff_iff_contDiffAt.2
    intro u
    dsimp [E]
    have hlin : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun v : ℝ => -c * v) u := by fun_prop
    exact Complex.ofRealCLM.contDiff.comp_contDiffAt u
      (Real.contDiff_exp.contDiffAt.comp u hlin)
  have hφtop : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ := by
    dsimp [φ]
    fun_prop
  have hHtop : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H := by
    apply contDiff_iff_contDiffAt.2
    intro u
    have hT : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) T (φ u) :=
      hTtop.contDiffAt (isOpen_Ioi.mem_nhds (Real.exp_pos (-u)))
    exact hT.comp u ((contDiff_iff_contDiffAt.1 hφtop) u)
  have hGtop : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G := by
    exact hEtop.mul hHtop
  have hEderiv (i : ℕ) (u : ℝ) :
      iteratedDeriv i E u =
        (((-c : ℝ) ^ i * Real.exp (-c * u) : ℝ) : ℂ) := by
    have hcast := congrFun
      (qs_p1_iteratedDeriv_ofReal_comp (fun v : ℝ => Real.exp (-c * v)) (by fun_prop) i) u
    have hreal := congrFun (iteratedDeriv_exp_const_mul i (-c : ℝ)) u
    simpa [E, neg_mul] using hcast.trans (congrArg (fun x : ℝ => (x : ℂ)) hreal)
  have htermInt (i : ℕ) :
      Integrable (fun u : ℝ =>
        (j.choose i : ℂ) * iteratedDeriv i E u * iteratedDeriv (j - i) H u) := by
    have hki : j - i ≤ j := Nat.sub_le _ _
    have hAc' : c + ((j - i : ℕ) : ℝ) < (A : ℝ) := by
      have hki' : ((j - i : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast hki
      exact lt_of_le_of_lt (by nlinarith [hki']) hAc
    have hbase := qs_p1_weighted_logComp_integrable (K := K) h hh c hc
      (j - i) A hAc'
    have heq :
        (fun u : ℝ =>
          (j.choose i : ℂ) * iteratedDeriv i E u * iteratedDeriv (j - i) H u) =
          fun u : ℝ =>
            ((j.choose i : ℂ) * ((-c : ℝ) ^ i : ℂ)) *
              (E u * iteratedDeriv (j - i)
                (fun v : ℝ => qsTransform K h (Real.exp (-v))) u) := by
      funext u
      rw [hEderiv]
      simp [E, H, T, φ, Complex.ofReal_mul, Complex.ofReal_pow]
      ring
    rw [heq]
    exact hbase.const_mul ((j.choose i : ℂ) * ((-c : ℝ) ^ i : ℂ))
  have hformula (u : ℝ) :
      iteratedDeriv j G u =
        ∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℂ) * iteratedDeriv i E u * iteratedDeriv (j - i) H u := by
    have hE : ContDiffAt ℝ (j : ℕ∞) E u := by
      exact ((contDiff_iff_contDiffAt.1 hEtop) u).of_le (by simp)
    have hH : ContDiffAt ℝ (j : ℕ∞) H u := by
      exact ((contDiff_iff_contDiffAt.1 hHtop) u).of_le (by simp)
    change iteratedDeriv j (E * H) u = _
    exact iteratedDeriv_mul hE hH
  have hsum : Integrable (fun u : ℝ =>
      ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℂ) * iteratedDeriv i E u * iteratedDeriv (j - i) H u) := by
    have hall : ∀ s : Finset ℕ, Integrable (fun u : ℝ =>
        ∑ i ∈ s, (j.choose i : ℂ) * iteratedDeriv i E u *
          iteratedDeriv (j - i) H u) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih =>
          have hsumEq :
              (fun u : ℝ => ∑ k ∈ insert i s,
                (j.choose k : ℂ) * iteratedDeriv k E u *
                  iteratedDeriv (j - k) H u) =
                (fun u : ℝ => (j.choose i : ℂ) * iteratedDeriv i E u *
                    iteratedDeriv (j - i) H u) +
                  (fun u : ℝ => ∑ k ∈ s,
                    (j.choose k : ℂ) * iteratedDeriv k E u *
                      iteratedDeriv (j - k) H u) := by
            funext u
            simp [Finset.sum_insert, hi]
          rw [hsumEq]
          exact (htermInt i).add ih
    exact hall _
  have heq :
      (fun u : ℝ => iteratedDeriv j (qsP1LogKernelLine (K := K) c h) u) =
        fun u => ∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℂ) * iteratedDeriv i E u * iteratedDeriv (j - i) H u := by
    funext u
    change iteratedDeriv j G u = _
    exact hformula u
  rw [heq]
  exact hsum

private theorem qs_p1_positive_halfplane_punctured_one_preconnected :
    IsPreconnected {z : ℂ | 0 < z.re ∧ z ≠ 1} := by
  letI : SMul ℝ ℂ := Complex.instRCLike.toSMul
  let A : Set ℂ := {z | 0 < z.re} ∩ {z | z.re < 1}
  let B : Set ℂ := {z | 0 < z.re} ∩ {z | 0 < z.im}
  let C : Set ℂ := {z | 0 < z.re} ∩ {z | z.im < 0}
  let R : Set ℂ := {z | 1 < z.re}
  have hA : IsPreconnected A := by
    apply Convex.isPreconnected
    exact (convex_halfSpace_re_gt 0).inter (convex_halfSpace_re_lt 1)
  have hB : IsPreconnected B := by
    apply Convex.isPreconnected
    exact (convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 0)
  have hC : IsPreconnected C := by
    apply Convex.isPreconnected
    exact (convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_lt 0)
  have hR : IsPreconnected R := by
    apply Convex.isPreconnected
    simpa [R] using (convex_halfSpace_re_gt 1)
  have hAB : IsPreconnected (A ∪ B) :=
    hA.union' ⟨(1 / 2 : ℂ) + Complex.I, by norm_num [A, B]⟩ hB
  have hABC : IsPreconnected ((A ∪ B) ∪ C) :=
    hAB.union' ⟨(1 / 2 : ℂ) - Complex.I, by norm_num [A, B, C]⟩ hC
  have hAll : IsPreconnected (((A ∪ B) ∪ C) ∪ R) :=
    hABC.union' ⟨(2 : ℂ) + Complex.I, by norm_num [A, B, C, R]⟩ hR
  have hcover : {z : ℂ | 0 < z.re ∧ z ≠ 1} = (((A ∪ B) ∪ C) ∪ R) := by
    ext z
    constructor
    · rintro ⟨hz, hne⟩
      rcases lt_trichotomy z.re 1 with hlt | heq | hgt
      · exact Or.inl (Or.inl (Or.inl ⟨hz, hlt⟩))
      · have him : z.im ≠ 0 := by
          intro him
          apply hne
          exact Complex.ext heq him
        rcases lt_or_gt_of_ne him with himlt | himgt
        · exact Or.inl (Or.inr ⟨hz, himlt⟩)
        · exact Or.inl (Or.inl (Or.inr ⟨hz, himgt⟩))
      · exact Or.inr hgt
    · rintro (((⟨hz, hlt⟩ | ⟨hz, him⟩) | ⟨hz, him⟩) | hgt)
      · refine ⟨hz, ?_⟩
        intro heq
        rw [heq] at hlt
        norm_num at hlt
      · exact ⟨hz, by intro heq; rw [heq] at him; norm_num at him⟩
      · exact ⟨hz, by intro heq; rw [heq] at him; norm_num at him⟩
      · change 1 < z.re at hgt
        refine ⟨by linarith, ?_⟩
        intro heq
        rw [heq] at hgt
        norm_num at hgt
  rw [hcover]
  exact hAll

private theorem qs_p1_transform_mellin_eq_regularized [IsTotallyComplex K]
    (h : ℝ → ℂ) (hh : IsQSWeight h) (δ : ℝ) (hδ : 0 < δ)
    (hconst : ∀ x ∈ Set.Icc (0 : ℝ) δ, h x = h 0) (u : ℂ)
    (hu : 0 < u.re) (hu1 : u ≠ 1) :
    mellin (qsTransform K h) u =
      qsGammaRatio K u * qsP1Mellin h δ (1 - u) := by
  let D : Set ℂ := {z | 0 < z.re ∧ z ≠ 1}
  let F : ℂ → ℂ := mellin (qsTransform K h)
  let G : ℂ → ℂ := fun z => qsGammaRatio K z * qsP1Mellin h δ (1 - z)
  have hDopen : IsOpen D := by
    change IsOpen ({z : ℂ | 0 < z.re} ∩ {z : ℂ | z ≠ (1 : ℂ)})
    exact (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_ne (x := (1 : ℂ)))
  have hFdiff : DifferentiableOn ℂ F D := by
    intro z hz
    exact (qs_p1_transform_mellin_differentiableAt (K := K) h hh hz.1).2.differentiableWithinAt
  have hGdiff : DifferentiableOn ℂ G D := by
    intro z hz
    have hGamma := qs_p1_gammaRatio_differentiableAt (K := K) hz.1
    have h1z : 1 - z ≠ 0 := by
      intro hzero
      apply hz.2
      calc
        z = 1 - (1 - z) := by ring
        _ = 1 := by rw [hzero]; ring
    have hregOn := qs_p1_regularized_mellin_differentiable h hh δ hδ hconst
    have hregAt : DifferentiableAt ℂ (qsP1Mellin h δ) (1 - z) :=
      (hregOn (1 - z) h1z).differentiableAt (isOpen_ne.mem_nhds h1z)
    have hregComp : DifferentiableAt ℂ (fun w : ℂ => qsP1Mellin h δ (1 - w)) z :=
      hregAt.comp z (by fun_prop)
    change DifferentiableWithinAt ℂ
      (fun w : ℂ => qsGammaRatio K w * qsP1Mellin h δ (1 - w)) D z
    exact (hGamma.mul hregComp).differentiableWithinAt
  have hFanalytic : AnalyticOnNhd ℂ F D := hFdiff.analyticOnNhd hDopen
  have hGanalytic : AnalyticOnNhd ℂ G D := hGdiff.analyticOnNhd hDopen
  have hstrip : ∀ z : ℂ, 0 < z.re → z.re < 1 → F z = G z := by
    intro z hz0 hz1
    have hP0 := qs_transform_mellin_P0 (K := K) h hh z hz0 hz1
    have hRe : 0 < (1 - z).re := by rw [Complex.sub_re, Complex.one_re]; linarith
    have hreg := qs_p1_regularized_mellin_agrees h hh δ hδ hconst (1 - z) hRe
    rw [← hreg] at hP0
    simpa [F, G] using hP0
  have hstripOpen : IsOpen {z : ℂ | 0 < z.re ∧ z.re < 1} := by
    exact (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hmid : (1 / 2 : ℂ) ∈ D := by norm_num [D]
  have hfg : F =ᶠ[𝓝 (1 / 2 : ℂ)] G := by
    filter_upwards [hstripOpen.mem_nhds (by norm_num)] with z hz
    exact hstrip z hz.1 hz.2
  have hEq := hFanalytic.eqOn_of_preconnected_of_eventuallyEq hGanalytic
    (by simpa [D] using qs_p1_positive_halfplane_punctured_one_preconnected)
    hmid hfg
  exact hEq ⟨hu, hu1⟩

private theorem qs_p1_fourier_norm_bound (f : ℝ → ℂ) (hf : Integrable f) (w : ℝ) :
    ‖𝓕 f w‖ ≤ ∫ u : ℝ, ‖f u‖ := by
  exact VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 volume (innerₗ ℝ) f w

private theorem qs_p1_fourier_polynomial_decay (g : ℝ → ℂ)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hderiv : ∀ j : ℕ, Integrable (iteratedDeriv j g)) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℝ, ‖𝓕 g w‖ ≤ C / (1 + |w|) ^ N := by
  let A₀ : ℝ := ∫ u : ℝ, ‖g u‖
  let Aₙ : ℝ := ∫ u : ℝ, ‖iteratedDeriv N g u‖
  have hA₀ : 0 ≤ A₀ := by
    dsimp [A₀]
    exact integral_nonneg (fun _ => norm_nonneg _)
  have hAₙ : 0 ≤ Aₙ := by
    dsimp [Aₙ]
    exact integral_nonneg (fun _ => norm_nonneg _)
  let C : ℝ := max (A₀ * 2 ^ N) Aₙ
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hfreq : ∀ w : ℝ, ∀ n : ℕ,
      𝓕 (iteratedDeriv n g) w =
        (2 * Real.pi * Complex.I * (w : ℂ)) ^ n * 𝓕 g w := by
    intro w n
    induction n with
    | zero => simp
    | succ n ih =>
      have hdiff : Differentiable ℝ (iteratedDeriv n g) :=
        hg.differentiable_iteratedDeriv n
          (WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top n))
      have hIntDeriv : Integrable (deriv (iteratedDeriv n g)) := by
        rw [← iteratedDeriv_succ]
        exact hderiv (n + 1)
      have hfd := Real.fourier_deriv (hderiv n) hdiff hIntDeriv
      have hpoint := congrFun hfd w
      rw [iteratedDeriv_succ]
      calc
        𝓕 (deriv (iteratedDeriv n g)) w =
            (2 * Real.pi * Complex.I * (w : ℂ)) *
              𝓕 (iteratedDeriv n g) w := by
          simpa [smul_eq_mul] using hpoint
        _ = (2 * Real.pi * Complex.I * (w : ℂ)) ^ (n + 1) * 𝓕 g w := by
          rw [ih]
          ring
  have hqnorm (w : ℝ) :
      ‖(2 * Real.pi * Complex.I * (w : ℂ))‖ = 2 * Real.pi * |w| := by
    have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
    have hpi : ‖(Real.pi : ℂ)‖ = Real.pi := by
      rw [Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    have hI : ‖Complex.I‖ = 1 := by simp
    have hwR : ‖(w : ℂ)‖ = |w| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    calc
      _ = ‖(2 : ℂ)‖ * ‖(Real.pi : ℂ)‖ * ‖Complex.I‖ * ‖(w : ℂ)‖ := by
        simp only [norm_mul]
      _ = 2 * Real.pi * |w| := by rw [htwo, hpi, hI, hwR]; ring
  refine ⟨C, hC, ?_⟩
  intro w
  have hFourier₀ := qs_p1_fourier_norm_bound g (hderiv 0) w
  have hden : 0 < (1 + |w|) ^ N := pow_pos (by positivity) _
  rcases le_total |w| 1 with hw | hw
  · apply (le_div_iff₀ hden).2
    have hdenLe : (1 + |w|) ^ N ≤ (2 : ℝ) ^ N :=
      pow_le_pow_left₀ (by positivity) (by linarith) N
    calc
      ‖𝓕 g w‖ * (1 + |w|) ^ N ≤ A₀ * (1 + |w|) ^ N :=
        mul_le_mul_of_nonneg_right hFourier₀ (by positivity)
      _ ≤ A₀ * 2 ^ N := mul_le_mul_of_nonneg_left hdenLe hA₀
      _ ≤ C := le_max_left _ _
  · have hqpos : 0 < 2 * Real.pi * |w| := by positivity
    have hqge : 1 + |w| ≤ 2 * Real.pi * |w| := by
      nlinarith [Real.pi_gt_three, abs_nonneg w, hw]
    have hqpow : (1 + |w|) ^ N ≤ (2 * Real.pi * |w|) ^ N :=
      pow_le_pow_left₀ (by positivity) hqge N
    have hFourierN := qs_p1_fourier_norm_bound (iteratedDeriv N g) (hderiv N) w
    have hnormN : ‖𝓕 (iteratedDeriv N g) w‖ =
        (2 * Real.pi * |w|) ^ N * ‖𝓕 g w‖ := by
      rw [hfreq w N, norm_mul, norm_pow, hqnorm]
    have hprod : ‖𝓕 g w‖ * (1 + |w|) ^ N ≤ Aₙ := by
      calc
        _ ≤ ‖𝓕 g w‖ * (2 * Real.pi * |w|) ^ N :=
          mul_le_mul_of_nonneg_left hqpow (norm_nonneg _)
        _ = ‖𝓕 (iteratedDeriv N g) w‖ := by rw [hnormN]; ring
        _ ≤ Aₙ := by simpa [Aₙ] using hFourierN
    apply (le_div_iff₀ hden).2
    calc
      ‖𝓕 g w‖ * (1 + |w|) ^ N ≤ Aₙ := hprod
      _ ≤ C := le_max_right _ _

private theorem qs_p1_fourier_polynomial_decay_uniform
    (g : ℝ → ℝ → ℂ) (hg : ∀ c, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (g c))
    (a b : ℝ) (hderiv : ∀ c ∈ Set.Icc a b, ∀ n,
      Integrable (iteratedDeriv n (g c)))
    (N : ℕ) (A₀ Aₙ : ℝ) (hA₀ : 0 ≤ A₀) (hAₙ : 0 ≤ Aₙ)
    (hbound₀ : ∀ c ∈ Set.Icc a b, ∫ u : ℝ, ‖g c u‖ ≤ A₀)
    (hboundₙ : ∀ c ∈ Set.Icc a b,
      ∫ u : ℝ, ‖iteratedDeriv N (g c) u‖ ≤ Aₙ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c ∈ Set.Icc a b, ∀ w : ℝ,
      ‖𝓕 (g c) w‖ ≤ C / (1 + |w|) ^ N := by
  let C : ℝ := max (A₀ * 2 ^ N) Aₙ
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hfreq (c : ℝ) (hc : c ∈ Set.Icc a b) (w : ℝ) (n : ℕ) :
      𝓕 (iteratedDeriv n (g c)) w =
        (2 * Real.pi * Complex.I * (w : ℂ)) ^ n * 𝓕 (g c) w := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hdiff : Differentiable ℝ (iteratedDeriv n (g c)) :=
        (hg c).differentiable_iteratedDeriv n
          (WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top n))
      have hIntDeriv : Integrable (deriv (iteratedDeriv n (g c))) := by
        rw [← iteratedDeriv_succ]
        exact hderiv c hc (n + 1)
      have hfd := Real.fourier_deriv (hderiv c hc n) hdiff hIntDeriv
      have hpoint := congrFun hfd w
      rw [iteratedDeriv_succ]
      calc
        𝓕 (deriv (iteratedDeriv n (g c))) w =
            (2 * Real.pi * Complex.I * (w : ℂ)) *
              𝓕 (iteratedDeriv n (g c)) w := by
          simpa [smul_eq_mul] using hpoint
        _ = (2 * Real.pi * Complex.I * (w : ℂ)) ^ (n + 1) *
              𝓕 (g c) w := by rw [ih]; ring
  have hqnorm (w : ℝ) :
      ‖(2 * Real.pi * Complex.I * (w : ℂ))‖ = 2 * Real.pi * |w| := by
    have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
    have hpi : ‖(Real.pi : ℂ)‖ = Real.pi := by
      rw [Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    have hI : ‖Complex.I‖ = 1 := by simp
    have hwR : ‖(w : ℂ)‖ = |w| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    calc
      _ = ‖(2 : ℂ)‖ * ‖(Real.pi : ℂ)‖ * ‖Complex.I‖ * ‖(w : ℂ)‖ := by
        simp only [norm_mul]
      _ = 2 * Real.pi * |w| := by rw [htwo, hpi, hI, hwR]; ring
  refine ⟨C, hC, ?_⟩
  intro c hc w
  have hFourier₀ := qs_p1_fourier_norm_bound (g c) (hderiv c hc 0) w
  have hFourier₀' : ‖𝓕 (g c) w‖ ≤ A₀ := hFourier₀.trans (hbound₀ c hc)
  have hden : 0 < (1 + |w|) ^ N := pow_pos (by positivity) _
  rcases le_total |w| 1 with hw | hw
  · apply (le_div_iff₀ hden).2
    have hdenLe : (1 + |w|) ^ N ≤ (2 : ℝ) ^ N :=
      pow_le_pow_left₀ (by positivity) (by linarith) N
    calc
      ‖𝓕 (g c) w‖ * (1 + |w|) ^ N ≤ A₀ * (1 + |w|) ^ N :=
        mul_le_mul_of_nonneg_right hFourier₀' (by positivity)
      _ ≤ A₀ * 2 ^ N := mul_le_mul_of_nonneg_left hdenLe hA₀
      _ ≤ C := le_max_left _ _
  · have hqpos : 0 < 2 * Real.pi * |w| := by positivity
    have hqge : 1 + |w| ≤ 2 * Real.pi * |w| := by
      nlinarith [Real.pi_gt_three, abs_nonneg w, hw]
    have hqpow : (1 + |w|) ^ N ≤ (2 * Real.pi * |w|) ^ N :=
      pow_le_pow_left₀ (by positivity) hqge N
    have hFourierN := qs_p1_fourier_norm_bound
      (iteratedDeriv N (g c)) (hderiv c hc N) w
    have hFourierN' : ‖𝓕 (iteratedDeriv N (g c)) w‖ ≤ Aₙ :=
      hFourierN.trans (hboundₙ c hc)
    have hnormN : ‖𝓕 (iteratedDeriv N (g c)) w‖ =
        (2 * Real.pi * |w|) ^ N * ‖𝓕 (g c) w‖ := by
      rw [hfreq c hc w N, norm_mul, norm_pow, hqnorm]
    have hprod : ‖𝓕 (g c) w‖ * (1 + |w|) ^ N ≤ Aₙ := by
      calc
        _ ≤ ‖𝓕 (g c) w‖ * (2 * Real.pi * |w|) ^ N :=
          mul_le_mul_of_nonneg_left hqpow (norm_nonneg _)
        _ = ‖𝓕 (iteratedDeriv N (g c)) w‖ := by rw [hnormN]; ring
        _ ≤ Aₙ := hFourierN'
    apply (le_div_iff₀ hden).2
    calc
      ‖𝓕 (g c) w‖ * (1 + |w|) ^ N ≤ Aₙ := hprod
      _ ≤ C := le_max_right _ _

private theorem qs_p1_mellin_eq_fourier_line (h : ℝ → ℂ) (c t : ℝ) :
    mellin h ((c : ℂ) + (t : ℂ) * Complex.I) =
      𝓕 (qsP1MellinLogKernel c h) (t / (2 * Real.pi)) := by
  rw [mellin_eq_fourier]
  have hfun : (fun u : ℝ =>
      Real.exp (-((c : ℂ) + (t : ℂ) * Complex.I).re * u) • h (Real.exp (-u))) =
        qsP1MellinLogKernel c h := by
    funext u
    simp [qsP1MellinLogKernel, smul_eq_mul, Complex.ofReal_exp]
  rw [hfun]
  simp

private theorem qs_p1_mellin_vertical_polynomial_decay_uniform (h : ℝ → ℂ)
    (hh : IsQSWeight h) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c ∈ Set.Icc a b, ∀ t : ℝ,
      ‖mellin h ((c : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C / (1 + |t|) ^ N := by
  classical
  let g : ℝ → ℝ → ℂ := fun c => qsP1MellinLogKernel c h
  have hg (c : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (g c) := by
    have hker : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (qsP1MellinLogKernel c h) := by
      have hhs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h := hh.1
      unfold qsP1MellinLogKernel
      fun_prop
    simpa [g] using hker
  have hderiv : ∀ c ∈ Set.Icc a b, ∀ n,
      Integrable (iteratedDeriv n (g c)) := by
    intro c hc n
    have hcpos : 0 < c := lt_of_lt_of_le ha hc.1
    simpa [g] using qs_p1_iteratedDeriv_logKernel_integrable h hh c hcpos n
  have hmajor (n : ℕ) :
      ∃ G : ℝ → ℝ, Integrable G ∧ ∀ c ∈ Set.Icc a b, ∀ u : ℝ,
        ‖iteratedDeriv n (g c) u‖ ≤ G u := by
    simpa [g] using
      qs_p1_mellinLogKernel_iteratedDeriv_uniform_majorant h hh a b ha hab n
  let G₀ : ℝ → ℝ := Classical.choose (hmajor 0)
  let Gₙ : ℝ → ℝ := Classical.choose (hmajor N)
  have hG₀ : Integrable G₀ := (Classical.choose_spec (hmajor 0)).1
  have hGₙ : Integrable Gₙ := (Classical.choose_spec (hmajor N)).1
  have hG₀eq : G₀ = Classical.choose (hmajor 0) := by rfl
  have hGₙeq : Gₙ = Classical.choose (hmajor N) := by rfl
  have hG₀bound (c : ℝ) (hc : c ∈ Set.Icc a b) (u : ℝ) : ‖g c u‖ ≤ G₀ u := by
    rw [hG₀eq]
    simpa [g, iteratedDeriv_zero] using (Classical.choose_spec (hmajor 0)).2 c hc u
  have hGₙbound (c : ℝ) (hc : c ∈ Set.Icc a b) (u : ℝ) :
      ‖iteratedDeriv N (g c) u‖ ≤ Gₙ u := by
    rw [hGₙeq]
    exact (Classical.choose_spec (hmajor N)).2 c hc u
  let A₀ : ℝ := ∫ u : ℝ, G₀ u
  let Aₙ : ℝ := ∫ u : ℝ, Gₙ u
  have hA₀ : 0 ≤ A₀ := by
    dsimp [A₀]
    exact integral_nonneg
      (fun u => le_trans (norm_nonneg _) (hG₀bound a ⟨le_rfl, hab⟩ u))
  have hAₙ : 0 ≤ Aₙ := by
    dsimp [Aₙ]
    exact integral_nonneg
      (fun u => le_trans (norm_nonneg _) (hGₙbound a ⟨le_rfl, hab⟩ u))
  have hbound₀ (c : ℝ) (hc : c ∈ Set.Icc a b) :
      ∫ u : ℝ, ‖g c u‖ ≤ A₀ := by
    have hnorm : Integrable (fun u : ℝ => ‖g c u‖) := by
      simpa [iteratedDeriv_zero] using (hderiv c hc 0).norm
    calc
      _ ≤ ∫ u : ℝ, G₀ u := integral_mono_ae hnorm hG₀
        (Filter.Eventually.of_forall fun u => hG₀bound c hc u)
      _ = A₀ := by rfl
  have hboundₙ (c : ℝ) (hc : c ∈ Set.Icc a b) :
      ∫ u : ℝ, ‖iteratedDeriv N (g c) u‖ ≤ Aₙ := by
    calc
      _ ≤ ∫ u : ℝ, Gₙ u := integral_mono_ae (hderiv c hc N).norm hGₙ
        (Filter.Eventually.of_forall fun u => hGₙbound c hc u)
      _ = Aₙ := by rfl
  obtain ⟨C, hC, hFourier⟩ := qs_p1_fourier_polynomial_decay_uniform
    g hg a b hderiv N A₀ Aₙ hA₀ hAₙ hbound₀ hboundₙ
  refine ⟨C * (2 * Real.pi) ^ N, mul_nonneg hC (by positivity), ?_⟩
  intro c hc t
  let w : ℝ := t / (2 * Real.pi)
  have ht : t = (2 * Real.pi) * w := by
    dsimp [w]
    field_simp
  have habs : |t| = 2 * Real.pi * |w| := by
    rw [ht, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  have hscale : 1 + |t| ≤ (2 * Real.pi) * (1 + |w|) := by
    rw [habs]
    have hq : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    nlinarith [abs_nonneg w]
  have hscalePow : (1 + |t|) ^ N ≤ (2 * Real.pi) ^ N * (1 + |w|) ^ N := by
    calc
      (1 + |t|) ^ N ≤ ((2 * Real.pi) * (1 + |w|)) ^ N :=
        pow_le_pow_left₀ (by positivity) hscale N
      _ = (2 * Real.pi) ^ N * (1 + |w|) ^ N := by rw [mul_pow]
  have hline : mellin h ((c : ℂ) + (t : ℂ) * Complex.I) = 𝓕 (g c) w := by
    simpa [g, w] using qs_p1_mellin_eq_fourier_line h c t
  have hdenw : 0 < (1 + |w|) ^ N := pow_pos (by positivity) _
  have hdent : 0 < (1 + |t|) ^ N := pow_pos (by positivity) _
  calc
    ‖mellin h ((c : ℂ) + (t : ℂ) * Complex.I)‖ = ‖𝓕 (g c) w‖ := by rw [hline]
    _ ≤ C / (1 + |w|) ^ N := hFourier c hc w
    _ ≤ C * (2 * Real.pi) ^ N / (1 + |t|) ^ N := by
      apply (div_le_div_iff₀ hdenw hdent).2
      calc
        C * (1 + |t|) ^ N ≤ C * ((2 * Real.pi) ^ N * (1 + |w|) ^ N) :=
          mul_le_mul_of_nonneg_left hscalePow hC
        _ = (C * (2 * Real.pi) ^ N) * (1 + |w|) ^ N := by ring

private theorem qs_p1_mellin_differentiableAt (h : ℝ → ℂ) (hh : IsQSWeight h)
    {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ (mellin h) s := by
  obtain ⟨B, hB⟩ := hh.2.1
  have hlocal : LocallyIntegrableOn h (Set.Ioi (0 : ℝ)) :=
    hh.1.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi
  have htop : h =O[atTop] (fun x : ℝ => x ^ (-(s.re + 1) : ℝ)) := by
    rw [Asymptotics.isBigO_iff_eventually]
    filter_upwards [eventually_atTop.2 ⟨1, fun _ hx => hx⟩] with C hC
    filter_upwards [eventually_atTop.2 ⟨max B 1, fun _ hx => hx⟩] with x hx
    have hxB : B ≤ x := (le_max_left _ _).trans hx
    simp [hB x hxB]
    have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
    positivity
  have hbot : h =O[nhdsWithin 0 (Set.Ioi (0 : ℝ))] (fun _ : ℝ => (1 : ℂ)) := by
    simpa using
      (hh.1.continuous.continuousAt.mono_left nhdsWithin_le_nhds).isBigO_one ℂ
  exact mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := 0) hlocal htop
    (by linarith) (by simpa using hbot) hs

private theorem qs_p1_vertical_integral_shift (F : ℂ → ℂ) (a b : ℝ) (hab : a < b)
    (hcont : ContinuousOn F {z : ℂ | a ≤ z.re ∧ z.re ≤ b})
    (hdiff : ∀ z : ℂ, a < z.re → z.re < b → DifferentiableAt ℂ F z)
    (hdecay : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      ‖F z‖ ≤ C / (1 + |z.im|) ^ 2) :
    ∫ t : ℝ, F ((a : ℂ) + (t : ℂ) * Complex.I) =
      ∫ t : ℝ, F ((b : ℂ) + (t : ℂ) * Complex.I) := by
  classical
  obtain ⟨C, hC, hdecay⟩ := hdecay
  have hlineInt (c : ℝ) (hca : a ≤ c) (hcb : c ≤ b) :
      Integrable (fun t : ℝ => F ((c : ℂ) + (t : ℂ) * Complex.I)) := by
    have hstrip : Set.MapsTo (fun t : ℝ => (c : ℂ) + (t : ℂ) * Complex.I) Set.univ
        {z : ℂ | a ≤ z.re ∧ z.re ≤ b} := by
      intro t _
      simp only [Set.mem_setOf_eq, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero,
        zero_add]
      simpa using ⟨hca, hcb⟩
    have hlineCont : Continuous (fun t : ℝ => F ((c : ℂ) + (t : ℂ) * Complex.I)) := by
      change Continuous (F ∘ fun t : ℝ => (c : ℂ) + (t : ℂ) * Complex.I)
      exact hcont.comp_continuous (by fun_prop) (fun t => hstrip (Set.mem_univ t))
    have hbound : ∀ t : ℝ,
        ‖F ((c : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * (1 + t ^ 2)⁻¹ := by
      intro t
      have h := hdecay ((c : ℂ) + (t : ℂ) * Complex.I) (by simpa using hca)
        (by simpa using hcb)
      have him : ((c : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
      rw [him] at h
      have hden : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by
        nlinarith [sq_abs t, abs_nonneg t]
      have hpos₁ : 0 < (1 + |t|) ^ 2 := by positivity
      have hpos₂ : 0 < 1 + t ^ 2 := by positivity
      have hdiv : C / (1 + |t|) ^ 2 ≤ C / (1 + t ^ 2) := by
        apply (div_le_div_iff₀ hpos₁ hpos₂).2
        nlinarith [hC, hden]
      simpa [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.I_re, Complex.I_im, zero_mul, mul_one, add_zero,
        div_eq_mul_inv] using h.trans hdiv
    refine (integrable_inv_one_add_sq.const_mul C).mono' hlineCont.aestronglyMeasurable ?_
    filter_upwards [] with t
    simpa [div_eq_mul_inv, mul_comm] using hbound t
  let Tn : ℕ → ℝ := fun n => (n : ℝ) + 1
  have hTn : Tendsto Tn atTop atTop := by
    simpa [Tn] using tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hnegTn : Tendsto (fun n : ℕ => -Tn n) atTop atBot := by
    exact tendsto_neg_atTop_atBot.comp hTn
  have hdenTn : Tendsto (fun n : ℕ => (1 + Tn n) ^ 2) atTop atTop := by
    have hbase : Tendsto (fun n : ℕ => Tn n + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop (1 : ℝ) hTn
    have hpow : (fun n : ℕ => (1 + Tn n) ^ 2) = fun n => (Tn n + 1) ^ 2 := by
      funext n
      ring
    rw [hpow]
    exact (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hbase
  have hsmall : Tendsto (fun n : ℕ => 2 * C * (b - a) / (1 + Tn n) ^ 2)
      atTop (𝓝 0) := by
    have hinv : Tendsto (fun n : ℕ => ((1 + Tn n) ^ 2)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hdenTn
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      hinv.mul_const (2 * C * (b - a))
  have hR : Tendsto (fun n : ℕ => ∫ t : ℝ in (-(Tn n))..(Tn n),
      F ((b : ℂ) + (t : ℂ) * Complex.I)) atTop
      (𝓝 <| ∫ t : ℝ, F ((b : ℂ) + (t : ℂ) * Complex.I)) := by
    exact intervalIntegral_tendsto_integral (hlineInt b hab.le (le_of_eq rfl)) hnegTn hTn
  have hL : Tendsto (fun n : ℕ => ∫ t : ℝ in (-(Tn n))..(Tn n),
      F ((a : ℂ) + (t : ℂ) * Complex.I)) atTop
      (𝓝 <| ∫ t : ℝ, F ((a : ℂ) + (t : ℂ) * Complex.I)) := by
    exact intervalIntegral_tendsto_integral (hlineInt a (le_of_eq rfl) hab.le) hnegTn hTn
  have hdiffLimit : Tendsto (fun n : ℕ =>
      (∫ t : ℝ in (-(Tn n))..(Tn n), F ((b : ℂ) + (t : ℂ) * Complex.I)) -
        ∫ t : ℝ in (-(Tn n))..(Tn n), F ((a : ℂ) + (t : ℂ) * Complex.I)) atTop
      (𝓝 ((∫ t : ℝ, F ((b : ℂ) + (t : ℂ) * Complex.I)) -
        ∫ t : ℝ, F ((a : ℂ) + (t : ℂ) * Complex.I))) := hR.sub hL
  have hnorm : Tendsto (fun n : ℕ =>
      ‖(∫ t : ℝ in (-(Tn n))..(Tn n), F ((b : ℂ) + (t : ℂ) * Complex.I)) -
        (∫ t : ℝ in (-(Tn n))..(Tn n), F ((a : ℂ) + (t : ℂ) * Complex.I))‖)
      atTop (𝓝 0) := by
    have hle : ∀ n : ℕ,
        ‖(∫ t : ℝ in (-(Tn n))..(Tn n), F ((b : ℂ) + (t : ℂ) * Complex.I)) -
          (∫ t : ℝ in (-(Tn n))..(Tn n), F ((a : ℂ) + (t : ℂ) * Complex.I))‖ ≤
          2 * C * (b - a) / (1 + Tn n) ^ 2 := by
      intro n
      have hTpos : 0 < Tn n := by dsimp [Tn]; positivity
      let z : ℂ := (a : ℂ) + ((-Tn n : ℝ) : ℂ) * Complex.I
      let w : ℂ := (b : ℂ) + ((Tn n : ℝ) : ℂ) * Complex.I
      have hrectSub : (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) ⊆
          {q : ℂ | a ≤ q.re ∧ q.re ≤ b} := by
        intro q hq
        rw [Complex.mem_reProdIm] at hq
        have hqre : q.re ∈ Set.uIcc a b := by simpa [z, w] using hq.1
        rw [Set.uIcc_of_le hab.le] at hqre
        exact Set.mem_Icc.mp hqre
      have hrectCont : ContinuousOn F (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) :=
        hcont.mono hrectSub
      have hrectDiff : DifferentiableOn ℂ F
          (Set.Ioo (min z.re w.re) (max z.re w.re) ×ℂ
            Set.Ioo (min z.im w.im) (max z.im w.im)) := by
        intro q hq
        rw [Complex.mem_reProdIm] at hq
        have hqre : q.re ∈ Set.Ioo a b := by
          simpa [z, w, min_eq_left hab.le, max_eq_right hab.le] using hq.1
        exact (hdiff q hqre.1 hqre.2).differentiableWithinAt
      have hCauchy :=
        Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
          F z w hrectCont hrectDiff
      have hCauchy' :
          (∫ x : ℝ in a..b, F (x + (-Tn n : ℝ) * Complex.I)) -
          (∫ x : ℝ in a..b, F (x + (Tn n : ℝ) * Complex.I)) +
          Complex.I • (∫ t : ℝ in (-(Tn n))..(Tn n), F (b + t * Complex.I)) -
          Complex.I • (∫ t : ℝ in (-(Tn n))..(Tn n), F (a + t * Complex.I)) = 0 := by
        simpa [z, w, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, sub_zero,
          zero_mul, mul_zero, one_mul, add_zero] using hCauchy
      have hbottom : ‖∫ x : ℝ in a..b, F (x + (-Tn n : ℝ) * Complex.I)‖ ≤
          (C / (1 + Tn n) ^ 2) * |b - a| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro x hx
        have hx' : a ≤ x ∧ x ≤ b := by
          rw [Set.uIoc_of_le hab.le, Set.mem_Ioc] at hx
          exact ⟨hx.1.le, hx.2⟩
        have h := hdecay (x + (-Tn n : ℝ) * Complex.I)
          (by simpa using hx'.1) (by simpa using hx'.2)
        have him : (x + (-Tn n : ℝ) * Complex.I).im = -Tn n := by simp
        rw [him] at h
        simpa [abs_neg, abs_of_pos hTpos] using h
      have htop : ‖∫ x : ℝ in a..b, F (x + (Tn n : ℝ) * Complex.I)‖ ≤
          (C / (1 + Tn n) ^ 2) * |b - a| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro x hx
        have hx' : a ≤ x ∧ x ≤ b := by
          rw [Set.uIoc_of_le hab.le, Set.mem_Ioc] at hx
          exact ⟨hx.1.le, hx.2⟩
        have h := hdecay (x + (Tn n : ℝ) * Complex.I)
          (by simpa using hx'.1) (by simpa using hx'.2)
        have him : (x + (Tn n : ℝ) * Complex.I).im = Tn n := by simp
        rw [him, abs_of_pos hTpos] at h
        exact h
      have hvert : Complex.I •
          ((∫ t : ℝ in (-(Tn n))..(Tn n), F (b + t * Complex.I)) -
            ∫ t : ℝ in (-(Tn n))..(Tn n), F (a + t * Complex.I)) =
          (∫ x : ℝ in a..b, F (x + (Tn n : ℝ) * Complex.I)) -
            ∫ x : ℝ in a..b, F (x + (-Tn n : ℝ) * Complex.I) := by
        linear_combination hCauchy'
      have hnormV : ‖(∫ t : ℝ in (-(Tn n))..(Tn n), F (b + t * Complex.I)) -
          (∫ t : ℝ in (-(Tn n))..(Tn n), F (a + t * Complex.I))‖ ≤
          ‖∫ x : ℝ in a..b, F (x + (Tn n : ℝ) * Complex.I)‖ +
            ‖∫ x : ℝ in a..b, F (x + (-Tn n : ℝ) * Complex.I)‖ := by
        calc
          _ = ‖Complex.I • ((∫ t : ℝ in (-(Tn n))..(Tn n), F (b + t * Complex.I)) -
                ∫ t : ℝ in (-(Tn n))..(Tn n), F (a + t * Complex.I))‖ := by simp
          _ = ‖(∫ x : ℝ in a..b, F (x + (Tn n : ℝ) * Complex.I)) -
                ∫ x : ℝ in a..b, F (x + (-Tn n : ℝ) * Complex.I)‖ := by rw [hvert]
          _ ≤ _ := norm_sub_le _ _
      have hlen : |b - a| = b - a := abs_of_pos (sub_pos.mpr hab)
      calc
        _ ≤ ‖∫ x : ℝ in a..b, F (x + (Tn n : ℝ) * Complex.I)‖ +
            ‖∫ x : ℝ in a..b, F (x + (-Tn n : ℝ) * Complex.I)‖ := hnormV
        _ ≤ (C / (1 + Tn n) ^ 2) * |b - a| +
            (C / (1 + Tn n) ^ 2) * |b - a| := add_le_add htop hbottom
        _ = 2 * C * (b - a) / (1 + Tn n) ^ 2 := by rw [hlen]; ring
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)) hsmall
      (fun n => norm_nonneg _)
      (fun n => hle n)
  have hzero : Tendsto (fun n : ℕ =>
      (∫ t : ℝ in (-(Tn n))..(Tn n), F ((b : ℂ) + (t : ℂ) * Complex.I)) -
        (∫ t : ℝ in (-(Tn n))..(Tn n), F ((a : ℂ) + (t : ℂ) * Complex.I))) atTop (𝓝 0) := by
    exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have hEq := tendsto_nhds_unique hdiffLimit hzero
  exact (sub_eq_zero.mp hEq).symm

private theorem qs_p1_original_mellin_vertical_shift
    (h : ℝ → ℂ) (hh : IsQSWeight h) (X : ℝ) (hX : 0 < X)
    (Lc : ℂ → ℂ) (hLc : Differentiable ℂ Lc)
    (hbound : ∃ C α : ℝ, 0 ≤ C ∧ 0 ≤ α ∧
      ∀ s : ℂ, 3 / 1000 ≤ s.re → s.re ≤ 4 →
        ‖Lc s‖ ≤ C * (2 + |s.im|) ^ α) :
    ∫ t : ℝ,
      (X : ℂ) ^ ((2 : ℂ) + (t : ℂ) * Complex.I) *
        Lc ((2 : ℂ) + (t : ℂ) * Complex.I) *
        mellin h ((2 : ℂ) + (t : ℂ) * Complex.I) =
    ∫ t : ℝ,
      (X : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) *
        Lc ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) *
        mellin h ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) := by
  classical
  obtain ⟨Cₗ, α, hCₗ, hα, hLbound⟩ := hbound
  letI : NeZero (X : ℂ) := ⟨Complex.ofReal_ne_zero.mpr hX.ne'⟩
  let F : ℂ → ℂ := fun s => (X : ℂ) ^ s * Lc s * mellin h s
  let S : Set ℂ := {s | 1 / 2 ≤ s.re ∧ s.re ≤ 2}
  have hpowCont : Continuous (fun s : ℂ => (X : ℂ) ^ s) := by fun_prop
  have hMellinCont : ContinuousOn (mellin h) S := by
    intro s hs
    change 1 / 2 ≤ s.re ∧ s.re ≤ 2 at hs
    have hspos : 0 < s.re := by linarith
    exact (qs_p1_mellin_differentiableAt h hh hspos).continuousAt.continuousWithinAt
  have hFcont : ContinuousOn F S := by
    change ContinuousOn (fun s : ℂ =>
      ((X : ℂ) ^ s * Lc s) * mellin h s) S
    exact (hpowCont.continuousOn.mul hLc.continuous.continuousOn).mul hMellinCont
  have hFdiff : ∀ s : ℂ, 1 / 2 < s.re → s.re < 2 → DifferentiableAt ℂ F s := by
    intro s hs₁ hs₂
    have hspos : 0 < s.re := by linarith
    change DifferentiableAt ℂ (fun z : ℂ =>
      ((X : ℂ) ^ z * Lc z) * mellin h z) s
    exact ((differentiableAt_id.const_cpow (Or.inl (by exact Complex.ofReal_ne_zero.mpr hX.ne'))).mul
      (hLc s)).mul (qs_p1_mellin_differentiableAt h hh hspos)
  let N : ℕ := ⌈α + 2⌉₊ + 1
  have hαN : α ≤ (N : ℝ) := by
    dsimp [N]
    have hceil : α + 2 ≤ (⌈α + 2⌉₊ : ℝ) := Nat.le_ceil _
    push_cast
    linarith
  obtain ⟨Cₘ, hCₘ, hMellin⟩ :=
    qs_p1_mellin_vertical_polynomial_decay_uniform h hh (1 / 2) 2 (by norm_num) (by norm_num) (N + 2)
  let D : ℝ := max (X ^ (2 : ℝ)) (X ^ ((1 / 2 : ℝ)))
  have hD : 0 ≤ D := by
    dsimp [D]
    exact le_max_of_le_left (Real.rpow_nonneg hX.le _)
  have hXbound : ∀ r ∈ Set.Icc (1 / 2 : ℝ) 2, X ^ r ≤ D := by
    intro r hr
    by_cases hXone : 1 ≤ X
    · exact (Real.rpow_le_rpow_of_exponent_le hXone hr.2).trans (le_max_left _ _)
    · have hXle : X ≤ 1 := le_of_not_ge hXone
      exact (Real.rpow_le_rpow_of_exponent_ge hX hXle hr.1).trans (le_max_right _ _)
  have hdecay : ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 →
      ‖F s‖ ≤ C / (1 + |s.im|) ^ 2 := by
    refine ⟨D * Cₗ * (2 : ℝ) ^ α * Cₘ, by positivity, ?_⟩
    intro s hs₁ hs₂
    let u : ℝ := 1 + |s.im|
    have hu : 0 < u := by dsimp [u]; positivity
    have hu1 : 1 ≤ u := by dsimp [u]; nlinarith [abs_nonneg s.im]
    have hsline : s.re ∈ Set.Icc (1 / 2 : ℝ) 2 := ⟨hs₁, hs₂⟩
    have hM := hMellin s.re hsline s.im
    have hlineEq : (s.re : ℂ) + (s.im : ℂ) * Complex.I = s := by
      apply Complex.ext <;> simp
    rw [hlineEq] at hM
    have hLc := hLbound s (by linarith [hs₁]) (by linarith [hs₂])
    have hheight : (2 + |s.im|) ^ α ≤ (2 : ℝ) ^ α * u ^ N := by
      have hfactor : 2 + |s.im| ≤ 2 * u := by
        dsimp [u]
        nlinarith [abs_nonneg s.im]
      calc
        (2 + |s.im|) ^ α ≤ (2 * u) ^ α :=
          Real.rpow_le_rpow (by positivity) hfactor hα
        _ = (2 : ℝ) ^ α * u ^ α := by
          rw [Real.mul_rpow (by norm_num) (le_of_lt hu)]
        _ ≤ (2 : ℝ) ^ α * u ^ (N : ℝ) := by
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hu1 hαN) (Real.rpow_nonneg (by norm_num) _)
        _ = (2 : ℝ) ^ α * u ^ N := by rw [Real.rpow_natCast]
    have hXnorm : ‖(X : ℂ) ^ s‖ ≤ D := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hX]
      exact hXbound s.re hsline
    have hprod : ‖F s‖ ≤ D * (Cₗ * (2 + |s.im|) ^ α) *
        (Cₘ / u ^ (N + 2)) := by
      dsimp [F]
      calc
        _ = (‖(X : ℂ) ^ s‖ * ‖Lc s‖) * ‖mellin h s‖ := by simp [norm_mul]
        _ ≤ D * (Cₗ * (2 + |s.im|) ^ α) * (Cₘ / u ^ (N + 2)) := by
          exact mul_le_mul (mul_le_mul hXnorm hLc (norm_nonneg _) hD) hM
            (norm_nonneg _) (by positivity)
    have hfinal : D * (Cₗ * (2 + |s.im|) ^ α) *
        (Cₘ / u ^ (N + 2)) ≤ (D * Cₗ * (2 : ℝ) ^ α * Cₘ) / u ^ 2 := by
      have huPow : u ^ (N + 2) = u ^ N * u ^ 2 := by rw [pow_add]
      calc
        _ ≤ D * (Cₗ * ((2 : ℝ) ^ α * u ^ N)) * (Cₘ / u ^ (N + 2)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_left
          · exact mul_le_mul_of_nonneg_left hheight hCₗ
          · exact hD
        _ = D * (Cₗ * ((2 : ℝ) ^ α * u ^ N)) * (Cₘ / (u ^ N * u ^ 2)) := by
          rw [huPow]
        _ = (D * Cₗ * (2 : ℝ) ^ α * Cₘ) / u ^ 2 := by
          field_simp [ne_of_gt hu]
    exact hprod.trans hfinal
  have hshift := qs_p1_vertical_integral_shift F (1 / 2) 2 (by norm_num)
    hFcont hFdiff hdecay
  simpa [F] using hshift.symm


/-- The Mellin transform of a QS weight decays faster than any fixed polynomial on every
positive vertical line. -/
theorem qs_p1_mellin_vertical_polynomial_decay (h : ℝ → ℂ)
    (hh : IsQSWeight h) (c : ℝ) (hc : 0 < c) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖mellin h ((c : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C / (1 + |t|) ^ N := by
  let g : ℝ → ℂ := qsP1MellinLogKernel c h
  have hgCont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g := by
    have hker : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (qsP1MellinLogKernel c h) := by
      have hhs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h := hh.1
      unfold qsP1MellinLogKernel
      fun_prop
    simpa [g] using hker
  have hderiv : ∀ j : ℕ, Integrable (iteratedDeriv j g) := by
    intro j
    simpa [g] using
      qs_p1_iteratedDeriv_logKernel_integrable h hh c hc j
  obtain ⟨C, hC, hFourier⟩ := qs_p1_fourier_polynomial_decay g hgCont hderiv N
  refine ⟨C * (2 * Real.pi) ^ N, mul_nonneg hC (by positivity), ?_⟩
  intro t
  let w : ℝ := t / (2 * Real.pi)
  have ht : t = (2 * Real.pi) * w := by
    dsimp [w]
    field_simp
  have habs : |t| = 2 * Real.pi * |w| := by
    rw [ht, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  have hscale : 1 + |t| ≤ (2 * Real.pi) * (1 + |w|) := by
    rw [habs]
    have hq : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    nlinarith [abs_nonneg w]
  have hscalePow : (1 + |t|) ^ N ≤ (2 * Real.pi) ^ N * (1 + |w|) ^ N := by
    calc
      (1 + |t|) ^ N ≤ ((2 * Real.pi) * (1 + |w|)) ^ N :=
        pow_le_pow_left₀ (by positivity) hscale N
      _ = (2 * Real.pi) ^ N * (1 + |w|) ^ N := by rw [mul_pow]
  have hline : mellin h ((c : ℂ) + (t : ℂ) * Complex.I) =
      𝓕 g w := by
    simpa [g, w] using qs_p1_mellin_eq_fourier_line h c t
  have hdenw : 0 < (1 + |w|) ^ N := pow_pos (by positivity) _
  have hdent : 0 < (1 + |t|) ^ N := pow_pos (by positivity) _
  calc
    ‖mellin h ((c : ℂ) + (t : ℂ) * Complex.I)‖ = ‖𝓕 g w‖ := by rw [hline]
    _ ≤ C / (1 + |w|) ^ N := hFourier w
    _ ≤ C * (2 * Real.pi) ^ N / (1 + |t|) ^ N := by
      apply (div_le_div_iff₀ hdenw hdent).2
      calc
        C * (1 + |t|) ^ N ≤ C * ((2 * Real.pi) ^ N * (1 + |w|) ^ N) :=
          mul_le_mul_of_nonneg_left hscalePow hC
        _ = (C * (2 * Real.pi) ^ N) * (1 + |w|) ^ N := by ring

theorem qs_p1_transform_mellin_vertical_polynomial_decay [IsTotallyComplex K]
    (h : ℝ → ℂ) (hh : IsQSWeight h) (c : ℝ) (hc : 0 < c) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖mellin (qsTransform K h) ((c : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C / (1 + |t|) ^ N := by
  let g : ℝ → ℂ := qsP1LogKernelLine (K := K) c h
  have hgCont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g := by
    apply contDiff_iff_contDiffAt.2
    intro u
    let E : ℝ → ℂ := fun v => ((Real.exp (-c * v) : ℝ) : ℂ)
    let H : ℝ → ℂ := fun v => qsTransform K h (Real.exp (-v))
    have hE : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) E u := by
      dsimp [E]
      have hlin : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun v : ℝ => -c * v) u := by fun_prop
      exact Complex.ofRealCLM.contDiff.comp_contDiffAt u
        (Real.contDiff_exp.contDiffAt.comp u hlin)
    have hTtop : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (qsTransform K h) (Set.Ioi 0) := by
      obtain ⟨hT, _⟩ := qs_transform_bounds_P0 (K := K) h hh 1 0 1 (by norm_num)
      exact hT
    have hT : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (qsTransform K h) (Real.exp (-u)) :=
      hTtop.contDiffAt (isOpen_Ioi.mem_nhds (Real.exp_pos (-u)))
    have hφ : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun v : ℝ => Real.exp (-v)) u := by fun_prop
    have hH : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H u := by
      dsimp [H]
      exact hT.comp u hφ
    change ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (E * H) u
    exact hE.mul hH
  have hderiv : ∀ j : ℕ, Integrable (iteratedDeriv j g) := by
    intro j
    let A : ℕ := ⌈c + (j : ℝ)⌉₊ + 1
    have hAc : c + (j : ℝ) < (A : ℝ) := by
      dsimp [A]
      have hceil : c + (j : ℝ) ≤ (⌈c + (j : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
      push_cast
      linarith
    simpa [g] using
      qs_p1_logKernelLine_iteratedDeriv_integrable_all (K := K) h hh c hc j A hAc
  obtain ⟨C, hC, hFourier⟩ := qs_p1_fourier_polynomial_decay g hgCont hderiv N
  refine ⟨C * (2 * Real.pi) ^ N, mul_nonneg hC (by positivity), ?_⟩
  intro t
  let w : ℝ := t / (2 * Real.pi)
  have ht : t = (2 * Real.pi) * w := by
    dsimp [w]
    field_simp
  have habs : |t| = 2 * Real.pi * |w| := by
    rw [ht, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  have hscale : 1 + |t| ≤ (2 * Real.pi) * (1 + |w|) := by
    rw [habs]
    have hq : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    nlinarith [abs_nonneg w]
  have hscalePow : (1 + |t|) ^ N ≤ (2 * Real.pi) ^ N * (1 + |w|) ^ N := by
    calc
      (1 + |t|) ^ N ≤ ((2 * Real.pi) * (1 + |w|)) ^ N :=
        pow_le_pow_left₀ (by positivity) hscale N
      _ = (2 * Real.pi) ^ N * (1 + |w|) ^ N := by rw [mul_pow]
  have hline : mellin (qsTransform K h) ((c : ℂ) + (t : ℂ) * Complex.I) =
      𝓕 g w := by
    rw [mellin_eq_fourier]
    have hfun : (fun u : ℝ =>
        Real.exp (-((c : ℂ) + (t : ℂ) * Complex.I).re * u) •
          qsTransform K h (Real.exp (-u))) = qsP1LogKernelLine (K := K) c h := by
      funext u
      simp [qsP1LogKernelLine]
    rw [hfun]
    simp [g, w]
  have hdenw : 0 < (1 + |w|) ^ N := pow_pos (by positivity) _
  have hdent : 0 < (1 + |t|) ^ N := pow_pos (by positivity) _
  calc
    ‖mellin (qsTransform K h) ((c : ℂ) + (t : ℂ) * Complex.I)‖ = ‖𝓕 g w‖ := by
      rw [hline]
    _ ≤ C / (1 + |w|) ^ N := hFourier w
    _ ≤ C * (2 * Real.pi) ^ N / (1 + |t|) ^ N := by
      apply (div_le_div_iff₀ hdenw hdent).2
      calc
        C * (1 + |t|) ^ N ≤ C * ((2 * Real.pi) ^ N * (1 + |w|) ^ N) :=
          mul_le_mul_of_nonneg_left hscalePow hC
        _ = (C * (2 * Real.pi) ^ N) * (1 + |w|) ^ N := by ring

private theorem qs_p1_fourier_integrable_of_two_derivatives (g : ℝ → ℂ)
    (hg : Integrable g) (hgDiff : Differentiable ℝ g) (hg₁ : Integrable (deriv g))
    (hgDerivDiff : Differentiable ℝ (deriv g))
    (hg₂ : Integrable (deriv (deriv g))) : Integrable (𝓕 g) := by
  have hFourier0 : 𝓕 (deriv g) = fun w : ℝ =>
      (2 * Real.pi * Complex.I * w) • 𝓕 g w := by
    exact Real.fourier_deriv hg hgDiff hg₁
  have hFourier1 : 𝓕 (deriv (deriv g)) = fun w : ℝ =>
      (2 * Real.pi * Complex.I * w) • 𝓕 (deriv g) w := by
    exact Real.fourier_deriv hg₁ hgDerivDiff hg₂
  let A₀ : ℝ := ∫ u : ℝ, ‖g u‖
  let A₂ : ℝ := ∫ u : ℝ, ‖deriv (deriv g) u‖
  have hA₀ : 0 ≤ A₀ := by
    dsimp [A₀]
    exact integral_nonneg (fun _ => norm_nonneg _)
  have hA₂ : 0 ≤ A₂ := by
    dsimp [A₂]
    exact integral_nonneg (fun _ => norm_nonneg _)
  let C : ℝ := 2 * (A₀ + A₂)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbound : ∀ w : ℝ, ‖𝓕 g w‖ ≤ C * (1 + w ^ 2)⁻¹ := by
    intro w
    rcases le_total |w| 1 with hw | hw
    · have hsmall := qs_p1_fourier_norm_bound g hg w
      have hden : 0 < 1 + w ^ 2 := by positivity
      apply (le_div_iff₀ hden).2
      have hsmall' : ‖𝓕 g w‖ ≤ A₀ := by simpa [A₀] using hsmall
      rcases abs_le.mp hw with ⟨hwl, hwr⟩
      have hw2 : w ^ 2 ≤ 1 := by nlinarith
      dsimp [C]
      nlinarith [hA₀, hA₂, hsmall']
    · have hqnorm :
          ‖(2 * Real.pi * Complex.I * (w : ℂ))‖ = 2 * Real.pi * |w| := by
        have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
        have hpi : ‖(Real.pi : ℂ)‖ = Real.pi := by
          rw [Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
        have hI : ‖Complex.I‖ = 1 := by simp
        have hwR : ‖(w : ℂ)‖ = |w| := by
          rw [Complex.norm_real, Real.norm_eq_abs]
        calc
          _ = ‖(2 : ℂ)‖ * ‖(Real.pi : ℂ)‖ * ‖Complex.I‖ * ‖(w : ℂ)‖ := by
            simp only [norm_mul]
          _ = 2 * Real.pi * |w| := by rw [htwo, hpi, hI, hwR]; ring
      have hfactor : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
      have hqpos : 0 < 2 * Real.pi * |w| := by positivity
      have hqbound : ((2 * Real.pi * |w|) ^ 2) * ‖𝓕 g w‖ ≤ A₂ := by
        have hpoint0 := congrFun hFourier0 w
        have hpoint1 := congrFun hFourier1 w
        have hsecond : 𝓕 (deriv (deriv g)) w =
            (2 * Real.pi * Complex.I * (w : ℂ)) ^ 2 * 𝓕 g w := by
          calc
            _ = (2 * Real.pi * Complex.I * (w : ℂ)) * 𝓕 (deriv g) w := by
              simpa [smul_eq_mul] using hpoint1
            _ = (2 * Real.pi * Complex.I * (w : ℂ)) ^ 2 * 𝓕 g w := by
              rw [show 𝓕 (deriv g) w =
                (2 * Real.pi * Complex.I * (w : ℂ)) * 𝓕 g w by
                  simpa [smul_eq_mul] using hpoint0]
              ring
        calc
          _ = ‖(2 * Real.pi * Complex.I * (w : ℂ)) ^ 2 * 𝓕 g w‖ := by
            rw [norm_mul, norm_pow, hqnorm]
          _ = ‖𝓕 (deriv (deriv g)) w‖ := by rw [← hsecond]
          _ ≤ A₂ := by
            simpa [A₂] using qs_p1_fourier_norm_bound (deriv (deriv g)) hg₂ w
      have hw0 : w ≠ 0 := by
        intro hz
        subst w
        norm_num at hw
      have hdenw : 0 < w ^ 2 := sq_pos_of_ne_zero hw0
      have hqge : |w| ≤ 2 * Real.pi * |w| := by
        have hfact : 0 ≤ 2 * Real.pi - 1 := by linarith
        nlinarith [abs_nonneg w, mul_nonneg hfact (abs_nonneg w)]
      have hwSq : w ^ 2 ≤ (2 * Real.pi * |w|) ^ 2 := by
        nlinarith [sq_abs w, sq_nonneg (2 * Real.pi * |w|)]
      have hlarge : ‖𝓕 g w‖ ≤ A₂ / w ^ 2 := by
        have hprod := mul_le_mul_of_nonneg_right hwSq (norm_nonneg (𝓕 g w))
        have hprod' : w ^ 2 * ‖𝓕 g w‖ ≤ A₂ := hprod.trans hqbound
        exact (le_div_iff₀ hdenw).2 (by nlinarith [hprod'])
      have hden : 0 < 1 + w ^ 2 := by positivity
      have hdenCmp : 1 + w ^ 2 ≤ 2 * w ^ 2 := by
        have hwabs : 1 ≤ w ^ 2 := by
          have habs : 1 ≤ |w| := hw
          nlinarith [sq_abs w]
        nlinarith
      have hlarge' : ‖𝓕 g w‖ * (1 + w ^ 2) ≤ 2 * A₂ := by
        calc
          _ ≤ (A₂ / w ^ 2) * (1 + w ^ 2) :=
            mul_le_mul_of_nonneg_right hlarge (by positivity)
          _ = A₂ * ((1 + w ^ 2) / w ^ 2) := by ring
          _ ≤ A₂ * 2 := by
            have hratio : (1 + w ^ 2) / w ^ 2 ≤ 2 := (div_le_iff₀ hdenw).2 hdenCmp
            exact mul_le_mul_of_nonneg_left hratio hA₂
          _ = 2 * A₂ := by ring
      apply (le_div_iff₀ hden).2
      dsimp [C]
      nlinarith [hA₀, hA₂, hlarge']
  have hFourierCont : Continuous (𝓕 g) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hg
  refine (integrable_inv_one_add_sq.const_mul C).mono' hFourierCont.aestronglyMeasurable ?_
  filter_upwards [] with w
  simpa [div_eq_mul_inv, mul_comm] using hbound w

private theorem qs_p1_transform_mellin_eq_fourier_line [IsTotallyComplex K]
    (h : ℝ → ℂ) (c t : ℝ) :
    mellin (qsTransform K h) ((c : ℂ) + (t : ℂ) * Complex.I) =
      𝓕 (qsP1LogKernelLine (K := K) c h) (t / (2 * Real.pi)) := by
  rw [mellin_eq_fourier]
  have hfun : (fun u : ℝ =>
      Real.exp (-((c : ℂ) + (t : ℂ) * Complex.I).re * u) •
        qsTransform K h (Real.exp (-u))) = qsP1LogKernelLine (K := K) c h := by
    funext u
    simp [qsP1LogKernelLine]
  rw [hfun]
  simp

private theorem qs_p1_transform_mellin_vertical_polynomial_decay_uniform
    [IsTotallyComplex K] (h : ℝ → ℂ) (hh : IsQSWeight h)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c ∈ Set.Icc a b, ∀ t : ℝ,
      ‖mellin (qsTransform K h) ((c : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C / (1 + |t|) ^ N := by
  classical
  let g : ℝ → ℝ → ℂ := fun c => qsP1LogKernelLine (K := K) c h
  have hg (c : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (g c) := by
    have hker : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (qsP1LogKernelLine (K := K) c h) := by
      apply contDiff_iff_contDiffAt.2
      intro u
      let E : ℝ → ℂ := fun v => ((Real.exp (-c * v) : ℝ) : ℂ)
      let H : ℝ → ℂ := fun v => qsTransform K h (Real.exp (-v))
      have hE : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) E u := by
        dsimp [E]
        have hlin : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun v : ℝ => -c * v) u := by fun_prop
        exact Complex.ofRealCLM.contDiff.comp_contDiffAt u
          (Real.contDiff_exp.contDiffAt.comp u hlin)
      have hTtop : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (qsTransform K h) (Set.Ioi 0) := by
        obtain ⟨hT, _⟩ := qs_transform_bounds_P0 (K := K) h hh 1 0 1 (by norm_num)
        exact hT
      have hT : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (qsTransform K h) (Real.exp (-u)) :=
        hTtop.contDiffAt (isOpen_Ioi.mem_nhds (Real.exp_pos (-u)))
      have hφ : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun v : ℝ => Real.exp (-v)) u := by fun_prop
      have hH : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H u := by
        dsimp [H]
        exact hT.comp u hφ
      change ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (E * H) u
      exact hE.mul hH
    simpa [g] using hker
  have hderiv : ∀ c ∈ Set.Icc a b, ∀ n,
      Integrable (iteratedDeriv n (g c)) := by
    intro c hc n
    have hcpos : 0 < c := lt_of_lt_of_le ha hc.1
    let A : ℕ := ⌈c + (n : ℝ)⌉₊ + 1
    have hAc : c + (n : ℝ) < (A : ℝ) := by
      dsimp [A]
      have hceil : c + (n : ℝ) ≤ (⌈c + (n : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
      push_cast
      linarith
    simpa [g] using
      qs_p1_logKernelLine_iteratedDeriv_integrable_all (K := K) h hh c hcpos n A hAc
  have hmajor (n : ℕ) :
      ∃ G : ℝ → ℝ, Integrable G ∧ ∀ c ∈ Set.Icc a b, ∀ u : ℝ,
        ‖iteratedDeriv n (g c) u‖ ≤ G u := by
    let A : ℕ := ⌈b + (n : ℝ)⌉₊ + 1
    have hAc : b + (n : ℝ) < (A : ℝ) := by
      dsimp [A]
      have hceil : b + (n : ℝ) ≤ (⌈b + (n : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
      push_cast
      linarith
    exact qs_p1_logKernelLine_iteratedDeriv_uniform_majorant
      (K := K) h hh a b ha hab n A hAc
  let G₀ : ℝ → ℝ := Classical.choose (hmajor 0)
  let Gₙ : ℝ → ℝ := Classical.choose (hmajor N)
  have hG₀ : Integrable G₀ := (Classical.choose_spec (hmajor 0)).1
  have hGₙ : Integrable Gₙ := (Classical.choose_spec (hmajor N)).1
  have hG₀eq : G₀ = Classical.choose (hmajor 0) := by rfl
  have hGₙeq : Gₙ = Classical.choose (hmajor N) := by rfl
  have hG₀bound (c : ℝ) (hc : c ∈ Set.Icc a b) (u : ℝ) :
      ‖g c u‖ ≤ G₀ u := by
    rw [hG₀eq]
    simpa [g, iteratedDeriv_zero] using (Classical.choose_spec (hmajor 0)).2 c hc u
  have hGₙbound (c : ℝ) (hc : c ∈ Set.Icc a b) (u : ℝ) :
      ‖iteratedDeriv N (g c) u‖ ≤ Gₙ u :=
    by rw [hGₙeq]; exact (Classical.choose_spec (hmajor N)).2 c hc u
  let A₀ : ℝ := ∫ u : ℝ, G₀ u
  let Aₙ : ℝ := ∫ u : ℝ, Gₙ u
  have hA₀ : 0 ≤ A₀ := by
    dsimp [A₀]
    exact integral_nonneg
      (fun u => le_trans (norm_nonneg _) (hG₀bound a ⟨le_rfl, hab⟩ u))
  have hAₙ : 0 ≤ Aₙ := by
    dsimp [Aₙ]
    exact integral_nonneg
      (fun u => le_trans (norm_nonneg _) (hGₙbound a ⟨le_rfl, hab⟩ u))
  have hbound₀ (c : ℝ) (hc : c ∈ Set.Icc a b) :
      ∫ u : ℝ, ‖g c u‖ ≤ A₀ := by
    have hnorm : Integrable (fun u : ℝ => ‖g c u‖) := by
      simpa [iteratedDeriv_zero] using (hderiv c hc 0).norm
    calc
      _ ≤ ∫ u : ℝ, G₀ u := integral_mono_ae hnorm hG₀
        (Filter.Eventually.of_forall fun u => hG₀bound c hc u)
      _ = A₀ := by rfl
  have hboundₙ (c : ℝ) (hc : c ∈ Set.Icc a b) :
      ∫ u : ℝ, ‖iteratedDeriv N (g c) u‖ ≤ Aₙ := by
    calc
      _ ≤ ∫ u : ℝ, Gₙ u := integral_mono_ae (hderiv c hc N).norm hGₙ
        (Filter.Eventually.of_forall fun u => hGₙbound c hc u)
      _ = Aₙ := by rfl
  obtain ⟨C, hC, hFourier⟩ := qs_p1_fourier_polynomial_decay_uniform
    g hg a b hderiv N A₀ Aₙ hA₀ hAₙ hbound₀ hboundₙ
  refine ⟨C * (2 * Real.pi) ^ N, mul_nonneg hC (by positivity), ?_⟩
  intro c hc t
  let w : ℝ := t / (2 * Real.pi)
  have ht : t = (2 * Real.pi) * w := by
    dsimp [w]
    field_simp
  have habs : |t| = 2 * Real.pi * |w| := by
    rw [ht, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  have hscale : 1 + |t| ≤ (2 * Real.pi) * (1 + |w|) := by
    rw [habs]
    have hq : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    nlinarith [abs_nonneg w]
  have hscalePow : (1 + |t|) ^ N ≤ (2 * Real.pi) ^ N * (1 + |w|) ^ N := by
    calc
      (1 + |t|) ^ N ≤ ((2 * Real.pi) * (1 + |w|)) ^ N :=
        pow_le_pow_left₀ (by positivity) hscale N
      _ = (2 * Real.pi) ^ N * (1 + |w|) ^ N := by rw [mul_pow]
  have hline : mellin (qsTransform K h) ((c : ℂ) + (t : ℂ) * Complex.I) =
      𝓕 (g c) w := by
    simpa [g, w] using qs_p1_transform_mellin_eq_fourier_line (K := K) h c t
  have hdenw : 0 < (1 + |w|) ^ N := pow_pos (by positivity) _
  have hdent : 0 < (1 + |t|) ^ N := pow_pos (by positivity) _
  calc
    ‖mellin (qsTransform K h) ((c : ℂ) + (t : ℂ) * Complex.I)‖ = ‖𝓕 (g c) w‖ := by
      rw [hline]
    _ ≤ C / (1 + |w|) ^ N := hFourier c hc w
    _ ≤ C * (2 * Real.pi) ^ N / (1 + |t|) ^ N := by
      apply (div_le_div_iff₀ hdenw hdent).2
      calc
        C * (1 + |t|) ^ N ≤ C * ((2 * Real.pi) ^ N * (1 + |w|) ^ N) :=
          mul_le_mul_of_nonneg_left hscalePow hC
        _ = (C * (2 * Real.pi) ^ N) * (1 + |w|) ^ N := by ring

private theorem qs_p1_transform_mellin_vertical_integrable [IsTotallyComplex K]
    (h : ℝ → ℂ) (hh : IsQSWeight h) (c : ℝ) (hc : 0 < c) :
    Complex.VerticalIntegrable (mellin (qsTransform K h)) c := by
  let A : ℕ := ⌈c + 2⌉₊ + 2
  have hAc : c + 2 < (A : ℝ) := by
    dsimp [A]
    have hceil : c + 2 ≤ (⌈c + 2⌉₊ : ℝ) := Nat.le_ceil _
    push_cast
    linarith
  let g : ℝ → ℂ := qsP1LogKernelLine (K := K) c h
  have hgCont : ContDiff ℝ ((2 : ℕ∞) : WithTop ℕ∞) g := by
    apply contDiff_iff_contDiffAt.2
    intro u
    let E : ℝ → ℂ := fun v => (Real.exp (-c * v) : ℝ)
    let H : ℝ → ℂ := fun v => qsTransform K h (Real.exp (-v))
    have hE : ContDiffAt ℝ 2 E u := by
      change ContDiffAt ℝ 2 (fun v : ℝ => Complex.ofReal (Real.exp (-c * v))) u
      have hlin : ContDiffAt ℝ 2 (fun v : ℝ => -c * v) u := by fun_prop
      exact Complex.ofRealCLM.contDiff.comp_contDiffAt u
        (Real.contDiff_exp.contDiffAt.comp u hlin)
    have hTtop : ContDiffAt ℝ (⊤ : ℕ∞) (qsTransform K h) (Real.exp (-u)) := by
      obtain ⟨hTdiff, _⟩ := qs_transform_bounds_P0 (K := K) h hh 1 0 1 (by norm_num)
      exact hTdiff.contDiffAt (isOpen_Ioi.mem_nhds (Real.exp_pos _))
    have hT : ContDiffAt ℝ 2 (qsTransform K h) (Real.exp (-u)) :=
      hTtop.of_le (by norm_num)
    have hH : ContDiffAt ℝ 2 H u := by
      dsimp [H]
      exact hT.comp u (by fun_prop)
    change ContDiffAt ℝ 2 (E * H) u
    exact hE.mul hH
  have hg : Integrable g := by
    simpa [g, iteratedDeriv_zero] using
    qs_p1_logKernelLine_iteratedDeriv_integrable (K := K) h hh c hc A hAc 0 (by omega)
  have hg₁ : Integrable (deriv g) := by
    simpa [g, iteratedDeriv_one] using
    qs_p1_logKernelLine_iteratedDeriv_integrable (K := K) h hh c hc A hAc 1 (by omega)
  have hg₂ : Integrable (deriv (deriv g)) := by
    simpa [g, iteratedDeriv_succ, iteratedDeriv_one] using
    qs_p1_logKernelLine_iteratedDeriv_integrable (K := K) h hh c hc A hAc 2 (by omega)
  have hgDiff : Differentiable ℝ g := hgCont.differentiable (by simp)
  have hgDerivDiff : Differentiable ℝ (deriv g) := hgCont.differentiable_deriv_two
  have hFourierInt := qs_p1_fourier_integrable_of_two_derivatives g hg hgDiff hg₁
    hgDerivDiff hg₂
  have hScaled : Integrable (fun t : ℝ => 𝓕 g (t / (2 * Real.pi))) := by
    simpa [div_eq_mul_inv] using
      hFourierInt.comp_mul_right' (R := (2 * Real.pi)⁻¹) (by positivity)
  change Integrable (fun t : ℝ => mellin (qsTransform K h) (c + t * Complex.I))
  exact hScaled.congr (Filter.Eventually.of_forall fun t =>
    (qs_p1_transform_mellin_eq_fourier_line (K := K) h c t).symm)

theorem qs_p1_dual_kernel_shift [IsTotallyComplex K]
    (h : ℝ → ℂ) (hh : IsQSWeight h) (δ : ℝ) (hδ : 0 < δ)
    (hconst : ∀ x ∈ Set.Icc (0 : ℝ) δ, h x = h 0)
    (σ : ℝ) (hσ : 0 < σ) (y : ℝ) (hy : 0 < y) :
    mellinInv (1 + σ)
      (fun u : ℂ => qsGammaRatio K u * qsP1Mellin h δ (1 - u)) y =
    qsTransform K h y := by
  let c : ℝ := 1 + σ
  have hc : 0 < c := by dsimp [c]; linarith
  have hconv := qs_p1_transform_mellin_differentiableAt (K := K) h hh
    (s := (c : ℂ)) (by simpa [c] using hc)
  have hvertical := qs_p1_transform_mellin_vertical_integrable (K := K) h hh c hc
  obtain ⟨hTdiff, _⟩ := qs_transform_bounds_P0 (K := K) h hh 1 0 1 (by norm_num)
  have hTcont : ContinuousAt (qsTransform K h) y :=
    (hTdiff.contDiffAt (isOpen_Ioi.mem_nhds hy)).continuousAt
  have hinversion := mellinInv_mellin_eq c (qsTransform K h) hy hconv.1 hvertical hTcont
  have hlineAE : (fun t : ℝ =>
      (y : ℂ) ^ (-(c + (t : ℂ) * Complex.I)) •
        (qsGammaRatio K (c + (t : ℂ) * Complex.I) *
          qsP1Mellin h δ (1 - (c + (t : ℂ) * Complex.I)))) =ᵐ[volume]
      (fun t : ℝ => (y : ℂ) ^ (-(c + (t : ℂ) * Complex.I)) •
        mellin (qsTransform K h) (c + (t : ℂ) * Complex.I)) := by
    filter_upwards [volume.ae_ne (0 : ℝ)] with t ht
    let u : ℂ := (c : ℂ) + (t : ℂ) * Complex.I
    have huRe : 0 < u.re := by
      have hre : u.re = c := by simp [u]
      rw [hre]
      exact hc
    have huNe : u ≠ 1 := by
      intro heq
      have him : u.im = t := by simp [u]
      have hzero : t = 0 := by simpa [heq] using him.symm
      exact ht hzero
    have heq := qs_p1_transform_mellin_eq_regularized (K := K) h hh δ hδ hconst u huRe huNe
    have hintegrand := congrArg (fun z : ℂ => (y : ℂ) ^ (-u) • z) heq.symm
    simpa [u] using hintegrand
  have hInv :
      mellinInv c (fun u : ℂ => qsGammaRatio K u * qsP1Mellin h δ (1 - u)) y =
        mellinInv c (mellin (qsTransform K h)) y := by
    unfold mellinInv
    congr 1
    exact integral_congr_ae hlineAE
  calc
    mellinInv (1 + σ)
        (fun u : ℂ => qsGammaRatio K u * qsP1Mellin h δ (1 - u)) y =
        mellinInv c (fun u : ℂ => qsGammaRatio K u * qsP1Mellin h δ (1 - u)) y := by
      simp [c]
    _ = mellinInv c (mellin (qsTransform K h)) y := hInv
    _ = qsTransform K h y := hinversion

private theorem qs_p1_mellin_vertical_integrable (h : ℝ → ℂ) (hh : IsQSWeight h) :
    Complex.VerticalIntegrable (mellin h) 2 := by
  let g := qsP1LogKernel h
  have hgCont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g := by
    dsimp [g]
    unfold qsP1LogKernel qsP1MellinLogKernel
    have hhs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h := hh.1
    fun_prop
  have hg : Integrable g := by
    change Integrable (qsP1MellinLogKernel 2 h)
    simpa only [iteratedDeriv_zero] using
      qs_p1_iteratedDeriv_logKernel_integrable h hh 2 (by norm_num) 0
  have hg₁ : Integrable (deriv g) := by
    change Integrable (deriv (qsP1MellinLogKernel 2 h))
    simpa only [iteratedDeriv_one] using
      qs_p1_iteratedDeriv_logKernel_integrable h hh 2 (by norm_num) 1
  have hg₂ : Integrable (deriv (deriv g)) := by
    change Integrable (deriv (deriv (qsP1MellinLogKernel 2 h)))
    simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using
      qs_p1_iteratedDeriv_logKernel_integrable h hh 2 (by norm_num) 2
  have hgDiff : Differentiable ℝ g := hgCont.differentiable (by simp)
  have hgDerivDiff : Differentiable ℝ (deriv g) := by
    have hgCont2 : ContDiff ℝ ((2 : ℕ∞) : WithTop ℕ∞) g := hgCont.of_le (by simp)
    exact hgCont2.differentiable_deriv_two
  have hFourier0 : 𝓕 (deriv g) = fun w : ℝ =>
      (2 * Real.pi * Complex.I * w) • 𝓕 g w := by
    exact Real.fourier_deriv hg hgDiff hg₁
  have hFourier1 : 𝓕 (deriv (deriv g)) = fun w : ℝ =>
      (2 * Real.pi * Complex.I * w) • 𝓕 (deriv g) w := by
    exact Real.fourier_deriv hg₁ hgDerivDiff hg₂
  let A₀ : ℝ := ∫ u : ℝ, ‖g u‖
  let A₂ : ℝ := ∫ u : ℝ, ‖deriv (deriv g) u‖
  have hA₀ : 0 ≤ A₀ := by
    dsimp [A₀]
    exact integral_nonneg (fun _ => norm_nonneg _)
  have hA₂ : 0 ≤ A₂ := by
    dsimp [A₂]
    exact integral_nonneg (fun _ => norm_nonneg _)
  let C : ℝ := 2 * (A₀ + A₂)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbound : ∀ w : ℝ, ‖𝓕 g w‖ ≤ C * (1 + w ^ 2)⁻¹ := by
    intro w
    rcases le_total |w| 1 with hw | hw
    · have hsmall := qs_p1_fourier_norm_bound g hg w
      have hden : 0 < 1 + w ^ 2 := by positivity
      apply (le_div_iff₀ hden).2
      have hsmall' : ‖𝓕 g w‖ ≤ A₀ := by simpa [A₀] using hsmall
      rcases abs_le.mp hw with ⟨hwl, hwr⟩
      have hw2 : w ^ 2 ≤ 1 := by nlinarith
      dsimp [C]
      nlinarith [hA₀, hA₂, hsmall']
    · have hqnorm :
          ‖(2 * Real.pi * Complex.I * (w : ℂ))‖ = 2 * Real.pi * |w| := by
        have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
        have hpi : ‖(Real.pi : ℂ)‖ = Real.pi := by
          rw [Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
        have hI : ‖Complex.I‖ = 1 := by simp
        have hwR : ‖(w : ℂ)‖ = |w| := by
          rw [Complex.norm_real, Real.norm_eq_abs]
        calc
          _ = ‖(2 : ℂ)‖ * ‖(Real.pi : ℂ)‖ * ‖Complex.I‖ * ‖(w : ℂ)‖ := by
            simp only [norm_mul]
          _ = 2 * Real.pi * |w| := by rw [htwo, hpi, hI, hwR]; ring
      have hfactor : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
      have hqpos : 0 < 2 * Real.pi * |w| := by positivity
      have hqbound :
          ((2 * Real.pi * |w|) ^ 2) * ‖𝓕 g w‖ ≤ A₂ := by
        have hpoint0 := congrFun hFourier0 w
        have hpoint1 := congrFun hFourier1 w
        have hsecond : 𝓕 (deriv (deriv g)) w =
            (2 * Real.pi * Complex.I * (w : ℂ)) ^ 2 * 𝓕 g w := by
          calc
            _ = (2 * Real.pi * Complex.I * (w : ℂ)) * 𝓕 (deriv g) w := by
              simpa [smul_eq_mul] using hpoint1
            _ = (2 * Real.pi * Complex.I * (w : ℂ)) ^ 2 * 𝓕 g w := by
              rw [show 𝓕 (deriv g) w =
                (2 * Real.pi * Complex.I * (w : ℂ)) * 𝓕 g w by
                  simpa [smul_eq_mul] using hpoint0]
              ring
        calc
          _ = ‖(2 * Real.pi * Complex.I * (w : ℂ)) ^ 2 * 𝓕 g w‖ := by
            rw [norm_mul, norm_pow, hqnorm]
          _ = ‖𝓕 (deriv (deriv g)) w‖ := by rw [← hsecond]
          _ ≤ A₂ := by
            simpa [A₂] using qs_p1_fourier_norm_bound (deriv (deriv g)) hg₂ w
      have hw0 : w ≠ 0 := by
        intro hz
        subst w
        norm_num at hw
      have hdenw : 0 < w ^ 2 := sq_pos_of_ne_zero hw0
      have hqge : |w| ≤ 2 * Real.pi * |w| := by
        have hfact : 0 ≤ 2 * Real.pi - 1 := by linarith
        nlinarith [abs_nonneg w, mul_nonneg hfact (abs_nonneg w)]
      have hwSq : w ^ 2 ≤ (2 * Real.pi * |w|) ^ 2 := by
        nlinarith [sq_abs w, sq_nonneg (2 * Real.pi * |w|)]
      have hlarge : ‖𝓕 g w‖ ≤ A₂ / w ^ 2 := by
        have hprod := mul_le_mul_of_nonneg_right hwSq (norm_nonneg (𝓕 g w))
        have hprod' : w ^ 2 * ‖𝓕 g w‖ ≤ A₂ := hprod.trans hqbound
        exact (le_div_iff₀ hdenw).2 (by nlinarith [hprod'])
      have hden : 0 < 1 + w ^ 2 := by positivity
      have hdenCmp : 1 + w ^ 2 ≤ 2 * w ^ 2 := by
        have hwabs : 1 ≤ w ^ 2 := by
          have habs : 1 ≤ |w| := hw
          nlinarith [sq_abs w]
        nlinarith
      have hlarge' : ‖𝓕 g w‖ * (1 + w ^ 2) ≤ 2 * A₂ := by
        calc
          _ ≤ (A₂ / w ^ 2) * (1 + w ^ 2) :=
            mul_le_mul_of_nonneg_right hlarge (by positivity)
          _ = A₂ * ((1 + w ^ 2) / w ^ 2) := by ring
          _ ≤ A₂ * 2 := by
            have hratio : (1 + w ^ 2) / w ^ 2 ≤ 2 := (div_le_iff₀ hdenw).2 hdenCmp
            exact mul_le_mul_of_nonneg_left hratio hA₂
          _ = 2 * A₂ := by ring
      apply (le_div_iff₀ hden).2
      dsimp [C]
      nlinarith [hA₀, hA₂, hlarge']
  have hFourierCont : Continuous (𝓕 g) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hg
  have hFourierInt : Integrable (𝓕 g) := by
    refine (integrable_inv_one_add_sq.const_mul C).mono' hFourierCont.aestronglyMeasurable ?_
    filter_upwards [] with w
    simpa [div_eq_mul_inv, mul_comm] using hbound w
  have hScaled : Integrable (fun t : ℝ => 𝓕 g (t / (2 * Real.pi))) := by
    simpa [div_eq_mul_inv] using
      hFourierInt.comp_mul_right' (R := (2 * Real.pi)⁻¹) (by positivity)
  change Integrable (fun t : ℝ => mellin h ((2 : ℂ) + (t : ℂ) * Complex.I))
  exact hScaled.congr (Filter.Eventually.of_forall fun t =>
    (qs_p1_mellin_eq_fourier_line h 2 t).symm)

theorem qs_p1_original_mellin_representation [IsTotallyComplex K]
    (χ : ArtinPrimitiveRoots.A1.HeckeChar K) (hsq : χ ^ 2 = 1)
    (h : ℝ → ℂ) (hh : IsQSWeight h) (X : ℝ) (hX : 0 < X) :
    ∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥},
        χ.idealValue a.1 * h ((Ideal.absNorm a.1 : ℝ) / X) =
      mellinInv 2 (fun s : ℂ => (X : ℂ) ^ s * heckeLSeries χ s * mellin h s) 1 := by
  classical
  let y : {I : Ideal (𝓞 K) // I ≠ ⊥} → ℝ :=
    fun a => (Ideal.absNorm a.1 : ℝ) / X
  let sline : ℝ → ℂ := fun t => (2 : ℂ) + (t : ℂ) * Complex.I
  let F : {I : Ideal (𝓞 K) // I ≠ ⊥} → ℝ → ℂ := fun a t =>
    χ.idealValue a.1 * ((y a : ℂ) ^ (-sline t) * mellin h (sline t))
  have hy (a : {I : Ideal (𝓞 K) // I ≠ ⊥}) : 0 < y a := by
    dsimp [y]
    apply div_pos
    · apply Nat.cast_pos.mpr
      have hn0 : Ideal.absNorm a.1 ≠ 0 := by
        intro hn
        exact a.2 (Ideal.absNorm_eq_zero_iff.mp hn)
      exact Nat.pos_iff_ne_zero.mpr hn0
    · exact hX
  have hchar (a : {I : Ideal (𝓞 K) // I ≠ ⊥}) : ‖χ.idealValue a.1‖ ≤ 1 :=
    qs_p1_idealValue_norm_le_one χ hsq a.1
  have hM : Integrable (fun t : ℝ => mellin h (sline t)) := by
    have hMv : Complex.VerticalIntegrable (mellin h) 2 :=
      qs_p1_mellin_vertical_integrable h hh
    change Integrable (fun t : ℝ => mellin h (sline t))
    exact hMv
  let J : ℝ := ∫ t : ℝ, ‖mellin h (sline t)‖
  have hJ : 0 ≤ J := by
    dsimp [J]
    exact integral_nonneg (fun _ => norm_nonneg _)
  have hJint : Integrable (fun t : ℝ => ‖mellin h (sline t)‖) := hM.norm
  have hcoeff : Summable (fun a : {I : Ideal (𝓞 K) // I ≠ ⊥} =>
      ‖χ.idealValue a.1‖ * (y a) ^ (-2 : ℝ)) := by
    have hnormsum : Summable (fun I : Ideal (𝓞 K) =>
        ArtinPrimitiveRoots.Hecke.idealNormRpowTerm (K := K) 2 I) :=
      ArtinPrimitiveRoots.Hecke.summable_idealNormRpow (K := K) (by norm_num)
    have hbase : Summable (fun a : {I : Ideal (𝓞 K) // I ≠ ⊥} =>
        X ^ (2 : ℝ) * ArtinPrimitiveRoots.Hecke.idealNormRpowTerm (K := K) 2 a.1) :=
      (hnormsum.subtype (fun I : Ideal (𝓞 K) => I ≠ ⊥)).mul_left (X ^ (2 : ℝ))
    apply Summable.of_nonneg_of_le (fun _ => by positivity) (fun a => ?_) hbase
    have hn0 : Ideal.absNorm a.1 ≠ 0 := by
      intro hn
      exact a.2 (Ideal.absNorm_eq_zero_iff.mp hn)
    have hn : 0 < (Ideal.absNorm a.1 : ℝ) :=
      Nat.cast_pos.mpr (Nat.pos_iff_ne_zero.mpr hn0)
    have hscale : (y a) ^ (-2 : ℝ) = X ^ (2 : ℝ) *
        (Ideal.absNorm a.1 : ℝ) ^ (-2 : ℝ) := by
      dsimp [y]
      calc
        ((Ideal.absNorm a.1 : ℝ) / X) ^ (-2 : ℝ) =
            (Ideal.absNorm a.1 : ℝ) ^ (-2 : ℝ) / X ^ (-2 : ℝ) :=
              Real.div_rpow (Nat.cast_nonneg _) hX.le _
        _ = ((Ideal.absNorm a.1 : ℝ) ^ (2 : ℝ))⁻¹ /
              (X ^ (2 : ℝ))⁻¹ := by
                rw [Real.rpow_neg hn.le 2, Real.rpow_neg hX.le 2]
        _ = X ^ (2 : ℝ) * ((Ideal.absNorm a.1 : ℝ) ^ (2 : ℝ))⁻¹ := by
              rw [div_eq_mul_inv, inv_inv]
              exact mul_comm (((Ideal.absNorm a.1 : ℝ) ^ (2 : ℝ))⁻¹)
                (X ^ (2 : ℝ))
        _ = X ^ (2 : ℝ) * (Ideal.absNorm a.1 : ℝ) ^ (-2 : ℝ) := by
              rw [← Real.rpow_neg hn.le 2]
    have hterm : ArtinPrimitiveRoots.Hecke.idealNormRpowTerm (K := K) 2 a.1 =
        (Ideal.absNorm a.1 : ℝ) ^ (-2 : ℝ) := by
      simp [ArtinPrimitiveRoots.Hecke.idealNormRpowTerm, hn0]
    calc
      ‖χ.idealValue a.1‖ * (y a) ^ (-2 : ℝ) =
          ‖χ.idealValue a.1‖ * (X ^ (2 : ℝ) *
            (Ideal.absNorm a.1 : ℝ) ^ (-2 : ℝ)) := by rw [hscale]
      _ ≤ 1 * (X ^ (2 : ℝ) * (Ideal.absNorm a.1 : ℝ) ^ (-2 : ℝ)) := by
        exact mul_le_mul_of_nonneg_right (hchar a) (by positivity)
      _ = X ^ (2 : ℝ) * ArtinPrimitiveRoots.Hecke.idealNormRpowTerm (K := K) 2 a.1 := by
        rw [hterm]
        ring
  have hphaseNorm (a : {I : Ideal (𝓞 K) // I ≠ ⊥}) (t : ℝ) :
      ‖(y a : ℂ) ^ (-sline t)‖ = (y a) ^ (-2 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (hy a)]
    simp [sline]
  have hFint (a : {I : Ideal (𝓞 K) // I ≠ ⊥}) : Integrable (F a) := by
    letI : NeZero (y a : ℂ) := ⟨Complex.ofReal_ne_zero.mpr (hy a).ne'⟩
    have hphaseCont : Continuous (fun t : ℝ => (y a : ℂ) ^ (-sline t)) := by
      exact (continuous_const_cpow (y a : ℂ)).comp (by fun_prop)
    have hprod : Integrable (fun t : ℝ =>
      ((y a : ℂ) ^ (-sline t)) * mellin h (sline t)) :=
      hM.bdd_mul hphaseCont.aestronglyMeasurable
        (Filter.Eventually.of_forall fun t => by rw [hphaseNorm])
    simpa [F] using hprod.const_mul (χ.idealValue a.1)
  have hFnorm (a : {I : Ideal (𝓞 K) // I ≠ ⊥}) (t : ℝ) :
      ‖F a t‖ = (‖χ.idealValue a.1‖ * (y a) ^ (-2 : ℝ)) *
        ‖mellin h (sline t)‖ := by
    simp only [F, norm_mul, hphaseNorm]
    ring
  have hFsum : Summable (fun a : {I : Ideal (𝓞 K) // I ≠ ⊥} =>
      ∫ t : ℝ, ‖F a t‖) := by
    have hmajor := hcoeff.mul_left J
    refine hmajor.congr ?_
    intro a
    calc
      J * (‖χ.idealValue a.1‖ * (y a) ^ (-2 : ℝ)) =
          (‖χ.idealValue a.1‖ * (y a) ^ (-2 : ℝ)) * J := by ring
      _ =
          ∫ t : ℝ, (‖χ.idealValue a.1‖ * (y a) ^ (-2 : ℝ)) *
            ‖mellin h (sline t)‖ := by
              rw [integral_const_mul]
      _ = ∫ t : ℝ, ‖F a t‖ := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall fun t => (hFnorm a t).symm
  haveI : Countable {I : Ideal (𝓞 K) // I ≠ ⊥} := by
    let F₀ : ℕ → Type := fun n =>
      {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ n}
    haveI : ∀ n, Finite (F₀ n) := by
      intro n
      apply (Ideal.finite_setOfPred_absNorm_le n).subset
      intro I hI
      exact hI.2
    let f : (Σ n : ℕ, F₀ n) → {I : Ideal (𝓞 K) // I ≠ ⊥} := fun p =>
      ⟨p.2.1, p.2.2.1⟩
    have hsurj : Function.Surjective f := by
      intro a
      exact ⟨⟨Ideal.absNorm a.1, ⟨a.1, a.2, le_rfl⟩⟩, rfl⟩
    have hrange : Set.range f = Set.univ := Set.range_eq_univ.mpr hsurj
    rw [← Set.countable_univ_iff]
    rw [← hrange]
    exact Set.countable_range f
  have hsumInt := integral_tsum_of_summable_integral_norm hFint hFsum
  have hpoint (t : ℝ) :
      ∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥}, F a t =
        (X : ℂ) ^ (sline t) * heckeLSeries χ (sline t) * mellin h (sline t) := by
    have hpow (a : {I : Ideal (𝓞 K) // I ≠ ⊥}) :
        ((y a : ℝ) : ℂ) ^ (-sline t) =
          (X : ℂ) ^ (sline t) *
            ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-sline t) := by
      dsimp [y]
      have hn0 : Ideal.absNorm a.1 ≠ 0 := by
        intro hn
        exact a.2 (Ideal.absNorm_eq_zero_iff.mp hn)
      have hn : 0 < (Ideal.absNorm a.1 : ℝ) :=
        Nat.cast_pos.mpr (Nat.pos_iff_ne_zero.mpr hn0)
      rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg hn.le hX.le]
      calc
        ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-sline t) / (X : ℂ) ^ (-sline t) =
            ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-sline t) *
              ((X : ℂ) ^ (-sline t))⁻¹ := by rw [div_eq_mul_inv]
        _ = ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-sline t) * (X : ℂ) ^ (sline t) := by
              congr 1
              simp [Complex.cpow_neg]
        _ = (X : ℂ) ^ (sline t) *
              ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-sline t) := by ring
    calc
      ∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥}, F a t =
          ∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥},
            (X : ℂ) ^ (sline t) * ((χ.idealValue a.1 *
              ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-sline t)) * mellin h (sline t)) := by
                apply tsum_congr
                intro a
                simp [F, hpow, mul_assoc, mul_left_comm, mul_comm]
      _ = (X : ℂ) ^ (sline t) *
            (∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥},
              (χ.idealValue a.1 * ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-sline t)) *
                mellin h (sline t)) := by rw [tsum_mul_left]
      _ = (X : ℂ) ^ (sline t) *
            ((∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥},
              χ.idealValue a.1 * ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-sline t)) *
                mellin h (sline t)) := by rw [tsum_mul_right]
      _ = (X : ℂ) ^ (sline t) * heckeLSeries χ (sline t) * mellin h (sline t) := by
            rw [heckeLSeries]
            exact (mul_assoc ((X : ℂ) ^ (sline t))
              (∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥},
                χ.idealValue a.1 * ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-sline t))
              (mellin h (sline t))).symm
  have hterm (a : {I : Ideal (𝓞 K) // I ≠ ⊥}) :
      χ.idealValue a.1 * h (y a) =
        ((1 / (2 * Real.pi) : ℝ) : ℂ) • ∫ t : ℝ, F a t := by
    have hInv := mellinInv_mellin_eq 2 h (hy a)
      (qs_p1_mellin_convergent h hh (2 : ℂ) (by norm_num))
      (qs_p1_mellin_vertical_integrable h hh) (hh.1.continuous.continuousAt)
    rw [← hInv]
    simp only [mellinInv, RCLike.real_smul_eq_coe_mul (K := ℂ), smul_eq_mul]
    calc
      χ.idealValue a.1 *
          (((1 / (2 * Real.pi) : ℝ) : ℂ) *
            ∫ t : ℝ, (y a : ℂ) ^ (-(2 + (t : ℂ) * Complex.I)) *
              mellin h (2 + (t : ℂ) * Complex.I)) =
          ((1 / (2 * Real.pi) : ℝ) : ℂ) *
            (χ.idealValue a.1 *
              ∫ t : ℝ, (y a : ℂ) ^ (-(2 + (t : ℂ) * Complex.I)) *
                mellin h (2 + (t : ℂ) * Complex.I)) := by ring
      _ = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
            ∫ t : ℝ, χ.idealValue a.1 *
              ((y a : ℂ) ^ (-(2 + (t : ℂ) * Complex.I)) *
                mellin h (2 + (t : ℂ) * Complex.I)) := by
              rw [← integral_const_mul]
      _ = ((1 / (2 * Real.pi) : ℝ) : ℂ) • ∫ t : ℝ, F a t := by
            change ((1 / (2 * Real.pi) : ℝ) : ℂ) *
              ∫ t : ℝ, χ.idealValue a.1 *
                ((y a : ℂ) ^ (-(2 + (t : ℂ) * Complex.I)) *
                  mellin h (2 + (t : ℂ) * Complex.I)) =
              ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, F a t
            apply congrArg (fun z : ℂ => ((1 / (2 * Real.pi) : ℝ) : ℂ) * z)
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun t => by simp [F, sline, smul_eq_mul]
  calc
    (∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥}, χ.idealValue a.1 * h (y a)) =
        ∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥},
          ((1 / (2 * Real.pi) : ℝ) : ℂ) • ∫ t : ℝ, F a t := by
            apply tsum_congr
            exact hterm
    _ = ((1 / (2 * Real.pi) : ℝ) : ℂ) •
          (∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥}, ∫ t : ℝ, F a t) := by
            exact tsum_const_smul'' ((1 / (2 * Real.pi) : ℝ) : ℂ)
    _ = ((1 / (2 * Real.pi) : ℝ) : ℂ) •
          ∫ t : ℝ, ∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥}, F a t := by
            rw [hsumInt]
    _ = mellinInv 2 (fun s : ℂ => (X : ℂ) ^ s * heckeLSeries χ s * mellin h s) 1 := by
          simp [mellinInv, hpoint, sline, smul_eq_mul]

/-- Mellin inversion for a smooth QS weight on a positive input, on the line `Re s = 2`. -/
theorem qs_p1_mellin_inversion (h : ℝ → ℂ) (hh : IsQSWeight h) (x : ℝ) (hx : 0 < x) :
    mellinInv 2 (mellin h) x = h x := by
  exact mellinInv_mellin_eq 2 h hx
    (qs_p1_mellin_convergent h hh (2 : ℂ) (by norm_num))
    (qs_p1_mellin_vertical_integrable h hh) (hh.1.continuous.continuousAt)

end ArtinPrimitiveRoots.A2

end
