import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-POISSON».P0
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-MATRIX».M1
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# P1 analytic helpers

The initial helper proves absolute convergence of the transformed ideal series. The contour and
Mellin continuation arguments are added below as they are established.
-/

set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain MeasureTheory
open Asymptotics
open Filter Topology
open scoped FourierTransform

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
    (A B : ℝ) (hAB : A ≤ B)
    (hleft : ∀ x, x < A → f x = 0)
    (hright : ∃ c : ℂ, ∀ x, B < x → f x = c * ((Real.exp (-2 * x) : ℝ) : ℂ)) :
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
  have hexpI : IntegrableOn (fun x : ℝ => Real.exp (-2 * x)) (Set.Ioi B) :=
    integrableOn_exp_mul_Ioi (by norm_num) B
  have hrightI : IntegrableOn f (Set.Ioi B) := by
    have hbase : IntegrableOn (fun x : ℝ => c * ((Real.exp (-2 * x) : ℝ) : ℂ))
        (Set.Ioi B) := by
      have hsmul : IntegrableOn (fun x : ℝ => (Real.exp (-2 * x)) • c) (Set.Ioi B) :=
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

private def qsP1LogKernel (h : ℝ → ℂ) (u : ℝ) : ℂ :=
  (Real.exp (-2 * u) : ℝ) • h (Real.exp (-u))

private theorem qs_p1_iteratedDeriv_logKernel_integrable
    (h : ℝ → ℂ) (hh : IsQSWeight h) (j : ℕ) (hj : j ≤ 2) :
    Integrable (fun u : ℝ => iteratedDeriv j (qsP1LogKernel h) u) := by
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
  have hker : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (qsP1LogKernel h) := by
    have hhs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h := hh.1
    unfold qsP1LogKernel
    fun_prop
  have hdercont : Continuous (fun u : ℝ => iteratedDeriv j (qsP1LogKernel h) u) :=
    hker.continuous_iteratedDeriv j (by simp)
  have hleft : ∀ u : ℝ, u < A → iteratedDeriv j (qsP1LogKernel h) u = 0 := by
    intro u hu
    have hloc : qsP1LogKernel h =ᶠ[𝓝 u] (fun _ : ℝ => (0 : ℂ)) := by
      filter_upwards [IsOpen.mem_nhds isOpen_Iio hu] with v hv
      change v < A at hv
      have hlog : Real.log B₀ < -v := by
        have := neg_lt_neg hv
        simpa [A] using this
      have hnorm : B₀ < Real.exp (-v) := by
        have he := Real.exp_lt_exp.mpr hlog
        simpa [Real.exp_log hB₀] using he
      have hzero := hB (Real.exp (-v)) (le_trans (le_max_left _ _) hnorm.le)
      simp [qsP1LogKernel, hzero]
    rw [hloc.iteratedDeriv_eq j]
    simp [iteratedDeriv_const]
  have hright : ∃ c : ℂ, ∀ u : ℝ, C < u →
      iteratedDeriv j (qsP1LogKernel h) u = c * ((Real.exp (-2 * u) : ℝ) : ℂ) := by
    let c : ℂ := ((((-2 : ℝ) ^ j) : ℝ) : ℂ) * h 0
    refine ⟨c, ?_⟩
    intro u hu
    have hloc : qsP1LogKernel h =ᶠ[𝓝 u]
        (fun v : ℝ => (Real.exp (-2 * v) : ℝ) • h 0) := by
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
      simpa [qsP1LogKernel, hval]
    have hEq := hloc.iteratedDeriv_eq j
    have hexp : iteratedDeriv j (fun v : ℝ => Real.exp (-2 * v)) u =
        (-2 : ℝ) ^ j * Real.exp (-2 * u) := by
      simpa using congrFun (iteratedDeriv_exp_const_mul j (-2 : ℝ)) u
    rw [hEq]
    have hExpCont : ContDiffAt ℝ (j : ℕ∞) (fun v : ℝ => Real.exp (-2 * v)) u := by
      fun_prop
    rw [iteratedDeriv_smul_const hExpCont (h 0), hexp]
    dsimp [c]
    simp only [smul_eq_mul, Complex.ofReal_mul]
    ring
  exact qs_p1_integrable_of_tails hdercont A C hAC hleft hright

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

private theorem qs_p1_mellin_eq_fourier_line (h : ℝ → ℂ) (t : ℝ) :
    mellin h ((2 : ℂ) + (t : ℂ) * Complex.I) =
      𝓕 (qsP1LogKernel h) (t / (2 * Real.pi)) := by
  rw [mellin_eq_fourier]
  have hfun : (fun u : ℝ =>
      Real.exp (-(2 + (t : ℂ) * Complex.I).re * u) • h (Real.exp (-u))) =
        qsP1LogKernel h := by
    funext u
    simp [qsP1LogKernel]
  rw [hfun]
  simp

private theorem qs_p1_fourier_norm_bound (f : ℝ → ℂ) (hf : Integrable f) (w : ℝ) :
    ‖𝓕 f w‖ ≤ ∫ u : ℝ, ‖f u‖ := by
  exact VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 volume (innerₗ ℝ) f w

private theorem qs_p1_mellin_vertical_integrable (h : ℝ → ℂ) (hh : IsQSWeight h) :
    Complex.VerticalIntegrable (mellin h) 2 := by
  let g := qsP1LogKernel h
  have hgCont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g := by
    dsimp [g]
    unfold qsP1LogKernel
    have hhs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h := hh.1
    fun_prop
  have hg : Integrable g := by
    simpa [g] using qs_p1_iteratedDeriv_logKernel_integrable h hh 0 (by omega)
  have hg₁ : Integrable (deriv g) := by
    simpa [g, iteratedDeriv_one] using qs_p1_iteratedDeriv_logKernel_integrable h hh 1 (by omega)
  have hg₂ : Integrable (deriv (deriv g)) := by
    simpa [g, iteratedDeriv_succ, iteratedDeriv_one] using
      qs_p1_iteratedDeriv_logKernel_integrable h hh 2 (by omega)
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
    (qs_p1_mellin_eq_fourier_line h t).symm)

/-- Mellin inversion for a smooth QS weight on a positive input, on the line `Re s = 2`. -/
theorem qs_p1_mellin_inversion (h : ℝ → ℂ) (hh : IsQSWeight h) (x : ℝ) (hx : 0 < x) :
    mellinInv 2 (mellin h) x = h x := by
  exact mellinInv_mellin_eq 2 h hx
    (qs_p1_mellin_convergent h hh (2 : ℂ) (by norm_num))
    (qs_p1_mellin_vertical_integrable h hh) (hh.1.continuous.continuousAt)

end ArtinPrimitiveRoots.A2

end
