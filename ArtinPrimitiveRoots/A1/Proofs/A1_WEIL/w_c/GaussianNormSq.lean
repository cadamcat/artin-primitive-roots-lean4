import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.w_c.FiniteOrthogonality
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.IndexValue

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory
open scoped ENNReal
open scoped ComplexConjugate

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol_w_c

open ArtinPrimitiveRoots.A1
open ArtinPrimitiveRoots.Proofs.a1_weil_sol

variable {F : Type} [Field F] [NumberField F]

local instance measurableGaussianNormSq (v : FinPlace F) : MeasurableSpace (v.adicCompletion F) := borel _
local instance borelGaussianNormSq (v : FinPlace F) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

def quadraticBallAnnihilator (A : AddCharData F) (v : FinPlace F) (N : ℕ)
    (a : (v.adicCompletion F)ˣ) : Set (v.adicCompletion F) :=
  localBall v N ∩ ⋂ x : {x : v.adicCompletion F // x ∈ localBall v N},
    {t | A.ψ v (-2 * (a : v.adicCompletion F) * x.1 * t) = 1}

theorem setIntegral_add_left_eq_self_localBall
    (v : FinPlace F) (N : ℕ) (μ : Measure (v.adicCompletion F))
    (hμ : Measure.IsAddHaarMeasure μ) (b : v.adicCompletion F)
    (hb : b ∈ localBall v N) (f : v.adicCompletion F → ℂ) :
    (∫ x in localBall v N, f (b + x) ∂μ) =
      ∫ x in localBall v N, f x ∂μ := by
  classical
  letI : Measure.IsAddHaarMeasure μ := hμ
  have hB := localBall_measurableSet v N
  have hmem (x : v.adicCompletion F) :
      (b + x ∈ localBall v N) ↔ x ∈ localBall v N := by
    constructor
    · intro hx
      have hneg := localBall_neg_mem v N hb
      have hsum := localBall_add_mem v N hx hneg
      have heq : (b + x) + -b = x := by abel
      simpa only [heq] using hsum
    · exact fun hx => localBall_add_mem v N hb hx
  let g : v.adicCompletion F → ℂ := (localBall v N).indicator f
  have hpoint (x : v.adicCompletion F) :
      (localBall v N).indicator (fun y => f (b + y)) x = g (b + x) := by
    simp [g, Set.indicator, hmem x]
  calc
    (∫ x in localBall v N, f (b + x) ∂μ) =
        ∫ x, (localBall v N).indicator (fun y => f (b + y)) x ∂μ :=
      (integral_indicator hB).symm
    _ = ∫ x, g (b + x) ∂μ := by
      exact integral_congr_ae (ae_of_all μ hpoint)
    _ = ∫ x, g x ∂μ := integral_add_left_eq_self g b
    _ = ∫ x in localBall v N, f x ∂μ := integral_indicator hB

/-- The square norm of a truncated quadratic integral is the product of the ball volume
and the volume of the bilinear-character annihilator. -/
theorem quadraticBall_normSq_of_annihilator_condition
    (A : AddCharData F) (v : FinPlace F) (μ : Measure (v.adicCompletion F))
    (hμ : Measure.IsAddHaarMeasure μ) (hψ : LocalCharacterRegular A v)
    (a : (v.adicCompletion F)ˣ) (N : ℕ)
    (hquad : ∀ t ∈ quadraticBallAnnihilator A v N a,
      A.ψ v ((a : v.adicCompletion F) * t ^ 2) = 1) :
    Complex.normSq (quadraticIntegral A v μ a N) =
      μ.real (localBall v N) * μ.real (quadraticBallAnnihilator A v N a) := by
  classical
  letI : Measure.IsAddHaarMeasure μ := hμ
  let B := localBall v N
  let D := quadraticBallAnnihilator A v N a
  let μB := μ.restrict B
  have hBcompact : IsCompact B := by dsimp [B]; exact localBall_isCompact v N
  have hBmeas : MeasurableSet B := by dsimp [B]; exact localBall_measurableSet v N
  have hBfinite : μ B ≠ ∞ := hBcompact.measure_ne_top
  letI : IsFiniteMeasure μB := isFiniteMeasure_restrict.mpr hBfinite
  have hDclosed : IsClosed D := by
    dsimp [D, quadraticBallAnnihilator, B]
    apply IsClosed.inter
    · rw [localBall_eq_closedBall]
      exact Metric.isClosed_closedBall
    · apply isClosed_iInter
      intro x
      apply isClosed_eq
      · exact hψ.1.comp (by fun_prop)
      · exact continuous_const
  have hDmeas : MeasurableSet D := hDclosed.measurableSet
  have hDcompact : IsCompact D := hBcompact.of_isClosed_subset hDclosed (by
    intro t ht
    exact ht.1)
  have hDsub : D ⊆ B := by
    intro t ht
    exact ht.1
  have hmassB : μB.real Set.univ = μ.real B := by
    change (μ.restrict B Set.univ).toReal = (μ B).toReal
    rw [Measure.restrict_apply_univ]
  have hmassD : μB.real D = μ.real D := by
    change (μ.restrict B D).toReal = (μ D).toReal
    rw [Measure.restrict_apply hDmeas, Set.inter_eq_left.mpr hDsub]
  let q : v.adicCompletion F → ℂ := fun x =>
    A.ψ v ((a : v.adicCompletion F) * x ^ 2)
  have hqcont : Continuous q := by
    dsimp [q]
    exact hψ.1.comp (by fun_prop)
  have hqint : Integrable q μB := by
    refine (integrable_const (1 : ℝ)).mono' hqcont.aestronglyMeasurable ?_
    filter_upwards with x
    simp [q, hψ.2.2]
  have hqconjcont : Continuous (fun x => conj (q x)) := by fun_prop
  have hqconj : Integrable (fun x => conj (q x)) μB := by
    refine (integrable_const (1 : ℝ)).mono' hqconjcont.aestronglyMeasurable ?_
    filter_upwards with x
    simp [q, hψ.2.2]
  have hprodint : Integrable (fun z : v.adicCompletion F × v.adicCompletion F =>
      q z.1 * conj (q z.2)) (μB.prod μB) := hqint.mul_prod hqconj
  let I : ℂ := ∫ x, q x ∂μB
  have hI : I = quadraticIntegral A v μ a N := by
    rfl
  have hprod : (∫ z, q z.1 * conj (q z.2) ∂μB.prod μB) =
      I * conj I := by
    calc
      (∫ z, q z.1 * conj (q z.2) ∂μB.prod μB) =
          (∫ x, q x ∂μB) * ∫ x, conj (q x) ∂μB := integral_prod_mul q (fun x => conj (q x))
      _ = I * conj I := by simp [I, integral_conj]
  have hdouble : I * conj I =
      ∫ x, ∫ y, q x * conj (q y) ∂μB ∂μB := by
    calc
      I * conj I = ∫ z, q z.1 * conj (q z.2) ∂μB.prod μB := hprod.symm
      _ = ∫ x, ∫ y, q x * conj (q y) ∂μB ∂μB := integral_prod _ hprodint
  have hshifted :
      (∫ x, ∫ y, q x * conj (q y) ∂μB ∂μB) =
        ∫ x, ∫ t, q x * conj (q (x + t)) ∂μB ∂μB := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hBmeas] with x hx
    change (∫ y in B, q x * conj (q y) ∂μ) =
      ∫ t in B, q x * conj (q (x + t)) ∂μ
    exact (setIntegral_add_left_eq_self_localBall v N μ hμ x hx
      (fun y => q x * conj (q y))).symm
  let G : v.adicCompletion F × v.adicCompletion F → ℂ :=
    fun z => q z.1 * conj (q (z.1 + z.2))
  have hGcont : Continuous G := by
    dsimp [G]
    fun_prop
  have hGint : Integrable G (μB.prod μB) := by
    refine (integrable_const (1 : ℝ)).mono' hGcont.aestronglyMeasurable ?_
    filter_upwards with z
    simp [G, q, hψ.2.2]
  have hswap :
      (∫ x, ∫ t, q x * conj (q (x + t)) ∂μB ∂μB) =
        ∫ t, ∫ x, G (x, t) ∂μB ∂μB := by
    calc
      (∫ x, ∫ t, q x * conj (q (x + t)) ∂μB ∂μB) =
          ∫ z, G z ∂μB.prod μB := (integral_prod _ hGint).symm
      _ = ∫ t, ∫ x, G (x, t) ∂μB ∂μB := integral_prod_symm G hGint
  have hcharStar (z : v.adicCompletion F) :
      conj (A.ψ v z) = A.ψ v (-z) := by
    have hmul : A.ψ v z * A.ψ v (-z) = 1 := by
      simpa using ((A.ψ v).map_add_eq_mul z (-z)).symm
    calc
      conj (A.ψ v z) = (A.ψ v z)⁻¹ := (Complex.inv_eq_conj (hψ.2.2 z)).symm
      _ = A.ψ v (-z) := (eq_inv_of_mul_eq_one_right hmul).symm
  have hGpoint (x t : v.adicCompletion F) :
      G (x, t) = A.ψ v (-((a : v.adicCompletion F) * t ^ 2)) *
        A.ψ v (-2 * (a : v.adicCompletion F) * x * t) := by
    dsimp [G, q]
    rw [hcharStar]
    calc
      A.ψ v ((a : v.adicCompletion F) * x ^ 2) *
          A.ψ v (-((a : v.adicCompletion F) * (x + t) ^ 2)) =
        A.ψ v ((a : v.adicCompletion F) * x ^ 2 -
          (a : v.adicCompletion F) * (x + t) ^ 2) := by
            rw [← (A.ψ v).map_add_eq_mul]
            congr 1
            ring
      _ = A.ψ v (-((a : v.adicCompletion F) * t ^ 2) -
          2 * (a : v.adicCompletion F) * x * t) := by congr 1 <;> ring
      _ = A.ψ v (-((a : v.adicCompletion F) * t ^ 2)) *
          A.ψ v (-2 * (a : v.adicCompletion F) * x * t) :=
        by
          have hsum : -((a : v.adicCompletion F) * t ^ 2) -
              2 * (a : v.adicCompletion F) * x * t =
              -((a : v.adicCompletion F) * t ^ 2) +
                (-2 * (a : v.adicCompletion F) * x * t) := by ring
          rw [hsum]
          exact (A.ψ v).map_add_eq_mul _ _
  have hinner (t : v.adicCompletion F) (ht : t ∈ B) :
      (∫ x, G (x, t) ∂μB) =
        if t ∈ D then (μB.real Set.univ : ℂ) else 0 := by
    have hkernel (x : v.adicCompletion F) :
      G (x, t) = A.ψ v (-((a : v.adicCompletion F) * t ^ 2)) *
          A.ψ v ((-2 * (a : v.adicCompletion F) * t) * x) := by
      rw [hGpoint]
      rw [show -2 * (a : v.adicCompletion F) * x * t =
          (-2 * (a : v.adicCompletion F) * t) * x by ring]
    have hkernelInt :
        (∫ x, G (x, t) ∂μB) =
      A.ψ v (-((a : v.adicCompletion F) * t ^ 2)) *
            ∫ x, A.ψ v ((-2 * (a : v.adicCompletion F) * t) * x) ∂μB := by
      rw [integral_congr_ae (ae_of_all _ hkernel), integral_const_mul]
    by_cases htD : t ∈ D
    · have hDprop : t ∈ B ∧ ∀ x ∈ B,
          A.ψ v (-2 * (a : v.adicCompletion F) * x * t) = 1 := by
        simpa [D, quadraticBallAnnihilator, B, Set.mem_iInter, Set.mem_inter_iff,
          Set.mem_ofPred_eq] using htD
      have htriv : ∀ x ∈ B,
          A.ψ v ((-2 * (a : v.adicCompletion F) * t) * x) = 1 := by
        intro x hx
        convert hDprop.2 x hx using 1 <;> ring
      have hquad' : A.ψ v (-((a : v.adicCompletion F) * t ^ 2)) = 1 := by
        calc
          A.ψ v (-((a : v.adicCompletion F) * t ^ 2)) =
              (A.ψ v ((a : v.adicCompletion F) * t ^ 2))⁻¹ :=
            (A.ψ v).map_neg_eq_inv _
          _ = 1 := by rw [hquad t htD]; simp
      have hlin : (∫ x, A.ψ v ((-2 * (a : v.adicCompletion F) * t) * x) ∂μB) =
          (μB.real Set.univ : ℂ) := by
        change (∫ x in B, A.ψ v ((-2 * (a : v.adicCompletion F) * t) * x) ∂μ) = _
        rw [linearBallIntegral_eq_measure_of_trivial A v μ N
          ((-2 * (a : v.adicCompletion F) * t)) htriv]
        exact congrArg (fun r : ℝ => (r : ℂ)) hmassB.symm
      rw [hkernelInt, hquad', hlin]
      simp only [if_pos htD, one_mul]
    · have hlin : (∫ x, A.ψ v ((-2 * (a : v.adicCompletion F) * t) * x) ∂μB) = 0 := by
        have hnotAll : ¬∀ x ∈ B,
            A.ψ v (-2 * (a : v.adicCompletion F) * x * t) = 1 := by
          intro hall
          have hDmem : t ∈ D := by
            have hall' : ∀ x ∈ B,
                A.ψ v (-(2 * (a : v.adicCompletion F) * x * t)) = 1 := by
              intro x hx
              convert hall x hx using 1 <;> ring
            simpa [D, quadraticBallAnnihilator, Set.mem_iInter, Set.mem_inter_iff,
              Set.mem_ofPred_eq] using ⟨ht, hall'⟩
          exact htD hDmem
        have hnontriv : ∃ x ∈ B,
            A.ψ v ((-2 * (a : v.adicCompletion F) * t) * x) ≠ 1 := by
          have hnontriv' : ∃ x ∈ B,
              A.ψ v (-2 * (a : v.adicCompletion F) * x * t) ≠ 1 := by
            by_contra hn
            apply hnotAll
            intro x hx
            by_contra hne
            exact hn ⟨x, hx, hne⟩
          rcases hnontriv' with ⟨x, hx, hne⟩
          refine ⟨x, hx, ?_⟩
          intro h
          have harg : -2 * (a : v.adicCompletion F) * x * t =
              (-2 * (a : v.adicCompletion F) * t) * x := by ring
          rw [← harg] at h
          exact hne h
        change (∫ x in B, A.ψ v ((-2 * (a : v.adicCompletion F) * t) * x) ∂μ) = 0
        exact linearBallIntegral_eq_zero_of_nontrivial A v μ hμ N
          ((-2 * (a : v.adicCompletion F) * t)) hnontriv
      rw [hkernelInt, hlin]
      simp only [if_neg htD, mul_zero]
  have hinnerAE :
      (fun t => ∫ x, G (x, t) ∂μB) =ᵐ[μB]
        D.indicator (fun _ => (μB.real Set.univ : ℂ)) := by
    filter_upwards [ae_restrict_mem hBmeas] with t ht
    by_cases htD : t ∈ D
    · calc
        (∫ x, G (x, t) ∂μB) = if t ∈ D then (μB.real Set.univ : ℂ) else 0 := hinner t ht
        _ = D.indicator (fun _ => (μB.real Set.univ : ℂ)) t := by
          rw [if_pos htD, Set.indicator_of_mem htD]
    · calc
        (∫ x, G (x, t) ∂μB) = if t ∈ D then (μB.real Set.univ : ℂ) else 0 := hinner t ht
        _ = D.indicator (fun _ => (μB.real Set.univ : ℂ)) t := by
          rw [if_neg htD, Set.indicator_of_notMem htD]
  have hresult : I * conj I =
      (μB.real Set.univ : ℂ) * (μB.real D : ℂ) := by
    calc
      I * conj I = ∫ x, ∫ y, q x * conj (q y) ∂μB ∂μB := hdouble
      _ = ∫ x, ∫ t, q x * conj (q (x + t)) ∂μB ∂μB := hshifted
      _ = ∫ t, ∫ x, G (x, t) ∂μB ∂μB := hswap
      _ = ∫ t, D.indicator (fun _ => (μB.real Set.univ : ℂ)) t ∂μB :=
        integral_congr_ae hinnerAE
      _ = (μB.real D : ℂ) * (μB.real Set.univ : ℂ) := by
        rw [integral_indicator_const (μ := μB) (e := (μB.real Set.univ : ℂ)) hDmeas]
        rw [Algebra.smul_def]
        change (μB.real D : ℂ) * (μB.real Set.univ : ℂ) = _
        rfl
      _ = _ := by ring
  have hnorm' : Complex.normSq I = μB.real Set.univ * μB.real D := by
    apply Complex.ofReal_inj.mp
    calc
      (Complex.normSq I : ℂ) = I * conj I := by
        rw [Complex.normSq_eq_conj_mul_self]
        ring
      _ = (μB.real Set.univ : ℂ) * (μB.real D : ℂ) := hresult
      _ = ((μB.real Set.univ * μB.real D : ℝ) : ℂ) := by rw [Complex.ofReal_mul]
  rw [hI, hmassB, hmassD] at hnorm'
  exact hnorm'

end ArtinPrimitiveRoots.Proofs.a1_weil_sol_w_c
