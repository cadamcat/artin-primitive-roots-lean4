import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.w_c.BallGeometry

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol_w_c

open ArtinPrimitiveRoots.A1
open ArtinPrimitiveRoots.Proofs.a1_weil_sol

variable {F : Type} [Field F] [NumberField F]

local instance measurableFiniteOrthogonality (v : FinPlace F) : MeasurableSpace (v.adicCompletion F) := borel _
local instance borelFiniteOrthogonality (v : FinPlace F) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

theorem linearBallIntegral_eq_zero_of_nontrivial
    (A : AddCharData F) (v : FinPlace F) (μ : Measure (v.adicCompletion F))
    (hμ : Measure.IsAddHaarMeasure μ) (N : ℕ) (c : v.adicCompletion F)
    (hchar : ∃ b ∈ localBall v N, A.ψ v (c * b) ≠ 1) :
    (∫ x in localBall v N, A.ψ v (c * x) ∂μ) = 0 := by
  classical
  letI : Measure.IsAddHaarMeasure μ := hμ
  obtain ⟨b, hb, hχ⟩ := hchar
  let f : v.adicCompletion F → ℂ :=
    (localBall v N).indicator (fun x => A.ψ v (c * x))
  have hpoint (x : v.adicCompletion F) :
      f (b + x) = A.ψ v (c * b) * f x := by
    by_cases hx : x ∈ localBall v N
    · have hbx : b + x ∈ localBall v N := localBall_add_mem v N hb hx
      simp [f, hx, hbx, ← AddChar.map_add_eq_mul, mul_add, mul_assoc]
    · have hbx : b + x ∉ localBall v N := by
        intro h
        have h' := localBall_add_mem v N h (localBall_neg_mem v N hb)
        have h'' : (b + x) + -b = x := by abel
        rw [h''] at h'
        exact hx h'
      simp [f, hx, hbx]
  have hshift : (∫ x, f (b + x) ∂μ) = ∫ x, f x ∂μ :=
    integral_add_left_eq_self f b
  have hscalar : (∫ x, f (b + x) ∂μ) = A.ψ v (c * b) * ∫ x, f x ∂μ := by
    rw [integral_congr_ae (ae_of_all μ hpoint), integral_const_mul]
  have hzero : (A.ψ v (c * b) - 1) * ∫ x, f x ∂μ = 0 := by
    calc
      (A.ψ v (c * b) - 1) * ∫ x, f x ∂μ =
          (∫ x, f (b + x) ∂μ) - ∫ x, f x ∂μ := by rw [hscalar]; ring
      _ = 0 := by rw [hshift]; ring
  have hI : (∫ x, f x ∂μ) = 0 := by
    rcases mul_eq_zero.mp hzero with h | h
    · exact False.elim (sub_ne_zero.mpr hχ h)
    · exact h
  calc
    (∫ x in localBall v N, A.ψ v (c * x) ∂μ) = ∫ x, f x ∂μ := by
      rw [← integral_indicator (localBall_measurableSet v N)]
    _ = 0 := hI

theorem linearBallIntegral_eq_measure_of_trivial
    (A : AddCharData F) (v : FinPlace F) (μ : Measure (v.adicCompletion F))
    (N : ℕ) (c : v.adicCompletion F)
    (htriv : ∀ x ∈ localBall v N, A.ψ v (c * x) = 1) :
    (∫ x in localBall v N, A.ψ v (c * x) ∂μ) = (μ.real (localBall v N) : ℂ) := by
  calc
    (∫ x in localBall v N, A.ψ v (c * x) ∂μ) =
        ∫ x in localBall v N, (1 : ℂ) ∂μ :=
      setIntegral_congr_fun (localBall_measurableSet v N) (fun x hx => htriv x hx)
    _ = (μ.real (localBall v N) : ℂ) := by
      rw [setIntegral_const]
      simp

end ArtinPrimitiveRoots.Proofs.a1_weil_sol_w_c
