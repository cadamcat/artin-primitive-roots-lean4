import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.w_c.GaussianCutoff
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.HaarScale

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory
open scoped ENNReal

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol_w_c

open ArtinPrimitiveRoots.A1
open ArtinPrimitiveRoots.Proofs.a1_weil_sol

variable {F : Type} [Field F] [NumberField F]

local instance measurableGaussianScaleMeasure (v : FinPlace F) : MeasurableSpace (v.adicCompletion F) := borel _
local instance borelGaussianScaleMeasure (v : FinPlace F) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

theorem quadraticBallAnnihilator_measure_scale
    (A : AddCharData F) (v : FinPlace F) (μ : Measure (v.adicCompletion F))
    (hμ : Measure.IsAddHaarMeasure μ) (hψ : LocalCharacterRegular A v)
    (a : (v.adicCompletion F)ˣ) (N : ℕ)
    (hTailA : ∀ s ∈ linearBallAnnihilator A v N,
      s ∈ localBall v N ∧ (a : v.adicCompletion F)⁻¹ * s ∈ localBall v N)
    (hTail1 : ∀ s ∈ linearBallAnnihilator A v N,
      s ∈ localBall v N ∧ (1 : (v.adicCompletion F)ˣ)⁻¹ * s ∈ localBall v N) :
    μ.real (quadraticBallAnnihilator A v N a) =
      (absFin v (a : v.adicCompletion F))⁻¹ *
        μ.real (quadraticBallAnnihilator A v N 1) := by
  classical
  let B := localBall v N
  let D₀ := linearBallAnnihilator A v N
  let Dₐ := quadraticBallAnnihilator A v N a
  let D₁ := quadraticBallAnnihilator A v N 1
  let f : v.adicCompletion F → v.adicCompletion F := fun x => (a : v.adicCompletion F) * x
  have hD₀closed : IsClosed D₀ := by
    dsimp [D₀, linearBallAnnihilator]
    apply isClosed_iInter
    intro x
    apply isClosed_eq
    · exact hψ.1.comp (by fun_prop)
    · exact continuous_const
  have hD₀meas : MeasurableSet D₀ := hD₀closed.measurableSet
  have hAnnIff (s : v.adicCompletion F) :
      s ∈ D₀ ↔ ∀ x ∈ B, A.ψ v (-2 * x * s) = 1 := by
    constructor
    · intro hs
      have hs' := hs
      simp only [D₀, linearBallAnnihilator, Set.mem_iInter, Set.mem_ofPred_eq] at hs'
      intro x hx
      exact hs' ⟨x, hx⟩
    · intro hs
      simp only [D₀, linearBallAnnihilator, Set.mem_iInter, Set.mem_ofPred_eq]
      intro x
      exact hs x.1 x.2
  have hD₀sub : D₀ ⊆ B := by
    intro s hs
    exact (hTail1 s hs).1
  have hDaEq : Dₐ = f ⁻¹' D₀ := by
    ext t
    constructor
    · intro ht
      have htprop : t ∈ B ∧ ∀ x ∈ B,
          A.ψ v (-2 * (a : v.adicCompletion F) * x * t) = 1 := by
        simpa [Dₐ, quadraticBallAnnihilator, B, Set.mem_iInter, Set.mem_inter_iff,
          Set.mem_ofPred_eq] using ht
      change f t ∈ D₀
      apply (hAnnIff (f t)).2
      intro x hx
      convert htprop.2 x hx using 1 <;> simp [f] <;> ring_nf
    · intro ht
      change f t ∈ D₀ at ht
      have hchar := (hAnnIff (f t)).1 ht
      have htprop : ∀ x ∈ B, A.ψ v (-2 * (a : v.adicCompletion F) * x * t) = 1 := by
        intro x hx
        convert hchar x hx using 1 <;> simp [f] <;> ring_nf
      have htinB : t ∈ B := by
        have hh := (hTailA (f t) ht).2
        simpa [f, mul_assoc] using hh
      have hmem : t ∈ Dₐ := by
        simp only [Dₐ, quadraticBallAnnihilator, Set.mem_iInter, Set.mem_inter_iff,
          Set.mem_ofPred_eq]
        refine ⟨?_, ?_⟩
        · simpa [B] using htinB
        · intro x
          exact htprop x.1 (by simpa [B] using x.2)
      exact hmem
  have hD1Eq : D₁ = D₀ := by
    ext s
    constructor
    · intro hs
      have hsprop : s ∈ B ∧ ∀ x ∈ B, A.ψ v (-2 * (1 : v.adicCompletion F) * x * s) = 1 := by
        simpa [D₁, quadraticBallAnnihilator, B, Set.mem_iInter, Set.mem_inter_iff,
          Set.mem_ofPred_eq] using hs
      have hchar : ∀ x ∈ B, A.ψ v (-2 * x * s) = 1 := by
        intro x hx
        convert hsprop.2 x hx using 1 <;> ring_nf
      exact (hAnnIff s).2 hchar
    · intro hs
      have hchar := (hAnnIff s).1 hs
      have hsprop : ∀ x ∈ B, A.ψ v (-2 * (1 : v.adicCompletion F) * x * s) = 1 := by
        intro x hx
        convert hchar x hx using 1 <;> ring_nf
      have hsB : s ∈ B := (hTail1 s hs).1
      simp only [D₁, quadraticBallAnnihilator, Set.mem_iInter, Set.mem_inter_iff,
        Set.mem_ofPred_eq]
      refine ⟨?_, ?_⟩
      · simpa [B] using hsB
      · intro x
        exact hsprop x.1 (by simpa [B] using x.2)
  have hmapApply : μ.map f D₀ = μ (f ⁻¹' D₀) :=
    Measure.map_apply (by fun_prop) hD₀meas
  have hscale : μ Dₐ =
      (ENNReal.ofReal (absFin v (a : v.adicCompletion F)))⁻¹ * μ D₀ := by
    rw [hDaEq]
    calc
      μ (f ⁻¹' D₀) = μ.map f D₀ := hmapApply.symm
      _ = ((ENNReal.ofReal (absFin v (a : v.adicCompletion F)))⁻¹ • μ) D₀ := by
        rw [local_haar_scale v μ hμ a]
      _ = _ := by simp [Measure.smul_apply, smul_eq_mul]
  have habs : 0 < absFin v (a : v.adicCompletion F) :=
    (local_absolute_value v).2.1 a
  have hscaleReal : μ.real Dₐ =
      (absFin v (a : v.adicCompletion F))⁻¹ * μ.real D₀ := by
    rw [Measure.real_def, Measure.real_def, hscale,
      ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.toReal_ofReal habs.le]
  change μ.real Dₐ = (absFin v (a : v.adicCompletion F))⁻¹ * μ.real D₁
  rw [hD1Eq]
  exact hscaleReal

end ArtinPrimitiveRoots.Proofs.a1_weil_sol_w_c
