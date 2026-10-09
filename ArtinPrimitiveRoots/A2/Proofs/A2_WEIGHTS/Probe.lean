import ArtinPrimitiveRoots.A2.Reflection.Missing
import ArtinPrimitiveRoots.A2.Proofs.A2_ZF_TOP.SelfDualMeasure
import ArtinPrimitiveRoots.A2.Proofs.A2_WEIGHTS.Finite
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-POISSON».P0
import Mathlib.LinearAlgebra.Countable
open NumberField IsDedekindDomain MeasureTheory
open ArtinPrimitiveRoots A1 A2
noncomputable section
private instance adicCompletion_separableSpace {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) : TopologicalSpace.SeparableSpace (v.adicCompletion F) := by
  letI : Countable F := by
    letI : Countable ℚ := inferInstance
    exact Finsupp.Countable.of_moduleFinite (R := ℚ) (M := F)
  exact TopologicalSpace.SeparableSpace.of_denseRange
    (algebraMap F (v.adicCompletion F)) (v.denseRange_algebraMap (K := F))
private instance adicCompletion_secondCountable {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) : SecondCountableTopology (v.adicCompletion F) :=
  UniformSpace.secondCountable_of_separable (v.adicCompletion F)
variable {F : Type} [Field F] [NumberField F] {CE : ℕ} {condη : Ideal (𝓞 F)}
  (S : SData F CE condη) (μ : ∀ v : FinPlace F, Theta.LocHaar v)
#synth BorelSpace (∀ v : S.Sf, v.1.adicCompletion F)
#check HasDerivAt.comp
#check Complex.hasDerivAt_exp
#check HasDerivAt.comp_ofReal
#check MeasureTheory.integral_Ioi_deriv_mul_eq_sub
#check HasCompactSupport.toSchwartzMap
#check ContDiffBump.toSchwartzMap
 #check _private.ArtinPrimitiveRoots.A2.Proofs.«A2-QS-POISSON».P0.«0».ArtinPrimitiveRoots.A2.qs_mellin_vertical_decay_uniform_of_zero
 #check ArtinPrimitiveRoots.A2.mellin
run_cmd do
  let env ← Lean.getEnv
  for (n, _) in env.constants.toList do
    if n.toString.contains "qs_mellin_vertical_decay_uniform_of_zero" then
      Lean.logInfo m!"FOUND {n}"
open ArtinPrimitiveRoots.A2
open Lean Elab Tactic Term
#check Lean.Meta.apply
#check Lean.MVarId.apply
#check Lean.Meta.mkConstWithFreshMVarLevels
#check Lean.Elab.Tactic.liftMetaTactic
elab "exact_hidden_qs_uniform" : tactic => do
  let mut n := Lean.Name.str Lean.Name.anonymous "_private"
  for p in ["ArtinPrimitiveRoots", "A2", "Proofs", "A2-QS-POISSON", "P0"] do
    n := Lean.Name.str n p
  n := Lean.Name.num n 0
  for p in ["ArtinPrimitiveRoots", "A2", "qs_mellin_vertical_decay_uniform_of_zero"] do
    n := Lean.Name.str n p
  liftMetaTactic fun g => do
    let e ← Lean.Meta.mkConstWithFreshMVarLevels n
    g.apply e
  evalTactic (← `(tactic| all_goals assumption))
example (g : ℝ → ℂ) (hg : IsQSWeight g) (hgzero : g 0 = 0)
    (a b : ℝ) (hab : a ≤ b) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Set.Icc a b, ∀ t : ℝ, 2 * Real.pi ≤ |t| →
      ‖mellin g ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C / |t| ^ N := by
  exact_hidden_qs_uniform
#synth BorelSpace (InfinitePlace F → ℂ)
#synth BorelSpace S.FS
@[instance_reducible] private noncomputable def prodMeas : MeasurableSpace S.FS := Prod.instMeasurableSpace
private theorem prodMeas_eq_borel : prodMeas S = borel S.FS := by
  letI : MeasurableSpace S.FS := prodMeas S
  letI : BorelSpace S.FS := inferInstance
  exact BorelSpace.measurable_eq
private noncomputable def addRef : @Measure S.FS (prodMeas S) :=
  (Measure.pi fun v : S.Sf => (μ v.1).μ).prod (Measure.pi fun _ : InfinitePlace F => (volume : Measure ℂ))
private theorem addRef_haar : Measure.IsAddHaarMeasure (addRef S μ) := by
  letI : MeasurableSpace S.FS := prodMeas S
  letI : BorelSpace S.FS := inferInstance
  letI : ∀ v : S.Sf, SigmaFinite ((μ v.1).μ) := fun v => by
    letI : ProperSpace (v.1.adicCompletion F) := bridgeFin_properSpace v.1
    letI : SigmaCompactSpace (v.1.adicCompletion F) := inferInstance
    infer_instance
  letI : SigmaFinite (volume : Measure ℂ) := inferInstance
  have hpi : Measure.IsAddHaarMeasure (Measure.pi fun v : S.Sf => (μ v.1).μ) := inferInstance
  have hpc : Measure.IsAddHaarMeasure (Measure.pi fun _ : InfinitePlace F => (volume : Measure ℂ)) := inferInstance
  letI : SigmaFinite (Measure.pi fun v : S.Sf => (μ v.1).μ) := inferInstance
  letI : SigmaFinite (Measure.pi fun _ : InfinitePlace F => (volume : Measure ℂ)) := inferInstance
  have hp : Measure.IsAddHaarMeasure ((Measure.pi fun v : S.Sf => (μ v.1).μ).prod
      (Measure.pi fun _ : InfinitePlace F => (volume : Measure ℂ))) := inferInstance
  exact hp
