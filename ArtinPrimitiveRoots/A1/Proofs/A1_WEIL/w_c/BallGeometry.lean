import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.HaarScale
import Mathlib.Topology.MetricSpace.Ultra.Basic

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol_w_c

open ArtinPrimitiveRoots.A1
open ArtinPrimitiveRoots.Proofs.a1_weil_sol

variable {F : Type} [Field F] [NumberField F]

local instance measurableBallGeometry (v : FinPlace F) : MeasurableSpace (v.adicCompletion F) := borel _
local instance borelBallGeometry (v : FinPlace F) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

def valuedBall (v : FinPlace F) (k : ℤ) : Set (v.adicCompletion F) :=
  {x | Valued.v x ≤ WithZero.exp k}

private theorem exists_radius_element (v : FinPlace F) (k : ℤ) :
    ∃ z : v.adicCompletion F, Valued.v z = WithZero.exp k := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hπ0 : π ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  let z : v.adicCompletion F := (algebraMap F (v.adicCompletion F) π) ^ (-k)
  have hzval : Valued.v (algebraMap F (v.adicCompletion F) π) = WithZero.exp (-1 : ℤ) := by
    change Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ)
    exact (v.valuedAdicCompletion_eq_valuation' π).trans hπ
  refine ⟨z, ?_⟩
  dsimp [z]
  rw [map_zpow₀, hzval]
  rw [← WithZero.exp_zsmul]
  simp

private noncomputable def radiusElement (v : FinPlace F) (k : ℤ) : v.adicCompletion F :=
  Classical.choose (exists_radius_element v k)

private theorem radiusElement_spec (v : FinPlace F) (k : ℤ) :
    Valued.v (radiusElement v k) = WithZero.exp k :=
  Classical.choose_spec (exists_radius_element v k)

theorem valuedBall_eq_closedBall (v : FinPlace F) (k : ℤ) :
    valuedBall v k = Metric.closedBall 0 ‖radiusElement v k‖ := by
  ext x
  simp only [valuedBall, Set.mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right]
  rw [Valued.toNormedField.norm_le_iff, radiusElement_spec]

theorem valuedBall_isOpen (v : FinPlace F) (k : ℤ) : IsOpen (valuedBall v k) := by
  rw [valuedBall_eq_closedBall]
  apply IsUltrametricDist.isOpen_closedBall 0
  have hz : radiusElement v k ≠ 0 := by
    intro h
    have hspec := radiusElement_spec v k
    rw [h, map_zero] at hspec
    exact WithZero.exp_ne_zero hspec.symm
  exact norm_ne_zero_iff.mpr hz

theorem valuedBall_isCompact (v : FinPlace F) (k : ℤ) : IsCompact (valuedBall v k) := by
  rw [valuedBall_eq_closedBall]
  exact isCompact_closedBall 0 ‖radiusElement v k‖

theorem localBall_eq_closedBall (v : FinPlace F) (N : ℕ) :
    localBall v N = Metric.closedBall 0 ‖radiusElement v (N : ℤ)‖ := by
  change valuedBall v (N : ℤ) = _
  exact valuedBall_eq_closedBall v N

theorem localBall_isCompact (v : FinPlace F) (N : ℕ) : IsCompact (localBall v N) := by
  rw [localBall_eq_closedBall]
  exact isCompact_closedBall 0 ‖radiusElement v (N : ℤ)‖

theorem localBall_measurableSet (v : FinPlace F) (N : ℕ) : MeasurableSet (localBall v N) := by
  rw [localBall_eq_closedBall]
  exact Metric.isClosed_closedBall.measurableSet

theorem localBall_isOpen (v : FinPlace F) (N : ℕ) : IsOpen (localBall v N) := by
  rw [localBall_eq_closedBall]
  exact IsUltrametricDist.isOpen_closedBall 0 (norm_ne_zero_iff.mpr (by
    intro h
    have hspec := radiusElement_spec v (N : ℤ)
    rw [h, map_zero] at hspec
    exact WithZero.exp_ne_zero hspec.symm))

theorem localBall_add_mem (v : FinPlace F) (N : ℕ) {x y : v.adicCompletion F}
    (hx : x ∈ localBall v N) (hy : y ∈ localBall v N) : x + y ∈ localBall v N := by
  rw [localBall_eq_closedBall] at hx hy ⊢
  simp only [Metric.mem_closedBall, dist_zero_right] at hx hy ⊢
  exact (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)

theorem localBall_neg_mem (v : FinPlace F) (N : ℕ) {x : v.adicCompletion F}
    (hx : x ∈ localBall v N) : -x ∈ localBall v N := by
  rw [localBall_eq_closedBall] at hx ⊢
  simp only [Metric.mem_closedBall, dist_zero_right] at hx ⊢
  simpa using hx

end ArtinPrimitiveRoots.Proofs.a1_weil_sol_w_c
