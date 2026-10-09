import ArtinPrimitiveRoots.A1.Field
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false
set_option maxHeartbeats 800000

open NumberField
open scoped Classical Pointwise

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_rffwd_sol
open ArtinPrimitiveRoots.A1

theorem continuous_unit_function_bound_on_sheet {F : Type} [Field F] [NumberField F]
    {CE : ℕ} {condη : Ideal (𝓞 F)} (S : SData F CE condη)
    (K : Set S.FS) (hK : IsCompact K) (l : ℝ) (hl : 0 < l)
    (f : S.FSˣ → ℂ) (hf : Continuous f) :
    ∃ C : ℝ, ∀ u : S.FSˣ, (u : S.FS) ∈ K →
      S.absS (u : S.FS) = l → ‖f u‖ ≤ C := by
  classical
  have hAbsFin (v : FinPlace F) (x : v.adicCompletion F) :
      absFin v x = ‖x‖ := by
    unfold absFin
    rw [dif_pos (HeightOneSpectrum.absNorm_ne_zero v)]
    exact (FinitePlace.norm_def v x).symm
  have hAbs : Continuous S.absS := by
    unfold SData.absS
    apply Continuous.mul
    · apply continuous_finsetProd Finset.univ
      intro v hv
      have h : Continuous (absFin v.1) := by
        convert (continuous_norm : Continuous fun x : v.1.adicCompletion F => ‖x‖) using 1
        ext x
        exact hAbsFin v.1 x
      exact h.comp ((continuous_apply v).comp continuous_fst)
    · apply continuous_finsetProd Finset.univ
      intro w hw
      exact Complex.continuous_normSq.comp ((continuous_apply w).comp continuous_snd)
  have hCoords (y : S.FS) : IsUnit y ↔
      (∀ v : S.Sf, y.1 v ≠ 0) ∧ (∀ w : InfinitePlace F, y.2 w ≠ 0) := by
    simp [Prod.isUnit_iff, Pi.isUnit_iff]
  have hUnit (y : S.FS) (hy : S.absS y = l) : IsUnit y := by
    have hnz : S.absS y ≠ 0 := by rw [hy]; exact hl.ne'
    apply (hCoords y).mpr
    constructor
    · intro v hz
      have hzabs : absFin v.1 (y.1 v) = 0 := by
        rw [hz, hAbsFin]
        simp
      have hprod : (∏ v' : S.Sf, absFin v'.1 (y.1 v')) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ v) hzabs
      apply hnz
      unfold SData.absS
      rw [hprod]
      simp
    · intro w hz
      have hzabs : Complex.normSq (y.2 w) = 0 := by simp [hz]
      have hprod : (∏ w' : InfinitePlace F, Complex.normSq (y.2 w')) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ w) hzabs
      apply hnz
      unfold SData.absS
      rw [hprod]
      simp
  let B : Set S.FS := K ∩ {y | S.absS y = l}
  have hB : IsCompact B := hK.inter_right (isClosed_eq hAbs continuous_const)
  have hBUnit (y : S.FS) (hy : y ∈ B) : IsUnit y := hUnit y hy.2
  let invCoords : S.FS → S.FS := fun y =>
    ((fun v => (y.1 v)⁻¹), (fun w => (y.2 w)⁻¹))
  have hInvCont : ContinuousOn invCoords B := by
    have hfin : ∀ v : S.Sf, ContinuousOn (fun y : S.FS => (y.1 v)⁻¹) B := by
      intro v
      exact ((continuous_apply v).comp continuous_fst).continuousOn.inv₀
        (fun y hy => ((hCoords y).mp (hBUnit y hy)).1 v)
    have harch : ∀ w : InfinitePlace F, ContinuousOn (fun y : S.FS => (y.2 w)⁻¹) B := by
      intro w
      exact ((continuous_apply w).comp continuous_snd).continuousOn.inv₀
        (fun y hy => ((hCoords y).mp (hBUnit y hy)).2 w)
    exact (continuousOn_pi.2 hfin).prodMk (continuousOn_pi.2 harch)
  have hInvEq (u : S.FSˣ) : invCoords (u : S.FS) = ((u⁻¹ : S.FSˣ) : S.FS) := by
    have hu := (hCoords (u : S.FS)).mp u.isUnit
    have hmul : (u : S.FS) * ((u⁻¹ : S.FSˣ) : S.FS) = 1 :=
      congrArg (fun z : S.FSˣ => (z : S.FS)) (mul_inv_cancel u)
    apply Prod.ext
    · funext v
      dsimp only [invCoords]
      apply mul_left_cancel₀ (hu.1 v)
      have hc := congrArg (fun y : S.FS => y.1 v) hmul
      change (u : S.FS).1 v * ((u⁻¹ : S.FSˣ) : S.FS).1 v = 1 at hc
      calc
        _ = 1 := mul_inv_cancel₀ (hu.1 v)
        _ = _ := hc.symm
    · funext w
      dsimp only [invCoords]
      apply mul_left_cancel₀ (hu.2 w)
      have hc := congrArg (fun y : S.FS => y.2 w) hmul
      change (u : S.FS).2 w * ((u⁻¹ : S.FSˣ) : S.FS).2 w = 1 at hc
      calc
        _ = 1 := mul_inv_cancel₀ (hu.2 w)
        _ = _ := hc.symm
  have hBI : IsCompact (invCoords '' B) := hB.image_of_continuousOn hInvCont
  let BIop : Set (S.FSᵐᵒᵖ) := MulOpposite.op '' (invCoords '' B)
  have hBIop : IsCompact BIop := hBI.image MulOpposite.opHomeomorph.continuous
  let BU : Set S.FSˣ := {u | (u : S.FS) ∈ B}
  have hPre : Units.embedProduct S.FS ⁻¹' (B ×ˢ BIop) = BU := by
    ext u
    change ((u : S.FS) ∈ B ∧
      MulOpposite.op ((u⁻¹ : S.FSˣ) : S.FS) ∈ BIop) ↔ (u : S.FS) ∈ B
    constructor
    · exact And.left
    · intro hu
      refine ⟨hu, ?_⟩
      refine ⟨invCoords (u : S.FS), ⟨(u : S.FS), hu, rfl⟩, ?_⟩
      rw [hInvEq]
  have hBU : IsCompact BU := by
    have h := (Units.isClosedEmbedding_embedProduct (α := S.FS)).isCompact_preimage
      (hB.prod hBIop)
    rwa [hPre] at h
  obtain ⟨C, hC⟩ := hBU.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨C, ?_⟩
  intro u hu hnorm
  exact hC u ⟨hu, hnorm⟩

end ArtinPrimitiveRoots.Proofs.a2_rffwd_sol
