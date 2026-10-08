import ArtinPrimitiveRoots.Proofs.th_continue_b.TorusReduction
import ArtinPrimitiveRoots.Proofs.th_continue_b.TorusSL
import ArtinPrimitiveRoots.Proofs.th_continue_b.ThetaCoordContinuous
import ArtinPrimitiveRoots.Proofs.th_continue_b.ThetaResidual

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 256
open NumberField IsDedekindDomain
open scoped Classical Topology MatrixGroups
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

theorem continuedEis_theta_torus_ratio_chart
    {P : CoverPackage D S H A} {G : GlobalDatum P}
    {I : ContinuedEisInput P G} {C : ContinuedEisComponents I}
    (R : ContinuedEisReconstruction C) (g h : P.tc.G) (y0 : S.FSˣ) :
    ∃ (j : C.J) (p : S.FSˣ → ArtinPrimitiveRoots.A1.Spec.Coord F),
      ContinuousAt p y0 ∧
      (∀ y, p y ∈ ArtinPrimitiveRoots.A1.Spec.posSet F) ∧
      ∀ y, R.theta (g * P.tc.aS
        (continuedEis_archPart S (y0⁻¹ * y)) * h) =
        C.componentTheta j (ArtinPrimitiveRoots.A1.Spec.ptX F (p y)) := by
  classical
  have hBasePoint (w : InfinitePlace F) (m : SL(2, ℂ)) :
      ArtinPrimitiveRoots.A1.Spec.pt (continuedEis_baseCoord m).1
        (continuedEis_baseCoord m).2 =
      m • ArtinPrimitiveRoots.A1.Spec.pt (0 : ℂ) (1 : ℝ) := by
    as_aux_lemma =>
      have hc := congrFun (continuedEis_coords_base_action (F := F) m) w
      have hp := congrArg (fun z : ℂ × ℝ => ArtinPrimitiveRoots.A1.Spec.pt z.1 z.2) hc
      exact hp.symm.trans (ArtinPrimitiveRoots.A1.Spec.pt_horiz_height
        (m • ArtinPrimitiveRoots.A1.Spec.pt (0 : ℂ) (1 : ℝ)))
  have hSLMul (U V : S.FSˣ → SL(2, ℂ))
      (hU : ∀ i j, ContinuousAt (fun q => U q i j) y0)
      (hV : ∀ i j, ContinuousAt (fun q => V q i j) y0) :
      ∀ i j, ContinuousAt (fun q => (U q * V q) i j) y0 := by
    intro i j
    change ContinuousAt (fun q => ∑ k : Fin 2, U q i k * V q k j) y0
    simp only [Fin.sum_univ_two]
    exact ((hU i 0).mul (hV 0 j)).add ((hU i 1).mul (hV 1 j))
  obtain ⟨j, γ, x0, yH, kinf, k, hyH, hkinf, hk, hg⟩ :=
    continuedEis_component_representatives C (g * h)
  obtain ⟨rKin, hqKin, hFKin, hCKin⟩ := hkinf
  obtain ⟨rH, hqH⟩ := P.q_surj h
  let kSL (w : InfinitePlace F) : SL(2, ℂ) :=
    continuedEis_slLiftPGL (P.compC w rKin)
  have hkSL (w : InfinitePlace F) :
      Matrix.SpecialLinearGroup.toPGL (kSL w) = P.compC w rKin :=
    continuedEis_slLiftPGL_toPGL (P.compC w rKin)
  let hSL (w : InfinitePlace F) : SL(2, ℂ) :=
    continuedEis_slLiftPGL (P.compC w rH)
  have hhSL (w : InfinitePlace F) :
      Matrix.SpecialLinearGroup.toPGL (hSL w) = P.compC w rH :=
    continuedEis_slLiftPGL_toPGL (P.compC w rH)
  let arch (q : S.FSˣ) : S.FSˣ := continuedEis_archPart S (y0⁻¹ * q)
  let d (q : S.FSˣ) (w : InfinitePlace F) : SL(2, ℂ) :=
    (hSL w)⁻¹ * continuedEis_slTorus (S.compC w (y0⁻¹ * q)) * hSL w
  let M (q : S.FSˣ) (w : InfinitePlace F) : SL(2, ℂ) :=
    ArtinPrimitiveRoots.A1.Spec.ptMat (x0 w) (yH w) (hyH w) * kSL w * d q w
  let p (q : S.FSˣ) : ArtinPrimitiveRoots.A1.Spec.Coord F :=
    fun w => continuedEis_baseCoord (M q w)
  have hTorEntry (w : InfinitePlace F) : ∀ i j,
      ContinuousAt (fun q : S.FSˣ =>
        continuedEis_slTorus (S.compC w (y0⁻¹ * q)) i j) y0 := by
    have hC : Continuous (S.compC w) := by
      unfold SData.compC
      apply Continuous.units_map
      exact (continuous_apply w).comp continuous_snd
    have hRatio : Continuous (fun q : S.FSˣ => S.compC w (y0⁻¹ * q)) :=
      hC.comp (continuous_const.mul continuous_id)
    have hVal : ContinuousAt (fun q : S.FSˣ =>
        (S.compC w (y0⁻¹ * q) : ℂ)) y0 :=
      Units.continuous_val.continuousAt.comp hRatio.continuousAt
    have hOne : (S.compC w (y0⁻¹ * y0) : ℂ) = 1 := by
      rw [inv_mul_cancel, map_one, Units.val_one]
    have hRoot : ContinuousAt (fun q : S.FSˣ =>
        Complex.sqrt (S.compC w (y0⁻¹ * q) : ℂ)) y0 := by
      have hS : ContinuousAt Complex.sqrt
          (S.compC w (y0⁻¹ * y0) : ℂ) := by
        rw [hOne]
        exact Complex.continuousAt_sqrt (Or.inl (by norm_num))
      exact hS.comp (f := fun q : S.FSˣ => (S.compC w (y0⁻¹ * q) : ℂ)) hVal
    have hRootNe : Complex.sqrt (S.compC w (y0⁻¹ * y0) : ℂ) ≠ 0 := by
      rw [hOne, Complex.sqrt_one]
      exact one_ne_zero
    intro i j
    fin_cases i <;> fin_cases j
    · exact hRoot
    · exact continuousAt_const
    · exact continuousAt_const
    · exact hRoot.inv₀ hRootNe
  have hDentry (w : InfinitePlace F) : ∀ i j,
      ContinuousAt (fun q : S.FSˣ => d q w i j) y0 := by
    have hFirst := hSLMul (fun _ : S.FSˣ => (hSL w)⁻¹)
      (fun q => continuedEis_slTorus (S.compC w (y0⁻¹ * q)))
      (fun i j => continuousAt_const) (hTorEntry w)
    exact hSLMul
      (fun q => (hSL w)⁻¹ * continuedEis_slTorus (S.compC w (y0⁻¹ * q)))
      (fun _ => hSL w) hFirst (fun i j => continuousAt_const)
  have hMentry (w : InfinitePlace F) : ∀ i j,
      ContinuousAt (fun q : S.FSˣ => M q w i j) y0 := by
    exact hSLMul (fun _ : S.FSˣ =>
      ArtinPrimitiveRoots.A1.Spec.ptMat (x0 w) (yH w) (hyH w) * kSL w)
      (fun q => d q w) (fun i j => continuousAt_const) (hDentry w)
  have hpCont : ContinuousAt p y0 := by
    apply continuousAt_pi.mpr
    intro w
    exact continuedEis_baseCoord_continuousAt (fun q => M q w) y0 (hMentry w)
  have hpPos (q : S.FSˣ) : p q ∈ ArtinPrimitiveRoots.A1.Spec.posSet F := by
    intro w
    exact inv_pos.mpr (continuedEis_baseDen_pos (M q w))
  have hpHeight (q : S.FSˣ) : ∀ w, 0 < (p q w).2 := hpPos q
  have hptX (q : S.FSˣ) : ArtinPrimitiveRoots.A1.Spec.ptX F (p q) =
      fun w => M q w • ArtinPrimitiveRoots.A1.Spec.pt (0 : ℂ) (1 : ℝ) := by
    funext w
    exact hBasePoint w (M q w)
  let rT (q : S.FSˣ) : P.RP := Classical.choose (P.aS_components (arch q))
  have hqT (q : S.FSˣ) : P.q (rT q) = P.tc.aS (arch q) :=
    (Classical.choose_spec (P.aS_components (arch q))).1
  have hFT (q : S.FSˣ) (v : FinPlace F) : P.compF v (rT q) = 1 := by
    have hRaw := (Classical.choose_spec (P.aS_components (arch q))).2.1 v
    by_cases hv : v ∈ S.Sf
    · rw [dite_eq_left hv] at hRaw
      have hU : S.compU ⟨v, hv⟩ (arch q) = 1 := by
        apply Units.ext
        rfl
      rw [hU, (P.loc v).a_one] at hRaw
      exact hRaw
    · rw [dite_eq_right hv] at hRaw
      exact hRaw
  have hCT (q : S.FSˣ) (w : InfinitePlace F) :
      P.compC w (rT q) = Matrix.SpecialLinearGroup.toPGL
        (continuedEis_slTorus (S.compC w (y0⁻¹ * q))) := by
    have hRaw := (Classical.choose_spec (P.aS_components (arch q))).2.2 w
    have hU : S.compC w (arch q) = S.compC w (y0⁻¹ * q) := by
      apply Units.ext
      rfl
    rw [hU] at hRaw
    exact hRaw.trans (continuedEis_slTorus_toPGL _).symm
  let rD (q : S.FSˣ) : P.RP := rH⁻¹ * rT q * rH
  let δ (q : S.FSˣ) : P.tc.G := h⁻¹ * P.tc.aS (arch q) * h
  have hqD (q : S.FSˣ) : P.q (rD q) = δ q := by
    change P.q (rH⁻¹ * rT q * rH) = h⁻¹ * P.tc.aS (arch q) * h
    rw [map_mul, map_mul, map_inv, hqH, hqT]
  have hFD (q : S.FSˣ) (v : FinPlace F) : P.compF v (rD q) = 1 := by
    change P.compF v (rH⁻¹ * rT q * rH) = 1
    rw [map_mul, map_mul, map_inv, hFT]
    simp only [mul_one, inv_mul_cancel]
  have hCD (q : S.FSˣ) (w : InfinitePlace F) :
      P.compC w (rD q) = Matrix.SpecialLinearGroup.toPGL (d q w) := by
    let c : P.RP →* PGL(2, ℂ) := P.compC w
    have hT : c (rT q) = Matrix.SpecialLinearGroup.toPGL
        (continuedEis_slTorus (S.compC w (y0⁻¹ * q))) := hCT q w
    have hH : Matrix.SpecialLinearGroup.toPGL (hSL w) = c rH := hhSL w
    have hRaw : c (rD q) = (c rH)⁻¹ *
        Matrix.SpecialLinearGroup.toPGL
          (continuedEis_slTorus (S.compC w (y0⁻¹ * q))) * c rH := by
      change c (rH⁻¹ * rT q * rH) = _
      rw [c.map_mul, c.map_mul, c.map_inv, hT]
    have hMap : Matrix.SpecialLinearGroup.toPGL (d q w) =
        (c rH)⁻¹ * Matrix.SpecialLinearGroup.toPGL
          (continuedEis_slTorus (S.compC w (y0⁻¹ * q))) * c rH := by
      change Matrix.SpecialLinearGroup.toPGL ((hSL w)⁻¹ *
        continuedEis_slTorus (S.compC w (y0⁻¹ * q)) * hSL w) = _
      rw [map_mul, map_mul, map_inv, hH]
    exact hRaw.trans hMap.symm
  let b (q : S.FSˣ) : P.tc.G :=
    nInf P (fun w => (p q w).1) * aInf P (fun w => (p q w).2)
  let rB (q : S.FSˣ) : P.RP :=
    continuedEis_rootRep P (fun w => (p q w).1) *
      continuedEis_archRep P (fun w => (p q w).2) (hpHeight q)
  have hqB (q : S.FSˣ) :
      P.q (rB q) = b q := by
    change P.q (continuedEis_rootRep P (fun w => (p q w).1) *
        continuedEis_archRep P (fun w => (p q w).2) (hpHeight q)) = _
    rw [map_mul, continuedEis_rootRep_q, continuedEis_archRep_q]
  have hFB (q : S.FSˣ) (v : FinPlace F) :
      P.compF v (rB q) = 1 := by
    change P.compF v (continuedEis_rootRep P (fun w => (p q w).1) *
        continuedEis_archRep P (fun w => (p q w).2) (hpHeight q)) = _
    rw [map_mul, continuedEis_rootRep_compF, continuedEis_archRep_compF]
    simp
  have hCB (q : S.FSˣ)
      (w : InfinitePlace F) :
      P.compC w (rB q) = Matrix.SpecialLinearGroup.toPGL
        (ArtinPrimitiveRoots.A1.Spec.ptMat (p q w).1 (p q w).2 (hpHeight q w)) := by
    have hroot : P.compC w (continuedEis_rootRep P (fun w => (p q w).1)) =
        QuotientGroup.mk (upperM ℂ (p q w).1) :=
      continuedEis_rootRep_compC P (fun w => (p q w).1) w
    have harch : P.compC w (continuedEis_archRep P (fun w => (p q w).2) (hpHeight q)) =
        QuotientGroup.mk (diagM ℂ (continuedEis_archUnit (fun w => (p q w).2)
          (hpHeight q) w)) :=
      continuedEis_archRep_compC P (fun w => (p q w).2) (hpHeight q) w
    have hcan : (QuotientGroup.mk (upperM ℂ (p q w).1) : PGL2 ℂ) *
        (QuotientGroup.mk (diagM ℂ (continuedEis_archUnit (fun w => (p q w).2)
          (hpHeight q) w)) : PGL2 ℂ) =
        Matrix.SpecialLinearGroup.toPGL
          (ArtinPrimitiveRoots.A1.Spec.ptMat (p q w).1 (p q w).2 (hpHeight q w)) := by
      have hmul : (QuotientGroup.mk (upperM ℂ (p q w).1) : PGL2 ℂ) *
          (QuotientGroup.mk (diagM ℂ (continuedEis_archUnit (fun w => (p q w).2)
            (hpHeight q) w)) : PGL2 ℂ) =
          (QuotientGroup.mk (upperM ℂ (p q w).1 *
            diagM ℂ (continuedEis_archUnit (fun w => (p q w).2) (hpHeight q) w)) : PGL2 ℂ) := by
        change Matrix.ProjGenLinGroup.mk (upperM ℂ (p q w).1) *
            Matrix.ProjGenLinGroup.mk (diagM ℂ (continuedEis_archUnit
              (fun w => (p q w).2) (hpHeight q) w)) = _
        exact ((Matrix.ProjGenLinGroup.mk).map_mul _ _).symm
      have hmat : (QuotientGroup.mk (upperM ℂ (p q w).1 *
          diagM ℂ (continuedEis_archUnit (fun w => (p q w).2) (hpHeight q) w)) : PGL2 ℂ) =
          Matrix.SpecialLinearGroup.toPGL
            (ArtinPrimitiveRoots.A1.Spec.ptMat (p q w).1 (p q w).2 (hpHeight q w)) := by
        change QuotientGroup.mk (upperM ℂ (p q w).1 *
            diagM ℂ (continuedEis_archUnit (fun w => (p q w).2) (hpHeight q) w)) =
          QuotientGroup.mk (ArtinPrimitiveRoots.A1.Spec.ptMat
            (p q w).1 (p q w).2 (hpHeight q w) : GL (Fin 2) ℂ)
        simpa [continuedEis_archUnit] using
          (continuedEis_ptMat_pgl (p q w).1 (p q w).2 (hpHeight q w)).symm
      exact hmul.trans hmat
    have hBmap : P.compC w (rB q) =
        P.compC w (continuedEis_rootRep P (fun w => (p q w).1)) *
          P.compC w (continuedEis_archRep P (fun w => (p q w).2) (hpHeight q)) := by
      exact (P.compC w).map_mul _ _
    rw [hroot, harch] at hBmap
    exact hBmap.trans hcan
  let rA (q : S.FSˣ) : P.RP :=
    continuedEis_rootRep P x0 * continuedEis_archRep P yH hyH * rKin * rD q
  have hqA (q : S.FSˣ) : P.q (rA q) =
      nInf P x0 * aInf P yH * kinf * δ q := by
    change P.q (continuedEis_rootRep P x0 *
      continuedEis_archRep P yH hyH * rKin * rD q) = _
    rw [map_mul, map_mul, map_mul, continuedEis_rootRep_q,
      continuedEis_archRep_q, hqKin, hqD]
  have hFA (q : S.FSˣ) (v : FinPlace F) : P.compF v (rA q) = 1 := by
    simp only [rA, map_mul, continuedEis_rootRep_compF,
      continuedEis_archRep_compF, hFKin, hFD, one_mul]
  have hCA (q : S.FSˣ) (w : InfinitePlace F) :
      P.compC w (rA q) = Matrix.SpecialLinearGroup.toPGL (M q w) := by
    have hPt : (QuotientGroup.mk (upperM ℂ (x0 w)) : PGL2 ℂ) *
        (QuotientGroup.mk (diagM ℂ (continuedEis_archUnit yH hyH w)) : PGL2 ℂ) =
        Matrix.SpecialLinearGroup.toPGL
          (ArtinPrimitiveRoots.A1.Spec.ptMat (x0 w) (yH w) (hyH w)) := by
      have hMul : (QuotientGroup.mk (upperM ℂ (x0 w)) : PGL2 ℂ) *
          (QuotientGroup.mk (diagM ℂ (continuedEis_archUnit yH hyH w)) : PGL2 ℂ) =
          QuotientGroup.mk (upperM ℂ (x0 w) *
            diagM ℂ (continuedEis_archUnit yH hyH w)) := by
        change Matrix.ProjGenLinGroup.mk _ * Matrix.ProjGenLinGroup.mk _ = _
        exact ((Matrix.ProjGenLinGroup.mk).map_mul _ _).symm
      have hMat : (QuotientGroup.mk (upperM ℂ (x0 w) *
          diagM ℂ (continuedEis_archUnit yH hyH w)) : PGL2 ℂ) =
          Matrix.SpecialLinearGroup.toPGL
            (ArtinPrimitiveRoots.A1.Spec.ptMat (x0 w) (yH w) (hyH w)) := by
        change QuotientGroup.mk (upperM ℂ (x0 w) *
          diagM ℂ (continuedEis_archUnit yH hyH w)) =
          QuotientGroup.mk (ArtinPrimitiveRoots.A1.Spec.ptMat
            (x0 w) (yH w) (hyH w) : GL (Fin 2) ℂ)
        exact (continuedEis_ptMat_pgl (x0 w) (yH w) (hyH w)).symm
      exact hMul.trans hMat
    change P.compC w (continuedEis_rootRep P x0 *
      continuedEis_archRep P yH hyH * rKin * rD q) = _
    rw [map_mul, map_mul, map_mul, continuedEis_rootRep_compC,
      continuedEis_archRep_compC, hCD, hPt, ← hkSL]
    change Matrix.SpecialLinearGroup.toPGL
        (ArtinPrimitiveRoots.A1.Spec.ptMat (x0 w) (yH w) (hyH w)) *
        Matrix.SpecialLinearGroup.toPGL (kSL w) *
        Matrix.SpecialLinearGroup.toPGL (d q w) =
      Matrix.SpecialLinearGroup.toPGL
        (ArtinPrimitiveRoots.A1.Spec.ptMat (x0 w) (yH w) (hyH w) * kSL w * d q w)
    have hFirst := (Matrix.SpecialLinearGroup.toPGL).map_mul
      (ArtinPrimitiveRoots.A1.Spec.ptMat (x0 w) (yH w) (hyH w)) (kSL w)
    have hLast := (Matrix.SpecialLinearGroup.toPGL).map_mul
      (ArtinPrimitiveRoots.A1.Spec.ptMat (x0 w) (yH w) (hyH w) * kSL w) (d q w)
    exact (congrArg (fun a => a * Matrix.SpecialLinearGroup.toPGL (d q w))
      hFirst.symm).trans hLast.symm
  let rRes (q : S.FSˣ) : P.RP :=
    (rB q)⁻¹ * rA q
  let κ (q : S.FSˣ) : P.tc.G := P.q (rRes q)
  have hκ (q : S.FSˣ) : κ q ∈ infCompact P := by
    refine ⟨rRes q, rfl, ?_, ?_⟩
    · intro v
      simp [rRes, map_mul, map_inv, hFA q v, hFB q v]
    · intro w
      have horbit : M q w • ArtinPrimitiveRoots.A1.Spec.pt (0 : ℂ) (1 : ℝ) =
          ArtinPrimitiveRoots.A1.Spec.pt (p q w).1 (p q w).2 :=
        congrFun (hptX q).symm w
      obtain ⟨uGL, huUnit, huPGL⟩ := continuedEis_slPointResidual F (M q w)
        (p q w).1 (p q w).2 (hpHeight q w) horbit
      refine ⟨uGL, huUnit, ?_⟩
      have hCm : P.compC w (rRes q) = P.compC w ((rB q)⁻¹) * P.compC w (rA q) :=
        (P.compC w).map_mul _ _
      have hCi : P.compC w ((rB q)⁻¹) * P.compC w (rA q) =
          (P.compC w (rB q))⁻¹ * P.compC w (rA q) :=
        congrArg (fun a => a * P.compC w (rA q)) ((P.compC w).map_inv _)
      have hCe := congrArg₂ (fun a b : PGL2 ℂ => a⁻¹ * b) (hCB q w) (hCA q w)
      exact (hCm.trans hCi).trans (hCe.trans huPGL)
  have hκcomm (q : S.FSˣ) :
      κ q * j = j * κ q := by
    have hj := C.finite_components j j.property
    have hκF : ∃ x : P.RP, P.q x = κ q ∧ ∀ v, P.compF v x = 1 := by
      refine ⟨rRes q, ?_, ?_⟩
      · rfl
      · intro v
        simp [rRes, map_mul, map_inv, hFA q v, hFB q v]
    exact (continuedEis_mixed_commute P hj hκF).symm
  have hkD (q : S.FSˣ) : k * δ q = δ q * k := by
    obtain ⟨rK, hqK, hKC, _⟩ := hk
    exact continuedEis_mixed_commute P ⟨rK, hqK, hKC⟩ ⟨rD q, hqD q, hFD q⟩
  have hjKin : j * kinf = kinf * j := by
    exact continuedEis_mixed_commute P (C.finite_components j j.property)
      ⟨rKin, hqKin, hFKin⟩
  have hjD (q : S.FSˣ) : j * δ q = δ q * j := by
    exact continuedEis_mixed_commute P (C.finite_components j j.property)
      ⟨rD q, hqD q, hFD q⟩
  have hjTail (q : S.FSˣ) : j * (kinf * δ q) = (kinf * δ q) * j := by
    calc
      j * (kinf * δ q) = (j * kinf) * δ q := by group
      _ = (kinf * j) * δ q := by rw [hjKin]
      _ = kinf * (j * δ q) := by group
      _ = kinf * (δ q * j) := by rw [hjD q]
      _ = (kinf * δ q) * j := by group
  have hbκ (q : S.FSˣ) : b q * κ q = P.q (rA q) := by
    calc
      b q * κ q = P.q (rB q) * P.q (rRes q) := by rw [hqB]
      _ = P.q (rB q * rRes q) := ((P.q).map_mul _ _).symm
      _ = P.q (rA q) := by simp only [rRes, mul_inv_cancel_left]
  have hOrbitGroup (q : S.FSˣ) : g * P.tc.aS (arch q) * h =
      P.tc.rat γ * ((b q * j) * κ q * k) := by
    have hStart : g * P.tc.aS (arch q) * h = (g * h) * δ q := by
      dsimp only [δ]
      group
    have hMoveK : ((nInf P x0 * aInf P yH * j) * kinf * k) * δ q =
        ((nInf P x0 * aInf P yH * j) * kinf * δ q) * k := by
      calc
        _ = (nInf P x0 * aInf P yH * j) * kinf * (k * δ q) := by group
        _ = (nInf P x0 * aInf P yH * j) * kinf * (δ q * k) := by rw [hkD q]
        _ = _ := by group
    have hMoveJ : (nInf P x0 * aInf P yH * j) * kinf * δ q =
        (nInf P x0 * aInf P yH * kinf * δ q) * j := by
      calc
        _ = (nInf P x0 * aInf P yH) * (j * (kinf * δ q)) := by group
        _ = (nInf P x0 * aInf P yH) * ((kinf * δ q) * j) := by rw [hjTail q]
        _ = _ := by group
    calc
      _ = (g * h) * δ q := hStart
      _ = P.tc.rat γ * (((nInf P x0 * aInf P yH * j) * kinf * k) * δ q) := by
        rw [hg]
        group
      _ = P.tc.rat γ * (((nInf P x0 * aInf P yH * j) * kinf * δ q) * k) := by rw [hMoveK]
      _ = P.tc.rat γ * ((P.q (rA q) * j) * k) := by rw [hMoveJ, ← hqA q]
      _ = P.tc.rat γ * ((b q * κ q * j) * k) := by rw [← hbκ q]
      _ = P.tc.rat γ * ((b q * j) * κ q * k) := by
        have hOrder : b q * κ q * j = b q * j * κ q := by
          calc
            b q * κ q * j = b q * (κ q * j) := by group
            _ = b q * (j * κ q) := by rw [hκcomm q]
            _ = b q * j * κ q := by group
        rw [hOrder]
  have hthetaEq (q : S.FSˣ) :
      R.theta (g * P.tc.aS (arch q) * h) =
        C.componentTheta j (ArtinPrimitiveRoots.A1.Spec.ptX F (p q)) := by
    rw [hOrbitGroup q]
    calc
      R.theta (P.tc.rat γ * ((b q * j) * κ q * k)) =
          R.theta (((b q * j) * κ q) * k) := R.theta_aut γ _
      _ = R.theta ((b q * j) * κ q) := R.theta_level ((b q * j) * κ q) k hk
      _ = R.theta (b q * j) := R.theta_compact (b q * j) (κ q) (hκ q)
      _ = C.componentTheta j (ArtinPrimitiveRoots.A1.Spec.ptX F (p q)) := by
        have hcoords : ArtinPrimitiveRoots.A1.Spec.coordsX F
            (ArtinPrimitiveRoots.A1.Spec.ptX F (p q)) = p q := by
          funext w
          simp [ArtinPrimitiveRoots.A1.Spec.coordsX,
            ArtinPrimitiveRoots.A1.Spec.ptX, ArtinPrimitiveRoots.A1.Spec.horiz_pt,
            ArtinPrimitiveRoots.A1.Spec.height_pt, hpHeight q w]
        have hfst : (fun w => ArtinPrimitiveRoots.A1.Spec.horiz
            (ArtinPrimitiveRoots.A1.Spec.ptX F (p q) w)) = fun w => (p q w).1 := by
          funext w
          exact congrArg Prod.fst (congrFun hcoords w)
        have hsnd : (fun w => ArtinPrimitiveRoots.A1.Spec.height
            (ArtinPrimitiveRoots.A1.Spec.ptX F (p q) w)) = fun w => (p q w).2 := by
          funext w
          exact congrArg Prod.snd (congrFun hcoords w)
        have hclassical : classicalOf P R.theta j
            (ArtinPrimitiveRoots.A1.Spec.ptX F (p q)) = R.theta (b q * j) := by
          dsimp [classicalOf, b]
          rw [hfst, hsnd]
        calc
          R.theta (b q * j) = classicalOf P R.theta j
              (ArtinPrimitiveRoots.A1.Spec.ptX F (p q)) := hclassical.symm
          _ = C.componentTheta j (ArtinPrimitiveRoots.A1.Spec.ptX F (p q)) :=
            congrFun (R.theta_component j) _
  exact ⟨j, p, hpCont, hpPos, hthetaEq⟩

end ArtinPrimitiveRoots.A1.Theta
