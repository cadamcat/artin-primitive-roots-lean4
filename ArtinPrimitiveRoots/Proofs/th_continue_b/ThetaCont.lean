import ArtinPrimitiveRoots.Proofs.th_continue_b.ThetaResidual

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 256
open NumberField IsDedekindDomain
open scoped Classical ContDiff MatrixGroups
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

theorem continuedEis_theta_jointRoots_chart
    {P : CoverPackage D S H A} {G : GlobalDatum P}
    {I : ContinuedEisInput P G} {C : ContinuedEisComponents I}
    (R : ContinuedEisReconstruction C) :
    ∀ g : P.tc.G, ∃ j : C.J,
      ∃ p : ((InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) →
          ArtinPrimitiveRoots.A1.Spec.Coord F,
        ContDiff ℝ ∞ p ∧
        (∀ q, p q ∈ ArtinPrimitiveRoots.A1.Spec.posSet F) ∧
        ∀ q, R.theta (nInf P q.1 * g * nInf P q.2) =
          C.componentTheta j (ArtinPrimitiveRoots.A1.Spec.ptX F (p q)) := by
  classical
  intro g
  have hBasePoint (w : InfinitePlace F) (m : SL(2, ℂ)) :
      ArtinPrimitiveRoots.A1.Spec.pt (continuedEis_baseCoord m).1
        (continuedEis_baseCoord m).2 =
      m • ArtinPrimitiveRoots.A1.Spec.pt (0 : ℂ) (1 : ℝ) := by
    as_aux_lemma =>
      have hc := congrFun (continuedEis_coords_base_action (F := F) m) w
      have hp := congrArg (fun z : ℂ × ℝ => ArtinPrimitiveRoots.A1.Spec.pt z.1 z.2) hc
      exact hp.symm.trans (ArtinPrimitiveRoots.A1.Spec.pt_horiz_height
        (m • ArtinPrimitiveRoots.A1.Spec.pt (0 : ℂ) (1 : ℝ)))
  obtain ⟨j, γ, x0, y0, kinf, k, hy0, hkinf, hk, hg⟩ :=
    continuedEis_component_representatives C g
  obtain ⟨rKin, hqKin, hFKin, hCKin⟩ := hkinf
  let kSL (w : InfinitePlace F) : SL(2, ℂ) :=
    continuedEis_slLiftPGL (P.compC w rKin)
  have hkSL (w : InfinitePlace F) :
      Matrix.SpecialLinearGroup.toPGL (kSL w) = P.compC w rKin :=
    continuedEis_slLiftPGL_toPGL (P.compC w rKin)
  let d (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ))
      (w : InfinitePlace F) : SL(2, ℂ) :=
    continuedEis_conjugateRoot (Matrix.GeneralLinearGroup.map w.embedding γ) (q.1 w)
  let M (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ))
      (w : InfinitePlace F) : SL(2, ℂ) :=
    d q w * ArtinPrimitiveRoots.A1.Spec.ptMat (x0 w) (y0 w) (hy0 w) *
      kSL w * ArtinPrimitiveRoots.A1.Spec.upperHom ℂ
        (@Multiplicative.ofAdd ℂ (q.2 w))
  let base : ArtinPrimitiveRoots.A1.Spec.X F := fun _ =>
    ArtinPrimitiveRoots.A1.Spec.pt (0 : ℂ) (1 : ℝ)
  let orbit (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) :
      ArtinPrimitiveRoots.A1.Spec.X F :=
    ArtinPrimitiveRoots.A1.Spec.actAtPlaces F (M q) base
  let p (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) :
      ArtinPrimitiveRoots.A1.Spec.Coord F := fun w => continuedEis_baseCoord (M q w)
  have hMentry : ∀ w i j, ContDiff ℝ ∞ (fun q :
      (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ) => M q w i j) := by
    intro w i j
    have hx : ContDiff ℝ ∞ (fun q :
        (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ) => q.1 w) :=
      (contDiff_apply ℝ ℂ w).comp contDiff_fst
    have hy : ContDiff ℝ ∞ (fun q :
        (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ) => q.2 w) :=
      (contDiff_apply ℝ ℂ w).comp contDiff_snd
    have hEntries := continuedEis_jointMatrix_contDiff
      (Matrix.GeneralLinearGroup.map w.embedding γ)
      (ArtinPrimitiveRoots.A1.Spec.ptMat (x0 w) (y0 w) (hy0 w) * kSL w)
      (fun q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ) => q.1 w)
      (fun q => q.2 w) hx hy
    simpa only [M, d, mul_assoc] using hEntries i j
  have hpSmooth : ContDiff ℝ ∞ p := by
    rw [contDiff_pi]
    intro w
    exact continuedEis_baseCoord_contDiff (fun q => M q w)
      (fun i j => hMentry w i j)
  have hpPos (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) :
      p q ∈ ArtinPrimitiveRoots.A1.Spec.posSet F := by
    intro w
    exact inv_pos.mpr (continuedEis_baseDen_pos (M q w))
  have hpHeight (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) :
      ∀ w, 0 < (p q w).2 := by
    simpa [ArtinPrimitiveRoots.A1.Spec.posSet] using hpPos q
  have hptX (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) :
      ArtinPrimitiveRoots.A1.Spec.ptX F (p q) = orbit q := by
    funext w
    exact hBasePoint w (M q w)
  let b (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) : P.tc.G :=
    nInf P (fun w => (p q w).1) * aInf P (fun w => (p q w).2)
  let rB (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) : P.RP :=
    continuedEis_rootRep P (fun w => (p q w).1) *
      continuedEis_archRep P (fun w => (p q w).2) (hpHeight q)
  have hqB (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) :
      P.q (rB q) = b q := by
    change P.q (continuedEis_rootRep P (fun w => (p q w).1) *
        continuedEis_archRep P (fun w => (p q w).2) (hpHeight q)) = _
    rw [map_mul, continuedEis_rootRep_q, continuedEis_archRep_q]
  have hFB (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) (v : FinPlace F) :
      P.compF v (rB q) = 1 := by
    change P.compF v (continuedEis_rootRep P (fun w => (p q w).1) *
        continuedEis_archRep P (fun w => (p q w).2) (hpHeight q)) = _
    rw [map_mul, continuedEis_rootRep_compF, continuedEis_archRep_compF]
    simp
  have hCB (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ))
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
  let rA (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) : P.RP :=
    (P.ratRP γ)⁻¹ * continuedEis_rootRep P q.1 * P.ratRP γ *
      continuedEis_rootRep P x0 * continuedEis_archRep P y0 hy0 * rKin *
      continuedEis_rootRep P q.2
  have hqA (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) :
      P.q (rA q) = (P.tc.rat γ)⁻¹ * nInf P q.1 * P.tc.rat γ *
        nInf P x0 * aInf P y0 * kinf * nInf P q.2 := by
    simp [rA, map_mul, map_inv, P.q_ratRP, continuedEis_rootRep_q,
      continuedEis_archRep_q, hqKin]
  have hFA (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) (v : FinPlace F) :
      P.compF v (rA q) = 1 := by
    simp [rA, map_mul, map_inv, P.compF_ratRP, continuedEis_rootRep_compF,
      continuedEis_archRep_compF, hFKin]
  have hCA (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ))
      (w : InfinitePlace F) :
      P.compC w (rA q) = Matrix.SpecialLinearGroup.toPGL (M q w) := by
    have hd : Matrix.SpecialLinearGroup.toPGL (d q w) =
        (QuotientGroup.mk (Matrix.GeneralLinearGroup.map w.embedding γ) : PGL2 ℂ)⁻¹ *
          (QuotientGroup.mk (upperM ℂ (q.1 w)) : PGL2 ℂ) *
          (QuotientGroup.mk (Matrix.GeneralLinearGroup.map w.embedding γ) : PGL2 ℂ) := by
      have hGL : Matrix.SpecialLinearGroup.toGL (d q w) =
          (Matrix.GeneralLinearGroup.map w.embedding γ)⁻¹ * upperM ℂ (q.1 w) *
            Matrix.GeneralLinearGroup.map w.embedding γ :=
        continuedEis_conjugateRoot_toGL (Matrix.GeneralLinearGroup.map w.embedding γ) (q.1 w)
      change Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL (d q w)) =
        (Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map w.embedding γ))⁻¹ *
          Matrix.ProjGenLinGroup.mk (upperM ℂ (q.1 w)) *
          Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map w.embedding γ)
      rw [hGL]
      exact ((Matrix.ProjGenLinGroup.mk).map_mul _ _).trans
        (congrArg₂ (· * ·)
          (((Matrix.ProjGenLinGroup.mk).map_mul _ _).trans
            (congrArg (fun a => a * Matrix.ProjGenLinGroup.mk (upperM ℂ (q.1 w)))
              ((Matrix.ProjGenLinGroup.mk).map_inv _))) rfl)
    have hpt : Matrix.SpecialLinearGroup.toPGL
        (ArtinPrimitiveRoots.A1.Spec.ptMat (x0 w) (y0 w) (hy0 w)) =
        (QuotientGroup.mk (upperM ℂ (x0 w)) : PGL2 ℂ) *
          (QuotientGroup.mk (diagM ℂ (continuedEis_archUnit y0 hy0 w)) : PGL2 ℂ) := by
      have hptMat : Matrix.SpecialLinearGroup.toPGL
          (ArtinPrimitiveRoots.A1.Spec.ptMat (x0 w) (y0 w) (hy0 w)) =
          (QuotientGroup.mk (upperM ℂ (x0 w) *
            diagM ℂ (continuedEis_archUnit y0 hy0 w)) : PGL2 ℂ) := by
        change Matrix.ProjGenLinGroup.mk
            (ArtinPrimitiveRoots.A1.Spec.ptMat (x0 w) (y0 w) (hy0 w) : GL (Fin 2) ℂ) = _
        exact continuedEis_ptMat_pgl (x0 w) (y0 w) (hy0 w)
      have hptMul : (QuotientGroup.mk (upperM ℂ (x0 w) *
          diagM ℂ (continuedEis_archUnit y0 hy0 w)) : PGL2 ℂ) =
          (QuotientGroup.mk (upperM ℂ (x0 w)) : PGL2 ℂ) *
            (QuotientGroup.mk (diagM ℂ (continuedEis_archUnit y0 hy0 w)) : PGL2 ℂ) := by
        change Matrix.ProjGenLinGroup.mk
            (upperM ℂ (x0 w) * diagM ℂ (continuedEis_archUnit y0 hy0 w)) =
          Matrix.ProjGenLinGroup.mk (upperM ℂ (x0 w)) *
            Matrix.ProjGenLinGroup.mk (diagM ℂ (continuedEis_archUnit y0 hy0 w))
        exact (Matrix.ProjGenLinGroup.mk).map_mul _ _
      exact hptMat.trans hptMul
    have hAraw : P.compC w (rA q) =
        (QuotientGroup.mk (Matrix.GeneralLinearGroup.map w.embedding γ) : PGL2 ℂ)⁻¹ *
          (QuotientGroup.mk (upperM ℂ (q.1 w)) : PGL2 ℂ) *
          (QuotientGroup.mk (Matrix.GeneralLinearGroup.map w.embedding γ) : PGL2 ℂ) *
          (QuotientGroup.mk (upperM ℂ (x0 w)) : PGL2 ℂ) *
          (QuotientGroup.mk (diagM ℂ (continuedEis_archUnit y0 hy0 w)) : PGL2 ℂ) *
          P.compC w rKin * (QuotientGroup.mk (upperM ℂ (q.2 w)) : PGL2 ℂ) := by
      simp only [rA, map_mul, map_inv, P.compC_ratRP,
        continuedEis_rootRep_compC, continuedEis_archRep_compC]
    have hAmap :
        (QuotientGroup.mk (Matrix.GeneralLinearGroup.map w.embedding γ) : PGL2 ℂ)⁻¹ *
          (QuotientGroup.mk (upperM ℂ (q.1 w)) : PGL2 ℂ) *
          (QuotientGroup.mk (Matrix.GeneralLinearGroup.map w.embedding γ) : PGL2 ℂ) *
          (QuotientGroup.mk (upperM ℂ (x0 w)) : PGL2 ℂ) *
          (QuotientGroup.mk (diagM ℂ (continuedEis_archUnit y0 hy0 w)) : PGL2 ℂ) *
          P.compC w rKin * (QuotientGroup.mk (upperM ℂ (q.2 w)) : PGL2 ℂ) =
        Matrix.SpecialLinearGroup.toPGL (d q w) *
          Matrix.SpecialLinearGroup.toPGL
            (ArtinPrimitiveRoots.A1.Spec.ptMat (x0 w) (y0 w) (hy0 w)) *
          Matrix.SpecialLinearGroup.toPGL (kSL w) *
          Matrix.SpecialLinearGroup.toPGL
            (ArtinPrimitiveRoots.A1.Spec.upperHom ℂ
              (@Multiplicative.ofAdd ℂ (q.2 w))) := by
      have hDpart :
          (QuotientGroup.mk (Matrix.GeneralLinearGroup.map w.embedding γ) : PGL2 ℂ)⁻¹ *
            (QuotientGroup.mk (upperM ℂ (q.1 w)) : PGL2 ℂ) *
            (QuotientGroup.mk (Matrix.GeneralLinearGroup.map w.embedding γ) : PGL2 ℂ) =
          Matrix.SpecialLinearGroup.toPGL (d q w) := hd.symm
      have hPtpart : (QuotientGroup.mk (upperM ℂ (x0 w)) : PGL2 ℂ) *
          (QuotientGroup.mk (diagM ℂ (continuedEis_archUnit y0 hy0 w)) : PGL2 ℂ) =
          Matrix.SpecialLinearGroup.toPGL
            (ArtinPrimitiveRoots.A1.Spec.ptMat (x0 w) (y0 w) (hy0 w)) := hpt.symm
      have hKinpart : P.compC w rKin = Matrix.SpecialLinearGroup.toPGL (kSL w) :=
        (hkSL w).symm
      have hNpart : (QuotientGroup.mk (upperM ℂ (q.2 w)) : PGL2 ℂ) =
          Matrix.SpecialLinearGroup.toPGL
            (ArtinPrimitiveRoots.A1.Spec.upperHom ℂ
              (@Multiplicative.ofAdd ℂ (q.2 w))) :=
        (continuedEis_upperHom_pgl (q.2 w)).symm
      calc
        _ = (QuotientGroup.mk (Matrix.GeneralLinearGroup.map w.embedding γ) : PGL2 ℂ)⁻¹ *
              (QuotientGroup.mk (upperM ℂ (q.1 w)) : PGL2 ℂ) *
              (QuotientGroup.mk (Matrix.GeneralLinearGroup.map w.embedding γ) : PGL2 ℂ) *
              ((QuotientGroup.mk (upperM ℂ (x0 w)) : PGL2 ℂ) *
                (QuotientGroup.mk (diagM ℂ (continuedEis_archUnit y0 hy0 w)) : PGL2 ℂ)) *
              P.compC w rKin * QuotientGroup.mk (upperM ℂ (q.2 w)) :=
          continuedEis_assoc_arch_product _ _ _ _ _ _ _
        _ = _ := by
          rw [hDpart, hPtpart, hKinpart, hNpart]
          rfl
    have hMmap : Matrix.SpecialLinearGroup.toPGL (d q w) *
          Matrix.SpecialLinearGroup.toPGL
            (ArtinPrimitiveRoots.A1.Spec.ptMat (x0 w) (y0 w) (hy0 w)) *
          Matrix.SpecialLinearGroup.toPGL (kSL w) *
          Matrix.SpecialLinearGroup.toPGL
            (ArtinPrimitiveRoots.A1.Spec.upperHom ℂ
              (@Multiplicative.ofAdd ℂ (q.2 w))) =
        Matrix.SpecialLinearGroup.toPGL (M q w) := by
      change _ = Matrix.SpecialLinearGroup.toPGL
        (d q w * ArtinPrimitiveRoots.A1.Spec.ptMat (x0 w) (y0 w) (hy0 w) *
          kSL w * ArtinPrimitiveRoots.A1.Spec.upperHom ℂ
            (@Multiplicative.ofAdd ℂ (q.2 w)))
      simp only [map_mul]
    exact hAraw.trans (hAmap.trans hMmap)
  let rRes (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) : P.RP :=
    (rB q)⁻¹ * rA q
  let κ (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) : P.tc.G := P.q (rRes q)
  have hκ (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) : κ q ∈ infCompact P := by
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
  have hκcomm (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) :
      κ q * j = j * κ q := by
    have hj := C.finite_components j j.property
    have hκF : ∃ x : P.RP, P.q x = κ q ∧ ∀ v, P.compF v x = 1 := by
      refine ⟨rRes q, ?_, ?_⟩
      · rfl
      · intro v
        simp [rRes, map_mul, map_inv, hFA q v, hFB q v]
    exact (continuedEis_mixed_commute P hj hκF).symm
  have hkRoot (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) :
      k * nInf P q.2 = nInf P q.2 * k := by
    obtain ⟨rK, hqK, hKC, _⟩ := hk
    have hRoot : ∃ rU : P.RP, P.q rU = nInf P q.2 ∧ ∀ v, P.compF v rU = 1 :=
      ⟨continuedEis_rootRep P q.2, continuedEis_rootRep_q P q.2,
        continuedEis_rootRep_compF P q.2⟩
    exact continuedEis_mixed_commute P ⟨rK, hqK, hKC⟩ hRoot
  have hjKin : j * kinf = kinf * j := by
    have hj := C.finite_components j j.property
    exact continuedEis_mixed_commute P hj ⟨rKin, hqKin, hFKin⟩
  have hjRoot (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) :
      j * nInf P q.2 = nInf P q.2 * j := by
    have hj := C.finite_components j j.property
    have hRoot : ∃ rU : P.RP, P.q rU = nInf P q.2 ∧ ∀ v, P.compF v rU = 1 :=
      ⟨continuedEis_rootRep P q.2, continuedEis_rootRep_q P q.2,
        continuedEis_rootRep_compF P q.2⟩
    exact continuedEis_mixed_commute P hj hRoot
  have hjTail (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) :
      j * (kinf * nInf P q.2) = (kinf * nInf P q.2) * j := by
    calc
      j * (kinf * nInf P q.2) = (j * kinf) * nInf P q.2 := by group
      _ = (kinf * j) * nInf P q.2 := by rw [hjKin]
      _ = kinf * (j * nInf P q.2) := by group
      _ = kinf * (nInf P q.2 * j) := by rw [hjRoot q]
      _ = (kinf * nInf P q.2) * j := by group
  let δ (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) : P.tc.G :=
    (P.tc.rat γ)⁻¹ * nInf P q.1 * P.tc.rat γ
  have hconj (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) :
      nInf P q.1 * P.tc.rat γ = P.tc.rat γ * δ q := by
    dsimp [δ]
    group
  have hqA' (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) :
      P.q (rA q) = δ q * nInf P x0 * aInf P y0 * kinf * nInf P q.2 := by
    simpa [δ] using hqA q
  have hbκ (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) :
      b q * κ q = P.q (rA q) := by
    calc
      b q * κ q = P.q (rB q) * P.q (rRes q) := by rw [hqB]
      _ = P.q (rB q * rRes q) := by simp
      _ = P.q (rA q) := by simp [rRes]
  have hOrbitGroup (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) :
      nInf P q.1 * g * nInf P q.2 =
        P.tc.rat γ * ((b q * j) * κ q * k) := by
    have hMoveK :
        ((nInf P x0 * aInf P y0 * j) * kinf * k) * nInf P q.2 =
          ((nInf P x0 * aInf P y0 * j) * kinf * nInf P q.2) * k := by
      calc
        _ = (nInf P x0 * aInf P y0 * j) * kinf * (k * nInf P q.2) := by group
        _ = (nInf P x0 * aInf P y0 * j) * kinf * (nInf P q.2 * k) := by rw [hkRoot q]
        _ = _ := by group
    have hMoveJ :
        (nInf P x0 * aInf P y0 * j) * kinf * nInf P q.2 =
          (nInf P x0 * aInf P y0 * kinf * nInf P q.2) * j := by
      calc
        _ = (nInf P x0 * aInf P y0) * (j * (kinf * nInf P q.2)) := by group
        _ = (nInf P x0 * aInf P y0) * ((kinf * nInf P q.2) * j) := by rw [hjTail q]
        _ = _ := by group
    calc
      nInf P q.1 * g * nInf P q.2 =
          nInf P q.1 * (P.tc.rat γ * ((nInf P x0 * aInf P y0 * j) * kinf * k)) *
            nInf P q.2 := by rw [hg]; group
      _ =
          P.tc.rat γ * (δ q * (((nInf P x0 * aInf P y0 * j) * kinf * k) *
            nInf P q.2)) := by rw [← mul_assoc, hconj q]; group
      _ = P.tc.rat γ * (δ q *
          ((nInf P x0 * aInf P y0 * j) * kinf * nInf P q.2) * k) := by
        rw [hMoveK]
        group
      _ = P.tc.rat γ * ((P.q (rA q) * j) * k) := by
        rw [hMoveJ]
        calc
          P.tc.rat γ * (δ q * (nInf P x0 * aInf P y0 * kinf * nInf P q.2 * j) * k) =
              P.tc.rat γ * ((δ q * nInf P x0 * aInf P y0 * kinf * nInf P q.2 * j) * k) := by
            congr 1
            group
          _ = P.tc.rat γ * ((P.q (rA q) * j) * k) := by rw [← hqA' q]
      _ = P.tc.rat γ * ((b q * κ q * j) * k) := by
        rw [← hbκ q]
      _ = P.tc.rat γ * ((b q * j) * κ q * k) := by
        have horder : b q * κ q * j = b q * j * κ q := by
          calc
            b q * κ q * j = b q * (κ q * j) := by group
            _ = b q * (j * κ q) := by rw [hκcomm q]
            _ = b q * j * κ q := by group
        rw [horder]
  have hthetaEq (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) :
      R.theta (nInf P q.1 * g * nInf P q.2) =
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
  exact ⟨j, p, hpSmooth, hpPos, hthetaEq⟩

end ArtinPrimitiveRoots.A1.Theta
