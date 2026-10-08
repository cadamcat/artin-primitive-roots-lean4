import ArtinPrimitiveRoots.Proofs.th_continue_b.TorusFiniteLevel

set_option autoImplicit false
set_option maxHeartbeats 30000
set_option maxRecDepth 128
open NumberField IsDedekindDomain
open scoped Classical Topology MatrixGroups
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

def continuedEis_archPart (S : SData F CE condη) (y : S.FSˣ) : S.FSˣ where
  val := (1, y.val.2)
  inv := (1, y.inv.2)
  val_inv := by
    apply Prod.ext
    · exact one_mul _
    · have h := congrArg (fun z : S.FS => z.2) y.val_inv
      exact h
  inv_val := by
    apply Prod.ext
    · exact one_mul _
    · have h := congrArg (fun z : S.FS => z.2) y.inv_val
      exact h

theorem continuedEis_theta_torus_local_reduction
    {P : CoverPackage D S H A} {G : GlobalDatum P}
    {I : ContinuedEisInput P G} {C : ContinuedEisComponents I}
    (R : ContinuedEisReconstruction C) (g h : P.tc.G) (y0 : S.FSˣ) :
    ∀ᶠ y in 𝓝 y0,
      R.theta (g * P.tc.aS y * h) =
        R.theta (g * P.tc.aS y0 *
          P.tc.aS (continuedEis_archPart S (y0⁻¹ * y)) * h) := by
  classical
  have hArchF (u : S.FSˣ) (v : S.Sf) :
      S.compU v (continuedEis_archPart S u) = 1 := by
    apply Units.ext
    rfl
  have hArchC (u : S.FSˣ) (w : InfinitePlace F) :
      S.compC w (continuedEis_archPart S u) = S.compC w u := by
    apply Units.ext
    rfl
  have hDiag (a b : ℂˣ) : diagM ℂ a * diagM ℂ b = diagM ℂ (a * b) := by
    apply Units.ext
    change (!![(a : ℂ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) *
      !![(b : ℂ), 0; 0, 1] = !![((a * b : ℂˣ) : ℂ), 0; 0, 1]
    rw [Matrix.mul_fin_two]
    simp only [mul_zero, zero_mul, add_zero, zero_add, mul_one, Units.val_mul]
  have hDiagRatio (a b : ℂˣ) :
      diagM ℂ (a⁻¹ * b) = (diagM ℂ a)⁻¹ * diagM ℂ b := by
    apply eq_inv_mul_iff_mul_eq.mpr
    rw [hDiag, mul_inv_cancel_left]
  have hPGLRatio (a b : ℂˣ) :
      (QuotientGroup.mk (diagM ℂ (a⁻¹ * b)) : PGL2 ℂ) =
        (QuotientGroup.mk (diagM ℂ a) : PGL2 ℂ)⁻¹ *
          (QuotientGroup.mk (diagM ℂ b) : PGL2 ℂ) := by
    change Matrix.ProjGenLinGroup.mk (diagM ℂ (a⁻¹ * b)) =
      (Matrix.ProjGenLinGroup.mk (diagM ℂ a))⁻¹ *
        Matrix.ProjGenLinGroup.mk (diagM ℂ b)
    rw [hDiagRatio, (Matrix.ProjGenLinGroup.mk).map_mul, map_inv]
  obtain ⟨rH, hqH⟩ := P.q_surj h
  obtain ⟨r0, hq0, hF0, hC0⟩ := P.aS_components y0
  filter_upwards [continuedEis_finiteTorus_eventually_level C rH y0] with y hy
  let u : S.FSˣ := continuedEis_archPart S (y0⁻¹ * y)
  obtain ⟨rA, hqA, hFA, hCA⟩ := P.aS_components u
  obtain ⟨rY, hqY, hFY, hCY⟩ := P.aS_components y
  have hFAOne (v : FinPlace F) : P.compF v rA = 1 := by
    by_cases hv : v ∈ S.Sf
    · rw [hFA v, dite_eq_left hv]
      change (P.loc v).a (S.compU ⟨v, hv⟩ (continuedEis_archPart S (y0⁻¹ * y))) = 1
      rw [hArchF, (P.loc v).a_one]
    · rw [hFA v, dite_eq_right hv]
  have hU (w : InfinitePlace F) :
      S.compC w u = (S.compC w y0)⁻¹ * S.compC w y := by
    change S.compC w (continuedEis_archPart S (y0⁻¹ * y)) = _
    rw [hArchC, map_mul, map_inv]
  let rF : P.RP := rA⁻¹ * r0⁻¹ * rY
  have hFF (v : FinPlace F) : P.compF v rF =
      if hv : v ∈ S.Sf then
        ((P.loc v).a (S.compU ⟨v, hv⟩ y0))⁻¹ *
          (P.loc v).a (S.compU ⟨v, hv⟩ y) else 1 := by
    change P.compF v (rA⁻¹ * r0⁻¹ * rY) = _
    rw [map_mul, map_mul, map_inv, map_inv, hFAOne v, hF0 v, hFY v]
    by_cases hv : v ∈ S.Sf
    · simp only [dite_eq_left hv, inv_one, one_mul]
    · simp only [dite_eq_right hv, inv_one, one_mul]
  have hCF (w : InfinitePlace F) : P.compC w rF = 1 := by
    change P.compC w (rA⁻¹ * r0⁻¹ * rY) = 1
    rw [map_mul, map_mul, map_inv, map_inv, hCA w, hC0 w, hCY w, hU w,
      hPGLRatio]
    group
  let rK : P.RP := rH⁻¹ * rF * rH
  let k : P.tc.G := P.q rK
  have hK : k ∈ levelSet P I.T0 C.hsub C.m := by
    refine ⟨rK, rfl, ?_, ?_, ?_⟩
    · intro w
      change P.compC w (rH⁻¹ * rF * rH) = 1
      rw [map_mul, map_mul, map_inv, hCF w]
      simp only [mul_one, inv_mul_cancel]
    · intro v hvT
      change P.compF v (rH⁻¹ * rF * rH) ∈ (P.loc v).Kc (C.m v)
      rw [map_mul, map_mul, map_inv, hFF v]
      by_cases hv : v ∈ S.Sf
      · rw [dite_eq_left hv]
        exact hy ⟨v, hv⟩
      · rw [dite_eq_right hv]
        simpa only [mul_one, inv_mul_cancel] using ((P.loc v).Kc (C.m v)).one_mem
    · intro v hvT
      have hv : v ∉ S.Sf := fun h => hvT (C.hsub h)
      change P.compF v (rH⁻¹ * rF * rH) ∈
        (P.tame v (fun h => hvT (C.hsub h))).Kmax
      rw [map_mul, map_mul, map_inv, hFF v, dite_eq_right hv]
      simpa only [mul_one, inv_mul_cancel] using
        (P.tame v (fun h => hvT (C.hsub h))).Kmax.one_mem
  have hFactor : P.tc.aS y = P.tc.aS y0 * P.tc.aS u * P.q rF := by
    calc
      P.tc.aS y = P.q rY := hqY.symm
      _ = P.q (r0 * rA * rF) := by
        congr 1
        dsimp only [rF]
        group
      _ = P.tc.aS y0 * P.tc.aS u * P.q rF := by
        rw [map_mul, map_mul, hq0, hqA]
  have hQK : k = h⁻¹ * P.q rF * h := by
    change P.q (rH⁻¹ * rF * rH) = _
    rw [map_mul, map_mul, map_inv, hqH]
  have hArg : g * P.tc.aS y * h =
      (g * P.tc.aS y0 * P.tc.aS u * h) * k := by
    rw [hFactor, hQK]
    group
  rw [hArg]
  exact R.theta_level (g * P.tc.aS y0 * P.tc.aS u * h) k hK

end ArtinPrimitiveRoots.A1.Theta
