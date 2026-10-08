import ArtinPrimitiveRoots.Proofs.th_family_lead_p.MatrixIwasawa
import ArtinPrimitiveRoots.Proofs.th_family_lead_p.SpecResidueBounds

set_option autoImplicit false
open NumberField Matrix
open scoped Classical MatrixGroups Matrix.Norms.Elementwise
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.majorant_sol
open ArtinPrimitiveRoots.A1 ArtinPrimitiveRoots.A1.Theta

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

private def thetaArchRPValue (P : CoverPackage D S H A)
    (c : InfinitePlace F → PGL2 ℂ) : P.RP :=
  Classical.choose (P.comp_surj (fun _ => 1) c (by simp))

private theorem thetaArchRPValue_compF (P : CoverPackage D S H A)
    (c : InfinitePlace F → PGL2 ℂ) (v : FinPlace F) :
    P.compF v (thetaArchRPValue P c) = 1 :=
  (Classical.choose_spec (P.comp_surj (fun _ => 1) c (by simp))).1 v

private theorem thetaArchRPValue_compC (P : CoverPackage D S H A)
    (c : InfinitePlace F → PGL2 ℂ) (w : InfinitePlace F) :
    P.compC w (thetaArchRPValue P c) = c w :=
  (Classical.choose_spec (P.comp_surj (fun _ => 1) c (by simp))).2 w

/-- Insert the full archimedean tuple, with every finite component equal to one. -/
def thetaArchRP (P : CoverPackage D S H A) : (InfinitePlace F → PGL2 ℂ) →* P.RP where
  toFun := thetaArchRPValue P
  map_one' := by
    apply P.comp_ext
    · intro v
      simp only [thetaArchRPValue_compF, map_one]
    · intro w
      simp only [thetaArchRPValue_compC, Pi.one_apply, map_one]
  map_mul' c d := by
    apply P.comp_ext
    · intro v
      simp only [thetaArchRPValue_compF, map_mul, mul_one]
    · intro w
      simp only [thetaArchRPValue_compC, map_mul, Pi.mul_apply]

@[simp] theorem thetaArchRP_compF (P : CoverPackage D S H A)
    (c : InfinitePlace F → PGL2 ℂ) (v : FinPlace F) :
    P.compF v (thetaArchRP P c) = 1 := thetaArchRPValue_compF P c v

@[simp] theorem thetaArchRP_compC (P : CoverPackage D S H A)
    (c : InfinitePlace F → PGL2 ℂ) (w : InfinitePlace F) :
    P.compC w (thetaArchRP P c) = c w := thetaArchRPValue_compC P c w

theorem thetaArchRP_commutes_finite (P : CoverPackage D S H A)
    (c : InfinitePlace F → PGL2 ℂ) (x : P.RP) (hx : ∀ w, P.compC w x = 1) :
    P.q (thetaArchRP P c) * P.q x = P.q x * P.q (thetaArchRP P c) := by
  have h : thetaArchRP P c * x = x * thetaArchRP P c := by
    apply P.comp_ext
    · intro v
      simp
    · intro w
      simp [hx]
  simpa only [map_mul] using congrArg P.q h

@[simp] theorem thetaArchRP_nInf (P : CoverPackage D S H A)
    (x : InfinitePlace F → ℂ) :
    P.q (thetaArchRP P (fun w => QuotientGroup.mk (upperM ℂ (x w)))) = nInf P x := by
  obtain ⟨r, hq, hF, hC⟩ := P.nS_components
    ((0 : ∀ v : S.Sf, v.1.adicCompletion F), x)
  have hr : thetaArchRP P (fun w => QuotientGroup.mk (upperM ℂ (x w))) = r := by
    apply P.comp_ext
    · intro v
      rw [thetaArchRP_compF, hF]
      split_ifs <;> simp
    · intro w
      rw [thetaArchRP_compC, hC]
  rw [hr, hq]
  rfl

private theorem theta_diagM_one : diagM ℂ (1 : ℂˣ) = (1 : GL (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagM]

private theorem thetaArchRP_atComplex (P : CoverPackage D S H A)
    (w : InfinitePlace F) (u : ℂˣ) :
    P.q (thetaArchRP P (fun w' => if w' = w then
      QuotientGroup.mk (diagM ℂ u) else 1)) = P.tc.aS (S.atComplex w u) := by
  obtain ⟨r, hq, hF, hC⟩ := P.aS_components (S.atComplex w u)
  have hr : thetaArchRP P (fun w' => if w' = w then
      QuotientGroup.mk (diagM ℂ u) else 1) = r := by
    apply P.comp_ext
    · intro v
      rw [thetaArchRP_compF, hF]
      have hu : ∀ v : S.Sf, S.compU v (S.atComplex w u) = 1 := by
        intro v
        apply Units.ext
        simp [SData.compU, SData.atComplex]
      split_ifs <;> simp [hu, (P.loc v).a_one]
    · intro w'
      rw [thetaArchRP_compC, hC]
      have hu : S.compC w' (S.atComplex w u) = if w' = w then u else 1 := by
        by_cases h : w' = w
        · subst w'
          apply Units.ext
          simp [SData.compC, SData.atComplex]
        · apply Units.ext
          simp [SData.compC, SData.atComplex, h]
      rw [hu]
      split_ifs <;> simp [theta_diagM_one]
  rw [hr, hq]

private theorem theta_list_prod_single {α M : Type} [Monoid M] [DecidableEq α]
    (l : List α) (hl : l.Nodup) (a : α) (ha : a ∈ l) (m : M) :
    (l.map fun b => if b = a then m else 1).prod = m := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    rcases List.nodup_cons.mp hl with ⟨hb, hl⟩
    simp only [List.mem_cons] at ha
    by_cases h : b = a
    · subst b
      have htail : (l.map fun b => if b = a then m else 1).prod = 1 := by
        apply List.prod_eq_one
        intro x hx
        rcases List.mem_map.mp hx with ⟨c, hc, rfl⟩
        have hne : c ≠ a := fun hca => hb (hca ▸ hc)
        simp [hne]
      simp [htail]
    · have ha' : a ∈ l := by
        rcases ha with hEq | hmem
        · exact (h hEq.symm).elim
        · exact hmem
      simp only [List.map_cons, List.prod_cons, if_neg h, one_mul]
      exact ih hl ha'

@[simp] theorem thetaArchRP_aInf (P : CoverPackage D S H A)
    (y : InfinitePlace F → ℝ) (hy : ∀ w, 0 < y w) :
    P.q (thetaArchRP P (fun w => QuotientGroup.mk
      (diagM ℂ (Units.mk0 (y w : ℂ) (Complex.ofReal_ne_zero.mpr (hy w).ne'))))) =
        aInf P y := by
  let c : InfinitePlace F → PGL2 ℂ := fun w => QuotientGroup.mk
    (diagM ℂ (Units.mk0 (y w : ℂ) (Complex.ofReal_ne_zero.mpr (hy w).ne')))
  let l := (Finset.univ : Finset (InfinitePlace F)).toList
  have hc : c = (l.map fun w => fun w' => if w' = w then c w else 1).prod := by
    funext w'
    simp only [Pi.list_prod_apply, List.map_map]
    change c w' = (l.map fun w => if w' = w then c w else 1).prod
    have he : (fun w => if w' = w then c w else 1) =
        fun w => if w = w' then c w' else 1 := by
      funext w
      by_cases h : w = w'
      · simp [h]
      · simp [h, Ne.symm h]
    rw [he]
    exact (theta_list_prod_single l (Finset.nodup_toList _)
      w' (Finset.mem_toList.mpr (Finset.mem_univ w')) (c w')).symm
  change P.q (thetaArchRP P c) = _
  rw [hc, map_list_prod, map_list_prod]
  simp only [List.map_map, Function.comp_apply]
  unfold aInf
  rw [dif_pos hy]
  apply congrArg List.prod
  apply List.map_congr_left
  intro w hw
  exact thetaArchRP_atComplex P w
    (Units.mk0 (y w : ℂ) (Complex.ofReal_ne_zero.mpr (hy w).ne'))

/-- The archimedean insertion identifies the spherical residue with its smooth matrix formula. -/
theorem theta_residue_component_matrix_formula
    [IsTotallyComplex F] {P : CoverPackage D S H A} {G : GlobalDatum P}
    {I : ContinuedEisInput P G} {C : ContinuedEisComponents I}
    (R : ContinuedEisReconstruction C) (j : C.J) :
    (∀ g : InfinitePlace F → GL (Fin 2) ℂ,
      R.theta (P.q (thetaArchRP P (fun w => QuotientGroup.mk (g w))) * j) =
        C.componentTheta j (ArtinPrimitiveRoots.A1.Spec.ptX F
          (thetaMatrixCoords (fun w => (g w : Matrix (Fin 2) (Fin 2) ℂ))))) ∧
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun m => C.componentTheta j (ArtinPrimitiveRoots.A1.Spec.ptX F
        (thetaMatrixCoords m))) thetaMatrixRegion := by
  constructor
  · intro g
    have hi : ∀ w : InfinitePlace F,
        ∃ hy : 0 < (thetaMatrixCoord (g w : Matrix (Fin 2) (Fin 2) ℂ)).2,
          ∃ k : GL (Fin 2) ℂ,
            (k : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
            (QuotientGroup.mk (g w) : PGL2 ℂ) = QuotientGroup.mk
              (upperM ℂ (thetaMatrixCoord (g w : Matrix (Fin 2) (Fin 2) ℂ)).1 *
                diagM ℂ (Units.mk0
                  ((thetaMatrixCoord (g w : Matrix (Fin 2) (Fin 2) ℂ)).2 : ℂ)
                  (Complex.ofReal_ne_zero.mpr hy.ne')) * k) :=
      fun w => theta_matrix_pgl_iwasawa F (g w)
    choose hy k hk hd using hi
    let x : InfinitePlace F → ℂ := fun w =>
      (thetaMatrixCoord (g w : Matrix (Fin 2) (Fin 2) ℂ)).1
    let y : InfinitePlace F → ℝ := fun w =>
      (thetaMatrixCoord (g w : Matrix (Fin 2) (Fin 2) ℂ)).2
    let cK : InfinitePlace F → PGL2 ℂ := fun w => QuotientGroup.mk (k w)
    have hdecomp : (fun w => (QuotientGroup.mk (g w) : PGL2 ℂ)) =
        (fun w => QuotientGroup.mk (upperM ℂ (x w))) *
          (fun w => QuotientGroup.mk (diagM ℂ (Units.mk0
            (y w : ℂ) (Complex.ofReal_ne_zero.mpr (hy w).ne')))) * cK := by
      funext w
      simpa only [Pi.mul_apply, QuotientGroup.mk_mul] using hd w
    have harch : P.q (thetaArchRP P (fun w => QuotientGroup.mk (g w))) =
        nInf P x * aInf P y * P.q (thetaArchRP P cK) := by
      rw [hdecomp]
      simp only [map_mul, thetaArchRP_nInf, thetaArchRP_aInf P y hy]
    have hcompact : P.q (thetaArchRP P cK) ∈ infCompact P := by
      refine ⟨thetaArchRP P cK, rfl, ?_, ?_⟩
      · intro v
        exact thetaArchRP_compF P cK v
      · intro w
        exact ⟨k w, hk w, thetaArchRP_compC P cK w⟩
    have hcomm : P.q (thetaArchRP P cK) * j = j * P.q (thetaArchRP P cK) := by
      obtain ⟨r, hr, hC⟩ := C.finite_components j j.property
      rw [← hr]
      exact thetaArchRP_commutes_finite P cK r hC
    calc
      R.theta (P.q (thetaArchRP P (fun w => QuotientGroup.mk (g w))) * j) =
          R.theta ((nInf P x * aInf P y * j) * P.q (thetaArchRP P cK)) := by
        rw [harch, mul_assoc, hcomm, ← mul_assoc]
      _ = R.theta (nInf P x * aInf P y * j) := R.theta_compact _ _ hcompact
      _ = C.componentTheta j (ArtinPrimitiveRoots.A1.Spec.ptX F
          (thetaMatrixCoords (fun w => (g w : Matrix (Fin 2) (Fin 2) ℂ)))) := by
        have heval := congrFun (R.theta_component j)
          (ArtinPrimitiveRoots.A1.Spec.ptX F
            (thetaMatrixCoords (fun w => (g w : Matrix (Fin 2) (Fin 2) ℂ))))
        simpa [classicalOf, ArtinPrimitiveRoots.A1.Spec.ptX,
          ArtinPrimitiveRoots.A1.Spec.horiz_pt, ArtinPrimitiveRoots.A1.Spec.height_pt,
          thetaMatrixCoords, x, y, hy] using heval
  · have hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p => C.componentTheta j (ArtinPrimitiveRoots.A1.Spec.ptX F p))
        (ArtinPrimitiveRoots.A1.Spec.posSet F) := by
      dsimp [ContinuedEisComponents.componentTheta]
      apply ContDiffOn.sum
      intro i hi
      simpa only [smul_eq_mul] using
        (C.d j i).res_smooth.const_smul (C.c j i (1 / 6))
    exact hs.comp (theta_matrix_coordinates_regular (F := F)).1
      (theta_matrix_coordinates_regular (F := F)).2.1

end ArtinPrimitiveRoots.Proofs.majorant_sol
