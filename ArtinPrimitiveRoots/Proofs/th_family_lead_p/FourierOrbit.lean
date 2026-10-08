import ArtinPrimitiveRoots.Proofs.th_family_lead_p.FiniteUnipotentLift
import ArtinPrimitiveRoots.Theta.Res
import ArtinPrimitiveRoots.Theta.Proofs.TH_FACTOR.thetaWhit_argument_decomposition
import ArtinPrimitiveRoots.Theta.Proofs.TH_FACTOR.thetaWhit_tail_invariance
import ArtinPrimitiveRoots.Proofs.th_family_lead_p.DerivativeInvariance
import ArtinPrimitiveRoots.Theta.Proofs.TH_FAMILY_FIELDS.theta_WS_fields

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- A period-fixing conjugate of a finite unipotent is unchanged after a right archimedean
unipotent translate. This extends the section-fixing condition along the root orbit needed when
differentiating a torus coefficient. -/
theorem scalarFix_rightNInf_of_scalarFix {P : CoverPackage D S H A}
    {G : GlobalDatum P} (fv : ∀ v : FinPlace F, (P.loc v).L → (G.T v).V)
    (fc : InfinitePlace F → PGL2 ℂ → ℂ) (g : P.tc.G)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    (hfix : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
      scalarOf P G fv fc (h * (g⁻¹ * nFin P ξ * g)) = scalarOf P G fv fc h)
    (z : InfinitePlace F → ℂ) :
    ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
      scalarOf P G fv fc
        (h * ((g * nInf P z)⁻¹ * nFin P ξ * (g * nInf P z))) =
          scalarOf P G fv fc h := by
  intro ξ hξ h
  obtain ⟨xg, hqg⟩ := P.q_surj g
  obtain ⟨xFin, hqFin, -, hCFin⟩ := nFin_has_finite_only_lift P ξ
  let xC := xg⁻¹ * xFin * xg
  have hqC : P.q xC = g⁻¹ * nFin P ξ * g := by
    dsimp [xC]
    rw [(P.q).map_mul, (P.q).map_mul, (P.q).map_inv, hqg, hqFin]
  have hCC : ∀ w, P.compC w xC = 1 := by
    intro w
    dsimp [xC]
    rw [(P.compC w).map_mul, (P.compC w).map_mul, (P.compC w).map_inv, hCFin w]
    simp
  have hcomm := finite_only_commutes_with_nInf P xC hCC z
  let c := g⁻¹ * nFin P ξ * g
  have hcomm' : c * nInf P z = nInf P z * c := by
    simpa [c, ← hqC] using hcomm
  have hconj :
      (g * nInf P z)⁻¹ * nFin P ξ * (g * nInf P z) =
        g⁻¹ * nFin P ξ * g := by
    calc
      (g * nInf P z)⁻¹ * nFin P ξ * (g * nInf P z) =
          (nInf P z)⁻¹ * c * nInf P z := by dsimp [c]; group
      _ = c := by
        calc
          (nInf P z)⁻¹ * c * nInf P z = (nInf P z)⁻¹ * (c * nInf P z) := by group
          _ = (nInf P z)⁻¹ * (nInf P z * c) := by rw [hcomm']
          _ = c := by group
      _ = g⁻¹ * nFin P ξ * g := rfl
  rw [hconj]
  exact hfix ξ hξ h

/-- The archimedean unipotent parametrization is additive. -/
theorem nInf_add (P : CoverPackage D S H A) (x y : InfinitePlace F → ℂ) :
    nInf P (x + y) = nInf P x * nInf P y := by
  change P.tc.nS (Multiplicative.ofAdd ((0 : ∀ v : S.Sf, v.1.adicCompletion F), x + y)) =
    P.tc.nS (Multiplicative.ofAdd ((0 : ∀ v : S.Sf, v.1.adicCompletion F), x)) *
      P.tc.nS (Multiplicative.ofAdd ((0 : ∀ v : S.Sf, v.1.adicCompletion F), y))
  have hη : ((0 : ∀ v : S.Sf, v.1.adicCompletion F), x + y) =
      ((0 : ∀ v : S.Sf, v.1.adicCompletion F), x) +
        ((0 : ∀ v : S.Sf, v.1.adicCompletion F), y) := by
    ext <;> simp
  rw [hη, ofAdd_add, map_mul]

/-- The exterior diagonal component has trivial archimedean coordinates and commutes with
archimedean unipotents. -/
theorem aExt_comm_nInf {P : CoverPackage D S H A} (ν : Fˣ)
    (z : InfinitePlace F → ℂ) :
    P.tc.aExt ν * nInf P z = nInf P z * P.tc.aExt ν := by
  obtain ⟨xS, hqS, _, hcompS⟩ := P.aS_components (S.diagU ν)
  let xR := P.ratRP (diagGL ν)
  let xA := xS⁻¹ * xR
  have hqA : P.q xA = P.tc.aExt ν := by
    dsimp [xA, xR]
    rw [(P.q).map_mul, (P.q).map_inv, P.q_ratRP, hqS, P.tc.rat_diag]
    group
  have hdiag (w : InfinitePlace F) :
      Matrix.GeneralLinearGroup.map w.embedding (diagGL ν) =
        diagM ℂ (Units.map w.embedding.toMonoidHom ν) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagGL, diagM]
  have hcompR (w : InfinitePlace F) :
      P.compC w xR = QuotientGroup.mk (diagM ℂ (Units.map w.embedding.toMonoidHom ν)) := by
    dsimp [xR]
    rw [P.compC_ratRP, hdiag]
    rfl
  have hcompU (w : InfinitePlace F) :
      S.compC w (S.diagU ν) = Units.map w.embedding.toMonoidHom ν := by
    apply Units.ext
    rfl
  have hCA : ∀ w, P.compC w xA = 1 := by
    intro w
    dsimp [xA]
    rw [(P.compC w).map_mul, (P.compC w).map_inv, hcompS w, hcompR w]
    rw [hcompU w]
    simp
  have hcomm := finite_only_commutes_with_nInf P xA hCA z
  rw [hqA] at hcomm
  exact hcomm

/-- The S-torus acts on the archimedean root subgroup by its diagonal coordinates. -/
theorem aS_nInf_action {P : CoverPackage D S H A} (y : S.FSˣ)
    (x : InfinitePlace F → ℂ) :
    P.tc.aS y * nInf P x =
      nInf P (fun w => ((y : S.FS).2 w) * x w) * P.tc.aS y := by
  let q : S.FS := ((0 : ∀ v : S.Sf, v.1.adicCompletion F), x)
  have hmul : q * (y : S.FS) =
      ((0 : ∀ v : S.Sf, v.1.adicCompletion F), fun w => ((y : S.FS).2 w) * x w) := by
    apply Prod.ext
    · funext v
      simp [q]
    · funext w
      simp [q, mul_comm]
  have hcancel : (q * (y : S.FS)) * (y⁻¹ : S.FS) = q := by
    simp [mul_assoc]
  have hLift : P.tc.nS (Multiplicative.ofAdd (q * (y : S.FS))) * P.tc.aS y =
      P.tc.aS y * P.tc.nS (Multiplicative.ofAdd q) := by
    simpa [hcancel] using P.tc.liftS_na (q * (y : S.FS)) y
  change P.tc.aS y * P.tc.nS (Multiplicative.ofAdd q) = _
  rw [← hLift, hmul]
  rfl

/-- Rational diagonal translation conjugates `nFin` by multiplying its rational parameter. -/
theorem ratDiag_mul_nFin {P : CoverPackage D S H A} (ν : Fˣ) (ξ : F) :
    P.tc.rat (diagGL ν) * nFin P ξ =
      nFin P ((ν : F) * ξ) * P.tc.rat (diagGL ν) := by
  have hmat : diagGL ν * upperGL ξ = upperGL ((ν : F) * ξ) * diagGL ν := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagGL, upperGL, Matrix.mul_apply]
  have hx : (fun w => w.embedding (ν : F) * (-(infEmbA ξ) w)) =
      -(infEmbA ((ν : F) * ξ)) := by
    funext w
    simp [infEmbA, map_mul, mul_neg]
  have hrat : P.tc.rat (diagGL ν) * P.tc.rat (upperGL ξ) =
      P.tc.rat (upperGL ((ν : F) * ξ)) * P.tc.rat (diagGL ν) := by
    rw [← (P.tc.rat).map_mul, ← (P.tc.rat).map_mul, hmat]
  have hdiagN (x : InfinitePlace F → ℂ) :
      P.tc.rat (diagGL ν) * nInf P x =
        nInf P (fun w => w.embedding (ν : F) * x w) * P.tc.rat (diagGL ν) := by
    calc
      P.tc.rat (diagGL ν) * nInf P x =
          P.tc.aS (S.diagU ν) * P.tc.aExt ν * nInf P x := by rw [P.tc.rat_diag ν]
      _ =
          P.tc.aS (S.diagU ν) * nInf P x * P.tc.aExt ν := by
            calc
              (P.tc.aS (S.diagU ν) * P.tc.aExt ν) * nInf P x =
                  P.tc.aS (S.diagU ν) * (P.tc.aExt ν * nInf P x) := by group
              _ = P.tc.aS (S.diagU ν) * (nInf P x * P.tc.aExt ν) := by
                    rw [aExt_comm_nInf]
              _ = P.tc.aS (S.diagU ν) * nInf P x * P.tc.aExt ν := by group
      _ = nInf P (fun w => w.embedding (ν : F) * x w) *
          P.tc.aS (S.diagU ν) * P.tc.aExt ν := by
            rw [aS_nInf_action]
            congr 1
      _ = nInf P (fun w => w.embedding (ν : F) * x w) *
          P.tc.rat (diagGL ν) := by
            calc
              (nInf P (fun w => w.embedding (ν : F) * x w) * P.tc.aS (S.diagU ν)) *
                  P.tc.aExt ν =
                nInf P (fun w => w.embedding (ν : F) * x w) *
                  (P.tc.aS (S.diagU ν) * P.tc.aExt ν) := by group
              _ = nInf P (fun w => w.embedding (ν : F) * x w) *
                  P.tc.rat (diagGL ν) := by
                    exact congrArg
                      (fun v => nInf P (fun w => w.embedding (ν : F) * x w) * v)
                      (P.tc.rat_diag ν).symm
  calc
    P.tc.rat (diagGL ν) * nFin P ξ =
        P.tc.rat (diagGL ν) * P.tc.rat (upperGL ξ) *
          nInf P (-(infEmbA ξ)) := by simp [nFin, mul_assoc]
    _ = P.tc.rat (upperGL ((ν : F) * ξ)) * P.tc.rat (diagGL ν) *
          nInf P (-(infEmbA ξ)) := by rw [hrat]
    _ = P.tc.rat (upperGL ((ν : F) * ξ)) *
          nInf P (fun w => w.embedding (ν : F) * (-(infEmbA ξ) w)) *
            P.tc.rat (diagGL ν) := by
          calc
            (P.tc.rat (upperGL ((ν : F) * ξ)) * P.tc.rat (diagGL ν)) *
                nInf P (-(infEmbA ξ)) =
              P.tc.rat (upperGL ((ν : F) * ξ)) *
                (P.tc.rat (diagGL ν) * nInf P (-(infEmbA ξ))) := by group
            _ = P.tc.rat (upperGL ((ν : F) * ξ)) *
                (nInf P (fun w => w.embedding (ν : F) * (-(infEmbA ξ) w)) *
                  P.tc.rat (diagGL ν)) := by
                    exact congrArg (fun t => P.tc.rat (upperGL ((ν : F) * ξ)) * t)
                      (hdiagN (-(infEmbA ξ)))
            _ = P.tc.rat (upperGL ((ν : F) * ξ)) *
                nInf P (fun w => w.embedding (ν : F) * (-(infEmbA ξ) w)) *
                  P.tc.rat (diagGL ν) := by group
    _ = nFin P ((ν : F) * ξ) * P.tc.rat (diagGL ν) := by
          rw [hx]
          rfl

/-- A conjugate of a finite unipotent by any adelic point remains finite-only. -/
theorem ratConj_nFin_comm_nInf {P : CoverPackage D S H A}
    (g : P.tc.G) (ξ : F) (z : InfinitePlace F → ℂ) :
    (g⁻¹ * nFin P ξ * g) * nInf P z = nInf P z * (g⁻¹ * nFin P ξ * g) := by
  obtain ⟨xg, hqg⟩ := P.q_surj g
  obtain ⟨xFin, hqFin, -, hCFin⟩ := nFin_has_finite_only_lift P ξ
  let xC := xg⁻¹ * xFin * xg
  have hqC : P.q xC = g⁻¹ * nFin P ξ * g := by
    dsimp [xC]
    rw [(P.q).map_mul, (P.q).map_mul, (P.q).map_inv, hqg, hqFin]
  have hCC : ∀ w, P.compC w xC = 1 := by
    intro w
    dsimp [xC]
    rw [(P.compC w).map_mul, (P.compC w).map_mul, (P.compC w).map_inv, hCFin w]
    simp
  have h := finite_only_commutes_with_nInf P xC hCC z
  rw [hqC] at h
  exact h

private theorem psiInf_one_neg_mul (x : InfinitePlace F → ℂ) :
    psiInf 1 (-x) * psiInf 1 x = 1 := by
  simp only [psiInf, map_one, one_mul]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro w hw
  have hterm : psiC (-x w) * psiC (x w) = 1 := by
    unfold psiC
    rw [Complex.neg_re]
    rw [← Complex.exp_add]
    push_cast
    ring_nf
    simp
  exact hterm

private theorem S_e_arch_eq_psiInf (x : InfinitePlace F → ℂ) :
    S.e A ((0 : ∀ v : S.Sf, v.1.adicCompletion F), x) = psiInf 1 x := by
  simp [SData.e, psiInf]

/-- The finite-unipotent and archimedean-root laws cancel on rational upper unipotents. -/
theorem thetaWhit_ratUpper_invariant {P : CoverPackage D S H A}
    {N : ThetaNormalizationInput P} {𝓛 : Finset (SChar S)}
    (B : ThetaCommonSections P N 𝓛) (Q : ThetaFamilyUpstream B) (ξ : F) :
    ∀ g, thetaWhit B.C (P.tc.rat (upperGL ξ) * g) = thetaWhit B.C g := by
  intro g
  have hzero : nInf P (0 : InfinitePlace F → ℂ) = 1 := by
    change P.tc.nS (Multiplicative.ofAdd (0 : S.FS)) = 1
    rw [ofAdd_zero, map_one]
  have hcancel : nInf P (-(infEmbA ξ)) * nInf P (infEmbA ξ) = 1 := by
    rw [← nInf_add P (-(infEmbA ξ)) (infEmbA ξ)]
    have hsum : -(infEmbA ξ) + infEmbA ξ = (0 : InfinitePlace F → ℂ) := by simp
    rw [hsum, hzero]
  have hratio : P.tc.rat (upperGL ξ) = nFin P ξ * nInf P (infEmbA ξ) := by
    dsimp [nFin]
    calc
      P.tc.rat (upperGL ξ) = P.tc.rat (upperGL ξ) * 1 := by simp
      _ = P.tc.rat (upperGL ξ) *
          (nInf P (-(infEmbA ξ)) * nInf P (infEmbA ξ)) := by rw [hcancel]
      _ = (P.tc.rat (upperGL ξ) * nInf P (-(infEmbA ξ))) * nInf P (infEmbA ξ) := by
            group
  calc
    thetaWhit B.C (P.tc.rat (upperGL ξ) * g) =
        thetaWhit B.C ((nFin P ξ * nInf P (infEmbA ξ)) * g) := by rw [hratio]
    _ = thetaWhit B.C (nFin P ξ * (nInf P (infEmbA ξ) * g)) := by group
    _ = psiInf 1 (infEmbA (-ξ)) * thetaWhit B.C (nInf P (infEmbA ξ) * g) :=
          Q.finite_unipotent ξ (nInf P (infEmbA ξ) * g)
    _ = psiInf 1 (-(infEmbA ξ)) *
          (S.e A ((0 : ∀ v : S.Sf, v.1.adicCompletion F), infEmbA ξ) * thetaWhit B.C g) := by
            have hroot := (thetaWhit_equiv B.Fam B.C).2.1
              ((0 : ∀ v : S.Sf, v.1.adicCompletion F), infEmbA ξ) g
            change thetaWhit B.C (nInf P (infEmbA ξ) * g) = _ at hroot
            simpa [infEmbA] using
              congrArg (fun z => psiInf 1 (-(infEmbA ξ)) * z) hroot
    _ = thetaWhit B.C g := by
          rw [S_e_arch_eq_psiInf]
          calc
            psiInf 1 (-(infEmbA ξ)) * (psiInf 1 (infEmbA ξ) * thetaWhit B.C g) =
                (psiInf 1 (-(infEmbA ξ)) * psiInf 1 (infEmbA ξ)) * thetaWhit B.C g := by group
            _ = 1 * thetaWhit B.C g := by rw [psiInf_one_neg_mul]
            _ = thetaWhit B.C g := by simp

private def fourierOrbitDerivativeStep (P : CoverPackage D S H A)
    (m : InfinitePlace F → ℤ) (w : InfinitePlace F) (Ψ : P.tc.G → ℂ) : P.tc.G → ℂ :=
  fun g =>
    fderiv ℝ (fun z : ℂ => Ψ (g * nInf P (Pi.single w z))) 0 1 -
      (m w : ℂ) * Complex.I *
        fderiv ℝ (fun z : ℂ => Ψ (g * nInf P (Pi.single w z))) 0 Complex.I

private theorem fourierOrbitDerivativeStep_congr {P : CoverPackage D S H A}
    (m : InfinitePlace F → ℤ) (w : InfinitePlace F) (Ψ Ψ' : P.tc.G → ℂ)
    (g g' : P.tc.G)
    (h : ∀ z : ℂ, Ψ (g * nInf P (Pi.single w z)) =
      Ψ' (g' * nInf P (Pi.single w z))) :
    fourierOrbitDerivativeStep P m w Ψ g =
      fourierOrbitDerivativeStep P m w Ψ' g' := by
  unfold fourierOrbitDerivativeStep
  have hfun : (fun z : ℂ => Ψ (g * nInf P (Pi.single w z))) =
      fun z => Ψ' (g' * nInf P (Pi.single w z)) := funext h
  rw [hfun]

private theorem listFoldr_fourierOrbit_congr {P : CoverPackage D S H A}
    (m : InfinitePlace F → ℤ) (ws : List (InfinitePlace F))
    (Ψ Ψ' : P.tc.G → ℂ) (g : P.tc.G)
    (h : ∀ z, Ψ (g * nInf P z) = Ψ' (g * nInf P z)) :
    List.foldr (fun w acc => fourierOrbitDerivativeStep P m w acc) Ψ ws g =
      List.foldr (fun w acc => fourierOrbitDerivativeStep P m w acc) Ψ' ws g := by
  induction ws generalizing g with
  | nil =>
      have hzero : nInf P (0 : InfinitePlace F → ℂ) = 1 := by
        change P.tc.nS (Multiplicative.ofAdd (0 : S.FS)) = 1
        rw [ofAdd_zero, map_one]
      simpa [hzero] using h (0 : InfinitePlace F → ℂ)
  | cons w ws ih =>
      simp only [List.foldr_cons]
      apply fourierOrbitDerivativeStep_congr
      intro z
      apply ih
      intro y
      have hadd := nInf_add P (Pi.single w z) y
      calc
        Ψ ((g * nInf P (Pi.single w z)) * nInf P y) =
            Ψ (g * nInf P (Pi.single w z + y)) := by rw [mul_assoc, ← hadd]
        _ = Ψ' (g * nInf P (Pi.single w z + y)) := h _
        _ = Ψ' ((g * nInf P (Pi.single w z)) * nInf P y) := by
            rw [mul_assoc, ← hadd]

/-- The finite root-derivative operator depends only on values along the right archimedean
unipotent orbit through its base point. -/
theorem thetaFamilyDeriv_congr_rightNInf_orbit {P : CoverPackage D S H A}
    (m : InfinitePlace F → ℤ) (Ψ Ψ' : P.tc.G → ℂ) (g : P.tc.G)
    (h : ∀ z, Ψ (g * nInf P z) = Ψ' (g * nInf P z)) :
    thetaFamilyDeriv P m Ψ g = thetaFamilyDeriv P m Ψ' g := by
  unfold thetaFamilyDeriv
  exact listFoldr_fourierOrbit_congr m (Finset.univ.toList) Ψ Ψ' g h

private theorem listFoldr_fourierOrbit_leftTranslate {P : CoverPackage D S H A}
    (m : InfinitePlace F → ℤ) (ws : List (InfinitePlace F))
    (Ψ : P.tc.G → ℂ) (a g : P.tc.G) :
    List.foldr (fun w acc => fourierOrbitDerivativeStep P m w acc)
      (fun h => Ψ (a * h)) ws g =
    List.foldr (fun w acc => fourierOrbitDerivativeStep P m w acc)
      Ψ ws (a * g) := by
  induction ws generalizing a g with
  | nil => rfl
  | cons w ws ih =>
      simp only [List.foldr_cons]
      apply fourierOrbitDerivativeStep_congr
      intro z
      simpa [mul_assoc] using ih a (g * nInf P (Pi.single w z))

/-- Left translation of the input function commutes with the iterated right-root derivative. -/
theorem thetaFamilyDeriv_leftTranslate {P : CoverPackage D S H A}
    (m : InfinitePlace F → ℤ) (Ψ : P.tc.G → ℂ) (a g : P.tc.G) :
    thetaFamilyDeriv P m (fun h => Ψ (a * h)) g = thetaFamilyDeriv P m Ψ (a * g) := by
  unfold thetaFamilyDeriv
  exact listFoldr_fourierOrbit_leftTranslate m (Finset.univ.toList) Ψ a g

/-- Rational upper-unipotent invariance transfers from `thetaWhit` to its differentiated
Whittaker coefficient. -/
theorem thetaFamilyW_ratUpper_invariant {P : CoverPackage D S H A}
    {N : ThetaNormalizationInput P} {𝓛 : Finset (SChar S)}
    (B : ThetaCommonSections P N 𝓛) (Q : ThetaFamilyUpstream B)
    (L : SChar S) (ξ : F) :
    ∀ g, thetaFamilyW B L (P.tc.rat (upperGL ξ) * g) = thetaFamilyW B L g := by
  intro g
  have hEq : ∀ z, thetaWhit B.C (P.tc.rat (upperGL ξ) * (g * nInf P z)) =
      thetaWhit B.C (g * nInf P z) := by
    intro z
    exact thetaWhit_ratUpper_invariant B Q ξ (g * nInf P z)
  have hderiv := thetaFamilyDeriv_congr_rightNInf_orbit L.m
    (fun h => thetaWhit B.C (P.tc.rat (upperGL ξ) * h)) (thetaWhit B.C) g hEq
  have htranslate := thetaFamilyDeriv_leftTranslate L.m (thetaWhit B.C)
    (P.tc.rat (upperGL ξ)) g
  unfold thetaFamilyW
  rw [← htranslate, hderiv]

/-- The differentiated Whittaker coefficient has the expected finite-unipotent character. -/
theorem thetaFamilyW_nFin_character {P : CoverPackage D S H A}
    {N : ThetaNormalizationInput P} {𝓛 : Finset (SChar S)}
    (B : ThetaCommonSections P N 𝓛) (Q : ThetaFamilyUpstream B)
    (L : SChar S) (hL : L ∈ 𝓛) (ξ : F) :
    ∀ g, thetaFamilyW B L (nFin P ξ * g) =
      psiInf 1 (-(infEmbA ξ)) * thetaFamilyW B L g := by
  intro g
  have hRat := thetaFamilyW_ratUpper_invariant B Q L ξ
  have hS := (theta_WS_fields B L hL).1
    ((0 : ∀ v : S.Sf, v.1.adicCompletion F), -infEmbA ξ) g
  calc
    thetaFamilyW B L (nFin P ξ * g) =
        thetaFamilyW B L
          (P.tc.rat (upperGL ξ) * (nInf P (-(infEmbA ξ)) * g)) := by
            simp [nFin, mul_assoc]
    _ = thetaFamilyW B L (nInf P (-(infEmbA ξ)) * g) := hRat _
    _ = psiInf 1 (-(infEmbA ξ)) * thetaFamilyW B L g := by
          calc
            thetaFamilyW B L (nInf P (-(infEmbA ξ)) * g) =
                S.e A ((0 : ∀ v : S.Sf, v.1.adicCompletion F), -infEmbA ξ) *
                  thetaFamilyW B L g := by simpa [nInf] using hS
            _ = psiInf 1 (-(infEmbA ξ)) * thetaFamilyW B L g := by
                  rw [S_e_arch_eq_psiInf]

/-- A conjugated finite-unipotent section fixer is also a right period for the differentiated
Whittaker coefficient. -/
theorem thetaFamilyW_right_of_scalarFix {P : CoverPackage D S H A}
    {N : ThetaNormalizationInput P} {𝓛 : Finset (SChar S)}
    (B : ThetaCommonSections P N 𝓛) (L : SChar S) (g : P.tc.G) (ξ : F)
    (hfix : ∀ s h, scalarOf P N.G (B.Fam.sec s).f (B.Fam.sec s).fC
      (h * (g⁻¹ * nFin P ξ * g)) =
        scalarOf P N.G (B.Fam.sec s).f (B.Fam.sec s).fC h) :
    ∀ h, thetaFamilyW B L (h * (g⁻¹ * nFin P ξ * g)) = thetaFamilyW B L h := by
  let k := g⁻¹ * nFin P ξ * g
  have htheta := thetaWhit_tail_invariance B.Fam B.C k hfix
  have hcomm : ∀ (w : InfinitePlace F) (z : ℂ),
      k * P.tc.nS (Multiplicative.ofAdd
        ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z)) =
        P.tc.nS (Multiplicative.ofAdd
          ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z)) * k := by
    intro w z
    simpa [k, nInf] using ratConj_nFin_comm_nInf (P := P) g ξ (Pi.single w z)
  have hderiv := thetaFamilyDeriv_right_invariant P L.m (thetaWhit B.C) k htheta hcomm
  intro h
  change (thetaNormalizationScalar N)⁻¹ *
      thetaFamilyDeriv P L.m (thetaWhit B.C) (h * k) =
    (thetaNormalizationScalar N)⁻¹ * thetaFamilyDeriv P L.m (thetaWhit B.C) h
  rw [hderiv h]

/-- The Whittaker coefficient vanishes at a rational diagonal frequency that is not dual to a
period ideal fixing the family at the base point. -/
theorem thetaFamilyW_zero_of_not_dual {P : CoverPackage D S H A}
    {N : ThetaNormalizationInput P} {𝓛 : Finset (SChar S)}
    (B : ThetaCommonSections P N 𝓛) (Q : ThetaFamilyUpstream B)
    (L : SChar S) (hL : L ∈ 𝓛) (g : P.tc.G)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    (hfix : ∀ s, ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
      scalarOf P N.G (B.Fam.sec s).f (B.Fam.sec s).fC
        (h * (g⁻¹ * nFin P ξ * g)) = scalarOf P N.G (B.Fam.sec s).f (B.Fam.sec s).fC h)
    (ν : Fˣ)
    (hν : ¬ ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), psiInf (ν : F) (infEmbA ξ) = 1) :
    thetaFamilyW B L (P.tc.rat (diagGL ν) * g) = 0 := by
  classical
  push Not at hν
  rcases hν with ⟨ξ, hξ, hχ⟩
  let aν := P.tc.rat (diagGL ν)
  let k := g⁻¹ * nFin P ξ * g
  let W := thetaFamilyW B L (aν * g)
  let q := psiInf 1 (-(infEmbA ((ν : F) * ξ)))
  have hprod : q * psiInf (ν : F) (infEmbA ξ) = 1 := by
    have hEmb : infEmbA ((ν : F) * ξ) =
        fun w => w.embedding (ν : F) * (infEmbA ξ) w := by
      funext w
      simp [infEmbA, map_mul]
    dsimp [q]
    rw [hEmb]
    simpa [psiInf] using
      (psiInf_one_neg_mul (fun w => w.embedding (ν : F) * (infEmbA ξ) w))
  have hqne : q ≠ 1 := by
    intro hq
    apply hχ
    have := hprod
    rw [hq] at this
    simpa using this
  have hright := thetaFamilyW_right_of_scalarFix B L g ξ (fun s h => hfix s ξ hξ h)
  have hconj : (aν * g) * k = aν * nFin P ξ * g := by
    dsimp [aν, k]
    group
  have hdiag : aν * nFin P ξ * g = nFin P ((ν : F) * ξ) * (aν * g) := by
    dsimp [aν]
    calc
      P.tc.rat (diagGL ν) * nFin P ξ * g =
          (nFin P ((ν : F) * ξ) * P.tc.rat (diagGL ν)) * g := by
            rw [ratDiag_mul_nFin]
      _ = nFin P ((ν : F) * ξ) * (P.tc.rat (diagGL ν) * g) := by group
  have hW : W = q * W := by
    calc
      W = thetaFamilyW B L ((aν * g) * k) := (hright (aν * g)).symm
      _ = thetaFamilyW B L (aν * nFin P ξ * g) := by rw [hconj]
      _ = thetaFamilyW B L (nFin P ((ν : F) * ξ) * (aν * g)) := by rw [hdiag]
      _ = q * thetaFamilyW B L (aν * g) := thetaFamilyW_nFin_character B Q L hL
        ((ν : F) * ξ) (aν * g)
      _ = q * W := rfl
  have hmul : (q - 1) * W = 0 := by
    calc
      (q - 1) * W = q * W - W := by ring
      _ = W - W := by rw [hW.symm]
      _ = 0 := sub_self W
  rcases mul_eq_zero.mp hmul with hq | hW0
  · exact False.elim (hqne (sub_eq_zero.mp hq))
  · exact hW0

/-- Torus coefficients are complex-linear in the function. -/
theorem torusCoeff_const_mul {P : CoverPackage D S H A}
    (c : ℂ) (Ψ : P.tc.G → ℂ) (g : P.tc.G)
    (Pd : Set (InfinitePlace F → ℂ)) (ν : F) :
    torusCoeff P (fun h => c * Ψ h) g Pd ν = c * torusCoeff P Ψ g Pd ν := by
  unfold torusCoeff
  have hInt :
      (∫ x in Pd, (c * Ψ (nInf P x * g)) * psiInf (-ν) x) =
        c * (∫ x in Pd, Ψ (nInf P x * g) * psiInf (-ν) x) := by
    rw [show (fun x => (c * Ψ (nInf P x * g)) * psiInf (-ν) x) =
        fun x => c * (Ψ (nInf P x * g) * psiInf (-ν) x) by
      funext x
      ring]
    rw [integral_const_mul]
  rw [hInt]
  ring

/-- On a common adapted domain, the normalized Whittaker value is the matching Fourier
coefficient of the normalized theta function. -/
theorem thetaFamilyW_eq_torusCoeff {P : CoverPackage D S H A}
    {N : ThetaNormalizationInput P} {𝓛 : Finset (SChar S)}
    (B : ThetaCommonSections P N 𝓛) (Q : ThetaFamilyUpstream B)
    (L : SChar S) (g : P.tc.G)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (h𝔞 : 𝔞 ≠ 0)
    (Pd : Set (InfinitePlace F → ℂ))
    (hPd : IsAddFundamentalDomain
      ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom) Pd volume)
    (hPdBound : Bornology.IsBounded Pd) (hPdMeas : MeasurableSet Pd)
    (hfix : ∀ s, ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
      scalarOf P N.G (B.Fam.sec s).f (B.Fam.sec s).fC
        (h * (g⁻¹ * nFin P ξ * g)) =
          scalarOf P N.G (B.Fam.sec s).f (B.Fam.sec s).fC h)
    (ν : Fˣ) (hν : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F),
      psiInf (ν : F) (infEmbA ξ) = 1) :
    torusCoeff P (thetaFamilyTheta B L) g Pd (ν : F) =
      thetaFamilyW B L (P.tc.rat (diagGL ν) * g) := by
  let c : ℂ := (thetaNormalizationScalar N)⁻¹
  have hfixOrbit : ∀ z s ξ, ξ ∈ (𝔞 : Submodule (𝓞 F) F) → ∀ h,
      scalarOf P N.G (B.Fam.sec s).f (B.Fam.sec s).fC
        (h * ((g * nInf P z)⁻¹ * nFin P ξ * (g * nInf P z))) =
          scalarOf P N.G (B.Fam.sec s).f (B.Fam.sec s).fC h := by
    intro z s ξ hξ h
    exact scalarFix_rightNInf_of_scalarFix
      (B.Fam.sec s).f (B.Fam.sec s).fC g 𝔞 (hfix s) z ξ hξ h
  have hcoeff (z : InfinitePlace F → ℂ) :
      torusCoeff P B.C.theta (g * nInf P z) Pd (ν : F) =
        thetaWhit B.C (P.tc.rat (diagGL ν) * (g * nInf P z)) :=
    theta_fourierCoeff B.Fam B.C (g * nInf P z) 𝔞 h𝔞 (hfixOrbit z)
      Pd hPd hPdBound ν hν
  have hderiv := thetaFamilyDeriv_congr_rightNInf_orbit L.m
    (fun h => torusCoeff P B.C.theta h Pd (ν : F))
    (fun h => thetaWhit B.C (P.tc.rat (diagGL ν) * h)) g hcoeff
  have hcomm := Q.commutation L.m g Pd ν hPdBound hPdMeas
  calc
    torusCoeff P (thetaFamilyTheta B L) g Pd (ν : F) =
        c * torusCoeff P (thetaFamilyDeriv P L.m B.C.theta) g Pd (ν : F) := by
          change torusCoeff P
            (fun h => c * thetaFamilyDeriv P L.m B.C.theta h) g Pd (ν : F) = _
          exact torusCoeff_const_mul c (thetaFamilyDeriv P L.m B.C.theta) g Pd (ν : F)
    _ = c * thetaFamilyDeriv P L.m
        (fun h => torusCoeff P B.C.theta h Pd (ν : F)) g := by rw [hcomm]
    _ = c * thetaFamilyDeriv P L.m
        (fun h => thetaWhit B.C (P.tc.rat (diagGL ν) * h)) g := by
          exact congrArg (fun v : ℂ => c * v) hderiv
    _ = c * thetaFamilyDeriv P L.m (thetaWhit B.C)
        (P.tc.rat (diagGL ν) * g) := by
          exact congrArg (fun v : ℂ => c * v)
            (thetaFamilyDeriv_leftTranslate L.m (thetaWhit B.C)
              (P.tc.rat (diagGL ν)) g)
    _ = thetaFamilyW B L (P.tc.rat (diagGL ν) * g) := by
          rfl

end ArtinPrimitiveRoots.A1.Theta
