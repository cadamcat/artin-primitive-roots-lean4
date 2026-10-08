import ArtinPrimitiveRoots.Theta.Proofs.TH_FAMILY_FIELDS.Defs
import ArtinPrimitiveRoots.Theta.Proofs.TH_FAMILY_FIELDS.theta_uniform_adapted_lattice
import ArtinPrimitiveRoots.Theta.Proofs.TH_FAMILY_FIELDS.theta_translation_regular_fields
import ArtinPrimitiveRoots.Theta.Proofs.TH_FACTOR.thetaWhit_tail_invariance

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}
local instance residueMaximal (v : FinPlace F) : v.asIdeal.IsMaximal := v.isMaximal
local instance residueField (v : FinPlace F) : Field (𝓞 F ⧸ v.asIdeal) :=
  Ideal.Quotient.field v.asIdeal

private def thetaFourierSingleCLM (w : InfinitePlace F) :
    ℂ →L[ℝ] (InfinitePlace F → ℂ) :=
  ContinuousLinearMap.pi fun v => if v = w then ContinuousLinearMap.id ℝ ℂ else 0

private theorem thetaFourierSingleCLM_apply (w : InfinitePlace F) (z : ℂ) :
    thetaFourierSingleCLM w z = Pi.single w z := by
  funext v
  change (ContinuousLinearMap.pi (fun v : InfinitePlace F =>
    if v = w then ContinuousLinearMap.id ℝ ℂ else 0)) z v = (Pi.single w z : InfinitePlace F → ℂ) v
  rw [ContinuousLinearMap.pi_apply]
  by_cases hv : v = w <;> simp [Pi.single, hv]

private def thetaFourierRootStep (w : InfinitePlace F) (m : ℤ)
    (f : (InfinitePlace F → ℂ) → ℂ) : (InfinitePlace F → ℂ) → ℂ := fun x =>
  fderiv ℝ (fun z : ℂ => f (x + Pi.single w z)) 0 1 -
    (m : ℂ) * Complex.I * fderiv ℝ (fun z : ℂ => f (x + Pi.single w z)) 0 Complex.I

private def thetaFourierGroupStep {P : CoverPackage D S H A} (w : InfinitePlace F) (m : ℤ)
    (Ψ : P.tc.G → ℂ) : P.tc.G → ℂ := fun g =>
  fderiv ℝ (fun z : ℂ => Ψ (g * P.tc.nS
      (Multiplicative.ofAdd ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z)))) 0 1 -
    (m : ℂ) * Complex.I *
      fderiv ℝ (fun z : ℂ => Ψ (g * P.tc.nS
        (Multiplicative.ofAdd ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z)))) 0 Complex.I

private theorem nInf_add_fourier {P : CoverPackage D S H A} (x y : InfinitePlace F → ℂ) :
    nInf P (x + y) = nInf P x * nInf P y := by
  have hp : ((0 : ∀ v : S.Sf, v.1.adicCompletion F), x + y) =
      ((0, x) : S.FS) + ((0, y) : S.FS) := by
    ext v <;> simp
  change P.tc.nS (Multiplicative.ofAdd ((0 : ∀ v : S.Sf, v.1.adicCompletion F), x + y)) =
    P.tc.nS (Multiplicative.ofAdd ((0, x) : S.FS)) *
      P.tc.nS (Multiplicative.ofAdd ((0, y) : S.FS))
  rw [hp, ofAdd_add, map_mul]

private theorem thetaFamilyDeriv_fold_rootChart {P : CoverPackage D S H A}
    (m : InfinitePlace F → ℤ) (ws : List (InfinitePlace F))
    (Ψ : P.tc.G → ℂ) (g : P.tc.G) (x : InfinitePlace F → ℂ) :
    ws.foldr (fun w acc => thetaFourierGroupStep w (m w) acc) Ψ (g * nInf P x) =
      ws.foldr (fun w acc => thetaFourierRootStep w (m w) acc)
        (fun y => Ψ (g * nInf P y)) x := by
  revert x
  induction ws with
  | nil => intro x; rfl
  | cons w ws ih =>
      intro x
      have hcurve :
          (fun z : ℂ => ws.foldr (fun w acc => thetaFourierGroupStep w (m w) acc) Ψ
            (g * nInf P x * P.tc.nS (Multiplicative.ofAdd
              ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z)))) =
          (fun z => ws.foldr (fun w acc => thetaFourierRootStep w (m w) acc)
            (fun y => Ψ (g * nInf P y)) (x + Pi.single w z)) := by
        funext z
        have hsingle : P.tc.nS (Multiplicative.ofAdd
            ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z)) =
            nInf P (Pi.single w z) := rfl
        rw [mul_assoc, hsingle, ← nInf_add_fourier]
        exact ih (x + Pi.single w z)
      change thetaFourierGroupStep w (m w)
          (ws.foldr (fun w acc => thetaFourierGroupStep w (m w) acc) Ψ) (g * nInf P x) =
        thetaFourierRootStep w (m w)
          (ws.foldr (fun w acc => thetaFourierRootStep w (m w) acc)
            (fun y => Ψ (g * nInf P y))) x
      simp only [thetaFourierGroupStep, thetaFourierRootStep]
      rw [hcurve]

private theorem thetaFourierRootStep_congr (w : InfinitePlace F) (m : ℤ)
    (f f' : (InfinitePlace F → ℂ) → ℂ) (U : Set (InfinitePlace F → ℂ))
    (hU : IsOpen U) (hEq : ∀ x ∈ U, f x = f' x) (x : InfinitePlace F → ℂ) (hx : x ∈ U) :
    thetaFourierRootStep w m f x = thetaFourierRootStep w m f' x := by
  let curve : ℂ → (InfinitePlace F → ℂ) := fun z => x + Pi.single w z
  have hcurveCont : Continuous curve := by
    have hEq : curve = fun z => x + thetaFourierSingleCLM w z := by
      funext z
      simp [curve, thetaFourierSingleCLM_apply]
    rw [hEq]
    fun_prop
  have hpre : IsOpen (curve ⁻¹' U) := hU.preimage hcurveCont
  have hzero : (0 : ℂ) ∈ curve ⁻¹' U := by simp [curve, hx]
  have heq : (fun z => f (curve z)) =ᶠ[𝓝 (0 : ℂ)] fun z => f' (curve z) := by
    filter_upwards [hpre.mem_nhds hzero] with z hz
    exact hEq (curve z) hz
  have hderiv := heq.fderiv_eq (𝕜 := ℝ)
  have h1 := congrArg (fun T : ℂ →L[ℝ] ℂ => T 1) hderiv
  have hI := congrArg (fun T : ℂ →L[ℝ] ℂ => T Complex.I) hderiv
  simp only [thetaFourierRootStep, curve]
  rw [h1, hI]

private theorem thetaFamilyDeriv_rootChart {P : CoverPackage D S H A}
    (m : InfinitePlace F → ℤ) (Ψ : P.tc.G → ℂ) (g : P.tc.G) :
    thetaFamilyDeriv P m Ψ g =
      ((Finset.univ : Finset (InfinitePlace F)).toList).foldr
        (fun w acc => thetaFourierRootStep w (m w) acc) (fun x => Ψ (g * nInf P x)) 0 := by
  have h := thetaFamilyDeriv_fold_rootChart m
    (Finset.univ : Finset (InfinitePlace F)).toList Ψ g 0
  change ((Finset.univ : Finset (InfinitePlace F)).toList).foldr
      (fun w acc => thetaFourierGroupStep w (m w) acc) Ψ g =
    ((Finset.univ : Finset (InfinitePlace F)).toList).foldr
      (fun w acc => thetaFourierRootStep w (m w) acc) (fun x => Ψ (g * nInf P x)) 0
  have hzero : P.tc.nS (Multiplicative.ofAdd
      ((0 : ∀ v : S.Sf, v.1.adicCompletion F), (0 : InfinitePlace F → ℂ))) = 1 := by
    change P.tc.nS (1 : Multiplicative S.FS) = 1
    exact map_one P.tc.nS
  simpa [nInf, hzero] using h

theorem thetaFamilyDeriv_congr_rootOrbit {P : CoverPackage D S H A}
    (m : InfinitePlace F → ℤ) (Ψ Φ : P.tc.G → ℂ) (g h : P.tc.G)
    (U : Set (InfinitePlace F → ℂ)) (hU : IsOpen U) (h0 : (0 : InfinitePlace F → ℂ) ∈ U)
    (hEq : ∀ x ∈ U, Ψ (g * nInf P x) = Φ (h * nInf P x)) :
    thetaFamilyDeriv P m Ψ g = thetaFamilyDeriv P m Φ h := by
  have hfold (ws : List (InfinitePlace F)) :
      ∀ x ∈ U,
        ws.foldr (fun w acc => thetaFourierRootStep w (m w) acc)
          (fun y => Ψ (g * nInf P y)) x =
        ws.foldr (fun w acc => thetaFourierRootStep w (m w) acc)
          (fun y => Φ (h * nInf P y)) x := by
    induction ws with
    | nil => exact hEq
    | cons w ws ih =>
        intro x hx
        exact thetaFourierRootStep_congr w (m w)
          (ws.foldr (fun w acc => thetaFourierRootStep w (m w) acc)
            (fun y => Ψ (g * nInf P y)))
          (ws.foldr (fun w acc => thetaFourierRootStep w (m w) acc)
            (fun y => Φ (h * nInf P y))) U hU (fun y hy => ih y hy) x hx
  rw [thetaFamilyDeriv_rootChart, thetaFamilyDeriv_rootChart]
  exact hfold (Finset.univ : Finset (InfinitePlace F)).toList 0 h0

private theorem thetaFourier_residue_rep (v : FinPlace F) (x : F) (a b : 𝓞 F)
    (hb : b ∉ v.asIdeal)
    (hab : x * algebraMap (𝓞 F) F b = algebraMap (𝓞 F) F a) :
    residue v x = Ideal.Quotient.mk v.asIdeal a / Ideal.Quotient.mk v.asIdeal b := by
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  have hex : ∃ ab : 𝓞 F × 𝓞 F, ab.2 ∉ v.asIdeal ∧
      x * algebraMap (𝓞 F) F ab.2 = algebraMap (𝓞 F) F ab.1 := ⟨(a, b), hb, hab⟩
  have hcross : hex.choose.1 * b = a * hex.choose.2 := by
    apply (IsFractionRing.injective (𝓞 F) F)
    simp only [map_mul]
    rw [← hex.choose_spec.2, ← hab]
    ring
  have hqcross := congrArg (Ideal.Quotient.mk v.asIdeal) hcross
  have hbq : Ideal.Quotient.mk v.asIdeal b ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hb
  have hdq : Ideal.Quotient.mk v.asIdeal hex.choose.2 ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hex.choose_spec.1
  unfold residue
  rw [dif_pos hex, ← div_eq_mul_inv, div_eq_div_iff hdq hbq]
  simpa only [map_mul] using hqcross

private theorem thetaFourier_residue_ne_zero_of_valuation_one (v : FinPlace F) (x : F)
    (hx : HeightOneSpectrum.valuation F v x = 1) : residue v x ≠ 0 := by
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  have hle : HeightOneSpectrum.valuation F v x ≤ 1 := by rw [hx]
  obtain ⟨a, b, hab⟩ := v.exists_primeCompl_mul_eq_of_integer x hle
  have hbval : HeightOneSpectrum.valuation F v (algebraMap (𝓞 F) F b.val) = 1 :=
    (v.valuation_eq_one_iff_notMem (K := F) (r := b.val)).2 b.property
  have hval : HeightOneSpectrum.valuation F v x =
      HeightOneSpectrum.valuation F v (algebraMap (𝓞 F) F a) := by
    have h := congrArg (HeightOneSpectrum.valuation F v) hab
    simpa only [map_mul, hbval, mul_one] using h
  have haVal : HeightOneSpectrum.valuation F v (algebraMap (𝓞 F) F a) = 1 := by
    rw [← hval]
    exact hx
  have haNot : a ∉ v.asIdeal :=
    (v.valuation_eq_one_iff_notMem (K := F) (r := a)).mp haVal
  rw [thetaFourier_residue_rep v x a b b.property hab]
  have haq : Ideal.Quotient.mk v.asIdeal a ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using haNot
  have hbq : Ideal.Quotient.mk v.asIdeal b.val ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using
      (Ideal.mem_primeCompl_iff.mp b.property)
  exact div_ne_zero haq hbq

private theorem thetaFourier_valuation_eq_one_of_mk_eq_one (v : FinPlace F) (x : F)
    (hx : (FinitePlace.mk v) x = 1) : HeightOneSpectrum.valuation F v x = 1 := by
  have hnorm : ‖FinitePlace.embedding v x‖ = 1 := by
    simpa only [FinitePlace.mk_apply] using hx
  rw [FinitePlace.norm_embedding'] at hnorm
  exact (WithZeroMulInt.toNNReal_eq_one_iff (HeightOneSpectrum.valuation F v x)
    (HeightOneSpectrum.absNorm_ne_zero v) (ne_of_gt (HeightOneSpectrum.one_lt_absNorm_nnreal v))).mp
      (by exact_mod_cast hnorm)

private theorem thetaFourier_psiC_neg (z : ℂ) : psiC (-z) = (psiC z)⁻¹ := by
  unfold psiC
  rw [Complex.neg_re, Complex.ofReal_neg]
  have harg : -(4 * Real.pi * Complex.I * (-(z.re) : ℂ)) =
      -(-(4 * Real.pi * Complex.I * (z.re : ℂ))) := by push_cast; ring
  rw [harg]
  simp [Complex.exp_neg]

private theorem thetaFourier_psiInf_neg_mul (ν ξ : F) :
    psiInf 1 (infEmbA (-(ν * ξ))) = (psiInf ν (infEmbA ξ))⁻¹ := by
  classical
  unfold psiInf
  conv_rhs => rw [← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro w hw
  simp [infEmbA, thetaFourier_psiC_neg]

private theorem thetaFourier_aExt_comm_nInf {P : CoverPackage D S H A}
    (ν : Fˣ) (x : S.FS) :
    P.tc.aExt ν * P.tc.nS (Multiplicative.ofAdd x) =
      P.tc.nS (Multiplicative.ofAdd x) * P.tc.aExt ν := by
  classical
  let bad : Set (FinPlace F) :=
    Function.mulSupport (fun v : FinPlace F => (FinitePlace.mk v) (ν : F)) ∪
      Function.mulSupport (fun v : FinPlace F => (FinitePlace.mk v) ((ν⁻¹ : Fˣ) : F))
  have hbad : bad.Finite := by
    exact (finitePlace_mk_hasFiniteMulSupport ν.ne_zero).union
      (finitePlace_mk_hasFiniteMulSupport (Units.ne_zero (ν⁻¹)))
  have hbadT : (bad \ (S.Sf : Set (FinPlace F))).Finite := hbad.sdiff
  let T : Finset (FinPlace F) := hbadT.toFinset
  have hT (v : FinPlace F) (hv : v ∈ T) : v ∉ S.Sf := by
    exact (Set.mem_sdiff v).mp (hbadT.mem_toFinset.mp hv) |>.2
  have hres : ∀ v : FinPlace F, v ∉ S.Sf → v ∉ T →
      residue v (ν : F) ≠ 0 ∧ residue v ((ν⁻¹ : Fˣ) : F) ≠ 0 := by
    intro v hvS hvT
    have hvbad : v ∉ bad := by
      intro hvb
      apply hvT
      exact hbadT.mem_toFinset.mpr (Set.mem_sdiff v |>.mpr ⟨hvb, hvS⟩)
    have hνnorm : (FinitePlace.mk v) (ν : F) = 1 := by
      by_contra hne
      apply hvbad
      exact Or.inl (by simpa [Function.mem_mulSupport] using hne)
    have hνinvnorm : (FinitePlace.mk v) ((ν⁻¹ : Fˣ) : F) = 1 := by
      by_contra hne
      apply hvbad
      exact Or.inr (by simpa [Function.mem_mulSupport] using hne)
    exact ⟨thetaFourier_residue_ne_zero_of_valuation_one v _
        (thetaFourier_valuation_eq_one_of_mk_eq_one v _ hνnorm),
      thetaFourier_residue_ne_zero_of_valuation_one v _
        (thetaFourier_valuation_eq_one_of_mk_eq_one v _ hνinvnorm)⟩
  obtain ⟨k, hk, hcomm, hdecomp⟩ := P.tc.aExt_split ν T
    (fun v hv => hT v hv)
    (fun v hvS hvT => hres v hvS hvT)
  let n : P.tc.G := P.tc.nS (Multiplicative.ofAdd x)
  let loc (v : FinPlace F) : P.tc.G := P.tc.a v (toLoc v ν)
  have hloc (v : FinPlace F) (hv : v ∈ T) : loc v * n = n * loc v := by
    have hvS := hT v hv
    exact P.tc.comm_S v hvS (P.tc.a v (toLoc v ν)) (P.tc.a_mem v (toLoc v ν)) n
      (P.tc.nS_mem (Multiplicative.ofAdd x))
  have hprod (l : List (FinPlace F)) (hl : ∀ v ∈ l, v ∈ T) :
      (l.map loc).prod * n = n * (l.map loc).prod := by
    induction l with
    | nil => simp
    | cons v l ih =>
        have hvT : v ∈ T := hl v (by simp)
        have hlT : ∀ v' ∈ l, v' ∈ T := fun v' hv' => hl v' (by simp [hv'])
        change (loc v * (l.map loc).prod) * n = n * (loc v * (l.map loc).prod)
        calc
          (loc v * (l.map loc).prod) * n = loc v * ((l.map loc).prod * n) := by group
          _ = loc v * (n * (l.map loc).prod) := by rw [ih hlT]
          _ = (loc v * n) * (l.map loc).prod := by group
          _ = (n * loc v) * (l.map loc).prod := by rw [hloc v hvT]
          _ = n * (loc v * (l.map loc).prod) := by group
  have hnK : k * n = n * k := P.tc.Kext_comm_S k hk n (P.tc.nS_mem (Multiplicative.ofAdd x))
  calc
    P.tc.aExt ν * n = (T.toList.map loc).prod * k * n := by rw [hdecomp]
    _ = (T.toList.map loc).prod * (n * k) := by calc
      _ = (T.toList.map loc).prod * (k * n) := by group
      _ = (T.toList.map loc).prod * (n * k) := by rw [hnK]
    _ = n * ((T.toList.map loc).prod * k) := by calc
      _ = ((T.toList.map loc).prod * n) * k := by group
      _ = (n * (T.toList.map loc).prod) * k := by
        rw [hprod T.toList (by intro v hv; exact Finset.mem_toList.mp hv)]
      _ = n * ((T.toList.map loc).prod * k) := by group
    _ = n * P.tc.aExt ν := by rw [hdecomp]

private theorem thetaFourier_nInf_diag {P : CoverPackage D S H A} (ν : Fˣ) (ξ : F) :
    nInf P (-(infEmbA ((ν : F) * ξ))) * P.tc.rat (diagGL ν) =
      P.tc.rat (diagGL ν) * nInf P (-(infEmbA ξ)) := by
  let xν : S.FS := ((0 : ∀ v : S.Sf, v.1.adicCompletion F),
    -(infEmbA ((ν : F) * ξ)))
  let xξ : S.FS := ((0 : ∀ v : S.Sf, v.1.adicCompletion F), -(infEmbA ξ))
  have hdiag (v : InfinitePlace F) : ((S.diagU ν : S.FSˣ) : S.FS).2 v =
      v.embedding (ν : F) := by
    simp [SData.diagU, SData.diag]
  have hS : nInf P (-(infEmbA ((ν : F) * ξ))) * P.tc.aS (S.diagU ν) =
      P.tc.aS (S.diagU ν) * nInf P (-(infEmbA ξ)) := by
    change P.tc.nS (Multiplicative.ofAdd xν) * P.tc.aS (S.diagU ν) =
      P.tc.aS (S.diagU ν) * P.tc.nS (Multiplicative.ofAdd xξ)
    have hxmul : xν = xξ * (S.diagU ν : S.FS) := by
      ext v
      · simp [xν, xξ, SData.diagU, SData.diag]
      · change -(infEmbA ((ν : F) * ξ) v) =
          -(infEmbA ξ v) * ((S.diagU ν : S.FS).2 v)
        rw [hdiag]
        simp [infEmbA, map_mul]
        ring
    have hLift := P.tc.liftS_na xν (S.diagU ν)
    rw [hxmul] at hLift
    simp [Units.val_inv] at hLift
    rw [← hxmul] at hLift
    exact hLift
  have hE : nInf P (-(infEmbA ξ)) * P.tc.aExt ν =
      P.tc.aExt ν * nInf P (-(infEmbA ξ)) := by
    exact (thetaFourier_aExt_comm_nInf ν xξ).symm
  calc
    nInf P (-(infEmbA ((ν : F) * ξ))) * P.tc.rat (diagGL ν) =
        nInf P (-(infEmbA ((ν : F) * ξ))) *
          (P.tc.aS (S.diagU ν) * P.tc.aExt ν) := by rw [P.tc.rat_diag]
    _ = (nInf P (-(infEmbA ((ν : F) * ξ))) * P.tc.aS (S.diagU ν)) * P.tc.aExt ν := by group
    _ = (P.tc.aS (S.diagU ν) * nInf P (-(infEmbA ξ))) * P.tc.aExt ν := by rw [hS]
    _ = P.tc.aS (S.diagU ν) * (nInf P (-(infEmbA ξ)) * P.tc.aExt ν) := by group
    _ = P.tc.aS (S.diagU ν) * (P.tc.aExt ν * nInf P (-(infEmbA ξ))) := by rw [hE]
    _ = (P.tc.aS (S.diagU ν) * P.tc.aExt ν) * nInf P (-(infEmbA ξ)) := by group
    _ = P.tc.rat (diagGL ν) * nInf P (-(infEmbA ξ)) := by rw [P.tc.rat_diag]

private theorem thetaFourier_nFin_diag {P : CoverPackage D S H A} (ν : Fˣ) (ξ : F) :
    nFin P ((ν : F) * ξ) * P.tc.rat (diagGL ν) =
      P.tc.rat (diagGL ν) * nFin P ξ := by
  have hmat : upperGL ((ν : F) * ξ) * diagGL ν = diagGL ν * upperGL ξ := by
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [upperGL, diagGL, Matrix.mul_apply] <;> ring
  have hrat : P.tc.rat (upperGL ((ν : F) * ξ)) * P.tc.rat (diagGL ν) =
      P.tc.rat (diagGL ν) * P.tc.rat (upperGL ξ) := by
    calc
      _ = P.tc.rat (upperGL ((ν : F) * ξ) * diagGL ν) := ((P.tc.rat).map_mul _ _).symm
      _ = P.tc.rat (diagGL ν * upperGL ξ) := by rw [hmat]
      _ = _ := (P.tc.rat).map_mul _ _
  change (P.tc.rat (upperGL ((ν : F) * ξ)) *
      nInf P (-(infEmbA ((ν : F) * ξ)))) * P.tc.rat (diagGL ν) =
    P.tc.rat (diagGL ν) * (P.tc.rat (upperGL ξ) * nInf P (-(infEmbA ξ)))
  calc
    _ = P.tc.rat (upperGL ((ν : F) * ξ)) *
        (nInf P (-(infEmbA ((ν : F) * ξ))) * P.tc.rat (diagGL ν)) := by group
    _ = P.tc.rat (upperGL ((ν : F) * ξ)) *
        (P.tc.rat (diagGL ν) * nInf P (-(infEmbA ξ))) := by rw [thetaFourier_nInf_diag]
    _ = (P.tc.rat (upperGL ((ν : F) * ξ)) * P.tc.rat (diagGL ν)) *
        nInf P (-(infEmbA ξ)) := by group
    _ = (P.tc.rat (diagGL ν) * P.tc.rat (upperGL ξ)) *
        nInf P (-(infEmbA ξ)) := by rw [hrat]
    _ = P.tc.rat (diagGL ν) *
        (P.tc.rat (upperGL ξ) * nInf P (-(infEmbA ξ))) := by group

/-- Export summability and the exact zero/nonzero-frequency split for the normalized residue.
Guide: sol-thin-thglobal/PROOFS.md:1204–1207.
Uses ThetaTorusFourierInput (supplied by torus_fourier_expansion), theta_constantTerm, theta_fourierCoeff, thetaWhit_nFin argument and mixed root differentiation. -/
theorem theta_fourier_expansion {P : CoverPackage D S H A}
    (hRP : HasRestrictedProductTopology P)
    {N : ThetaNormalizationInput P} {𝓛 : Finset (SChar S)}
    (B : ThetaCommonSections P N 𝓛) (Q : ThetaFamilyUpstream B) (L : SChar S) (hL : L ∈ 𝓛) (g : P.tc.G) :
    Summable (fun ν : Fˣ => thetaFamilyW B L (P.tc.rat (diagGL ν) * g)) ∧
      thetaFamilyTheta B L g = thetaFamilyThetaN B L g +
        ∑' ν : Fˣ, thetaFamilyW B L (P.tc.rat (diagGL ν) * g) := by
  classical
  let E := InfinitePlace F → ℂ
  letI : TopologicalSpace P.tc.G := P.tc.topology
  letI : IsTopologicalGroup P.tc.G := P.tc.topGroup
  have hnInf : Continuous (nInf P) := by
    unfold nInf
    exact P.nS_cont.comp (by fun_prop)
  let U : Set E := Metric.closedBall 0 (1 : ℝ)
  have hUcompact : IsCompact U := by
    change IsCompact (Metric.closedBall (0 : E) 1)
    exact isCompact_closedBall 0 1
  let rootMap : E → P.tc.G := fun x => g * nInf P x
  have hrootMap : Continuous rootMap := continuous_const.mul hnInf
  let K : Set P.tc.G := rootMap '' U
  have hK : @IsCompact P.tc.G P.tc.topology K := hUcompact.image hrootMap
  have hzero : nInf P (0 : E) = 1 := by
    change P.tc.nS (1 : Multiplicative S.FS) = 1
    exact map_one P.tc.nS
  have hzeroN : P.tc.nS (Multiplicative.ofAdd
      ((0 : ∀ v : S.Sf, v.1.adicCompletion F), (0 : E))) = 1 := by
    change P.tc.nS (1 : Multiplicative S.FS) = 1
    exact map_one P.tc.nS
  have hgK : g ∈ K := by
    refine ⟨0, ?_, ?_⟩
    · simp [U]
    · simp [rootMap, hzero]
  obtain ⟨𝔞, Pd, h𝔞, hPd, hb, hPdMeas, hψa, hfix, hper⟩ :=
    theta_uniform_adapted_lattice hRP B Q K hK
  have hfix_at (x : E) (hx : x ∈ U) :
      ∀ s, ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
        scalarOf P N.G (B.Fam.sec s).f (B.Fam.sec s).fC
          (h * ((g * nInf P x)⁻¹ * nFin P ξ * (g * nInf P x))) =
            scalarOf P N.G (B.Fam.sec s).f (B.Fam.sec s).fC h := by
    apply hfix (rootMap x) ?_
    exact ⟨x, hx, rfl⟩
  have hper_g : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ x : E,
      thetaFamilyTheta B L (nInf P (x + infEmbA ξ) * g) =
        thetaFamilyTheta B L (nInf P x * g) := hper L hL g hgK
  have hJ : JointRootSmooth P (thetaFamilyTheta B L) := by
    intro g'
    change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : E × E => (thetaNormalizationScalar N)⁻¹ *
        thetaFamilyDeriv P L.m B.C.theta (nInf P p.1 * g' * nInf P p.2))
    exact contDiff_const.mul
      (thetaFamilyDeriv_jointRootSmooth L.m B.C.theta B.C.jointRoots g')
  have hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : E => thetaFamilyTheta B L (nInf P x * g)) := by
    have hparam : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : E => (x, (0 : E))) := contDiff_id.prodMk contDiff_const
    have h := (hJ g).comp hparam
    simpa [Function.comp_def, thetaFamilyTheta, nInf, hzero, hzeroN, mul_assoc] using h
  have hHasSum := Q.torus_fourier (thetaFamilyTheta B L) g 𝔞 h𝔞 hper_g hsmooth Pd hPd hb
  have hballOpen : IsOpen (Metric.ball (0 : E) 1) := Metric.isOpen_ball
  have hzeroMem : (0 : E) ∈ Metric.ball (0 : E) 1 := by simp
  have hcoeffDual (ν : Fˣ)
      (hν : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), psiInf (ν : F) (infEmbA ξ) = 1)
      (x : E) (hx : x ∈ Metric.ball (0 : E) 1) :
      torusCoeff P B.C.theta (g * nInf P x) Pd (ν : F) =
        thetaWhit B.C (P.tc.rat (diagGL ν) * (g * nInf P x)) := by
    exact theta_fourierCoeff B.Fam B.C (g * nInf P x) 𝔞 h𝔞
      (hfix_at x (Metric.ball_subset_closedBall hx)) Pd hPd hb ν hν
  have hcoeffZero (x : E) (hx : x ∈ Metric.ball (0 : E) 1) :
      torusCoeff P B.C.theta (g * nInf P x) Pd 0 = thetaFamilyBaseN B (g * nInf P x) := by
    simpa [thetaFamilyBaseN] using theta_constantTerm B.Fam B.C (g * nInf P x)
      𝔞 h𝔞 (hfix_at x (Metric.ball_subset_closedBall hx)) Pd hPd hb
  have hcomm (ν : F) :
      torusCoeff P (thetaFamilyDeriv P L.m B.C.theta) g Pd ν =
        thetaFamilyDeriv P L.m (fun h => torusCoeff P B.C.theta h Pd ν) g :=
    Q.commutation L.m g Pd ν hb hPdMeas
  have hcoeffDualDeriv (ν : Fˣ)
      (hν : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), psiInf (ν : F) (infEmbA ξ) = 1) :
      torusCoeff P (thetaFamilyTheta B L) g Pd (ν : F) =
        thetaFamilyW B L (P.tc.rat (diagGL ν) * g) := by
    have hEq : ∀ x ∈ Metric.ball (0 : E) 1,
        torusCoeff P B.C.theta (g * nInf P x) Pd (ν : F) =
          thetaWhit B.C (P.tc.rat (diagGL ν) * g * nInf P x) := by
      intro x hx
      simpa [mul_assoc] using hcoeffDual ν hν x hx
    have hroot := thetaFamilyDeriv_congr_rootOrbit L.m
      (fun h => torusCoeff P B.C.theta h Pd (ν : F))
      (thetaWhit B.C)
      g (P.tc.rat (diagGL ν) * g) (Metric.ball (0 : E) 1) hballOpen hzeroMem hEq
    have hnormalize :
        torusCoeff P (thetaFamilyTheta B L) g Pd (ν : F) =
          (thetaNormalizationScalar N)⁻¹ *
            torusCoeff P (thetaFamilyDeriv P L.m B.C.theta) g Pd (ν : F) := by
      simp [thetaFamilyTheta, torusCoeff, integral_const_mul, mul_assoc]
      ring
    calc
      _ = (thetaNormalizationScalar N)⁻¹ *
          torusCoeff P (thetaFamilyDeriv P L.m B.C.theta) g Pd (ν : F) := hnormalize
      _ = (thetaNormalizationScalar N)⁻¹ *
          thetaFamilyDeriv P L.m (fun h => torusCoeff P B.C.theta h Pd (ν : F)) g := by
            rw [hcomm (ν : F)]
      _ = (thetaNormalizationScalar N)⁻¹ *
          thetaFamilyDeriv P L.m
            (thetaWhit B.C) (P.tc.rat (diagGL ν) * g) := by rw [hroot]
      _ = thetaFamilyW B L (P.tc.rat (diagGL ν) * g) := rfl
  have hcoeffZeroDeriv :
      torusCoeff P (thetaFamilyTheta B L) g Pd 0 = thetaFamilyThetaN B L g := by
    have hEq : ∀ x ∈ Metric.ball (0 : E) 1,
        torusCoeff P B.C.theta (g * nInf P x) Pd 0 = thetaFamilyBaseN B (g * nInf P x) :=
      hcoeffZero
    have hroot := thetaFamilyDeriv_congr_rootOrbit L.m
      (fun h => torusCoeff P B.C.theta h Pd 0) (thetaFamilyBaseN B) g g
      (Metric.ball (0 : E) 1) hballOpen hzeroMem hEq
    calc
      torusCoeff P (thetaFamilyTheta B L) g Pd 0 =
          (thetaNormalizationScalar N)⁻¹ *
            torusCoeff P (thetaFamilyDeriv P L.m B.C.theta) g Pd 0 := by
              simp [thetaFamilyTheta, torusCoeff, integral_const_mul, mul_assoc]
              ring
      _ = (thetaNormalizationScalar N)⁻¹ *
          thetaFamilyDeriv P L.m (fun h => torusCoeff P B.C.theta h Pd 0) g := by
            rw [hcomm 0]
      _ = (thetaNormalizationScalar N)⁻¹ *
          thetaFamilyDeriv P L.m (thetaFamilyBaseN B) g := by rw [hroot]
      _ = thetaFamilyThetaN B L g := rfl
  have hOffWhit (ν : Fˣ)
      (hν : ¬ ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), psiInf (ν : F) (infEmbA ξ) = 1)
      (x : E) (hx : x ∈ Metric.ball (0 : E) 1) :
      thetaWhit B.C (P.tc.rat (diagGL ν) * (g * nInf P x)) = 0 := by
    classical
    push_neg at hν
    obtain ⟨ξ, hξ, hψξ⟩ := hν
    have hchar : psiInf 1 (infEmbA (-((ν : F) * ξ))) ≠ 1 := by
      rw [thetaFourier_psiInf_neg_mul]
      exact inv_ne_one.mpr hψξ
    let g' : P.tc.G := g * nInf P x
    let k : P.tc.G := g'⁻¹ * nFin P ξ * g'
    have hkfix : ∀ s h, scalarOf P N.G (B.Fam.sec s).f (B.Fam.sec s).fC (h * k) =
        scalarOf P N.G (B.Fam.sec s).f (B.Fam.sec s).fC h := by
      intro s h
      simpa [g', k, mul_assoc] using hfix_at x (Metric.ball_subset_closedBall hx) s ξ hξ h
    have htail := thetaWhit_tail_invariance B.Fam B.C k hkfix
    let d : P.tc.G := P.tc.rat (diagGL ν)
    have hconj : (d * g') * k = nFin P ((ν : F) * ξ) * (d * g') := by
      calc
        (d * g') * k = d * nFin P ξ * g' := by simp [d, g', k]; group
        _ = nFin P ((ν : F) * ξ) * d * g' := by
          rw [← thetaFourier_nFin_diag]
        _ = nFin P ((ν : F) * ξ) * (d * g') := by group
    have htail' : thetaWhit B.C (nFin P ((ν : F) * ξ) * (d * g')) =
        thetaWhit B.C (d * g') := by
      simpa [hconj] using htail (d * g')
    have hfinite := Q.finite_unipotent ((ν : F) * ξ) (d * g')
    have hmul : (1 - psiInf 1 (infEmbA (-((ν : F) * ξ)))) * thetaWhit B.C (d * g') = 0 := by
      have heq : thetaWhit B.C (d * g') =
          psiInf 1 (infEmbA (-((ν : F) * ξ))) * thetaWhit B.C (d * g') :=
        htail'.symm.trans hfinite
      calc
        _ = thetaWhit B.C (d * g') -
            psiInf 1 (infEmbA (-((ν : F) * ξ))) * thetaWhit B.C (d * g') := by ring
        _ = 0 := by
          have hsub : thetaWhit B.C (d * g') -
              psiInf 1 (infEmbA (-((ν : F) * ξ))) * thetaWhit B.C (d * g') =
              psiInf 1 (infEmbA (-((ν : F) * ξ))) * thetaWhit B.C (d * g') -
              psiInf 1 (infEmbA (-((ν : F) * ξ))) * thetaWhit B.C (d * g') :=
            congrArg (fun y : ℂ => y -
              psiInf 1 (infEmbA (-((ν : F) * ξ))) * thetaWhit B.C (d * g')) heq
          simpa using hsub
    have hfactor : 1 - psiInf 1 (infEmbA (-((ν : F) * ξ))) ≠ 0 := by
      intro h
      apply hchar
      exact (sub_eq_zero.mp h).symm
    rcases mul_eq_zero.mp hmul with h | h
    · exact (hfactor h).elim
    · simpa [d, g'] using h
  have hWSOff (ν : Fˣ)
      (hν : ¬ ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), psiInf (ν : F) (infEmbA ξ) = 1) :
      thetaFamilyW B L (P.tc.rat (diagGL ν) * g) = 0 := by
    have hEq : ∀ x ∈ Metric.ball (0 : E) 1,
        thetaWhit B.C (P.tc.rat (diagGL ν) * g * nInf P x) = 0 := by
      intro x hx
      simpa [mul_assoc] using hOffWhit ν hν x hx
    have hroot := thetaFamilyDeriv_congr_rootOrbit L.m (thetaWhit B.C)
      (fun _ => (0 : ℂ)) (P.tc.rat (diagGL ν) * g) 1
      (Metric.ball (0 : E) 1) hballOpen hzeroMem hEq
    have hz : thetaFamilyDeriv P L.m (fun _ => (0 : ℂ)) 1 = 0 := by
      classical
      have hfold (ws : List (InfinitePlace F)) :
          ws.foldr (fun w acc => thetaFourierGroupStep (P := P) w (L.m w) acc)
              (fun _ : P.tc.G => (0 : ℂ)) = fun _ : P.tc.G => (0 : ℂ) := by
        induction ws with
        | nil => rfl
        | cons w ws ih =>
            rw [List.foldr_cons, ih]
            funext h
            simp [thetaFourierGroupStep]
      change (((Finset.univ : Finset (InfinitePlace F)).toList.foldr
        (fun w acc => thetaFourierGroupStep (P := P) w (L.m w) acc)
        (fun _ : P.tc.G => (0 : ℂ))) 1) = 0
      rw [hfold]
    change (thetaNormalizationScalar N)⁻¹ *
      thetaFamilyDeriv P L.m (thetaWhit B.C) (P.tc.rat (diagGL ν) * g) = 0
    rw [hroot, hz]
    simp
  let Dual : Type := {ν : F // ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F),
    psiInf ν (infEmbA ξ) = 1}
  have hHasSumDual : HasSum (fun ν : Dual => torusCoeff P (thetaFamilyTheta B L) g Pd ν.1)
      (thetaFamilyTheta B L g) := hHasSum
  have hzeroDual : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), psiInf (0 : F) (infEmbA ξ) = 1 := by
    intro ξ hξ
    simp [psiInf, psiC]
  let d0 : Dual := ⟨0, hzeroDual⟩
  let I : Type := {d : Dual // d ≠ d0}
  let e : I ↪ Fˣ := ⟨fun z => Units.mk0 z.1.1 (by
      intro hz
      apply z.2
      apply Subtype.ext
      exact hz), by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun u : Fˣ => (u : F)) hxy⟩
  let W : Fˣ → ℂ := fun ν => thetaFamilyW B L (P.tc.rat (diagGL ν) * g)
  have hcoeffIpoint (z : I) :
      torusCoeff P (thetaFamilyTheta B L) g Pd z.1.1 = W (e z) := by
    have hdual : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F),
        psiInf ((e z : Fˣ) : F) (infEmbA ξ) = 1 := by
      change ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), psiInf z.1.1 (infEmbA ξ) = 1
      exact z.1.2
    have hcoeff := hcoeffDualDeriv (e z) hdual
    have heval : ((e z : Fˣ) : F) = z.1.1 := rfl
    rw [heval] at hcoeff
    simpa [W] using hcoeff
  have hsrc : Summable (fun z : I => W (e z)) := by
    have hs : Summable (fun z : I => torusCoeff P (thetaFamilyTheta B L) g Pd z.1.1) := by
      exact hHasSumDual.summable.subtype (fun d : Dual => d ≠ d0)
    exact hs.congr hcoeffIpoint
  have hzeroOutside : ∀ ν : Fˣ, ν ∉ Set.range e → W ν = 0 := by
    intro ν hνrange
    by_contra hW
    have hdual : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F),
        psiInf (ν : F) (infEmbA ξ) = 1 := by
      by_contra hnot
      exact hW (hWSOff ν hnot)
    let d : Dual := ⟨(ν : F), hdual⟩
    have hd0 : d ≠ d0 := by
      intro h
      have hval := congrArg Subtype.val h
      exact ν.ne_zero hval
    let z : I := ⟨d, hd0⟩
    have heq : e z = ν := by
      apply Units.ext
      rfl
    exact hνrange ⟨z, heq⟩
  have hsumW : Summable W :=
    (Function.Injective.summable_iff e.injective hzeroOutside).mp hsrc
  let eRange : I ≃ Set.range e := Equiv.ofInjective e e.injective
  have hTsum : (∑' ν : Fˣ, W ν) = ∑' z : I, W (e z) := by
    calc
      (∑' ν : Fˣ, W ν) = ∑' ν : Fˣ,
          Set.indicator (Set.range e) W ν := by
            apply tsum_congr
            intro ν
            by_cases hν : ν ∈ Set.range e
            · simp [hν]
            · simp [hν, hzeroOutside ν hν]
      _ = ∑' r : Set.range e, W r.1 := by rw [← tsum_subtype]
      _ = ∑' z : I, W (e z) := (eRange.tsum_eq (fun r => W r.1)).symm
  have hsplit : (∑' d : Dual, torusCoeff P (thetaFamilyTheta B L) g Pd d.1) =
      torusCoeff P (thetaFamilyTheta B L) g Pd 0 +
        ∑' z : I, torusCoeff P (thetaFamilyTheta B L) g Pd z.1.1 := by
    rw [(hHasSumDual.summable).tsum_eq_add_tsum_ite d0]
    congr 1
    have hite :
        (∑' d : Dual, ite (d = d0) 0 (torusCoeff P (thetaFamilyTheta B L) g Pd d.1)) =
          ∑' d : Dual, Set.indicator {d : Dual | d ≠ d0}
            (fun d => torusCoeff P (thetaFamilyTheta B L) g Pd d.1) d := by
      apply tsum_congr
      intro d
      by_cases hd : d = d0 <;> simp [Set.indicator_apply, hd]
    have hsubtype :
        (∑' z : I, torusCoeff P (thetaFamilyTheta B L) g Pd z.1.1) =
          ∑' d : Dual, Set.indicator {d : Dual | d ≠ d0}
            (fun d => torusCoeff P (thetaFamilyTheta B L) g Pd d.1) d := by
      change (∑' z : {d : Dual // d ∈ ({d : Dual | d ≠ d0})},
          torusCoeff P (thetaFamilyTheta B L) g Pd z.1.1) = _
      simpa only [Set.mem_setOf_eq] using tsum_subtype {d : Dual | d ≠ d0}
        (fun d => torusCoeff P (thetaFamilyTheta B L) g Pd d.1)
    exact hite.trans hsubtype.symm
  have hcoeffI : (∑' z : I, torusCoeff P (thetaFamilyTheta B L) g Pd z.1.1) =
      ∑' z : I, W (e z) := by
    apply tsum_congr
    exact hcoeffIpoint
  have hzeroCoeff : torusCoeff P (thetaFamilyTheta B L) g Pd 0 =
      thetaFamilyThetaN B L g := by
    simpa [d0] using hcoeffZeroDeriv
  refine ⟨hsumW, ?_⟩
  calc
    thetaFamilyTheta B L g =
        ∑' d : Dual, torusCoeff P (thetaFamilyTheta B L) g Pd d.1 :=
          hHasSumDual.tsum_eq.symm
    _ = torusCoeff P (thetaFamilyTheta B L) g Pd 0 +
        ∑' z : I, torusCoeff P (thetaFamilyTheta B L) g Pd z.1.1 := hsplit
    _ = thetaFamilyThetaN B L g + ∑' ν : Fˣ, W ν := by
          rw [hzeroCoeff, hcoeffI, hTsum]
    _ = thetaFamilyThetaN B L g +
        ∑' ν : Fˣ, thetaFamilyW B L (P.tc.rat (diagGL ν) * g) := by rfl
end ArtinPrimitiveRoots.A1.Theta
