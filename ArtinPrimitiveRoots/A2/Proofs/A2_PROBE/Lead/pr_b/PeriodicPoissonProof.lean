import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE.Lead.pr_b.PeriodicPoissonAux
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false
set_option maxHeartbeats 10000000
open NumberField IsDedekindDomain MeasureTheory
open ArtinPrimitiveRoots A1 A2
open ArtinPrimitiveRoots.Proofs.a2_probe_sol
open scoped Classical Topology
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.pr_b

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}

noncomputable def residueCosetEquiv (g p : S.R)
    (hspan : Ideal.span {g} = Ideal.span {p}) (hp : p ≠ 0) :
    (S.R ⧸ Ideal.span {g}) × S.R ≃ S.R := by
  classical
  let Q := S.R ⧸ Ideal.span {g}
  let qmk : S.R →+* Q := Ideal.Quotient.mk (Ideal.span {g})
  have hpMem : p ∈ Ideal.span {g} := by
    rw [hspan]
    exact Ideal.subset_span (Set.mem_singleton p)
  have hkill : qmk p = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hpMem
  let f : Q × S.R → S.R := fun z => z.1.out + p * z.2
  have hclass (r : Q) (j : S.R) : qmk (f (r, j)) = r := by
    dsimp [f, qmk]
    calc
      Ideal.Quotient.mk (Ideal.span {g}) (r.out + p * j) =
          Ideal.Quotient.mk (Ideal.span {g}) r.out +
            Ideal.Quotient.mk (Ideal.span {g}) (p * j) := by rw [map_add]
      _ = r + 0 := by rw [Ideal.Quotient.mk_out, map_mul, hkill, zero_mul]
      _ = r := by simp
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    change f x = f y at hxy
    have hr : x.1 = y.1 := by
      calc
        x.1 = qmk (f x) := (hclass x.1 x.2).symm
        _ = qmk (f y) := congrArg qmk hxy
        _ = y.1 := hclass y.1 y.2
    have hout : x.1.out = y.1.out := congrArg Quotient.out hr
    have hpj : p * x.2 = p * y.2 := by
      change x.1.out + p * x.2 = y.1.out + p * y.2 at hxy
      rw [hout] at hxy
      exact add_left_cancel hxy
    exact Prod.ext hr (mul_left_cancel₀ hp hpj)
  · intro x
    let r : Q := qmk x
    have hzero : qmk (x - r.out) = 0 := by
      dsimp [r, qmk]
      rw [map_sub, Ideal.Quotient.mk_out, sub_self]
    have hmem : x - r.out ∈ Ideal.span {p} := by
      have hmem' : x - r.out ∈ Ideal.span {g} :=
        Ideal.Quotient.eq_zero_iff_mem.mp hzero
      exact (congrArg (fun J : Ideal S.R => x - r.out ∈ J) hspan).mp hmem'
    obtain ⟨j, hj⟩ := Ideal.mem_span_singleton'.mp hmem
    refine ⟨(r, j), ?_⟩
    change r.out + p * j = x
    calc
      r.out + p * j = r.out + j * p := by rw [mul_comm]
      _ = r.out + (x - r.out) := by rw [hj]
      _ = x := by ring

theorem leadFiniteGauss_add_gen (R : ReflectionSetup D S H Bd A ϑ bc μ v0)
    (s : S.ExtIdeal) (z r : S.R) :
    ArtinPrimitiveRoots.Proofs.a2_probe_sol.leadFiniteGauss R s
        ((z : F) + (bc.gen s : F) * (r : F)) =
      ArtinPrimitiveRoots.Proofs.a2_probe_sol.leadFiniteGauss R s (z : F) := by
  classical
  let Q := ResidueRing R.exterior s
  letI : Fintype Q := R.exterior.residueFinite s
  have hgen0 : (bc.gen s : F) ≠ 0 := Units.ne_zero (bc.gen s)
  unfold ArtinPrimitiveRoots.Proofs.a2_probe_sol.leadFiniteGauss
    ArtinPrimitiveRoots.Proofs.a2_probe_sol.leadFiniteGaussAt
  simp only [finsum_eq_sum_of_fintype]
  apply Finset.sum_congr rfl
  intro d hd
  have harg :
      ((z : F) + (bc.gen s : F) * (r : F)) * (d.out : F) / (bc.gen s : F) =
        (z : F) * (d.out : F) / (bc.gen s : F) + (r : F) * (d.out : F) := by
    field_simp [hgen0] <;> ring
  calc
    chiIdealPow D s.1 (d.out : F) 1 *
        S.e A (S.diag (((z : F) + (bc.gen s : F) * (r : F)) * (d.out : F) /
          (bc.gen s : F))) =
      chiIdealPow D s.1 (d.out : F) 1 *
        (S.e A (S.diag ((z : F) * (d.out : F) / (bc.gen s : F))) *
          S.e A (S.diag ((r : F) * (d.out : F)))) := by
            rw [harg, map_add, e_add]
    _ = chiIdealPow D s.1 (d.out : F) 1 *
        S.e A (S.diag ((z : F) * (d.out : F) / (bc.gen s : F))) := by
            have hmul : (r : F) * (d.out : F) = ((r * d.out : S.R) : F) := by simp
            rw [hmul, e_diagR_one S D A (r * d.out)]
            simp

theorem additivePhase_norm_one (R : ReflectionSetup D S H Bd A ϑ bc μ v0)
    (I : S.ExtIdeal) (p : S.R)
    (hspan : Ideal.span {R.exterior.genR I} = Ideal.span {p})
    (hp : p ≠ 0) (x : S.R) :
    ‖S.e A (S.diag ((x : F) / (p : F)))‖ = 1 := by
  classical
  let Q0 := ResidueRing R.exterior I
  letI : Fintype Q0 := R.exterior.residueFinite I
  let Q := S.R ⧸ Ideal.span {p}
  let e : Q0 ≃ Q := Ideal.quotEquivOfEq hspan
  letI : Fintype Q := Fintype.ofEquiv Q0 e
  have hcard : Fintype.card Q = Ideal.absNorm I.1 := by
    calc
      Fintype.card Q = Fintype.card Q0 := (Fintype.card_congr e).symm
      _ = Ideal.absNorm I.1 := R.exterior.residue_card I
  let q : ℕ := Fintype.card Q
  have hI0 : I.1 ≠ 0 := by
    simpa only [Ideal.zero_eq_bot] using I.2.1
  have hqNat : 0 < Ideal.absNorm I.1 :=
    Ideal.absNorm_pos_of_nonZeroDivisors
      ⟨I.1, mem_nonZeroDivisors_iff_ne_zero.mpr hI0⟩
  have hqpos : 0 < q := by
    dsimp [q]
    rw [hcard]
    exact hqNat
  let qmk : S.R →+* Q := Ideal.Quotient.mk (Ideal.span {p})
  have hkill : qmk ((Fintype.card Q : S.R) * x) = 0 := by
    have hcardKill : (Fintype.card Q) • qmk x = 0 := card_nsmul_eq_zero
    calc
      qmk ((Fintype.card Q : S.R) * x) = qmk ((Fintype.card Q) • x) := by
        simp [nsmul_eq_mul]
      _ = (Fintype.card Q) • qmk x := map_nsmul qmk (Fintype.card Q) x
      _ = 0 := hcardKill
  have hmem : (Fintype.card Q : S.R) * x ∈ Ideal.span {p} :=
    Ideal.Quotient.eq_zero_iff_mem.mp hkill
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
  have hpF : (p : F) ≠ 0 := by
    intro hz
    apply hp
    exact Subtype.ext hz
  have hratio : (r : F) = (Fintype.card Q : F) * (x : F) / (p : F) := by
    have hcast := congrArg (fun y : S.R => (y : F)) hr
    change (r : F) * (p : F) = (Fintype.card Q : F) * (x : F) at hcast
    calc
      (r : F) = ((r : F) * (p : F)) / (p : F) := by field_simp [hpF]
      _ = (Fintype.card Q : F) * (x : F) / (p : F) := by rw [hcast]
  let eDiag : AddChar F ℂ := {
    toFun := fun y => S.e A (S.diag y)
    map_zero_eq_one' := by simpa using e_diagR_one S D A (0 : S.R)
    map_add_eq_mul' := by
      intro y₁ y₂
      calc
        S.e A (S.diag (y₁ + y₂)) =
            S.e A (S.diag y₁ + S.diag y₂) := by rw [map_add]
        _ = S.e A (S.diag y₁) * S.e A (S.diag y₂) := e_add S A _ _ }
  have hone : eDiag ((Fintype.card Q : F) * (x : F) / (p : F)) = 1 := by
    rw [← hratio]
    exact e_diagR_one S D A r
  have harg : (Fintype.card Q : F) * ((x : F) / (p : F)) =
      (Fintype.card Q : F) * (x : F) / (p : F) := by ring
  have hphasePow :
      eDiag ((x : F) / (p : F)) ^ Fintype.card Q = 1 := by
    have h := eDiag.map_nsmul_eq_pow (Fintype.card Q) ((x : F) / (p : F))
    have h' : eDiag ((Fintype.card Q : F) * ((x : F) / (p : F))) =
        eDiag ((x : F) / (p : F)) ^ Fintype.card Q := by
      simpa [eDiag, nsmul_eq_mul] using h
    rw [harg, hone] at h'
    exact h'.symm
  have hfin : IsOfFinOrder (eDiag ((x : F) / (p : F))) :=
    (isOfFinOrder_iff_pow_eq_one).2 ⟨Fintype.card Q, hqpos, hphasePow⟩
  exact hfin.norm_eq_one

theorem periodicPoisson
    (R : ReflectionSetup D S H Bd A ϑ bc μ v0) (sd : S.SelfDualMeasure A)
    (W : ArtinPrimitiveRoots.Proofs.a2_probe_sol.ProbeWeights (S := S))
    (hcoset : LeadCosetContract sd W) (hfinite : LeadFiniteContract R)
    (s I : S.ExtIdeal) (a : Fˣ) (ha : S.IsGen (a : F) I.1)
    (hallowed : Bd.Allowed a) (k : S.FSˣ) :
    Summable (fun m : S.R =>
      ‖(qI s.1 ^ (-(1 / 2 : ℝ)) : ℝ) *
        ArtinPrimitiveRoots.Proofs.a2_probe_sol.leadFiniteGauss R s (-(m : F)) *
        chiIdealPow D I.1 (m : F) 1 *
          W.W0 (S.diag (m : F) * (k⁻¹ : S.FSˣ).val)‖) ∧
    Summable (fun h : S.R =>
      ‖ArtinPrimitiveRoots.Proofs.a2_probe_sol.leadFiniteFactor R s I a (h : F) *
        ArtinPrimitiveRoots.Proofs.a2_probe_sol.leadFourier sd W ((k : S.FS) *
          S.diag ((h : F) / ((bc.gen s : F) * (a : F))))‖) ∧
    (∑' m : S.R,
      (qI s.1 ^ (-(1 / 2 : ℝ)) : ℝ) *
        ArtinPrimitiveRoots.Proofs.a2_probe_sol.leadFiniteGauss R s (-(m : F)) *
        chiIdealPow D I.1 (m : F) 1 *
          W.W0 (S.diag (m : F) * (k⁻¹ : S.FSˣ).val)) =
      ((S.absS (k : S.FS) /
        (qI s.1 ^ (1 / 2 : ℝ) * qI I.1) : ℝ) : ℂ) *
        ∑' h : S.R,
          ArtinPrimitiveRoots.Proofs.a2_probe_sol.leadFiniteFactor R s I a (h : F) *
            ArtinPrimitiveRoots.Proofs.a2_probe_sol.leadFourier sd W ((k : S.FS) *
              S.diag ((h : F) / ((bc.gen s : F) * (a : F)))) := by
  classical
  let total := R.exterior.mul s I
  let genS : S.R := R.exterior.genR s
  let genI : S.R := R.exterior.genR I
  let genTotal : S.R := R.exterior.genR total
  let period : Fˣ := bc.gen s * a
  have hgenPeriod : S.IsGen (period : F) total.1 := by
    dsimp [period, total]
    rw [R.exterior.mul_val]
    exact isGen_mul s.1 I.1 (bc.gen s) a (bc.gen_spec s).1 ha
  have hallowedPeriod : Bd.Allowed period := by
    change (QuotientGroup.mk (S.diagU period) : S.V) ∈ Bd.B
    rw [map_mul]
    exact Bd.B.mul_mem (bc.gen_spec s).2 hallowed
  obtain ⟨uI, huI⟩ := allowed_generator_lift R I a ha hallowed
  let aR : S.R := uI ^ 6 * genI
  have haRval : (aR : F) = (a : F) := by
    simpa [aR, genI] using huI
  have hAssocI : Associated aR genI := by
    dsimp [aR]
    exact associated_unit_mul_left genI (uI ^ 6) (uI ^ 6).isUnit
  have hspanI : Ideal.span {genI} = Ideal.span {aR} :=
    Ideal.span_singleton_eq_span_singleton.mpr hAssocI.symm
  let pR : S.R := genS * aR
  have hpval : (pR : F) = (period : F) := by
    dsimp [pR, period, genS]
    rw [R.exterior.genR_val, haRval]
  obtain ⟨ε, hε, hrel⟩ :=
    Bd.allowed_unique total.1 period (bc.gen total)
      ⟨hgenPeriod, hallowedPeriod⟩ (bc.gen_spec total)
  let epsUS : S.US := ⟨ε, hε⟩
  let epsR : S.Rˣ := Set.unitEquivUnitsInteger (S.Sf : Set (FinPlace F)) F epsUS
  have hrelF : (period : F) = ((ε : Fˣ) : F) ^ 6 * (bc.gen total : F) := by
    have h := congrArg (fun z : Fˣ => (z : F)) hrel
    simpa using h
  have hepsR : ((epsR : S.Rˣ) : F) = (ε : Fˣ) := by rfl
  have hpEq : pR = epsR ^ 6 * genTotal := by
    apply Subtype.ext
    calc
      (pR : F) = (period : F) := hpval
      _ = ((ε : Fˣ) : F) ^ 6 * (bc.gen total : F) := hrelF
      _ = ((epsR ^ 6 * genTotal : S.R) : F) := by
        simp [hepsR, genTotal, R.exterior.genR_val]
  have hAssocTotal : Associated pR genTotal := by
    rw [hpEq]
    exact associated_unit_mul_left genTotal (epsR ^ 6) (epsR ^ 6).isUnit
  have hspanTotal : Ideal.span {genTotal} = Ideal.span {pR} :=
    Ideal.span_singleton_eq_span_singleton.mpr hAssocTotal.symm
  have hpRnezero : pR ≠ 0 := by
    intro hz
    have hpF0 : (pR : F) = 0 := congrArg (fun z : S.R => (z : F)) hz
    apply Units.ne_zero period
    rw [← hpval]
    exact hpF0
  let Q := ResidueRing R.exterior total
  letI : Fintype Q := R.exterior.residueFinite total
  let E : Q × S.R ≃ S.R := residueCosetEquiv genTotal pR hspanTotal hpRnezero
  have hEapply (r : Q) (j : S.R) : E (r, j) = r.out + pR * j := by
    rfl
  have hElt (r : Q) (j : S.R) :
      ((E (r, j) : S.R) : F) = (r.out : F) + (period : F) * (j : F) := by
    rw [hEapply]
    change (r.out : F) + (pR : F) * (j : F) = _
    rw [hpval]
  let qS : ℝ := qI s.1
  let qT : ℝ := qI total.1
  have hqT : qT = qS * qI I.1 := by
    dsimp [qT, qS, qI, total]
    rw [R.exterior.mul_val, map_mul]
    norm_cast
  have absNormPos (J : Ideal (𝓞 F)) (hJ : J ≠ 0) : 0 < Ideal.absNorm J :=
    Ideal.absNorm_pos_of_nonZeroDivisors
      ⟨J, mem_nonZeroDivisors_iff_ne_zero.mpr hJ⟩
  have hs0 : s.1 ≠ 0 := by simpa only [Ideal.zero_eq_bot] using s.2.1
  have hI0 : I.1 ≠ 0 := by simpa only [Ideal.zero_eq_bot] using I.2.1
  have hqSNat : 0 < Ideal.absNorm s.1 := absNormPos s.1 hs0
  have hqSpos : 0 < qS := by
    dsimp [qS, qI]
    exact_mod_cast hqSNat
  have hqSone : 1 ≤ qS := by
    dsimp [qS, qI]
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hqSNat))
  have hqIpos : 0 < qI I.1 := by
    dsimp [qI]
    exact_mod_cast absNormPos I.1 hI0
  let coeff : S.R → ℂ := fun m =>
    (qS ^ (-(1 / 2 : ℝ)) : ℝ) *
      ArtinPrimitiveRoots.Proofs.a2_probe_sol.leadFiniteGauss R s (-(m : F)) *
        chiIdealPow D I.1 (m : F) 1
  let phase : Q → S.R → ℂ := fun r h =>
    S.e A (S.diag ((r.out : F) * (h : F) / (period : F)))
  let fourier : S.R → ℂ := fun h =>
    ArtinPrimitiveRoots.Proofs.a2_probe_sol.leadFourier sd W ((k : S.FS) *
      S.diag ((h : F) / (period : F)))
  let factor : S.R → ℂ := fun h =>
    ArtinPrimitiveRoots.Proofs.a2_probe_sol.leadFiniteFactor R s I a (h : F)
  let normW : S.R → ℝ := fun m =>
    ‖W.W0 (S.diag (m : F) * (k⁻¹ : S.FSˣ).val)‖
  let summand : S.R → ℂ := fun m => coeff m * W.W0
    (S.diag (m : F) * (k⁻¹ : S.FSˣ).val)
  have hCoeffBound (m : S.R) : ‖coeff m‖ ≤ qS := by
    have hgauss :
        ‖ArtinPrimitiveRoots.Proofs.a2_probe_sol.leadFiniteGauss R s (-(m : F))‖ ≤ qS := by
      simpa [qS] using hfinite.2 s (-m)
    have hchi : ‖chiIdealPow D I.1 (m : F) 1‖ ≤ 1 :=
      (a2_bridge_SYMBOL D S).ideal_norm_le I.1 (m : F) 1
    have hpowPos : 0 < qS ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hqSpos _
    have hpowLe : qS ^ (-(1 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hqSone (by norm_num)
    calc
      ‖coeff m‖ = qS ^ (-(1 / 2 : ℝ)) *
          ‖ArtinPrimitiveRoots.Proofs.a2_probe_sol.leadFiniteGauss R s (-(m : F))‖ *
            ‖chiIdealPow D I.1 (m : F) 1‖ := by
        dsimp [coeff]
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpowPos]
      _ ≤ 1 * qS * 1 := by gcongr
      _ = qS := by ring
  have hrowCoeff (r : Q) (j : S.R) : coeff (E (r, j)) = coeff r.out := by
    have hgauss :
        ArtinPrimitiveRoots.Proofs.a2_probe_sol.leadFiniteGauss R s
            (-((E (r, j) : S.R) : F)) =
          ArtinPrimitiveRoots.Proofs.a2_probe_sol.leadFiniteGauss R s (-(r.out : F)) := by
      have harg :
          -((r.out : F) + (period : F) * (j : F)) =
            (-(r.out : F)) + (bc.gen s : F) * (-((aR * j : S.R) : F)) := by
        rw [← hpval]
        have hpr : (pR : F) = (bc.gen s : F) * (aR : F) := by
          dsimp [pR, genS]
          rw [R.exterior.genR_val]
        rw [hpr]
        have hmul : ((aR * j : S.R) : F) = (aR : F) * (j : F) := by simp
        rw [hmul]
        ring
      rw [hElt, harg]
      simpa using leadFiniteGauss_add_gen R s (-r.out) (-(aR * j))
    have hmemA : pR * j ∈ Ideal.span {aR} := by
      apply Ideal.mem_span_singleton'.mpr
      refine ⟨genS * j, ?_⟩
      dsimp [pR]
      ring
    have hmemI : pR * j ∈ Ideal.span {genI} :=
      (congrArg (fun J : Ideal S.R => pR * j ∈ J) hspanI).mpr hmemA
    have hmem : E (r, j) - r.out ∈ Ideal.span {genI} := by
      rw [hEapply]
      have hdiff : r.out + pR * j - r.out = pR * j := by ring
      rw [hdiff]
      exact hmemI
    have hchi := chiIdealPow_eq_of_mod R I (E (r, j)) r.out hmem
    dsimp [coeff]
    rw [hgauss, hchi]
  have hWarg (r : Q) (j : S.R) :
      W.W0 (S.diag ((E (r, j) : S.R) : F) * (k⁻¹ : S.FSˣ).val) =
        W.W0 (S.diag ((r.out : F) + (period : F) * (j : F)) *
          (k⁻¹ : S.FSˣ).val) := by
    rw [hElt r j]
  have hPairW : Summable (fun z : Q × S.R => normW (E (z.1, z.2))) := by
    refine (summable_prod_of_nonneg (f := fun z : Q × S.R => normW (E (z.1, z.2)))
      (fun z => norm_nonneg _)).2 ?_
    constructor
    · intro r
      have hcos := hcoset total period hgenPeriod r.out k
      have hfun : (fun j : S.R => normW (E (r, j))) =
          fun (j : S.R) => ‖W.W0 (S.diag ((r.out : F) + (period : F) * (j : F)) *
            (k⁻¹ : S.FSˣ).val)‖ := by
        funext j
        dsimp [normW]
        rw [hWarg]
      rw [hfun]
      exact hcos.1
    · exact Summable.of_finite
  have hWsum : Summable normW := E.summable_iff.mp hPairW
  have hFirst : Summable (fun m : S.R => ‖summand m‖) := by
    apply (hWsum.mul_left qS).of_norm_bounded
    intro m
    calc
      ‖‖summand m‖‖ = ‖summand m‖ := Real.norm_of_nonneg (norm_nonneg _)
      _ = ‖coeff m‖ * normW m := by
        dsimp [summand, normW]
        rw [norm_mul]
      _ ≤ qS * normW m :=
        mul_le_mul_of_nonneg_right (hCoeffBound m) (norm_nonneg _)
  have hCosetFourier : Summable (fun h : S.R => ‖fourier h‖) := by
    exact (hcoset total period hgenPeriod (0 : S.R) k).2.1
  have hFactorBound (h : S.R) : ‖factor h‖ ≤ qS * qI I.1 := by
    exact (hfinite.1 s I a ha hallowed h).2.1
  have hSecond : Summable (fun h : S.R => ‖factor h * fourier h‖) := by
    apply (hCosetFourier.mul_left (qS * qI I.1)).of_norm_bounded
    intro h
    calc
      ‖‖factor h * fourier h‖‖ = ‖factor h * fourier h‖ :=
        Real.norm_of_nonneg (norm_nonneg _)
      _ = ‖factor h‖ * ‖fourier h‖ := norm_mul _ _
      _ ≤ (qS * qI I.1) * ‖fourier h‖ :=
        mul_le_mul_of_nonneg_right (hFactorBound h) (norm_nonneg _)
  have htransform (h : S.R) :
      (∑ r : Q, coeff r.out * phase r h) =
        (qS ^ (1 / 2 : ℝ) : ℝ) * factor h := by
    have hraw := (hfinite.1 s I a ha hallowed h).1
    rw [finsum_eq_sum_of_fintype] at hraw
    simpa [coeff, phase, factor, qS, period, mul_assoc, mul_comm, mul_left_comm] using hraw
  have hphaseNorm (r : Q) (h : S.R) : ‖phase r h‖ = 1 := by
    dsimp [phase]
    rw [← hpval]
    have hmul : ((r.out * h : S.R) : F) = (r.out : F) * (h : F) := by simp
    rw [← hmul]
    exact additivePhase_norm_one R total pR hspanTotal hpRnezero (r.out * h)
  let pairTerm : Q × S.R → ℂ := fun z =>
    coeff z.1.out * (phase z.1 z.2 * fourier z.2)
  have hPairNorm : Summable (fun z : Q × S.R => ‖pairTerm z‖) := by
    refine (summable_prod_of_nonneg (f := fun z : Q × S.R => ‖pairTerm z‖)
      (fun z => norm_nonneg _)).2 ?_
    constructor
    · intro r
      apply (hCosetFourier.mul_left ‖coeff r.out‖).of_norm_bounded
      intro h
      simp [pairTerm, hphaseNorm r h, mul_assoc]
    · exact Summable.of_finite
  have hPair : Summable pairTerm := summable_norm_iff.mp hPairNorm
  have hPairSwap : Summable (fun z : S.R × Q => pairTerm (z.2, z.1)) :=
    hPair.comp_injective (Equiv.prodComm Q S.R).symm.injective
  have hswap :
      (∑ r : Q, coeff r.out * ∑' h : S.R, phase r h * fourier h) =
        ∑' h : S.R, ∑ r : Q, pairTerm (r, h) := by
    calc
      _ = ∑' r : Q, ∑' h : S.R, pairTerm (r, h) := by
        rw [tsum_fintype]
        apply Finset.sum_congr rfl
        intro r hr
        dsimp [pairTerm]
        rw [tsum_mul_left]
      _ = ∑' z : Q × S.R, pairTerm z := hPair.tsum_prod.symm
      _ = ∑' z : S.R × Q, pairTerm (z.2, z.1) :=
        (Equiv.prodComm Q S.R).tsum_eq (fun z => pairTerm (z.2, z.1))
      _ = ∑' h : S.R, ∑' r : Q, pairTerm (r, h) := hPairSwap.tsum_prod
      _ = ∑' h : S.R, ∑ r : Q, pairTerm (r, h) := by
        apply tsum_congr
        intro h
        rw [tsum_fintype]
  have hsumPair (h : S.R) :
      (∑ r : Q, pairTerm (r, h)) =
        (qS ^ (1 / 2 : ℝ) : ℝ) * factor h * fourier h := by
    calc
      (∑ r : Q, pairTerm (r, h)) =
          ∑ r : Q, (coeff r.out * phase r h) * fourier h := by
            apply Finset.sum_congr rfl
            intro r hr
            dsimp [pairTerm]
            ring
      _ = (∑ r : Q, coeff r.out * phase r h) * fourier h := by
            rw [Finset.sum_mul]
      _ = (qS ^ (1 / 2 : ℝ) : ℝ) * factor h * fourier h := by rw [htransform]
  have hswapSeries :
      (∑' h : S.R, ∑ r : Q, pairTerm (r, h)) =
        (qS ^ (1 / 2 : ℝ) : ℝ) * ∑' h : S.R, factor h * fourier h := by
    calc
      _ = ∑' h : S.R, ((qS ^ (1 / 2 : ℝ) : ℝ) * factor h * fourier h) := by
        apply tsum_congr
        intro h
        exact hsumPair h
      _ = ∑' h : S.R, (qS ^ (1 / 2 : ℝ) : ℝ) * (factor h * fourier h) := by
        apply tsum_congr
        intro h
        ring
      _ = (qS ^ (1 / 2 : ℝ) : ℝ) * ∑' h : S.R, factor h * fourier h := tsum_mul_left
  have hCosetFormula (r : Q) :
      (∑' j : S.R, W.W0 (S.diag ((r.out : F) + (period : F) * (j : F)) *
        (k⁻¹ : S.FSˣ).val)) =
        ((S.absS (k : S.FS) / qT : ℝ) : ℂ) *
          ∑' h : S.R, phase r h * fourier h := by
    simpa [phase, fourier] using
      (hcoset total period hgenPeriod r.out k).2.2
  have hTsum :
      (∑' m : S.R, summand m) =
        ((S.absS (k : S.FS) / qT : ℝ) : ℂ) *
          ((qS ^ (1 / 2 : ℝ) : ℝ) * ∑' h : S.R, factor h * fourier h) := by
    have hFirstComplex : Summable summand := summable_norm_iff.mp hFirst
    have hfirstPair : Summable (fun z : Q × S.R => summand (E z)) :=
      E.summable_iff.mpr hFirstComplex
    have hrowTerm (r : Q) (j : S.R) :
        summand (E (r, j)) = coeff r.out *
          W.W0 (S.diag ((r.out : F) + (period : F) * (j : F)) *
            (k⁻¹ : S.FSˣ).val) := by
      dsimp only [summand]
      rw [hrowCoeff r j, hWarg r j]
    calc
      _ = ∑' z : Q × S.R, summand (E z) := (E.tsum_eq summand).symm
      _ = ∑' r : Q, ∑' j : S.R, summand (E (r, j)) := hfirstPair.tsum_prod
      _ = ∑ r : Q, coeff r.out *
          ∑' j : S.R, W.W0 (S.diag ((r.out : F) + (period : F) * (j : F)) *
            (k⁻¹ : S.FSˣ).val) := by
        rw [tsum_fintype]
        apply Finset.sum_congr rfl
        intro r hr
        calc
          (∑' j : S.R, summand (E (r, j))) =
              ∑' j : S.R, coeff r.out *
                W.W0 (S.diag ((r.out : F) + (period : F) * (j : F)) *
                  (k⁻¹ : S.FSˣ).val) := by
                    apply tsum_congr
                    intro j
                    exact hrowTerm r j
          _ = coeff r.out *
              ∑' j : S.R, W.W0 (S.diag ((r.out : F) + (period : F) * (j : F)) *
                (k⁻¹ : S.FSˣ).val) := tsum_mul_left
      _ = ∑ r : Q, coeff r.out *
          (((S.absS (k : S.FS) / qT : ℝ) : ℂ) *
            ∑' h : S.R, phase r h * fourier h) := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [hCosetFormula r]
      _ = ((S.absS (k : S.FS) / qT : ℝ) : ℂ) *
          ∑ r : Q, coeff r.out * ∑' h : S.R, phase r h * fourier h := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        ring
      _ = ((S.absS (k : S.FS) / qT : ℝ) : ℂ) *
          ∑' h : S.R, ∑ r : Q, pairTerm (r, h) := by
        rw [hswap]
      _ = ((S.absS (k : S.FS) / qT : ℝ) : ℂ) *
          ((qS ^ (1 / 2 : ℝ) : ℝ) * ∑' h : S.R, factor h * fourier h) := by
        rw [hswapSeries]
  have hsqrtSq : qS ^ (1 / 2 : ℝ) * qS ^ (1 / 2 : ℝ) = qS := by
    rw [← Real.rpow_add hqSpos]
    norm_num
  have hsqrtPos : 0 < qS ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hqSpos _
  have hscalarReal :
      (S.absS (k : S.FS) / qT) * qS ^ (1 / 2 : ℝ) =
        S.absS (k : S.FS) / (qS ^ (1 / 2 : ℝ) * qI I.1) := by
    have hden : qS * qI I.1 =
        (qS ^ (1 / 2 : ℝ) * qS ^ (1 / 2 : ℝ)) * qI I.1 := by
      rw [hsqrtSq]
    rw [hqT]
    rw [hden]
    field_simp [ne_of_gt hsqrtPos, ne_of_gt hqIpos] <;> ring
  have hscalar :
      ((S.absS (k : S.FS) / qT : ℝ) : ℂ) *
          (qS ^ (1 / 2 : ℝ) : ℝ) =
        ((S.absS (k : S.FS) / (qS ^ (1 / 2 : ℝ) * qI I.1) : ℝ) : ℂ) :=
    by
      rw [← Complex.ofReal_mul]
      exact congrArg (fun x : ℝ => (x : ℂ)) hscalarReal
  refine ⟨hFirst, hSecond, ?_⟩
  calc
    _ = ((S.absS (k : S.FS) / qT : ℝ) : ℂ) *
        ((qS ^ (1 / 2 : ℝ) : ℝ) * ∑' h : S.R, factor h * fourier h) := by
          simpa [summand, coeff, qS] using hTsum
    _ = (((S.absS (k : S.FS) / qT : ℝ) : ℂ) *
          (qS ^ (1 / 2 : ℝ) : ℝ)) * ∑' h : S.R, factor h * fourier h := by ring
    _ = ((S.absS (k : S.FS) / (qS ^ (1 / 2 : ℝ) * qI I.1) : ℝ) : ℂ) *
          ∑' h : S.R, factor h * fourier h := by rw [hscalar]
    _ = _ := by
      have hperiodVal : (period : F) = (bc.gen s : F) * (a : F) := by
        simp [period]
      have hseries :
          (∑' h : S.R, factor h * fourier h) =
            ∑' h : S.R, leadFiniteFactor R s I a (h : F) *
              leadFourier sd W ((k : S.FS) *
                S.diag ((h : F) / ((bc.gen s : F) * (a : F)))) := by
        apply tsum_congr
        intro h
        simp only [factor, fourier]
        rw [hperiodVal]
      exact congrArg
        (fun z : ℂ =>
          ((S.absS (k : S.FS) / (qS ^ (1 / 2 : ℝ) * qI I.1) : ℝ) : ℂ) * z)
        hseries

end ArtinPrimitiveRoots.Proofs.pr_b
