import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_FOURIER.Defs
import ArtinPrimitiveRoots.Arith.SUnit
import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.Core
import ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.NumberFieldFractionalIdealFactorization
import ClassFieldTheory.AlgebraicNumberTheory.SUnit.Rank
import ClassFieldTheory.AlgebraicNumberTheory.RayClass.Narrow
import Mathlib.RingTheory.DedekindDomain.SelmerGroup

set_option autoImplicit false
open NumberField IsDedekindDomain
open ClassFieldTheory

open scoped Classical nonZeroDivisors
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

theorem finite_ringOfIntegersUnit_cubeQuotient {F : Type} [Field F] [NumberField F] :
    Finite ((𝓞 F)ˣ ⧸ (powMonoidHom (α := (𝓞 F)ˣ) 3).range) := by
  classical
  letI : Group.FG (𝓞 F)ˣ :=
    Group.fg_iff_monoid_fg.mpr (inferInstance : Monoid.FG (𝓞 F)ˣ)
  letI : (powMonoidHom (α := (𝓞 F)ˣ) 3).range.FiniteIndex :=
    Subgroup.finiteIndex_range_powMonoidHom_of_fg ((𝓞 F)ˣ) (by norm_num)
  infer_instance

private def residueLift {α : Type*} (S : Finset α)
    (r : {v : α // v ∈ S} → Fin 3) : α →₀ ℤ :=
  Finsupp.onFinset S (fun v => if hv : v ∈ S then ((r ⟨v, hv⟩).val : ℤ) else 0)
    (by
      intro v hv
      by_contra hnot
      simp [hnot] at hv)

private theorem residueLift_apply {α : Type*} (S : Finset α)
    (r : {v : α // v ∈ S} → Fin 3) (v : α) :
    residueLift S r v = if hv : v ∈ S then (r ⟨v, hv⟩).val else 0 := by
  classical
  by_cases hv : v ∈ S
  · simp [residueLift, hv]
  · simp [residueLift, hv]

private theorem exists_divisor_residue_decomposition {F : Type} [Field F] [NumberField F]
    (S : Finset (FinPlace F)) (e : FinPlace F →₀ ℤ)
    (hout : ∀ v ∉ S, (e v : ZMod 3) = 0) :
    ∃ (r : {v : FinPlace F // v ∈ S} → Fin 3) (d : FinPlace F →₀ ℤ),
      e = 3 • d + residueLift S r := by
  classical
  let r : {v : FinPlace F // v ∈ S} → Fin 3 := fun v =>
    ⟨(e v.1 : ZMod 3).val, ZMod.val_lt _⟩
  let rem := residueLift S r
  let d := (e - rem).mapRange (fun z : ℤ => z / 3) (by simp)
  refine ⟨r, d, ?_⟩
  ext v
  by_cases hv : v ∈ S
  · have hval : ((e v : ZMod 3).val : ℤ) = e v % 3 := by
      exact_mod_cast ZMod.val_intCast (n := 3) (a := e v)
    have hr : rem v = e v % 3 := by simp [rem, residueLift_apply, r, hv, hval]
    change e v = 3 * ((e v - rem v) / 3) + rem v
    rw [hr]
    omega
  · have hval : ((e v : ZMod 3).val : ℤ) = e v % 3 := by
      exact_mod_cast ZMod.val_intCast (n := 3) (a := e v)
    have hrem : rem v = 0 := by simp [rem, residueLift_apply, hv]
    have hmod : e v % 3 = 0 := by
      rw [← hval, hout v hv]
      rfl
    change e v = 3 * ((e v - rem v) / 3) + rem v
    rw [hrem]
    omega

set_option maxHeartbeats 600000 in
theorem valuationMod_eq_one_iff_countMod_eq_zero {F : Type} [Field F] [NumberField F]
    (δ : Fˣ) (v : FinPlace F) :
    v.valuationOfNeZeroMod 3 (QuotientGroup.mk δ) = 1 ↔
    (FractionalIdeal.count F v
        ((toPrincipalIdeal (𝓞 F) F δ : NumberFieldFractionalIdealGroup F) :
          FractionalIdeal (nonZeroDivisors (𝓞 F)) F) : ZMod 3) = 0 := by
  classical
  let e := Int.quotientZMultiplesNatEquivZMod 3
  let hmap : (powMonoidHom (α := Fˣ) 3).range ≤
      (AddSubgroup.toSubgroup (AddSubgroup.zmultiples (3 : ℤ))).comap
        (v.valuationOfNeZero) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨v.valuationOfNeZero x, by
      simp only [powMonoidHom_apply, map_pow, Int.toAdd_pow]
      rfl⟩
  let f := QuotientGroup.map (powMonoidHom (α := Fˣ) 3).range
    (AddSubgroup.toSubgroup (AddSubgroup.zmultiples (3 : ℤ)))
    (v.valuationOfNeZero) hmap
  change e.toMultiplicative.toMonoidHom (f (QuotientGroup.mk δ)) = 1 ↔ _
  have hlog : Multiplicative.toAdd (v.valuationOfNeZero δ) =
      WithZero.log (v.valuation F (δ : F)) := by
    exact congrArg WithZero.log (v.valuationOfNeZero_eq δ)
  have hcount : FractionalIdeal.count F v
      ((toPrincipalIdeal (𝓞 F) F δ : NumberFieldFractionalIdealGroup F) :
        FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
      -Multiplicative.toAdd (v.valuationOfNeZero δ) := by
    rw [IdeleGroup.count_toPrincipalIdeal, hlog]
  constructor
  · intro h
    have hq : f (QuotientGroup.mk δ) = 1 := by
      apply e.toMultiplicative.injective
      exact h
    erw [QuotientGroup.map_mk'] at hq
    have hmem : Multiplicative.toAdd (v.valuationOfNeZero δ) ∈
        AddSubgroup.zmultiples (3 : ℤ) := by
      have hm := (QuotientGroup.eq_one_iff _).mp hq
      simpa using hm
    rcases Int.mem_zmultiples_iff.mp hmem with ⟨k, hk⟩
    have hdiv : (3 : ℤ) ∣ FractionalIdeal.count F v
        ((toPrincipalIdeal (𝓞 F) F δ : NumberFieldFractionalIdealGroup F) :
          FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
      rw [hcount, hk]
      exact ⟨-k, by ring⟩
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).2 hdiv
  · intro h
    have hdiv : (3 : ℤ) ∣ FractionalIdeal.count F v
        ((toPrincipalIdeal (𝓞 F) F δ : NumberFieldFractionalIdealGroup F) :
          FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp h
    rw [hcount] at hdiv
    have hmem : Multiplicative.toAdd (v.valuationOfNeZero δ) ∈
        AddSubgroup.zmultiples (3 : ℤ) := by
      rw [Int.mem_zmultiples_iff]
      exact dvd_neg.mp hdiv
    have hq0 : (QuotientGroup.mk (v.valuationOfNeZero δ) :
        Multiplicative ℤ ⧸ AddSubgroup.toSubgroup (AddSubgroup.zmultiples (3 : ℤ))) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (by simpa using hmem)
    have hq : f (QuotientGroup.mk' (powMonoidHom (α := Fˣ) 3).range δ) = 1 := by
      let N := (powMonoidHom (α := Fˣ) 3).range
      let M := AddSubgroup.toSubgroup (AddSubgroup.zmultiples (3 : ℤ))
      change QuotientGroup.map N M (v.valuationOfNeZero) hmap (QuotientGroup.mk' N δ) = 1
      calc
        _ = QuotientGroup.mk' M (v.valuationOfNeZero δ) :=
          QuotientGroup.map_mk' N M (v.valuationOfNeZero) hmap δ
        _ = 1 := hq0
    change e.toMultiplicative.toMonoidHom
      (f (QuotientGroup.mk' (powMonoidHom (α := Fˣ) 3).range δ)) = 1
    rw [hq]
    exact e.toMultiplicative.map_one

theorem countVector_principal_eq_ordv {F : Type} [Field F] [NumberField F]
    (δ : Fˣ) (v : FinPlace F) :
    NumberFieldFractionalIdealGroup.countVector (toPrincipalIdeal (𝓞 F) F δ) v =
      ordv v (toLoc v δ) := by
  classical
  have hlog : Multiplicative.toAdd (v.valuationOfNeZero δ) =
      WithZero.log (v.valuation F (δ : F)) :=
    congrArg WithZero.log (v.valuationOfNeZero_eq δ)
  have hlocal : Valued.v ((toLoc v δ : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      v.valuation F (δ : F) := by
    change Valued.v (algebraMap F (v.adicCompletion F) (δ : F)) = _
    simp only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply, v.valuedAdicCompletion_eq_valuation']
  have hlocal0 : Valued.v ((toLoc v δ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (Units.ne_zero (toLoc v δ))
  have hord : ordv v (toLoc v δ) = -Multiplicative.toAdd (v.valuationOfNeZero δ) := by
    simp only [ordv]
    rw [WithZero.toAdd_unzero_eq_log hlocal0, hlocal, ← hlog]
  have hcount : FractionalIdeal.count F v
      ((toPrincipalIdeal (𝓞 F) F δ : NumberFieldFractionalIdealGroup F) :
        FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
      -Multiplicative.toAdd (v.valuationOfNeZero δ) := by
    rw [IdeleGroup.count_toPrincipalIdeal, hlog]
  calc
    NumberFieldFractionalIdealGroup.countVector (toPrincipalIdeal (𝓞 F) F δ) v =
        FractionalIdeal.count F v
          ((toPrincipalIdeal (𝓞 F) F δ : NumberFieldFractionalIdealGroup F) :
            FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
          rw [NumberFieldFractionalIdealGroup.countVector_apply]
    _ = -Multiplicative.toAdd (v.valuationOfNeZero δ) := hcount
    _ = ordv v (toLoc v δ) := hord.symm

theorem valuationMod_eq_one_iff_ordvMod_eq_zero {F : Type} [Field F] [NumberField F]
    (δ : Fˣ) (v : FinPlace F) :
    v.valuationOfNeZeroMod 3 (QuotientGroup.mk δ) = 1 ↔
      (ordv v (toLoc v δ) : ZMod 3) = 0 := by
  rw [valuationMod_eq_one_iff_countMod_eq_zero δ v]
  have hcount : FractionalIdeal.count F v
      ((toPrincipalIdeal (𝓞 F) F δ : NumberFieldFractionalIdealGroup F) :
        FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = ordv v (toLoc v δ) := by
    simpa [NumberFieldFractionalIdealGroup.countVector_apply] using
      countVector_principal_eq_ordv δ v
  rw [hcount]

theorem unitPart_factor {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (x : (v.adicCompletion F)ˣ) :
    unifLoc v ^ ordv v x * unitPart v x = x := by
  dsimp [unitPart]
  calc
    unifLoc v ^ ordv v x * (x * unifLoc v ^ (-ordv v x)) =
        x * (unifLoc v ^ ordv v x * (unifLoc v ^ ordv v x)⁻¹) := by
          rw [zpow_neg]
          ac_rfl
    _ = x := by simp

theorem unitPart_isLocUnit {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (x : (v.adicCompletion F)ˣ) :
    IsLocUnit v (unitPart v x) := by
  have hx0 : Valued.v (x : v.adicCompletion F) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr x.ne_zero
  have hxv : Valued.v (x : v.adicCompletion F) = WithZero.exp (-ordv v x) := by
    rw [← WithZero.exp_log hx0]
    simp [ordv, WithZero.toAdd_unzero_eq_log hx0]
  have hπ : Valued.v (unifLoc v : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    change Valued.v ((unif v : F) : v.adicCompletion F) = WithZero.exp (-1 : ℤ)
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (HeightOneSpectrum.valuation_exists_uniformizer F v).choose_spec
  have hval : Valued.v (unitPart v x : v.adicCompletion F) = 1 := by
    simp only [unitPart, Units.val_mul, Units.val_zpow_eq_zpow_val]
    change Valued.v ((x : v.adicCompletion F) *
      (unifLoc v : v.adicCompletion F) ^ (-ordv v x)) = 1
    rw [map_mul, map_zpow₀, hxv, hπ]
    rw [← WithZero.exp_zsmul, ← WithZero.exp_add]
    congr 1
    simp
  constructor
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, hval]
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    have hval' : Valued.v (((unitPart v x)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
      simp [hval]
    rw [hval']

private theorem idealGroup_class_surjective {F : Type} [Field F] [NumberField F] :
    Function.Surjective (ClassGroup.mk F : NumberFieldFractionalIdealGroup F →* ClassGroup (𝓞 F)) := by
  intro c
  obtain ⟨I, hI⟩ := ClassGroup.mk0_surjective (R := 𝓞 F) c
  refine ⟨FractionalIdeal.mk0 F I, ?_⟩
  simpa [ClassGroup.mk_mk0] using hI

private noncomputable def idealClassRepresentative {F : Type} [Field F] [NumberField F]
    (c : ClassGroup (𝓞 F)) : NumberFieldFractionalIdealGroup F :=
  Classical.choose (idealGroup_class_surjective (F := F) c)

private theorem idealClassRepresentative_spec {F : Type} [Field F] [NumberField F]
    (c : ClassGroup (𝓞 F)) :
    ClassGroup.mk F (idealClassRepresentative c) = c :=
  Classical.choose_spec (idealGroup_class_surjective (F := F) c)

private theorem classGroup_mk_eq_iff_scalar_multiple {F : Type} [Field F] [NumberField F]
    (I J : FractionalIdeal (𝓞 F)⁰ F) (hI : I ≠ 0) (hJ : J ≠ 0) :
    ClassGroup.mk F (Units.mk0 I hI) = ClassGroup.mk F (Units.mk0 J hJ) ↔
      ∃ a : F, a ≠ 0 ∧ I * FractionalIdeal.spanSingleton (𝓞 F)⁰ a = J := by
  constructor
  · intro h
    have hq := congrArg (ClassGroup.equiv (R := 𝓞 F) F) h
    have hmapI : Units.mapEquiv
        (↑(FractionalIdeal.canonicalEquiv (𝓞 F)⁰ F F)) (Units.mk0 I hI) =
          Units.mk0 I hI := by
      apply Units.ext
      simp [FractionalIdeal.canonicalEquiv_self]
    have hmapJ : Units.mapEquiv
        (↑(FractionalIdeal.canonicalEquiv (𝓞 F)⁰ F F)) (Units.mk0 J hJ) =
          Units.mk0 J hJ := by
      apply Units.ext
      simp [FractionalIdeal.canonicalEquiv_self]
    have hq' : QuotientGroup.mk' (toPrincipalIdeal (𝓞 F) F).range (Units.mk0 I hI) =
        QuotientGroup.mk' (toPrincipalIdeal (𝓞 F) F).range (Units.mk0 J hJ) := by
      rw [ClassGroup.equiv_mk F, ClassGroup.equiv_mk F] at hq
      rw [hmapI, hmapJ] at hq
      exact hq
    rcases (QuotientGroup.mk'_eq_mk' (toPrincipalIdeal (𝓞 F) F).range).mp hq' with
      ⟨u, hu, hmul⟩
    rcases MonoidHom.mem_range.mp hu with ⟨a, rfl⟩
    refine ⟨(a : F), a.ne_zero, ?_⟩
    have hval := congrArg (fun x : NumberFieldFractionalIdealGroup F =>
      (x : FractionalIdeal (𝓞 F)⁰ F)) hmul
    simpa [Units.val_mul, coe_toPrincipalIdeal] using hval
  · rintro ⟨a, ha, hmul⟩
    let u : Fˣ := Units.mk0 a ha
    have hu : toPrincipalIdeal (𝓞 F) F u ∈ (toPrincipalIdeal (𝓞 F) F).range := ⟨u, rfl⟩
    have hmul' : Units.mk0 I hI * toPrincipalIdeal (𝓞 F) F u = Units.mk0 J hJ := by
      apply Units.ext
      simpa [u, Units.val_mul, coe_toPrincipalIdeal] using hmul
    apply (ClassGroup.equiv (R := 𝓞 F) F).injective
    have hq' : QuotientGroup.mk' (toPrincipalIdeal (𝓞 F) F).range (Units.mk0 I hI) =
        QuotientGroup.mk' (toPrincipalIdeal (𝓞 F) F).range (Units.mk0 J hJ) :=
      (QuotientGroup.mk'_eq_mk' (toPrincipalIdeal (𝓞 F) F).range).2
        ⟨toPrincipalIdeal (𝓞 F) F u, hu, hmul'⟩
    have hmapI : Units.mapEquiv
        (↑(FractionalIdeal.canonicalEquiv (𝓞 F)⁰ F F)) (Units.mk0 I hI) =
          Units.mk0 I hI := by
      apply Units.ext
      simp [FractionalIdeal.canonicalEquiv_self]
    have hmapJ : Units.mapEquiv
        (↑(FractionalIdeal.canonicalEquiv (𝓞 F)⁰ F F)) (Units.mk0 J hJ) =
          Units.mk0 J hJ := by
      apply Units.ext
      simp [FractionalIdeal.canonicalEquiv_self]
    rw [ClassGroup.equiv_mk F, ClassGroup.equiv_mk F]
    rw [hmapI, hmapJ]
    exact hq'

private theorem exists_principalGenerator {F : Type} [Field F] [NumberField F]
    (I : NumberFieldFractionalIdealGroup F) (hI : ClassGroup.mk F I = 1) :
    ∃ x : Fˣ, toPrincipalIdeal (𝓞 F) F x = I := by
  have hmk : ClassGroup.mk F I = ClassGroup.mk F (1 : NumberFieldFractionalIdealGroup F) := by
    simpa using hI
  have hmk' : ClassGroup.mk F
      (Units.mk0 (I : FractionalIdeal (𝓞 F)⁰ F) (Units.ne_zero I)) =
      ClassGroup.mk F (Units.mk0 (1 : FractionalIdeal (𝓞 F)⁰ F) (by simp)) := by
    simpa using hmk
  obtain ⟨a, ha, hspan⟩ :=
    (classGroup_mk_eq_iff_scalar_multiple (F := F)
      (I : FractionalIdeal (𝓞 F)⁰ F) (1 : FractionalIdeal (𝓞 F)⁰ F)
      (Units.ne_zero I) (by simp)).mp hmk'
  let u : Fˣ := Units.mk0 a ha
  have hmul : I * toPrincipalIdeal (𝓞 F) F u = 1 := by
    apply Units.ext
    simpa [u, Units.val_mul, coe_toPrincipalIdeal] using hspan
  have hIeq : I = (toPrincipalIdeal (𝓞 F) F u)⁻¹ := by
    have htmp := congrArg (fun z : NumberFieldFractionalIdealGroup F =>
      z * (toPrincipalIdeal (𝓞 F) F u)⁻¹) hmul
    simpa [mul_assoc] using htmp
  refine ⟨u⁻¹, ?_⟩
  rw [map_inv]
  exact hIeq.symm

private abbrev CubeClass (F : Type) [Field F] [NumberField F] :=
  Fˣ ⧸ (powMonoidHom (α := Fˣ) 3).range

private abbrev ResidueFunction {F : Type} [Field F] [NumberField F]
    (S : Finset (FinPlace F)) :=
  {v : FinPlace F // v ∈ S} → Fin 3

private noncomputable def residueIdeal {F : Type} [Field F] [NumberField F]
    (S : Finset (FinPlace F)) (r : ResidueFunction S) : NumberFieldFractionalIdealGroup F :=
  NumberFieldFractionalIdealGroup.factorization
    (Multiplicative.ofAdd (residueLift S r))

private noncomputable def betaCandidate {F : Type} [Field F] [NumberField F]
    (S : Finset (FinPlace F)) (r : ResidueFunction S) (c : ClassGroup (𝓞 F)) : Fˣ := by
  classical
  letI : Fintype (ClassGroup (𝓞 F)) := inferInstance
  let J := idealClassRepresentative (F := F) c
  let H := J ^ 3 * residueIdeal S r
  exact if h : ClassGroup.mk F H = 1 then Classical.choose (exists_principalGenerator H h)
    else 1

private theorem betaCandidate_spec {F : Type} [Field F] [NumberField F]
    (S : Finset (FinPlace F)) (r : ResidueFunction S) (c : ClassGroup (𝓞 F))
    (h : ClassGroup.mk F (idealClassRepresentative (F := F) c ^ 3 * residueIdeal S r) = 1) :
    toPrincipalIdeal (𝓞 F) F (betaCandidate S r c) =
      idealClassRepresentative (F := F) c ^ 3 * residueIdeal S r := by
  classical
  dsimp [betaCandidate]
  rw [dif_pos h]
  exact Classical.choose_spec (exists_principalGenerator
    (idealClassRepresentative (F := F) c ^ 3 * residueIdeal S r) h)

private def unitCubeClass (F : Type) [Field F] [NumberField F] : Type :=
  (𝓞 F)ˣ ⧸ (powMonoidHom (α := (𝓞 F)ˣ) 3).range

private noncomputable def selmerCandidate {F : Type} [Field F] [NumberField F]
    (S : Finset (FinPlace F)) (r : ResidueFunction S) (c : ClassGroup (𝓞 F))
    (u : unitCubeClass F) : CubeClass F :=
  QuotientGroup.mk (betaCandidate S r c *
    Units.map (algebraMap (𝓞 F) F).toMonoidHom (Quotient.out u))

theorem finite_numberField_cubeSelmer' {F : Type} [Field F] [NumberField F]
    (S : Finset (FinPlace F)) :
    Finite (IsDedekindDomain.selmerGroup (R := 𝓞 F) (K := F)
      (S := (S : Set (FinPlace F))) (n := 3)) := by
  classical
  let H : Subgroup (CubeClass F) :=
    IsDedekindDomain.selmerGroup (R := 𝓞 F) (K := F)
      (S := (S : Set (FinPlace F))) (n := 3)
  letI : Fintype (ClassGroup (𝓞 F)) := inferInstance
  letI : Finite (unitCubeClass F) := finite_ringOfIntegersUnit_cubeQuotient
  letI : Fintype (unitCubeClass F) := Fintype.ofFinite (α := unitCubeClass F)
  letI : Fintype (ResidueFunction S) := Fintype.ofFinite (α := ResidueFunction S)
  let candidate : ResidueFunction S × ClassGroup (𝓞 F) × unitCubeClass F → CubeClass F :=
    fun t => selmerCandidate S t.1 t.2.1 t.2.2
  have hrange : (Set.range candidate).Finite := Set.finite_range candidate
  have hcover : (H : Set (CubeClass F)) ⊆ Set.range candidate := by
    intro q hq
    let δ : Fˣ := Quotient.out (q : CubeClass F)
    change (∀ v, v ∉ (S : Set (FinPlace F)) →
      v.valuationOfNeZeroMod 3 (q : CubeClass F) = 1) at hq
    have hout : ∀ v ∉ S, (NumberFieldFractionalIdealGroup.countVector
        (toPrincipalIdeal (𝓞 F) F δ) v : ZMod 3) = 0 := by
      intro v hv
      have hloc : v.valuationOfNeZeroMod 3 (QuotientGroup.mk δ) = 1 := by
        simpa [δ] using hq v hv
      simpa [NumberFieldFractionalIdealGroup.countVector_apply] using
        (valuationMod_eq_one_iff_countMod_eq_zero δ v).mp hloc
    obtain ⟨r, d, hdecomp⟩ := exists_divisor_residue_decomposition S
      (NumberFieldFractionalIdealGroup.countVector (toPrincipalIdeal (𝓞 F) F δ)) hout
    let Iδ : NumberFieldFractionalIdealGroup F := toPrincipalIdeal (𝓞 F) F δ
    let J : NumberFieldFractionalIdealGroup F :=
      NumberFieldFractionalIdealGroup.factorization (Multiplicative.ofAdd d)
    let A : NumberFieldFractionalIdealGroup F := residueIdeal S r
    have hfacI : NumberFieldFractionalIdealGroup.factorization
        (Multiplicative.ofAdd (NumberFieldFractionalIdealGroup.countVector Iδ)) = Iδ := by
      apply NumberFieldFractionalIdealGroup.ext_count
      intro v
      rw [NumberFieldFractionalIdealGroup.count_factorization]
      simp [Iδ, NumberFieldFractionalIdealGroup.countVector_apply]
    have hfact : Iδ = J ^ 3 * A := by
      calc
        Iδ = NumberFieldFractionalIdealGroup.factorization
            (Multiplicative.ofAdd (NumberFieldFractionalIdealGroup.countVector Iδ)) := hfacI.symm
        _ = NumberFieldFractionalIdealGroup.factorization
            (Multiplicative.ofAdd (3 • d + residueLift S r)) := by rw [hdecomp]
        _ = J ^ 3 * A := by
          have hmul : Multiplicative.ofAdd (3 • d + residueLift S r) =
              (Multiplicative.ofAdd d) ^ 3 * Multiplicative.ofAdd (residueLift S r) := by
            apply Multiplicative.ext
            simp
          rw [hmul]
          simp [J, A, residueIdeal]
    have hclassI : ClassGroup.mk F Iδ = 1 := by
      apply (ClassGroup.mk_eq_one_iff (I := Iδ)).2
      refine ⟨(δ : F), ?_⟩
      simp [Iδ, toPrincipalIdeal]
    have hclassProd : ClassGroup.mk F (J ^ 3 * A) = 1 := by
      have h := congrArg (ClassGroup.mk F) hfact
      rw [hclassI] at h
      exact h.symm
    let c : ClassGroup (𝓞 F) := ClassGroup.mk F J
    have hJclass : ClassGroup.mk F J =
        ClassGroup.mk F (idealClassRepresentative (F := F) c) := by
      rw [idealClassRepresentative_spec c]
    have hHclass : ClassGroup.mk F
        (idealClassRepresentative (F := F) c ^ 3 * A) = 1 := by
      calc
        _ = (ClassGroup.mk F (idealClassRepresentative (F := F) c)) ^ 3 *
              ClassGroup.mk F A := by simp
        _ = (ClassGroup.mk F J) ^ 3 * ClassGroup.mk F A := by rw [idealClassRepresentative_spec c]
        _ = 1 := by simpa [map_mul, map_pow] using hclassProd
    have hbeta := betaCandidate_spec S r c hHclass
    have hJclass' : ClassGroup.mk F
        (Units.mk0 (J : FractionalIdeal (𝓞 F)⁰ F) (Units.ne_zero J)) =
        ClassGroup.mk F (Units.mk0
          (idealClassRepresentative (F := F) c : FractionalIdeal (𝓞 F)⁰ F)
          (Units.ne_zero (idealClassRepresentative (F := F) c))) := by
      simpa using hJclass
    obtain ⟨a, ha, hspan⟩ :=
      (classGroup_mk_eq_iff_scalar_multiple (F := F)
        (J : FractionalIdeal (𝓞 F)⁰ F)
        (idealClassRepresentative (F := F) c : FractionalIdeal (𝓞 F)⁰ F)
        (Units.ne_zero J) (Units.ne_zero (idealClassRepresentative (F := F) c))).mp hJclass'
    let α : Fˣ := Units.mk0 a ha
    have hJmul : J * toPrincipalIdeal (𝓞 F) F α =
        idealClassRepresentative (F := F) c := by
      apply Units.ext
      simpa [α, Units.val_mul, coe_toPrincipalIdeal] using hspan
    have hJrel : J = idealClassRepresentative (F := F) c *
        toPrincipalIdeal (𝓞 F) F α⁻¹ := by
      calc
        J = (J * toPrincipalIdeal (𝓞 F) F α) *
              (toPrincipalIdeal (𝓞 F) F α)⁻¹ := by simp
        _ = idealClassRepresentative (F := F) c *
              (toPrincipalIdeal (𝓞 F) F α)⁻¹ := by rw [hJmul]
        _ = idealClassRepresentative (F := F) c *
              toPrincipalIdeal (𝓞 F) F α⁻¹ := by rw [map_inv]
    have hprincipalδ : toPrincipalIdeal (𝓞 F) F δ =
        toPrincipalIdeal (𝓞 F) F (betaCandidate S r c * (α⁻¹) ^ 3) := by
      calc
        _ = Iδ := rfl
        _ = J ^ 3 * A := hfact
        _ = (idealClassRepresentative (F := F) c ^ 3 * A) *
              toPrincipalIdeal (𝓞 F) F (α⁻¹ ^ 3) := by
                rw [hJrel, mul_pow]
                rw [map_pow]
                simp [mul_comm, mul_left_comm]
        _ = _ := by rw [← hbeta]; simp [map_mul, map_pow]
    let cand : Fˣ := betaCandidate S r c * (α⁻¹) ^ 3
    let z : Fˣ := δ * cand⁻¹
    have hz : toPrincipalIdeal (𝓞 F) F z = 1 := by
      simp [z, cand, map_mul, map_inv, hprincipalδ]
    obtain ⟨u0, hu0⟩ :=
      (RayClass.toPrincipalIdeal_eq_one_iff_mem_integralUnits z).mp hz
    let u : unitCubeClass F := QuotientGroup.mk u0
    let uRep : (𝓞 F)ˣ := Quotient.out u
    have huRep : (QuotientGroup.mk uRep : unitCubeClass F) = QuotientGroup.mk u0 := by
      change (QuotientGroup.mk (Quotient.out u) : unitCubeClass F) = QuotientGroup.mk u0
      rw [QuotientGroup.out_eq' u]
    let N := (powMonoidHom (α := (𝓞 F)ˣ) 3).range
    let M := (powMonoidHom (α := Fˣ) 3).range
    let emb := (Units.map (algebraMap (𝓞 F) F).toMonoidHom : (𝓞 F)ˣ →* Fˣ)
    have hpow : N ≤ M.comap emb := by
      rintro _ ⟨x, rfl⟩
      exact ⟨emb x, by simp [powMonoidHom_apply, map_pow]⟩
    let φ := QuotientGroup.map N M emb hpow
    have huMap := congrArg φ huRep
    have huMap' : (QuotientGroup.mk (emb uRep) : CubeClass F) =
        QuotientGroup.mk (emb u0) := by
      simpa [φ, N, M] using huMap
    have hu0' : emb u0 = δ * cand⁻¹ := by
      simpa [z, RayClass.integralUnitToFieldUnit, emb] using hu0
    have hδ : δ = emb u0 * cand := by
      calc
        δ = (δ * cand⁻¹) * cand := by group
        _ = emb u0 * cand := by rw [← hu0']
    have hunitRatio0 : emb uRep / emb u0 ∈ M :=
      (QuotientGroup.eq_iff_div_mem (N := M)).mp huMap'
    have hunitRatio : emb u0 / emb uRep ∈ M := by
      simpa [div_eq_mul_inv, mul_comm] using M.inv_mem hunitRatio0
    have hcubeMem : (α⁻¹) ^ 3 ∈ M :=
      ⟨α⁻¹, by simp [powMonoidHom_apply]⟩
    have hratioEq : δ / (betaCandidate S r c * emb uRep) =
        (α⁻¹) ^ 3 * (emb u0 / emb uRep) := by
      rw [hδ]
      dsimp only [cand]
      simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
    have hratio : δ / (betaCandidate S r c * emb uRep) ∈ M := by
      rw [hratioEq]
      exact M.mul_mem hcubeMem hunitRatio
    have hclass : (QuotientGroup.mk δ : CubeClass F) =
        QuotientGroup.mk (betaCandidate S r c * emb uRep) := by
      exact (QuotientGroup.eq_iff_div_mem (N := M)).2 hratio
    refine ⟨(r, c, u), ?_⟩
    change selmerCandidate S r c u = q
    calc
      selmerCandidate S r c u = QuotientGroup.mk δ := hclass.symm
      _ = q := QuotientGroup.out_eq' q
  have hH : (H : Set (CubeClass F)).Finite := hrange.subset hcover
  letI : Fintype H := hH.fintype
  exact inferInstance

end ArtinPrimitiveRoots.A1.Theta
