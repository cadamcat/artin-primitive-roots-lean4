import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.Defs
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.Localization.Defs

set_option autoImplicit false
open NumberField IsDedekindDomain ClassFieldTheory
open scoped Classical nonZeroDivisors
noncomputable section
namespace ArtinPrimitiveRoots.A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

def conductorDenominators (S : A1.SData F CE condη) : Submonoid (𝓞 F) where
  carrier := {d | d ≠ 0 ∧ ∀ v : A1.FinPlace F, v ∉ S.Sf →
    v.valuation F (d : F) = 1}
  one_mem' := by
    refine ⟨by norm_num, ?_⟩
    intro v hv
    exact v.valuation_eq_one_iff_notMem.mpr (Ideal.IsPrime.one_notMem v.isPrime)
  mul_mem' := by
    rintro a b ⟨ha, hfa⟩ ⟨hb, hfb⟩
    refine ⟨mul_ne_zero ha hb, ?_⟩
    intro v hv
    change v.valuation F ((a : F) * (b : F)) = 1
    rw [map_mul, hfa v hv, hfb v hv]
    simp

private def conductorDenominatorIdeal (x : F) : Ideal (𝓞 F) where
  carrier := {d | ∃ a : 𝓞 F, (d : F) * x = (a : F)}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨x₀, hx₀⟩ ⟨y₀, hy₀⟩
    refine ⟨x₀ + y₀, ?_⟩
    change ((a : F) + (b : F)) * x = (x₀ : F) + (y₀ : F)
    rw [add_mul, hx₀, hy₀]
  smul_mem' := by
    rintro a d ⟨x₀, hx₀⟩
    refine ⟨a * x₀, ?_⟩
    change ((a : F) * (d : F)) * x = (a : F) * (x₀ : F)
    rw [mul_assoc, hx₀]

private theorem conductorDenominatorIdeal_mem (x : F) (d : 𝓞 F) :
    d ∈ conductorDenominatorIdeal (F := F) x ↔
      ∃ a : 𝓞 F, (d : F) * x = (a : F) := Iff.rfl

private theorem conductorDenominatorIdeal_ne_bot (x : F) :
    conductorDenominatorIdeal (F := F) x ≠ ⊥ := by
  obtain ⟨a, b, hab⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors (𝓞 F)) x
  have hden : ((b : 𝓞 F) : F) * x = (a : 𝓞 F) := by
    rw [← hab, IsFractionRing.mk'_eq_div]
    have hb : ((b : 𝓞 F) : F) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.property
    field_simp [hb]
  have hb : (b : 𝓞 F) ∈ conductorDenominatorIdeal (F := F) x :=
    ⟨a, hden⟩
  intro h
  have : (b : 𝓞 F) ∈ (⊥ : Ideal (𝓞 F)) := h ▸ hb
  have hbzero : (b : 𝓞 F) = 0 := by simpa using this
  exact (mem_nonZeroDivisors_iff_ne_zero.mp b.property) hbzero

private theorem conductorDenominatorIdeal_not_le (S : A1.SData F CE condη)
    (x : S.R) (v : A1.FinPlace F) (hv : v ∉ S.Sf) :
    ¬ conductorDenominatorIdeal (F := F) (x : F) ≤ v.asIdeal := by
  have hxv : v.valuation F (x : F) ≤ 1 := x.property v hv
  obtain ⟨n, d, hnd⟩ := v.exists_primeCompl_mul_eq_of_integer (x : F) hxv
  have hd : (d : 𝓞 F) ∈ conductorDenominatorIdeal (F := F) (x : F) := by
    rw [conductorDenominatorIdeal_mem]
    exact ⟨n, by
      change ((d : 𝓞 F) : F) * (x : F) = (n : 𝓞 F)
      rw [mul_comm]
      exact hnd⟩
  intro hle
  exact d.property (hle hd)

theorem conductorDenominatorIdeal_pow_principal (I : Ideal (𝓞 F))
    (hI : I ≠ ⊥) : ∃ a : 𝓞 F,
      Ideal.span {a} = I ^ Fintype.card (ClassGroup (𝓞 F)) := by
  let p0 : (Ideal (𝓞 F))⁰ := ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩
  let n := Fintype.card (ClassGroup (𝓞 F))
  have hClass : ClassGroup.mk0 p0 ^ n = 1 := by
    simpa [n] using (pow_card_eq_one (x := ClassGroup.mk0 p0))
  have hn0 : I ^ n ≠ ⊥ := pow_ne_zero _ hI
  have hClassPow : ClassGroup.mk0
      ⟨I ^ n, mem_nonZeroDivisors_iff_ne_zero.mpr hn0⟩ = 1 := by
    change ClassGroup.mk0 (p0 ^ n) = 1
    rw [map_pow]
    exact hClass
  have hPrincipal : (I ^ n).IsPrincipal :=
    (ClassGroup.mk0_eq_one_iff (mem_nonZeroDivisors_iff_ne_zero.mpr hn0)).mp hClassPow
  obtain ⟨a, ha⟩ := hPrincipal.principal
  exact ⟨a, ha.symm⟩

private theorem conductorDenominatorIdeal_pow_not_le (S : A1.SData F CE condη)
    (x : S.R) (v : A1.FinPlace F) (hv : v ∉ S.Sf) :
    ¬ (conductorDenominatorIdeal (F := F) (x : F)) ^
        Fintype.card (ClassGroup (𝓞 F)) ≤ v.asIdeal := by
  intro hle
  have hD : conductorDenominatorIdeal (F := F) (x : F) ≤ v.asIdeal :=
    v.isPrime.le_of_pow_le hle
  exact conductorDenominatorIdeal_not_le S x v hv hD

theorem conductorSInteger_fraction (S : A1.SData F CE condη) (x : S.R) :
    ∃ a : 𝓞 F, ∃ d : conductorDenominators S,
      (x : F) * ((d : 𝓞 F) : F) = (a : F) := by
  classical
  let D := conductorDenominatorIdeal (F := F) (x : F)
  have hD : D ≠ ⊥ := conductorDenominatorIdeal_ne_bot (x : F)
  obtain ⟨a, ha⟩ := conductorDenominatorIdeal_pow_principal D hD
  have hpow : Ideal.span {a} = D ^ Fintype.card (ClassGroup (𝓞 F)) := ha
  have hcard : Fintype.card (ClassGroup (𝓞 F)) ≠ 0 :=
    (Fintype.card_pos : 0 < Fintype.card (ClassGroup (𝓞 F))).ne'
  have hpowle : D ^ Fintype.card (ClassGroup (𝓞 F)) ≤ D :=
    Ideal.pow_le_self hcard
  have haDpow : a ∈ D ^ Fintype.card (ClassGroup (𝓞 F)) := by
    rw [← hpow]
    exact Ideal.subset_span (by simp)
  have haD : a ∈ D := hpowle haDpow
  obtain ⟨b, hbx⟩ := (conductorDenominatorIdeal_mem (x : F) a).mp haD
  have ha0 : a ≠ 0 := by
    intro h
    have hpownz : D ^ Fintype.card (ClassGroup (𝓞 F)) ≠ ⊥ := pow_ne_zero _ hD
    have hbot : D ^ Fintype.card (ClassGroup (𝓞 F)) = (⊥ : Ideal (𝓞 F)) := by
      simpa [h] using hpow.symm
    exact hpownz hbot
  have hfinite (v : A1.FinPlace F) (hv : v ∉ S.Sf) :
      v.valuation F (a : F) = 1 := by
    have hnotle := conductorDenominatorIdeal_pow_not_le S x v hv
    have hnotmem : a ∉ v.asIdeal := by
      intro hamem
      apply hnotle
      rw [← hpow]
      exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hamem)
    exact v.valuation_eq_one_iff_notMem.mpr hnotmem
  refine ⟨b, ⟨a, ⟨ha0, hfinite⟩⟩, ?_⟩
  change (x : F) * ((a : 𝓞 F) : F) = (b : F)
  rw [mul_comm]
  exact hbx

private theorem conductorDenominator_inverse_mem (S : A1.SData F CE condη)
    (d : conductorDenominators S) :
    (((d : 𝓞 F) : F)⁻¹) ∈ S.R := by
  intro v hv
  have hd := d.property.2 v hv
  rw [map_inv₀, hd]
  simp

theorem conductorSInteger_isLocalization (S : A1.SData F CE condη) :
    IsLocalization (conductorDenominators S) S.R := by
  rw [isLocalization_iff]
  constructor
  · intro d
    apply isUnit_iff_exists_inv.mpr
    refine ⟨⟨((d : 𝓞 F) : F)⁻¹, conductorDenominator_inverse_mem S d⟩, ?_⟩
    apply Subtype.ext
    change ((d : 𝓞 F) : F) * ((d : 𝓞 F) : F)⁻¹ = 1
    exact mul_inv_cancel₀ ((FaithfulSMul.algebraMap_injective (𝓞 F) F).ne d.property.1)
  constructor
  · intro x
    obtain ⟨a, d, hxd⟩ := conductorSInteger_fraction S x
    refine ⟨(a, d), ?_⟩
    apply Subtype.ext
    change (x : F) * ((d : 𝓞 F) : F) = (a : F)
    exact hxd
  · intro a b hab
    have habF : (a : F) = (b : F) := congrArg (fun z : S.R => (z : F)) hab
    have habO : a = b := (FaithfulSMul.algebraMap_injective (𝓞 F) F) habF
    exact ⟨1, by simp [habO]⟩

private theorem conductorDenominator_quotient_isUnit (S : A1.SData F CE condη)
    (q : S.ExtIdeal) (d : conductorDenominators S) :
    IsUnit (Ideal.Quotient.mk q.1 (d : 𝓞 F)) := by
  have htop : Ideal.span {(d : 𝓞 F)} ⊔ q.1 = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    have hqM : q.1 ≤ M := le_trans le_sup_right hle
    have hM0 : M ≠ ⊥ := by
      intro hMbot
      exact q.2.1 (bot_unique (by simpa [hMbot] using hqM))
    let v : A1.FinPlace F := ⟨M, hM.isPrime, hM0⟩
    by_cases hvS : v ∈ S.Sf
    · exact q.2.2 v hvS (by simpa [v] using hqM)
    · have hdv := d.property.2 v hvS
      have hnotmem : (d : 𝓞 F) ∉ v.asIdeal := v.valuation_eq_one_iff_notMem.mp hdv
      have hspan : Ideal.span {(d : 𝓞 F)} ≤ v.asIdeal := by
        exact le_trans le_sup_left hle
      exact hnotmem (hspan (Ideal.subset_span (by simp)))
  have hcop : IsCoprime (Ideal.span {(d : 𝓞 F)}) q.1 :=
    Ideal.isCoprime_iff_sup_eq.mpr htop
  have hone : (1 : 𝓞 F) ∈ Ideal.span {(d : 𝓞 F)} ⊔ q.1 := by rw [htop]; exact Submodule.mem_top
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hone
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hx
  apply isUnit_iff_exists_inv.mpr
  refine ⟨Ideal.Quotient.mk q.1 c, ?_⟩
  have heq := congrArg (Ideal.Quotient.mk q.1) hxy
  rw [map_add, map_mul, map_one, Ideal.Quotient.eq_zero_iff_mem.mpr hy, add_zero] at heq
  simpa [mul_comm] using heq

private noncomputable def conductorResidueRed (S : A1.SData F CE condη)
    (q : S.ExtIdeal) : S.R →+* ConductorResidueRing q := by
  letI : IsLocalization (conductorDenominators S) S.R := conductorSInteger_isLocalization S
  exact IsLocalization.lift (M := conductorDenominators S) (S := S.R)
    (g := Ideal.Quotient.mk q.1) (conductorDenominator_quotient_isUnit S q)

/-- Exact localization comparison for the exterior residue ring. -/
private theorem conductorResidueRed_integral (S : A1.SData F CE condη)
    (q : S.ExtIdeal) (a : 𝓞 F) :
    conductorResidueRed S q (algebraMap (𝓞 F) S.R a) = Ideal.Quotient.mk q.1 a := by
  letI : IsLocalization (conductorDenominators S) S.R := conductorSInteger_isLocalization S
  simp [conductorResidueRed, IsLocalization.lift_eq]

private theorem conductorResidueRed_ker (S : A1.SData F CE condη)
    (q : S.ExtIdeal) :
    RingHom.ker (conductorResidueRed S q) =
      Ideal.map (algebraMap (𝓞 F) S.R) q.1 := by
  classical
  letI : IsLocalization (conductorDenominators S) S.R := conductorSInteger_isLocalization S
  ext x
  change conductorResidueRed S q x = 0 ↔
    x ∈ Ideal.map (algebraMap (𝓞 F) S.R) q.1
  constructor
  · intro hx
    obtain ⟨a, d, hxd⟩ := IsLocalization.exists_mk'_eq
      (conductorDenominators S) x
    have hmk : conductorResidueRed S q (IsLocalization.mk' S.R a d) = 0 := by
      rw [hxd]
      exact hx
    have ha0 : Ideal.Quotient.mk q.1 a = 0 := by
      have hspec := IsLocalization.lift_mk'_spec
        (M := conductorDenominators S) (S := S.R)
        (conductorDenominator_quotient_isUnit S q) a 0 d
      simpa [conductorResidueRed] using hspec.mp hmk
    have haq : a ∈ q.1 := Ideal.Quotient.eq_zero_iff_mem.mp ha0
    rw [← hxd]
    exact (IsLocalization.mk'_mem_map_algebraMap_iff
      (M := conductorDenominators S) (S := S.R) q.1 a d).2
        ⟨1, (conductorDenominators S).one_mem, by simpa using haq⟩
  · intro hx
    obtain ⟨y, hxd⟩ :=
      (IsLocalization.mem_map_algebraMap_iff
        (M := conductorDenominators S) (S := S.R) (I := q.1) (z := x)).mp hx
    have haq : (y.1 : 𝓞 F) ∈ q.1 := y.1.property
    have hred := congrArg (conductorResidueRed S q) hxd
    have hdunit := conductorDenominator_quotient_isUnit S q y.2
    have hzero : Ideal.Quotient.mk q.1 (y.1 : 𝓞 F) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr haq
    have hmul : conductorResidueRed S q x *
        Ideal.Quotient.mk q.1 (y.2 : 𝓞 F) = 0 := by
      rw [map_mul, conductorResidueRed_integral S q (y.2 : 𝓞 F),
        conductorResidueRed_integral S q (y.1 : 𝓞 F), hzero] at hred
      exact hred
    exact (IsUnit.mul_left_eq_zero hdunit).mp hmul

private theorem conductorResidueRed_surjective (S : A1.SData F CE condη)
    (q : S.ExtIdeal) : Function.Surjective (conductorResidueRed S q) := by
  intro y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨algebraMap (𝓞 F) S.R a, conductorResidueRed_integral S q a⟩

/-- Localization away from S identifies R/qR with O_F/q; include the unit
modulus and do not choose a junk residue for an element with a denominator.
Uses exterior coprimality; feeds primitive_conductor_residue_bridge. -/
theorem conductor_residues_exists (S : A1.SData F CE condη) :
    Nonempty (ConductorResidues S) := by
  classical
  exact ⟨{
    red := conductorResidueRed S
    integral := conductorResidueRed_integral S
    ker := conductorResidueRed_ker S
    surjective := conductorResidueRed_surjective S
  }⟩

end ArtinPrimitiveRoots.A2
