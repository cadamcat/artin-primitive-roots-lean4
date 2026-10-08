import ArtinPrimitiveRoots.A1.Proofs.A1_GENERATORS.Generator
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.Localization.Defs

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical nonZeroDivisors

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.A1CRT

open ArtinPrimitiveRoots.A1 ArtinPrimitiveRoots.Proofs.A1Generators

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

private def denominatorIdeal (x : F) : Ideal (𝓞 F) where
  carrier := {d | ∃ a : 𝓞 F, (d : F) * x = (a : F)}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨a', ha'⟩ ⟨b', hb'⟩
    refine ⟨a' + b', ?_⟩
    change ((a : F) + (b : F)) * x = (a' : F) + (b' : F)
    rw [add_mul, ha', hb']
  smul_mem' := by
    rintro a d ⟨b, hb⟩
    refine ⟨a * b, ?_⟩
    change ((a : F) * (d : F)) * x = (a : F) * (b : F)
    rw [mul_assoc, hb]

private theorem denominatorIdeal_mem (x : F) (d : 𝓞 F) :
    d ∈ denominatorIdeal (F := F) x ↔ ∃ a : 𝓞 F, (d : F) * x = (a : F) := Iff.rfl

private theorem denominatorIdeal_ne_bot (x : F) : denominatorIdeal (F := F) x ≠ ⊥ := by
  obtain ⟨a, b, hab⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors (𝓞 F)) x
  have hden : ((b : 𝓞 F) : F) * x = (a : 𝓞 F) := by
    rw [← hab, IsFractionRing.mk'_eq_div]
    have hb : ((b : 𝓞 F) : F) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.property
    field_simp [hb]
  have hb : (b : 𝓞 F) ∈ denominatorIdeal (F := F) x := ⟨a, hden⟩
  intro h
  have : (b : 𝓞 F) ∈ (⊥ : Ideal (𝓞 F)) := h ▸ hb
  have hbzero : (b : 𝓞 F) = 0 := by simpa using this
  exact (mem_nonZeroDivisors_iff_ne_zero.mp b.property) hbzero

private theorem denominatorIdeal_not_le (S : SData F CE condη)
    (x : S.R) (v : FinPlace F) (hv : v ∉ S.Sf) :
    ¬ denominatorIdeal (F := F) (x : F) ≤ v.asIdeal := by
  have hxv : v.valuation F (x : F) ≤ 1 := x.property v hv
  obtain ⟨n, d, hnd⟩ := v.exists_primeCompl_mul_eq_of_integer (x : F) hxv
  have hd : (d : 𝓞 F) ∈ denominatorIdeal (F := F) (x : F) := by
    rw [denominatorIdeal_mem]
    exact ⟨n, by
      change ((d : 𝓞 F) : F) * (x : F) = (n : 𝓞 F)
      rw [mul_comm]
      exact hnd⟩
  intro hle
  exact d.property (hle hd)

private theorem denominatorIdeal_pow_principal (I : Ideal (𝓞 F))
    (hI : I ≠ ⊥) :
    ∃ a : 𝓞 F, Ideal.span {a} = I ^ Fintype.card (ClassGroup (𝓞 F)) := by
  let p0 : (Ideal (𝓞 F))⁰ := ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩
  let n := Fintype.card (ClassGroup (𝓞 F))
  have hClass : ClassGroup.mk0 p0 ^ n = 1 := by
    simpa [n] using (pow_card_eq_one (x := ClassGroup.mk0 p0))
  have hn0 : I ^ n ≠ ⊥ := pow_ne_zero _ hI
  have hClassPow : ClassGroup.mk0 ⟨I ^ n, mem_nonZeroDivisors_iff_ne_zero.mpr hn0⟩ = 1 := by
    change ClassGroup.mk0 (p0 ^ n) = 1
    rw [map_pow]
    exact hClass
  have hPrincipal : (I ^ n).IsPrincipal :=
    (ClassGroup.mk0_eq_one_iff (mem_nonZeroDivisors_iff_ne_zero.mpr hn0)).mp hClassPow
  obtain ⟨a, ha⟩ := hPrincipal.principal
  exact ⟨a, ha.symm⟩

private theorem denominatorIdeal_pow_not_le (S : SData F CE condη)
    (x : S.R) (v : FinPlace F) (hv : v ∉ S.Sf) :
    ¬ denominatorIdeal (F := F) (x : F) ^ Fintype.card (ClassGroup (𝓞 F)) ≤ v.asIdeal := by
  intro hle
  have hD : denominatorIdeal (F := F) (x : F) ≤ v.asIdeal :=
    v.isPrime.le_of_pow_le hle
  exact denominatorIdeal_not_le S x v hv hD

theorem sInteger_fraction (S : SData F CE condη) (x : S.R) :
    ∃ a : 𝓞 F, ∃ d : generatorDenominators S,
      (x : F) * ((d : 𝓞 F) : F) = (a : F) := by
  classical
  let D := denominatorIdeal (F := F) (x : F)
  have hD : D ≠ ⊥ := denominatorIdeal_ne_bot (x : F)
  obtain ⟨a, ha⟩ := denominatorIdeal_pow_principal D hD
  have hpow : Ideal.span {a} = D ^ Fintype.card (ClassGroup (𝓞 F)) := ha
  have hcard : Fintype.card (ClassGroup (𝓞 F)) ≠ 0 :=
    (Fintype.card_pos : 0 < Fintype.card (ClassGroup (𝓞 F))).ne'
  have hpowle : D ^ Fintype.card (ClassGroup (𝓞 F)) ≤ D := Ideal.pow_le_self hcard
  have haDpow : a ∈ D ^ Fintype.card (ClassGroup (𝓞 F)) := by
    rw [← hpow]
    exact Ideal.subset_span (by simp)
  have haD : a ∈ D := hpowle haDpow
  obtain ⟨b, hbx⟩ := (denominatorIdeal_mem (F := F) (x : F) a).mp haD
  have ha0 : a ≠ 0 := by
    intro h
    have hpownz : D ^ Fintype.card (ClassGroup (𝓞 F)) ≠ ⊥ := pow_ne_zero _ hD
    have hbot : D ^ Fintype.card (ClassGroup (𝓞 F)) = (⊥ : Ideal (𝓞 F)) := by
      simpa [h] using hpow.symm
    exact hpownz hbot
  have hfinite (v : FinPlace F) (hv : v ∉ S.Sf) : v.valuation F (a : F) = 1 := by
    have hnotle := denominatorIdeal_pow_not_le S x v hv
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

private theorem denominator_inverse_mem (S : SData F CE condη)
    (d : generatorDenominators S) : (((d : 𝓞 F) : F)⁻¹) ∈ S.R := by
  intro v hv
  have hd := d.property.2 v hv
  rw [map_inv₀, hd]
  simp

/-- The ring of S-integers is the localization at elements supported on S. -/
theorem sInteger_isLocalization (S : SData F CE condη) :
    IsLocalization (generatorDenominators S) S.R := by
  rw [isLocalization_iff]
  constructor
  · intro d
    apply isUnit_iff_exists_inv.mpr
    refine ⟨⟨((d : 𝓞 F) : F)⁻¹, denominator_inverse_mem S d⟩, ?_⟩
    apply Subtype.ext
    change ((d : 𝓞 F) : F) * ((d : 𝓞 F) : F)⁻¹ = 1
    exact mul_inv_cancel₀ ((FaithfulSMul.algebraMap_injective (𝓞 F) F).ne d.property.1)
  constructor
  · intro x
    obtain ⟨a, d, hxd⟩ := sInteger_fraction S x
    refine ⟨(a, d), ?_⟩
    apply Subtype.ext
    change (x : F) * ((d : 𝓞 F) : F) = (a : F)
    exact hxd
  · intro a b hab
    have habF : (a : F) = (b : F) := congrArg (fun z : S.R => (z : F)) hab
    have habO : a = b := (FaithfulSMul.algebraMap_injective (𝓞 F) F) habF
    exact ⟨1, by simp [habO]⟩

end ArtinPrimitiveRoots.Proofs.A1CRT
