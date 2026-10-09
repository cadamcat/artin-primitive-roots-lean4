import ArtinPrimitiveRoots.A1.Field
import ClassFieldTheory.KummerTheory.Concrete.SUnitPreparation.SUnitPowerQuotient

set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_bdata_sol
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- The image of the S-units in the sixth-power quotient has order `6 ^ (#S_f + #infinite places)`,
once a local sixth power in that image is a global sixth power of an S-unit. -/
theorem s_unit_image_cardinality (D : FieldData F) (S : SData F CE condη)
    (hinj : ∀ u : Fˣ, u ∈ S.US → (∃ x : S.FSˣ, S.diagU u = x ^ 6) →
      ∃ ε ∈ S.US, u = ε ^ 6) :
    Nat.card (S.US.map (((QuotientGroup.mk' _) : S.FSˣ →* S.V).comp S.diagU)) =
      6 ^ (S.Sf.card + numComplex F) := by
  classical
  let : CommGroup S.V := QuotientGroup.Quotient.commGroup _
  let P : Subgroup S.FSˣ := (powMonoidHom 6 : S.FSˣ →* S.FSˣ).range
  let f : Fˣ →* S.V := ((QuotientGroup.mk' P) : S.FSˣ →* S.V).comp S.diagU
  let g : S.US →* S.V := f.comp S.US.subtype
  let R : Subgroup S.US := (powMonoidHom 6 : S.US →* S.US).range
  have hrange : S.US.map f = g.range := by
    rw [show g = f.comp S.US.subtype from rfl, MonoidHom.range_comp,
      Subgroup.range_subtype]
  have hker : R = g.ker := by
    ext u
    constructor
    · rintro ⟨ε, rfl⟩
      change (QuotientGroup.mk (S.diagU ((ε ^ 6 : S.US) : Fˣ)) : S.V) = 1
      rw [Subgroup.coe_pow, map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr ⟨S.diagU (ε : Fˣ), rfl⟩
    · intro hu
      change (QuotientGroup.mk (S.diagU (u : Fˣ)) : S.V) = 1 at hu
      obtain ⟨x, hx⟩ := (QuotientGroup.eq_one_iff _).mp hu
      obtain ⟨ε, hε, heq⟩ := hinj u u.2 ⟨x, hx.symm⟩
      refine ⟨⟨ε, hε⟩, ?_⟩
      exact Subtype.ext heq.symm
  let e := QuotientGroup.liftEquiv (H := g.range) R
    (φ := g.rangeRestrict) g.rangeRestrict_surjective
    (hker.trans g.ker_rangeRestrict.symm)
  have hroot : IsPrimitiveRoot (D.ζ12 ^ 2) 6 := by
    simpa using D.hζ12.pow_of_dvd (by norm_num : (2 : ℕ) ≠ 0) (by norm_num : 2 ∣ 12)
  let n : ℕ+ := ⟨6, by norm_num⟩
  have hmu : (primitiveRoots 6 F).Nonempty :=
    ⟨D.ζ12 ^ 2, (mem_primitiveRoots (k := 6) (by norm_num : 0 < 6)).mpr hroot⟩
  have hcard := KummerTheory.card_sUnit_nthPowerQuotient (K := F) S.Sf n hmu
  change Nat.card (S.US.map f) = _
  rw [hrange, ← Nat.card_congr e.toEquiv]
  have hpow : (powMonoidHom 6 : S.US →* S.US).range =
      (powMonoidHom (n : ℕ) : S.US →* S.US).range := rfl
  simp only [R, hpow]
  rw [hcard, KummerTheory.totalPlaceCard, numComplex]
  have hn : (n : ℕ) = 6 := rfl
  rw [hn, Nat.add_comm]

end ArtinPrimitiveRoots.Proofs.a1_bdata_sol
