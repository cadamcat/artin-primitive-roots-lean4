import ArtinPrimitiveRoots.Proofs.qs_nq0_sol.ResidueUnits
import ArtinPrimitiveRoots.A1.Proofs.A1_GAUSS.FiniteField

/-! Multiplicative characters realizing the frozen sextic residue symbols. -/

set_option autoImplicit false

open NumberField IsDedekindDomain

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_gauss_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

theorem residue_character_exists (D : FieldData F) (P : FinPlace F)
    (h6 : (6 : 𝓞 F) ∉ P.asIdeal) :
    ∃ χ : MulChar (𝓞 F ⧸ P.asIdeal) ℂ,
      (∀ x : 𝓞 F, χ (Ideal.Quotient.mk P.asIdeal x) =
        chi D P (algebraMap (𝓞 F) F x)) ∧ χ ^ 6 = 1 := by
  classical
  letI : P.asIdeal.IsMaximal := P.isMaximal
  letI : Field (𝓞 F ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
  let q := Ideal.Quotient.mk P.asIdeal
  let ι := algebraMap (𝓞 F) F
  obtain ⟨hcop, hne1⟩ := coprime_six_of_not_mem_six P h6
  have hinj := Ideal.rootsOfUnityMapQuot_injective (I := P.asIdeal) 6 hne1 hcop
  have hr (x : 𝓞 F) : residue P (ι x) = q x :=
    ArtinPrimitiveRoots.A2.qs_nq0_residue_algebraMap P x
  have hspec (x : 𝓞 F) (hx : q x ≠ 0) :
      q ((chiAlg P (ι x) : (𝓞 F)ˣ) : 𝓞 F) =
        q x ^ ((Ideal.absNorm P.asIdeal - 1) / 6) := by
    have hx' : residue P (ι x) ≠ 0 := by rwa [hr]
    simpa only [hr] using ArtinPrimitiveRoots.A2.qs_nq0_chiAlg_reduction D P h6 (ι x) hx'
  have hcongr (x y : 𝓞 F) (hxy : q x = q y) :
      chi D P (ι x) = chi D P (ι y) := by
    by_cases hx : q x = 0
    · have hy : q y = 0 := hxy.symm.trans hx
      simp only [chi, hr, hx, hy, if_pos, zero_mul]
    · have hy : q y ≠ 0 := by rwa [← hxy]
      have halg : chiAlg P (ι x) = chiAlg P (ι y) := by
        apply hinj
        apply Units.ext
        change q ((chiAlg P (ι x) : (𝓞 F)ˣ) : 𝓞 F) =
          q ((chiAlg P (ι y) : (𝓞 F)ˣ) : 𝓞 F)
        rw [hspec x hx, hspec y hy, hxy]
      simp only [chi, hr, if_neg hx, if_neg hy, halg]
  let f : (𝓞 F ⧸ P.asIdeal) → ℂ := fun x => chi D P (ι x.out)
  have hout (x : 𝓞 F) : f (q x) = chi D P (ι x) := by
    apply hcongr
    exact Ideal.Quotient.mk_out (q x)
  have hf0 : f 0 = 0 := by
    calc
      f 0 = f (q 0) := by rw [map_zero]
      _ = chi D P (ι 0) := hout 0
      _ = 0 := by rw [chi, hr 0, q.map_zero, if_pos rfl]
  have hf1 : f 1 = 1 := by
    have hr1 : residue P (ι 1) = 1 := (hr 1).trans q.map_one
    have halg := ArtinPrimitiveRoots.A2.qs_nq0_chiAlg_eq_one_of_residue_one P h6 (ι 1) hr1
    calc
      f 1 = f (q 1) := by rw [map_one]
      _ = chi D P (ι 1) := hout 1
      _ = 1 := by
        rw [chi, hr1, if_neg one_ne_zero, halg]
        simp only [Subgroup.coe_one, Units.val_one, map_one]
  have hmul (a b : 𝓞 F) :
      chi D P (ι (a * b)) = chi D P (ι a) * chi D P (ι b) := by
    by_cases ha : q a = 0
    · have hab : q (a * b) = 0 := by rw [map_mul, ha, zero_mul]
      simp only [chi, hr, ha, hab, if_pos, zero_mul]
    by_cases hb : q b = 0
    · have hab : q (a * b) = 0 := by rw [map_mul, hb, mul_zero]
      simp only [chi, hr, hb, hab, if_pos, mul_zero]
    have hab : q (a * b) ≠ 0 := by rw [map_mul]; exact mul_ne_zero ha hb
    have halg : chiAlg P (ι (a * b)) = chiAlg P (ι a) * chiAlg P (ι b) := by
      apply hinj
      apply Units.ext
      change q ((chiAlg P (ι (a * b)) : (𝓞 F)ˣ) : 𝓞 F) =
        q (((chiAlg P (ι a) : (𝓞 F)ˣ) : 𝓞 F) *
          ((chiAlg P (ι b) : (𝓞 F)ˣ) : 𝓞 F))
      calc
        q ((chiAlg P (ι (a * b)) : (𝓞 F)ˣ) : 𝓞 F) =
            q (a * b) ^ ((Ideal.absNorm P.asIdeal - 1) / 6) := hspec (a * b) hab
        _ = q a ^ ((Ideal.absNorm P.asIdeal - 1) / 6) *
            q b ^ ((Ideal.absNorm P.asIdeal - 1) / 6) := by rw [map_mul, mul_pow]
        _ = q (((chiAlg P (ι a) : (𝓞 F)ˣ) : 𝓞 F) *
            ((chiAlg P (ι b) : (𝓞 F)ˣ) : 𝓞 F)) := by
              rw [map_mul, hspec a ha, hspec b hb]
    simp only [chi, hr, if_neg ha, if_neg hb, if_neg hab]
    rw [halg]
    simp only [Subgroup.coe_mul, Units.val_mul, map_mul]
  have hfmul (x y : 𝓞 F ⧸ P.asIdeal) : f (x * y) = f x * f y := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := P.asIdeal) x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective (I := P.asIdeal) y
    rw [← map_mul, hout, hout, hout]
    exact hmul a b
  let χ : MulChar (𝓞 F ⧸ P.asIdeal) ℂ :=
    { toFun := f
      map_one' := hf1
      map_mul' := hfmul
      map_nonunit' := by
        intro x hx
        have hx0 : x = 0 := by simpa only [isUnit_iff_ne_zero, not_not] using hx
        subst x
        exact hf0 }
  refine ⟨χ, hout, ?_⟩
  apply MulChar.ext
  intro u
  rw [MulChar.pow_apply_coe, MulChar.one_apply_coe]
  let a := (u : 𝓞 F ⧸ P.asIdeal).out
  have ha : q a ≠ 0 := by rw [Ideal.Quotient.mk_out]; exact u.ne_zero
  have hra : residue P (ι a) ≠ 0 := by rwa [hr]
  change chi D P (ι a) ^ 6 = 1
  rw [chi, if_neg hra]
  have hroot : (((chiAlg P (ι a) : (𝓞 F)ˣ) : 𝓞 F)) ^ 6 = 1 :=
    (mem_rootsOfUnity' 6 _).mp (chiAlg P (ι a)).property
  rw [← map_pow, ← map_pow, hroot, map_one, map_one]

theorem twelve_dvd_absNorm_sub_one (D : FieldData F) (P : FinPlace F)
    (h6 : (6 : 𝓞 F) ∉ P.asIdeal) :
    12 ∣ Ideal.absNorm P.asIdeal - 1 := by
  let : P.asIdeal.IsMaximal := P.isMaximal
  let : Field (𝓞 F ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
  obtain ⟨hcop6, hne1⟩ := coprime_six_of_not_mem_six P h6
  have hcop2 : (Ideal.absNorm P.asIdeal).Coprime 2 :=
    Nat.Coprime.of_dvd_right (by decide : 2 ∣ 6) hcop6
  have hcop12 : (Ideal.absNorm P.asIdeal).Coprime 12 := by
    simpa using Nat.Coprime.mul_right hcop6 hcop2
  have hprim := D.hζ12.toInteger_isPrimitiveRoot.idealQuotient_mk
    (I := P.asIdeal) hne1 hcop12
  let u : (𝓞 F ⧸ P.asIdeal)ˣ := (hprim.isUnit (by decide)).unit
  have hprim_u : IsPrimitiveRoot u 12 := IsPrimitiveRoot.coe_units_iff.mp hprim
  have hdvd : 12 ∣ Nat.card (𝓞 F ⧸ P.asIdeal)ˣ := by
    rw [hprim_u.eq_orderOf]
    exact orderOf_dvd_natCard (x := u)
  rwa [Nat.card_units, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply] at hdvd

end ArtinPrimitiveRoots.Proofs.a1_gauss_sol
