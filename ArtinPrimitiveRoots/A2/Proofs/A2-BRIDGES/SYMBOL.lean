import /- Local package with a hyphenated directory name. -/ ArtinPrimitiveRoots.A2.Proofs.«A2-BRIDGES».Defs

set_option autoImplicit false
set_option maxHeartbeats 800000
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A2.BridgeSymbol
open ArtinPrimitiveRoots A1 A1.Theta
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}
local instance residueMaximal (v : FinPlace F) : v.asIdeal.IsMaximal := v.isMaximal
local instance residueField (v : FinPlace F) : Field (𝓞 F ⧸ v.asIdeal) :=
  Ideal.Quotient.field v.asIdeal

private theorem residue_rep (v : FinPlace F) (x : F) (a b : 𝓞 F)
    (hb : b ∉ v.asIdeal) (hab : x * algebraMap (𝓞 F) F b = algebraMap (𝓞 F) F a) :
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
  rw [dif_pos hex]
  rw [← div_eq_mul_inv, div_eq_div_iff hdq hbq]
  simpa only [map_mul] using hqcross

private theorem residue_algebraMap (v : FinPlace F) (a : 𝓞 F) :
    residue v (algebraMap (𝓞 F) F a) = Ideal.Quotient.mk v.asIdeal a := by
  simpa using residue_rep v _ a 1 (Ideal.IsPrime.one_notMem v.isPrime) (by simp)

private theorem residue_mul (v : FinPlace F) (x y : F)
    (hx : HeightOneSpectrum.valuation F v x ≤ 1) (hy : HeightOneSpectrum.valuation F v y ≤ 1) :
    residue v (x * y) = residue v x * residue v y := by
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  obtain ⟨a, b, hab⟩ := v.exists_primeCompl_mul_eq_of_integer x hx
  obtain ⟨c, d, hcd⟩ := v.exists_primeCompl_mul_eq_of_integer y hy
  have hbd : b.val * d.val ∉ v.asIdeal := fun h =>
    (v.isPrime.mem_or_mem h).elim b.property d.property
  have hrep : (x * y) * algebraMap (𝓞 F) F (b.val * d.val) =
      algebraMap (𝓞 F) F (a * c) := by
    rw [map_mul, map_mul, ← hab, ← hcd]
    ring
  rw [residue_rep v _ _ _ hbd hrep, residue_rep v _ _ _ b.property hab,
    residue_rep v _ _ _ d.property hcd, map_mul, map_mul]
  ring

private theorem residue_ne_zero (v : FinPlace F) (x : F)
    (hx : HeightOneSpectrum.valuation F v x ≤ 1) :
    residue v x ≠ 0 ↔ HeightOneSpectrum.valuation F v x = 1 := by
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  obtain ⟨a, b, hab⟩ := v.exists_primeCompl_mul_eq_of_integer x hx
  have hbval : HeightOneSpectrum.valuation F v (algebraMap (𝓞 F) F b.val) = 1 :=
    (v.valuation_eq_one_iff_notMem (K := F) (r := b.val)).2 b.property
  have hval : HeightOneSpectrum.valuation F v x =
      HeightOneSpectrum.valuation F v (algebraMap (𝓞 F) F a) := by
    have := congrArg (HeightOneSpectrum.valuation F v) hab
    simpa only [map_mul, hbval, mul_one] using this
  rw [residue_rep v _ _ _ b.property hab, div_ne_zero_iff, hval,
    v.valuation_eq_one_iff_notMem (K := F) (r := a)]
  have hb : b.val ∉ v.asIdeal := b.property
  simp only [ne_eq, Ideal.Quotient.eq_zero_iff_mem, hb, not_false_eq_true, and_true]

private theorem residue_congr (v : FinPlace F) (x y : F)
    (hx : HeightOneSpectrum.valuation F v x ≤ 1) (hy : HeightOneSpectrum.valuation F v y ≤ 1)
    (hxy : HeightOneSpectrum.valuation F v (x - y) < 1) : residue v x = residue v y := by
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  obtain ⟨a, b, hab⟩ := v.exists_primeCompl_mul_eq_of_integer x hx
  obtain ⟨c, d, hcd⟩ := v.exists_primeCompl_mul_eq_of_integer y hy
  have hbval : HeightOneSpectrum.valuation F v (algebraMap (𝓞 F) F b.val) = 1 :=
    (v.valuation_eq_one_iff_notMem (K := F) (r := b.val)).2 b.property
  have hdval : HeightOneSpectrum.valuation F v (algebraMap (𝓞 F) F d.val) = 1 :=
    (v.valuation_eq_one_iff_notMem (K := F) (r := d.val)).2 d.property
  have hcross : algebraMap (𝓞 F) F (a * d.val - c * b.val) =
      (x - y) * algebraMap (𝓞 F) F b.val * algebraMap (𝓞 F) F d.val := by
    simp only [map_sub, map_mul]
    rw [← hab, ← hcd]
    ring
  have hmem : a * d.val - c * b.val ∈ v.asIdeal := by
    apply (v.valuation_lt_one_iff_mem (K := F) _).1
    change HeightOneSpectrum.valuation F v (algebraMap (𝓞 F) F (a * d.val - c * b.val)) < 1
    rw [hcross, map_mul, map_mul, hbval, hdval, mul_one, mul_one]
    exact hxy
  have hqcross : Ideal.Quotient.mk v.asIdeal a * Ideal.Quotient.mk v.asIdeal d.val =
      Ideal.Quotient.mk v.asIdeal c * Ideal.Quotient.mk v.asIdeal b.val := by
    have := (Ideal.Quotient.eq_zero_iff_mem).2 hmem
    simpa only [map_sub, map_mul, sub_eq_zero] using this
  rw [residue_rep v _ _ _ b.property hab, residue_rep v _ _ _ d.property hcd]
  apply (div_eq_div_iff ?_ ?_).2 hqcross
  · exact fun h => b.property ((Ideal.Quotient.eq_zero_iff_mem).1 h)
  · exact fun h => d.property ((Ideal.Quotient.eq_zero_iff_mem).1 h)

private theorem chi_congr (D : FieldData F) (v : FinPlace F) (x y : F)
    (h : residue v x = residue v y) : chi D v x = chi D v y := by
  simp only [chi, chiAlg, h]

private theorem chi_six (D : FieldData F) (v : FinPlace F) (x : F) (hx : residue v x ≠ 0) :
    chi D v x ^ (6 : ℕ) = 1 := by
  have h := congrArg Units.val ((mem_rootsOfUnity 6 (chiAlg v x : (𝓞 F)ˣ)).1 (chiAlg v x).property)
  rw [chi, if_neg hx, ← map_pow, ← map_pow]
  simpa only [Units.val_pow_eq_pow_val, Units.val_one, map_one] using
    congrArg (fun a : 𝓞 F => D.σ0 (algebraMap (𝓞 F) F a)) h

private theorem chi_norm (D : FieldData F) (v : FinPlace F) (x : F) (hx : residue v x ≠ 0) :
    ‖chi D v x‖ = 1 := by
  exact ((isOfFinOrder_iff_pow_eq_one).2 ⟨6, by norm_num, chi_six D v x hx⟩).norm_eq_one


private theorem chi_norm_le (D : FieldData F) (v : FinPlace F) (x : F) : ‖chi D v x‖ ≤ 1 := by
  by_cases hx : residue v x = 0
  · simp [chi, hx]
  · exact (chi_norm D v x hx).le

private theorem chi_zpow_norm_le (D : FieldData F) (v : FinPlace F) (x : F) (e : ℤ) :
    ‖chi D v x ^ e‖ ≤ 1 := by
  by_cases hx : residue v x = 0
  · by_cases he : e = 0
    · simp [he]
    · simp [chi, hx, zero_zpow e he]
  · simp [norm_zpow, chi_norm D v x hx]

private theorem chiPow_norm_le (D : FieldData F) (v : FinPlace F) (x : F) (e : ℤ) :
    ‖chiPow D v x e‖ ≤ 1 := by
  by_cases hx : residue v x = 0
  · simp [chiPow, hx]
  · simp [chiPow, hx, norm_zpow, chi_norm D v x hx]

private theorem localChi_of_approx (D : FieldData F) (v : FinPlace F)
    (t : (v.adicCompletion F)ˣ) (a : 𝓞 F) (ha : a ∉ v.asIdeal)
    (hta : Valued.v ((t : v.adicCompletion F) - algebraMap F _ (algebraMap (𝓞 F) F a)) < 1) :
    localChi D v t = chi D v (algebraMap (𝓞 F) F a) := by
  have hex : ∃ b : 𝓞 F, b ∉ v.asIdeal ∧
      Valued.v ((t : v.adicCompletion F) - algebraMap F _ (algebraMap (𝓞 F) F b)) < 1 :=
    ⟨a, ha, hta⟩
  have hcmp : Valued.v (algebraMap F (v.adicCompletion F)
      (algebraMap (𝓞 F) F hex.choose - algebraMap (𝓞 F) F a)) < 1 := by
    rw [map_sub]
    have h := (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).map_sub_lt hta hex.choose_spec.2
    convert h using 1 <;> ring
  have hglobal : HeightOneSpectrum.valuation F v
      (algebraMap (𝓞 F) F hex.choose - algebraMap (𝓞 F) F a) < 1 := by
    simpa only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply, v.valuedAdicCompletion_eq_valuation'] using hcmp
  have hres := residue_congr v _ _ (v.valuation_le_one hex.choose)
    (v.valuation_le_one a) hglobal
  unfold localChi
  rw [dif_pos hex]
  exact chi_congr D v _ _ hres

private theorem toLoc_isLocUnit (v : FinPlace F) (x : Fˣ)
    (hx : HeightOneSpectrum.valuation F v (x : F) = 1) : IsLocUnit v (toLoc v x) := by
  have hval : Valued.v ((toLoc v x : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
    change Valued.v (algebraMap F (v.adicCompletion F) (x : F)) = 1
    simp only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply, v.valuedAdicCompletion_eq_valuation', hx]
  constructor
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hval.le
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    simp only [Units.val_inv_eq_inv_val, map_inv₀, hval, inv_one, le_refl]

private theorem localChi_global (D : FieldData F) (v : FinPlace F) (x : Fˣ)
    (hx : HeightOneSpectrum.valuation F v (x : F) = 1) :
    localChi D v (toLoc v x) = chi D v (x : F) := by
  obtain ⟨a, ha⟩ := v.exists_valuation_sub_lt_of_integer hx.le (1 : (WithZero (Multiplicative ℤ))ˣ)
  simp only [Units.val_one] at ha
  have haval : HeightOneSpectrum.valuation F v (algebraMap (𝓞 F) F a) = 1 := by
    have hlt : HeightOneSpectrum.valuation F v (algebraMap (𝓞 F) F a - (x : F)) <
        HeightOneSpectrum.valuation F v (x : F) := by rwa [hx]
    exact ((HeightOneSpectrum.valuation F v).map_eq_of_sub_lt hlt).trans hx
  have hamem : a ∉ v.asIdeal := (v.valuation_eq_one_iff_notMem (K := F)).1 haval
  have hta : Valued.v ((toLoc v x : (v.adicCompletion F)ˣ).val -
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) < 1 := by
    change Valued.v (algebraMap F (v.adicCompletion F) (x : F) -
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) < 1
    rw [← map_sub]
    simpa only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply, v.valuedAdicCompletion_eq_valuation', Valuation.map_sub_swap] using ha
  rw [localChi_of_approx D v _ a hamem hta]
  apply chi_congr
  exact residue_congr v _ _ (v.valuation_le_one a) hx.le ha

private theorem chi_mul (D : FieldData F) (S : SData F CE condη)
    (v : FinPlace F) (hv : v ∉ S.Sf) (x y : F)
    (hx : HeightOneSpectrum.valuation F v x ≤ 1)
    (hy : HeightOneSpectrum.valuation F v y ≤ 1) :
    chi D v (x * y) = chi D v x * chi D v y := by
  by_cases hx0 : residue v x = 0
  · simp [chi, hx0, residue_mul v x y hx hy]
  by_cases hy0 : residue v y = 0
  · simp [chi, hy0, residue_mul v x y hx hy]
  have hxv := (residue_ne_zero v x hx).1 hx0
  have hyv := (residue_ne_zero v y hy).1 hy0
  have hxne : x ≠ 0 := by intro h; simp [h] at hxv
  have hyne : y ≠ 0 := by intro h; simp [h] at hyv
  let a : Fˣ := Units.mk0 x hxne
  let b : Fˣ := Units.mk0 y hyne
  have habv : HeightOneSpectrum.valuation F v ((a * b : Fˣ) : F) = 1 := by
    simp only [Units.val_mul, Units.val_mk0, map_mul, a, b, hxv, hyv, mul_one]
  have h6 : (6 : 𝓞 F) ∉ v.asIdeal := fun h => hv (S.over6 v h)
  have h := (localChi_basic (D := D) (v := v) h6).2.2.1 (toLoc v a) (toLoc v b)
    (toLoc_isLocUnit v a hxv) (toLoc_isLocUnit v b hyv)
  rw [← map_mul, localChi_global D v (a * b) habv,
    localChi_global D v a hxv, localChi_global D v b hyv] at h
  exact h

private theorem chi_minus_one (D : FieldData F) (S : SData F CE condη)
    (v : FinPlace F) (hv : v ∉ S.Sf) : chi D v (-1) = 1 := by
  have h6 : (6 : 𝓞 F) ∉ v.asIdeal := fun h => hv (S.over6 v h)
  have h := (localChi_basic (D := D) (v := v) h6).2.1
  have hv1 : HeightOneSpectrum.valuation F v ((-1 : Fˣ) : F) = 1 := by simp
  have heq := localChi_global D v (-1) hv1
  have ht : toLoc v (-1) = (-1 : (v.adicCompletion F)ˣ) := by
    ext
    simp [toLoc]
  rw [ht] at heq
  exact heq.symm.trans h

private theorem localChi_norm_le (D : FieldData F) (v : FinPlace F)
    (t : (v.adicCompletion F)ˣ) : ‖localChi D v t‖ ≤ 1 := by
  unfold localChi
  split_ifs with h
  · exact chi_norm_le D v _
  · simp

private theorem localChi_six (D : FieldData F) (S : SData F CE condη)
    (v : FinPlace F) (hv : v ∉ S.Sf) (t : (v.adicCompletion F)ˣ) (ht : IsLocUnit v t) :
    localChi D v t ^ (6 : ℕ) = 1 :=
  (localChi_basic (D := D) (v := v) (fun h => hv (S.over6 v h))).2.2.2.1 t ht

private theorem localChi_norm (D : FieldData F) (S : SData F CE condη)
    (v : FinPlace F) (hv : v ∉ S.Sf) (t : (v.adicCompletion F)ˣ) (ht : IsLocUnit v t) :
    ‖localChi D v t‖ = 1 :=
  ((isOfFinOrder_iff_pow_eq_one).2 ⟨6, by norm_num, localChi_six D S v hv t ht⟩).norm_eq_one

private theorem norm_multiset_map_prod_le_one {α : Type*} (s : Multiset α) (f : α → ℂ)
    (hf : ∀ x, x ∈ s → ‖f x‖ ≤ 1) : ‖(s.map f).prod‖ ≤ 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, norm_mul]
    exact mul_le_one₀ (hf a (by simp)) (norm_nonneg _) (ih fun x hx => hf x (Multiset.mem_cons_of_mem hx))

private theorem ideal_norm_le (D : FieldData F) (I : Ideal (𝓞 F)) (x : F) (e : ℤ) :
    ‖chiIdealPow D I x e‖ ≤ 1 := by
  unfold chiIdealPow
  apply norm_multiset_map_prod_le_one
  intro P hP
  split_ifs with h
  · exact chiPow_norm_le D _ x e
  · simp

private theorem ideal_mul (D : FieldData F) (I J : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (x : F) (e : ℤ) : chiIdealPow D (I * J) x e = chiIdealPow D I x e * chiIdealPow D J x e := by
  have hI0 : I ≠ 0 := by simpa only [Ideal.zero_eq_bot] using hI
  have hJ0 : J ≠ 0 := by simpa only [Ideal.zero_eq_bot] using hJ
  simp only [chiIdealPow, UniqueFactorizationMonoid.normalizedFactors_mul hI0 hJ0,
    Multiset.map_add, Multiset.prod_add]

private theorem chiPow_add (D : FieldData F) (v : FinPlace F) (x : F) (e f : ℤ) :
    chiPow D v x (e + f) = chiPow D v x e * chiPow D v x f := by
  by_cases hx : residue v x = 0
  · simp [chiPow, hx]
  · have hc : chi D v x ≠ 0 := by
      intro h
      have h6 := chi_six D v x hx
      simp [h] at h6
    simp only [chiPow, if_neg hx]
    exact zpow_add₀ hc e f

private theorem ideal_add (D : FieldData F) (I : Ideal (𝓞 F)) (x : F) (e f : ℤ) :
    chiIdealPow D I x (e + f) = chiIdealPow D I x e * chiIdealPow D I x f := by
  unfold chiIdealPow
  rw [← Multiset.prod_map_mul]
  congr 1
  apply Multiset.map_congr rfl
  intro P hP
  split_ifs with h
  · exact chiPow_add D _ x e f
  · simp

private theorem ideal_zero (D : FieldData F) (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (x : F) :
    chiIdealPow D I x 0 = if ∀ v : FinPlace F, v.asIdeal ∣ I → residue v x ≠ 0 then 1 else 0 := by
  classical
  by_cases hs : ∀ v : FinPlace F, v.asIdeal ∣ I → residue v x ≠ 0
  · rw [if_pos hs]
    unfold chiIdealPow
    apply Multiset.prod_eq_one
    intro z hz
    obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.1 hz
    split_ifs with h
    · have hp := hs ⟨P, h.1, h.2⟩ (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP)
      simp [chiPow, hp]
    · rfl
  · rw [if_neg hs]
    push_neg at hs
    obtain ⟨v, hv, hx⟩ := hs
    unfold chiIdealPow
    apply Multiset.prod_eq_zero
    apply Multiset.mem_map.2
    refine ⟨v.asIdeal, ?_, ?_⟩
    · apply (UniqueFactorizationMonoid.mem_normalizedFactors_iff (by
        simpa only [Ideal.zero_eq_bot] using hI)).2
      exact ⟨v.prime, hv⟩
    · simp [v.isPrime, v.ne_bot, chiPow, hx]


private theorem chiPow_mul (D : FieldData F) (S : SData F CE condη)
    (v : FinPlace F) (hv : v ∉ S.Sf) (x y : F) (e : ℤ)
    (hx : HeightOneSpectrum.valuation F v x ≤ 1)
    (hy : HeightOneSpectrum.valuation F v y ≤ 1) :
    chiPow D v (x * y) e = chiPow D v x e * chiPow D v y e := by
  by_cases hx0 : residue v x = 0
  · simp [chiPow, hx0, residue_mul v x y hx hy]
  by_cases hy0 : residue v y = 0
  · simp [chiPow, hy0, residue_mul v x y hx hy]
  simp [chiPow, residue_mul v x y hx hy, hx0, hy0, chi_mul D S v hv x y hx hy, mul_zpow]

private theorem ideal_element_mul (D : FieldData F) (S : SData F CE condη)
    (I : Ideal (𝓞 F)) (hI : S.IsExterior I) (x y : F) (e : ℤ)
    (hxy : ∀ v : FinPlace F, v.asIdeal ∣ I →
      HeightOneSpectrum.valuation F v x ≤ 1 ∧ HeightOneSpectrum.valuation F v y ≤ 1) :
    chiIdealPow D I (x * y) e = chiIdealPow D I x e * chiIdealPow D I y e := by
  unfold chiIdealPow
  rw [← Multiset.prod_map_mul]
  congr 1
  apply Multiset.map_congr rfl
  intro P hP
  by_cases hp : P.IsPrime ∧ P ≠ ⊥
  · simp only [dif_pos hp]
    let v : FinPlace F := ⟨P, hp.1, hp.2⟩
    have hvd : v.asIdeal ∣ I := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP
    have hvS : v ∉ S.Sf := fun hv => hI.2 v hv (Ideal.le_of_dvd hvd)
    exact chiPow_mul D S v hvS x y e (hxy v hvd).1 (hxy v hvd).2
  · simp [hp]


end ArtinPrimitiveRoots.A2.BridgeSymbol


namespace ArtinPrimitiveRoots.A2
open ArtinPrimitiveRoots A1 A1.Theta
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- All support-sensitive symbol bridges.
Uses SymbolBridge, actual localChi and Theta.Shared.localChi_basic. Owned by LEAD. -/
theorem a2_bridge_SYMBOL (D : FieldData F) (S : SData F CE condη) : SymbolBridge D S := by
  refine {
    residue_algebraMap := BridgeSymbol.residue_algebraMap
    residue_congr := BridgeSymbol.residue_congr
    residue_mul := BridgeSymbol.residue_mul
    residue_ne_zero := BridgeSymbol.residue_ne_zero
    chi_mul := BridgeSymbol.chi_mul D S
    chi_congr := BridgeSymbol.chi_congr D
    chi_six := BridgeSymbol.chi_six D
    chi_norm := BridgeSymbol.chi_norm D
    chiPow_nonzero := ?_
    chiPow_zero := ?_
    chi_minus_one := BridgeSymbol.chi_minus_one D S
    chi_norm_le := BridgeSymbol.chi_norm_le D
    chi_zpow_norm_le := BridgeSymbol.chi_zpow_norm_le D
    chiPow_norm_le := BridgeSymbol.chiPow_norm_le D
    localChi_approximant := ?_
    localChi_norm_le := BridgeSymbol.localChi_norm_le D
    localChi_six := BridgeSymbol.localChi_six D S
    localChi_norm := BridgeSymbol.localChi_norm D S
    ideal_one := ?_
    ideal_norm_le := BridgeSymbol.ideal_norm_le D
    ideal_mul := BridgeSymbol.ideal_mul D
    ideal_element_mul := BridgeSymbol.ideal_element_mul D S
    ideal_exponent_add := BridgeSymbol.ideal_add D
    ideal_zero_exponent := BridgeSymbol.ideal_zero D }
  · intro v x e hx
    exact if_neg hx
  · intro v x e hx
    exact if_pos hx
  · intro v hv t ht a ha hta
    exact BridgeSymbol.localChi_of_approx D v t a ha hta
  · intro x e
    have hf : UniqueFactorizationMonoid.normalizedFactors (⊤ : Ideal (𝓞 F)) = 0 := by
      rw [← Ideal.one_eq_top, UniqueFactorizationMonoid.normalizedFactors_one]
    simp only [chiIdealPow, hf, Multiset.map_zero, Multiset.prod_zero]

end ArtinPrimitiveRoots.A2
