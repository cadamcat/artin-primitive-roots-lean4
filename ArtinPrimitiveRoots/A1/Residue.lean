import ArtinPrimitiveRoots.A1.Field

/-!
# A1 interface, §2: residue symbols

Frozen interface of part A1 (paper §§2, 2a, 3, App. 10). Each `sorry` is owned by a package of
`research/design/A1-DESIGN.md` §3, named in its docstring. Design: `research/design/A1-Interface.lean`
(Opus A1 sub-agent, 2026-10-07).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-! ## 2. Residue symbols (def:ar-residue-symbol; read through `σ0`) -/

/-- Residue of a `P`-integral element of `F` in `O_F/P` (0 if not `P`-integral). -/
def residue (P : FinPlace F) (x : F) : 𝓞 F ⧸ P.asIdeal :=
  letI : P.asIdeal.IsMaximal := P.isMaximal
  letI : Field (𝓞 F ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
  if h : ∃ ab : 𝓞 F × 𝓞 F, ab.2 ∉ P.asIdeal ∧ x * algebraMap (𝓞 F) F ab.2 = algebraMap (𝓞 F) F ab.1
  then Ideal.Quotient.mk P.asIdeal h.choose.1 * (Ideal.Quotient.mk P.asIdeal h.choose.2)⁻¹
  else 0

/-- The sextic residue symbol at `P` as a root of unity of `O_F`:
the unique `ζ ∈ μ6` with `ζ ≡ x^{(NP-1)/6} mod P` (1 if no such root, e.g. `x ≡ 0`). -/
def chiAlg (P : FinPlace F) (x : F) : rootsOfUnity 6 (𝓞 F) :=
  if h : ∃ ζ : rootsOfUnity 6 (𝓞 F),
      Ideal.Quotient.mk P.asIdeal ((ζ : (𝓞 F)ˣ) : 𝓞 F) =
        residue P x ^ ((Ideal.absNorm P.asIdeal - 1) / 6)
  then h.choose else 1

/-- `χ_P(x) ∈ ℂ`: `σ0(chiAlg P x)` if `x` is a `P`-unit, else `0` (02:237–244). -/
def chi (D : FieldData F) (P : FinPlace F) (x : F) : ℂ :=
  if residue P x = 0 then 0
  else D.σ0 (algebraMap (𝓞 F) F ((chiAlg P x : (𝓞 F)ˣ) : 𝓞 F))

/-- `χ_P(x)^j` with the zero convention (also for `6 ∣ j`), `j ∈ ℤ` (02:245–247). -/
def chiPow (D : FieldData F) (P : FinPlace F) (x : F) (j : ℤ) : ℂ :=
  if residue P x = 0 then 0 else chi D P x ^ j

/-- `χ_I(x)^j = Π_{P^k ∥ I} χ_P(x)^{jk}` over the prime factorization of `I` (02:248–255);
`χ_{O_F} = 1`. -/
def chiIdealPow (D : FieldData F) (I : Ideal (𝓞 F)) (x : F) (j : ℤ) : ℂ :=
  ((UniqueFactorizationMonoid.normalizedFactors I).map fun P =>
    if h : P.IsPrime ∧ P ≠ ⊥ then chiPow D ⟨P, h.1, h.2⟩ x j else 1).prod

lemma coprime_six_of_not_mem_six (P : FinPlace F) (hP : (6 : 𝓞 F) ∉ P.asIdeal) :
    (Ideal.absNorm P.asIdeal).Coprime 6 ∧ Ideal.absNorm P.asIdeal ≠ 1 := by
  have : P.asIdeal.IsMaximal := P.isMaximal
  obtain ⟨p, n, hn, hpP, hpPrime, hpNorm⟩ := Ideal.exists_prime_and_absNorm_eq_pow P.asIdeal
  have hp6 : ¬ p ∣ 6 := by
    intro hdvd
    obtain ⟨k, hk⟩ := hdvd
    have : (6 : 𝓞 F) ∈ P.asIdeal := by
      have h6 : (6 : 𝓞 F) = (p : 𝓞 F) * (k : 𝓞 F) := by
        rw [← Nat.cast_mul, ← hk, Nat.cast_ofNat]
      rw [h6]
      exact Ideal.mul_mem_right _ _ hpP
    exact hP this
  have hpc : p.Coprime 6 := (Nat.Prime.coprime_iff_not_dvd hpPrime).mpr hp6
  have hnorm_c : (Ideal.absNorm P.asIdeal).Coprime 6 := by
    rw [hpNorm]
    exact Nat.Coprime.pow_left n hpc
  have hnorm_ne1 : Ideal.absNorm P.asIdeal ≠ 1 := by
    rw [hpNorm]
    exact ne_of_gt (one_lt_pow₀ (Nat.Prime.one_lt hpPrime) (ne_of_gt hn))
  exact ⟨hnorm_c, hnorm_ne1⟩

lemma six_dvd_absNorm_sub_one (D : FieldData F) (P : FinPlace F) (hP : (6 : 𝓞 F) ∉ P.asIdeal) :
    6 ∣ Ideal.absNorm P.asIdeal - 1 := by
  have : P.asIdeal.IsMaximal := P.isMaximal
  let _ := Ideal.Quotient.field P.asIdeal
  have ⟨hcop, hne1⟩ := coprime_six_of_not_mem_six P hP
  have hζ6 : IsPrimitiveRoot (D.ζ12 ^ 2) 6 := D.hζ12.pow_of_dvd (p := 2) (by decide) (by decide)
  have hprim := hζ6.toInteger_isPrimitiveRoot.idealQuotient_mk (I := P.asIdeal) hne1 hcop
  let u : (𝓞 F ⧸ P.asIdeal)ˣ := (hprim.isUnit (by decide)).unit
  have hprim_u : IsPrimitiveRoot u 6 :=
    IsPrimitiveRoot.coe_units_iff.mp hprim
  have h_dvd : 6 ∣ Nat.card (𝓞 F ⧸ P.asIdeal)ˣ := by
    rw [hprim_u.eq_orderOf]
    exact orderOf_dvd_natCard (x := u)
  rwa [Nat.card_units, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply] at h_dvd

lemma mul_div_cancel_six (N : ℕ) (h : 6 ∣ N) : 2 * (N / 6) = N / 3 := by
  rcases h with ⟨k, rfl⟩
  rw [Nat.mul_div_cancel_left _ (by decide : 6 > 0)]
  have : 6 * k = 3 * (2 * k) := by omega
  rw [this, Nat.mul_div_cancel_left _ (by decide : 3 > 0)]

/-- `χ_P²` is the cubic residue symbol (used in ar:residue-lift, 02:502–505). Package P-ARITH-GAUSS. -/
theorem chiAlg_sq_eq_cubic (D : FieldData F) (P : FinPlace F) (x : F)
    (hP : (6 : 𝓞 F) ∉ P.asIdeal) (hx : residue P x ≠ 0) :
    Ideal.Quotient.mk P.asIdeal ((((chiAlg P x) ^ 2 : rootsOfUnity 6 (𝓞 F)) : (𝓞 F)ˣ) : 𝓞 F) =
      residue P x ^ ((Ideal.absNorm P.asIdeal - 1) / 3) := by
  have : P.asIdeal.IsMaximal := P.isMaximal
  let _ := Ideal.Quotient.field P.asIdeal
  have ⟨hcop, hne1⟩ := coprime_six_of_not_mem_six P hP
  have hdvd6 := six_dvd_absNorm_sub_one D P hP
  have hζ6 : IsPrimitiveRoot (D.ζ12 ^ 2) 6 := D.hζ12.pow_of_dvd (p := 2) (by decide) (by decide)
  have hprim := hζ6.toInteger_isPrimitiveRoot.idealQuotient_mk (I := P.asIdeal) hne1 hcop
  have hru : IsUnit (residue P x) := isUnit_iff_ne_zero.mpr hx
  let r_u : (𝓞 F ⧸ P.asIdeal)ˣ := hru.unit
  have hr_pow : (residue P x ^ ((Ideal.absNorm P.asIdeal - 1) / 6)) ^ 6 = 1 := by
    rw [← pow_mul, mul_comm, Nat.mul_div_cancel' hdvd6]
    have h1 : ((r_u : 𝓞 F ⧸ P.asIdeal) ^ (Ideal.absNorm P.asIdeal - 1)) =
        (((r_u ^ (Ideal.absNorm P.asIdeal - 1) : (𝓞 F ⧸ P.asIdeal)ˣ) : 𝓞 F ⧸ P.asIdeal)) := by
      exact (Units.val_pow_eq_pow_val r_u _).symm
    have h2 : r_u ^ (Ideal.absNorm P.asIdeal - 1) = 1 := by
      have h_card : Nat.card (𝓞 F ⧸ P.asIdeal)ˣ = Ideal.absNorm P.asIdeal - 1 := by
        rw [Nat.card_units, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
      rw [← h_card]
      exact pow_card_eq_one'
    have hr_eq : (r_u : 𝓞 F ⧸ P.asIdeal) = residue P x := rfl
    rw [← hr_eq, h1, h2, Units.val_one]
  obtain ⟨i, hi, heq⟩ := hprim.eq_pow_of_pow_eq_one hr_pow
  have hζ_pow : (hζ6.toInteger ^ i) ^ 6 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ6.toInteger_isPrimitiveRoot.pow_eq_one, one_pow]
  let ζ₀ : rootsOfUnity 6 (𝓞 F) := rootsOfUnity.mkOfPowEq (hζ6.toInteger ^ i) hζ_pow
  have h_exist : ∃ ζ : rootsOfUnity 6 (𝓞 F),
      Ideal.Quotient.mk P.asIdeal ((ζ : (𝓞 F)ˣ) : 𝓞 F) =
        residue P x ^ ((Ideal.absNorm P.asIdeal - 1) / 6) := by
    refine ⟨ζ₀, ?_⟩
    have : ((ζ₀ : (𝓞 F)ˣ) : 𝓞 F) = hζ6.toInteger ^ i := rootsOfUnity.coe_mkOfPowEq hζ_pow
    rw [this, map_pow]
    exact heq
  rw [chiAlg, dif_pos h_exist]
  have hspec := h_exist.choose_spec
  have hcoe2 : ((((h_exist.choose ^ 2 : rootsOfUnity 6 (𝓞 F)) : (𝓞 F)ˣ) : 𝓞 F)) =
      (((h_exist.choose : (𝓞 F)ˣ) : 𝓞 F)) ^ 2 := by
    push_cast; rfl
  rw [hcoe2, map_pow, hspec, ← pow_mul, mul_comm, mul_div_cancel_six _ hdvd6]


end ArtinPrimitiveRoots.A1
