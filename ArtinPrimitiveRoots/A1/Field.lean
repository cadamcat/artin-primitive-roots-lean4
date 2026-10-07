import Mathlib

/-!
# A1 interface, §0–1: field data, the finite set S, S-integers

Frozen interface of part A1 (paper §§2, 2a, 3, App. 10). Each `sorry` is owned by a package of
`research/design/A1-DESIGN.md` §3, named in its docstring. Design: `research/design/A1-Interface.lean`
(Opus A1 sub-agent, 2026-10-07).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1

/-! ## 0. Field data (def:ar-field; resolves D1) -/

/-- A1's field: a number field with a primitive 12th root of unity, and one fixed complex
embedding `σ0` through which every root-of-unity–valued symbol is read (A1 defect D1).
Cyclotomicity is not assumed (A1-DESIGN §1, Q4). -/
structure FieldData (F : Type) [Field F] [NumberField F] where
  ζ12 : F
  hζ12 : IsPrimitiveRoot ζ12 12
  σ0 : F →+* ℂ

/-- Part B's fields `ℚ(μ_n)`, `12 ∣ n`, contain a primitive 12th root of unity. -/
theorem cyclotomic_has_primitive_twelfth_root (n : ℕ) [NeZero n] (h : 12 ∣ n) :
    ∃ ζ : CyclotomicField n ℚ, IsPrimitiveRoot ζ 12 := by
  have : NeZero ((n : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne n)⟩
  have : IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ) :=
    CyclotomicField.isCyclotomicExtension n ℚ
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ (CyclotomicField n ℚ)
  obtain ⟨k, hk⟩ := h
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact NeZero.ne n (by simpa using hk)
  refine ⟨IsCyclotomicExtension.zeta n ℚ (CyclotomicField n ℚ) ^ k, ?_⟩
  have h2 := hζ.pow_of_dvd hk0 (by rw [hk]; exact dvd_mul_left k 12)
  have h3 : n / k = 12 := by
    rw [hk]; exact Nat.mul_div_cancel 12 (Nat.pos_of_ne_zero hk0)
  rwa [h3] at h2

/-- The instance of `FieldData` used by Part B (`F_q = ℚ(μ_{12q})`), for any choice of `σ0`. -/
def cyclotomicFieldData (n : ℕ) [NeZero n] (h : 12 ∣ n) (σ0 : CyclotomicField n ℚ →+* ℂ) :
    FieldData (CyclotomicField n ℚ) where
  ζ12 := (cyclotomic_has_primitive_twelfth_root n h).choose
  hζ12 := (cyclotomic_has_primitive_twelfth_root n h).choose_spec
  σ0 := σ0

variable {F : Type} [Field F] [NumberField F]

/-- `μ12 ⊂ F` forces `F` totally complex. Package P-ARITH-BASE. -/
theorem FieldData.isTotallyComplex (D : FieldData F) : IsTotallyComplex F := by
  refine ⟨fun v => ?_⟩
  rw [InfinitePlace.isComplex_iff]
  intro hreal
  let ι : F →+* ℝ := hreal.embedding
  have hprim : IsPrimitiveRoot (ι D.ζ12) 12 :=
    IsPrimitiveRoot.map_of_injective (f := ι) D.hζ12 (RingHom.injective ι)
  have hsq : ((ι D.ζ12) ^ 6) ^ 2 = 1 := by
    calc
      ((ι D.ζ12) ^ 6) ^ 2 = (ι D.ζ12) ^ (6 * 2) := by rw [pow_mul]
      _ = (ι D.ζ12) ^ 12 := by norm_num
      _ = 1 := hprim.pow_eq_one
  have hnonneg : 0 ≤ (ι D.ζ12) ^ 6 := by positivity
  rcases sq_eq_one_iff.mp hsq with h | h
  · exact hprim.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num) h
  · have : (ι D.ζ12) ^ 6 = -1 := h
    linarith

/-- Number of complex places, `r = [F:ℚ]/2`. -/
def numComplex (F : Type) [Field F] [NumberField F] : ℕ := Fintype.card (InfinitePlace F)

/-! ## 1. Places, the finite set `S`, S-integers (def:ar-S, def:ar-notation) -/

/-- Finite places of `F`. -/
abbrev FinPlace (F : Type) [Field F] [NumberField F] := HeightOneSpectrum (𝓞 F)

/-- The finite set `S` (its finite part `Sf`; all complex places are in `S` implicitly).
Choice order (A1-DESIGN §2.1): `CE` (A2's absolute Euler cutoff, `po:H-local-bounds`) and the
conductor `condη` of the target character are fixed first; then `S`; everything else after.
Item (v) of def:ar-S (theta-exceptional places) is empty in route C beyond the places over 3. -/
structure SData (F : Type) [Field F] [NumberField F] (CE : ℕ) (condη : Ideal (𝓞 F)) where
  Sf : Finset (FinPlace F)
  over6 : ∀ v : FinPlace F, (6 : 𝓞 F) ∈ v.asIdeal → v ∈ Sf
  cond_mem : ∀ v : FinPlace F, condη ≤ v.asIdeal → v ∈ Sf
  different_mem : ∀ v : FinPlace F, differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → v ∈ Sf
  euler_mem : ∀ v : FinPlace F, Ideal.absNorm v.asIdeal ≤ CE → v ∈ Sf
  pid : IsPrincipalIdealRing ((Sf : Set (FinPlace F)).integer F)

/-- Existence of `S` (add class-group generators). Package P-ARITH-BASE. -/
theorem SData.nonempty (CE : ℕ) (condη : Ideal (𝓞 F)) (hη : condη ≠ ⊥) :
    Nonempty (SData F CE condη) := by
  sorry

variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- `R = O_S`. -/
abbrev SData.R (S : SData F CE condη) : Subalgebra (𝓞 F) F :=
  ((S.Sf : Set (FinPlace F))).integer F

/-- `U_S = R^×`, as a subgroup of `Fˣ`. -/
abbrev SData.US (S : SData F CE condη) : Subgroup Fˣ :=
  ((S.Sf : Set (FinPlace F))).unit F

/-- Exterior ideal: a nonzero `O_F`-ideal prime to `S_f` (≅ a nonzero ideal of `R`). -/
def SData.IsExterior (S : SData F CE condη) (I : Ideal (𝓞 F)) : Prop :=
  I ≠ ⊥ ∧ ∀ v ∈ S.Sf, ¬ I ≤ v.asIdeal

/-- `c ∈ F^×` generates the exterior ideal `I` in `R`: equal valuations at all `v ∉ S`.
Corrected per rev-theta to require that `I` is exterior. -/
def SData.IsGen (S : SData F CE condη) (c : F) (I : Ideal (𝓞 F)) : Prop :=
  S.IsExterior I ∧ c ≠ 0 ∧ ∀ v : FinPlace F, v ∉ S.Sf →
    FractionalIdeal.count F v (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) c) =
      FractionalIdeal.count F v (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)

/-- `F_S = Π_{v∈S_f} F_v × Π_{w complex} ℂ` (complex places through `w.embedding`). -/
abbrev SData.FS (S : SData F CE condη) : Type :=
  (∀ v : S.Sf, v.1.adicCompletion F) × (InfinitePlace F → ℂ)

/-- Diagonal embedding `F → F_S`. -/
def SData.diag (S : SData F CE condη) : F →+* S.FS :=
  RingHom.prod (RingHom.pi fun v : S.Sf => algebraMap F (v.1.adicCompletion F))
    (RingHom.pi fun w : InfinitePlace F => w.embedding)

/-- Diagonal embedding on units. -/
def SData.diagU (S : SData F CE condη) : Fˣ →* S.FSˣ :=
  Units.map S.diag.toMonoidHom

/-- Normalized absolute value at a finite place: `‖x‖_v = (Nv)^{-v(x)}`. -/
def absFin (v : FinPlace F) (x : v.adicCompletion F) : ℝ :=
  if h : (Ideal.absNorm v.asIdeal : NNReal) ≠ 0 then
    (WithZeroMulInt.toNNReal h (Valued.v x) : ℝ) else 0

/-- `‖y‖_S = Π_{v∈S} ‖y_v‖_v` (complex: square of the modulus, def:ar-abs). -/
def SData.absS (S : SData F CE condη) (y : S.FS) : ℝ :=
  (∏ v : S.Sf, absFin v.1 (y.1 v)) * ∏ w : InfinitePlace F, Complex.normSq (y.2 w)

/-- Norm section `ℓ_T`: finite components 1, component `T^{1/(2r)}` at each complex place.
Corrected per rev-theta to require fixed field data and `T > 0`. -/
def SData.ell (D : FieldData F) (S : SData F CE condη) (T : ℝ) (hT : 0 < T) : S.FS :=
  (fun _ => 1, fun _ => ((T ^ ((1 : ℝ) / (2 * numComplex F)) : ℝ) : ℂ))

/-- `𝒱 = F_S^×/F_S^{×6}`. -/
abbrev SData.V (S : SData F CE condη) : Type :=
  S.FSˣ ⧸ (powMonoidHom 6 : S.FSˣ →* S.FSˣ).range

/-- Component of an `F_S`-unit at a finite place of `S`. -/
def SData.compU (S : SData F CE condη) (v : S.Sf) : S.FSˣ →* (v.1.adicCompletion F)ˣ :=
  Units.map ((Pi.evalMonoidHom (fun v : S.Sf => v.1.adicCompletion F) v).comp
    (MonoidHom.fst _ _))

/-- Component of an `F_S`-unit at a complex place. -/
def SData.compC (S : SData F CE condη) (w : InfinitePlace F) : S.FSˣ →* ℂˣ :=
  Units.map ((Pi.evalMonoidHom (fun _ : InfinitePlace F => ℂ) w).comp (MonoidHom.snd _ _))

/-- The unit of `F_S` equal to `z` at the complex place `w` and 1 elsewhere (rotations, T7). -/
def SData.atComplex (S : SData F CE condη) (w : InfinitePlace F) (z : ℂˣ) : S.FSˣ where
  val := (fun _ => 1, Function.update (fun _ => 1) w (z : ℂ))
  inv := (fun _ => 1, Function.update (fun _ => 1) w ((z⁻¹ : ℂˣ) : ℂ))
  val_inv := by
    ext v
    · simp
    · by_cases h : v = w
      · subst h; simp
      · simp [Function.update_of_ne h]
  inv_val := by
    ext v
    · simp
    · by_cases h : v = w
      · subst h; simp
      · simp [Function.update_of_ne h]


end ArtinPrimitiveRoots.A1
