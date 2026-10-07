import ArtinPrimitiveRoots.A1.Residue

/-!
# A1 interface, §3: Hilbert symbols, H_S, B, allowed generators

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

/-! ## 3. Hilbert symbols (def:ar-hilbert), `H_S`, `B`, allowed generators -/

/-- Embedding of `Fˣ` into the units of a completion. -/
def toLoc (v : FinPlace F) : Fˣ →* (v.adicCompletion F)ˣ :=
  Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom

/-- Sextic Hilbert symbols in the paper's orientation `(a,b)_{6,v} = Art_v(b)(a^{1/6})/a^{1/6}`
(02:114–118), valued in `μ6(F)`. Supplied by the ClassFieldTheory package (`localHilbertSymbol`,
arguments swapped; see `A1-LibraryBridge.lean`). Complex places contribute 1. -/
structure HilbertData (F : Type) [Field F] [NumberField F] where
  hilb : (v : FinPlace F) → (v.adicCompletion F)ˣ → (v.adicCompletion F)ˣ → rootsOfUnity 6 F
  mul_left : ∀ v a a' b, hilb v (a * a') b = hilb v a b * hilb v a' b
  mul_right : ∀ v a b b', hilb v a (b * b') = hilb v a b * hilb v a b'
  skew : ∀ v a b, hilb v a b * hilb v b a = 1
  sixth_power : ∀ v a b, (∃ c : (v.adicCompletion F)ˣ, a = c ^ 6) → hilb v a b = 1
  /-- Steinberg relation `(a, 1 - a)_v = 1` (added 2026-10-07: A1 interface gap G1, needed by the
  Kubota–Kazhdan–Patterson cocycle; ClassFieldTheory `IsSteinberg`). -/
  steinberg : ∀ (v : FinPlace F) (a : (v.adicCompletion F)ˣ) (h : (1 : v.adicCompletion F) - a ≠ 0),
    hilb v a (Units.mk0 _ h) = 1
  /-- nondegenerate on `F_v^×/F_v^{×6}` (ext:neukirch-V.3.2) -/
  nondeg : ∀ v a, (∀ b, hilb v a b = 1) → ∃ c : (v.adicCompletion F)ˣ, a = c ^ 6
  /-- Hilbert reciprocity for global elements (ext:neukirch-VI.8.1) -/
  product_formula : ∀ a b : Fˣ, (Function.mulSupport fun v => hilb v (toLoc v a) (toLoc v b)).Finite ∧
    ∏ᶠ v, hilb v (toLoc v a) (toLoc v b) = 1
  /-- tame formula for global elements at `v ∤ 6` (ext:neukirch-V.3.4): for a `v`-unit `u`,
  `(u, x)_{6,v} = χ_v(u)^{v(x)}` with `χ_v(u)` the residue root of unity. -/
  tame : ∀ (v : FinPlace F), (6 : 𝓞 F) ∉ v.asIdeal → ∀ (u x : Fˣ), residue v (u : F) ≠ 0 →
    (((hilb v (toLoc v u) (toLoc v x) : Fˣ) : F)) =
      (algebraMap (𝓞 F) F (((chiAlg v (u : F)) : (𝓞 F)ˣ) : 𝓞 F)) ^
        (FractionalIdeal.count F v (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (x : F)))

/-- Existence (ClassFieldTheory: `finitePlaceHilbertSymbol`, `localHilbertSymbol_tame_formula`,
`hilbertSymbol_allPlaces_product_eq_one`). Package P-CFT-GLUE. -/
theorem HilbertData.nonempty (D : FieldData F) : Nonempty (HilbertData F) := by
  sorry

/-- `H_S(x,y) = Π_{v∈S_f} (x_v,y_v)_{6,v}` on `F_S^×` (02:129). -/
def SData.HS (S : SData F CE condη) (H : HilbertData F) (x y : S.FSˣ) : rootsOfUnity 6 F :=
  ∏ v : S.Sf, H.hilb v.1 (S.compU v x) (S.compU v y)

/-- Image `E` of `U_S` in `𝒱`. -/
def SData.E (S : SData F CE condη) : Subgroup S.V :=
  S.US.map ((QuotientGroup.mk' _).comp S.diagU)

/-- lem:balanced-generators (c): an isotropic complement `B` of `E` in `𝒱`. -/
structure BData (S : SData F CE condη) (H : HilbertData F) where
  B : Subgroup S.V
  isotropic : ∀ x y : S.FSˣ, (QuotientGroup.mk x : S.V) ∈ B → (QuotientGroup.mk y : S.V) ∈ B →
    S.HS H x y = 1
  compl : IsCompl S.E B

/-- lem:balanced-generators (a)–(c). Package P-ARITH-B. -/
theorem BData.nonempty (D : FieldData F) (S : SData F CE condη) (H : HilbertData F) :
    Nonempty (BData S H) := by
  sorry

/-- Allowed generator: class of `a` in `𝒱` lies in `B` (02:229). -/
def BData.Allowed {S : SData F CE condη} {H : HilbertData F} (Bd : BData S H) (a : Fˣ) : Prop :=
  (QuotientGroup.mk (S.diagU a) : S.V) ∈ Bd.B

/-- lem:balanced-generators (d): allowed generators exist, unique up to `U_S^6`. -/
theorem BData.exists_allowed {S : SData F CE condη} {H : HilbertData F} (Bd : BData S H)
    (I : Ideal (𝓞 F)) (hI : S.IsExterior I) :
    ∃ a : Fˣ, S.IsGen (a : F) I ∧ Bd.Allowed a := by
  sorry

theorem BData.allowed_unique {S : SData F CE condη} {H : HilbertData F} (Bd : BData S H)
    (I : Ideal (𝓞 F)) (a b : Fˣ) (ha : S.IsGen (a : F) I ∧ Bd.Allowed a)
    (hb : S.IsGen (b : F) I ∧ Bd.Allowed b) :
    ∃ ε ∈ S.US, a = ε ^ 6 * b := by
  sorry

/-- lem:balanced-generators (e): balanced generators — a compact `𝒦_bal ⊂ F_S^1` with
`a/ℓ_{q_I} ∈ 𝒦_bal` for some allowed generator of every exterior `I`.
Corrected per rev-theta to use the positive norm section under fixed field data. -/
theorem BData.exists_balanced (D : FieldData F) {S : SData F CE condη} {H : HilbertData F}
    (Bd : BData S H) :
    ∃ K : Set S.FS, IsCompact K ∧ (∀ y ∈ K, S.absS y = 1) ∧
      ∀ (I : Ideal (𝓞 F)) (hI : S.IsExterior I), ∃ a : Fˣ,
        S.IsGen (a : F) I ∧ Bd.Allowed a ∧
          S.diag (a : F) *
            S.ell D ((Ideal.absNorm I : ℝ)⁻¹) (by
              have hnorm : 0 < Ideal.absNorm I :=
                Ideal.absNorm_pos_of_nonZeroDivisors
                  ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr
                    (by simpa [Ideal.zero_eq_bot] using hI.1)⟩
              exact inv_pos.mpr (Nat.cast_pos.mpr hnorm)) ∈ K := by
  sorry

/-- eq:sextic-reciprocity (02:257–266): `χ_P(p') = χ_{P'}(p)` for allowed generators of distinct
exterior primes. Package P-ARITH-RECIP. -/
theorem sextic_reciprocity (D : FieldData F) (S : SData F CE condη) (H : HilbertData F)
    (Bd : BData S H) (P P' : FinPlace F) (hP : P ∉ S.Sf) (hP' : P' ∉ S.Sf) (hne : P ≠ P')
    (p p' : Fˣ) (hp : S.IsGen (p : F) P.asIdeal ∧ Bd.Allowed p)
    (hp' : S.IsGen (p' : F) P'.asIdeal ∧ Bd.Allowed p') :
    chi D P (p' : F) = chi D P' (p : F) := by
  sorry

/-- eq:unit-symbol (02:279–283): `χ_I(ε) = H_S(ε,a)^{-1}` (read through `σ0`). -/
theorem unit_symbol (D : FieldData F) (S : SData F CE condη) (H : HilbertData F)
    (Bd : BData S H) (I : Ideal (𝓞 F)) (hI : S.IsExterior I) (a ε : Fˣ)
    (ha : S.IsGen (a : F) I ∧ Bd.Allowed a) (hε : ε ∈ S.US) :
    chiIdealPow D I (ε : F) 1 = D.σ0 (((S.HS H (S.diagU ε) (S.diagU a))⁻¹ : Fˣ) : F) := by
  sorry


end ArtinPrimitiveRoots.A1
