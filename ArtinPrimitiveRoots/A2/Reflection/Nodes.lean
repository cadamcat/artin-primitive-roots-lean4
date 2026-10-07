import ArtinPrimitiveRoots.A2.Defs
import ArtinPrimitiveRoots.A2.QuadraticSieve
import ArtinPrimitiveRoots.A1.AddChar

/-!
# Section 4: row replacement, moving twists, S-characters, and the finite mask
-/

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Row elements in one fixed exterior ideal fiber. -/
def reflectionRowFiber (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (K : Set S.FSˣ) (t : S.FSˣ) (Z : ℝ) (hZ : 0 < Z)
    (I : ArtinPrimitiveRoots.A1.SData.ExtIdeal S) : Set (ReflectionRow S) :=
  {r | InReflectionBox D S K t Z hZ r ∧ r.ideal = I}

/-- **rf:element-to-ideal** (04-reflection.tex:19-35, 1028-1029, 1225-1227).  On every fixed
compact annulus (also after a norm-one translate from the fixed compact `T`), ideal norms are
comparable to `Z^M₀`, row fibers have bounded cardinality, and the moving unit stays in a compact
norm-one set. -/
theorem rf_element_to_ideal
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H)
    (bc : BalancedChoices D S H Bd)
    (K T : Set S.FSˣ) (hK : IsCompact K) (hT : IsCompact T)
    (hTnorm : ∀ t ∈ T, S.absS (t : S.FS) = 1) :
    ∃ c₁ c₂ C : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ 0 < C ∧
      ∃ K' : Set S.FSˣ, IsCompact K' ∧ (∀ y ∈ K', S.absS (y : S.FS) = 1) ∧
        ∀ (Z : ℝ), (hZ : 2 ≤ Z) → ∀ t, t ∈ T → ∀ r : ReflectionRow S,
          InReflectionBox D S K t Z (by linarith) r →
            c₁ * Real.rpow Z M0 ≤ idealNorm r.ideal.1 ∧
            idealNorm r.ideal.1 ≤ c₂ * Real.rpow Z M0 ∧
            S.diagU (rowEpsilon S bc r) ∈ K' ∧
            Set.ncard (reflectionRowFiber D S K t Z (by linarith) r.ideal) ≤ ⌊C⌋₊ := by
  sorry

/-- **rf:moving-twist** (04-reflection.tex:37-49).  The zeroth-power convention is A1's masked
`chiPow`, so a shared prime makes both sides vanish. -/
theorem rf_moving_twist
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H)
    (bc : BalancedChoices D S H Bd)
    (r : ReflectionRow S) (J : Ideal (𝓞 F)) (hJ : S.IsExterior J)
    (a : Fˣ) (ha : S.IsGen (a : F) J ∧ Bd.Allowed a) :
    ArtinPrimitiveRoots.A1.chiIdealPow D J (rowElement S r : F) 1 =
      ArtinPrimitiveRoots.A1.chiIdealPow D J ((rowEpsilon S bc r : Fˣ) : F) 1 *
        (∏ᶠ P : ArtinPrimitiveRoots.A1.FinPlace F,
          if P.asIdeal ∣ r.ideal.1 then
            ArtinPrimitiveRoots.A1.chiPow D P (a : F) (rowPrimeExponent S r P)
          else 1) := by
  sorry

/-- **def:rf-S-character** (04-reflection.tex:51-65): `λ_ε(y)=H_S(ε,y)⁻¹`. -/
def lambdaEpsilon (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (ε : S.US) (y : S.FSˣ) : ℂ :=
  D.σ0 (((S.HS H (S.diagU ε) y)⁻¹ : Fˣ) : F)

/-- **def:rf-S-character** (04-reflection.tex:56-65): `L_υ=L_S·λ_ε` for the chosen representative
of the class `υ`. -/
def rfSCharacter (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (ϑ : ArtinPrimitiveRoots.A1.HeckeChar F) (ε : S.US) (y : S.FSˣ) : ℂ :=
  S.LS ϑ y * lambdaEpsilon D S H ε y

/-- **rf:S-character-identity** (04-reflection.tex:58-65). Includes the allowed-generator
identity, triviality on `U_S`, and dependence only on the class modulo `U_S^6`. Corrected per
sol-gate-a2 to require the combined character to be unramified outside `S`. -/
theorem rf_S_character_identity
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H)
    (A : ArtinPrimitiveRoots.A1.AddCharData F)
    (Λ G η : ArtinPrimitiveRoots.A1.HeckeChar F)
    (hΛG : ∀ v : ArtinPrimitiveRoots.A1.FinPlace F, v ∉ S.Sf →
      ∀ p : Fˣ, S.IsGen (p : F) v.asIdeal → Bd.Allowed p →
        ArtinPrimitiveRoots.A1.gamma D S A 1 v.asIdeal p *
          ArtinPrimitiveRoots.A1.gamma D S A 2 v.asIdeal p =
            -(Λ.primeValue v * G.primeValue v))
    (ε : S.US)
    (houtside : ∀ v : ArtinPrimitiveRoots.A1.FinPlace F, v ∉ S.Sf →
      (ArtinPrimitiveRoots.A1.vartheta Λ G η).UnramifiedAt v) :
    (∀ (J : Ideal (𝓞 F)) (hJ : S.IsExterior J) (a : Fˣ),
      S.IsGen (a : F) J → Bd.Allowed a →
      rfSCharacter D S H (ArtinPrimitiveRoots.A1.vartheta Λ G η) ε (S.diagU a) =
        (ArtinPrimitiveRoots.A1.vartheta Λ G η).idealValue J *
          ArtinPrimitiveRoots.A1.chiIdealPow D J ((ε : Fˣ) : F) 1) ∧
    (∀ γ : S.US, lambdaEpsilon D S H ε (S.diagU γ) = 1) ∧
    (∀ ε' : S.US, unitSixClass S ε' = unitSixClass S ε →
      ∀ y : S.FSˣ, lambdaEpsilon D S H ε' y = lambdaEpsilon D S H ε y) := by
  sorry

/-- **def:rf-mask** (04-reflection.tex:67-87): the local additive phase for the residue digits. -/
def maskPhase (A : ArtinPrimitiveRoots.A1.AddCharData F)
    (P : ArtinPrimitiveRoots.A1.FinPlace F) (p : Fˣ)
    (t x : 𝓞 F ⧸ P.asIdeal) : ℂ :=
  A.ψ P (algebraMap F (P.adicCompletion F)
    ((algebraMap (𝓞 F) F x.out) * (algebraMap (𝓞 F) F t.out) / (p : F)))

/-- **def:rf-mask** (04-reflection.tex:72-87): the local Gauss normalizer `τ_{p,j}`. -/
def maskTau (D : ArtinPrimitiveRoots.A1.FieldData F)
    (A : ArtinPrimitiveRoots.A1.AddCharData F)
    (P : ArtinPrimitiveRoots.A1.FinPlace F) (p : Fˣ) (j : Fin 6) : ℂ :=
  ∑ᶠ v : 𝓞 F ⧸ P.asIdeal,
    if v = 0 then 0 else
      ArtinPrimitiveRoots.A1.chi D P (algebraMap (𝓞 F) F v.out) ^ (-(j.1 : ℤ)) *
        maskPhase A P p 1 v

/-- **def:rf-mask** (04-reflection.tex:67-87): the normalized Gauss coefficient `α_{p,j}`. -/
def maskAlpha (D : ArtinPrimitiveRoots.A1.FieldData F)
    (A : ArtinPrimitiveRoots.A1.AddCharData F)
    (P : ArtinPrimitiveRoots.A1.FinPlace F) (p : Fˣ) (j : Fin 6)
    (x : 𝓞 F ⧸ P.asIdeal) : ℂ :=
  if hj : j = 0 then
    if x = 0 then 1 - (Ideal.absNorm P.asIdeal : ℂ)⁻¹
    else - (Ideal.absNorm P.asIdeal : ℂ)⁻¹
  else if x = 0 then 0 else
    (maskTau D A P p j)⁻¹ *
      ArtinPrimitiveRoots.A1.chi D P (algebraMap (𝓞 F) F x.out) ^ (-(j.1 : ℤ))

/-- **rf:mask-identity** (04-reflection.tex:88-97): the finite Fourier transform of `α_{p,j}`
is the masked sextic character, including the zero-frequency convention at `j=0`. -/
theorem rf_mask_identity
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H)
    (A : ArtinPrimitiveRoots.A1.AddCharData F)
    (P : ArtinPrimitiveRoots.A1.FinPlace F) (hP : P ∉ S.Sf)
    (p : Fˣ) (hp : S.IsGen (p : F) P.asIdeal ∧ Bd.Allowed p) :
    ∀ (j : Fin 6) (t : 𝓞 F ⧸ P.asIdeal),
      ∑ᶠ x : 𝓞 F ⧸ P.asIdeal, maskAlpha D A P p j x * maskPhase A P p t x =
        ArtinPrimitiveRoots.A1.chiPow D P (algebraMap (𝓞 F) F t.out) (j.1 : ℤ) := by
  sorry

/-- **lem:reflection-quadratic-sieve** (04-reflection.tex:941-1025): the narrow quadratic sieve
in the consumer form.  Rows and columns are squarefree exterior ideals, columns carry allowed
generators, and the symbol is A1's sextic symbol cubed. -/
theorem lem_reflection_quadratic_sieve
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ Cmax Dmax : ℝ, 1 ≤ Cmax → 1 ≤ Dmax →
        ∀ (rows cols : Finset (ArtinPrimitiveRoots.A1.SData.SqfExtIdeal S))
          (cgen : ArtinPrimitiveRoots.A1.SData.SqfExtIdeal S → F),
          (∀ I ∈ rows, idealNorm I.1 ≤ Dmax) →
          (∀ I ∈ cols, idealNorm I.1 ≤ Cmax ∧
            ∃ c : Fˣ, (c : F) = cgen I ∧ S.IsGen (c : F) I.1 ∧ Bd.Allowed c) →
          ∀ z : ArtinPrimitiveRoots.A1.SData.SqfExtIdeal S → ℂ,
            ∑ I ∈ rows,
              ‖∑ J ∈ cols, z J *
                ArtinPrimitiveRoots.A1.chiIdealPow D (I.1) (cgen J) 3‖ ^ 2 ≤
              C * (Cmax + Dmax) * Real.rpow (Cmax * Dmax) ε *
                ∑ J ∈ cols, ‖z J‖ ^ 2 := by
  sorry

/-- Symbol dictionary consumed by `lem:reflection-quadratic-sieve`: cubing the sextic symbol is
the quadratic residue symbol at an exterior prime. -/
theorem chi_cube_eq_quadSymbolAt
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (P : ArtinPrimitiveRoots.A1.FinPlace F) (h6 : (6 : 𝓞 F) ∉ P.asIdeal)
    (c : 𝓞 F) (hc : ArtinPrimitiveRoots.A1.residue P (algebraMap (𝓞 F) F c) ≠ 0) :
    ArtinPrimitiveRoots.A1.chi D P (algebraMap (𝓞 F) F c) ^ 3 =
      (quadSymbolAt P c : ℂ) := by
  sorry

/-- **def:rf-active** (04-reflection.tex:433-499): a squarefree active ideal `𝔣|rad(𝔥)` must
contain every row prime whose exponent modulo six is nonzero. -/
def IsActiveFactor (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (r : ReflectionRow S) (f : Ideal (𝓞 F)) : Prop :=
  S.IsExterior f ∧ Squarefree f ∧
    (∀ P : ArtinPrimitiveRoots.A1.FinPlace F, P.asIdeal ∣ f → P.asIdeal ∣ r.h.1) ∧
    (∀ P : ArtinPrimitiveRoots.A1.FinPlace F, P.asIdeal ∣ r.h.1 →
      rowPrimeExponent S r P ≠ 0 → P.asIdeal ∣ f)

/-- **def:rf-active** (04-reflection.tex:478-499): the local Weyl coefficient envelope `β_p(e)`.
Corrected per rev-a2 to require the prime-norm domain `1 < q`. -/
def betaPrime (q : ℝ) (_hq : 1 < q) (e : ℕ) : ℝ :=
  if e = 0 then 1
  else if e % 3 = 1 then Real.rpow q (-((e / 3 : ℕ) : ℝ))
  else if e % 3 = 0 then Real.rpow q (1 / 2 - ((e / 3 : ℕ) : ℝ))
  else 0

/-- **def:rf-active** (04-reflection.tex:478-499): the local Euler sum for `β_p`. Corrected per
rev-a2 to require both `1 < q` and a summability proof. -/
def betaEulerFactor (q : ℝ) (hq : 1 < q) (σ : ℝ)
    (_hsum : Summable (fun e : ℕ =>
      ((betaPrime q hq e * Real.rpow q (-(σ * (e : ℝ))) : ℝ) : ℂ))) : ℂ :=
  ∑' e : ℕ,
    ((betaPrime q hq e * Real.rpow q (-(σ * (e : ℝ))):ℝ) : ℂ)

/-- **rf:active-support** (04-reflection.tex:433-503): for a squarefree `𝔣|rad(𝔥)`,
`q_𝔣² ≤ q_𝔥`. -/
theorem rf_active_support_norm
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (r : ReflectionRow S) (f : Ideal (𝓞 F))
    (hf : IsActiveFactor S r f) :
    (Ideal.absNorm f : ℝ) ^ 2 ≤ (Ideal.absNorm r.h.1 : ℝ) := by
  sorry

/-- **rf:powerful-count** (04-reflection.tex:1035-1044): powerful exterior ideals have count
`O_F(P^{1/2})` below norm `2P`. -/
def powerfulExteriorIdeals (S : ArtinPrimitiveRoots.A1.SData F CE condη) (P : ℝ) :
    Finset (Ideal (𝓞 F)) :=
  ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊2 * P⌋₊).toFinset).filter
    (fun I => S.IsExterior I ∧ IsPowerful I)

/-- **rf:powerful-count** (04-reflection.tex:1035-1044). -/
theorem rf_powerful_count
    (S : ArtinPrimitiveRoots.A1.SData F CE condη) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P →
      (powerfulExteriorIdeals S P).card ≤ C * Real.rpow P (1 / 2 : ℝ) := by
  sorry

/-- **def:rf-column-cutoff** (04-reflection.tex:915-931): `𝓛=8D²P/Z`. -/
def reflectionColumnLength (P D Z : ℝ) : ℝ := 8 * D ^ 2 * P / Z

/-- **def:rf-column-cutoff** (04-reflection.tex:915-931): `R₀=Z^δ𝓛`. -/
def reflectionColumnCutoff (P D Z δ : ℝ) : ℝ :=
  Real.rpow Z δ * reflectionColumnLength P D Z

end ArtinPrimitiveRoots.A2
