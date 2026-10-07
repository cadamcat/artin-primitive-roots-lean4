import ArtinPrimitiveRoots.A2.Defs
import ArtinPrimitiveRoots.A2.QuadraticSieve
import ArtinPrimitiveRoots.A1.AddChar
import ArtinPrimitiveRoots.Hecke.Elementary
import ArtinPrimitiveRoots.A2.ZeroFree.Nodes

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
def reflectionRowFiber (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (K : Set S.FSˣ) (t : S.FSˣ) (Z : ℝ)
    (I : ArtinPrimitiveRoots.A1.SData.ExtIdeal S) : Set (ReflectionRow S) :=
  {r | InReflectionBox S K t Z r ∧ r.ideal = I}

/-- **rf:element-to-ideal** (04-reflection.tex:19-35, 1028-1029, 1225-1227).  On every fixed
compact annulus (also after a norm-one translate from the fixed compact `T`), ideal norms are
comparable to `Z^M₀`, row fibers have bounded cardinality, and the moving unit stays in a compact
norm-one set. -/
theorem rf_element_to_ideal
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H)
    (bc : BalancedChoices S H Bd)
    (K T : Set S.FSˣ) (hK : IsCompact K) (hT : IsCompact T)
    (hTnorm : ∀ t ∈ T, S.absS (t : S.FS) = 1) :
    ∃ c₁ c₂ C : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ 0 < C ∧
      ∃ K' : Set S.FSˣ, IsCompact K' ∧ (∀ y ∈ K', S.absS (y : S.FS) = 1) ∧
        ∀ (Z : ℝ), 2 ≤ Z → ∀ t, t ∈ T → ∀ r : ReflectionRow S,
          InReflectionBox S K t Z r →
            c₁ * Real.rpow Z M0 ≤ idealNorm r.ideal.1 ∧
            idealNorm r.ideal.1 ≤ c₂ * Real.rpow Z M0 ∧
            S.diagU (rowEpsilon S bc r) ∈ K' ∧
            Set.ncard (reflectionRowFiber S K t Z r.ideal) ≤ ⌊C⌋₊ := by
  sorry

/-- **rf:moving-twist** (04-reflection.tex:37-49).  The zeroth-power convention is A1's masked
`chiPow`, so a shared prime makes both sides vanish. -/
theorem rf_moving_twist
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H)
    (bc : BalancedChoices S H Bd)
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

/-- **rf:S-character-identity** (04-reflection.tex:58-65).  Includes the allowed-generator
identity, triviality on `U_S`, and dependence only on the class modulo `U_S^6`. -/
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
    (ε : S.US) :
    (∀ (J : Ideal (𝓞 F)) (hJ : S.IsExterior J) (a : Fˣ),
      S.IsGen (a : F) J → Bd.Allowed a →
      rfSCharacter D S H (ArtinPrimitiveRoots.A1.vartheta Λ G η) ε (S.diagU a) =
        (ArtinPrimitiveRoots.A1.vartheta Λ G η).idealValue J *
          ArtinPrimitiveRoots.A1.chiIdealPow D J ((ε : Fˣ) : F) 1) ∧
    (∀ γ : S.US, lambdaEpsilon D S H ε (S.diagU γ) = 1) ∧
    (∀ ε' : S.US, unitSixClass S ε' = unitSixClass S ε →
      ∀ y : S.FSˣ, lambdaEpsilon D S H ε' y = lambdaEpsilon D S H ε y) := by
  classical
  have hvartheta := ArtinPrimitiveRoots.A1.vartheta_S D S A H Bd η Λ G hΛG
  refine ⟨?_, ?_, ?_⟩
  · intro J hJ a hgen hallowed
    change S.LS (ArtinPrimitiveRoots.A1.vartheta Λ G η) (S.diagU a) *
        D.σ0 (((S.HS H (S.diagU ε) (S.diagU a))⁻¹ : Fˣ) : F) = _
    rw [hvartheta.1 J a hJ hgen]
    have hsymbol := ArtinPrimitiveRoots.A1.unit_symbol D S H Bd J hJ a ε
      ⟨hgen, hallowed⟩ ε.property
    rw [← hsymbol]
  · intro γ
    have hrepr (u : S.US) (v : ArtinPrimitiveRoots.A1.FinPlace F) (hv : v ∉ S.Sf) :
        ∃ n : 𝓞 F, ∃ d : v.asIdeal.primeCompl,
          ((u : Fˣ) : F) * algebraMap (𝓞 F) F (d : 𝓞 F) = algebraMap (𝓞 F) F n ∧
            n ∉ v.asIdeal := by
      have huval : v.valuation F ((u : Fˣ) : F) = 1 := u.property v hv
      obtain ⟨n, d, hnd⟩ := v.exists_primeCompl_mul_eq_of_integer ((u : Fˣ) : F)
        (le_of_eq huval)
      have hdval : v.valuation F (algebraMap (𝓞 F) F (d : 𝓞 F)) = 1 := by
        rw [v.valuation_eq_one_iff_notMem]
        exact d.2
      have hnval : v.valuation F (algebraMap (𝓞 F) F n) = 1 := by
        rw [← hnd, map_mul, huval, hdval, one_mul]
      exact ⟨n, d, hnd, (v.valuation_eq_one_iff_notMem).mp hnval⟩
    have hcountInt (v : ArtinPrimitiveRoots.A1.FinPlace F) (m : 𝓞 F) (hm : m ≠ 0)
        (hmval : v.valuation F (algebraMap (𝓞 F) F m) = 1) :
        FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
            (algebraMap (𝓞 F) F m)) = 0 := by
      have hnot : m ∉ v.asIdeal := (v.valuation_eq_one_iff_notMem).mp hmval
      have hJ : Ideal.span {m} ≠ ⊥ := by
        intro h
        exact hm (Ideal.span_singleton_eq_bot.mp h)
      have hfac : (Associates.mk v.asIdeal).count
          (Associates.mk (Ideal.span {m})).factors = 0 := by
        by_contra hne
        have hdvd : v.asIdeal ∣ Ideal.span {m} :=
          (Associates.count_ne_zero_iff_dvd hJ v.irreducible).mp hne
        exact hnot ((Ideal.dvd_span_singleton).mp hdvd)
      rw [← FractionalIdeal.coeIdeal_span_singleton,
        FractionalIdeal.count_coe F v hJ]
      exact_mod_cast hfac
    have hcount (u : S.US) (v : ArtinPrimitiveRoots.A1.FinPlace F)
        (hv : v ∉ S.Sf) :
        FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
            ((u : Fˣ) : F)) = 0 := by
      obtain ⟨n, d, hnd, hnnot⟩ := hrepr u v hv
      have hdm : (d : 𝓞 F) ≠ 0 := by
        intro hd
        exact d.2 (by simpa [hd] using (Ideal.zero_mem v.asIdeal))
      have hmapd : algebraMap (𝓞 F) F (d : 𝓞 F) ≠ 0 :=
        (map_ne_zero_iff (algebraMap (𝓞 F) F)
          (IsFractionRing.injective (𝓞 F) F)).mpr hdm
      have hnm : n ≠ 0 := by
        intro hn
        rw [hn, map_zero] at hnd
        exact (mul_ne_zero (Units.ne_zero (u : Fˣ)) hmapd) hnd
      have hdval : v.valuation F (algebraMap (𝓞 F) F (d : 𝓞 F)) = 1 := by
        rw [v.valuation_eq_one_iff_notMem]
        exact d.2
      have hnval : v.valuation F (algebraMap (𝓞 F) F n) = 1 := by
        rw [← hnd, map_mul, u.property v hv, hdval, one_mul]
      have hcntd := hcountInt v d hdm hdval
      have hcntn := hcountInt v n hnm hnval
      have hspan :
          FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) ((u : Fˣ) : F) *
              FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
                (algebraMap (𝓞 F) F (d : 𝓞 F)) =
            FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
              (algebraMap (𝓞 F) F n) := by
        rw [FractionalIdeal.spanSingleton_mul_spanSingleton, hnd]
      have hcounts := congrArg (FractionalIdeal.count F v) hspan
      have hsu :
          FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) ((u : Fˣ) : F) ≠ 0 :=
        FractionalIdeal.spanSingleton_ne_zero_iff.mpr
          (Units.ne_zero (u : Fˣ))
      have hsd :
          FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
            (algebraMap (𝓞 F) F (d : 𝓞 F)) ≠ 0 :=
        FractionalIdeal.spanSingleton_ne_zero_iff.mpr hmapd
      rw [FractionalIdeal.count_mul F v hsu hsd,
        hcntd, hcntn, add_zero] at hcounts
      exact hcounts
    have hres (v : ArtinPrimitiveRoots.A1.FinPlace F) (hv : v ∉ S.Sf) :
        ArtinPrimitiveRoots.A1.residue v ((ε : Fˣ) : F) ≠ 0 := by
      obtain ⟨n, d, hnd, hnnot⟩ := hrepr ε v hv
      have huval : v.valuation F ((ε : Fˣ) : F) = 1 := ε.property v hv
      let h : ∃ ab : 𝓞 F × 𝓞 F, ab.2 ∉ v.asIdeal ∧
          ((ε : Fˣ) : F) * algebraMap (𝓞 F) F ab.2 = algebraMap (𝓞 F) F ab.1 :=
        ⟨(n, d), d.2, hnd⟩
      letI : v.asIdeal.IsMaximal := v.isMaximal
      letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
      unfold ArtinPrimitiveRoots.A1.residue
      rw [dif_pos h]
      have hdval : v.valuation F (algebraMap (𝓞 F) F h.choose.2) = 1 := by
        rw [v.valuation_eq_one_iff_notMem]
        exact h.choose_spec.1
      have hnval : v.valuation F (algebraMap (𝓞 F) F h.choose.1) = 1 := by
        rw [← h.choose_spec.2, map_mul, huval, hdval, one_mul]
      have hnum : Ideal.Quotient.mk v.asIdeal h.choose.1 ≠ 0 := by
        intro hq
        exact ((v.valuation_eq_one_iff_notMem).mp hnval)
          (Ideal.Quotient.eq_zero_iff_mem.mp hq)
      have hden : Ideal.Quotient.mk v.asIdeal h.choose.2 ≠ 0 := by
        intro hq
        exact h.choose_spec.1 (Ideal.Quotient.eq_zero_iff_mem.mp hq)
      exact mul_ne_zero hnum (inv_ne_zero hden)
    have houtside (v : ArtinPrimitiveRoots.A1.FinPlace F) (hv : v ∉ S.Sf) :
        H.hilb v (ArtinPrimitiveRoots.A1.toLoc v (ε : Fˣ))
          (ArtinPrimitiveRoots.A1.toLoc v (γ : Fˣ)) = 1 := by
      have h6 : (6 : 𝓞 F) ∉ v.asIdeal := by
        intro h
        exact hv (S.over6 v h)
      have ht := H.tame v h6 (ε : Fˣ) (γ : Fˣ) (hres v hv)
      apply Subtype.ext
      simpa [hcount γ v hv] using ht
    let f : ArtinPrimitiveRoots.A1.FinPlace F → rootsOfUnity 6 F := fun v =>
      H.hilb v (ArtinPrimitiveRoots.A1.toLoc v (ε : Fˣ))
        (ArtinPrimitiveRoots.A1.toLoc v (γ : Fˣ))
    have hsupp : Function.mulSupport f ⊆ S.Sf := by
      intro v hv
      change f v ≠ 1 at hv
      by_contra hvS
      exact hv (by simpa [f] using houtside v hvS)
    have hcomp (v : S.Sf) (a : Fˣ) :
        S.compU v (S.diagU a) = ArtinPrimitiveRoots.A1.toLoc v.1 a := by
      ext
      rfl
    have hprodS : (∏ᶠ v : ArtinPrimitiveRoots.A1.FinPlace F, f v) =
        S.HS H (S.diagU ε) (S.diagU γ) := by
      calc
        (∏ᶠ v : ArtinPrimitiveRoots.A1.FinPlace F, f v) = ∏ v ∈ S.Sf, f v :=
          finprod_eq_prod_of_mulSupport_subset f hsupp
        _ = ∏ v ∈ S.Sf.attach, f v := (Finset.prod_attach S.Sf f).symm
        _ = S.HS H (S.diagU ε) (S.diagU γ) := by
          unfold ArtinPrimitiveRoots.A1.SData.HS
          simp [f, hcomp]
    have hglobal := H.product_formula (ε : Fˣ) (γ : Fˣ)
    have hHS : S.HS H (S.diagU ε) (S.diagU γ) = 1 := by
      rw [← hprodS]
      exact hglobal.2
    simp [lambdaEpsilon, hHS]
  · intro ε' hclass y
    have hmem : ε' / ε ∈ Gamma S := by
      exact (QuotientGroup.eq_iff_div_mem).mp (by simpa [unitSixClass] using hclass)
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hmem
    have hu' : u ^ 6 = ε' / ε := by
      simpa [sixthPowerOnUS] using hu
    have heps : ε' = ε * u ^ 6 := by
      calc
        ε' = ε * (ε' / ε) := (mul_div_cancel ε ε').symm
        _ = ε * u ^ 6 := by rw [← hu']
    have hmulHS (x z : S.FSˣ) :
        S.HS H (x * z) y = S.HS H x y * S.HS H z y := by
      unfold ArtinPrimitiveRoots.A1.SData.HS
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro v hv
      exact H.mul_left v.1 (S.compU v x) (S.compU v z) (S.compU v y)
    have hsixHS (x : S.FSˣ) : S.HS H (x ^ 6) y = 1 := by
      unfold ArtinPrimitiveRoots.A1.SData.HS
      apply Finset.prod_eq_one
      intro v hv
      exact H.sixth_power v.1 (S.compU v (x ^ 6)) (S.compU v y)
        ⟨S.compU v x, by simp [ArtinPrimitiveRoots.A1.SData.compU]⟩
    have hdiag : S.diagU ((ε * u ^ 6 : S.US) : Fˣ) =
        S.diagU (ε : Fˣ) * (S.diagU (u : Fˣ)) ^ 6 := by
      change S.diagU ((ε : Fˣ) * (u : Fˣ) ^ 6) =
        S.diagU (ε : Fˣ) * (S.diagU (u : Fˣ)) ^ 6
      rw [map_mul, map_pow]
    have hhs : S.HS H (S.diagU ε') y = S.HS H (S.diagU ε) y := by
      rw [heps, hdiag, hmulHS, hsixHS, mul_one]
    simp [lambdaEpsilon, hhs]

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

/-- **def:rf-active** (04-reflection.tex:478-499): the local Weyl coefficient envelope `β_p(e)`. -/
def betaPrime (q : ℝ) (e : ℕ) : ℝ :=
  if e = 0 then 1
  else if e % 3 = 1 then Real.rpow q (-((e / 3 : ℕ) : ℝ))
  else if e % 3 = 0 then Real.rpow q (1 / 2 - ((e / 3 : ℕ) : ℝ))
  else 0

/-- **def:rf-active** (04-reflection.tex:478-499): the local Euler sum for `β_p`. -/
def betaEulerFactor (q σ : ℝ) : ℂ :=
  ∑' e : ℕ,
    ((betaPrime q e * Real.rpow q (-(σ * (e : ℝ))):ℝ) : ℂ)

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

private theorem exists_powerful_decomposition (I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    (hpower : IsPowerful I) : ∃ A K : Ideal (𝓞 F), I = A ^ 2 * K ^ 3 := by
  classical
  let M := UniqueFactorizationMonoid.normalizedFactors I
  let e : Ideal (𝓞 F) →₀ ℕ := M.toFinsupp
  let expA : ℕ → ℕ := fun n => (n - 3 * (n % 2)) / 2
  let expK : ℕ → ℕ := fun n => n % 2
  let a : Ideal (𝓞 F) →₀ ℕ := e.mapRange expA (by simp [expA])
  let b : Ideal (𝓞 F) →₀ ℕ := e.mapRange expK (by simp [expK])
  let A : Ideal (𝓞 F) := a.prod (fun p n => p ^ n)
  let K : Ideal (𝓞 F) := b.prod (fun p n => p ^ n)
  have hexp (p : Ideal (𝓞 F)) (hp : p ∈ e.support) : 2 ≤ e p := by
    have hpM : p ∈ M := by simpa [e] using hp
    have hpPrime : Prime p := UniqueFactorizationMonoid.prime_of_normalized_factor p hpM
    have hpIdealPrime : p.IsPrime := Ideal.isPrime_of_prime hpPrime
    have hpne : p ≠ ⊥ := hpPrime.ne_zero
    let v : ArtinPrimitiveRoots.A1.FinPlace F := ⟨p, hpIdealPrime, hpne⟩
    have hpdiv : p ∣ I := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hpM
    have hp2 : p ^ 2 ∣ I := hpower v hpdiv
    have hcount := Multiset.count_le_of_le p
      ((UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors
        (pow_ne_zero 2 hpne) hI).mp hp2)
    have hcount2 : (UniqueFactorizationMonoid.normalizedFactors (p ^ 2)).count p = 2 := by
      simp [UniqueFactorizationMonoid.normalizedFactors_pow,
        UniqueFactorizationMonoid.normalizedFactors_irreducible hpPrime.irreducible]
    have hcountge : 2 ≤ Multiset.count p M := by
      calc
        2 = (UniqueFactorizationMonoid.normalizedFactors (p ^ 2)).count p := hcount2.symm
        _ ≤ M.count p := by simpa [M] using hcount
    simpa [e] using hcountge
  have harith (n : ℕ) (hn : n = 0 ∨ 2 ≤ n) :
      n = 2 * expA n + 3 * expK n := by
    rcases hn with rfl | hn
    · simp [expA, expK]
    · dsimp [expA, expK]
      omega
  have hexp : e = 2 • a + 3 • b := by
    ext p
    by_cases hp : p ∈ e.support
    · have hn := harith (e p) (Or.inr (hexp p hp))
      simpa [a, b, e, expA, expK, Finsupp.mapRange_apply] using hn
    · have hp0 : e p = 0 := (Finsupp.notMem_support_iff.mp hp)
      simp [a, b, e, expA, expK, hp, hp0]
  let g : Ideal (𝓞 F) → ℕ → Ideal (𝓞 F) := fun p n => p ^ n
  have hprodAdd (x y : Ideal (𝓞 F) →₀ ℕ) : (x + y).prod g = x.prod g * y.prod g := by
    apply Finsupp.prod_add_index'
    · intro p
      simp [g]
    · intro p n m
      simp [g, pow_add]
  have hprodN (n : ℕ) (x : Ideal (𝓞 F) →₀ ℕ) :
      (n • x).prod g = (x.prod g) ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [succ_nsmul, hprodAdd, ih, pow_succ]
  have hMprod : M.prod = e.prod g := by
    change M.prod = (Multiset.toFinsupp M).prod g
    rw [Finset.prod_multiset_count]
    simp [Finsupp.prod, g]
  have hIprod : I = M.prod := by
    exact (associated_iff_eq.mp (UniqueFactorizationMonoid.prod_normalizedFactors hI)).symm
  refine ⟨A, K, ?_⟩
  rw [hIprod, hMprod, hexp, hprodAdd, hprodN, hprodN]

private def zeroRayModulus : ClassFieldTheory.RayClassModulus F := ⟨0, ∅⟩

private abbrev trivialRayChar :
    ClassFieldTheory.RayClassGroup (zeroRayModulus (F := F)) →* ℂˣ := 1

private theorem charValue_trivialRay (I : Ideal (𝓞 F)) :
    ArtinPrimitiveRoots.Hecke.charValue (trivialRayChar (F := F)) I =
      if I = ⊥ then 0 else 1 := by
  classical
  by_cases hI : I = ⊥
  · subst I
    simp [ArtinPrimitiveRoots.Hecke.charValue,
      ArtinPrimitiveRoots.Hecke.IsCoprimeTo]
  · have hcop : ArtinPrimitiveRoots.Hecke.IsCoprimeTo
        (zeroRayModulus (F := F)) I := by
      change ∃ h' : I ≠ ⊥,
        ArtinPrimitiveRoots.Hecke.idealUnit I h' ∈
          ClassFieldTheory.rayClassPrimeToIdeals (zeroRayModulus (F := F))
      refine ⟨hI, ?_⟩
      change ∀ v, v ∈ (0 : ArtinPrimitiveRoots.A1.FinPlace F →₀ ℕ).support → _
      intro v hv
      simp at hv
    simp [ArtinPrimitiveRoots.Hecke.charValue, hI, hcop]

private theorem coeff_trivialRay_eq_idealCount {n : ℕ} (hn : n ≠ 0) :
    ArtinPrimitiveRoots.Hecke.coeff (trivialRayChar (F := F)) n =
      (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℂ) := by
  classical
  unfold ArtinPrimitiveRoots.Hecke.coeff
  let E := Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 F) n
  calc
    ∑ I ∈ E.toFinset,
        ArtinPrimitiveRoots.Hecke.charValue (trivialRayChar (F := F)) I =
      ∑ I ∈ E.toFinset, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro I hI
        rw [charValue_trivialRay]
        have hIn : Ideal.absNorm I = n := E.mem_toFinset.mp hI
        have hI0 : I ≠ ⊥ := by
          intro h
          subst I
          simp at hIn
          exact hn hIn.symm
        simp [hI0]
    _ = (E.toFinset.card : ℂ) := by simp
    _ = (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℂ) := by
      exact_mod_cast (Nat.card_eq_card_finite_toFinset E).symm

private theorem trivialRayTerm_summable :
    Summable (fun n : ℕ => ‖LSeries.term
      (ArtinPrimitiveRoots.Hecke.coeff (trivialRayChar (F := F)))
      ((3 / 2 : ℝ) : ℂ) n‖) := by
  have hs : 1 < (((3 / 2 : ℝ) : ℂ).re) := by norm_num
  exact (ArtinPrimitiveRoots.Hecke.LSeriesSummable_coeff
    (trivialRayChar (F := F)) hs).norm

private def idealNormWeight (n : ℕ) : ℝ :=
  if n = 0 then 0 else Real.rpow (n : ℝ) (-(3 / 2 : ℝ))

private theorem ideal_norm_weight_sum_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      (∑ I ∈ (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) N).toFinset,
        idealNormWeight (Ideal.absNorm I)) ≤ C := by
  classical
  let η := trivialRayChar (F := F)
  let term : ℕ → ℝ := fun n =>
    ‖LSeries.term (ArtinPrimitiveRoots.Hecke.coeff η) ((3 / 2 : ℝ) : ℂ) n‖
  have hterm : Summable term := by
    simpa [term, η] using trivialRayTerm_summable (F := F)
  let Z : ℝ := ∑' n, term n
  have hZ : 0 ≤ Z := tsum_nonneg (fun n => norm_nonneg _)
  refine ⟨Z + 1, by positivity, ?_⟩
  intro N
  let EN := Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) N
  let FN := EN.toFinset
  let ns := Finset.range (N + 1)
  let Eq (n : ℕ) := Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 F) n
  have hunion : FN = ns.biUnion (fun n => (Eq n).toFinset) := by
    ext I
    constructor
    · intro hI
      have hbound : Ideal.absNorm I ≤ N := EN.mem_toFinset.mp hI
      refine Finset.mem_biUnion.mpr ⟨Ideal.absNorm I, ?_, ?_⟩
      · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hbound)
      · exact (Eq (Ideal.absNorm I)).mem_toFinset.mpr rfl
    · intro h
      change I ∈ ns.biUnion (fun n => (Eq n).toFinset) at h
      rw [Finset.mem_biUnion] at h
      rcases h with ⟨n, hn, hI⟩
      have hnorm := (Eq n).mem_toFinset.mp hI
      change Ideal.absNorm I = n at hnorm
      have hbound : Ideal.absNorm I ≤ N := by
        rw [hnorm]
        exact Nat.le_of_lt_succ (Finset.mem_range.mp hn)
      exact EN.mem_toFinset.mpr hbound
  have hdisj : (ns : Set ℕ).PairwiseDisjoint (fun n => (Eq n).toFinset) := by
    intro n hn m hm hnm
    change Disjoint (↑((Eq n).toFinset)) (↑((Eq m).toFinset))
    rw [Finset.disjoint_left]
    intro I hIn hIm
    have h1 := (Eq n).mem_toFinset.mp hIn
    have h2 := (Eq m).mem_toFinset.mp hIm
    exact hnm (h1.symm.trans h2)
  have hsplit :
      (∑ I ∈ FN, idealNormWeight (Ideal.absNorm I)) =
        ∑ n ∈ ns, ∑ I ∈ (Eq n).toFinset, idealNormWeight (Ideal.absNorm I) := by
    rw [hunion, Finset.sum_biUnion hdisj]
  have hblock (n : ℕ) :
      (∑ I ∈ (Eq n).toFinset, idealNormWeight (Ideal.absNorm I)) =
        ((Eq n).toFinset.card : ℝ) * idealNormWeight n := by
    calc
      (∑ I ∈ (Eq n).toFinset, idealNormWeight (Ideal.absNorm I)) =
          ∑ I ∈ (Eq n).toFinset, idealNormWeight n := by
        apply Finset.sum_congr rfl
        intro I hI
        rw [(Eq n).mem_toFinset.mp hI]
      _ = ((Eq n).toFinset.card : ℝ) * idealNormWeight n := by simp
  have hcountCoeff (n : ℕ) (hn : n ≠ 0) :
      ((Eq n).toFinset.card : ℝ) * idealNormWeight n = term n := by
    have hcoeff := coeff_trivialRay_eq_idealCount (F := F) hn
    have hcard :
        ((Eq n).toFinset.card : ℝ) =
          (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℝ) := by
      exact_mod_cast (Nat.card_eq_card_finite_toFinset (Eq n)).symm
    rw [idealNormWeight, if_neg hn]
    dsimp [term]
    rw [LSeries.norm_term_eq, if_neg hn, hcoeff]
    simp only [Complex.norm_natCast, hcard]
    rw [show (((3 / 2 : ℝ) : ℂ).re) = 3 / 2 by simp,
      Real.rpow_neg (Nat.cast_nonneg n) (3 / 2)]
    ring_nf
  have hterm0 : idealNormWeight 0 = term 0 := by
    simp [idealNormWeight, term]
  have hblockEq (n : ℕ) :
      (∑ I ∈ (Eq n).toFinset, idealNormWeight (Ideal.absNorm I)) = term n := by
    by_cases hn : n = 0
    · subst n
      rw [hblock, hterm0]
      simp [term, LSeries.term]
    · rw [hblock, hcountCoeff n hn]
  have hsum :
      (∑ I ∈ FN, idealNormWeight (Ideal.absNorm I)) = ∑ n ∈ ns, term n := by
    rw [hsplit]
    apply Finset.sum_congr rfl
    intro n hn
    exact hblockEq n
  calc
    (∑ I ∈ FN, idealNormWeight (Ideal.absNorm I)) = ∑ n ∈ ns, term n := hsum
    _ ≤ ∑' n, term n := hterm.sum_le_tsum ns (fun n hn => norm_nonneg _)
    _ ≤ Z + 1 := by dsimp [Z]; linarith

/-- **rf:powerful-count** (04-reflection.tex:1035-1044). -/
theorem rf_powerful_count
    (S : ArtinPrimitiveRoots.A1.SData F CE condη) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P →
      (powerfulExteriorIdeals S P).card ≤ C * Real.rpow P (1 / 2 : ℝ) := by
  classical
  obtain ⟨C₀, hC₀, hIdealCount⟩ := ext_ideal_count (F := F)
  obtain ⟨Z, hZ, hWeightSum⟩ := ideal_norm_weight_sum_bound (F := F)
  refine ⟨2 * C₀ * (1 + C₀ + Z), by positivity, ?_⟩
  intro P hP
  let X : ℝ := 2 * P
  let R : ℝ := Real.sqrt X
  have hX : 1 ≤ X := by dsimp [X]; linarith
  have hR : 1 ≤ R := by
    dsimp [R]
    rw [← Real.sqrt_one]
    exact (Real.sqrt_le_sqrt_iff (by positivity : (0 : ℝ) ≤ X)).2 hX
  let E_R := Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊R⌋₊
  let All := E_R.toFinset
  let T := powerfulExteriorIdeals S P
  let Pairs := (All ×ˢ All).filter fun q : Ideal (𝓞 F) × Ideal (𝓞 F) =>
    (Ideal.absNorm q.1 : ℝ) ^ 2 * (Ideal.absNorm q.2 : ℝ) ^ 3 ≤ X
  have hAllCard : (All.card : ℝ) ≤ C₀ * R := by
    simpa [All, E_R] using hIdealCount R hR
  have hWeightAll :
      (∑ K ∈ All, idealNormWeight (Ideal.absNorm K)) ≤ Z := by
    simpa [All, E_R] using hWeightSum ⌊R⌋₊
  have hweightNonneg (K : Ideal (𝓞 F)) :
      0 ≤ idealNormWeight (Ideal.absNorm K) := by
    by_cases hK : Ideal.absNorm K = 0
    · simp [idealNormWeight, hK]
    · simp [idealNormWeight, hK]
      positivity
  have hRadiusSum :
      (∑ K ∈ All,
        (if K = ⊥ then R else 1 + R * idealNormWeight (Ideal.absNorm K))) ≤
          R + (All.card : ℝ) + R * Z := by
    have hbot : (⊥ : Ideal (𝓞 F)) ∈ All := by
      apply E_R.mem_toFinset.mpr
      change Ideal.absNorm (⊥ : Ideal (𝓞 F)) ≤ ⌊R⌋₊
      simp
    have hrest :
        (∑ K ∈ All.erase (⊥ : Ideal (𝓞 F)),
          (if K = ⊥ then R else 1 + R * idealNormWeight (Ideal.absNorm K))) =
          ((All.erase (⊥ : Ideal (𝓞 F))).card : ℝ) +
            R * ∑ K ∈ All.erase (⊥ : Ideal (𝓞 F)), idealNormWeight (Ideal.absNorm K) := by
      calc
        (∑ K ∈ All.erase (⊥ : Ideal (𝓞 F)),
            (if K = ⊥ then R else 1 + R * idealNormWeight (Ideal.absNorm K))) =
          ∑ K ∈ All.erase (⊥ : Ideal (𝓞 F)),
            (1 + R * idealNormWeight (Ideal.absNorm K)) := by
              apply Finset.sum_congr rfl
              intro K hK
              rw [if_neg (Finset.mem_erase.mp hK).1]
        _ = ((All.erase (⊥ : Ideal (𝓞 F))).card : ℝ) +
              ∑ K ∈ All.erase (⊥ : Ideal (𝓞 F)), R * idealNormWeight (Ideal.absNorm K) := by
          rw [Finset.sum_add_distrib]
          simp
        _ = ((All.erase (⊥ : Ideal (𝓞 F))).card : ℝ) +
              R * ∑ K ∈ All.erase (⊥ : Ideal (𝓞 F)), idealNormWeight (Ideal.absNorm K) := by
          rw [Finset.mul_sum]
    calc
      (∑ K ∈ All,
          (if K = ⊥ then R else 1 + R * idealNormWeight (Ideal.absNorm K))) =
        R + ∑ K ∈ All.erase (⊥ : Ideal (𝓞 F)),
          (if K = ⊥ then R else 1 + R * idealNormWeight (Ideal.absNorm K)) := by
            rw [← Finset.add_sum_erase All
              (fun K => if K = ⊥ then R else 1 + R * idealNormWeight (Ideal.absNorm K)) hbot]
            simp [hbot]
      _ = R + ((All.erase (⊥ : Ideal (𝓞 F))).card : ℝ) +
          R * ∑ K ∈ All.erase (⊥ : Ideal (𝓞 F)), idealNormWeight (Ideal.absNorm K) := by
            rw [hrest]
            ring
      _ ≤ R + (All.card : ℝ) + R * Z := by
        have hcardErase := Finset.card_le_card (Finset.erase_subset (⊥ : Ideal (𝓞 F)) All)
        have hcardEraseR :
            ((All.erase (⊥ : Ideal (𝓞 F))).card : ℝ) ≤ (All.card : ℝ) := by
          exact_mod_cast hcardErase
        have hsumErase :
            (∑ K ∈ All.erase (⊥ : Ideal (𝓞 F)), idealNormWeight (Ideal.absNorm K)) ≤ Z := by
          calc
            _ ≤ ∑ K ∈ All, idealNormWeight (Ideal.absNorm K) :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset (⊥ : Ideal (𝓞 F)) All)
                (fun K _ _ => hweightNonneg K)
            _ ≤ Z := hWeightAll
        have hRnonneg : 0 ≤ R := Real.sqrt_nonneg _
        have hscaled : R *
            (∑ K ∈ All.erase (⊥ : Ideal (𝓞 F)), idealNormWeight (Ideal.absNorm K)) ≤ R * Z :=
          mul_le_mul_of_nonneg_left hsumErase hRnonneg
        linarith [hcardEraseR, hscaled]
  have hdecompData (i : T.attach) : i.1.1 ≠ ⊥ ∧ IsPowerful i.1.1 := by
    rcases Finset.mem_filter.mp i.1.2 with ⟨_, h⟩
    exact ⟨h.1.1, h.2⟩
  have hexist (i : T.attach) : ∃ A K : Ideal (𝓞 F), i.1.1 = A ^ 2 * K ^ 3 :=
    exists_powerful_decomposition i.1.1 (hdecompData i).1 (hdecompData i).2
  let decomp (i : T.attach) : Ideal (𝓞 F) × Ideal (𝓞 F) :=
    ⟨Classical.choose (hexist i),
      Classical.choose (Classical.choose_spec (hexist i))⟩
  have hdecomp (i : T.attach) : i.1.1 = (decomp i).1 ^ 2 * (decomp i).2 ^ 3 := by
    exact Classical.choose_spec (Classical.choose_spec (hexist i))
  have hdecInj : Function.Injective decomp := by
    intro i j hij
    apply Subtype.ext
    apply Subtype.ext
    calc
      i.1.1 = (decomp i).1 ^ 2 * (decomp i).2 ^ 3 := hdecomp i
      _ = (decomp j).1 ^ 2 * (decomp j).2 ^ 3 := by rw [hij]
      _ = j.1.1 := (hdecomp j).symm
  have hdecompInPairs (i : T.attach) : decomp i ∈ Pairs := by
    have hmem := i.1.2
    change i.1.1 ∈ powerfulExteriorIdeals S P at hmem
    rcases Finset.mem_filter.mp hmem with ⟨hbase, hprop⟩
    have hI0 : i.1.1 ≠ ⊥ := hprop.1.1
    have hA0 : (decomp i).1 ≠ ⊥ := by
      intro hA
      apply hI0
      simpa [hA] using hdecomp i
    have hK0 : (decomp i).2 ≠ ⊥ := by
      intro hK
      apply hI0
      simpa [hK] using hdecomp i
    have hNA0 : Ideal.absNorm (decomp i).1 ≠ 0 := by
      intro hN
      exact hA0 (Ideal.absNorm_eq_zero_iff.mp hN)
    have hNK0 : Ideal.absNorm (decomp i).2 ≠ 0 := by
      intro hN
      exact hK0 (Ideal.absNorm_eq_zero_iff.mp hN)
    have hNA1 : (1 : ℝ) ≤ (Ideal.absNorm (decomp i).1 : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hNA0)
    have hNK1 : (1 : ℝ) ≤ (Ideal.absNorm (decomp i).2 : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hNK0)
    have hNnat : Ideal.absNorm i.1.1 ≤ ⌊2 * P⌋₊ := by
      exact (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊2 * P⌋₊).mem_toFinset.mp hbase
    have hNle : (Ideal.absNorm i.1.1 : ℝ) ≤ X := by
      calc
        _ ≤ (⌊2 * P⌋₊ : ℝ) := by exact_mod_cast hNnat
        _ ≤ 2 * P := Nat.floor_le (by positivity)
        _ = X := by rfl
    have hNprod : (Ideal.absNorm i.1.1 : ℝ) =
        (Ideal.absNorm (decomp i).1 : ℝ) ^ 2 *
          (Ideal.absNorm (decomp i).2 : ℝ) ^ 3 := by
      have h := congrArg Ideal.absNorm (hdecomp i)
      simpa only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow] using congrArg (fun n : ℕ => (n : ℝ)) h
    have hNA2 : (Ideal.absNorm (decomp i).1 : ℝ) ^ 2 ≤ X := by
      let qK : ℝ := (Ideal.absNorm (decomp i).2 : ℝ)
      have hNK1' : (1 : ℝ) ≤ qK := by simpa [qK] using hNK1
      have hK3 : (1 : ℝ) ≤ qK ^ 3 := by
        have hfac : qK ^ 3 - 1 = (qK - 1) * (qK ^ 2 + qK + 1) := by ring
        have hnonneg : 0 ≤ (qK - 1) * (qK ^ 2 + qK + 1) :=
          mul_nonneg (sub_nonneg.mpr hNK1') (by positivity)
        have hdiff : 0 ≤ qK ^ 3 - 1 := by rw [hfac]; exact hnonneg
        linarith
      let qA : ℝ := (Ideal.absNorm (decomp i).1 : ℝ)
      change qA ^ 2 ≤ X
      calc
        _ ≤ qA ^ 2 * qK ^ 3 := by
          calc
            qA ^ 2 = qA ^ 2 * 1 := by ring
            _ ≤ qA ^ 2 * qK ^ 3 := mul_le_mul_of_nonneg_left hK3 (sq_nonneg qA)
        _ = (Ideal.absNorm i.1.1 : ℝ) := by simpa [qA, qK] using hNprod.symm
        _ ≤ X := hNle
    have hNK2 : (Ideal.absNorm (decomp i).2 : ℝ) ^ 2 ≤ X := by
      let qA : ℝ := (Ideal.absNorm (decomp i).1 : ℝ)
      let qK : ℝ := (Ideal.absNorm (decomp i).2 : ℝ)
      have hNA1' : (1 : ℝ) ≤ qA := by simpa [qA] using hNA1
      have hNK1' : (1 : ℝ) ≤ qK := by simpa [qK] using hNK1
      have hA2 : (1 : ℝ) ≤ qA ^ 2 := by
        have hfac : qA ^ 2 - 1 = (qA - 1) * (qA + 1) := by ring
        have hnonneg : 0 ≤ (qA - 1) * (qA + 1) :=
          mul_nonneg (sub_nonneg.mpr hNA1') (by positivity)
        have hdiff : 0 ≤ qA ^ 2 - 1 := by rw [hfac]; exact hnonneg
        linarith
      have hK3 : qK ^ 2 ≤ qK ^ 3 := by
        calc
          qK ^ 2 = qK ^ 2 * 1 := by ring
          _ ≤ qK ^ 2 * qK := mul_le_mul_of_nonneg_left hNK1' (sq_nonneg qK)
          _ = qK ^ 3 := by ring
      change qK ^ 2 ≤ X
      calc
        _ ≤ qA ^ 2 * qK ^ 3 := by
          calc
            qK ^ 2 ≤ qK ^ 3 := hK3
            _ = 1 * qK ^ 3 := by ring
            _ ≤ qA ^ 2 * qK ^ 3 := mul_le_mul_of_nonneg_right hA2 (by positivity)
        _ = (Ideal.absNorm i.1.1 : ℝ) := by simpa [qA, qK] using hNprod.symm
        _ ≤ X := hNle
    have hAR : (Ideal.absNorm (decomp i).1 : ℝ) ≤ R :=
      by
        calc
          _ = Real.sqrt ((Ideal.absNorm (decomp i).1 : ℝ) ^ 2) :=
            (Real.sqrt_sq (by positivity)).symm
          _ ≤ Real.sqrt X := Real.sqrt_le_sqrt hNA2
    have hKR : (Ideal.absNorm (decomp i).2 : ℝ) ≤ R :=
      by
        calc
          _ = Real.sqrt ((Ideal.absNorm (decomp i).2 : ℝ) ^ 2) :=
            (Real.sqrt_sq (by positivity)).symm
          _ ≤ Real.sqrt X := Real.sqrt_le_sqrt hNK2
    have hAin : (decomp i).1 ∈ All := by
      apply E_R.mem_toFinset.mpr
      exact (Nat.le_floor_iff' hNA0).2 (by exact_mod_cast hAR)
    have hKin : (decomp i).2 ∈ All := by
      apply E_R.mem_toFinset.mpr
      exact (Nat.le_floor_iff' hNK0).2 (by exact_mod_cast hKR)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨hAin, hKin⟩, ?_⟩
    rw [← hNprod]
    exact hNle
  let f : T.attach → {q : Ideal (𝓞 F) × Ideal (𝓞 F) // q ∈ Pairs} :=
    fun i => ⟨decomp i, hdecompInPairs i⟩
  have hfinj : Function.Injective f := by
    intro i j hij
    apply hdecInj
    exact congrArg Subtype.val hij
  have hTcard : T.card ≤ Pairs.card := by
    calc
      T.card = Fintype.card T.attach := by simp
      _ ≤ Fintype.card {q : Ideal (𝓞 F) × Ideal (𝓞 F) // q ∈ Pairs} :=
        Fintype.card_le_of_injective f hfinj
      _ = Pairs.card := by simp
  have hsumPairs : (Pairs.card : ℝ) =
      ∑ K ∈ All, ((Pairs.filter fun q => q.2 = K).card : ℝ) := by
    have hmaps : Set.MapsTo Prod.snd (Pairs : Set (Ideal (𝓞 F) × Ideal (𝓞 F)))
        (All : Set (Ideal (𝓞 F))) := by
      intro q hq
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).2
    have hcard := Finset.card_eq_sum_card_fiberwise (f := Prod.snd) hmaps
    exact_mod_cast hcard
  have hfiber (K : Ideal (𝓞 F)) (hK : K ∈ All) :
      ((Pairs.filter fun q => q.2 = K).card : ℝ) ≤
        C₀ * (if K = ⊥ then R else 1 + R * idealNormWeight (Ideal.absNorm K)) := by
    let radius : ℝ := if K = ⊥ then R else 1 + R * idealNormWeight (Ideal.absNorm K)
    let E_K := Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊radius⌋₊
    let A_K := E_K.toFinset
    have hRadius : 1 ≤ radius := by
      dsimp [radius]
      split_ifs
      · exact hR
      · have hRnonneg : 0 ≤ R := Real.sqrt_nonneg _
        have hweight := hweightNonneg K
        have hmul : 0 ≤ R * idealNormWeight (Ideal.absNorm K) := mul_nonneg hRnonneg hweight
        linarith
    have hmap : Set.MapsTo Prod.fst
        ((Pairs.filter fun q => q.2 = K) : Set (Ideal (𝓞 F) × Ideal (𝓞 F)))
        (A_K : Set (Ideal (𝓞 F))) := by
      intro q hq
      have hq : q ∈ Pairs.filter (fun q => q.2 = K) := hq
      rcases Finset.mem_filter.mp hq with ⟨hqPairs, hqK⟩
      rcases Finset.mem_filter.mp hqPairs with ⟨hqProd, hqBound⟩
      rcases Finset.mem_product.mp hqProd with ⟨hqA, _⟩
      have hqAreal : (Ideal.absNorm q.1 : ℝ) ≤ radius := by
        by_cases hKbot : K = ⊥
        · have hnormNat := E_R.mem_toFinset.mp hqA
          have hRbound : (Ideal.absNorm q.1 : ℝ) ≤ R := by
            calc
              _ ≤ (⌊R⌋₊ : ℝ) := by exact_mod_cast hnormNat
              _ ≤ R := Nat.floor_le (Real.sqrt_nonneg X)
          simpa [radius, hKbot] using hRbound
        · have hK0 : Ideal.absNorm K ≠ 0 := by
            intro h0
            exact hKbot (Ideal.absNorm_eq_zero_iff.mp h0)
          have hqKpos : (0 : ℝ) < (Ideal.absNorm K : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hK0
          have hqK3pos : (0 : ℝ) < (Ideal.absNorm K : ℝ) ^ 3 := by positivity
          have hqcond : (Ideal.absNorm q.1 : ℝ) ^ 2 *
              (Ideal.absNorm K : ℝ) ^ 3 ≤ X := by simpa [hqK] using hqBound
          have hqA2 : (Ideal.absNorm q.1 : ℝ) ^ 2 ≤
              X / (Ideal.absNorm K : ℝ) ^ 3 :=
            (le_div_iff₀ hqK3pos).2 (by simpa [mul_comm] using hqcond)
          have hroot : (Ideal.absNorm q.1 : ℝ) ≤
              Real.sqrt (X / (Ideal.absNorm K : ℝ) ^ 3) := by
            calc
              _ = Real.sqrt ((Ideal.absNorm q.1 : ℝ) ^ 2) :=
                (Real.sqrt_sq (by positivity)).symm
              _ ≤ Real.sqrt (X / (Ideal.absNorm K : ℝ) ^ 3) :=
                Real.sqrt_le_sqrt hqA2
          have hrootDen : Real.sqrt ((Ideal.absNorm K : ℝ) ^ 3) =
              (Ideal.absNorm K : ℝ) ^ (3 / 2 : ℝ) := by
            have hpow : (Ideal.absNorm K : ℝ) ^ (3 / 2 : ℝ) =
                Real.sqrt (Ideal.absNorm K : ℝ) ^ 3 := by
              simpa [show (3 : ℝ) / 2 = (3 / 2 : ℝ) by norm_num] using
                (Real.rpow_div_two_eq_sqrt (x := (Ideal.absNorm K : ℝ)) 3
                  (le_of_lt hqKpos))
            have hden : Real.sqrt ((Ideal.absNorm K : ℝ) ^ 3) =
                (Ideal.absNorm K : ℝ) * Real.sqrt (Ideal.absNorm K : ℝ) := by
              rw [show (Ideal.absNorm K : ℝ) ^ 3 =
                (Ideal.absNorm K : ℝ) ^ 2 * (Ideal.absNorm K : ℝ) by ring,
                Real.sqrt_mul (sq_nonneg (Ideal.absNorm K : ℝ)),
                Real.sqrt_sq (le_of_lt hqKpos)]
            calc
              Real.sqrt ((Ideal.absNorm K : ℝ) ^ 3) =
                  (Ideal.absNorm K : ℝ) * Real.sqrt (Ideal.absNorm K : ℝ) := hden
              _ = Real.sqrt (Ideal.absNorm K : ℝ) ^ 3 := by
                rw [pow_succ, Real.sq_sqrt (le_of_lt hqKpos)]
              _ = (Ideal.absNorm K : ℝ) ^ (3 / 2 : ℝ) := hpow.symm
          have hrootEq : Real.sqrt (X / (Ideal.absNorm K : ℝ) ^ 3) =
              R * idealNormWeight (Ideal.absNorm K) := by
            have hneg : Real.rpow (Ideal.absNorm K : ℝ) (-(3 / 2 : ℝ)) =
                (Real.rpow (Ideal.absNorm K : ℝ) (3 / 2 : ℝ))⁻¹ :=
              Real.rpow_neg (le_of_lt hqKpos) (3 / 2)
            calc
              Real.sqrt (X / (Ideal.absNorm K : ℝ) ^ 3) =
                  Real.sqrt X / Real.sqrt ((Ideal.absNorm K : ℝ) ^ 3) := by
                    rw [Real.sqrt_div (by positivity)]
              _ = R * (Real.rpow (Ideal.absNorm K : ℝ) (3 / 2 : ℝ))⁻¹ := by
                    rw [hrootDen]
                    simp [R, div_eq_mul_inv]
              _ = R * Real.rpow (Ideal.absNorm K : ℝ) (-(3 / 2 : ℝ)) := by
                    rw [hneg]
              _ = R * idealNormWeight (Ideal.absNorm K) := by
                    simp [idealNormWeight, hK0]
          rw [hrootEq] at hroot
          have hweight : 0 ≤ idealNormWeight (Ideal.absNorm K) := hweightNonneg K
          have hle : (Ideal.absNorm q.1 : ℝ) ≤
              1 + R * idealNormWeight (Ideal.absNorm K) := by linarith
          simpa [radius, hKbot] using hle
      have hqAnat : Ideal.absNorm q.1 ≤ ⌊radius⌋₊ := by
        by_cases hqA0 : Ideal.absNorm q.1 = 0
        · simp [hqA0]
        · exact (Nat.le_floor_iff' hqA0).2 (by exact_mod_cast hqAreal)
      exact E_K.mem_toFinset.mpr hqAnat
    let FK := Pairs.filter (fun q => q.2 = K)
    have hinj : Set.InjOn Prod.fst (FK : Set (Ideal (𝓞 F) × Ideal (𝓞 F))) := by
      intro q hq q' hq' hfirst
      have hqK := (Finset.mem_filter.mp (show q ∈ FK from hq)).2
      have hq'K := (Finset.mem_filter.mp (show q' ∈ FK from hq')).2
      exact Prod.ext hfirst (hqK.trans hq'K.symm)
    have hcardNat := Finset.card_le_card_of_injOn Prod.fst (by
      simpa [FK] using hmap) hinj
    have hcardReal :
        ((Pairs.filter fun q => q.2 = K).card : ℝ) ≤ (A_K.card : ℝ) := by exact_mod_cast hcardNat
    have hcardBound : (A_K.card : ℝ) ≤ C₀ * radius := by
      simpa [A_K, E_K] using hIdealCount radius hRadius
    simpa [radius] using hcardReal.trans hcardBound
  have hPairsBound : (Pairs.card : ℝ) ≤ C₀ * (R + (All.card : ℝ) + R * Z) := by
    rw [hsumPairs]
    calc
      (∑ K ∈ All, ((Pairs.filter fun q => q.2 = K).card : ℝ)) ≤
          ∑ K ∈ All, C₀ * (if K = ⊥ then R else 1 + R * idealNormWeight (Ideal.absNorm K)) :=
        Finset.sum_le_sum fun K hK => hfiber K hK
      _ = C₀ * ∑ K ∈ All,
          (if K = ⊥ then R else 1 + R * idealNormWeight (Ideal.absNorm K)) := by
        rw [Finset.mul_sum]
      _ ≤ C₀ * (R + (All.card : ℝ) + R * Z) := by
        have h := hRadiusSum
        nlinarith [hC₀, hZ]
  have hrootBound : R ≤ 2 * Real.rpow P (1 / 2 : ℝ) := by
    have hroot2 : Real.sqrt 2 ≤ (2 : ℝ) := by
      rw [Real.sqrt_le_iff]
      norm_num
    have hRprod : R = Real.sqrt 2 * Real.sqrt P := by
      dsimp [R, X]
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) P]
    calc
      R = Real.sqrt 2 * Real.sqrt P := hRprod
      _ ≤ 2 * Real.sqrt P := mul_le_mul_of_nonneg_right hroot2 (Real.sqrt_nonneg P)
      _ = 2 * Real.rpow P (1 / 2 : ℝ) := by
        exact congrArg (fun x : ℝ => 2 * x) (Real.sqrt_eq_rpow P)
  calc
    (T.card : ℝ) ≤ (Pairs.card : ℝ) := by exact_mod_cast hTcard
    _ ≤ C₀ * (R + (All.card : ℝ) + R * Z) := hPairsBound
    _ ≤ C₀ * ((1 + C₀ + Z) * R) := by
      have h := hAllCard
      nlinarith [hC₀, hZ, hR]
    _ ≤ C₀ * (1 + C₀ + Z) * (2 * Real.rpow P (1 / 2 : ℝ)) := by
      have hcoef : 0 ≤ C₀ * (1 + C₀ + Z) := by positivity
      calc
        C₀ * ((1 + C₀ + Z) * R) = (C₀ * (1 + C₀ + Z)) * R := by ring
        _ ≤ (C₀ * (1 + C₀ + Z)) * (2 * Real.rpow P (1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hrootBound hcoef
        _ = C₀ * (1 + C₀ + Z) * (2 * Real.rpow P (1 / 2 : ℝ)) := by ring
    _ = (2 * C₀ * (1 + C₀ + Z)) * Real.rpow P (1 / 2 : ℝ) := by ring

/-- **def:rf-column-cutoff** (04-reflection.tex:915-931): `𝓛=8D²P/Z`. -/
def reflectionColumnLength (P D Z : ℝ) : ℝ := 8 * D ^ 2 * P / Z

/-- **def:rf-column-cutoff** (04-reflection.tex:915-931): `R₀=Z^δ𝓛`. -/
def reflectionColumnCutoff (P D Z δ : ℝ) : ℝ :=
  Real.rpow Z δ * reflectionColumnLength P D Z

end ArtinPrimitiveRoots.A2
