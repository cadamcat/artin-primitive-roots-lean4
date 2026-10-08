import ArtinPrimitiveRoots.A2.Defs
import ArtinPrimitiveRoots.A2.QuadraticSieve
import ArtinPrimitiveRoots.A1.AddChar
import ArtinPrimitiveRoots.Hecke.Elementary
import ArtinPrimitiveRoots.A2.ZeroFree.Nodes
import ArtinPrimitiveRoots.A2.Proofs.A2_RF_ARITH.LocalHecke
import ArtinPrimitiveRoots.A2.Proofs.«A2-BRIDGES».SYMBOL
import ArtinPrimitiveRoots.A2.Proofs.«A2-BRIDGES».FINITE_CHAR

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

private theorem rf_chiPow_pow_nat
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (P : ArtinPrimitiveRoots.A1.FinPlace F) (x : F) (e : ℤ)
    (n : ℕ) (hn : 0 < n) :
    ArtinPrimitiveRoots.A1.chiPow D P x e ^ n =
      ArtinPrimitiveRoots.A1.chiPow D P x (e * (n : ℤ)) := by
  by_cases hx : ArtinPrimitiveRoots.A1.residue P x = 0
  · simp [ArtinPrimitiveRoots.A1.chiPow, hx, hn.ne']
  · simp only [ArtinPrimitiveRoots.A1.chiPow, if_neg hx]
    rw [← zpow_natCast, ← zpow_mul]

private theorem rf_chiIdealPow_finprod
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (x : F) (e : ℤ) :
    ArtinPrimitiveRoots.A1.chiIdealPow D I x e =
      ∏ᶠ P : ArtinPrimitiveRoots.A1.FinPlace F,
        if P.asIdeal ∣ I then
          ArtinPrimitiveRoots.A1.chiPow D P x
            (e * (ArtinPrimitiveRoots.A1.idealExp P I : ℤ))
        else 1 := by
  classical
  have hI0 : I ≠ 0 := by simpa only [Ideal.zero_eq_bot] using hI
  unfold ArtinPrimitiveRoots.A1.chiIdealPow
  rw [Multiset.prod_map_eq_finprod]
  rw [← finprod_emb_domain'
    (IsDedekindDomain.HeightOneSpectrum.asIdeal_injective (R := 𝓞 F))
    (fun P : ArtinPrimitiveRoots.A1.FinPlace F =>
      if P.asIdeal ∣ I then
        ArtinPrimitiveRoots.A1.chiPow D P x
          (e * (ArtinPrimitiveRoots.A1.idealExp P I : ℤ))
      else 1)]
  apply finprod_congr
  intro Q
  by_cases hQ : Q.IsPrime ∧ Q ≠ ⊥
  · let P : ArtinPrimitiveRoots.A1.FinPlace F := ⟨Q, hQ.1, hQ.2⟩
    have hmem : Q ∈ Set.range
        (fun v : ArtinPrimitiveRoots.A1.FinPlace F => v.asIdeal) := ⟨P, rfl⟩
    rw [dif_pos hQ, dif_pos hmem]
    have hchoose : Classical.choose hmem = P :=
      IsDedekindDomain.HeightOneSpectrum.asIdeal_injective (Classical.choose_spec hmem)
    rw [hchoose]
    by_cases hdiv : P.asIdeal ∣ I
    · rw [if_pos hdiv]
      have hcount :
          (UniqueFactorizationMonoid.normalizedFactors I).count Q =
            ArtinPrimitiveRoots.A1.idealExp P I := by
        unfold ArtinPrimitiveRoots.A1.idealExp
        exact (Ideal.count_associates_factors_eq hI0 hQ.1 hQ.2).symm
      rw [hcount]
      apply rf_chiPow_pow_nat
      have hmemNorm : Q ∈ UniqueFactorizationMonoid.normalizedFactors I :=
        (UniqueFactorizationMonoid.mem_normalizedFactors_iff hI0).2
          ⟨Ideal.prime_of_isPrime hQ.2 hQ.1, hdiv⟩
      rw [← hcount]
      exact Multiset.count_pos.mpr hmemNorm
    · rw [if_neg hdiv]
      have hcount : (UniqueFactorizationMonoid.normalizedFactors I).count Q = 0 := by
        apply Multiset.count_eq_zero.mpr
        intro hmemNorm
        exact hdiv (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hmemNorm)
      simp [hcount]
  · have hnot : Q ∉ Set.range
        (fun v : ArtinPrimitiveRoots.A1.FinPlace F => v.asIdeal) := by
      rintro ⟨P, rfl⟩
      exact hQ ⟨P.isPrime, P.ne_bot⟩
    simp only [dif_neg hQ, one_pow, dif_neg hnot]

private theorem rf_gen_count
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (I : Ideal (𝓞 F)) (a : Fˣ) (ha : S.IsGen (a : F) I)
    (P : ArtinPrimitiveRoots.A1.FinPlace F) (hP : P ∉ S.Sf) :
    FractionalIdeal.count F P
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F)) =
      (ArtinPrimitiveRoots.A1.idealExp P I : ℤ) := by
  have hI0 : I ≠ ⊥ := ha.1.1
  rw [ha.2.2 P hP, FractionalIdeal.count_coe F P hI0]
  rfl

private theorem rf_gen_valuation
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (I : Ideal (𝓞 F)) (a : Fˣ) (ha : S.IsGen (a : F) I)
    (P : ArtinPrimitiveRoots.A1.FinPlace F) (hP : P ∉ S.Sf) :
    P.valuation F (a : F) =
      WithZero.exp (-(ArtinPrimitiveRoots.A1.idealExp P I : ℤ)) := by
  have hcount := rf_gen_count S I a ha P hP
  have hlog := ArtinPrimitiveRoots.A2.qs_nq0_count_spanSingleton_eq_neg_log_valuation
    P (a : F) a.ne_zero
  rw [hcount] at hlog
  have hLog : WithZero.log (P.valuation F (a : F)) =
      -(ArtinPrimitiveRoots.A1.idealExp P I : ℤ) := by
    linarith
  have hval0 : P.valuation F (a : F) ≠ 0 :=
    (Valuation.ne_zero_iff (P.valuation F)).mpr a.ne_zero
  calc
    P.valuation F (a : F) = WithZero.exp (WithZero.log (P.valuation F (a : F))) :=
      (WithZero.exp_log hval0).symm
    _ = WithZero.exp (-(ArtinPrimitiveRoots.A1.idealExp P I : ℤ)) := by rw [hLog]

private theorem rf_idealExp_eq_zero_iff
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    (P : ArtinPrimitiveRoots.A1.FinPlace F) :
    ArtinPrimitiveRoots.A1.idealExp P I = 0 ↔ ¬P.asIdeal ∣ I := by
  unfold ArtinPrimitiveRoots.A1.idealExp
  constructor
  · intro h hdiv
    exact ((Associates.count_ne_zero_iff_dvd hI P.irreducible).mpr hdiv) h
  · intro h
    by_contra hne
    exact h ((Associates.count_ne_zero_iff_dvd hI P.irreducible).mp hne)

private theorem rf_residue_zero_of_gen
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (SB : ArtinPrimitiveRoots.A2.SymbolBridge D S)
    (I : Ideal (𝓞 F)) (x : Fˣ) (hx : S.IsGen (x : F) I)
    (P : ArtinPrimitiveRoots.A1.FinPlace F) (hP : P ∉ S.Sf)
    (hdiv : P.asIdeal ∣ I) :
    ArtinPrimitiveRoots.A1.residue P (x : F) = 0 := by
  have hI0 : I ≠ ⊥ := hx.1.1
  have hexpNe : ArtinPrimitiveRoots.A1.idealExp P I ≠ 0 := by
    intro hz
    exact ((rf_idealExp_eq_zero_iff I hI0 P).mp hz) hdiv
  have hExpPos : 0 < ArtinPrimitiveRoots.A1.idealExp P I := Nat.pos_of_ne_zero hexpNe
  have hval := rf_gen_valuation S I x hx P hP
  have hlt : P.valuation F (x : F) < 1 := by
    rw [hval]
    calc
      WithZero.exp (-(ArtinPrimitiveRoots.A1.idealExp P I : ℤ)) <
          WithZero.exp (0 : ℤ) :=
        WithZero.exp_lt_exp.mpr (by
          have hExpPosZ : (0 : ℤ) < (ArtinPrimitiveRoots.A1.idealExp P I : ℤ) := by
            exact_mod_cast hExpPos
          exact neg_lt_zero.mpr hExpPosZ)
      _ = 1 := WithZero.exp_zero
  by_contra hres
  have hvalone := (SB.residue_ne_zero P (x : F) hlt.le).mp hres
  exact (ne_of_lt hlt) hvalone

private theorem rf_residue_ne_zero_of_gen_not_dvd
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (SB : ArtinPrimitiveRoots.A2.SymbolBridge D S)
    (I : Ideal (𝓞 F)) (x : Fˣ) (hx : S.IsGen (x : F) I)
    (P : ArtinPrimitiveRoots.A1.FinPlace F) (hP : P ∉ S.Sf)
    (hnot : ¬P.asIdeal ∣ I) :
    ArtinPrimitiveRoots.A1.residue P (x : F) ≠ 0 := by
  have hexp : ArtinPrimitiveRoots.A1.idealExp P I = 0 :=
    (rf_idealExp_eq_zero_iff I hx.1.1 P).2 hnot
  have hval : P.valuation F (x : F) = 1 := by
    simpa [hexp] using rf_gen_valuation S I x hx P hP
  exact (SB.residue_ne_zero P (x : F) hval.le).2 hval

private theorem rf_chiIdealPow_zero_of_prime
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    (P : ArtinPrimitiveRoots.A1.FinPlace F) (hdiv : P.asIdeal ∣ I)
    (x : F) (hx : ArtinPrimitiveRoots.A1.residue P x = 0) (e : ℤ) :
    ArtinPrimitiveRoots.A1.chiIdealPow D I x e = 0 := by
  classical
  unfold ArtinPrimitiveRoots.A1.chiIdealPow
  apply Multiset.prod_eq_zero
  have hmem : P.asIdeal ∈ UniqueFactorizationMonoid.normalizedFactors I :=
    (UniqueFactorizationMonoid.mem_normalizedFactors_iff hI).2 ⟨P.prime, hdiv⟩
  have hzero :
      (if h : P.asIdeal.IsPrime ∧ P.asIdeal ≠ ⊥ then
        ArtinPrimitiveRoots.A1.chiPow D ⟨P.asIdeal, h.1, h.2⟩ x e else 1) = 0 := by
    rw [dif_pos ⟨P.isPrime, P.ne_bot⟩]
    simp [ArtinPrimitiveRoots.A1.chiPow, hx]
  exact Multiset.mem_map.mpr ⟨P.asIdeal, hmem, hzero⟩

private theorem rf_twistProduct_zero
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    (x : F) (e : ArtinPrimitiveRoots.A1.FinPlace F → ℤ)
    (P : ArtinPrimitiveRoots.A1.FinPlace F) (hdiv : P.asIdeal ∣ I)
    (hx : ArtinPrimitiveRoots.A1.residue P x = 0) :
    (∏ᶠ Q : ArtinPrimitiveRoots.A1.FinPlace F,
      if Q.asIdeal ∣ I then ArtinPrimitiveRoots.A1.chiPow D Q x (e Q) else 1) = 0 := by
  classical
  let f : ArtinPrimitiveRoots.A1.FinPlace F → ℂ := fun Q =>
    if Q.asIdeal ∣ I then ArtinPrimitiveRoots.A1.chiPow D Q x (e Q) else 1
  have hsupp : Function.mulSupport f ⊆ {Q | Q.asIdeal ∣ I} := by
    intro Q hQ
    change f Q ≠ 1 at hQ
    by_cases hdivQ : Q.asIdeal ∣ I
    · exact hdivQ
    · simp [f, hdivQ] at hQ
  rw [finprod_eq_prod_of_mulSupport_subset_of_finite f hsupp (Ideal.finite_factors hI)]
  apply Finset.prod_eq_zero ((Ideal.finite_factors hI).mem_toFinset.mpr hdiv)
  simp [f, hdiv, ArtinPrimitiveRoots.A1.chiPow, hx]

private theorem rf_chiPow_mod_six
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (SB : ArtinPrimitiveRoots.A2.SymbolBridge D S)
    (P : ArtinPrimitiveRoots.A1.FinPlace F) (x : F) (e : ℤ)
    (hx : ArtinPrimitiveRoots.A1.residue P x ≠ 0) :
    ArtinPrimitiveRoots.A1.chiPow D P x (e % 6) =
      ArtinPrimitiveRoots.A1.chiPow D P x e := by
  simp only [ArtinPrimitiveRoots.A1.chiPow, if_neg hx]
  have hnorm := SB.chi_norm P x hx
  have hχ0 : ArtinPrimitiveRoots.A1.chi D P x ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    norm_num at hnorm
  let u : ℂˣ := Units.mk0 (ArtinPrimitiveRoots.A1.chi D P x) hχ0
  have hu6 : u ^ 6 = 1 := by
    apply Units.ext
    change ArtinPrimitiveRoots.A1.chi D P x ^ 6 = 1
    exact SB.chi_six P x hx
  have hpow := congrArg (fun y : ℂˣ => (y : ℂ)) (zpow_eq_zpow_emod' e hu6)
  simpa [u, Units.val_zpow_eq_zpow_val] using hpow.symm

private def rf_symbolUnit
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (P : ArtinPrimitiveRoots.A1.FinPlace F) (x : F) : ℂˣ :=
  Units.map D.σ0.toMonoidHom
    (Units.map (algebraMap (𝓞 F) F).toMonoidHom
      (ArtinPrimitiveRoots.A1.chiAlg P x : (𝓞 F)ˣ))

private theorem rf_symbolUnit_coe
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (P : ArtinPrimitiveRoots.A1.FinPlace F) (x : F)
    (hx : ArtinPrimitiveRoots.A1.residue P x ≠ 0) :
    (rf_symbolUnit D P x : ℂ) = ArtinPrimitiveRoots.A1.chi D P x := by
  simp [rf_symbolUnit, ArtinPrimitiveRoots.A1.chi, hx]

private theorem rf_ideal_symbol_reciprocity
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H)
    (I J : Ideal (𝓞 F)) (hI : S.IsExterior I) (hJ : S.IsExterior J)
    (a b : Fˣ)
    (ha : S.IsGen (a : F) J ∧ Bd.Allowed a)
    (hb : S.IsGen (b : F) I ∧ Bd.Allowed b)
    (hcop : IsCoprime I J) :
    ArtinPrimitiveRoots.A1.chiIdealPow D J (b : F) 1 =
      ArtinPrimitiveRoots.A1.chiIdealPow D I (a : F) 1 := by
  classical
  let SB := ArtinPrimitiveRoots.A2.a2_bridge_SYMBOL D S
  let g : rootsOfUnity 6 F →* ℂ :=
    (Units.coeHom ℂ).comp
      ((Units.map D.σ0.toMonoidHom).comp (rootsOfUnity 6 F).subtype)
  let f : ArtinPrimitiveRoots.A1.FinPlace F → ℂ := fun P =>
    g (H.hilb P (ArtinPrimitiveRoots.A1.toLoc P b) (ArtinPrimitiveRoots.A1.toLoc P a))
  let gJ : ArtinPrimitiveRoots.A1.FinPlace F → ℂ := fun P =>
    if P.asIdeal ∣ J then
      (rf_symbolUnit D P (b : F) : ℂ) ^ (ArtinPrimitiveRoots.A1.idealExp P J : ℤ)
    else 1
  let gI : ArtinPrimitiveRoots.A1.FinPlace F → ℂ := fun P =>
    if P.asIdeal ∣ I then
      (rf_symbolUnit D P (a : F) : ℂ) ^ (ArtinPrimitiveRoots.A1.idealExp P I : ℤ)
    else 1
  have hglobal := H.product_formula b a
  have hf : Function.HasFiniteMulSupport f := by
    change Function.HasFiniteMulSupport
      (fun P => g (H.hilb P (ArtinPrimitiveRoots.A1.toLoc P b)
        (ArtinPrimitiveRoots.A1.toLoc P a)))
    exact Function.HasFiniteMulSupport.fun_comp hglobal.1 g.map_one
  have hglobalComplex : (∏ᶠ P : ArtinPrimitiveRoots.A1.FinPlace F, f P) = 1 := by
    change (∏ᶠ P : ArtinPrimitiveRoots.A1.FinPlace F,
      g (H.hilb P (ArtinPrimitiveRoots.A1.toLoc P b) (ArtinPrimitiveRoots.A1.toLoc P a))) = 1
    rw [← g.map_finprod hglobal.1, hglobal.2, g.map_one]
  have hcomp (v : S.Sf) (u : Fˣ) :
      S.compU v (S.diagU u) = ArtinPrimitiveRoots.A1.toLoc v.1 u := by
    ext
    rfl
  have hHS : S.HS H (S.diagU b) (S.diagU a) = 1 :=
    Bd.isotropic (S.diagU b) (S.diagU a) hb.2 ha.2
  have hSprod : (∏ P ∈ S.Sf, f P) = g (S.HS H (S.diagU b) (S.diagU a)) := by
    calc
      (∏ P ∈ S.Sf, f P) = ∏ P ∈ S.Sf.attach, f P.1 :=
        (Finset.prod_attach S.Sf f).symm
      _ = g (S.HS H (S.diagU b) (S.diagU a)) := by
        unfold ArtinPrimitiveRoots.A1.SData.HS
        simp [f, g, hcomp]
  have splitS (u : ArtinPrimitiveRoots.A1.FinPlace F → ℂ)
      (hu : Function.HasFiniteMulSupport u) :
      (∏ᶠ P : ArtinPrimitiveRoots.A1.FinPlace F, u P) =
        (∏ P ∈ S.Sf, u P) * ∏ᶠ P ∉ S.Sf, u P := by
    have h_union := finprod_mem_union' (hst := disjoint_compl_right)
      (hs := S.Sf.finite_toSet.inter_of_left _)
      (ht := Set.Finite.subset hu Set.inter_subset_right) (f := u)
    rw [Set.union_compl_self, finprod_mem_univ] at h_union
    rw [finprod_mem_coe_finset] at h_union
    exact h_union
  have houtside : (∏ᶠ P ∉ S.Sf, f P) = 1 := by
    have h := hglobalComplex
    rw [splitS f hf, hSprod, hHS] at h
    simpa using h
  have hnotI (P : ArtinPrimitiveRoots.A1.FinPlace F)
      (hPJ : P.asIdeal ∣ J) : ¬P.asIdeal ∣ I := by
    intro hPI
    exact P.irreducible.not_isUnit (hcop.isUnit_of_dvd' hPI hPJ)
  have hnotJ (P : ArtinPrimitiveRoots.A1.FinPlace F)
      (hPI : P.asIdeal ∣ I) : ¬P.asIdeal ∣ J := by
    intro hPJ
    exact P.irreducible.not_isUnit (hcop.isUnit_of_dvd' hPI hPJ)
  have residue_of_gen (P : ArtinPrimitiveRoots.A1.FinPlace F)
      (hP : P ∉ S.Sf) (X : Ideal (𝓞 F)) (x : Fˣ)
      (hx : S.IsGen (x : F) X) (hnot : ¬P.asIdeal ∣ X) :
      ArtinPrimitiveRoots.A1.residue P (x : F) ≠ 0 := by
    have hexp : ArtinPrimitiveRoots.A1.idealExp P X = 0 :=
      (rf_idealExp_eq_zero_iff X hx.1.1 P).2 hnot
    have hval : P.valuation F (x : F) = 1 := by
      simpa [hexp] using rf_gen_valuation S X x hx P hP
    exact (SB.residue_ne_zero P (x : F) hval.le).2 hval
  have tameEval (P : ArtinPrimitiveRoots.A1.FinPlace F)
      (hP : P ∉ S.Sf) (h6 : (6 : 𝓞 F) ∉ P.asIdeal)
      (u x : Fˣ) (hres : ArtinPrimitiveRoots.A1.residue P (u : F) ≠ 0)
      (X : Ideal (𝓞 F)) (hx : S.IsGen (x : F) X) :
      g (H.hilb P (ArtinPrimitiveRoots.A1.toLoc P u)
          (ArtinPrimitiveRoots.A1.toLoc P x)) =
        (rf_symbolUnit D P (u : F) : ℂ) ^
          (ArtinPrimitiveRoots.A1.idealExp P X : ℤ) := by
    have htame := H.tame P h6 u x hres
    rw [rf_gen_count S X x hx P hP] at htame
    change D.σ0 (((H.hilb P (ArtinPrimitiveRoots.A1.toLoc P u)
        (ArtinPrimitiveRoots.A1.toLoc P x) : Fˣ) : F)) = _
    rw [htame]
    simp [rf_symbolUnit]
  have hlocal (P : ArtinPrimitiveRoots.A1.FinPlace F) (hP : P ∉ S.Sf) :
      f P = gJ P * (gI P)⁻¹ := by
    have h6 : (6 : 𝓞 F) ∉ P.asIdeal := by
      intro h
      exact hP (S.over6 P h)
    by_cases hPJ : P.asIdeal ∣ J
    · have hPI : ¬P.asIdeal ∣ I := hnotI P hPJ
      have hresB := residue_of_gen P hP I b hb.1 hPI
      have hlocalB := tameEval P hP h6 b a hresB J ha.1
      simp [f, gJ, gI, hPJ, hPI, hlocalB]
    · by_cases hPI : P.asIdeal ∣ I
      · have hresA := residue_of_gen P hP J a ha.1 hPJ
        have hlocalA := tameEval P hP h6 a b hresA I hb.1
        have hskewRoot :
            g (H.hilb P (ArtinPrimitiveRoots.A1.toLoc P b)
              (ArtinPrimitiveRoots.A1.toLoc P a)) *
            g (H.hilb P (ArtinPrimitiveRoots.A1.toLoc P a)
              (ArtinPrimitiveRoots.A1.toLoc P b)) = 1 := by
          rw [← g.map_mul, H.skew, g.map_one]
        have hskew' : f P * (rf_symbolUnit D P (a : F) : ℂ) ^
            (ArtinPrimitiveRoots.A1.idealExp P I : ℤ) = 1 := by
          calc
            f P * (rf_symbolUnit D P (a : F) : ℂ) ^
                (ArtinPrimitiveRoots.A1.idealExp P I : ℤ) =
                g (H.hilb P (ArtinPrimitiveRoots.A1.toLoc P b)
                  (ArtinPrimitiveRoots.A1.toLoc P a)) *
                g (H.hilb P (ArtinPrimitiveRoots.A1.toLoc P a)
                  (ArtinPrimitiveRoots.A1.toLoc P b)) := by rw [hlocalA]
            _ = 1 := hskewRoot
        have hfinv : f P =
            ((rf_symbolUnit D P (a : F) : ℂ) ^
              (ArtinPrimitiveRoots.A1.idealExp P I : ℤ))⁻¹ := by
          calc
            f P = f P * 1 := by simp
            _ = f P * ((rf_symbolUnit D P (a : F) : ℂ) ^
                (ArtinPrimitiveRoots.A1.idealExp P I : ℤ) *
                ((rf_symbolUnit D P (a : F) : ℂ) ^
                  (ArtinPrimitiveRoots.A1.idealExp P I : ℤ))⁻¹) := by simp
            _ = (f P * (rf_symbolUnit D P (a : F) : ℂ) ^
                (ArtinPrimitiveRoots.A1.idealExp P I : ℤ)) *
                ((rf_symbolUnit D P (a : F) : ℂ) ^
                  (ArtinPrimitiveRoots.A1.idealExp P I : ℤ))⁻¹ := by rw [mul_assoc]
            _ = _ := by rw [hskew']; simp
        simp [f, gJ, gI, hPJ, hPI, hfinv]
      · have hresB := residue_of_gen P hP I b hb.1 hPI
        have hlocalB := tameEval P hP h6 b a hresB J ha.1
        have hExpJ : ArtinPrimitiveRoots.A1.idealExp P J = 0 :=
          (rf_idealExp_eq_zero_iff J hJ.1 P).2 hPJ
        simp [f, gJ, gI, hPJ, hPI, hlocalB, hExpJ]
  have hgJ_support : Function.mulSupport gJ ⊆ {P | P.asIdeal ∣ J} := by
    intro P hP
    change gJ P ≠ 1 at hP
    by_cases hdiv : P.asIdeal ∣ J
    · exact hdiv
    · simp [gJ, hdiv] at hP
  have hgI_support : Function.mulSupport gI ⊆ {P | P.asIdeal ∣ I} := by
    intro P hP
    change gI P ≠ 1 at hP
    by_cases hdiv : P.asIdeal ∣ I
    · exact hdiv
    · simp [gI, hdiv] at hP
  have hgJ : Function.HasFiniteMulSupport gJ :=
    Set.Finite.subset (Ideal.finite_factors hJ.1) hgJ_support
  have hgI : Function.HasFiniteMulSupport gI :=
    Set.Finite.subset (Ideal.finite_factors hI.1) hgI_support
  have hJsf : ∀ P ∈ S.Sf, gJ P = 1 := by
    intro P hP
    have hnot : ¬P.asIdeal ∣ J := by
      intro hdiv
      exact hJ.2 P hP (Ideal.dvd_iff_le.mp hdiv)
    simp [gJ, hnot]
  have hIsf : ∀ P ∈ S.Sf, gI P = 1 := by
    intro P hP
    have hnot : ¬P.asIdeal ∣ I := by
      intro hdiv
      exact hI.2 P hP (Ideal.dvd_iff_le.mp hdiv)
    simp [gI, hnot]
  have hJall : (∏ᶠ P, gJ P) = ∏ᶠ P ∉ S.Sf, gJ P := by
    rw [splitS gJ hgJ, Finset.prod_eq_one hJsf, one_mul]
  have hIall : (∏ᶠ P, gI P) = ∏ᶠ P ∉ S.Sf, gI P := by
    rw [splitS gI hgI, Finset.prod_eq_one hIsf, one_mul]
  have hInvI : (∏ᶠ P ∉ S.Sf, gI P)⁻¹ =
      ∏ᶠ P ∉ S.Sf, (gI P)⁻¹ := by
    exact (MulEquiv.inv ℂ).toMonoidHom.map_finprod_mem'
      (Set.Finite.subset hgI Set.inter_subset_right)
  have hOutEq : (∏ᶠ P ∉ S.Sf, f P) =
      (∏ᶠ P ∉ S.Sf, gJ P) * (∏ᶠ P ∉ S.Sf, gI P)⁻¹ := by
    calc
      (∏ᶠ P ∉ S.Sf, f P) =
          ∏ᶠ P ∉ S.Sf, gJ P * (gI P)⁻¹ := by
            exact finprod_mem_congr rfl (fun P hP => hlocal P hP)
      _ = (∏ᶠ P ∉ S.Sf, gJ P) *
            (∏ᶠ P ∉ S.Sf, (gI P)⁻¹) :=
              finprod_mem_mul_distrib'
                (f := gJ) (g := fun P => (gI P)⁻¹)
                (Set.Finite.subset hgJ Set.inter_subset_right)
                (Set.Finite.subset hgI.fun_inv Set.inter_subset_right)
      _ = (∏ᶠ P ∉ S.Sf, gJ P) * (∏ᶠ P ∉ S.Sf, gI P)⁻¹ := by rw [← hInvI]
  have hJχ : ArtinPrimitiveRoots.A1.chiIdealPow D J (b : F) 1 =
      ∏ᶠ P, gJ P := by
    rw [rf_chiIdealPow_finprod D J hJ.1 (b : F) 1]
    apply finprod_congr
    intro P
    by_cases hdiv : P.asIdeal ∣ J
    · have hP : P ∉ S.Sf := by
        intro hP
        exact hJ.2 P hP (Ideal.dvd_iff_le.mp hdiv)
      have hresB := residue_of_gen P hP I b hb.1 (hnotI P hdiv)
      simp [gJ, hdiv, ArtinPrimitiveRoots.A1.chiPow, hresB,
        rf_symbolUnit_coe D P (b : F) hresB]
    · simp [gJ, hdiv]
  have hIχ : ArtinPrimitiveRoots.A1.chiIdealPow D I (a : F) 1 =
      ∏ᶠ P, gI P := by
    rw [rf_chiIdealPow_finprod D I hI.1 (a : F) 1]
    apply finprod_congr
    intro P
    by_cases hdiv : P.asIdeal ∣ I
    · have hP : P ∉ S.Sf := by
        intro hP
        exact hI.2 P hP (Ideal.dvd_iff_le.mp hdiv)
      have hresA := residue_of_gen P hP J a ha.1 (hnotJ P hdiv)
      simp [gI, hdiv, ArtinPrimitiveRoots.A1.chiPow, hresA,
        rf_symbolUnit_coe D P (a : F) hresA]
    · simp [gI, hdiv]
  have hJoutIout : (∏ᶠ P ∉ S.Sf, gJ P) =
      ∏ᶠ P ∉ S.Sf, gI P := by
    have h := houtside
    rw [hOutEq] at h
    calc
      (∏ᶠ P ∉ S.Sf, gJ P) =
          (∏ᶠ P ∉ S.Sf, gJ P) * 1 := by simp
      _ = (∏ᶠ P ∉ S.Sf, gJ P) *
          ((∏ᶠ P ∉ S.Sf, gI P)⁻¹ * ∏ᶠ P ∉ S.Sf, gI P) := by
            rw [inv_mul_cancel₀ (by
              have htotal : (∏ᶠ P, gI P) ≠ 0 := by
                apply finprod_ne_zero
                intro P
                by_cases hdiv : P.asIdeal ∣ I
                · simp only [gI, if_pos hdiv]
                  exact zpow_ne_zero _ (Units.ne_zero (rf_symbolUnit D P (a : F)))
                · simp [gI, hdiv]
              intro hz
              apply htotal
              rw [hIall, hz])]
      _ = ((∏ᶠ P ∉ S.Sf, gJ P) *
          (∏ᶠ P ∉ S.Sf, gI P)⁻¹) * ∏ᶠ P ∉ S.Sf, gI P := by rw [mul_assoc]
      _ = 1 * ∏ᶠ P ∉ S.Sf, gI P := by rw [h]
      _ = ∏ᶠ P ∉ S.Sf, gI P := by simp
  calc
    ArtinPrimitiveRoots.A1.chiIdealPow D J (b : F) 1 = ∏ᶠ P, gJ P := hJχ
    _ = ∏ᶠ P ∉ S.Sf, gJ P := hJall
    _ = ∏ᶠ P ∉ S.Sf, gI P := hJoutIout
    _ = ∏ᶠ P, gI P := hIall.symm
    _ = ArtinPrimitiveRoots.A1.chiIdealPow D I (a : F) 1 := hIχ.symm

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
  classical
  let I := r.ideal.1
  let ε := rowEpsilon S bc r
  let b := bc.gen r.ideal
  have hI : S.IsExterior I := r.ideal.2
  have hI0 : I ≠ ⊥ := r.ideal.2.1
  have hεgen : rowElement S r = ε * b :=
    Classical.choose_spec (exists_rowUnit S bc r)
  have hb : S.IsGen (b : F) I ∧ Bd.Allowed b := bc.gen_spec r.ideal
  let SB := ArtinPrimitiveRoots.A2.a2_bridge_SYMBOL D S
  have hxy (P : ArtinPrimitiveRoots.A1.FinPlace F) (hPJ : P.asIdeal ∣ J) :
      P.valuation F ((ε : Fˣ) : F) ≤ 1 ∧ P.valuation F (b : F) ≤ 1 := by
    have hP : P ∉ S.Sf := by
      intro hP
      exact hJ.2 P hP (Ideal.dvd_iff_le.mp hPJ)
    refine ⟨?_, ?_⟩
    · simpa [ε.property P hP]
    · have hval := rf_gen_valuation S I b hb.1 P hP
      have hle :
          WithZero.exp (-(ArtinPrimitiveRoots.A1.idealExp P I : ℤ)) ≤ 1 := by
        rw [← WithZero.exp_zero]
        have hn : (0 : ℤ) ≤ (ArtinPrimitiveRoots.A1.idealExp P I : ℤ) :=
          by exact_mod_cast (Nat.zero_le (ArtinPrimitiveRoots.A1.idealExp P I))
        exact WithZero.exp_le_exp.mpr (neg_nonpos.mpr hn)
      simpa [hval] using hle
  have hfactorBase :=
    SB.ideal_element_mul J hJ ((ε : Fˣ) : F) (b : F) 1 hxy
  have hfactor :
      ArtinPrimitiveRoots.A1.chiIdealPow D J (rowElement S r : F) 1 =
        ArtinPrimitiveRoots.A1.chiIdealPow D J ((ε : Fˣ) : F) 1 *
          ArtinPrimitiveRoots.A1.chiIdealPow D J (b : F) 1 := by
    rw [hεgen]
    exact hfactorBase
  by_cases hcop : IsCoprime I J
  · have hrecip := rf_ideal_symbol_reciprocity D S H Bd I J hI hJ a b ha hb hcop
    have hrowProduct :
        (∏ᶠ P : ArtinPrimitiveRoots.A1.FinPlace F,
          if P.asIdeal ∣ I then
            ArtinPrimitiveRoots.A1.chiPow D P (a : F) (rowPrimeExponent S r P)
          else 1) = ArtinPrimitiveRoots.A1.chiIdealPow D I (a : F) 1 := by
      rw [rf_chiIdealPow_finprod D I hI0 (a : F) 1]
      apply finprod_congr
      intro P
      by_cases hdiv : P.asIdeal ∣ I
      · have hP : P ∉ S.Sf := by
          intro hP
          exact hI.2 P hP (Ideal.dvd_iff_le.mp hdiv)
        have hnotJ : ¬P.asIdeal ∣ J := by
          intro hdivJ
          exact P.irreducible.not_isUnit (hcop.isUnit_of_dvd' hdiv hdivJ)
        have hresA := rf_residue_ne_zero_of_gen_not_dvd D S SB J a ha.1 P hP hnotJ
        have hexpRow : rowPrimeExponent S r P =
            (ArtinPrimitiveRoots.A1.idealExp P I : ℤ) % 6 := by
          unfold rowPrimeExponent rowExponentModSix
          rw [FractionalIdeal.count_coe F P hI0]
          rfl
        rw [if_pos hdiv, if_pos hdiv, hexpRow]
        simp only [one_mul]
        exact rf_chiPow_mod_six D S SB P (a : F)
          (ArtinPrimitiveRoots.A1.idealExp P I : ℤ) hresA
      · simp [hdiv]
    calc
      ArtinPrimitiveRoots.A1.chiIdealPow D J (rowElement S r : F) 1 =
          ArtinPrimitiveRoots.A1.chiIdealPow D J ((ε : Fˣ) : F) 1 *
            ArtinPrimitiveRoots.A1.chiIdealPow D J (b : F) 1 := hfactor
      _ = ArtinPrimitiveRoots.A1.chiIdealPow D J ((ε : Fˣ) : F) 1 *
            ArtinPrimitiveRoots.A1.chiIdealPow D I (a : F) 1 := by rw [hrecip]
      _ = ArtinPrimitiveRoots.A1.chiIdealPow D J ((ε : Fˣ) : F) 1 *
            (∏ᶠ P : ArtinPrimitiveRoots.A1.FinPlace F,
              if P.asIdeal ∣ I then
                ArtinPrimitiveRoots.A1.chiPow D P (a : F) (rowPrimeExponent S r P)
              else 1) := by rw [← hrowProduct]
  · have hnotcop_sup : I ⊔ J ≠ ⊤ := by
      intro htop
      exact hcop (Ideal.isCoprime_iff_sup_eq.mpr htop)
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (I ⊔ J) hnotcop_sup
    have hMbot : M ≠ ⊥ := by
      intro hbot
      apply hI.1
      apply le_antisymm
      · exact (le_trans le_sup_left hle).trans_eq hbot
      · exact bot_le
    let P : ArtinPrimitiveRoots.A1.FinPlace F := ⟨M, hM.isPrime, hMbot⟩
    have hPI : P.asIdeal ∣ I := Ideal.dvd_iff_le.mpr (le_trans le_sup_left hle)
    have hPJ : P.asIdeal ∣ J := Ideal.dvd_iff_le.mpr (le_trans le_sup_right hle)
    have hP : P ∉ S.Sf := by
      intro hP
      exact hI.2 P hP (Ideal.dvd_iff_le.mp hPI)
    have hrowgen : S.IsGen (rowElement S r : F) I := by
      simpa [rowElement] using r.generates
    have hresRow := rf_residue_zero_of_gen D S SB I (rowElement S r) hrowgen P hP hPI
    have hresB := rf_residue_zero_of_gen D S SB I b hb.1 P hP hPI
    have hresA := rf_residue_zero_of_gen D S SB J a ha.1 P hP hPJ
    have hzeroB := rf_chiIdealPow_zero_of_prime D J hJ.1 P hPJ (b : F) hresB 1
    have hzeroL : ArtinPrimitiveRoots.A1.chiIdealPow D J (rowElement S r : F) 1 = 0 := by
      rw [hfactor, hzeroB]
      simp
    have hzeroR := rf_twistProduct_zero D I hI0 (a : F)
      (fun Q => rowPrimeExponent S r Q) P hPI hresA
    rw [hzeroL, hzeroR]
    simp

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
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro J hJ a hgen hallowed
    change S.LS (ArtinPrimitiveRoots.A1.vartheta Λ G η) (S.diagU a) *
        D.σ0 (((S.HS H (S.diagU ε) (S.diagU a))⁻¹ : Fˣ) : F) = _
    have hLS := ArtinPrimitiveRoots.A2.rf_heckeChar_idealValue_eq_LS_of_gen
      D S (ArtinPrimitiveRoots.A1.vartheta Λ G η) houtside J a hgen
    rw [hLS]
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
  classical
  letI := ArtinPrimitiveRoots.A2.bridgeResidueField P
  letI := ArtinPrimitiveRoots.A2.bridgeResidueFintype P
  obtain ⟨_, ⟨χ, hχord, hχval⟩, ⟨ψ, hψprim, hψval⟩⟩ :=
    ArtinPrimitiveRoots.A2.a2_bridge_FINITE_CHAR D S A P hP p hp.1
  let SB := ArtinPrimitiveRoots.A2.a2_bridge_SYMBOL D S
  have hres (x : 𝓞 F ⧸ P.asIdeal) :
      ArtinPrimitiveRoots.A1.residue P (algebraMap (𝓞 F) F x.out) = x :=
    by simpa using SB.residue_algebraMap P x.out
  have hphase (t x : 𝓞 F ⧸ P.asIdeal) :
      maskPhase A P p t x = ψ (t * x) := (hψval t x).symm
  have hcharPower (e : ℤ) (x : 𝓞 F ⧸ P.asIdeal) :
      (χ ^ e) x = ArtinPrimitiveRoots.A1.chiPow D P
        (algebraMap (𝓞 F) F x.out) e := by
    by_cases hx : x = 0
    · subst x
      have hz : ArtinPrimitiveRoots.A1.residue P
          (algebraMap (𝓞 F) F (0 : 𝓞 F ⧸ P.asIdeal).out) = 0 := by
        rw [hres]
      rw [MulChar.map_nonunit _ (by simp : ¬ IsUnit (0 : 𝓞 F ⧸ P.asIdeal)),
        SB.chiPow_zero P _ e hz]
    · let u : (𝓞 F ⧸ P.asIdeal)ˣ := Units.mk0 x hx
      have hχu : χ (u : 𝓞 F ⧸ P.asIdeal) = ArtinPrimitiveRoots.A1.chiPow D P
          (algebraMap (𝓞 F) F x.out) 1 := by
        change χ x = _
        exact hχval x
      have hresne : ArtinPrimitiveRoots.A1.residue P
          (algebraMap (𝓞 F) F x.out) ≠ 0 := by
        rw [hres]
        exact hx
      have hEval : (χ ^ e) (u : 𝓞 F ⧸ P.asIdeal) = (χ u) ^ e := by
        calc
          (χ ^ e) (u : 𝓞 F ⧸ P.asIdeal) = χ (u ^ e : (𝓞 F ⧸ P.asIdeal)ˣ) :=
            MulChar.zpow_apply_coe χ e u
          _ = (χ u) ^ e := by
            change ((χ.toUnitHom (u ^ e) : ℂˣ) : ℂ) =
              ((χ.toUnitHom u : ℂˣ) : ℂ) ^ e
            rw [map_zpow, Units.val_zpow_eq_zpow_val]
      have hEvalX : (χ ^ e) x = (χ x) ^ e := by
        change (χ ^ e) (u : 𝓞 F ⧸ P.asIdeal) = (χ u) ^ e
        exact hEval
      calc
        (χ ^ e) x = (χ x) ^ e := hEvalX
        _ = (ArtinPrimitiveRoots.A1.chiPow D P
            (algebraMap (𝓞 F) F x.out) 1) ^ e := by rw [hχval x]
        _ = ArtinPrimitiveRoots.A1.chiPow D P
            (algebraMap (𝓞 F) F x.out) e := by
          rw [SB.chiPow_nonzero P _ 1 hresne, SB.chiPow_nonzero P _ e hresne]
          simp
  have htau (j : Fin 6) :
      maskTau D A P p j = gaussSum (χ ^ (-(j.1 : ℤ))) ψ := by
    unfold maskTau
    rw [ArtinPrimitiveRoots.A2.a2_bridge_FINITE_CHAR_finsum P
      (fun x : 𝓞 F ⧸ P.asIdeal => if x = 0 then 0 else
        ArtinPrimitiveRoots.A1.chi D P (algebraMap (𝓞 F) F x.out) ^ (-(j.1 : ℤ)) *
          maskPhase A P p 1 x)]
    rw [gaussSum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x = 0
    · subst x
      have hχzero : ((χ ^ (j.1 : ℤ))⁻¹) (0 : 𝓞 F ⧸ P.asIdeal) = 0 :=
        MulChar.map_nonunit _ (by simp : ¬ IsUnit (0 : 𝓞 F ⧸ P.asIdeal))
      simpa [zpow_neg] using hχzero.symm
    · have hresne : ArtinPrimitiveRoots.A1.residue P
          (algebraMap (𝓞 F) F x.out) ≠ 0 := by
        rw [hres]
        exact hx
      have hcoeff : ArtinPrimitiveRoots.A1.chi D P
          (algebraMap (𝓞 F) F x.out) ^ (-(j.1 : ℤ)) =
          (χ ^ (-(j.1 : ℤ))) x := by
        calc
          _ = ArtinPrimitiveRoots.A1.chiPow D P
              (algebraMap (𝓞 F) F x.out) (-(j.1 : ℤ)) :=
                (SB.chiPow_nonzero P _ _ hresne).symm
          _ = (χ ^ (-(j.1 : ℤ))) x := (hcharPower _ x).symm
      simp only [if_neg hx]
      rw [hcoeff, hphase]
      simp
  have hcharNotOne (j : Fin 6) (hj : j ≠ 0) :
      χ ^ (-(j.1 : ℤ)) ≠ (1 : MulChar (𝓞 F ⧸ P.asIdeal) ℂ) := by
    intro h
    have hd : (orderOf χ : ℤ) ∣ -(j.1 : ℤ) :=
      (orderOf_dvd_iff_zpow_eq_one).2 h
    rw [hχord] at hd
    have hd' : (6 : ℤ) ∣ (j.1 : ℤ) := by
      simpa using (dvd_neg.mp hd)
    have hdNat : 6 ∣ j.1 := Int.natCast_dvd_natCast.mp hd'
    have hjval : j.1 ≠ 0 := by
      intro hv
      apply hj
      exact Fin.ext hv
    have hjpos : 0 < j.1 := Nat.pos_of_ne_zero hjval
    have hjle : 6 ≤ j.1 := Nat.le_of_dvd hjpos hdNat
    omega
  have hcardPos : 0 < Fintype.card (𝓞 F ⧸ P.asIdeal) := Fintype.card_pos
  have hcardNe : (Fintype.card (𝓞 F ⧸ P.asIdeal) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hcardPos)
  have hnormCard :
      Fintype.card (𝓞 F ⧸ P.asIdeal) = Ideal.absNorm P.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hcardNorm : (Fintype.card (𝓞 F ⧸ P.asIdeal) : ℂ) =
      (Ideal.absNorm P.asIdeal : ℂ) := by exact_mod_cast hnormCard
  have hqNe : (Ideal.absNorm P.asIdeal : ℂ) ≠ 0 := by
    rw [← hcardNorm]
    exact hcardNe
  have horth (t : 𝓞 F ⧸ P.asIdeal) :
      (∑ x : 𝓞 F ⧸ P.asIdeal, ψ (t * x)) =
        if t = 0 then (Ideal.absNorm P.asIdeal : ℂ) else 0 :=
    ArtinPrimitiveRoots.A2.a2_bridge_FINITE_CHAR_orthogonality P ψ hψprim t
  have hfinsum (f : (𝓞 F ⧸ P.asIdeal) → ℂ) :
      (∑ᶠ x : 𝓞 F ⧸ P.asIdeal, f x) = ∑ x, f x :=
    ArtinPrimitiveRoots.A2.a2_bridge_FINITE_CHAR_finsum P f
  intro j t
  by_cases hj : j = 0
  · subst j
    have htarget : ArtinPrimitiveRoots.A1.chiPow D P
        (algebraMap (𝓞 F) F t.out) 0 = if t = 0 then 0 else 1 := by
      by_cases ht : t = 0 <;> simp [ArtinPrimitiveRoots.A1.chiPow, hres, ht]
    calc
      (∑ᶠ x : 𝓞 F ⧸ P.asIdeal,
          maskAlpha D A P p 0 x * maskPhase A P p t x) =
          ∑ x : 𝓞 F ⧸ P.asIdeal,
            maskAlpha D A P p 0 x * maskPhase A P p t x := hfinsum _
      _ = 1 - (Ideal.absNorm P.asIdeal : ℂ)⁻¹ *
          ∑ x : 𝓞 F ⧸ P.asIdeal, ψ (t * x) := by
        calc
          _ = ∑ x : 𝓞 F ⧸ P.asIdeal,
              ((if x = 0 then (1 : ℂ) else 0) -
                (Ideal.absNorm P.asIdeal : ℂ)⁻¹) * ψ (t * x) := by
            apply Finset.sum_congr rfl
            intro x _
            by_cases hx : x = 0 <;> simp [maskAlpha, hx, hphase]
          _ = (∑ x : 𝓞 F ⧸ P.asIdeal,
                (if x = 0 then (1 : ℂ) else 0) * ψ (t * x)) -
              ∑ x : 𝓞 F ⧸ P.asIdeal,
                (Ideal.absNorm P.asIdeal : ℂ)⁻¹ * ψ (t * x) := by
            rw [← Finset.sum_sub_distrib]
            congr 1
            ext x
            ring
          _ = 1 - (Ideal.absNorm P.asIdeal : ℂ)⁻¹ *
              ∑ x : 𝓞 F ⧸ P.asIdeal, ψ (t * x) := by
            have hdelta : (∑ x : 𝓞 F ⧸ P.asIdeal,
                (if x = 0 then (1 : ℂ) else 0) * ψ (t * x)) = 1 := by
              simp
            rw [hdelta, Finset.mul_sum]
      _ = if t = 0 then 0 else 1 := by
        rw [horth]
        by_cases ht : t = 0 <;> simp [ht, hqNe]
      _ = ArtinPrimitiveRoots.A1.chiPow D P
          (algebraMap (𝓞 F) F t.out) 0 := htarget.symm
  · let χj : MulChar (𝓞 F ⧸ P.asIdeal) ℂ := χ ^ (-(j.1 : ℤ))
    have hχjNe : χj ≠ 1 := by
      simpa [χj] using hcharNotOne j hj
    have htauNe : maskTau D A P p j ≠ 0 := by
      rw [htau]
      exact gaussSum_ne_zero_of_nontrivial hcardNe hχjNe hψprim
    have hcoeff (x : 𝓞 F ⧸ P.asIdeal) :
        ArtinPrimitiveRoots.A1.chi D P (algebraMap (𝓞 F) F x.out) ^ (-(j.1 : ℤ)) =
          χj x := by
      by_cases hx : x = 0
      · subst x
        have hz : ArtinPrimitiveRoots.A1.residue P
            (algebraMap (𝓞 F) F (0 : 𝓞 F ⧸ P.asIdeal).out) = 0 := by
          rw [hres]
        have hχzero : ArtinPrimitiveRoots.A1.chi D P
            (algebraMap (𝓞 F) F (0 : 𝓞 F ⧸ P.asIdeal).out) = 0 := by
          simp [ArtinPrimitiveRoots.A1.chi, hz]
        have hχjzero : χj (0 : 𝓞 F ⧸ P.asIdeal) = 0 :=
          MulChar.map_zero χj
        have hjval : j.1 ≠ 0 := by
          intro h
          apply hj
          exact Fin.ext h
        have hexp : (-(j.1 : ℤ)) ≠ 0 := by
          apply neg_ne_zero.mpr
          exact_mod_cast hjval
        rw [hχzero, hχjzero]
        exact zero_zpow _ hexp
      · have hresne : ArtinPrimitiveRoots.A1.residue P
            (algebraMap (𝓞 F) F x.out) ≠ 0 := by
          rw [hres]
          exact hx
        calc
          _ = ArtinPrimitiveRoots.A1.chiPow D P
              (algebraMap (𝓞 F) F x.out) (-(j.1 : ℤ)) :=
                (SB.chiPow_nonzero P _ _ hresne).symm
          _ = χj x := (hcharPower _ x).symm
    have halpha (x : 𝓞 F ⧸ P.asIdeal) :
        maskAlpha D A P p j x = (maskTau D A P p j)⁻¹ * χj x := by
      by_cases hx : x = 0
      · subst x
        have hχjzero : χj (0 : 𝓞 F ⧸ P.asIdeal) = 0 :=
          MulChar.map_nonunit χj (by simp : ¬ IsUnit (0 : 𝓞 F ⧸ P.asIdeal))
        simp [maskAlpha, hj, hχjzero]
      · simp [maskAlpha, hj, hx, hcoeff]
    calc
      (∑ᶠ x : 𝓞 F ⧸ P.asIdeal,
          maskAlpha D A P p j x * maskPhase A P p t x) =
          ∑ x : 𝓞 F ⧸ P.asIdeal,
            maskAlpha D A P p j x * maskPhase A P p t x := hfinsum _
      _ = ArtinPrimitiveRoots.A1.chiPow D P
          (algebraMap (𝓞 F) F t.out) (j.1 : ℤ) := by
        by_cases ht : t = 0
        · subst t
          have hz : ArtinPrimitiveRoots.A1.residue P
              (algebraMap (𝓞 F) F (0 : 𝓞 F ⧸ P.asIdeal).out) = 0 := by
            rw [hres]
          have htarget0 : ArtinPrimitiveRoots.A1.chiPow D P
              (algebraMap (𝓞 F) F (0 : 𝓞 F ⧸ P.asIdeal).out) (j.1 : ℤ) = 0 :=
            SB.chiPow_zero P _ _ hz
          calc
            _ = (maskTau D A P p j)⁻¹ *
                ∑ x : 𝓞 F ⧸ P.asIdeal, χj x := by
              calc
                _ = ∑ x : 𝓞 F ⧸ P.asIdeal,
                    ((maskTau D A P p j)⁻¹ * χj x) * ψ (0 * x) := by
                  apply Finset.sum_congr rfl
                  intro x _
                  rw [halpha, hphase]
                _ = (maskTau D A P p j)⁻¹ *
                    ∑ x : 𝓞 F ⧸ P.asIdeal, χj x := by
                  simp only [zero_mul, ψ.map_zero_eq_one, mul_one]
                  rw [Finset.mul_sum]
            _ = 0 := by
              calc
                _ = (maskTau D A P p j)⁻¹ * 0 := by
                  rw [MulChar.sum_eq_zero_of_ne_one hχjNe]
                _ = 0 := by simp
            _ = ArtinPrimitiveRoots.A1.chiPow D P
                (algebraMap (𝓞 F) F (0 : 𝓞 F ⧸ P.asIdeal).out) (j.1 : ℤ) := htarget0.symm
        · have hsumChange :
              (∑ x : 𝓞 F ⧸ P.asIdeal, χj x * ψ (t * x)) =
                χj (t⁻¹) * gaussSum χj ψ := by
            calc
              _ = ∑ y : 𝓞 F ⧸ P.asIdeal,
                  χj (t⁻¹ * y) * ψ (t * (t⁻¹ * y)) := by
                rw [Fintype.sum_bijective (fun x : 𝓞 F ⧸ P.asIdeal => t * x)
                  (mulLeft_bijective₀ t ht)
                  (fun x => χj x * ψ (t * x))
                  (fun y => χj (t⁻¹ * y) * ψ (t * (t⁻¹ * y))) (by
                    intro x
                    rw [show t⁻¹ * (t * x) = x by
                      calc
                        t⁻¹ * (t * x) = (t⁻¹ * t) * x := by ac_rfl
                        _ = x := by
                          calc
                            _ = 1 * x := congrArg (fun z : 𝓞 F ⧸ P.asIdeal => z * x)
                              (inv_mul_cancel₀ ht)
                            _ = x := one_mul x])]
              _ = ∑ y : 𝓞 F ⧸ P.asIdeal, χj (t⁻¹) * (χj y * ψ y) := by
                apply Finset.sum_congr rfl
                intro y _
                rw [map_mul]
                have hy : t * (t⁻¹ * y) = y := by
                  calc
                    t * (t⁻¹ * y) = (t * t⁻¹) * y := by ac_rfl
                    _ = y := by
                      calc
                        _ = 1 * y := congrArg (fun z : 𝓞 F ⧸ P.asIdeal => z * y)
                          (mul_inv_cancel₀ ht)
                        _ = y := one_mul y
                rw [hy]
                ring
              _ = χj (t⁻¹) * ∑ y : 𝓞 F ⧸ P.asIdeal, χj y * ψ y := by
                rw [Finset.mul_sum]
              _ = χj (t⁻¹) * gaussSum χj ψ := by rw [gaussSum]
          have htarget : χj (t⁻¹) = ArtinPrimitiveRoots.A1.chiPow D P
              (algebraMap (𝓞 F) F t.out) (j.1 : ℤ) := by
            let u : (𝓞 F ⧸ P.asIdeal)ˣ := Units.mk0 t ht
            have hEval : (χ ^ (-(j.1 : ℤ))) (u⁻¹ : 𝓞 F ⧸ P.asIdeal) =
                (χ ^ (j.1 : ℤ)) (u : 𝓞 F ⧸ P.asIdeal) := by
              calc
                (χ ^ (-(j.1 : ℤ))) (u⁻¹ : 𝓞 F ⧸ P.asIdeal) =
                    χ ((u⁻¹) ^ (-(j.1 : ℤ)) : (𝓞 F ⧸ P.asIdeal)ˣ) :=
                      MulChar.zpow_apply_coe χ _ u⁻¹
                _ = χ (u ^ (j.1 : ℤ) : (𝓞 F ⧸ P.asIdeal)ˣ) := by
                  congr 1
                  simp
                _ = (χ ^ (j.1 : ℤ)) (u : 𝓞 F ⧸ P.asIdeal) :=
                  (MulChar.zpow_apply_coe χ _ u).symm
            calc
              χj (t⁻¹) = (χ ^ (-(j.1 : ℤ))) (u⁻¹ : 𝓞 F ⧸ P.asIdeal) := by
                change (χ ^ (-(j.1 : ℤ))) (t⁻¹ : 𝓞 F ⧸ P.asIdeal) = _
                congr 1
              _ = (χ ^ (j.1 : ℤ)) (u : 𝓞 F ⧸ P.asIdeal) := hEval
              _ = ArtinPrimitiveRoots.A1.chiPow D P
                  (algebraMap (𝓞 F) F t.out) (j.1 : ℤ) := by
                change (χ ^ (j.1 : ℤ)) t = _
                exact hcharPower (j.1 : ℤ) t
          calc
            _ = (maskTau D A P p j)⁻¹ *
                ∑ x : 𝓞 F ⧸ P.asIdeal, χj x * ψ (t * x) := by
              calc
                _ = ∑ x : 𝓞 F ⧸ P.asIdeal,
                    ((maskTau D A P p j)⁻¹ * χj x) * ψ (t * x) := by
                  apply Finset.sum_congr rfl
                  intro x _
                  rw [halpha, hphase]
                _ = (maskTau D A P p j)⁻¹ *
                    ∑ x : 𝓞 F ⧸ P.asIdeal, χj x * ψ (t * x) := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro x _
                  ring
            _ = (maskTau D A P p j)⁻¹ *
                (χj (t⁻¹) * gaussSum χj ψ) := by rw [hsumChange]
            _ = χj (t⁻¹) := by
              rw [htau j]
              have hGaussNe : gaussSum (χ ^ (-(j.1 : ℤ))) ψ ≠ 0 := by
                rw [← htau j]
                exact htauNe
              calc
                _ = χj (t⁻¹) *
                    ((gaussSum (χ ^ (-(j.1 : ℤ))) ψ)⁻¹ *
                      gaussSum (χ ^ (-(j.1 : ℤ))) ψ) := by ring
                _ = χj (t⁻¹) := by
                  rw [inv_mul_cancel₀ hGaussNe, mul_one]
            _ = ArtinPrimitiveRoots.A1.chiPow D P
                (algebraMap (𝓞 F) F t.out) (j.1 : ℤ) := htarget

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
private theorem rf_residue_algebraMap
    (P : ArtinPrimitiveRoots.A1.FinPlace F) (c : 𝓞 F) :
    ArtinPrimitiveRoots.A1.residue P (algebraMap (𝓞 F) F c) =
      Ideal.Quotient.mk P.asIdeal c := by
  letI : P.asIdeal.IsMaximal := P.isMaximal
  letI : Field (𝓞 F ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
  have hex : ∃ ab : 𝓞 F × 𝓞 F, ab.2 ∉ P.asIdeal ∧
      algebraMap (𝓞 F) F c * algebraMap (𝓞 F) F ab.2 =
        algebraMap (𝓞 F) F ab.1 :=
    ⟨(c, 1), Ideal.IsPrime.one_notMem P.isPrime, by simp⟩
  have hcross : hex.choose.1 * (1 : 𝓞 F) = c * hex.choose.2 := by
    apply IsFractionRing.injective (𝓞 F) F
    simp only [map_mul]
    rw [← hex.choose_spec.2]
    simp only [map_one]
    ring_nf
  have hqcross := congrArg (Ideal.Quotient.mk P.asIdeal) hcross
  have hdq : Ideal.Quotient.mk P.asIdeal hex.choose.2 ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hex.choose_spec.1
  unfold ArtinPrimitiveRoots.A1.residue
  rw [dif_pos hex, ← div_eq_mul_inv, ← div_one (Ideal.Quotient.mk P.asIdeal c),
    div_eq_div_iff hdq one_ne_zero]
  simpa only [map_mul, map_one] using hqcross

private theorem rf_chiAlg_residue_eq_pow
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (P : ArtinPrimitiveRoots.A1.FinPlace F)
    (h6 : (6 : 𝓞 F) ∉ P.asIdeal) (x : F)
    (hx : ArtinPrimitiveRoots.A1.residue P x ≠ 0) :
    Ideal.Quotient.mk P.asIdeal
        ((ArtinPrimitiveRoots.A1.chiAlg P x : (𝓞 F)ˣ) : 𝓞 F) =
      ArtinPrimitiveRoots.A1.residue P x ^
        ((Ideal.absNorm P.asIdeal - 1) / 6) := by
  classical
  haveI : P.asIdeal.IsMaximal := P.isMaximal
  let k := 𝓞 F ⧸ P.asIdeal
  letI : Field k := Ideal.Quotient.field P.asIdeal
  have hcop := (ArtinPrimitiveRoots.A1.coprime_six_of_not_mem_six P h6).1
  have hne1 := (ArtinPrimitiveRoots.A1.coprime_six_of_not_mem_six P h6).2
  have hdvd6 := ArtinPrimitiveRoots.A1.six_dvd_absNorm_sub_one D P h6
  have hζ6 : IsPrimitiveRoot (D.ζ12 ^ 2) 6 :=
    D.hζ12.pow_of_dvd (p := 2) (by decide) (by decide)
  have hprim := hζ6.toInteger_isPrimitiveRoot.idealQuotient_mk
    (I := P.asIdeal) hne1 hcop
  let u : kˣ := (hprim.isUnit (by decide)).unit
  have hprim_u : IsPrimitiveRoot u 6 := IsPrimitiveRoot.coe_units_iff.mp hprim
  have hru : IsUnit (ArtinPrimitiveRoots.A1.residue P x) :=
    isUnit_iff_ne_zero.mpr hx
  let r_u : kˣ := hru.unit
  have hr_pow : (ArtinPrimitiveRoots.A1.residue P x ^
      ((Ideal.absNorm P.asIdeal - 1) / 6)) ^ 6 = 1 := by
    rw [← pow_mul, mul_comm, Nat.mul_div_cancel' hdvd6]
    have h1 : ((r_u : k) ^ (Ideal.absNorm P.asIdeal - 1)) =
        (((r_u ^ (Ideal.absNorm P.asIdeal - 1) : kˣ) : k)) := by
      exact (Units.val_pow_eq_pow_val r_u _).symm
    have h2 : r_u ^ (Ideal.absNorm P.asIdeal - 1) = 1 := by
      have hcard : Nat.card kˣ = Ideal.absNorm P.asIdeal - 1 := by
        rw [Nat.card_units, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
      rw [← hcard]
      exact pow_card_eq_one'
    have hrequ : (r_u : k) = ArtinPrimitiveRoots.A1.residue P x := rfl
    rw [← hrequ, h1, h2, Units.val_one]
  obtain ⟨i, hi, heq⟩ := hprim.eq_pow_of_pow_eq_one hr_pow
  have hζ_pow : (hζ6.toInteger ^ i) ^ 6 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ6.toInteger_isPrimitiveRoot.pow_eq_one, one_pow]
  let ζ₀ : rootsOfUnity 6 (𝓞 F) := rootsOfUnity.mkOfPowEq (hζ6.toInteger ^ i) hζ_pow
  have h_exist : ∃ ζ : rootsOfUnity 6 (𝓞 F),
      Ideal.Quotient.mk P.asIdeal ((ζ : (𝓞 F)ˣ) : 𝓞 F) =
        ArtinPrimitiveRoots.A1.residue P x ^
          ((Ideal.absNorm P.asIdeal - 1) / 6) := by
    refine ⟨ζ₀, ?_⟩
    have hcoe : ((ζ₀ : (𝓞 F)ˣ) : 𝓞 F) = hζ6.toInteger ^ i :=
      rootsOfUnity.coe_mkOfPowEq hζ_pow
    rw [hcoe, map_pow]
    exact heq
  unfold ArtinPrimitiveRoots.A1.chiAlg
  rw [dif_pos h_exist]
  exact h_exist.choose_spec

theorem chi_cube_eq_quadSymbolAt
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (P : ArtinPrimitiveRoots.A1.FinPlace F) (h6 : (6 : 𝓞 F) ∉ P.asIdeal)
    (c : 𝓞 F) (hc : ArtinPrimitiveRoots.A1.residue P (algebraMap (𝓞 F) F c) ≠ 0) :
    ArtinPrimitiveRoots.A1.chi D P (algebraMap (𝓞 F) F c) ^ 3 =
      (quadSymbolAt P c : ℂ) := by
  classical
  haveI : P.asIdeal.IsMaximal := P.isMaximal
  let k := 𝓞 F ⧸ P.asIdeal
  letI : Field k := Ideal.Quotient.field P.asIdeal
  haveI : Finite k := Ring.HasFiniteQuotients.finiteQuotient P.ne_bot
  letI : Fintype k := Fintype.ofFinite k
  let q := Ideal.absNorm P.asIdeal
  have hres := rf_residue_algebraMap P c
  have hdvd6 := ArtinPrimitiveRoots.A1.six_dvd_absNorm_sub_one D P h6
  have hthird : ((q - 1) / 6) * 3 = q / 2 := by omega
  have h2not : (2 : 𝓞 F) ∉ P.asIdeal := by
    intro h2
    have hmul : (2 : 𝓞 F) * 3 ∈ P.asIdeal := Ideal.mul_mem_right _ _ h2
    apply h6
    rw [show (6 : 𝓞 F) = (2 : 𝓞 F) * 3 by norm_num]
    exact hmul
  have hmk_two : Ideal.Quotient.mk P.asIdeal (2 : 𝓞 F) = (2 : k) := by
    rw [show (2 : 𝓞 F) = 1 + 1 by norm_num, map_add, map_one]
    norm_num
  have h2q : (2 : k) ≠ 0 := by
    intro h
    apply h2not
    have hmk : Ideal.Quotient.mk P.asIdeal (2 : 𝓞 F) = 0 := by
      rw [hmk_two, h]
    exact Ideal.Quotient.eq_zero_iff_mem.mp hmk
  have hchar : ringChar k ≠ 2 := by
    intro hchar
    haveI : CharP k 2 := ringChar.eq_iff.mp hchar
    exact h2q (CharP.cast_eq_zero k 2)
  have hqcard : Fintype.card k = q := by
    dsimp [k, q]
    simp [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  let z : 𝓞 F :=
    ((ArtinPrimitiveRoots.A1.chiAlg P (algebraMap (𝓞 F) F c) : (𝓞 F)ˣ) : 𝓞 F)
  let β : 𝓞 F := (quadSymbolAt P c : ℤ)
  have hzres : Ideal.Quotient.mk P.asIdeal z =
      (Ideal.Quotient.mk P.asIdeal c) ^ ((q - 1) / 6) := by
    calc
      Ideal.Quotient.mk P.asIdeal z =
          ArtinPrimitiveRoots.A1.residue P (algebraMap (𝓞 F) F c) ^
            ((Ideal.absNorm P.asIdeal - 1) / 6) := by
        simpa [z] using rf_chiAlg_residue_eq_pow D P h6
          (algebraMap (𝓞 F) F c) hc
      _ = (Ideal.Quotient.mk P.asIdeal c) ^ ((q - 1) / 6) := by rw [hres]
  have hz3res : Ideal.Quotient.mk P.asIdeal (z ^ 3) =
      (Ideal.Quotient.mk P.asIdeal c) ^ (q / 2) := by
    calc
      Ideal.Quotient.mk P.asIdeal (z ^ 3) =
          (Ideal.Quotient.mk P.asIdeal z) ^ 3 := by simp
      _ = (Ideal.Quotient.mk P.asIdeal c) ^ (((q - 1) / 6) * 3) := by
        rw [hzres, ← pow_mul]
      _ = (Ideal.Quotient.mk P.asIdeal c) ^ (q / 2) := by rw [hthird]
  have hquad : ((quadSymbolAt P c : ℤ) : k) =
      (Ideal.Quotient.mk P.asIdeal c) ^ (q / 2) := by
    have hquad' : ((quadSymbolAt P c : ℤ) : k) =
        (Ideal.Quotient.mk P.asIdeal c) ^ (Fintype.card k / 2) := by
      simpa [quadSymbolAt] using
        (quadraticChar_eq_pow_of_char_ne_two' hchar
          (Ideal.Quotient.mk P.asIdeal c))
    simpa [hqcard] using hquad'
  have hβres : Ideal.Quotient.mk P.asIdeal β = (quadSymbolAt P c : k) := by
    simp [β]
  have hβsqInt : (quadSymbolAt P c : ℤ) ^ 2 = 1 := by
    have hcq : Ideal.Quotient.mk P.asIdeal c ≠ 0 := by
      rw [← hres]
      exact hc
    have h := quadraticChar_sq_one hcq
    simpa [quadSymbolAt] using h
  have hβsq : β ^ 2 = 1 := by
    change ((quadSymbolAt P c : ℤ) : 𝓞 F) ^ 2 = 1
    exact_mod_cast hβsqInt
  have hz6 : z ^ 6 = 1 := by
    dsimp [z]
    have h := congrArg (fun u : (𝓞 F)ˣ => (u : 𝓞 F))
      (ArtinPrimitiveRoots.A1.chiAlg P (algebraMap (𝓞 F) F c)).property
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using h
  have hz3sq : (z ^ 3) ^ 2 = 1 := by
    calc
      (z ^ 3) ^ 2 = z ^ 6 := by
        rw [← pow_mul]
      _ = 1 := hz6
  have hsquares : (z ^ 3) ^ 2 = β ^ 2 := hz3sq.trans hβsq.symm
  have hred : Ideal.Quotient.mk P.asIdeal (z ^ 3) =
      Ideal.Quotient.mk P.asIdeal β := by
    calc
      Ideal.Quotient.mk P.asIdeal (z ^ 3) =
          (Ideal.Quotient.mk P.asIdeal c) ^ (q / 2) := hz3res
      _ = (quadSymbolAt P c : k) := hquad.symm
      _ = Ideal.Quotient.mk P.asIdeal β := hβres.symm
  have hβq : Ideal.Quotient.mk P.asIdeal β ≠ 0 := by
    intro h
    have hone : (1 : k) = 0 := by
      calc
        1 = (Ideal.Quotient.mk P.asIdeal β) ^ 2 := by
          rw [← map_pow, hβsq]
          simp
        _ = 0 := by rw [h]; simp
    exact one_ne_zero hone
  have hnotneg : z ^ 3 ≠ -β := by
    intro hneg
    have heq : Ideal.Quotient.mk P.asIdeal β =
        -Ideal.Quotient.mk P.asIdeal β := by
      calc
        Ideal.Quotient.mk P.asIdeal β = Ideal.Quotient.mk P.asIdeal (z ^ 3) := hred.symm
        _ = Ideal.Quotient.mk P.asIdeal (-β) := by rw [hneg]
        _ = -Ideal.Quotient.mk P.asIdeal β := map_neg _ _
    have hmul : (2 : k) * Ideal.Quotient.mk P.asIdeal β = 0 := by
      calc
        (2 : k) * Ideal.Quotient.mk P.asIdeal β =
            Ideal.Quotient.mk P.asIdeal β + Ideal.Quotient.mk P.asIdeal β := by ring
        _ = 0 := by
          calc
            _ = -Ideal.Quotient.mk P.asIdeal β + Ideal.Quotient.mk P.asIdeal β := by
              nth_rw 1 [heq]
            _ = 0 := by abel
    exact (mul_ne_zero h2q hβq) hmul
  have hroot : z ^ 3 = β := by
    rcases eq_or_eq_neg_of_sq_eq_sq (z ^ 3) β hsquares with h | h
    · exact h
    · exact (hnotneg h).elim
  have hchiEval : ArtinPrimitiveRoots.A1.chi D P (algebraMap (𝓞 F) F c) =
      D.σ0 (algebraMap (𝓞 F) F z) := by
    simp [ArtinPrimitiveRoots.A1.chi, z, hc]
  calc
    ArtinPrimitiveRoots.A1.chi D P (algebraMap (𝓞 F) F c) ^ 3 =
        (D.σ0 (algebraMap (𝓞 F) F z)) ^ 3 := by rw [hchiEval]
    _ = D.σ0 (algebraMap (𝓞 F) F (z ^ 3)) := by simp
    _ = D.σ0 (algebraMap (𝓞 F) F β) := by rw [hroot]
    _ = (quadSymbolAt P c : ℂ) := by simp [β]

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
  classical
  have hfne : f ≠ ⊥ := hf.1.1
  have hne : r.h.1 ≠ ⊥ := r.h.2.1
  have hf0 : f ≠ 0 := by simpa [Ideal.zero_eq_bot] using hfne
  have hdiv : f ^ 2 ∣ r.h.1 := by
    rw [UniqueFactorizationMonoid.dvd_iff_emultiplicity_le (pow_ne_zero 2 hf0)]
    intro P hP
    rw [emultiplicity_pow hP]
    by_cases hPf : P ∣ f
    · let v : ArtinPrimitiveRoots.A1.FinPlace F := HeightOneSpectrum.ofPrime hP
      have hPh : P ∣ r.h.1 := by
        simpa [v] using hf.2.2.1 v hPf
      have hP2h : P ^ 2 ∣ r.h.1 := by
        simpa [v] using r.h_powerful v hPh
      have hmultH : (2 : ℕ∞) ≤ emultiplicity P r.h.1 :=
        (pow_dvd_iff_le_emultiplicity).mp hP2h
      have hmultF : emultiplicity P f ≤ 1 := by
        have hsq := (squarefree_iff_emultiplicity_le_one f).mp hf.2.1 P
        exact hsq.resolve_right hP.not_isUnit
      calc
        (2 : ℕ∞) * emultiplicity P f ≤ 2 * 1 := by gcongr
        _ = 2 := by norm_num
        _ ≤ emultiplicity P r.h.1 := hmultH
    · have hmultF : emultiplicity P f = 0 := by
        by_contra hne'
        have hpos : 0 < emultiplicity P f := pos_iff_ne_zero.mpr hne'
        exact hPf ((dvd_iff_emultiplicity_pos).mp hpos)
      simp [hmultF]
  have hNdiv : Ideal.absNorm (f ^ 2) ∣ Ideal.absNorm r.h.1 :=
    Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp hdiv)
  have hhPos : 0 < Ideal.absNorm r.h.1 :=
    Ideal.absNorm_pos_of_nonZeroDivisors
      ⟨r.h.1, mem_nonZeroDivisors_iff_ne_zero.mpr (by simpa [Ideal.zero_eq_bot] using hne)⟩
  have hNle : Ideal.absNorm (f ^ 2) ≤ Ideal.absNorm r.h.1 :=
    Nat.le_of_dvd hhPos hNdiv
  have hNpow : Ideal.absNorm (f ^ 2) = Ideal.absNorm f ^ 2 := by simp
  have hNle' : Ideal.absNorm f ^ 2 ≤ Ideal.absNorm r.h.1 := by
    rw [← hNpow]
    exact hNle
  exact_mod_cast hNle'

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
