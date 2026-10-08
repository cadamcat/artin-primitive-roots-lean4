import ArtinPrimitiveRoots.A1.Residue
import ArtinPrimitiveRoots.A1.Proofs.A1_HILBERT.Core
import ArtinPrimitiveRoots.A1.Proofs.A1_HILBERT.Nondegenerate
import ArtinPrimitiveRoots.A1.Proofs.A1_HILBERT.Laws
import ArtinPrimitiveRoots.A1.Proofs.A1_HILBERT.Steinberg
import ArtinPrimitiveRoots.A1.Proofs.A1_HILBERT.Semilinear
import ArtinPrimitiveRoots.A1.Proofs.A1_HILBERT.CompletionComparison
import ArtinPrimitiveRoots.A1.Proofs.A1_HILBERT.GeneratedExtension
import ArtinPrimitiveRoots.A1.Proofs.A1_HILBERT.ArtinLocalization
import ArtinPrimitiveRoots.A1.Proofs.A1_HILBERT.GlobalRootComparison
import ArtinPrimitiveRoots.A1.Proofs.A1_HILBERT.Reciprocity
import ArtinPrimitiveRoots.A1.Proofs.A1_HILBERT.TameReduction
import ArtinPrimitiveRoots.A1.Proofs.A1_HILBERT.TameFrobenius
import ArtinPrimitiveRoots.A1.Proofs.A1_HILBERT.TameLocalSymbol
import ArtinPrimitiveRoots.A1.Proofs.A1_GENERATORS.Generator
import ArtinPrimitiveRoots.A1.Proofs.A1_KUMMER.ResidueCompatibility

/-!
# A1 interface, §3: Hilbert symbols, H_S, B, allowed generators

Frozen interface of part A1 (paper §§2, 2a, 3, App. 10). Each `sorry` is owned by a package of
`research/design/A1-DESIGN.md` §3, named in its docstring. Design: `research/design/A1-Interface.lean`
(Opus A1 sub-agent, 2026-10-07).
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

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
  classical
  letI : CommGroup S.V := QuotientGroup.Quotient.commGroup _
  obtain ⟨a₀, ha₀⟩ :=
    ArtinPrimitiveRoots.Proofs.A1Generators.exists_generator_of_pid S I hI
  let q₀ : S.V := (QuotientGroup.mk (S.diagU a₀) : S.V)
  have hsup : q₀ ∈ S.E ⊔ Bd.B := by
    rw [Bd.compl.sup_eq_top]
    exact Subgroup.mem_top q₀
  obtain ⟨e, he, b, hb, hmul⟩ :=
    (Subgroup.mem_sup (s := S.E) (t := Bd.B) (x := q₀)).mp hsup
  change e ∈ S.E at he
  obtain ⟨ε, hε, hεmap⟩ := Subgroup.mem_map.mp he
  let εu : S.US := ⟨ε, hε⟩
  have hεmap' : (QuotientGroup.mk (S.diagU (εu : Fˣ)) : S.V) = e := by
    simpa using hεmap
  let a : Fˣ := ((εu⁻¹ : S.US) : Fˣ) * a₀
  have hgen : S.IsGen (a : F) I := by
    exact ArtinPrimitiveRoots.Proofs.A1Generators.isGen_mul_sUnit S εu⁻¹ a₀ ha₀
  have hqa : (QuotientGroup.mk (S.diagU a) : S.V) = b := by
    change (QuotientGroup.mk
      (S.diagU (((εu⁻¹ : S.US) : Fˣ) * a₀)) : S.V) = b
    calc
      QuotientGroup.mk
          (S.diagU (((εu⁻¹ : S.US) : Fˣ) * a₀)) =
        QuotientGroup.mk (S.diagU ((εu⁻¹ : S.US) : Fˣ)) * q₀ := by simp [q₀]
      _ = (QuotientGroup.mk (S.diagU (εu : Fˣ)))⁻¹ * q₀ := by simp
      _ = e⁻¹ * q₀ := by rw [hεmap']
      _ = b := by rw [← hmul]; group
  refine ⟨a, hgen, ?_⟩
  change (QuotientGroup.mk (S.diagU a) : S.V) ∈ Bd.B
  rw [hqa]
  exact hb

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
private lemma a1gp_count_prime_self (P : FinPlace F) :
    FractionalIdeal.count F P
      (P.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 1 := by
  simpa using (FractionalIdeal.count_maximal (K := F) P P)

private lemma a1gp_count_prime_other (P P' : FinPlace F) (hne : P ≠ P') :
    FractionalIdeal.count F P
      (P'.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0 := by
  exact FractionalIdeal.count_maximal_coprime (K := F) P hne.symm

private lemma a1gp_hilb_eq_one_of_coe_eq_one (H : HilbertData F) (v : FinPlace F)
    (a b : Fˣ) (h : ((H.hilb v (toLoc v a) (toLoc v b) : Fˣ) : F) = 1) :
    H.hilb v (toLoc v a) (toLoc v b) = 1 := by
  apply Subtype.ext
  exact Units.ext h

private def a1gp_chiAlgUnit (P : FinPlace F) (x : F) : Fˣ :=
  Units.map (algebraMap (𝓞 F) F).toMonoidHom
    ((chiAlg P x : rootsOfUnity 6 (𝓞 F)) : (𝓞 F)ˣ)

private lemma a1gp_count_ideal_eq_factor_count (I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    (v : FinPlace F) :
    FractionalIdeal.count F v (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
      Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors I) := by
  rw [FractionalIdeal.count_coe F v hI,
    Ideal.count_associates_factors_eq hI v.isPrime v.ne_bot]

private def a1gp_factorPlace (I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    (P : {Q : Ideal (𝓞 F) // Q ∈ UniqueFactorizationMonoid.normalizedFactors I}) : FinPlace F :=
  ⟨P.1, (Ideal.mem_normalizedFactors_iff hI).mp P.2 |>.1,
    UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors P.2⟩

theorem sextic_reciprocity (D : FieldData F) (S : SData F CE condη) (H : HilbertData F)
    (Bd : BData S H) (P P' : FinPlace F) (hP : P ∉ S.Sf) (hP' : P' ∉ S.Sf) (hne : P ≠ P')
    (p p' : Fˣ) (hp : S.IsGen (p : F) P.asIdeal ∧ Bd.Allowed p)
    (hp' : S.IsGen (p' : F) P'.asIdeal ∧ Bd.Allowed p') :
    chi D P (p' : F) = chi D P' (p : F) := by
  classical
  have hcountP : FractionalIdeal.count F P
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (p : F)) = 1 := by
    calc
      _ = FractionalIdeal.count F P
          (P.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := hp.1.2.2 P hP
      _ = 1 := a1gp_count_prime_self P
  have hcountP' : FractionalIdeal.count F P'
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (p' : F)) = 1 := by
    calc
      _ = FractionalIdeal.count F P'
          (P'.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := hp'.1.2.2 P' hP'
      _ = 1 := a1gp_count_prime_self P'
  have hcountpAtP' : FractionalIdeal.count F P'
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (p : F)) = 0 := by
    calc
      _ = FractionalIdeal.count F P' (P.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :=
        hp.1.2.2 P' hP'
      _ = 0 := a1gp_count_prime_other P' P hne.symm
  have hcountp'AtP : FractionalIdeal.count F P
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (p' : F)) = 0 := by
    calc
      _ = FractionalIdeal.count F P (P'.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :=
        hp'.1.2.2 P hP
      _ = 0 := a1gp_count_prime_other P P' hne
  have hresP : residue P (p' : F) ≠ 0 := by
    apply (ArtinPrimitiveRoots.A1.KummerProofs.residue_ne_zero_iff_ord_zero P _).2
    exact ⟨hcountp'AtP, p'.ne_zero⟩
  have hresP' : residue P' (p : F) ≠ 0 := by
    apply (ArtinPrimitiveRoots.A1.KummerProofs.residue_ne_zero_iff_ord_zero P' _).2
    exact ⟨hcountpAtP', p.ne_zero⟩
  have h6P : (6 : 𝓞 F) ∉ P.asIdeal := by
    intro h
    exact hP (S.over6 P h)
  have h6P' : (6 : 𝓞 F) ∉ P'.asIdeal := by
    intro h
    exact hP' (S.over6 P' h)
  let f : FinPlace F → rootsOfUnity 6 F := fun v => H.hilb v (toLoc v p) (toLoc v p')
  have houtside (v : FinPlace F) (hvS : v ∉ S.Sf) (hvP : v ≠ P) (hvP' : v ≠ P') :
      f v = 1 := by
    have h6v : (6 : 𝓞 F) ∉ v.asIdeal := by
      intro h
      exact hvS (S.over6 v h)
    have hcountv : FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (p : F)) = 0 := by
      calc
        _ = FractionalIdeal.count F v (P.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :=
          hp.1.2.2 v hvS
        _ = 0 := a1gp_count_prime_other v P hvP
    have hcountv' : FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (p' : F)) = 0 := by
      calc
        _ = FractionalIdeal.count F v (P'.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :=
          hp'.1.2.2 v hvS
        _ = 0 := a1gp_count_prime_other v P' hvP'
    have hresv : residue v (p' : F) ≠ 0 := by
      apply (ArtinPrimitiveRoots.A1.KummerProofs.residue_ne_zero_iff_ord_zero v _).2
      exact ⟨hcountv', p'.ne_zero⟩
    have htame := H.tame v h6v p' p hresv
    rw [hcountv, zpow_zero] at htame
    have hback : H.hilb v (toLoc v p') (toLoc v p) = 1 :=
      a1gp_hilb_eq_one_of_coe_eq_one H v p' p (by simpa using htame)
    have hskew := H.skew v (toLoc v p) (toLoc v p')
    rw [hback, mul_one] at hskew
    change H.hilb v (toLoc v p) (toLoc v p') = 1
    exact hskew
  have hsupport : Function.mulSupport f ⊆ (S.Sf ∪ {P} ∪ {P'} : Finset (FinPlace F)) := by
    intro v hv
    by_contra hnot
    have hvnot : v ∉ S.Sf ∧ v ≠ P ∧ v ≠ P' := by
      refine ⟨?_, ?_, ?_⟩
      · intro hvS
        exact hnot (by simp [hvS])
      · intro heq
        subst v
        exact hnot (by simp)
      · intro heq
        subst v
        exact hnot (by simp)
    change f v ≠ 1 at hv
    exact hv (houtside v hvnot.1 hvnot.2.1 hvnot.2.2)
  have hdisjInner : Disjoint S.Sf {P} := Finset.disjoint_singleton_right.mpr hP
  have hP'not : P' ∉ S.Sf ∪ {P} := by
    simp only [Finset.mem_union, Finset.mem_singleton, not_or]
    exact ⟨hP', hne.symm⟩
  have hdisjOuter : Disjoint (S.Sf ∪ {P}) {P'} :=
    Finset.disjoint_singleton_right.mpr hP'not
  have hfiniteprod : (∏ᶠ v, f v) = (∏ v ∈ S.Sf, f v) * f P * f P' := by
    rw [finprod_eq_prod_of_mulSupport_subset (s := S.Sf ∪ {P} ∪ {P'}) f hsupport,
      Finset.prod_union hdisjOuter, Finset.prod_union hdisjInner,
      Finset.prod_singleton, Finset.prod_singleton]
  have hcomp (v : S.Sf) :
      S.compU v (S.diagU p) = toLoc v.1 p ∧ S.compU v (S.diagU p') = toLoc v.1 p' := by
    constructor <;> apply Units.ext <;> rfl
  have hsfAttach : (∏ v : S.Sf, H.hilb v.1 (toLoc v.1 p) (toLoc v.1 p')) = 1 := by
    calc
      _ = S.HS H (S.diagU p) (S.diagU p') := by
        unfold SData.HS
        refine Finset.prod_congr rfl ?_
        intro v hv
        rw [(hcomp v).1, (hcomp v).2]
      _ = 1 := Bd.isotropic (S.diagU p) (S.diagU p') hp.2 hp'.2
  have hsf : (∏ v ∈ S.Sf, f v) = 1 := by
    rw [← Finset.prod_attach S.Sf (fun v => f v)]
    simpa [f] using hsfAttach
  have hglobal : (∏ᶠ v, f v) = 1 := H.product_formula p p' |>.2
  have hcross : f P * f P' = 1 := by
    rw [hfiniteprod, hsf] at hglobal
    simpa using hglobal
  have hunitP : (H.hilb P (toLoc P p') (toLoc P p) : Fˣ) = a1gp_chiAlgUnit P (p' : F) := by
    have htame := H.tame P h6P p' p hresP
    rw [hcountP, zpow_one] at htame
    apply Units.ext
    simpa [a1gp_chiAlgUnit] using htame
  have hunitP' : (H.hilb P' (toLoc P' p) (toLoc P' p') : Fˣ) =
      a1gp_chiAlgUnit P' (p : F) := by
    have htame := H.tame P' h6P' p p' hresP'
    rw [hcountP', zpow_one] at htame
    apply Units.ext
    simpa [a1gp_chiAlgUnit] using htame
  have hchiP : chi D P (p' : F) =
      D.σ0 (((a1gp_chiAlgUnit P (p' : F) : Fˣ) : F)) := by
    simp [chi, hresP, a1gp_chiAlgUnit]
  have hchiP' : chi D P' (p : F) =
      D.σ0 (((a1gp_chiAlgUnit P' (p : F) : Fˣ) : F)) := by
    simp [chi, hresP', a1gp_chiAlgUnit]
  have hchiP_ne : chi D P (p' : F) ≠ 0 := by
    rw [chi, if_neg hresP]
    intro hzero
    have hzeroF : algebraMap (𝓞 F) F
        (((chiAlg P (p' : F) : rootsOfUnity 6 (𝓞 F)) : (𝓞 F)ˣ) : 𝓞 F) = 0 :=
      (RingHom.injective D.σ0) (by simpa using hzero)
    have hzeroO : (((chiAlg P (p' : F) : rootsOfUnity 6 (𝓞 F)) : (𝓞 F)ˣ) : 𝓞 F) = 0 :=
      (IsFractionRing.injective (𝓞 F) F) hzeroF
    exact Units.ne_zero _ (congrArg (fun z : 𝓞 F => z) hzeroO)
  have hskewP := H.skew P (toLoc P p) (toLoc P p')
  have hskewSigmaP :
      D.σ0 (((f P : Fˣ) : F)) * D.σ0 (((H.hilb P (toLoc P p') (toLoc P p) : Fˣ) : F)) = 1 := by
    have hval := congrArg (fun z : rootsOfUnity 6 F => ((z : Fˣ) : F)) hskewP
    have hval' : ((f P : Fˣ) : F) *
        ((H.hilb P (toLoc P p') (toLoc P p) : Fˣ) : F) = 1 := by
      simpa [f] using hval
    simpa [map_mul] using congrArg D.σ0 hval'
  have hcrossUnit : (f P : Fˣ) * (f P' : Fˣ) = 1 := by
    have hval := congrArg (fun z : rootsOfUnity 6 F => (z : Fˣ)) hcross
    simpa [f] using hval
  have hcrossSigma : D.σ0 (((f P : Fˣ) : F)) * D.σ0 (((f P' : Fˣ) : F)) = 1 := by
    have hval := congrArg (fun z : Fˣ => D.σ0 (z : F)) hcrossUnit
    simpa [map_mul] using hval
  have hchiP_inv : D.σ0 (((f P : Fˣ) : F)) = (chi D P (p' : F))⁻¹ := by
    rw [hunitP, ← hchiP] at hskewSigmaP
    calc
      D.σ0 (((f P : Fˣ) : F)) =
          D.σ0 (((f P : Fˣ) : F)) *
            (chi D P (p' : F) * (chi D P (p' : F))⁻¹) := by
              rw [mul_inv_cancel₀ hchiP_ne, mul_one]
      _ = (D.σ0 (((f P : Fˣ) : F)) * chi D P (p' : F)) *
          (chi D P (p' : F))⁻¹ := by rw [mul_assoc]
      _ = (chi D P (p' : F))⁻¹ := by rw [hskewSigmaP, one_mul]
  have hchiP'tame : chi D P' (p : F) =
      D.σ0 (((H.hilb P' (toLoc P' p) (toLoc P' p') : Fˣ) : F)) := by
    rw [hchiP', ← hunitP']
  have hchiEq : (chi D P (p' : F))⁻¹ * chi D P' (p : F) = 1 := by
    have hcrossSigma' := hcrossSigma
    rw [hchiP_inv, ← hchiP'tame] at hcrossSigma'
    exact hcrossSigma'
  calc
    chi D P (p' : F) = chi D P (p' : F) *
        ((chi D P (p' : F))⁻¹ * chi D P' (p : F)) := by rw [hchiEq, mul_one]
    _ = (chi D P (p' : F) * (chi D P (p' : F))⁻¹) * chi D P' (p : F) := by
        rw [mul_assoc]
    _ = chi D P' (p : F) := by rw [mul_inv_cancel₀ hchiP_ne, one_mul]

/-- eq:unit-symbol (02:279–283): `χ_I(ε) = H_S(ε,a)^{-1}` (read through `σ0`). -/
theorem unit_symbol (D : FieldData F) (S : SData F CE condη) (H : HilbertData F)
    (Bd : BData S H) (I : Ideal (𝓞 F)) (hI : S.IsExterior I) (a ε : Fˣ)
    (ha : S.IsGen (a : F) I ∧ Bd.Allowed a) (hε : ε ∈ S.US) :
    chiIdealPow D I (ε : F) 1 = D.σ0 (((S.HS H (S.diagU ε) (S.diagU a))⁻¹ : Fˣ) : F) := by
  classical
  let εu : S.US := ⟨ε, hε⟩
  let factorSet := (UniqueFactorizationMonoid.normalizedFactors I).toFinset
  let factorEmb : {P : Ideal (𝓞 F) // P ∈ factorSet} ↪ FinPlace F :=
    ⟨fun P => a1gp_factorPlace I hI.1 ⟨P.1, Multiset.mem_toFinset.mp P.2⟩,
      by
        intro P Q h
        apply Subtype.ext
        exact congrArg (fun v : FinPlace F => v.asIdeal) h⟩
  let factorPlaces : Finset (FinPlace F) := factorSet.attach.map factorEmb
  have hfactorDisjoint (v : FinPlace F) (hvS : v ∈ S.Sf) : v ∈ factorPlaces → False := by
    intro hv
    rcases Finset.mem_map.mp hv with ⟨P, hP, hPv⟩
    have hfac : P.1 ∈ UniqueFactorizationMonoid.normalizedFactors I :=
      Multiset.mem_toFinset.mp P.2
    have hle : I ≤ P.1 := (Ideal.mem_normalizedFactors_iff hI.1).mp hfac |>.2
    have hplace : P.1 = v.asIdeal := by
      have h := congrArg (fun w : FinPlace F => w.asIdeal) hPv
      exact h
    exact hI.2 v hvS (hplace ▸ hle)
  have hdisj : Disjoint S.Sf factorPlaces := by
    apply Finset.disjoint_left.mpr
    intro v hvS hvT
    exact hfactorDisjoint v hvS hvT
  have hcountε (v : FinPlace F) (hvS : v ∉ S.Sf) :
      FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (ε : F)) = 0 := by
    have hval : v.valuation F (ε : F) = 1 := εu.property v hvS
    rw [ArtinPrimitiveRoots.A2.qs_nq0_count_spanSingleton_eq_neg_log_valuation
      v (ε : F) ε.ne_zero, hval]
    simp
  have hresε (v : FinPlace F) (hvS : v ∉ S.Sf) : residue v (ε : F) ≠ 0 := by
    apply (ArtinPrimitiveRoots.A1.KummerProofs.residue_ne_zero_iff_ord_zero v _).2
    exact ⟨hcountε v hvS, ε.ne_zero⟩
  let f : FinPlace F → rootsOfUnity 6 F := fun v => H.hilb v (toLoc v ε) (toLoc v a)
  have houtside (v : FinPlace F) (hvS : v ∉ S.Sf) (hvT : v ∉ factorPlaces) : f v = 1 := by
    have hnotfac : v.asIdeal ∉ UniqueFactorizationMonoid.normalizedFactors I := by
      intro hfac
      apply hvT
      let P : {P : Ideal (𝓞 F) // P ∈ factorSet} :=
        ⟨v.asIdeal, Multiset.mem_toFinset.mpr hfac⟩
      apply Finset.mem_map.mpr
      refine ⟨P, Finset.mem_attach _ P, ?_⟩
      apply HeightOneSpectrum.ext
      rfl
    have hcountI := a1gp_count_ideal_eq_factor_count I hI.1 v
    have hcountZero : FractionalIdeal.count F v
        (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0 := by
      rw [hcountI]
      exact_mod_cast (Multiset.count_eq_zero.mpr hnotfac)
    have hcounta := ha.1.2.2 v hvS
    have h6v : (6 : 𝓞 F) ∉ v.asIdeal := by
      intro hv6
      exact hvS (S.over6 v hv6)
    have htame := H.tame v h6v ε a (hresε v hvS)
    rw [hcounta, hcountZero, zpow_zero] at htame
    have hback : H.hilb v (toLoc v ε) (toLoc v a) = 1 :=
      a1gp_hilb_eq_one_of_coe_eq_one H v ε a (by simpa using htame)
    simpa [f] using hback
  have hsupport : Function.mulSupport f ⊆ (S.Sf ∪ factorPlaces : Finset (FinPlace F)) := by
    intro v hv
    by_contra hnot
    have hvS : v ∉ S.Sf := by
      intro h
      exact hnot (by simp [h])
    have hvT : v ∉ factorPlaces := by
      intro h
      exact hnot (by simp [h])
    change f v ≠ 1 at hv
    exact hv (houtside v hvS hvT)
  have hcomp (v : S.Sf) :
      S.compU v (S.diagU ε) = toLoc v.1 ε ∧ S.compU v (S.diagU a) = toLoc v.1 a := by
    constructor <;> apply Units.ext <;> rfl
  have hsf : (∏ v : S.Sf, f v.1) = S.HS H (S.diagU ε) (S.diagU a) := by
    unfold SData.HS
    refine Finset.prod_congr rfl ?_
    intro v hv
    rw [(hcomp v).1, (hcomp v).2]
  have hsfBase : (∏ v ∈ S.Sf, f v) = S.HS H (S.diagU ε) (S.diagU a) := by
    rw [← Finset.prod_attach S.Sf (fun v => f v)]
    exact hsf
  have hfiniteprod : (∏ᶠ v, f v) =
      (∏ v ∈ S.Sf, f v) * ∏ v ∈ factorPlaces, f v := by
    rw [finprod_eq_prod_of_mulSupport_subset f hsupport, Finset.prod_union hdisj]
  have hglobal : (∏ᶠ v, f v) = 1 := H.product_formula ε a |>.2
  have hcross : S.HS H (S.diagU ε) (S.diagU a) *
      (∏ v ∈ factorPlaces, f v) = 1 := by
    rw [hfiniteprod, hsfBase] at hglobal
    simpa using hglobal
  have hlocal (v : FinPlace F) (hvT : v ∈ factorPlaces) :
      D.σ0 (((f v : Fˣ) : F)) =
        chi D v (ε : F) ^ (UniqueFactorizationMonoid.normalizedFactors I).count v.asIdeal := by
    have hvS : v ∉ S.Sf := by
      intro h
      exact hfactorDisjoint v h hvT
    have h6v : (6 : 𝓞 F) ∉ v.asIdeal := by
      intro hv6
      exact hvS (S.over6 v hv6)
    have hcounta := ha.1.2.2 v hvS
    have hcountI := a1gp_count_ideal_eq_factor_count I hI.1 v
    have htame := H.tame v h6v ε a (hresε v hvS)
    rw [hcounta, hcountI, zpow_natCast] at htame
    have hσ := congrArg D.σ0 htame
    simpa [f, chi, hresε v hvS, a1gp_chiAlgUnit, map_pow] using hσ
  have hlocalProd :
      (∏ v ∈ factorPlaces, D.σ0 (((f v : Fˣ) : F))) =
        ∏ v ∈ factorPlaces,
          chi D v (ε : F) ^ (UniqueFactorizationMonoid.normalizedFactors I).count v.asIdeal := by
    apply Finset.prod_congr rfl
    intro v hv
    exact hlocal v hv
  have hcrossUnit :
      ((S.HS H (S.diagU ε) (S.diagU a) : Fˣ) * ∏ v ∈ factorPlaces, (f v : Fˣ)) = 1 := by
    have h := congrArg (fun z : rootsOfUnity 6 F => (z : Fˣ)) hcross
    simpa using h
  have hcrossSigma :
      D.σ0 ((S.HS H (S.diagU ε) (S.diagU a) : Fˣ) : F) *
        ∏ v ∈ factorPlaces, D.σ0 (((f v : Fˣ) : F)) = 1 := by
    have h := congrArg (fun z : Fˣ => D.σ0 (z : F)) hcrossUnit
    simpa [map_mul] using h
  have hcrossSigma' :
      D.σ0 ((S.HS H (S.diagU ε) (S.diagU a) : Fˣ) : F) *
        ∏ v ∈ factorPlaces,
          chi D v (ε : F) ^ (UniqueFactorizationMonoid.normalizedFactors I).count v.asIdeal = 1 := by
    rw [hlocalProd] at hcrossSigma
    exact hcrossSigma
  have hchiProd :
      chiIdealPow D I (ε : F) 1 =
        ∏ v ∈ factorPlaces,
          chi D v (ε : F) ^ (UniqueFactorizationMonoid.normalizedFactors I).count v.asIdeal := by
    unfold chiIdealPow
    rw [Finset.prod_multiset_map_count]
    rw [← Finset.prod_attach factorSet]
    simp only [factorPlaces, Finset.prod_map]
    apply Finset.prod_congr rfl
    intro P hP
    have hfac : P.1 ∈ UniqueFactorizationMonoid.normalizedFactors I :=
      Multiset.mem_toFinset.mp P.2
    have hprimePair := (Ideal.mem_normalizedFactors_iff hI.1).mp hfac
    let v : FinPlace F := a1gp_factorPlace I hI.1 ⟨P.1, hfac⟩
    have hvS : v ∉ S.Sf := by
      intro hv
      apply hfactorDisjoint v hv
      apply Finset.mem_map.mpr
      exact ⟨P, Finset.mem_attach _ P, rfl⟩
    have hres : residue v (ε : F) ≠ 0 := hresε v hvS
    have hprimeNonzero : P.1 ≠ ⊥ :=
      UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors hfac
    have hrootEq :
        (⟨P.1, hprimePair.1, hprimeNonzero⟩ : FinPlace F) = factorEmb P := by
      apply HeightOneSpectrum.ext
      rfl
    have hfacIdeal : (factorEmb P).asIdeal = P.1 := by
      exact (congrArg (fun w : FinPlace F => w.asIdeal) hrootEq).symm
    have hcountEq :
        (UniqueFactorizationMonoid.normalizedFactors I).count P.1 =
          (UniqueFactorizationMonoid.normalizedFactors I).count (factorEmb P).asIdeal := by
      rw [hfacIdeal]
    have hfactorMember : factorEmb P ∈ factorPlaces := by
      apply Finset.mem_map.mpr
      exact ⟨P, Finset.mem_attach _ P, rfl⟩
    have hfactorOutsideS : factorEmb P ∉ S.Sf := by
      intro hv
      exact hfactorDisjoint (factorEmb P) hv hfactorMember
    have hresFactor : residue (factorEmb P) (ε : F) ≠ 0 :=
      hresε (factorEmb P) hfactorOutsideS
    rw [dif_pos ⟨hprimePair.1, hprimeNonzero⟩]
    rw [hcountEq]
    have hresRoot :
        residue (⟨P.1, hprimePair.1, hprimeNonzero⟩ : FinPlace F) (ε : F) ≠ 0 := by
      rw [hrootEq]
      exact hresFactor
    have hchiPow :
        chiPow D ⟨P.1, hprimePair.1, hprimeNonzero⟩ (ε : F) 1 =
          chi D ⟨P.1, hprimePair.1, hprimeNonzero⟩ (ε : F) := by
      simp [chiPow, hresRoot]
    rw [hchiPow, hrootEq]
  have hglobalComplex :
      D.σ0 ((S.HS H (S.diagU ε) (S.diagU a) : Fˣ) : F) *
        chiIdealPow D I (ε : F) 1 = 1 := by
    rw [hchiProd]
    exact hcrossSigma'
  have hHSne : D.σ0 ((S.HS H (S.diagU ε) (S.diagU a) : Fˣ) : F) ≠ 0 := by
    intro hzero
    have hzeroF : ((S.HS H (S.diagU ε) (S.diagU a) : Fˣ) : F) = 0 :=
      (RingHom.injective D.σ0) (by simpa using hzero)
    exact Units.ne_zero _ hzeroF
  have hHSinv :
      D.σ0 (((S.HS H (S.diagU ε) (S.diagU a))⁻¹ : Fˣ) : F) =
        (D.σ0 ((S.HS H (S.diagU ε) (S.diagU a) : Fˣ) : F))⁻¹ := by
    simp [Units.val_inv_eq_inv_val, map_inv₀]
  calc
    chiIdealPow D I (ε : F) 1 =
        (D.σ0 ((S.HS H (S.diagU ε) (S.diagU a) : Fˣ) : F))⁻¹ := by
          let b := D.σ0 ((S.HS H (S.diagU ε) (S.diagU a) : Fˣ) : F)
          have hcancel : (1 : ℂ) = b⁻¹ * b := (inv_mul_cancel₀ hHSne).symm
          calc
            _ = b⁻¹ * (b * chiIdealPow D I (ε : F) 1) := by
              calc
                _ = 1 * chiIdealPow D I (ε : F) 1 := by simp
                _ = (b⁻¹ * b) * chiIdealPow D I (ε : F) 1 := by rw [hcancel]
                _ = b⁻¹ * (b * chiIdealPow D I (ε : F) 1) := by exact mul_assoc _ _ _
            _ = b⁻¹ := by
              have h := congrArg
                (fun z : ℂ => b⁻¹ * z)
                hglobalComplex
              simpa using h
            _ = (D.σ0 ((S.HS H (S.diagU ε) (S.diagU a) : Fˣ) : F))⁻¹ := rfl
    _ = D.σ0 (((S.HS H (S.diagU ε) (S.diagU a))⁻¹ : Fˣ) : F) := hHSinv.symm


end ArtinPrimitiveRoots.A1
