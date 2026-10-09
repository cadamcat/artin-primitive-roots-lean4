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
import ArtinPrimitiveRoots.A1.Proofs.A1_HILBERT.TameResidueDictionary
import ArtinPrimitiveRoots.A1.Proofs.A1_HILBERT.TameGlobalUnit
import ArtinPrimitiveRoots.A1.Proofs.A1_HILBERT.TameValuation
import ArtinPrimitiveRoots.A1.Proofs.A1_HILBERT.TameRootData
import ArtinPrimitiveRoots.A1.Proofs.A1_HILBERT.Tame
import ArtinPrimitiveRoots.A1.Proofs.A1_LATTICE.UnitCompactCore
import ArtinPrimitiveRoots.A1.Proofs.A1_GENERATORS.Generator
import ArtinPrimitiveRoots.A1.Proofs.A1_KUMMER.ResidueCompatibility
import ArtinPrimitiveRoots.A1.Proofs.«A1-UNIQUE».Global
import ArtinPrimitiveRoots.A1.Proofs.A1_BDATA.LocalIndex
import ArtinPrimitiveRoots.A1.Proofs.A1_BDATA.NativeLocalIndex
import ArtinPrimitiveRoots.A1.Proofs.A1_BDATA.CanonicalTopology
import ArtinPrimitiveRoots.A1.Proofs.A1_BDATA.ResidueComparison
import ArtinPrimitiveRoots.A1.Proofs.A1_BDATA.DegreeComparison
import ArtinPrimitiveRoots.A1.Proofs.A1_BDATA.DegreeSum
import ArtinPrimitiveRoots.A1.Proofs.A1_BDATA.LocalCardinality
import ArtinPrimitiveRoots.A1.Proofs.A1_BDATA.GlobalCardinality
import ArtinPrimitiveRoots.A1.Proofs.A1_BDATA.SUnitCardinality
import ArtinPrimitiveRoots.A1.Proofs.A1_BDATA.SUnitInjection
import ArtinPrimitiveRoots.A1.Proofs.A1_BDATA.Symplectic
import ArtinPrimitiveRoots.A1.Proofs.A1_BDATA.PrimeComplement

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
  let h1 := ArtinPrimitiveRoots.Proofs.a1_hilbert_sol.hilbert_mul_norm_criterion_H1 D
  let h2 := ArtinPrimitiveRoots.Proofs.a1_hilbert_sol.hilbert_steinberg_skew_H2 D
  exact ⟨{
    hilb := ArtinPrimitiveRoots.Proofs.a1_hilbert_sol.hilb D
    mul_left := h1.1
    mul_right := h1.2
    skew := h2.1
    sixth_power := h2.2.1
    steinberg := h2.2.2
    nondeg := ArtinPrimitiveRoots.Proofs.a1_hilbert_sol.hilbert_nondegenerate_H3 D
    product_formula := ArtinPrimitiveRoots.Proofs.a1_hilbert_sol.hilbert_global_reciprocity_H5 D
    tame := ArtinPrimitiveRoots.Proofs.a1_hilbert_sol.hilbert_tame_formula_H4 D }⟩

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

private theorem a1_bdata_sol_HSQuot_exists (D : FieldData F) (S : SData F CE condη)
    (H : HilbertData F) :
    ∃ β : S.V →* (S.V →* rootsOfUnity 6 F),
      (∀ x y : S.FSˣ, β (QuotientGroup.mk x) (QuotientGroup.mk y) = S.HS H x y) ∧
      (∀ q : S.V, β q q = 1) ∧
      (∀ q : S.V, (∀ r : S.V, β q r = 1) → q = 1) := by
  classical
  have hr6 (v : FinPlace F) (a b : (v.adicCompletion F)ˣ)
      (hb : ∃ c : (v.adicCompletion F)ˣ, b = c ^ 6) : H.hilb v a b = 1 := by
    simpa [H.sixth_power v b a hb] using H.skew v a b
  have hr1 (v : FinPlace F) (a : (v.adicCompletion F)ˣ) : H.hilb v a 1 = 1 :=
    hr6 v a 1 ⟨1, by simp⟩
  let f : S.FSˣ →* (S.FSˣ →* rootsOfUnity 6 F) :=
    MonoidHom.mk' (fun x => MonoidHom.mk' (fun y => S.HS H x y) (by
      intro y z
      simp only [SData.HS, map_mul, H.mul_right, Finset.prod_mul_distrib])) (by
      intro x z
      ext y
      simp only [MonoidHom.mk'_apply, MonoidHom.mul_apply, SData.HS, map_mul,
        H.mul_left, Finset.prod_mul_distrib])
  let P := (powMonoidHom 6 : S.FSˣ →* S.FSˣ).range
  have hright (x : S.FSˣ) : P ≤ (f x).ker := by
    rintro y ⟨z, rfl⟩
    change S.HS H x (z ^ 6) = 1
    apply Finset.prod_eq_one
    intro v hv
    exact hr6 v.1 _ _ ⟨S.compU v z, by simp⟩
  let g : S.FSˣ →* (S.V →* rootsOfUnity 6 F) :=
    MonoidHom.mk' (fun x => QuotientGroup.lift P (f x) (hright x)) (by
      intro x z
      apply MonoidHom.ext
      intro q
      induction q using QuotientGroup.induction_on with
      | H y =>
        change f (x * z) y = f x y * f z y
        rw [map_mul, MonoidHom.mul_apply])
  have hleft : P ≤ g.ker := by
    rintro x ⟨z, rfl⟩
    apply MonoidHom.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | H y =>
      change S.HS H (z ^ 6) y = 1
      apply Finset.prod_eq_one
      intro v hv
      exact H.sixth_power v.1 _ _ ⟨S.compU v z, by simp⟩
  let β : S.V →* (S.V →* rootsOfUnity 6 F) := QuotientGroup.lift P g hleft
  have hβ (x y : S.FSˣ) : β (QuotientGroup.mk x) (QuotientGroup.mk y) = S.HS H x y :=
    rfl
  have hnegF : D.ζ12 ^ 6 = -1 := by
    have hroot : IsPrimitiveRoot (D.ζ12 ^ 6) 2 := by
      simpa using D.hζ12.pow_of_dvd (by norm_num : (6 : ℕ) ≠ 0) (by norm_num : 6 ∣ 12)
    exact hroot.eq_neg_one_of_two_right
  have halt (v : FinPlace F) (a : (v.adicCompletion F)ˣ) : H.hilb v a a = 1 := by
    by_cases ha : a = 1
    · subst a
      exact H.sixth_power v 1 1 ⟨1, by simp⟩
    let φ : (v.adicCompletion F)ˣ →* rootsOfUnity 6 F :=
      MonoidHom.mk' (H.hilb v a) (H.mul_right v a)
    have hane : (a : v.adicCompletion F) ≠ 1 := fun h => ha (Units.ext h)
    have haine : (a⁻¹ : (v.adicCompletion F)ˣ) ≠ 1 := inv_ne_one.mpr ha
    let s : (v.adicCompletion F)ˣ := Units.mk0 (1 - (a : v.adicCompletion F))
      (sub_ne_zero.mpr hane.symm)
    let t : (v.adicCompletion F)ˣ := Units.mk0 (1 - ((a⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F))
      (sub_ne_zero.mpr (fun h => haine (Units.ext h.symm)))
    have hs : φ s = 1 := H.steinberg v a _
    have ht : φ t = 1 := by
      have h := H.steinberg v a⁻¹ (sub_ne_zero.mpr (fun h => haine (Units.ext h.symm)))
      let ψ : (v.adicCompletion F)ˣ →* rootsOfUnity 6 F :=
        MonoidHom.mk' (fun x => H.hilb v x t) (fun x y => H.mul_left v x y t)
      change ψ a⁻¹ = 1 at h
      rw [map_inv, inv_eq_one] at h
      exact h
    have hts : t = (-1 : (v.adicCompletion F)ˣ) * a⁻¹ * s := by
      apply Units.ext
      simp only [t, s, Units.val_mk0, Units.val_mul, Units.val_neg, Units.val_one,
        Units.val_inv_eq_inv_val]
      field_simp
      ring
    let ξ : (v.adicCompletion F)ˣ :=
      toLoc v (Units.mk0 D.ζ12 (D.hζ12.ne_zero (by norm_num)))
    have hξ : ξ ^ 6 = (-1 : (v.adicCompletion F)ˣ) := by
      apply Units.ext
      change ((algebraMap F (v.adicCompletion F)) D.ζ12) ^ 6 = -1
      rw [← map_pow, hnegF, map_neg, map_one]
    have hn : φ (-1) = 1 := hr6 v a (-1) ⟨ξ, hξ.symm⟩
    rw [hts, map_mul, map_mul, hn, hs, map_inv, one_mul, mul_one, inv_eq_one] at ht
    exact ht
  refine ⟨β, hβ, ?_, ?_⟩
  · intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [hβ]
      apply Finset.prod_eq_one
      intro v hv
      exact halt v.1 (S.compU v x)
  · intro q hq
    induction q using QuotientGroup.induction_on with
    | H x =>
      have hx (y : S.FSˣ) : S.HS H x y = 1 := by
        rw [← hβ]
        exact hq _
      have hfin (v : S.Sf) : ∃ c : (v.1.adicCompletion F)ˣ, S.compU v x = c ^ 6 := by
        apply H.nondeg
        intro b
        let u : ∀ j : S.Sf, (j.1.adicCompletion F)ˣ := Pi.mulSingle v b
        let y : S.FSˣ :=
          { val := (fun j => (u j : j.1.adicCompletion F), fun _ => 1)
            inv := (fun j => ((u j)⁻¹ : j.1.adicCompletion F), fun _ => 1)
            val_inv := by ext j <;> simp
            inv_val := by ext j <;> simp }
        have hc (j : S.Sf) : S.compU j y = u j := Units.ext rfl
        have hsingle : S.HS H x y = H.hilb v.1 (S.compU v x) b := by
          unfold SData.HS
          rw [Finset.prod_eq_single v]
          · simp only [hc, u, Pi.mulSingle_eq_same]
          · intro j hj hjv
            simp only [hc, u, Pi.mulSingle_eq_of_ne hjv]
            exact hr1 j.1 _
          · simp
        rw [← hsingle]
        exact hx y
      have hcomplex (w : InfinitePlace F) : ∃ c : ℂˣ, S.compC w x = c ^ 6 := by
        obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (S.compC w x : ℂ) (by norm_num : 0 < (6 : ℕ))
        have hz0 : z ≠ 0 := by
          intro h
          rw [h, zero_pow (by norm_num)] at hz
          exact (S.compC w x).ne_zero hz.symm
        refine ⟨Units.mk0 z hz0, ?_⟩
        apply Units.ext
        exact hz.symm
      choose c hc using hfin
      choose d hd using hcomplex
      let y : S.FSˣ :=
        { val := (fun v => (c v : v.1.adicCompletion F), fun w => (d w : ℂ))
          inv := (fun v => ((c v)⁻¹ : v.1.adicCompletion F), fun w => ((d w)⁻¹ : ℂ))
          val_inv := by ext v <;> simp
          inv_val := by ext v <;> simp }
      apply (QuotientGroup.eq_one_iff _).mpr
      refine ⟨y, ?_⟩
      apply Units.ext
      apply Prod.ext <;> funext v
      · exact congrArg Units.val (hc v).symm
      · exact congrArg Units.val (hd v).symm

/-- The S-unit image is isotropic: two S-units pair to 1 at every place outside `S`
by the tame formula, so reciprocity makes the product over `S` trivial. -/
theorem _root_.ArtinPrimitiveRoots.Proofs.a1_bdata_sol.E_isotropic
    (S : SData F CE condη) (H : HilbertData F)
    (β : S.V →* (S.V →* rootsOfUnity 6 F))
    (hβ : ∀ x y : S.FSˣ,
      β (QuotientGroup.mk x) (QuotientGroup.mk y) = S.HS H x y) :
    ∀ q ∈ S.E, ∀ r ∈ S.E, β q r = 1 := by
  classical
  intro q hq r hr
  obtain ⟨u, hu, huq⟩ := Subgroup.mem_map.mp hq
  obtain ⟨ε, hε, hεr⟩ := Subgroup.mem_map.mp hr
  have hqmk : q = QuotientGroup.mk (S.diagU (u : Fˣ)) := by
    simpa using huq.symm
  have hrmk : r = QuotientGroup.mk (S.diagU (ε : Fˣ)) := by
    simpa using hεr.symm
  have hpair := hβ (S.diagU (u : Fˣ)) (S.diagU (ε : Fˣ))
  rw [← hqmk, ← hrmk] at hpair
  have hcount (a : Fˣ) (ha : a ∈ S.US) (v : FinPlace F) (hv : v ∉ S.Sf) :
      FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F)) = 0 := by
    have hval : v.valuation F (a : F) = 1 := ha v hv
    rw [ArtinPrimitiveRoots.A2.qs_nq0_count_spanSingleton_eq_neg_log_valuation
      v (a : F) a.ne_zero, hval]
    simp
  have hres (a : Fˣ) (ha : a ∈ S.US) (v : FinPlace F) (hv : v ∉ S.Sf) :
      residue v (a : F) ≠ 0 :=
    (ArtinPrimitiveRoots.A2.qs_nq0_residue_ne_zero_iff_valuation_one v (a : F)).mpr
      (ha v hv)
  have h6 (v : FinPlace F) (hv : v ∉ S.Sf) : (6 : 𝓞 F) ∉ v.asIdeal :=
    fun h => hv (S.over6 v h)
  let f : FinPlace F → rootsOfUnity 6 F := fun v => H.hilb v (toLoc v u) (toLoc v ε)
  have houtside (v : FinPlace F) (hv : v ∉ S.Sf) : f v = 1 := by
    have htame := H.tame v (h6 v hv) u ε (hres u hu v hv)
    rw [hcount ε hε v hv, zpow_zero] at htame
    apply Subtype.ext
    apply Units.ext
    simpa using htame
  have hsupport : Function.mulSupport f ⊆ S.Sf := by
    intro v hv
    by_contra hnot
    exact hv (houtside v hnot)
  have hfin : (∏ᶠ v, f v) = ∏ v ∈ S.Sf, f v :=
    finprod_eq_prod_of_mulSupport_subset f hsupport
  have hglobal : (∏ᶠ v, f v) = 1 := (H.product_formula (u : Fˣ) (ε : Fˣ)).2
  have hsf : (∏ v ∈ S.Sf, f v) =
      S.HS H (S.diagU (u : Fˣ)) (S.diagU (ε : Fˣ)) := by
    rw [← Finset.prod_attach S.Sf (fun v => f v)]
    unfold SData.HS
    refine Finset.prod_congr rfl ?_
    intro v _
    have hcu : S.compU v (S.diagU (u : Fˣ)) = toLoc v.1 u := by
      apply Units.ext
      rfl
    have hcε : S.compU v (S.diagU (ε : Fˣ)) = toLoc v.1 ε := by
      apply Units.ext
      rfl
    simp [f, hcu, hcε]
  exact hpair.trans (hsf.symm.trans (hfin.symm.trans hglobal))

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

private theorem a1_bdata_sol_allowed_ratio_local_sixth
    {S : SData F CE condη} {H : HilbertData F} (Bd : BData S H)
    (I : Ideal (𝓞 F)) (a b : Fˣ) (ha : S.IsGen (a : F) I ∧ Bd.Allowed a)
    (hb : S.IsGen (b : F) I ∧ Bd.Allowed b) :
    a / b ∈ S.US ∧ ∃ x : S.FSˣ, S.diagU (a / b) = x ^ 6 := by
  classical
  letI : CommGroup S.V := QuotientGroup.Quotient.commGroup _
  have hu : a / b ∈ S.US := by
    intro v hv
    have hcount : FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) ((a / b : Fˣ) : F)) = 0 := by
      rw [Units.val_div_eq_div_val]
      rw [← FractionalIdeal.spanSingleton_div_spanSingleton, div_eq_mul_inv,
        FractionalIdeal.count_mul F v
          (FractionalIdeal.spanSingleton_ne_zero_iff.mpr a.ne_zero)
          (inv_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr b.ne_zero)),
        FractionalIdeal.count_inv, ha.1.2.2 v hv, hb.1.2.2 v hv, add_neg_cancel]
    have hc := ArtinPrimitiveRoots.A2.qs_nq0_count_spanSingleton_eq_neg_log_valuation
      v ((a / b : Fˣ) : F) (a / b).ne_zero
    rw [hcount] at hc
    have hlog : WithZero.log (v.valuation F ((a / b : Fˣ) : F)) = 0 :=
      neg_eq_zero.mp hc.symm
    calc
      v.valuation F ((a / b : Fˣ) : F) =
          WithZero.exp (WithZero.log (v.valuation F ((a / b : Fˣ) : F))) :=
        (WithZero.exp_log ((v.valuation F).ne_zero_iff.mpr (a / b).ne_zero)).symm
      _ = 1 := by rw [hlog, WithZero.exp_zero]
  have hE : (QuotientGroup.mk (S.diagU (a / b)) : S.V) ∈ S.E := by
    exact Subgroup.mem_map.mpr ⟨a / b, hu, rfl⟩
  have hB : (QuotientGroup.mk (S.diagU (a / b)) : S.V) ∈ Bd.B := by
    have hdiv := Bd.B.div_mem ha.2 hb.2
    simpa only [map_div, QuotientGroup.mk_div] using hdiv
  have hclass : (QuotientGroup.mk (S.diagU (a / b)) : S.V) = 1 :=
    Subgroup.disjoint_def.mp Bd.compl.disjoint hE hB
  obtain ⟨x, hx⟩ := (QuotientGroup.eq_one_iff _).mp hclass
  exact ⟨hu, x, hx.symm⟩

private theorem a1_bdata_sol_exterior_symbol_trivial (S : SData F CE condη)
    (H : HilbertData F) (u : Fˣ) (hu : u ∈ S.US)
    (hlocal : ∃ x : S.FSˣ, S.diagU u = x ^ 6) :
    ∀ P : FinPlace F, P ∉ S.Sf → chiAlg P (u : F) = 1 := by
  classical
  obtain ⟨x, hx⟩ := hlocal
  intro P hP
  have hPext : S.IsExterior P.asIdeal := by
    refine ⟨P.ne_bot, ?_⟩
    intro v hv hle
    have heq : P.asIdeal = v.asIdeal := P.isMaximal.eq_of_le v.isPrime.ne_top hle
    have hplace : P = v := HeightOneSpectrum.ext heq
    exact hP (hplace ▸ hv)
  obtain ⟨c, hc⟩ :=
    ArtinPrimitiveRoots.Proofs.A1Generators.exists_generator_of_pid S P.asIdeal hPext
  have hres (v : FinPlace F) (hv : v ∉ S.Sf) : residue v (u : F) ≠ 0 :=
    (ArtinPrimitiveRoots.A2.qs_nq0_residue_ne_zero_iff_valuation_one v (u : F)).mpr
      (hu v hv)
  have h6 (v : FinPlace F) (hv : v ∉ S.Sf) : (6 : 𝓞 F) ∉ v.asIdeal := by
    intro h
    exact hv (S.over6 v h)
  let f : FinPlace F → rootsOfUnity 6 F := fun v => H.hilb v (toLoc v u) (toLoc v c)
  have hoff (v : FinPlace F) (hvP : v ≠ P) : f v = 1 := by
    by_cases hvS : v ∈ S.Sf
    · let vs : S.Sf := ⟨v, hvS⟩
      have hcomp : S.compU vs (S.diagU u) = toLoc v u := by
        apply Units.ext
        rfl
      have hpow := congrArg (S.compU vs) hx
      rw [hcomp, map_pow] at hpow
      exact H.sixth_power v (toLoc v u) (toLoc v c) ⟨S.compU vs x, hpow⟩
    · have hcount : FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (c : F)) = 0 := by
        calc
          _ = FractionalIdeal.count F v
              (P.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := hc.2.2 v hvS
          _ = 0 := FractionalIdeal.count_maximal_coprime (K := F) v hvP.symm
      have htame := H.tame v (h6 v hvS) u c (hres v hvS)
      rw [hcount, zpow_zero] at htame
      apply Subtype.ext
      exact Units.ext htame
  have hpair : H.hilb P (toLoc P u) (toLoc P c) = 1 := by
    change f P = 1
    rw [← finprod_eq_single f P hoff]
    exact (H.product_formula u c).2
  have hcountP : FractionalIdeal.count F P
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (c : F)) = 1 := by
    calc
      _ = FractionalIdeal.count F P
          (P.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := hc.2.2 P hP
      _ = 1 := by simpa using (FractionalIdeal.count_maximal (K := F) P P)
  have htame := H.tame P (h6 P hP) u c (hres P hP)
  rw [hpair, hcountP, zpow_one] at htame
  apply Subtype.ext
  apply Units.ext
  apply IsFractionRing.injective (𝓞 F) F
  simpa using htame.symm

private theorem a1_bdata_sol_mu6_of_hilbertData (H : HilbertData F) :
    ∃ ζ : F, IsPrimitiveRoot ζ 6 := by
  classical
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 F)
  let v : FinPlace F := ⟨P, hP.isPrime,
    Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField F)⟩
  obtain ⟨r, hr⟩ := v.valuation_exists_uniformizer F
  have hr0 : r ≠ 0 := (v.valuation F).ne_zero_iff.mp (by
    rw [hr]
    exact WithZero.coe_ne_zero)
  let π : (v.adicCompletion F)ˣ := toLoc v (Units.mk0 r hr0)
  have hπ : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    change Valued.v ((r : F) : v.adicCompletion F) = _
    rw [v.valuedAdicCompletion_eq_valuation']
    exact hr
  have hnot : ¬ ∀ b, H.hilb v (π ^ 2) b = 1 := by
    intro h
    obtain ⟨c, hc⟩ := H.nondeg v (π ^ 2) h
    have hlog := congrArg
      (fun y : (v.adicCompletion F)ˣ => WithZero.log (Valued.v (y : v.adicCompletion F))) hc
    simp only [Units.val_pow_eq_pow_val, map_pow, WithZero.log_pow, hπ,
      WithZero.log_exp, nsmul_eq_mul] at hlog
    norm_num at hlog
    omega
  obtain ⟨b, hb⟩ := not_forall.mp hnot
  let z : rootsOfUnity 6 F := H.hilb v π b
  have hmul : H.hilb v (π ^ 2) b = z ^ 2 := by
    simp only [pow_two, H.mul_left, z]
  have hz : z ^ 2 ≠ 1 := by
    rw [← hmul]
    exact hb
  let ω : F := ((z : Fˣ) : F) ^ 2
  have hωne : ω ≠ 1 := by
    intro h
    apply hz
    apply Subtype.ext
    apply Units.ext
    simpa [ω] using h
  have hz6 : (((z : Fˣ) : F) ^ 6) = 1 := by
    have h := (mem_rootsOfUnity 6 (z : Fˣ)).mp z.property
    simpa using congrArg (fun y : Fˣ => (y : F)) h
  have hω3 : ω ^ 3 = 1 := by
    dsimp [ω]
    rw [← pow_mul]
    exact hz6
  have hprim3 : IsPrimitiveRoot ω 3 :=
    isPrimitiveRoot_of_mem_nthRootsFinset (by norm_num)
      ((Polynomial.mem_nthRootsFinset (by norm_num) (1 : F)).mpr hω3) hωne
  have hprim2 : IsPrimitiveRoot (-1 : F) 2 := IsPrimitiveRoot.neg_one 0 (by decide)
  have hprim6 := hprim2.pow_mul_pow_lcm hprim3 (by decide) (by decide)
  rw [show Nat.lcm 2 3 = 6 by decide] at hprim6
  exact ⟨_, hprim6⟩

open Filter Topology in
private theorem a1_bdata_sol_local_sixth_everywhere_of_hilbert (S : SData F CE condη)
    (H : HilbertData F) (u : Fˣ) (hu : u ∈ S.US)
    (hlocal : ∃ x : S.FSˣ, S.diagU u = x ^ 6) :
    ∀ v : FinPlace F, ∃ c : (v.adicCompletion F)ˣ, toLoc v u = c ^ 6 := by
  classical
  obtain ⟨x, hx⟩ := hlocal
  intro v
  by_cases hv : v ∈ S.Sf
  · let vs : S.Sf := ⟨v, hv⟩
    refine ⟨S.compU vs x, ?_⟩
    have hcomp : S.compU vs (S.diagU u) = toLoc v u := by
      apply Units.ext
      rfl
    have hroot := congrArg (S.compU vs) hx
    rw [hcomp, map_pow] at hroot
    exact hroot
  · have hext := a1_bdata_sol_exterior_symbol_trivial S H u hu ⟨x, hx⟩ v hv
    let L := v.adicCompletion F
    have hpow : {y : Lˣ | ∃ c, y = c ^ 6} ∈ 𝓝 (1 : Lˣ) := by
      obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
      let a : L := NumberField.FinitePlace.embedding v (algebraMap (𝓞 F) F t)
      have htF : algebraMap (𝓞 F) F t ≠ 0 :=
        NumberField.RingOfIntegers.coe_ne_zero_iff.mpr ht0
      have ha0 : a ≠ 0 := (NumberField.FinitePlace.embedding v).injective.ne htF
      have hanorm : ‖a‖ < 1 :=
        (NumberField.FinitePlace.norm_lt_one_iff_mem (K := F) v t).mpr ht
      letI : NontriviallyNormedField L :=
        NontriviallyNormedField.ofNormNeOne ⟨a, ha0, ne_of_lt hanorm⟩
      have h6 : (6 : L) ≠ 0 := by
        intro h
        have hF : (6 : F) = 0 := (algebraMap F L).injective
          (by simpa only [map_ofNat, map_zero] using h)
        exact (by norm_num : (6 : F) ≠ 0) hF
      have hs : {y : L | ∃ c : L, y = c ^ 6} ∈ 𝓝 (1 : L) := by
        have hd : HasStrictDerivAt (fun y : L => y ^ 6) (6 : L) 1 := by
          simpa using hasStrictDerivAt_pow 6 (1 : L)
        have hm : Filter.map (fun y : L => y ^ 6) (𝓝 1) = 𝓝 1 := by
          simpa using hd.map_nhds_eq h6
        have hp : {y : L | ∃ c : L, y = c ^ 6} ∈
            Filter.map (fun y : L => y ^ 6) (𝓝 1) :=
          Filter.mem_map.mpr (Filter.Eventually.of_forall fun y => ⟨y, rfl⟩)
        rw [hm] at hp
        exact hp
      filter_upwards [(Units.continuous_val.tendsto (1 : Lˣ)).eventually hs] with y hy
      obtain ⟨c, hc⟩ := hy
      have hc0 : c ≠ 0 := by
        intro h
        apply y.ne_zero
        rw [hc, h, zero_pow (by decide : 6 ≠ 0)]
      refine ⟨Units.mk0 c hc0, ?_⟩
      apply Units.ext
      exact hc
    have hdu : DenseRange (toLoc v) := by
      let val : Lˣ → L := fun y => (y : L)
      have hval : IsOpenEmbedding val :=
        IsOpenUnits.isOpenEmbedding_unitsVal (M := L)
      rw [DenseRange, dense_iff_inter_open]
      intro V hV hVne
      obtain ⟨a, ha⟩ := (v.denseRange_algebraMap F).exists_mem_open
        (hval.isOpenMap V hV) (hVne.image val)
      obtain ⟨z, hz, hza⟩ := ha
      have ha0 : a ≠ 0 := by
        intro h
        have hzero : (z : L) = 0 := by simpa only [val, h, map_zero] using hza
        exact z.ne_zero hzero
      let au : Fˣ := Units.mk0 a ha0
      have heq : toLoc v au = z := by
        apply Units.ext
        exact hza.symm
      refine ⟨toLoc v au, ?_, au, rfl⟩
      rw [heq]
      exact hz
    let row : Lˣ →* rootsOfUnity 6 F :=
      MonoidHom.mk' (fun y => H.hilb v (toLoc v u) y)
        (fun y z => H.mul_right v (toLoc v u) y z)
    have hglobal (a : Fˣ) : row (toLoc v a) = 1 := by
      have h6 : (6 : 𝓞 F) ∉ v.asIdeal := fun h => hv (S.over6 v h)
      have hres : residue v (u : F) ≠ 0 :=
        (ArtinPrimitiveRoots.A2.qs_nq0_residue_ne_zero_iff_valuation_one v (u : F)).mpr
          (hu v hv)
      have htame := H.tame v h6 u a hres
      change H.hilb v (toLoc v u) (toLoc v a) = 1
      apply Subtype.ext
      exact Units.ext (by simpa [hext] using htame)
    have hright6 (c : Lˣ) : row (c ^ 6) = 1 := by
      have hl := H.sixth_power v (c ^ 6) (toLoc v u) ⟨c, rfl⟩
      have hs := H.skew v (toLoc v u) (c ^ 6)
      rw [hl, mul_one] at hs
      exact hs
    apply H.nondeg v (toLoc v u)
    intro y
    have hW : {z : Lˣ | ∃ c, y / z = c ^ 6} ∈ 𝓝 y := by
      have hcont : Continuous (fun z : Lˣ => y / z) := continuous_const.div' continuous_id
      have ht : Tendsto (fun z : Lˣ => y / z) (𝓝 y) (𝓝 (1 : Lˣ)) := by
        simpa only [div_self'] using hcont.tendsto y
      exact ht.eventually hpow
    obtain ⟨z, hz, hzrange⟩ := mem_closure_iff_nhds.mp (hdu y) _ hW
    obtain ⟨a, rfl⟩ := hzrange
    obtain ⟨c, hc⟩ := hz
    have heq := congrArg row hc
    rw [map_div, hright6, hglobal, div_one] at heq
    exact heq

/-- A local sixth power of an S-unit is a global sixth power of an S-unit. -/
theorem _root_.ArtinPrimitiveRoots.Proofs.a1_bdata_sol.s_unit_sixth_injective_of_hilbert
    (S : SData F CE condη) (H : HilbertData F) (u : Fˣ) (hu : u ∈ S.US)
    (hlocal : ∃ x : S.FSˣ, S.diagU u = x ^ 6) :
    ∃ ε ∈ S.US, u = ε ^ 6 := by
  obtain ⟨ε, heq⟩ := ArtinPrimitiveRoots.Proofs.a1_bdata_sol.global_sixth_of_local
    (a1_bdata_sol_mu6_of_hilbertData H) u
    (a1_bdata_sol_local_sixth_everywhere_of_hilbert S H u hu hlocal)
  exact ⟨ε, ArtinPrimitiveRoots.Proofs.a1_bdata_sol.s_unit_of_sixth S u ε hu heq, heq⟩

/-- The image of the S-units in the sixth-power quotient has order
`6 ^ (#S_f + #infinite places)`. -/
theorem _root_.ArtinPrimitiveRoots.Proofs.a1_bdata_sol.s_unit_image_cardinality_of_hilbert
    (D : FieldData F) (S : SData F CE condη) (H : HilbertData F) :
    Nat.card (S.US.map (((QuotientGroup.mk' _) : S.FSˣ →* S.V).comp S.diagU)) =
      6 ^ (S.Sf.card + numComplex F) :=
  ArtinPrimitiveRoots.Proofs.a1_bdata_sol.s_unit_image_cardinality D S
    (ArtinPrimitiveRoots.Proofs.a1_bdata_sol.s_unit_sixth_injective_of_hilbert S H)

theorem BData.allowed_unique {S : SData F CE condη} {H : HilbertData F} (Bd : BData S H)
    (I : Ideal (𝓞 F)) (a b : Fˣ) (ha : S.IsGen (a : F) I ∧ Bd.Allowed a)
    (hb : S.IsGen (b : F) I ∧ Bd.Allowed b) :
    ∃ ε ∈ S.US, a = ε ^ 6 * b := by
  obtain ⟨hu, hlocal⟩ := a1_bdata_sol_allowed_ratio_local_sixth Bd I a b ha hb
  obtain ⟨ε, heq⟩ := ArtinPrimitiveRoots.Proofs.a1_bdata_sol.global_sixth_of_local
    (a1_bdata_sol_mu6_of_hilbertData H) (a / b)
    (a1_bdata_sol_local_sixth_everywhere_of_hilbert S H (a / b) hu hlocal)
  refine ⟨ε, ?_, div_eq_iff_eq_mul.mp heq⟩
  intro v hv
  have hval := hu v hv
  rw [heq, Units.val_pow_eq_pow_val, map_pow] at hval
  have hlog := congrArg WithZero.log hval
  simp only [WithZero.log_pow, WithZero.log_one, nsmul_eq_mul] at hlog
  have hzero : WithZero.log (v.valuation F (ε : F)) = 0 := by omega
  calc
    v.valuation F (ε : F) = WithZero.exp (WithZero.log (v.valuation F (ε : F))) :=
      (WithZero.exp_log ((v.valuation F).ne_zero_iff.mpr ε.ne_zero)).symm
    _ = 1 := by rw [hzero, WithZero.exp_zero]

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
  classical
  have hAbsFinOne (v : FinPlace F) : absFin v 1 = 1 := by
    have hv : (Ideal.absNorm v.asIdeal : NNReal) ≠ 0 :=
      HeightOneSpectrum.absNorm_ne_zero v
    simp [absFin, hv]
  have hAbsSMul (S : SData F CE condη) (x y : S.FS) :
      S.absS (x * y) = S.absS x * S.absS y := by
    have hnorm (v : S.Sf) : Ideal.absNorm v.1.asIdeal ≠ 0 := by
      have hv : (Ideal.absNorm v.1.asIdeal : NNReal) ≠ 0 :=
        HeightOneSpectrum.absNorm_ne_zero v.1
      exact_mod_cast hv
    simp [SData.absS, absFin, hnorm, Finset.prod_mul_distrib, Complex.normSq_mul]
    ring
  have hAbsEll (S : SData F CE condη) (T : ℝ) (hT : 0 < T) :
      S.absS (S.ell D T hT) = T := by
    simp only [SData.absS, SData.ell]
    simp_rw [hAbsFinOne]
    simp only [Finset.prod_const_one, one_mul, Complex.normSq_ofReal,
      Finset.prod_const, Finset.card_univ]
    rw [show numComplex F = Fintype.card (InfinitePlace F) by rfl]
    have hc : (Fintype.card (InfinitePlace F) : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_pos_iff.mpr
        (inferInstance : Nonempty (InfinitePlace F))).ne'
    rw [← Real.rpow_add hT]
    rw [← Real.rpow_natCast (T ^ (1 / (2 * (Fintype.card (InfinitePlace F) : ℝ)) +
      1 / (2 * (Fintype.card (InfinitePlace F) : ℝ))))
        (Fintype.card (InfinitePlace F))]
    have hrpow := Real.rpow_mul (le_of_lt hT)
      (1 / (2 * (Fintype.card (InfinitePlace F) : ℝ)) +
        1 / (2 * (Fintype.card (InfinitePlace F) : ℝ)))
      (Fintype.card (InfinitePlace F) : ℝ)
    rw [hrpow.symm]
    have he : (1 / (2 * (Fintype.card (InfinitePlace F) : ℝ)) +
        1 / (2 * (Fintype.card (InfinitePlace F) : ℝ))) *
        (Fintype.card (InfinitePlace F) : ℝ) = 1 := by
      field_simp [hc]
      norm_num
    rw [he, Real.rpow_one]
  let ellUnit (S : SData F CE condη) (T : ℝ) (hT : 0 < T) : S.FSˣ := {
    val := S.ell D T hT
    inv := S.ell D T⁻¹ (inv_pos.mpr hT)
    val_inv := by
      ext v
      · simp [SData.ell]
      · simp [SData.ell, Real.inv_rpow (le_of_lt hT)]
        field_simp [Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hT _).ne']
    inv_val := by
      ext v
      · simp [SData.ell]
      · simp [SData.ell, Real.inv_rpow (le_of_lt hT)]
        field_simp [Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hT _).ne']
  }
  obtain ⟨K, hK, hKnorm, hrep⟩ :=
    ArtinPrimitiveRoots.Proofs.A1_LATTICE.fsOne_compact_representatives_core S D
  refine ⟨K, hK, hKnorm, ?_⟩
  intro I hI
  obtain ⟨a, haGen, haAllowed⟩ := Bd.exists_allowed I hI
  have hnormI : 0 < Ideal.absNorm I :=
    Ideal.absNorm_pos_of_nonZeroDivisors
      ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr
        (by simpa [Ideal.zero_eq_bot] using hI.1)⟩
  let T : ℝ := (Ideal.absNorm I : ℝ)⁻¹
  have hT : 0 < T := by
    dsimp [T]
    exact inv_pos.mpr (Nat.cast_pos.mpr hnormI)
  let x : S.FSˣ := S.diagU a * ellUnit S T hT
  have hdiagNorm : S.absS ((S.diagU a : S.FSˣ) : S.FS) = Ideal.absNorm I := by
    simpa [SData.diagU] using
      ArtinPrimitiveRoots.Proofs.A1_LATTICE.absS_diag_eq_norm_core
        D S (a : F) I hI haGen
  have hellNorm : S.absS (ellUnit S T hT : S.FS) = T := by
    change S.absS (S.ell D T hT) = T
    exact hAbsEll S T hT
  have hxNorm : S.absS (x : S.FS) = 1 := by
    change S.absS (((S.diagU a : S.FSˣ) : S.FS) *
      (ellUnit S T hT : S.FS)) = 1
    rw [hAbsSMul, hdiagNorm, hellNorm]
    dsimp [T]
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hnormI.ne')
  obtain ⟨y, hyK, u, hxu⟩ := hrep ⟨x, hxNorm⟩
  let uInv : S.US := u⁻¹
  let a' : Fˣ := ((uInv ^ 6 : S.US) : Fˣ) * a
  have ha'Gen : S.IsGen (a' : F) I := by
    change S.IsGen ((((uInv ^ 6 : S.US) : Fˣ) * a : Fˣ) : F) I
    exact ArtinPrimitiveRoots.Proofs.A1Generators.isGen_mul_sUnit
      S (uInv ^ 6) a haGen
  have hdiagA' : S.diagU a' =
      (S.diagU (uInv : Fˣ)) ^ 6 * S.diagU a := by
    simp [a', map_mul, map_pow]
  have hclass : (QuotientGroup.mk (S.diagU a') : S.V) =
      (QuotientGroup.mk (S.diagU a) : S.V) := by
    apply (QuotientGroup.eq_iff_div_mem).2
    change S.diagU a' / S.diagU a ∈
      (powMonoidHom 6 : S.FSˣ →* S.FSˣ).range
    rw [hdiagA']
    have hpow : (S.diagU (uInv : Fˣ)) ^ 6 ∈
        (powMonoidHom 6 : S.FSˣ →* S.FSˣ).range :=
      ⟨S.diagU (uInv : Fˣ), rfl⟩
    simpa using hpow
  have ha'Allowed : Bd.Allowed a' := by
    change (QuotientGroup.mk (S.diagU a') : S.V) ∈ Bd.B
    rw [hclass]
    exact haAllowed
  have hInvDiag : S.diagU (uInv : Fˣ) = (S.diagU (u : Fˣ))⁻¹ := by
    rw [show (uInv : Fˣ) = (u : Fˣ)⁻¹ by rfl, map_inv]
  have hdiagA'val : S.diag (a' : F) =
      (((S.diagU (uInv : Fˣ)) ^ 6 : S.FSˣ) : S.FS) * S.diag (a : F) := by
    simpa [SData.diagU] using
      congrArg (fun z : S.FSˣ => (z : S.FS)) hdiagA'
  have hxuVal : (x : S.FS) =
      (((S.diagU (u : Fˣ)) ^ 6 : S.FSˣ) : S.FS) * (y.1 : S.FS) :=
    congrArg (fun z : S.FSˣ => (z : S.FS)) hxu
  have hyEq : S.diag (a' : F) * S.ell D T hT = (y.1 : S.FS) := by
    calc
      S.diag (a' : F) * S.ell D T hT =
          (((S.diagU (uInv : Fˣ)) ^ 6 : S.FSˣ) : S.FS) *
            (S.diag (a : F) * S.ell D T hT) := by
              rw [hdiagA'val]
              ac_rfl
      _ = (((S.diagU (uInv : Fˣ)) ^ 6 : S.FSˣ) : S.FS) * (x : S.FS) := by
        rfl
      _ = (((S.diagU (uInv : Fˣ)) ^ 6 : S.FSˣ) : S.FS) *
            ((((S.diagU (u : Fˣ)) ^ 6 : S.FSˣ) : S.FS) * (y.1 : S.FS)) := by
              rw [hxuVal]
      _ = y.1 := by
        rw [hInvDiag]
        simp [inv_pow]
  have htargetEq :
      S.diag (a' : F) *
        S.ell D ((Ideal.absNorm I : ℝ)⁻¹) (by
          exact inv_pos.mpr (Nat.cast_pos.mpr hnormI)) = (y.1 : S.FS) := by
    simpa [T] using hyEq
  refine ⟨a', ha'Gen, ha'Allowed, ?_⟩
  rw [htargetEq]
  exact hyK

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
