import ArtinPrimitiveRoots.Hecke.Elementary
import ArtinPrimitiveRoots.A1.Characters
import ArtinPrimitiveRoots.A1.Proofs.A1_KUMMER.ContinuousCharacters
import ArtinPrimitiveRoots.Hecke.Dict.LocalCongruence
import ArtinPrimitiveRoots.Hecke.Dict.ConductorSupport
import ArtinPrimitiveRoots.Hecke.Dict.WeakApproximation
import ArtinPrimitiveRoots.Hecke.Proofs.«HK-DICT-IDELIC».Truncation
import ArtinPrimitiveRoots.Hecke.Proofs.«HK-DICT-IDELIC».LocalBridge
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace


/-!
# Hecke package: dictionary between ray-class characters and A1's idelic characters

Frozen interface (owned by the Hecke package). Conductor divisibility is A1's corrected `HeckeChar.ConductorDvd`.

Statements against the two frozen interfaces, imported directly from the built repo modules
`ArtinPrimitiveRoots.Hecke.Defs` and `ArtinPrimitiveRoots.A1.Characters` (both Mathlib-only).
Design and consumers: `A2-ALIGN.md` §2.  Proof sources (not compiled here): TauCeti
`HeckeCharacter.ofRayClassCharacter` (NumberField/Global/HeckeCharacter/Basic.lean:97),
`isFiniteOrder_iff_exists_rayClassCharacter` (HeckeCharacter/FiniteOrder.lean:80),
`RayClassCharacter.conductor`, `primitiveCharacter` (RayClass/Character/Conductor.lean:72,99),
`rayClassQuotient_mk_of_mem` (Ideles/Ray/ClassQuotient.lean:212); ClassFieldTheory
`rayClassGroup_hom_ext_finitePrime` (Theorems/ConductorsAndRayClassFields/
RayClassGroupHomExtFinitePrime.lean); plus an isomorphism between ClassFieldTheory's and TauCeti's
ideal-theoretic ray class groups (new).
-/

set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain Topology Filter

noncomputable section

namespace ArtinPrimitiveRoots.Dictionary

open ArtinPrimitiveRoots.A1 ArtinPrimitiveRoots.Hecke ClassFieldTheory

variable {F : Type} [Field F] [NumberField F]

/-! ## §0 Moduli as ideals; small package lemmas -/

/-- The ideal `∏_v 𝔭_v^{e_v}` of the finite part of a ray modulus. -/
def modulusIdeal (m : RayClassModulus F) : Ideal (𝓞 F) :=
  m.finitePart.prod (fun v e => v.asIdeal ^ e)

/-! The reusable product facts below are stated for arbitrary number-field types, then specialized
to the package's frozen `modulusIdeal` interface. -/
namespace HKDICTRay

variable {K : Type*} [Field K] [NumberField K]

/-- The integral ideal represented by a finitely supported family of prime exponents. -/
def modulusIdealOf (e : HeightOneSpectrum (𝓞 K) →₀ ℕ) : Ideal (𝓞 K) :=
  e.prod (fun v n => v.asIdeal ^ n)

omit [NumberField K] in
theorem modulusIdealOf_ne_bot (e : HeightOneSpectrum (𝓞 K) →₀ ℕ) :
    modulusIdealOf e ≠ ⊥ := by
  classical
  rw [modulusIdealOf, Finsupp.prod]
  exact Finset.prod_ne_zero_iff.mpr fun v hv => pow_ne_zero _ v.ne_bot

theorem modulusNorm_pos (m : RayClassModulus K) : 0 < Hecke.modulusNorm m := by
  classical
  rw [Hecke.modulusNorm, Finsupp.prod]
  apply Finset.prod_pos
  intro v hv
  exact pow_pos (Nat.zero_lt_of_lt
    (NumberField.HeightOneSpectrum.one_lt_absNorm v)) _

theorem modulusNorm_one_le (m : RayClassModulus K) :
    1 ≤ Hecke.modulusNorm m := by
  exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (modulusNorm_pos m))

end HKDICTRay

namespace HKDICTRay

section TypeZero

variable {K₀ : Type} [Field K₀] [NumberField K₀]

theorem idealExp_modulusIdealOf (e : HeightOneSpectrum (𝓞 K₀) →₀ ℕ)
    (v : FinPlace K₀) : A1.idealExp v (modulusIdealOf e) = e v := by
  classical
  have hcoe : (modulusIdealOf e : FractionalIdeal (nonZeroDivisors (𝓞 K₀)) K₀) =
      ∏ w ∈ e.support, (w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K₀)) K₀) ^ e w := by
    change (FractionalIdeal.coeIdealHom (nonZeroDivisors (𝓞 K₀)) K₀)
        (e.prod (fun w n => w.asIdeal ^ n)) = _
    rw [Finsupp.prod, map_prod]
    simp only [map_pow, FractionalIdeal.coeIdealHom_apply]
  have hcount : FractionalIdeal.count K₀ v
      (modulusIdealOf e : FractionalIdeal (nonZeroDivisors (𝓞 K₀)) K₀) = (e v : ℤ) := by
    rw [hcoe, FractionalIdeal.count_prod]
    · have hterm (w : HeightOneSpectrum (𝓞 K₀)) :
          FractionalIdeal.count K₀ v
              ((w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K₀)) K₀) ^ e w) =
            if w = v then (e w : ℤ) else 0 := by
        rw [FractionalIdeal.count_pow]
        by_cases hwv : w = v
        · subst w
          rw [FractionalIdeal.count_self]
          simp
        · rw [FractionalIdeal.count_maximal_coprime K₀ v hwv]
          simp [hwv]
      simp_rw [hterm]
      simp only [Finset.sum_ite_eq', Finsupp.mem_support_iff]
      by_cases hv : e v = 0 <;> simp [hv]
    · intro w hw
      exact pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr w.ne_bot)
  unfold A1.idealExp
  have hcount' := hcount
  rw [FractionalIdeal.count_coe K₀ v (modulusIdealOf_ne_bot e)] at hcount'
  exact_mod_cast hcount'

end TypeZero

variable {K : Type*} [Field K] [NumberField K]

/-- Primitivity is unchanged by inverting a ray class character. -/
theorem primitive_inv {m f : RayClassModulus K} (ψ : RayClassGroup m →* ℂˣ)
    (hprimitive : ∀ n : RayClassModulus K, FactorsThrough ψ n → n = f) :
    ∀ n : RayClassModulus K, FactorsThrough ψ⁻¹ n → n = f := by
  intro n hn
  apply hprimitive n
  refine ⟨hn.1, ?_⟩
  intro x hx hI
  have hval := hn.2 x hx hI
  change (ψ (QuotientGroup.mk ⟨toPrincipalIdeal (𝓞 K) K x, hI⟩))⁻¹ = 1 at hval
  exact inv_eq_one.mp hval

end HKDICTRay

/-- `modulusIdeal m` is nonzero. -/
theorem modulusIdeal_ne_bot (m : RayClassModulus F) : modulusIdeal m ≠ ⊥ := by
  change HKDICTRay.modulusIdealOf m.finitePart ≠ ⊥
  exact HKDICTRay.modulusIdealOf_ne_bot m.finitePart

/-- The norm of every ray modulus is positive. -/
theorem modulusNorm_pos (m : RayClassModulus F) : 0 < modulusNorm m :=
  HKDICTRay.modulusNorm_pos m

/-- The norm of every ray modulus is at least one. -/
theorem modulusNorm_one_le (m : RayClassModulus F) : 1 ≤ modulusNorm m :=
  HKDICTRay.modulusNorm_one_le m

/-- The exponent of a prime in `modulusIdeal m` is its finite-part exponent. -/
theorem idealExp_modulusIdeal (m : RayClassModulus F) (v : FinPlace F) :
    A1.idealExp v (modulusIdeal m) = m.finitePart v := by
  simpa [modulusIdeal, HKDICTRay.modulusIdealOf] using
    (HKDICTRay.idealExp_modulusIdealOf m.finitePart v)

/-- `N𝔪 = N(modulusIdeal 𝔪)`. Consumer: A2 `zf:convexity` (with `kummer_conductor`). -/
theorem modulusNorm_eq_absNorm (m : RayClassModulus F) :
    modulusNorm m = Ideal.absNorm (modulusIdeal m) := by
  classical
  simp [modulusNorm, modulusIdeal, Finsupp.prod, map_prod, map_pow]

private theorem modulusIdeal_antitone {n m : RayClassModulus F} (h : n ≤ m) :
    modulusIdeal m ≤ modulusIdeal n := by
  classical
  let d := m.finitePart - n.finitePart
  have hd : n.finitePart + d = m.finitePart := by
    ext v
    exact Nat.add_sub_of_le (h.1 v)
  unfold modulusIdeal
  rw [← hd, Finsupp.prod_add_index' (h_zero := by intro v; simp)
    (h_add := by intro v a b; simp [pow_add])]
  exact Ideal.mul_le_left

private theorem modulusNorm_mono {n m : RayClassModulus F} (h : n ≤ m) :
    modulusNorm n ≤ modulusNorm m := by
  have hdiv : modulusNorm n ∣ modulusNorm m := by
    rw [modulusNorm_eq_absNorm, modulusNorm_eq_absNorm]
    exact Ideal.absNorm_dvd_absNorm_of_le (modulusIdeal_antitone h)
  have hmpos : 0 < modulusNorm m := modulusNorm_pos m
  exact Nat.le_of_dvd hmpos hdiv

private def rayModulusWeight (m : RayClassModulus F) : ℕ :=
  m.finitePart.sum (fun _ e => e) + m.infinitePart.card

private theorem rayModulusWeight_strict_mono {n m : RayClassModulus F} (h : n ≤ m)
    (hne : n ≠ m) : rayModulusWeight n < rayModulusWeight m := by
  classical
  have hcard : n.infinitePart.card ≤ m.infinitePart.card := Finset.card_le_card h.2
  by_cases hfin : n.finitePart = m.finitePart
  · have hinf : n.infinitePart ≠ m.infinitePart := by
      intro hinf
      apply hne
      cases n
      cases m
      simp_all
    have hnot : ¬m.infinitePart ⊆ n.infinitePart := by
      intro hmn
      exact hinf (Finset.Subset.antisymm h.2 hmn)
    have hcard' : n.infinitePart.card < m.infinitePart.card :=
      Finset.card_lt_card ⟨h.2, hnot⟩
    have hsumEq : n.finitePart.sum (fun _ e => e) = m.finitePart.sum (fun _ e => e) :=
      congrArg (fun d : HeightOneSpectrum (𝓞 F) →₀ ℕ => d.sum (fun _ e => e)) hfin
    unfold rayModulusWeight
    omega
  · let d := m.finitePart - n.finitePart
    have hd : n.finitePart + d = m.finitePart := by
      ext v
      exact Nat.add_sub_of_le (h.1 v)
    have hd0 : d ≠ 0 := by
      intro hz
      apply hfin
      calc
        n.finitePart = n.finitePart + d := by simp [hz]
        _ = m.finitePart := hd
    have hdsum : 0 < d.sum (fun _ e => e) := by
      apply Finsupp.sum_pos _ hd0
      intro v hv
      exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hv)
    have hsum' : n.finitePart.sum (fun _ e => e) + d.sum (fun _ e => e) =
        m.finitePart.sum (fun _ e => e) := by
      rw [← hd, Finsupp.sum_add_index' (h_zero := by intro v; rfl)
        (h_add := by intro v a b; rfl)]
    unfold rayModulusWeight
    omega

/-- A character factors through its own modulus. -/
theorem factorsThrough_self {m : RayClassModulus F} (η : RayClassGroup m →* ℂˣ) :
    FactorsThrough η m := by
  refine ⟨⟨le_refl _, Finset.Subset.refl _⟩, ?_⟩
  intro x hx h
  have hmem : (⟨toPrincipalIdeal (𝓞 F) F x, h⟩ : rayClassPrimeToIdeals m) ∈
      rayPrincipalIdealSubgroupInPrimeTo m :=
    Subgroup.subset_closure ⟨x, hx, rfl⟩
  rw [(QuotientGroup.eq_one_iff _).mpr hmem, map_one]

/-- `conductorNorm η ≤ N𝔪`.  Consumer: A2 `zf:convexity` (H3 applied with the modulus bound of
`kummer_conductor`), `zf:row-conductor-family`. -/
theorem conductorNorm_le_modulusNorm {m : RayClassModulus F} (η : RayClassGroup m →* ℂˣ) :
    conductorNorm η ≤ modulusNorm m :=
  Nat.sInf_le ⟨m, factorsThrough_self η, rfl⟩

/-! ## §1 Ray class → idelic -/

private def d1IdeleCongrOneSubgroup (m : RayClassModulus F) :
    Subgroup (NumberField.IdeleGroup (𝓞 F) F) where
  carrier := {x |
    (∀ v : FinPlace F, v ∈ m.finitePart.support →
      ideleFiniteCoord v x ∈ rayLocalHigherUnitGroup v (m.finitePart v)) ∧
    ∀ w : RayClassRealPlace F, w ∈ m.infinitePart →
      0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
        (ideleInfiniteCoord w.1 x)}
  one_mem' := by
    constructor
    · intro v hv
      simpa only [map_one] using (rayLocalHigherUnitGroup v (m.finitePart v)).one_mem
    · intro w hw
      change 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
        (1 : w.1.Completion)
      simp
  mul_mem' := by
    rintro x y ⟨hx, hxinf⟩ ⟨hy, hyinf⟩
    refine ⟨fun v hv => ?_, fun w hw => ?_⟩
    · simpa only [map_mul] using
        (rayLocalHigherUnitGroup v (m.finitePart v)).mul_mem (hx v hv) (hy v hv)
    · simpa only [ideleInfiniteCoord_mul, map_mul] using mul_pos (hxinf w hw) (hyinf w hw)
  inv_mem' := by
    rintro x ⟨hx, hxinf⟩
    refine ⟨fun v hv => ?_, fun w hw => ?_⟩
    · simpa only [map_inv] using
        (rayLocalHigherUnitGroup v (m.finitePart v)).inv_mem (hx v hv)
    · change 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
        (ideleInfiniteCoord w.1 (x⁻¹))
      change 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
        ((ideleInfiniteCoordUnit w.1 (x⁻¹) : w.1.Completionˣ) : w.1.Completion)
      rw [map_inv, Units.val_inv_eq_inv_val, map_inv₀]
      exact inv_pos.mpr (hxinf w hw)

private theorem d1_ideleFiniteCoord_unitEmbedding (v : FinPlace F) (a : Fˣ) :
    ideleFiniteCoord v (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a) =
      finitePlaceUnitEmbedding v a := by
  apply Units.ext
  rfl

private theorem d1_valued_eq_one_of_bound (v : FinPlace F) (n : ℕ) (hn : 0 < n)
    (u : (v.adicCompletion F)ˣ)
    (h : Valued.v ((u : v.adicCompletion F) - 1) ≤ WithZero.exp (-(n : ℤ))) :
    Valued.v (u : v.adicCompletion F) = 1 := by
  have he : WithZero.exp (-(n : ℤ)) < 1 := by
    apply WithZero.exp_lt_one_iff.mpr
    omega
  have hsub : Valued.v ((u : v.adicCompletion F) - 1) <
      Valued.v (1 : v.adicCompletion F) := by
    simpa using h.trans_lt he
  simpa using (Valuation.map_eq_of_sub_lt (v := Valued.v)
    (x := (1 : v.adicCompletion F)) (y := (u : v.adicCompletion F)) hsub)

set_option maxHeartbeats 1000000 in
private theorem d1_exists_adjusted_idele (m : RayClassModulus F)
    (x : NumberField.IdeleGroup (𝓞 F) F) :
    ∃ a : Fˣ, NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a * x ∈ d1IdeleCongrOneSubgroup m := by
  classical
  let r : m.infinitePart → ℝ := fun w =>
    InfinitePlace.Completion.extensionEmbeddingOfIsReal w.1.2
      (ideleInfiniteCoord w.1.1 x)
  have hr (w : m.infinitePart) : r w ≠ 0 :=
    (map_ne_zero _).mpr (ideleInfiniteCoordUnit w.1.1 x).ne_zero
  let U : Set ((∀ v : m.finitePart.support, v.1.adicCompletion F) ×
      (∀ w : m.infinitePart, ℝ)) :=
    {p | (∀ v, Valued.v (p.1 v *
        (ideleFiniteCoord v.1 x : v.1.adicCompletion F) - 1) ≤
          WithZero.exp (-(m.finitePart v.1 : ℤ))) ∧
      ∀ w, 0 < p.2 w * r w}
  have hU : IsOpen U := by
    simp only [U, Set.setOf_and, Set.setOf_forall]
    refine (isOpen_iInter_of_finite fun v => ?_).inter
      (isOpen_iInter_of_finite fun w => ?_)
    · exact (v.1.isOpen_setOf_valued_le (K := F) WithZero.exp_ne_zero).preimage
        (f := fun p : (∀ v : m.finitePart.support, v.1.adicCompletion F) ×
          (∀ w : m.infinitePart, ℝ) =>
            p.1 v * (ideleFiniteCoord v.1 x : v.1.adicCompletion F) - 1) (by fun_prop)
    · exact isOpen_lt continuous_const (by fun_prop)
  have hp₀ : ((fun v : m.finitePart.support =>
      ((ideleFiniteCoord v.1 x)⁻¹ : (v.1.adicCompletion F)ˣ),
      fun w : m.infinitePart => (r w)⁻¹) :
      (∀ v : m.finitePart.support, v.1.adicCompletion F) ×
        (∀ w : m.infinitePart, ℝ)) ∈ U := by
    refine ⟨fun v => ?_, fun w => ?_⟩
    · simp only [Prod.fst, Function.comp_apply, Units.val_inv_eq_inv_val]
      rw [inv_mul_cancel₀ (ideleFiniteCoord v.1 x).ne_zero, sub_self, map_zero]
      exact zero_le
    · have hprod : (r w)⁻¹ * r w = 1 := inv_mul_cancel₀ (hr w)
      rw [hprod]
      exact zero_lt_one
  obtain ⟨α, hαf, hαi⟩ := (denseRange_algebraMap_embedding_of_isReal
      m.finitePart.support m.infinitePart).exists_mem_open hU ⟨_, hp₀⟩
  have hkey (a : Fˣ)
      (hfinite : ∀ v : m.finitePart.support,
        Valued.v (algebraMap F (v.1.adicCompletion F) (a : F) *
          (ideleFiniteCoord v.1 x : v.1.adicCompletion F) - 1) ≤
            WithZero.exp (-(m.finitePart v.1 : ℤ)))
      (hinf : ∀ w : m.infinitePart,
        0 < w.1.1.embedding_of_isReal w.1.2 (a : F) * r w) :
      NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a * x ∈ d1IdeleCongrOneSubgroup m := by
    refine ⟨fun v hv => ?_, fun w hw => ?_⟩
    · have he : 0 < m.finitePart v := Nat.pos_of_ne_zero
        (Finsupp.mem_support_iff.mp hv)
      let u := finitePlaceUnitEmbedding v a * ideleFiniteCoord v x
      have hu : Valued.v ((u : v.adicCompletion F) - 1) ≤
          WithZero.exp (-(m.finitePart v : ℤ)) := by
        simpa [u, finitePlaceUnitEmbedding] using hfinite ⟨v, hv⟩
      have huv : Valued.v (u : v.adicCompletion F) = 1 :=
        d1_valued_eq_one_of_bound v (m.finitePart v) he u hu
      have huInt : (u : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
        rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, huv]
      have huInvInt : ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈
          v.adicCompletionIntegers F := by
        rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
          Units.val_inv_eq_inv_val, map_inv₀, huv]
        simp
      have hloc := ArtinPrimitiveRoots.Proofs.hk_misc_p.d1_mem_rayLocalHigherUnitGroup_iff
        v (m.finitePart v) u
      have hloc' := hloc.mpr ⟨huInt, huInvInt, hu⟩
      change ideleFiniteCoord v (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a * x) ∈ _
      rw [map_mul, d1_ideleFiniteCoord_unitEmbedding]
      exact hloc'
    · change 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
        (ideleInfiniteCoord w.1 (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a * x))
      rw [ideleInfiniteCoord_mul, ideleInfiniteCoord_unitEmbedding, map_mul]
      have hglobal : InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
          (a : w.1.Completion) = w.1.embedding_of_isReal w.2 (a : F) :=
        (InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe w.2
          (WithAbs.toAbs _ (a : F))).trans (by simp)
      rw [hglobal]
      exact hinf ⟨w, hw⟩
  by_cases hα : α = 0
  · by_cases hS : m.finitePart.support.Nonempty
    · obtain ⟨v, hv⟩ := hS
      have hbound := hαf ⟨v, hv⟩
      have he : WithZero.exp (-(m.finitePart v : ℤ)) < 1 := by
        apply WithZero.exp_lt_one_iff.mpr
        have hp : 0 < m.finitePart v := Nat.pos_of_ne_zero
          (Finsupp.mem_support_iff.mp hv)
        omega
      have : 1 ≤ WithZero.exp (-(m.finitePart v : ℤ)) := by
        simpa [hα] using hbound
      exact (not_lt_of_ge this he).elim
    · by_cases hI : m.infinitePart.Nonempty
      · obtain ⟨w, hw⟩ := hI
        have hpos := hαi ⟨w, hw⟩
        simpa [hα] using hpos
      · refine ⟨1, ?_⟩
        have hx : x ∈ d1IdeleCongrOneSubgroup m := by
          constructor
          · intro v hv
            exact (hS ⟨v, hv⟩).elim
          · intro w hw
            exact (hI ⟨w, hw⟩).elim
        simpa using hx
  · exact ⟨Units.mk0 α hα, hkey (Units.mk0 α hα) hαf hαi⟩

private def d1IdeleIdealHom : NumberField.IdeleGroup (𝓞 F) F →*
    NumberFieldFractionalIdealGroup F :=
  Dictionary.toFractionalIdeal.comp (NumberField.IdeleGroup.toFiniteIdele (𝓞 F) F)

private theorem d1IdeleIdealPrimeTo (m : RayClassModulus F)
    (x : NumberField.IdeleGroup (𝓞 F) F) (hx : x ∈ d1IdeleCongrOneSubgroup m) :
    d1IdeleIdealHom x ∈ rayClassPrimeToIdeals m := by
  intro v hv
  have hlocal := ArtinPrimitiveRoots.Proofs.hk_misc_p.d1_mem_rayLocalHigherUnitGroup_iff
    v (m.finitePart v) (ideleFiniteCoord v x)
  have hdata := hlocal.mp (hx.1 v hv)
  have he : 0 < m.finitePart v := Nat.pos_of_ne_zero
    (Finsupp.mem_support_iff.mp hv)
  have hval : Valued.v (ideleFiniteCoord v x : v.adicCompletion F) = 1 :=
    d1_valued_eq_one_of_bound v (m.finitePart v) he (ideleFiniteCoord v x) hdata.2.2
  change FractionalIdeal.count F v
    (d1IdeleIdealHom x : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0
  rw [d1IdeleIdealHom, MonoidHom.comp_apply, Dictionary.count_coe_toFractionalIdeal]
  have hord : Dictionary.adicOrd (NumberField.IdeleGroup.toFiniteIdele (𝓞 F) F x) v = 0 := by
    rw [Dictionary.adicOrd_eq_zero_iff]
    simpa only [NumberField.IdeleGroup.coe_toFiniteIdele, ← Dictionary.ideleFiniteCoord_apply] using hval
  exact hord

private def d1IdeleRayClass (m : RayClassModulus F) :
    d1IdeleCongrOneSubgroup m →* RayClassGroup m :=
  (QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo m)).comp
    (MonoidHom.codRestrict
      (d1IdeleIdealHom.comp (d1IdeleCongrOneSubgroup m).subtype)
      (rayClassPrimeToIdeals m) (fun x => d1IdeleIdealPrimeTo m x.1 x.2))

private theorem d1IdeleRayClass_apply (m : RayClassModulus F)
    (x : d1IdeleCongrOneSubgroup m) :
    d1IdeleRayClass m x = QuotientGroup.mk
      ⟨d1IdeleIdealHom x.1, d1IdeleIdealPrimeTo m x.1 x.2⟩ := rfl

private theorem d1IdeleRayClass_one_of_ideal_one (m : RayClassModulus F)
    (x : d1IdeleCongrOneSubgroup m)
    (hI : d1IdeleIdealHom x.1 = 1) : d1IdeleRayClass m x = 1 := by
  rw [d1IdeleRayClass_apply]
  apply (QuotientGroup.eq_one_iff _).2
  apply Subgroup.mem_comap.mpr
  change d1IdeleIdealHom x.1 ∈ rayPrincipalIdealSubgroup m
  rw [hI]
  exact one_mem _

private theorem d1_ideleUnitEmbedding_mem_rayCongruent (m : RayClassModulus F)
    (a : Fˣ) (ha : NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a ∈ d1IdeleCongrOneSubgroup m) :
    IsRayCongruent m a := by
  refine ⟨fun v hv => ?_, fun w hw => ?_⟩
  · simpa only [d1_ideleFiniteCoord_unitEmbedding] using ha.1 v hv
  · have h := ha.2 w hw
    rw [ideleInfiniteCoord_unitEmbedding] at h
    have hglobal : InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
        (a : w.1.Completion) = w.1.embedding_of_isReal w.2 (a : F) :=
      (InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe w.2
        (WithAbs.toAbs _ (a : F))).trans (by simp)
    exact hglobal ▸ h

private theorem d1IdeleIdealHom_unitEmbedding (a : Fˣ) :
    d1IdeleIdealHom (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a) =
      toPrincipalIdeal (𝓞 F) F a := by
  simp [d1IdeleIdealHom, NumberField.IdeleGroup.toFiniteIdele_unitEmbedding,
    Dictionary.toFractionalIdeal_unitEmbedding]

private theorem d1IdeleRayClass_unitEmbedding (m : RayClassModulus F) (a : Fˣ)
    (ha : NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a ∈ d1IdeleCongrOneSubgroup m) :
    d1IdeleRayClass m ⟨NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a, ha⟩ = 1 := by
  rw [d1IdeleRayClass_apply]
  have hprincipal : toPrincipalIdeal (𝓞 F) F a ∈ rayPrincipalIdealSubgroup m :=
    Subgroup.subset_closure ⟨a, d1_ideleUnitEmbedding_mem_rayCongruent m a ha, rfl⟩
  have hmem : (⟨d1IdeleIdealHom (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a),
      d1IdeleIdealPrimeTo m (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a) ha⟩ :
        rayClassPrimeToIdeals m) ∈ rayPrincipalIdealSubgroupInPrimeTo m := by
    apply Subgroup.mem_comap.mpr
    change d1IdeleIdealHom (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a) ∈
      rayPrincipalIdealSubgroup m
    rw [d1IdeleIdealHom_unitEmbedding]
    exact hprincipal
  exact (QuotientGroup.eq_one_iff _).2 hmem

private theorem d1IdeleRayClass_eq_adjusted (m : RayClassModulus F)
    (x : NumberField.IdeleGroup (𝓞 F) F) (a b : Fˣ)
    (ha : NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a * x ∈ d1IdeleCongrOneSubgroup m)
    (hb : NumberField.IdeleGroup.unitEmbedding (𝓞 F) F b * x ∈ d1IdeleCongrOneSubgroup m) :
    d1IdeleRayClass m ⟨NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a * x, ha⟩ =
      d1IdeleRayClass m ⟨NumberField.IdeleGroup.unitEmbedding (𝓞 F) F b * x, hb⟩ := by
  let c : Fˣ := a * b⁻¹
  have hc : NumberField.IdeleGroup.unitEmbedding (𝓞 F) F c ∈ d1IdeleCongrOneSubgroup m := by
    have h := (d1IdeleCongrOneSubgroup m).mul_mem ha
      ((d1IdeleCongrOneSubgroup m).inv_mem hb)
    convert h using 1
    simp only [c, map_mul, map_inv]
    group
  have hsplit : (⟨NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a * x, ha⟩ :
      d1IdeleCongrOneSubgroup m) =
        ⟨NumberField.IdeleGroup.unitEmbedding (𝓞 F) F c, hc⟩ *
          ⟨NumberField.IdeleGroup.unitEmbedding (𝓞 F) F b * x, hb⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    simp only [c, map_mul, map_inv]
    group
  rw [hsplit, map_mul, d1IdeleRayClass_unitEmbedding m c hc]
  exact one_mul (d1IdeleRayClass m
    ⟨NumberField.IdeleGroup.unitEmbedding (𝓞 F) F b * x, hb⟩)

private noncomputable def d1IdeleToRayClassFun (m : RayClassModulus F)
    (x : NumberField.IdeleGroup (𝓞 F) F) : RayClassGroup m :=
  let a := Classical.choose (d1_exists_adjusted_idele m x)
  d1IdeleRayClass m ⟨NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a * x,
    Classical.choose_spec (d1_exists_adjusted_idele m x)⟩

private theorem d1IdeleToRayClassFun_eq (m : RayClassModulus F)
    (x : NumberField.IdeleGroup (𝓞 F) F) (a : Fˣ)
    (ha : NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a * x ∈ d1IdeleCongrOneSubgroup m) :
    d1IdeleToRayClassFun m x =
      d1IdeleRayClass m ⟨NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a * x, ha⟩ := by
  exact d1IdeleRayClass_eq_adjusted m x
    (Classical.choose (d1_exists_adjusted_idele m x)) a
    (Classical.choose_spec (d1_exists_adjusted_idele m x)) ha

set_option maxHeartbeats 1000000 in
private noncomputable def d1IdeleToRayClass (m : RayClassModulus F) :
    NumberField.IdeleGroup (𝓞 F) F →* RayClassGroup m where
  toFun := d1IdeleToRayClassFun m
  map_one' := by
    rw [d1IdeleToRayClassFun_eq m 1 1 (by simp)]
    simpa using d1IdeleRayClass_unitEmbedding m 1 (by simp)
  map_mul' x y := by
    obtain ⟨a, ha⟩ := d1_exists_adjusted_idele m x
    obtain ⟨b, hb⟩ := d1_exists_adjusted_idele m y
    have hmul : NumberField.IdeleGroup.unitEmbedding (𝓞 F) F (a * b) * (x * y) =
        NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a * x *
          (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F b * y) := by
      rw [map_mul, mul_mul_mul_comm]
    have hab : NumberField.IdeleGroup.unitEmbedding (𝓞 F) F (a * b) * (x * y) ∈
        d1IdeleCongrOneSubgroup m := by
      rw [hmul]
      exact (d1IdeleCongrOneSubgroup m).mul_mem ha hb
    rw [d1IdeleToRayClassFun_eq m (x * y) (a * b) hab,
      d1IdeleToRayClassFun_eq m x a ha, d1IdeleToRayClassFun_eq m y b hb,
      ← map_mul]
    exact congrArg (d1IdeleRayClass m) (Subtype.ext hmul)

private theorem d1IdeleToRayClass_unitEmbedding (m : RayClassModulus F) (a : Fˣ) :
    d1IdeleToRayClass m (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a) = 1 := by
  change d1IdeleToRayClassFun m (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a) = 1
  have ha : NumberField.IdeleGroup.unitEmbedding (𝓞 F) F (a⁻¹) *
      NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a ∈ d1IdeleCongrOneSubgroup m := by
    simp
  rw [d1IdeleToRayClassFun_eq m (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a) a⁻¹ ha]
  simpa using d1IdeleRayClass_unitEmbedding m 1 (by simp)

private noncomputable def d1RayClassQuotient (m : RayClassModulus F) :
    IdeleClassGroup (𝓞 F) F →* RayClassGroup m :=
  QuotientGroup.lift (NumberField.IdeleGroup.principalSubgroup (𝓞 F) F)
    (d1IdeleToRayClass m) (by
      rintro _ ⟨a, rfl⟩
      exact MonoidHom.mem_ker.mpr (d1IdeleToRayClass_unitEmbedding m a))

private theorem d1RayClassQuotient_mk (m : RayClassModulus F)
    (x : NumberField.IdeleGroup (𝓞 F) F) :
    d1RayClassQuotient m (QuotientGroup.mk x) = d1IdeleToRayClass m x := by
  simp [d1RayClassQuotient]

private theorem d1RayClassQuotient_comp_mk (m : RayClassModulus F) :
    (d1RayClassQuotient m).comp
      (QuotientGroup.mk' (NumberField.IdeleGroup.principalSubgroup (𝓞 F) F)) =
      d1IdeleToRayClass m := by
  ext x
  simp [d1RayClassQuotient]

private def d1AdeleRayOpenSet (m : RayClassModulus F) :
    Set (AdeleRing (𝓞 F) F) :=
  {a | (∀ v : FinPlace F, a.2 v ∈ v.adicCompletionIntegers F) ∧
    (∀ v, v ∈ m.finitePart.support →
      Valued.v ((a.2 v : v.adicCompletion F) - 1) ≤
        WithZero.exp (-(m.finitePart v : ℤ))) ∧
    ∀ w : RayClassRealPlace F, w ∈ m.infinitePart →
      0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 (a.1 w.1)}

private theorem d1AdeleRayOpenSet_isOpen (m : RayClassModulus F) :
    IsOpen (d1AdeleRayOpenSet m) := by
  classical
  have hInt : IsOpen {a : AdeleRing (𝓞 F) F |
      ∀ v : FinPlace F, a.2 v ∈ v.adicCompletionIntegers F} :=
    (RestrictedProduct.isOpen_forall_mem fun v : FinPlace F =>
      Valued.isOpen_valuationSubring _).preimage continuous_snd
  have hBound : IsOpen {a : AdeleRing (𝓞 F) F |
      ∀ v, v ∈ m.finitePart.support →
        Valued.v ((a.2 v : v.adicCompletion F) - 1) ≤
          WithZero.exp (-(m.finitePart v : ℤ))} := by
    have hset : {a : AdeleRing (𝓞 F) F |
        ∀ v, v ∈ m.finitePart.support →
          Valued.v ((a.2 v : v.adicCompletion F) - 1) ≤
            WithZero.exp (-(m.finitePart v : ℤ))} =
        ⋂ v ∈ m.finitePart.support, {a : AdeleRing (𝓞 F) F |
          Valued.v ((a.2 v : v.adicCompletion F) - 1) ≤
            WithZero.exp (-(m.finitePart v : ℤ))} := by
      ext a
      simp
    rw [hset]
    exact isOpen_biInter_finset fun v _ =>
      (v.isOpen_setOf_valued_le (K := F) WithZero.exp_ne_zero).preimage
        (f := fun a : AdeleRing (𝓞 F) F => (a.2 v : v.adicCompletion F) - 1)
        (((RestrictedProduct.continuous_eval v).comp continuous_snd).sub continuous_const)
  have hPos : IsOpen {a : AdeleRing (𝓞 F) F |
      ∀ w : RayClassRealPlace F, w ∈ m.infinitePart →
        0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 (a.1 w.1)} := by
    have hset : {a : AdeleRing (𝓞 F) F |
        ∀ w : RayClassRealPlace F, w ∈ m.infinitePart →
          0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 (a.1 w.1)} =
        ⋂ w ∈ m.infinitePart, {a : AdeleRing (𝓞 F) F |
          0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 (a.1 w.1)} := by
      ext a
      simp
    rw [hset]
    exact isOpen_biInter_finset fun w _ =>
      isOpen_lt continuous_const
        ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal w.2).continuous.comp
          ((continuous_apply w.1).comp continuous_fst))
  change IsOpen (({a : AdeleRing (𝓞 F) F |
      ∀ v : FinPlace F, a.2 v ∈ v.adicCompletionIntegers F} : Set _) ∩
    ({a : AdeleRing (𝓞 F) F |
      ∀ v, v ∈ m.finitePart.support →
        Valued.v ((a.2 v : v.adicCompletion F) - 1) ≤
          WithZero.exp (-(m.finitePart v : ℤ))} ∩
    {a : AdeleRing (𝓞 F) F |
      ∀ w : RayClassRealPlace F, w ∈ m.infinitePart →
        0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 (a.1 w.1)}))
  exact hInt.inter (hBound.inter hPos)

private def d1IdeleOpenNeighborhood (m : RayClassModulus F) :
    Set (NumberField.IdeleGroup (𝓞 F) F) :=
  (fun x : NumberField.IdeleGroup (𝓞 F) F => (x : AdeleRing (𝓞 F) F)) ⁻¹'
      d1AdeleRayOpenSet m ∩
    (fun x : NumberField.IdeleGroup (𝓞 F) F =>
      ((x⁻¹ : NumberField.IdeleGroup (𝓞 F) F) : AdeleRing (𝓞 F) F)) ⁻¹' d1AdeleRayOpenSet m

set_option maxHeartbeats 1000000 in
private theorem d1IdeleOpenNeighborhood_isOpen (m : RayClassModulus F) :
    IsOpen (d1IdeleOpenNeighborhood m) := by
  have hcoe : Continuous fun x : NumberField.IdeleGroup (𝓞 F) F => (x : AdeleRing (𝓞 F) F) :=
    Units.continuous_val
  have hcoeInv : Continuous fun x : NumberField.IdeleGroup (𝓞 F) F =>
      ((x⁻¹ : NumberField.IdeleGroup (𝓞 F) F) : AdeleRing (𝓞 F) F) :=
    Units.continuous_val.comp continuous_inv
  exact (d1AdeleRayOpenSet_isOpen m).preimage hcoe |>.inter
    ((d1AdeleRayOpenSet_isOpen m).preimage hcoeInv)

private theorem d1_local_unit_valued_eq_one (v : FinPlace F)
    (u : (v.adicCompletion F)ˣ)
    (hu : (u : v.adicCompletion F) ∈ v.adicCompletionIntegers F)
    (huinv : ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈
      v.adicCompletionIntegers F) :
    Valued.v (u : v.adicCompletion F) = 1 := by
  have huVal : Valued.v (u : v.adicCompletion F) ≤ 1 := by
    simpa only [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] using hu
  have huinvVal : Valued.v ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ≤ 1 := by
    simpa only [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] using huinv
  have hinvVal : (Valued.v (u : v.adicCompletion F))⁻¹ ≤ 1 := by
    simpa [Units.val_inv_eq_inv_val, map_inv₀] using huinvVal
  have hpos : 0 < Valued.v (u : v.adicCompletion F) :=
    (Valuation.pos_iff Valued.v).2 u.ne_zero
  exact le_antisymm huVal ((inv_le_one₀ hpos).mp hinvVal)

private theorem d1IdeleOpenNeighborhood_data (m : RayClassModulus F)
    (x : NumberField.IdeleGroup (𝓞 F) F) (hx : x ∈ d1IdeleOpenNeighborhood m) :
    x ∈ d1IdeleCongrOneSubgroup m ∧ d1IdeleIdealHom x = 1 := by
  change ((x : AdeleRing (𝓞 F) F) ∈ d1AdeleRayOpenSet m) ∧
    (((x⁻¹ : NumberField.IdeleGroup (𝓞 F) F) : AdeleRing (𝓞 F) F) ∈ d1AdeleRayOpenSet m) at hx
  rcases hx with ⟨hx, hxi⟩
  rcases hx with ⟨hxInt, hxBound, hxPos⟩
  rcases hxi with ⟨hxiInt, hxiBound, hxiPos⟩
  have huInt (v : FinPlace F) :
      (ideleFiniteCoord v x : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
    simpa only [ideleFiniteCoord_apply] using hxInt v
  have huInvInt (v : FinPlace F) :
      (((ideleFiniteCoord v x)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈
        v.adicCompletionIntegers F := by
    have h := hxiInt v
    simpa only [← ideleFiniteCoord_apply, map_inv, Units.val_inv_eq_inv_val] using h
  have hlocal (v : FinPlace F) : Valued.v (ideleFiniteCoord v x : v.adicCompletion F) = 1 :=
    d1_local_unit_valued_eq_one v (ideleFiniteCoord v x) (huInt v) (huInvInt v)
  have hxSub : x ∈ d1IdeleCongrOneSubgroup m := by
    refine ⟨fun v hv => ?_, fun w hw => ?_⟩
    · exact (ArtinPrimitiveRoots.Proofs.hk_misc_p.d1_mem_rayLocalHigherUnitGroup_iff
        v (m.finitePart v) (ideleFiniteCoord v x)).mpr
          ⟨huInt v, huInvInt v, hxBound v hv⟩
    · simpa [ideleInfiniteCoord] using hxPos w hw
  have horder (v : FinPlace F) :
      Dictionary.adicOrd (NumberField.IdeleGroup.toFiniteIdele (𝓞 F) F x) v = 0 := by
    rw [Dictionary.adicOrd_eq_zero_iff]
    simpa only [NumberField.IdeleGroup.coe_toFiniteIdele, ← ideleFiniteCoord_apply] using hlocal v
  have hI : d1IdeleIdealHom x = 1 := by
    change Dictionary.toFractionalIdeal (NumberField.IdeleGroup.toFiniteIdele (𝓞 F) F x) = 1
    exact (Dictionary.toFractionalIdeal_eq_one_iff).2 horder
  exact ⟨hxSub, hI⟩

private theorem d1IdeleToRayClass_one_of_openNeighborhood (m : RayClassModulus F)
    (x : NumberField.IdeleGroup (𝓞 F) F) (hx : x ∈ d1IdeleOpenNeighborhood m) :
    d1IdeleToRayClass m x = 1 := by
  obtain ⟨hxSub, hI⟩ := d1IdeleOpenNeighborhood_data m x hx
  have hOneSub : NumberField.IdeleGroup.unitEmbedding (𝓞 F) F 1 * x ∈
      d1IdeleCongrOneSubgroup m := by simpa using hxSub
  have hrep : d1IdeleRayClass m ⟨NumberField.IdeleGroup.unitEmbedding (𝓞 F) F 1 * x, hOneSub⟩ =
      d1IdeleRayClass m ⟨x, hxSub⟩ := by
    have heq : (⟨NumberField.IdeleGroup.unitEmbedding (𝓞 F) F 1 * x, hOneSub⟩ :
        d1IdeleCongrOneSubgroup m) = ⟨x, hxSub⟩ := by
      apply Subtype.ext
      simp
    exact congrArg (d1IdeleRayClass m) heq
  change d1IdeleToRayClassFun m x = 1
  rw [d1IdeleToRayClassFun_eq m x 1 hOneSub]
  rw [hrep]
  exact d1IdeleRayClass_one_of_ideal_one m ⟨x, hxSub⟩ hI

private theorem d1_continuous_of_isOpen_ker {G H : Type*} [Group G] [MulOneClass H]
    [TopologicalSpace G] [TopologicalSpace H] [SeparatelyContinuousMul G]
    (f : G →* H) (hf : IsOpen (f.ker : Set G)) : Continuous f := by
  refine continuous_iff_continuousAt.mpr fun x => tendsto_const_nhds.congr' ?_
  have hcoset : ∀ᶠ y in 𝓝 x, x⁻¹ * y ∈ f.ker := by
    have hmul : Tendsto (fun y => x⁻¹ * y) (𝓝 x) (𝓝 1) := by
      simpa using (continuous_const_mul x⁻¹).tendsto x
    exact hmul.eventually (Filter.eventually_mem_set.mpr (hf.mem_nhds (one_mem f.ker)))
  filter_upwards [hcoset] with y hy
  calc
    f x = f x * f (x⁻¹ * y) := by rw [MonoidHom.mem_ker.mp hy, mul_one]
    _ = f y := by rw [← map_mul, mul_inv_cancel_left]

private theorem d1RayClassPullback_continuous (m : RayClassModulus F)
    (η : RayClassGroup m →* ℂˣ) :
    Continuous (η.comp (d1RayClassQuotient m)) := by
  classical
  let N := NumberField.IdeleGroup.principalSubgroup (𝓞 F) F
  let q : NumberField.IdeleGroup (𝓞 F) F → IdeleClassGroup (𝓞 F) F := QuotientGroup.mk' N
  let ψ := η.comp (d1RayClassQuotient m)
  have hUOpen : IsOpen (Set.image q (d1IdeleOpenNeighborhood m)) := by
    exact QuotientGroup.isOpenMap_coe (d1IdeleOpenNeighborhood m)
      (d1IdeleOpenNeighborhood_isOpen m)
  have hAone : (1 : AdeleRing (𝓞 F) F) ∈ d1AdeleRayOpenSet m := by
    change (∀ v : FinPlace F,
        (1 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F) ∧
      (∀ v, v ∈ m.finitePart.support →
        Valued.v (((1 : FiniteAdeleRing (𝓞 F) F) v : v.adicCompletion F) - 1) ≤
          WithZero.exp (-(m.finitePart v : ℤ))) ∧
      ∀ w : RayClassRealPlace F, w ∈ m.infinitePart →
        0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
          ((1 : InfiniteAdeleRing F) w.1)
    constructor
    · intro v
      simp
    · constructor
      · intro v hv
        simp
      · intro w hw
        have hone : (1 : InfiniteAdeleRing F) w.1 = 1 := rfl
        rw [hone]
        norm_num
  have hOneU : (1 : NumberField.IdeleGroup (𝓞 F) F) ∈ d1IdeleOpenNeighborhood m := by
    change (1 : AdeleRing (𝓞 F) F) ∈ d1AdeleRayOpenSet m ∧
      (((1 : NumberField.IdeleGroup (𝓞 F) F)⁻¹ : NumberField.IdeleGroup (𝓞 F) F) :
        AdeleRing (𝓞 F) F) ∈ d1AdeleRayOpenSet m
    simp only [inv_one]
    exact ⟨hAone, hAone⟩
  have hOneImage : (1 : IdeleClassGroup (𝓞 F) F) ∈
      Set.image q (d1IdeleOpenNeighborhood m) := by
    exact ⟨1, hOneU, by simp [q]⟩
  have hImageKer : Set.image q (d1IdeleOpenNeighborhood m) ⊆ ψ.ker := by
    rintro z ⟨x, hx, rfl⟩
    change η (d1RayClassQuotient m (QuotientGroup.mk x)) = 1
    rw [d1RayClassQuotient_mk]
    change η (d1IdeleToRayClass m x) = 1
    rw [d1IdeleToRayClass_one_of_openNeighborhood m x hx]
    simp
  have hkerNhds : (ψ.ker : Set (IdeleClassGroup (𝓞 F) F)) ∈ 𝓝 1 :=
    Filter.mem_of_superset (hUOpen.mem_nhds hOneImage) hImageKer
  exact d1_continuous_of_isOpen_ker ψ
    (Subgroup.isOpen_of_mem_nhds ψ.ker hkerNhds)

private theorem d1_localIdele_rayClass_one (m : RayClassModulus F) (v : FinPlace F)
    (u : (v.adicCompletion F)ˣ)
    (hu : (u : v.adicCompletion F) ∈ v.adicCompletionIntegers F)
    (huinv : ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈
      v.adicCompletionIntegers F)
    (hbound : Valued.v ((u : v.adicCompletion F) - 1) ≤
      WithZero.exp (-(m.finitePart v : ℤ))) :
    d1IdeleToRayClass m (NumberField.IdeleGroup.ofAdicCompletion (𝓞 F) F v u) = 1 := by
  let y := NumberField.IdeleGroup.ofAdicCompletion (𝓞 F) F v u
  have hySub : y ∈ d1IdeleCongrOneSubgroup m := by
    refine ⟨fun w hw => ?_, fun w hw => ?_⟩
    · by_cases hEq : w = v
      · subst w
        simpa [y] using
          (ArtinPrimitiveRoots.Proofs.hk_misc_p.d1_mem_rayLocalHigherUnitGroup_iff
            v (m.finitePart v) u).mpr ⟨hu, huinv, hbound⟩
      · simpa [y, ideleFiniteCoord_ofAdicCompletion_of_ne w v hEq] using
          (rayLocalHigherUnitGroup w (m.finitePart w)).one_mem
    · have hcoord : ideleInfiniteCoord w.1 y = 1 := by
        rw [← ideleInfiniteCoordUnit_apply, ideleInfiniteCoordUnit_ofAdicCompletion]
        simp
      rw [hcoord]
      simp
  have hval (w : FinPlace F) : Valued.v (ideleFiniteCoord w y : w.adicCompletion F) = 1 := by
    by_cases hEq : w = v
    · subst w
      simpa [y] using d1_local_unit_valued_eq_one v u hu huinv
    · simp [y, ideleFiniteCoord_ofAdicCompletion_of_ne w v hEq]
  have horder (w : FinPlace F) :
      Dictionary.adicOrd (NumberField.IdeleGroup.toFiniteIdele (𝓞 F) F y) w = 0 := by
    rw [Dictionary.adicOrd_eq_zero_iff]
    simpa only [NumberField.IdeleGroup.coe_toFiniteIdele, ← ideleFiniteCoord_apply] using hval w
  have hI : d1IdeleIdealHom y = 1 := by
    change Dictionary.toFractionalIdeal (NumberField.IdeleGroup.toFiniteIdele (𝓞 F) F y) = 1
    exact (Dictionary.toFractionalIdeal_eq_one_iff).2 horder
  have h1Sub : NumberField.IdeleGroup.unitEmbedding (𝓞 F) F 1 * y ∈ d1IdeleCongrOneSubgroup m := by
    simpa using hySub
  change d1IdeleToRayClassFun m y = 1
  rw [d1IdeleToRayClassFun_eq m y 1 h1Sub]
  have hrep : d1IdeleRayClass m ⟨NumberField.IdeleGroup.unitEmbedding (𝓞 F) F 1 * y, h1Sub⟩ =
      d1IdeleRayClass m ⟨y, hySub⟩ := by
    apply congrArg (d1IdeleRayClass m)
    apply Subtype.ext
    simp
  rw [hrep]
  exact d1IdeleRayClass_one_of_ideal_one m ⟨y, hySub⟩ hI

private theorem d1_localIdele_rayClassQuotient_one (m : RayClassModulus F) (v : FinPlace F)
    (u : (v.adicCompletion F)ˣ)
    (hu : (u : v.adicCompletion F) ∈ v.adicCompletionIntegers F)
    (huinv : ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈
      v.adicCompletionIntegers F)
    (hbound : Valued.v ((u : v.adicCompletion F) - 1) ≤
      WithZero.exp (-(m.finitePart v : ℤ))) :
    d1RayClassQuotient m
      (QuotientGroup.mk (NumberField.IdeleGroup.ofAdicCompletion (𝓞 F) F v u)) = 1 := by
  rw [d1RayClassQuotient_mk]
  exact d1_localIdele_rayClass_one m v u hu huinv hbound

private noncomputable def d1RayClassHeckeChar (m : RayClassModulus F)
    (η : RayClassGroup m →* ℂˣ) : HeckeChar F := {
  toMonoidHom := η.comp (d1RayClassQuotient m)
  continuous_toFun := d1RayClassPullback_continuous m η }

private theorem d1_rayClassCharacter_pullback (m : RayClassModulus F)
    (η : RayClassGroup m →* ℂˣ) :
    IsOfFinOrder (d1RayClassHeckeChar m η) ∧
      (d1RayClassHeckeChar m η).ConductorDvd (modulusIdeal m) ∧
      ∀ v : FinPlace F, v ∉ m.finitePart.support →
        (d1RayClassHeckeChar m η).UnramifiedAt v := by
  classical
  let χ : HeckeChar F := d1RayClassHeckeChar m η
  have hχfin : IsOfFinOrder χ := by
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨Nat.card (RayClassGroup m), Nat.card_pos, ?_⟩
    apply ContinuousMonoidHom.ext
    intro c
    rw [ContinuousMonoidHom.pow_apply]
    change (η (d1RayClassQuotient m c)) ^ Nat.card (RayClassGroup m) = 1
    rw [← map_pow, pow_card_eq_one', map_one]
  have hcond : χ.ConductorDvd (modulusIdeal m) := by
    intro v u hu huinv hbound
    change η (d1RayClassQuotient m
      (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u)) = 1
    have hbound' : Valued.v ((u : v.adicCompletion F) - 1) ≤
        WithZero.exp (-(m.finitePart v : ℤ)) := by
      simpa [idealExp_modulusIdeal] using hbound
    have hq := d1_localIdele_rayClassQuotient_one m v u hu huinv hbound'
    simpa using congrArg η hq
  refine ⟨hχfin, hcond, ?_⟩
  intro v hv u hu huinv
  have huVal : Valued.v (u : v.adicCompletion F) ≤ 1 := by
    simpa only [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] using hu
  have hsub : Valued.v ((u : v.adicCompletion F) - 1) ≤ 1 := by
    calc
      Valued.v ((u : v.adicCompletion F) - 1) ≤
      max (Valued.v (u : v.adicCompletion F)) (Valued.v (1 : v.adicCompletion F)) :=
        Valuation.map_sub _ _ _
      _ ≤ 1 := max_le huVal (by simp)
  have hbound : Valued.v ((u : v.adicCompletion F) - 1) ≤
      WithZero.exp (-(A1.idealExp v (modulusIdeal m) : ℤ)) := by
    rw [idealExp_modulusIdeal]
    have hexp : m.finitePart v = 0 := Finsupp.notMem_support_iff.mp hv
    simpa [hexp] using hsub
  exact hcond v u hu huinv hbound

private noncomputable def d1UniformizerUnit (v : FinPlace F) : (v.adicCompletion F)ˣ :=
  ArtinPrimitiveRoots.A1.toLoc v
    (Units.mk0 (ArtinPrimitiveRoots.A1.unif (F := F) v)
      (ArtinPrimitiveRoots.A1.unif_ne_zero (F := F) v))

private theorem d1UniformizerUnit_valued (v : FinPlace F) :
    Valued.v (d1UniformizerUnit v : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
  change Valued.v (algebraMap F (v.adicCompletion F)
    (ArtinPrimitiveRoots.A1.unif (F := F) v)) = _
  have hmap : algebraMap F (v.adicCompletion F) (ArtinPrimitiveRoots.A1.unif (F := F) v) =
      (ArtinPrimitiveRoots.A1.unif (F := F) v : v.adicCompletion F) := by
    simpa using congrFun
      (HeightOneSpectrum.algebraMap_adicCompletion (S := F) (K := F) (v := v))
      (ArtinPrimitiveRoots.A1.unif (F := F) v)
  rw [hmap]
  rw [v.valuedAdicCompletion_eq_valuation'
    (ArtinPrimitiveRoots.A1.unif (F := F) v)]
  simpa [ArtinPrimitiveRoots.A1.unif] using
    (HeightOneSpectrum.valuation_exists_uniformizer F v).choose_spec

private theorem d1IdeleIdealHom_uniformizer (v : FinPlace F) :
    d1IdeleIdealHom (NumberField.IdeleGroup.ofAdicCompletion (𝓞 F) F v (d1UniformizerUnit v)) =
      finitePrimeFractionalIdeal v := by
  let y := NumberField.IdeleGroup.ofAdicCompletion (𝓞 F) F v (d1UniformizerUnit v)
  have hcount (w : FinPlace F) :
      FractionalIdeal.count F w (d1IdeleIdealHom y :
        FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
        FractionalIdeal.count F w
          (finitePrimeFractionalIdeal v : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
    rw [d1IdeleIdealHom, MonoidHom.comp_apply, Dictionary.count_coe_toFractionalIdeal]
    rw [Dictionary.adicOrd_def, NumberField.IdeleGroup.coe_toFiniteIdele,
      ← ideleFiniteCoord_apply]
    by_cases hw : w = v
    · subst w
      rw [ideleFiniteCoord_ofAdicCompletion, d1UniformizerUnit_valued]
      simp [WithZero.log_exp]
      have hself : FractionalIdeal.count F v
          (finitePrimeFractionalIdeal v : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 1 := by
        simpa [finitePrimeFractionalIdeal] using FractionalIdeal.count_self F v
      rw [hself]
    · rw [ideleFiniteCoord_ofAdicCompletion_of_ne w v hw]
      simp
      have hother : FractionalIdeal.count F w
          (finitePrimeFractionalIdeal v : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0 := by
        simpa [finitePrimeFractionalIdeal] using
          (FractionalIdeal.count_maximal_coprime F w (Ne.symm hw))
      rw [hother]
  rw [FractionalIdeal.finprod_unitOfPrime_zpow_count (d1IdeleIdealHom y),
    FractionalIdeal.finprod_unitOfPrime_zpow_count (finitePrimeFractionalIdeal v)]
  apply finprod_congr
  intro w
  rw [hcount w]

private theorem d1IdeleToRayClass_uniformizer (m : RayClassModulus F) (v : FinPlace F)
    (hv : v ∉ m.finitePart.support) :
    d1IdeleToRayClass m
        (NumberField.IdeleGroup.ofAdicCompletion (𝓞 F) F v (d1UniformizerUnit v)) =
      rayClassOfFinitePrime m v hv := by
  let y := NumberField.IdeleGroup.ofAdicCompletion (𝓞 F) F v (d1UniformizerUnit v)
  have hySub : y ∈ d1IdeleCongrOneSubgroup m := by
    refine ⟨fun w hw => ?_, fun w hw => ?_⟩
    · have hne : w ≠ v := by
        intro h
        exact hv (h ▸ hw)
      simpa [y, ideleFiniteCoord_ofAdicCompletion_of_ne w v hne] using
        (rayLocalHigherUnitGroup w (m.finitePart w)).one_mem
    · have hcoord : ideleInfiniteCoord w.1 y = 1 := by
        rw [← ideleInfiniteCoordUnit_apply, ideleInfiniteCoordUnit_ofAdicCompletion]
        simp
      rw [hcoord]
      simp
  have h1Sub : NumberField.IdeleGroup.unitEmbedding (𝓞 F) F 1 * y ∈ d1IdeleCongrOneSubgroup m := by
    simpa using hySub
  change d1IdeleToRayClassFun m y = _
  rw [d1IdeleToRayClassFun_eq m y 1 h1Sub]
  have hrep : d1IdeleRayClass m ⟨NumberField.IdeleGroup.unitEmbedding (𝓞 F) F 1 * y, h1Sub⟩ =
      d1IdeleRayClass m ⟨y, hySub⟩ := by
    apply congrArg (d1IdeleRayClass m)
    apply Subtype.ext
    simp
  rw [hrep, d1IdeleRayClass_apply]
  have hsub : (⟨d1IdeleIdealHom y, d1IdeleIdealPrimeTo m y hySub⟩ :
      rayClassPrimeToIdeals m) =
        ⟨finitePrimeFractionalIdeal v, finitePrimeFractionalIdeal_mem_primeTo m v hv⟩ := by
    apply Subtype.ext
    exact d1IdeleIdealHom_uniformizer v
  rw [hsub]
  rfl

private theorem d1_isCoprimeTo_prime (m : RayClassModulus F) (v : FinPlace F)
    (hv : v ∉ m.finitePart.support) : IsCoprimeTo m v.asIdeal := by
  refine ⟨v.ne_bot, ?_⟩
  intro w hw
  have hwv : w ≠ v := by
    intro h
    exact hv (h ▸ hw)
  simpa [idealUnit] using
    (FractionalIdeal.count_maximal_coprime F w (Ne.symm hwv))

private theorem d1_rayClassOfFinitePrime_eq_rayClass (m : RayClassModulus F)
    (v : FinPlace F) (hv : v ∉ m.finitePart.support) (hcop : IsCoprimeTo m v.asIdeal) :
    rayClassOfFinitePrime m v hv = rayClass m v.asIdeal hcop := by
  classical
  unfold rayClassOfFinitePrime rayClass
  congr 1

private theorem d1_rayClassCharacter_primeValue (m : RayClassModulus F)
    (η : RayClassGroup m →* ℂˣ) (v : FinPlace F)
    (hv : v ∉ m.finitePart.support) :
    (d1RayClassHeckeChar m η).UnramifiedAt v ∧
      (d1RayClassHeckeChar m η).primeValue v = charValue η v.asIdeal := by
  classical
  obtain ⟨_, _, hunram⟩ := d1_rayClassCharacter_pullback m η
  have hcop := d1_isCoprimeTo_prime m v hv
  have hclass : d1RayClassQuotient m
      (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v (d1UniformizerUnit v)) =
        rayClass m v.asIdeal hcop := by
    calc
      d1RayClassQuotient m
          (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v (d1UniformizerUnit v)) =
          d1IdeleToRayClass m
            (NumberField.IdeleGroup.ofAdicCompletion (𝓞 F) F v (d1UniformizerUnit v)) := by
              simpa only [IdeleClassGroup.ofAdicCompletion, MonoidHom.comp_apply] using
                DFunLike.congr_fun (d1RayClassQuotient_comp_mk m)
                  (NumberField.IdeleGroup.ofAdicCompletion (𝓞 F) F v (d1UniformizerUnit v))
      _ = rayClassOfFinitePrime m v hv := d1IdeleToRayClass_uniformizer m v hv
      _ = rayClass m v.asIdeal hcop :=
        d1_rayClassOfFinitePrime_eq_rayClass m v hv hcop
  have hloc : (d1RayClassHeckeChar m η).loc v (d1UniformizerUnit v) =
      η (rayClass m v.asIdeal hcop) := by
    change η (d1RayClassQuotient m
      (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v (d1UniformizerUnit v))) = _
    rw [hclass]
  refine ⟨hunram v hv, ?_⟩
  simp only [HeckeChar.primeValue, hunram v hv, if_pos]
  change (((d1RayClassHeckeChar m η).loc v (d1UniformizerUnit v) : ℂˣ) : ℂ) =
    charValue η v.asIdeal
  rw [hloc]
  simp [charValue, hcop]

/-- **DICT-1.** A ray-class character gives a finite-order idelic character with the same values at
the primes prime to `𝔪`, unramified there, and with conductor dividing `modulusIdeal 𝔪`.
Its local components at `S` (A1's `SData.LS`, `vartheta`) are the `S`-adic component of `η`.
Consumers: `HeckeBoundary.a2_zero_free_every_continuation` (proof: builds A1's `condη`, `SData`,
`ϑ = Λ⁻¹G⁻¹χ`, `Bm`); A1 `vartheta_S`; A2 `def:rf-S-character`, `prop:euler-product`,
`po:H-product`. -/
theorem exists_heckeChar_of_rayClass (m : RayClassModulus F) (η : RayClassGroup m →* ℂˣ) :
    ∃ χ : HeckeChar F, IsOfFinOrder χ ∧ χ.ConductorDvd (modulusIdeal m) ∧
      ∀ v : FinPlace F, v ∉ m.finitePart.support →
        χ.UnramifiedAt v ∧ χ.primeValue v = charValue η v.asIdeal := by
  let χ := d1RayClassHeckeChar m η
  obtain ⟨hfin, hcond, _⟩ := d1_rayClassCharacter_pullback m η
  refine ⟨χ, hfin, hcond, ?_⟩
  intro v hv
  simpa [χ] using d1_rayClassCharacter_primeValue m η v hv

theorem normalizedFactor_not_mem_support {m : RayClassModulus F}
    {I : Ideal (𝓞 F)} (hI : IsCoprimeTo m I) {P : Ideal (𝓞 F)}
    (hP : P ∈ UniqueFactorizationMonoid.normalizedFactors I) :
    ∃ v : FinPlace F, v.asIdeal = P ∧ v ∉ m.finitePart.support := by
  rcases hI with ⟨hI0, hcop⟩
  have hP' := (Ideal.mem_normalizedFactors_iff hI0).1 hP
  have hP0 : P ≠ ⊥ := by
    intro hzero
    apply hI0
    exact le_antisymm (hzero ▸ hP'.2) bot_le
  let v : FinPlace F := ⟨P, hP'.1, hP0⟩
  refine ⟨v, rfl, ?_⟩
  intro hv
  have hcountI : FractionalIdeal.count F v
      (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0 := by
    simpa [idealUnit] using hcop v hv
  rw [FractionalIdeal.count_coe F v hI0,
    Ideal.count_associates_factors_eq hI0 v.isPrime v.ne_bot] at hcountI
  have hcountZero : Multiset.count v.asIdeal
      (UniqueFactorizationMonoid.normalizedFactors I) = 0 := by
    exact_mod_cast hcountI
  have hcountpos : 0 < Multiset.count P (UniqueFactorizationMonoid.normalizedFactors I) :=
    Multiset.count_pos.mpr hP
  have hcountpos' : 0 < Multiset.count v.asIdeal
      (UniqueFactorizationMonoid.normalizedFactors I) := by
    simpa [v] using hcountpos
  omega

theorem charValue_eq_zero_of_mem_support {m : RayClassModulus F}
    (η : RayClassGroup m →* ℂˣ) {v : FinPlace F}
    (hv : v ∈ m.finitePart.support) : charValue η v.asIdeal = 0 := by
  classical
  have hnot : ¬ IsCoprimeTo m v.asIdeal := by
    rintro ⟨hI0, hcop⟩
    have hcount : FractionalIdeal.count F v
        (idealUnit v.asIdeal hI0 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0 :=
      hcop v hv
    have hcount' : FractionalIdeal.count F v
        (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 1 :=
      FractionalIdeal.count_self F v
    have : (0 : ℤ) = 1 := by simpa [idealUnit] using hcount.symm.trans hcount'
    omega
  simp [charValue, hnot]

/-- Ideal values agree on ideals prime to `𝔪` (multiplicativity on both sides).
Consumer: A1 `Bm` / A2 `lem:reflection-theta-representation` (`ϑ(𝔄)` with `ϑ` built from `χ`). -/
theorem idealValue_eq_charValue {m : RayClassModulus F} (η : RayClassGroup m →* ℂˣ)
    (χ : HeckeChar F) (hχ : ∀ v : FinPlace F, v ∉ m.finitePart.support →
      χ.UnramifiedAt v ∧ χ.primeValue v = charValue η v.asIdeal)
    (I : Ideal (𝓞 F)) (hI : IsCoprimeTo m I) : χ.idealValue I = charValue η I := by
  classical
  rcases hI with ⟨hI0, hcop⟩
  let fs := UniqueFactorizationMonoid.normalizedFactors I
  have hfactor (P : Ideal (𝓞 F)) (hP : P ∈ fs) :
      (if h : P.IsPrime ∧ P ≠ ⊥ then χ.primeValue ⟨P, h.1, h.2⟩ else 1) =
        charValue η P := by
    have hP' := (Ideal.mem_normalizedFactors_iff hI0).1 hP
    obtain ⟨v, hvP, hv⟩ := normalizedFactor_not_mem_support ⟨hI0, hcop⟩ hP
    have hP0 : P ≠ ⊥ := by rw [← hvP]; exact v.ne_bot
    have hval := (hχ v hv).2
    have hpair : P.IsPrime ∧ P ≠ ⊥ := ⟨hP'.1, hP0⟩
    rw [dif_pos hpair]
    have hv' : (⟨P, hpair.1, hpair.2⟩ : FinPlace F) = v :=
      HeightOneSpectrum.ext hvP.symm
    rw [hv']
    simpa [hvP] using hval
  have hcharTop : charValue η (⊤ : Ideal (𝓞 F)) = 1 := by
    classical
    have htop : IsCoprimeTo m (⊤ : Ideal (𝓞 F)) := by
      refine ⟨by simp, ?_⟩
      intro v hv
      simpa [idealUnit] using FractionalIdeal.count_one F v
    have hunitTop : idealUnit (⊤ : Ideal (𝓞 F)) htop.1 = 1 := by
      apply Units.ext
      simp [idealUnit]
    have hclassTop : rayClass m ⊤ htop = 1 := by
      have hsub : (⟨idealUnit ⊤ htop.1, htop.2⟩ : rayClassPrimeToIdeals m) = 1 := by
        apply Subtype.ext
        exact hunitTop
      simp [rayClass, hsub]
    simp [charValue, htop, hclassTop]
  have hprodChar (s : Multiset (Ideal (𝓞 F))) :
      (s.map (charValue η)).prod = charValue η s.prod := by
    induction s using Multiset.induction_on with
    | empty => simp [hcharTop]
    | cons P s ih => simp [Hecke.charValue_mul, ih]
  calc
    χ.idealValue I = (fs.map fun P =>
        if h : P.IsPrime ∧ P ≠ ⊥ then χ.primeValue ⟨P, h.1, h.2⟩ else 1).prod := rfl
    _ = (fs.map (charValue η)).prod := by
      exact congrArg Multiset.prod (Multiset.map_congr rfl fun P hP => hfactor P hP)
    _ = charValue η fs.prod := hprodChar fs
    _ = charValue η I := by rw [Ideal.prod_normalizedFactors_eq_self hI0]

open Classical in
/-- The partial L-series as an Euler product in A1's prime values (from
`Hecke.LSeriesRay_eulerProduct`).  Consumer: every place where the paper writes `L^S(·, χ)`
(A2 `prop:euler-product`, `zf:principal-row`, `prop:zero-density`). -/
theorem LSeriesRay_hasProd_primeValue {m : RayClassModulus F} (η : RayClassGroup m →* ℂˣ)
    (χ : HeckeChar F) (hχ : ∀ v : FinPlace F, v ∉ m.finitePart.support →
      χ.UnramifiedAt v ∧ χ.primeValue v = charValue η v.asIdeal) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun v : FinPlace F => if v ∈ m.finitePart.support then (1 : ℂ) else
      (1 - χ.primeValue v * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)
      (LSeriesRay η s) := by
  have heuler := Hecke.LSeriesRay_eulerProduct η hs
  apply heuler.congr_fun
  intro v
  by_cases hv : v ∈ m.finitePart.support
  · simp [hv, charValue_eq_zero_of_mem_support η hv]
  · simp [hv, (hχ v hv).2]

private theorem heckeLoc_eq_of_primeValue (χ χ' : HeckeChar F) (v : FinPlace F)
    (hχ : χ.UnramifiedAt v) (hχ' : χ'.UnramifiedAt v)
    (hprime : χ.primeValue v = χ'.primeValue v) (u : (v.adicCompletion F)ˣ) :
    χ.loc v u = χ'.loc v u := by
  classical
  let π : (v.adicCompletion F)ˣ :=
    toLoc v (Units.mk0 (unif v) (unif_ne_zero v))
  have hπ : χ.loc v π = χ'.loc v π := by
    apply Units.ext
    simpa [HeckeChar.primeValue, hχ, hχ', π] using hprime
  have hunif : v.valuation F (unif v) = WithZero.exp (-1 : ℤ) := by
    simpa [unif] using (HeightOneSpectrum.valuation_exists_uniformizer F v).choose_spec
  have hπval : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    calc
      Valued.v (π : v.adicCompletion F) =
          Valued.v (algebraMap F (v.adicCompletion F) (unif v)) := by
            simp [π, toLoc]
      _ = v.valuation F (unif v) := v.valuedAdicCompletion_eq_valuation' (unif v)
      _ = WithZero.exp (-1 : ℤ) := hunif
  have hval : Valued.v (u : v.adicCompletion F) ≠ 0 := by simpa using u.ne_zero
  let k : ℤ := -WithZero.log (Valued.v (u : v.adicCompletion F))
  have hpow : Valued.v ((π ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      Valued.v (u : v.adicCompletion F) := by
    calc
      Valued.v ((π ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
          Valued.v (π : v.adicCompletion F) ^ k := by simp
      _ = WithZero.exp (-k) := by
        rw [hπval]
        simpa [k] using (WithZero.exp_zsmul k (-1 : ℤ)).symm
      _ = Valued.v (u : v.adicCompletion F) := by
        simp [k, WithZero.exp_log hval]
  let u₀ : (v.adicCompletion F)ˣ := u * (π ^ k)⁻¹
  have hu₀val : Valued.v (u₀ : v.adicCompletion F) = 1 := by
    dsimp [u₀]
    rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀, hpow]
    exact mul_inv_cancel₀ hval
  have hu₀int : (u₀ : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hu₀val.le
  have hu₀invint : ((u₀⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈
      v.adicCompletionIntegers F := by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
      Units.val_inv_eq_inv_val, map_inv₀, hu₀val]
    simp
  have hχ₀ := hχ u₀ hu₀int hu₀invint
  have hχ'₀ := hχ' u₀ hu₀int hu₀invint
  have hπpow : χ.loc v (π ^ k) = χ'.loc v (π ^ k) := by
    simpa only [map_zpow] using congrArg (fun z : ℂˣ => z ^ k) hπ
  have hdecomp : u₀ * π ^ k = u := by
    dsimp [u₀]
    group
  calc
    χ.loc v u = χ.loc v (u₀ * π ^ k) := congrArg (χ.loc v) hdecomp.symm
    _ = χ.loc v u₀ * χ.loc v (π ^ k) := map_mul _ _ _
    _ = 1 * χ'.loc v (π ^ k) := by rw [hχ₀, hπpow]
    _ = χ'.loc v u₀ * χ'.loc v (π ^ k) := by rw [hχ'₀]
    _ = χ'.loc v (u₀ * π ^ k) := (map_mul _ _ _).symm
    _ = χ'.loc v u := congrArg (χ'.loc v) hdecomp

/-! ## §2 Idelic → ray class -/

private noncomputable def rayModulusFromIdeal (n : Ideal (𝓞 F)) (hn : n ≠ ⊥) :
    RayClassModulus F := by
  classical
  let eFun : FinPlace F → ℕ := fun v => A1.idealExp v n
  have heSupp : (Function.support eFun).Finite := by
    apply (Ideal.finite_factors hn).subset
    intro v hv
    have hcount :
        (Associates.mk v.asIdeal).count (Associates.mk n).factors ≠ 0 := by
      exact_mod_cast hv
    exact (Associates.count_ne_zero_iff_dvd hn v.irreducible).mp hcount
  let e : FinPlace F →₀ ℕ := Finsupp.ofSupportFinite eFun heSupp
  exact ⟨e, Finset.univ⟩

private theorem modulusIdeal_rayModulusFromIdeal (n : Ideal (𝓞 F)) (hn : n ≠ ⊥) :
    modulusIdeal (rayModulusFromIdeal n hn) = n := by
  classical
  let eFun : FinPlace F → ℕ := fun v => A1.idealExp v n
  let e : FinPlace F →₀ ℕ := Finsupp.ofSupportFinite eFun (by
    apply (Ideal.finite_factors hn).subset
    intro v hv
    have hcount :
        (Associates.mk v.asIdeal).count (Associates.mk n).factors ≠ 0 := by
      exact_mod_cast hv
    exact (Associates.count_ne_zero_iff_dvd hn v.irreducible).mp hcount)
  have he (v : FinPlace F) : e v = eFun v := by
    simp [e, Finsupp.ofSupportFinite_coe]
  change e.prod (fun v k => v.asIdeal ^ k) = n
  have hmul : Function.mulSupport (fun v : FinPlace F => v.asIdeal ^ eFun v) ⊆ e.support := by
    intro v hv
    by_contra hnot
    have hev : e v = 0 := Finsupp.notMem_support_iff.mp hnot
    have hzero : eFun v = 0 := by rw [← he v, hev]
    simp [Function.mem_mulSupport, hzero] at hv
  calc
    e.prod (fun v k => v.asIdeal ^ k) =
        ∏ v ∈ e.support, v.asIdeal ^ eFun v := by
      rw [Finsupp.prod]
      apply Finset.prod_congr rfl
      intro v hv
      rw [he]
    _ = ∏ᶠ v : FinPlace F, v.asIdeal ^ eFun v :=
      (finprod_eq_prod_of_mulSupport_subset _ hmul).symm
    _ = n := by
      simpa [eFun, A1.idealExp, IsDedekindDomain.HeightOneSpectrum.maxPowDividing] using
        Ideal.finprod_heightOneSpectrum_factorization hn

private noncomputable def completionIntegerUniformizer (v : FinPlace F) :
    v.adicCompletionIntegers F :=
  ⟨algebraMap F (v.adicCompletion F) (ArtinPrimitiveRoots.A1.unif (F := F) v), by
    change Valued.v (algebraMap F (v.adicCompletion F)
      (ArtinPrimitiveRoots.A1.unif (F := F) v)) ≤ 1
    have hmap : algebraMap F (v.adicCompletion F) (ArtinPrimitiveRoots.A1.unif (F := F) v) =
        (ArtinPrimitiveRoots.A1.unif (F := F) v : v.adicCompletion F) := by
      simpa using congrFun
        (HeightOneSpectrum.algebraMap_adicCompletion (S := F) (K := F) (v := v))
        (ArtinPrimitiveRoots.A1.unif (F := F) v)
    have hval := v.valuedAdicCompletion_eq_valuation'
      (ArtinPrimitiveRoots.A1.unif (F := F) v)
    have hunif : v.valuation F (ArtinPrimitiveRoots.A1.unif (F := F) v) =
        WithZero.exp (-1 : ℤ) := by
      simpa [ArtinPrimitiveRoots.A1.unif] using
        (HeightOneSpectrum.valuation_exists_uniformizer F v).choose_spec
    rw [hmap, hval, hunif]
    exact (WithZero.exp_le_one_iff).mpr (by norm_num)⟩

private theorem completionIntegerUniformizer_val (v : FinPlace F) :
  Valued.v (completionIntegerUniformizer v : v.adicCompletion F) =
      WithZero.exp (-1 : ℤ) := by
  change Valued.v (algebraMap F (v.adicCompletion F)
    (ArtinPrimitiveRoots.A1.unif (F := F) v)) = _
  have hmap : algebraMap F (v.adicCompletion F) (ArtinPrimitiveRoots.A1.unif (F := F) v) =
      (ArtinPrimitiveRoots.A1.unif (F := F) v : v.adicCompletion F) := by
    simpa using congrFun
      (HeightOneSpectrum.algebraMap_adicCompletion (S := F) (K := F) (v := v))
      (ArtinPrimitiveRoots.A1.unif (F := F) v)
  rw [hmap]
  rw [v.valuedAdicCompletion_eq_valuation'
    (ArtinPrimitiveRoots.A1.unif (F := F) v)]
  simpa [ArtinPrimitiveRoots.A1.unif] using
    (HeightOneSpectrum.valuation_exists_uniformizer F v).choose_spec

private theorem valued_sub_one_le_of_mem_rayLocalHigherUnitGroup (v : FinPlace F)
    (n : ℕ) (u : (v.adicCompletion F)ˣ)
    (hu : u ∈ rayLocalHigherUnitGroup v n) :
    (u : v.adicCompletion F) ∈ v.adicCompletionIntegers F ∧
      ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈
        v.adicCompletionIntegers F ∧
      Valued.v ((u : v.adicCompletion F) - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  classical
  let A : ValuationSubring (v.adicCompletion F) := v.adicCompletionIntegers F
  let J := IsLocalRing.maximalIdeal A
  let π : A := completionIntegerUniformizer v
  let vC : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  have hInt : vC.Integers A := by
    change vC.Integers vC.valuationSubring
    exact Valuation.valuationSubring.integers vC
  have hπval : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    simpa [π] using completionIntegerUniformizer_val v
  have hmax : J = Ideal.span {π} := by
    have hmaxSet : (J : Set A) = {x : A | Valued.v (x : v.adicCompletion F) < 1} := by
      ext x
      change x ∈ IsLocalRing.maximalIdeal A ↔ vC (x : v.adicCompletion F) < 1
      exact Valuation.mem_maximalIdeal_iff (v := vC)
    have hspanSet : (Ideal.span {π} : Set A) =
        {x : A | Valued.v (x : v.adicCompletion F) ≤ WithZero.exp (-1 : ℤ)} := by
      simpa [vC, hπval, ValuationSubring.algebraMap_apply] using
        hInt.coe_span_singleton_eq_setOfPred_le_v_algebraMap π
    have hsets : {x : A | Valued.v (x : v.adicCompletion F) < 1} =
        {x : A | Valued.v (x : v.adicCompletion F) ≤ WithZero.exp (-1 : ℤ)} := by
      ext x
      constructor
      · intro hx
        by_cases hx0 : x = 0
        · simp [hx0]
        · have hvx : Valued.v (x : v.adicCompletion F) ≠ 0 := by
            intro hz
            exact hx0 (Subtype.ext ((Valuation.zero_iff Valued.v).mp hz))
          have hxlt : Valued.v (x : v.adicCompletion F) < 1 := by
            simpa only [Set.mem_setOf_eq] using hx
          have hlog : WithZero.log (Valued.v (x : v.adicCompletion F)) < 0 := by
            apply WithZero.exp_lt_one_iff.mp
            simpa only [WithZero.exp_log hvx] using hxlt
          have hlog' : WithZero.log (Valued.v (x : v.adicCompletion F)) ≤ -1 := by omega
          calc
            Valued.v (x : v.adicCompletion F) =
                WithZero.exp (WithZero.log (Valued.v (x : v.adicCompletion F))) :=
                  (WithZero.exp_log hvx).symm
            _ ≤ WithZero.exp (-1 : ℤ) := WithZero.exp_le_exp.mpr hlog'
      · intro hx
        exact hx.trans_lt (WithZero.exp_lt_one_iff.mpr (by norm_num))
    exact SetLike.coe_injective (hmaxSet.trans (hsets.trans hspanSet.symm))
  have hπirr : Irreducible π :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).2 hmax
  have hpowSet (k : ℕ) : ((J ^ k : Ideal A) : Set A) =
      {x : A | Valued.v (x : v.adicCompletion F) ≤ WithZero.exp (-(k : ℤ))} := by
    rw [hInt.maximalIdeal_pow_eq_setOfPred_le_v_algebraMap_pow hπirr k]
    have hpv : (Valued.v (algebraMap A (v.adicCompletion F) π)) ^ k =
        WithZero.exp (-(k : ℤ)) := by
      simpa [ValuationSubring.algebraMap_apply] using (by
        rw [hπval]
        simpa using (WithZero.exp_zsmul (k : ℤ) (-1 : ℤ)).symm :
          (Valued.v (π : v.adicCompletion F)) ^ k = WithZero.exp (-(k : ℤ)))
    rw [hpv]
    ext x
    simp [ValuationSubring.algebraMap_apply, vC]
  rw [rayLocalHigherUnitGroup, Subgroup.mem_map] at hu
  rcases hu with ⟨y, hyker, hy⟩
  let z : A.toSubmonoidˣ := A.toSubmonoid.unitsEquivUnitsType y
  let zval : A := ⟨(z.val : v.adicCompletion F), z.val.property⟩
  have hquot : Ideal.Quotient.mk (J ^ n) zval = 1 := by
    have h := hyker
    change Units.map (Ideal.Quotient.mk (J ^ n)).toMonoidHom
      (A.toSubmonoid.unitsEquivUnitsType y) = 1 at h
    have hval := congrArg Units.val h
    change Ideal.Quotient.mk (J ^ n) zval = 1 at hval
    exact hval
  have hcong : zval - (1 : A) ∈ (J ^ n : Ideal A) :=
    (Ideal.Quotient.mk_eq_one_iff_sub_mem (I := J ^ n) zval).mp hquot
  have hyval : (zval : v.adicCompletion F) = (u : v.adicCompletion F) := by
    have h := congrArg Units.val hy
    change (zval : v.adicCompletion F) = (u : v.adicCompletion F) at h
    exact h
  let zInv : A.toSubmonoidˣ := A.toSubmonoid.unitsEquivUnitsType y⁻¹
  let zInvval : A := ⟨(zInv.val : v.adicCompletion F), zInv.val.property⟩
  have hzInt : (zval : v.adicCompletion F) ∈ A := zval.property
  have hzInvInt : (zInvval : v.adicCompletion F) ∈ A := zInvval.property
  have hboundA : Valued.v ((zval - (1 : A) : A) : v.adicCompletion F) ≤
      WithZero.exp (-(n : ℤ)) := by
    have hmem : zval - (1 : A) ∈ ((J ^ n : Ideal A) : Set A) := hcong
    rw [hpowSet n] at hmem
    exact hmem
  refine ⟨?_, ?_, ?_⟩
  · rw [← hyval]
    exact hzInt
  · rw [show ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
        (zInvval : v.adicCompletion F) by
      have hyInv : A.units.subtype y⁻¹ = u⁻¹ := by
        rw [map_inv, hy]
      have h := congrArg Units.val hyInv
      change ((zInv : A.toSubmonoidˣ).val : v.adicCompletion F) =
        ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) at h
      calc
        ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
            ((zInv : A.toSubmonoidˣ).val : v.adicCompletion F) := h.symm
        _ = (zInvval : v.adicCompletion F) := rfl]
    exact hzInvInt
  · rw [← hyval]
    simpa using hboundA

private def d2LocalUniformizerIdele (v : FinPlace F) : NumberField.IdeleGroup (𝓞 F) F :=
  NumberField.IdeleGroup.ofAdicCompletion (𝓞 F) F v
    (toLoc v (Units.mk0 (ArtinPrimitiveRoots.A1.unif (F := F) v)
      (ArtinPrimitiveRoots.A1.unif_ne_zero (F := F) v)))

private def d2IdealExponent (I : NumberFieldFractionalIdealGroup F)
    (v : FinPlace F) : ℤ :=
  FractionalIdeal.count F v
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)

private theorem d2IdealExponent_mul
    (I J : NumberFieldFractionalIdealGroup F) (v : FinPlace F) :
    d2IdealExponent (I * J) v = d2IdealExponent I v + d2IdealExponent J v := by
  exact FractionalIdeal.count_mul F v
    (Units.ne_zero I) (Units.ne_zero J)

private theorem d2IdealExponent_one (v : FinPlace F) :
    d2IdealExponent (1 : NumberFieldFractionalIdealGroup F) v = 0 := by
  exact FractionalIdeal.count_one F v

private theorem d2IdealIdelFactor_hasFiniteMulSupport
    (I : NumberFieldFractionalIdealGroup F) :
    Function.HasFiniteMulSupport
      (fun v : FinPlace F => d2LocalUniformizerIdele v ^ d2IdealExponent I v) := by
  have hExp : ∀ᶠ v : FinPlace F in Filter.cofinite, d2IdealExponent I v = 0 :=
    FractionalIdeal.finite_factors
      (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
  have hFactor : ∀ᶠ v : FinPlace F in Filter.cofinite,
      d2LocalUniformizerIdele v ^ d2IdealExponent I v = 1 := by
    filter_upwards [hExp] with v hv
    simp [hv]
  exact Filter.eventually_cofinite.mp hFactor

private noncomputable def d2IdealIdelHom :
    NumberFieldFractionalIdealGroup F →* NumberField.IdeleGroup (𝓞 F) F where
  toFun I := ∏ᶠ v : FinPlace F,
    d2LocalUniformizerIdele v ^ d2IdealExponent I v
  map_one' := by
    apply finprod_eq_one_of_forall_eq_one
    intro v
    rw [d2IdealExponent_one]
    simp
  map_mul' I J := by
    have hExp (v : FinPlace F) := d2IdealExponent_mul I J v
    simp_rw [hExp, zpow_add]
    exact finprod_mul_distrib
      (d2IdealIdelFactor_hasFiniteMulSupport I)
      (d2IdealIdelFactor_hasFiniteMulSupport J)

private noncomputable def d2IdealHeckeHom (χ : HeckeChar F) :
    NumberFieldFractionalIdealGroup F →* ℂˣ :=
  (χ : IdeleClassGroup (𝓞 F) F →* ℂˣ).comp
    ((QuotientGroup.mk' (NumberField.IdeleGroup.principalSubgroup (𝓞 F) F)).comp
      d2IdealIdelHom)

private noncomputable def d2RayIdealHeckeHom {m : RayClassModulus F}
    (χ : HeckeChar F) : rayClassPrimeToIdeals m →* ℂˣ :=
  (d2IdealHeckeHom χ).comp (rayClassPrimeToIdeals m).subtype

private theorem d2IdealIdelHom_finiteCoord
    (I : NumberFieldFractionalIdealGroup F) (v : FinPlace F) :
    Dictionary.ideleFiniteCoord v (d2IdealIdelHom I) =
      toLoc v (Units.mk0 (ArtinPrimitiveRoots.A1.unif (F := F) v)
        (ArtinPrimitiveRoots.A1.unif_ne_zero (F := F) v)) ^ d2IdealExponent I v := by
  classical
  have hfinite := d2IdealIdelFactor_hasFiniteMulSupport I
  change Dictionary.ideleFiniteCoord v
    (∏ᶠ w : FinPlace F, d2LocalUniformizerIdele w ^ d2IdealExponent I w) = _
  rw [MonoidHom.map_finprod (Dictionary.ideleFiniteCoord v) hfinite]
  have hother (w : FinPlace F) (hw : w ≠ v) :
      Dictionary.ideleFiniteCoord v
        (d2LocalUniformizerIdele w ^ d2IdealExponent I w) = 1 := by
    rw [map_zpow, d2LocalUniformizerIdele,
      Dictionary.ideleFiniteCoord_ofAdicCompletion_of_ne v w (Ne.symm hw)]
    simp
  rw [finprod_eq_single _ v hother]
  simp [d2LocalUniformizerIdele, map_zpow,
    Dictionary.ideleFiniteCoord_ofAdicCompletion]

private theorem d2IdealIdelHom_infiniteCoord
    (I : NumberFieldFractionalIdealGroup F) (w : InfinitePlace F) :
    Dictionary.ideleInfiniteCoordUnit w (d2IdealIdelHom I) = 1 := by
  classical
  have hfinite := d2IdealIdelFactor_hasFiniteMulSupport I
  change Dictionary.ideleInfiniteCoordUnit w
    (∏ᶠ v : FinPlace F, d2LocalUniformizerIdele v ^ d2IdealExponent I v) = _
  rw [MonoidHom.map_finprod (Dictionary.ideleInfiniteCoordUnit w) hfinite]
  apply finprod_eq_one_of_forall_eq_one
  intro v
  simp [d2LocalUniformizerIdele, map_zpow,
    Dictionary.ideleInfiniteCoordUnit_ofAdicCompletion]

private theorem d2_continuous_range_subsingleton
    {G : Type*} [TopologicalSpace G] [PreconnectedSpace G]
    (f : G → ℂˣ) (hf : Continuous f) {n : ℕ} [NeZero n]
    (hpow : ∀ x, f x ^ n = 1) : ∀ x y, f x = f y := by
  classical
  let root : Set.range f → rootsOfUnity n ℂ := fun z =>
    ⟨z.1, (mem_rootsOfUnity n z.1).2 (by
      rcases z.2 with ⟨x, hx⟩
      simpa [hx] using hpow x)⟩
  have hroot : Function.Injective root := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : rootsOfUnity n ℂ => (z : ℂˣ)) hxy
  letI : Finite (Set.range f) := Finite.of_injective root hroot
  have hfinite : (Set.range f).Finite := Set.toFinite _
  have hpre : IsPreconnected (Set.range f) := isPreconnected_range hf
  have hsub : (Set.range f).Subsingleton := by
    by_contra hsub
    have hnontrivial : (Set.range f).Nontrivial := by
      by_contra hnontrivial
      apply hsub
      intro x hx y hy
      by_contra hxy
      exact hnontrivial ⟨x, hx, y, hy, hxy⟩
    exact hfinite.not_infinite (hpre.infinite_of_nontrivial hnontrivial)
  intro x y
  exact hsub ⟨x, rfl⟩ ⟨y, rfl⟩

private theorem d2_connected_finite_order_monoidHom_trivial
    {G : Type*} [Monoid G] [TopologicalSpace G] [PreconnectedSpace G]
    (f : G →* ℂˣ) (hf : Continuous f) {n : ℕ} [NeZero n]
    (hpow : ∀ x, f x ^ n = 1) : f = 1 := by
  ext x
  have h := d2_continuous_range_subsingleton f hf hpow x 1
  simpa using h

private theorem d2_positive_real_character_eq_one
    (f : ℝˣ →* ℂˣ) (hf : Continuous f) {n : ℕ} [NeZero n]
    (hpow : ∀ x, f x ^ n = 1) (x : ℝˣ) (hx : 0 < (x : ℝ)) : f x = 1 := by
  letI : PreconnectedSpace (Set.Ioi (0 : ℝ)) :=
    Subtype.preconnectedSpace (isConnected_Ioi (a := (0 : ℝ))).isPreconnected
  let g : Set.Ioi (0 : ℝ) → ℂˣ := fun y => f (Units.mk0 (y : ℝ) y.2.ne')
  have hunit : Continuous fun y : Set.Ioi (0 : ℝ) => Units.mk0 (y : ℝ) y.2.ne' := by
    rw [Units.continuous_iff]
    constructor
    · exact continuous_subtype_val
    · have hnonzero : Set.Ioi (0 : ℝ) ⊆ ({0}ᶜ : Set ℝ) := by
        intro y hy
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact ne_of_gt hy
      have h := (continuousOn_inv₀ (G₀ := ℝ)).mono hnonzero
      rw [continuousOn_iff_continuous_domRestrict] at h
      change Continuous ((Set.Ioi (0 : ℝ)).domRestrict Inv.inv)
      exact h
  have hg : Continuous g := hf.comp hunit
  have hpowg : ∀ y, g y ^ n = 1 := by
    intro y
    exact hpow (Units.mk0 (y : ℝ) y.2.ne')
  have hconst := d2_continuous_range_subsingleton g hg hpowg
  have h := hconst ⟨x, hx⟩ ⟨1, by norm_num⟩
  simpa [g] using h

private noncomputable def d2_completionComplexContinuousMulEquiv
    (w : InfinitePlace F) (hw : w.IsComplex) : w.Completion ≃ₜ* ℂ where
  __ := (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).toMulEquiv
  continuous_toFun :=
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).isometry_toFun.continuous
  continuous_invFun :=
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).symm.isometry_toFun.continuous

private noncomputable def d2_completionRealContinuousMulEquiv
    (w : InfinitePlace F) (hw : w.IsReal) : w.Completion ≃ₜ* ℝ where
  __ := (InfinitePlace.Completion.ringEquivRealOfIsReal hw).toMulEquiv
  continuous_toFun :=
    (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).isometry_toFun.continuous
  continuous_invFun :=
    (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.isometry_toFun.continuous

private theorem d2_heckeChar_locInf_continuous (χ : HeckeChar F) (w : InfinitePlace F) :
    Continuous (χ.locInf w) := by
  change Continuous (fun x => χ (IdeleClassGroup.ofCompletion (𝓞 F) F w x))
  exact χ.continuous.comp (IdeleClassGroup.continuous_ofCompletion (𝓞 F) F w)

private theorem d2_heckeChar_locInf_pow_eq_one (χ : HeckeChar F) {n : ℕ}
    (hpow : χ ^ n = 1) (w : InfinitePlace F) (u : w.Completionˣ) :
    (χ.locInf w u) ^ n = 1 := by
  have h := congrArg (fun ψ : HeckeChar F =>
    ψ (IdeleClassGroup.ofCompletion (𝓞 F) F w u)) hpow
  simpa [HeckeChar.locInf] using h

private theorem d2_heckeChar_locInf_eq_one_of_isComplex
    (χ : HeckeChar F) (hχ : IsOfFinOrder χ) (w : InfinitePlace F)
    (hw : w.IsComplex) : χ.locInf w = 1 := by
  obtain ⟨n, hn, hpow⟩ := (isOfFinOrder_iff_pow_eq_one.mp hχ)
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let e := Units.mapContinuousMulEquiv (d2_completionComplexContinuousMulEquiv w hw)
  let f : ℂˣ →* ℂˣ := (χ.locInf w).comp e.symm.toMulEquiv.toMonoidHom
  have hfcont : Continuous f := by
    change Continuous fun z => χ.locInf w (e.symm z)
    exact (d2_heckeChar_locInf_continuous χ w).comp e.symm.continuous
  have hfpow : ∀ z, f z ^ n = 1 := by
    intro z
    change (χ.locInf w (e.symm z)) ^ n = 1
    exact d2_heckeChar_locInf_pow_eq_one χ hpow w (e.symm z)
  have hf := d2_connected_finite_order_monoidHom_trivial f hfcont hfpow
  ext u
  have h := DFunLike.congr_fun hf (e u)
  change χ.locInf w (e.symm (e u)) = 1 at h
  rw [e.symm_apply_apply] at h
  exact congrArg Units.val h

private theorem d2_heckeChar_locInf_eq_one_of_real_positive
    (χ : HeckeChar F) (hχ : IsOfFinOrder χ) (w : InfinitePlace F)
    (hw : w.IsReal) (x : Fˣ)
    (hx : 0 < w.embedding_of_isReal hw (x : F)) :
    χ.locInf w (Units.map (algebraMap F w.Completion).toMonoidHom x) = 1 := by
  obtain ⟨n, hn, hpow⟩ := (isOfFinOrder_iff_pow_eq_one.mp hχ)
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let e := Units.mapContinuousMulEquiv (d2_completionRealContinuousMulEquiv w hw)
  let u : w.Completionˣ := Units.map (algebraMap F w.Completion).toMonoidHom x
  let f : ℝˣ →* ℂˣ := (χ.locInf w).comp e.symm.toMulEquiv.toMonoidHom
  have hfcont : Continuous f := by
    change Continuous fun y => χ.locInf w (e.symm y)
    exact (d2_heckeChar_locInf_continuous χ w).comp e.symm.continuous
  have hfpow : ∀ y, f y ^ n = 1 := by
    intro y
    change (χ.locInf w (e.symm y)) ^ n = 1
    exact d2_heckeChar_locInf_pow_eq_one χ hpow w (e.symm y)
  have heq : e u = Units.map (w.embedding_of_isReal hw).toMonoidHom x := by
    apply Units.ext
    change InfinitePlace.Completion.ringEquivRealOfIsReal hw
      (algebraMap F w.Completion (x : F)) = w.embedding_of_isReal hw (x : F)
    rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
      InfinitePlace.Completion.algebraMap_apply]
    exact (InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw
      (WithAbs.toAbs _ (x : F))).trans (by simp)
  have hypos : 0 < (e u : ℝ) := by
    rw [heq]
    exact hx
  have hlocal := d2_positive_real_character_eq_one f hfcont hfpow (e u) hypos
  change χ.locInf w (e.symm (e u)) = 1 at hlocal
  rw [e.symm_apply_apply] at hlocal
  exact hlocal

private theorem d2_local_unit_valued_eq_one (v : FinPlace F)
    (u : (v.adicCompletion F)ˣ)
    (hu : (u : v.adicCompletion F) ∈ v.adicCompletionIntegers F)
    (huinv : ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈
      v.adicCompletionIntegers F) :
    Valued.v (u : v.adicCompletion F) = 1 := by
  have huVal : Valued.v (u : v.adicCompletion F) ≤ 1 := by
    simpa only [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] using hu
  have huinvVal : Valued.v ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ≤ 1 := by
    simpa only [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] using huinv
  have hinvVal : (Valued.v (u : v.adicCompletion F))⁻¹ ≤ 1 := by
    simpa [Units.val_inv_eq_inv_val, map_inv₀] using huinvVal
  have hpos : 0 < Valued.v (u : v.adicCompletion F) :=
    (Valuation.pos_iff Valued.v).2 u.ne_zero
  exact le_antisymm huVal ((inv_le_one₀ hpos).mp hinvVal)

private theorem d2_valued_unit_mul (v : FinPlace F) (u z : (v.adicCompletion F)ˣ) :
    Valued.v ((u * z : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      Valued.v (u : v.adicCompletion F) * Valued.v (z : v.adicCompletion F) := by
  change Valued.v ((u : v.adicCompletion F) * (z : v.adicCompletion F)) = _
  exact map_mul _ _ _

private theorem d2_valued_unit_inv (v : FinPlace F) (u : (v.adicCompletion F)ˣ) :
    Valued.v ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      (Valued.v (u : v.adicCompletion F))⁻¹ := by
  rw [Units.val_inv_eq_inv_val]
  exact Valuation.map_inv Valued.v (u : v.adicCompletion F)

private theorem d2_valued_unit_zpow (v : FinPlace F) (u : (v.adicCompletion F)ˣ)
    (e : ℤ) :
    Valued.v ((u ^ e : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      Valued.v (u : v.adicCompletion F) ^ e := by
  rw [Units.val_zpow_eq_zpow_val]
  by_cases he : 0 ≤ e
  · have he' : e = (e.toNat : ℤ) := by omega
    rw [he']
    simpa only [zpow_natCast] using
      (Valuation.map_pow Valued.v (u : v.adicCompletion F) e.toNat)
  · let n : ℕ := (-e).toNat
    have he' : e = -(n : ℤ) := by dsimp [n]; omega
    rw [he']
    calc
      Valued.v ((u : v.adicCompletion F) ^ (-(n : ℤ))) =
          (Valued.v ((u : v.adicCompletion F) ^ (n : ℕ)))⁻¹ := by
            rw [zpow_neg]
            exact Valuation.map_inv Valued.v ((u : v.adicCompletion F) ^ (n : ℕ))
      _ = (Valued.v (u : v.adicCompletion F) ^ n)⁻¹ := by
        rw [Valuation.map_pow]
      _ = Valued.v (u : v.adicCompletion F) ^ (-(n : ℤ)) := by
        rw [zpow_neg]
        simp only [zpow_natCast]

open Classical in
private theorem d2IdealHeckeHom_one_of_ray
    (χ : HeckeChar F) (hχ : IsOfFinOrder χ) (m : RayClassModulus F)
    (hmInf : m.infinitePart = Finset.univ)
    (hc : χ.ConductorDvd (modulusIdeal m)) (x : Fˣ)
    (hx : IsRayCongruent m x) :
    d2IdealHeckeHom χ (toPrincipalIdeal (𝓞 F) F x) = 1 := by
  classical
  let I : NumberFieldFractionalIdealGroup F := toPrincipalIdeal (𝓞 F) F x
  let p : NumberField.IdeleGroup (𝓞 F) F := NumberField.IdeleGroup.unitEmbedding (𝓞 F) F x
  let i : NumberField.IdeleGroup (𝓞 F) F := d2IdealIdelHom I
  let r : NumberField.IdeleGroup (𝓞 F) F := i * p⁻¹
  let q : NumberField.IdeleGroup (𝓞 F) F →* IdeleClassGroup (𝓞 F) F :=
    QuotientGroup.mk' (NumberField.IdeleGroup.principalSubgroup (𝓞 F) F)
  let θ : NumberField.IdeleGroup (𝓞 F) F →* ℂˣ := (χ : IdeleClassGroup (𝓞 F) F →* ℂˣ).comp q
  have hθContinuous : Continuous θ := χ.continuous.comp QuotientGroup.continuous_mk
  have hToLocVal (v : FinPlace F) :
      Valued.v (toLoc v x : v.adicCompletion F) = v.valuation F (x : F) := by
    change Valued.v (algebraMap F (v.adicCompletion F) (x : F)) = _
    exact v.valuedAdicCompletion_eq_valuation' (x : F)
  have hExp (v : FinPlace F) :
      d2IdealExponent I v = -WithZero.log (Valued.v (toLoc v x : v.adicCompletion F)) := by
    change FractionalIdeal.count F v
      (toPrincipalIdeal (𝓞 F) F x : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = _
    rw [FractionalIdeal.count_toPrincipalIdeal_eq_neg_log_valuation, ← hToLocVal]
  have hPrincipalCoord (v : FinPlace F) :
      Dictionary.ideleFiniteCoord v p = toLoc v x := by
    apply Units.ext
    rfl
  have hRCoord (v : FinPlace F) :
      Dictionary.ideleFiniteCoord v r =
        toLoc v (Units.mk0 (ArtinPrimitiveRoots.A1.unif (F := F) v)
          (ArtinPrimitiveRoots.A1.unif_ne_zero (F := F) v)) ^ d2IdealExponent I v *
          (toLoc v x)⁻¹ := by
    dsimp [r]
    rw [map_mul, d2IdealIdelHom_finiteCoord, map_inv, hPrincipalCoord]
  have hUniformizerVal (v : FinPlace F) :
      Valued.v (toLoc v (Units.mk0 (ArtinPrimitiveRoots.A1.unif (F := F) v)
        (ArtinPrimitiveRoots.A1.unif_ne_zero (F := F) v)) : v.adicCompletion F) =
        WithZero.exp (-1 : ℤ) := by
    simpa [ArtinPrimitiveRoots.A1.toLoc, completionIntegerUniformizer] using
      completionIntegerUniformizer_val v
  have hRVal (v : FinPlace F) :
      Valued.v (Dictionary.ideleFiniteCoord v r : v.adicCompletion F) = 1 := by
    rw [hRCoord]
    have hpow : (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) ^
        d2IdealExponent I v =
        WithZero.exp (-d2IdealExponent I v) := by
      simpa using (WithZero.exp_zsmul (d2IdealExponent I v) (-1 : ℤ)).symm
    have hvx : Valued.v (toLoc v x : v.adicCompletion F) ≠ 0 :=
      (Valuation.ne_zero_iff Valued.v).2 (Units.ne_zero (toLoc v x))
    have hvalStep :
        Valued.v (((toLoc v
          (Units.mk0 (ArtinPrimitiveRoots.A1.unif (F := F) v)
            (ArtinPrimitiveRoots.A1.unif_ne_zero (F := F) v)) ^ d2IdealExponent I v *
          (toLoc v x)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)) =
        Valued.v (toLoc v
          (Units.mk0 (ArtinPrimitiveRoots.A1.unif (F := F) v)
            (ArtinPrimitiveRoots.A1.unif_ne_zero (F := F) v)) : v.adicCompletion F) ^
          d2IdealExponent I v * (Valued.v (toLoc v x : v.adicCompletion F))⁻¹ := by
      calc
        Valued.v (((toLoc v
            (Units.mk0 (ArtinPrimitiveRoots.A1.unif (F := F) v)
              (ArtinPrimitiveRoots.A1.unif_ne_zero (F := F) v)) ^ d2IdealExponent I v *
            (toLoc v x)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)) =
            Valued.v ((toLoc v
                (Units.mk0 (ArtinPrimitiveRoots.A1.unif (F := F) v)
                  (ArtinPrimitiveRoots.A1.unif_ne_zero (F := F) v)) ^
                d2IdealExponent I v : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
              Valued.v (((toLoc v x)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) := by
                exact d2_valued_unit_mul v _ _
        _ = _ := by
          rw [d2_valued_unit_zpow, d2_valued_unit_inv]
    calc
      Valued.v (((toLoc v
          (Units.mk0 (ArtinPrimitiveRoots.A1.unif (F := F) v)
            (ArtinPrimitiveRoots.A1.unif_ne_zero (F := F) v)) ^ d2IdealExponent I v *
          (toLoc v x)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)) =
          Valued.v (toLoc v
              (Units.mk0 (ArtinPrimitiveRoots.A1.unif (F := F) v)
                (ArtinPrimitiveRoots.A1.unif_ne_zero (F := F) v)) : v.adicCompletion F) ^
              d2IdealExponent I v * (Valued.v (toLoc v x : v.adicCompletion F))⁻¹ := by
            exact hvalStep
      _ = WithZero.exp (-d2IdealExponent I v) *
            (Valued.v (toLoc v x : v.adicCompletion F))⁻¹ := by
              rw [hUniformizerVal, hpow]
      _ = WithZero.exp (WithZero.log (Valued.v (toLoc v x : v.adicCompletion F))) *
            (Valued.v (toLoc v x : v.adicCompletion F))⁻¹ := by
              rw [hExp]
              simp
      _ = 1 := by rw [WithZero.exp_log hvx]; exact mul_inv_cancel₀ hvx
  have hLocalChar (v : FinPlace F) :
      χ.loc v (Dictionary.ideleFiniteCoord v r) = 1 := by
    let u := Dictionary.ideleFiniteCoord v r
    have huVal : Valued.v (u : v.adicCompletion F) = 1 := by
      simpa [u] using hRVal v
    have hu : (u : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
      rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, huVal]
    have huinvVal : Valued.v ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
      simpa [huVal] using d2_valued_unit_inv v u
    have huinv : ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈
        v.adicCompletionIntegers F := by
      rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, huinvVal]
    by_cases hv : v ∈ m.finitePart.support
    · have hxLocal : toLoc v x ∈ rayLocalHigherUnitGroup v (m.finitePart v) := hx.1 v hv
      have hxInvLocal : toLoc v (x⁻¹) ∈ rayLocalHigherUnitGroup v (m.finitePart v) := by
        change finitePlaceUnitEmbedding v (x⁻¹) ∈ rayLocalHigherUnitGroup v (m.finitePart v)
        exact (IsRayCongruent.inv hx).1 v hv
      have hvalx : Valued.v (toLoc v x : v.adicCompletion F) = 1 := by
        obtain ⟨hxu, hxi, _⟩ := valued_sub_one_le_of_mem_rayLocalHigherUnitGroup
          v (m.finitePart v) (toLoc v x) hxLocal
        exact d2_local_unit_valued_eq_one v (toLoc v x) hxu hxi
      have hExpZero : d2IdealExponent I v = 0 := by
        rw [hExp, hvalx, WithZero.log_one]
        simp
      have hcoord : Dictionary.ideleFiniteCoord v r = (toLoc v x)⁻¹ := by
        rw [hRCoord, hExpZero]
        simp
      have hlocal := valued_sub_one_le_of_mem_rayLocalHigherUnitGroup
        v (m.finitePart v) (toLoc v (x⁻¹)) hxInvLocal
      have hexp := idealExp_modulusIdeal m v
      have hbound : Valued.v ((toLoc v (x⁻¹) : v.adicCompletion F) - 1) ≤
          WithZero.exp (-(A1.idealExp v (modulusIdeal m) : ℤ)) := by
        simpa only [← hexp] using hlocal.2.2
      have hχlocal := hc v (toLoc v (x⁻¹)) hlocal.1 hlocal.2.1 hbound
      rw [hcoord]
      simpa only [map_inv] using hχlocal
    · have hExpZero : A1.idealExp v (modulusIdeal m) = 0 := by
        rw [idealExp_modulusIdeal]
        exact Finsupp.notMem_support_iff.mp hv
      have hbound : Valued.v ((u : v.adicCompletion F) - 1) ≤
          WithZero.exp (-(A1.idealExp v (modulusIdeal m) : ℤ)) := by
        have htriangle : Valued.v ((u : v.adicCompletion F) - 1) ≤ 1 := by
          calc
            Valued.v ((u : v.adicCompletion F) - 1) ≤
                max (Valued.v (u : v.adicCompletion F)) (Valued.v (1 : v.adicCompletion F)) :=
                  Valuation.map_sub _ _ _
            _ ≤ 1 := by rw [hRVal]; simp
        simpa [hExpZero] using htriangle
      exact hc v u hu huinv hbound
  have hInfiniteChar (w : InfinitePlace F) :
      χ.locInf w (Dictionary.ideleInfiniteCoordUnit w r) = 1 := by
    have hpInf : Dictionary.ideleInfiniteCoordUnit w p =
        Units.map (algebraMap F w.Completion).toMonoidHom x := by
      apply Units.ext
      rfl
    have hpInv : Dictionary.ideleInfiniteCoordUnit w (p⁻¹) =
        (Units.map (algebraMap F w.Completion).toMonoidHom x)⁻¹ := by
      rw [(Dictionary.ideleInfiniteCoordUnit w).map_inv, hpInf]
    have hrInf : Dictionary.ideleInfiniteCoordUnit w r =
        Units.map (algebraMap F w.Completion).toMonoidHom (x⁻¹) := by
      dsimp [r]
      calc
        Dictionary.ideleInfiniteCoordUnit w
            (d2IdealIdelHom I * p⁻¹) =
            Dictionary.ideleInfiniteCoordUnit w (d2IdealIdelHom I) *
              Dictionary.ideleInfiniteCoordUnit w (p⁻¹) := map_mul _ _ _
        _ = (Units.map (algebraMap F w.Completion).toMonoidHom x)⁻¹ := by
          rw [d2IdealIdelHom_infiniteCoord, hpInv]
          simp
        _ = Units.map (algebraMap F w.Completion).toMonoidHom (x⁻¹) := by
          simp [map_inv]
    rw [hrInf]
    rcases w.isReal_or_isComplex with hreal | hcomplex
    · let wr : RayClassRealPlace F := ⟨w, hreal⟩
      have hwr : wr ∈ m.infinitePart := by
        rw [hmInf]
        exact Finset.mem_univ _
      have hposInv : 0 < w.embedding_of_isReal hreal ((x⁻¹ : Fˣ) : F) :=
        (IsRayCongruent.inv hx).2 wr hwr
      exact d2_heckeChar_locInf_eq_one_of_real_positive χ hχ w hreal (x⁻¹) hposInv
    · have hcomplex' := d2_heckeChar_locInf_eq_one_of_isComplex χ hχ w hcomplex
      simpa using congrArg (fun ψ : w.Completionˣ →* ℂˣ =>
        ψ (Units.map (algebraMap F w.Completion).toMonoidHom (x⁻¹))) hcomplex'
  have hθInfinite (w : InfinitePlace F) :
      θ (NumberField.IdeleGroup.ofCompletion (𝓞 F) F w (Dictionary.ideleInfiniteCoordUnit w r)) = 1 :=
    hInfiniteChar w
  have hθFinite (v : FinPlace F) :
      θ (NumberField.IdeleGroup.ofAdicCompletion (𝓞 F) F v (Dictionary.ideleFiniteCoord v r)) = 1 :=
    hLocalChar v
  have htrunc (S : Finset (FinPlace F)) :
      θ (ArtinPrimitiveRoots.Proofs.hk_misc_p.d2IdeleSupportTrunc r S) = 1 := by
    change θ ((∏ w ∈ Finset.univ,
      NumberField.IdeleGroup.ofCompletion (𝓞 F) F w (Dictionary.ideleInfiniteCoordUnit w r)) *
      ∏ v ∈ S, NumberField.IdeleGroup.ofAdicCompletion (𝓞 F) F v (Dictionary.ideleFiniteCoord v r)) = 1
    rw [map_mul, map_prod, map_prod]
    have harch : (∏ w ∈ Finset.univ,
        θ (NumberField.IdeleGroup.ofCompletion (𝓞 F) F w (Dictionary.ideleInfiniteCoordUnit w r))) = 1 :=
      Finset.prod_eq_one (fun w _ => hθInfinite w)
    have hfinite : (∏ v ∈ S,
        θ (NumberField.IdeleGroup.ofAdicCompletion (𝓞 F) F v (Dictionary.ideleFiniteCoord v r))) = 1 :=
      Finset.prod_eq_one (fun v _ => hθFinite v)
    rw [harch, hfinite]
    simp
  have hθTendsto : Tendsto (fun S : Finset (FinPlace F) =>
      θ (ArtinPrimitiveRoots.Proofs.hk_misc_p.d2IdeleSupportTrunc r S)) atTop (𝓝 (θ r)) :=
    hθContinuous.continuousAt.tendsto.comp
      (ArtinPrimitiveRoots.Proofs.hk_misc_p.tendsto_d2IdeleSupportTrunc r)
  have hθconstant : (fun S : Finset (FinPlace F) =>
      θ (ArtinPrimitiveRoots.Proofs.hk_misc_p.d2IdeleSupportTrunc r S)) =
        fun _ => (1 : ℂˣ) := funext htrunc
  rw [hθconstant] at hθTendsto
  have hθr : θ r = 1 := tendsto_nhds_unique hθTendsto tendsto_const_nhds
  have hθp : θ p = 1 := by
    have hq : q p = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨x, rfl⟩
    simp [θ, hq]
  have hrp : r * p = i := by
    dsimp [r]
    group
  change θ i = 1
  calc
    θ i = θ (r * p) := by rw [hrp]
    _ = θ r * θ p := map_mul _ _ _
    _ = 1 := by rw [hθr, hθp]; simp

private theorem d2IdealIdelHom_prime (v : FinPlace F) :
    d2IdealIdelHom (idealUnit v.asIdeal v.ne_bot) = d2LocalUniformizerIdele v := by
  classical
  let I : NumberFieldFractionalIdealGroup F := idealUnit v.asIdeal v.ne_bot
  have hcoe : (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
      (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
    simp [I, idealUnit]
  have hself : d2IdealExponent I v = 1 := by
    rw [d2IdealExponent, hcoe, FractionalIdeal.count_self]
  have hother (w : FinPlace F) (hw : w ≠ v) : d2IdealExponent I w = 0 := by
    rw [d2IdealExponent, hcoe]
    exact FractionalIdeal.count_maximal_coprime F w hw.symm
  have hprod : (∏ᶠ w : FinPlace F,
      d2LocalUniformizerIdele w ^ d2IdealExponent I w) = d2LocalUniformizerIdele v := by
    calc
      (∏ᶠ w : FinPlace F, d2LocalUniformizerIdele w ^ d2IdealExponent I w) =
          d2LocalUniformizerIdele v ^ d2IdealExponent I v :=
        finprod_eq_single _ v (fun w hw => by rw [hother w hw]; simp)
      _ = d2LocalUniformizerIdele v := by rw [hself]; simp
  change (∏ᶠ w : FinPlace F, d2LocalUniformizerIdele w ^ d2IdealExponent I w) = _
  exact hprod

open Classical in
/-- **DICT-2.** A finite-order idelic character with conductor dividing `𝔫 ≠ 0` is a character
of `Cl_𝔪(F)` for the modulus `𝔪` with finite part `𝔫` and all real places (for totally complex `F`
there are none), with the same prime values off `𝔫`.
Consumers: A2 `zf:row-conductor-family`, `zf:convexity`, `zf:small-rows`,
`zf:intermediate-rows` (numerator `L^S(w, χ_•(u))` from A1 `kummer_exists`), `prop:zero-density`
(`ω_u = η κ_u⁻¹`). -/
theorem exists_rayClass_of_heckeChar (χ : HeckeChar F) (hχ : IsOfFinOrder χ) (n : Ideal (𝓞 F))
    (hn : n ≠ ⊥) (hc : χ.ConductorDvd n) :
    ∃ (m : RayClassModulus F) (ψ : RayClassGroup m →* ℂˣ),
      modulusIdeal m = n ∧ m.infinitePart = Finset.univ ∧
      ∀ v : FinPlace F, v ∉ m.finitePart.support → charValue ψ v.asIdeal = χ.primeValue v := by
  classical
  let m : RayClassModulus F := rayModulusFromIdeal n hn
  have hmIdeal : modulusIdeal m = n := modulusIdeal_rayModulusFromIdeal n hn
  have hmInf : m.infinitePart = Finset.univ := rfl
  have hcM : χ.ConductorDvd (modulusIdeal m) := by rw [hmIdeal]; exact hc
  have hglobal : rayPrincipalIdealSubgroup m ≤ (d2IdealHeckeHom χ).ker := by
    rw [rayPrincipalIdealSubgroup, Subgroup.closure_le]
    rintro I ⟨x, hx, rfl⟩
    exact (MonoidHom.mem_ker).mpr
      (d2IdealHeckeHom_one_of_ray χ hχ m hmInf hcM x hx)
  have hker : rayPrincipalIdealSubgroupInPrimeTo m ≤ (d2RayIdealHeckeHom χ).ker := by
    intro P hP
    have hP' : (P : NumberFieldFractionalIdealGroup F) ∈ rayPrincipalIdealSubgroup m := by
      change (P : NumberFieldFractionalIdealGroup F) ∈ rayPrincipalIdealSubgroup m at hP
      exact hP
    have hval := MonoidHom.mem_ker.mp (hglobal hP')
    exact (MonoidHom.mem_ker).mpr (by simpa [d2RayIdealHeckeHom] using hval)
  let ψ : RayClassGroup m →* ℂˣ :=
    QuotientGroup.lift (rayPrincipalIdealSubgroupInPrimeTo m)
      (d2RayIdealHeckeHom χ) hker
  have hcop (v : FinPlace F) (hv : v ∉ m.finitePart.support) :
      IsCoprimeTo m v.asIdeal := by
    refine ⟨v.ne_bot, ?_⟩
    intro w hw
    have hwv : w ≠ v := by
      intro hEq
      exact hv (hEq ▸ hw)
    simpa [idealUnit] using
      (FractionalIdeal.count_maximal_coprime F w hwv.symm)
  have hprimeRep (v : FinPlace F) (hv : v ∉ m.finitePart.support) :
      d2IdealHeckeHom χ (idealUnit v.asIdeal v.ne_bot) =
        χ.loc v (toLoc v (Units.mk0 (ArtinPrimitiveRoots.A1.unif (F := F) v)
          (ArtinPrimitiveRoots.A1.unif_ne_zero (F := F) v))) := by
    change χ (QuotientGroup.mk' (NumberField.IdeleGroup.principalSubgroup (𝓞 F) F)
      (d2IdealIdelHom (idealUnit v.asIdeal v.ne_bot))) = _
    rw [d2IdealIdelHom_prime]
    rfl
  have hUnramified (v : FinPlace F) (hv : v ∉ m.finitePart.support) :
      χ.UnramifiedAt v := by
    intro u hu huinv
    have hval : Valued.v (u : v.adicCompletion F) = 1 :=
      d2_local_unit_valued_eq_one v u hu huinv
    have hbound : Valued.v ((u : v.adicCompletion F) - 1) ≤ 1 := by
      calc
        Valued.v ((u : v.adicCompletion F) - 1) ≤
            max (Valued.v (u : v.adicCompletion F)) (Valued.v (1 : v.adicCompletion F)) :=
              Valuation.map_sub _ _ _
        _ ≤ 1 := by rw [hval]; simp
    have hexp : A1.idealExp v (modulusIdeal m) = 0 := by
      rw [idealExp_modulusIdeal]
      exact Finsupp.notMem_support_iff.mp hv
    exact hcM v u hu huinv (by simpa [hexp] using hbound)
  refine ⟨m, ψ, hmIdeal, hmInf, ?_⟩
  intro v hv
  let P : rayClassPrimeToIdeals m :=
    ⟨idealUnit v.asIdeal v.ne_bot, (hcop v hv).2⟩
  let π : (v.adicCompletion F)ˣ :=
    toLoc v (Units.mk0 (ArtinPrimitiveRoots.A1.unif (F := F) v)
      (ArtinPrimitiveRoots.A1.unif_ne_zero (F := F) v))
  have hclass : rayClass m v.asIdeal (hcop v hv) = QuotientGroup.mk P := rfl
  have hψ : ψ (QuotientGroup.mk P) = χ.loc v π := by
    calc
      ψ (QuotientGroup.mk P) = d2RayIdealHeckeHom χ P := by
        simp [ψ, d2RayIdealHeckeHom]
      _ = d2IdealHeckeHom χ (idealUnit v.asIdeal v.ne_bot) := rfl
      _ = χ.loc v π := by simpa [π] using hprimeRep v hv
  have hcharValue : charValue ψ v.asIdeal =
      ((ψ (rayClass m v.asIdeal (hcop v hv)) : ℂˣ) : ℂ) := by
    simp [charValue, hcop v hv]
  calc
    charValue ψ v.asIdeal =
        ((ψ (rayClass m v.asIdeal (hcop v hv)) : ℂˣ) : ℂ) := hcharValue
    _ = ((χ.loc v π : ℂˣ) : ℂ) := by
          exact congrArg (fun z : ℂˣ => (z : ℂ)) (by simpa [hclass] using hψ)
    _ = χ.primeValue v := by
      simp [HeckeChar.primeValue, hUnramified v hv, π]

/-! ## §3 Uniqueness and primitive characters -/

/-- **DICT-3.** Idelic characters agreeing (and unramified) at all primes outside a finite set are
equal (weak approximation and continuity).  Consumer: A2 `zf:row-conductor-family` (the `ω_u` are
pairwise distinct, transported from A1 `kummer_eq_iff`), `lem:conductor-sieve`. -/
theorem heckeChar_eq_of_primeValue (χ χ' : HeckeChar F) (T : Finset (FinPlace F))
    (h : ∀ v : FinPlace F, v ∉ T →
      χ.UnramifiedAt v ∧ χ'.UnramifiedAt v ∧ χ.primeValue v = χ'.primeValue v) :
    χ = χ' := by
  classical
  let δ : HeckeChar F := χ / χ'
  have hout (v : FinPlace F) (hv : v ∉ T) : δ.loc v = 1 := by
    apply MonoidHom.ext
    intro u
    change χ.loc v u * (χ'.loc v u)⁻¹ = 1
    have hloc := heckeLoc_eq_of_primeValue χ χ' v (h v hv).1 (h v hv).2.1
      (h v hv).2.2 u
    rw [hloc]
    simp
  let W := (Finset.univ : Finset (InfinitePlace F))
  let U := (∀ P : T, (P.1.adicCompletion F)ˣ) × (∀ w : W, w.1.Completionˣ)
  let R := (∀ P : T, P.1.adicCompletion F) × (∀ w : W, w.1.Completion)
  let φ : U → ℂˣ := fun z =>
    (∏ P : T, δ.loc P.1 (z.1 P)) * ∏ w : W, δ.locInf w.1 (z.2 w)
  have hφ : Continuous φ := by
    apply Continuous.mul
    · apply continuous_finsetProd
      intro P _
      exact (δ.continuous.comp
        (IdeleClassGroup.continuous_ofAdicCompletion (𝓞 F) F P.1)).comp
          ((continuous_apply P).comp continuous_fst)
    · apply continuous_finsetProd
      intro w _
      exact (δ.continuous.comp
        (IdeleClassGroup.continuous_ofCompletion (𝓞 F) F w.1)).comp
          ((continuous_apply w).comp continuous_snd)
  let ρ : NumberField.IdeleGroup (𝓞 F) F → U := fun x =>
    (fun P => Dictionary.ideleFiniteCoord P.1 x,
      fun w => Dictionary.ideleInfiniteCoordUnit w.1 x)
  have hρ : Continuous ρ := by
    apply Continuous.prodMk
    · apply continuous_pi
      intro P
      apply Units.continuous_iff.mpr
      exact ⟨((RestrictedProduct.continuous_eval P.1).comp continuous_snd).comp
          Units.continuous_val,
        ((RestrictedProduct.continuous_eval P.1).comp continuous_snd).comp
          Units.continuous_coe_inv⟩
    · apply continuous_pi
      intro w
      apply Units.continuous_iff.mpr
      exact ⟨((continuous_apply w.1).comp continuous_fst).comp Units.continuous_val,
        ((continuous_apply w.1).comp continuous_fst).comp Units.continuous_coe_inv⟩
  let g : ContinuousMonoidHom (NumberField.IdeleGroup (𝓞 F) F) ℂˣ :=
    ⟨MonoidHom.mk' (fun x => φ (ρ x)) (fun x y => by
      simp only [φ, ρ, map_mul, Finset.prod_mul_distrib]
      ac_rfl), hφ.comp hρ⟩
  let q : NumberField.IdeleGroup (𝓞 F) F →* IdeleClassGroup (𝓞 F) F := QuotientGroup.mk' _
  let f : ContinuousMonoidHom (NumberField.IdeleGroup (𝓞 F) F) ℂˣ :=
    ⟨δ.toMonoidHom.comp q, δ.continuous.comp QuotientGroup.continuous_mk⟩
  have hfg : f = g := by
    apply ArtinPrimitiveRoots.Proofs.a1_kummer_sol.idele_hom_ext
    · intro w x
      change δ.locInf w x = φ (ρ (NumberField.IdeleGroup.ofCompletion (𝓞 F) F w x))
      dsimp only [φ, ρ]
      simp only [Dictionary.ideleFiniteCoord_ofCompletion, map_one,
        Finset.prod_const_one, one_mul]
      symm
      rw [Finset.prod_eq_single (⟨w, Finset.mem_univ w⟩ : W)]
      · rw [Dictionary.ideleInfiniteCoordUnit_ofCompletion_self]
      · intro v _ hv
        have hvw : v.1 ≠ w := fun heq => hv (Subtype.ext heq)
        rw [Dictionary.ideleInfiniteCoordUnit_ofCompletion_of_ne v.1 w hvw, map_one]
      · simp
    · intro P x
      change δ.loc P x = φ (ρ (NumberField.IdeleGroup.ofAdicCompletion (𝓞 F) F P x))
      dsimp only [φ, ρ]
      simp only [Dictionary.ideleInfiniteCoordUnit_ofAdicCompletion, map_one,
        Finset.prod_const_one, mul_one]
      by_cases hPT : P ∈ T
      · symm
        rw [Finset.prod_eq_single (⟨P, hPT⟩ : T)]
        · rw [Dictionary.ideleFiniteCoord_ofAdicCompletion]
        · intro Q _ hQ
          have hQP : Q.1 ≠ P := fun heq => hQ (Subtype.ext heq)
          rw [Dictionary.ideleFiniteCoord_ofAdicCompletion_of_ne Q.1 P hQP, map_one]
        · simp
      · rw [hout P hPT, MonoidHom.one_apply]
        symm
        apply Finset.prod_eq_one
        intro Q _
        have hQP : Q.1 ≠ P := fun heq => hPT (heq ▸ Q.2)
        rw [Dictionary.ideleFiniteCoord_ofAdicCompletion_of_ne Q.1 P hQP, map_one]
  let d : F → R := fun a =>
    (fun P => algebraMap F (P.1.adicCompletion F) a,
      fun w => algebraMap F w.1.Completion a)
  have hd : DenseRange d := Dictionary.weakApproximation_denseRange T W
  let du : Fˣ → U := fun a =>
    (fun P => Units.map (algebraMap F (P.1.adicCompletion F)).toMonoidHom a,
      fun w => Units.map (algebraMap F w.1.Completion).toMonoidHom a)
  let val : U → R := fun z =>
    (fun P => (z.1 P : P.1.adicCompletion F), fun w => (z.2 w : w.1.Completion))
  have hval : IsOpenEmbedding val :=
    (IsOpenEmbedding.piMap (fun P : T =>
      IsOpenUnits.isOpenEmbedding_unitsVal (M := P.1.adicCompletion F))).prodMap
      (IsOpenEmbedding.piMap (fun w : W =>
        IsOpenUnits.isOpenEmbedding_unitsVal (M := w.1.Completion)))
  have hdu : DenseRange du := by
    rw [DenseRange, dense_iff_inter_open]
    intro V hV hVne
    obtain ⟨a, ha⟩ := hd.exists_mem_open (hval.isOpenMap V hV)
      (hVne.image val)
    obtain ⟨z, hzV, hza⟩ := ha
    have ha0 : a ≠ 0 := by
      intro ha0
      let w : W := ⟨Classical.arbitrary (InfinitePlace F), Finset.mem_univ _⟩
      have heq := congrArg (fun t : R => t.2 w) hza
      change (z.2 w : w.1.Completion) = algebraMap F w.1.Completion a at heq
      rw [ha0, map_zero] at heq
      exact (z.2 w).ne_zero heq
    let au : Fˣ := Units.mk0 a ha0
    have heq : du au = z := by
      apply Prod.ext
      · funext P
        apply Units.ext
        exact (congrArg (fun t : R => t.1 P) hza).symm
      · funext w
        apply Units.ext
        exact (congrArg (fun t : R => t.2 w) hza).symm
    exact ⟨du au, heq ▸ hzV, au, rfl⟩
  have hprincipal (a : Fˣ) : φ (du a) = 1 := by
    have hr : ρ (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a) = du a := by
      apply Prod.ext
      · funext P
        apply Units.ext
        rfl
      · funext w
        apply Units.ext
        rfl
    rw [← hr]
    change g (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a) = 1
    rw [← hfg]
    change δ (q (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a)) = 1
    have hq : q (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨a, rfl⟩
    rw [hq, map_one]
  have hφone : φ = fun _ => (1 : ℂˣ) :=
    hdu.equalizer hφ continuous_const (funext hprincipal)
  have hδ : δ = 1 := by
    apply ContinuousMonoidHom.ext
    intro y
    refine QuotientGroup.induction_on y (fun x => ?_)
    change f x = 1
    rw [hfg]
    exact congrFun hφone (ρ x)
  exact div_eq_one.mp hδ

private theorem exists_rayCongruent_generator_with_prime_valuation
    {m : RayClassModulus F} (T : Finset (FinPlace F)) (v : FinPlace F)
    (hvT : v ∈ T) (hvM : v ∉ m.finitePart.support) :
    ∃ (a : 𝓞 F) (ha0 : a ≠ 0) (x : Fˣ),
    x = Units.mk0 (algebraMap (𝓞 F) F a)
        (fun hmap => ha0 ((IsFractionRing.injective (𝓞 F) F) (by simpa using hmap))) ∧
        IsRayCongruent m x ∧
        (∀ q ∈ m.finitePart.support, a ∉ q.asIdeal) ∧
        Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span {a})) = 1 ∧
        ∀ w ∈ T, w ≠ v → Multiset.count w.asIdeal
          (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a})) = 0 := by
  classical
  let U := T ∪ m.finitePart.support
  let e (q : FinPlace F) : ℕ :=
    if q = v then 2 else if q ∈ m.finitePart.support then m.finitePart q else 1
  have hvU : v ∈ U := Finset.mem_union_left _ hvT
  have hlt : v.asIdeal ^ 2 < v.asIdeal := by
    simpa using Ideal.pow_succ_lt_pow v.ne_bot 1
  obtain ⟨r, hrV, hrV2⟩ := SetLike.exists_of_lt hlt
  obtain ⟨x₀, hx₀⟩ := exists_forall_sub_mem_ideal
      (s := U) (fun q : FinPlace F => q.asIdeal) e
      (by intro q hq; exact q.prime)
      (by
        intro q hq q' hq' hne hideal
        exact hne (HeightOneSpectrum.ext hideal))
      (fun q => if q.1 = v then r else 1)
  have hx₀q (q : FinPlace F) (hq : q ∈ U) :
      x₀ - (if q = v then r else 1) ∈ q.asIdeal ^ e q := by
    simpa using hx₀ q hq
  have hx₀v : x₀ - r ∈ v.asIdeal ^ 2 := by
    simpa [e] using hx₀q v hvU
  let z (q : FinPlace F) : 𝓞 F :=
    Classical.choose (Submodule.exists_mem_ne_zero_of_ne_bot
      (pow_ne_zero (e q) q.ne_bot))
  have hz (q : FinPlace F) : z q ∈ q.asIdeal ^ e q ∧ z q ≠ 0 :=
    Classical.choose_spec (Submodule.exists_mem_ne_zero_of_ne_bot
      (pow_ne_zero (e q) q.ne_bot))
  let y : 𝓞 F := ∏ q ∈ U, z q
  have hy0 : y ≠ 0 := by
    dsimp [y]
    exact Finset.prod_ne_zero_iff.mpr fun q hq => (hz q).2
  have hyq (q : FinPlace F) (hq : q ∈ U) : y ∈ q.asIdeal ^ e q := by
    dsimp [y]
    rw [← Finset.mul_prod_erase U z hq]
    simpa [mul_comm] using
      (Ideal.mul_mem_left (q.asIdeal ^ e q) (∏ q' ∈ U.erase q, z q') (hz q).1)
  have hyq2 (q : FinPlace F) (hq : q ∈ U) : y ^ 2 ∈ q.asIdeal ^ e q := by
    rw [pow_two]
    exact Ideal.mul_mem_left (q.asIdeal ^ e q) y (hyq q hq)
  let ratio (w : ClassFieldTheory.RayClassRealPlace F) : ℝ :=
    -(w.1.embedding_of_isReal w.2 (algebraMap (𝓞 F) F x₀)) /
      w.1.embedding_of_isReal w.2 (algebraMap (𝓞 F) F (y ^ 2))
  let B : ℝ := ∑ w ∈ m.infinitePart, max 0 (ratio w)
  obtain ⟨N, hN⟩ := exists_nat_gt B
  let a : 𝓞 F := x₀ + (N : 𝓞 F) * y ^ 2
  have haCongr (q : FinPlace F) (hq : q ∈ U) :
      a - (if q = v then r else 1) ∈ q.asIdeal ^ e q := by
    have h1 := hx₀q q hq
    have h2 : (N : 𝓞 F) * y ^ 2 ∈ q.asIdeal ^ e q :=
      Ideal.mul_mem_left (q.asIdeal ^ e q) (N : 𝓞 F) (hyq2 q hq)
    have hEq : a - (if q = v then r else 1) =
        (x₀ - (if q = v then r else 1)) + (N : 𝓞 F) * y ^ 2 := by
      dsimp [a]
      ring
    rw [hEq]
    exact Ideal.add_mem _ h1 h2
  have haUnit (q : FinPlace F) (hq : q ∈ U) (hqv : q ≠ v) : a ∉ q.asIdeal := by
    have he : 0 < e q := by
      dsimp [e]
      split_ifs with hqeq hqM
      · exact False.elim (hqv hqeq)
      · exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hqM)
      · omega
    have hsub' : a - 1 ∈ q.asIdeal ^ e q := by
      simpa only [if_neg hqv] using haCongr q hq
    have hsub : a - 1 ∈ q.asIdeal :=
      Ideal.pow_le_self (I := q.asIdeal) (Nat.ne_zero_of_lt he) hsub'
    intro haq
    have hone : (1 : 𝓞 F) ∈ q.asIdeal := by
      have hmem := Ideal.sub_mem (I := q.asIdeal) haq hsub
      simpa [sub_sub_cancel] using hmem
    exact q.isPrime.one_notMem hone
  have haNotV2 : a ∉ v.asIdeal ^ 2 := by
    intro hav2
    have hdiff : a - r ∈ v.asIdeal ^ 2 := by
      simpa [e] using haCongr v hvU
    have : r ∈ v.asIdeal ^ 2 := by
      have hdiff := Ideal.sub_mem (v.asIdeal ^ 2) hav2 hdiff
      simpa [sub_sub_cancel] using hdiff
    exact hrV2 this
  have haV : a ∈ v.asIdeal := by
    have hdiff : a - r ∈ v.asIdeal ^ 2 := by
      simpa [e] using haCongr v hvU
    have hdiff' : a - r ∈ v.asIdeal :=
      Ideal.pow_le_self (I := v.asIdeal) (by decide) hdiff
    have hmem := Ideal.add_mem v.asIdeal hdiff' hrV
    have hEq : a = (a - r) + r := by ring
    rw [hEq]
    exact hmem
  have ha0 : a ≠ 0 := by
    intro hz
    apply haNotV2
    simpa [hz] using (Ideal.zero_mem (v.asIdeal ^ 2))
  let x : Fˣ := Units.mk0 (algebraMap (𝓞 F) F a)
    (fun hmap => ha0 ((IsFractionRing.injective (𝓞 F) F) (by simpa using hmap)))
  have hpositive (w : ClassFieldTheory.RayClassRealPlace F) (hw : w ∈ m.infinitePart) :
      0 < w.1.embedding_of_isReal w.2 (algebraMap (𝓞 F) F a) := by
    have hyF0 : algebraMap (𝓞 F) F y ≠ 0 := by
      intro hmap
      exact hy0 ((IsFractionRing.injective (𝓞 F) F) (by simpa using hmap))
    have hyEmb0 : w.1.embedding_of_isReal w.2 (algebraMap (𝓞 F) F y) ≠ 0 :=
      (map_ne_zero (w.1.embedding_of_isReal w.2)
        (a := algebraMap (𝓞 F) F y)).2 hyF0
    have hd : 0 < w.1.embedding_of_isReal w.2 (algebraMap (𝓞 F) F (y ^ 2)) := by
      simpa [map_pow] using sq_pos_of_ne_zero hyEmb0
    have hratio : ratio w < N := by
      have hle : ratio w ≤ B := by
        dsimp [B]
        exact (le_max_right 0 (ratio w)).trans
          (Finset.single_le_sum (fun w' _ => le_max_left 0 (ratio w')) hw)
      exact hle.trans_lt hN
    have hmul := (div_lt_iff₀ hd).mp hratio
    dsimp [a]
    have hEval : w.1.embedding_of_isReal w.2
        (algebraMap (𝓞 F) F (x₀ + (N : 𝓞 F) * y ^ 2)) =
        w.1.embedding_of_isReal w.2 (algebraMap (𝓞 F) F x₀) +
          (N : ℝ) * w.1.embedding_of_isReal w.2 (algebraMap (𝓞 F) F (y ^ 2)) := by
      simp [map_add, map_mul]
    rw [hEval]
    linarith
  have hRay : IsRayCongruent m x := by
    constructor
    · intro q hq
      have hqU : q ∈ U := Finset.mem_union_right _ hq
      have hqv : q ≠ v := by
        intro heq
        exact hvM (heq ▸ hq)
      have heq : e q = m.finitePart q := by
        dsimp [e]
        rw [if_neg hqv, if_pos hq]
      have hqcong : a - 1 ∈ q.asIdeal ^ (m.finitePart q) := by
        have htmp := haCongr q hqU
        rw [heq] at htmp
        simpa only [if_neg hqv] using htmp
      exact localUnit_mem_rayLocalHigherUnitGroup_of_congruent
        q (m.finitePart q) a x rfl (haUnit q hqU hqv) hqcong
    · intro w hw
      exact hpositive w hw
  have hnotMod : ∀ q ∈ m.finitePart.support, a ∉ q.asIdeal := by
    intro q hq
    have hqU : q ∈ U := Finset.mem_union_right _ hq
    have hqv : q ≠ v := by
      intro heq
      exact hvM (heq ▸ hq)
    exact haUnit q hqU hqv
  have hspan0 : Ideal.span {a} ≠ ⊥ := by
    intro hbot
    apply ha0
    exact Ideal.span_singleton_eq_bot.mp hbot
  have hcountV : Multiset.count v.asIdeal
      (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a})) = 1 := by
    apply Ideal.count_normalizedFactors_eq (n := 1)
    · simpa using (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr haV))
    · intro hle
      exact haNotV2 (hle (Ideal.subset_span (by simp)))
  have hcountOther (q : FinPlace F) (hq : q ∈ T) (hqv : q ≠ v) :
      Multiset.count q.asIdeal
        (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a})) = 0 := by
    apply Multiset.count_eq_zero.mpr
    intro hmem
    have hfac := (Ideal.mem_normalizedFactors_iff hspan0).1 hmem
    have haq : a ∈ q.asIdeal := hfac.2 (Ideal.subset_span (by simp))
    exact haUnit q (Finset.mem_union_left _ hq) hqv haq
  exact ⟨a, ha0, x, ⟨rfl, ⟨hRay, ⟨hnotMod, ⟨hcountV, hcountOther⟩⟩⟩⟩⟩

def primeToRayIdeal (m : RayClassModulus F) (v : FinPlace F)
    (hv : v ∉ m.finitePart.support) : rayClassPrimeToIdeals m :=
  ⟨idealUnit v.asIdeal v.ne_bot, by
    intro w hw
    have hne : w ≠ v := by
      intro hEq
      exact hv (hEq ▸ hw)
    change FractionalIdeal.count F w
      (idealUnit v.asIdeal v.ne_bot : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0
    simpa [idealUnit] using
      (FractionalIdeal.count_maximal_coprime F w hne.symm)⟩

def rayIdealExponent {m : RayClassModulus F}
    (I : rayClassPrimeToIdeals m) (v : FinPlace F) : ℤ :=
  FractionalIdeal.count F v
    ((I : NumberFieldFractionalIdealGroup F) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)

open Classical in
theorem rayIdealFactorization {m : RayClassModulus F}
    (I : rayClassPrimeToIdeals m) :
    I = ∏ᶠ v : FinPlace F,
      (if hv : v ∉ m.finitePart.support then primeToRayIdeal m v hv else 1) ^
        rayIdealExponent I v := by
  classical
  let p (v : FinPlace F) : rayClassPrimeToIdeals m :=
    if hv : v ∉ m.finitePart.support then primeToRayIdeal m v hv else 1
  have hexpFinite : ∀ᶠ v : FinPlace F in Filter.cofinite, rayIdealExponent I v = 0 :=
    FractionalIdeal.finite_factors
      ((I : NumberFieldFractionalIdealGroup F) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
  have hfinite : Function.HasFiniteMulSupport
      (fun v : FinPlace F => p v ^ rayIdealExponent I v) := by
    have hEv : ∀ᶠ v : FinPlace F in Filter.cofinite,
        p v ^ rayIdealExponent I v = 1 := by
      filter_upwards [hexpFinite] with v hv
      simp [hv]
    exact Filter.eventually_cofinite.mp hEv
  let coeHom : rayClassPrimeToIdeals m →* FractionalIdeal (nonZeroDivisors (𝓞 F)) F :=
    (Units.coeHom (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)).comp
      (rayClassPrimeToIdeals m).subtype
  have hmap : coeHom (∏ᶠ v : FinPlace F, p v ^ rayIdealExponent I v) =
      ∏ᶠ v : FinPlace F, coeHom (p v) ^ rayIdealExponent I v := by
    simpa only [map_zpow] using MonoidHom.map_finprod coeHom hfinite
  have hterm (v : FinPlace F) :
      (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ^ rayIdealExponent I v =
        coeHom (p v) ^ rayIdealExponent I v := by
    by_cases hv : v ∉ m.finitePart.support
    · have hv0 : m.finitePart v = 0 := by
        by_contra hne
        exact hv (Finsupp.mem_support_iff.mpr hne)
      simp [p, hv0, coeHom, primeToRayIdeal, idealUnit]
    · have hv' : v ∈ m.finitePart.support := by simpa using hv
      have hz : rayIdealExponent I v = 0 := I.property v hv'
      simp [p, hv, coeHom, hz]
  apply Subtype.ext
  apply Units.ext
  have hfac := FractionalIdeal.finprod_heightOneSpectrum_factorization'
    (R := 𝓞 F) (K := F) (Units.ne_zero (I : NumberFieldFractionalIdealGroup F))
  calc
    ((I : NumberFieldFractionalIdealGroup F) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
        ∏ᶠ v : FinPlace F,
          (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ^
            rayIdealExponent I v := hfac.symm
    _ = ∏ᶠ v : FinPlace F, coeHom (p v) ^ rayIdealExponent I v := by
      apply finprod_congr
      exact hterm
    _ = coeHom (∏ᶠ v : FinPlace F, p v ^ rayIdealExponent I v) := hmap.symm
    _ = (((∏ᶠ v : FinPlace F, p v ^ rayIdealExponent I v : rayClassPrimeToIdeals m) :
        NumberFieldFractionalIdealGroup F) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := rfl

theorem rayIdealHom_ext {m : RayClassModulus F}
    (f g : rayClassPrimeToIdeals m →* ℂˣ)
    (hprime : ∀ v : FinPlace F, ∀ hv : v ∉ m.finitePart.support,
      f (primeToRayIdeal m v hv) = g (primeToRayIdeal m v hv)) : f = g := by
  classical
  apply MonoidHom.ext
  intro I
  let p (v : FinPlace F) : rayClassPrimeToIdeals m :=
    if hv : v ∉ m.finitePart.support then primeToRayIdeal m v hv else 1
  have hfinite : ∀ᶠ v : FinPlace F in Filter.cofinite, rayIdealExponent I v = 0 :=
    FractionalIdeal.finite_factors
      ((I : NumberFieldFractionalIdealGroup F) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
  have hfinite' : Function.HasFiniteMulSupport
      (fun v : FinPlace F => p v ^ rayIdealExponent I v) := by
    have hEv : ∀ᶠ v : FinPlace F in Filter.cofinite,
        p v ^ rayIdealExponent I v = 1 := by
      filter_upwards [hfinite] with v hv
      simp [hv]
    exact Filter.eventually_cofinite.mp hEv
  calc
    f I = f (∏ᶠ v : FinPlace F, p v ^ rayIdealExponent I v) :=
      congrArg f (rayIdealFactorization I)
    _ = ∏ᶠ v : FinPlace F, f (p v) ^ rayIdealExponent I v := by
      simpa only [map_zpow] using MonoidHom.map_finprod f hfinite'
    _ = ∏ᶠ v : FinPlace F, g (p v) ^ rayIdealExponent I v := by
      apply finprod_congr
      intro v
      by_cases hv : v ∉ m.finitePart.support
      · have hp : p v = primeToRayIdeal m v hv := by
          simpa only [p, dite_eq_left hv]
        rw [hp, hprime v hv]
      · have hv' : v ∈ m.finitePart.support := by simpa using hv
        have hz : rayIdealExponent I v = 0 := I.property v hv'
        have hp : p v = 1 := by
          simpa only [p, dite_eq_right hv]
        rw [hp, hz]
        simp
    _ = g (∏ᶠ v : FinPlace F, p v ^ rayIdealExponent I v) := by
      symm
      simpa only [map_zpow] using MonoidHom.map_finprod g hfinite'
    _ = g I := congrArg g (rayIdealFactorization I).symm

/-- **DICT-4.** Ray-class characters agreeing at all primes outside a finite set `T` are equal
(every ray class contains an ideal prime to `T`).  Consumer: A2 `lem:conductor-sieve`
(distinctness of the family on the ray-class side), `zf:row-conductor-family`. -/
theorem rayClassChar_eq_of_charValue {m : RayClassModulus F} (η η' : RayClassGroup m →* ℂˣ)
    (T : Finset (FinPlace F))
    (h : ∀ v : FinPlace F, v ∉ T → charValue η v.asIdeal = charValue η' v.asIdeal) :
    η = η' := by
  classical
  let qmap : rayClassPrimeToIdeals m →* RayClassGroup m :=
    QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo m)
  let f : rayClassPrimeToIdeals m →* ℂˣ := η.comp qmap
  let g : rayClassPrimeToIdeals m →* ℂˣ := η'.comp qmap
  let ρ : rayClassPrimeToIdeals m →* ℂˣ := f * g⁻¹
  have hDirect (v : FinPlace F) (hvM : v ∉ m.finitePart.support)
      (hvT : v ∉ T) : ρ (primeToRayIdeal m v hvM) = 1 := by
    let hcop : IsCoprimeTo m v.asIdeal := by
      refine ⟨v.ne_bot, ?_⟩
      intro w hw
      exact (primeToRayIdeal m v hvM).property w hw
    have hclass : rayClass m v.asIdeal hcop = QuotientGroup.mk
        (primeToRayIdeal m v hvM) := by
      rfl
    have hchar : charValue η v.asIdeal = ((η (rayClass m v.asIdeal hcop) : ℂˣ) : ℂ) := by
      simp [charValue, hcop]
    have hchar' : charValue η' v.asIdeal = ((η' (rayClass m v.asIdeal hcop) : ℂˣ) : ℂ) := by
      simp [charValue, hcop]
    have hvalue : η (rayClass m v.asIdeal hcop) = η' (rayClass m v.asIdeal hcop) := by
      apply Units.ext
      calc
        ((η (rayClass m v.asIdeal hcop) : ℂˣ) : ℂ) = charValue η v.asIdeal := hchar.symm
        _ = charValue η' v.asIdeal := h v hvT
        _ = ((η' (rayClass m v.asIdeal hcop) : ℂˣ) : ℂ) := hchar'
    have hfg : f (primeToRayIdeal m v hvM) = g (primeToRayIdeal m v hvM) := by
      change η (QuotientGroup.mk (primeToRayIdeal m v hvM)) =
        η' (QuotientGroup.mk (primeToRayIdeal m v hvM))
      rw [← hclass]
      exact hvalue
    simp [ρ, hfg]
  have hAtExcluded (v : FinPlace F) (hvM : v ∉ m.finitePart.support)
      (hvT : v ∈ T) : ρ (primeToRayIdeal m v hvM) = 1 := by
    obtain ⟨a, ha0, x, hx, hRay, hnotMod, hcountV, hcountOther⟩ :=
      exists_rayCongruent_generator_with_prime_valuation T v hvT hvM
    let I : Ideal (𝓞 F) := Ideal.span {a}
    have hI0 : I ≠ ⊥ := by
      intro hbot
      apply ha0
      exact Ideal.span_singleton_eq_bot.mp (by simpa [I] using hbot)
    have hIcop : IsCoprimeTo m I := by
      refine ⟨hI0, ?_⟩
      intro q hqM
      have hcountNat : Multiset.count q.asIdeal
          (UniqueFactorizationMonoid.normalizedFactors I) = 0 := by
        apply Multiset.count_eq_zero.mpr
        intro hmem
        have hfac := (Ideal.mem_normalizedFactors_iff hI0).1 (by simpa [I] using hmem)
        exact hnotMod q hqM (hfac.2 (Ideal.subset_span (by simp)))
      have hcount : FractionalIdeal.count F q
          (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0 := by
        rw [FractionalIdeal.count_coe F q hI0,
          Ideal.count_associates_factors_eq hI0 q.isPrime q.ne_bot]
        exact_mod_cast hcountNat
      change FractionalIdeal.count F q
        (idealUnit I hI0 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0
      simpa [idealUnit] using hcount
    let P : rayClassPrimeToIdeals m := ⟨idealUnit I hI0, hIcop.2⟩
    have hprincipalEq : toPrincipalIdeal (𝓞 F) F x = idealUnit I hI0 := by
      apply Units.ext
      rw [coe_toPrincipalIdeal, hx]
      simp only [Units.val_mk0]
      dsimp [idealUnit, I]
      exact (FractionalIdeal.coeIdeal_span_singleton
        (R := 𝓞 F) (S := nonZeroDivisors (𝓞 F)) (P := F) a).symm
    have htoMem : toPrincipalIdeal (𝓞 F) F x ∈ rayClassPrimeToIdeals m := by
      rw [hprincipalEq]
      exact P.property
    let P' : rayClassPrimeToIdeals m := ⟨toPrincipalIdeal (𝓞 F) F x, htoMem⟩
    have hP' : P' ∈ rayPrincipalIdealSubgroupInPrimeTo m :=
      Subgroup.subset_closure ⟨x, hRay, rfl⟩
    have hP'P : P' = P := by
      apply Subtype.ext
      exact hprincipalEq
    have hP : P ∈ rayPrincipalIdealSubgroupInPrimeTo m := by
      simpa [hP'P] using hP'
    have hρP : ρ P = 1 := by
      have hclassOne : qmap P = 1 := (QuotientGroup.eq_one_iff _).mpr hP
      simp [ρ, f, g, hclassOne]
    have hexp (q : FinPlace F) : rayIdealExponent P q =
        (Multiset.count q.asIdeal (UniqueFactorizationMonoid.normalizedFactors I) : ℤ) := by
      unfold rayIdealExponent
      have hcoe : ((P : NumberFieldFractionalIdealGroup F) :
          FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
        (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
        simp [P, idealUnit]
      rw [hcoe, FractionalIdeal.count_coe F q hI0,
        Ideal.count_associates_factors_eq hI0 q.isPrime q.ne_bot]
    have hexpV : rayIdealExponent P v = 1 := by
      rw [hexp]
      exact_mod_cast hcountV
    have hexpOther (q : FinPlace F) (hq : q ∈ T) (hqv : q ≠ v) :
        rayIdealExponent P q = 0 := by
      rw [hexp]
      exact_mod_cast hcountOther q hq hqv
    let pfun (q : FinPlace F) : rayClassPrimeToIdeals m :=
      if hq : q ∉ m.finitePart.support then primeToRayIdeal m q hq else 1
    have hfinite : ∀ᶠ q : FinPlace F in Filter.cofinite, rayIdealExponent P q = 0 := by
      simpa [rayIdealExponent] using
        (FractionalIdeal.finite_factors
          ((P : NumberFieldFractionalIdealGroup F) :
            FractionalIdeal (nonZeroDivisors (𝓞 F)) F))
    have hmulSupport : Function.HasFiniteMulSupport
        (fun q : FinPlace F => pfun q ^ rayIdealExponent P q) := by
      have hEv : ∀ᶠ q : FinPlace F in Filter.cofinite,
          pfun q ^ rayIdealExponent P q = 1 := by
        filter_upwards [hfinite] with q hq
        simp [hq]
      exact Filter.eventually_cofinite.mp hEv
    have hρfactor : ρ P = ∏ᶠ q : FinPlace F, ρ (pfun q) ^ rayIdealExponent P q := by
      calc
        ρ P = ρ (∏ᶠ q : FinPlace F, pfun q ^ rayIdealExponent P q) :=
          congrArg ρ (rayIdealFactorization P)
        _ = ∏ᶠ q : FinPlace F, ρ (pfun q) ^ rayIdealExponent P q := by
          simpa only [map_zpow] using MonoidHom.map_finprod ρ hmulSupport
    have hterm (q : FinPlace F) (hqv : q ≠ v) :
        ρ (pfun q) ^ rayIdealExponent P q = 1 := by
      by_cases hqM : q ∈ m.finitePart.support
      · have hfalse : ¬ q ∉ m.finitePart.support := by simpa using hqM
        simp only [pfun, dite_eq_right hfalse]
        simp
      · by_cases hqT : q ∈ T
        · have hzero := hexpOther q hqT hqv
          simp only [pfun, dite_eq_left hqM]
          simp [hzero]
        · have hprimeq := hDirect q hqM hqT
          simp only [pfun, dite_eq_left hqM]
          simp [hprimeq]
    have hρv : ρ (primeToRayIdeal m v hvM) = 1 := by
      have hpfunV : pfun v = primeToRayIdeal m v hvM := by
        dsimp [pfun]
        rw [dite_eq_left hvM]
      have hprod : (∏ᶠ q : FinPlace F, ρ (pfun q) ^ rayIdealExponent P q) =
          ρ (pfun v) ^ rayIdealExponent P v :=
        finprod_eq_single _ v (fun q hqv => hterm q hqv)
      have hone : (1 : ℂˣ) = ρ (pfun v) := by
        calc
          1 = ρ P := hρP.symm
          _ = ∏ᶠ q : FinPlace F, ρ (pfun q) ^ rayIdealExponent P q := hρfactor
          _ = ρ (pfun v) ^ rayIdealExponent P v := hprod
          _ = ρ (pfun v) := by rw [hexpV]; simp
      simpa [hpfunV] using hone.symm
    exact hρv
  have hprime : ∀ v : FinPlace F, ∀ hv : v ∉ m.finitePart.support,
      f (primeToRayIdeal m v hv) = g (primeToRayIdeal m v hv) := by
    intro v hv
    have hrho : ρ (primeToRayIdeal m v hv) = 1 := by
      by_cases hvT : v ∈ T
      · exact hAtExcluded v hv hvT
      · exact hDirect v hv hvT
    have hdiv : f (primeToRayIdeal m v hv) *
        (g (primeToRayIdeal m v hv))⁻¹ = 1 := by
      simpa [ρ] using hrho
    calc
      f (primeToRayIdeal m v hv) =
          f (primeToRayIdeal m v hv) * (g (primeToRayIdeal m v hv))⁻¹ *
            g (primeToRayIdeal m v hv) := by simp [mul_assoc]
      _ = 1 * g (primeToRayIdeal m v hv) := by rw [hdiv]
      _ = g (primeToRayIdeal m v hv) := by simp
  have hfg : f = g := rayIdealHom_ext f g hprime
  apply MonoidHom.ext
  intro c
  obtain ⟨I, rfl⟩ := QuotientGroup.mk'_surjective
    (rayPrincipalIdealSubgroupInPrimeTo m) c
  exact DFunLike.congr_fun hfg I

/-- **DICT-P.** Every ray-class character is induced by a primitive one, at a modulus of norm
`conductorNorm η`.  Consumers: A2 `prop:zero-density` (the detector runs on the primitive
`L_F(s, ω_u)`), `lem:conductor-sieve` (family of distinct primitive characters with
`N𝔣 ≤ C₀U`; primitivity gives a primitive residue character and `|τ| = √N𝔮`). -/
theorem exists_primitive {m : RayClassModulus F} (η : RayClassGroup m →* ℂˣ) :
    ∃ (f : RayClassModulus F) (η' : RayClassGroup f →* ℂˣ),
      f ≤ m ∧ modulusNorm f = conductorNorm η ∧
      (∀ v : FinPlace F, v ∉ m.finitePart.support →
        charValue η v.asIdeal = charValue η' v.asIdeal) ∧
      ∀ n : RayClassModulus F, FactorsThrough η' n → n = f := by
  classical
  let normSet : Set ℕ :=
    {N | ∃ n : RayClassModulus F, FactorsThrough η n ∧ modulusNorm n = N}
  have hnormSet : normSet.Nonempty := by
    exact ⟨modulusNorm m, m, factorsThrough_self η, rfl⟩
  have hnormMem : conductorNorm η ∈ normSet := by
    simpa [conductorNorm, normSet] using Nat.sInf_mem hnormSet
  obtain ⟨f₀, hf₀, hf₀norm⟩ := hnormMem
  let weightSet : Set ℕ :=
    {w | ∃ n : RayClassModulus F, FactorsThrough η n ∧
      modulusNorm n = conductorNorm η ∧ rayModulusWeight n = w}
  have hweightSet : weightSet.Nonempty := by
    exact ⟨rayModulusWeight f₀, f₀, hf₀, hf₀norm, rfl⟩
  have hweightMem := Nat.sInf_mem hweightSet
  obtain ⟨f, hf, hfnorm, hfweight⟩ := hweightMem
  obtain ⟨η', hηeq⟩ := exists_rayClassChar_of_factorsThrough hf.1 η hf
  have hcop (q : FinPlace F) (hq : q ∉ m.finitePart.support) :
      IsCoprimeTo m q.asIdeal := by
    refine ⟨q.ne_bot, ?_⟩
    intro w hw
    exact (primeToRayIdeal m q hq).property w hw
  have hcopF (q : FinPlace F) (hq : q ∉ m.finitePart.support) :
      IsCoprimeTo f q.asIdeal := by
    have hqF : q ∉ f.finitePart.support := by
      intro hq'
      exact hq (Finsupp.support_mono hf.1.1 hq')
    refine ⟨q.ne_bot, ?_⟩
    intro w hw
    exact (primeToRayIdeal f q hqF).property w hw
  have hprimeClass (q : FinPlace F) (hq : q ∉ m.finitePart.support) :
      η (rayClass m q.asIdeal (hcop q hq)) =
        η' (rayClass f q.asIdeal (hcopF q hq)) := by
    let Pm := primeToRayIdeal m q hq
    have hqF : q ∉ f.finitePart.support := by
      intro hq'
      exact hq (Finsupp.support_mono hf.1.1 hq')
    let Pf := primeToRayIdeal f q hqF
    have hclassM : rayClass m q.asIdeal (hcop q hq) = QuotientGroup.mk Pm := rfl
    have hclassF : rayClass f q.asIdeal (hcopF q hq) = QuotientGroup.mk Pf := rfl
    have hmap : rayClassMap hf.1 (QuotientGroup.mk Pm) = QuotientGroup.mk Pf := by
      rw [rayClassMap_apply_mk]
      congr 1
    have hηprime := DFunLike.congr_fun hηeq (QuotientGroup.mk Pm)
    simpa [MonoidHom.comp_apply, hclassM, hclassF, hmap] using hηprime
  refine ⟨f, η', hf.1, hfnorm, ?_, ?_⟩
  · intro q hq
    have hvalue := hprimeClass q hq
    simp only [charValue, dif_pos (hcop q hq), dif_pos (hcopF q hq)]
    exact congrArg (fun z : ℂˣ => (z : ℂ)) hvalue
  · intro n hn
    have hηFactorsN : FactorsThrough η n := by
      refine ⟨⟨le_trans hn.1.1 hf.1.1, Finset.Subset.trans hn.1.2 hf.1.2⟩, ?_⟩
      intro x hx hI
      have hIF : toPrincipalIdeal (𝓞 F) F x ∈ rayClassPrimeToIdeals f := by
        intro q hq
        exact hI q (Finsupp.support_mono hf.1.1 hq)
      let Pm : rayClassPrimeToIdeals m := ⟨toPrincipalIdeal (𝓞 F) F x, hI⟩
      let Pf : rayClassPrimeToIdeals f := ⟨toPrincipalIdeal (𝓞 F) F x, hIF⟩
      have hmap : rayClassMap hf.1 (QuotientGroup.mk Pm) = QuotientGroup.mk Pf := by
        rw [rayClassMap_apply_mk]
        congr 1
      have hηprime := DFunLike.congr_fun hηeq (QuotientGroup.mk Pm)
      have hηvalue : η (QuotientGroup.mk Pm) = η' (QuotientGroup.mk Pf) := by
        calc
          η (QuotientGroup.mk Pm) =
              η' (rayClassMap hf.1 (QuotientGroup.mk Pm)) := by
            simpa [MonoidHom.comp_apply] using hηprime
          _ = η' (QuotientGroup.mk Pf) := congrArg η' hmap
      change η (QuotientGroup.mk Pm) = 1
      rw [hηvalue]
      exact hn.2 x hx hIF
    have hnormLower : conductorNorm η ≤ modulusNorm n :=
      Nat.sInf_le ⟨n, hηFactorsN, rfl⟩
    have hnormUpper : modulusNorm n ≤ modulusNorm f := modulusNorm_mono hn.1
    have hnormEq : modulusNorm n = conductorNorm η := by
      rw [hfnorm] at hnormUpper
      exact le_antisymm hnormUpper hnormLower
    have hnWeight : rayModulusWeight n ∈ weightSet :=
      ⟨n, hηFactorsN, hnormEq, rfl⟩
    have hweightLower : rayModulusWeight f ≤ rayModulusWeight n := by
      rw [hfweight]
      exact Nat.sInf_le hnWeight
    by_contra hne
    have hweightStrict := rayModulusWeight_strict_mono hn.1 hne
    omega

/-- A primitive inducer of a nontrivial character is nontrivial. -/
theorem primitive_inducer_ne_one {m f : RayClassModulus F}
    (hfm : f ≤ m) (η : RayClassGroup m →* ℂˣ) (ψ : RayClassGroup f →* ℂˣ)
    (hη : η ≠ 1)
    (hprime : ∀ v : FinPlace F, v ∉ m.finitePart.support →
      charValue η v.asIdeal = charValue ψ v.asIdeal) : ψ ≠ 1 := by
  intro hψ
  have hcopM (v : FinPlace F) (hv : v ∉ m.finitePart.support) :
      IsCoprimeTo m v.asIdeal := by
    refine ⟨v.ne_bot, ?_⟩
    intro w hw
    exact (primeToRayIdeal m v hv).property w hw
  have hcopF (v : FinPlace F) (hv : v ∉ m.finitePart.support) :
      IsCoprimeTo f v.asIdeal := by
    have hvF : v ∉ f.finitePart.support := by
      intro hvF
      exact hv (Finsupp.support_mono hfm.1 hvF)
    refine ⟨v.ne_bot, ?_⟩
    intro w hw
    exact (primeToRayIdeal f v hvF).property w hw
  have hchar : ∀ v : FinPlace F, v ∉ m.finitePart.support →
      charValue η v.asIdeal = charValue (1 : RayClassGroup m →* ℂˣ) v.asIdeal := by
    intro v hv
    have hval := hprime v hv
    rw [hψ] at hval
    simpa [charValue, hcopM v hv, hcopF v hv] using hval
  have hηone : η = (1 : RayClassGroup m →* ℂˣ) :=
    rayClassChar_eq_of_charValue η 1 m.finitePart.support hchar
  exact hη hηone

end ArtinPrimitiveRoots.Dictionary
