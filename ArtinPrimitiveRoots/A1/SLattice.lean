import ArtinPrimitiveRoots.A1.AddChar
import ArtinPrimitiveRoots.A1.Proofs.A1_LATTICE.Core
import Mathlib.MeasureTheory.Group.Measure

/-!
# A1 arithmetic base: the S-integer lattice

This file records the Lean statements corresponding to `lem:s-lattice` and
`ar:balanced-compact` in the A1 blueprint.  The analytic objects are stated using the product
space `S.FS`, its diagonal S-integer subgroup, finite sums of standard archimedean Schwartz and
finite-place test functions, and a self-dual Haar measure for the character `S.e`.
The lattice outcomes take `D : FieldData F`, which supplies the paper's `μ₁₂ ⊂ F` hypothesis and
the required total-complexity property.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory
open scoped Classical SchwartzMap

noncomputable section

namespace ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

local instance instMeasurableFS (S : SData F CE condη) : MeasurableSpace S.FS :=
  borel S.FS
local instance instBorelFS (S : SData F CE condη) : BorelSpace S.FS := ⟨rfl⟩

/-! ## Test functions and the self-dual measure -/

/-- Locally constant compactly supported test functions at a finite place in `S`. -/
def SData.FiniteTest (S : SData F CE condη) (v : S.Sf) :=
  {f : v.1.adicCompletion F → ℂ // Continuous f ∧ HasCompactSupport f ∧ IsLocallyConstant f}

/-- Archimedean Schwartz functions on the product of complex places. -/
abbrev SData.ArchSchwartz (F : Type) [Field F] [NumberField F] :=
  SchwartzMap (InfinitePlace F → ℂ) ℂ

/-- A pure tensor in the standard Bruhat--Schwartz space on `F_S`. -/
def SData.tensorFunction (S : SData F CE condη) (arch : SData.ArchSchwartz F)
    (finite : ∀ v : S.Sf, S.FiniteTest v) : S.FS → ℂ :=
  fun x => arch x.2 * ∏ v : S.Sf, (finite v).1 (x.1 v)

/-- The Bruhat--Schwartz space: finite linear combinations of archimedean Schwartz functions
tensored with locally constant compactly supported functions at the places in `S_f`. -/
def SData.BruhatSchwartz (S : SData F CE condη) : Submodule ℂ (S.FS → ℂ) :=
  Submodule.span ℂ (Set.range fun p : SData.ArchSchwartz F ×
      (∀ v : S.Sf, S.FiniteTest v) => S.tensorFunction p.1 p.2)

/-- The Fourier transform associated to `e` and a Haar measure on `F_S`. -/
def SData.fourier (S : SData F CE condη) (A : AddCharData F)
    (μ : Measure S.FS) (f : S.FS → ℂ) : S.FS → ℂ :=
  fun y => ∫ x, f x * S.e A (-(x * y)) ∂μ

/-- A self-dual Haar measure for the additive character `e`, characterized by Fourier inversion
on the Bruhat--Schwartz space. -/
structure SData.SelfDualMeasure (S : SData F CE condη) (A : AddCharData F) where
  measure : Measure S.FS
  isHaar : Measure.IsAddHaarMeasure measure
  fourier_inversion : ∀ f : S.BruhatSchwartz, ∀ x : S.FS,
    S.fourier A measure (S.fourier A measure (f : S.FS → ℂ)) x = (f : S.FS → ℂ) (-x)

/-! ## The lattice and its annihilator -/

/-- The diagonal image of the S-integers in `F_S`. -/
def SData.diagR (S : SData F CE condη) : Set S.FS :=
  Set.range fun x : S.R => S.diag (x : F)

/-- The annihilator of a subset of `F_S` under the pairing `e(xy)`. -/
def SData.annihilator (S : SData F CE condη) (A : AddCharData F) (Γ : Set S.FS) : Set S.FS :=
  {y | ∀ x ∈ Γ, S.e A (x * y) = 1}

/-- A measurable fundamental domain for the diagonal S-integer lattice. -/
def SData.IsLatticeFundamentalDomain (S : SData F CE condη) (K : Set S.FS) : Prop :=
  ∀ x : S.FS, ∃! p : S.R × S.FS, p.2 ∈ K ∧ x = S.diag (p.1 : F) + p.2

/-- The diagonal S-integer lattice is discrete and has compact quotient.  The compact set in the
second clause is a compact set of representatives modulo the diagonal image. -/
theorem SData.diagR_discrete_cocompact (S : SData F CE condη) (D : FieldData F) :
    IsDiscrete (S.diagR : Set S.FS) ∧
      ∃ K : Set S.FS, IsCompact K ∧
        ∀ x : S.FS, ∃ r : S.R, ∃ k ∈ K, x = S.diag (r : F) + k := by
  refine ⟨?_, ?_⟩
  · simpa [SData.diagR] using
      ArtinPrimitiveRoots.Proofs.A1_LATTICE.diagR_isDiscrete S D
  · exact ArtinPrimitiveRoots.Proofs.A1_LATTICE.diagR_has_compact_cover S D

/-- The S-integer lattice is its own annihilator for the pairing `e(xy)`. -/
theorem SData.diagR_eq_annihilator (S : SData F CE condη) (D : FieldData F)
    (A : AddCharData F) :
    S.diagR = S.annihilator A S.diagR := by
  sorry

private noncomputable def covolArchToMixedEquiv (D : FieldData F) :
    (InfinitePlace F → ℂ) ≃L[ℝ] NumberField.mixedEmbedding.mixedSpace F := by
  let e : (InfinitePlace F → ℂ) ≃ₗ[ℝ] NumberField.mixedEmbedding.mixedSpace F :=
    { toFun := fun z =>
        (fun w : {w : InfinitePlace F // NumberField.InfinitePlace.IsReal w} =>
          False.elim
            ((NumberField.InfinitePlace.not_isComplex_iff_isReal.mpr w.2)
              (D.isTotallyComplex.isComplex w.1)),
          fun w : {w : InfinitePlace F // NumberField.InfinitePlace.IsComplex w} => z w.1)
      invFun := fun z w => z.2 ⟨w, D.isTotallyComplex.isComplex w⟩
      left_inv := by intro z; rfl
      right_inv := by
        intro z
        apply Prod.ext
        · funext w
          exact False.elim
            ((NumberField.InfinitePlace.not_isComplex_iff_isReal.mpr w.2)
              (D.isTotallyComplex.isComplex w.1))
        · funext w
          rfl
      map_add' := by
        intro x y
        apply Prod.ext
        · funext w
          exact False.elim
            ((NumberField.InfinitePlace.not_isComplex_iff_isReal.mpr w.2)
              (D.isTotallyComplex.isComplex w.1))
        · funext w
          rfl
      map_smul' := by
        intro c x
        apply Prod.ext
        · funext w
          exact False.elim
            ((NumberField.InfinitePlace.not_isComplex_iff_isReal.mpr w.2)
              (D.isTotallyComplex.isComplex w.1))
        · funext w
          simp }
  have hecont : Continuous e := by
    refine continuous_prodMk.mpr ⟨continuous_const, continuous_pi ?_⟩
    intro w
    exact continuous_apply w.1
  exact e.toContinuousLinearEquivOfContinuous hecont

private theorem covol_arch_fundamental_reduction (D : FieldData F)
    (z : InfinitePlace F → ℂ) :
    ∃ a : 𝓞 F, ∃ p ∈ (covolArchToMixedEquiv D).symm ''
        ZSpan.fundamentalDomain (NumberField.mixedEmbedding.latticeBasis F),
      z = (fun w => w.embedding (a : F)) + p := by
  classical
  let e := covolArchToMixedEquiv D
  let P : Set (NumberField.mixedEmbedding.mixedSpace F) :=
    ZSpan.fundamentalDomain (NumberField.mixedEmbedding.latticeBasis F)
  let zM : NumberField.mixedEmbedding.mixedSpace F := e z
  obtain ⟨y, hy⟩ :=
    ZSpan.exist_unique_vadd_mem_fundamentalDomain
      (NumberField.mixedEmbedding.latticeBasis F) zM
  have hyP : (y : NumberField.mixedEmbedding.mixedSpace F) + zM ∈ P := by
    have hy' : (y : NumberField.mixedEmbedding.mixedSpace F) +ᵥ zM ∈ P := hy.1
    simpa only [vadd_eq_add] using hy'
  have hyInt : (y : NumberField.mixedEmbedding.mixedSpace F) ∈
      NumberField.mixedEmbedding.integerLattice F :=
    (NumberField.mixedEmbedding.mem_span_latticeBasis F).mp y.property
  have hnegInt : -(y : NumberField.mixedEmbedding.mixedSpace F) ∈
      NumberField.mixedEmbedding.integerLattice F :=
    (NumberField.mixedEmbedding.integerLattice F).neg_mem hyInt
  change ∃ a : 𝓞 F,
      NumberField.mixedEmbedding F (algebraMap (𝓞 F) F a) =
        -(y : NumberField.mixedEmbedding.mixedSpace F) at hnegInt
  obtain ⟨a, ha⟩ := hnegInt
  let pM : NumberField.mixedEmbedding.mixedSpace F := (y : _) + zM
  have hpM : pM ∈ P := by simpa [pM] using hyP
  have heDiag : e (fun w : InfinitePlace F => w.embedding (a : F)) =
      NumberField.mixedEmbedding F (a : F) := by
    apply Prod.ext
    · funext w
      exact False.elim
        ((NumberField.InfinitePlace.not_isComplex_iff_isReal.mpr w.2)
          (D.isTotallyComplex.isComplex w.1))
    · funext w
      rfl
  have hzM : zM = NumberField.mixedEmbedding F (a : F) + pM := by
    calc
      zM = -(y : NumberField.mixedEmbedding.mixedSpace F) + pM := by
        dsimp [pM, zM]
        abel
      _ = NumberField.mixedEmbedding F (a : F) + pM := by rw [← ha]
  refine ⟨a, e.symm pM, ⟨pM, hpM, rfl⟩, ?_⟩
  apply e.injective
  rw [map_add, heDiag, e.apply_symm_apply]
  exact hzM

private theorem covol_arch_fundamental_unique (D : FieldData F) (a : 𝓞 F)
    {p q : InfinitePlace F → ℂ}
    (hp : covolArchToMixedEquiv D p ∈ ZSpan.fundamentalDomain
      (NumberField.mixedEmbedding.latticeBasis F))
    (hq : covolArchToMixedEquiv D q ∈ ZSpan.fundamentalDomain
      (NumberField.mixedEmbedding.latticeBasis F))
    (h : (fun w : InfinitePlace F => w.embedding (a : F)) + p = q) :
    a = 0 ∧ p = q := by
  classical
  let e := covolArchToMixedEquiv D
  let L : Submodule ℤ (NumberField.mixedEmbedding.mixedSpace F) :=
    Submodule.span ℤ (Set.range (NumberField.mixedEmbedding.latticeBasis F))
  letI : Fintype (Module.Free.ChooseBasisIndex ℤ (𝓞 F)) := Fintype.ofFinite _
  have heDiag : e (fun w : InfinitePlace F => w.embedding (a : F)) =
      NumberField.mixedEmbedding F (a : F) := by
    apply Prod.ext
    · funext w
      exact False.elim
        ((NumberField.InfinitePlace.not_isComplex_iff_isReal.mpr w.2)
          (D.isTotallyComplex.isComplex w.1))
    · funext w
      rfl
  have hmix : NumberField.mixedEmbedding F (a : F) + e p = e q := by
    have h' := congrArg e h
    rw [map_add, heDiag] at h'
    exact h'
  have haInt' : NumberField.mixedEmbedding F (a : F) ∈
      NumberField.mixedEmbedding.integerLattice F := by
    change ∃ b : 𝓞 F, NumberField.mixedEmbedding F (algebraMap (𝓞 F) F b) = _
    exact ⟨a, rfl⟩
  have haInt : NumberField.mixedEmbedding F (a : F) ∈ L :=
    (NumberField.mixedEmbedding.mem_span_latticeBasis F).2 haInt'
  let d : L := ⟨NumberField.mixedEmbedding F (a : F), haInt⟩
  have hzero : (0 : L) +ᵥ e q ∈
      ZSpan.fundamentalDomain (NumberField.mixedEmbedding.latticeBasis F) := by
    simpa using hq
  have hshift : (-d) +ᵥ e q ∈
      ZSpan.fundamentalDomain (NumberField.mixedEmbedding.latticeBasis F) := by
    have htrans : -(NumberField.mixedEmbedding F (a : F)) + e q = e p := by
      calc
        -(NumberField.mixedEmbedding F (a : F)) + e q =
            -(NumberField.mixedEmbedding F (a : F)) +
              (NumberField.mixedEmbedding F (a : F) + e p) := by rw [← hmix]
        _ = e p := by abel
    have hshiftAdd : ((-d : L) : NumberField.mixedEmbedding.mixedSpace F) + e q ∈
        ZSpan.fundamentalDomain (NumberField.mixedEmbedding.latticeBasis F) := by
      change -(NumberField.mixedEmbedding F (a : F)) + e q ∈ _
      rw [htrans]
      exact hp
    change ((-d : L) : NumberField.mixedEmbedding.mixedSpace F) + e q ∈ _
    exact hshiftAdd
  have hzeroFloor := (ZSpan.vadd_mem_fundamentalDomain
    (NumberField.mixedEmbedding.latticeBasis F) (0 : L) (e q)).mp hzero
  have hshiftFloor := (ZSpan.vadd_mem_fundamentalDomain
    (NumberField.mixedEmbedding.latticeBasis F) (-d) (e q)).mp hshift
  have hd : d = 0 := by
    have h0d : (0 : L) = -d := hzeroFloor.trans hshiftFloor.symm
    have hneg := congrArg (fun x : L => -x) h0d
    simpa using hneg.symm
  have hmix0 : NumberField.mixedEmbedding F (a : F) = 0 := congrArg Subtype.val hd
  have haF : (a : F) = 0 := NumberField.mixedEmbedding_injective F (by simpa using hmix0)
  have ha : a = 0 := Subtype.ext haF
  refine ⟨ha, ?_⟩
  subst a
  funext w
  simpa using congrFun h w

private theorem exists_measurable_lattice_fundamental_domain
    (S : SData F CE condη) (D : FieldData F) :
    ∃ K : Set S.FS, MeasurableSet K ∧ S.IsLatticeFundamentalDomain K := by
  classical
  letI : MeasurableSpace (∀ v : S.Sf, v.1.adicCompletion F) :=
    borel (∀ v : S.Sf, v.1.adicCompletion F)
  letI : BorelSpace (∀ v : S.Sf, v.1.adicCompletion F) := ⟨rfl⟩
  let O : ∀ v : S.Sf, Set (v.1.adicCompletion F) :=
    fun v => v.1.adicCompletionIntegers F
  let B : Set (∀ v : S.Sf, v.1.adicCompletion F) := Set.pi Set.univ O
  have hOopen (v : S.Sf) : IsOpen (O v) := Valued.isOpen_valuationSubring _
  have hBopen : IsOpen B := by
    apply isOpen_set_pi Set.finite_univ
    intro v hv
    exact hOopen v
  have hBmeas : MeasurableSet B := hBopen.measurableSet
  have hcompletion (v : S.Sf) (z : F) (hz : v.1.valuation F z ≤ 1) :
      algebraMap F (v.1.adicCompletion F) z ∈ v.1.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    change Valued.v (z : v.1.adicCompletion F) ≤ 1
    rw [v.1.valuedAdicCompletion_eq_valuation']
    exact hz
  let e := covolArchToMixedEquiv D
  let P : Set (NumberField.mixedEmbedding.mixedSpace F) :=
    ZSpan.fundamentalDomain (NumberField.mixedEmbedding.latticeBasis F)
  let C : Set (InfinitePlace F → ℂ) := e.symm '' P
  have hPmeas : MeasurableSet P := ZSpan.fundamentalDomain_measurableSet _
  have hCeq : C = e ⁻¹' P := by
    ext z
    constructor
    · rintro ⟨p, hp, rfl⟩
      simpa using hp
    · intro hz
      exact ⟨e z, hz, e.symm_apply_apply z⟩
  have hCmeas : MeasurableSet C := by
    rw [hCeq]
    exact e.continuous.measurable hPmeas
  let K : Set S.FS := B ×ˢ C
  have hKeq : K = Prod.fst ⁻¹' B ∩ Prod.snd ⁻¹' C := by
    ext z
    simp [K]
  have hKmeas : MeasurableSet K := by
    rw [hKeq]
    exact (continuous_fst.measurable hBmeas).inter
      (continuous_snd.measurable hCmeas)
  have hfund : S.IsLatticeFundamentalDomain K := by
    intro x
    obtain ⟨r₀, hr₀⟩ := ArtinPrimitiveRoots.Proofs.A1_LATTICE.s_integer_finite_approx S x.1
    obtain ⟨a, p, hp, harch⟩ := covol_arch_fundamental_reduction D
      (x.2 - fun w => w.embedding (r₀ : F))
    let aR : S.R := algebraMap (𝓞 F) (S.R) a
    let r : S.R := r₀ + aR
    have hrCast : (r : F) = (r₀ : F) + (a : F) := by
      simp [r, aR]
    let k : S.FS := x - S.diag (r : F)
    have hkB : k.1 ∈ B := by
      change ∀ v : S.Sf, v ∈ Set.univ → k.1 v ∈ O v
      intro v _
      have h₁ := hr₀ v
      have h₂ : algebraMap F (v.1.adicCompletion F) (a : F) ∈ O v := by
        simpa [O] using hcompletion v (a : F) (v.1.valuation_le_one a)
      have hsub := (v.1.adicCompletionIntegers F).sub_mem h₁ h₂
      change x.1 v - algebraMap F (v.1.adicCompletion F) (r : F) ∈ O v
      rw [hrCast, map_add]
      simpa [O, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsub
    have hkArch : k.2 ∈ C := by
      have hfun : (fun w : InfinitePlace F => x.2 w - w.embedding (r : F)) = p := by
        funext w
        have hw := congrFun harch w
        have hw' : x.2 w - w.embedding (r₀ : F) = w.embedding (a : F) + p w := by
          simpa using hw
        rw [hrCast, map_add]
        calc
          x.2 w - (w.embedding (r₀ : F) + w.embedding (a : F)) =
              (x.2 w - w.embedding (r₀ : F)) - w.embedding (a : F) := by abel
          _ = (w.embedding (a : F) + p w) - w.embedding (a : F) := by rw [hw']
          _ = p w := by abel
      change (fun w : InfinitePlace F => x.2 w - w.embedding (r : F)) ∈ C
      rw [hfun]
      exact hp
    have hk : k ∈ K := ⟨hkB, hkArch⟩
    have hrep : x = S.diag (r : F) + k := by
      dsimp [k]
      abel
    refine ⟨(r, k), ⟨hk, hrep⟩, ?_⟩
    intro q hq
    rcases q with ⟨s, l⟩
    have hlB : l.1 ∈ B := hq.1.1
    have hlC : l.2 ∈ C := hq.1.2
    have hKfinite (z : S.FS) (hz : z ∈ K) (v : S.Sf) : z.1 v ∈ O v := by
      have hzB : z.1 ∈ B := hz.1
      exact hzB v (by simp)
    have hkO (v : S.Sf) : k.1 v ∈ O v := hKfinite k hk v
    have hlO (v : S.Sf) : l.1 v ∈ O v := by
      exact hKfinite l ⟨hlB, hlC⟩ v
    have hdeltaLocal (v : S.Sf) :
        algebraMap F (v.1.adicCompletion F) ((s : F) - (r : F)) ∈
          v.1.adicCompletionIntegers F := by
      have hkr : x.1 v =
          algebraMap F (v.1.adicCompletion F) (r : F) + k.1 v := by
        have h := congrArg (fun z : S.FS => z.1 v) hrep
        simpa [ArtinPrimitiveRoots.A1.SData.diag] using h
      have hsl : x.1 v =
          algebraMap F (v.1.adicCompletion F) (s : F) + l.1 v := by
        have h := congrArg (fun z : S.FS => z.1 v) hq.2
        simpa [ArtinPrimitiveRoots.A1.SData.diag] using h
      have hR : algebraMap F (v.1.adicCompletion F) (r : F) = x.1 v - k.1 v := by
        calc
          algebraMap F (v.1.adicCompletion F) (r : F) =
              (algebraMap F (v.1.adicCompletion F) (r : F) + k.1 v) - k.1 v := by abel
          _ = x.1 v - k.1 v := by rw [← hkr]
      have hS : algebraMap F (v.1.adicCompletion F) (s : F) = x.1 v - l.1 v := by
        calc
          algebraMap F (v.1.adicCompletion F) (s : F) =
              (algebraMap F (v.1.adicCompletion F) (s : F) + l.1 v) - l.1 v := by abel
          _ = x.1 v - l.1 v := by rw [← hsl]
      have hdelta : algebraMap F (v.1.adicCompletion F) ((s : F) - (r : F)) =
          k.1 v - l.1 v := by
        rw [map_sub]
        calc
          algebraMap F (v.1.adicCompletion F) (s : F) -
              algebraMap F (v.1.adicCompletion F) (r : F) =
              (x.1 v - l.1 v) - (x.1 v - k.1 v) := by rw [hS, hR]
          _ = k.1 v - l.1 v := by abel
      rw [hdelta]
      exact (v.1.adicCompletionIntegers F).sub_mem (hkO v) (hlO v)
    have hval (v : HeightOneSpectrum (𝓞 F)) : v.valuation F ((s : F) - (r : F)) ≤ 1 := by
      by_cases hv : v ∈ S.Sf
      · let vS : S.Sf := ⟨v, hv⟩
        have hvint := hdeltaLocal vS
        simp [HeightOneSpectrum.algebraMap_adicCompletion] at hvint
        rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hvint
        rw [vS.1.valuedAdicCompletion_eq_valuation'] at hvint
        exact hvint
      · exact (s - r).property v hv
    obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F
      ((s : F) - (r : F)) hval
    have hlC' : l.2 ∈ C := hq.1.2
    change l.2 ∈ e.symm '' P at hlC'
    change k.2 ∈ e.symm '' P at hkArch
    obtain ⟨pL, hpL, hpLeq⟩ := hlC'
    obtain ⟨pK, hpK, hpKeq⟩ := hkArch
    have heL : e l.2 = pL := by rw [← hpLeq]; exact e.apply_symm_apply pL
    have heK : e k.2 = pK := by rw [← hpKeq]; exact e.apply_symm_apply pK
    have harchRel : (fun w : InfinitePlace F => w.embedding (b : F)) + l.2 = k.2 := by
      funext w
      have hkr : x.2 w = w.embedding (r : F) + k.2 w := by
        have h := congrArg (fun z : S.FS => z.2 w) hrep
        simpa [ArtinPrimitiveRoots.A1.SData.diag] using h
      have hsl : x.2 w = w.embedding (s : F) + l.2 w := by
        have h := congrArg (fun z : S.FS => z.2 w) hq.2
        simpa [ArtinPrimitiveRoots.A1.SData.diag] using h
      calc
        w.embedding (b : F) + l.2 w =
            w.embedding ((s : F) - (r : F)) + l.2 w := by rw [← hb]
        _ = (w.embedding (s : F) - w.embedding (r : F)) + l.2 w := by rw [map_sub]
        _ = (w.embedding (s : F) + l.2 w) - w.embedding (r : F) := by abel
        _ = x.2 w - w.embedding (r : F) := by rw [← hsl]
        _ = (w.embedding (r : F) + k.2 w) - w.embedding (r : F) := by rw [hkr]
        _ = k.2 w := by abel
    have hbL : e l.2 ∈ P := by rw [heL]; exact hpL
    have hbK : e k.2 ∈ P := by rw [heK]; exact hpK
    obtain ⟨hb0, hklArch⟩ := covol_arch_fundamental_unique D b hbL hbK harchRel
    have hdelta0 : (s : F) - (r : F) = 0 := by
      rw [hb0] at hb
      simpa using hb.symm
    have hsr : s = r := Subtype.ext (sub_eq_zero.mp hdelta0)
    have hsum : S.diag (r : F) + k = S.diag (s : F) + l := hrep.symm.trans hq.2
    rw [hsr] at hsum
    have hkl : k = l := add_left_cancel hsum
    exact Prod.ext hsr hkl.symm
  exact ⟨K, hKmeas, hfund⟩

private instance covolAdicCompletionSeparableSpace (v : FinPlace F) :
    TopologicalSpace.SeparableSpace (v.adicCompletion F) := by
  letI : Countable F := by
    letI : Countable ℚ := inferInstance
    exact Finsupp.Countable.of_moduleFinite (R := ℚ) (M := F)
  exact TopologicalSpace.SeparableSpace.of_denseRange
    (algebraMap F (v.adicCompletion F)) (v.denseRange_algebraMap (K := F))

private instance covolAdicCompletionSecondCountable (v : FinPlace F) :
    SecondCountableTopology (v.adicCompletion F) :=
  UniformSpace.secondCountable_of_separable (v.adicCompletion F)

private instance covolAdicCompletionLocallyCompactSpace (v : FinPlace F) :
    LocallyCompactSpace (v.adicCompletion F) := by
  have hK : IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    ArtinPrimitiveRoots.Proofs.A1_LATTICE.adicCompletionIntegers_compact v
  have hO : IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    Valued.isOpen_valuationSubring _
  have hz : (0 : v.adicCompletion F) ∈ v.adicCompletionIntegers F :=
    (v.adicCompletionIntegers F).zero_mem
  exact IsCompact.locallyCompactSpace_of_mem_nhds_of_addGroup hK
    (hO.mem_nhds hz)

private theorem covol_self_dual_measure_unique
    (S : SData F CE condη) (A : AddCharData F)
    (μ ν : S.SelfDualMeasure A) (f : S.BruhatSchwartz)
    (hf : (f : S.FS → ℂ) 0 ≠ 0) : μ.measure = ν.measure := by
  classical
  letI : ∀ v : S.Sf, SecondCountableTopology (v.1.adicCompletion F) :=
    fun v => inferInstance
  letI : ∀ v : S.Sf, LocallyCompactSpace (v.1.adicCompletion F) :=
    fun v => inferInstance
  letI : SecondCountableTopology S.FS := inferInstance
  letI : LocallyCompactSpace S.FS := inferInstance
  letI : Measure.IsAddHaarMeasure μ.measure := μ.isHaar
  letI : Measure.IsAddHaarMeasure ν.measure := ν.isHaar
  let c : NNReal := Measure.addHaarScalarFactor μ.measure ν.measure
  have hmeasure : μ.measure = (c : ENNReal) • ν.measure := by
    simpa [c] using Measure.isAddLeftInvariant_eq_smul μ.measure ν.measure
  have hF (g : S.FS → ℂ) :
      S.fourier A μ.measure g = fun y => (c : ℂ) * S.fourier A ν.measure g y := by
    funext y
    simp only [SData.fourier]
    rw [hmeasure, MeasureTheory.integral_smul_measure]
    simp [c, smul_eq_mul]
  have hF_smul (d : ℂ) (g : S.FS → ℂ) :
      S.fourier A ν.measure (fun y => d * g y) =
        (fun x => d * S.fourier A ν.measure g x) := by
    funext x
    simp only [SData.fourier]
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    funext y
    ring
  have hdouble (x : S.FS) :
      S.fourier A μ.measure (S.fourier A μ.measure (f : S.FS → ℂ)) x =
        (c : ℂ) ^ 2 *
          S.fourier A ν.measure (S.fourier A ν.measure (f : S.FS → ℂ)) x := by
    calc
      _ = (c : ℂ) * S.fourier A ν.measure
          (S.fourier A μ.measure (f : S.FS → ℂ)) x := by rw [hF]
      _ = (c : ℂ) * S.fourier A ν.measure
          (fun y => (c : ℂ) * S.fourier A ν.measure (f : S.FS → ℂ) y) x := by rw [hF f]
      _ = _ := by rw [hF_smul]; ring
  have hμ := μ.fourier_inversion f 0
  rw [hdouble, ν.fourier_inversion f 0] at hμ
  have hc2 : (c : ℂ) ^ 2 = 1 := (mul_eq_right₀ hf).mp (by simpa using hμ)
  have hcReal : (c : ℝ) ^ 2 = 1 := by exact_mod_cast hc2
  have hc : c = 1 := by
    apply Subtype.ext
    rcases sq_eq_one_iff.mp hcReal with h | h
    · exact h
    · have hcNonneg : 0 ≤ (c : ℝ) := NNReal.coe_nonneg c
      linarith
  simpa [hc] using hmeasure

private theorem measurable_fundamental_domain_measure_one
    (S : SData F CE condη) (D : FieldData F) (A : AddCharData F)
    (μ : S.SelfDualMeasure A) (K : Set S.FS)
    (hK : MeasurableSet K ∧ S.IsLatticeFundamentalDomain K) :
    μ.measure K = 1 := by
  sorry

/-- The diagonal copy of `R` has covolume one for the self-dual Haar measure. -/
theorem SData.diagR_covolume_one (S : SData F CE condη) (D : FieldData F)
    (A : AddCharData F)
    (μ : S.SelfDualMeasure A) :
    ∃ K : Set S.FS, MeasurableSet K ∧ S.IsLatticeFundamentalDomain K ∧ μ.measure K = 1 := by
  obtain ⟨K, hmeas, hfund⟩ := exists_measurable_lattice_fundamental_domain S D
  exact ⟨K, hmeas, hfund,
    measurable_fundamental_domain_measure_one S D A μ K ⟨hmeas, hfund⟩⟩

/-- Poisson summation on `R` for Bruhat--Schwartz functions on `F_S`, including absolute
convergence of both lattice sums. -/
theorem SData.poisson (S : SData F CE condη) (D : FieldData F) (A : AddCharData F)
    (μ : S.SelfDualMeasure A) (f : S.BruhatSchwartz) :
    Summable (fun m : S.R => ‖(f : S.FS → ℂ) (S.diag (m : F))‖) ∧
      Summable (fun ν : S.R => ‖S.fourier A μ.measure (f : S.FS → ℂ) (S.diag (ν : F))‖) ∧
      ∑' m : S.R, (f : S.FS → ℂ) (S.diag (m : F)) =
        ∑' ν : S.R, S.fourier A μ.measure (f : S.FS → ℂ) (S.diag (ν : F)) := by
  sorry

/-! ## Scaling and the norm identity -/

/-- The annihilator of `aR` is `a⁻¹R`. -/
theorem SData.annihilator_diag_mul (S : SData F CE condη) (D : FieldData F)
    (A : AddCharData F)
    (a : Fˣ) :
    S.annihilator A (Set.range fun x : S.R => S.diag ((a : F) * (x : F))) =
      Set.range fun x : S.R => S.diag ((a : F)⁻¹ * (x : F)) := by
  classical
  have hself := S.diagR_eq_annihilator D A
  have ha0 : (a : F) ≠ 0 := Units.ne_zero a
  ext y
  constructor
  · intro hy
    have hmul_ann : S.diag (a : F) * y ∈ S.annihilator A S.diagR := by
      intro x hx
      rcases hx with ⟨r, rfl⟩
      have h := hy (S.diag ((a : F) * (r : F))) ⟨r, rfl⟩
      simpa [map_mul, mul_assoc, mul_comm, mul_left_comm] using h
    have hmul_mem : S.diag (a : F) * y ∈ S.diagR := hself.symm ▸ hmul_ann
    rcases hmul_mem with ⟨r, hr⟩
    change S.diag (r : F) = S.diag (a : F) * y at hr
    refine ⟨r, ?_⟩
    calc
      S.diag ((a : F)⁻¹ * (r : F)) =
          S.diag ((a : F)⁻¹) * S.diag (r : F) := by rw [map_mul]
      _ = S.diag ((a : F)⁻¹) * (S.diag (a : F) * y) := by rw [hr]
      _ = y := by
        calc
          S.diag ((a : F)⁻¹) * (S.diag (a : F) * y) =
              (S.diag ((a : F)⁻¹) * S.diag (a : F)) * y := by rw [mul_assoc]
          _ = S.diag (1 : F) * y := by rw [← map_mul, inv_mul_cancel₀ ha0]
          _ = y := by simp
  · intro hy
    rcases hy with ⟨r, hr⟩
    subst y
    intro x hx
    rcases hx with ⟨s, rfl⟩
    have hr_diag : S.diag (r : F) ∈ S.diagR := ⟨r, rfl⟩
    have hr_ann : S.diag (r : F) ∈ S.annihilator A S.diagR :=
      hself ▸ hr_diag
    have h := hr_ann (S.diag (s : F)) ⟨s, rfl⟩
    have hpair :
        S.diag ((a : F) * (s : F)) * S.diag ((a : F)⁻¹ * (r : F)) =
          S.diag (s : F) * S.diag (r : F) := by
      calc
        S.diag ((a : F) * (s : F)) * S.diag ((a : F)⁻¹ * (r : F)) =
            S.diag (((a : F) * (s : F)) * ((a : F)⁻¹ * (r : F))) := by
              simp only [map_mul]
        _ = S.diag ((s : F) * (r : F)) := by
          congr 1
          field_simp [ha0]
        _ = S.diag (s : F) * S.diag (r : F) := by simp only [map_mul]
    change S.e A
      (S.diag ((a : F) * (s : F)) * S.diag ((a : F)⁻¹ * (r : F))) = 1
    rw [hpair]
    exact h

/-- The norm identity in `lem:s-lattice` with the total-complexity hypothesis made explicit.
This is the corrected version of the frozen `SData.absS_diag_eq_norm`, whose interface omits
`FieldData F`. -/
theorem SData.absS_diag_eq_norm_ofFieldData (S : SData F CE condη) (D : FieldData F)
    (x : F) (I : Ideal (𝓞 F)) (hI : S.IsExterior I) (hx : S.IsGen x I) :
    S.absS (S.diag x) = Ideal.absNorm I := by
  have : IsTotallyComplex F := D.isTotallyComplex
  exact S.absS_diag_eq_norm x I hI hx

/-- Scaling Poisson summation from `R` to the exterior fractional ideal `aR`. -/
theorem SData.poisson_scaled (S : SData F CE condη) (D : FieldData F) (A : AddCharData F)
    (μ : S.SelfDualMeasure A) (f : S.BruhatSchwartz) (a : Fˣ) (I : Ideal (𝓞 F))
    (hI : S.IsExterior I) (ha : S.IsGen (a : F) I) :
    ∑' m : S.R, (f : S.FS → ℂ) (S.diag ((a : F) * (m : F))) =
      ((Ideal.absNorm I : ℝ) : ℂ)⁻¹ *
        ∑' ν : S.R, S.fourier A μ.measure (f : S.FS → ℂ)
          (S.diag ((a : F)⁻¹ * (ν : F))) := by
  sorry

/-- Every nonzero S-integer has S-norm at least one. -/
theorem SData.absS_diag_ge_one (S : SData F CE condη) (D : FieldData F)
    (x : S.R) (hx : (x : F) ≠ 0) :
    1 ≤ S.absS (S.diag (x : F)) := by
  have : IsTotallyComplex F := D.isTotallyComplex
  have hprod := prod_abs_eq_one hx
  have hf_supp : (Function.mulSupport fun v => ‖FinitePlace.embedding v (x : F)‖).Finite :=
    finitePlace_mk_hasFiniteMulSupport hx
  have h_split : (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖FinitePlace.embedding v (x : F)‖) =
      (∏ v ∈ S.Sf, ‖FinitePlace.embedding v (x : F)‖) * ∏ᶠ v ∉ S.Sf, ‖FinitePlace.embedding v (x : F)‖ := by
    have h_union := finprod_mem_union' (hst := disjoint_compl_right)
      (hs := S.Sf.finite_toSet.inter_of_left _)
      (ht := Set.Finite.subset hf_supp Set.inter_subset_right)
      (f := fun v => ‖FinitePlace.embedding v (x : F)‖)
    rw [Set.union_compl_self, finprod_mem_univ] at h_union
    rw [finprod_mem_coe_finset] at h_union
    exact h_union
  have h_prod_decomp : (∏ᶠ w : FinitePlace F, w (x : F)) =
      (∏ v ∈ S.Sf, ‖FinitePlace.embedding v (x : F)‖) * ∏ᶠ v ∉ S.Sf, ‖FinitePlace.embedding v (x : F)‖ := by
    rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
    change (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖FinitePlace.embedding v (x : F)‖) = _
    exact h_split
  rw [h_prod_decomp] at hprod
  have h_absS : S.absS (S.diag (x : F)) =
      (∏ v ∈ S.Sf, ‖FinitePlace.embedding v (x : F)‖) * ∏ w : InfinitePlace F, w (x : F) ^ w.mult :=
    absS_diag_eq S (x : F)
  have h_prod_absS : S.absS (S.diag (x : F)) * (∏ᶠ v ∉ S.Sf, ‖FinitePlace.embedding v (x : F)‖) = 1 := by
    rw [h_absS]
    calc ((∏ v ∈ S.Sf, ‖FinitePlace.embedding v (x : F)‖) * ∏ w : InfinitePlace F, w (x : F) ^ w.mult) *
          (∏ᶠ v ∉ S.Sf, ‖FinitePlace.embedding v (x : F)‖)
      _ = (∏ w : InfinitePlace F, w (x : F) ^ w.mult) *
          ((∏ v ∈ S.Sf, ‖FinitePlace.embedding v (x : F)‖) * ∏ᶠ v ∉ S.Sf, ‖FinitePlace.embedding v (x : F)‖) := by ring
      _ = 1 := hprod
  have h_eq : (∏ᶠ v ∉ S.Sf, ‖FinitePlace.embedding v (x : F)‖) =
      ∏ v ∈ hf_supp.toFinset with v ∉ S.Sf, ‖FinitePlace.embedding v (x : F)‖ :=
    finprod_mem_eq_prod_filter (fun v => ‖FinitePlace.embedding v (x : F)‖) ((S.Sf : Set _)ᶜ) hf_supp
  have hP_le_one : (∏ᶠ v ∉ S.Sf, ‖FinitePlace.embedding v (x : F)‖) ≤ 1 := by
    rw [h_eq]
    refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun v hv =>
      norm_embedding_le_one_of_valuation_le_one v (x : F) (x.property v (Finset.mem_filter.mp hv).2)
  have h_absS_nonneg : 0 ≤ S.absS (S.diag (x : F)) := by
    rw [h_absS]
    refine mul_nonneg (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      (Finset.prod_nonneg fun w _ => ?_)
    exact pow_nonneg (w.1.nonneg _) _
  calc 1
    _ = S.absS (S.diag (x : F)) * (∏ᶠ v ∉ S.Sf, ‖FinitePlace.embedding v (x : F)‖) := h_prod_absS.symm
    _ ≤ S.absS (S.diag (x : F)) * 1 := mul_le_mul_of_nonneg_left hP_le_one h_absS_nonneg
    _ = S.absS (S.diag (x : F)) := mul_one _

/-! ## Compactness modulo sixth powers of S-units -/

/-- The norm-one subgroup of `F_Sˣ`. -/
def SData.FSOne (S : SData F CE condη) :=
  {x : S.FSˣ // S.absS (x : S.FS) = 1}

/-- Two norm-one elements differ by the sixth power of a diagonal S-unit. -/
def SData.fsOneRel (S : SData F CE condη) (x y : S.FSOne) : Prop :=
  ∃ u : S.US, x.1 = (S.diagU (u : Fˣ)) ^ 6 * y.1

/-- The equivalence relation defining `F_S^1 / U_S^6`. -/
def SData.fsOneSetoid (S : SData F CE condη) : Setoid S.FSOne where
  r := S.fsOneRel
  iseqv := {
    refl := by
      intro x
      change ∃ u : S.US, x.1 = (S.diagU (u : Fˣ)) ^ 6 * x.1
      refine ⟨1, ?_⟩
      simp
    symm := by
      intro x y h
      rcases h with ⟨u, hu⟩
      refine ⟨u⁻¹, ?_⟩
      have hmap : S.diagU ((u⁻¹ : S.US) : Fˣ) = (S.diagU (u : Fˣ))⁻¹ := by
        rw [show ((u⁻¹ : S.US) : Fˣ) = (u : Fˣ)⁻¹ by rfl, map_inv]
      rw [hmap, hu]
      group
    trans := by
      intro x y z hxy hyz
      rcases hxy with ⟨u, hu⟩
      rcases hyz with ⟨v, hv⟩
      refine ⟨u * v, ?_⟩
      have hmap : S.diagU ((u * v : S.US) : Fˣ) =
          S.diagU (u : Fˣ) * S.diagU (v : Fˣ) := by
        rw [show ((u * v : S.US) : Fˣ) = (u : Fˣ) * (v : Fˣ) by rfl, map_mul]
      rw [hmap]
      calc
        x.1 = (S.diagU (u : Fˣ)) ^ 6 * y.1 := hu
        _ = (S.diagU (u : Fˣ) * S.diagU (v : Fˣ)) ^ 6 * z.1 := by
          rw [hv, mul_pow]
          group
  }

private theorem S_units_finite_mod_six (S : SData F CE condη) :
    Finite (S.US ⧸ (powMonoidHom 6 : S.US →* S.US).range) := by
  sorry

private theorem fsOne_compact_representatives (S : SData F CE condη) (D : FieldData F) :
    ∃ K : Set S.FS, IsCompact K ∧
      ∀ x : S.FSOne, ∃ y : S.FSOne, (y.1 : S.FS) ∈ K ∧ S.fsOneRel x y := by
  sorry

/-- Compactness of `F_S^1/U_S^6`, stated as a compact set of representatives for its quotient. -/
theorem SData.FSOne_quotient_compact (S : SData F CE condη) (D : FieldData F) :
    ∃ K : Set S.FS, IsCompact K ∧
      ∀ x : S.FSOne, ∃ y : S.FSOne, (y.1 : S.FS) ∈ K ∧ S.fsOneRel x y := by
  exact fsOne_compact_representatives S D

end ArtinPrimitiveRoots.A1
