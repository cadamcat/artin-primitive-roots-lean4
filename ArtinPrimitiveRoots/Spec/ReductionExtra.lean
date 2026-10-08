import ArtinPrimitiveRoots.Spec.Stage1
import Mathlib.LinearAlgebra.Countable
import Mathlib.Topology.Bases
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Remaining reduction-theory nodes R8--R10 and R12--R14. -/

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- R8 `spec:siegel-cover` — P-SPEC.md:221, 308–313. The Siegel sets with the R1 translation
domains, R4 balance constants, and R7 Minkowski scale cover every point modulo `Γ`. Correction
from review lane `rev-spec`: use the Siegel sets with the doubled balance bound. Correction from
`sol-gate-spec`: calibrate the Minkowski scale and require pointwise translation coverage. -/
theorem R8_siegel_cover (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (d : SiegelData F Γ) :
    ∀ z : X F, ∃ i : d.ι, ∃ γ : Γ,
      (d.σ i)⁻¹ • ((γ : SL(2,𝓞 F)) • z) ∈ SiegelData.setAt F d i := by
  sorry

/-- R9 `spec:proper` — P-SPEC.md:222, 315–324. Arithmetic compact intersections and Siegel-set
intersections are finite; freeness gives disjoint neighborhoods for nonidentity elements. -/
theorem R9_proper (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (d : SiegelData F Γ) :
    (∀ K K' : Set (X F), IsCompact K → IsCompact K' →
      {γ : SL(2,𝓞 F) | ∃ z ∈ K, γ • z ∈ K'}.Finite) ∧
    {γ : Γ | ∃ z ∈ SiegelData.unionSet F d,
      (γ : SL(2,𝓞 F)) • z ∈ SiegelData.unionSet F d}.Finite ∧
    (∀ (hfree : FreeAction F Γ) (z : X F),
      ∃ U : Set (X F), IsOpen U ∧ z ∈ U ∧
        ∀ γ : Γ, γ ≠ 1 → Disjoint ((fun x => (γ : SL(2,𝓞 F)) • x) '' U) U) := by
  sorry

/-- R10 `spec:cusp-separation` — P-SPEC.md:223, 326–328. Above a uniform height threshold,
large representatives at one cusp differ by its stabilizer; compact sets meet only finitely many
high-height cusp cosets. Correction from review lane `rev-spec`: require a common sufficiently
large threshold for each representative set. -/
theorem R10_cusp_separation (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] :
    (∀ σ : SL(2,F), ∃ A₀ : ℝ, 1 ≤ A₀ ∧
      ∀ A : ℝ, A₀ ≤ A → ∀ γ γ' : Γ, ∀ z : X F,
        A ≤ normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
        A ≤ normHeight F (σ⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
        γ' * γ⁻¹ ∈ cuspStab F Γ σ) ∧
    (∀ (d : SiegelData F Γ), ∃ A₀ : ℝ, 1 ≤ A₀ ∧
      ∀ A : ℝ, A₀ ≤ A → ∀ i j : d.ι, ∀ γ γ' : Γ, ∀ z : X F,
        A ≤ normHeight F ((d.σ i)⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
        A ≤ normHeight F ((d.σ j)⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
        i = j ∧ γ' * γ⁻¹ ∈ cuspStab F Γ (d.σ i)) ∧
    (∀ σ : SL(2,F), ∀ K : Set (X F), IsCompact K → ∀ A : ℝ, 0 < A →
      {q : CuspCosets F Γ σ | ∃ z ∈ K,
        A ≤ normHeight F (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • z))}.Finite) := by
  sorry

private theorem normHeight_ptX'_eq (x : InfinitePlace F → ℂ)
    (y : InfinitePlace F → ℝ) (hy : ∀ w, 0 < y w) :
    normHeight F (ptX' F x y) = ∏ w : InfinitePlace F, y w := by
  change (∏ w : InfinitePlace F, height ((ptX' F x y) w)) = _
  apply Finset.prod_congr rfl
  intro w hw
  exact (G1_h3_basics (F := F)).1 (x w) (y w) (hy w)

private theorem coordsX_ptX'_eq (x : InfinitePlace F → ℂ)
    (y : InfinitePlace F → ℝ) (hy : ∀ w, 0 < y w) :
    coordsX F (ptX' F x y) = fun w => (x w, y w) := by
  funext w
  exact Prod.ext
    ((G1_h3_basics (F := F)).2.1 (x w) (y w) (hy w))
    ((G1_h3_basics (F := F)).1 (x w) (y w) (hy w))

private theorem secondCountable_X : SecondCountableTopology (X F) := by
  rcases (G1_h3_basics (F := F)) with
    ⟨_, _, _, _, _, _, _, _, _, _, _, ⟨e, _, _⟩⟩
  exact e.symm.secondCountableTopology

private theorem secondCountable_H3 (F : Type) [Field F] [NumberField F]
    [IsTotallyComplex F] : SecondCountableTopology H3 := by
  letI : SecondCountableTopology (X F) := secondCountable_X (F := F)
  let w₀ : InfinitePlace F := Classical.choice inferInstance
  let c : H3 → X F := fun z _ => z
  let eval : X F → H3 := fun z => z w₀
  have hc : Continuous c := by
    change Continuous (fun z : H3 => fun _ : InfinitePlace F => z)
    apply continuous_pi
    intro w
    exact continuous_id
  have heval : Continuous eval := continuous_apply w₀
  have hleft : Function.LeftInverse eval c := by
    intro z
    simp [eval, c]
  exact hleft.isEmbedding heval hc |>.secondCountableTopology

private theorem borelSpace_X : BorelSpace (X F) := by
  letI : SecondCountableTopology H3 := secondCountable_H3 F
  letI : BorelSpace H3 := ⟨rfl⟩
  letI : Countable (InfinitePlace F) := Finite.to_countable
  change BorelSpace (∀ w : InfinitePlace F, H3)
  exact Pi.borelSpace

private theorem opensMeasurable_X : OpensMeasurableSpace (X F) := by
  letI : BorelSpace (X F) := borelSpace_X (F := F)
  exact BorelSpace.opensMeasurable

private theorem coordsX_measurable : Measurable (coordsX F) := by
  rcases (G1_h3_basics (F := F)) with
    ⟨_, _, _, _, _, _, _, _, _, _, _, ⟨e, _, hcoord⟩⟩
  letI : BorelSpace (X F) := borelSpace_X (F := F)
  letI : OpensMeasurableSpace (X F) := opensMeasurable_X (F := F)
  have hcont : Continuous (fun z : X F => (e.symm z).val) :=
    continuous_subtype_val.comp e.symm.continuous
  have heq : (fun z : X F => (e.symm z).val) = coordsX F := funext hcoord
  rw [← heq]
  exact hcont.measurable

private theorem ptX_coordsX (z : X F) : ptX F (coordsX F z) = z := by
  rcases (G1_h3_basics (F := F)) with
    ⟨_, _, _, _, _, _, _, _, _, _, _, ⟨e, he, hcoord⟩⟩
  calc
    ptX F (coordsX F z) = ptX F ((e.symm z).val) := congrArg (ptX F) (hcoord z).symm
    _ = e (e.symm z) := (he (e.symm z)).symm
    _ = z := e.apply_symm_apply z

private theorem coordsX_ptX (p : Coord F) (hp : p ∈ posSet F) :
    coordsX F (ptX F p) = p := by
  rcases (G1_h3_basics (F := F)) with
    ⟨_, _, _, _, _, _, hcoord, _, _, _, _, _⟩
  exact hcoord p hp

private def siegelCoordRegion (P : Set (InfinitePlace F → ℂ)) (B c : ℝ) : Set (Coord F) :=
  {p | (fun w => (p w).1) ∈ P ∧ IsBalancedHeights F B (fun w => (p w).2) ∧
    c ≤ ∏ w : InfinitePlace F, (p w).2}

private theorem balancedHeights_measurableSet (B : ℝ) :
    MeasurableSet {y : InfinitePlace F → ℝ | IsBalancedHeights F B y} := by
  have hpos : MeasurableSet {y : InfinitePlace F → ℝ | ∀ w, 0 < y w} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun w => measurableSet_Ioi.preimage (measurable_pi_apply w)
  have hlog (w : InfinitePlace F) : Measurable (fun y : InfinitePlace F → ℝ => Real.log (y w)) :=
    Real.measurable_log.comp (measurable_pi_apply w)
  have hsum : Measurable (fun y : InfinitePlace F → ℝ =>
      ∑ w : InfinitePlace F, Real.log (y w)) :=
    Finset.measurable_fun_sum Finset.univ (fun w hw => hlog w)
  have hbalFun (w : InfinitePlace F) : Measurable (fun y : InfinitePlace F → ℝ =>
      |Real.log (y w) - (placeCount F)⁻¹ *
        ∑ w' : InfinitePlace F, Real.log (y w')|) :=
    ((hlog w).sub (measurable_const.mul hsum)).abs
  have hbal : MeasurableSet {y : InfinitePlace F → ℝ |
      ∀ w, |Real.log (y w) - (placeCount F)⁻¹ *
        ∑ w' : InfinitePlace F, Real.log (y w')| ≤ B} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun w => measurableSet_Iic.preimage (hbalFun w)
  change MeasurableSet ({y : InfinitePlace F → ℝ | ∀ w, 0 < y w} ∩
    {y : InfinitePlace F → ℝ | ∀ w, |Real.log (y w) - (placeCount F)⁻¹ *
      ∑ w' : InfinitePlace F, Real.log (y w')| ≤ B})
  exact hpos.inter hbal

private theorem siegelCoordRegion_measurableSet (P : Set (InfinitePlace F → ℂ))
    (hP : MeasurableSet P) (B c : ℝ) : MeasurableSet (siegelCoordRegion P B c) := by
  have hhor : Measurable (fun p : Coord F => fun w => (p w).1) := by
    apply measurable_pi_iff.mpr
    intro w
    exact measurable_fst.comp (measurable_pi_apply w)
  have hy : Measurable (fun p : Coord F => fun w => (p w).2) := by
    apply measurable_pi_iff.mpr
    intro w
    exact measurable_snd.comp (measurable_pi_apply w)
  have hprod : Measurable (fun p : Coord F => ∏ w : InfinitePlace F, (p w).2) := by
    simpa using Finset.measurable_fun_prod Finset.univ
      (fun w hw => measurable_snd.comp (measurable_pi_apply w))
  have hlow : MeasurableSet {p : Coord F | c ≤ ∏ w : InfinitePlace F, (p w).2} :=
    measurableSet_Ici.preimage hprod
  dsimp [siegelCoordRegion]
  change MeasurableSet ((fun p : Coord F => fun w => (p w).1) ⁻¹' P ∩
    ((fun p : Coord F => fun w => (p w).2) ⁻¹'
      {y : InfinitePlace F → ℝ | IsBalancedHeights F B y} ∩
    {p : Coord F | c ≤ ∏ w : InfinitePlace F, (p w).2}))
  exact (hP.preimage hhor).inter
    ((balancedHeights_measurableSet (F := F) B).preimage hy |>.inter hlow)

private theorem siegelSet_eq_coords_preimage (P : Set (InfinitePlace F → ℂ)) (B c : ℝ) :
    siegelSet F P B c = (coordsX F) ⁻¹' siegelCoordRegion P B c := by
  ext z
  constructor
  · rintro ⟨x, y, hz, hx, hbal, hlo⟩
    have hcoord : coordsX F z = fun w => (x w, y w) := by
      rw [hz]
      exact coordsX_ptX'_eq x y hbal.1
    have hN := normHeight_ptX'_eq x y hbal.1
    refine ⟨?_, ?_, ?_⟩
    · simpa [hcoord] using hx
    · simpa [hcoord] using hbal
    · have hp : c ≤ ∏ w : InfinitePlace F, y w := by simpa [hN] using hlo
      simpa [hcoord] using hp
  · rintro ⟨hx, hbal, hlo⟩
    let x : InfinitePlace F → ℂ := fun w => (coordsX F z w).1
    let y : InfinitePlace F → ℝ := fun w => (coordsX F z w).2
    have hbalY : IsBalancedHeights F B y := by simpa [y] using hbal
    have hrec := ptX_coordsX (F := F) z
    have hN := normHeight_ptX'_eq x y hbalY.1
    refine ⟨x, y, ?_, ?_, hbalY, ?_⟩
    · calc
        z = ptX F (coordsX F z) := hrec.symm
        _ = ptX' F x y := rfl
    · simpa [x] using hx
    · simpa [y, hN] using hlo

private theorem measurableSet_siegelSet (P : Set (InfinitePlace F → ℂ))
    (hP : MeasurableSet P) (B c : ℝ) : MeasurableSet (siegelSet F P B c) := by
  rw [siegelSet_eq_coords_preimage (F := F) P B c]
  exact (siegelCoordRegion_measurableSet (F := F) P hP B c).preimage
    (coordsX_measurable (F := F))

private def realCoordSeq (ws : List (InfinitePlace F)) (p : Coord F) : List ℝ :=
  ws.flatMap fun w => [(p w).1.re, (p w).1.im, (p w).2]

private def lexLEList (l m : List ℝ) : Prop :=
  l = m ∨ List.Lex (· < ·) l m

private theorem lexLEList_cons (a b : ℝ) (l m : List ℝ) :
    lexLEList (a :: l) (b :: m) ↔ a < b ∨ a = b ∧ lexLEList l m := by
  constructor
  · rintro (hEq | hLex)
    · simp only [List.cons.injEq] at hEq
      exact Or.inr ⟨hEq.1, Or.inl hEq.2⟩
    · cases hLex with
      | rel hlt => exact Or.inl hlt
      | cons htail => exact Or.inr ⟨rfl, Or.inr htail⟩
  · rintro (hlt | ⟨hab, htail⟩)
    · exact Or.inr (List.Lex.rel hlt)
    · subst b
      rcases htail with hEq | hLex
      · subst m
        exact Or.inl rfl
      · exact Or.inr (List.Lex.cons hLex)

private theorem measurableSet_lexCoordSeq (ws : List (InfinitePlace F)) :
    MeasurableSet {p : Coord F × Coord F |
      lexLEList (realCoordSeq ws p.1) (realCoordSeq ws p.2)} := by
  induction ws with
  | nil => simp [realCoordSeq, lexLEList]
  | cons w ws ih =>
    have h1 : Measurable (fun p : Coord F × Coord F => (p.1 w).1.re) := by fun_prop
    have h1' : Measurable (fun p : Coord F × Coord F => (p.2 w).1.re) := by fun_prop
    have h2 : Measurable (fun p : Coord F × Coord F => (p.1 w).1.im) := by fun_prop
    have h2' : Measurable (fun p : Coord F × Coord F => (p.2 w).1.im) := by fun_prop
    have h3 : Measurable (fun p : Coord F × Coord F => (p.1 w).2) := by fun_prop
    have h3' : Measurable (fun p : Coord F × Coord F => (p.2 w).2) := by fun_prop
    have hlt1 : MeasurableSet {p : Coord F × Coord F | (p.1 w).1.re < (p.2 w).1.re} :=
      measurableSet_lt h1 h1'
    have heq1 : MeasurableSet {p : Coord F × Coord F | (p.1 w).1.re = (p.2 w).1.re} :=
      measurableSet_eq_fun h1 h1'
    have hlt2 : MeasurableSet {p : Coord F × Coord F | (p.1 w).1.im < (p.2 w).1.im} :=
      measurableSet_lt h2 h2'
    have heq2 : MeasurableSet {p : Coord F × Coord F | (p.1 w).1.im = (p.2 w).1.im} :=
      measurableSet_eq_fun h2 h2'
    have hlt3 : MeasurableSet {p : Coord F × Coord F | (p.1 w).2 < (p.2 w).2} :=
      measurableSet_lt h3 h3'
    have heq3 : MeasurableSet {p : Coord F × Coord F | (p.1 w).2 = (p.2 w).2} :=
      measurableSet_eq_fun h3 h3'
    change MeasurableSet {p : Coord F × Coord F |
      lexLEList ([((p.1 w).1.re), (p.1 w).1.im, (p.1 w).2] ++ realCoordSeq ws p.1)
        ([((p.2 w).1.re), (p.2 w).1.im, (p.2 w).2] ++ realCoordSeq ws p.2)}
    simp only [lexLEList_cons, List.cons_append]
    exact hlt1.union (heq1.inter (hlt2.union (heq2.inter
      (hlt3.union (heq3.inter ih)))))

private theorem measurableSet_coordLexLE :
    MeasurableSet {p : Coord F × Coord F | coordLexLE F p.1 p.2} := by
  simpa [coordLexLE, realCoordList, realCoordSeq, lexLEList] using
    measurableSet_lexCoordSeq (F := F) (Finset.univ.toList)

private theorem realCoordSeq_injective_on (ws : List (InfinitePlace F))
    (p q : Coord F) (h : realCoordSeq ws p = realCoordSeq ws q) :
    ∀ w ∈ ws, p w = q w := by
  induction ws with
  | nil => intro w hw; simp at hw
  | cons w ws ih =>
    have hHead : [(p w).1.re, (p w).1.im, (p w).2] =
        [(q w).1.re, (q w).1.im, (q w).2] := by
      simpa [realCoordSeq] using congrArg (List.take 3) h
    have hTail : realCoordSeq ws p = realCoordSeq ws q := by
      simpa [realCoordSeq] using congrArg (List.drop 3) h
    have hparts := hHead
    simp only [List.cons.injEq] at hparts
    rcases hparts with ⟨hre, him, hrest⟩
    have hy := hrest.1
    have hcomplex : (p w).1 = (q w).1 := Complex.ext hre him
    have hplace : p w = q w := Prod.ext hcomplex hy
    intro w' hw'
    rcases List.mem_cons.mp hw' with rfl | hw'
    · exact hplace
    · exact ih hTail w' hw'

private theorem realCoordList_injective : Function.Injective (realCoordList F) := by
  intro p q hpq
  have hseq : realCoordSeq (Finset.univ.toList) p = realCoordSeq (Finset.univ.toList) q := by
    simpa [realCoordList, realCoordSeq] using hpq
  funext w
  apply realCoordSeq_injective_on (Finset.univ.toList) p q hseq w
  simp

private theorem coordLexLE_iff_listLE (p q : Coord F) :
    coordLexLE F p q ↔ realCoordList F p ≤ realCoordList F q := by
  change (realCoordList F p = realCoordList F q ∨
    List.Lex (· < ·) (realCoordList F p) (realCoordList F q)) ↔ _
  rw [le_iff_lt_or_eq]
  constructor
  · rintro (heq | hlex)
    · exact Or.inr heq
    · exact Or.inl ((List.lt_iff_lex_lt _ _).2 hlex)
  · rintro (hlt | heq)
    · exact Or.inr ((List.lt_iff_lex_lt _ _).1 hlt)
    · exact Or.inl heq

private theorem continuous_h3_action (g : SL(2,ℂ)) :
    Continuous (fun z : H3 => g • z) := by
  have hmul : Continuous (fun h : SL(2,ℂ) => g * h) := by
    apply Continuous.subtype_mk
    change Continuous (fun h : SL(2,ℂ) =>
      (g : Matrix (Fin 2) (Fin 2) ℂ) * (h : Matrix (Fin 2) (Fin 2) ℂ))
    exact continuous_const.mul continuous_subtype_val
  apply (QuotientGroup.isQuotientMap_mk SU2).continuous_iff.mpr
  exact continuous_quotient_mk'.comp hmul

private theorem continuousSL2FAction (g : SL(2,F)) :
    Continuous (fun z : X F => g • z) := by
  apply continuous_pi
  intro w
  exact (continuous_h3_action (toInf F g w)).comp (continuous_apply w)

private theorem siegelUnion_measurable (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (d : SiegelData F Γ) : MeasurableSet (SiegelData.unionSet F d) := by
  classical
  letI : BorelSpace (X F) := borelSpace_X (F := F)
  letI : OpensMeasurableSpace (X F) := opensMeasurable_X (F := F)
  letI : Fintype d.ι := d.fintype
  have hrepr : SiegelData.unionSet F d =
      ⋃ i : d.ι, (fun z : X F => (d.σ i)⁻¹ • z) ⁻¹' SiegelData.setAt F d i := by
    ext z
    simp only [SiegelData.unionSet, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨i, x, hx, rfl⟩
      refine ⟨i, ?_⟩
      simpa using hx
    · rintro ⟨i, hx⟩
      exact ⟨i, (d.σ i)⁻¹ • z, hx, by simp⟩
  rw [hrepr]
  apply MeasurableSet.iUnion
  intro i
  have hset : MeasurableSet (SiegelData.setAt F d i) := by
    simpa [SiegelData.setAt] using
      (measurableSet_siegelSet (F := F) (d.P i) (d.P_measurable i)
        (2 * d.B i) (SiegelData.lowerHeight F d i))
  exact hset.preimage ((continuousSL2FAction (F := F) ((d.σ i)⁻¹)).measurable)

private theorem fundamentalDomainCandidate_measurable
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (d : SiegelData F Γ) :
    MeasurableSet (fundamentalDomainCandidate F Γ (SiegelData.unionSet F d)) := by
  classical
  letI : BorelSpace (X F) := borelSpace_X (F := F)
  letI : OpensMeasurableSpace (X F) := opensMeasurable_X (F := F)
  let S := SiegelData.unionSet F d
  have hS : MeasurableSet S := siegelUnion_measurable Γ d
  letI : Countable (𝓞 F) := Finsupp.Countable.of_moduleFinite (R := ℤ) (M := 𝓞 F)
  have hrow : (Set.univ : Set (Fin 2 → 𝓞 F)).Countable := by
    simpa using (Set.countable_univ_pi (π := fun _ : Fin 2 => 𝓞 F)
      (s := fun _ => Set.univ) (fun _ => Set.countable_univ))
  have hmatrix : (Set.univ : Set (Fin 2 → Fin 2 → 𝓞 F)).Countable := by
    simpa using (Set.countable_univ_pi (π := fun _ : Fin 2 => Fin 2 → 𝓞 F)
      (s := fun _ => Set.univ) (fun _ => hrow))
  letI : Countable (Matrix (Fin 2) (Fin 2) (𝓞 F)) := Set.countable_univ_iff.mp hmatrix
  have hSL : {A : Matrix (Fin 2) (Fin 2) (𝓞 F) | A.det = 1}.Countable :=
    Set.Countable.mono (Set.subset_univ _) Set.countable_univ
  letI : Countable (SL(2,𝓞 F)) := hSL.to_subtype
  have hΓ : (Γ : Set SL(2,𝓞 F)).Countable :=
    Set.Countable.mono (Set.subset_univ _) Set.countable_univ
  letI : Countable Γ := hΓ.to_subtype
  have hCond (γ : Γ) : MeasurableSet {z : X F |
      ((γ : SL(2,𝓞 F)) • z ∈ S →
        coordLexLE F (coordsX F z) (coordsX F ((γ : SL(2,𝓞 F)) • z)))} := by
    have hact : Measurable (fun z : X F => (γ : SL(2,𝓞 F)) • z) :=
      (continuousSL2FAction (F := F) (toSLF F (γ : SL(2,𝓞 F)))).measurable
    have htrans : MeasurableSet {z : X F | (γ : SL(2,𝓞 F)) • z ∈ S} :=
      hS.preimage hact
    have hpair : Measurable (fun z : X F =>
        (coordsX F z, coordsX F ((γ : SL(2,𝓞 F)) • z))) :=
      (coordsX_measurable (F := F)).prodMk
        ((coordsX_measurable (F := F)).comp hact)
    have hlex : MeasurableSet {z : X F |
        coordLexLE F (coordsX F z) (coordsX F ((γ : SL(2,𝓞 F)) • z))} :=
      measurableSet_coordLexLE.preimage hpair
    have heq : {z : X F | ((γ : SL(2,𝓞 F)) • z ∈ S →
        coordLexLE F (coordsX F z) (coordsX F ((γ : SL(2,𝓞 F)) • z)))} =
        {z | (γ : SL(2,𝓞 F)) • z ∈ S}ᶜ ∪
          {z | coordLexLE F (coordsX F z) (coordsX F ((γ : SL(2,𝓞 F)) • z))} := by
      ext z
      by_cases hz : (γ : SL(2,𝓞 F)) • z ∈ S <;> simp [hz]
    rw [heq]
    exact htrans.compl.union hlex
  simp only [fundamentalDomainCandidate, Set.setOf_and, Set.ofPred_forall]
  exact hS.inter (MeasurableSet.iInter hCond)

private theorem candidate_existsUniqueRep (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (hfree : FreeAction F Γ) (d : SiegelData F Γ) (z : X F) :
    ∃! η : Γ, (η : SL(2,𝓞 F)) • z ∈
      fundamentalDomainCandidate F Γ (SiegelData.unionSet F d) := by
  classical
  let S := SiegelData.unionSet F d
  let D := fundamentalDomainCandidate F Γ S
  obtain ⟨i, γ₀, hAt⟩ := R8_siegel_cover Γ d z
  let x₀ : X F := (γ₀ : SL(2,𝓞 F)) • z
  have hx₀ : x₀ ∈ S := by
    change ∃ i, ∃ x, x ∈ SiegelData.setAt F d i ∧ (d.σ i) • x = x₀
    exact ⟨i, (d.σ i)⁻¹ • x₀, hAt, by simp [x₀]⟩
  let T : Set Γ := {δ | (δ : SL(2,𝓞 F)) • x₀ ∈ S}
  have hOverlap : {δ : Γ | ∃ x : X F, x ∈ S ∧
      (δ : SL(2,𝓞 F)) • x ∈ S}.Finite := by
    simpa [S] using (R9_proper Γ d).2.1
  have hTfinite : T.Finite := hOverlap.subset fun δ hδ => ⟨x₀, hx₀, hδ⟩
  have hTnonempty : T.Nonempty := ⟨1, by change (1 : SL(2,𝓞 F)) • x₀ ∈ S; simpa using hx₀⟩
  let f : Γ → List ℝ := fun δ =>
    realCoordList F (coordsX F ((δ : SL(2,𝓞 F)) • x₀))
  obtain ⟨δ₀, hδ₀, hmin⟩ := Set.exists_min_image T f hTfinite hTnonempty
  let y : X F := (δ₀ : SL(2,𝓞 F)) • x₀
  have hyS : y ∈ S := by simpa [T, y] using hδ₀
  have hyD : y ∈ D := by
    change y ∈ S ∧ ∀ δ : Γ,
      ((δ : SL(2,𝓞 F)) • y ∈ S →
        coordLexLE F (coordsX F y) (coordsX F ((δ : SL(2,𝓞 F)) • y)))
    refine ⟨hyS, ?_⟩
    intro δ hδ
    apply (coordLexLE_iff_listLE (coordsX F y)
      (coordsX F ((δ : SL(2,𝓞 F)) • y))).2
    have hδT : δ * δ₀ ∈ T := by
      change ((δ * δ₀ : Γ) : SL(2,𝓞 F)) • x₀ ∈ S
      simpa [y, mul_smul] using hδ
    have hmin' := hmin (δ * δ₀) hδT
    simpa [f, y, mul_smul] using hmin'
  let η : Γ := δ₀ * γ₀
  have hη : (η : SL(2,𝓞 F)) • z = y := by
    simp [η, y, x₀, mul_smul]
  have hηD : (η : SL(2,𝓞 F)) • z ∈ D := by simpa [hη] using hyD
  refine ⟨η, hηD, ?_⟩
  intro θ hθD
  have hyD' : y ∈ S ∧ ∀ δ : Γ,
      ((δ : SL(2,𝓞 F)) • y ∈ S →
        coordLexLE F (coordsX F y) (coordsX F ((δ : SL(2,𝓞 F)) • y))) := hyD
  have hθD' : (θ : SL(2,𝓞 F)) • z ∈ S ∧ ∀ δ : Γ,
      ((δ : SL(2,𝓞 F)) • ((θ : SL(2,𝓞 F)) • z) ∈ S →
        coordLexLE F (coordsX F ((θ : SL(2,𝓞 F)) • z))
          (coordsX F ((δ : SL(2,𝓞 F)) • ((θ : SL(2,𝓞 F)) • z)))) := hθD
  have h12 : ((θ * η⁻¹ : Γ) : SL(2,𝓞 F)) • y =
      (θ : SL(2,𝓞 F)) • z := by
    rw [← hη]
    simp [mul_smul]
  have h21 : ((η * θ⁻¹ : Γ) : SL(2,𝓞 F)) • ((θ : SL(2,𝓞 F)) • z) = y := by
    calc
      _ = (η : SL(2,𝓞 F)) • z := by simp [mul_smul]
      _ = y := hη
  have h12mem : ((θ * η⁻¹ : Γ) : SL(2,𝓞 F)) • y ∈ S := by
    rw [h12]
    exact hθD'.1
  have h21mem : ((η * θ⁻¹ : Γ) : SL(2,𝓞 F)) • ((θ : SL(2,𝓞 F)) • z) ∈ S := by
    rw [h21]
    exact hyD'.1
  have hlex₁ := hyD'.2 (θ * η⁻¹) h12mem
  have hlex₂ := hθD'.2 (η * θ⁻¹) h21mem
  have hlex₁' : coordLexLE F (coordsX F y)
      (coordsX F ((θ : SL(2,𝓞 F)) • z)) := by simpa only [h12] using hlex₁
  have hlex₂' : coordLexLE F (coordsX F ((θ : SL(2,𝓞 F)) • z))
      (coordsX F y) := by simpa only [h21] using hlex₂
  have hlist₁ := (coordLexLE_iff_listLE (coordsX F y)
    (coordsX F ((θ : SL(2,𝓞 F)) • z))).mp hlex₁'
  have hlist₂ := (coordLexLE_iff_listLE (coordsX F ((θ : SL(2,𝓞 F)) • z))
    (coordsX F y)).mp hlex₂'
  have hcoord : coordsX F y = coordsX F ((θ : SL(2,𝓞 F)) • z) :=
    realCoordList_injective (F := F) (le_antisymm hlist₁ hlist₂)
  have hpoint : y = (θ : SL(2,𝓞 F)) • z := by
    calc
      y = ptX F (coordsX F y) := (ptX_coordsX (F := F) y).symm
      _ = ptX F (coordsX F ((θ : SL(2,𝓞 F)) • z)) := by rw [hcoord]
      _ = (θ : SL(2,𝓞 F)) • z := ptX_coordsX (F := F) _
  have hfix : ((θ * η⁻¹ : Γ) : SL(2,𝓞 F)) • y = y := by
    calc
      _ = (θ : SL(2,𝓞 F)) • z := h12
      _ = y := hpoint.symm
  have htriv := hfree ((θ * η⁻¹ : Γ) : SL(2,𝓞 F)) (θ * η⁻¹).property y hfix
  have hsub : θ * η⁻¹ = 1 := Subtype.ext htriv
  exact mul_inv_eq_one.mp hsub

private theorem balancedHeightRelativeBounds (y : InfinitePlace F → ℝ) (B c : ℝ)
    (hy : ∀ w, 0 < y w)
    (hbal : ∀ w, |Real.log (y w) - (placeCount F)⁻¹ *
      ∑ w' : InfinitePlace F, Real.log (y w')| ≤ B)
    (hc : 0 < c) (hlo : c ≤ ∏ w : InfinitePlace F, y w) :
    0 < Real.exp (Real.log c / placeCount F - B) ∧
    0 < Real.exp (-2 * B) ∧ 0 < Real.exp (2 * B) ∧ 0 ≤ B ∧
      (∀ w₀, Real.exp (Real.log c / placeCount F - B) ≤ y w₀) ∧
      ∀ w₀ w, Real.exp (-2 * B) * y w₀ ≤ y w ∧
        y w ≤ Real.exp (2 * B) * y w₀ := by
  have hr : 0 < placeCount F := by
    unfold placeCount
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty (InfinitePlace F)))
  have hprodpos : 0 < ∏ w : InfinitePlace F, y w := lt_of_lt_of_le hc hlo
  have hlogprod : Real.log (∏ w : InfinitePlace F, y w) =
      ∑ w : InfinitePlace F, Real.log (y w) := by
    simpa using (Real.log_prod (s := Finset.univ) (f := y) (by
      intro w hw
      exact (hy w).ne'))
  have havg : (placeCount F)⁻¹ * ∑ w : InfinitePlace F, Real.log (y w) =
      Real.log (∏ w : InfinitePlace F, y w) / placeCount F := by
    rw [← hlogprod]
    simp [div_eq_mul_inv, mul_comm]
  have hloglo : Real.log c ≤ Real.log (∏ w : InfinitePlace F, y w) :=
    Real.log_le_log hc hlo
  have havglo := div_le_div_of_nonneg_right hloglo (le_of_lt hr)
  have hB : 0 ≤ B :=
    le_trans (abs_nonneg _) (hbal (Classical.choice (inferInstance : Nonempty (InfinitePlace F))))
  let a := Real.exp (Real.log c / placeCount F - B)
  let L := Real.exp (-2 * B)
  let U := Real.exp (2 * B)
  have ha : 0 < a := Real.exp_pos _
  have hL : 0 < L := Real.exp_pos _
  have hU : 0 < U := Real.exp_pos _
  refine ⟨?_, ?_, ?_, hB, ?_, ?_⟩
  · simpa [a] using ha
  · simpa [L] using hL
  · simpa [U] using hU
  · intro w
    have hleft := (abs_le.mp (hbal w)).1
    rw [havg] at hleft
    have hlog : Real.log c / placeCount F - B ≤ Real.log (y w) := by
      linarith
    have hexp := Real.exp_le_exp.mpr hlog
    simpa [a, Real.exp_log (hy w)] using hexp
  · intro w₀ w
    have hleft₀ := (abs_le.mp (hbal w₀)).1
    have hright₀ := (abs_le.mp (hbal w₀)).2
    have hleft := (abs_le.mp (hbal w)).1
    have hright := (abs_le.mp (hbal w)).2
    rw [havg] at hleft₀ hright₀ hleft hright
    have hlow : Real.log (y w₀) - 2 * B ≤ Real.log (y w) := by linarith
    have hhigh : Real.log (y w) ≤ Real.log (y w₀) + 2 * B := by linarith
    constructor
    · have hexp := Real.exp_le_exp.mpr hlow
      calc
        L * y w₀ = Real.exp (Real.log (y w₀) - 2 * B) := by
          dsimp [L]
          calc
            Real.exp (-2 * B) * y w₀ =
                Real.exp (-2 * B) * Real.exp (Real.log (y w₀)) := by
                  rw [Real.exp_log (hy w₀)]
            _ = Real.exp ((-2 * B) + Real.log (y w₀)) := (Real.exp_add _ _).symm
            _ = Real.exp (Real.log (y w₀) - 2 * B) := by congr 1 <;> ring
        _ ≤ Real.exp (Real.log (y w)) := hexp
        _ = y w := Real.exp_log (hy w)
    · have hexp := Real.exp_le_exp.mpr hhigh
      calc
        y w = Real.exp (Real.log (y w)) := (Real.exp_log (hy w)).symm
        _ ≤ Real.exp (Real.log (y w₀) + 2 * B) := hexp
        _ = U * y w₀ := by
          simp [U, Real.exp_add, Real.exp_log (hy w₀), mul_comm]

private theorem measurableSet_posSet : MeasurableSet (posSet F) := by
  unfold posSet
  rw [Set.ofPred_forall]
  exact MeasurableSet.iInter fun w =>
    measurableSet_lt measurable_const (measurable_snd.comp (measurable_pi_apply w))

private theorem ptX_continuousOn_posSet : ContinuousOn (ptX F) (posSet F) := by
  rcases (G1_h3_basics (F := F)) with
    ⟨_, _, _, _, _, _, _, _, _, _, _, ⟨e, he, _⟩⟩
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun p : {p : Coord F // p ∈ posSet F} => ptX F p.1)
  have heq : (fun p : {p : Coord F // p ∈ posSet F} => ptX F p.1) = e :=
    funext fun p => (he p).symm
  rw [heq]
  exact e.continuous

private theorem ptX_aemeasurable_weighted :
    AEMeasurable (ptX F)
      ((volume.restrict (posSet F)).withDensity
        (fun p : Coord F => ENNReal.ofReal (∏ w, ((p w).2 ^ 3)⁻¹))) := by
  letI : BorelSpace (X F) := borelSpace_X (F := F)
  letI : Countable (InfinitePlace F) := Finite.to_countable
  letI : BorelSpace (Coord F) := by
    change BorelSpace (∀ w : InfinitePlace F, ℂ × ℝ)
    exact Pi.borelSpace
  letI : OpensMeasurableSpace (Coord F) := BorelSpace.opensMeasurable
  have hbase : AEMeasurable (ptX F) (volume.restrict (posSet F)) :=
    ptX_continuousOn_posSet.aemeasurable measurableSet_posSet
  exact hbase.mono_ac (withDensity_absolutelyContinuous _ _)

private theorem ptX_siegelPreimage_inter_posSet (P : Set (InfinitePlace F → ℂ))
    (B c : ℝ) :
    (ptX F ⁻¹' siegelSet F P B c) ∩ posSet F = siegelCoordRegion P B c := by
  ext p
  constructor
  · rintro ⟨hp, hpos⟩
    have hcoord := coordsX_ptX (F := F) p hpos
    rw [siegelSet_eq_coords_preimage (F := F) P B c] at hp
    simpa [hcoord] using hp
  · intro hp
    have hpos : p ∈ posSet F := by
      intro w
      exact hp.2.1.1 w
    have hcoord := coordsX_ptX (F := F) p hpos
    constructor
    · rw [siegelSet_eq_coords_preimage (F := F) P B c]
      simpa [hcoord] using hp
    · exact hpos

private theorem volX_siegelSet_eq_source (P : Set (InfinitePlace F → ℂ))
    (hP : MeasurableSet P) (B c : ℝ) :
    volX F (siegelSet F P B c) =
      ((volume.restrict (posSet F)).withDensity
        (fun p : Coord F => ENNReal.ofReal (∏ w, ((p w).2 ^ 3)⁻¹)))
        (siegelCoordRegion P B c) := by
  let ρ : Coord F → ENNReal := fun p => ENNReal.ofReal (∏ w, ((p w).2 ^ 3)⁻¹)
  let μ := (volume.restrict (posSet F)).withDensity ρ
  have hS : MeasurableSet (siegelSet F P B c) := measurableSet_siegelSet (F := F) P hP B c
  have hpre := ptX_siegelPreimage_inter_posSet (F := F) P B c
  have hbase0 : (volume.restrict (posSet F)) (posSet F)ᶜ = 0 := by
    rw [Measure.restrict_apply (measurableSet_posSet (F := F)).compl]
    simp
  have hzero : μ (posSet F)ᶜ = 0 :=
    (withDensity_absolutelyContinuous (volume.restrict (posSet F)) ρ) hbase0
  have hsupport : μ (ptX F ⁻¹' siegelSet F P B c) =
      μ ((ptX F ⁻¹' siegelSet F P B c) ∩ posSet F) := by
    apply le_antisymm
    · calc
        μ (ptX F ⁻¹' siegelSet F P B c) ≤
            μ ((ptX F ⁻¹' siegelSet F P B c) ∩ posSet F ∪ (posSet F)ᶜ) := by
              apply measure_mono
              intro p hp
              by_cases hpos : p ∈ posSet F
              · exact Or.inl ⟨hp, hpos⟩
              · exact Or.inr hpos
        _ ≤ μ ((ptX F ⁻¹' siegelSet F P B c) ∩ posSet F) + μ (posSet F)ᶜ :=
            measure_union_le _ _
        _ = _ := by simp [hzero]
    · exact measure_mono Set.inter_subset_left
  rw [volX, Measure.map_apply_of_aemeasurable
    (ptX_aemeasurable_weighted (F := F)) hS, hsupport, hpre]

private def siegelScaledBox (R lo hi : ℝ) : Set (Coord F) :=
  Set.pi Set.univ fun _ : InfinitePlace F =>
    Metric.closedBall (0 : ℂ) R ×ˢ Set.Icc lo hi

private theorem siegelScaledBox_measurable (R lo hi : ℝ) :
    MeasurableSet (siegelScaledBox (F := F) R lo hi) := by
  apply MeasurableSet.univ_pi
  intro w
  exact MeasurableSet.prod Metric.isClosed_closedBall.measurableSet measurableSet_Icc

private theorem siegelScaledBox_volume (R lo hi : ℝ) :
    volume (siegelScaledBox (F := F) R lo hi) =
      (volume (Metric.closedBall (0 : ℂ) R) * ENNReal.ofReal (hi - lo)) ^
        Fintype.card (InfinitePlace F) := by
  rw [siegelScaledBox, volume_pi_pi]
  simp [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Finset.prod_const]

private theorem siegelDensity_le_of_mem_scaledBox (R lo hi : ℝ) (hlo : 0 < lo)
    (p : Coord F) (hp : p ∈ siegelScaledBox (F := F) R lo hi) :
    ENNReal.ofReal (∏ w : InfinitePlace F, ((p w).2 ^ 3)⁻¹) ≤
      ENNReal.ofReal (((lo ^ 3)⁻¹) ^ Fintype.card (InfinitePlace F)) := by
  have hprod : (∏ w : InfinitePlace F, ((p w).2 ^ 3)⁻¹) ≤
      ∏ _w : InfinitePlace F, ((lo ^ 3)⁻¹) := by
    apply Finset.prod_le_prod₀
    · intro w hw
      have hwbox := (Set.mem_pi.mp hp) w (Set.mem_univ w)
      have hpos : 0 < (p w).2 := lt_of_lt_of_le hlo (Set.mem_Icc.mp hwbox.2).1
      positivity
    · intro w hw
      have hwbox := (Set.mem_pi.mp hp) w (Set.mem_univ w)
      have hpos : 0 < (p w).2 := lt_of_lt_of_le hlo (Set.mem_Icc.mp hwbox.2).1
      have hpow : lo ^ 3 ≤ (p w).2 ^ 3 := by
        gcongr
        exact (Set.mem_Icc.mp hwbox.2).1
      exact (inv_le_inv₀ (pow_pos hpos 3) (pow_pos hlo 3)).2 hpow
  have hconst : (∏ _w : InfinitePlace F, ((lo ^ 3)⁻¹)) =
      ((lo ^ 3)⁻¹) ^ Fintype.card (InfinitePlace F) := by simp
  exact ENNReal.ofReal_le_ofReal (hconst ▸ hprod)

private def weightedCoordVolume : Measure (Coord F) :=
  (volume.restrict (posSet F)).withDensity
    (fun p : Coord F => ENNReal.ofReal (∏ w, ((p w).2 ^ 3)⁻¹))

private theorem weightedCoordVolume_box_le (R lo hi : ℝ) (hlo : 0 < lo) :
    weightedCoordVolume (F := F) (siegelScaledBox R lo hi) ≤
      (volume (Metric.closedBall (0 : ℂ) R) *
        ENNReal.ofReal ((lo ^ 3)⁻¹ * hi)) ^ Fintype.card (InfinitePlace F) := by
  let ρ : Coord F → ENNReal := fun p => ENNReal.ofReal (∏ w, ((p w).2 ^ 3)⁻¹)
  let M := ENNReal.ofReal (((lo ^ 3)⁻¹) ^ Fintype.card (InfinitePlace F))
  have hd : 0 ≤ (lo ^ 3)⁻¹ := inv_nonneg.mpr (pow_nonneg hlo.le _)
  have hbox := siegelScaledBox_measurable (F := F) R lo hi
  have hbound : ∫⁻ p in siegelScaledBox R lo hi, ρ p ∂(volume.restrict (posSet F)) ≤
      M * (volume.restrict (posSet F)) (siegelScaledBox R lo hi) := by
    calc
      _ ≤ ∫⁻ _p in siegelScaledBox R lo hi, M ∂(volume.restrict (posSet F)) :=
        setLIntegral_mono measurable_const
          (fun p hp => siegelDensity_le_of_mem_scaledBox R lo hi hlo p hp)
      _ = _ := by simp
  have hvol : (volume.restrict (posSet F)) (siegelScaledBox R lo hi) ≤
      volume (siegelScaledBox (F := F) R lo hi) :=
    Measure.le_iff'.mp Measure.restrict_le_self _
  calc
    weightedCoordVolume (F := F) (siegelScaledBox R lo hi) =
        ∫⁻ p in siegelScaledBox R lo hi, ρ p ∂(volume.restrict (posSet F)) := by
      exact withDensity_apply _ hbox
    _ ≤ M * volume (siegelScaledBox (F := F) R lo hi) :=
      hbound.trans (by gcongr)
    _ = ENNReal.ofReal ((lo ^ 3)⁻¹) ^ Fintype.card (InfinitePlace F) *
        (volume (Metric.closedBall (0 : ℂ) R) * ENNReal.ofReal (hi - lo)) ^
          Fintype.card (InfinitePlace F) := by
      dsimp [M]
      rw [siegelScaledBox_volume, ENNReal.ofReal_pow hd]
    _ ≤ ENNReal.ofReal ((lo ^ 3)⁻¹) ^ Fintype.card (InfinitePlace F) *
        (volume (Metric.closedBall (0 : ℂ) R) * ENNReal.ofReal hi) ^
          Fintype.card (InfinitePlace F) := by
      gcongr
      exact sub_le_self hi hlo.le
    _ = _ := by
      rw [ENNReal.ofReal_mul hd]
      simp only [mul_pow]
      exact mul_left_comm _ _ _

private theorem scaled_density_width (k h : ℝ) (n : ℕ) :
    ((k * 4 ^ n) ^ 3)⁻¹ * (h * 4 ^ n) =
      ((k ^ 3)⁻¹ * h) * ((1 : ℝ) / 16) ^ n := by
  have hpow : ((4 : ℝ) ^ n) ^ 3 = ((4 : ℝ) ^ 3) ^ n := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm n 3]
  calc
    _ = ((k ^ 3)⁻¹ * h) * (((((4 : ℝ) ^ 3)⁻¹) ^ n) * 4 ^ n) := by
      rw [mul_pow, mul_inv, hpow, inv_pow]
      ring
    _ = ((k ^ 3)⁻¹ * h) * (((4 : ℝ) ^ 3)⁻¹ * 4) ^ n := by rw [mul_pow]
    _ = _ := by norm_num

private theorem weightedCoordVolume_scaledBox_union_lt_top (R k h : ℝ)
    (hk : 0 < k) (hh : 0 < h) :
    weightedCoordVolume (F := F)
      (⋃ n : ℕ, siegelScaledBox R (k * 4 ^ n) (h * 4 ^ n)) < ⊤ := by
  let r := Fintype.card (InfinitePlace F)
  let C := (volume (Metric.closedBall (0 : ℂ) R) *
    ENNReal.ofReal ((k ^ 3)⁻¹ * h)) ^ r
  let q : ENNReal := ENNReal.ofReal ((1 : ℝ) / 16) ^ r
  have hr : r ≠ 0 := (Fintype.card_pos_iff.mpr
    (inferInstance : Nonempty (InfinitePlace F))).ne'
  have hC : C < ⊤ := ENNReal.pow_lt_top
    (ENNReal.mul_lt_top (isCompact_closedBall (0 : ℂ) R).measure_lt_top
      ENNReal.ofReal_lt_top)
  have hq : q < 1 := by
    exact pow_lt_one₀ (by positivity) (by norm_num) hr
  have hd : 0 ≤ (k ^ 3)⁻¹ * h := by positivity
  have hbound (n : ℕ) : weightedCoordVolume (F := F)
      (siegelScaledBox R (k * 4 ^ n) (h * 4 ^ n)) ≤ C * q ^ n := by
    calc
      _ ≤ (volume (Metric.closedBall (0 : ℂ) R) *
          ENNReal.ofReal (((k * 4 ^ n) ^ 3)⁻¹ * (h * 4 ^ n))) ^ r :=
        weightedCoordVolume_box_le R _ _ (mul_pos hk (by positivity))
      _ = C * q ^ n := by
        rw [scaled_density_width, ENNReal.ofReal_mul hd,
          ENNReal.ofReal_pow (by norm_num)]
        dsimp [C, q]
        rw [← mul_assoc, mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm n r]
  calc
    _ ≤ ∑' n : ℕ, weightedCoordVolume (F := F)
        (siegelScaledBox R (k * 4 ^ n) (h * 4 ^ n)) := measure_iUnion_le _
    _ ≤ ∑' n : ℕ, C * q ^ n := ENNReal.tsum_le_tsum hbound
    _ = C * ∑' n : ℕ, q ^ n := ENNReal.tsum_mul_left
    _ < ⊤ := ENNReal.mul_lt_top hC (tsum_geometric_lt_top.mpr hq)

private theorem exists_scaled_slab {a t : ℝ} (ha : 0 < a) (hat : a ≤ t) :
    ∃ n : ℕ, a * 4 ^ n ≤ t ∧ t ≤ a * 4 ^ (n + 1) := by
  let q := t / a
  have hq : 1 ≤ q := (one_le_div₀ ha).2 hat
  have hE : ∃ n : ℕ, q < (4 : ℝ) ^ n :=
    pow_unbounded_of_one_lt q (by norm_num)
  let N := Nat.find hE
  have hN := Nat.find_spec hE
  have hNne : N ≠ 0 := by
    intro h0
    have hfind : Nat.find hE = 0 := by simpa [N] using h0
    rw [hfind] at hN
    have hqbad : q < 1 := by simpa using hN
    exact (not_lt_of_ge hq) hqbad
  have hNpos : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hNne
  have hprev : ¬ q < (4 : ℝ) ^ (N - 1) := Nat.find_min hE (Nat.pred_lt hNne)
  let n := N - 1
  have hn : n + 1 = N := Nat.sub_add_cancel hNpos
  have hqlo : (4 : ℝ) ^ n ≤ q := le_of_not_gt (by simpa [n] using hprev)
  have hqhi : q ≤ (4 : ℝ) ^ (n + 1) := by rw [hn]; exact hN.le
  refine ⟨n, ?_, ?_⟩
  · calc
      a * 4 ^ n ≤ a * q := mul_le_mul_of_nonneg_left hqlo ha.le
      _ = t := by dsimp [q]; field_simp [ha.ne']
  · calc
      t = a * q := by dsimp [q]; field_simp [ha.ne']
      _ ≤ a * 4 ^ (n + 1) := mul_le_mul_of_nonneg_left hqhi ha.le


private theorem siegelCoordRegion_boxCover (P : Set (InfinitePlace F → ℂ))
    (hPbounded : Bornology.IsBounded P) (B c : ℝ) (hc : 0 < c) :
    ∃ R a L U : ℝ, P ⊆ Metric.closedBall 0 R ∧
      0 < a ∧ 0 < L ∧ 0 < U ∧
      siegelCoordRegion P B c ⊆
        ⋃ n : ℕ, siegelScaledBox R (L * a * 4 ^ n) (U * a * 4 ^ (n + 1)) := by
  classical
  obtain ⟨R, hR⟩ := hPbounded.subset_closedBall (0 : InfinitePlace F → ℂ)
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  let a := Real.exp (Real.log c / placeCount F - B)
  let L := Real.exp (-2 * B)
  let U := Real.exp (2 * B)
  have ha : 0 < a := Real.exp_pos _
  have hL : 0 < L := Real.exp_pos _
  have hU : 0 < U := Real.exp_pos _
  refine ⟨R, a, L, U, hR, ha, hL, hU, ?_⟩
  intro p hp
  let x : InfinitePlace F → ℂ := fun w => (p w).1
  let y : InfinitePlace F → ℝ := fun w => (p w).2
  have hrel := balancedHeightRelativeBounds y B c hp.2.1.1 hp.2.1.2 hc hp.2.2
  rcases hrel with ⟨ha', hL', hU', hB', hbase, hratio⟩
  have hbase' : a ≤ y w₀ := by simpa [a] using hbase w₀
  obtain ⟨n, htnlo, htnhi⟩ := exists_scaled_slab (by simpa [a] using ha) hbase'
  have hxPi : x ∈ Metric.closedBall (0 : InfinitePlace F → ℂ) R := hR hp.1
  have hxnorm : ‖x‖ ≤ R := by
    simpa [dist_zero_right] using (Metric.mem_closedBall.mp hxPi)
  have hxw : ∀ w, x w ∈ Metric.closedBall (0 : ℂ) R := by
    intro w
    apply Metric.mem_closedBall.mpr
    calc
      dist (x w) 0 = ‖x w‖ := by simp
      _ ≤ ‖x‖ := norm_le_pi_norm x w
      _ ≤ R := hxnorm
  have hylow : ∀ w, L * a * 4 ^ n ≤ y w := by
    intro w
    calc
      L * a * 4 ^ n = L * (a * 4 ^ n) := by ring
      _ ≤ L * y w₀ := mul_le_mul_of_nonneg_left htnlo hL.le
      _ ≤ y w := (hratio w₀ w).1
  have hyhigh : ∀ w, y w ≤ U * a * 4 ^ (n + 1) := by
    intro w
    calc
      y w ≤ U * y w₀ := (hratio w₀ w).2
      _ ≤ U * (a * 4 ^ (n + 1)) := mul_le_mul_of_nonneg_left htnhi hU.le
      _ = U * a * 4 ^ (n + 1) := by ring
  have hbox : p ∈ siegelScaledBox R (L * a * 4 ^ n) (U * a * 4 ^ (n + 1)) := by
    simp only [siegelScaledBox, Set.mem_pi, Set.mem_univ, true_implies]
    intro w
    exact ⟨hxw w, Set.mem_Icc.mpr ⟨hylow w, hyhigh w⟩⟩
  exact Set.mem_iUnion.mpr ⟨n, hbox⟩



private theorem lowerHeight_pos (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (d : SiegelData F Γ) (i : d.ι) : 0 < SiegelData.lowerHeight F d i := by
  let g : SL(2,F) := (d.σ i)⁻¹
  have hrow : g 1 0 ≠ 0 ∨ g 1 1 ≠ 0 := by
    by_contra h
    push_neg at h
    have hd := g.2
    rw [Matrix.det_fin_two] at hd
    simp [h.1, h.2] at hd
  have hI : bottomRowFractionalIdeal F g ≠ 0 := by
    rw [bottomRowFractionalIdeal, FractionalIdeal.spanFinset_ne_zero]
    rcases hrow with h | h
    · exact ⟨0, Finset.mem_univ _, by simpa [bottomRow] using h⟩
    · exact ⟨1, Finset.mem_univ _, by simpa [bottomRow] using h⟩
  have hnorm : FractionalIdeal.absNorm (bottomRowFractionalIdeal F g) ≠ 0 := by
    intro hz
    exact hI (FractionalIdeal.absNorm_eq_zero_iff.mp hz)
  have hnormQ : 0 < FractionalIdeal.absNorm (bottomRowFractionalIdeal F g) :=
    lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg _) (Ne.symm hnorm)
  have hnormR : 0 < ((FractionalIdeal.absNorm (bottomRowFractionalIdeal F g) : ℚ) : ℝ) :=
    by exact_mod_cast hnormQ
  dsimp [SiegelData.lowerHeight]
  exact inv_pos.mpr (mul_pos hnormR d.C_M_pos)

private theorem volX_siegelSet_lt_top (P : Set (InfinitePlace F → ℂ))
    (hPmeas : MeasurableSet P) (hPbounded : Bornology.IsBounded P)
    (B c : ℝ) (hc : 0 < c) : volX F (siegelSet F P B c) < ⊤ := by
  rw [volX_siegelSet_eq_source P hPmeas B c]
  change weightedCoordVolume (F := F) (siegelCoordRegion P B c) < ⊤
  obtain ⟨R, a, L, U, hR, ha, hL, hU, hcover⟩ :=
    siegelCoordRegion_boxCover P hPbounded B c hc
  have hhi (n : ℕ) : U * a * 4 ^ (n + 1) = (U * a * 4) * 4 ^ n := by
    rw [pow_succ]
    ring
  have hcover' : siegelCoordRegion P B c ⊆
      ⋃ n : ℕ, siegelScaledBox R ((L * a) * 4 ^ n) ((U * a * 4) * 4 ^ n) := by
    simpa only [hhi] using hcover
  exact lt_of_le_of_lt (measure_mono hcover')
    (weightedCoordVolume_scaledBox_union_lt_top R (L * a) (U * a * 4)
      (mul_pos hL ha) (mul_pos (mul_pos hU ha) (by norm_num)))

private theorem volX_smul_preimage_eq (g : SL(2,F)) (S : Set (X F))
    (hS : MeasurableSet S) :
    volX F ((fun z : X F => g • z) ⁻¹' S) = volX F S := by
  letI : BorelSpace (X F) := borelSpace_X (F := F)
  have hf : Measurable (fun z : X F => g • z) :=
    (continuousSL2FAction (F := F) g).measurable
  have hmap : Measure.map (fun z : X F => g • z) (volX F) = volX F :=
    (G3_volume (F := F)).1 (toInf F g)
  calc
    _ = Measure.map (fun z : X F => g • z) (volX F) S :=
      (Measure.map_apply hf hS).symm
    _ = _ := by rw [hmap]

private theorem volX_siegelUnion_lt_top (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (d : SiegelData F Γ) : volX F (SiegelData.unionSet F d) < ⊤ := by
  classical
  letI : Fintype d.ι := d.fintype
  let S : d.ι → Set (X F) := fun i =>
    (fun z : X F => (d.σ i)⁻¹ • z) ⁻¹' SiegelData.setAt F d i
  have hcover : SiegelData.unionSet F d ⊆ ⋃ i : d.ι, S i := by
    rintro z ⟨i, x, hx, rfl⟩
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    simpa [S] using hx
  have hfinite (i : d.ι) : volX F (S i) < ⊤ := by
    change volX F ((fun z : X F => (d.σ i)⁻¹ • z) ⁻¹'
      siegelSet F (d.P i) (2 * d.B i) (SiegelData.lowerHeight F d i)) < ⊤
    rw [volX_smul_preimage_eq _ _
      (measurableSet_siegelSet (d.P i) (d.P_measurable i) _ _)]
    exact volX_siegelSet_lt_top (d.P i) (d.P_measurable i) (d.P_bounded i)
      _ _ (lowerHeight_pos Γ d i)
  calc
    _ ≤ volX F (⋃ i : d.ι, S i) := measure_mono hcover
    _ ≤ ∑ i : d.ι, volX F (S i) := measure_iUnion_fintype_le (volX F) S
    _ < ⊤ := ENNReal.sum_lt_top.mpr (fun i hi => hfinite i)

/-- R12 `spec:fund-domain` — P-SPEC.md:225, 338–342. The lexicographically least point in each
Siegel-covered orbit is a measurable finite-volume fundamental domain when the action is free.
Correction from `sol-gate-spec`: require calibrated Siegel data so the covering premise holds. -/
theorem R12_fund_domain (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (hfree : FreeAction F Γ) (d : SiegelData F Γ) :
    let D := fundamentalDomainCandidate F Γ (SiegelData.unionSet F d)
    MeasurableSet D ∧ IsFundamentalDomain Γ D (volX F) ∧ volX F D < ⊤ := by
  change MeasurableSet (fundamentalDomainCandidate F Γ (SiegelData.unionSet F d)) ∧
    IsFundamentalDomain Γ (fundamentalDomainCandidate F Γ (SiegelData.unionSet F d))
      (volX F) ∧ volX F (fundamentalDomainCandidate F Γ (SiegelData.unionSet F d)) < ⊤
  have hDmeas := fundamentalDomainCandidate_measurable Γ d
  refine ⟨hDmeas, ?_, ?_⟩
  · exact IsFundamentalDomain.mk' hDmeas.nullMeasurableSet
      (candidate_existsUniqueRep Γ hfree d)
  · apply lt_of_le_of_lt (measure_mono ?_) (volX_siegelUnion_lt_top Γ d)
    intro z hz
    exact hz.1

private theorem balanced_height_bounds (y : InfinitePlace F → ℝ) (B c A : ℝ)
    (hy : ∀ w, 0 < y w)
    (hbal : ∀ w, |Real.log (y w) - (placeCount F)⁻¹ *
      ∑ w' : InfinitePlace F, Real.log (y w')| ≤ B)
    (hc : 0 < c) (hlo : c ≤ ∏ w : InfinitePlace F, y w)
    (hhi : (∏ w : InfinitePlace F, y w) ≤ A) :
    ∀ w, Real.exp (Real.log c / placeCount F - B) ≤ y w ∧
      y w ≤ Real.exp (Real.log A / placeCount F + B) := by
  have hr : 0 < placeCount F := by
    unfold placeCount
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty (InfinitePlace F)))
  have hprodpos : 0 < ∏ w : InfinitePlace F, y w := lt_of_lt_of_le hc hlo
  have hlogprod : Real.log (∏ w : InfinitePlace F, y w) =
      ∑ w : InfinitePlace F, Real.log (y w) := by
    simpa using (Real.log_prod (s := Finset.univ) (f := y) (by
      intro w hw
      exact (hy w).ne'))
  have havg : (placeCount F)⁻¹ * ∑ w : InfinitePlace F, Real.log (y w) =
      Real.log (∏ w : InfinitePlace F, y w) / placeCount F := by
    rw [← hlogprod]
    simp [div_eq_mul_inv, mul_comm]
  have hloglo : Real.log c ≤ Real.log (∏ w : InfinitePlace F, y w) :=
    Real.log_le_log hc hlo
  have hloghi : Real.log (∏ w : InfinitePlace F, y w) ≤ Real.log A :=
    Real.log_le_log hprodpos hhi
  have havglo := div_le_div_of_nonneg_right hloglo (le_of_lt hr)
  have havghi := div_le_div_of_nonneg_right hloghi (le_of_lt hr)
  intro w
  have hleft := (abs_le.mp (hbal w)).1
  have hright := (abs_le.mp (hbal w)).2
  rw [havg] at hleft hright
  constructor
  · have hlog : Real.log c / placeCount F - B ≤ Real.log (y w) := by linarith
    have := Real.exp_le_exp.mpr hlog
    simpa [Real.exp_log (hy w)] using this
  · have hlog : Real.log (y w) ≤ Real.log A / placeCount F + B := by linarith
    have := Real.exp_le_exp.mpr hlog
    simpa [Real.exp_log (hy w)] using this


/-- Compactness of the bounded balanced boxes from calibrated Siegel data. -/
theorem compactBox_isCompact (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (d : SiegelData F Γ) (i : d.ι) (A : ℝ) (hA : 0 ≤ A) :
    IsCompact (SiegelData.compactBox F d i A) := by
  let c := SiegelData.lowerHeight F d i
  have hc : 0 < c := lowerHeight_pos Γ d i
  by_cases hAc : A < c
  · have hempty : SiegelData.compactBox F d i A = ∅ := by
      ext z
      constructor
      · rintro ⟨x, y, hEq, hx, hbal, hlo, hhi⟩
        have : c ≤ A := le_trans hlo hhi
        exact (not_le_of_gt hAc) this
      · simp
    simpa [hempty]
  · have hca : c ≤ A := le_of_not_gt hAc
    have hApos : 0 < A := hc.trans_le hca
    let lo := Real.exp (Real.log c / placeCount F - 2 * d.B i)
    let hi := Real.exp (Real.log A / placeCount F + 2 * d.B i)
    have hloPos : 0 < lo := Real.exp_pos _
    have hhiPos : 0 < hi := Real.exp_pos _
    let Xcoord := InfinitePlace F → ℂ
    let Ycoord := InfinitePlace F → ℝ
    let K : Set (Xcoord × Ycoord) :=
      {p | p.1 ∈ closure (d.P i) ∧
        (∀ w, p.2 w ∈ Set.Icc lo hi) ∧
        (∀ w, |Real.log (max lo (p.2 w)) - (placeCount F)⁻¹ *
          ∑ w' : InfinitePlace F, Real.log (max lo (p.2 w'))| ≤ 2 * d.B i) ∧
        (∏ w : InfinitePlace F, p.2 w) ∈ Set.Icc c A}
    let Ybox : Set Ycoord := {y | ∀ w, y w ∈ Set.Icc lo hi}
    have hPcompact : IsCompact (closure (d.P i)) := (d.P_bounded i).isCompact_closure
    have hYcompact : IsCompact Ybox := by
      exact isCompact_pi_infinite (fun _ => isCompact_Icc)
    have hbase : IsCompact (closure (d.P i) ×ˢ Ybox) := hPcompact.prod hYcompact
    have hlogClamp : Continuous (fun t : ℝ => Real.log (max lo t)) := by
      apply Real.continuousOn_log.comp_continuous
      · fun_prop
      · intro t
        exact ne_of_gt (lt_of_lt_of_le hloPos (le_max_left _ _))
    have hlogW : ∀ w, Continuous (fun p : Xcoord × Ycoord =>
        Real.log (max lo (p.2 w))) := fun w =>
      hlogClamp.comp ((continuous_apply w).comp continuous_snd)
    have hlogSum : Continuous (fun p : Xcoord × Ycoord =>
        ∑ w : InfinitePlace F, Real.log (max lo (p.2 w))) := by
      exact continuous_finsetSum Finset.univ (fun w hw => hlogW w)
    have hbalanceFun (w : InfinitePlace F) : Continuous (fun p : Xcoord × Ycoord =>
        |Real.log (max lo (p.2 w)) - (placeCount F)⁻¹ *
          ∑ w' : InfinitePlace F, Real.log (max lo (p.2 w'))|) := by
      exact ((hlogW w).sub (continuous_const.mul hlogSum)).abs
    have hPclosed : IsClosed {p : Xcoord × Ycoord | p.1 ∈ closure (d.P i)} :=
      isClosed_closure.preimage continuous_fst
    have hYclosed : IsClosed {p : Xcoord × Ycoord | ∀ w, p.2 w ∈ Set.Icc lo hi} := by
      rw [Set.ofPred_forall]
      exact isClosed_iInter fun w =>
        isClosed_Icc.preimage ((continuous_apply w).comp continuous_snd)
    have hbalanceClosed : IsClosed {p : Xcoord × Ycoord |
        ∀ w, |Real.log (max lo (p.2 w)) - (placeCount F)⁻¹ *
          ∑ w' : InfinitePlace F, Real.log (max lo (p.2 w'))| ≤ 2 * d.B i} := by
      rw [Set.ofPred_forall]
      exact isClosed_iInter fun w => isClosed_Iic.preimage (hbalanceFun w)
    have hprodFun : Continuous (fun p : Xcoord × Ycoord =>
        ∏ w : InfinitePlace F, p.2 w) := by
      exact continuous_finsetProd Finset.univ (fun w hw =>
        (continuous_apply w).comp continuous_snd)
    have hprodClosed : IsClosed {p : Xcoord × Ycoord |
        (∏ w : InfinitePlace F, p.2 w) ∈ Set.Icc c A} :=
      isClosed_Icc.preimage hprodFun
    have hKclosed : IsClosed K := by
      change IsClosed ({p : Xcoord × Ycoord | p.1 ∈ closure (d.P i)} ∩
        ({p | ∀ w, p.2 w ∈ Set.Icc lo hi} ∩
          ({p | ∀ w, |Real.log (max lo (p.2 w)) - (placeCount F)⁻¹ *
            ∑ w' : InfinitePlace F, Real.log (max lo (p.2 w'))| ≤ 2 * d.B i} ∩
            {p | (∏ w : InfinitePlace F, p.2 w) ∈ Set.Icc c A})))
      exact hPclosed.inter (hYclosed.inter (hbalanceClosed.inter hprodClosed))
    have hKsub : K ⊆ closure (d.P i) ×ˢ Ybox := by
      intro p hp
      exact ⟨hp.1, hp.2.1⟩
    have hKcompact : IsCompact K := hbase.of_isClosed_subset hKclosed hKsub
    rcases (G1_h3_basics (F := F)) with
      ⟨_, _, _, _, _, _, _, _, _, _, _, ⟨e, he, _⟩⟩
    let q : Xcoord × Ycoord → {p : Coord F // p ∈ posSet F} := fun p =>
      ⟨fun w => (p.1 w, max lo (p.2 w)), fun w =>
        lt_of_lt_of_le hloPos (le_max_left _ _)⟩
    have hq : Continuous q := by
      dsimp [q]
      apply Continuous.subtype_mk
      apply continuous_pi
      intro w
      fun_prop
    let φ : Xcoord × Ycoord → X F := fun p => (d.σ i) • e (q p)
    have hact : Continuous (fun z : X F => (d.σ i) • z) := by
      apply continuous_pi
      intro w
      exact (continuous_h3_action (toInf F (d.σ i) w)).comp (continuous_apply w)
    have hφ : Continuous φ := by
      dsimp [φ]
      exact hact.comp (e.continuous.comp hq)
    have hφcoord (x : Xcoord) (y : Ycoord) (hylo : ∀ w, lo ≤ y w) :
        φ (x, y) = (d.σ i) • ptX' F x y := by
      have hpoint : ptX F (q (x, y)).val = ptX' F x y := by
        ext w
        simp [q, ptX, ptX', max_eq_right (hylo w)]
      change (d.σ i) • e (q (x, y)) = _
      rw [he (q (x, y)), hpoint]
    have hboxeq : SiegelData.compactBox F d i A = φ '' K := by
      ext z
      constructor
      · rintro ⟨x, y, hz, hx, hbal, hlo, hhi⟩
        have hN := normHeight_ptX'_eq x y hbal.1
        have hprodlo : c ≤ ∏ w : InfinitePlace F, y w := by simpa [hN, c] using hlo
        have hprodhi : (∏ w : InfinitePlace F, y w) ≤ A := by simpa [hN] using hhi
        have hbounds := balanced_height_bounds y (2 * d.B i) c A hbal.1 hbal.2 hc
          hprodlo hprodhi
        have hmax : ∀ w, max lo (y w) = y w := fun w => max_eq_right (hbounds w).1
        refine ⟨(x, y), ?_, ?_⟩
        · refine ⟨hx, ?_, ?_, ?_⟩
          · intro w
            exact Set.mem_Icc.mpr (hbounds w)
          · intro w
            simpa [placeCount, hmax] using hbal.2 w
          · exact Set.mem_Icc.mpr ⟨hprodlo, hprodhi⟩
        · calc
            φ (x, y) = (d.σ i) • ptX' F x y := hφcoord x y (fun w => (hbounds w).1)
            _ = z := hz.symm
      · rintro ⟨⟨x, y⟩, hp, rfl⟩
        have hy : ∀ w, 0 < y w := fun w => lt_of_lt_of_le hloPos (Set.mem_Icc.mp (hp.2.1 w)).1
        have hmax : ∀ w, max lo (y w) = y w := fun w => max_eq_right (Set.mem_Icc.mp (hp.2.1 w)).1
        have hbal : IsBalancedHeights F (2 * d.B i) y := by
          refine ⟨hy, ?_⟩
          intro w
          simpa [placeCount, hmax] using hp.2.2.1 w
        have hN := normHeight_ptX'_eq x y hy
        refine ⟨x, y, ?_, hp.1, hbal, ?_, ?_⟩
        · exact hφcoord x y (fun w => (Set.mem_Icc.mp (hp.2.1 w)).1)
        · simpa [hN, c] using (Set.mem_Icc.mp hp.2.2.2).1
        · simpa [hN] using (Set.mem_Icc.mp hp.2.2.2).2
    rw [hboxeq]
    exact hKcompact.image hφ


/-- R13 `spec:compact-part` — P-SPEC.md:226. Bounded cusp heights reduce to the union of the
compact balanced boxes from the R8 Siegel sets. Correction from `sol-gate-spec`: require calibrated
Siegel data so the lower height floor comes from R7. -/
theorem R13_compact_part (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (d : SiegelData F Γ) :
    (∀ A : ℝ, 0 ≤ A → ∀ i : d.ι, IsCompact (SiegelData.compactBox F d i A)) ∧
    (∀ A : ℝ, 0 ≤ A → ∀ z : X F,
      (∀ i : d.ι, ∀ γ : Γ,
        normHeight F ((d.σ i)⁻¹ • ((γ : SL(2,𝓞 F)) • z)) ≤ A) →
      z ∈ SiegelData.compactOrbit F d A) := by
  constructor
  · intro A hA i
    exact compactBox_isCompact Γ d i A hA
  · intro A hA z hz
    obtain ⟨i, γ, hSiegel⟩ := R8_siegel_cover Γ d z
    rcases hSiegel with ⟨x, y, hxy, hx, hbal, hlower⟩
    have hupper : normHeight F ((d.σ i)⁻¹ • ((γ : SL(2,𝓞 F)) • z)) ≤ A := hz i γ
    have hbox : (γ : SL(2,𝓞 F)) • z ∈ SiegelData.compactBox F d i A := by
      refine ⟨x, y, ?_, subset_closure hx, hbal, hlower, ?_⟩
      · have h := congrArg (fun q : X F => d.σ i • q) hxy
        simpa [smul_smul] using h
      · simpa [hxy] using hupper
    refine ⟨i, ?_⟩
    refine ⟨γ⁻¹, (γ : SL(2,𝓞 F)) • z, hbox, ?_⟩
    simp

private theorem countable_Gamma (Γ : Subgroup SL(2,𝓞 F)) : Countable Γ := by
  letI : Countable (𝓞 F) := Finsupp.Countable.of_moduleFinite (R := ℤ) (M := 𝓞 F)
  have hrow : (Set.univ : Set (Fin 2 → 𝓞 F)).Countable := by
    simpa using (Set.countable_univ_pi (π := fun _ : Fin 2 => 𝓞 F)
      (s := fun _ => Set.univ) (fun _ => Set.countable_univ))
  have hmatrix : (Set.univ : Set (Fin 2 → Fin 2 → 𝓞 F)).Countable := by
    simpa using (Set.countable_univ_pi (π := fun _ : Fin 2 => Fin 2 → 𝓞 F)
      (s := fun _ => Set.univ) (fun _ => hrow))
  letI : Countable (Matrix (Fin 2) (Fin 2) (𝓞 F)) := Set.countable_univ_iff.mp hmatrix
  have hSL : {A : Matrix (Fin 2) (Fin 2) (𝓞 F) | A.det = 1}.Countable :=
    Set.Countable.mono (Set.subset_univ _) Set.countable_univ
  letI : Countable (SL(2,𝓞 F)) := hSL.to_subtype
  exact (Set.Countable.mono (Set.subset_univ (Γ : Set SL(2,𝓞 F)))
    Set.countable_univ).to_subtype

private theorem normHeight_measurable : Measurable (normHeight F) := by
  change Measurable (fun z : X F => ∏ w : InfinitePlace F, (coordsX F z w).2)
  exact Finset.measurable_fun_prod Finset.univ (fun w hw =>
    measurable_snd.comp ((measurable_pi_apply w).comp (coordsX_measurable (F := F))))

private theorem cuspTail_measurable (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F)) (A : ℝ) :
    MeasurableSet (cuspTail F Γ σ A) := by
  letI : Countable Γ := countable_Gamma Γ
  letI : BorelSpace (X F) := borelSpace_X (F := F)
  have hrepr : cuspTail F Γ σ A = ⋃ γ : Γ,
      (fun z : X F => (σ⁻¹ * toSLF F (γ : SL(2,𝓞 F))) • z) ⁻¹'
        {z | A < normHeight F z} := by
    ext z
    simp only [cuspTail, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage, mul_smul]
    rfl
  rw [hrepr]
  apply MeasurableSet.iUnion
  intro γ
  exact (measurableSet_Ioi.preimage (normHeight_measurable (F := F))).preimage
    ((continuousSL2FAction (F := F) _).measurable)

private theorem cuspTail_smul_iff (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (A : ℝ) (γ : Γ) (z : X F) :
    ((γ : SL(2,𝓞 F)) • z ∈ cuspTail F Γ σ A) ↔ z ∈ cuspTail F Γ σ A := by
  constructor
  · rintro ⟨η, hη⟩
    refine ⟨η * γ, ?_⟩
    simpa [mul_smul] using hη
  · rintro ⟨η, hη⟩
    refine ⟨η * γ⁻¹, ?_⟩
    simpa [mul_smul] using hη

private def cuspCoordRegion (P : Set (InfinitePlace F → ℂ))
    (Y : Set (InfinitePlace F → ℝ)) (A : ℝ) : Set (Coord F) :=
  {p | (fun w => (p w).1) ∈ P ∧ (fun w => (p w).2) ∈ Y ∧
    A < ∏ w : InfinitePlace F, (p w).2}

private def cuspStrip (σ : SL(2,F)) (P : Set (InfinitePlace F → ℂ))
    (Y : Set (InfinitePlace F → ℝ)) (A : ℝ) : Set (X F) :=
  (fun z : X F => coordsX F (σ⁻¹ • z)) ⁻¹' cuspCoordRegion P Y A

private theorem cuspCoordRegion_measurable (P : Set (InfinitePlace F → ℂ))
    (hP : MeasurableSet P) (Y : Set (InfinitePlace F → ℝ))
    (hY : MeasurableSet Y) (A : ℝ) : MeasurableSet (cuspCoordRegion P Y A) := by
  have hx : Measurable (fun p : Coord F => fun w => (p w).1) :=
    measurable_pi_iff.mpr fun w => measurable_fst.comp (measurable_pi_apply w)
  have hy : Measurable (fun p : Coord F => fun w => (p w).2) :=
    measurable_pi_iff.mpr fun w => measurable_snd.comp (measurable_pi_apply w)
  have hp : Measurable (fun p : Coord F => ∏ w : InfinitePlace F, (p w).2) :=
    Finset.measurable_fun_prod Finset.univ
      (fun w hw => measurable_snd.comp (measurable_pi_apply w))
  exact (hP.preimage hx).inter ((hY.preimage hy).inter (measurableSet_Ioi.preimage hp))

private theorem cuspStrip_measurable (σ : SL(2,F)) (P : Set (InfinitePlace F → ℂ))
    (hP : MeasurableSet P) (Y : Set (InfinitePlace F → ℝ))
    (hY : MeasurableSet Y) (A : ℝ) : MeasurableSet (cuspStrip σ P Y A) := by
  letI : BorelSpace (X F) := borelSpace_X (F := F)
  exact (cuspCoordRegion_measurable P hP Y hY A).preimage
    ((coordsX_measurable (F := F)).comp
      ((continuousSL2FAction (F := F) σ⁻¹).measurable))

private theorem cuspStrip_eq_image (σ : SL(2,F)) (P : Set (InfinitePlace F → ℂ))
    (Y : Set (InfinitePlace F → ℝ)) (hYpos : ∀ y ∈ Y, ∀ w, 0 < y w) (A : ℝ) :
    cuspStrip σ P Y A = (fun p : Coord F => σ • ptX F p) '' cuspCoordRegion P Y A := by
  ext z
  constructor
  · intro hz
    refine ⟨coordsX F (σ⁻¹ • z), hz, ?_⟩
    change σ • ptX F (coordsX F (σ⁻¹ • z)) = z
    rw [ptX_coordsX]
    simp
  · rintro ⟨p, hp, rfl⟩
    have hpos : p ∈ posSet F := hYpos _ hp.2.1
    change coordsX F (σ⁻¹ • (σ • ptX F p)) ∈ cuspCoordRegion P Y A
    simpa [coordsX_ptX p hpos] using hp

private theorem cuspStrip_subset_tail (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (P : Set (InfinitePlace F → ℂ)) (Y : Set (InfinitePlace F → ℝ)) (A : ℝ) :
    cuspStrip σ P Y A ⊆ cuspTail F Γ σ A := by
  intro z hz
  refine ⟨1, ?_⟩
  simpa [normHeight, coordsX] using hz.2.2

private theorem cuspUnitMatrix_mul_eq (ε δ : (𝓞 F)ˣ) (μ ν : F) :
    cuspUnitMatrix F ε μ * cuspUnitMatrix F δ ν =
      cuspUnitMatrix F (ε * δ)
        (algebraMap (𝓞 F) F (ε : 𝓞 F) * ν +
          μ * (algebraMap (𝓞 F) F (δ : 𝓞 F))⁻¹) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cuspUnitMatrix, Matrix.mul_apply, Fin.sum_univ_two, mul_inv]
  exact mul_comm _ _

private theorem cuspUnitMatrix_inv_eq (ε : (𝓞 F)ˣ) (μ : F) :
    (cuspUnitMatrix F ε μ)⁻¹ = cuspUnitMatrix F ε⁻¹ (-μ) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cuspUnitMatrix, map_units_inv]

private theorem cuspUnit_realized (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (ε : (𝓞 F)ˣ) (hε : ε ∈ cuspUnits F Γ σ) :
    ε ∈ cuspUnitSet F Γ σ := by
  change ε ∈ Subgroup.closure (cuspUnitSet F Γ σ) at hε
  induction hε using Subgroup.closure_induction with
  | mem ε hε => exact hε
  | one =>
    refine ⟨0, 1, ?_⟩
    simp only [Subgroup.coe_one, map_one, mul_one, inv_mul_cancel]
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cuspUnitMatrix]
  | mul ε δ hε hδ ihε ihδ =>
    rcases ihε with ⟨μ, γ, hγ⟩
    rcases ihδ with ⟨ν, η, hη⟩
    refine ⟨algebraMap (𝓞 F) F (ε : 𝓞 F) * ν +
      μ * (algebraMap (𝓞 F) F (δ : 𝓞 F))⁻¹, γ * η, ?_⟩
    calc
      _ = (σ⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * σ) *
          (σ⁻¹ * toSLF F (η : SL(2,𝓞 F)) * σ) := by
        simp only [Subgroup.coe_mul, map_mul]
        group
      _ = _ := by rw [hγ, hη, cuspUnitMatrix_mul_eq]
  | inv ε hε ihε =>
    rcases ihε with ⟨μ, γ, hγ⟩
    refine ⟨-μ, γ⁻¹, ?_⟩
    calc
      _ = (σ⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * σ)⁻¹ := by
        simp only [Subgroup.coe_inv, map_inv]
        group
      _ = _ := by rw [hγ, cuspUnitMatrix_inv_eq]

private theorem height_pos_all (z : H3) : 0 < height z := by
  rw [height_eq_hyperbolicHeight]
  exact OAI.CubicEisenstein.hyperbolicHeight_pos z

include F in
private theorem horiz_smul_borel (g : SL(2,ℂ)) (hg : g 1 0 = 0) (z : H3) :
    horiz (g • z) = (g 0 0) ^ 2 * horiz z + g 0 0 * g 0 1 := by
  have hdet : g 0 0 * g 1 1 = 1 := by
    have h := g.property
    rw [Matrix.det_fin_two, hg] at h
    simpa using h
  have ha : g 0 0 ≠ 0 := by
    intro h
    simp [h] at hdet
  have hd : g 1 1 = (g 0 0)⁻¹ := eq_inv_of_mul_eq_one_right hdet
  have hz11 : herm z 1 1 ≠ 0 := by
    intro h
    have hpos := height_pos_all z
    simp [height, h] at hpos
  have hstar : star ((g 0 0)⁻¹) ≠ 0 := star_ne_zero.mpr (inv_ne_zero ha)
  have hherm := (G1_h3_basics (F := F)).2.2.2.1 g z
  have h01 := congrArg (fun H : Matrix (Fin 2) (Fin 2) ℂ => H 0 1) hherm
  have h11 := congrArg (fun H : Matrix (Fin 2) (Fin 2) ℂ => H 1 1) hherm
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, hg] at h01 h11
  unfold horiz
  rw [h01, h11, hd]
  field_simp [ha, hz11, hstar]
  <;> ring

include F in
private theorem height_smul_borel (g : SL(2,ℂ)) (hg : g 1 0 = 0) (z : H3) :
    height (g • z) = Complex.normSq (g 0 0) * height z := by
  have hdet : g 0 0 * g 1 1 = 1 := by
    have h := g.property
    rw [Matrix.det_fin_two, hg] at h
    simpa using h
  have hd : g 1 1 = (g 0 0)⁻¹ := eq_inv_of_mul_eq_one_right hdet
  have h := (G1_h3_basics (F := F)).2.2.1 g (horiz z) (height z) (height_pos_all z)
  rw [(G1_h3_basics (F := F)).2.2.2.2.2.1 z] at h
  simpa [hg, hd, Complex.normSq_inv, div_eq_mul_inv, mul_comm] using h

private theorem cuspUnitMatrix_action (ε : (𝓞 F)ˣ) (μ : F)
    (x : InfinitePlace F → ℂ) (y : InfinitePlace F → ℝ) (hy : ∀ w, 0 < y w) :
    cuspUnitMatrix F ε μ • ptX' F x y =
      ptX' F (fun w => (w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))) ^ 2 * x w +
        w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F)) * w.embedding μ)
        (unitHeightAction F ε y) := by
  funext w
  let g : SL(2,ℂ) := Matrix.SpecialLinearGroup.map w.embedding (cuspUnitMatrix F ε μ)
  change g • pt (x w) (y w) = _
  have hcoeg : (g : Matrix (Fin 2) (Fin 2) ℂ) =
      (cuspUnitMatrix F ε μ : Matrix (Fin 2) (Fin 2) F).map w.embedding :=
    Matrix.SpecialLinearGroup.map_apply_coe w.embedding (cuspUnitMatrix F ε μ)
  have hg : g 1 0 = 0 := by
    change (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0
    rw [hcoeg]
    simp [Matrix.map_apply, cuspUnitMatrix]
  calc
    _ = pt (horiz (g • pt (x w) (y w))) (height (g • pt (x w) (y w))) :=
      ((G1_h3_basics (F := F)).2.2.2.2.2.1 _).symm
    _ = _ := by
      rw [horiz_smul_borel (F := F) g hg, height_smul_borel (F := F) g hg,
        (G1_h3_basics (F := F)).1 _ _ (hy w),
        (G1_h3_basics (F := F)).2.1 _ _ (hy w)]
      simp [hcoeg, Matrix.map_apply, cuspUnitMatrix, unitHeightAction, ptX']

private theorem weightedCoordVolume_pos_ae :
    ∀ᵐ p ∂(weightedCoordVolume (F := F)), p ∈ posSet F := by
  rw [ae_iff]
  have hbase : (volume.restrict (posSet F)) (posSet F)ᶜ = 0 := by
    rw [Measure.restrict_apply (measurableSet_posSet (F := F)).compl]
    simp
  exact (withDensity_absolutelyContinuous (volume.restrict (posSet F))
    (fun p : Coord F => ENNReal.ofReal (∏ w, ((p w).2 ^ 3)⁻¹))) hbase

private theorem weightedCoordVolume_absolutelyContinuous :
    weightedCoordVolume (F := F) ≪ (volume : Measure (Coord F)) := by
  exact (withDensity_absolutelyContinuous (volume.restrict (posSet F))
    (fun p : Coord F => ENNReal.ofReal (∏ w, ((p w).2 ^ 3)⁻¹))).trans
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)

private theorem volX_coords_preimage_eq (E : Set (Coord F)) (hE : MeasurableSet E) :
    volX F ((coordsX F) ⁻¹' E) = weightedCoordVolume (F := F) E := by
  rw [volX, Measure.map_apply_of_aemeasurable (ptX_aemeasurable_weighted (F := F))
    (hE.preimage (coordsX_measurable (F := F)))]
  apply measure_congr
  filter_upwards [weightedCoordVolume_pos_ae (F := F)] with p hp
  simp only [Set.mem_preimage, coordsX_ptX p hp]

private theorem coord_horizontal_null (B : Set (InfinitePlace F → ℂ))
    (hB : MeasurableSet B) (hBzero : volume B = 0) :
    volume ((fun p : Coord F => fun w => (p w).1) ⁻¹' B) = 0 := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℂ ℝ (InfinitePlace F)
  have hMP : MeasurePreserving e (volume : Measure (Coord F))
      (volume : Measure ((InfinitePlace F → ℂ) × (InfinitePlace F → ℝ))) :=
    volume_measurePreserving_arrowProdEquivProdArrow ℂ ℝ (InfinitePlace F)
  have heq : (fun p : Coord F => fun w => (p w).1) ⁻¹' B =
      e ⁻¹' (B ×ˢ Set.univ) := by
    ext p
    simp [e, MeasurableEquiv.arrowProdEquivProdArrow]
  rw [heq]
  calc
    _ = Measure.map e (volume : Measure (Coord F)) (B ×ˢ Set.univ) :=
      (Measure.map_apply hMP.measurable (hB.prod MeasurableSet.univ)).symm
    _ = 0 := by
      rw [hMP.map_eq, Measure.volume_eq_prod, Measure.prod_prod]
      simp [hBzero]

private theorem volX_horizontal_null (σ : SL(2,F)) (B : Set (InfinitePlace F → ℂ))
    (hB : MeasurableSet B) (hBzero : volume B = 0) :
    volX F {z | (fun w => (coordsX F (σ⁻¹ • z) w).1) ∈ B} = 0 := by
  let E : Set (Coord F) := (fun p : Coord F => fun w => (p w).1) ⁻¹' B
  have hE : MeasurableSet E := hB.preimage
    (measurable_pi_iff.mpr fun w => measurable_fst.comp (measurable_pi_apply w))
  have hzero : weightedCoordVolume (F := F) E = 0 :=
    weightedCoordVolume_absolutelyContinuous (coord_horizontal_null B hB hBzero)
  change volX F ((fun z : X F => σ⁻¹ • z) ⁻¹' ((coordsX F) ⁻¹' E)) = 0
  rw [volX_smul_preimage_eq σ⁻¹ _ (hE.preimage (coordsX_measurable (F := F))),
    volX_coords_preimage_eq E hE]
  exact hzero

private theorem gamma_measurable (Γ : Subgroup SL(2,𝓞 F)) :
    MeasurableConstSMul Γ (X F) := by
  letI : BorelSpace (X F) := borelSpace_X (F := F)
  exact ⟨fun γ => (continuousSL2FAction (F := F) (toSLF F (γ : SL(2,𝓞 F)))).measurable⟩

private theorem gamma_volInvariant (Γ : Subgroup SL(2,𝓞 F)) :
    SMulInvariantMeasure Γ (X F) (volX F) :=
  ⟨fun γ S hS => volX_smul_preimage_eq (toSLF F (γ : SL(2,𝓞 F))) S hS⟩

private theorem gamma_tailInvariant (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F)) (A : ℝ) :
    SMulInvariantMeasure Γ (X F) ((volX F).restrict (cuspTail F Γ σ A)) := by
  letI : MeasurableConstSMul Γ (X F) := gamma_measurable Γ
  have hT := cuspTail_measurable Γ σ A
  refine ⟨fun γ S hS => ?_⟩
  have heq : ((fun z : X F => γ • z) ⁻¹' S) ∩ cuspTail F Γ σ A =
      (fun z : X F => γ • z) ⁻¹' (S ∩ cuspTail F Γ σ A) := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    change ((γ : SL(2,𝓞 F)) • z ∈ S ∧ z ∈ cuspTail F Γ σ A) ↔
      ((γ : SL(2,𝓞 F)) • z ∈ S ∧ (γ : SL(2,𝓞 F)) • z ∈ cuspTail F Γ σ A)
    rw [cuspTail_smul_iff Γ σ A γ z]
  rw [Measure.restrict_apply (hS.preimage (measurable_const_smul γ)),
    Measure.restrict_apply hS, heq]
  exact volX_smul_preimage_eq (toSLF F (γ : SL(2,𝓞 F))) (S ∩ cuspTail F Γ σ A)
    (hS.inter hT)

private theorem cuspStab_unitMatrix (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (γ : Γ) (hγ : γ ∈ cuspStab F Γ σ) :
    ∃ ε : (𝓞 F)ˣ, ε ∈ cuspUnits F Γ σ ∧ ∃ μ : F,
      σ⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * σ = cuspUnitMatrix F ε μ := by
  let b : SL(2,F) := σ⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * σ
  have htri : b ∈ borelSL F := by
    simpa [b, cuspStab, MulAut.conj_apply] using hγ
  obtain ⟨ε, hε, hnorm⟩ :=
    ((G2_x_action (F := F)).2.2.1 (γ : SL(2,𝓞 F)) σ htri).1
  have ha : algebraMap (𝓞 F) F (ε : 𝓞 F) = b 0 0 := hε
  have hb10 : b 1 0 = 0 := htri
  have hdet : b 0 0 * b 1 1 = 1 := by
    have h := b.property
    rw [Matrix.det_fin_two, hb10] at h
    simpa using h
  have hb11 : b 1 1 = (b 0 0)⁻¹ := eq_inv_of_mul_eq_one_right hdet
  have hshape : b = cuspUnitMatrix F ε (b 0 1) := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · exact ha.symm
    · rfl
    · exact hb10
    · simpa [cuspUnitMatrix, ha] using hb11
  exact ⟨ε, Subgroup.subset_closure ⟨b 0 1, γ, hshape⟩, b 0 1, hshape⟩

private theorem cusp_conjugate_action (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (γ : Γ) (b : SL(2,F)) (hb : σ⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * σ = b)
    (z : X F) : (γ : SL(2,𝓞 F)) • (σ • z) = σ • (b • z) := by
  have hmul : toSLF F (γ : SL(2,𝓞 F)) * σ = σ * b := by
    have h := congrArg (fun g : SL(2,F) => σ * g) hb
    simpa only [← mul_assoc, mul_inv_cancel, one_mul] using h
  change toSLF F (γ : SL(2,𝓞 F)) • (σ • z) = σ • (b • z)
  rw [← mul_smul, hmul, mul_smul]

private theorem unitHeightAction_product (ε : (𝓞 F)ˣ) (y : InfinitePlace F → ℝ) :
    (∏ w : InfinitePlace F, unitHeightAction F ε y w) = ∏ w : InfinitePlace F, y w := by
  have hnorm : absUnitNorm F ε = 1 := by
    simpa [absUnitNorm, absFieldNorm_eq_abs_norm] using (NumberField.Units.norm F ε)
  unfold unitHeightAction
  rw [Finset.prod_mul_distrib]
  have hp : (∏ w : InfinitePlace F,
      Complex.normSq (w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F)))) = 1 := by
    simpa [absUnitNorm, absFieldNorm, Complex.normSq_eq_norm_sq] using hnorm
  rw [hp, one_mul]

private theorem unitHeightAction_unique_sign (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (Y : Set (InfinitePlace F → ℝ))
    (hYpos : ∀ y ∈ Y, ∀ w, 0 < y w)
    (hYfd : ∀ y, (∀ w, 0 < y w) →
      ∃ ε : (𝓞 F)ˣ, ε ∈ cuspUnits F Γ σ ∧ unitHeightAction F ε y ∈ Y ∧
        ∀ ε' : (𝓞 F)ˣ, ε' ∈ cuspUnits F Γ σ → unitHeightAction F ε' y ∈ Y →
          ε' = ε ∨ ε' = -ε)
    (y : InfinitePlace F → ℝ) (hy : y ∈ Y) (ε : (𝓞 F)ˣ)
    (hε : ε ∈ cuspUnits F Γ σ) (hεY : unitHeightAction F ε y ∈ Y) :
    ε = 1 ∨ ε = -1 := by
  obtain ⟨δ, hδ, hδY, huniq⟩ := hYfd y (hYpos y hy)
  have hone : unitHeightAction F 1 y = y := by
    funext w
    simp [unitHeightAction]
  have h1 : unitHeightAction F 1 y ∈ Y := by rw [hone]; exact hy
  have hδsign : δ = 1 ∨ δ = -1 := by
    rcases huniq 1 (Subgroup.one_mem _) h1 with h | h
    · exact Or.inl h.symm
    · right
      have hn := congrArg (fun u : (𝓞 F)ˣ => -u) h
      simpa using hn.symm
  rcases huniq ε hε hεY with h | h <;> rcases hδsign with hδ1 | hδ1
  · exact Or.inl (h.trans hδ1)
  · exact Or.inr (h.trans hδ1)
  · right; simpa [hδ1] using h
  · left; simpa [hδ1] using h

private theorem signedMatrix_action (ε : (𝓞 F)ˣ) (μ : F)
    (hε : (algebraMap (𝓞 F) F (ε : 𝓞 F)) ^ 2 = 1)
    (x : InfinitePlace F → ℂ) (y : InfinitePlace F → ℝ) (hy : ∀ w, 0 < y w) :
    signedCuspTranslationMatrix F ε μ hε • ptX' F x y =
      ptX' F (fun w => x w + w.embedding μ) y := by
  have hinv : (algebraMap (𝓞 F) F (ε : 𝓞 F))⁻¹ =
      algebraMap (𝓞 F) F (ε : 𝓞 F) :=
    (eq_inv_of_mul_eq_one_left (by simpa [pow_two] using hε)).symm
  have hmatrix : signedCuspTranslationMatrix F ε μ hε =
      cuspUnitMatrix F ε (algebraMap (𝓞 F) F (ε : 𝓞 F) * μ) := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [signedCuspTranslationMatrix, cuspUnitMatrix, hinv]
  rw [hmatrix, cuspUnitMatrix_action ε _ x y hy]
  funext w
  have hw : (w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))) ^ 2 = 1 := by
    rw [← map_pow, hε, map_one]
  have hn : Complex.normSq (w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))) = 1 := by
    have hs := congrArg (fun z : ℂ => ‖z‖) hw
    simpa only [norm_pow, norm_one, Complex.normSq_eq_norm_sq] using hs
  have hx : (w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))) ^ 2 * x w +
      w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F)) *
        w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F) * μ) = x w + w.embedding μ := by
    rw [map_mul]
    calc
      _ = (w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))) ^ 2 *
          (x w + w.embedding μ) := by ring
      _ = _ := by rw [hw]; simp
  change pt _ _ = pt _ _
  dsimp only
  rw [hx]
  simp [unitHeightAction, hn]

private theorem cuspTranslation_realized (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (σ : SL(2,F)) (t : cuspTranslationExtensionComplex F Γ σ) :
    ∃ γ : Γ, ∀ (x : InfinitePlace F → ℂ) (y : InfinitePlace F → ℝ),
      (∀ w, 0 < y w) →
      (γ : SL(2,𝓞 F)) • (σ • ptX' F x y) = σ • ptX' F (x + (t : _)) y := by
  rcases AddSubgroup.mem_map.mp t.property with ⟨μ, hμ, ht⟩
  rcases ((R1_cusp_lattice Γ σ).2.2.1 μ).mp hμ with ⟨ε, hε, γ, hγ⟩
  refine ⟨γ, ?_⟩
  intro x y hy
  rw [cusp_conjugate_action Γ σ γ _ hγ, signedMatrix_action ε μ hε x y hy]
  have ht' : (fun w : InfinitePlace F => w.embedding μ) = (t : InfinitePlace F → ℂ) := ht
  rw [← ht']
  rfl

private theorem gamma_kernel_eq_one (Γ : Subgroup SL(2,𝓞 F)) (D : Set (X F))
    (hD : IsFundamentalDomain Γ D (volX F)) (γ : Γ)
    (hfix : ∀ z : X F, (γ : SL(2,𝓞 F)) • z = z) : γ = 1 := by
  letI : Countable Γ := countable_Gamma Γ
  letI : SMulInvariantMeasure Γ (X F) (volX F) := gamma_volInvariant Γ
  have hμ : volX F ≠ 0 := by
    intro h
    have hn := (G3_volume (F := F)).2.2.2.1 Set.univ isOpen_univ Set.univ_nonempty
    simp [h] at hn
  have hDzero := hD.measure_ne_zero hμ
  by_contra hγ
  have hdis := hD.aedisjoint hγ
  have himage : (fun z : X F => γ • z) '' D = D := by
    have hf : (fun z : X F => γ • z) = id := by funext z; exact hfix z
    rw [hf, Set.image_id]
  have honeimage : (fun z : X F => (1 : Γ) • z) '' D = D := by
    have hf : (fun z : X F => (1 : Γ) • z) = id := by funext z; exact one_smul _ _
    rw [hf, Set.image_id]
  have hn : volX F D = 0 := by
    change volX F (((fun z : X F => γ • z) '' D) ∩
      ((fun z : X F => (1 : Γ) • z) '' D)) = 0 at hdis
    rw [himage, honeimage, Set.inter_self] at hdis
    exact hdis
  exact hDzero hn

private theorem countable_cuspTranslations (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F)) :
    Countable (cuspTranslationExtensionComplex F Γ σ) := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := F)
  have hcount : (Set.range (infEmb F)).Countable := Set.countable_range _
  have hsub : (cuspTranslationExtensionComplex F Γ σ : Set (InfinitePlace F → ℂ)) ⊆
      Set.range (infEmb F) := by
    intro x hx
    rcases AddSubgroup.mem_map.mp hx with ⟨μ, hμ, rfl⟩
    exact ⟨μ, rfl⟩
  exact (hcount.mono hsub).to_subtype

private def horizontalBad (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (P : Set (InfinitePlace F → ℂ)) : Set (InfinitePlace F → ℂ) :=
  {x | ∀ t : cuspTranslationExtensionComplex F Γ σ, x + (t : _) ∉ P}

private def cuspHorizontal (σ : SL(2,F)) (z : X F) : InfinitePlace F → ℂ :=
  fun w => (coordsX F (σ⁻¹ • z) w).1

private def cuspBadOrbit (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (P : Set (InfinitePlace F → ℂ)) : Set (X F) :=
  ⋃ γ : Γ, (fun z : X F => cuspHorizontal σ ((γ : SL(2,𝓞 F)) • z)) ⁻¹'
    horizontalBad Γ σ P

private theorem cuspHorizontal_measurable (σ : SL(2,F)) : Measurable (cuspHorizontal σ) := by
  letI : BorelSpace (X F) := borelSpace_X (F := F)
  have hpair := (coordsX_measurable (F := F)).comp
    ((continuousSL2FAction (F := F) σ⁻¹).measurable)
  exact measurable_pi_iff.mpr fun w =>
    measurable_fst.comp ((measurable_pi_apply w).comp hpair)

private theorem horizontalBad_measurable (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (P : Set (InfinitePlace F → ℂ)) (hP : MeasurableSet P) :
    MeasurableSet (horizontalBad Γ σ P) := by
  letI : Countable (cuspTranslationExtensionComplex F Γ σ) := countable_cuspTranslations Γ σ
  unfold horizontalBad
  rw [Set.ofPred_forall]
  exact MeasurableSet.iInter fun t =>
    (hP.preimage (measurable_id.add measurable_const)).compl

private theorem horizontalBad_null (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (P : Set (InfinitePlace F → ℂ))
    (hP : IsAddFundamentalDomain (cuspTranslationExtensionComplex F Γ σ) P) :
    volume (horizontalBad Γ σ P) = 0 := by
  have hae : ∀ᵐ x : InfinitePlace F → ℂ ∂volume, x ∉ horizontalBad Γ σ P := by
    filter_upwards [hP.ae_covers] with x hx
    intro hbad
    rcases hx with ⟨t, ht⟩
    change (t : InfinitePlace F → ℂ) + x ∈ P at ht
    exact hbad t (by simpa [add_comm] using ht)
  simpa only [not_not, Set.setOf_mem_eq] using (ae_iff.mp hae)

private theorem cuspBadOrbit_null (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (P : Set (InfinitePlace F → ℂ)) (hPmeas : MeasurableSet P)
    (hP : IsAddFundamentalDomain (cuspTranslationExtensionComplex F Γ σ) P) :
    volX F (cuspBadOrbit Γ σ P) = 0 := by
  letI : Countable Γ := countable_Gamma Γ
  have hB := horizontalBad_measurable Γ σ P hPmeas
  have hBzero := horizontalBad_null Γ σ P hP
  have hzero : volX F ((cuspHorizontal σ) ⁻¹' horizontalBad Γ σ P) = 0 :=
    volX_horizontal_null σ _ hB hBzero
  unfold cuspBadOrbit
  apply measure_iUnion_null
  intro γ
  change volX F ((fun z : X F => toSLF F (γ : SL(2,𝓞 F)) • z) ⁻¹'
    ((cuspHorizontal σ) ⁻¹' horizontalBad Γ σ P)) = 0
  rw [volX_smul_preimage_eq _ _ (hB.preimage (cuspHorizontal_measurable σ))]
  exact hzero

private theorem coordsX_pos (z : X F) : coordsX F z ∈ posSet F := by
  rcases (G1_h3_basics (F := F)) with
    ⟨_, _, _, _, _, _, _, _, _, _, _, ⟨e, _, he⟩⟩
  rw [← he z]
  exact (e.symm z).property

private theorem cuspStrip_cover_good (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (σ : SL(2,F)) (P : Set (InfinitePlace F → ℂ)) (Y : Set (InfinitePlace F → ℝ))
    (hYpos : ∀ y ∈ Y, ∀ w, 0 < y w)
    (hYfd : ∀ y, (∀ w, 0 < y w) →
      ∃ ε : (𝓞 F)ˣ, ε ∈ cuspUnits F Γ σ ∧ unitHeightAction F ε y ∈ Y ∧
        ∀ ε' : (𝓞 F)ˣ, ε' ∈ cuspUnits F Γ σ → unitHeightAction F ε' y ∈ Y →
          ε' = ε ∨ ε' = -ε)
    (A : ℝ) (z : X F) (hz : z ∈ cuspTail F Γ σ A)
    (hgood : z ∉ cuspBadOrbit Γ σ P) :
    ∃ γ : Γ, (γ : SL(2,𝓞 F)) • z ∈ cuspStrip σ P Y A := by
  classical
  rcases hz with ⟨δ, hδ⟩
  let u := σ⁻¹ • ((δ : SL(2,𝓞 F)) • z)
  let x : InfinitePlace F → ℂ := fun w => (coordsX F u w).1
  let y : InfinitePlace F → ℝ := fun w => (coordsX F u w).2
  have hy : ∀ w, 0 < y w := coordsX_pos u
  have hrec : u = ptX' F x y := (ptX_coordsX u).symm
  have hδpoint : (δ : SL(2,𝓞 F)) • z = σ • ptX' F x y := by
    rw [← hrec]
    simp [u]
  have hhigh : A < ∏ w : InfinitePlace F, y w := by
    simpa [← normHeight_ptX'_eq x y hy, ← hrec, u] using hδ
  obtain ⟨ε, hε, hεY, hεuniq⟩ := hYfd y hy
  rcases cuspUnit_realized Γ σ ε hε with ⟨μ, η, hη⟩
  let x₁ : InfinitePlace F → ℂ := fun w =>
    (w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))) ^ 2 * x w +
      w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F)) * w.embedding μ
  let y₁ := unitHeightAction F ε y
  have hy₁ : ∀ w, 0 < y₁ w := hYpos y₁ hεY
  have hmove : ((η * δ : Γ) : SL(2,𝓞 F)) • z = σ • ptX' F x₁ y₁ := by
    simp only [Subgroup.coe_mul, mul_smul, hδpoint]
    rw [cusp_conjugate_action Γ σ η _ hη, cuspUnitMatrix_action ε μ x y hy]
  have hhor : cuspHorizontal σ (((η * δ : Γ) : SL(2,𝓞 F)) • z) = x₁ := by
    rw [hmove]
    have hc := coordsX_ptX'_eq x₁ y₁ hy₁
    funext w
    simpa [cuspHorizontal, hc] using congrArg (fun p : Coord F => (p w).1) hc
  have hnotbad : x₁ ∉ horizontalBad Γ σ P := by
    intro hbad
    apply hgood
    refine Set.mem_iUnion.mpr ⟨η * δ, ?_⟩
    change cuspHorizontal σ (((η * δ : Γ) : SL(2,𝓞 F)) • z) ∈ horizontalBad Γ σ P
    rw [hhor]
    exact hbad
  have htrans : ∃ t : cuspTranslationExtensionComplex F Γ σ, x₁ + (t : _) ∈ P := by
    by_contra h
    apply hnotbad
    intro t ht
    exact h ⟨t, ht⟩
  rcases htrans with ⟨t, ht⟩
  obtain ⟨κ, hκ⟩ := cuspTranslation_realized Γ σ t
  refine ⟨κ * (η * δ), ?_⟩
  have hfinal : ((κ * (η * δ) : Γ) : SL(2,𝓞 F)) • z =
      σ • ptX' F (x₁ + (t : _)) y₁ := by
    rw [Subgroup.coe_mul, mul_smul, hmove]
    exact hκ x₁ y₁ hy₁
  rw [hfinal, cuspStrip_eq_image σ P Y hYpos A]
  refine ⟨fun w => (x₁ w + (t : InfinitePlace F → ℂ) w, y₁ w), ?_, rfl⟩
  refine ⟨ht, hεY, ?_⟩
  simpa [y₁, unitHeightAction_product ε y] using hhigh

private theorem unitHeightAction_pos (ε : (𝓞 F)ˣ) (y : InfinitePlace F → ℝ)
    (hy : ∀ w, 0 < y w) : ∀ w, 0 < unitHeightAction F ε y w := by
  intro w
  have ha : algebraMap (𝓞 F) F (ε : 𝓞 F) ≠ 0 :=
    (ε.isUnit.map (algebraMap (𝓞 F) F)).ne_zero
  have haw : w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F)) ≠ 0 := by
    intro h
    apply ha
    apply w.embedding.injective
    simpa using h
  unfold unitHeightAction
  rw [Complex.normSq_eq_norm_sq]
  exact mul_pos (pow_pos (norm_pos_iff.mpr haw) 2) (hy w)

private theorem cuspUnit_coords (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F)) (γ : Γ)
    (ε : (𝓞 F)ˣ) (μ : F)
    (hγ : σ⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * σ = cuspUnitMatrix F ε μ) (z : X F) :
    coordsX F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) = fun w =>
      ((w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))) ^ 2 *
          (coordsX F (σ⁻¹ • z) w).1 +
        w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F)) * w.embedding μ,
       unitHeightAction F ε (fun w => (coordsX F (σ⁻¹ • z) w).2) w) := by
  let x : InfinitePlace F → ℂ := fun w => (coordsX F (σ⁻¹ • z) w).1
  let y : InfinitePlace F → ℝ := fun w => (coordsX F (σ⁻¹ • z) w).2
  have hy : ∀ w, 0 < y w := coordsX_pos _
  have hrec : z = σ • ptX' F x y := by
    change z = σ • ptX F (coordsX F (σ⁻¹ • z))
    rw [ptX_coordsX]
    simp
  have hmove : (γ : SL(2,𝓞 F)) • z = σ • ptX' F
      (fun w => (w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))) ^ 2 * x w +
        w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F)) * w.embedding μ)
      (unitHeightAction F ε y) := by
    rw [hrec, cusp_conjugate_action Γ σ γ _ hγ, cuspUnitMatrix_action ε μ x y hy]
  rw [hmove]
  simp only [inv_smul_smul]
  exact coordsX_ptX'_eq _ _ (unitHeightAction_pos ε y hy)

private theorem cuspUnit_signed_translation (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (γ : Γ) (ε : (𝓞 F)ˣ) (μ : F)
    (hγ : σ⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * σ = cuspUnitMatrix F ε μ)
    (hsign : ε = 1 ∨ ε = -1) :
    ∃ t : cuspTranslationExtensionComplex F Γ σ,
      ∀ (x : InfinitePlace F → ℂ) (y : InfinitePlace F → ℝ), (∀ w, 0 < y w) →
        (γ : SL(2,𝓞 F)) • (σ • ptX' F x y) = σ • ptX' F (x + (t : _)) y := by
  let ν := algebraMap (𝓞 F) F (ε : 𝓞 F) * μ
  have hs : (algebraMap (𝓞 F) F (ε : 𝓞 F)) ^ 2 = 1 := by
    rcases hsign with rfl | rfl <;> simp
  have hmatrix : cuspUnitMatrix F ε μ = signedCuspTranslationMatrix F ε ν hs := by
    rcases hsign with rfl | rfl <;> apply Subtype.ext <;> ext i j <;>
      fin_cases i <;> fin_cases j <;> simp [cuspUnitMatrix, signedCuspTranslationMatrix, ν]
  have hν : ν ∈ cuspTranslationExtension F Γ σ :=
    AddSubgroup.subset_closure ⟨ε, hs, γ, hγ.trans hmatrix⟩
  let t : cuspTranslationExtensionComplex F Γ σ :=
    ⟨infEmb F ν, AddSubgroup.mem_map.mpr ⟨ν, hν, rfl⟩⟩
  refine ⟨t, ?_⟩
  intro x y hy
  rw [cusp_conjugate_action Γ σ γ _ (hγ.trans hmatrix), signedMatrix_action ε ν hs x y hy]
  rfl

private theorem cuspHorizontal_shift (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F)) (γ : Γ)
    (t : cuspTranslationExtensionComplex F Γ σ)
    (hshift : ∀ (x : InfinitePlace F → ℂ) (y : InfinitePlace F → ℝ), (∀ w, 0 < y w) →
      (γ : SL(2,𝓞 F)) • (σ • ptX' F x y) = σ • ptX' F (x + (t : _)) y)
    (z : X F) : cuspHorizontal σ ((γ : SL(2,𝓞 F)) • z) =
      cuspHorizontal σ z + (t : _) := by
  let x : InfinitePlace F → ℂ := fun w => (coordsX F (σ⁻¹ • z) w).1
  let y : InfinitePlace F → ℝ := fun w => (coordsX F (σ⁻¹ • z) w).2
  have hy : ∀ w, 0 < y w := coordsX_pos _
  have hrec : z = σ • ptX' F x y := by
    change z = σ • ptX F (coordsX F (σ⁻¹ • z))
    rw [ptX_coordsX]
    simp
  calc
    _ = x + (t : _) := by
      rw [hrec, hshift x y hy]
      have hc := coordsX_ptX'_eq (x + (t : InfinitePlace F → ℂ)) y hy
      funext w
      simpa [cuspHorizontal, hc] using congrArg (fun p : Coord F => (p w).1) hc
    _ = _ := rfl

private theorem cuspTranslation_nonzero (Γ : Subgroup SL(2,𝓞 F)) (D : Set (X F))
    (hD : IsFundamentalDomain Γ D (volX F)) (σ : SL(2,F)) (γ : Γ) (hγ : γ ≠ 1)
    (t : cuspTranslationExtensionComplex F Γ σ)
    (hshift : ∀ (x : InfinitePlace F → ℂ) (y : InfinitePlace F → ℝ), (∀ w, 0 < y w) →
      (γ : SL(2,𝓞 F)) • (σ • ptX' F x y) = σ • ptX' F (x + (t : _)) y) : t ≠ 0 := by
  intro ht
  apply hγ
  apply gamma_kernel_eq_one Γ D hD γ
  intro z
  let x : InfinitePlace F → ℂ := fun w => (coordsX F (σ⁻¹ • z) w).1
  let y : InfinitePlace F → ℝ := fun w => (coordsX F (σ⁻¹ • z) w).2
  have hy : ∀ w, 0 < y w := coordsX_pos _
  have hrec : z = σ • ptX' F x y := by
    change z = σ • ptX F (coordsX F (σ⁻¹ • z))
    rw [ptX_coordsX]
    simp
  calc
    _ = σ • ptX' F (x + (t : _)) y := by rw [hrec]; exact hshift x y hy
    _ = z := by simpa [ht] using hrec.symm

private theorem horizontal_overlap_null (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (P : Set (InfinitePlace F → ℂ)) (hPmeas : MeasurableSet P)
    (hP : IsAddFundamentalDomain (cuspTranslationExtensionComplex F Γ σ) P)
    (t : cuspTranslationExtensionComplex F Γ σ) (ht : t ≠ 0) :
    volume (P ∩ (fun x : InfinitePlace F → ℂ => x - (t : _)) ⁻¹' P) = 0 := by
  have hdis := hP.aedisjoint ht
  change volume (((fun x : InfinitePlace F → ℂ => (t : _) + x) '' P) ∩
    ((fun x : InfinitePlace F → ℂ => ((0 : cuspTranslationExtensionComplex F Γ σ) : _) + x) '' P)) = 0 at hdis
  have hzero : (fun x : InfinitePlace F → ℂ => ((0 : cuspTranslationExtensionComplex F Γ σ) : _) + x) '' P = P := by
    have hf : (fun x : InfinitePlace F → ℂ => ((0 : cuspTranslationExtensionComplex F Γ σ) : _) + x) = id := by
      funext x
      simp
    rw [hf, Set.image_id]
  have himage : (fun x : InfinitePlace F → ℂ => (t : _) + x) '' P =
      (fun x : InfinitePlace F → ℂ => x - (t : _)) ⁻¹' P := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      change (t : _) + u - (t : _) ∈ P
      simpa using hu
    · intro hx
      refine ⟨x - (t : _), hx, ?_⟩
      change (t : _) + (x - (t : _)) = x
      abel
  rw [himage, hzero] at hdis
  simpa [Set.inter_comm] using hdis

private theorem cuspStrip_overlap_stabilizer (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (P : Set (InfinitePlace F → ℂ)) (Y : Set (InfinitePlace F → ℝ)) (A₀ A : ℝ)
    (hA : A₀ ≤ A)
    (hsep : ∀ γ γ' : Γ, ∀ z : X F,
      A₀ ≤ normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
      A₀ ≤ normHeight F (σ⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
        γ' * γ⁻¹ ∈ cuspStab F Γ σ)
    (γ : Γ) (z : X F) (hz : z ∈ cuspStrip σ P Y A)
    (hγz : (γ : SL(2,𝓞 F)) • z ∈ cuspStrip σ P Y A) : γ ∈ cuspStab F Γ σ := by
  have h1 : A₀ ≤ normHeight F (σ⁻¹ • z) := hA.trans hz.2.2.le
  have h2 : A₀ ≤ normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) := hA.trans hγz.2.2.le
  simpa using hsep 1 γ z (by simpa using h1) h2

private theorem cuspStrip_aedisjoint (Γ : Subgroup SL(2,𝓞 F)) (D : Set (X F))
    (hD : IsFundamentalDomain Γ D (volX F)) (σ : SL(2,F))
    (P : Set (InfinitePlace F → ℂ)) (hPmeas : MeasurableSet P)
    (hP : IsAddFundamentalDomain (cuspTranslationExtensionComplex F Γ σ) P)
    (Y : Set (InfinitePlace F → ℝ)) (hYpos : ∀ y ∈ Y, ∀ w, 0 < y w)
    (hYfd : ∀ y, (∀ w, 0 < y w) →
      ∃ ε : (𝓞 F)ˣ, ε ∈ cuspUnits F Γ σ ∧ unitHeightAction F ε y ∈ Y ∧
        ∀ ε' : (𝓞 F)ˣ, ε' ∈ cuspUnits F Γ σ → unitHeightAction F ε' y ∈ Y →
          ε' = ε ∨ ε' = -ε)
    (A₀ A : ℝ) (hA : A₀ ≤ A)
    (hsep : ∀ γ γ' : Γ, ∀ z : X F,
      A₀ ≤ normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
      A₀ ≤ normHeight F (σ⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
        γ' * γ⁻¹ ∈ cuspStab F Γ σ)
    (γ : Γ) (hγ : γ ≠ 1) :
    AEDisjoint (volX F) ((fun z : X F => (γ : SL(2,𝓞 F)) • z) '' cuspStrip σ P Y A)
      (cuspStrip σ P Y A) := by
  classical
  by_cases hstab : γ ∈ cuspStab F Γ σ
  · obtain ⟨ε, hε, μ, hmatrix⟩ := cuspStab_unitMatrix Γ σ γ hstab
    by_cases hsign : ε = 1 ∨ ε = -1
    · obtain ⟨t, hshift⟩ := cuspUnit_signed_translation Γ σ γ ε μ hmatrix hsign
      have ht := cuspTranslation_nonzero Γ D hD σ γ hγ t hshift
      let B := P ∩ (fun x : InfinitePlace F → ℂ => x - (t : _)) ⁻¹' P
      have hB : MeasurableSet B := hPmeas.inter
        (hPmeas.preimage (measurable_id.sub measurable_const))
      have hBzero : volume B = 0 := horizontal_overlap_null Γ σ P hPmeas hP t ht
      apply measure_mono_null ?_ (volX_horizontal_null σ B hB hBzero)
      rintro z ⟨⟨u, hu, rfl⟩, hgu⟩
      change cuspHorizontal σ ((γ : SL(2,𝓞 F)) • u) ∈ B
      refine ⟨hgu.1, ?_⟩
      rw [cuspHorizontal_shift Γ σ γ t hshift u]
      change (cuspHorizontal σ u + (t : InfinitePlace F → ℂ)) - (t : _) ∈ P
      rw [add_sub_cancel_right]
      change (fun w => (coordsX F (σ⁻¹ • u) w).1) ∈ P
      exact hu.1
    · have hempty : ((fun z : X F => (γ : SL(2,𝓞 F)) • z) '' cuspStrip σ P Y A) ∩
          cuspStrip σ P Y A = ∅ := by
        ext z
        constructor
        · rintro ⟨⟨u, hu, rfl⟩, hgu⟩
          have hc := cuspUnit_coords Γ σ γ ε μ hmatrix u
          have hh : (fun w => (coordsX F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • u)) w).2) =
              unitHeightAction F ε (fun w => (coordsX F (σ⁻¹ • u) w).2) := by
            funext w
            exact congrArg (fun p : Coord F => (p w).2) hc
          have hεY : unitHeightAction F ε (fun w => (coordsX F (σ⁻¹ • u) w).2) ∈ Y := by
            rw [← hh]
            exact hgu.2.1
          exact (hsign (unitHeightAction_unique_sign Γ σ Y hYpos hYfd _ hu.2.1 ε hε hεY)).elim
        · simp
      change volX F _ = 0
      rw [hempty]
      simp
  · have hempty : ((fun z : X F => (γ : SL(2,𝓞 F)) • z) '' cuspStrip σ P Y A) ∩
        cuspStrip σ P Y A = ∅ := by
      ext z
      constructor
      · rintro ⟨⟨u, hu, rfl⟩, hgu⟩
        exact (hstab (cuspStrip_overlap_stabilizer Γ σ P Y A₀ A hA hsep γ u hu hgu)).elim
      · simp
    change volX F _ = 0
    rw [hempty]
    simp

private theorem cuspStrip_fundamentalDomain (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F)) (σ : SL(2,F))
    (P : Set (InfinitePlace F → ℂ)) (hPmeas : MeasurableSet P)
    (hP : IsAddFundamentalDomain (cuspTranslationExtensionComplex F Γ σ) P)
    (Y : Set (InfinitePlace F → ℝ)) (hYmeas : MeasurableSet Y)
    (hYpos : ∀ y ∈ Y, ∀ w, 0 < y w)
    (hYfd : ∀ y, (∀ w, 0 < y w) →
      ∃ ε : (𝓞 F)ˣ, ε ∈ cuspUnits F Γ σ ∧ unitHeightAction F ε y ∈ Y ∧
        ∀ ε' : (𝓞 F)ˣ, ε' ∈ cuspUnits F Γ σ → unitHeightAction F ε' y ∈ Y →
          ε' = ε ∨ ε' = -ε)
    (A₀ A : ℝ) (hA : A₀ ≤ A)
    (hsep : ∀ γ γ' : Γ, ∀ z : X F,
      A₀ ≤ normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
      A₀ ≤ normHeight F (σ⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
        γ' * γ⁻¹ ∈ cuspStab F Γ σ) :
    IsFundamentalDomain Γ (cuspStrip σ P Y A) ((volX F).restrict (cuspTail F Γ σ A)) := by
  letI : Countable Γ := countable_Gamma Γ
  letI : MeasurableConstSMul Γ (X F) := gamma_measurable Γ
  letI : SMulInvariantMeasure Γ (X F) ((volX F).restrict (cuspTail F Γ σ A)) :=
    gamma_tailInvariant Γ σ A
  have hbad : ((volX F).restrict (cuspTail F Γ σ A)) (cuspBadOrbit Γ σ P) = 0 :=
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
      (cuspBadOrbit_null Γ σ P hPmeas hP)
  have hgood : ∀ᵐ z ∂((volX F).restrict (cuspTail F Γ σ A)), z ∉ cuspBadOrbit Γ σ P := by
    rw [ae_iff]
    simpa only [not_not, Set.setOf_mem_eq] using hbad
  refine IsFundamentalDomain.mk'' (cuspStrip_measurable σ P hPmeas Y hYmeas A).nullMeasurableSet
    ?_ ?_ (fun γ => (measurePreserving_smul γ _).quasiMeasurePreserving)
  · filter_upwards [hgood, ae_restrict_mem (cuspTail_measurable Γ σ A)] with z hzGood hzTail
    exact cuspStrip_cover_good Γ σ P Y hYpos hYfd A z hzTail hzGood
  · intro γ hγ
    have hbase := cuspStrip_aedisjoint Γ D hD σ P hPmeas hP Y hYpos hYfd A₀ A hA hsep γ hγ
    exact (Measure.absolutelyContinuous_of_le Measure.restrict_le_self) hbase

private theorem cuspStrip_integral_transfer (Γ : Subgroup SL(2,𝓞 F))
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F)) (σ : SL(2,F))
    (P : Set (InfinitePlace F → ℂ)) (Y : Set (InfinitePlace F → ℝ)) (A : ℝ)
    (hR : IsFundamentalDomain Γ (cuspStrip σ P Y A)
      ((volX F).restrict (cuspTail F Γ σ A)))
    (G : X F → ℂ) (hGinv : IsGammaInvariant F Γ G)
    (hGint : IntegrableOn G (D ∩ cuspTail F Γ σ A) (volX F)) :
    IntegrableOn G (cuspStrip σ P Y A) (volX F) ∧
      (∫ z in D ∩ cuspTail F Γ σ A, G z ∂(volX F)) =
        ∫ z in cuspStrip σ P Y A, G z ∂(volX F) := by
  letI : Countable Γ := countable_Gamma Γ
  letI : MeasurableConstSMul Γ (X F) := gamma_measurable Γ
  letI : SMulInvariantMeasure Γ (X F) ((volX F).restrict (cuspTail F Γ σ A)) :=
    gamma_tailInvariant Γ σ A
  have hT := cuspTail_measurable Γ σ A
  have hDr : IsFundamentalDomain Γ D ((volX F).restrict (cuspTail F Γ σ A)) :=
    hD.mono (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  have hf : ∀ γ : Γ, ∀ z : X F, G (γ • z) = G z :=
    fun γ z => hGinv (γ : SL(2,𝓞 F)) γ.property z
  have hDint : IntegrableOn G D ((volX F).restrict (cuspTail F Γ σ A)) := by
    simpa only [IntegrableOn, Measure.restrict_restrict' hT] using hGint
  have hRint := (hDr.integrableOn_iff hR hf).mp hDint
  have hrestrict : ((volX F).restrict (cuspTail F Γ σ A)).restrict (cuspStrip σ P Y A) =
      (volX F).restrict (cuspStrip σ P Y A) :=
    Measure.restrict_restrict_of_subset (cuspStrip_subset_tail Γ σ P Y A)
  refine ⟨?_, ?_⟩
  · simpa only [IntegrableOn, hrestrict] using hRint
  · have hinter : cuspStrip σ P Y A ∩ cuspTail F Γ σ A = cuspStrip σ P Y A :=
      Set.inter_eq_left.mpr (cuspStrip_subset_tail Γ σ P Y A)
    simpa only [Measure.restrict_restrict' hT, hinter] using hDr.setIntegral_eq hR hf

private def cuspChart (σ : SL(2,F)) (p : Coord F) : X F := σ • ptX F p

private theorem cuspChart_aemeasurable (σ : SL(2,F)) :
    AEMeasurable (cuspChart σ) (weightedCoordVolume (F := F)) := by
  letI : BorelSpace (X F) := borelSpace_X (F := F)
  exact ((continuousSL2FAction (F := F) σ).measurable).comp_aemeasurable
    (ptX_aemeasurable_weighted (F := F))

private theorem cuspChart_map (σ : SL(2,F)) :
    Measure.map (cuspChart σ) (weightedCoordVolume (F := F)) = volX F := by
  letI : BorelSpace (X F) := borelSpace_X (F := F)
  have hs : Measurable (fun z : X F => σ • z) := (continuousSL2FAction (F := F) σ).measurable
  calc
    _ = Measure.map (fun z : X F => σ • z)
        (Measure.map (ptX F) (weightedCoordVolume (F := F))) :=
      (AEMeasurable.map_map_of_aemeasurable hs.aemeasurable
        (ptX_aemeasurable_weighted (F := F))).symm
    _ = volX F := (G3_volume (F := F)).1 (toInf F σ)

private theorem cuspChart_preimage_strip (σ : SL(2,F))
    (P : Set (InfinitePlace F → ℂ)) (Y : Set (InfinitePlace F → ℝ)) (A : ℝ) :
    (cuspChart σ) ⁻¹' cuspStrip σ P Y A =ᵐ[weightedCoordVolume (F := F)]
      cuspCoordRegion P Y A := by
  filter_upwards [weightedCoordVolume_pos_ae (F := F)] with p hp
  change (coordsX F (σ⁻¹ • (σ • ptX F p)) ∈ cuspCoordRegion P Y A) =
    (p ∈ cuspCoordRegion P Y A)
  rw [inv_smul_smul, coordsX_ptX p hp]

private theorem cuspChart_map_restrict (σ : SL(2,F)) (P : Set (InfinitePlace F → ℂ))
    (hP : MeasurableSet P) (Y : Set (InfinitePlace F → ℝ))
    (hY : MeasurableSet Y) (A : ℝ) :
    Measure.map (cuspChart σ) ((weightedCoordVolume (F := F)).restrict (cuspCoordRegion P Y A)) =
      (volX F).restrict (cuspStrip σ P Y A) := by
  have hE := cuspCoordRegion_measurable P hP Y hY A
  have hR := cuspStrip_measurable σ P hP Y hY A
  have hφ := cuspChart_aemeasurable σ
  have hφr : AEMeasurable (cuspChart σ)
      ((weightedCoordVolume (F := F)).restrict (cuspCoordRegion P Y A)) :=
    hφ.mono_ac (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  have heq := cuspChart_preimage_strip σ P Y A
  ext S hS
  rw [Measure.map_apply_of_aemeasurable hφr hS, Measure.restrict_apply' hE,
    Measure.restrict_apply hS, ← cuspChart_map σ,
    Measure.map_apply_of_aemeasurable hφ (hS.inter hR), Set.preimage_inter]
  apply measure_congr
  filter_upwards [heq] with p hp
  simp only [Set.mem_inter_iff, Set.mem_preimage] at hp ⊢
  rw [hp]

private theorem cuspStrip_pullback (σ : SL(2,F)) (P : Set (InfinitePlace F → ℂ))
    (hP : MeasurableSet P) (Y : Set (InfinitePlace F → ℝ))
    (hY : MeasurableSet Y) (A : ℝ) (G : X F → ℂ)
    (hG : IntegrableOn G (cuspStrip σ P Y A) (volX F)) :
    Integrable (fun p : Coord F => G (cuspChart σ p))
      ((weightedCoordVolume (F := F)).restrict (cuspCoordRegion P Y A)) ∧
    (∫ z in cuspStrip σ P Y A, G z ∂(volX F)) =
      ∫ p in cuspCoordRegion P Y A, G (cuspChart σ p) ∂(weightedCoordVolume (F := F)) := by
  have hφ : AEMeasurable (cuspChart σ)
      ((weightedCoordVolume (F := F)).restrict (cuspCoordRegion P Y A)) :=
    (cuspChart_aemeasurable σ).mono_ac
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  have hmap := cuspChart_map_restrict σ P hP Y hY A
  have hGmap : Integrable G (Measure.map (cuspChart σ)
      ((weightedCoordVolume (F := F)).restrict (cuspCoordRegion P Y A))) := by
    rw [hmap]
    exact hG
  refine ⟨hGmap.comp_aemeasurable hφ, ?_⟩
  rw [← hmap]
  exact integral_map hφ hGmap.aestronglyMeasurable

private def coordinateDensity (p : Coord F) : ENNReal :=
  ENNReal.ofReal (∏ w : InfinitePlace F, ((p w).2 ^ 3)⁻¹)

private theorem coordinateDensity_measurable : Measurable (coordinateDensity (F := F)) := by
  have hm : Measurable (fun p : Coord F => ∏ w : InfinitePlace F, ((p w).2 ^ 3)⁻¹) :=
    Finset.measurable_fun_prod Finset.univ (fun w hw =>
      ((measurable_snd.comp (measurable_pi_apply w)).pow_const 3).inv)
  exact hm.ennreal_ofReal

private theorem coordinateDensity_mul (p : Coord F) (hp : p ∈ posSet F) (g : ℂ) :
    (coordinateDensity p).toReal • g = g * (∏ w : InfinitePlace F, ((p w).2 ^ 3)⁻¹) := by
  have hd : 0 ≤ ∏ w : InfinitePlace F, ((p w).2 ^ 3)⁻¹ := by
    apply Finset.prod_nonneg
    intro w hw
    exact inv_nonneg.mpr (pow_nonneg (hp w).le _)
  rw [coordinateDensity, ENNReal.toReal_ofReal hd, Complex.real_smul, mul_comm]

private theorem cuspStrip_weighted_pullback (σ : SL(2,F)) (P : Set (InfinitePlace F → ℂ))
    (hP : MeasurableSet P) (Y : Set (InfinitePlace F → ℝ))
    (hY : MeasurableSet Y) (hYpos : ∀ y ∈ Y, ∀ w, 0 < y w)
    (A : ℝ) (G : X F → ℂ) (hG : IntegrableOn G (cuspStrip σ P Y A) (volX F)) :
    IntegrableOn (fun p : Coord F => G (cuspChart σ p) *
      (∏ w : InfinitePlace F, ((p w).2 ^ 3)⁻¹)) (cuspCoordRegion P Y A) volume ∧
    (∫ z in cuspStrip σ P Y A, G z ∂(volX F)) =
      ∫ p in cuspCoordRegion P Y A, G (cuspChart σ p) *
        (∏ w : InfinitePlace F, ((p w).2 ^ 3)⁻¹) ∂volume := by
  have hE := cuspCoordRegion_measurable P hP Y hY A
  have hEpos : cuspCoordRegion P Y A ⊆ posSet F := fun p hp => hYpos _ hp.2.1
  have hμ : (weightedCoordVolume (F := F)).restrict (cuspCoordRegion P Y A) =
      (volume.restrict (cuspCoordRegion P Y A)).withDensity (coordinateDensity (F := F)) := by
    rw [weightedCoordVolume, restrict_withDensity hE,
      Measure.restrict_restrict_of_subset hEpos]
    rfl
  obtain ⟨hPull, hInt⟩ := cuspStrip_pullback σ P hP Y hY A G hG
  rw [hμ] at hPull hInt
  have hρ := coordinateDensity_measurable (F := F)
  have hfinite : ∀ᵐ p ∂(volume.restrict (cuspCoordRegion P Y A)), coordinateDensity p < ⊤ :=
    Filter.Eventually.of_forall fun p => ENNReal.ofReal_lt_top
  have hweight := (integrable_withDensity_iff_integrable_smul' hρ hfinite).mp hPull
  have hae : (fun p : Coord F => (coordinateDensity p).toReal • G (cuspChart σ p)) =ᵐ[
      volume.restrict (cuspCoordRegion P Y A)]
      (fun p : Coord F => G (cuspChart σ p) * (∏ w, ((p w).2 ^ 3)⁻¹)) := by
    filter_upwards [ae_restrict_mem hE] with p hp
    exact coordinateDensity_mul p (hEpos hp) _
  refine ⟨hweight.congr hae, ?_⟩
  calc
    _ = ∫ p, G (cuspChart σ p)
        ∂(volume.restrict (cuspCoordRegion P Y A)).withDensity (coordinateDensity (F := F)) := hInt
    _ = ∫ p in cuspCoordRegion P Y A, (coordinateDensity p).toReal •
        G (cuspChart σ p) ∂volume := integral_withDensity_eq_integral_toReal_smul hρ hfinite _
    _ = _ := integral_congr_ae hae

private theorem cuspHeightRegion_measurable (Y : Set (InfinitePlace F → ℝ))
    (hY : MeasurableSet Y) (A : ℝ) :
    MeasurableSet {y ∈ Y | A < ∏ w : InfinitePlace F, y w} := by
  have hprod : Measurable (fun y : InfinitePlace F → ℝ => ∏ w, y w) :=
    Finset.measurable_fun_prod Finset.univ (fun w hw => measurable_pi_apply w)
  exact hY.inter (measurableSet_Ioi.preimage hprod)

private theorem cuspRegion_product_measure (P : Set (InfinitePlace F → ℂ))
    (hP : MeasurableSet P) (Y : Set (InfinitePlace F → ℝ))
    (hY : MeasurableSet Y) (A : ℝ) :
    MeasurePreserving (MeasurableEquiv.arrowProdEquivProdArrow ℂ ℝ (InfinitePlace F))
      (volume.restrict (cuspCoordRegion P Y A))
      ((volume.restrict P).prod
        (volume.restrict {y ∈ Y | A < ∏ w : InfinitePlace F, y w})) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℂ ℝ (InfinitePlace F)
  let H := {y ∈ Y | A < ∏ w : InfinitePlace F, y w}
  have hH : MeasurableSet H := cuspHeightRegion_measurable Y hY A
  have hMP := volume_measurePreserving_arrowProdEquivProdArrow ℂ ℝ (InfinitePlace F)
  have hpre : e ⁻¹' (P ×ˢ H) = cuspCoordRegion P Y A := by
    ext p
    simp [e, H, cuspCoordRegion, MeasurableEquiv.arrowProdEquivProdArrow]
  have h := hMP.restrict_preimage (hP.prod hH)
  rw [hpre] at h
  simpa only [Measure.volume_eq_prod, ← Measure.prod_restrict] using h

private theorem integral_cuspStrip (σ : SL(2,F)) (P : Set (InfinitePlace F → ℂ))
    (hP : MeasurableSet P) (Y : Set (InfinitePlace F → ℝ))
    (hY : MeasurableSet Y) (hYpos : ∀ y ∈ Y, ∀ w, 0 < y w)
    (A : ℝ) (G : X F → ℂ) (hG : IntegrableOn G (cuspStrip σ P Y A) (volX F)) :
    (∫ z in cuspStrip σ P Y A, G z ∂(volX F)) =
      ∫ y in {y ∈ Y | A < ∏ w : InfinitePlace F, y w},
        (∫ x in P, G (σ • ptX' F x y) ∂volume) *
          (∏ w : InfinitePlace F, (y w ^ 3)⁻¹) ∂volume := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℂ ℝ (InfinitePlace F)
  let H := {y ∈ Y | A < ∏ w : InfinitePlace F, y w}
  let f : (InfinitePlace F → ℂ) × (InfinitePlace F → ℝ) → ℂ := fun p =>
    G (σ • ptX' F p.1 p.2) * (∏ w : InfinitePlace F, (p.2 w ^ 3)⁻¹)
  obtain ⟨hweighted, hcoordinate⟩ := cuspStrip_weighted_pullback σ P hP Y hY hYpos A G hG
  have hMP := cuspRegion_product_measure P hP Y hY A
  have hcomp : (fun p : Coord F => G (cuspChart σ p) *
      (∏ w : InfinitePlace F, ((p w).2 ^ 3)⁻¹)) = f ∘ e := rfl
  have hf : Integrable f ((volume.restrict P).prod (volume.restrict H)) := by
    apply (hMP.integrable_comp_emb e.measurableEmbedding).mp
    rw [← hcomp]
    exact hweighted
  calc
    _ = ∫ p in cuspCoordRegion P Y A, G (cuspChart σ p) *
        (∏ w : InfinitePlace F, ((p w).2 ^ 3)⁻¹) ∂volume := hcoordinate
    _ = ∫ p, f p ∂(volume.restrict P).prod (volume.restrict H) := by
      rw [hcomp]
      exact hMP.integral_comp' f
    _ = ∫ y in H, ∫ x in P, f (x, y) ∂volume ∂volume := integral_prod_symm f hf
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y =>
        integral_mul_const ((∏ w : InfinitePlace F, (y w ^ 3)⁻¹ : ℝ) : ℂ)
          (fun x => G (σ • ptX' F x y))

/-- R14 `spec:cusp-fubini` — P-SPEC.md:227, 344–347. The invariant integral over a high cusp
tail is the integral over a unit-height domain and a signed-translation domain. Correction from
`sol-gate-spec`: assume integrability on the quotient tail used by the change of fundamental domain. -/
theorem R14_cusp_fubini (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (σ : SL(2,F)) (A₀ A : ℝ) (hA₀ : 1 ≤ A₀) (hA : A₀ ≤ A)
    (hsep : ∀ γ γ' : Γ, ∀ z : X F,
      A₀ ≤ normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
      A₀ ≤ normHeight F (σ⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
      γ' * γ⁻¹ ∈ cuspStab F Γ σ)
    (Y : Set (InfinitePlace F → ℝ))
    (hYmeas : MeasurableSet Y)
    (hYpos : ∀ y ∈ Y, ∀ w, 0 < y w)
    (hYfd : ∀ y, (∀ w, 0 < y w) →
      ∃ ε : (𝓞 F)ˣ, ε ∈ cuspUnits F Γ σ ∧ unitHeightAction F ε y ∈ Y ∧
        ∀ ε' : (𝓞 F)ˣ, ε' ∈ cuspUnits F Γ σ → unitHeightAction F ε' y ∈ Y →
          ε' = ε ∨ ε' = -ε)
    (P' : Set (InfinitePlace F → ℂ))
    (hP' : IsAddFundamentalDomain (cuspTranslationExtensionComplex F Γ σ) P')
    (hP'meas : MeasurableSet P')
    (G : X F → ℂ) (hGinv : IsGammaInvariant F Γ G)
    (hGint : IntegrableOn G (D ∩ cuspTail F Γ σ A) (volX F)) :
    ∫ z in D ∩ cuspTail F Γ σ A, G z ∂(volX F) =
      ∫ y in {y ∈ Y | A < ∏ w : InfinitePlace F, y w},
        (∫ x in P', G (σ • ptX' F x y) ∂volume) *
          (∏ w : InfinitePlace F, (y w ^ 3)⁻¹) ∂volume := by
  have hR := cuspStrip_fundamentalDomain Γ D hD σ P' hP'meas hP' Y hYmeas hYpos hYfd
    A₀ A hA hsep
  obtain ⟨hGstrip, htransport⟩ :=
    cuspStrip_integral_transfer Γ D hD σ P' Y A hR G hGinv hGint
  exact htransport.trans (integral_cuspStrip σ P' hP'meas Y hYmeas hYpos A G hGstrip)

end ArtinPrimitiveRoots.A1.Spec
