import ArtinPrimitiveRoots.Spec.Stage1
import Mathlib.LinearAlgebra.Countable
import Mathlib.Topology.Bases
import Mathlib.Data.Set.Finite.Lemmas

-- Preserve the frozen quotient topology used in Geometry.
attribute [-instance] OAI.CubicEisenstein.complexSLTopology

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
  · sorry

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
  sorry

end ArtinPrimitiveRoots.A1.Spec
