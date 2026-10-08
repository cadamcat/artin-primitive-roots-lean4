import ArtinPrimitiveRoots.A2.ZeroFree.Nodes
import ArtinPrimitiveRoots.A2.ZeroFree.Density
import ArtinPrimitiveRoots.A2.Poisson.Missing
import ArtinPrimitiveRoots.A2.Interface

/-! A2 statement interfaces derived from the design lane. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
open NumberField IsDedekindDomain MeasureTheory
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A2
open ArtinPrimitiveRoots A1 A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

section ZeroFree
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}
variable (R : ReflectionSetup D S H Bd A ϑ bc μ v0) (sd : S.SelfDualMeasure A)
  (W : PoissonWeights (S := S)) (η : HeckeChar F) (U : FrequencyData S D η)
  (HA : HeckeAnalysis F) (HC : EulerCorrection R η U)

def frequencyDyad (U0 : ℝ) : Set U.U := {u | U0 ≤ U.q u ∧ U.q u < 2 * U0}
def rowTwist (u : U.U) : HeckeChar F := η * (U.kummer u)⁻¹

/-- A single fixed choice of exceptional sets, with constants uniform over all growing dyads. -/
structure ZeroDensityData where
  ρ : ℝ
  ρ_pos : 0 < ρ
  U0 : ℝ
  U0_two : 2 ≤ U0
  Cexc : ℝ
  Cexc_pos : 0 < Cexc
  E : ℝ → Finset U.U
  E_sub : ∀ T, U0 ≤ T → ∀ u ∈ E T, u ∈ frequencyDyad η U T
  E_count : ∀ T, U0 ≤ T → ((E T).card : ℝ) ≤ Cexc * T ^ (1 / 2 : ℝ)
  covers : ∀ T, U0 ≤ T → ∀ u ∈ frequencyDyad η U T,
    (rowTwist η U u = 1 ∨ ∃ s : ℂ, 996 / 1000 ≤ s.re ∧ |s.im| ≤ 4 * T ^ ρ ∧ HA.L (rowTwist η U u) s = 0) →
      u ∈ E T
  reciprocal : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ T, U0 ≤ T →
    ∀ u ∈ frequencyDyad η U T, u ∉ E T → ∀ s : ℂ, 998 / 1000 ≤ s.re → |s.im| ≤ 2 * T ^ ρ →
      HA.LS S (rowTwist η U u) s ≠ 0 ∧ ‖(HA.LS S (rowTwist η U u) s)⁻¹‖ ≤ C * T ^ ε

/-- zf:height-decay, 06:389–411. Real strips are fixed, with positive lower z endpoint. -/
theorem zf_height_decay : ∀ lξ rξ lw rw lz rz A0 : ℝ,
  lξ ≤ rξ → lw ≤ rw → 0 < lz → lz ≤ rz → 0 < A0 → ∃ C : ℝ, 0 < C ∧
    ∀ ξ w z : ℂ, lξ ≤ ξ.re → ξ.re ≤ rξ → lw ≤ w.re → w.re ≤ rw → lz ≤ z.re → z.re ≤ rz →
      ‖Complex.exp ((ξ + z - 1) ^ 2) * weightM R sd W z * weightW1hat W w‖ ≤
        C * Real.exp (-((ξ.im + z.im) ^ 2)) * (1 + |z.im|) ^ (-A0) * (1 + |w.im|) ^ (-A0) := by
  sorry
/-- zf:height-decay, 06:389-411. Gaussian convolution preserves arbitrary polynomial decay. -/
theorem zf_height_convolution : ∀ A1 : ℝ, 0 < A1 → ∃ A0 C : ℝ, 1 < A0 ∧ 0 < C ∧ ∀ T : ℝ,
  (∫ v : ℝ, Real.exp (-((T + v) ^ 2)) * (1 + |v|) ^ (-A0)) ≤ C * (1 + |T|) ^ (-A1) := by
  sorry
/-- def:zf-principal-mellin, 06:458–476: the exact residue scalar in the chosen normalization. -/
def principalConstant : ℂ := HA.RS S ^ 2 / 6 * weightM R sd W (1 / 6) * weightW1hat W 1
def principalSignal (Z : ℝ) : ℂ := fEta (Heta R η U HC) (HA.LS S η) Z

def rowKernel (u : U.U) (Z : ℝ) (ξ w z : ℂ) : ℂ :=
  mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ w z * (U.q u : ℂ) ^ (-z) *
    HA.LS S 1 (6 * z) * HA.LS S (U.kummer u) w * HC.H u ![ξ,w,z] / HA.LS S (rowTwist η U u) ξ

def rowContribution (C : Finset U.U) (Z : ℝ) : ℂ :=
  tripleVertical 4 4 2 (fun ξ w z => mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ w z *
    ∑ u ∈ C, (U.q u : ℂ) ^ (-z) * calF R η U u ξ w z)

def principalRw (Z : ℝ) : ℂ := tripleVertical (1 + δ1) (95 / 100) (1 / 6 + δ1) (rowKernel R sd W η U HA HC U.one Z)
def principalRz (Z : ℝ) : ℂ := HA.RS S * weightW1hat W 1 *
  vertical (1 + δ1) (fun ξ => vertical (16 / 100) (fun z =>
    (Z : ℂ) ^ ((a : ℂ) / 2 + ξ - 1 + (h0 : ℂ) * z) * Complex.exp ((ξ + z - 1) ^ 2) *
      weightM R sd W z * HA.LS S 1 (6 * z) * HC.H U.one ![ξ,1,z] / HA.LS S η ξ))

/-- zf:principal-row, 06:413–477. The residue at z=1/6 carries R_S/6, accounted for in c₀. -/
theorem zf_principal_row : EulerHypotheses R η → (∀ v hv p, eulerNeighborhood p →
    ‖normalizedLocal R η U U.one v hv (p 0) (p 1) (p 2) - 1‖ < 1 / 2) → WeightSpec R sd W →
  principalConstant R sd W HA ≠ 0 ∧ ∃ C Z0 : ℝ, 0 < C ∧ 2 ≤ Z0 ∧ ∀ Z, Z0 ≤ Z →
    rowContribution R sd W η U {U.one} Z = principalConstant R sd W HA * principalSignal R η U HA HC Z +
      principalRw R sd W η U HA HC Z + principalRz R sd W η U HA HC Z ∧
    ‖principalRw R sd W η U HA HC Z‖ ≤ C * Z ^ ((7 / 15 - 5 / 10000 : ℝ)) ∧
    ‖principalRz R sd W η U HA HC Z‖ ≤ C * Z ^ ((7 / 15 - 5 / 10000 : ℝ)) := by
  sorry
/-- zf:small-rows, 06:479–551: any subset of a nonprincipal dyad, with explicit cardinal cost. -/
theorem zf_small_rows : EulerHypotheses R η → ∀ α B ε : ℝ, 0 ≤ α → 0 < B → 0 < ε → ∃ C : ℝ, 0 < C ∧
  ∀ T Z : ℝ, 1 ≤ T → 2 ≤ Z → ∀ rows : Finset U.U,
    (∀ u ∈ rows, u ≠ U.one ∧ u ∈ frequencyDyad η U T) → (rows.card : ℝ) ≤ B * T ^ α →
      rowContribution R sd W η U rows Z = tripleVertical (1 + δ1) (3 / 1000) (4 / 10)
        (fun ξ w z => ∑ u ∈ rows, rowKernel R sd W η U HA HC u Z ξ w z) ∧
      ‖rowContribution R sd W η U rows Z‖ ≤
        C * Z ^ Estar (1 + δ1) (3 / 1000) (4 / 10) * T ^ (α + 1 / 2 - 4 / 10 + ε) := by
  sorry
variable (ZD : ZeroDensityData η U HA)
/-- Actual central part of the good rows after the truncated ξ shift. -/
def goodCentral (rows : Finset U.U) (T Z : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ t in Set.Icc (-(T ^ ZD.ρ)) (T ^ ZD.ρ),
    vertical (3 / 1000) (fun w => vertical (4 / 10) (fun z =>
      ∑ u ∈ rows, rowKernel R sd W η U HA HC u Z (998 / 1000 + t * Complex.I) w z))

/-- zf:intermediate-rows, 06:552–605. The good reciprocal is used only in its rectangle.
The remainder is defined by subtraction so the conclusion bounds the entire contour remainder. -/
theorem zf_intermediate_rows : EulerHypotheses R η → ∀ ε A1 : ℝ, 0 < ε → 1 / ZD.ρ < A1 →
  ∃ C Z0 : ℝ, 0 < C ∧ 2 ≤ Z0 ∧ ∀ Z T, Z0 ≤ Z → Z ^ (9 / 100 : ℝ) < T →
    T ≤ Z ^ (10001 / 100000 : ℝ) → ZD.U0 ≤ T → ∀ rows : Finset U.U,
    (∀ u ∈ rows, u ≠ U.one ∧ u ∈ frequencyDyad η U T ∧ u ∉ ZD.E T) →
      ‖goodCentral R sd W η U HA HC ZD rows T Z‖ ≤
        C * Z ^ Estar (998 / 1000) (3 / 1000) (4 / 10) * T ^ (11 / 10 + ε) ∧
      ‖rowContribution R sd W η U rows Z - goodCentral R sd W η U HA HC ZD rows T Z‖ ≤
        C * Z ^ Estar (1 + δ1) (3 / 1000) (4 / 10) * T ^ (11 / 10 + ε - ZD.ρ * A1) := by
  sorry
/-- zf:far-rows, 06:607–630. Large but fixed z-line; constants independent of T,Z. -/
theorem zf_far_rows : EulerHypotheses R η → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ Z T, 2 ≤ Z →
  Z ^ (10001 / 100000 : ℝ) < T → ∀ rows : Finset U.U,
    (∀ u ∈ rows, u ≠ U.one ∧ u ∈ frequencyDyad η U T) →
    ‖rowContribution R sd W η U rows Z‖ ≤ C * Z ^ (3849 / 1000 + (1 / 10 : ℝ) * 350000) *
      T ^ (1 - (350000 : ℝ) + ε) := by
  sorry
/-- Finite dyad enumeration is arithmetic input, not a total-tsum surrogate for finiteness. -/
structure DyadEnumeration where
  rows : ℝ → Finset U.U
  mem_rows : ∀ T, 1 ≤ T → ∀ u, u ∈ rows T ↔ u ≠ U.one ∧ u ∈ frequencyDyad η U T
variable (DE : DyadEnumeration η U)
def nonprincipalDyad (T Z : ℝ) : ℂ := rowContribution R sd W η U (DE.rows T) Z

/-- zf:row-sum, 06:632–645: complex sum bound plus absolute convergence of the dyadic series. -/
theorem zf_row_sum : EulerHypotheses R η → ∃ C Z0 : ℝ, 0 < C ∧ 2 ≤ Z0 ∧ ∀ Z, Z0 ≤ Z →
  Summable (fun j : ℕ => ‖nonprincipalDyad R sd W η U DE ((2 : ℝ) ^ j) Z‖) ∧
  ‖∑' j : ℕ, nonprincipalDyad R sd W η U DE ((2 : ℝ) ^ j) Z‖ ≤ C * Z ^ ((7 / 15 - 4 / 10000 : ℝ)) := by
  sorry
/-- `zf:probe-asymptotic`, 06:647–681, for the actual probe and exact principal scalar. The
corrected probe-low route consumes the split Gauss data from `sol-gate-a2b`. -/
theorem zf_probe_asymptotic
    (hSplit : GaussSplit (D := D) (S := S) (H := H) (Bd := Bd) (A := A) (ϑ := ϑ) η) :
  EulerHypotheses R η → (∀ v hv p, eulerNeighborhood p →
    ‖normalizedLocal R η U U.one v hv (p 0) (p 1) (p 2) - 1‖ < 1 / 2) → WeightSpec R sd W → ∃ C Z0 : ℝ, 0 < C ∧ 2 ≤ Z0 ∧ ∀ Z, Z0 ≤ Z →
  ‖probe R W (Z ^ a) (Z ^ b) Z - principalConstant R sd W HA * principalSignal R η U HA HC Z‖ ≤
    C * Z ^ ((7 / 15 - 4 / 10000 : ℝ)) := by
  sorry
/-- `zf:f-bounds`, 06:682–707. Both endpoints and continuity are included. The corrected
`prop:probe-low` dependency carries `GaussSplit` (`sol-gate-a2b`). -/
theorem zf_f_bounds
    (hSplit : GaussSplit (D := D) (S := S) (H := H) (Bd := Bd) (A := A) (ϑ := ϑ) η) :
  EulerHypotheses R η → (∀ v hv p, eulerNeighborhood p →
    ‖normalizedLocal R η U U.one v hv (p 0) (p 1) (p 2) - 1‖ < 1 / 2) → WeightSpec R sd W →
  ContinuousOn (principalSignal R η U HA HC) (Set.Ioi 0) ∧
  (∃ C Z0 : ℝ, 0 < C ∧ 2 ≤ Z0 ∧ ∀ Z, Z0 ≤ Z →
    ‖principalSignal R η U HA HC Z‖ ≤ C * Z ^ ((7 / 15 - 1 / 20000 : ℝ))) ∧
  ∀ A0 : ℝ, 0 < A0 → ∃ C : ℝ, 0 < C ∧ ∀ Z, 0 < Z → Z ≤ 1 →
    ‖principalSignal R η U HA HC Z‖ ≤ C * Z ^ A0 := by
  sorry
end ZeroFree

section ZeroFreeSupplement
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}
variable (R : ReflectionSetup D S H Bd A ϑ bc μ v0) (sd : S.SelfDualMeasure A)
  (W : PoissonWeights (S := S)) (η : HeckeChar F) (U : FrequencyData S D η)
  (HA : HeckeAnalysis F) (HC : EulerCorrection R η U) (ZD : ZeroDensityData η U HA)
/-- zf:intermediate-rows, 06:552-605. Exceptional subsets use the original low-w contour and α=1/2. -/
theorem zf_intermediate_exceptional_rows : EulerHypotheses R η → ∀ ε : ℝ, 0 < ε →
  ∃ C : ℝ, 0 < C ∧ ∀ Z T, 2 ≤ Z → Z ^ (9 / 100 : ℝ) < T →
    T ≤ Z ^ (10001 / 100000 : ℝ) → ZD.U0 ≤ T → ∀ rows : Finset U.U,
    (∀ u ∈ rows, u ≠ U.one ∧ u ∈ ZD.E T) →
      ‖rowContribution R sd W η U rows Z‖ ≤
        C * Z ^ Estar (1 + δ1) (3 / 1000) (4 / 10) * T ^ (6 / 10 + ε) := by
  intro hEuler ε hε
  let HC0 : EulerCorrection R η U := canonicalEulerCorrection R η U
  obtain ⟨C, hC, hsmall⟩ :=
    zf_small_rows (R := R) (sd := sd) (W := W) (η := η) (U := U)
      (HA := HA) (HC := HC0) hEuler (1 / 2) ZD.Cexc ε (by norm_num) ZD.Cexc_pos hε
  refine ⟨C, hC, ?_⟩
  intro Z T hZ hTlo hThi hU0 rows hrows
  have hT : 1 ≤ T := le_trans (by norm_num : 1 ≤ (2 : ℝ))
    (le_trans ZD.U0_two hU0)
  have hsubset : rows ⊆ ZD.E T := by
    intro u hu
    exact (hrows u hu).2
  have hcard : (rows.card : ℝ) ≤ ZD.Cexc * T ^ (1 / 2 : ℝ) := by
    calc
      (rows.card : ℝ) ≤ ((ZD.E T).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsubset
      _ ≤ ZD.Cexc * T ^ (1 / 2 : ℝ) := ZD.E_count T hU0
  have hgood : ∀ u ∈ rows, u ≠ U.one ∧ u ∈ frequencyDyad η U T := by
    intro u hu
    exact ⟨(hrows u hu).1, ZD.E_sub T hU0 u ((hrows u hu).2)⟩
  have hbound := hsmall T Z hT hZ rows hgood hcard
  have hexp : (1 / 2 : ℝ) + 1 / 2 - 4 / 10 + ε = 6 / 10 + ε := by ring
  rw [hexp] at hbound
  exact hbound.2
end ZeroFreeSupplement

/-! ## Continuation dictionary and fixed exceptional-set conversion -/

section DensityCoherence
variable {D : FieldData F} {S : SData F CE condη} (η : HeckeChar F)
  (fd : FrequencyData S D η) (HA : HeckeAnalysis F)

def completeFromAnalysis (u : fd.U) (h : fd.omega u ≠ 1) :
    HeckeLContinuation (fd.omega u) :=
  (HA.2.2.1 (fd.omega u) (fd.omega_finiteOrder u) h).choose

theorem completeFromAnalysis_eq (u : fd.U) (h : fd.omega u ≠ 1) :
    (completeFromAnalysis η fd HA u h).value = HA.L (fd.omega u) :=
  (HA.2.2.1 (fd.omega u) (fd.omega_finiteOrder u) h).choose_spec

/-- Finite omitted Euler factors in the complete-to-incomplete dictionary (06:165–185). -/
def omittedFactors (χ : HeckeChar F) (s : ℂ) : ℂ :=
  ∏ v ∈ S.Sf, (1 - χ.primeValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))

/-- The canonical complete and incomplete continuations plus the finite-deletion identity needed
by zero density and the Euler product. Producer obligation, `sol-gate-a2b` (06:165–185). -/
structure IncompleteDictionary where
  complete : ∀ u : fd.U, fd.omega u ≠ 1 → HeckeLContinuation (fd.omega u)
  complete_eq : ∀ u h, (complete u h).value = HA.L (fd.omega u)
  incomplete : ∀ u : fd.U, fd.omega u ≠ 1 →
    IncompleteHeckeLContinuation S (η * (fd.kummer u)⁻¹)
  incomplete_eq : ∀ u h s, 997 / 1000 < s.re →
    (incomplete u h).value s = HA.LS S (η * (fd.kummer u)⁻¹) s
  factors_nonzero : ∀ χ : HeckeChar F, IsOfFinOrder χ → ∀ s : ℂ,
    0 < s.re → omittedFactors (S := S) χ s ≠ 0

/-- Analytic producer obligation for `IncompleteDictionary`; continuation and deletion uniqueness
are not consequences of aggregate `HeckeAnalysis` fields alone (`prop:euler-product`, 05:407–433;
`prop:zero-density`, 06:165–185). -/
theorem incompleteDictionary_exists : Nonempty (IncompleteDictionary η fd HA) := by
  sorry

/-- Exact output required to populate the unchanged `ZeroDensityData` record. Its single `E T`
also covers the trivial row and the complete continuation zeros (06:165–185). -/
structure DensityOutput (K : IncompleteDictionary η fd HA) where
  ρ : ℝ
  ρ_pos : 0 < ρ
  U0 : ℝ
  U0_two : 2 ≤ U0
  Cexc : ℝ
  Cexc_pos : 0 < Cexc
  E : ℝ → Finset fd.U
  sub : ∀ T, U0 ≤ T → ∀ u ∈ E T, T ≤ fd.q u ∧ fd.q u < 2 * T
  count : ∀ T, U0 ≤ T → ((E T).card : ℝ) ≤ Cexc * T ^ (1 / 2 : ℝ)
  covers : ∀ T, U0 ≤ T → ∀ u, T ≤ fd.q u → fd.q u < 2 * T →
    (fd.omega u = 1 ∨ ∃ h : fd.omega u ≠ 1, ∃ s : ℂ,
      996 / 1000 ≤ s.re ∧ |s.im| ≤ 4 * T ^ ρ ∧ (K.complete u h).value s = 0) → u ∈ E T
  reciprocal : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ T, U0 ≤ T →
    ∀ u, T ≤ fd.q u → fd.q u < 2 * T → u ∉ E T → ∀ h : fd.omega u ≠ 1,
      ∀ s : ℂ, 998 / 1000 ≤ s.re → |s.im| ≤ 2 * T ^ ρ →
        ‖((K.incomplete u h).value s)⁻¹‖ ≤ C * T ^ ε

/-- Corrected producer contract for `prop:zero-density`; its exponent respects the actual
conductor-height exponent used by the detector (06:165–185). -/
def densityProducerStatement (K : IncompleteDictionary η fd HA) : Prop :=
  IsOfFinOrder η → (∀ v, v ∉ S.Sf → η.UnramifiedAt v) →
    ∀ AF : ℝ, 0 < AF → ConductorHeightBound (F := F) AF →
      ∃ O : DensityOutput η fd HA K, O.ρ < min (1 / 10) (1 / (AF + 1))

/-- Zero-density producer obligation with the corrected fixed-`E` and continuation dictionary.
The analytic theorem remains to be proved (06:165–185). -/
theorem prop_zero_density_dictionary (K : IncompleteDictionary η fd HA) :
    densityProducerStatement η fd HA K := by
  sorry

/-- The corrected producer's complete-zero coverage supplies nonvanishing for the unchanged
`ZeroDensityData` consumer; finite deleted factors are explicit. This adapter for `prop:zero-density`
is proved (06:165–185). -/
def density_to_consumer (K : IncompleteDictionary η fd HA)
    (O : DensityOutput η fd HA K) : ZeroDensityData η fd HA where
  ρ := O.ρ
  ρ_pos := O.ρ_pos
  U0 := O.U0
  U0_two := O.U0_two
  Cexc := O.Cexc
  Cexc_pos := O.Cexc_pos
  E := O.E
  E_sub := by
    intro T hT u hu
    exact ⟨(O.sub T hT u hu).1, (O.sub T hT u hu).2⟩
  E_count := O.count
  covers := by
    intro T hT u hu hbad
    have heq := fd.omega_induces_twist u
    apply O.covers T hT u hu.1 hu.2
    rcases hbad with hp | ⟨s, hs, ht, hz⟩
    · exact Or.inl (heq.trans hp)
    · by_cases hn : fd.omega u = 1
      · exact Or.inl hn
      · refine Or.inr ⟨hn, s, hs, ht, ?_⟩
        rw [K.complete_eq u hn, heq]
        exact hz
  reciprocal := by
    intro ε hε
    obtain ⟨C, hC, hb⟩ := O.reciprocal ε hε
    refine ⟨C, hC, ?_⟩
    intro T hT u hu hgood s hs ht
    have heq := fd.omega_induces_twist u
    have hn : fd.omega u ≠ 1 := by
      intro hp
      exact hgood (O.covers T hT u hu.1 hu.2 (Or.inl hp))
    have hl : HA.L (fd.omega u) s ≠ 0 := by
      intro hz
      apply hgood
      apply O.covers T hT u hu.1 hu.2
      refine Or.inr ⟨hn, s, by linarith, ?_, ?_⟩
      · have hpow : 0 ≤ T ^ O.ρ := Real.rpow_nonneg (by linarith [O.U0_two]) _
        nlinarith
      · rw [K.complete_eq u hn]
        exact hz
    refine ⟨?_, ?_⟩
    · change HA.L (η * (fd.kummer u)⁻¹) s *
        omittedFactors (S := S) (η * (fd.kummer u)⁻¹) s ≠ 0
      rw [← heq]
      exact mul_ne_zero hl (K.factors_nonzero _ (fd.omega_finiteOrder u) s (by linarith))
    · have hh := hb T hT u hu.1 hu.2 hgood hn s hs ht
      rwa [K.incomplete_eq u hn s (by linarith)] at hh

end DensityCoherence

/-! ## Frequency dictionary adapters for §6 row families -/

section FrequencyRowCoherence
variable {D : FieldData F} {S : SData F CE condη} (η : HeckeChar F)
  (fd : FrequencyData S D η)

/-- Complete-shell form of the stored frequency count and conductor data; the fixed local
component set and idelic induction are retained (06:13–30). -/
def rowFamilyStatement : Prop :=
  ∃ Ccount Ccond : ℝ, 0 < Ccount ∧ 0 < Ccond ∧ ∃ LS : Finset (SLocalCharacter S),
    ∀ T : ℝ, 2 ≤ T → {u : fd.U | T ≤ fd.q u ∧ fd.q u < 2 * T}.Finite ∧
      (Set.ncard {u : fd.U | T ≤ fd.q u ∧ fd.q u < 2 * T} : ℝ) ≤ Ccount * T ∧
      (∀ u, T ≤ fd.q u → fd.q u < 2 * T → ∃ f : Ideal (𝓞 F),
        IsPrimitiveConductor (fd.omega u) f ∧ (Ideal.absNorm f : ℝ) ≤ Ccond * T ∧
          SComponent S (fd.omega u) ∈ LS) ∧
      Function.Injective fd.omega ∧ (∀ u, fd.kummer u = 1 ↔ u = fd.one) ∧
      (∀ u, fd.omega u = η * (fd.kummer u)⁻¹)

/-- Proved adapter from `FrequencyData` to the complete finite-shell row dictionary consumed by
`zf:row-conductor-family`; the low shell is separate below (06:13–30). -/
theorem rowFamily_from_data : rowFamilyStatement η fd := by
  obtain ⟨Cc, hCc, hc⟩ := fd.dyadic_count
  obtain ⟨Cf, hCf, hf⟩ := fd.conductor_bound
  obtain ⟨LS, hLS⟩ := fd.local_components_finite
  refine ⟨Cc, 2 * Cf, hCc, by positivity, LS, ?_⟩
  intro T hT
  obtain ⟨hfin, hcount⟩ := hc T hT
  refine ⟨hfin, hcount, ?_, fd.omega_injective, fd.kummer_principal_iff,
    fd.omega_induces_twist⟩
  intro u hu hul
  obtain ⟨f, hprim, hb⟩ := hf u
  refine ⟨f, hprim, ?_, hLS u⟩
  nlinarith

/-- The initial shell is finite by `FrequencyData.low_shell_bound`, producing the dyad
enumeration consumed by `zf:row-sum` (06:13–30). -/
theorem dyadEnumeration_nonempty : Nonempty (DyadEnumeration η fd) := by
  have hfin (T : ℝ) (hT : 1 ≤ T) :
      {u : fd.U | u ≠ fd.one ∧ T ≤ fd.q u ∧ fd.q u < 2 * T}.Finite := by
    by_cases hT2 : 2 ≤ T
    · exact (fd.dyadic_count.choose_spec.2 T hT2).1.subset (by intro u hu; exact hu.2)
    · apply fd.low_shell_bound.choose_spec.2.1.subset
      intro u hu
      exact ⟨le_trans hT hu.2.1, lt_trans hu.2.2 (by linarith)⟩
  refine ⟨⟨fun T => if hT : 1 ≤ T then (hfin T hT).toFinset else ∅, ?_⟩⟩
  intro T hT u
  simp [hT, frequencyDyad]

end FrequencyRowCoherence

end ArtinPrimitiveRoots.A2
