import ArtinPrimitiveRoots.TypeII.PD.MemoryResults
import ArtinPrimitiveRoots.TypeII.PP.Results

/-!
# Design B-PD-MajorArcs: drop-in replacement for `TypeII/PD/MajorArcs.lean` (PD §5)

Replaces the mismatched `major_separation` and `major_energy`, and corrects the stated `major_term`
(it lacked the size hypothesis on `β` and the smoothness/support
hypotheses on `η`, so it was false as stated).  Declarations marked COPY are verbatim copies of
the frozen ones and stay unchanged.

What changed mathematically (PD 05:257-433):
* `B_λ(t)` is `(1/Y) Σ_b η(b/Y) e(-λb/Y) (∏V_i^{-1}) χ(b) b^{it}` over products `b` of one prime
  per group (maj:polynomials) — not a product over bands: the cutoff `η(b/Y)e(-λb/Y)` couples
  the bands, and PD isolates one band by Mellin inversion of `f_λ(y) = η(y)e(-λy)` (05:381-415).
* All three polynomials carry Dirichlet characters modulo the arc denominator `k ≤ L^{A₀}`
  (the six-character expansion, 05:263-276).  The frozen `major_energy` allowed arbitrary
  bounded twists of `α`, for which the long-coefficient hypothesis gives nothing.
* `major_separation` is the reduction (maj:bound) ⇐ (maj:energy) for all characters and arc
  parameters; `major_energy` proves (maj:energy).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical MeasureTheory
open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.TypeII.PP

noncomputable section

/-- COPY. Small-prime polynomial on one prime band. -/
noncomputable def bandPrimePolynomial (P : ℝ) (Pset : Finset ℕ)
    (chiValue : ℕ → ℂ) (xi t : ℝ) : ℂ :=
  (1 / P) * ∑ p ∈ Pset,
    chiValue p * Complex.exp (Complex.I * (t + xi) * Real.log (p : ℝ))

/-- COPY. The long coefficient polynomial `M_α(t)` with an arbitrary twist. -/
noncomputable def alphaFrequency {δ C c₁ c₂ : ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (x t : ℝ) (chiValue : ℕ → ℂ) : ℂ :=
  (1 / family.Hm x) *
    ∑ m ∈ familyTerms family x,
      family.alpha x m * chiValue m * Complex.exp (Complex.I * t * Real.log (m : ℝ))

/-- COPY. The second-variable polynomial `N_β(t)` with an arbitrary twist. -/
noncomputable def betaFrequency (Hn : ℝ) (beta chiValue : ℕ → ℂ) (t : ℝ) : ℂ :=
  (1 / Hn) *
    ∑ n ∈ dyadicIntegers Hn,
      beta n * chiValue n * Complex.exp (Complex.I * t * Real.log (n : ℝ))

/-- COPY. The finite family of unit intervals that meet the large-frequency set. -/
def sparseUnitIntervals (x X B P A_s : ℝ) (Pset : Finset ℕ)
    (chiValue : ℕ → ℂ) (xi : ℝ) : Set ℤ :=
  {j : ℤ | ∃ t : ℝ, (j : ℝ) ≤ t ∧ t ≤ (j : ℝ) + 1 ∧
    |t| ≤ 2 * X * Real.rpow (Real.log x) B ∧
    Real.rpow (Real.log x) A_s *
      ‖bandPrimePolynomial P Pset chiValue xi t‖ > 1}

/-- COPY. Supremum of the `N_β` energy on one unit interval. -/
noncomputable def betaUnitIntervalEnergy (Hn : ℝ) (beta chiValue : ℕ → ℂ)
    (j : ℤ) : ℝ :=
  sSup ((fun t : ℝ => ‖betaFrequency Hn beta chiValue t‖ ^ 2) ''
    Set.Icc (j : ℝ) ((j : ℝ) + 1))

/-- COPY. The energy integral in `maj:energy`. -/
noncomputable def majorEnergyIntegral (T : ℝ) (B M N : ℝ → ℂ) : ℝ :=
  ∫ t in (-T)..T, ‖B t * M t * N t‖ ^ 2

/-- COPY. `maj:sparse-frequency` — PD `05-major-arcs.tex:165-255`, Lemma 5.3. Correction from
refutation lane `sol-gate-b` fixes `C₁` before the asymptotic constants. -/
theorem sparse_frequency (δ C : ℝ) (hδ : 0 < δ) (hC : 0 < C) :
    ∀ C₁ : ℝ, 0 < C₁ → ∀ B A_s : ℝ, 0 < B → 0 < A_s →
      ∃ C₀ x₀ : ℝ, 0 < C₀ ∧ 2 < x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          let L := Real.log x
          ∀ X : ℝ, x / 2 ≤ X → X ≤ 2 * x →
          ∀ P : ℝ, (1 / 20 : ℝ) * Real.rpow L (1 / 10 : ℝ) ≤ Real.log P →
              Real.log P ≤ C₁ * Real.rpow L (1 / 5 : ℝ) →
              ∀ Pset : Finset ℕ,
                (∀ p ∈ Pset, p.Prime ∧ P ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * P) →
                ∀ q : ℕ, 1 ≤ q →
                  ∀ χ : DirichletCharacter ℂ q, ∀ xi : ℝ,
                    ∀ Hn : ℝ, Real.rpow x δ ≤ Hn → Hn ≤ 2 * x →
                      ∀ beta chiN : ℕ → ℂ,
                        (∀ n ∈ dyadicIntegers Hn, ‖beta n‖ ≤ Real.rpow L C) →
                        (∀ n, ‖chiN n‖ ≤ 1) →
                          let bad := sparseUnitIntervals x X B P A_s Pset
                            (fun p => (χ (p : ZMod q) : ℂ)) xi
                          (Set.ncard bad : ℝ) ≤
                            Real.exp (C₀ * Real.rpow L (91 / 100 : ℝ)) ∧
                          (∑' j : ℤ, if j ∈ bad then
                            betaUnitIntervalEnergy Hn beta chiN j else 0) ≤
                            C₀ * Real.rpow L (2 * C + 1) := by
  sorry

/-- NEW. Products `b` of one prime from every group, as a finite set of tuples. -/
def markedTupleSet (x : ℝ) (K : ℕ) (a : Fin K → ℝ) : Finset (Fin K → ℕ) :=
  Fintype.piFinset fun i => primeBand x (a i)

/-- NEW. `B_λ(t)` of (maj:polynomials), PD 05:311-313:
`(1/Y) Σ_b η(b/Y) e(-λb/Y) (∏_i V_i^{-1}) χ(b) b^{it}`. -/
def majorBPolynomial (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (Y lam : ℝ) (eta : ℝ → ℝ)
    {k : ℕ} (χ : DirichletCharacter ℂ k) (t : ℝ) : ℂ :=
  (1 / Y : ℂ) * ∑ tb ∈ markedTupleSet x K a,
    (eta ((tupleProduct tb : ℝ) / Y) : ℂ) *
      additiveCharacter (-lam * (tupleProduct tb : ℝ) / Y) *
      ((∏ i : Fin K, (bandMass x (a i))⁻¹ : ℝ) : ℂ) *
      χ ((tupleProduct tb : ℕ) : ZMod k) *
      Complex.exp (Complex.I * t * Real.log (tupleProduct tb : ℝ))

/-- NEW. `M_α(t)` with a Dirichlet character (maj:M-definition, PD 05:44-55). -/
def majorMPolynomial {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂) (x : ℝ)
    {k : ℕ} (χ : DirichletCharacter ℂ k) (t : ℝ) : ℂ :=
  alphaFrequency family x t (fun m => χ (m : ZMod k))

/-- NEW. `N_β(t)` with a Dirichlet character (maj:polynomials). -/
def majorNPolynomial (Hn : ℝ) (beta : ℕ → ℂ) {k : ℕ} (χ : DirichletCharacter ℂ k) (t : ℝ) : ℂ :=
  betaFrequency Hn beta (fun n => χ (n : ZMod k)) t

/-- NEW. The energy of (maj:energy): `∫_{|t| ≤ 2XL^{B₁}} |B_λ M_α N_β|²`, one modulus `k`
for the three characters. -/
def majorEnergy (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (Y lam B₁ : ℝ) (eta : ℝ → ℝ)
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ)
    {k : ℕ} (χb χm χn : DirichletCharacter ℂ k) : ℝ :=
  majorEnergyIntegral (2 * (family.Hm x * family.Hn x) * Real.rpow (Real.log x) B₁)
    (majorBPolynomial x K a Y lam eta χb) (majorMPolynomial family x χm)
    (majorNPolynomial (family.Hn x) beta χn)

/-- `t2:pd.major-separation` — PD 05:257-376.  REPLACES the frozen `major_separation`.  The
reduction of (maj:bound) to (maj:energy): arcs disjoint; on an arc `θ = h/k + λ/Y` all
variables are units mod `k`; six-character Fourier expansion of `e(h(bmn-ars-b+a)/k)` with total
mass `≤ k⁶`; exact Mellin separation (maj:Mellin-separation) of `ψ_λ(X(w-w'))` with transform
decay (maj:transform-decay) (`B₀` fixed after `A₀`); normalization (maj:XY-normalization);
product mean square (maj:product-mean) (exponent `C₄(C)`); tails beyond the retained rectangle
`|s'| ≤ L^{B₁}`, `|t| ≤ XL^{B₁}` (maj:retained-rectangle); Cauchy in `t`; the conjugate endpoint
polynomial `Q'` is covered by the same hypothesis (conjugate characters, `-λ`, `t ↦ -t`). -/
theorem major_separation (δ C c₁ c₂ : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (hδ : 0 < δ) (hC : 0 < C) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (ha : ValidBands K a)
    (eta psi : ℝ → ℝ) (heta : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) eta) (heta_supp : Function.support eta ⊆ Set.Icc 1 4)
    (heta_nonneg : ∀ y, 0 ≤ eta y) (heta_part : IsDyadicPartition eta)
    (hpsi : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) psi) (hpsi_supp : HasCompactSupport psi)
    (hpsi_one : ∀ t ∈ Set.Icc (-4 : ℝ) 4, psi t = 1) :
    ∀ A₀ D : ℝ, 0 < A₀ → 0 < D →
      ∃ B₁ A' : ℝ, 0 < B₁ ∧ 0 < A' ∧
        ∀ family : CoefficientFamily δ C c₁ c₂,
          ∃ C' x₀ : ℝ, 0 < C' ∧ 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
            ∀ beta : ℕ → ℂ,
              (∀ n, beta n ≠ 0 → n ∈ dyadicIntegers (family.Hn x) ∧
                roughAbove n (roughCutoff x)) →
              (∀ n ∈ dyadicIntegers (family.Hn x),
                ‖beta n‖ ≤ Real.rpow (Real.log x) C) →
              ∀ Y ∈ dyadicScales x K,
                (∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.rpow (Real.log x) A₀ →
                  ∀ χb χm χn : DirichletCharacter ℂ k, ∀ lam : ℝ,
                    |lam| ≤ 2 * Real.rpow (Real.log x) A₀ →
                      majorEnergy x K a Y lam B₁ eta family beta χb χm χn ≤
                        Real.rpow (Real.log x) (-A')) →
                ‖majorArcSum x K a Y A₀ family beta eta psi‖ ≤
                  C' * (family.Hm x * family.Hn x) * Y * Real.rpow (Real.log x) (-D) := by
  sorry

/-- `t2:pd.major-energy` — PD 05:371-433.  REPLACES the frozen `major_energy`.  (maj:energy):
for every fixed `A₀, B₁, A'` the energy is `≪ L^{-A'}`, uniformly in the characters of modulus
`≤ L^{A₀}` and `|λ| ≤ 2L^{A₀}`.  Proof: write `b = p b'` with `p ∈ 𝒫₁` in `O(L)` dyads `[P,2P)`;
Mellin inversion of `f_λ(y) = η(y)e(-λy)` with `L¹` norm `≪ L^{C₅}`; Minkowski reduces to
(maj:isolated-energy) uniformly in the shift `ξ` (`|Q_{b'}| ≪ 1`); on `|P_s| ≤ L^{-A_s}` use
(maj:product-mean); on the sparse unit intervals of `sparse_frequency` use
`|M_α(t)| ≪ L^{-A}` — this is exactly the hypothesis `HasLongCoefficientCancellation` (the role
of PD Lemma 5.2) applied with `B = B₁ + 1`. -/
theorem major_energy (δ C c₁ c₂ : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (hδ : 0 < δ) (hC : 0 < C) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (ha : ValidBands K a)
    (eta : ℝ → ℝ) (heta : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) eta) (heta_supp : Function.support eta ⊆ Set.Icc 1 4)
    (heta_nonneg : ∀ y, 0 ≤ eta y) :
    ∀ A₀ B₁ A' : ℝ, 0 < A₀ → 0 < B₁ → 0 < A' →
      ∀ family : CoefficientFamily δ C c₁ c₂, HasLongCoefficientCancellation family →
        ∃ C' x₀ : ℝ, 0 < C' ∧ 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
          ∀ beta : ℕ → ℂ,
            (∀ n, beta n ≠ 0 → n ∈ dyadicIntegers (family.Hn x) ∧
              roughAbove n (roughCutoff x)) →
            (∀ n ∈ dyadicIntegers (family.Hn x),
              ‖beta n‖ ≤ Real.rpow (Real.log x) C) →
            ∀ Y ∈ dyadicScales x K,
              ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.rpow (Real.log x) A₀ →
                ∀ χb χm χn : DirichletCharacter ℂ k, ∀ lam : ℝ,
                  |lam| ≤ 2 * Real.rpow (Real.log x) A₀ →
                    majorEnergy x K a Y lam B₁ eta family beta χb χm χn ≤
                      C' * Real.rpow (Real.log x) (-A') := by
  sorry

/-- `prop:major-term` — PD 05:9-30, Proposition 5.1.  CORRECTED restatement of the frozen
`major_term`: adds `‖β_n‖ ≤ L^C` and the smoothness/support of `η` (without them the bound is
false).  Proof: `major_separation` with `D`, then `major_energy` with the resulting `B₁, A'`.
Correction from refutation lane `sol-gate-b` fixes the family and cutoffs before `C_D` and `x₀`. -/
theorem major_term
    (δ C Dstar q_d c₁ c₂ : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (hδ : 0 < δ) (hC : 0 < C) (hD : 0 < Dstar)
    (hqd₀ : 0 < q_d) (hqd₁ : q_d < 1)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (ha : ValidBands K a) :
    ∀ A₀ : ℝ, 0 < A₀ →
      ∀ family : CoefficientFamily δ C c₁ c₂,
        HasLongCoefficientCancellation family →
        ∀ eta psi : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) eta → Function.support eta ⊆ Set.Icc 1 4 →
          (∀ y, 0 ≤ eta y) → IsDyadicPartition eta →
          ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) psi → HasCompactSupport psi →
          (∀ t ∈ Set.Icc (-4) 4, psi t = 1) →
          ∃ C_D x₀ : ℝ, 0 < C_D ∧ 2 ≤ x₀ ∧
          ∀ x : ℝ, x₀ ≤ x →
            ∀ Y, Y ∈ dyadicScales x K →
            ∀ beta : ℕ → ℂ,
              (∀ n, beta n ≠ 0 → n ∈ dyadicIntegers (family.Hn x) ∧
                roughAbove n (roughCutoff x)) →
              (∀ n ∈ dyadicIntegers (family.Hn x),
                ‖beta n‖ ≤ Real.rpow (Real.log x) C) →
                ‖majorArcSum x K a Y A₀ family beta eta psi‖ ≤
                  C_D * (family.Hm x * family.Hn x) * Y *
                    Real.rpow (Real.log x) (-Dstar) := by
  sorry

/-- COPY. `t2:pd.completion` — PD `05-major-arcs.tex:435-465` and 08-type-ii.tex:236-250.
Its proof now uses `minor_replacement` (B-PD-Chain) and the corrected `major_term`. -/
theorem completion
    (δ C Dstar q_d c₁ c₂ : ℝ)
    (hδ : 0 < δ) (hC : 0 < C) (hD : 0 < Dstar)
    (hqd₀ : 0 < q_d) (hqd₁ : q_d < 1)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ a : Fin K → ℝ, ValidBands K a →
      ∀ family : CoefficientFamily δ C c₁ c₂,
        HasLongCoefficientCancellation family →
        ∃ C' x₀ : ℝ, 0 < C' ∧ 2 ≤ x₀ ∧
          ∀ x : ℝ, x₀ ≤ x →
            ∀ beta : ℕ → ℂ,
              (∀ n, beta n ≠ 0 → n ∈ dyadicIntegers (family.Hn x) ∧
                roughAbove n (roughCutoff x)) →
              (∀ n ∈ dyadicIntegers (family.Hn x),
                ‖beta n‖ ≤ Real.rpow (Real.log x) C) →
              ∀ F : ℕ → ℂ, IsMarkedInvariant x K a F →
                ‖markedBilinearSum x K a q_d F (family.Hm x) (family.Hn x)
                  (family.interval x) (family.alpha x) beta‖ ≤
                    C' * (family.Hm x * family.Hn x) *
                      Real.rpow (Real.log x) (-Dstar) := by
  sorry

end

end ArtinPrimitiveRoots.TypeII.PD
