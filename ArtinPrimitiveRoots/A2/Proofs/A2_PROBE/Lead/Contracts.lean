import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE.Lead.Defs
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
open ArtinPrimitiveRoots A1 A2
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a2_probe_sol
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}
variable (R : ReflectionSetup D S H Bd A ϑ bc μ v0) (sd : S.SelfDualMeasure A)
variable (W : ProbeWeights (S := S)) (η : HeckeChar F) (U : FrequencyData S D η)

/-- The already proved private coset producer, exposed as a callback. -/
def LeadCosetContract : Prop :=
  ∀ (I : S.ExtIdeal) (a : Fˣ), S.IsGen (a : F) I.1 → ∀ (b : S.R) (k : S.FSˣ),
    Summable (fun m : S.R =>
      ‖W.W0 (S.diag ((b : F) + (a : F) * (m : F)) * (k⁻¹ : S.FSˣ).val)‖) ∧
    Summable (fun h : S.R =>
      ‖leadFourier sd W ((k : S.FS) * S.diag ((h : F) / (a : F)))‖) ∧
    (∑' m : S.R,
      W.W0 (S.diag ((b : F) + (a : F) * (m : F)) * (k⁻¹ : S.FSˣ).val)) =
      ((S.absS (k : S.FS) / qI I.1 : ℝ) : ℂ) *
        ∑' h : S.R, S.e A (S.diag ((b : F) * (h : F) / (a : F))) *
          leadFourier sd W ((k : S.FS) * S.diag ((h : F) / (a : F)))

/-- The accepted finite transform, bound and Gamma invariance, plus Gauss row bound. -/
def LeadFiniteContract : Prop :=
  (∀ (s I : S.ExtIdeal) (a : Fˣ), S.IsGen (a : F) I.1 → Bd.Allowed a → ∀ h : S.R,
    (∑ᶠ m : ResidueRing R.exterior (R.exterior.mul s I),
      (qI s.1 ^ (-(1 / 2 : ℝ)) : ℝ) * leadFiniteGauss R s (-(m.out : F)) *
        chiIdealPow D I.1 (m.out : F) 1 *
          S.e A (S.diag ((h : F) * (m.out : F) / ((bc.gen s : F) * (a : F))))) =
      (qI s.1 ^ (1 / 2 : ℝ) : ℝ) * leadFiniteFactor R s I a (h : F) ∧
    ‖leadFiniteFactor R s I a (h : F)‖ ≤ qI s.1 * qI I.1 ∧
    ∀ γ : Gamma S,
      leadFiniteFactor R s I a (((γ.1 : Fˣ) : F) * (h : F)) =
        leadFiniteFactor R s I a (h : F)) ∧
  (∀ (s : S.ExtIdeal) (m : S.R), ‖leadFiniteGauss R s (m : F)‖ ≤ qI s.1)

/-- Actual full-sheet integrability and the full integral-of-norm bound. -/
def LeadSheetsContract : Prop :=
  (∀ T : ℝ, 0 < T → Integrable (leadFourier sd W) (R.sheets.sheet T)) ∧
  ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T →
    (∫ y, ‖leadFourier sd W y‖ ∂(R.sheets.sheet T)) ≤ C / T ^ 2

/-- Current classification proof, including uniqueness only of the pair. -/
def LeadClassContract : Prop :=
  ∀ x : S.R, (x : F) ≠ 0 → ∃! ur : U.U × S.ExtIdeal, ∃ γ : Gamma S,
    (x : F) = ((γ.1 : Fˣ) : F) * (U.repr ur.1 : F) * (bc.gen ur.2 : F) ^ 6

/-- Existing generator-ratio producer. -/
def LeadRatioContract : Prop :=
  ∀ (I : Ideal (𝓞 F)) (x y : F), S.IsGen x I → S.IsGen y I →
    ∃ ε : S.US, x = (ε : Fˣ) * y

/-- A triple reindexing equivalence with its exact field-value law. -/
def LeadEquivContract : Prop :=
  ∃ e : ((U.U × S.ExtIdeal) × Gamma S) ≃ {x : S.R // (x : F) ≠ 0},
    ∀ p, ((e p).1 : F) = ((p.2.1 : Fˣ) : F) *
      (U.repr p.1.1 : F) * (bc.gen p.1.2 : F) ^ 6

/-- Pointwise inversions already available in the original module. -/
def LeadInversionsContract : Prop :=
  (∀ T : ℝ, 0 < T → leadV0 R sd W T =
    leadVertical 2 (fun z => leadM R sd W z * (T : ℂ) ^ (-z))) ∧
  (∀ T : ℝ, 0 < T → W.W1 T =
    leadVertical 4 (fun w => leadW1hat W w * (T : ℂ) ^ (-w))) ∧
  (∀ T : ℝ, 0 < T → (PG T : ℂ) =
    leadVertical 5 (fun ξ => Complex.exp (ξ ^ 2) * (T : ℂ) ^ (-ξ)))

/-- The existing uniform coefficient bound at the actual three real parts. -/
def LeadCoeffBoundContract : Prop :=
  ∀ ξ w z : ℂ, ξ.re = 4 → w.re = 4 → z.re = 2 → ∀ (u : U.U)
    (p : S.SqfExtIdeal × S.ExtIdeal × S.ExtIdeal × S.ExtIdeal),
    ‖leadCalFTerm R η U u ξ w z p‖ ≤
      (qI p.1.1 ^ (-3 : ℝ)) * (qI p.2.1.1 ^ (-10 : ℝ)) *
        (qI p.2.2.1.1 ^ (-3 : ℝ)) * (qI p.2.2.2.1 ^ (-12 : ℝ))

/-- The final orbit clause, used as the preceding target by the Mellin assembly. -/
def LeadExpansionContract : Prop :=
  ∀ X Y Z : ℝ, 0 < X → 0 < Y → 0 < Z →
    Summable (fun p => ‖leadOrbitTerm R sd W η U X Y Z p‖) ∧
      leadProbe R W X Y Z = ((X ^ (1 / 2 : ℝ) / Y : ℝ) : ℂ) *
        ∑' p, leadOrbitTerm R sd W η U X Y Z p

end ArtinPrimitiveRoots.Proofs.a2_probe_sol
